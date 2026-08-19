# Writing a Rocq cost probe: allocated words, time, peak RSS

How to measure what a heavy `vm_compute` actually costs, and how to write the
probe files. Distilled from the 2026-08-01 CFGVer investigation
(`PLAN-encoded-instr.md` §9), where switching from wall clock to allocated words
is what turned an unresolved three-session question into an exact model.

## 0. Which metric, and why

| metric | how | use it for |
|---|---|---|
| **`allocated_words`** | OCaml GC stats at exit | **the default.** Total work. Deterministic to ~0.0002% |
| `top_heap_words` | same | peak heap; the memory-ceiling question |
| user CPU | `Time Eval …` prints `(Yu,Zs)`; `/usr/bin/time %U` | cross-checking; far better than wall |
| peak RSS | `/usr/bin/time %M` (in KB) | what bounds `make -jN` |
| wall clock | anything | **almost nothing** — see below |

Measured on this box, same day, byte-identical probes: wall clock came out
1.055/3.567/7.107 s in one run and 0.679/1.527/3.491 s in the next — **2.3×
apart**. The same runs' `allocated_words` differed by 1,100 words in 527 M.
Anything you intend to compare or quote should be allocated words.

Allocation also tracks time closely *within* one run (ratios 2.39/2.29/2.35 vs
2.25/2.29/2.50), so you lose nothing by using it.

## 1. Turning on GC stats

`OCAMLRUNPARAM='v=0x400'` makes the OCaml runtime dump GC counters to stderr
when the process exits:

```
allocated_words: 2114489442
minor_words: ...
major_words: ...
minor_collections: ...
major_collections: 11
heap_words: ...
top_heap_words: 388005888
compactions: 0
```

`rocq_compile_file` cannot set env vars, so this is one of the legitimate uses of
a direct `coqc` call:

```bash
OCAMLRUNPARAM='v=0x400' coqc -w none \
  -Q case_study/RiscvPmp Katamaran.RiscvPmp -R theories Katamaran \
  case_study/RiscvPmp/CFGVer/Example/MyProbe.v
```

Add `/usr/bin/time` when you also want RSS and user CPU:

```bash
OCAMLRUNPARAM='v=0x400' /usr/bin/time -f "@@rss=%MkB wall=%e user=%U" coqc … 2>&1
```

## 2. File layout: one definitions file, one runner per data point

**Rule: ONE heavy `Eval` per `coqc` process.** Several in one process contaminate
each other — later ones run against a heap earlier ones grew. Measured 2026-07-29
on byte-identical computations, within-run growth ratios *flipped direction*
between runs (5.08→5.99 vs 5.72→2.60) and peak RSS differed 3.30 vs 5.35 GB.

So: definitions in a shared file, and a tiny runner per N.

```coq
(* MyCommon.v — definitions only, NO Eval. *)
(* Require EXPORT, not Import: downstream runners need the notations
   (𝕊, the N numeral scope). With a bare Import they print raw BinNums. *)
From Katamaran Require Export RiscvPmp.CFGVer.Example.Prelude.

Definition my_contract (n : nat) : @CFGVerifierContract ["p" :: ty_xlenbits] := …

Definition my_measure (n : nat) : SomeResult :=
  cfg_map (my_contract n) (fun ia p exits P i ec fl =>
    census (CFG_VC_triple p exits P i fl)).
```

```coq
(* MyRun8.v *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.MyCommon.
Time Eval vm_compute in (my_measure 8).
```

```coq
(* MyRun0.v — THE BASELINE. Imports only, no Eval. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.MyCommon.
```

The baseline is not optional: the `Require` alone allocates ~393 M words here, so
raw figures are ~75% import noise at small N. **Every number you report is
`allocated_words(runner) − allocated_words(baseline)`.**

Probe files are not in `_CoqProject`, so `make` has no rule for them — compile
via `rocq_compile_file` (resolves through the `-Q`/`-R` mappings) or the direct
`coqc` above.

## 3. Force the computation with a cheap consumer — never print

`vm_compute` is call-by-value, so wrapping the thing you want in a small-result
consumer forces the whole computation while leaving nothing to print. A printed
VC is easily 100 MB and you will mostly measure the *printer*: a historical note
claimed "the raw VC times out >90 s at N=2" while the full pipeline over it took
7.6 s — impossible under CBV, and entirely a printing artifact.

```coq
Time Eval vm_compute in (SymProp.Statistics.size (CFG_VC_triple …)).
```

`SymProp.Statistics.size` returns **`N`, not `nat`** — no `N.of_nat`. It also
scores `error` and `block` as 0 and counts only nodes, never the terms inside
them, so write your own census when terms matter.

## 4. A census over the raw tree

Sum whatever you care about over the RAW tree (never postprocessed —
`postprocess`'s `solve_uvars` substitutes variable definitions back in, shrinking
node counts while expanding terms). Pattern: a record, an add function, one
`Fixpoint`.

```coq
Record C : Set := MkC { c_nodes : N ; c_pcsum : N ; c_tsize : N }.
Definition cadd (a b : C) : C :=
  MkC (c_nodes a + c_nodes b) (c_pcsum a + c_pcsum b) (c_tsize a + c_tsize b).

(* p = enclosing path-condition length. assertk AND assumek both extend the
   world (Propositions.v:414, `wsafe`), so both count. *)
Fixpoint ccount {Σ} (p : N) (s : 𝕊 Σ) {struct s} : C :=
  let here := MkC 1 p 0 in
  match s with
  | SymProp.angelic_binary o1 o2 => cadd here (cadd (ccount p o1) (ccount p o2))
  | SymProp.demonic_binary o1 o2 => cadd here (cadd (ccount p o1) (ccount p o2))
  | SymProp.error _              => here
  | SymProp.block                => here
  | SymProp.assertk fml _ k      => cadd (MkC 1 p (fsize fml)) (ccount (p+1) k)
  | SymProp.assumek fml k        => cadd (MkC 1 p (fsize fml)) (ccount (p+1) k)
  | SymProp.angelicv _ k         => cadd here (ccount p k)
  | SymProp.demonicv _ k         => cadd here (ccount p k)
  | @SymProp.assert_vareq _ x σ xIn t _ k => cadd (MkC 1 p (tsize t)) (ccount p k)
  | @SymProp.assume_vareq _ x σ xIn t k   => cadd (MkC 1 p (tsize t)) (ccount p k)
  | SymProp.debug _ k            => cadd here (ccount p k)
  end.
```

Two traps:

- The `*_vareq` constructors carry implicit args; you need the explicit form
  `@SymProp.assert_vareq _ x σ xIn t msg k`, not `assert_vareq x t msg k`.
- **Max-depth cannot be folded through an add-combinator** (it needs
  max-with-child). Use a separate cheap pass and stitch the results.

### Term size, and the guard checker

The obvious `tsize` recursing into `term_tuple`'s `Env` is **rejected by Coq's
guard checker** — `Env` is a separate inductive parameterized by `Term Σ`, not
mutually inductive with it, so the recursive call on a field isn't seen as
structural. (`env.snoc` also needs THREE pattern args, `env.snoc ts' b t`.)

Don't fight it. Treat `term_tuple`/`term_record`/`formula_user` as **leaves**, and
add a second counter for how many such leaves you hit. If that counter is 0, your
measure is exact rather than approximate — which is the whole point, and was true
for every CFGVer arm measured:

```coq
Fixpoint tsize {Σ σ} (t : Term Σ σ) {struct t} : N :=
  match t with
  | term_binop _ t1 t2 => 1 + tsize t1 + tsize t2
  | term_unop _ t1     => 1 + tsize t1
  | term_union _ _ t1  => 1 + tsize t1
  | term_tuple _       => 1        (* leaf; counted by tnest *)
  | term_record _ _    => 1        (* leaf; counted by tnest *)
  | _                  => 1
  end.
```

## 5. Measuring inside the executor

When the answer isn't in the tree, instrument the executor. `SHeapSpec` hands you
the heap directly:

```coq
Definition SHeapSpec (A : TYPE) : TYPE := □(A -> SHeap -> 𝕊) -> SHeap -> 𝕊.
```

so a probe combinator can read it (`SHeap Σ = list (Chunk Σ)`,
`PathCondition Σ = Ctx (Formula Σ)` for `wco w`). Emit *k* `SymProp.debug` nodes
to smuggle a number out: `nc_debug` is **0** in the uninstrumented executor, so
it is a clean channel, and every other counter stays available as the control.

```coq
Definition zz_dbg_msg {w : World} : AMessage w :=
  amsg.mk {| debug_string_pathcondition := wco w;
             debug_string_message := "zz-probe" |}.

Fixpoint zz_debugs {w : World} (n : nat) (p : 𝕊 w) {struct n} : 𝕊 w :=
  match n with O => p | S n' => SymProp.debug zz_dbg_msg (zz_debugs n' p) end.

Definition zz_measure {w : World} (h : SHeap w) : nat := List.length h.

Definition zz_probe {A} : ⊢ SHeapSpec A -> SHeapSpec A :=
  fun w m Φ h => zz_debugs (zz_measure h) (m Φ h).
```

Then wrap the step in `sexec_cfg_addr`:

```coq
⟨ θ1 ⟩ apc' <- zz_probe (sexec_instruction i apc anp wd) ;;
```

The census now reports **Σ over steps** of the measure. To measure a subset,
filter — e.g. only duplicable `encodes_instr` chunks:

```coq
List.length (List.filter (fun c => match c with
                                   | chunk_user encodes_instr _ => true
                                   | _ => false end) h)
```

Turning the same combinator into a *causal* test is a one-line change — pass a
filtered heap onward instead of counting it:

```coq
fun w m Φ h => m Φ (zz_gc h)
```

**Rebuild cost:** this touches `Verifier.v`, so rebuild the light chain
(`make -f Makefile.coq case_study/RiscvPmp/CFGVer/Example/Prelude.vo`, then the
probe files). `VerifierRel.v` is NOT needed for probes — it's on the heavy branch
— which is what makes this affordable. Revert with
`git checkout case_study/RiscvPmp/CFGVer/Verifier.v` **and rebuild**, or the
`.vo`s stay instrumented.

## 6. Analysing: fit, and hold a point out

Ratios per doubling are not enough — an exponent that rises with N is exactly
what a quadratic with a small coefficient looks like, and quoting one doubling is
how three separate wrong conclusions got recorded in this project. Fit
`a + b·N + c·N²` on three points and **check it against a fourth you did not
use**:

```python
# exact rational solve on N=1,2,8; verify at N=4
import fractions as F
M=[[1,1,1,F.Fraction(y1)],[1,2,4,F.Fraction(y2)],[1,8,64,F.Fraction(y8)]]
# ... gaussian elimination ...
# then: assert abs(a+4*b+16*c - y4)/y4 < 1e-3
```

A held-out point agreeing to 0.001% is what licenses calling something "exactly
quadratic". `numpy` is not installed here; plain `fractions` is exact and fine.

Useful derived quantities: `b/c` is the **crossover N** where the quadratic
overtakes the linear term (24.6 in the CFGVer case — which is precisely why the
measured exponent kept rising and why series stopping at N=8 misled).

## 6b. Three things that were MEASURED on 2026-08-19 — use the numbers

These were priced deliberately, because each had previously been stated as a
qualitative caution and each had been under-weighted as a result.

**(a) The tactic protocol is worth 1.81×, and it is ENTIRELY the `Qed`.** Same
contract (`loop1_cfg_contract_param 16`), only the `Proof.` script varying,
baseline-subtracted:

| script | allocated words | |
|---|---|---|
| `intros; vm_compute; solve_vc; solve_symbase_fetch.` **`Qed.`** | 548,225,615 | |
| same tactics, **`Admitted.`** | 302,956,516 | |
| `intros. vm_compute. solve_vc.` **`Admitted.`** | 302,967,712 | |

- `Qed` alone: **1.8096×** — it re-runs the whole executor through the VM cast.
- `solve_symbase_fetch` **plus** the period-vs-semicolon goal-selection
  difference: **0.99996×**, i.e. free to four decimals.

So the usual phrasing of this rule — "a real `Qed` re-runs the executor *and*
`solve_symbase_fetch` is extra work" — bundles a 1.81× factor with a 0.004% one.
Only the `Qed` matters. **1.81× is larger than most genuine findings** (the
byte-classing win at 8 declared cells is 1.77×), so a protocol mismatch can
fully impersonate the biggest real effect in a study. That is the concrete reason
to treat it as a landmine and not a style note.

**(b) `allocated_words` is deterministic to 0.0008%.** Same probe run twice:
1,155,336,724 vs 1,155,345,950 — 9,226 words apart. Consequences worth drawing:
one run per point genuinely suffices, and a 1.06× ratio sits ~7,500× above the
noise floor. **It also means a wrong cost number is essentially never noise** —
it is a comparison-design error (wrong baseline, wrong denominator, wrong
protocol). Reach for a checklist, not more repetitions.

**(c) A stale imports baseline COMPRESSES ratios**, by 3.7% at N=8 and 4.5% at
N=32 in the measured case (true 1.097×/1.765× read as 1.057×/1.686× when a
baseline 28% too small was used). Direction matters: baseline error biases toward
*under*-claiming a gain, while a protocol mismatch inflates. Both directions are
available, so neither can be waved off as conservative.

## 7. Checklist / traps

- **Gate on `Finished transaction`.** A probe that fails to compile reports the
  *baseline* allocation, which reads as "this variant is free". This actually
  happened twice.
- **RE-MEASURE the imports-only baseline for the commit you are measuring on.**
  It is example-independent — three sibling `Common` chains measured within 313
  words (0.00005%) of each other — but it is **not stable across commits**: it
  moved 434,833,198 → 604,283,692 (**+39%**) over ~6 days of unrelated landings.
  A record that says "same figure re-used, deterministic" is telling you the
  first fact and not the second. Cost: see 6b(c).
- **Subtract an imports-only baseline.**
- **ONE heavy `Eval` per process.**
- **`rocq_compile_file` deletes `.vo` by default.** Running it on a committed
  file without `keep_vo=True` removes that file's build artifact — it silently
  deleted `Verifier.vo` out of the real build tree mid-session. Always
  `keep_vo=True` on anything real, and on any probe a sibling will `Require`.
- **Census every counter as a control**, not just the one you expect to move. An
  intervention that changes others has changed the tree, not just its cost.
- **Prefer additive interventions.** A postcondition is only ever *produced*, so
  adding to it adds assumes and cannot truncate a path into an `error` leaf;
  removals can, and a truncated path reads as a speedup.
- **`Time (all: tac)` is a syntax error** — `all:` is a sentence-level selector.
  Time `(t1; t2)` jointly.
- **`all: idtac "x"` prints once regardless of goal count**, including at zero
  goals. To count goals: `all: (let n := numgoals in idtac "count:" n)`.
- **A `tail`-terminated pipeline reports `tail`'s exit code, not the build's.**
  `make ... | grep ... | tail` returned 0 for a `make` that exited 2, and the
  failure was reported as a success. Use `set -o pipefail`, or capture to a log
  and check `$?` before filtering. Corollary: piping a long build through `tail`
  also destroys interim visibility, since the pipe buffers until it closes —
  redirect to a file and `tail` the file separately.
- **`strings X.vo | grep -x name` reports nothing for names that ARE present.**
  `-x` demands a whole-line match and `.vo` strings embed names in longer blobs.
  This produced "absent" for two lemmas that certainly existed, on top of reading
  a `.vo` that the failed build had left stale. Drop `-x`, and check the artifact's
  mtime before believing either answer.
- **`keep_vo=True` is a NO-OP in a dune project.** The artifact goes to
  `_build/default`, never the source tree, and the tool says so only in a
  `dune_build_warning` field. So after changing any file, every *downstream* file
  stays unbuildable by `rocq_compile_file` until a real `make` has run — it fails
  with "makes inconsistent assumptions over library", which reads like a genuine
  inconsistency and is not. **`make` is the authority for anything a sibling will
  `Require`**, not just for the one heavy file.
