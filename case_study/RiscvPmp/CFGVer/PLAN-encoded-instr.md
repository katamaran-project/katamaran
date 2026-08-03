# PLAN — remove `encoded_instr`, the last per-step logical variable

Status: **DONE 2026-08-01** (gate green, axiom-clean) — §7-RESULTS has the
outcome, **§8-FOLLOWUP corrects its scaling claim and supersedes it**. Branch
`nextpc-param`. Sequel to `PLAN-nextpc-param.md`, which removed `an` the same
way.

The change did what it set out to do — execution-driven `|wctx|` growth is zero,
survivors +15/trip → +1/trip — but §8 shows that was **not** the binding
constraint on end-to-end cost: measured with a real `Qed`, the exponent is 1.48
at N=8→16 and rising, the growth lives in `vm_compute` and `Qed` rather than in
the solver, and a concrete base does not flatten it either. Read §8 before
quoting any timing from §7.

> **§9 measures the cost law and §10 ROOT-CAUSES it. Read §10 first.** The
> quadratic is a LEAKED HEAP CHUNK: `encodes_instr` is duplicable, so
> `heap_extractions` never removes it and the symbolic heap grows by exactly one
> chunk per instruction step. Filtering it collapses the quadratic coefficient to
> −0.043% of itself with a byte-identical census. **Note the name collision that
> hid this for three sessions: the `encoded_instr` VARIABLE that this plan removed
> and the `encodes_instr` CHUNK that leaks are different objects.** A sound
> chunk-GC may already exist at tag `archive/gc-attempt-2026-07`.

## §0. Why this is worth doing, and what "done" looks like

Measured on the flat `zzn` reproducer (`PLAN-nextpc-param.md` §5-RESULTS, probe
`Example/ZZSurv.v`): after the `an` fix, the surviving demonic variables are

| N | survivors | composition |
|---|---|---|
| 1 | 20 | `p`, `np`, `v`, `v.1`, `v.2`, `mv` + **`encoded_instr` ×14** |
| 2 | 35 | those + `mv.1` + **`encoded_instr` ×28** |

`encoded_instr` is exactly **one per instruction step** and is the **only**
execution-driven survivor. Everything else is either a fixed constant or (`mv`)
declared by the contract's own spec list. So this is not another halving:
**removing it takes execution-driven `|wctx|` growth to zero**, which is the one
thing that could change the exponent rather than the constant. The `an` fix
bought ~1.5-1.6× with the exponent unchanged (4^1.90 vs 4^1.95); that is the
baseline this must beat, and the success criterion is a **flat** survivor slope,
not a smaller one.

**Gate:** `ZZSurv.v` reports a survivor count that does NOT grow with N except
for reproducer-declared `mv`. Then time at N=4/8, then the full gate.

## §1. Why the obvious fixes are dead (all checked — do not re-propose)

- **Orient the solver's unification the other way.** Not a fix. `result_fetch`
  (angelic) and `encoded_instr` (demonic) are joined by ONE equation
  (`result_fetch = term_union KF_Base encoded_instr`), so exactly one of the
  pair survives per step whichever way you unify. It is a rename.
- **Give the encoding a function symbol** (`encode : AST -> word`). Impossible:
  `Machine.v:147` is `Axiom pure_decode : bv 32 -> string + AST`, uninterpreted,
  so there is nothing to compute with and no injectivity to exploit. Also
  unnecessary — see §2.
- **Make `encodes_instr` non-duplicable** (`Sig.v:333`). Heap-side, so it cannot
  help: the variable stays DECLARED in `wctx` whether or not its chunk is in the
  heap, and heap size is measured at 0.95× (not a driver). Independently, it
  breaks `valid_execute_fetch` (`Spec.v:765`) because inside `fun_fetch`
  (`Machine.v:872-883`) one chunk must serve BOTH `close_ptsto_instr`'s consume
  and fetch's postcondition export — fixable only by re-producing it there.
  Note also that `encodes_instr`'s interpretation is a PURE proposition
  (`⌜pure_decode code = inr instr⌝`, `IrisInstance.v:295`), so duplicable is the
  semantically honest marking.
- **A world-GC that collects it.** Unfixable, see `PLAN-nextpc-param.md` §0.

## §2. The idea, and the evidence it is the right one

**Why `encoded_instr` survives while the other per-step variables do not.**

> **CORRECTED 2026-07-31.** An earlier draft of this section claimed the
> per-step `op` came from `lemma_open_ptsto_instr`'s `∃ "op"` and died because
> `lemma_close_ptsto_instr` supplies `cl` as a lemma pattern argument
> (`Spec.v:653`). **That was wrong.** `fetch` has a CONTRACT
> (`SepContractFun fetch`, registered `Spec.v:517`), so the CFG executor uses
> the contract and never the body; `open_ptsto_instr`/`close_ptsto_instr` are
> invoked only inside `fun_fetch` (`Machine.v:875/880`), i.e. in
> `valid_execute_fetch`, never once per step. The per-step `op` in the census is
> the ITYPE **operation field**, a pattern variable from matching the decoded
> AST.

The real asymmetry: `result_decode`, `imm`, `rs1`, `rd`, `op` all die because the
**AST is a literal**. The prologue owns `chunk_user ptstoinstr [a; term_val ty_ast i]`
with `i` a literal, `decode`'s postcondition pins `result_decode = instr`, and
matching a literal AST resolves its fields to literal components — so each is
unified away.

`encoded_instr` has no literal available, and by §4-SPIKE fact 1 it can never
acquire one: the word is not determined by the instruction. That is precisely why
it must be supplied as a variable from outside, per address, at contract entry.

So give it a supplier. Concretely, move the word from fetch's **postcondition**
to its **precondition**:

```coq
(* Spec.v:311, sep_contract_fetch_instr — sketch *)
sep_contract_logic_variables := [… ; "w" :: ty_word];
sep_contract_precondition    := … ∗ ptstomem a w ∗ encodes_instr(w, i) ∗ …;
sep_contract_postcondition   := … ∗ result_fetch = term_union KF_Base (term_var "w") ∗ …;
```

No existential, so no demonic variable. `w` is determined by the precondition,
hence instantiated **angelically** at the call — and the census shows angelic
variables are eliminated without exception (`nc_angelicv` = `nc_asserteq` at
every N, before and after the `an` fix).

**The part that makes it flat rather than merely smaller.** The `w` for each
instruction address is introduced **once, at contract entry** — one per
instruction in the program, not one per execution step. A loop re-executing the
same 14 addresses reuses the same 14 variables on every trip, so `|wctx|` grows
with PROGRAM SIZE and stops growing with TRIP COUNT. This is the same move as
the `an` fix (replace an `∃` by a parameter supplied from outside); the only new
ingredient is that the supplier is a per-address table rather than a threaded
scalar.

`sexec_cfg_addr` already threads a **term-keyed table** from pc-term to `AST`
(`SInstrTable`), so it can carry pc-term → word-term by the same mechanism.

## §3-CHOSEN. Thread the word through `ptstoinstr` — decided 2026-07-31

Chosen over two alternatives on the user's instruction to keep as much existing
structure as possible. **`fun_fetch`'s body and BOTH lemma invocations stay
exactly as they are**; only the predicate's shape changes.

    ptstoinstr : [ty_xlenbits; ty_ast]  ->  [ty_xlenbits; ty_word; ty_ast]

- `Sig.v:317` arg list; `:356` precision becomes
  `MkPrecise [ty_xlenbits] [ty_word; ty_ast]` — consuming the chunk FROM THE
  ADDRESS determines both the word and the AST, which is exactly why
  `use lemma open_ptsto_instr [tmp]` still works with its single argument.
  `:335` duplicability stays `false` (it is exclusive memory ownership).
- `IrisInstance.v:248` / `IrisInstanceBinary.v:187`: `interp_ptsto_instr` gains
  the word and **loses its `∃ v`**. That loss IS the word-parameterized
  `ptsto_instrs` of §4-SPIKE, hence a restatement, not a weakening.
- `open_ptsto_instr` (`Spec.v:644`): pre `ptstoinstr paddr w i`, post
  `ptstomem paddr w ∗ encodes_instr(w,i) ∗ secLeak w` — **mentions the word, no
  `∃`**. `close_ptsto_instr` (`:653`): post `ptstoinstr paddr cl i`; its `Lem`
  signature ALREADY carries the word (`Machine.v:257`) and `fun_fetch` already
  passes `exp_var "result"` for it (`Machine.v:880`).
- `sep_contract_fetch_instr` (`Spec.v:271`): pre takes `ptstoinstr a w i` with
  `w` a logic variable; post becomes `result_fetch = KF_Base w` — **no `∃`, so no
  per-step demonic variable.** Open gives `ptstomem a w`, the read returns
  exactly `w`, close restores.
- `exec_instruction_prologue` (`Verifier.v:126`): owns `ptstoinstr a w i`, with
  `w` supplied from the word table.
  > **REVERSED 2026-08-01.** This bullet originally read "supplied from the
  > PARALLEL word table (decided: parallel, not an extended `SInstrTable`, to
  > leave `itable_rel` and `TablesRel.v`'s faith lemmas alone)". Both shapes were
  > implemented; the parallel one was dropped. Its stated benefit did not
  > materialise — `itable_rel` and the faith lemmas end up untouched EITHER way,
  > because the word column lives on `SInstrTableW` (the executor's type), not on
  > the Σ-level `SInstrTable` the faith lemmas talk about. Meanwhile parallel
  > cost a second lookup per step that could disagree with the first, an
  > unreachable-but-carried error case in `sexec_cfg_addr`, and a full duplicate
  > `wtable_rel` family (persist / forgetting / lookup / faith) threaded through
  > the fuel induction. Fused: one lookup, one loop-carried relation. See
  > §7-RESULTS.

Rejected alternatives, for the record: (a) removing the open/close pair from
`fun_fetch` and giving fetch the pre-opened form — sound (`st_lemmak`,
`SmallStep/Step.v:101`, proves `use lemma` is operationally a no-op) but changes
the shared ISA model; (b) adding a NEW word-carrying predicate alongside
`ptstoinstr` — no program change, but a new constructor in the shared
`PredicateKit` with exhaustive matches in both Iris instance files. Changing the
existing predicate's shape is smaller than either.

Note `ty_word` and `ty_xlenbits` are both `4 * 8` and already interoperate in
this code (`close_ptsto_instr` uses `ty_xlenbits`, `encodes_instr` uses
`ty_word`), so the mixed usage is a non-issue.

**Scope: 52 sites in 8 built files** — `Adequacy.v` 19, `VerifierRel.v` 11,
`EndToEnd.v` 5, `Sig.v` 4, `Verifier.v` 4, `Spec.v` 4, `IrisInstanceBinary.v` 3,
`IrisInstance.v` 2. Not built, so unaffected in practice but noted: BlockVer,
BinaryBlockVer, FemtoKernel, test/ (`_CoqProject` lines 53-55/89 and its note at
line 16 — re-enable and fix if ever revived).

**Tactic:** `Sig.v` is near the bottom of the chain, so a `full` compile per
iteration costs ~15 min at `-j1` here. An arity change breaks STATEMENTS, so
drive the sweep with `mode="vos"` (statements only, no proof bodies) and pay
`full` only once the shapes settle.

## §3. Sketch of the changes (superseded by §3-CHOSEN)

1. **`Spec.v` — `sep_contract_fetch_instr`** (`:311`): as §2. The `encodes_instr`
   chunk moves from post to pre; `∃ "encoded_instr"` disappears.
2. **`Spec.v` — the open/close lemma pair** (`:644`, `:653`): the CFG verifier
   will hold `ptstomem`+`encodes_instr` directly rather than `ptstoinstr`, so
   check whether `open_ptsto_instr` is still needed on this path at all, or
   whether the prologue should simply carry the opened form.
3. **`Verifier.v` — `exec_instruction_prologue`** (`:126`): carry the word for
   the current pc, as a third parameter alongside `"a"` and `"np"`.
4. **`Verifier.v` — a word table.** Either extend `SInstrTable` to
   `list (Term _ ty_xlenbits * AST * Term _ ty_word)` or add a parallel
   `SWordTable`. Extending the existing one keeps `lookup_instr` as the single
   dispatch point; a parallel table keeps `itable_rel` untouched. **Decision
   needed — see §5.**
5. **`Verifier.v` — `sexec_triple_addr`**: introduce the per-address word
   variables once, via `demonic_ctx`, and build the table from them.
6. **`VerifierRel.v`**: mirror in `cexec_*`; extend `rexec_instruction` and
   `rexec_cfg_addr` with the extra argument; a word-table analogue of
   `itable_rel`/`etable_rel` plus its `_forget` transport lemmas.
7. **`TablesRel.v`**: the faithfulness lemma for the word table.
8. **`Adequacy.v` / `VerifierRel.v` soundness**: `ptsto_instrs` currently owns
   `interp_ptsto_instr a i` per address; it must additionally (or instead)
   expose `ptstomem a w ∗ encodes_instr(w, i)`. This is where the real Iris work
   is — see §4.
9. **`GenContract.v`**: declare the per-address word variables in the generated
   contract.

## §4-SPIKE. RESULT 2026-07-31: the cheap variant is IMPOSSIBLE, and the
## trusted-surface change is a RESTATEMENT, not a weakening

Two source facts, and they settle both questions without writing any code.

**1. `encodes_instr(w, i)` can never pin `w`.** `pure_decode` is an uninterpreted
`Axiom` (`Machine.v:147`) and there is NO injectivity lemma anywhere in the tree.
So from `encodes_instr(op, i)` and `encodes_instr(w, i)` you get
`pure_decode op = inr i = pure_decode w` and **not** `op = w`. Any scheme that
tries to identify the fetched word from the known instruction dies here — this
is why dead end 3 in the memory note is far more far-reaching than "no encoder".

**2. The word is existentially hidden inside the resource itself.**
`interp_ptsto_instr` (`IrisInstance.v:248`) is
`∃ v, @interp_ptstomem 4 addr v ∗ ⌜pure_decode v = inr instr⌝`. `ptsto_instrs` is
a `big_sepM` of exactly that. So the verifier genuinely does not know the word;
it learns a FRESH unknown one on every fetch, because the resource only ever
promised "SOME word that decodes to `i`". **The per-step existential is not a
contract-style accident — it mirrors the `∃` in the resource.**

Hence the §4 "cheaper variant" below is struck: there is nothing to unify the
table's word against while `ptsto_instrs` keeps that `∃`. Owning the word per
address is FORCED, not a design preference.

**But it costs no generality, and need not change the end theorems at all.**
Since

    interp_ptsto_instr a i  ⊣⊢  ∃ v, ptstomem a v ∗ ⌜pure_decode v = inr i⌝

we have `ptsto_instrs instrs ⊣⊢ ∃ words, ptsto_instrs_w words instrs`. So a
word-PARAMETERIZED end theorem (∀ words, memory holds them ∧ they decode to the
program → noninterferent) **implies** the current one: destruct the `∃` and
apply. This is the same `∀`-parameter ≡ `∃` argument that justified the nextpc
fix, one level up.

**Consequence for the plan:** keep every existing `*_noninterferent` statement
byte-identical and derive it as a corollary of a word-parameterized lemma. The
trusted statement surface does NOT change; only an internal lemma is added.
That retires §5 decision 1 — the answer is "no trusted-surface change needed".

## §4. The risk, stated plainly — SUPERSEDED by §4-SPIKE above

The Iris side is the part I cannot predict. Today `ptsto_instrs` (`VerifierRel.v`)
is a `big_sepM` of `interp_ptsto_instr`, and `ptsto_instrs_lookup` extracts one
entry with a framing wand. The new shape needs each entry to yield
`ptstomem a w ∗ encodes_instr(w, i)` for the *specific* `w` the contract
declared for that address — i.e. the ghost state must pin a chosen word per
address, and `create_resources`/`ImplPre` must establish it.

That is a genuine change to the **trusted statement surface**, unlike the `an`
fix, which needed none. `ImplPre` would have to say "the instruction memory
holds these words" rather than "holds these instructions". Whether that is
acceptable is a judgement call, and it should be made **before** any code is
written, because it is the difference between a mechanical port and a redesign
of what the end theorems assume.

A cheaper variant worth pricing first: keep `ptsto_instrs` as-is and have the
prologue open it per step (as now), but arrange for the opened word to be
unified against the table's `w` — recovering `op`'s mechanism (a supplied term)
without changing what `ImplPre` asserts. If that works it is strictly better; I
do not yet know whether the unification lands.

## §5. Decisions to take before starting

1. **Trusted surface:** is changing `ImplPre` to name instruction *words* rather
   than instructions acceptable? If not, only the §4 cheaper variant is on the
   table, and it may not work.
2. **Table shape:** extend `SInstrTable` (one dispatch point, touches
   `itable_rel` and every faith lemma) or add a parallel word table (more
   plumbing, less churn in existing proofs)?
3. **Scope of the first commit:** the §4 cheaper variant as a spike — cheap to
   try, and its outcome decides question 1 — or straight to the full change?

Recommendation: **spike §4's cheaper variant first**, measure with `ZZSurv.v`,
and only then decide 1 and 2. It is the only step that can retire the biggest
unknown without committing to a trusted-surface change.

## §6. Methodology notes (carried forward, cost real time to learn)

- `Example/ZZSurv.v` is the instrument: it computes the survivor multiset
  directly. Run it at N=1 and N=2 and compare *composition*, not just counts.
- Fresh-name suffixes (`.1`, `.2`, …) mark exactly the un-eliminated variables —
  a survivor must be alpha-renamed when the next step reintroduces its base
  name. Reading the name list is often faster than any counter.
- **ONE heavy `Eval` per `coqc` process** (`ZZCommon.v`'s header): several in one
  process contaminate each other badly.
- The ZZ probes are **not in `_CoqProject`**, so `make` has no rule for them —
  use `rocq_compile_file`, which resolves via the `-Q`/`-R` mappings.
- `rocq_start` on `VerifierRel.v` OOMs pet (peak ~5 GB against a 7.6 GB cap).
  Use preamble mode for shape failures, or a `Show.`+`admit`+`Admitted` goal
  dump for context — see the `rocq-implementation` skill §1.
- Timing comparisons on this box are weak evidence: the recorded spread on
  identical code is 1.31× at N=4. Prefer the deterministic census.
- Bound `-j` by RAM (~6 GB/job); `GATE_JOBS=1` when a browser is open, per
  `scripts/gate.sh`'s own comment. `Error 143` is earlyoom, not a code defect.

---

## §7-RESULTS. DONE 2026-08-01 — the curve bends, gate GREEN

**Gate:** `✓ GATE PASSED — build clean, no holes, 12 end theorems axiom-clean
(only: Machine.pure_decode Base.mmioenv).` Same axiom set as the pre-change
baseline at `30c9517a` / `05a4ba00`, so the word threading added nothing.

### The decisive datum: execution-driven `|wctx|` growth is ZERO

`Example/ZZSurv.v`, same flat `zzn` reproducer as §0:

| N | survivors BEFORE | survivors AFTER |
|---|---|---|
| 1 | 20 — `p, np, v, v.1, v.2, mv` + **`encoded_instr` ×14** | 20 — `p`, **`w`…`w.13`**, `np, v, v.1, v.2, mv` |
| 2 | 35 — those + `mv.1` + **`encoded_instr` ×28** | **21** — those + `mv.1` |
| 4 | (would be 65) | **23** |
| 8 | (would be 125) | **27** |

Growth per trip: **+15 → +1**, and that +1 is `mv`, which this reproducer's own
`zzn_mem_specs n` declares. That is exactly §0's success criterion. The 14
survivors that remain are the program's 14 word variables — bound to PROGRAM
SIZE, not trip count, which is the whole point of introducing them once at
contract entry.

`encoded_instr` no longer appears in the demonicv census at all.

### Timing: a real exponent change, unlike the `an` fix

> **SCOPE-CORRECTED 2026-08-01 — read §8 before quoting any number below.**
> Every figure in this subsection is `zzn_raw_nc`, i.e. VC **construction plus a
> node census**. It does NOT include `solve_vc`, `solve_symbase_fetch`, or `Qed`.
> Measured end-to-end on the SAME reproducer with a real `Qed`, the exponent at
> N=8→16 is **1.48**, not 1.05, and it is RISING. The survivor result below
> stands and is re-confirmed; the claim that it "bends the curve" of end-to-end
> verification cost does not. §8 has the stage breakdown and the actual driver.

| N | before (s) | after (s) |
|---|---|---|
| 1 | 0.736 | 1.003 |
| 2 | 3.754 | 3.644 |
| 4 | 10.197 | 7.568 |
| 8 | — | 14.146 |

Exponent per doubling on the SAME range (N=2→4): **1.44 → 1.05**. At N=4→8 it is
**0.90**. Compare `PLAN-nextpc-param.md` §5-RESULTS, which had to report "the
curve does not bend because `|wctx|` still grows linearly via `encoded_instr`" —
it now does bend, and for exactly the predicted reason.

N=1 is slightly SLOWER (1.00 vs 0.74): the 14 word variables are introduced even
for a single trip, and there is no reuse to amortise them. Crossover is ~N=2.

**Corroboration that does not depend on wall-clock** (this box's spread on
identical code is 1.31× at N=4, so treat the seconds as weak evidence): node
counts are exactly linear in N (`nc_angbin` 344 / 687 / 1373 / 2745), and time
now tracks them. Previously time grew superlinearly while nodes grew linearly —
that mismatch WAS the anomaly, and it is gone.

### What the change actually was

Three decisions, in the order they were taken:

1. **Fused, not parallel** (user call). The word is a COLUMN of the executor's
   table (`SInstrTableW`), not a parallel address→word table. One lookup, so the
   two can never disagree; and only ONE relation (`itable_relW`) has to survive
   the induction on fuel. The parallel shape needed a duplicate
   `wtable_rel`/persist/forgetting/lookup family alongside `itable_rel`'s.
2. **Words supplied through the EXISTING `demonic_ctx`**, by extending its
   context from `Σ` to `Σ ▻▻ words_ctx (length tbl)` and splitting with
   `env.drop`/`env.take`. The alternative — declaring them in the contract's own
   Σ — would have made `CFGVerifierContract`'s type depend on the program and
   rippled through `gen_contract*`, `concretize_*`, and every example.
   Consequence, verified by compiling them unchanged: **`Contracts.v`,
   `GenContract.v`, `TablesRel.v`, `EndToEnd.v` and all seven examples needed NO
   source changes.** Only `Tables.v` gained definitions (it lost nothing).
3. **Word supply is a TOTAL FUNCTION** `bv xlenbits -> bv word`, not a gmap. A
   partial map carried no information (the word list is exactly as long as the
   instruction list) but forced a "no word here" case into `cexec_cfg_addr`, a
   domain side condition into `ptsto_instrs_w`, and a matching branch into every
   proof below it.

`ptsto_instrs instrs` is now `∃ words, ptsto_instrs_w words instrs`, which keeps
its old MEANING ("some word that decodes to `i` at each address") and hence its
old role in `ImplPre`. **The trusted statement surface did not change**, as
§4-SPIKE predicted and §4 feared it could not.

### The risk in §4 did not materialise

§4 worried that pinning a chosen word per address would force `ImplPre` to name
instruction *words*. It does not: `intro_ptsto_instrs` (`Adequacy.v`) **already
receives the word list `ws`**, so the words are in hand exactly where instruction
ownership is introduced. No gmap-construction induction, no new hypothesis
travelling down from the end theorems. Likewise the word guard is free —
`wtable_rel_cws_of` holds by construction from `itable_rel`, because `cws_of` is
built from `words` at the table's own addresses.

### `valid_execute_fetch` — the obligation no `vos` pass could judge

Verifies unchanged. `Sig.v`'s precision annotation
`MkPrecise [ty_xlenbits] [ty_word; ty_ast]` means consuming the chunk FROM THE
ADDRESS determines both the word and the AST, so `use lemma open_ptsto_instr
[tmp]` still resolves with its single argument and **`Machine.v` is untouched**.

### Methodology: exactly when `-vos` checks a proof

**`-vos` skips a proof body UNLESS the enclosing section has section VARIABLES
whose usage must be read off the proof term** (no `Proof using` annotation). A
bare `Section` is NOT enough — it needs `Context`/`Variable`. Verified both ways
on scratch files: an unsectioned false lemma compiles under `-vos` (exit 0); the
same lemma inside `Section S. Context (X : Type).` fails.

Concretely in this tree — worth knowing before trusting any `vos` sweep here:

| where | section variables? | `vos` checks proofs? |
|---|---|---|
| `VerifierRel.v` `Section Soundness` | `Context {Σ} {GS}` | **yes** |
| `VerifierRel.v` `Section Shallow` / `Section Relational` | none | **no** |
| `Adequacy.v` | `Context {Σ} {GS}` | **yes** |
| `Tables.v` (file top level) | n/a | **no** |
| `Spec.v` / `SpecIris.v` (plain `Module`) | n/a | **no** |

An earlier note in this session over-claimed that the sweeps validated
`rexec_cfg_addr` — they did not; it lives in `Section Relational`. ALL FIVE
proof errors that survived to `full` mode were in the "no" rows:

- `Tables.v`'s two new `bv.eqb` lemmas. A bare `cbn` unfolds `bv.eqb` into
  `N.eqb (bv.bin _) (bv.bin _)` so the rewrite stops matching (use
  `cbn [words_of_list]`), and `destruct (bv.eqb_spec …)` will NOT abstract a
  closed scrutinee sitting inside an `if` — decide the boolean first.
- `SpecIris.v`'s `open`/`close_ptsto_instr_sound`: `interp_ptsto_instr` no longer
  hides the word behind an `∃`, so the destructuring intro pattern and the
  matching `iExists` both had to go.
- `itable_relW_zip`'s `->` intro pattern for the word conjunct: the preceding
  `subst` already eliminates `cx` via `Hx`, so the equation arrives in exactly
  the form the goal wants and a rewrite finds nothing to act on.
- `words_of_env_take_inst`: `rewrite <- inst_env_take` does not fire even fully
  instantiated — `inst`'s resolved instance arguments differ from the goal's,
  although the goal contains the term textually. An explicit `assert` + `rewrite`
  works. Note `replace X with Y by (symmetry; apply …)` ALSO fails: with
  SSReflect loaded the `by` clause does not run `symmetry` before `apply`.

Two further tactic traps found while the sweeps were still useful: `congruence`
chokes on `bv`'s proof field (go through `discriminate`), and SSReflect rejects
the comma form `rewrite H1, H2 in H`.

And one design lesson: prefer an **Iris-level wrapper lemma** (`itable_relW_zip_pred`)
over `iStopProof` at a call site. `iStopProof` folds the WHOLE persistent context
into a single conjunction, so its intro pattern breaks whenever an unrelated
hypothesis is introduced earlier in the proof.

## §8-FOLLOWUP. What the §7 numbers do and do not show — 2026-08-01

Prompted by the question "does `zzn` work at N=64?". It does not, but not for a
code reason; and answering it properly invalidated §7's headline scaling claim.

### The error is the N RANGE, not the measurement scope

> **This subsection was itself rewritten once.** A first version blamed §7's
> figure on measuring only VC CONSTRUCTION (`zzn_raw_nc`) and excluding
> `solve_vc`/`solve_symbase_fetch`/`Qed`. **That diagnosis is wrong** and is kept
> here only so nobody re-derives it. The stages agree to within noise:
>
> | N | raw census (§7's metric) | postprocess census | `vm_compute` on the real goal |
> |---|---|---|---|
> | 1 | 1.003 | 1.009 | 1.01 |
> | 8 | 14.146 | 14.291 | 14.28 |
> | 16 | — | 40.985 | 39.77 |
>
> `postprocess` is FREE (re-confirming the 2026-07-29 finding), and `Qed ≈
> vm_compute` (next subsection). So the raw census is a perfectly good proxy for
> the RATIO, and §7 was not measuring the wrong thing.

§7 was measuring the right thing over **too short an N range**, and quoted the
two most favourable windows. The exponent per doubling is not constant:

| window | 1→2 | 2→4 | 4→8 | **8→16** |
|---|---|---|---|---|
| exponent | 1.86 | **1.05** | **0.90** | **1.52** |

§7 quoted the middle two and concluded "the curve bends". End to end with a real
`Qed`, the same series reads:

| N | wall (s) | net of ~5.8 s imports | ratio | exponent |
|---|---|---|---|---|
| 1 | 14.60 | 8.8 | — | — |
| 2 | 17.39 | 11.6 | 1.32 | 0.40 |
| 4 | 21.49 | 15.7 | 1.35 | 0.43 |
| 8 | 36.99 | 31.2 | 1.99 | 0.99 |
| 16 | 92.42 | 86.6 | **2.78** | **1.48** |

The low-N ratios are constant-dominated; **1.48 is the only trustworthy figure,
and the exponent is RISING.** So the `encoded_instr` fix did not flatten
end-to-end cost. **What it did do is exactly what §7 claims for it** — survivor
growth +15/trip → +1/trip, re-confirmed — which means `|wctx|` was simply not the
binding constraint at these trip counts.

**Rule this establishes: never quote an exponent from a single doubling, and
never from a series that stops at N=8.** Both mistakes in this file's history
(and the world-GC's, below) come from exactly that.

### Why the world-GC "worked" and this "didn't" — it didn't either

The obvious objection: the archived world-GC (`PLAN-unquantify-forward.md`,
tag `archive/gc-attempt-2026-07`) removed the same per-step variables and was
reported at **10.7× with the speedup GROWING in N** (2.24× at N=1 → 10.67× at
N=8). Fixing them at source instead gives no slope change. Same intervention,
opposite verdict — so one of the two verdicts is an artifact.

It is the GC's. Put all three arms on the same footing (all `Eval vm_compute` on
the census, same reproducer):

| N | GC-era baseline | world+chunk GC | both source fixes |
|---|---|---|---|
| 1 | 1.030 | 0.459 | 1.003 |
| 2 | 6.571 | 0.884 | 3.644 |
| 4 | 16.279 | 3.327 | 7.568 |
| 8 | 81.454 | 7.632 | 14.146 |
| **exponent N=1→8** | **2.10** | **1.35** | **1.27** |

**The GC arm's own slope is ~1.35; the source fixes' is ~1.27.** Both take a
~2.10 baseline down to ~1.3. They had the SAME effect on the exponent, which is
what the shared mechanism predicts. The GC's "speedup grows with N" headline is a
ratio against a steeply superlinear baseline — the baseline's 2.10 is what grows,
not the GC arm's flatness. §7's "the curve bends" is the identical artifact,
measured a different way, two sessions apart.

Where the GC IS genuinely ahead is the CONSTANT: 7.632 vs 14.146 s at N=8, a
1.85× edge — and shrinking (2.3× at N=4 → 1.85× at N=8), as expected if both
remove the same asymptotic term and the GC additionally collects residue the
source fix leaves live. Two candidates for that residue, neither confirmed: the
14 word variables, introduced once at contract entry but live in EVERY world
thereafter; and `mv`, of which this reproducer's own `zzn_mem_specs n` declares
n, each live until its cell is written.

**Caveats.** The GC arm was never measured past N=8, so it may well rise to ~1.5
at 8→16 as the source fix does — its 1.35 and the source fix's 1.27 are NOT
distinguishable given this box's 1.31× spread on identical code. Only the
~2.10 → ~1.3 shift is real. And the GC is unsound and unprovable (see the memory
note), so it was never an available lever regardless.

### Stage breakdown, and the real driver

Parametric base (`gen_contract_rel`, `term_var "p"`):

| stage | N=1 | N=8 | N=16 | 8→16 exponent |
|---|---|---|---|---|
| `vm_compute` | 1.01 | 14.28 | 39.77 | 1.48 |
| `solve_vc` | 7.90 | 6.42 | 10.50 | **~0.7 (flat)** |
| `solve_symbase_fetch` (all goals) | — | — | <1 s | negligible |
| `Qed` | — | ~10.4* | 35.12 | **1.76** |

\* by subtraction. **`solve_vc` is a fixed toll, not a scaling term.** The growth
is in `vm_compute` and in `Qed`, which is 41% of the N=16 run. No node census or
earlier probe in this investigation measured `Qed` at all.

### `Qed` is not checking a big proof term — it is re-running the executor

The natural reading of "`Qed` is 41% of the run" is that the proof term is huge.
**It is not.** Node census of the POSTPROCESSED tree — the thing `safeE` unfolds
and the kernel checks (`safeE P := VerificationConditionWithErasure
(erase_symprop P)`):

| N=16 | postprocessed tree | `vm_compute` | `Qed` |
|---|---|---|---|
| concrete base | **1 node** (`nc_block := 1`, every other counter 0) | 25.97 s | 21.55 s |
| parametric base | 67 nodes (30 `assertk`, 35 `demonicv`, 2 `assumek`) | 39.77 s | 35.12 s |

With a concrete base the obligation is **empty** — the whole VC collapses to
`block`, there is nothing to prove — and `Qed` still costs 21.55 s. So the cost
cannot be the proof term.

It is the **VM cast**. The `vm_compute` tactic emits a `VMcast` into the proof
term, and the kernel re-executes that same normalization at `Qed`. Hence
`Qed ≈ vm_compute`, which holds across both bases and every N:

| `Qed` / `vm_compute` | N=1 | N=8 | N=16 |
|---|---|---|---|
| concrete | 1.06 | 0.58 | 0.83 |
| parametric | — | 0.73 | 0.88 |

**Consequence: you pay for the symbolic execution TWICE — once in the tactic,
once in the kernel — and essentially nothing for the obligation.** Total ≈
1.7–1.9× `vm_compute`, so `vm_compute` is the only worthwhile target, and any
speedup there carries through to `Qed` proportionally. Conversely, work aimed at
shrinking the FINAL tree (unquantify, post-hoc pruning, fewer residual goals) is
attacking something that already costs ~nothing.

### Concrete vs parametric base

`gen_contract` (literal base, `Σ = [ctx]`, no base-bound precondition) decides
the fetch bounds inside `vm_compute`, so `solve_vc` has nothing to do:

| N | base | `vm_compute` | `solve_vc` | goals left | `Qed` | net |
|---|---|---|---|---|---|---|
| 1 | concrete | 0.49 | **0.00** | **0** | 0.53 | 1.0 |
| 8 | concrete | 9.68 | **0.00** | **0** | 5.64 | 15.3 |
| 16 | concrete | 25.97 | **0.00** | **0** | 21.55 | 47.5 |
| 16 | parametric | 39.77 | 10.50 | 30 | 35.12 | 86.6 |

Concrete is ~1.8× faster at N=16 and 8.9× at N=1 — but its 8→16 exponent is
**1.63**, if anything STEEPER than parametric's 1.48. **The symbolic base is a
shrinking constant-factor penalty, not the scaling driver.** Do not spend effort
on symbolic-base handling expecting a slope change.

### What `solve_vc` leaves behind

All of it is one shape, one per instruction address:

```
0 ≤ 1024 - (4 + unsigned (p ⊕ off))     off ∈ {0x0, 0x4, …, 0x34, 0x38}
```

— the 14 instructions plus the exit address. The `SyncVal p => p | NonSyncVal _ _
=> False` wrapper is just how `formula_relop` prints; it is NOT a secret-data
wall. Counts: **15 / 22 / 30** at N=1/8/16, i.e. **+1 per trip** (each iteration's
store address `p ⊕ (56+4i)` needs its own bound). Linear, and cheap — all 30 cost
under a second. With a concrete base there are none.

### Ceiling on this box

N=16 is the highest rung that completes. N=32 was killed by earlyoom
(`signal 15`, no Coq diagnostic) 100 s into `vm_compute` at 5.80 GB RSS against
4.6 GiB available — a MEMORY limit, not a code result. RSS grows 2.77 / 3.66 /
5.60 GB (param) and 2.78 / 3.35 / 4.84 GB (concrete) at N=1/8/16. N=32 is
plausibly reachable on a quieter box; N=64 was never attempted.

### Measurement traps that produced three wrong answers here

Recorded because each one produced a confident, wrong, reported result:

- **`all: idtac "X"` prints exactly ONCE regardless of the goal count, including
  at ZERO goals.** It is useless as a goal counter — it only says "the tactic
  ran". This produced a fictitious "1 residual goal at every N". The working form
  is `all: (let n := numgoals in idtac "count:" n)`, verified against known
  0/2/3-goal states. A BARE `numgoals` sentence reports **1** whatever the true
  count, because a plain tactic focuses one goal. For dumping, `all: (match goal
  with |- ?G => idtac G end)` does iterate per goal.
- **`solve_vc. solve_symbase_fetch.` is NOT `solve_vc; solve_symbase_fetch`.**
  The period form runs the fetch tactic on the FIRST of 15–30 goals; the gate's
  semicolon form runs it on all. The period form is what made `zzn` look like it
  had a permanent discharge gap and a leftover `NonSyncVal` wall. `zzn`
  discharges fully with a real `Qed` at N=1/2/4/8/16, and its reg/mem specs are
  identical to `key_schedule_loop2`'s.
- **`Time (all: tac)` is a syntax error** — `all:` is a sentence-level selector,
  and an `Ltac` body cannot contain one either. Time `(t1; t2)` together, or take
  the stage cost as a residual against the wall clock.

### Still open: WHAT makes `vm_compute` superlinear

> **ANSWERED 2026-08-01 — see §9.** The cost law is
> `work ≈ (heap size) × (α·S + β·S²)` with `S` the number of instruction steps
> executed. It is an exact quadratic, the crossover is N≈25, and the quadratic
> term is invisible in the tree: every structural counter is *exactly* affine in
> N. The "remaining suspect" below (term size) is **refuted** — measured
> sublinear, `tmax` pinned at 10. Read §9 instead of the paragraph below.

Unanswered, and now the only question that matters. What is ruled OUT:

- **Not the residual bounds goals** — the concrete base has zero of them and the
  steepest `Qed` growth of anything measured.
- **Not the proof term / final tree size** — 1 node at N=16, concrete.
- **Not `postprocess`** — free, to within noise (table at the top of §8).
- **Not `solve_vc`** — flat.
- **Not `|wctx|` growth** — that is what this whole plan removed.
- **Not symbolic-base handling** — concrete is steeper (1.63 vs 1.48).

The remaining suspect is the size of the TERMS the raw tree carries, which no
instrument here can see: every census counts NODES, and `postprocess`'s
`solve_uvars` eliminates variables **by substitution** (`uctx_subst`), re-inlining
each `v = t` definition — which shrinks the node count while EXPANDING the
surviving terms. This is the same mechanism that defeated the SSA-naming attempt
(see the memory note).

A term-size measure was started (`Example/ZZTSize.v`: `tsize`/`fsize`/`sptsize`,
summing every `Term` in a `SymProp`, reported raw-vs-postprocessed as a pair) and
is NOT finished: the mutual fixpoint over `Term` and `Env (Term Σ)` is rejected by
the guard checker, because `Env` is a separate inductive parameterized by
`Term Σ` rather than mutually inductive with it, so the recursive call on a field
is not seen as structural. Two ways out, neither tried: treat `term_tuple`/
`term_record` as leaves and separately count them (exact if the count is zero —
worth checking first, it may well be for `zzn`), or find the idiom `Terms.v`'s own
`Fixpoint`s (`subst`, `peval`, `occurs_check`) use for the same nesting.
Note the pattern arity trap already hit: `env.snoc` needs THREE pattern arguments
(`env.snoc ts' b t`) because `b` is a constructor argument, not a parameter.

### Not measured

`key_schedule_loop2` itself at any N above 2. Everything here is the flat `zzn`
reproducer, whose 10-instruction chain (`addi a0,a1,1` ×10) deliberately keeps
every register term O(1). The k^trip-count TERM-DUPLICATION mechanism — three
copies of A0 per iteration in the real masking chain — is untouched by this work
and remains the expected wall for the real program. Probe files:
`Example/ZZProveRun*.v`, `Example/ZZStg{P,C}*.v`, `Example/ZZQ.v` (concrete-base
twin), `Example/ZZCtl{Ksl,Zzn}.v` (the n=2 ksl-vs-zzn control pair),
`Example/ZZGoalsP1.v` (the goal dump), `Example/ZZSize.v` + `ZZSz{P,C}*.v` (the
postprocessed node census), `Example/ZZTSize.v` (the unfinished term-size
measure).

## §9-DIAGNOSIS. The cost law, measured — 2026-08-01

§8 closed with "what makes `vm_compute` superlinear" open, and named term size as
the last suspect. It is not term size. The answer is a **quadratic in the number
of instruction steps, multiplied by the symbolic heap size**, and none of it is
visible in the tree.

### Method: allocated words, not wall clock

`OCAMLRUNPARAM='v=0x400' coqc …` prints OCaml GC stats at exit. **`allocated_words`
is the metric this investigation should have been using all along:**

- **Deterministic.** Two runs of the same probe differed by 1.1k words in 527M
  (0.0002%). Wall clock on this box differed by **2.3×** between two runs of the
  identical probe set on the same day (B1/B2/B4 = 1.055/3.567/7.107 s in one run,
  0.679/1.527/3.491 s in the next). Every wall-clock exponent in §7 and §8 was
  measured through that noise.
- **Immune to page-cache state and to memory pressure**, which §8's N=16 runs
  (5.6 GB RSS on a 15 GB box) were not.
- Subtract an imports-only baseline probe (same `Require`, no `Eval`); it is
  ~393.3 M words here.

Time tracks allocation closely (ratios 2.25/2.29/2.50 against 2.39/2.29/2.35), so
allocation is a faithful proxy for cost, just a much quieter one.

### The tree is EXACTLY affine; only the work is quadratic

`Example/ZZDiagCommon.v` censuses the RAW tree for what accumulates along a path
(path-condition length, live-context size, term size, depth) rather than nodes
alone. On the fixed-heap reproducer `zzf` at N=1/2/4/8, **every counter fits
`a + b·N` with 0.0000% error**:

| counter | model |
|---|---|
| nodes | 42 + 2126·N |
| path-condition sum | −15311 + 36142·N |
| live-variable sum | 619 + 43902·N |
| term size | 159 + 491·N |
| depth | 41 + 1322·N |

Allocation is the only thing that is not:

    alloc(N) = −38.6M + 165.9M·N + 6.754M·N²      (fit on N=1,2,8)

Held out at N=4 it predicts within **0.001%**. This is a clean quadratic, not a
fitted curve.

**Validated out of range at N=16** (run after freeing memory; the model above
never saw any N>8):

| quantity | predicted | measured | error |
|---|---|---|---|
| net allocated words | 4,345,191,846 | 4,345,812,186 | **−0.014%** |
| nodes | 34058 | 34058 | 0.0000% |
| path-condition sum | 562961 | 562961 | 0.0000% |
| live-variable sum | 703051 | 703051 | 0.0000% |
| term size | 8015 | 8015 | 0.0000% |
| depth | 21193 | 21193 | 0.0000% |

`dc_tmax` is still **10** at N=16, and `dc_nest` still 0. N=16 cost 24.7 s of
`vm_compute` at 3.46 GB RSS with the box quiet — well under §8's 5.6 GB, which
was measured under memory pressure.

It also explains §8's central puzzle — why the exponent *rises* with N. The
quadratic term only overtakes the linear one at **N = 24.6**:

| N | 8 | 16 | 32 | 64 |
|---|---|---|---|---|
| predicted exponent per doubling | 1.23 | 1.34 | 1.49 | 1.65 |

§8 measured 1.48 for wall time at 8→16 against 1.34 here for allocation; the gap
is the memory pressure of its N=16 run, not algorithmics.

### The law: work ≈ (heap size) × (α·S + β·S²), S = instruction steps

Three factorial arms, each fitting a quadratic to <0.005% held-out error:

- **Body length L ∈ {9, 14, 24}** at N=1/2/4/8 (`Example/ZZDiagL.v`). The linear
  coefficient `b` scales as ~L² (b/L = 7.26 / 11.85 / 23.93 M) and the quadratic
  `c` as ~L^2.3 (c/L² = 0.0291 / 0.0345 / 0.0454 M). Both are consistent with
  per-step cost ∝ heap size, since the heap holds ONE `ptstoinstr` chunk per
  instruction, and with steps S = L·N.
- **Heap size at fixed trip count** (`zzm_contract`, 1 trip, k ∈ {1,2,4,8} cells).
  Each extra chunk costs ~10 M words over 14 steps (9.45 / 9.97 / 11.01 per cell,
  i.e. ~0.71 M per chunk per step) while nodes move 2168→2175 and **term size is
  identical at 650**. Per-step cost is linear in heap size.
- **Heap large but CONSTANT while trips grow** (`Example/ZZDiagH.v`, 8 cells).
  Against the 1-cell arm, the linear term scales 1.501× and the quadratic 1.457×
  — the SAME factor, so the crossover barely moves (24.6 → 25.3). The quadratic
  is therefore not a second, independent mechanism: it is the same per-step
  heap work, with a factor that itself grows linearly in steps taken.

Putting it together: **per-step cost ≈ H·(α + β·k)** for heap size H and k steps
already taken, hence total ≈ H·(α·S + β·S²). Leading term at large N is
O(L·(L·N)²).

### That mechanism was tested and is REFUTED — 2026-08-01

The candidate was: the heap is persisted forward at each step through a world
chain whose length grows with steps taken, so each chunk pays O(k).

`sexec_cfg_addr` (`Verifier.v:369`) really does re-persist BOTH tables every step

    sexec_cfg_addr n' (persist_itableW θ1 tbl) (persist_etable θ1 exits) ...

and `is_exit` `peval`-compares the pc against every exit entry every step. So the
**exit table is a per-step cost knob that changes no steps, no heap, no
instruction table and no tree** — the ideal single-variable test
(`Example/ZZDiagE.v`, 24 extra exit offsets at 100..192, none of which can ever
match a pc). Control: the census is byte-identical to the 0-extra arm at N=1/2/4/8.

| | per entry/chunk per step | total, ratio per doubling |
|---|---|---|
| 24 extra EXIT entries | 2401 / 2339 / 2304 / **2288** — flat, slightly falling | 1.948 / 1.970 / **1.986** — exactly LINEAR |
| 7 extra HEAP chunks | 749k / 846k / 942k / **1085k** — rising | 2.259 / 2.227 / **2.302** — superlinear |

**Verdict: per-step persisting/copying is NOT the growth.** Exit entries undergo
exactly the persist-and-peval treatment the hypothesis blamed, and their per-step
cost does not grow at all. What that mechanism DOES explain is the linear term —
`b ∝ L²` is per-step table copying, O(table × steps) — which is the larger term
below N≈25 but never the scaling wall.

Two further things the same table says:

- A heap chunk costs **~320× more per step** than an exit entry (750k vs 2.3k
  words). So the heap cost is not copying either; it is consume/produce
  unification and solver work per chunk.
- **The heap story is also incomplete as an explanation of the quadratic.** The
  7 added chunks are INERT (declared, never written, since A3 is pinned), and
  their per-chunk-per-step cost grows only **1.45× from N=1 to N=8** — far too
  slow to generate a quadratic on its own, which would need ~8×. So inert
  heap-chunk scanning is ruled out as the main carrier too, even though heap SIZE
  does scale the quadratic coefficient (1.457× for 7 extra cells, §9 arm H).

What carries the quadratic was therefore not reachable from any contract knob —
correctly predicting that the next instrument had to go INSIDE the executor.
**§10 does that and identifies it: a leaked duplicable `encodes_instr` chunk, one
per instruction step.** The reasoning above still holds and is why §10 looked
where it did: not per-step copying, not the exit table, not inert heap chunks,
but the ACTIVE consume/produce path.

### What this rules OUT, with evidence

- **Term size.** Sublinear (159 + 491·N), and `dc_tmax` is pinned at **10** for
  every N and every arm. `dc_nest = 0`, so the measure is exact rather than an
  approximation — the §8 worry that `term_tuple`/`term_record` might hide size
  does not apply to `zzn`. §8's last suspect is dead.
- **Fuel.** 4.4× the fuel (68 → 300 at N=4) costs **+0.04%** allocation and leaves
  every structural counter byte-identical. Excess fuel is free; do not tune it.
- **`|wctx|` growth.** Live-variable sum is exactly affine and the per-node average
  is a flat 20.6 at every N. The `an` + `encoded_instr` fixes did what §7 claims,
  and the cost stayed quadratic anyway — so `|wctx|` was never the driver.
  **`Verifier.v`'s prologue comment claiming it is has been corrected.**
- **The measuring instrument.** A control using only `SymProp.Statistics.size`
  allocates within **0.3%** of the full census at every N, so the quadratic is in
  tree CONSTRUCTION.

### A confound in `zzn` that §7/§8 did not isolate

`zzn_mem_specs n` declares **n** memory cells, so the reproducer grows the heap
AND the trip count together. Holding A3 still (`zzf_instrs`, `addi a3,a3,0`) pins
the heap at one cell for every N. With the confound removed the live-variable sum
goes from mildly superlinear (2.08, 2.18 per doubling) to **exactly linear**
(1.99, 1.99) — the residual growth §7 attributed to `mv` was entirely this. It is
also worth 1.60× of allocation at N=8 (2757.8 M vs 1721.2 M), so any `zzn` number
quoted from §7/§8 carries it.

### Measurement traps added to §8's list

- **A probe that FAILS TO COMPILE reports the baseline allocation**, which reads
  as "this variant is free". Always gate on `Finished transaction` before
  believing an `allocated_words` figure.
- `SymProp.Statistics.size` already returns `N`, not `nat`.

### Consequences

- **`vm_compute` is the only worthwhile target** (§8 established `Qed` re-runs it
  via the VM cast, `solve_vc` is flat, `postprocess` is free). Within it, the
  lever is (a) the number of instruction steps and (b) the symbolic heap size —
  and note L enters BOTH, which is why long programs hurt more than trip counts.
- **Shrinking `|wctx|` further is not worth doing for speed.** That avenue is now
  measured out; the two source fixes were correct but the slope lives elsewhere.
- **Predicted ceiling.** At N=32 the model gives 12.2 G words (~2.8× N=16) and at
  N=64 38.2 G (~3.1×). N=32 was already killed by earlyoom at N=32 in §8; nothing
  here changes that verdict, and the model says N=64 is ~22× N=16 in work.

### Probe files

`Example/ZZDiagCommon.v` (census + `zzf`/`zzm` isolation arms), `ZZDiagL.v`
(body-length factorial), `ZZDiagH.v` (constant large heap), runners
`ZZDg{A,B,C,S,F,H}*.v` and `ZZDgL{9,24}_*.v`. All THROWAWAY, none in
`_CoqProject`; compile via `rocq_compile_file`, or via `coqc` directly when the
`OCAMLRUNPARAM` GC stats are wanted.

## §10-ROOTCAUSE. The quadratic is a LEAKED HEAP CHUNK — 2026-08-03

§9 established the cost law and refuted every contract-reachable explanation. The
carrier turned out to be inside the executor, and it is simple:

> **`encodes_instr` is `is_duplicable := true` (`Sig.v:343`), and
> `heap_extractions` KEEPS duplicable chunks on consume (`Chunks.v:106`). So every
> fetch adds an `encodes_instr` chunk to the symbolic heap and nothing ever removes
> it. The heap grows by exactly ONE chunk per instruction step. Per-step cost is
> linear in heap size (§9 arm C), so the total is quadratic.**

### How it was measured: instrument the executor, read out via `nc_debug`

`SHeapSpec A := □(A -> SHeap -> 𝕊) -> SHeap -> 𝕊` hands the heap to any
combinator, and `nc_debug` is **0** in the uninstrumented executor, so *k*
`SymProp.debug` nodes are a clean channel for smuggling a number out per step
(technique inherited from the archived `ZZFwdCommon.v`). Added temporarily to
`Verifier.v`, wrapping the step at `:369`:

```coq
Definition zz_probe {A} : ⊢ SHeapSpec A -> SHeapSpec A :=
  fun w m Φ h => zz_debugs (zz_measure h) (m Φ h).
...
⟨ θ1 ⟩ apc' <- zz_probe (sexec_instruction i apc anp wd) ;;
```

The census then reports **Σ over steps** of `zz_measure`. Controls unchanged in
every arm: `nc_angbin` 344/687/1373/2745 (identical to §7's figures),
`nc_demonicv` affine, `nc_assertk` pinned at 15. Only `Verifier.v` and the LIGHT
chain need rebuilding — `VerifierRel.v` is not on the probe path — which is what
made this affordable. Recipe generalised in
`.claude/skills/rocq-timeout-triage/references/allocation-probes.md`.

### The numbers (fits on N=1,2,8; N=4 held out)

| `zz_measure` | Σ over steps | held-out N=4 |
|---|---|---|
| whole heap (`List.length h`) | `105·N + 98·N²` | 1988 predicted = 1988 measured, **EXACT** |
| only `chunk_user encodes_instr` | `98·N² − 7·N` | 1540 = 1540, **EXACT** |
| difference (real heap) | `112·N`, **zero N² term** | — |

Three things fall straight out:

1. **The entire N² term is `encodes_instr`** — 98N² in both rows.
2. **The real heap is a constant 8 chunks** (112N / 14N steps): registers, pc, the
   memory cell, the current `ptstoinstr`. Nothing else leaks.
3. **It is exactly one chunk per step, and the probe sits before the produce.**
   With S = 14N steps, one chunk accumulating per step and the heap read *before*
   each step's produce gives Σ(k=0..S−1) k = S(S−1)/2 = **14N(14N−1)/2 = 98N² −
   7N** — the fitted model, linear term and sign included. Verified at N=1/2/4/8:
   91/378/1540/6216 against measured 91/378/1540/6216.

Average heap size runs 14.5 / 21.5 / 35.5 / 63.5 at N=1/2/4/8 = `7.5 + 7N`.

### Causal confirmation: filtering the chunk kills the quadratic

Same probe point, one line changed — pass a filtered heap onward instead of
counting it:

```coq
Definition zz_gc {w} (h : SHeap w) : SHeap w :=
  List.filter (fun c => match c with
                        | chunk_user encodes_instr _ => false
                        | _ => true end) h.
Definition zz_probe {A} : ⊢ SHeapSpec A -> SHeapSpec A :=
  fun w m Φ h => m Φ (zz_gc h).
```

**Control: every census counter byte-identical to the uninstrumented arm** at
N=1/2/4/8 (nodes 2168/4294/8546/17050, pcsum 20831/56973/129257/273825, wsum,
tsize, depth). No completeness lost; the VC is structurally unchanged.

| | constant | linear/N | **quadratic/N²** |
|---|---|---|---|
| leak present | −38,557,049 | 165,936,467 | **6,754,351** |
| `encodes_instr` GC'd | −38,555,325 | 167,376,080 | **−2,902** |

**The quadratic coefficient collapses to −0.043% of itself, i.e. zero.** The
constant is untouched and the linear term rises 0.87% — the filter's own per-step
cost. Both quadratic fits hold their N=4 held-out point to 0.002%.

Independently: a **pure affine** model fits the GC arm on N=1,8 and predicts the
two held-out points to **−0.006%** and **−0.004%** (`alloc = −38.5M +
167.3M·N`), with ratios per doubling 2.299 / 2.130 / 2.061 → 2. With the leak
plugged, allocation is affine in N.

Projected, using the two fitted models:

| N | 8 | 16 | 32 | 64 | 128 |
|---|---|---|---|---|---|
| leak present (G words) | 1.72 | 4.35 | 12.19 | 38.25 | 131.86 |
| GC'd (G words) | 1.30 | 2.64 | 5.32 | 10.67 | 21.38 |
| **speedup** | 1.32× | 1.65× | 2.29× | **3.58×** | **6.17×** |

Unbounded growth, as expected when a quadratic term is removed rather than scaled.

### Why three sessions missed this, and it is NOT the fix this plan landed

**The `encoded_instr` VARIABLE and the `encodes_instr` CHUNK are different objects
with nearly identical names.** This plan removed the variable from `wctx` (§7,
confirmed: survivors +15/trip → +1/trip). The chunk is still produced and retained
on every step. That is precisely why a successful `|wctx|` fix changed no slope —
and it is the answer to §8's "why did the world-GC look better": the GC arm was
collecting the chunk too.

The accumulation was in fact **already known** — the 2026-07-29 chunk-GC session
found it, named the exact mechanism (duplicable + `heap_extractions`), and measured
1596 retained at N=4. It was set aside on the strength of "heap size is measured
NOT to be a driver (0.95×)". **That measurement is hereby refuted**: heap size is
the driver, and the 0.95× figure (a "constant-heap variant" of a since-replaced
executor, in wall clock) should not be requoted. The historical "chunk-only GC =
−6% at N=4" is likewise superseded — measured here, GCing the chunk saves 14% at
N=4 and the saving grows without bound.

### The fix may already be proved

Per the memory note, the chunk-GC half of the archived attempt is **sound and
proved** — `refine_chunk_gc`, `inst_gc_heap`, `interpret_scheap_gc_heap` at tag
`archive/gc-attempt-2026-07` (tip `48c651f0`, branch `unquantify-gate`). It was
discarded only because it was bundled with the *world*-GC, which is unprovable
(`gc_dead_roots` pins a dead variable to an arbitrary value, so the tree is
vacuously safe at disagreeing valuations), and because heap size was believed not
to matter. Both reasons are now gone.

**Recommended next step:** recover `refine_chunk_gc` and friends from the archive
and land the chunk GC ALONE, without any world GC. Unlike the archived bundle this
needs no new core machinery and no trusted-surface change — it filters a
duplicable chunk whose Iris interpretation is a pure proposition
(`⌜pure_decode code = inr instr⌝`, `IrisInstance.v:295`), which is why dropping it
loses nothing. NOT ATTEMPTED HERE; the numbers above come from an unsound probe
filter, which is fine for attribution and not fine for the trusted path.

### Probe files and state

`Example/ZZDgP{1,2,4,8}.v` are the readout runners (they define `zzf_nc` inline
over `ZZCommon`'s `NC`, which is the record that carries `nc_debug`). The
`Verifier.v` instrumentation was REVERTED and the full `Results.vo` closure
rebuilt green (30 files, 0 errors) — nothing in the tree is instrumented.
