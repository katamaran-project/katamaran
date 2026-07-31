# PLAN — remove `encoded_instr`, the last per-step logical variable

Status: **DONE 2026-08-01** — see §7-RESULTS at the bottom for the outcome and
the measured numbers. Branch `nextpc-param`. Sequel to `PLAN-nextpc-param.md`,
which removed `an` the same way but did NOT bend the curve; this one does.

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

## §7-RESULTS. DONE 2026-08-01 — the curve bends

### The decisive datum: execution-driven `|wctx|` growth is ZERO

`Example/ZZSurv.v`, same flat `zzn` reproducer as §0:

| N | survivors BEFORE | survivors AFTER |
|---|---|---|
| 1 | 20 — `p, np, v, v.1, v.2, mv` + **`encoded_instr` ×14** | 20 — `p`, **`w`…`w.13`**, `np, v, v.1, v.2, mv` |
| 2 | 35 — those + `mv.1` + **`encoded_instr` ×28** | **21** — those + `mv.1` |
| 4 | (would be 49) | **23** |
| 8 | (would be 105) | **27** |

Growth per trip: **+15 → +1**, and that +1 is `mv`, which this reproducer's own
`zzn_mem_specs n` declares. That is exactly §0's success criterion. The 14
survivors that remain are the program's 14 word variables — bound to PROGRAM
SIZE, not trip count, which is the whole point of introducing them once at
contract entry.

`encoded_instr` no longer appears in the demonicv census at all.

### Timing: a real exponent change, unlike the `an` fix

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

### Methodology correction worth keeping

**`-vos` does NOT skip proof bodies inside a `Section` with a `Context`** — Coq
must run the proof to compute which section variables to generalize over.
Verified both ways on scratch files (unsectioned false lemma → exit 0; sectioned
false lemma → error). Every CFGVer file wraps its content in
`Section CFGVerificationDerived`, so these `vos` sweeps DO check tactics, and
they caught two real errors (`congruence` chokes on `bv`'s proof field;
SSReflect rejects `rewrite H1, H2 in H`).

The exceptions are what bit: code at file top level (`Tables.v`) or in a plain
`Module` (`Spec.v`'s `valid_execute_fetch`) IS skipped. `Tables.v`'s two new
`bv.eqb` lemmas were both wrong and only `full` mode found them — a bare `cbn`
unfolds `bv.eqb` into `N.eqb (bv.bin _) (bv.bin _)` so the rewrite stops
matching, and `destruct (bv.eqb_spec …)` will not abstract a closed scrutinee
sitting inside an `if`.
