# PLAN — remove `encoded_instr`, the last per-step logical variable

Status: drafted 2026-07-31, not started. Branch `nextpc-param` (tip `05a4ba00`).
Sequel to `PLAN-nextpc-param.md`, which removed `an` the same way.

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

**Why `encoded_instr` survives while `op` — also `∃`-produced, also demonic,
also once per step — does not.** `lemma_close_ptsto_instr` takes `cl` as a
**lemma pattern argument** (`Spec.v:653`), so the *program* supplies a concrete
term for the word, and `op` is unified against it and dies. `encoded_instr` has
no supplier: its only equation relates it to another variable.

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

## §3. Sketch of the changes

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

## §4. The risk, stated plainly

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
