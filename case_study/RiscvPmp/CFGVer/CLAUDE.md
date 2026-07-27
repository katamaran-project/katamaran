# CFGVer directory notes

Facts that apply to *any* edit in this subtree, not just one task — kept
here (not in the `cfgver` hub skill) so they load unconditionally whenever
Claude touches a file under `case_study/RiscvPmp/CFGVer/`, with no chance of
a skill-routing miss. Task-specific detail (which sub-skill to read for
which layer) stays in the `cfgver` hub skill and its sub-skills.

## File layout and compilation order

Post 2026-07-17 split of the old monolithic `Examples.v`:

`Spec.v` → `Verifier.v` → `Tables.v` → `Contracts.v` → `GenContract.v` → then
TWO INDEPENDENT BRANCHES that rejoin at `Example/<Prog>Result.v`:

- **example branch (LIGHT, ~2.45 GB):** `Example/Prelude.v` →
  `Example/{MvSwap,Jumps,Countdown,SetX2,Cmovznz4,Precompute,KeyScheduleLoop}.v`
  (mutually independent, each just `Require Import …Example.Prelude`)
- **adequacy branch (HEAVY, ~3.9 GB):** `SpecIris.v` → `VerifierRel.v` →
  `TablesRel.v` → `Adequacy.v` → `EndToEnd.v`

→ `Example/<Prog>Result.v` (one per example; needs its example AND `EndToEnd`) →
`Results.v` (re-export shell only — no proofs; the merge gate's single build
target, so its closure is every result).

`Noninterference.v` sits outside both branches: it depends only on `Semantics` +
`RiscvPmp.Machine`, so it builds in parallel with everything above.

### The light/heavy split (2026-07-27) — DON'T UNDO IT

Every `coqc` process pays a peak-RSS floor. Measured layer costs: `Semantics` +
`Machine` 1.12 GB, `+ Sig` +0.94, `+ all executors` +0.56, `+ binary Iris model`
+0.98. Three files were split so that the Iris model and the shallow/refine/
soundness stack stay OFF the example path — the examples only need to
`vm_compute` the SYMBOLIC executor:

| light (no Iris) | heavy (Iris) | boundary |
|---|---|---|
| `Spec.v` — `Assembly`, `Specification` instance, symbolic executor | `SpecIris.v` — shallow executor, `RiscvPmpIrisInstanceWithContracts` | old line 863 |
| `Verifier.v` — `safeE`, `Section Symbolic` | `VerifierRel.v` — `Shallow`, `Relational`, `Soundness` | old `Section Relational` |
| `Tables.v` — reg aliases, list/table builders | `TablesRel.v` — the 5 `itable_rel`/`etable_rel` faith lemmas | old line 175 |

Result: `Contracts.v`, `GenContract.v`, `Example/Prelude.v` and every
`Example/*.v` dropped 3.6 GB → ~2.46 GB. **Adding an Iris (or `ShallowExecutor`
/ `MicroSail.Soundness`) require to any light file silently puts ~1.2 GB back on
all seven examples**, which is what bounds the gate's `-j`.

Two traps this created:
- `Tables.v` needs an explicit `Open Scope list_scope.` after its imports.
  `RiscvPmp.Sig` re-imports `ctx.notations`, whose `_ :: _` Binding notation
  hijacks list cons; the file only ever parsed by accident because
  `Import iris.proofmode.tactics.` came last. `Import ListNotations` last does
  NOT fix it — only opening the scope does.
- Names that moved to `VerifierRel` must be referenced as
  `Katamaran.RiscvPmp.CFGVer.VerifierRel.<name>` (`cexec_cfg_addr`,
  `cexec_triple_addr`, `itable_rel`, `etable_rel`, `ptsto_instrs`,
  `ptsto_instrs_lookup`, `rcfg_verification_condition`,
  `sound_exec_instruction`). `safeE` and `scfg_verification_condition` stayed in
  `Verifier`.

**Keep the two branches independent.** `Example/Prelude.v` deliberately stops at
`GenContract` and must NOT Export `EndToEnd`: the `Adequacy`→`EndToEnd` chain
costs ~85 s, and today it builds in the parallel shadow of the examples. Making
any `Example/*.v` require `EndToEnd` — e.g. to host its own end-to-end theorem —
serializes those 85 s ahead of every example and costs ~40 s of wall time on a
-j2 gate build. That is exactly why the end theorems live in separate
`<Prog>Result.v` files rather than in the examples themselves.

`Noninterference.v` is the trusted statement layer (step relations,
`declare_*`, `noninterferent_strong`, spec types) and genuinely does not depend
on the verifier — it requires neither `CFGVer.Spec` nor `RiscvPmp.Sig`.

**When modifying a file, recompile it with `keep_vo=True` before compiling
files downstream of it** — otherwise `Cannot find a physical path bound to …`
errors on the dependents.

| File | Contents | Matching skill |
|------|----------|----------------|
| `Spec.v` | `Assembly` instruction-builder synonyms; CFGVer's own leakage-aware `Specification` instance (`secLeakvar`/`inv_leakage`-annotated contracts, distinct from `../Contracts.v`); the SYMBOLIC executor. Iris-free | cfgver-contracts |
| `SpecIris.v` | shallow executor + `RiscvPmpIrisInstanceWithContracts` (the Iris wiring split out of `Spec.v`) | cfgver-soundness |
| `Verifier.v` | `safeE`, `sexec_cfg_addr`, `scfg_verification_condition` (`Section Symbolic`). Iris-free | cfgver-executor |
| `VerifierRel.v` | `cexec_cfg_addr` (`Shallow`), `rexec_cfg_addr` + `RefineCompat` instances + `itable_rel`/`etable_rel` (`Relational`), `ptsto_instrs` + `sound_exec_instruction` (`Soundness`) | cfgver-refinement, cfgver-rsolve, cfgver-soundness |
| `Noninterference.v` | trusted statement defs; requires only `Semantics`+`Machine` | cfgver-endtoend |
| `Tables.v` | reg aliases, `instrs_of_list`, `table_of_list`/`exits_of_*`. Iris-free | cfgver-executor |
| `TablesRel.v` | the `itable_rel`/`etable_rel` faith lemmas (statements mention `Pred w`, hence Iris). Sole consumer: `EndToEnd.v` | cfgver-executor |
| `Contracts.v` | `CFGVerifierContract`, `minimal_pre`, `↦ᵣ`/`↦ₘ`, `solve_vc` | cfgver-contracts, cfgver-solve-vc |
| `GenContract.v` | `gen_contract(_param/_rel)`, `param_val`, concretize maps | cfgver-gen-contract(-internals) |
| `Adequacy.v` | `myWP2_loop`, `create_resources`, `semWP2_*`, `sound_*_myWP2` | cfgver-soundness, cfgver-wp2 |
| `EndToEnd.v` | `cfg_instrs_*`, `gen_implpre*`, `gen_contract_noninterferent*` (incl. the `_simple`/`_rel_simple` common-case bridges + the `ni_rel_corollary` tactic notation that folds the `_rel` concrete-corollary ritual) | cfgver-endtoend(-internals), cfgver-memory |
| `Example/Prelude.v` | shared `Require Export`/`Import` preamble every example re-imports (no defs) | cfgver-new-example |
| `Example/<Prog>.v` | per-program instrs+specs (statement-relevant), parametric contract, `valid_*_param` VC. Only the `_param` form exists — the concrete-base contracts/VCs were removed as dead in 2026-07-27 | cfgver-new-example |
| `Example/<Prog>Result.v` | that program's end-to-end `*_noninterferent[_param]` theorems (trusted statement surface, gate-checked) | cfgver-endtoend |
| `Results.v` | re-export shell over the `<Prog>Result.v` files; no proofs | cfgver-endtoend |

## Importing CFGVer.Verifier downstream

```coq
(* At top level, after the main Require Import block: *)
From Katamaran Require
     RiscvPmp.CFGVer.Verifier.
```

Then use qualified names (`Katamaran.RiscvPmp.CFGVer.Verifier.foo`). Do NOT
`Require Import` — it clashes with BlockVer's identically-named definitions.
The other CFGVer files (`Noninterference`, `Tables`, `Contracts`, …) are safe
to plain `Require Import`.

> **BlockVer-contingent.** This idiom exists only because BlockVer shares names
> with CFGVer. Once BlockVer is consolidated away (see TODO.md cleanup items),
> switch the downstream files to a plain `Require Import` and delete this note.
