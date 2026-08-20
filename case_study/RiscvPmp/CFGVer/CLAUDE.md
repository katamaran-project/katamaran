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

Every `coqc` process pays a peak-RSS floor. Measured layer costs (bare-`Require`
probes, peak RSS — the only metric worth tuning on here, see below):

| layer | RSS | marginal |
|---|---|---|
| `Semantics` + `Machine` + `Sig` | 1.96 GB | — (55%, irreducible) |
| `+ CFGVer.Spec` (executor instantiation) | 2.32 | **+0.36** |
| `+ Verifier` | 2.32 | +0.00 |
| `+ Contracts` + `GenContract` | 2.32 | +0.00 |
| `+ EndToEnd` (Iris chain) | 3.56 | **+1.24** |

**`Iris` is 3.4x heavier than the whole symbolic verifier layer** — the recurring
intuition that the symbolic executor is the expensive part is measured false.
**`Verifier`/`Contracts`/`GenContract` cost +0.00 on top of `Spec`**, so no split
among those three can move the number. And the executor cannot be dropped by any
file except `Noninterference.v`: every other file names `ValidCFGVerifierContract`
or `gen_contract_param` in a *statement*, whose type must typecheck, so its
closure is mandatory whether or not `vm_compute` reduces it.

Hence the split below targets Iris, not the executor — three files were split so
that the Iris model and the shallow/refine/soundness stack stay OFF the example
path:

| light (no Iris) | heavy (Iris) | boundary |
|---|---|---|
| `Spec.v` — `Assembly`, `Specification` instance, symbolic executor | `SpecIris.v` — shallow executor, `RiscvPmpIrisInstanceWithContracts` | old line 863 |
| `Verifier.v` — `safeE`, `Section Symbolic` | `VerifierRel.v` — `Shallow`, `Relational`, `Soundness` | old `Section Relational` |
| `Tables.v` — reg aliases, list/table builders | `TablesRel.v` — the 5 `itable_rel`/`etable_rel` faith lemmas | old line 175 |

Result: `Contracts.v`, `GenContract.v`, `Example/Prelude.v` and every
`Example/*.v` dropped 3.6 GB → ~2.46 GB. **Adding an Iris (or `ShallowExecutor`
/ `MicroSail.Soundness`) require to any light file silently puts ~1.2 GB back on
all seven examples**, which is what bounds the gate's `-j`.

**Judge changes here on peak RSS, not wall time.** A full rebuild appeared to
regress ~11% after this split (404 s → 448 s), which prompted a hunt for a DAG
fix. That hunt came up empty and the premise did not survive checking: wall
times on this box swing with `.vo` page-cache state (an *unchanged*
`TablesRel.v` measured 22/43/32 s on three consecutive runs — see
**rocq-timeout-triage** Step 1b). The split was KEPT, on the strength of the RSS
numbers above, which are deterministic. Don't re-open the wall-time question
without user-CPU or back-to-back measurements.

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
serializes those 85 s ahead of every example instead of alongside them. (The
argument here is structural — it lengthens the critical path — not a wall-time
measurement; see the RSS caveat above before quoting any second count.) That is
exactly why the end theorems live in separate
`<Prog>Result.v` files rather than in the examples themselves.

**The one-file-per-program `Result` layout is a DELIBERATE trade — don't merge it
back.** Measured (2026-07-27): each `Example/<Prog>Result.v` is ~5-8 s and 3.26 GB
of which essentially 100% is `Require` load — the proofs are two `apply`s and a
`cbn; lia`. So on a *full* rebuild the 7 files cost ~35 s more CPU than a single
merged `Results.v` would, and merging was considered on those grounds. It was
rejected because the split is what makes a PER-PROGRAM BUILD TARGET possible:
`make Example/Cmovznz4Result.vo` pulls in only Cmovznz4 plus the heavy chain,
whereas a merged `Results.v` requires all seven examples, so checking any single
end theorem would mean building ~224 s of unrelated example VCs. Iteration on one
program beats full-rebuild CPU here. (The 0.80 GB of Iris each Result file carries
but never mentions is real waste — it is inherited transitively through
`EndToEnd` — but it is not recoverable by rearranging files; see the dead-ends
section and `theories/CLAUDE.md` on why `Require` transitivity bounds this.)

### Dead ends — do not retry (2026-07-27)

- **Splitting `SpecIris.v`'s four `Include`s into separate files.** Three
  reasons, any one fatal: (1) `ShallowSoundness.Soundness` takes an
  `(Import HOAR : ProgramLogicOn …)` parameter that `SpecIris.v` never passes —
  the preceding `Include` makes the *ambient* module satisfy it, which is
  precisely why all four live in one module; (2) `VerifierRel` needs both halves
  anyway (`Section Relational` uses the Iris instance, `Section Soundness` uses
  `sound_cexec`/`sound_stm`/`contractsSound`), so the files would stay serial;
  (3) the four `Include`s are only **~4 s of `SpecIris`'s 62 s** — the cost is
  the eight Iris body lemmas (`read_ram_sound`'s `Qed.` alone is 11.7 s).
- **Merging the heavy files to save file-load tax.** `TablesRel` and `Adequacy`
  are siblings (neither requires the other), so `TablesRel` already builds in
  `Adequacy`'s shadow at `-j≥2`. The real heavy path is
  `Spec → SpecIris → VerifierRel → Adequacy → EndToEnd`, and its cost is genuine
  proof work — `rsolve` at `VerifierRel:198` (9.4 s), `consume_sound` at
  `VerifierRel:706` (6.4 s) — that no file arrangement touches.

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

**Currently violated in `Tables.v`/`Contracts.v`/`GenContract.v` (2026-08-20,
AnnotInstr migration Phase 1, commit 323db24c) — flagged, not yet fixed.** All
three now do `Require Import RiscvPmp.CFGVer.Verifier` and reference
`Annot`/`AnnotInstr`/`AnnotAST`/`AnnotGhost`/`strip` unqualified, because
qualifying them hit a confusing `rocq_compile_file` dune-fallback resolution
failure mid-session (see **rocq-implementation**'s tooling-caveat entry) that
was mistaken for the names genuinely not existing. It compiles today
(`make -f Makefile.coq`, verified) ONLY because BlockVer is fully commented out
of `_CoqProject` on this branch, so there is no live BlockVer module to clash
with. **This is latent, not inert**: reactivating BlockVer alongside these
files without reverting this first will reproduce exactly the clash this note
exists to prevent. To fix: revert the three `Require Import` back to bare
`Require`, and qualify every bare `Annot`/`AnnotInstr`/`AnnotAST`/`AnnotGhost`/
`strip` occurrence (`Tables.v`'s `table_of_list'`/`exits_of_list`, `Contracts.v`'s
`CFG_VC_triple`/`Valid_CFG_VC`/`CFGVerifierContract`/`cfg_map`, and six
`GenContract.v` builders) as `Katamaran.RiscvPmp.CFGVer.Verifier.<name>` —
confirm the qualified path actually resolves with a plain `rocq_check`/
`rocq_start` probe FIRST (not `Locate`, which reported false negatives on stale
state during this session), then re-run GATE 1 (Phase 1 of
`plans/PLAN-annotinstr.md`) to confirm nothing broke.
