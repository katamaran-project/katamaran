# CFGVer directory notes

Facts that apply to *any* edit in this subtree, not just one task — kept
here (not in the `cfgver` hub skill) so they load unconditionally whenever
Claude touches a file under `case_study/RiscvPmp/CFGVer/`, with no chance of
a skill-routing miss. Task-specific detail (which sub-skill to read for
which layer) stays in the `cfgver` hub skill and its sub-skills.

## File layout and compilation order

Post 2026-07-17 split of the old monolithic `Examples.v`:

`Spec.v` → `Verifier.v` → {`Noninterference.v`, `Tables.v`} → `Contracts.v` →
`GenContract.v` → `Adequacy.v` → `EndToEnd.v` →
`Example/{MvSwap,Jumps,Countdown,SetX2,Cmovznz4,Precompute,KeyScheduleLoop}.v`
(mutually independent) → `Results.v` (aggregator: the concrete
`*_noninterferent` theorems the merge gate checks).

`Noninterference.v` is the trusted statement layer (step relations,
`declare_*`, `noninterferent_strong`, spec types) and deliberately does not
depend on the verifier.

**When modifying a file, recompile it with `keep_vo=True` before compiling
files downstream of it** — otherwise `Cannot find a physical path bound to …`
errors on the dependents.

| File | Contents | Matching skill |
|------|----------|----------------|
| `Noninterference.v` | trusted statement defs | cfgver-endtoend |
| `Tables.v` | reg aliases, `instrs_of_list`, `table_of_list`/`exits_of_*`, faith lemmas | cfgver-executor |
| `Contracts.v` | `CFGVerifierContract`, `minimal_pre`, `↦ᵣ`/`↦ₘ`, `solve_vc` | cfgver-contracts, cfgver-solve-vc |
| `GenContract.v` | `gen_contract(_param/_rel)`, `param_val`, concretize maps | cfgver-gen-contract(-internals) |
| `Adequacy.v` | `myWP2_loop`, `create_resources`, `semWP2_*`, `sound_*_myWP2` | cfgver-soundness, cfgver-wp2 |
| `EndToEnd.v` | `cfg_instrs_*`, `gen_implpre*`, `gen_contract_noninterferent*` | cfgver-endtoend(-internals), cfgver-memory |
| `Example/*.v` | per-program instrs+specs (statement-relevant), contract, `valid_*` VC | cfgver-new-example |
| `Results.v` | concrete end-to-end theorems | cfgver-endtoend |

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
