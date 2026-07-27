# CFGVer directory notes

Facts that apply to *any* edit in this subtree, not just one task — kept
here (not in the `cfgver` hub skill) so they load unconditionally whenever
Claude touches a file under `case_study/RiscvPmp/CFGVer/`, with no chance of
a skill-routing miss. Task-specific detail (which sub-skill to read for
which layer) stays in the `cfgver` hub skill and its sub-skills.

## File layout and compilation order

Post 2026-07-17 split of the old monolithic `Examples.v`:

`Spec.v` → `Verifier.v` → {`Noninterference.v`, `Tables.v`} → `Contracts.v` →
`GenContract.v` → then TWO INDEPENDENT BRANCHES that rejoin at `Results.v`:

- **example branch:** `Example/Prelude.v` →
  `Example/{MvSwap,Jumps,Countdown,SetX2,Cmovznz4,Precompute,KeyScheduleLoop}.v`
  (mutually independent, each just `Require Import …Example.Prelude`)
- **adequacy branch:** `Adequacy.v` → `EndToEnd.v`

→ `Example/<Prog>Result.v` (one per example; needs its example AND `EndToEnd`) →
`Results.v` (re-export shell only — no proofs; the merge gate's single build
target, so its closure is every result).

**Keep the two branches independent.** `Example/Prelude.v` deliberately stops at
`GenContract` and must NOT Export `EndToEnd`: the `Adequacy`→`EndToEnd` chain
costs ~85 s, and today it builds in the parallel shadow of the examples. Making
any `Example/*.v` require `EndToEnd` — e.g. to host its own end-to-end theorem —
serializes those 85 s ahead of every example and costs ~40 s of wall time on a
-j2 gate build. That is exactly why the end theorems live in separate
`<Prog>Result.v` files rather than in the examples themselves.

`Noninterference.v` is the trusted statement layer (step relations,
`declare_*`, `noninterferent_strong`, spec types) and deliberately does not
depend on the verifier.

**When modifying a file, recompile it with `keep_vo=True` before compiling
files downstream of it** — otherwise `Cannot find a physical path bound to …`
errors on the dependents.

| File | Contents | Matching skill |
|------|----------|----------------|
| `Spec.v` | `Assembly` instruction-builder synonyms; CFGVer's own leakage-aware `Specification` instance (`secLeakvar`/`inv_leakage`-annotated contracts, distinct from `../Contracts.v`) | cfgver-contracts |
| `Noninterference.v` | trusted statement defs | cfgver-endtoend |
| `Tables.v` | reg aliases, `instrs_of_list`, `table_of_list`/`exits_of_*`, faith lemmas | cfgver-executor |
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
