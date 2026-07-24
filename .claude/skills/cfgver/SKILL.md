---
name: cfgver
description: >
  Index/hub for the Katamaran RISC-V PMP CFG verifier (case_study/RiscvPmp/CFGVer/).
  Use when starting CFGVer work, when the request spans multiple layers, or when no
  focused sub-skill clearly matches. Routes to: cfgver-new-example (the recipe for
  verifying a new program), cfgver-executor (symbolic executor + VC),
  cfgver-refinement (concrete mirror + relational lemmas), cfgver-rsolve (the rsolve
  tactic), cfgver-soundness (the chain), cfgver-wp2 (semWP2 mechanics),
  cfgver-contracts (the contract record, hand-written contracts), cfgver-gen-contract
  (the generator user guide), cfgver-gen-contract-internals, cfgver-solve-vc (VC
  discharge), cfgver-endtoend (wiring user guide), cfgver-endtoend-internals, and
  cfgver-memory (data memory). If the request clearly matches one of those, use it
  directly instead. Katamaran-specific; generic Rocq/Coq → the rocq skill.
---

# CFGVer — reference hub

Entry point for the CFG verifier (`case_study/RiscvPmp/CFGVer/`). The reference is
split into focused skills so only the relevant one loads.

> **Directory-wide facts (file layout/compile order, the `Require`-vs-
> `Require Import Verifier` landmine) now live in
> `case_study/RiscvPmp/CFGVer/CLAUDE.md`** — that file loads automatically
> whenever a CFGVer file is touched, so it isn't repeated here. This skill
> covers *which sub-skill to read*, not those directory-wide facts.

For generic Rocq workflow (compile-first iteration, lemma search, proof repair)
use the **rocq** plugin skill; generic pitfalls live in **rocq-pitfalls**,
**bv-pitfalls**, **gmap-pitfalls**, **iris-proofmode**.

## Module map — which skill to read

| Skill | Covers | Read when |
|-------|--------|-----------|
| **cfgver-new-example** | the 6-step recipe: asm → contract → VC → end lemma → axiom check | verifying/adding a new program (most common task) |
| **cfgver-executor** | symbolic executor `sexec_cfg_addr`, term-table instruction store, `ptsto_instrs`, `scfg_verification_condition` | how the verifier decides/executes; VC construction; symbolic-pc errors |
| **cfgver-refinement** | concrete mirror `cexec_cfg_addr`, the mirroring discipline, `RefineCompat`, `rexec_cfg_addr` | reading/extending the relational layer; proving a new relational (ℛ⟦⟧) lemma |
| **cfgver-rsolve** | driving `rsolve`: debug workflow, instance template, divergence/OOM, manual bind pairing | an `rsolve` failure/hang/OOM; writing a `RefineCompat` instance |
| **cfgver-soundness** | the VC → `myWP2_loop` → leakage chain; `WP2_loop` vs `myWP2_loop` | understanding/extending the theorem architecture |
| **cfgver-wp2** | binary WP2 proof mechanics: `semWP2_unfold`, `stm_to_val`, `IVal`, `Result2` (library skill) | a semWP2/adequacy proof is stuck |
| **cfgver-contracts** | the `CFGVerifierContract` record, field semantics, Σ choice, hand-written contracts, `Valid`/`Debug` | what a contract IS; writing one without the generator |
| **cfgver-gen-contract** | the generator user guide: spec triples, `extra_exit_offs`, the 5 premises | declaring public/private/pinned registers or memory via `gen_contract` |
| **cfgver-gen-contract-internals** | `gen_reg_asn`/`gen_pre` builders, `gen_implpre` (library skill) | modifying/extending the generator machinery itself |
| **cfgver-solve-vc** | `vm_compute. solve_vc.`, residual patterns, `DebugCFGVerifierContract`, tight-fuel `False`, vm_compute divergence | discharging or debugging a VC |
| **cfgver-endtoend** | `cfg_instrs_endToEnd`, its call pattern, the `ImplPre` obligation | wiring a hand-written contract; debugging `ImplPre` |
| **cfgver-endtoend-internals** | proof bodies of the wiring lemmas, `_with_mem` proof patterns (library skill) | modifying/extending the wiring lemmas themselves |
| **cfgver-memory** | data-memory infra: `interp_mem_with_*`, `instrsAndDataMemory`, `_with_mem` variants | the program reads/writes data memory |

Dependency order: `executor ← refinement ← soundness ← contracts ← endtoend ← memory`,
with `gen-contract` on top of `contracts` and `new-example` orchestrating all of them.
Library skills (loaded from parents, rarely self-firing): `cfgver-rsolve`,
`cfgver-wp2`, `cfgver-gen-contract-internals`, `cfgver-endtoend-internals`.
References files (zero listing cost, reachable only via parent bodies):
`cfgver/references/registers.md` (two-world register machinery, from
cfgver-gen-contract-internals/cfgver-endtoend-internals); `cfgver/references/
asm-vocabulary.md` (AST constructor field order, register aliases, and the
backward-branch-immediate convention for hand-authored programs, from
cfgver-new-example).

> **Importing `CFGVer.Verifier` downstream** (the `Require`-vs-`Require Import`
> BlockVer name-clash idiom) also moved to
> `case_study/RiscvPmp/CFGVer/CLAUDE.md`.

> **Current example status** (which programs are verified, parametric-base
> coverage, the `precompute`/`key_schedule_loop2` open gaps) is project state,
> not skill reference — it now lives in the `project_cfgver_state` memory
> file (kept fresher there, since memory is expected to be point-in-time and
> gets revisited/corrected, unlike skill bodies).
