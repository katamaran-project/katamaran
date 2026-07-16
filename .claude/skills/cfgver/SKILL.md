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

Compilation order: `Spec.v` → `Verifier.v` → `Examples.v`. When modifying
`Verifier.v`, recompile it with `keep_vo=True` before compiling `Examples.v`.
For generic Rocq workflow (compile-first iteration, lemma search, proof repair)
use the **rocq** plugin skill; generic pitfalls live in **rocq-pitfalls**,
**bv-pitfalls**, **gmap-pitfalls**, **iris-proofmode**.

## Module map — which skill to read

| Skill | Covers | Read when |
|-------|--------|-----------|
| **cfgver-new-example** | the 6-step recipe: asm → contract → VC → end lemma → axiom check | verifying/adding a new program (most common task) |
| **cfgver-executor** | symbolic executor `sexec_cfg_addr`, gmap instruction store, `ptsto_instrs`, `sblock_verification_condition` | how the verifier decides/executes; VC construction; symbolic-pc errors |
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
`cfgver/references/registers.md` (two-world register machinery).

## Importing CFGVer.Verifier into Examples.v

```coq
(* At top level, after the main Require Import block: *)
From Katamaran Require
     RiscvPmp.CFGVer.Verifier.
```

Then use qualified names (`Katamaran.RiscvPmp.CFGVer.Verifier.foo`). Do NOT
`Require Import` — it clashes with BlockVer's identically-named definitions.

> **BlockVer-contingent.** This idiom exists only because BlockVer shares names
> with CFGVer. Once BlockVer is consolidated away (see TODO.md cleanup items),
> switch `Examples.v` to a plain `Require Import` and delete this note.

## Example status (2026-07-16)

All CFGVer examples compile with **zero `Admitted`**, each with a
`valid_<prog>_cfg_contract` VC and a `<prog>_noninterferent` end lemma, axiom-clean
(`pure_decode` + `mmioenv` only): `swap`, `jumpIfZero`, `jmp_fwd`, `countdown`,
`countdown_mem`, `set_X2_to_42`, `cmovznz4`. Parametric base:
`set_X2_to_42_noninterferent_param` and `cmovznz4_noninterferent_param`
(∀ init_addr); the concrete cmovznz4 lemmas (base 0 and 256) are corollaries of
the parametric one. `valid_jmp_fwd` (BlockVer) stays `Admitted` — BlockVer cannot
handle JAL; intentional.
