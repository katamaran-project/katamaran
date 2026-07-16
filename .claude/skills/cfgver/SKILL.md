---
name: cfgver
description: >
  Index/hub for the Katamaran RISC-V PMP CFG verifier (case_study/RiscvPmp/CFGVer/).
  Use when starting CFGVer work, when the request spans multiple layers, or — the most
  common task — when VERIFYING A NEW EXAMPLE PROGRAM end-to-end (this skill contains
  that step-by-step recipe). Routes to the focused sub-skills: cfgver-executor
  (symbolic executor + VC), cfgver-refinement (concrete mirror + relational lemmas),
  cfgver-rsolve (driving/debugging the rsolve tactic), cfgver-soundness (the chain),
  cfgver-wp2 (semWP2 proof mechanics), cfgver-contracts (specifying programs with
  gen_contract), cfgver-contracts-internals (generator machinery), cfgver-endtoend
  (wiring user guide), cfgver-endtoend-internals (wiring proof internals), and
  cfgver-memory (data-memory infra). If the request clearly matches one of those,
  use it directly instead. Katamaran-specific; generic Rocq/Coq → the rocq skill.
---

# CFGVer — reference hub

Entry point for the CFG verifier (`case_study/RiscvPmp/CFGVer/`). The detailed
reference is split into focused skills (below) so only the relevant one loads.

Compilation order: `Spec.v` → `Verifier.v` → `Examples.v`. When modifying
`Verifier.v`, recompile it with `keep_vo=True` before compiling `Examples.v`.
The `CLAUDE.md` "Common pitfalls" table is always loaded — check it first for a
symptom→fix lookup. For generic Rocq workflow (compile-first iteration, lemma
search, proof repair) use the **rocq** plugin skill.

## Module map — which skill to read

| Skill | Covers | Read when |
|-------|--------|-----------|
| **cfgver-executor** | symbolic executor `sexec_cfg_addr`, gmap instruction store, `ptsto_instrs`, `sblock_verification_condition` | how the verifier decides/executes; VC construction; symbolic-pc errors |
| **cfgver-refinement** | concrete mirror `cexec_cfg_addr`, the `RefineCompat` relation, `rexec_cfg_addr` | reading/extending the relational layer; proving a new relational (ℛ⟦⟧) lemma |
| **cfgver-rsolve** | driving `rsolve`: debug workflow, instance template, divergence/OOM, manual bind pairing | an `rsolve` failure/hang/OOM; writing a `RefineCompat` instance |
| **cfgver-soundness** | the VC → `myWP2_loop` → leakage chain; `WP2_loop` vs `myWP2_loop` | understanding/extending the theorem architecture |
| **cfgver-wp2** | binary WP2 proof mechanics: `semWP2_unfold`, `stm_to_val`, `IVal`, `Result2` (library skill) | a semWP2/adequacy proof is stuck (unreduced match, `env.drop_cat`, `iMod` on a modality-match) |
| **cfgver-contracts** | specifying programs: `reg_spec`/`mem_full_spec` triples, `extra_exit_offs`, `gen_contract`, the 5 premises of `gen_contract_noninterferent` | declaring public/private/pinned registers or memory for a program |
| **cfgver-contracts-internals** | `gen_reg_asn`/`gen_pre` builders, `gen_implpre`, `declare_pub_*` (library skill) | modifying/extending the generator machinery itself |
| **cfgver-endtoend** | `cfg_instrs_endToEnd`, its call pattern, the `ImplPre` obligation | wiring a hand-written contract; debugging `ImplPre` |
| **cfgver-endtoend-internals** | proof bodies of the wiring lemmas, `_with_mem` proof patterns (library skill) | modifying/extending the wiring lemmas themselves |
| **cfgver-memory** | data-memory infra: `interp_mem_with_*`, `instrsAndDataMemory`, `_with_mem` variants | the program reads/writes data memory |

Dependency order: `executor ← refinement ← soundness ← contracts ← endtoend ← memory`.
Library skills (loaded from parents, rarely self-firing): `cfgver-rsolve`,
`cfgver-wp2`, `cfgver-contracts-internals`, `cfgver-endtoend-internals`.
References files (zero listing cost, reachable only via parent bodies):
`cfgver/references/registers.md` (two-world register machinery). The standalone
**gmap-pitfalls** skill covers stdpp-gmap traps (unreducible lookup matches; the
gmap-import Zify rewrite breaking lia) — generic Rocq, not CFGVer-specific.

## Recipe: verifying a new example program end-to-end

The most common CFGVer task. Every existing example (`swap`, `countdown_mem`,
`cmovznz4`, …) follows this shape — copy the closest analogue rather than starting
from scratch.

1. **Instructions.** Translate the RV32I assembly (e.g. Compiler Explorer output of
   `clang -O2 -march=rv32i`) into a `list AST` with
   `case_study/RiscvPmp/CFGVer/tools/asm_to_ast.py` — it tags each entry with its
   source line for auditability. Don't hand-transcribe.
2. **Exit condition + fuel.** Typically `pcOutOfInstrs_exitCond init_addr instrs`;
   fuel must exceed the number of instruction steps actually executed. If control
   flow can exit other than by falling off the end (e.g. a forward branch past the
   block), collect those as `extra_exit_offs`.
3. **Contract.** `gen_contract init_addr reg_specs mem_specs instrs extra_exit_offs
   ec fl` — spec formats and premise details in **cfgver-contracts**.
4. **VC.** `Lemma valid_<prog>_cfg_contract : ValidCFGVerifierContract ….
   Proof. vm_compute. solve_vc. Qed.` Residuals table below.
5. **End lemma.** `<prog>_noninterferent : noninterferent_strong …` by
   `eapply gen_contract_noninterferent;` discharging its **five** premises: NoDup of
   register indices, `HDataAddrs` (data contiguous after code), the length bound,
   `HexitOffs` (exitCond true at fall-through + each extra exit), and the VC from
   step 4.
6. **Axiom hygiene.** `Print Assumptions <prog>_noninterferent.` must show only
   `pure_decode` and `mmioenv` (the model's inherent parameters). Anything else —
   especially `functional_extensionality` — means a proof took a shortcut; fix it.

## Importing CFGVer.Verifier into Examples.v

```coq
(* At top level, after the main Require Import block: *)
From Katamaran Require
     RiscvPmp.CFGVer.Verifier.
```

Then use qualified names (`Katamaran.RiscvPmp.CFGVer.Verifier.foo`). Do NOT
`Require Import` — it causes notation/name conflicts with BlockVer.

## Example status (2026-07-16)

All CFGVer examples compile with **zero `Admitted`**, each with a
`valid_<prog>_cfg_contract` VC and a `<prog>_noninterferent` end lemma, axiom-clean
(`pure_decode` + `mmioenv` only): `swap`, `jumpIfZero`, `jmp_fwd`, `countdown`,
`countdown_mem`, `set_X2_to_42`, `cmovznz4`. Parametric base:
`set_X2_to_42_noninterferent_param` and `cmovznz4_noninterferent_param`
(∀ init_addr); the concrete cmovznz4 lemmas (base 0 and 256) are corollaries of
the parametric one. `valid_jmp_fwd` (BlockVer) stays `Admitted` — BlockVer cannot
handle JAL; intentional.

## `solve_vc` residual patterns

After `vm_compute`, typical residuals and their solutions:

| Residual | Solution |
|----------|----------|
| `VerificationConditionWithErasure (Erasure.eformula_secLeak [bv 0x0] ∧ ⊤)` | `solve_vc.` |
| `VerificationConditionWithErasure ⊤` | `constructor.` |
| `VerificationConditionWithErasure False` | wrong VC — check exitCond or postcondition |

`solve_vc` is from `RiscvPmpBlockVerifExecutor` (imported globally in `Examples.v`).
