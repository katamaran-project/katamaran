---
name: cfgver-solve-vc
description: >
  Discharging Katamaran CFGVer verification conditions — the vm_compute + solve_vc
  pattern, its residuals, and its failure modes. Use when proving a
  valid_<prog>_cfg_contract / ValidCFGVerifierContract goal, when solve_vc leaves a
  residual (VerificationConditionWithErasure …), when the VC reduces to a bare False,
  or when vm_compute on a VC hangs/diverges. Covers the residual→tactic table,
  DebugCFGVerifierContract for inspecting a failing VC, the tight-fuel False, and
  the symbolic-bv.of_N divergence. NOT for building the contract itself
  (cfgver-contracts / cfgver-gen-contract).
---

# Discharging CFGVer VCs (`vm_compute. solve_vc.`)

The standard discharge is one line:

```coq
Lemma valid_<prog>_cfg_contract : ValidCFGVerifierContract <prog>_cfg_contract.
Proof. vm_compute. solve_vc. Qed.
```

`solve_vc` is the exported Ltac defined in `CFGVer/Contracts.v` (on top of
`RiscvPmpCFGVerifExecutor` helpers); `Require Import …CFGVer.Contracts`
brings it in.

## Residual patterns after `vm_compute`

| Residual | Solution |
|----------|----------|
| `VerificationConditionWithErasure (Erasure.eformula_secLeak [bv 0x0] ∧ ⊤)` | `solve_vc.` |
| `VerificationConditionWithErasure ⊤` | `constructor.` |
| `VerificationConditionWithErasure False` | wrong VC — see below |

## When the VC is `False` (or `solve_vc` can't close it)

1. **Inspect instead of guessing:** state the same contract as
   `DebugCFGVerifierContract c` (a `VerificationCondition` instead of `safeE`),
   `vm_compute`, and read the residual formula.
2. **Tight fuel:** a bare `False` deep in the VC often means fuel is too tight —
   it must exceed the executed step count *with slack* (`cmovznz4` needed 35 for
   29 instructions; exactly 29 produced a misleading `False` that looked like a
   missing `secLeak` fact).
3. **Exit mismatch:** the exit choice checks the contract's exit-*term* table; a
   pc that should exit but matches no exit term fails the branch. Check
   `extra_exit_offs` / `cfg_exits`.
4. **Wrong postcondition/exitCond wiring** in hand-written contracts —
   → **cfgver-contracts** (the ignored-fields subtlety).

## When `vm_compute` itself hangs

A symbolic (non-literal) argument reaching `bv.of_N` at width 32 does not reduce
and `vm_compute` diverges. In parametric-base contracts, keep the base as
`term_var "p"` and apply `bv.of_N` only to concrete offsets.
