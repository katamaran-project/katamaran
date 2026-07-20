---
name: cfgver-solve-vc
description: >
  Discharging Katamaran CFGVer verification conditions — the vm_compute + solve_vc
  pattern, its residuals, and its failure modes. Use when proving a
  valid_<prog>_cfg_contract / ValidCFGVerifierContract goal, when solve_vc leaves a
  residual (VerificationConditionWithErasure …), when the VC reduces to a bare False,
  when vm_compute on a VC hangs/diverges, or when a `secLeak` GOAL (not hypothesis)
  is left open after an sltu/comparison instruction on private data (e.g. a
  borrow-chain subtraction). Covers the residual→tactic table,
  DebugCFGVerifierContract for inspecting a failing VC, the tight-fuel False, the
  symbolic-bv.of_N divergence, and the comparison-on-private-data gap. This skill
  is the CFGVer OPERATIONAL side (discharging / inspecting / debugging the resulting
  VC); for the framework-level REASON a comparison on secret (NonSyncVal) data forces
  the goal to False or leaves a secLeak open in the first place — the noninterference
  value-model wall, not a fuel/residual issue — see `secret-data-walls`. NOT for
  building the contract itself (cfgver-contracts / cfgver-gen-contract).
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
| `secLeak ?x` left as an open GOAL after `vm_compute. solve_vc.` (not a hypothesis `Hs : secLeak ?x` to `destruct`) | comparison-on-private-data gap — see below, likely not closable per-proof |

## `secLeak` left as a GOAL, not a hypothesis (comparison/relop on private data)

Distinguish this from the destructible-hypothesis pattern (`Hs : secLeak ?x |- _`,
closed via `destruct x as [?|??]; [|destruct Hs]`, used in every `_param`
contract's tail): here the residual is `|- RiscvPmpSignature.secLeak v` for some
free `v : RelVal _` that has NO existing hypothesis about it at all — an
obligation to *prove* `v` is public, not a case to eliminate.

**Root cause:** `solve_vc`'s automation only derives `secLeak (f t1 t2)`
*compositionally*, from `secLeak t1`/`secLeak t2` already holding
(`instprop_formula_secLeak_binop`, `Contracts.v`). There is no rule for "this
relop's two worlds may legitimately disagree, and nothing downstream needs it
to be public" — i.e. no support (yet) for a comparison used as a pure VALUE on
genuinely private operands. Concretely this fires on `SLTU`/`SLT`-family
instructions (RV32's only carry/borrow-detection primitive, e.g. the standard
`sltu`-based borrow chain a compiler emits for any multi-word/64-bit-on-32-bit
subtraction) when their operands are private register/memory values — every
comparison in every other CFGVer example is instead used as an actual (public)
branch predicate, which is a different, already-supported code path.

**What to do:** if the compared value can legitimately be marked public in the
`reg_spec`/`mem_full_spec`, do that — the residual disappears. If it genuinely
must stay private (the whole point of the proof), this is **not** closable by
any known tactic combination; it needs the executor/`solve_vc` model extended
with a rule for "case-split on the relop, then show non-interference holds
either way" (tracked in `TODO.md`'s "Botan CT::Mask / 64-bit-subtraction gap",
hit by `precompute`'s real `uint64_t` form — worked around there by scaling the
data to a native 32-bit word so the subtraction never needs a borrow-chain
comparison at all). Diagnostic path: `rocq_start` at the failing lemma,
`rocq_check` with `vm_compute. solve_vc.`, and read the remaining `Goal N`s'
hypothesis lists — a bare `secLeak v` with `v` unmentioned anywhere above it is
the tell.

## When the VC is `False` (or `solve_vc` can't close it)

1. **Inspect instead of guessing:** state the same contract as
   `DebugCFGVerifierContract c` (a `VerificationCondition` instead of `safeE`),
   `vm_compute`, and read the residual formula.
2. **Tight fuel:** a bare `False` deep in the VC often means fuel is too tight —
   it must exceed the executed step count *with slack* (`cmovznz4` needed 35 for
   29 instructions; exactly 29 produced a misleading `False` that looked like a
   missing `secLeak` fact).
3. **Wrong backward-branch offset, if the program has a hand-authored loop:**
   the exact same misleading-`False` symptom, but with fuel already generous —
   a `BNE`/`BEQ` immediate is relative to *that instruction's own address*, not
   the loop body's total length (`key_schedule_loop2` hit this: `-(N*4)` instead
   of the correct `-((N-1)*4)` sent the taken branch to an unmapped address).
   Not an issue for programs translated via `asm_to_ast.py` (it resolves labels
   automatically) — only for loops hand-authored like `countdown`/
   `countdown_mem`/`key_schedule_loop2`. Full convention + worked examples:
   **`cfgver/references/asm-vocabulary.md`**.
4. **Exit mismatch:** the exit choice checks the contract's exit-*term* table; a
   pc that should exit but matches no exit term fails the branch. Check
   `extra_exit_offs` / `cfg_exits`.
5. **Wrong postcondition/exitCond wiring** in hand-written contracts —
   → **cfgver-contracts** (the ignored-fields subtlety).

## When `vm_compute` itself hangs

A symbolic (non-literal) argument reaching `bv.of_N` at width 32 does not reduce
and `vm_compute` diverges. In parametric-base contracts, keep the base as
`term_var "p"` and apply `bv.of_N` only to concrete offsets.
