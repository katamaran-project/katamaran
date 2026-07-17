---
name: cfgver-contracts
description: >
  Katamaran CFGVer contracts in general — what a CFGVerifierContract IS and how to
  write one by hand. Use when asking about the contract record and its fields
  (cfg_init_addr, cfg_placement, cfg_exits, cfg_precondition, cfg_instrs,
  cfg_exitCond, cfg_fuel), choosing the logical context Σ ([ctx] concrete vs
  ["p"∷ty_xlenbits] parametric base), why the symbolic VC ignores cfg_init_addr and
  cfg_exitCond, ValidCFGVerifierContract / Valid_CFG_VC / DebugCFGVerifierContract,
  or hand-writing a contract without the generator (as for
  cmovznz4_cfg_contract_param) — including the assertion vocabulary: ↦ᵣ / ↦ₘ
  points-to, asn.exist, secLeakvar (leak permission for public values),
  asn_init_pc, and base-bound formulas. NOT for the gen_contract generator's spec
  lists (cfgver-gen-contract) and NOT for discharging VC residuals (cfgver-solve-vc).
---

# CFGVer contracts in general

What a contract *is* — independent of the `gen_contract` generator
(→ **cfgver-gen-contract**). Definitions in `CFGVer/Contracts.v`.

## The record

```coq
Record CFGVerifierContract {Σ} :=
  MkCFGVerifierContract
  { cfg_init_addr     : N
  ; cfg_placement     : Term Σ ty_xlenbits
  ; cfg_exits         : list (Term Σ ty_xlenbits)
  ; cfg_precondition  : Assertion (Σ ▻ "a" ∷ ty_xlenbits)
  ; cfg_instrs        : list AST
  ; cfg_exitCond      : bv xlenbits -> bool
  ; cfg_fuel          : nat
  }.
```

| Field | Meaning |
|---|---|
| `Σ` | logical context: `[ctx]` for a concrete contract; `["p"∷ty_xlenbits]` for a parametric base (the base is then `term_var "p"`) |
| `cfg_placement` | where the code sits, as a **term**: `term_val … (bv.of_N ia)` concrete, `term_var "p"` parametric |
| `cfg_exits` | exit addresses as **terms** (built by `exits_of_offs` from base-relative offsets) — this is what the symbolic executor's exit choice checks against |
| `cfg_precondition` | `Assertion (Σ ▻ "a"∷ty_xlenbits)` — "a" is the start pc; parametric contracts must also include the base bound `unsigned p + size ≤ lenAddr` here, or fetch bounds are unprovable |
| `cfg_instrs` | the program, a `list AST` placed at `cfg_placement` |
| `cfg_init_addr`, `cfg_exitCond` | **NOT used by the symbolic VC** (source comment on `Valid_CFG_VC`, `Contracts.v`) — carried for the end-to-end statement |

**The ignored-fields subtlety:** the VC dispatches exits against the *term table*
`cfg_exits`, not against `cfg_exitCond`. The two are reconnected only at the
end-to-end stage, by the `HexitOffs` premise of `gen_contract_noninterferent`
(via `etable_faith_exits_of_offs`): every exit term must satisfy `exitCond`. A
hand-written contract whose `cfg_exits` and `cfg_exitCond` disagree will pass the
VC and fail there.

## Validity

```coq
Definition ValidCFGVerifierContract {Σ} (c : @CFGVerifierContract Σ) : Prop :=
  cfg_map c Valid_CFG_VC.
(* Valid_CFG_VC … := safeE (postprocess (CFG_VC_triple p exits P i fl)). *)
```

Discharge pattern: `Proof. vm_compute. solve_vc. Qed.` — residual patterns and
failure modes in **cfgver-solve-vc**.

**Debugging a failing VC:** `DebugCFGVerifierContract c` is the same VC wrapped as
a `VerificationCondition` instead of `safeE` — state it as a `Lemma`, `vm_compute`,
and read the residual instead of guessing.

## Hand-writing a contract: the assertion vocabulary

A hand-written precondition is built from exactly what the generator would emit
(cf. `gen_reg_asn`/`gen_mem_asn` in **cfgver-gen-contract-internals**):

| Assertion | Meaning |
|---|---|
| `r ↦ᵣ t` / `t_addr ↦ₘ t_val` | register / memory-word points-to (terms) |
| `asn.exist "v" ty_xlenbits (…)` | existentially quantified value ("some value") |
| `secLeakvar "v"` | **leak permission**: the value of `"v"` is public — allowed to influence leakage. Its *absence* is what makes a value secret |
| `asn_init_pc t` | the start pc `"a"` equals `t` |
| `asn.formula (formula_relop …)` | pure side conditions — e.g. the parametric base bound `unsigned p + size ≤ lenAddr` |

So: public register = `asn.exist "v" … (r ↦ᵣ term_var "v" ∗ secLeakvar "v")`;
private = the same without `secLeakvar`; pinned = `r ↦ᵣ term_val … v` directly.

Exemplar: `cmovznz4_cfg_contract_param` (`Example/Cmovznz4.v`) — `Σ = ["p"∷ty_xlenbits]`,
placement `term_var "p"`, exits at `bvadd p (of_N off)` terms, precondition with
the base bound plus register/memory assertions. Two rules of thumb:

- Build addresses as `bop.bvadd (term_var "p") (term_val … (bv.of_N off))` — only
  concrete offsets under `bv.of_N`; a symbolic argument to `bv.of_N` makes
  `vm_compute` diverge.
- There is also a notation `{{ P }} i @cfg[ ec , fl ]` for concrete contracts
  at `init_addr`, kept `Local` in `Example/MvSwap.v` (its only user) because it
  turns `{{`/`}}` into lexer keywords that break any other `}}` occurrence.

**Consuming a contract:** the once-and-for-all route is
`gen_contract_noninterferent` (generator contracts, → **cfgver-gen-contract**);
hand-written contracts wire through `cfg_instrs_endToEnd` (→ **cfgver-endtoend**).
