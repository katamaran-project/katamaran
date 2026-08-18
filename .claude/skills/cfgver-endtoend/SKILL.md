---
name: cfgver-endtoend
description: >
  Katamaran CFGVer end-to-end wiring (register path) — using cfg_instrs_endToEnd to
  connect a verified contract to the concrete leakage-equivalence theorem for a
  register-only program: its premises (pc/privilege register reads, mem_has_instrs,
  length bound), the eapply call pattern with its implicit-argument traps, and the
  ImplPre proof obligation with its gen_contract patterns (including empty specs).
  Programs built with gen_contract_param / gen_contract_rel* normally use the
  matching gen_contract_noninterferent_param / _rel* bridge instead
  (cfgver-gen-contract); reach for this when wiring a hand-written contract or debugging
  the ImplPre goal. For programs that read/write DATA MEMORY see cfgver-memory
  (the _with_mem / _with_memory variants).
---

# CFGVer end-to-end wiring (register path)

Wires a verified `CFGVerifierContract` to a concrete leakage-equivalence statement
for a program that touches only registers.

**Shortcut for generated contracts:** if the contract came from `gen_contract_param`
or one of the `gen_contract_rel*` builders, you normally never call this directly —
the matching `gen_contract_noninterferent_param` / `_rel*` bridge
(→ **cfgver-gen-contract**) wraps the whole wiring. This skill matters for
hand-written contracts, for understanding/debugging the `ImplPre` obligation, and
for a literal-base `gen_contract` contract: that builder is still live (it has
example and rig users) but its bridge `gen_contract_noninterferent` was **deleted
2026-08-18** as dead, so a concrete-base end theorem must either wire through
`cfg_instrs_endToEnd` here or recover that lemma from git history.

> **Data memory?** For programs that read/write data memory use the
> **cfgver-memory** skill — `cfg_instrs_endToEnd_with_memory` and the `_with_mem`
> lemma variants.

> **Modifying the wiring lemmas themselves** (their internal proofs, the
> double-iFrame idiom, the `_with_mem` proof patterns)? That's
> **cfgver-endtoend-internals**. The register predicates in the premises are
> documented in `.claude/skills/cfgver/references/registers.md`.

## `cfg_instrs_endToEnd`

Bundles adequacy + memory splitting + `cfg_instrs_safe` so that program-specific
proofs only supply `ImplPre`.

```coq
Lemma cfg_instrs_endToEnd {γ1 γ2 γ1' γ2' : RegStore} {μ1 μ2 μ1' μ2' : Memory}
  instrs' exitCond n ws {R} {ι : Valuation R}
  public_registers
  (HpubReg : declare_public_registers γ1 γ2 public_registers)
  (contract : @CFGVerifierContract R)
  (valid_contract : ValidCFGVerifierContract contract)
  (contractInstrs : cfg_instrs contract = instrs')
  (contractExitCond : cfg_exitCond contract = exitCond)
  (ImplPre : forall `{sailGS2 Σ},
      interp_gprs_with_public_registers γ1 γ2 public_registers ∗
      cur_privilege ↦ᵣ ty.SyncVal Machine ∗
      interp_inv_constant_time -∗
      asn.interpret (extend_to_minimal_pre (cfg_precondition contract))
        ι.["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)]) :
  (4 * N.of_nat (length instrs') < lenAddr)%N ->
  mem_has_instrs μ1 (bv.of_N init_addr) ws instrs' ->
  mem_has_instrs μ2 (bv.of_N init_addr) ws instrs' ->
  RiscvPmpProgram.read_register γ1 cur_privilege = Machine ->
  RiscvPmpProgram.read_register γ2 cur_privilege = Machine ->
  RiscvPmpProgram.read_register γ1 pc = bv.of_N init_addr ->
  RiscvPmpProgram.read_register γ2 pc = bv.of_N init_addr ->
  ⟨ γ1, μ1 ⟩ -(exitCond, n)->* ⟨ γ1', μ1' ⟩ ->
  ⟨ γ2, μ2 ⟩ -(exitCond, n)->* ⟨ γ2', μ2' ⟩ ->
  leakage_trace μ1 = leakage_trace μ2 ->
  leakage_trace μ1' = leakage_trace μ2'.
```

There is no `ImplPost` parameter — `CFGVerifierContract` has no postcondition field.

## Call pattern

```coq
eapply (@cfg_instrs_endToEnd γ1 γ2 γ1' γ2' μ1 μ2 μ1' μ2'
  instrs my_exitCond n ws [ctx] [env]
  [existT ty_xlenbits x1] HpubReg my_cfg_contract
  valid_my_cfg_contract eq_refl eq_refl).
all: try eauto.
```

`my_cfg_contract` / `valid_my_cfg_contract` are placeholders for a **hand-written**
concrete-base (`Σ = [ctx]`) contract. None of CFGVer's own examples supply one any
more: since the Phase 4.2 parametric migration each `Example/*.v` proves only a
`valid_*_cfg_contract_param` VC and reaches its concrete result as a corollary of the
parametric theorem, so the concrete-base contracts and their VCs were removed as dead
compile time.

- `@` is required: `Set Implicit Arguments.` makes `instrs'` and `exitCond` implicit
  (they appear in the types of `contractInstrs`/`contractExitCond`).
- **`all: try eauto.` must come BEFORE the `-` bullets** — it discharges the routine
  goals (memory, register reads, execution steps) first, leaving only `ImplPre` and
  the length bound for the focused bullets.

## The `ImplPre` obligation for `gen_contract` contracts

When `contract = gen_contract …` (→ **cfgver-gen-contract**), the goal after `cbn` is a
pair of `⌜P⌝ ∧ emp` fragments (one per precondition conjunct) followed by
`cur_privilege` and `interp_inv_constant_time`.

**Empty specs** pattern:

```coq
assert (HpubReg : declare_public_registers γ1 γ2 []) by constructor.
eapply (@cfg_instrs_endToEnd ... [] HpubReg jmp_fwd_cfg_contract_gen
  valid_jmp_fwd_cfg_contract_gen eq_refl eq_refl).
all: try eauto.
- intros Σ H.
  iIntros "(Hregs & Hpriv & #Hinv)".
  cbn. iFrame "∗ #".                        (* frames Hpriv and Hinv *)
  iSplit; (iSplit; [iPureIntro | done]).    (* decompose ⌜P⌝ ∧ emp per fragment *)
  all: vm_compute; done.
- cbn. by unfold lenAddr.
```

`declare_public_registers γ1 γ2 []` is proved `by constructor` (stdpp's `Forall_nil`
is an iff lemma, not the constructor).
