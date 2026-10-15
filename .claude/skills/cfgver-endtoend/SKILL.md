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

## Which end-to-end lemma (2026-10-02)

- **`cfg_instrs_endToEnd_gen`** is THE core: data memory anywhere
  (`data_layout_ok`, see **cfgver-memory**). Every other end-to-end lemma is a
  corollary of it.
- **`GenProg.gen_prog_noninterferent`** is the generic whole-program BRIDGE for
  a contract in `gen_prog_contract` form (see **cfgver-gen-contract**,
  "Whole-program generator form"): ImplPre is done once inside; premises are a
  valuation, sync-ness, NoDup, facts, `data_ok`, `data_layout_ok`, the length
  bound, validity. Prefer it for a new example with data or pointer arguments.
- `cfg_instrs_endToEnd` (below, register-only) and `_with_memory`
  (contiguous data) remain for existing callers.

## `cfg_instrs_endToEnd`

A corollary of `cfg_instrs_endToEnd_gen` at `data_specs = []`, so that
program-specific proofs only supply `ImplPre`.

```coq
Lemma cfg_instrs_endToEnd {γ1 γ2 γ1' : RegStore} {μ1 μ2 μ1' : Memory}
  {instrs : list AST} (exit_addr : N) n ws {R} {ι : Valuation R}
  public_registers
  (HpubReg : declare_public_registers γ1 γ2 public_registers)
  (contract : @CFGVerifierContract R)
  (valid_contract : ValidCFGVerifierContract contract)   (* SEALED, Validity.v *)
  (contractInstrs : cfg_instrs contract = instrs)         (* eq_refl *)
  (init_addr : N)                          (* the contract has no load address *)
  (contractPlacement : inst (cfg_placement contract) ι = ty.SyncVal (bv.of_N init_addr))
  (HexitFaith : etable_rel (ty.SyncVal (bv.of_N exit_addr)) (cfg_exit contract) ι)
  (ImplPre : forall `{sailGS2 Σ}, … -∗
      asn.interpret (extend_to_minimal_pre (cfg_precondition contract))
        ι.["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)]) :
  (init_addr + 4 * N.of_nat (length instrs) < lenAddr)%N ->
  mem_has_instrs μ1 (bv.of_N init_addr) ws instrs ->
  mem_has_instrs μ2 (bv.of_N init_addr) ws instrs ->
  (* cur_privilege = Machine and pc = bv.of_N init_addr, in both γ1 and γ2 *) … ->
  ⟨ γ1, μ1 ⟩ -(atPc exit_addr, n)->* ⟨ γ1', μ1' ⟩ ->
  leakage_trace μ1 = leakage_trace μ2 ->
  ∃ γ2' μ2', ⟨ γ2, μ2 ⟩ -(atPc exit_addr, n)->* ⟨ γ2', μ2' ⟩ ∧
             leakage_trace μ1' = leakage_trace μ2'.
```

(Abridged; exact text at `EndToEnd.v`, `Lemma cfg_instrs_endToEnd`.) The exit is
the literal `exit_addr : N`; `atPc exit_addr` (`Noninterference.v`) is `fun v =>
bv.eqb v (bv.of_N exit_addr)`. `HexitFaith` ties it to the contract's one exit
term — for `cfg_exit := exit_of_off p off` discharge it with
`etable_faith_exit_of_off` (`TablesRel.v`), or for a segment with
`seg_exit_table_ok` (`GenCompose.v`).

**No annotation appears here (PLAN-valid-blk-annot.md Phase 4).** Every bridge —
this one, `_with_memory`, `cfg_instrs_verified`/`_safe`(`_with_mem`),
`GenCompose.contract_run`/`seg_run`/`loop_*` — takes only the SEALED
`ValidCFGVerifierContract contract` (`Validity.v`) and states memory over the
plain `list AST`. The annotated list, the raw `cfg_vc`, and block validity live
inside the seal, and are supplied only where the contract is proved valid:
`solve_valid <the example's VC>` for a block-free program, or
`@ValidCFGVerifierContract_intro _ c LV` with a TYPED list
`LV : list (AnnotInstrV blkValid)` (each block carries its own validity), the
VC by `exact` (conversion) and `reflexivity` when it
carries blocks (`Example/CountdownRecResult.cdLink_valid`). There is no `blocksSound` premise
any more.

## Call pattern

```coq
eapply (@cfg_instrs_endToEnd γ1 γ2 γ1' μ1 μ2 μ1'
  instrs (init_addr + 4 * N)%N n ws [ctx] [env]
  [existT ty_xlenbits x1] HpubReg my_cfg_contract
  my_cfg_contract_valid eq_refl init_addr).
  (* eq_refl: contractInstrs *)
(* contractPlacement and HexitFaith are then goals *)
all: try eauto.
```

Live example: `Example/CountdownRecResult.v` (placement by `reflexivity`, exit by
`seg_exit_table_ok`).

`my_cfg_contract` / `valid_my_cfg_contract` are placeholders for a **hand-written**
concrete-base (`Σ = [ctx]`) contract. None of CFGVer's own examples supply one any
more: since the Phase 4.2 parametric migration each `Example/*.v` proves only a
`valid_*_cfg_contract_param` VC and reaches its concrete result as a corollary of the
parametric theorem, so the concrete-base contracts and their VCs were removed as dead
compile time.

- `@` is required: `instrs` is implicit.
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
  valid_jmp_fwd_cfg_contract_gen init_addr eq_refl).
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
