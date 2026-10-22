---
name: cfgver-gen-contract-internals
description: >
  Internal machinery of the Katamaran CFGVer contract generator — library skill,
  normally reached from cfgver-gen-contract. Consult when MODIFYING or extending the
  generator itself, not when merely specifying a program: the gen_reg_asn / gen_pre /
  gen_mem_asn / gen_mem_pre assertion builders, gen_public_regs and reg_convert, the
  once-and-for-all gen_implpre lemma (Iris register ownership entails the interpreted
  gen_pre), declare_public_registers, and the declare_pub_head_true /
  declare_pub_tail helpers with their implicit-argument and Forall_nil pitfalls.
  For USING gen_contract see cfgver-gen-contract.
---

# Contract-generator internals

How `gen_contract`'s pieces are built and proved. Users specifying a program need
only **cfgver-gen-contract**; this skill is for changing the machinery (new spec forms,
new assertion shapes, extending `gen_implpre`).

Assertion builders and `gen_contract*` live in `GenContract.v`; the
`gen_implpre*` bridge lemmas live in `EndToEnd.v`.

## Assertion builders

```coq
Definition gen_reg_asn {Σ} (s : reg_spec) : Assertion Σ :=
  let '(r, sp) := s in
  match sp with
  | Known v => r ↦ᵣ term_val ty_xlenbits v
  | Public  => asn.exist "v" ty_xlenbits (r ↦ᵣ term_var "v" ∗ secLeakvar "v")
  | Secret  => asn.exist "v" ty_xlenbits (r ↦ᵣ term_var "v")
  end.

Definition gen_pre {Σ} (specs : list reg_spec) : Assertion Σ :=
  List.fold_right (fun s acc => gen_reg_asn s ∗ acc) ⊤ specs.
```

`gen_mem_asn` / `gen_mem_pre` follow the same shape over `mem_cell`
(`N * val_spec word`, address `term_val (bv.of_N a)`) with `↦ₘ`. `r : gpr`
reaches `↦ᵣ` (which takes a `RegIdx`) through the coercion `gpr_idx`
(`Tables.v`). **An Ltac `match goal` pattern does NOT insert that coercion**:
write `asn_regidx_pts (gpr_idx r) ?t`, not `asn_regidx_pts r ?t` (the latter
silently never matches — `GenProg.gen_regs_q_concretize`).
`gen_pre [] = ⊤`, so the empty-spec case degenerates gracefully.

```coq
(* SpecLists.v (proof side; the kernel states regs_sat): the Public entries' registers.  The Iris layer
   (IrisInstanceBinary.v, shared) still wants a sigma list; EndToEnd.v's
   pub_regs_sig converts at the bridges. *)
Definition gen_public_regs (specs : list reg_spec) : list (Reg ty_xlenbits) :=
  base.omap (fun '(r, s) => match s with Public => Some (gpr_reg r) | _ => None end) specs.
```

## `gen_implpre` — the once-and-for-all `ImplPre`

```coq
Lemma gen_implpre `{sailGS2 Σ}
    (specs : list reg_spec) (γ1 γ2 : RegStore)
    {Σ0} (ι : Valuation (Σ0 ▻ "a"∷ty_xlenbits))
    (HpubReg : declare_public_registers γ1 γ2 (gen_public_regs specs))
    (HND : NoDup (map reg_spec_idx specs))          (* reg_spec_idx := gpr_idx ∘ fst *)
    (HInitRegs1 : …) (HInitRegs2 : …) :
  interp_gprs_with_public_registers γ1 γ2 (pub_regs_sig (gen_public_regs specs)) ⊢
  asn.interpret (gen_pre specs) ι.
```

Converts Iris register ownership into the interpreted symbolic `gen_pre`. For public
registers it uses `regPstsTo_sync_is_nonsync` to unify `NonSyncVal v v` into
`SyncVal v`. The `ι` context is generalized over `Σ0` (backward-compatible with
`[ctx]`) so the same lemma serves the parametric-base bridges. A ~130-line Iris
induction — extensions should reuse it (cf. the concretize trick in the `_rel`
bridge) rather than re-prove it.

## The segment generator: one generator, the exit a TERM (2026-10-22)

`GenSegment.gen_seg_contract_at base base_a ex code fl regs extra_pre post`
is the ONE block generator — loops, straight segments and FUNCTIONS alike.
`gen_seg_contract … target …` is its abbreviation at `exit_of_off base target`
(a proof that `cbn`s through it needs `gen_seg_contract_at` in the list too).
A function is `gen_seg_contract_at … (term_var "r") … (secLeakvar "r" ∗ pre) …`
with `X1 ↦ᵣ term_var "r"` in pre: the block is entered from every call site
with whatever X1 holds and resumes at `subst cfg_exit`. Validity:
`GenCompose.blkValid_of_seg_at`, whose ONLY exit-specific premise `Hex` is
"the precondition makes the exit a SyncVal" (`etable_rel`), discharged by
`seg_exit_sync_off` (offset exit, from the placement) or `seg_exit_sync_pub`
(a leading `secLeak ex_a` in extra_pre). `blkValid_of_loop_seg` is the offset
corollary. Worked case: `Example/Rsa/RsaSpikeSub.v` (`br_i31_sub`). The
model's JALR is `pc := rs1 + imm` (no `& ~1`), and `is_exit` is syntactic, so
a function's VC needs no "return address outside the code" premise.

A NON-LEAF function (worked case `Example/Rsa/RsaSpikeSub2.v`, a caller with
a frame and a tail call): its `code` is ITSELF AND ITS CALLEES as linked —
a block's table must hold every pc its run reaches, and a callee is reached
through a block on the callee's first instruction, so it must be in the
table. Pin `sp` and the callee-saved `s_i` to the SAME logic variable in pre
and post (that is what lets the caller keep its pointers across the call),
and own the frame as `gen_data_at (t_add sp (-16)) [DCell Secret; …]` — the
generator's cell form, so a whole-program `gen_prog_contract` stating
`DPtr (sp − 16)` + the same cells hands them over unchanged. A tail call's
block exit is the caller's own `r` reloaded by `lw ra`; that only matches
the caller's exit because `peval` drops the same-width `sext` every `lw`
produces (`PartialEvaluation.peval_sext`, 2026-10-22). Without it the
symptom is `"sexec_cfg_addr: no instruction key matches this pc term"` with
`secLeak (sext r)` in the dumped path condition.

## Register machinery

The two-world register predicates `gen_implpre` builds on
(`declare_public_registers`, `interp_gprs_with_(public_)registers`,
`something_registers`, `regPstsTo_sync_is_nonsync`, the `declare_pub_*` helpers and
their pitfalls) are documented in `.claude/skills/cfgver/references/registers.md` —
read that file when working on this layer.
