(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel, Dominique Devriese, Sander Huyghebaert  *)
(* All rights reserved.                                                       *)
(*                                                                            *)
(* Redistribution and use in source and binary forms, with or without         *)
(* modification, are permitted provided that the following conditions are     *)
(* met:                                                                       *)
(*                                                                            *)
(* 1. Redistributions of source code must retain the above copyright notice,  *)
(*    this list of conditions and the following disclaimer.                   *)
(*                                                                            *)
(* 2. Redistributions in binary form must reproduce the above copyright       *)
(*    notice, this list of conditions and the following disclaimer in the     *)
(*    documentation and/or other materials provided with the distribution.    *)
(*                                                                            *)
(* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS        *)
(* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED  *)
(* TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR *)
(* PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR          *)
(* CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,      *)
(* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,        *)
(* PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR         *)
(* PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF     *)
(* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING       *)
(* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS         *)
(* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.               *)
(******************************************************************************)


(* ========================================================================= *)
(* EndToEnd.v — generic end-to-end wiring.                                   *)
(*                                                                           *)
(* From a ValidCFGVerifierContract to noninterferent_strong: the             *)
(* cfg_instrs_* contract lemmas, the gen_implpre / gen_implpre_mem bridges   *)
(* from machine-level initialization to generated preconditions, the         *)
(* cfg_instrs_endToEnd(_with_memory) wiring, and the                         *)
(* gen_contract_noninterferent_{param,rel,rel_classed,rel_bytes}[_simple]     *)
(* theorems that Results.v                                                   *)
(* instantiates per example.                                                 *)
(* ========================================================================= *)

From Coq Require Import
     ZArith.ZArith
     Lists.List
     micromega.Lia
     Strings.String.
From Katamaran Require Import
     Notations
     Bitvector
     Semantics
     RiscvPmp.CFGVer.Spec
     RiscvPmp.Machine
     RiscvPmp.Sig.
From stdpp Require Import gmap.
From Katamaran Require Import
     RiscvPmp.CFGVer.Verifier
     RiscvPmp.CFGVer.VerifierRel
     RiscvPmp.CFGVer.SpecIris
     RiscvPmp.CFGVer.TablesRel
     RiscvPmp.CFGVer.Noninterference
     RiscvPmp.CFGVer.Tables
     RiscvPmp.CFGVer.Contracts
     RiscvPmp.CFGVer.GenContract
     RiscvPmp.CFGVer.Adequacy.
From iris.base_logic Require Import lib.gen_heap lib.iprop invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac big_op.
From iris.program_logic Require weakestpre adequacy.
From iris.proofmode Require string_ident tactics.
From stdpp Require namespaces.
From Equations Require Import Equations.

Import RiscvPmpProgram.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import bv.notations.
Import env.notations.
Import ListNotations.

Import RiscvPmpCFGVerifExecutor.
Import Assembly.
Import RiscvPmp.Sig.
Import iris.proofmode.tactics.
Import iris.proofmode.tactics.
Import IrisInstanceBinary.
Import RiscvPmpIrisInstance2.
Import RiscvPmpSemantics.
Import RiscvPmpIrisAdeqParams2.
Import SmallStepNotations.
Import IrisModelBinary.RiscvPmpIrisBase2.
Import iris.algebra.excl.
Import iris.algebra.gmap.
Import IrisModel.RiscvPmpIrisBase.

  Definition cfg_instrs_pre `{sailGS2 Σ} instrs γ1 γ2 : iProp Σ :=
    own_regstore2 γ1 γ2 ∗
      Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs
        (* MEMORY holds instructions, not annotations.  `ai_instr <$> <map>`
           rather than `instrs_of_list _ (strip _)` so these five sites match
           Adequacy.v's soundness lemmas SYNTACTICALLY — Adequacy has no choice
           in the matter, since its `instrs` is a gmap and cannot say `strip`.
           instrsMemory / intro_ptsto_instrs produce the OTHER form, so the
           bridge (Tables.v's fmap_instrs_of_list) is applied where those two
           meet, inside cfg_instrs_endToEnd*.  Both directions cost exactly two
           rewrites; this one keeps the five statements uniform with
           Adequacy. *)
        (ai_instr <$> instrs_of_list (bv.of_N init_addr) instrs) ∗
      interp_inv_constant_time.

  Definition cfg_instrs_contract `{sailGS2 Σ} exitCond instrs γ1 γ2 :=
    (cfg_instrs_pre instrs γ1 γ2 -∗ exitCond_WP2_loop exitCond)%I.

  Lemma cfg_instrs_verified `{sailGS2 Σ} instrs' exitCond γ1 γ2 R (ι : Valuation R)
    (contract : @CFGVerifierContract R)
    (valid_contract : ValidCFGVerifierContract contract)
    (init_addr : N)    (contractInitAddr : cfg_init_addr contract = init_addr)
    (contractInstrs : cfg_instrs contract = instrs')
    (contractExitCond : cfg_exitCond contract = exitCond)
    (contractPlacement : inst (T := fun Σ => Term Σ ty_xlenbits) (cfg_placement contract) ι
                      = ty.SyncVal (@bv.of_N xlenbits init_addr))
    (Hleninstrs : (init_addr + 4 * N.of_nat (length instrs') < lenAddr)%N)
    (HexitsFaith : Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx R)
                     exitCond (cfg_exits contract) ι)
    (ImplPre : interp_gprs_with_registers γ1 γ2 ∗
               cur_privilege ↦ᵣ ty.SyncVal Machine ∗
               interp_inv_constant_time -∗
               asn.interpret (extend_to_minimal_pre (cfg_precondition contract))
                 ι.["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)]) :
    RiscvPmpProgram.read_register γ1 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ2 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ1 pc = (bv.of_N init_addr) ->
    RiscvPmpProgram.read_register γ2 pc = (bv.of_N init_addr) ->
    ⊢ own_regstore2 γ1 γ2 ∗
      Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs
        (ai_instr <$> instrs_of_list (bv.of_N init_addr) instrs') ∗
      interp_inv_constant_time
    -∗ exitCond_WP2_loop exitCond.
  Proof.
    iIntros (γ1curpriv γ2curpriv γ1pc γ2pc) "Hpre".
    iDestruct "Hpre" as "(Hregs & Hinstrs & #Hinv)".
    cbn.
    iDestruct "Hregs" as "(Hpc & Hnpc & Hstatus & Htvec & Hcause & Hepc & Hpriv & Hregs)".
    rewrite γ1curpriv γ1pc γ2curpriv γ2pc.
    rewrite !regPstsTo_sync_is_nonsync.
    unfold exitCond_WP2_loop.
    destruct contract.
    cbn in valid_contract, contractInitAddr, contractInstrs, contractExitCond, contractPlacement,
      HexitsFaith, ImplPre.
    subst cfg_init_addr cfg_instrs cfg_exitCond.
    unfold Valid_CFG_VC, CFG_VC_triple in valid_contract.
    assert (Hif : Katamaran.RiscvPmp.CFGVer.VerifierRel.itable_rel (w := wlctx R)
                    (instrs_of_list (bv.of_N init_addr) instrs')
                    (table_of_list cfg_placement 0 instrs') ι).
    { apply itable_faith_of_list; [exact contractPlacement|].
      apply table_bound_of_lenAddr, Hleninstrs. }
    iApply (sound_scfg_verification_condition_myWP2
              valid_contract _ Hif HexitsFaith
              $! (SyncVal (bv.of_N init_addr))
              with "[Hpc Hnpc Hstatus Htvec Hcause Hepc Hpriv Hregs Hinstrs]").
    - iSplitL "Hpriv Hregs".
      + iApply ImplPre. iFrame "Hinv Hpriv".
        rewrite gprs_with_registers_equiv. cbn.
        repeat (iDestruct "Hregs" as "($ & Hregs)").
      + iSplit. { done. }
        iFrame.
    (* `& _` absorbs the re-threaded exit assertion (Adequacy.v,
         sound_cexec_triple_addr_myWP2).  These callers want only pc-in-exit,
         and CFG_VC_triple still passes a trivial post, so there is nothing to
         use here — but the conjunct has to be introduced. *)
    - iIntros (an) "(%Hexit & Hpc & Hnpc & Hinstrs & _)".
      destruct an as [v | v1 v2].
      + cbn in Hexit. iExists v. iFrame "Hpc". iPureIntro. rewrite Hexit. exact I.
      + contradiction.
  Qed.

  Lemma cfg_instrs_safe `{sailGS2 Σ} instrs' exitCond γ1 γ2 {R} {ι : Valuation R}
    (contract : @CFGVerifierContract R)
    (valid_contract : ValidCFGVerifierContract contract)
    (init_addr : N)    (contractInitAddr : cfg_init_addr contract = init_addr)
    (contractInstrs : cfg_instrs contract = instrs')
    (contractExitCond : cfg_exitCond contract = exitCond)
    (contractPlacement : inst (T := fun Σ => Term Σ ty_xlenbits) (cfg_placement contract) ι
                      = ty.SyncVal (@bv.of_N xlenbits init_addr))
    (Hleninstrs : (init_addr + 4 * N.of_nat (length instrs') < lenAddr)%N)
    (HexitsFaith : Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx R)
                     exitCond (cfg_exits contract) ι)
    (ImplPre : interp_gprs_with_registers γ1 γ2 ∗
               cur_privilege ↦ᵣ ty.SyncVal Machine ∗
               interp_inv_constant_time -∗
               asn.interpret (extend_to_minimal_pre (cfg_precondition contract))
                 ι.["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)]) :
    RiscvPmpProgram.read_register γ1 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ2 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ1 pc = (bv.of_N init_addr) ->
    RiscvPmpProgram.read_register γ2 pc = (bv.of_N init_addr) ->
    ⊢ own_regstore2 γ1 γ2 ∗
      Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs
        (ai_instr <$> instrs_of_list (bv.of_N init_addr) instrs') ∗
      interp_inv_constant_time
    -∗ exitCond_WP2_loop exitCond.
  Proof.
    iIntros (γ1curpriv γ2curpriv γ1pc γ2pc) "H".
    iApply cfg_instrs_verified; eauto.
  Qed.

  Lemma cfg_instrs_verified_with_mem `{sailGS2 Σ} instrs' exitCond γ1 γ2
    {R} {ι : Valuation R}
    (data_specs : list mem_spec) (μ1 μ2 : Memory)
    (contract : @CFGVerifierContract R)
    (valid_contract : ValidCFGVerifierContract contract)
    (init_addr : N)    (contractInitAddr : cfg_init_addr contract = init_addr)
    (contractInstrs : cfg_instrs contract = instrs')
    (contractExitCond : cfg_exitCond contract = exitCond)
    (contractPlacement : inst (T := fun Σ => Term Σ ty_xlenbits) (cfg_placement contract) ι
                      = ty.SyncVal (@bv.of_N xlenbits init_addr))
    (Hleninstrs : (init_addr + 4 * N.of_nat (length instrs') < lenAddr)%N)
    (HexitsFaith : Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx R)
                     exitCond (cfg_exits contract) ι)
    (ImplPre : interp_gprs_with_registers γ1 γ2 ∗
               interp_mem_with_public_memory μ1 μ2 data_specs ∗
               cur_privilege ↦ᵣ ty.SyncVal Machine ∗
               interp_inv_constant_time -∗
               asn.interpret (extend_to_minimal_pre (cfg_precondition contract))
                 ι.["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)]) :
    RiscvPmpProgram.read_register γ1 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ2 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ1 pc = (bv.of_N init_addr) ->
    RiscvPmpProgram.read_register γ2 pc = (bv.of_N init_addr) ->
    ⊢ own_regstore2 γ1 γ2 ∗
      Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs
        (ai_instr <$> instrs_of_list (bv.of_N init_addr) instrs') ∗
      interp_mem_with_public_memory μ1 μ2 data_specs ∗
      interp_inv_constant_time
    -∗ exitCond_WP2_loop exitCond.
  Proof.
    iIntros (γ1curpriv γ2curpriv γ1pc γ2pc) "Hpre".
    iDestruct "Hpre" as "(Hregs & Hinstrs & Hmem & #Hinv)".
    cbn.
    iDestruct "Hregs" as
      "(Hpc & Hnpc & Hstatus & Htvec & Hcause & Hepc & Hpriv & Hregs)".
    rewrite γ1curpriv γ1pc γ2curpriv γ2pc.
    rewrite !regPstsTo_sync_is_nonsync.
    unfold exitCond_WP2_loop.
    destruct contract.
    cbn in valid_contract, contractInitAddr, contractInstrs, contractExitCond, contractPlacement,
      HexitsFaith, ImplPre.
    subst cfg_init_addr cfg_instrs cfg_exitCond.
    unfold Valid_CFG_VC, CFG_VC_triple in valid_contract.
    assert (Hif : Katamaran.RiscvPmp.CFGVer.VerifierRel.itable_rel (w := wlctx R)
                    (instrs_of_list (bv.of_N init_addr) instrs')
                    (table_of_list cfg_placement 0 instrs') ι).
    { apply itable_faith_of_list; [exact contractPlacement|].
      apply table_bound_of_lenAddr, Hleninstrs. }
    iApply (sound_scfg_verification_condition_myWP2
              valid_contract _ Hif HexitsFaith
              $! (SyncVal (bv.of_N init_addr))
              with "[Hpc Hnpc Hstatus Htvec Hcause Hepc Hpriv Hregs Hinstrs Hmem]").
    - iSplitL "Hpriv Hregs Hmem".
      + iApply ImplPre. iFrame "Hinv Hpriv Hmem".
        rewrite gprs_with_registers_equiv. cbn.
        repeat (iDestruct "Hregs" as "($ & Hregs)").
      + iSplit. { done. }
        iFrame.
    (* `& _` absorbs the re-threaded exit assertion (Adequacy.v,
         sound_cexec_triple_addr_myWP2).  These callers want only pc-in-exit,
         and CFG_VC_triple still passes a trivial post, so there is nothing to
         use here — but the conjunct has to be introduced. *)
    - iIntros (an) "(%Hexit & Hpc & Hnpc & Hinstrs & _)".
      destruct an as [v | v1 v2].
      + cbn in Hexit. iExists v. iFrame "Hpc". iPureIntro. rewrite Hexit. exact I.
      + contradiction.
  Qed.

  Lemma cfg_instrs_safe_with_mem `{sailGS2 Σ} instrs' exitCond γ1 γ2
    {R} {ι : Valuation R}
    (data_specs : list mem_spec) (μ1 μ2 : Memory)
    (contract : @CFGVerifierContract R)
    (valid_contract : ValidCFGVerifierContract contract)
    (init_addr : N)    (contractInitAddr : cfg_init_addr contract = init_addr)
    (contractInstrs : cfg_instrs contract = instrs')
    (contractExitCond : cfg_exitCond contract = exitCond)
    (contractPlacement : inst (T := fun Σ => Term Σ ty_xlenbits) (cfg_placement contract) ι
                      = ty.SyncVal (@bv.of_N xlenbits init_addr))
    (Hleninstrs : (init_addr + 4 * N.of_nat (length instrs') < lenAddr)%N)
    (HexitsFaith : Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx R)
                     exitCond (cfg_exits contract) ι)
    (ImplPre : interp_gprs_with_registers γ1 γ2 ∗
               interp_mem_with_public_memory μ1 μ2 data_specs ∗
               cur_privilege ↦ᵣ ty.SyncVal Machine ∗
               interp_inv_constant_time -∗
               asn.interpret (extend_to_minimal_pre (cfg_precondition contract))
                 ι.["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)]) :
    RiscvPmpProgram.read_register γ1 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ2 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ1 pc = (bv.of_N init_addr) ->
    RiscvPmpProgram.read_register γ2 pc = (bv.of_N init_addr) ->
    ⊢ own_regstore2 γ1 γ2 ∗
      Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs
        (ai_instr <$> instrs_of_list (bv.of_N init_addr) instrs') ∗
      interp_mem_with_public_memory μ1 μ2 data_specs ∗
      interp_inv_constant_time
    -∗ exitCond_WP2_loop exitCond.
  Proof.
    iIntros (γ1curpriv γ2curpriv γ1pc γ2pc) "H".
    iApply cfg_instrs_verified_with_mem; eauto.
  Qed.

    Lemma something_registers `{sailGS2 Σ} {γ1 γ2} {public_registers : list {x : Ty & Reg x}}
      (HpubReg : declare_public_registers γ1 γ2 public_registers)
      : interp_gprs_with_registers γ1 γ2 ⊣⊢ interp_gprs_with_public_registers γ1 γ2 public_registers.
    Proof.
      unfold interp_gprs_with_public_registers, interp_gprs_with_registers, interp_ptsreg_with_public_registers, interp_ptsreg_with_registers.
      iSplit;
        iApply big_sepS_mono;
        intros x Hx;
        destruct (reg_convert x); auto.
    Qed.

  (* ------------------------------------------------------------------ *)
  (* Public memory equivalence: analogous to something_registers         *)
  (* ------------------------------------------------------------------ *)

  (* When declare_public_memory holds, the all-NonSyncVal representation
     interp_mem_with_memory is equivalent to interp_mem_with_public_memory.
     Proof: walk the spec list; for public entries use ptstomem_sync_is_nonsync
     (worlds agree by HpubMem so NonSyncVal w w = SyncVal w). *)
  Lemma something_memory `{sailGS2 Σ} μ1 μ2 (specs : list mem_spec)
      (HpubMem : declare_public_memory μ1 μ2 (gen_public_addrs specs)) :
    interp_mem_with_memory μ1 μ2 specs ⊣⊢
    interp_mem_with_public_memory μ1 μ2 specs.
  Proof.
    unfold interp_mem_with_memory, interp_mem_with_public_memory.
    iApply big_sepL_proper.
    intros k [a pub] Hspec.
    destruct pub; [|done].
    rewrite <- ptstomem_sync_is_nonsync.
    (* Need: get_word μ1 a = get_word μ2 a, i.e., a ∈ gen_public_addrs specs *)
    assert (Heq : get_word μ1 a = get_word μ2 a).
    { unfold declare_public_memory in HpubMem.
      rewrite Forall_forall in HpubMem.
      apply HpubMem.
      unfold gen_public_addrs.
      apply elem_of_list_omap.
      exists (a, true). split; [|done].
      now apply elem_of_list_lookup_2 with k. }
    rewrite Heq. done.
  Qed.

  (* Helper lemmas for declare_public_memory, analogous to the register ones *)
  Lemma declare_pub_mem_head_true a rest μ1 μ2 :
    declare_public_memory μ1 μ2 (gen_public_addrs ((a, true) :: rest)) →
    get_word μ1 a = get_word μ2 a.
  Proof.
    unfold declare_public_memory, gen_public_addrs. cbn.
    rewrite Forall_cons. tauto.
  Qed.

  Lemma declare_pub_mem_tail a pub rest μ1 μ2 :
    declare_public_memory μ1 μ2 (gen_public_addrs ((a, pub) :: rest)) →
    declare_public_memory μ1 μ2 (gen_public_addrs rest).
  Proof.
    unfold declare_public_memory, gen_public_addrs. cbn.
    destruct pub; cbn; [rewrite Forall_cons; tauto | done].
  Qed.

  (* ------------------------------------------------------------------ *)
  (* gen_implpre: once-and-for-all ImplPre for gen_contract              *)
  (* (placed here: needs declare_public_registers + regPstsTo_sync)     *)
  (* ------------------------------------------------------------------ *)

  Lemma gen_reg_asn_of_ptsreg `{sailGS2 Σ}
      (r : RegIdx) (pub : bool) (opt_v : option (Val ty_xlenbits))
      (γ1 γ2 : RegStore)
      {Σ0} (ι : Valuation (Σ0 ▻ "a"∷ty_xlenbits))
      (Heq : pub = true → opt_v = None →
             ∀ x, reg_convert r = Some x →
               read_register γ1 x = read_register γ2 x)
      (HInit : ∀ v x, opt_v = Some v →
                      reg_convert r = Some x →
                      read_register γ1 x = v ∧ read_register γ2 x = v) :
    interp_ptsreg_with_registers r γ1 γ2 ⊢
    asn.interpret (gen_reg_asn (r, pub, opt_v)) ι.
  Proof.
    unfold interp_ptsreg_with_registers, gen_reg_asn.
    destruct opt_v as [v|].
    - destruct (reg_convert r) as [x|] eqn:Hrc.
      + specialize (HInit v x eq_refl eq_refl) as [Hv1 Hv2].
        rewrite Hv1. rewrite Hv2.
        unfold reg_pointsTo21.
        rewrite regPstsTo_sync_is_nonsync.
        iIntros "Hr".
        unfold asn_regidx_pts. rewrite Hrc. cbn. iExact "Hr".
      + iIntros "_".
        unfold asn_regidx_pts. rewrite Hrc. cbn. done.
    - destruct (reg_convert r) as [x|] eqn:Hrc.
      + destruct pub.
        * specialize (Heq eq_refl eq_refl x eq_refl) as Hval.
          rewrite <- Hval.
          unfold reg_pointsTo21.
          rewrite regPstsTo_sync_is_nonsync.
          iIntros "Hr".
          iExists (SyncVal (read_register γ1 x)).
          unfold asn_regidx_pts. rewrite Hrc. cbn. iFrame. done.
        * iIntros "Hr".
          iExists (NonSyncVal (read_register γ1 x) (read_register γ2 x)).
          unfold asn_regidx_pts. rewrite Hrc. cbn. iExact "Hr".
      + iIntros "_". iExists (SyncVal bv.zero).
        unfold asn_regidx_pts. rewrite Hrc.
        destruct pub; cbn; done.
  Qed.

  Lemma declare_pub_head_true r x opt_v rest γ1 γ2 :
    reg_convert r = Some x →
    declare_public_registers γ1 γ2 (gen_public_regs ((r, true, opt_v) :: rest)) →
    read_register γ1 x = read_register γ2 x.
  Proof.
    intros Hrc Hpub.
    unfold declare_public_registers, gen_public_regs in Hpub.
    cbn in Hpub. rewrite Hrc in Hpub. cbn in Hpub.
    rewrite Forall_cons in Hpub. exact (proj1 Hpub).
  Qed.

  Lemma declare_pub_tail r pub opt_v rest γ1 γ2 :
    declare_public_registers γ1 γ2 (gen_public_regs ((r, pub, opt_v) :: rest)) →
    declare_public_registers γ1 γ2 (gen_public_regs rest).
  Proof.
    intros Hpub.
    unfold declare_public_registers, gen_public_regs in Hpub |-*.
    cbn in Hpub |-*.
    destruct pub.
    - destruct (reg_convert r); cbn in Hpub |-*;
        [rewrite Forall_cons in Hpub; exact (proj2 Hpub) | exact Hpub].
    - exact Hpub.
  Qed.

  Lemma declare_init_tail_regs r pub opt_v rest γ :
    declare_init_registers γ (gen_init_regs ((r, pub, opt_v) :: rest)) →
    declare_init_registers γ (gen_init_regs rest).
  Proof.
    unfold declare_init_registers, gen_init_regs. cbn.
    destruct opt_v as [v|].
    - destruct (reg_convert r) as [x|]; cbn.
      + rewrite Forall_cons. tauto.
      + auto.
    - auto.
  Qed.

  Lemma gen_implpre_inner `{sailGS2 Σ}
      (specs : list reg_spec) (γ1 γ2 : RegStore)
      {Σ0} (ι : Valuation (Σ0 ▻ "a"∷ty_xlenbits))
      (HpubReg : declare_public_registers γ1 γ2 (gen_public_regs specs))
      (HND : NoDup (map reg_spec_idx specs))
      (HInitRegs1 : declare_init_registers γ1 (gen_init_regs specs))
      (HInitRegs2 : declare_init_registers γ2 (gen_init_regs specs))
      (S : gset RegIdx)
      (HS : ∀ s, s ∈ specs → reg_spec_idx s ∈ S) :
    ([∗ set] r ∈ S, interp_ptsreg_with_registers r γ1 γ2) ⊢
    asn.interpret (gen_pre specs) ι.
  Proof.
    iInduction specs as [|[[r pub] opt_v] rest] "IH"
        forall (HpubReg HND HInitRegs1 HInitRegs2 S HS).
    - simpl. iIntros "_". done.
    - simpl gen_pre. simpl asn.interpret.
      rewrite NoDup_cons in HND. destruct HND as [Hnotin HND].
      iIntros "H".
      iDestruct (big_sepS_delete with "H") as "[Hr Hrest]".
      { apply HS. apply elem_of_cons. left. done. }
      iSplitL "Hr".
      + iApply gen_reg_asn_of_ptsreg; [| |iExact "Hr"].
        * intros Hpub Hnone x Hrc. subst pub.
          by eapply declare_pub_head_true.
        * intros v x Hsome Hrc.
          split.
          -- unfold declare_init_registers, gen_init_regs in HInitRegs1.
             cbn in HInitRegs1. rewrite Hsome in HInitRegs1. rewrite Hrc in HInitRegs1. cbn in HInitRegs1.
             apply Forall_inv in HInitRegs1. exact HInitRegs1.
          -- unfold declare_init_registers, gen_init_regs in HInitRegs2.
             cbn in HInitRegs2. rewrite Hsome in HInitRegs2. rewrite Hrc in HInitRegs2. cbn in HInitRegs2.
             apply Forall_inv in HInitRegs2. exact HInitRegs2.
      + iApply ("IH" $!
                  (declare_pub_tail r pub opt_v rest HpubReg)
                  HND
                  (declare_init_tail_regs r pub opt_v rest HInitRegs1)
                  (declare_init_tail_regs r pub opt_v rest HInitRegs2)
                  (S ∖ {[r]}) with "[] [Hrest]").
        * iPureIntro.
          intros s Hs.
          rewrite elem_of_difference.
          split.
          -- apply HS. rewrite elem_of_cons. by right.
          -- rewrite elem_of_list_In in Hs.
             apply (in_map reg_spec_idx) in Hs.
             rewrite <- elem_of_list_In in Hs.
             intro Hcontr. rewrite elem_of_singleton in Hcontr.
             rewrite Hcontr in Hs. by apply Hnotin in Hs.
        * cbn. iFrame.
  Qed.

  Lemma gen_implpre `{sailGS2 Σ}
      (specs : list reg_spec) (γ1 γ2 : RegStore)
      {Σ0} (ι : Valuation (Σ0 ▻ "a"∷ty_xlenbits))
      (HpubReg : declare_public_registers γ1 γ2 (gen_public_regs specs))
      (HND : NoDup (map reg_spec_idx specs))
      (HInitRegs1 : declare_init_registers γ1 (gen_init_regs specs))
      (HInitRegs2 : declare_init_registers γ2 (gen_init_regs specs)) :
    interp_gprs_with_public_registers γ1 γ2 (gen_public_regs specs) ⊢
    asn.interpret (gen_pre specs) ι.
  Proof.
    rewrite <- (something_registers HpubReg).
    unfold interp_gprs_with_registers.
    apply gen_implpre_inner;
      [exact HpubReg | exact HND | exact HInitRegs1 | exact HInitRegs2 |].
    intros s _. unfold reg_file.
    apply elem_of_list_to_set, bv.finite.elem_of_enum.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* gen_implpre_mem: once-and-for-all ImplPre for memory               *)
  (* Analogous to gen_implpre for registers.                            *)
  (* ------------------------------------------------------------------ *)

  Lemma declare_init_mem_tail
      (a : Val ty_xlenbits) is_pub opt_v rest μ :
    declare_init_memory μ (gen_init_mem ((a, is_pub, opt_v) :: rest)) →
    declare_init_memory μ (gen_init_mem rest).
  Proof.
    unfold declare_init_memory, gen_init_mem. cbn.
    destruct opt_v as [v|].
    - rewrite Forall_cons. tauto.
    - auto.
  Qed.

  (* Per-entry helper: converts Iris ownership of one entry in
     interp_mem_with_public_memory into its symbolic gen_mem_asn
     interpretation.  HInitMem1/2 supply the init value when opt_v = Some. *)
  Lemma gen_mem_asn_of_ptstomem `{sailGS2 Σ}
      (a : Val ty_xlenbits) (is_pub : bool)
      (opt_v : option (Val ty_xlenbits))
      (μ1 μ2 : Memory)
      {Σ0} (ι : Valuation (Σ0 ▻ "a"∷ty_xlenbits))
      (HInitMem1 : ∀ v, opt_v = Some v → get_word μ1 a = v)
      (HInitMem2 : ∀ v, opt_v = Some v → get_word μ2 a = v) :
    (if is_pub
     then interp_ptstomem (width := 4) (SyncVal a) (SyncVal (get_word μ1 a))
     else interp_ptstomem (width := 4) (SyncVal a)
            (NonSyncVal (get_word μ1 a) (get_word μ2 a)))
    ⊢ asn.interpret (gen_mem_asn (a, is_pub, opt_v)) ι.
  Proof.
    unfold gen_mem_asn.
    destruct opt_v as [v|]; destruct is_pub; cbn.
    - have Hv1 := HInitMem1 v eq_refl. rewrite Hv1.
      cbn [ty.valToRelVal]. iIntros "H". iExact "H".
    - have Hv1 := HInitMem1 v eq_refl. have Hv2 := HInitMem2 v eq_refl.
      rewrite Hv1 Hv2. rewrite ptstomem_sync_is_nonsync.
      cbn [ty.valToRelVal]. iIntros "H". iExact "H".
    - cbn [ty.valToRelVal]. iIntros "H".
      iExists (SyncVal (get_word μ1 a)). iFrame. done.
    - cbn [ty.valToRelVal]. iIntros "H".
      iExists (NonSyncVal (get_word μ1 a) (get_word μ2 a)). iExact "H".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Byte-granular counterpart of gen_mem_asn_of_ptstomem
     (PLAN-byte-memory.md §5.3 / PLAN-check-scalar-full.md §3): the
     byte-expanded contract (gen_mem_asn_bytes) asks for four ptstomem 1
     chunks per data-memory entry, but Iris only ever hands out the
     WORD-granular interp_mem_with_public_memory.  Bridge by peeling
     get_word's own four-byte bv.app nest with ptstomem_bv_app and
     re-deriving each byte's value from vector_subrange via
     vector_subrange_app_shift / vector_subrange_0_app (Bitvector.v)
     rather than reassociating bv.app under an eq_rect. *)

  Lemma bv_one_eq_of_N {n} : @bv.one n = bv.of_N 1.
  Proof. destruct n; vm_compute; reflexivity. Qed.

  Lemma bv_zero_eq_of_N {n} : @bv.zero n = bv.of_N 0.
  Proof. destruct n; vm_compute; reflexivity. Qed.

  (* get_word's own nested bv.app, restated as a RelVal identity so
     ptstomem_bv_app applies directly -- holds by REFLEXIVITY in both the
     SyncVal and NonSyncVal case, since liftBinOpRV's (SyncVal,SyncVal)
     and catch-all branches both unfold to the same nested bv.app that
     get_word's own definition builds. *)
  Lemma get_word_sync_app μ a :
    SyncVal (get_word μ a) =
    ty.liftBinOp (σ1 := ty.bvec byte) (σ2 := ty.bvec (3*byte)) (σ3 := ty.bvec word) bv.app
      (SyncVal (memory_ram μ a))
     (ty.liftBinOp (σ1 := ty.bvec byte) (σ2 := ty.bvec (2*byte)) (σ3 := ty.bvec (3*byte)) bv.app
       (SyncVal (memory_ram μ (bv.add bv.one a)))
       (ty.liftBinOp (σ1 := ty.bvec byte) (σ2 := ty.bvec byte) (σ3 := ty.bvec (2*byte)) bv.app
         (SyncVal (memory_ram μ (bv.add (bv.of_N 2) a)))
         (ty.liftBinOp (σ1 := ty.bvec byte) (σ2 := ty.bvec 0) (σ3 := ty.bvec byte) bv.app
           (SyncVal (memory_ram μ (bv.add (bv.of_N 3) a))) (SyncVal bv.nil)))).
  Proof. unfold get_word. reflexivity. Qed.

  Lemma get_word_nonsync_app μ1 μ2 a :
    NonSyncVal (get_word μ1 a) (get_word μ2 a) =
    ty.liftBinOp (σ1 := ty.bvec byte) (σ2 := ty.bvec (3*byte)) (σ3 := ty.bvec word) bv.app
      (NonSyncVal (memory_ram μ1 a) (memory_ram μ2 a))
     (ty.liftBinOp (σ1 := ty.bvec byte) (σ2 := ty.bvec (2*byte)) (σ3 := ty.bvec (3*byte)) bv.app
       (NonSyncVal (memory_ram μ1 (bv.add bv.one a)) (memory_ram μ2 (bv.add bv.one a)))
       (ty.liftBinOp (σ1 := ty.bvec byte) (σ2 := ty.bvec byte) (σ3 := ty.bvec (2*byte)) bv.app
         (NonSyncVal (memory_ram μ1 (bv.add (bv.of_N 2) a)) (memory_ram μ2 (bv.add (bv.of_N 2) a)))
         (ty.liftBinOp (σ1 := ty.bvec byte) (σ2 := ty.bvec 0) (σ3 := ty.bvec byte) bv.app
           (NonSyncVal (memory_ram μ1 (bv.add (bv.of_N 3) a)) (memory_ram μ2 (bv.add (bv.of_N 3) a)))
           (SyncVal bv.nil)))).
  Proof. unfold get_word. reflexivity. Qed.

  (* app with an empty tail is the identity, at the RelVal level. *)
  Lemma relval_app_nil (b : RelVal (ty.bvec byte)) :
    ty.liftBinOp (σ1 := ty.bvec byte) (σ2 := ty.bvec 0) (σ3 := ty.bvec byte) bv.app b (SyncVal bv.nil) = b.
  Proof. destruct b as [v|v1 v2]; cbn; rewrite ?bv.app_nil_r; reflexivity. Qed.

  (* A single byte is (up to the trivial width-0 True remainder)
     the same ownership as a width-1 ptstomem. *)
  Lemma interp_ptsto_ptstomem1 `{sailGS2 Σ} (addr : RVAddr) (b : RelVal (ty.bvec byte)) :
    interp_ptsto addr b ⊢ interp_ptstomem (width := 1) addr b.
  Proof.
    rewrite <- (relval_app_nil b) at 2.
    rewrite ptstomem_bv_app.
    iIntros "$". done.
  Qed.

  (* Byte j of get_word, at get_word's own canonical address form
     (of_N j + a, matching get_word's own definition) and at the
     commuted form (a + of_N j, matching byte_addr_val/byte_addr_rel's
     canonical output). *)
  Lemma get_word_byte0 μ a : bv.vector_subrange 0 8 (get_word μ a) = memory_ram μ (bv.add (bv.of_N 0) a).
  Proof.
    unfold get_word. rewrite <- bv_zero_eq_of_N. rewrite bv.add_zero_l.
    apply (@bv.vector_subrange_0_app 8 24).
  Qed.

  Lemma get_word_byte1 μ a : bv.vector_subrange 8 8 (get_word μ a) = memory_ram μ (bv.add (bv.of_N 1) a).
  Proof.
    unfold get_word. rewrite bv_one_eq_of_N.
    rewrite (@bv.vector_subrange_app_shift 8 24 0 8).
    apply (@bv.vector_subrange_0_app 8 16).
  Qed.

  Lemma get_word_byte2 μ a : bv.vector_subrange 16 8 (get_word μ a) = memory_ram μ (bv.add (bv.of_N 2) a).
  Proof.
    unfold get_word. rewrite bv_one_eq_of_N.
    rewrite (@bv.vector_subrange_app_shift 8 24 8 8).
    rewrite (@bv.vector_subrange_app_shift 8 16 0 8).
    apply (@bv.vector_subrange_0_app 8 8).
  Qed.

  Lemma get_word_byte3 μ a : bv.vector_subrange 24 8 (get_word μ a) = memory_ram μ (bv.add (bv.of_N 3) a).
  Proof.
    unfold get_word. rewrite bv_one_eq_of_N.
    rewrite (@bv.vector_subrange_app_shift 8 24 16 8).
    rewrite (@bv.vector_subrange_app_shift 8 16 8 8).
    rewrite (@bv.vector_subrange_app_shift 8 8 0 8).
    apply (@bv.vector_subrange_0_app 8 0).
  Qed.

  Lemma get_word_byte0' μ a : bv.vector_subrange 0 8 (get_word μ a) = memory_ram μ a.
  Proof. rewrite get_word_byte0. rewrite <- bv_zero_eq_of_N. rewrite bv.add_zero_l. reflexivity. Qed.

  Lemma get_word_byte1c μ a : bv.vector_subrange 8 8 (get_word μ a) = memory_ram μ (bv.add a (bv.of_N 1)).
  Proof. rewrite bv.add_comm. apply get_word_byte1. Qed.

  Lemma get_word_byte3c μ a : bv.vector_subrange 24 8 (get_word μ a) = memory_ram μ (bv.add a (bv.of_N 3)).
  Proof. rewrite bv.add_comm. apply get_word_byte3. Qed.

  (* Width-generic analog of ptstomem_sync_is_nonsync (Adequacy.v:638,
     there only stated at width 4): a NonSyncVal of the SAME value on both
     sides is the same ownership as a SyncVal, at any width. *)
  Lemma ptstomem_sync_is_nonsync_gen `{sailGS2 Σ} {width} (a : Val ty_word) (w : Val (ty.bvec (width*byte))) :
    interp_ptstomem (width := width) (SyncVal a) (NonSyncVal w w) ⊣⊢
    interp_ptstomem (width := width) (SyncVal a) (SyncVal w).
  Proof. unfold interp_ptstomem. auto. Qed.

  (* The byte-granular per-entry bridge itself. Mirrors
     gen_mem_asn_of_ptstomem above but targets gen_mem_asn_bytes
     (GenContract.v), whose PVExist branch is now a WORD existential
     ("mw") with byte projections -- so the address arithmetic here (not
     needed for gen_mem_asn_of_ptstomem, whose entries stay word-shaped)
     is the one genuinely new piece. *)
  Lemma gen_mem_asn_of_ptstomem_bytes `{sailGS2 Σ}
      (a : Val ty_xlenbits) (is_pub : bool) (opt_v : option (Val ty_xlenbits))
      (μ1 μ2 : Memory)
      {Σ0} (ι : Valuation Σ0)
      (HInitMem1 : ∀ v, opt_v = Some v → get_word μ1 a = v)
      (HInitMem2 : ∀ v, opt_v = Some v → get_word μ2 a = v) :
    (if is_pub
     then interp_ptstomem (width := 4) (SyncVal a) (SyncVal (get_word μ1 a))
     else interp_ptstomem (width := 4) (SyncVal a)
            (NonSyncVal (get_word μ1 a) (get_word μ2 a)))
    ⊢ asn.interpret (gen_mem_asn_bytes (a, is_pub, opt_v)) ι.
  Proof.
    destruct opt_v as [v|]; destruct is_pub; cbn.
    - (* PVConst, is_pub = true *)
      have Hv1 := HInitMem1 v eq_refl. rewrite <- Hv1.
      rewrite get_word_sync_app.
      rewrite ptstomem_bv_app. rewrite ptstomem_bv_app. rewrite ptstomem_bv_app.
      cbn [ty.liftUnOp ty.liftUnOpRV].
      rewrite bv_one_eq_of_N. rewrite bv.add_assoc. rewrite bv.of_N_add.
      change (1+2)%N with 3%N.
      rewrite bv.add_assoc. rewrite bv.of_N_add.
      change (1+2)%N with 3%N.
      rewrite <- (bv.add_zero_r (x:=a)) at 1 2.
      rewrite <- bv_zero_eq_of_N.
      rewrite (bv.add_comm (x:=a) (y:=bv.zero)).
      rewrite (bv.add_comm (x:=bv.of_N 1) (y:=a)).
      rewrite (bv.add_comm (x:=bv.of_N 2) (y:=a)).
      rewrite (bv.add_comm (x:=bv.of_N 3) (y:=a)).
      rewrite get_word_byte0. rewrite get_word_byte1.
      rewrite get_word_byte2. rewrite get_word_byte3.
      rewrite (bv.add_comm (x:=bv.of_N 0) (y:=a)).
      rewrite (bv.add_comm (x:=bv.of_N 1) (y:=a)).
      rewrite (bv.add_comm (x:=bv.of_N 2) (y:=a)).
      rewrite (bv.add_comm (x:=bv.of_N 3) (y:=a)).
      rewrite <- bv_zero_eq_of_N.
      rewrite interp_ptsto_ptstomem1. rewrite interp_ptsto_ptstomem1. rewrite interp_ptsto_ptstomem1.
      rewrite relval_app_nil.
      iIntros "($&$&$&$)".
    - (* PVConst, is_pub = false *)
      have Hv1 := HInitMem1 v eq_refl. have Hv2 := HInitMem2 v eq_refl.
      rewrite get_word_nonsync_app.
      rewrite ptstomem_bv_app. rewrite ptstomem_bv_app. rewrite ptstomem_bv_app.
      cbn [ty.liftUnOp ty.liftUnOpRV].
      rewrite bv_one_eq_of_N. rewrite bv.add_assoc. rewrite bv.of_N_add.
      change (1+2)%N with 3%N.
      rewrite <- (bv.add_zero_r (x:=a)) at 1 2.
      rewrite <- bv_zero_eq_of_N.
      rewrite (bv.add_comm (x:=a) (y:=bv.zero)).
      rewrite (bv.add_comm (x:=bv.of_N 1) (y:=a)).
      rewrite (bv.add_comm (x:=bv.of_N 2) (y:=a)).
      rewrite (bv.add_comm (x:=bv.of_N 3) (y:=a)).
      rewrite (bv.add_comm (x:=a) (y:=bv.of_N 2)).
      rewrite bv.add_assoc. rewrite bv.of_N_add.
      change (1+2)%N with 3%N.
      rewrite (bv.add_comm (x:=bv.of_N 3) (y:=a)).
      rewrite <- get_word_byte0. rewrite <- get_word_byte1c.
      rewrite <- get_word_byte2. rewrite <- get_word_byte3c.
      rewrite Hv1.
      rewrite <- get_word_byte0'. rewrite <- get_word_byte1c.
      rewrite <- get_word_byte2. rewrite <- get_word_byte3c.
      rewrite Hv2.
      rewrite relval_app_nil.
      rewrite interp_ptsto_ptstomem1. rewrite interp_ptsto_ptstomem1. rewrite interp_ptsto_ptstomem1.
      rewrite ptstomem_sync_is_nonsync_gen. rewrite ptstomem_sync_is_nonsync_gen.
      rewrite ptstomem_sync_is_nonsync_gen. rewrite ptstomem_sync_is_nonsync_gen.
      iIntros "($&$&$&$)".
    - (* PVExist, is_pub = true *)
      iIntros "H".
      iExists (SyncVal (get_word μ1 a)).
      unfold uop.evalRel. cbn [ty.liftUnOp ty.liftUnOpRV uop.eval].
      iSplitL "H".
      { iRevert "H".
        rewrite get_word_sync_app.
        rewrite ptstomem_bv_app. rewrite ptstomem_bv_app. rewrite ptstomem_bv_app.
        cbn [ty.liftUnOp ty.liftUnOpRV].
        rewrite bv_one_eq_of_N. rewrite bv.add_assoc. rewrite bv.of_N_add.
        change (1+2)%N with 3%N.
        rewrite <- (bv.add_zero_r (x:=a)) at 1 2.
        rewrite <- bv_zero_eq_of_N.
        rewrite (bv.add_comm (x:=a) (y:=bv.zero)).
        rewrite (bv.add_comm (x:=bv.of_N 1) (y:=a)).
        rewrite (bv.add_comm (x:=bv.of_N 2) (y:=a)).
        rewrite (bv.add_comm (x:=bv.of_N 3) (y:=a)).
        rewrite interp_ptsto_ptstomem1. rewrite interp_ptsto_ptstomem1. rewrite interp_ptsto_ptstomem1.
        rewrite relval_app_nil.
        rewrite (bv.add_comm (x:=a) (y:=bv.of_N 2)).
        rewrite bv.add_assoc. rewrite bv.of_N_add.
        change (1+2)%N with 3%N.
        rewrite (bv.add_comm (x:=bv.of_N 3) (y:=a)).
        rewrite <- get_word_byte0'. rewrite <- get_word_byte1c.
        rewrite <- get_word_byte2. rewrite <- get_word_byte3c.
        rewrite bv.add_zero_l.
        iIntros "($&$&$&$)". }
      iSplit; [done|done].
    - (* PVExist, is_pub = false *)
      iIntros "H".
      iExists (NonSyncVal (get_word μ1 a) (get_word μ2 a)).
      unfold uop.evalRel. cbn [ty.liftUnOp ty.liftUnOpRV uop.eval].
      iSplitL "H".
      { iRevert "H".
        rewrite get_word_nonsync_app.
        rewrite ptstomem_bv_app. rewrite ptstomem_bv_app. rewrite ptstomem_bv_app.
        cbn [ty.liftUnOp ty.liftUnOpRV].
        rewrite bv_one_eq_of_N. rewrite bv.add_assoc. rewrite bv.of_N_add.
        change (1+2)%N with 3%N.
        rewrite <- (bv.add_zero_r (x:=a)) at 1 2.
        rewrite <- bv_zero_eq_of_N.
        rewrite (bv.add_comm (x:=a) (y:=bv.zero)).
        rewrite (bv.add_comm (x:=bv.of_N 1) (y:=a)).
        rewrite (bv.add_comm (x:=bv.of_N 2) (y:=a)).
        rewrite (bv.add_comm (x:=bv.of_N 3) (y:=a)).
        rewrite interp_ptsto_ptstomem1. rewrite interp_ptsto_ptstomem1. rewrite interp_ptsto_ptstomem1.
        rewrite relval_app_nil.
        rewrite (bv.add_comm (x:=a) (y:=bv.of_N 2)).
        rewrite bv.add_assoc. rewrite bv.of_N_add.
        change (1+2)%N with 3%N.
        rewrite (bv.add_comm (x:=bv.of_N 3) (y:=a)).
        rewrite <- get_word_byte0'. rewrite <- get_word_byte1c.
        rewrite <- get_word_byte2. rewrite <- get_word_byte3c.
        rewrite <- get_word_byte0'. rewrite <- get_word_byte1c.
        rewrite <- get_word_byte2. rewrite <- get_word_byte3c.
        rewrite bv.add_zero_l.
        iIntros "($&$&$&$)". }
      iSplit; [done|done].
  Qed.

  (* ------------------------------------------------------------------ *)
  (* CLASSED data block: ImplPre side of gen_mem_pre_rel_classed          *)
  (* (GenContract.v; PLAN-classed-existentials.md Phase 3).               *)
  (*                                                                      *)
  (* The witness for a class's single existential is the CONCATENATION of  *)
  (* its cell values, so it needs a name before anything can be stated.    *)
  (* mem_class_width (cons k r) is DEFINITIONALLY xlenbits +               *)
  (* mem_class_width r, which is what lets bv.app typecheck with no        *)
  (* transport.                                                           *)
  Fixpoint words_app (μ : Memory) (pv : Val ty_xlenbits) (ks : list N)
      : bv (mem_class_width ks) :=
    match ks return bv (mem_class_width ks) with
    | nil      => bv.nil
    | cons k r => bv.app (get_word μ (bv.add pv (bv.of_N k))) (words_app μ pv r)
    end.

  (* Core of the bridge.  Two statement choices make the induction work, both
     found the hard way:

     - `mwt`, the class variable's TERM, is a PARAMETER rather than fixed to
       `term_var "mw"`.  gen_mem_cells_class's cons branch applies itself to
       `term_unop (uop.bvdrop xlenbits) mwt`, a NON-variable term at the SAME
       logical context; fixing the third argument to a variable puts the IH at a
       different context and it does not apply.
     - `pterm` is a parameter too (cf. byte_addr_rel), so one lemma serves the
       base-relative and concrete address forms.

     Each step is then just bv.take_app / bv.drop_app.  This is the payoff of
     using uop.bvtake/bvdrop rather than uop.vector_subrange in the generator:
     PLAN-byte-memory.md §10 had to bridge subrange against appView by hand.

     The `: RelVal (ty.bvec _)` ascription on Hmw is REQUIRED -- without it
     elaboration reads the RHS as `RV (bv _)` and fails to find
     `Inst ?T (RV (bv _))`.  Note also that plain `cbn` is what exposes the
     `evalRel` form; `cbn [inst inst_env]` leaves `luser` folded and the
     subsequent `rewrite bv.take_app` then finds no subterm. *)
  Lemma gen_mem_cells_class_intro `{sailGS2 Σ}
      (ks : list N) {Σ0} (ι : Valuation Σ0)
      (pterm : Term Σ0 ty_xlenbits) (pv : Val ty_xlenbits)
      (mwt : Term Σ0 (ty.bvec (mem_class_width ks)))
      (μ1 μ2 : Memory)
      (Hp : inst pterm ι = SyncVal pv)
      (Hmw : inst mwt ι =
               (NonSyncVal (words_app μ1 pv ks) (words_app μ2 pv ks)
                : RelVal (ty.bvec (mem_class_width ks)))) :
    ([∗ list] k ∈ ks,
       interp_ptstomem (width := 4) (SyncVal (bv.add pv (bv.of_N k)))
         (NonSyncVal (get_word μ1 (bv.add pv (bv.of_N k)))
                     (get_word μ2 (bv.add pv (bv.of_N k)))))
    ⊢ asn.interpret
        (gen_mem_cells_class ks
           (fun k => term_binop bop.bvadd pterm (term_val ty_xlenbits (bv.of_N k)))
           mwt) ι.
  Proof.
    generalize dependent mwt. induction ks as [|k r IH]; intros mwt Hmw.
    - iIntros "_". done.
    - rewrite big_sepL_cons. iIntros "[Hhead Hrest]".
      cbn [gen_mem_cells_class asn.interpret]. iSplitL "Hhead".
      + cbn. rewrite Hp. cbn [words_app] in Hmw. rewrite Hmw.
        unfold bop.evalRel, uop.evalRel; cbn; rewrite !bv.take_app; iApply "Hhead".
      + assert (Hd : inst (term_unop (uop.bvdrop xlenbits) mwt) ι
                     = (NonSyncVal (words_app μ1 pv r) (words_app μ2 pv r)
                        : RelVal (ty.bvec (mem_class_width r)))).
        { cbn. rewrite Hmw. cbn [words_app].
          unfold uop.evalRel; cbn. rewrite !bv.drop_app. reflexivity. }
        iApply (IH _ Hd). iExact "Hrest".
  Qed.

  (* SyncVal twin, for the PUBLIC class.  A NonSyncVal v v witness would not do:
     secLeak is defined by a match on the CONSTRUCTOR (Formulas.v:117), so
     secLeak (NonSyncVal v v) is False however equal the sides are, and
     secLeakvar on the grouped variable would be unprovable.  Proof script is
     identical to the NonSyncVal case. *)
  Lemma gen_mem_cells_class_intro_sync `{sailGS2 Σ}
      (ks : list N) {Σ0} (ι : Valuation Σ0)
      (pterm : Term Σ0 ty_xlenbits) (pv : Val ty_xlenbits)
      (mwt : Term Σ0 (ty.bvec (mem_class_width ks)))
      (μ : Memory)
      (Hp : inst pterm ι = SyncVal pv)
      (Hmw : inst mwt ι = (SyncVal (words_app μ pv ks)
                           : RelVal (ty.bvec (mem_class_width ks)))) :
    ([∗ list] k ∈ ks,
       interp_ptstomem (width := 4) (SyncVal (bv.add pv (bv.of_N k)))
         (SyncVal (get_word μ (bv.add pv (bv.of_N k)))))
    ⊢ asn.interpret
        (gen_mem_cells_class ks
           (fun k => term_binop bop.bvadd pterm (term_val ty_xlenbits (bv.of_N k)))
           mwt) ι.
  Proof.
    generalize dependent mwt. induction ks as [|k r IH]; intros mwt Hmw.
    - iIntros "_". done.
    - rewrite big_sepL_cons. iIntros "[Hhead Hrest]".
      cbn [gen_mem_cells_class asn.interpret]. iSplitL "Hhead".
      + cbn. rewrite Hp. cbn [words_app] in Hmw. rewrite Hmw.
        unfold bop.evalRel, uop.evalRel; cbn; rewrite !bv.take_app; iApply "Hhead".
      + assert (Hd : inst (term_unop (uop.bvdrop xlenbits) mwt) ι
                     = (SyncVal (words_app μ pv r)
                        : RelVal (ty.bvec (mem_class_width r)))).
        { cbn. rewrite Hmw. cbn [words_app].
          unfold uop.evalRel; cbn. rewrite !bv.drop_app. reflexivity. }
        iApply (IH _ Hd). iExact "Hrest".
  Qed.

  (* The two class wrappers: supply the iExists witness, and for the public
     class discharge secLeakvar on the grouped variable (secLeak (SyncVal _) is
     True by definition).  These are stated at the KEYS level, which is why
     GenContract.v splits gen_mem_*_class_ks out: `destruct (mem_rel_keys
     specs)` fails with "Conclusion depends on the bodies of ..." since the
     existential's type mentions mem_class_width of it. *)
  Lemma gen_mem_priv_class_ks_intro `{sailGS2 Σ} (ks : list N)
      (pv : Val ty_xlenbits) (va : RelVal ty_xlenbits) (μ1 μ2 : Memory) :
    ([∗ list] k ∈ ks,
       interp_ptstomem (width := 4) (SyncVal (bv.add pv (bv.of_N k)))
         (NonSyncVal (get_word μ1 (bv.add pv (bv.of_N k)))
                     (get_word μ2 (bv.add pv (bv.of_N k)))))
    ⊢ asn.interpret (gen_mem_priv_class_ks ks)
        ([env].["p"∷ty_xlenbits ↦ SyncVal pv].["a"∷ty_xlenbits ↦ va]).
  Proof.
    destruct ks as [|k r].
    - iIntros "_". done.
    - cbn [gen_mem_priv_class_ks asn.interpret]. iIntros "H".
      iExists (NonSyncVal (words_app μ1 pv (cons k r)) (words_app μ2 pv (cons k r))).
      iApply gen_mem_cells_class_intro; [reflexivity|reflexivity|iExact "H"].
  Qed.

  Lemma gen_mem_pub_class_ks_intro `{sailGS2 Σ} (ks : list N)
      (pv : Val ty_xlenbits) (va : RelVal ty_xlenbits) (μ : Memory) :
    ([∗ list] k ∈ ks,
       interp_ptstomem (width := 4) (SyncVal (bv.add pv (bv.of_N k)))
         (SyncVal (get_word μ (bv.add pv (bv.of_N k)))))
    ⊢ asn.interpret (gen_mem_pub_class_ks ks)
        ([env].["p"∷ty_xlenbits ↦ SyncVal pv].["a"∷ty_xlenbits ↦ va]).
  Proof.
    destruct ks as [|k r].
    - iIntros "_". done.
    - cbn [gen_mem_pub_class_ks asn.interpret]. iIntros "H".
      iExists (SyncVal (words_app μ pv (cons k r))).
      iSplitL "H".
      + iApply gen_mem_cells_class_intro_sync; [reflexivity|reflexivity|iExact "H"].
      + (* secLeakvar "mwpub": secLeak (SyncVal _) is True by the match in
           Formulas.v:117, but the goal arrives as `instprop (formula_secLeak
           ...) ι`, so it must be reduced first -- a bare `exact I` fails with
           "The term I has type True while it is expected to have type
           instprop (formula_secLeak ...)".  This is also exactly why the public
           class needs the SyncVal cells lemma: with a NonSyncVal witness this
           goal would be False. *)
        iPureIntro. cbn. first [exact I | done].
  Qed.

  (* ====================================================================== *)
  (* BYTE-GRANULAR CLASSED ImplPre (PLAN-unify-generators.md stage 2).        *)
  (*                                                                        *)
  (* Byte twins of the four lemmas above.  The structure is NOT a new         *)
  (* bv-slicing induction, which is what the plan expected: the per-cell      *)
  (* obligation turns out to be exactly the PVExist branch of                 *)
  (* gen_mem_asn_of_ptstomem_bytes MINUS its `iExists` -- there the witness   *)
  (* had to be supplied per entry, here it is already fixed by the group      *)
  (* hypothesis.  So that branch is factored out below as an ABSTRACT-address *)
  (* split and reused on both sides, and the group peel is just               *)
  (* bv.take_app / bv.drop_app, identical to the word case.                   *)
  (* ====================================================================== *)

  (* Split ONE word chunk into its four byte chunks, at an abstract address. *)
  Lemma ptstomem4_split_bytes `{sailGS2 Σ} (a : Val ty_xlenbits) (μ1 μ2 : Memory) :
    interp_ptstomem (width := 4) (SyncVal a)
      (NonSyncVal (get_word μ1 a) (get_word μ2 a))
    ⊢ interp_ptstomem (width := 1) (SyncVal (bv.add a (bv.of_N 0)))
        (NonSyncVal (bv.vector_subrange 0 8 (get_word μ1 a))
                    (bv.vector_subrange 0 8 (get_word μ2 a)))
      ∗ interp_ptstomem (width := 1) (SyncVal (bv.add a (bv.of_N 1)))
          (NonSyncVal (bv.vector_subrange 8 8 (get_word μ1 a))
                      (bv.vector_subrange 8 8 (get_word μ2 a)))
      ∗ interp_ptstomem (width := 1) (SyncVal (bv.add a (bv.of_N 2)))
          (NonSyncVal (bv.vector_subrange 16 8 (get_word μ1 a))
                      (bv.vector_subrange 16 8 (get_word μ2 a)))
      ∗ interp_ptstomem (width := 1) (SyncVal (bv.add a (bv.of_N 3)))
          (NonSyncVal (bv.vector_subrange 24 8 (get_word μ1 a))
                      (bv.vector_subrange 24 8 (get_word μ2 a))).
  Proof.
    rewrite get_word_nonsync_app.
    rewrite ptstomem_bv_app. rewrite ptstomem_bv_app. rewrite ptstomem_bv_app.
    cbn [ty.liftUnOp ty.liftUnOpRV].
    rewrite bv_one_eq_of_N. rewrite bv.add_assoc. rewrite bv.of_N_add.
    change (1+2)%N with 3%N.
    rewrite <- (bv.add_zero_r (x:=a)) at 1 2.
    rewrite <- bv_zero_eq_of_N.
    rewrite (bv.add_comm (x:=a) (y:=bv.zero)).
    rewrite (bv.add_comm (x:=bv.of_N 1) (y:=a)).
    rewrite (bv.add_comm (x:=bv.of_N 2) (y:=a)).
    rewrite (bv.add_comm (x:=bv.of_N 3) (y:=a)).
    rewrite interp_ptsto_ptstomem1. rewrite interp_ptsto_ptstomem1.
    rewrite interp_ptsto_ptstomem1.
    rewrite relval_app_nil.
    (* Byte 3's address arrives as `of_N 1 + (a + of_N 2)`; fold it to
       `a + of_N 3`.  bv.add_assoc is stated LEFT-to-right, so the forward
       direction re-associates; bv.of_N_add COLLAPSES a sum of two of_N's (it
       does not expand one), so of_N 1 + of_N 2 |-> of_N 3. *)
    rewrite (bv.add_assoc (x:=bv.of_N 1) (y:=a) (z:=bv.of_N 2)).
    rewrite (bv.add_comm (x:=bv.of_N 1) (y:=a)).
    rewrite <- (bv.add_assoc (x:=a) (y:=bv.of_N 1) (z:=bv.of_N 2)).
    rewrite bv.of_N_add.
    change (1+2)%N with 3%N.
    rewrite bv.add_zero_l.
    (* get_word_byte2 is stated with the OFFSET FIRST (`of_N 2 + a`), unlike the
       `c` variants which take the address first -- hence the add_comm before it
       and not before bytes 1 or 3.  Each block of four converts one side. *)
    rewrite <- get_word_byte0'. rewrite <- get_word_byte1c.
    rewrite (bv.add_comm (x:=a) (y:=bv.of_N 2)).
    rewrite <- get_word_byte2.
    rewrite <- get_word_byte3c.
    rewrite <- get_word_byte0'. rewrite <- get_word_byte1c.
    rewrite <- get_word_byte2.
    rewrite <- get_word_byte3c.
    done.
  Qed.

  (* SyncVal twin, for the public class. *)
  Lemma ptstomem4_split_bytes_sync `{sailGS2 Σ} (a : Val ty_xlenbits) (μ : Memory) :
    interp_ptstomem (width := 4) (SyncVal a) (SyncVal (get_word μ a))
    ⊢ interp_ptstomem (width := 1) (SyncVal (bv.add a (bv.of_N 0)))
        (SyncVal (bv.vector_subrange 0 8 (get_word μ a)))
      ∗ interp_ptstomem (width := 1) (SyncVal (bv.add a (bv.of_N 1)))
          (SyncVal (bv.vector_subrange 8 8 (get_word μ a)))
      ∗ interp_ptstomem (width := 1) (SyncVal (bv.add a (bv.of_N 2)))
          (SyncVal (bv.vector_subrange 16 8 (get_word μ a)))
      ∗ interp_ptstomem (width := 1) (SyncVal (bv.add a (bv.of_N 3)))
          (SyncVal (bv.vector_subrange 24 8 (get_word μ a))).
  Proof.
    (* Identical chain, with get_word_sync_app for get_word_nonsync_app and ONE
       block of four byte rewrites rather than two -- one side to convert. *)
    rewrite get_word_sync_app.
    rewrite ptstomem_bv_app. rewrite ptstomem_bv_app. rewrite ptstomem_bv_app.
    cbn [ty.liftUnOp ty.liftUnOpRV].
    rewrite bv_one_eq_of_N. rewrite bv.add_assoc. rewrite bv.of_N_add.
    change (1+2)%N with 3%N.
    rewrite <- (bv.add_zero_r (x:=a)) at 1 2.
    rewrite <- bv_zero_eq_of_N.
    rewrite (bv.add_comm (x:=a) (y:=bv.zero)).
    rewrite (bv.add_comm (x:=bv.of_N 1) (y:=a)).
    rewrite (bv.add_comm (x:=bv.of_N 2) (y:=a)).
    rewrite (bv.add_comm (x:=bv.of_N 3) (y:=a)).
    rewrite interp_ptsto_ptstomem1. rewrite interp_ptsto_ptstomem1.
    rewrite interp_ptsto_ptstomem1.
    rewrite relval_app_nil.
    rewrite (bv.add_assoc (x:=bv.of_N 1) (y:=a) (z:=bv.of_N 2)).
    rewrite (bv.add_comm (x:=bv.of_N 1) (y:=a)).
    rewrite <- (bv.add_assoc (x:=a) (y:=bv.of_N 1) (z:=bv.of_N 2)).
    rewrite bv.of_N_add.
    change (1+2)%N with 3%N.
    rewrite bv.add_zero_l.
    rewrite <- get_word_byte0'. rewrite <- get_word_byte1c.
    rewrite (bv.add_comm (x:=a) (y:=bv.of_N 2)).
    rewrite <- get_word_byte2.
    rewrite <- get_word_byte3c.
    done.
  Qed.

  Lemma gen_mem_cells_class_bytes_intro `{sailGS2 Σ}
      (ks : list N) {Σ0} (ι : Valuation Σ0)
      (pterm : Term Σ0 ty_xlenbits) (pv : Val ty_xlenbits)
      (mwt : Term Σ0 (ty.bvec (mem_class_width ks)))
      (μ1 μ2 : Memory)
      (Hp : inst pterm ι = SyncVal pv)
      (Hmw : inst mwt ι =
               (NonSyncVal (words_app μ1 pv ks) (words_app μ2 pv ks)
                : RelVal (ty.bvec (mem_class_width ks)))) :
    ([∗ list] k ∈ ks,
       interp_ptstomem (width := 4) (SyncVal (bv.add pv (bv.of_N k)))
         (NonSyncVal (get_word μ1 (bv.add pv (bv.of_N k)))
                     (get_word μ2 (bv.add pv (bv.of_N k)))))
    ⊢ asn.interpret
        (gen_mem_cells_class_bytes ks (fun k j => byte_addr_rel pterm k j) mwt) ι.
  Proof.
    generalize dependent mwt. induction ks as [|k r IH]; intros mwt Hmw.
    - iIntros "_". done.
    - rewrite big_sepL_cons. iIntros "[Hhead Hrest]".
      cbn [gen_mem_cells_class_bytes asn.interpret]. iSplitL "Hhead".
      + (* Group peel, then re-associate `pv + of_N (k+j)` into
           `(pv + of_N k) + of_N j` so the abstract split applies. *)
        cbn. rewrite Hp. cbn [words_app] in Hmw. rewrite Hmw.
        unfold bop.evalRel, uop.evalRel; cbn.
        rewrite !bv.take_app.
        rewrite <- !bv.of_N_add.
        rewrite !bv.add_assoc.
        iApply ptstomem4_split_bytes. iExact "Hhead".
      + assert (Hd : inst (term_unop (uop.bvdrop xlenbits) mwt) ι
                     = (NonSyncVal (words_app μ1 pv r) (words_app μ2 pv r)
                        : RelVal (ty.bvec (mem_class_width r)))).
        { cbn. rewrite Hmw. cbn [words_app].
          unfold uop.evalRel; cbn. rewrite !bv.drop_app. reflexivity. }
        iApply (IH _ Hd). iExact "Hrest".
  Qed.

  (* SyncVal twin.  Needed for the same reason as the word case: secLeak matches
     on the CONSTRUCTOR, so secLeak (NonSyncVal v v) is False however equal the
     sides are, and secLeakvar on the grouped variable would be unprovable. *)
  Lemma gen_mem_cells_class_bytes_intro_sync `{sailGS2 Σ}
      (ks : list N) {Σ0} (ι : Valuation Σ0)
      (pterm : Term Σ0 ty_xlenbits) (pv : Val ty_xlenbits)
      (mwt : Term Σ0 (ty.bvec (mem_class_width ks)))
      (μ : Memory)
      (Hp : inst pterm ι = SyncVal pv)
      (Hmw : inst mwt ι =
               (SyncVal (words_app μ pv ks)
                : RelVal (ty.bvec (mem_class_width ks)))) :
    ([∗ list] k ∈ ks,
       interp_ptstomem (width := 4) (SyncVal (bv.add pv (bv.of_N k)))
         (SyncVal (get_word μ (bv.add pv (bv.of_N k)))))
    ⊢ asn.interpret
        (gen_mem_cells_class_bytes ks (fun k j => byte_addr_rel pterm k j) mwt) ι.
  Proof.
    generalize dependent mwt. induction ks as [|k r IH]; intros mwt Hmw.
    - iIntros "_". done.
    - rewrite big_sepL_cons. iIntros "[Hhead Hrest]".
      cbn [gen_mem_cells_class_bytes asn.interpret]. iSplitL "Hhead".
      + cbn. rewrite Hp. cbn [words_app] in Hmw. rewrite Hmw.
        unfold bop.evalRel, uop.evalRel; cbn.
        rewrite !bv.take_app.
        rewrite <- !bv.of_N_add.
        rewrite !bv.add_assoc.
        iApply ptstomem4_split_bytes_sync. iExact "Hhead".
      + assert (Hd : inst (term_unop (uop.bvdrop xlenbits) mwt) ι
                     = (SyncVal (words_app μ pv r)
                        : RelVal (ty.bvec (mem_class_width r)))).
        { cbn. rewrite Hmw. cbn [words_app].
          unfold uop.evalRel; cbn. rewrite bv.drop_app. reflexivity. }
        iApply (IH _ Hd). iExact "Hrest".
  Qed.

  (* Class wrappers, mirroring gen_mem_{priv,pub}_class_ks_intro above. *)
  Lemma gen_mem_priv_class_ks_bytes_intro `{sailGS2 Σ} (ks : list N)
      (pv : Val ty_xlenbits) (va : RelVal ty_xlenbits) (μ1 μ2 : Memory) :
    ([∗ list] k ∈ ks,
       interp_ptstomem (width := 4) (SyncVal (bv.add pv (bv.of_N k)))
         (NonSyncVal (get_word μ1 (bv.add pv (bv.of_N k)))
                     (get_word μ2 (bv.add pv (bv.of_N k)))))
    ⊢ asn.interpret (gen_mem_priv_class_ks_bytes ks)
        ([env].["p"∷ty_xlenbits ↦ SyncVal pv].["a"∷ty_xlenbits ↦ va]).
  Proof.
    destruct ks as [|k r].
    - iIntros "_". done.
    - cbn [gen_mem_priv_class_ks_bytes asn.interpret]. iIntros "H".
      iExists (NonSyncVal (words_app μ1 pv (cons k r)) (words_app μ2 pv (cons k r))).
      iApply gen_mem_cells_class_bytes_intro; [reflexivity|reflexivity|iExact "H"].
  Qed.

  Lemma gen_mem_pub_class_ks_bytes_intro `{sailGS2 Σ} (ks : list N)
      (pv : Val ty_xlenbits) (va : RelVal ty_xlenbits) (μ : Memory) :
    ([∗ list] k ∈ ks,
       interp_ptstomem (width := 4) (SyncVal (bv.add pv (bv.of_N k)))
         (SyncVal (get_word μ (bv.add pv (bv.of_N k)))))
    ⊢ asn.interpret (gen_mem_pub_class_ks_bytes ks)
        ([env].["p"∷ty_xlenbits ↦ SyncVal pv].["a"∷ty_xlenbits ↦ va]).
  Proof.
    destruct ks as [|k r].
    - iIntros "_". done.
    - cbn [gen_mem_pub_class_ks_bytes asn.interpret]. iIntros "H".
      iExists (SyncVal (words_app μ pv (cons k r))).
      iSplitL "H".
      + iApply gen_mem_cells_class_bytes_intro_sync;
          [reflexivity|reflexivity|iExact "H"].
      + iPureIntro. cbn. first [exact I | done].
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* Splitting the resource list by class -- the last structural piece of the *)
  (* classed bridge.  gen_mem_pre_rel_classed groups its cells by publicness  *)
  (* while interp_mem_with_public_memory is a big_opL in SPEC order, so the   *)
  (* resources must be re-associated into pinned ++ public ++ private.        *)
  (*                                                                        *)
  (* This is provable only because that big_opL's body does NOT depend on the *)
  (* index: Iris's big_opL_permutation applies to `λ _ : nat, f` exactly.      *)
  (* ---------------------------------------------------------------------- *)
  Lemma three_way_perm {A} (p q : A -> bool) (l : list A) :
    l ≡ₚ List.filter (fun x => negb (p x)) l
      ++ List.filter (fun x => andb (p x) (q x)) l
      ++ List.filter (fun x => andb (p x) (negb (q x))) l.
  Proof.
    induction l as [|a l IH]; [reflexivity|].
    cbn. destruct (p a) eqn:Hp; destruct (q a) eqn:Hq; cbn.
    (* Permutation_cons_app is the exact shape here; `rewrite
       Permutation_middle` matches an UNINTENDED instance and leaves an
       unprovable goal. *)
    - now apply Permutation_cons_app.
    - rewrite app_assoc. apply Permutation_cons_app. rewrite <- app_assoc. exact IH.
    - now apply perm_skip.
    - now apply perm_skip.
  Qed.

  (* Generic and reusable: split a big_sepL three ways by two booleans. *)
  Lemma big_sepL_three_way {PROP : bi} {A} (p q : A -> bool) (Φ : A -> PROP)
      (l : list A) :
    ([∗ list] x ∈ l, Φ x)
    ⊢ ([∗ list] x ∈ List.filter (fun x => negb (p x)) l, Φ x)
      ∗ ([∗ list] x ∈ List.filter (fun x => andb (p x) (q x)) l, Φ x)
      ∗ ([∗ list] x ∈ List.filter (fun x => andb (p x) (negb (q x))) l, Φ x).
  Proof.
    rewrite (big_opL_permutation Φ l _ (three_way_perm p q l)).
    rewrite !big_sepL_app. done.
  Qed.

  (* The resource-level instance.  big_sepL_fmap moves the map inside so the
     filters stay on the ORIGINAL spec list -- doing it the other way round
     would additionally require filter/map commutation. *)
  Lemma interp_mem_partition `{sailGS2 Σ} (μ1 μ2 : Memory)
      (specs : list mem_full_spec) :
    interp_mem_with_public_memory μ1 μ2 (map mem_full_to_spec specs)
    ⊢ interp_mem_with_public_memory μ1 μ2
        (map mem_full_to_spec
           (List.filter (fun s => negb (mem_full_is_exist s)) specs))
      ∗ interp_mem_with_public_memory μ1 μ2
        (map mem_full_to_spec
           (List.filter (fun s => andb (mem_full_is_exist s) (mem_full_is_pub s)) specs))
      ∗ interp_mem_with_public_memory μ1 μ2
        (map mem_full_to_spec
           (List.filter (fun s => andb (mem_full_is_exist s) (negb (mem_full_is_pub s))) specs)).
  Proof.
    unfold interp_mem_with_public_memory.
    rewrite !(big_sepL_fmap mem_full_to_spec).
    apply (big_sepL_three_way mem_full_is_exist mem_full_is_pub).
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* Bridging the two FILTER LEVELS.  interp_mem_partition filters at the    *)
  (* mem_full_spec level, on `map (concretize_mem ia) specs`; the classed     *)
  (* precondition filters at the mem_spec_rel level, on `specs`.  The two     *)
  (* classifications agree under concretize_mem (it sends PVExist to None,    *)
  (* PVConst/PVBaseOff to Some _, and copies the publicness bit), so the      *)
  (* filters commute with the map.                                           *)
  (*                                                                        *)
  (* interp_mem_partition itself dodges filter/map commutation via            *)
  (* big_sepL_fmap; it is unavoidable here, at the spec-level boundary.       *)
  (* ---------------------------------------------------------------------- *)
  Lemma concretize_mem_is_exist (ia : N) (s : mem_spec_rel) :
    mem_full_is_exist (concretize_mem ia s) = mem_spec_is_exist s.
  Proof. destruct s as [[k pub] pv]; destruct pv; reflexivity. Qed.

  Lemma concretize_mem_is_pub (ia : N) (s : mem_spec_rel) :
    mem_full_is_pub (concretize_mem ia s) = mem_spec_is_pub s.
  Proof. destruct s as [[k pub] pv]; destruct pv; reflexivity. Qed.

  (* Generic in the predicate pair, so the three class filters below are one
     line each.  NOTE `cbn [List.map]` rather than `cbn [map]`: the bare name
     is ambiguous here (Ltac2's List.map is in scope) and a one-element delta
     flag `[map]` is a PARSE error, "[smart_global] expected after '['" --
     while `[map List.filter]` happens to parse.  Qualify it. *)
  Lemma filter_map_concretize_mem (ia : N)
      (P : mem_spec_rel -> bool) (Q : mem_full_spec -> bool)
      (HPQ : forall s, Q (concretize_mem ia s) = P s)
      (specs : list mem_spec_rel) :
    map (concretize_mem ia) (List.filter P specs)
    = List.filter Q (map (concretize_mem ia) specs).
  Proof.
    induction specs as [|s r IH]; [reflexivity|].
    cbn [map List.filter]. rewrite HPQ. destruct (P s).
    - cbn [List.map]. f_equal. exact IH.
    - exact IH.
  Qed.

  (* The three instances, one per class of gen_mem_pre_rel_classed.  Two
     separate `rewrite`s rather than `rewrite A, B` -- the comma form is a
     parse error in this file's notation environment. *)
  Lemma filter_pinned_concretize (ia : N) (specs : list mem_spec_rel) :
    map (concretize_mem ia) (List.filter (fun s => negb (mem_spec_is_exist s)) specs)
    = List.filter (fun s => negb (mem_full_is_exist s)) (map (concretize_mem ia) specs).
  Proof.
    apply filter_map_concretize_mem. intros s. now rewrite concretize_mem_is_exist.
  Qed.

  Lemma filter_pub_concretize (ia : N) (specs : list mem_spec_rel) :
    map (concretize_mem ia)
      (List.filter (fun s => andb (mem_spec_is_exist s) (mem_spec_is_pub s)) specs)
    = List.filter (fun s => andb (mem_full_is_exist s) (mem_full_is_pub s))
        (map (concretize_mem ia) specs).
  Proof.
    apply filter_map_concretize_mem. intros s.
    rewrite concretize_mem_is_exist. rewrite concretize_mem_is_pub. reflexivity.
  Qed.

  Lemma filter_priv_concretize (ia : N) (specs : list mem_spec_rel) :
    map (concretize_mem ia)
      (List.filter (fun s => andb (mem_spec_is_exist s) (negb (mem_spec_is_pub s))) specs)
    = List.filter (fun s => andb (mem_full_is_exist s) (negb (mem_full_is_pub s)))
        (map (concretize_mem ia) specs).
  Proof.
    apply filter_map_concretize_mem. intros s.
    rewrite concretize_mem_is_exist. rewrite concretize_mem_is_pub. reflexivity.
  Qed.

  (* Restricting to the PINNED class does not change the required initial
     memory: gen_init_mem is an omap that already drops every None entry, and
     concretize_mem sends exactly the PVExist (i.e. non-pinned) entries to
     None.  This is what lets gen_implpre_mem be reused for the pinned group
     with the caller's unfiltered declare_init_memory hypotheses. *)
  Lemma gen_init_mem_filter_pinned (ia : N) (specs : list mem_spec_rel) :
    gen_init_mem (map (concretize_mem ia)
      (List.filter (fun s => negb (mem_spec_is_exist s)) specs))
    = gen_init_mem (map (concretize_mem ia) specs).
  Proof.
    induction specs as [|[[k pub] pv] r IH]; [reflexivity|].
    (* gen_init_mem must be unfolded in the IH too, or `rewrite IH` finds no
       subterm once the goal's copy has been reduced to its omap. *)
    unfold gen_init_mem in *.
    destruct pv;
      cbn [List.map List.filter mem_spec_is_exist negb concretize_mem omap list_omap];
      rewrite IH; reflexivity.
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* Per-group resource conversion: one class's slice of                     *)
  (* interp_mem_with_public_memory, in the [∗ list] over KEYS form that       *)
  (* gen_mem_{pub,priv}_class_ks_intro consume.                              *)
  (*                                                                        *)
  (* Only the publicness hypothesis is needed -- interp_mem_with_public_memory *)
  (* branches on the pub bit and ignores the value slot entirely, so nothing   *)
  (* here has to know the group is PVExist.  bv.of_N_add relates              *)
  (* concretize_mem's `of_N (ia + k)` to the wrappers' `add (of_N ia)          *)
  (* (of_N k)`, exactly as in gen_mem_pre_rel_concretize.                     *)
  (* ---------------------------------------------------------------------- *)
  Lemma interp_mem_group_priv `{sailGS2 Σ} (μ1 μ2 : Memory) (ia : N)
      (G : list mem_spec_rel)
      (Hpriv : forall s, In s G -> mem_spec_is_pub s = false) :
    interp_mem_with_public_memory μ1 μ2
      (map mem_full_to_spec (map (concretize_mem ia) G))
    ⊢ [∗ list] k ∈ mem_rel_keys G,
        interp_ptstomem (width := 4)
          (SyncVal (bv.add (bv.of_N ia) (bv.of_N k)))
          (NonSyncVal (get_word μ1 (bv.add (bv.of_N ia) (bv.of_N k)))
                      (get_word μ2 (bv.add (bv.of_N ia) (bv.of_N k)))).
  Proof.
    revert Hpriv. induction G as [|s G' IH]; intros Hpriv.
    - done.
    - destruct s as [[k pub] pv].
      assert (Hp : pub = false) by (apply (Hpriv (k, pub, pv)); now left).
      subst pub.
      cbn [List.map mem_rel_keys mem_full_to_spec concretize_mem].
      unfold interp_mem_with_public_memory. cbn [big_opL].
      iIntros "[Hh Ht]". iSplitL "Hh".
      + rewrite bv.of_N_add. iExact "Hh".
      + iApply IH; [ intros s Hs; apply Hpriv; now right | iExact "Ht" ].
  Qed.

  (* Public twin.  Note the value is get_word μ1 on BOTH sides -- that is what
     interp_mem_with_public_memory's public branch hands out, and it is why the
     SyncVal cells lemma (and hence a provable secLeakvar) is available here. *)
  Lemma interp_mem_group_pub `{sailGS2 Σ} (μ1 μ2 : Memory) (ia : N)
      (G : list mem_spec_rel)
      (Hpub : forall s, In s G -> mem_spec_is_pub s = true) :
    interp_mem_with_public_memory μ1 μ2
      (map mem_full_to_spec (map (concretize_mem ia) G))
    ⊢ [∗ list] k ∈ mem_rel_keys G,
        interp_ptstomem (width := 4)
          (SyncVal (bv.add (bv.of_N ia) (bv.of_N k)))
          (SyncVal (get_word μ1 (bv.add (bv.of_N ia) (bv.of_N k)))).
  Proof.
    revert Hpub. induction G as [|s G' IH]; intros Hpub.
    - done.
    - destruct s as [[k pub] pv].
      assert (Hp : pub = true) by (apply (Hpub (k, pub, pv)); now left).
      subst pub.
      cbn [List.map mem_rel_keys mem_full_to_spec concretize_mem].
      unfold interp_mem_with_public_memory. cbn [big_opL].
      iIntros "[Hh Ht]". iSplitL "Hh".
      + rewrite bv.of_N_add. iExact "Hh".
      + iApply IH; [ intros s Hs; apply Hpub; now right | iExact "Ht" ].
  Qed.

  (* interp_mem_partition restated with the filters at the mem_spec_rel level,
     which is where gen_mem_pre_rel_classed puts them. *)
  Lemma interp_mem_partition_rel `{sailGS2 Σ} (μ1 μ2 : Memory) (ia : N)
      (specs : list mem_spec_rel) :
    interp_mem_with_public_memory μ1 μ2
      (map mem_full_to_spec (map (concretize_mem ia) specs))
    ⊢ interp_mem_with_public_memory μ1 μ2
        (map mem_full_to_spec (map (concretize_mem ia)
           (List.filter (fun s => negb (mem_spec_is_exist s)) specs)))
      ∗ interp_mem_with_public_memory μ1 μ2
        (map mem_full_to_spec (map (concretize_mem ia)
           (List.filter (fun s => andb (mem_spec_is_exist s) (mem_spec_is_pub s)) specs)))
      ∗ interp_mem_with_public_memory μ1 μ2
        (map mem_full_to_spec (map (concretize_mem ia)
           (List.filter (fun s => andb (mem_spec_is_exist s) (negb (mem_spec_is_pub s))) specs))).
  Proof.
    rewrite filter_pinned_concretize.
    rewrite filter_pub_concretize.
    rewrite filter_priv_concretize.
    apply interp_mem_partition.
  Qed.

  (* Once-and-for-all ImplPre for the memory portion of gen_contract:
     converts interp_mem_with_public_memory μ1 μ2 (map mem_full_to_spec specs)
     into asn.interpret (gen_mem_pre specs) ι. *)
  Lemma gen_implpre_mem `{sailGS2 Σ}
      (specs : list mem_full_spec) (μ1 μ2 : Memory)
      {Σ0} (ι : Valuation (Σ0 ▻ "a"∷ty_xlenbits))
      (HInitMem1 : declare_init_memory μ1 (gen_init_mem specs))
      (HInitMem2 : declare_init_memory μ2 (gen_init_mem specs)) :
    interp_mem_with_public_memory μ1 μ2 (map mem_full_to_spec specs) ⊢
    asn.interpret (gen_mem_pre specs) ι.
  Proof.
    iInduction specs as [|[[a is_pub] opt_v] rest] "IH"
        forall (μ1 μ2 HInitMem1 HInitMem2).
    - iIntros "_". done.
    - cbn [map mem_full_to_spec].
      unfold interp_mem_with_public_memory. cbn [big_opL].
      iIntros "[Hhead Hrest]".
      cbn [gen_mem_pre List.fold_right asn.interpret].
      iSplitL "Hhead".
      { iApply gen_mem_asn_of_ptstomem.
        - intros v Hv.
          unfold declare_init_memory, gen_init_mem in HInitMem1.
          cbn in HInitMem1. rewrite Hv in HInitMem1.
          apply Forall_inv in HInitMem1. exact HInitMem1.
        - intros v Hv.
          unfold declare_init_memory, gen_init_mem in HInitMem2.
          cbn in HInitMem2. rewrite Hv in HInitMem2.
          apply Forall_inv in HInitMem2. exact HInitMem2.
        - iExact "Hhead". }
      iApply ("IH" $! μ1 μ2 with "[%] [%] Hrest").
      * eapply declare_init_mem_tail. exact HInitMem1.
      * eapply declare_init_mem_tail. exact HInitMem2.
  Qed.

    (* Note: these lemmas conclude the raw ∃ rather than noninterferent_strong
       because ImplPre closes over γ1/γ2 via the valuation ι, which would
       require abstracting mk_ι : RegStore → RegStore → Valuation R to make
       the conclusion universally quantified. *)
    Lemma cfg_instrs_endToEnd {γ1 γ2 γ1' : RegStore} {μ1 μ2 μ1' : Memory}
      instrs' exitCond n ws {R} {ι : Valuation R}
      public_registers
      (HpubReg : declare_public_registers γ1 γ2 public_registers)
      (contract : @CFGVerifierContract R)
      (valid_contract : ValidCFGVerifierContract contract)
      (init_addr : N)      (contractInitAddr : cfg_init_addr contract = init_addr)
      (contractInstrs : cfg_instrs contract = instrs')
      (contractExitCond : cfg_exitCond contract = exitCond)
      (contractPlacement : inst (T := fun Σ => Term Σ ty_xlenbits) (cfg_placement contract) ι
                        = ty.SyncVal (@bv.of_N xlenbits init_addr))
      (HexitsFaith : Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx R)
                       exitCond (cfg_exits contract) ι)
      (ImplPre : forall `{sailGS2 Σ},
          interp_gprs_with_public_registers γ1 γ2 public_registers ∗
          cur_privilege ↦ᵣ ty.SyncVal Machine ∗
          interp_inv_constant_time -∗
          asn.interpret (extend_to_minimal_pre (cfg_precondition contract))
            ι.["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)]) :
      (init_addr + 4 * N.of_nat (length instrs') < lenAddr)%N ->
      mem_has_instrs μ1 (bv.of_N init_addr) ws (strip instrs') ->
      mem_has_instrs μ2 (bv.of_N init_addr) ws (strip instrs') ->
      RiscvPmpProgram.read_register γ1 cur_privilege = Machine ->
      RiscvPmpProgram.read_register γ2 cur_privilege = Machine ->
      RiscvPmpProgram.read_register γ1 pc = bv.of_N init_addr ->
      RiscvPmpProgram.read_register γ2 pc = bv.of_N init_addr ->
      ⟨ γ1, μ1 ⟩ -(exitCond, n)->* ⟨ γ1', μ1' ⟩ ->
      leakage_trace μ1 = leakage_trace μ2 ->
      ∃ γ2' μ2',
        ⟨ γ2, μ2 ⟩ -(exitCond, n)->* ⟨ γ2', μ2' ⟩ ∧
        leakage_trace μ1' = leakage_trace μ2'.
    Proof.
      intros Hleninstrs μinit1 μinit2 γ1curpriv γ2curpriv γ1pc γ2pc
        steps1 Htrace.
      (* Length bound in BOTH forms: some premises below are stated over
         `strip instrs'` (the trusted ones) and others over `instrs'`; ghosts
         occupy no address so they agree (strip_length), but only up to a
         syntactic rewrite.  Normalising to ONE form was tried and merely moved
         the stranded side goal elsewhere in the script. *)
      assert (Hleninstrs_s :
                (init_addr + 4 * N.of_nat (length (strip instrs')) < lenAddr)%N)
        by (rewrite strip_length; exact Hleninstrs).
      apply (adequacy_gen_RiscVNStepsExitCond_strong
        (μ21 := μ2) (γ21 := γ2)
        (fun _ μ2' => leakage_trace μ1' = leakage_trace μ2')
        steps1).
      iIntros (Σ' H').
      iIntros "(Hmem & H')".
      iPoseProof (mem_res2_split_leak with "Hmem") as "(Hmem & Hleak)".
      iPoseProof (constant_time_from_mem_res2_only_leak with "Hleak")
        as "Hinv"; auto.
      iMod "Hinv" as "#Hinv".
      iMod (instrsMemory init_addr with "Hmem") as "H"; eauto.
      (* THE ONE BRIDGE.  instrsMemory yields the map over `strip instrs'`,
         while cfg_instrs_safe (matching Adequacy.v) wants the projection of
         the map over `instrs'`.  Equal by Tables.v's fmap_instrs_of_list; the
         `unfold strip` is needed because `strip` is not syntactically `map`,
         which is why a bare `rewrite <- fmap_instrs_of_list` finds no
         subterm. *)
      assert (Hbridge : instrs_of_list (bv.of_N init_addr) (strip instrs')
                      = ai_instr <$> instrs_of_list (bv.of_N init_addr) instrs')
        by (unfold strip; now rewrite fmap_instrs_of_list).
      iEval (rewrite Hbridge) in "H".
      iSplitR "".
      - iApply (cfg_instrs_safe γ1 γ2 contract).
        all: eauto.
        iIntros "(Hregs & Hpriv & #Hinv')".
        iApply ImplPre.
        iFrame "∗ #".
        by iFrame "∗ #".
      - iModIntro.
        iIntros (γ22 μ22) "Rmem".
        iInv "Hinv" as "Hleak".
        iPoseProof (mem_inv2_split_leak with "Rmem") as "(Rmem & [Htr1 Htr2])".
        unfold mem_inv_only_leak.
        iMod "Hleak".
        iDestruct "Hleak" as "[%t [Hfrag1 Hfrag2]]".
        iDestruct (trace.trace_full_frag_eq with "Htr1 Hfrag1") as "->".
        iDestruct (trace.trace_full_frag_eq with "Htr2 Hfrag2") as "->".
        iModIntro. iFrame.
        iApply fupd_mask_intro; first set_solver.
        now iIntros "_".
    Qed.

  (* ------------------------------------------------------------------ *)
  (* cfg_instrs_endToEnd_with_memory                                     *)
  (* Like cfg_instrs_endToEnd, but also passes data memory ownership     *)
  (* to ImplPre via interp_mem_with_public_memory.                       *)
  (* data_specs describes the data words at init_addr + 4*|instrs| + …  *)
  (* (contiguous layout immediately after the instruction region).       *)
  (* ------------------------------------------------------------------ *)
    Lemma cfg_instrs_endToEnd_with_memory
        {γ1 γ2 γ1' : RegStore} {μ1 μ2 μ1' : Memory}
        instrs' exitCond n ws_instrs {R} {ι : Valuation R}
        public_registers
        (HpubReg : declare_public_registers γ1 γ2 public_registers)
        data_specs
        (HpubMem : declare_public_memory μ1 μ2 (gen_public_addrs data_specs))
        (contract : @CFGVerifierContract R)
        (valid_contract : ValidCFGVerifierContract contract)
        (init_addr : N)        (contractInitAddr : cfg_init_addr contract = init_addr)
        (contractInstrs : cfg_instrs contract = instrs')
        (contractExitCond : cfg_exitCond contract = exitCond)
        (contractPlacement : inst (T := fun Σ => Term Σ ty_xlenbits) (cfg_placement contract) ι
                          = ty.SyncVal (@bv.of_N xlenbits init_addr))
        (HexitsFaith : Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx R)
                         exitCond (cfg_exits contract) ι)
        (HDataAddrs : ∀ i spec, data_specs !! i = Some spec →
            spec.1 = bv.of_N (init_addr + 4 * N.of_nat (length instrs')
                               + 4 * N.of_nat i))
        (ImplPre : forall `{sailGS2 Σ},
            interp_gprs_with_public_registers γ1 γ2 public_registers ∗
            interp_mem_with_public_memory μ1 μ2 data_specs ∗
            cur_privilege ↦ᵣ ty.SyncVal Machine ∗
            interp_inv_constant_time -∗
            asn.interpret (extend_to_minimal_pre (cfg_precondition contract))
              ι.["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)]) :
        (init_addr + 4 * N.of_nat (length instrs') +
         4 * N.of_nat (length data_specs) < lenAddr)%N →
        mem_has_instrs μ1 (bv.of_N init_addr) ws_instrs (strip instrs') →
        mem_has_instrs μ2 (bv.of_N init_addr) ws_instrs (strip instrs') →
        RiscvPmpProgram.read_register γ1 cur_privilege = Machine →
        RiscvPmpProgram.read_register γ2 cur_privilege = Machine →
        RiscvPmpProgram.read_register γ1 pc = bv.of_N init_addr →
        RiscvPmpProgram.read_register γ2 pc = bv.of_N init_addr →
        ⟨ γ1, μ1 ⟩ -(exitCond, n)->* ⟨ γ1', μ1' ⟩ →
        leakage_trace μ1 = leakage_trace μ2 →
        ∃ γ2' μ2',
          ⟨ γ2, μ2 ⟩ -(exitCond, n)->* ⟨ γ2', μ2' ⟩ ∧
          leakage_trace μ1' = leakage_trace μ2'.
    Proof.
      intros Hlen μinit1 μinit2 γ1curpriv γ2curpriv γ1pc γ2pc
        steps1 Htrace.
      assert (Hleninstrs : (init_addr + 4 * N.of_nat (length instrs') < lenAddr)%N)
        by (unfold lenAddr in *; lia).
      (* instrsAndDataMemory is instantiated at `strip instrs'`, so its length
         premise is over the stripped list while Hlen is over instrs'.  Ghosts
         occupy no address (strip_length), but the two differ syntactically. *)
      assert (Hlen_s : (init_addr + 4 * N.of_nat (length (strip instrs')) +
                        4 * N.of_nat (length data_specs) < lenAddr)%N)
        by (rewrite strip_length; exact Hlen).
      assert (HDataAddrs_s :
                ∀ (i : nat) (spec : bv word * bool),
                  data_specs !! i = Some spec ->
                  spec.1 = bv.of_N (init_addr
                                    + 4 * N.of_nat (length (strip instrs'))
                                    + 4 * N.of_nat i))
        by (rewrite strip_length; exact HDataAddrs).
      apply (adequacy_gen_RiscVNStepsExitCond_strong
        (μ21 := μ2) (γ21 := γ2)
        (fun _ μ2' => leakage_trace μ1' = leakage_trace μ2')
        steps1).
      iIntros (Σ' H').
      iIntros "(Hmem & H')".
      iPoseProof (mem_res2_split_leak with "Hmem") as "(Hmem & Hleak)".
      iPoseProof (constant_time_from_mem_res2_only_leak with "Hleak")
        as "Hinv"; auto.
      iMod "Hinv" as "#Hinv".
      (* Extract instruction + data memory from raw byte ownership *)
      iMod (instrsAndDataMemory init_addr ws_instrs data_specs (strip instrs') with "Hmem") as "[H Hmemdata]";
        [exact Hlen_s | exact μinit1 | exact μinit2 | exact HDataAddrs_s |].
      (* Same single bridge as cfg_instrs_endToEnd — see the note there. *)
      assert (Hbridge : instrs_of_list (bv.of_N init_addr) (strip instrs')
                      = ai_instr <$> instrs_of_list (bv.of_N init_addr) instrs')
        by (unfold strip; now rewrite fmap_instrs_of_list).
      iEval (rewrite Hbridge) in "H".
      (* Convert all-NonSyncVal to public form *)
      rewrite (something_memory data_specs HpubMem).
      iSplitR "".
      - iApply (cfg_instrs_safe_with_mem γ1 γ2 data_specs μ1 μ2 contract).
        all: eauto.
        iIntros "(Hregs & Hmem & Hpriv & #Hinv')".
        iApply ImplPre.
        rewrite <- (something_registers HpubReg).
        iFrame "Hmem ∗ #".
        by iFrame "∗ #".
      - iModIntro.
        iIntros (γ22 μ22) "Rmem".
        iInv "Hinv" as "Hleak".
        iPoseProof (mem_inv2_split_leak with "Rmem") as "(Rmem & [Htr1 Htr2])".
        unfold mem_inv_only_leak.
        iMod "Hleak".
        iDestruct "Hleak" as "[%t [Hfrag1 Hfrag2]]".
        iDestruct (trace.trace_full_frag_eq with "Htr1 Hfrag1") as "->".
        iDestruct (trace.trace_full_frag_eq with "Htr2 Hfrag2") as "->".
        iModIntro. iFrame.
        iApply fupd_mask_intro; first set_solver.
        now iIntros "_".
    Qed.

  (* gen_contract_noninterferent_param is defined further down, with the other
     thin delegations, after the unified pair gen_contract_noninterferent_u /
     _u_simple that they all delegate to (PLAN-unify-generators.md stage 3b). *)

  Lemma gen_pre_rel_concretize `{sailGS2 Σ}
      (reg_specs : list reg_spec_rel) (ia : N) (va : RelVal ty_xlenbits) :
    asn.interpret (gen_pre_rel reg_specs)
      ([env].["p"∷ty_xlenbits ↦ SyncVal (bv.of_N ia)].["a"∷ty_xlenbits ↦ va])
    = asn.interpret (gen_pre (map (concretize_reg ia) reg_specs))
      ([env].["p"∷ty_xlenbits ↦ SyncVal (bv.of_N ia)].["a"∷ty_xlenbits ↦ va]).
  Proof.
    induction reg_specs as [|[[r pub] pv] rest IH]; [reflexivity|].
    cbn [gen_pre_rel gen_pre map List.fold_right].
    cbn [asn.interpret]. f_equal; [|exact IH].
    destruct pv; cbn.
    - reflexivity.
    - reflexivity.
    - unfold asn_regidx_pts.
      destruct (reg_convert r) as [reg|]; cbn; [|reflexivity].
      cbn [ty.valToRelVal]. do 2 f_equal. apply bv.of_N_add.
  Qed.

  Lemma gen_mem_pre_rel_concretize `{sailGS2 Σ}
      (mem_specs : list mem_spec_rel) (ia : N) (va : RelVal ty_xlenbits) :
    asn.interpret (gen_mem_pre_rel mem_specs)
      ([env].["p"∷ty_xlenbits ↦ SyncVal (bv.of_N ia)].["a"∷ty_xlenbits ↦ va])
    = asn.interpret (gen_mem_pre (map (concretize_mem ia) mem_specs))
      ([env].["p"∷ty_xlenbits ↦ SyncVal (bv.of_N ia)].["a"∷ty_xlenbits ↦ va]).
  Proof.
    induction mem_specs as [|[[k pub] pv] rest IH]; [reflexivity|].
    cbn [gen_mem_pre_rel gen_mem_pre map List.fold_right].
    cbn [asn.interpret]. f_equal; [|exact IH].
    destruct pv; cbn.
    2: { cbn [ty.valToRelVal]. do 2 f_equal. apply bv.of_N_add. }
    2: { cbn [ty.valToRelVal]. f_equal; (f_equal; apply bv.of_N_add). }
    destruct pub; cbn.
    all: cbn [ty.valToRelVal]; rewrite bv.of_N_add; reflexivity.
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* CLASSED memory ImplPre (PLAN-classed-existentials.md Phase 3, step 2).   *)
  (*                                                                        *)
  (* The counterpart of gen_implpre_mem for gen_mem_pre_rel_classed.  Unlike   *)
  (* the _rel path there is NO concretize rewrite to lean on -- see the note   *)
  (* at gen_mem_pre_rel_classed in GenContract.v on why no concrete classed    *)
  (* builder can exist (the two sides' existential widths agree only           *)
  (* propositionally) -- so this attacks the rel assertion directly:            *)
  (*                                                                        *)
  (*   interp_mem_partition_rel  splits the resources three ways,              *)
  (*   gen_implpre_mem           handles the PINNED group (via the concretize   *)
  (*                             rewrite, which IS available for that group),  *)
  (*   interp_mem_group_{pub,priv} + gen_mem_{pub,priv}_class_ks_intro          *)
  (*                             handle the two grouped-existential classes.   *)
  (* ---------------------------------------------------------------------- *)
  Lemma gen_implpre_mem_class `{sailGS2 Σ}
      (specs : list mem_spec_rel) (ia : N) (μ1 μ2 : Memory)
      (va : RelVal ty_xlenbits)
      (HInitMem1 : declare_init_memory μ1 (gen_init_mem (map (concretize_mem ia) specs)))
      (HInitMem2 : declare_init_memory μ2 (gen_init_mem (map (concretize_mem ia) specs))) :
    interp_mem_with_public_memory μ1 μ2
      (map mem_full_to_spec (map (concretize_mem ia) specs))
    ⊢ asn.interpret (gen_mem_pre_rel_classed specs)
        ([env].["p"∷ty_xlenbits ↦ SyncVal (bv.of_N ia)].["a"∷ty_xlenbits ↦ va]).
  Proof.
    assert (Hpin1 : declare_init_memory μ1 (gen_init_mem (map (concretize_mem ia)
              (List.filter (fun s => negb (mem_spec_is_exist s)) specs)))).
    { rewrite gen_init_mem_filter_pinned. exact HInitMem1. }
    assert (Hpin2 : declare_init_memory μ2 (gen_init_mem (map (concretize_mem ia)
              (List.filter (fun s => negb (mem_spec_is_exist s)) specs)))).
    { rewrite gen_init_mem_filter_pinned. exact HInitMem2. }
    iIntros "H".
    iDestruct (interp_mem_partition_rel with "H") as "(Hpin & Hpub & Hpriv)".
    unfold gen_mem_pre_rel_classed. cbn [asn.interpret].
    iSplitL "Hpin".
    { rewrite gen_mem_pre_rel_concretize.
      iApply (gen_implpre_mem (map (concretize_mem ia)
                (List.filter (fun s => negb (mem_spec_is_exist s)) specs)) _ Hpin1 Hpin2).
      iExact "Hpin". }
    iSplitL "Hpub".
    { unfold gen_mem_pub_class_rel.
      iApply (gen_mem_pub_class_ks_intro _ (bv.of_N ia) va μ1).
      iApply (interp_mem_group_pub μ1 μ2 ia _).
      - intros s Hs. apply filter_In in Hs. destruct Hs as [_ Hf].
        destruct (andb_prop _ _ Hf) as [_ Hb]. exact Hb.
      - iExact "Hpub". }
    unfold gen_mem_priv_class_rel.
    iApply (gen_mem_priv_class_ks_intro _ (bv.of_N ia) va μ1 μ2).
    iApply (interp_mem_group_priv μ1 μ2 ia _).
    - intros s Hs. apply filter_In in Hs. destruct Hs as [_ Hf].
      destruct (andb_prop _ _ Hf) as [_ Hb]. apply negb_true_iff. exact Hb.
    - iExact "Hpriv".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Byte-granular counterpart of gen_mem_pre_rel_concretize
     (PLAN-check-scalar-full.md §3): pure asn.interpret equality, no Iris.
     Each entry now needs FOUR address reconciliations (one per byte
     offset j = 0..3) instead of one. *)
  Lemma addr_reconcile (ia k j : N) :
    @bv.add xlenbits (bv.of_N ia) (bv.of_N (k+j)) = @bv.add xlenbits (bv.of_N (ia+k)) (bv.of_N j).
  Proof. rewrite bv.of_N_add. rewrite bv.of_N_add. f_equal. lia. Qed.

  Lemma gen_mem_pre_rel_bytes_concretize `{sailGS2 Σ}
      (mem_specs : list mem_spec_rel) (ia : N) (va : RelVal ty_xlenbits) :
    asn.interpret (gen_mem_pre_rel_bytes mem_specs)
      ([env].["p"∷ty_xlenbits ↦ SyncVal (bv.of_N ia)].["a"∷ty_xlenbits ↦ va])
    = asn.interpret (gen_mem_pre_bytes (map (concretize_mem ia) mem_specs))
      ([env].["p"∷ty_xlenbits ↦ SyncVal (bv.of_N ia)].["a"∷ty_xlenbits ↦ va]).
  Proof.
    induction mem_specs as [|[[k pub] pv] rest IH]; [reflexivity|].
    cbn [gen_mem_pre_rel_bytes gen_mem_pre_bytes map List.fold_right].
    cbn [asn.interpret]. f_equal; [|exact IH].
    destruct pv; cbn.
    - rewrite (addr_reconcile ia k 0). rewrite (addr_reconcile ia k 1).
      rewrite (addr_reconcile ia k 2). rewrite (addr_reconcile ia k 3).
      reflexivity.
    - rewrite (addr_reconcile ia k 0). rewrite (addr_reconcile ia k 1).
      rewrite (addr_reconcile ia k 2). rewrite (addr_reconcile ia k 3).
      reflexivity.
    - rewrite (addr_reconcile ia k 0). rewrite (addr_reconcile ia k 1).
      rewrite (addr_reconcile ia k 2). rewrite (addr_reconcile ia k 3).
      rewrite bv.of_N_add. rewrite bv.of_N_add.
      reflexivity.
  Qed.

  (* Byte-granular counterpart of gen_implpre_mem: list-level induction over
     gen_implpre_mem_bytes's per-entry bridge gen_mem_asn_of_ptstomem_bytes. *)
  Lemma gen_implpre_mem_bytes `{sailGS2 Σ}
      (specs : list mem_full_spec) (μ1 μ2 : Memory)
      {Σ0} (ι : Valuation Σ0)
      (HInitMem1 : declare_init_memory μ1 (gen_init_mem specs))
      (HInitMem2 : declare_init_memory μ2 (gen_init_mem specs)) :
    interp_mem_with_public_memory μ1 μ2 (map mem_full_to_spec specs) ⊢
    asn.interpret (gen_mem_pre_bytes specs) ι.
  Proof.
    iInduction specs as [|[[a is_pub] opt_v] rest] "IH"
        forall (μ1 μ2 HInitMem1 HInitMem2).
    - iIntros "_". done.
    - cbn [map mem_full_to_spec].
      unfold interp_mem_with_public_memory. cbn [big_opL].
      iIntros "[Hhead Hrest]".
      cbn [gen_mem_pre_bytes List.fold_right asn.interpret].
      iSplitL "Hhead".
      { iApply gen_mem_asn_of_ptstomem_bytes.
        - intros v Hv.
          unfold declare_init_memory, gen_init_mem in HInitMem1.
          cbn in HInitMem1. rewrite Hv in HInitMem1.
          apply Forall_inv in HInitMem1. exact HInitMem1.
        - intros v Hv.
          unfold declare_init_memory, gen_init_mem in HInitMem2.
          cbn in HInitMem2. rewrite Hv in HInitMem2.
          apply Forall_inv in HInitMem2. exact HInitMem2.
        - iExact "Hhead". }
      iApply ("IH" $! μ1 μ2 with "[%] [%] Hrest").
      * eapply declare_init_mem_tail. exact HInitMem1.
      * eapply declare_init_mem_tail. exact HInitMem2.
  Qed.

  (* Three-way-partition ImplPre for the BYTE-granular classed block
     (PLAN-unify-generators.md stage 2).  Byte twin of gen_implpre_mem_class:
     same partition, same pinned-group treatment, but the two grouped classes go
     through the _bytes class intros and the pinned group through
     gen_mem_pre_rel_bytes_concretize + gen_implpre_mem_bytes.

     Note gen_mem_pre_rel_bytes_classed names gen_mem_{pub,priv}_class_ks_bytes
     with mem_rel_keys inline, so unlike the word case there is no
     gen_mem_*_class_rel wrapper to unfold first. *)
  Lemma gen_implpre_mem_bytes_class `{sailGS2 Σ}
      (specs : list mem_spec_rel) (ia : N) (μ1 μ2 : Memory)
      (va : RelVal ty_xlenbits)
      (HInitMem1 : declare_init_memory μ1 (gen_init_mem (map (concretize_mem ia) specs)))
      (HInitMem2 : declare_init_memory μ2 (gen_init_mem (map (concretize_mem ia) specs))) :
    interp_mem_with_public_memory μ1 μ2
      (map mem_full_to_spec (map (concretize_mem ia) specs))
    ⊢ asn.interpret (gen_mem_pre_rel_bytes_classed specs)
        ([env].["p"∷ty_xlenbits ↦ SyncVal (bv.of_N ia)].["a"∷ty_xlenbits ↦ va]).
  Proof.
    assert (Hpin1 : declare_init_memory μ1 (gen_init_mem (map (concretize_mem ia)
              (List.filter (fun s => negb (mem_spec_is_exist s)) specs)))).
    { rewrite gen_init_mem_filter_pinned. exact HInitMem1. }
    assert (Hpin2 : declare_init_memory μ2 (gen_init_mem (map (concretize_mem ia)
              (List.filter (fun s => negb (mem_spec_is_exist s)) specs)))).
    { rewrite gen_init_mem_filter_pinned. exact HInitMem2. }
    iIntros "H".
    iDestruct (interp_mem_partition_rel with "H") as "(Hpin & Hpub & Hpriv)".
    unfold gen_mem_pre_rel_bytes_classed. cbn [asn.interpret].
    iSplitL "Hpin".
    { rewrite gen_mem_pre_rel_bytes_concretize.
      iApply (gen_implpre_mem_bytes (map (concretize_mem ia)
                (List.filter (fun s => negb (mem_spec_is_exist s)) specs)) _ Hpin1 Hpin2).
      iExact "Hpin". }
    iSplitL "Hpub".
    { iApply (gen_mem_pub_class_ks_bytes_intro _ (bv.of_N ia) va μ1).
      iApply (interp_mem_group_pub μ1 μ2 ia _).
      - intros s Hs. apply filter_In in Hs. destruct Hs as [_ Hf].
        destruct (andb_prop _ _ Hf) as [_ Hb]. exact Hb.
      - iExact "Hpub". }
    iApply (gen_mem_priv_class_ks_bytes_intro _ (bv.of_N ia) va μ1 μ2).
    iApply (interp_mem_group_priv μ1 μ2 ia _).
    - intros s Hs. apply filter_In in Hs. destruct Hs as [_ Hf].
      destruct (andb_prop _ _ Hf) as [_ Hb]. apply negb_true_iff. exact Hb.
    - iExact "Hpriv".
  Qed.

  (* ===================================================================== *)
  (* THE UNIFIED BRIDGE (PLAN-unify-generators.md stage 3b).                *)
  (*                                                                        *)
  (* One noninterference bridge over gen_contract_u, carrying BOTH a         *)
  (* word-granular classed block and a byte-granular block.  This is the     *)
  (* generalisation the (now-deleted) gen_contract_noninterferent_rel_bytes'  *)
  (* own header comment asked for -- it fixed its word list to [] "to avoid   *)
  (* threading a big_sepL_app list-append split through the ImplPre proof    *)
  (* for a case nothing exercises", and said to generalise "if that need     *)
  (* ever arises".  Unifying the family is that need, so the split is done   *)
  (* here once, in interp_mem_app / gen_init_mem_app below.                  *)
  (*                                                                        *)
  (* The trusted side sees ONE data list, word_data ++ byte_data, matching   *)
  (* the concatenation gen_contract_rel_bytes already assumed on that side   *)
  (* (GenContract.v) -- so HDataAddrs' contiguous layout is unchanged, and    *)
  (* callers keep word cells first.                                          *)
  (* ===================================================================== *)

  (* Append split for the data resource.  interp_mem_with_public_memory is a
     big_sepL over the mapped list, so this is just map_app + big_sepL_app --
     the same shape big_sepL_three_way / interp_mem_partition already exploit
     for the three-way publicness split. *)
  Lemma interp_mem_app `{sailGS2 Σ} (μ1 μ2 : Memory) (A B : list mem_full_spec) :
    interp_mem_with_public_memory μ1 μ2 (map mem_full_to_spec (A ++ B))
    ⊢ interp_mem_with_public_memory μ1 μ2 (map mem_full_to_spec A)
      ∗ interp_mem_with_public_memory μ1 μ2 (map mem_full_to_spec B).
  Proof.
    unfold interp_mem_with_public_memory.
    rewrite map_app.
    rewrite big_sepL_app.
    done.
  Qed.

  (* gen_init_mem is a base.omap, which distributes over append; so the
     caller's single declare_init_memory hypothesis splits into one per block. *)
  (* stdpp already has omap_app; do NOT hand-roll the induction -- `cbn` rewrites
     `omap` to `list_omap` while the IH keeps it folded, so `rewrite IH` then fails
     with "found no subterm" (verified on a scratch probe). *)
  Lemma gen_init_mem_app (A B : list mem_full_spec) :
    gen_init_mem (A ++ B) = gen_init_mem A ++ gen_init_mem B.
  Proof. unfold gen_init_mem. apply omap_app. Qed.

  Lemma declare_init_mem_app (μ : Memory) (A B : list mem_full_spec) :
    declare_init_memory μ (gen_init_mem (A ++ B)) ->
    declare_init_memory μ (gen_init_mem A) /\ declare_init_memory μ (gen_init_mem B).
  Proof.
    unfold declare_init_memory.
    rewrite gen_init_mem_app.
    intros HF.
    apply Forall_app in HF.
    exact HF.
  Qed.

  Lemma gen_contract_noninterferent_u
      (reg_specs : list reg_spec_rel)
      (word_data : list mem_spec_rel)
      (byte_data : list mem_spec_rel)
      (instrs : list AnnotInstr)
      (extra_exit_offs : list N)
      (bound : N)
      (exitCond : bv xlenbits -> bool)
      (fuel : nat)
      (init_addr : N)
      (HND : NoDup (map reg_spec_idx (map (concretize_reg init_addr) reg_specs)))
      (HDataAddrs : ∀ i spec,
          (map mem_full_to_spec
             (map (concretize_mem init_addr) (word_data ++ byte_data))) !! i = Some spec →
          spec.1 = bv.of_N (init_addr + 4 * N.of_nat (length instrs)
                             + 4 * N.of_nat i))
      (Hlen : (init_addr + 4 * N.of_nat (length instrs) +
               4 * N.of_nat (length (word_data ++ byte_data)) < lenAddr)%N)
      (Hbound : (init_addr + bound < lenAddr)%N)
      (HexitOffs : List.Forall
          (fun o => exitCond (bv.add (bv.of_N init_addr) (bv.of_N o)) = true)
          ((4 * N.of_nat (length instrs))%N :: extra_exit_offs))
      (valid_contract : ValidCFGVerifierContract
          (gen_contract_u init_addr reg_specs word_data byte_data instrs
             extra_exit_offs bound exitCond fuel)) :
    noninterferent_strong init_addr (strip instrs) exitCond
      (map (concretize_reg init_addr) reg_specs)
      (map (concretize_mem init_addr) (word_data ++ byte_data)).
  Proof.
    intros γ1 γ2 μ1 μ2 ws Hmem1 Hmem2 HpubReg HpubMem
      HInitReg1 HInitReg2 HInitMem1 HInitMem2
      γ1curpriv γ2curpriv γ1pc γ2pc Htrace n γ1' μ1' steps1.
    assert (HexitsFaith : Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx ["p"∷ty_xlenbits]) exitCond
      (exits_of_offs (term_var "p")
         ((4 * N.of_nat (length instrs))%N :: extra_exit_offs))
      ([env].["p"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)])).
    { apply etable_faith_exits_of_offs with (cbase := bv.of_N init_addr);
        [reflexivity | exact HexitOffs]. }
    (* Split the caller's single declare_init_memory pair, one per block. *)
    rewrite map_app in HInitMem1.
    rewrite map_app in HInitMem2.
    apply declare_init_mem_app in HInitMem1.
    apply declare_init_mem_app in HInitMem2.
    destruct HInitMem1 as [HInitMem1w HInitMem1b].
    destruct HInitMem2 as [HInitMem2w HInitMem2b].
    eapply (@cfg_instrs_endToEnd_with_memory γ1 γ2 γ1' μ1 μ2 μ1'
      instrs exitCond n ws
      ["p"∷ty_xlenbits] ([env].["p"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)])
      (gen_public_regs (map (concretize_reg init_addr) reg_specs)) HpubReg
      (map mem_full_to_spec (map (concretize_mem init_addr) (word_data ++ byte_data))) HpubMem
      (gen_contract_u init_addr reg_specs word_data byte_data instrs extra_exit_offs
         bound exitCond fuel)
      valid_contract
      init_addr
      eq_refl eq_refl eq_refl eq_refl HexitsFaith HDataAddrs).
    all: try eauto.
    2: { rewrite !length_map. exact Hlen. }
    intros Σ H.
    iIntros "(Hregs & Hmemdata & Hpriv & #Hinv)".
    cbn.
    iFrame "Hpriv #".
    iSplitL "".
    { iSplit; [iPureIntro | done]. cbn [ty.valToRelVal]. reflexivity. }
    iSplitL "".
    { iSplit; [iPureIntro | done]. unfold bv.unsigned.
      assert (Hexp : (1024 < bv.exp2 xlenbits)%N) by (vm_compute; reflexivity).
      assert (Hib : (init_addr < bv.exp2 xlenbits)%N).
      { unfold lenAddr in Hbound. set (E := bv.exp2 xlenbits) in *; clearbody E. lia. }
      rewrite (bv.bin_of_N_small Hib). unfold lenAddr in *. lia. }
    iSplitL "Hregs".
    { rewrite gen_pre_rel_concretize.
      iApply (gen_implpre (map (concretize_reg init_addr) reg_specs) _ HpubReg HND HInitReg1 HInitReg2).
      iExact "Hregs". }
    (* Now the two data blocks.  Split the resource the same way the
       hypotheses were split above, then hand each half to its own ImplPre.
       μ1/μ2 stay IMPLICIT in both gen_implpre_mem_* lemmas -- positional and
       μ-free is the only form that elaborates; passing them positionally reports
       "μ1 has type Memory while RelVal ty_xlenbits was expected", and the fully
       named form fails too (Coq's `(x := v)` accepts implicit names only).  See
       cfgver-endtoend-internals, "the CLASSED memory ImplPre". *)
    rewrite map_app.
    iDestruct (interp_mem_app with "Hmemdata") as "(Hword & Hbyte)".
    iSplitL "Hword".
    { iApply (gen_implpre_mem_class word_data init_addr _ HInitMem1w HInitMem2w).
      iExact "Hword". }
    (* Byte half now goes through the CLASSED ImplPre (stage 2), symmetrically
       with the word half above -- no concretize rewrite is needed, because
       gen_implpre_mem_bytes_class attacks the rel assertion directly for the same
       width-index reason gen_implpre_mem_class does. *)
    iApply (gen_implpre_mem_bytes_class byte_data init_addr _
              HInitMem1b HInitMem2b).
    iExact "Hbyte".
  Qed.

  (* Common-case specialisation: no extra exits, standard fall-through exit.
     The single bridge every example should use. *)
  Lemma gen_contract_noninterferent_u_simple
      (reg_specs : list reg_spec_rel)
      (word_data : list mem_spec_rel)
      (byte_data : list mem_spec_rel)
      (instrs : list AnnotInstr) (bound : N) (fuel : nat) (init_addr : N)
      (HND : NoDup (map reg_spec_idx (map (concretize_reg init_addr) reg_specs)))
      (HDataAddrs : ∀ i spec,
          (map mem_full_to_spec
             (map (concretize_mem init_addr) (word_data ++ byte_data))) !! i = Some spec →
          spec.1 = bv.of_N (init_addr + 4 * N.of_nat (length instrs)
                             + 4 * N.of_nat i))
      (Hlen : (init_addr + 4 * N.of_nat (length instrs) +
               4 * N.of_nat (length (word_data ++ byte_data)) < lenAddr)%N)
      (Hbound : (init_addr + bound < lenAddr)%N)
      (valid_contract : ValidCFGVerifierContract
          (gen_contract_u init_addr reg_specs word_data byte_data instrs []
             bound (pcOutOfInstrs_exitCond init_addr (strip instrs)) fuel)) :
    noninterferent_strong init_addr (strip instrs)
      (pcOutOfInstrs_exitCond init_addr (strip instrs))
      (map (concretize_reg init_addr) reg_specs)
      (map (concretize_mem init_addr) (word_data ++ byte_data)).
  Proof.
    eapply gen_contract_noninterferent_u.
    6: exact valid_contract.
    - exact HND.
    - exact HDataAddrs.
    - exact Hlen.
    - exact Hbound.
    (* `<- strip_length`: pcOutOfInstrs_fallthrough is instantiated at
       `strip instrs`, so it wants `length (strip instrs)` where the goal has
       `length instrs`.  Ghosts occupy no address, so these agree. *)
    - constructor;
        [rewrite <- (strip_length instrs); apply pcOutOfInstrs_fallthrough
        | constructor].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* Thin delegations onto the unified pair above (stage 3b).  These keep    *)
  (* their callers unchanged -- all 13 Example/*Result.v proofs and every     *)
  (* end-theorem STATEMENT are byte-identical across this refactor -- and     *)
  (* they absorb the append/naming ritual that calling _u directly would     *)
  (* otherwise export to each call site.  Only TWO real implementations       *)
  (* remain: gen_contract_noninterferent_u and _u_simple.                     *)
  (* The three GENERAL bridges these replaced (_rel over gen_contract_rel,    *)
  (* _rel_classed, _rel_bytes) were deleted 2026-08-18 -- they had no callers *)
  (* once the _simple forms were re-pointed here.                             *)
  (* ------------------------------------------------------------------- *)


  (* Parameterized-base noninterference bridge for a REGISTER-ONLY program
     (PLAN Phase 4.2).  Consumes the symbolic-base contract gen_contract_param
     (Σ = ["p"]); the symbolic VC is proved ONCE, uniformly in init_addr, and
     reused here for every concrete init_addr -- no per-address vm_compute.

     Two ancestors are gone, both 2026-08-18 (PLAN-unify-generators.md):
     stage 0 deleted the non-parametric gen_contract_noninterferent (over
     gen_contract at a literal base) as dead -- recover it from git history if a
     concrete-base end theorem is ever wanted.  Stage 1 replaced this lemma's own
     ~40-line copy of the cfg_instrs_endToEnd_with_memory + ImplPre ritual with a
     DELEGATION -- then to gen_contract_noninterferent_rel_classed, and since
     stage 3b straight to gen_contract_noninterferent_u (that intermediate bridge
     is now deleted).  It type-checks because, at word_data = byte_data = [],
     _rel_classed's conclusion
       noninterferent_strong .. (map (concretize_reg ia) rs_rel)
                                (map (concretize_mem ia) [])
     collapses to this one's: the memory list is [] definitionally, and the
     register list is reg_specs by map_concretize_reg_to_rel -- concretize_reg
     inverts reg_spec_to_rel at EVERY base, since a constant-value reg_spec is by
     construction base-independent.  That equation is not definitional for a
     variable list, which is why the proof opens by rewriting the goal into the
     concretized form rather than applying directly.

     Note there is no HDataAddrs premise any more (it quantified over the deleted
     mem_specs, and is vacuous at []), and Hlen lost its 4*|mem_specs| term. *)
  Lemma gen_contract_noninterferent_param
      (reg_specs : list reg_spec)
      (instrs : list AnnotInstr)
      (extra_exit_offs : list N)
      (exitCond : bv xlenbits -> bool)
      (fuel : nat)
      (init_addr : N)      (HND : NoDup (map reg_spec_idx reg_specs))
      (Hlen : (init_addr + 4 * N.of_nat (length instrs) < lenAddr)%N)
      (HexitOffs : List.Forall
          (fun o => exitCond (bv.add (bv.of_N init_addr) (bv.of_N o)) = true)
          ((4 * N.of_nat (length instrs))%N :: extra_exit_offs))
      (valid_contract : ValidCFGVerifierContract
          (gen_contract_param init_addr reg_specs instrs extra_exit_offs
             exitCond fuel)) :
    noninterferent_strong init_addr (strip instrs) exitCond reg_specs [].
  Proof.
    rewrite <- (map_concretize_reg_to_rel init_addr reg_specs).
    (* Every data argument of _rel_classed is IMPLICIT (each occurs in some
       premise's type, under Set Implicit Arguments), so none may be passed
       POSITIONALLY -- doing so reports `"map reg_spec_to_rel reg_specs" has type
       "list reg_spec_rel" while it is expected to have type "NoDup (...)"`, i.e.
       the first argument is read as HND.  The `(name := v)` form is exactly what
       implicits accept.

       Four of them are NOT determined by the conclusion -- mem_specs and
       extra_exit_offs, fuel and bound -- so they are pinned here by name.  Pinning
       mem_specs is not optional: the conclusion's data slot is
       `map (concretize_mem init_addr) ?mem_specs` against our `[]`, and
       unification will NOT solve `map f ?l == []` (verified: it fails with
       "Unable to unify map S ?M = map S ?M with [] = []").  Given by name it goes
       through by CONVERSION instead, since `map f [] == []` definitionally.
       With all four pinned nothing floats, so the usual
       "discharge valid_contract FIRST" ordering hazard cannot arise and the
       premises may be discharged in order. *)
    eapply (gen_contract_noninterferent_u
              (word_data := []) (byte_data := [])
              (extra_exit_offs := extra_exit_offs)
              (bound := (4 * N.of_nat (length instrs))%N) (fuel := fuel)).
    - rewrite map_concretize_reg_to_rel. exact HND.
    - intros i spec Hlk; cbn in Hlk; discriminate.
    - cbn. lia.
    - exact Hlen.
    - exact HexitOffs.
    - exact valid_contract.
  Qed.


  (* ---------------------------------------------------------------------- *)
  (* Common-case bridges.                                                   *)
  (*                                                                        *)
  (* gen_contract_noninterferent_param / _rel take five (resp. six) side    *)
  (* premises, three of which are mechanical for the overwhelmingly common  *)
  (* program shape: NO data memory (param), NO exit other than falling off  *)
  (* the end, and the standard pcOutOfInstrs_exitCond.  The two bridges     *)
  (* below specialise to that shape and discharge the mechanical premises   *)
  (* (the vacuous/empty HDataAddrs for _param, the single fall-through      *)
  (* HexitOffs, the +0 in Hlen) internally, so a caller supplies only the   *)
  (* genuinely program-specific facts and the VC.                           *)
  (*                                                                        *)
  (* A subtle side benefit: in the GENERAL bridges, mem_specs /             *)
  (* extra_exit_offs / exitCond are unification metavariables shared across *)
  (* every side goal, which is what makes the "discharge valid_contract     *)
  (* FIRST or unification picks the wrong goal" hazard bite.  Here those    *)
  (* three are FIXED by the statement, so only `fuel` floats and it appears *)
  (* solely in the VC premise -- the ordering hazard simply cannot arise,   *)
  (* and callers may discharge the remaining premises in any order.         *)

  (* Register-only, straight-line (fall-through exit) programs. *)
  Lemma gen_contract_noninterferent_param_simple
      (reg_specs : list reg_spec) (instrs : list AnnotInstr) (fuel : nat) (init_addr : N)
      (HND : NoDup (map reg_spec_idx reg_specs))
      (Hlen : (init_addr + 4 * N.of_nat (length instrs) < lenAddr)%N)
      (valid_contract : ValidCFGVerifierContract
          (gen_contract_param init_addr reg_specs instrs []
             (pcOutOfInstrs_exitCond init_addr (strip instrs)) fuel)) :
    noninterferent_strong init_addr (strip instrs)
      (pcOutOfInstrs_exitCond init_addr (strip instrs)) reg_specs [].
  Proof.
    (* one premise fewer since stage 1: _param's HDataAddrs quantified over the
       deleted mem_specs, so the vacuous-lookup bullet is gone and the VC moved
       from position 5 to 4. *)
    eapply gen_contract_noninterferent_param.
    4: exact valid_contract.
    - exact HND.
    - cbn. lia.
    (* `<- strip_length`: pcOutOfInstrs_fallthrough is instantiated at
       `strip instrs`, so it wants `length (strip instrs)` where the goal has
       `length instrs`.  Ghosts occupy no address, so these agree. *)
    - constructor;
        [rewrite <- (strip_length instrs); apply pcOutOfInstrs_fallthrough
        | constructor].
  Qed.


  (* Base-relative programs (possibly with data memory), straight-line exit, data
     block in CLASSED form.  HDataAddrs / Hlen / Hbound stay caller obligations --
     they depend on the actual data layout and base bound -- but HexitOffs and the
     ordering hazard are handled here.
     The unclassed twin (gen_contract_noninterferent_rel_simple, over
     gen_contract_rel) was deleted 2026-08-18 as dead -- stage 0 of
     PLAN-unify-generators.md.  Its conclusion was byte-identical to this
     lemma's, which is why migrating an example to gen_contract_rel_classed was a
     one-identifier change in its Result file and did not move the trusted
     statement surface. *)
  Lemma gen_contract_noninterferent_rel_classed_simple
      (reg_specs : list reg_spec_rel) (mem_specs : list mem_spec_rel)
      (instrs : list AnnotInstr) (bound : N) (fuel : nat) (init_addr : N)
      (HND : NoDup (map reg_spec_idx (map (concretize_reg init_addr) reg_specs)))
      (HDataAddrs : ∀ i spec,
          (map mem_full_to_spec (map (concretize_mem init_addr) mem_specs)) !! i = Some spec →
          spec.1 = bv.of_N (init_addr + 4 * N.of_nat (length instrs)
                             + 4 * N.of_nat i))
      (Hlen : (init_addr + 4 * N.of_nat (length instrs) +
               4 * N.of_nat (length mem_specs) < lenAddr)%N)
      (Hbound : (init_addr + bound < lenAddr)%N)
      (valid_contract : ValidCFGVerifierContract
          (gen_contract_rel_classed init_addr reg_specs mem_specs instrs []
             bound (pcOutOfInstrs_exitCond init_addr (strip instrs)) fuel)) :
    noninterferent_strong init_addr (strip instrs)
      (pcOutOfInstrs_exitCond init_addr (strip instrs))
      (map (concretize_reg init_addr) reg_specs)
      (map (concretize_mem init_addr) mem_specs).
  Proof.
    (* Re-pointed at the unified bridge (stage 3b).  `A ++ [] = A` is NOT
       definitional for a variable list, so the goal is first rewritten into the
       append form _u concludes over; the premises then need the same rewrite
       back.  byte_data is named because unification cannot solve
       `map f ?l == []` (see the note in gen_contract_noninterferent_param). *)
    rewrite <- (app_nil_r mem_specs).
    eapply (gen_contract_noninterferent_u
              (byte_data := []) (extra_exit_offs := [])
              (bound := bound) (fuel := fuel)).
    - exact HND.
    - rewrite app_nil_r. exact HDataAddrs.
    - rewrite app_nil_r. exact Hlen.
    - exact Hbound.
    (* `<- strip_length`: pcOutOfInstrs_fallthrough is instantiated at
       `strip instrs`, so it wants `length (strip instrs)` where the goal has
       `length instrs`.  Ghosts occupy no address, so these agree. *)
    - constructor;
        [rewrite <- (strip_length instrs); apply pcOutOfInstrs_fallthrough
        | constructor].
    - exact valid_contract.
  Qed.


  (* Common-case specialisation: no extra exits, standard fall-through exit
     -- mirrors gen_contract_noninterferent_rel_classed_simple. *)
  Lemma gen_contract_noninterferent_rel_bytes_simple
      (reg_specs : list reg_spec_rel) (byte_mem_specs : list mem_spec_rel)
      (instrs : list AnnotInstr) (bound : N) (fuel : nat) (init_addr : N)
      (HND : NoDup (map reg_spec_idx (map (concretize_reg init_addr) reg_specs)))
      (HDataAddrs : ∀ i spec,
          (map mem_full_to_spec (map (concretize_mem init_addr) byte_mem_specs)) !! i = Some spec →
          spec.1 = bv.of_N (init_addr + 4 * N.of_nat (length instrs)
                             + 4 * N.of_nat i))
      (Hlen : (init_addr + 4 * N.of_nat (length instrs) +
               4 * N.of_nat (length byte_mem_specs) < lenAddr)%N)
      (Hbound : (init_addr + bound < lenAddr)%N)
      (valid_contract : ValidCFGVerifierContract
          (gen_contract_rel_bytes init_addr reg_specs [] byte_mem_specs instrs []
             bound (pcOutOfInstrs_exitCond init_addr (strip instrs)) fuel)) :
    noninterferent_strong init_addr (strip instrs)
      (pcOutOfInstrs_exitCond init_addr (strip instrs))
      (map (concretize_reg init_addr) reg_specs)
      (map (concretize_mem init_addr) byte_mem_specs).
  Proof.
    (* Re-pointed at the unified bridge (stage 3b).  Here word_data := [] and
       `[] ++ B` DOES reduce to B, so no goal rewrite is needed -- only the naming
       of word_data, since unification cannot solve `map f ?l == []`. *)
    eapply (gen_contract_noninterferent_u
              (word_data := []) (extra_exit_offs := [])
              (bound := bound) (fuel := fuel)).
    - exact HND.
    - exact HDataAddrs.
    - exact Hlen.
    - exact Hbound.
    (* `<- strip_length`: pcOutOfInstrs_fallthrough is instantiated at
       `strip instrs`, so it wants `length (strip instrs)` where the goal has
       `length instrs`.  Ghosts occupy no address, so these agree. *)
    - constructor;
        [rewrite <- (strip_length instrs); apply pcOutOfInstrs_fallthrough
        | constructor].
    - exact valid_contract.
  Qed.

  (* --------------------------------------------------------------------- *)
  (* Concrete corollary of a `_rel` parametric theorem.                     *)
  (*                                                                        *)
  (* A `gen_contract_rel` example proves its noninterference ONCE for a     *)
  (* symbolic base (`<prog>_noninterferent_param`), concluding over         *)
  (* `map (concretize_reg base) specs_rel` / `map (concretize_mem base) …`. *)
  (* The concrete end theorem in Results.v is stated over literal spec      *)
  (* lists, so deriving it is a fixed ritual: prove the literal lists equal *)
  (* the concretized ones (a `vm_compute`-decidable equality), rewrite, and *)
  (* apply the parametric lemma, discharging its base bound.  This tactic   *)
  (* folds that ritual.  The concrete base is read from the goal, so the    *)
  (* SAME invocation serves both the init_addr = 0 corollary and a nonzero  *)
  (* one (e.g. cmovznz4_start = 256) -- only the base-definition to unfold  *)
  (* for the final `lia` differs, hence the `base_def` argument.            *)
  Tactic Notation "ni_rel_corollary"
      constr(param_lemma) constr(reg_specs_rel) constr(mem_specs_rel)
      reference(base_def) :=
    match goal with
    | |- noninterferent_strong ?base _ _ ?rs ?ms =>
        let Hr := fresh "Hr" in
        let Hm := fresh "Hm" in
        assert (Hr : rs = map (concretize_reg base) reg_specs_rel)
          by (vm_compute; reflexivity);
        assert (Hm : ms = map (concretize_mem base) mem_specs_rel)
          by (vm_compute; reflexivity);
        rewrite Hr Hm;
        apply param_lemma;
        unfold base_def, lenAddr; lia
    end.
