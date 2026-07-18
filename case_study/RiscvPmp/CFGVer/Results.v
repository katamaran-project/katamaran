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
(* Results.v — the concrete end-to-end noninterference theorems.             *)
(*                                                                           *)
(* One theorem per verified example program, each an instantiation of the    *)
(* generic bridges in EndToEnd.v with the example's valid_* VC proof.        *)
(* These statements (together with Noninterference.v and the per-example     *)
(* instruction/spec definitions) are the trusted surface of CFGVer: what     *)
(* they assert can be audited without reading the verifier or the proofs.    *)
(* The merge gate checks each of them with Print Assumptions.                *)
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
     RiscvPmp.CFGVer.Verifier.
From Katamaran Require Export
     RiscvPmp.CFGVer.Noninterference
     RiscvPmp.CFGVer.Tables
     RiscvPmp.CFGVer.Contracts
     RiscvPmp.CFGVer.GenContract
     RiscvPmp.CFGVer.Adequacy
     RiscvPmp.CFGVer.EndToEnd
     RiscvPmp.CFGVer.Example.MvSwap
     RiscvPmp.CFGVer.Example.Jumps
     RiscvPmp.CFGVer.Example.Countdown
     RiscvPmp.CFGVer.Example.SetX2
     RiscvPmp.CFGVer.Example.Cmovznz4.
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


  Lemma swap_noninterferent :
    noninterferent_strong init_addr [MV X3 X2; MV X2 X1; MV X1 X3]
      (pcOutOfInstrs_exitCond init_addr [MV X3 X2; MV X2 X1; MV X1 X3])
      [(X1, false, None); (X2, false, None); (X3, false, None)] [].
  Proof.
    eapply gen_contract_noninterferent;
      [apply Prelude.nodup_fixed; reflexivity |
       intros ? ? H; rewrite lookup_nil in H; discriminate |
       by cbn; unfold lenAddr | repeat constructor | exact valid_swap_cfg_contract].
  Qed.

  Lemma jumpIfZero_noninterferent :
    noninterferent_strong init_addr [BEQ X1 X0 true_offset]
      (pcOutOfInstrs_exitCond init_addr [BEQ X1 X0 true_offset]) [(X1, true, None)] [].
  Proof.
    eapply gen_contract_noninterferent.
    5: exact valid_jump_if_zero_cfg_contract.
    - apply Prelude.nodup_fixed; reflexivity.
    - intros ? ? H; rewrite lookup_nil in H; discriminate.
    - by cbn; unfold lenAddr.
    - repeat constructor.
  Qed.

  Lemma jmp_fwd_safe_cfg `{sailGS2 Σ} γ1 γ2 :
    RiscvPmpProgram.read_register γ1 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ2 cur_privilege = Machine ->
    RiscvPmpProgram.read_register γ1 pc = bv.of_N init_addr ->
    RiscvPmpProgram.read_register γ2 pc = bv.of_N init_addr ->
    ⊢ cfg_instrs_contract jmp_fwd_exitCond [JAL X0 jmp_offset; NOP] γ1 γ2.
  Proof.
    intros γ1curpriv γ2curpriv γ1pc γ2pc.
    unfold cfg_instrs_contract, cfg_instrs_pre, exitCond_WP2_loop.
    iIntros "(Hregs & Hinstrs & #Hinv)".
    cbn.
    iDestruct "Hregs" as
      "(Hpc & Hnpc & Hstatus & Htvec & Hcause & Hepc & Hpriv & Hregs)".
    rewrite γ1curpriv γ1pc γ2curpriv γ2pc.
    rewrite !regPstsTo_sync_is_nonsync.
    assert (Hif : Katamaran.RiscvPmp.CFGVer.Verifier.itable_rel (w := wlctx [ctx])
                    (instrs_of_list (bv.of_N init_addr) [JAL X0 jmp_offset; NOP])
                    (table_of_list (term_val ty_xlenbits (bv.of_N init_addr)) 0
                       [JAL X0 jmp_offset; NOP]) [env]).
    { apply itable_faith_of_list; [reflexivity|].
      apply table_bound_of_lenAddr. now vm_compute. }
    assert (Hef : Katamaran.RiscvPmp.CFGVer.Verifier.etable_rel (w := wlctx [ctx])
                    jmp_fwd_exitCond
                    (exits_of_offs (term_val ty_xlenbits (bv.of_N init_addr))
                       ((4 * N.of_nat (length [JAL X0 jmp_offset; NOP]))%N :: []))
                    [env]).
    { apply etable_faith_exits_of_offs with (cbase := bv.of_N init_addr);
        [reflexivity | repeat constructor]. }
    iApply (sound_scfg_verification_condition_myWP2
              valid_jmp_fwd_cfg_contract _ Hif Hef
              $! (SyncVal (bv.of_N init_addr))
              with "[Hpc Hnpc Hstatus Htvec Hcause Hepc Hpriv Hregs Hinstrs]").
    - iSplitL "Hpriv".
      + cbn. iSplit. { iPureIntro. split; tauto. }
        by iFrame "∗ #".
      + iFrame "Hpc". iSplitL "Hnpc". { iExists _. iExact "Hnpc". }
        iExact "Hinstrs".
    - iIntros (an) "(%Hexit & Hpc & Hnpc & Hinstrs)".
      destruct an as [v | vl vr].
      + cbn in Hexit. iExists v. iFrame "Hpc". iPureIntro. rewrite Hexit. exact I.
      + contradiction.
  Qed.

  Lemma jmp_fwd_noninterferent_cfg :
    noninterferent_strong init_addr [JAL X0 jmp_offset; NOP] jmp_fwd_exitCond [] [].
  Proof.
    eapply gen_contract_noninterferent.
    5: exact valid_jmp_fwd_cfg_contract. (* To fix wrong unification in step 4 that would make step 5 impossble, we do step 5 first, TODO: we probably need to handle this problem on a higher level. *) 
    - apply Prelude.nodup_fixed; reflexivity.
    - intros ? ? H; rewrite lookup_nil in H; discriminate.
    - by cbn; unfold lenAddr.
    - repeat constructor. (* vm_compute was not necessary here. *)
  Qed.

  Lemma countdown_noninterferent :
    noninterferent_strong init_addr [ADDI X1 X1 neg_one_12; BNE X1 X0 back_offset]
      countdown_exitCond [(X1, true, Some (bv.of_N 2))] [].
  Proof.
    eapply gen_contract_noninterferent.
    5: exact valid_countdown_cfg_contract. (* To fix wrong unification in step 4 that would make step 5 impossble, we do step 5 first, TODO: we probably need to handle this problem on a higher level. *) 
    - apply Prelude.nodup_fixed; reflexivity.
    - intros ? ? H. rewrite lookup_nil in H; discriminate.
    - by cbn; unfold lenAddr.
    - repeat constructor. (* vm_compute was not necessary here. *)
  Qed.

  Lemma countdown_mem_noninterferent :
    noninterferent_strong init_addr countdown_mem_instrs countdown_mem_exitCond
      [(X1, false, None)] [(bv.of_N 16, true, Some (bv.of_N 2))].
  Proof.
    eapply gen_contract_noninterferent.
    5: exact valid_countdown_mem_cfg_contract. (* To fix wrong unification in step 4 that would make step 5 impossble, we do step 5 first, TODO: we probably need to handle this problem on a higher level. *) 
    - apply Prelude.nodup_fixed; reflexivity.
    - intros [|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]] spec H; cbn in H; (* I probably don't need this big of a case-split but it works. TODO: Hide this in a tactic or figure out how to prove it generally. *)
      try (inversion H; subst; vm_compute; done); discriminate.
    - by cbn; unfold lenAddr.
    - repeat constructor. (* vm_compute was not necessary here. *)
  Qed.

  (* Phase 4.2 headline: set_X2_to_42 verified end-to-end for a UNIVERSAL base
     address, from the single symbolic-base VC valid_set_X2_to_42_param — no
     per-address vm_compute.  The (init_addr + 4 < lenAddr) premise is the base
     bound the fetch obligations need; it is the `(bound)` the plan anticipated. *)
  Lemma set_X2_to_42_noninterferent_param (init_addr : N) :
    (init_addr + 4 < lenAddr)%N ->
    noninterferent_strong init_addr [ADDI X2 X0 (bv.of_N 42)]
      (pcOutOfInstrs_exitCond init_addr [ADDI X2 X0 (bv.of_N 42)])
      [(X2, false, None)] [].
  Proof.
    intros Hbound.
    eapply gen_contract_noninterferent_param.
    - apply Prelude.nodup_fixed; reflexivity.
    - intros ? ? Hlk; rewrite lookup_nil in Hlk; discriminate.
    - cbn. lia.
    - constructor; [apply pcOutOfInstrs_fallthrough | constructor].
    - exact (valid_set_X2_to_42_param init_addr).
  Qed.

  (* Phase 4.2 headline #2: cmovznz4 (29 instrs, 12 data words, base-relative
     data pointers) verified end-to-end for a UNIVERSAL base address, from the
     single symbolic-base VC valid_cmovznz4_cfg_contract_param via the reusable
     base-relative bridge gen_contract_noninterferent_rel.  The concrete reg /
     mem specs are the base-relative specs concretized at init_addr. *)
  Lemma cmovznz4_noninterferent_param (init_addr : N) :
    (init_addr + 164 < lenAddr)%N ->
    noninterferent_strong init_addr cmovznz4_instrs
      (pcOutOfInstrs_exitCond init_addr cmovznz4_instrs)
      (map (concretize_reg init_addr) cmovznz4_reg_specs_rel)
      (map (concretize_mem init_addr) cmovznz4_mem_specs_rel).
  Proof.
    intros Hb.
    eapply gen_contract_noninterferent_rel.
    - apply Prelude.nodup_fixed; reflexivity.
    - intros [|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]] spec H; cbn in H;
        try (inversion H; subst; cbn; f_equal; lia); try discriminate.
    - cbn. lia.
    - exact Hb.
    - constructor; [apply pcOutOfInstrs_fallthrough | constructor].
    - exact (valid_cmovznz4_cfg_contract_param init_addr).
  Qed.

  (* The two concrete cmovznz4 results are now corollaries of the universal-base
     theorem above: the single source of truth is valid_cmovznz4_cfg_contract_param.
     The concrete reg/mem specs are exactly the base-relative specs concretized at
     the respective base (init_addr = 0, and cmovznz4_start = 256), so the
     conclusions coincide definitionally (checked by vm_compute). *)
  Lemma cmovznz4_noninterferent :
    noninterferent_strong init_addr cmovznz4_instrs (pcOutOfInstrs_exitCond init_addr cmovznz4_instrs)
      cmovznz4_reg_specs cmovznz4_mem_specs.
  Proof.
    assert (Hr : cmovznz4_reg_specs = map (concretize_reg init_addr) cmovznz4_reg_specs_rel)
      by (vm_compute; reflexivity).
    assert (Hm : cmovznz4_mem_specs = map (concretize_mem init_addr) cmovznz4_mem_specs_rel)
      by (vm_compute; reflexivity).
    rewrite Hr Hm.
    apply cmovznz4_noninterferent_param.
    unfold init_addr, lenAddr; lia.
  Qed.

  (* Fully end-to-end at the genuinely nonzero start address cmovznz4_start = 256,
     as a corollary of the universal-base version. *)
  Lemma cmovznz4_noninterferent_at_start :
    noninterferent_strong cmovznz4_start cmovznz4_instrs
      (pcOutOfInstrs_exitCond cmovznz4_start cmovznz4_instrs)
      cmovznz4_reg_specs_at_start cmovznz4_mem_specs_at_start.
  Proof.
    assert (Hr : cmovznz4_reg_specs_at_start = map (concretize_reg cmovznz4_start) cmovznz4_reg_specs_rel)
      by (vm_compute; reflexivity).
    assert (Hm : cmovznz4_mem_specs_at_start = map (concretize_mem cmovznz4_start) cmovznz4_mem_specs_rel)
      by (vm_compute; reflexivity).
    rewrite Hr Hm.
    apply cmovznz4_noninterferent_param.
    unfold cmovznz4_start, lenAddr; lia.
  Qed.

