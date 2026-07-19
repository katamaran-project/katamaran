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
     RiscvPmp.CFGVer.Example.Cmovznz4
     RiscvPmp.CFGVer.Example.Precompute
     RiscvPmp.CFGVer.Example.KeyScheduleLoop.
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


  (* Phase 4.2: swap verified end-to-end for a UNIVERSAL base address, from
     the single symbolic-base VC valid_swap_cfg_contract_param. *)
  Lemma swap_noninterferent_param (init_addr : N) :
    (init_addr + 12 < lenAddr)%N ->
    noninterferent_strong init_addr [MV X3 X2; MV X2 X1; MV X1 X3]
      (pcOutOfInstrs_exitCond init_addr [MV X3 X2; MV X2 X1; MV X1 X3])
      [(X1, false, None); (X2, false, None); (X3, false, None)] [].
  Proof.
    intros Hbound.
    eapply gen_contract_noninterferent_param.
    5: exact (valid_swap_cfg_contract_param init_addr). (* must come first: doing the other bullets before this one lets their unification pick the wrong goal *)
    - apply Prelude.nodup_fixed; reflexivity.
    - intros ? ? Hlk; rewrite lookup_nil in Hlk; discriminate.
    - cbn. lia.
    - constructor; [apply pcOutOfInstrs_fallthrough | constructor].
  Qed.

  Lemma swap_noninterferent :
    noninterferent_strong init_addr [MV X3 X2; MV X2 X1; MV X1 X3]
      (pcOutOfInstrs_exitCond init_addr [MV X3 X2; MV X2 X1; MV X1 X3])
      [(X1, false, None); (X2, false, None); (X3, false, None)] [].
  Proof.
    apply swap_noninterferent_param.
    unfold init_addr, lenAddr; lia.
  Qed.

  (* Phase 4.2: jump_if_zero verified end-to-end for a UNIVERSAL base
     address, from the single symbolic-base VC
     valid_jump_if_zero_cfg_contract_param. *)
  Lemma jumpIfZero_noninterferent_param (init_addr : N) :
    (init_addr + 4 < lenAddr)%N ->
    noninterferent_strong init_addr [BEQ X1 X0 true_offset]
      (pcOutOfInstrs_exitCond init_addr [BEQ X1 X0 true_offset]) [(X1, true, None)] [].
  Proof.
    intros Hbound.
    eapply gen_contract_noninterferent_param.
    5: exact (valid_jump_if_zero_cfg_contract_param init_addr). (* must come first: doing the other bullets before this one lets their unification pick the wrong goal *)
    - apply Prelude.nodup_fixed; reflexivity.
    - intros ? ? Hlk; rewrite lookup_nil in Hlk; discriminate.
    - cbn. lia.
    - (* extra_exit_offs = [8%N] here (unlike every other example, whose
         extra_exit_offs = []), so HexitOffs is a 2-element Forall: the
         fall-through offset (4) plus the branch target (8). *)
      constructor.
      + apply pcOutOfInstrs_fallthrough.
      + constructor; [ | constructor ].
        unfold pcOutOfInstrs_exitCond, bv.ugeb, bv.uleb.
        apply N.leb_le.
        rewrite bv.of_N_add.
        assert (Hlen1 : N.of_nat (length [BEQ X1 X0 true_offset]) = 1%N) by reflexivity.
        rewrite Hlen1.
        unfold lenAddr in Hbound.
        assert (Hs4 : (init_addr + 4 * 1 < bv.exp2 xlenbits)%N)
          by (apply N.le_lt_trans with (m := 1024%N); [lia | vm_compute; reflexivity]).
        assert (Hs8 : (init_addr + 8 < bv.exp2 xlenbits)%N)
          by (apply N.le_lt_trans with (m := 1028%N); [lia | vm_compute; reflexivity]).
        rewrite (bv.bin_of_N_small Hs4) (bv.bin_of_N_small Hs8).
        lia.
  Qed.

  Lemma jumpIfZero_noninterferent :
    noninterferent_strong init_addr [BEQ X1 X0 true_offset]
      (pcOutOfInstrs_exitCond init_addr [BEQ X1 X0 true_offset]) [(X1, true, None)] [].
  Proof.
    apply jumpIfZero_noninterferent_param.
    unfold init_addr, lenAddr; lia.
  Qed.

  (* Phase 4.2: jmp_fwd verified end-to-end for a UNIVERSAL base address,
     from the single symbolic-base VC valid_jmp_fwd_cfg_contract_param --
     confirms the JAL forward-jump case. *)
  Lemma jmp_fwd_noninterferent_param (init_addr : N) :
    (init_addr + 8 < lenAddr)%N ->
    noninterferent_strong init_addr [JAL X0 jmp_offset; NOP]
      (pcOutOfInstrs_exitCond init_addr [JAL X0 jmp_offset; NOP]) [] [].
  Proof.
    intros Hbound.
    eapply gen_contract_noninterferent_param.
    5: exact (valid_jmp_fwd_cfg_contract_param init_addr). (* must come first: doing the other bullets before this one lets their unification pick the wrong goal *)
    - apply Prelude.nodup_fixed; reflexivity.
    - intros ? ? Hlk; rewrite lookup_nil in Hlk; discriminate.
    - cbn. lia.
    - constructor; [apply pcOutOfInstrs_fallthrough | constructor].
  Qed.

  (* jmp_fwd_exitCond is definitionally pcOutOfInstrs_exitCond 0 [JAL...; NOP]
     (both reduce to fun v => bv.ugeb v (bv.of_N 8)), so this is a corollary
     with no rewrite needed, same as countdown_noninterferent. *)
  Lemma jmp_fwd_noninterferent_cfg :
    noninterferent_strong init_addr [JAL X0 jmp_offset; NOP] jmp_fwd_exitCond [] [].
  Proof.
    apply jmp_fwd_noninterferent_param.
    unfold init_addr, lenAddr; lia.
  Qed.

  (* Phase 4.2: countdown verified end-to-end for a UNIVERSAL base address,
     from the single symbolic-base VC valid_countdown_cfg_contract_param --
     confirms the BACKWARD branch (BNE back_offset) case works with the exact
     same offset-agnostic tail as the forward-only programs (cmovznz4/set_X2). *)
  Lemma countdown_noninterferent_param (init_addr : N) :
    (init_addr + 8 < lenAddr)%N ->
    noninterferent_strong init_addr [ADDI X1 X1 neg_one_12; BNE X1 X0 back_offset]
      (pcOutOfInstrs_exitCond init_addr [ADDI X1 X1 neg_one_12; BNE X1 X0 back_offset])
      [(X1, true, Some (bv.of_N 2))] [].
  Proof.
    intros Hbound.
    eapply gen_contract_noninterferent_param.
    5: exact (valid_countdown_cfg_contract_param init_addr). (* must come first: doing the other bullets before this one lets their unification pick the wrong goal *)
    - apply Prelude.nodup_fixed; reflexivity.
    - intros ? ? Hlk; rewrite lookup_nil in Hlk; discriminate.
    - cbn. lia.
    - constructor; [apply pcOutOfInstrs_fallthrough | constructor].
  Qed.

  (* The concrete result is now a corollary of the universal-base theorem
     above: countdown_exitCond is definitionally pcOutOfInstrs_exitCond at
     init_addr = 0, so no vm_compute/rewrite is needed here at all. *)
  Lemma countdown_noninterferent :
    noninterferent_strong init_addr [ADDI X1 X1 neg_one_12; BNE X1 X0 back_offset]
      countdown_exitCond [(X1, true, Some (bv.of_N 2))] [].
  Proof.
    apply countdown_noninterferent_param.
    unfold init_addr, lenAddr; lia.
  Qed.

  (* Phase 4.2: countdown_mem verified end-to-end for a UNIVERSAL base
     address, from the single symbolic-base VC
     valid_countdown_mem_cfg_contract_param -- confirms a BACKWARD branch
     combined with base-RELATIVE memory (via the X0->X2 register rewrite,
     see the comment in Countdown.v) works with the same reusable bridge and
     offset-agnostic tail as every other example. *)
  Lemma countdown_mem_noninterferent_param (init_addr : N) :
    (init_addr + 20 < lenAddr)%N ->
    noninterferent_strong init_addr countdown_mem_instrs
      (pcOutOfInstrs_exitCond init_addr countdown_mem_instrs)
      (map (concretize_reg init_addr) countdown_mem_reg_specs_rel)
      (map (concretize_mem init_addr) countdown_mem_mem_specs_rel).
  Proof.
    intros Hb.
    eapply gen_contract_noninterferent_rel.
    6: exact (valid_countdown_mem_cfg_contract_param init_addr). (* must come first: doing the other bullets before this one lets their unification pick the wrong goal *)
    - apply Prelude.nodup_fixed; reflexivity.
    - intros [|i] spec H; cbn in H;
        try (inversion H; subst; cbn; f_equal; lia); discriminate.
    - cbn. lia.
    - exact Hb.
    - constructor; [apply pcOutOfInstrs_fallthrough | constructor].
  Qed.

  (* The concrete result is now a corollary of the universal-base theorem
     above. The reg_specs literal gains an X2 entry compared to before the
     X0->X2 rewrite (X2 = base = 0 here, so this is the same program
     behaviorally, just with the base held in an explicit register instead
     of the hardwired-zero one). *)
  Lemma countdown_mem_noninterferent :
    noninterferent_strong init_addr countdown_mem_instrs countdown_mem_exitCond
      [(X1, false, None); (X2, false, Some (bv.of_N init_addr))]
      [(bv.of_N 16, true, Some (bv.of_N 2))].
  Proof.
    assert (Hr : [(X1, false, None); (X2, false, Some (bv.of_N init_addr))]
                 = map (concretize_reg init_addr) countdown_mem_reg_specs_rel)
      by (vm_compute; reflexivity).
    assert (Hm : [(bv.of_N 16, true, Some (bv.of_N 2))]
                 = map (concretize_mem init_addr) countdown_mem_mem_specs_rel)
      by (vm_compute; reflexivity).
    rewrite Hr Hm.
    apply countdown_mem_noninterferent_param.
    unfold init_addr, lenAddr; lia.
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
    5: exact (valid_set_X2_to_42_param init_addr). (* must come first: doing the other bullets before this one lets their unification pick the wrong goal *)
    - apply Prelude.nodup_fixed; reflexivity.
    - intros ? ? Hlk; rewrite lookup_nil in Hlk; discriminate.
    - cbn. lia.
    - constructor; [apply pcOutOfInstrs_fallthrough | constructor].
  Qed.

  (* The concrete result at init_addr = 0, as a corollary -- this was
     missing before (set_X2 had only the parametric headline). *)
  Lemma set_X2_to_42_noninterferent :
    noninterferent_strong init_addr [ADDI X2 X0 (bv.of_N 42)]
      (pcOutOfInstrs_exitCond init_addr [ADDI X2 X0 (bv.of_N 42)])
      [(X2, false, None)] [].
  Proof.
    apply set_X2_to_42_noninterferent_param.
    unfold init_addr, lenAddr; lia.
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
    6: exact (valid_cmovznz4_cfg_contract_param init_addr). (* must come first: doing the other bullets before this one lets their unification pick the wrong goal *)
    - apply Prelude.nodup_fixed; reflexivity.
    - intros [|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]] spec H; cbn in H;
        try (inversion H; subst; cbn; f_equal; lia); try discriminate.
    - cbn. lia.
    - exact Hb.
    - constructor; [apply pcOutOfInstrs_fallthrough | constructor].
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

  (* Phase 4.2 headline #3: precompute (Botan's GHASH::key_schedule masking
     step, 32-bit-word analogue, 10 instrs, no memory) verified end-to-end
     for a UNIVERSAL base address, from the single symbolic-base VC
     valid_precompute_cfg_contract_param -- no per-address vm_compute. *)
  Lemma precompute_noninterferent_param (init_addr : N) :
    (init_addr + 40 < lenAddr)%N ->
    noninterferent_strong init_addr precompute_instrs
      (pcOutOfInstrs_exitCond init_addr precompute_instrs)
      precompute_reg_specs [].
  Proof.
    intros Hbound.
    eapply gen_contract_noninterferent_param.
    5: exact (valid_precompute_cfg_contract_param init_addr). (* must come first: doing the other bullets before this one lets their unification pick the wrong goal *)
    - apply Prelude.nodup_fixed; reflexivity.
    - intros ? ? Hlk; rewrite lookup_nil in Hlk; discriminate.
    - cbn. lia.
    - constructor; [apply pcOutOfInstrs_fallthrough | constructor].
  Qed.

  (* The concrete result at init_addr = 0, as a corollary. *)
  Lemma precompute_noninterferent :
    noninterferent_strong init_addr precompute_instrs
      (pcOutOfInstrs_exitCond init_addr precompute_instrs) precompute_reg_specs [].
  Proof.
    apply precompute_noninterferent_param.
    unfold init_addr, lenAddr; lia.
  Qed.

  (* Phase 4.2 headline #4: key_schedule_loop2 (small-N=2 feasibility spike
     toward the full Botan GHASH::key_schedule loop -- see the header comment
     in Example/KeyScheduleLoop.v) verified end-to-end for a UNIVERSAL base
     address, from the single symbolic-base VC
     valid_key_schedule_loop2_cfg_contract_param -- confirms a backward
     branch whose body both re-runs secret arithmetic AND stores to an
     advancing (base-relative) table address works with the same reusable
     bridge and offset-agnostic tail as every other example. *)
  Lemma key_schedule_loop2_noninterferent_param (init_addr : N) :
    (init_addr + 64 < lenAddr)%N ->
    noninterferent_strong init_addr key_schedule_loop2_instrs
      (pcOutOfInstrs_exitCond init_addr key_schedule_loop2_instrs)
      (map (concretize_reg init_addr) key_schedule_loop2_reg_specs_rel)
      (map (concretize_mem init_addr) key_schedule_loop2_mem_specs_rel).
  Proof.
    intros Hb.
    eapply gen_contract_noninterferent_rel.
    6: exact (valid_key_schedule_loop2_cfg_contract_param init_addr). (* must come first: doing the other bullets before this one lets their unification pick the wrong goal *)
    - apply Prelude.nodup_fixed; reflexivity.
    - intros [|[|i]] spec H; cbn in H;
        try (inversion H; subst; cbn; f_equal; lia); try discriminate.
    - cbn. lia.
    - exact Hb.
    - constructor; [apply pcOutOfInstrs_fallthrough | constructor].
  Qed.

  (* The concrete result is now a corollary of the universal-base theorem
     above. *)
  Lemma key_schedule_loop2_noninterferent :
    noninterferent_strong init_addr key_schedule_loop2_instrs key_schedule_loop2_exitCond
      key_schedule_loop2_reg_specs key_schedule_loop2_mem_specs.
  Proof.
    assert (Hr : key_schedule_loop2_reg_specs = map (concretize_reg init_addr) key_schedule_loop2_reg_specs_rel)
      by (vm_compute; reflexivity).
    assert (Hm : key_schedule_loop2_mem_specs = map (concretize_mem init_addr) key_schedule_loop2_mem_specs_rel)
      by (vm_compute; reflexivity).
    rewrite Hr Hm.
    apply key_schedule_loop2_noninterferent_param.
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

