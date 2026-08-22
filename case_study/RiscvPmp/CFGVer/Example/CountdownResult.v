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
(* Example/CountdownResult.v — end-to-end noninterference theorem(s) for        *)
(* countdown (backward branch) and countdown_mem.              *)
(*                                                                           *)
(* TRUSTED STATEMENT SURFACE: what these theorems assert can be audited       *)
(* without reading the verifier or any proof.  The merge gate checks each of  *)
(* them with Print Assumptions; Results.v re-exports them so the gate's       *)
(* single build target still pulls in every result.                          *)
(*                                                                           *)
(* Each theorem instantiates a generic bridge from EndToEnd.v with the VC     *)
(* proved in Example/Countdown.v.  This file is deliberately SEPARATE from      *)
(* Example/Countdown.v: requiring EndToEnd (and so Adequacy) here keeps the     *)
(* example itself EndToEnd-free, so the 85 s Adequacy->EndToEnd chain goes on *)
(* building in parallel with the examples instead of ahead of all of them.    *)
(* ========================================================================= *)

From Katamaran Require Import
     RiscvPmp.CFGVer.Example.Prelude
     RiscvPmp.CFGVer.EndToEnd
     RiscvPmp.CFGVer.Example.Countdown.

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
  (* This theorem's program is an INLINE literal (countdown_mem_instrs belongs
     to countdown_mem_noninterferent_param below -- CountdownResult.v is the one
     MIXED file, and a script that assumed one program per Result file put the
     wrong rewrite here).  Same job done locally: restate over `strip <literal>`,
     the form the EndToEnd bridges now conclude, reflexivity-equal so the
     theorem above is unchanged. *)
  assert (Hstrip : strip [ADDI X1 X1 neg_one_12; BNE X1 X0 back_offset]
                 = [ADDI X1 X1 neg_one_12; BNE X1 X0 back_offset]) by reflexivity.
  rewrite <- Hstrip.
  eapply gen_contract_noninterferent_param_simple.
  - apply Prelude.nodup_fixed; reflexivity.
  - cbn; lia.
  - exact (valid_countdown_cfg_contract_param init_addr).
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
  (* Restate over `strip countdown_mem_instrs`, the form the bridges conclude;
     reflexivity-equal by strip_id_countdown_mem_instrs. *)
  rewrite <- strip_id_countdown_mem_instrs.
  eapply gen_contract_noninterferent_rel_classed_simple.
  - apply Prelude.nodup_fixed; reflexivity.
  - intros [|i] spec H; cbn in H;
      try (inversion H; subst; cbn; f_equal; lia); discriminate.
  - cbn. lia.
  - exact Hb.
  - exact (valid_countdown_mem_cfg_contract_param init_addr).
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
  ni_rel_corollary countdown_mem_noninterferent_param
    countdown_mem_reg_specs_rel countdown_mem_mem_specs_rel init_addr.
Qed.

