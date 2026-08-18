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
(* Example/JumpsResult.v — end-to-end noninterference theorem(s) for        *)
(* jump_if_zero (BEQ) and jmp_fwd (JAL).                       *)
(*                                                                           *)
(* TRUSTED STATEMENT SURFACE: what these theorems assert can be audited       *)
(* without reading the verifier or any proof.  The merge gate checks each of  *)
(* them with Print Assumptions; Results.v re-exports them so the gate's       *)
(* single build target still pulls in every result.                          *)
(*                                                                           *)
(* Each theorem instantiates a generic bridge from EndToEnd.v with the VC     *)
(* proved in Example/Jumps.v.  This file is deliberately SEPARATE from      *)
(* Example/Jumps.v: requiring EndToEnd (and so Adequacy) here keeps the     *)
(* example itself EndToEnd-free, so the 85 s Adequacy->EndToEnd chain goes on *)
(* building in parallel with the examples instead of ahead of all of them.    *)
(* ========================================================================= *)

From Katamaran Require Import
     RiscvPmp.CFGVer.Example.Prelude
     RiscvPmp.CFGVer.EndToEnd
     RiscvPmp.CFGVer.Example.Jumps.

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
  4: exact (valid_jump_if_zero_cfg_contract_param init_addr). (* must come first: doing the other bullets before this one lets their unification pick the wrong goal *)
  (* Position 4, not 5, and no vacuous-lookup bullet: stage 1 of
     PLAN-unify-generators.md dropped _param's mem_specs and with it the
     HDataAddrs premise. *)
  - apply Prelude.nodup_fixed; reflexivity.
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
  eapply gen_contract_noninterferent_param_simple.
  - apply Prelude.nodup_fixed; reflexivity.
  - cbn; lia.
  - exact (valid_jmp_fwd_cfg_contract_param init_addr).
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

