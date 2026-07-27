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
(* Example/KeyScheduleLoopResult.v — end-to-end noninterference theorem(s) for        *)
(* key_schedule_loop2 (small-N=2 GHASH loop spike).            *)
(*                                                                           *)
(* TRUSTED STATEMENT SURFACE: what these theorems assert can be audited       *)
(* without reading the verifier or any proof.  The merge gate checks each of  *)
(* them with Print Assumptions; Results.v re-exports them so the gate's       *)
(* single build target still pulls in every result.                          *)
(*                                                                           *)
(* Each theorem instantiates a generic bridge from EndToEnd.v with the VC     *)
(* proved in Example/KeyScheduleLoop.v.  This file is deliberately SEPARATE from      *)
(* Example/KeyScheduleLoop.v: requiring EndToEnd (and so Adequacy) here keeps the     *)
(* example itself EndToEnd-free, so the 85 s Adequacy->EndToEnd chain goes on *)
(* building in parallel with the examples instead of ahead of all of them.    *)
(* ========================================================================= *)

From Katamaran Require Import
     RiscvPmp.CFGVer.Example.Prelude
     RiscvPmp.CFGVer.EndToEnd
     RiscvPmp.CFGVer.Example.KeyScheduleLoop.

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
  eapply gen_contract_noninterferent_rel_simple.
  - apply Prelude.nodup_fixed; reflexivity.
  - intros [|[|i]] spec H; cbn in H;
      try (inversion H; subst; cbn; f_equal; lia); try discriminate.
  - cbn. lia.
  - exact Hb.
  - exact (valid_key_schedule_loop2_cfg_contract_param init_addr).
Qed.

(* The concrete result is now a corollary of the universal-base theorem
   above. *)
Lemma key_schedule_loop2_noninterferent :
  noninterferent_strong init_addr key_schedule_loop2_instrs key_schedule_loop2_exitCond
    key_schedule_loop2_reg_specs key_schedule_loop2_mem_specs.
Proof.
  ni_rel_corollary key_schedule_loop2_noninterferent_param
    key_schedule_loop2_reg_specs_rel key_schedule_loop2_mem_specs_rel init_addr.
Qed.

