(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel, Dominique Devriese, Sander Huyghebaert  *)
(* All rights reserved.                                                       *)
(*                                                                            *)
(* Redistribution and use in source and binary forms, with or without         *)
(* modification, are permitted provided that the following conditions are     *)
(* met:                                                                       *)
(*                                                                            *)
(* 1. Redistributions of source code must retain the above copyright notice,  *)
(*    this list of conditions and this disclaimer.                            *)
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
(* Example/BearSSLCheckScalarLoop1Result.v — end-to-end noninterference for   *)
(* BearSSL P-256 `check_scalar` loop 1 (klen = 32, byte-granular memory).     *)
(*                                                                           *)
(* TRUSTED STATEMENT SURFACE — see BearSSLMuladdResult.v for the rationale   *)
(* behind the Example/<Prog>Result.v split.  Deliberately separate from      *)
(* Example/BearSSLCheckScalarLoop1.v so the Adequacy->EndToEnd chain builds  *)
(* in parallel with the examples rather than ahead of all of them.          *)
(* ========================================================================= *)

From Katamaran Require Import
     RiscvPmp.CFGVer.Example.Prelude
     RiscvPmp.CFGVer.EndToEnd
     RiscvPmp.CFGVer.Example.BearSSLCheckScalarLoop1.

(* The first byte-granular (lbu) example proved end-to-end in the repo,
   universal in the base address, from the single symbolic-base VC
   valid_loop1_cfg_contract_param via the byte-granular base-relative bridge
   gen_contract_noninterferent_rel_bytes_simple.  Bound 48 = last declared
   byte's offset (47) + 1, rounded up to the base bound the contract states. *)
Lemma check_scalar_loop1_noninterferent_param (init_addr : N) :
  (init_addr + 48 < lenAddr)%N ->
  noninterferent_strong init_addr loop1_instrs
    (pcOutOfInstrs_exitCond init_addr loop1_instrs)
    (map (concretize_reg init_addr) loop1_reg_specs_rel)
    (map (concretize_mem init_addr) loop1_byte_specs_rel).
Proof.
  intros Hb.
  (* Restate the goal over `strip loop1_instrs` -- the form the EndToEnd
     bridges now conclude.  reflexivity-equal (strip_id_loop1_instrs), so
     the theorem above is literally the same statement as before the
     AnnotInstr migration; this rewrite is where that is discharged. *)
  rewrite <- strip_id_loop1_instrs.
  eapply gen_contract_noninterferent_rel_bytes_simple.
  - apply Prelude.nodup_fixed; reflexivity.
  - intros [|[|[|[|[|[|[|[|i]]]]]]]] spec H; cbn in H;
      try (inversion H; subst; cbn; f_equal; lia); try discriminate.
  - cbn. lia.
  - exact Hb.
  - exact (valid_loop1_cfg_contract_param init_addr).
Qed.

(* Concrete corollary at the conventional init_addr = 0. *)
Lemma check_scalar_loop1_noninterferent :
  noninterferent_strong init_addr loop1_instrs
    (pcOutOfInstrs_exitCond init_addr loop1_instrs)
    (map (concretize_reg init_addr) loop1_reg_specs_rel)
    (map (concretize_mem init_addr) loop1_byte_specs_rel).
Proof.
  apply check_scalar_loop1_noninterferent_param.
  unfold init_addr, lenAddr; lia.
Qed.
