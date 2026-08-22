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
(* Example/BearSSLMuladdResult.v — end-to-end noninterference for the        *)
(* BearSSL `br_i31_muladd_small` quotient-estimate step.                     *)
(*                                                                           *)
(* TRUSTED STATEMENT SURFACE: what these theorems assert can be audited       *)
(* without reading the verifier or any proof.  The merge gate checks each of  *)
(* them with Print Assumptions; Results.v re-exports them so the gate's       *)
(* single build target still pulls in every result.                          *)
(*                                                                           *)
(* Kept SEPARATE from Example/BearSSLMuladd.v on purpose: requiring EndToEnd  *)
(* (and so Adequacy) here keeps the example itself EndToEnd-free, so the 85 s *)
(* Adequacy->EndToEnd chain builds in parallel with the examples rather than  *)
(* ahead of all of them.                                                     *)
(* ========================================================================= *)

From Katamaran Require Import
     RiscvPmp.CFGVer.Example.Prelude
     RiscvPmp.CFGVer.EndToEnd
     RiscvPmp.CFGVer.Example.BearSSLMuladd.

(* The 12-instruction branch-free RV32I body of BearSSL's quotient-estimate
   step is noninterferent for an ARBITRARY 4-aligned load address, with ALL
   THREE inputs (a0, b0, g) secret: the leakage trace is identical however the
   two worlds' inputs differ.

   Bound: 12 instructions * 4 bytes = 48. *)
Lemma muladd_q_noninterferent_param (init_addr : N) :
  (init_addr + 48 < lenAddr)%N ->
  noninterferent_strong init_addr muladd_q_instrs
    (pcOutOfInstrs_exitCond init_addr muladd_q_instrs)
    muladd_q_reg_specs [].
Proof.
  intros Hbound.
  (* Restate the goal over `strip muladd_q_instrs` -- the form the EndToEnd
     bridges now conclude.  reflexivity-equal (strip_id_muladd_q_instrs), so
     the theorem above is literally the same statement as before the
     AnnotInstr migration; this rewrite is where that is discharged. *)
  rewrite <- strip_id_muladd_q_instrs.
  eapply gen_contract_noninterferent_param_simple.
  - apply Prelude.nodup_fixed; reflexivity.
  - cbn; lia.
  - exact (valid_muladd_q_cfg_contract_param init_addr).
Qed.

(* Concrete-base corollary at the default init_addr. *)
Lemma muladd_q_noninterferent :
  noninterferent_strong init_addr muladd_q_instrs
    (pcOutOfInstrs_exitCond init_addr muladd_q_instrs)
    muladd_q_reg_specs [].
Proof.
  apply muladd_q_noninterferent_param.
  unfold init_addr, lenAddr; lia.
Qed.
