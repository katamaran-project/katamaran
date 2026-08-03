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
(* Example/BearSSLCheckScalarResult.v — end-to-end noninterference for the   *)
(* BearSSL P-256 `check_scalar` comparison step.                             *)
(*                                                                           *)
(* TRUSTED STATEMENT SURFACE — see BearSSLMuladdResult.v for the rationale   *)
(* behind the Example/<Prog>Result.v split.                                  *)
(* ========================================================================= *)

From Katamaran Require Import
     RiscvPmp.CFGVer.Example.Prelude
     RiscvPmp.CFGVer.EndToEnd
     RiscvPmp.CFGVer.Example.BearSSLCheckScalar.

(* Bound: 16 instructions * 4 bytes = 64. *)
Lemma check_scalar_noninterferent_param (init_addr : N) :
  (init_addr + 64 < lenAddr)%N ->
  noninterferent_strong init_addr check_scalar_instrs
    (pcOutOfInstrs_exitCond init_addr check_scalar_instrs)
    check_scalar_reg_specs [].
Proof.
  intros Hbound.
  eapply gen_contract_noninterferent_param_simple.
  - apply Prelude.nodup_fixed; reflexivity.
  - cbn; lia.
  - exact (valid_check_scalar_cfg_contract_param init_addr).
Qed.

Lemma check_scalar_noninterferent :
  noninterferent_strong init_addr check_scalar_instrs
    (pcOutOfInstrs_exitCond init_addr check_scalar_instrs)
    check_scalar_reg_specs [].
Proof.
  apply check_scalar_noninterferent_param.
  unfold init_addr, lenAddr; lia.
Qed.
