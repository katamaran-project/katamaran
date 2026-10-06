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
(* Example/Aes/InvMixColumnsResult.v — end-to-end noninterference for both   *)
(* AES InvMixColumns versions of Example/Aes/InvMixColumns.v.                *)
(*                                                                           *)
(* TRUSTED STATEMENT SURFACE.  Read against THIS branch's leakage model      *)
(* (LeakPc | LeakMemRead | LeakMemWrite -- a multiplication emits nothing),   *)
(* both theorems say the trace is independent of the secret column in A0.   *)
(* That both hold is expected: the code is branch-free and touches no data   *)
(* memory.  They are the baseline against which the multiplier-latency       *)
(* model is to separate them.                                                *)
(* ========================================================================= *)

From Katamaran Require Import
     RiscvPmp.CFGVer.Example.Prelude
     RiscvPmp.CFGVer.EndToEnd
     RiscvPmp.CFGVer.Example.Aes.InvMixColumns.

(* Linux master inv_mix_columns: 38 instructions = 152 bytes. *)
Lemma imc_linux_noninterferent_param (init_addr : N) :
  (init_addr + 152 < lenAddr)%N ->
  noninterferent_strong init_addr imc_linux_instrs (init_addr + 152)%N
    imc_linux_reg_specs [].
Proof.
  intros Hbound.
  eapply gen_contract_noninterferent_param_simple.
  - apply Prelude.nodup_fixed; reflexivity.
  - cbn; lia.
  - solve_valid valid_imc_linux_cfg_contract_param.
Qed.

(* inv_mix_columns with Algorithm 7 multiplies: 60 instructions = 240 bytes. *)
Lemma imc_alg7_noninterferent_param (init_addr : N) :
  (init_addr + 240 < lenAddr)%N ->
  noninterferent_strong init_addr imc_alg7_instrs (init_addr + 240)%N
    imc_alg7_reg_specs [].
Proof.
  intros Hbound.
  eapply gen_contract_noninterferent_param_simple.
  - apply Prelude.nodup_fixed; reflexivity.
  - cbn; lia.
  - solve_valid valid_imc_alg7_cfg_contract_param.
Qed.
