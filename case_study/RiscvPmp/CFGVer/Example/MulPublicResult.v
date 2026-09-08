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
(* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THE          *)
(* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.               *)
(******************************************************************************)

(* ========================================================================= *)
(* Example/MulPublicResult.v — end-to-end noninterference theorem for        *)
(* mul_public, the example that exercises the `LeakMul` leakage event.       *)
(*                                                                           *)
(* TRUSTED STATEMENT SURFACE: what this theorem asserts can be audited       *)
(* without reading the verifier or any proof.  The merge gate checks it with *)
(* Print Assumptions; Results.v re-exports it so the gate's single build     *)
(* target still pulls it in.                                                 *)
(*                                                                           *)
(* Read against the extended leakage model, the theorem says: for a program  *)
(* whose two multiplications take PUBLIC operands, the leakage trace — which *)
(* now records those operands via LeakMul — is independent of the secret in  *)
(* A2.  Same statement form as every other example; the STRENGTH of the      *)
(* claim changed because LeakEvent gained a constructor, not because this    *)
(* file says anything new.                                                   *)
(* ========================================================================= *)

From Katamaran Require Import
     RiscvPmp.CFGVer.Example.Prelude
     RiscvPmp.CFGVer.EndToEnd
     RiscvPmp.CFGVer.Example.MulPublic.

(* Universal base address, from the single symbolic-base VC
   valid_mul_public_cfg_contract_param.  4 instructions = 16 bytes. *)
Lemma mul_public_noninterferent_param (init_addr : N) :
  (init_addr + 16 < lenAddr)%N ->
  noninterferent_strong init_addr mul_public_instrs
    (pcOutOfInstrs_exitCond init_addr mul_public_instrs)
    mul_public_reg_specs [].
Proof.
  intros Hbound.
  (* Restate over `strip mul_public_instrs`, the form the EndToEnd bridges
     conclude; reflexivity-equal by strip_id_mul_public_instrs. *)
  rewrite <- strip_id_mul_public_instrs.
  eapply gen_contract_noninterferent_param_simple.
  - apply Prelude.nodup_fixed; reflexivity.
  - cbn; lia.
  - exact (valid_mul_public_cfg_contract_param init_addr).
Qed.

(* The concrete-base result as a corollary, at the model's own init_addr. *)
Lemma mul_public_noninterferent :
  noninterferent_strong init_addr mul_public_instrs
    (pcOutOfInstrs_exitCond init_addr mul_public_instrs)
    mul_public_reg_specs [].
Proof.
  apply mul_public_noninterferent_param.
  unfold init_addr, lenAddr; lia.
Qed.
