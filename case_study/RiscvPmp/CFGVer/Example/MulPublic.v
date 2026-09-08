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
(* Example/MulPublic.v — the MUL-leaks-its-operands leakage model.           *)
(*                                                                           *)
(* This example exists to exercise the FOURTH leakage event, `LeakMul`       *)
(* (Base.v), which a variable-latency multiplier justifies: a multiplication *)
(* leaks BOTH of its operands.  Under that model a multiplication is         *)
(* admissible exactly when both operands are public, which is what this      *)
(* program does and what the theorem in MulPublicResult.v certifies.         *)
(*                                                                           *)
(* The shape is the ordinary constant-time table-index idiom: a PUBLIC index *)
(* times a PUBLIC element size gives a public byte offset, which is then     *)
(* combined with SECRET data.  The multiplications are on public operands,   *)
(* so their leakage is harmless; the secret only ever reaches ADD, which     *)
(* emits no event.                                                           *)
(*                                                                           *)
(*     A0  index        PUBLIC                                               *)
(*     A1  element size PUBLIC                                               *)
(*     A2  secret word  SECRET                                               *)
(*                                                                           *)
(*     MUL   T0, A0, A1     ; T0 <- lo(A0 * A1)   leaks A0, A1  (both public)*)
(*     MULHU T1, A0, A1     ; T1 <- hi(A0 * A1)   leaks A0, A1  (both public)*)
(*     ADD   T2, A2, T0     ; T2 <- A2 + T0       secret, leaks nothing      *)
(*     ADD   A3, T2, T1     ; A3 <- T2 + T1       secret, leaks nothing      *)
(*                                                                           *)
(* Both MUL and MULHU are included deliberately: the whole MUL/MULH/MULHU/   *)
(* MULHSU family routes through the single `fun_execute_MUL` body that       *)
(* carries the emit site, so covering two of them covers the wiring for all  *)
(* four.                                                                     *)
(*                                                                           *)
(* The NEGATIVE half of this case study — the same program with a SECRET     *)
(* multiplication operand, which must and does FAIL to verify — is not a     *)
(* theorem (it has none) and so lives in the probes ZZMulLeak.v /            *)
(* ZZMulLeakSecret.v with the measurements written up in                     *)
(* diagnostics/mul-leakage-model.md.                                         *)
(*                                                                           *)
(* The instruction list and reg spec definitions below are                   *)
(* STATEMENT-RELEVANT: the noninterference theorem in MulPublicResult.v      *)
(* references them by name.  The contract and valid_* VC proof are not.      *)
(* ========================================================================= *)

From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.

Definition mul_public_instrs : list AST :=
  [ MUL   T0 A0 A1
  ; MULHU T1 A0 A1
  ; ADD   T2 A2 T0
  ; ADD   A3 T2 T1 ].

(* A0 and A1 are the multiplication operands and are the ONLY registers that
   have to be public — that requirement is exactly what LeakMul adds.  A2 is
   secret, and stays secret through T2 and A3. *)
Definition mul_public_reg_specs : list reg_spec :=
  [ (A0, true,  None)     (* index        PUBLIC — a MUL operand *)
  ; (A1, true,  None)     (* element size PUBLIC — a MUL operand *)
  ; (A2, false, None)     (* secret word                          *)
  ; (T0, false, None); (T1, false, None); (T2, false, None)
  ; (A3, false, None) ].

Definition mul_public_cfg_contract_param (ia : N) : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_param ia mul_public_reg_specs mul_public_instrs []
    (pcOutOfInstrs_exitCond ia mul_public_instrs) 12.

(* `strip` is the identity on a coerced plain-AST list; the EndToEnd bridges
   conclude over `strip instrs`, so MulPublicResult.v rewrites with this. *)
Lemma strip_id_mul_public_instrs : strip mul_public_instrs = mul_public_instrs.
Proof. reflexivity. Qed.

Lemma valid_mul_public_cfg_contract_param (ia : N) :
  ValidCFGVerifierContract (mul_public_cfg_contract_param ia).
Proof. intros; vm_compute; solve_vc; solve_symbase_fetch. Qed.
