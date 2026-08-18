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
(* Example/Jumps.v — jump_if_zero (conditional branch) and jmp_fwd (JAL).   *)
(*                                                                           *)
(* The instruction list and reg/mem spec definitions below are               *)
(* STATEMENT-RELEVANT: the noninterference theorems in Results.v reference   *)
(* them by name.  The contracts and valid_* VC proofs are not.               *)
(* ========================================================================= *)

From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.

    Definition true_offset : bv 13 := bv.of_N 8.

    Import TermNotations.

    (* TODO: would rather write jump_if_zero (true_offset : bv 13) ... *)
    (* Jumps to `true_offset` when the value of X1 is equal to zero. The
         default offset allows one instruction between the fall-through path
         and the branch target. X1 must be a public register (secLeak). *)
    (* ===== Phase 4.2: base-parametric jump_if_zero VC =====
       Supersedes the removed concrete-base pair jump_if_zero_cfg_contract /
       valid_jump_if_zero_cfg_contract (see MvSwap.v for the rationale). *)
    Definition jump_if_zero_cfg_contract_param (ia : N) : @CFGVerifierContract ["p" :: ty_xlenbits] :=
      gen_contract_param ia [(X1, true, None)]
        [BEQ X1 X0 true_offset] [8%N]
        (pcOutOfInstrs_exitCond ia [BEQ X1 X0 true_offset])
        3.

    Lemma valid_jump_if_zero_cfg_contract_param (ia : N) :
      ValidCFGVerifierContract (jump_if_zero_cfg_contract_param ia).
    Proof. intros; vm_compute; solve_vc; solve_symbase_fetch. Qed.
    (* ===== end Phase 4.2 ===== *)

    (* Unconditional forward jump: jumps 8 bytes ahead (2 instruction widths).
       The CFG verifier handles this correctly by following the actual PC. *)
    Definition jmp_offset : bv 21 := bv.of_N 8.

    (* CFGVer verification of jmp_fwd: the CFG verifier follows the actual PC
       after each instruction, so it correctly handles the forward jump that
       BlockVer cannot. Exit condition: PC ≥ 8 (execution left the program). *)
    Definition jmp_fwd_exitCond : bv xlenbits -> bool :=
      fun v => bv.ugeb v (bv.of_N 8).

    (* ===== Phase 4.2: base-parametric jmp_fwd VC =====
       Supersedes the removed concrete-base pair jmp_fwd_cfg_contract /
       valid_jmp_fwd_cfg_contract (see MvSwap.v for the rationale). *)
    Definition jmp_fwd_cfg_contract_param (ia : N) : @CFGVerifierContract ["p" :: ty_xlenbits] :=
      gen_contract_param ia []
        [JAL X0 jmp_offset; NOP] []
        (pcOutOfInstrs_exitCond ia [JAL X0 jmp_offset; NOP])
        5.

    Lemma valid_jmp_fwd_cfg_contract_param (ia : N) :
      ValidCFGVerifierContract (jmp_fwd_cfg_contract_param ia).
    Proof. intros; vm_compute; solve_vc; solve_symbase_fetch. Qed.
    (* ===== end Phase 4.2 ===== *)

