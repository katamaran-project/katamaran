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
    (* Jumps to `true_offset` when the value of X1 is equal to zero. X1 must
       be a public register (secLeak).

       ONE EXIT, AT THE JOIN POINT (2026-09-25, plans/PLAN-exit-targets.md
       §4a).  The program used to be the lone `[BEQ X1 X0 8]`, with TWO exits:
       the fall-through at +4 and the branch target at +8 (extra_exit_offs =
       [8]).  The trailing NOP makes both paths meet at +8, which is now the
       fall-through too, so extra_exit_offs = [] and the single-exit design
       applies.  It is the same discipline as cutting a real segment at the
       point where its paths rejoin.  To REVERT: restore
       `[BEQ X1 X0 true_offset] [8%N] … 3` here and the HexitOffs proof in
       JumpsResult.v from the commit before this change. *)
    (* ===== Phase 4.2: base-parametric jump_if_zero VC =====
       Supersedes the removed concrete-base pair jump_if_zero_cfg_contract /
       valid_jump_if_zero_cfg_contract (see MvSwap.v for the rationale). *)
    Definition jump_if_zero_cfg_contract_param (ia : N) : @CFGVerifierContract ["p" :: ty_xlenbits] :=
      gen_contract_param ia [(X1, true, None)]
        [BEQ X1 X0 true_offset; NOP]
        5.

    Lemma valid_jump_if_zero_cfg_contract_param (ia : N) :
      cfg_vc (jump_if_zero_cfg_contract_param ia) (cfg_instrs (jump_if_zero_cfg_contract_param ia)).
    Proof. solve_param_vc. Qed.
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
        [JAL X0 jmp_offset; NOP]
        5.

    Lemma valid_jmp_fwd_cfg_contract_param (ia : N) :
      cfg_vc (jmp_fwd_cfg_contract_param ia) (cfg_instrs (jmp_fwd_cfg_contract_param ia)).
    Proof. solve_param_vc. Qed.
    (* ===== end Phase 4.2 ===== *)

