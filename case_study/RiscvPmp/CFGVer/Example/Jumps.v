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

From Coq Require Import
     ZArith.ZArith
     Lists.List
     micromega.Lia
     Strings.String.
From Katamaran Require Import
     Notations
     Bitvector
     Semantics
     RiscvPmp.BlockVer.Spec
     RiscvPmp.BlockVer.Verifier
     RiscvPmp.Machine
     RiscvPmp.Sig.
From stdpp Require Import gmap.
From Katamaran Require
     RiscvPmp.CFGVer.Verifier.
From Katamaran Require Import
     RiscvPmp.CFGVer.Noninterference
     RiscvPmp.CFGVer.Tables
     RiscvPmp.CFGVer.Contracts
     RiscvPmp.CFGVer.GenContract.

From iris.proofmode Require string_ident tactics.

Import RiscvPmpProgram.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import bv.notations.
Import env.notations.
Import ListNotations.

Import RiscvPmpBlockVerifExecutor.
Import Assembly.
Import RiscvPmp.Sig.
Import iris.proofmode.tactics.
Import asn.notations.
Import TermNotations.

    Definition true_offset : bv 13 := bv.of_N 8.

    Import TermNotations.

    (* TODO: would rather write jump_if_zero (true_offset : bv 13) ... *)
    (* Jumps to `true_offset` when the value of X1 is equal to zero. The
         default offset allows one instruction between this block and the true
         block. X1 must be a public register (secLeak). *)
    Definition jump_if_zero_cfg_contract : CFGVerifierContract :=
      gen_contract init_addr [(X1, true, None)] []
        [BEQ X1 X0 true_offset] [8%N]
        (pcOutOfInstrs_exitCond init_addr [BEQ X1 X0 true_offset])
        3.

    Lemma valid_jump_if_zero_cfg_contract :
      ValidCFGVerifierContract jump_if_zero_cfg_contract.
    Proof. vm_compute. solve_vc. Qed.

    (* Unconditional forward jump: jumps 8 bytes ahead (2 instruction widths).
       The CFG verifier handles this correctly by following the actual PC. *)
    Definition jmp_offset : bv 21 := bv.of_N 8.

    (* CFGVer verification of jmp_fwd: the CFG verifier follows the actual PC
       after each instruction, so it correctly handles the forward jump that
       BlockVer cannot. Exit condition: PC ≥ 8 (execution left the block). *)
    Definition jmp_fwd_exitCond : bv xlenbits -> bool :=
      fun v => bv.ugeb v (bv.of_N 8).

    Definition jmp_fwd_cfg_contract : CFGVerifierContract :=
      gen_contract init_addr [] [] [JAL X0 jmp_offset; NOP] [] jmp_fwd_exitCond 5.

    Lemma valid_jmp_fwd_cfg_contract : ValidCFGVerifierContract jmp_fwd_cfg_contract.
    Proof. vm_compute. solve_vc. Qed.

