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
(* Example/Countdown.v — register countdown loop + memory countdown loop.   *)
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
     RiscvPmp.CFGVer.Spec
     RiscvPmp.Machine
     RiscvPmp.Sig.
From stdpp Require Import gmap.
From Katamaran Require Import
     RiscvPmp.CFGVer.Verifier
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

Import RiscvPmpCFGVerifExecutor.
Import Assembly.
Import RiscvPmp.Sig.
Import iris.proofmode.tactics.
Import asn.notations.
Import TermNotations.

    (* -4 in 13-bit two's complement: branches jump back 4 bytes (one instruction) *)
    Definition back_offset : bv 13 := bv.of_N 8188.

    (* -1 in 12-bit two's complement: ADDI immediate for decrement *)
    Definition neg_one_12 : bv 12 := bv.of_N 4095.

    (* Countdown program: X1 starts at 2 and counts down to 0.
       addr 0: ADDI X1 X1 (-1)  -- decrement X1
       addr 4: BNE X1 X0 (-4)   -- if X1 != 0, jump back to addr 0
       addr 8: exit (exitCond satisfied)
       Concrete execution: X1=2→1, BNE taken; X1=1→0, BNE not taken; exit.
       Backward branch actually fires, demonstrating CFGVer handles loops. *)
    Definition countdown_exitCond : bv xlenbits -> bool :=
      fun v => bv.ugeb v (bv.of_N 8).

    Definition countdown_cfg_contract : CFGVerifierContract :=
      gen_contract init_addr [(X1, true, Some (bv.of_N 2))] []
        [ADDI X1 X1 neg_one_12; BNE X1 X0 back_offset] []
        countdown_exitCond
        5.

    Lemma valid_countdown_cfg_contract :
      ValidCFGVerifierContract countdown_cfg_contract.
    Proof. vm_compute. solve_vc. Qed.


    (* Memory countdown: 4 instructions + a data word at address 16.
       addr  0: LOAD  imm=16 rs1=X0 rd=X1  -- X1 := mem[X0+16] = mem[16]
       addr  4: ADDI  X1 X1 (-1)            -- X1 := X1 - 1
       addr  8: STORE imm=16 rs2=X1 rs1=X0  -- mem[16] := X1
       addr 12: BNE   X1 X0 (-12)           -- if X1 ≠ 0, jump back to addr 0
       Data:    mem[16] = 2 initially.
       Two iterations: 2→1 (branch), 1→0 (fall-through); exit at pc=16. *)
    Definition back_12_offset : bv 13 := bv.of_N 8180.

    Definition countdown_mem_exitCond : bv xlenbits -> bool :=
      fun v => bv.ugeb v (bv.of_N 16).

    Definition countdown_mem_instrs : list AST :=
      [ LOAD (bv.of_N 16) X0 X1 false WORD
      ; ADDI X1 X1 neg_one_12
      ; STORE (bv.of_N 16) X1 X0 WORD
      ; BNE X1 X0 back_12_offset ].

    Definition countdown_mem_cfg_contract : CFGVerifierContract :=
      gen_contract init_addr [(X1, false, None)] [(bv.of_N 16, true, Some (bv.of_N 2))]
        countdown_mem_instrs []
        countdown_mem_exitCond
        10.

    Lemma valid_countdown_mem_cfg_contract :
      ValidCFGVerifierContract countdown_mem_cfg_contract.
    Proof. vm_compute. solve_vc. Qed.
