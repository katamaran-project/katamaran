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
(* Example/MvSwap.v — register-move examples and the 3-register swap.       *)
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

(* Contract-literal sugar (kept Local: it turns {{ / }} into lexer
   keywords, so it must not leak beyond this file). *)
Local Notation "'{{' P '}}' i '@cfg[' ec ',' fl ']'" :=
  (@MkCFGVerifierContract [ctx] init_addr
     (term_val ty_xlenbits (bv.of_N init_addr))
     (exits_of_list (term_val ty_xlenbits (bv.of_N init_addr)) i)
     P%asn i ec fl)
  (at level 90).
Local Notation "'{{' P '}}' i '@cfg[' ec ',' fl ']' 'with' logvars" :=
  (@MkCFGVerifierContract logvars init_addr
     (term_val ty_xlenbits (bv.of_N init_addr))
     (exits_of_list (term_val ty_xlenbits (bv.of_N init_addr)) i)
     P%asn i ec fl)
  (at level 90).

    Definition mv_zero_ex : CFGVerifierContract :=
      {{ asn_init_pc (bv.of_N init_addr) ∗ ∃ "v", X1 ↦ᵣ term_var "v" }}
        [MV X1 X0]
      @cfg[ pcOutOfInstrs_exitCond init_addr [MV X1 X0] , 3 ].

    Example valid_mv_zero_ex : ValidCFGVerifierContract mv_zero_ex.
    Proof. vm_compute. solve_vc. Qed.

    Definition mv_same_reg_ex : CFGVerifierContract :=
      {{ asn_init_pc (bv.of_N init_addr) ∗ X1 ↦ᵣ term_var "x" }}
        [MV X1 X1]
      @cfg[ pcOutOfInstrs_exitCond init_addr [MV X1 X1] , 3 ]
      with ["x" :: ty_xlenbits].

    Example valid_mv_same_reg_ex : ValidCFGVerifierContract mv_same_reg_ex.
    Proof. vm_compute. solve_vc. Qed.

    Definition mv_ex : CFGVerifierContract :=
      {{ asn_init_pc (bv.of_N init_addr) ∗ X1 ↦ᵣ term_var "x" ∗ X2 ↦ᵣ term_var "y" }}
        [MV X1 X2]
      @cfg[ pcOutOfInstrs_exitCond init_addr [MV X1 X2] , 3 ]
      with ["x" :: ty_xlenbits; "y" :: ty_xlenbits].

    Example valid_mv_ex : ValidCFGVerifierContract mv_ex.
    Proof. vm_compute. solve_vc. Qed.

    (* Nonzero-start demonstrator for Step 2 (init_addr parameterization):
       a single MV loaded at address 256 (0x100, 4-byte aligned) instead of
       the usual 0. Exercises gen_contract's init_addr parameter (building
       asn_init_pc (bv.of_N 256)), and the executor's base<=pc load guard
       at a genuinely nonzero base (first fetch index (256-256)/4 = 0).
       Uses a manually-correct exit condition (pc >= 256+4) rather than
       pcOutOfInstrs_exitCond, whose threshold is still absolute-zero-
       relative (4*|instrs|, not init_addr + 4*|instrs|) -- parameterizing
       it is Step 4, not yet done; using it here at a nonzero start would
       make the exit condition trivially true from the very first pc,
       making the contract vacuously (not meaningfully) valid. *)
    Definition mv_nonzero_start_ex : CFGVerifierContract :=
      gen_contract (256%N) [(X1, false, None)] []
        [MV X1 X0] []
        (fun v => bv.ugeb v (bv.of_N 260))
        3.

    Example valid_mv_nonzero_start_ex : ValidCFGVerifierContract mv_nonzero_start_ex.
    Proof. vm_compute. solve_vc. Qed.

    Definition swap_cfg_contract : CFGVerifierContract :=
      gen_contract init_addr
        [(X1, false, None); (X2, false, None); (X3, false, None)] []
        [MV X3 X2; MV X2 X1; MV X1 X3] []
        (pcOutOfInstrs_exitCond init_addr [MV X3 X2; MV X2 X1; MV X1 X3])
        5.

    Lemma valid_swap_cfg_contract : ValidCFGVerifierContract swap_cfg_contract.
    Proof. vm_compute. solve_vc. Qed.
