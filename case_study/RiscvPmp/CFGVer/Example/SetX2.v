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
(* Example/SetX2.v — set_X2_to_42 and its symbolic-base PoC variant.        *)
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

    Definition set_X2_to_42 : CFGVerifierContract :=
      gen_contract init_addr [(X2, false, None)] []
        [ADDI X2 X0 (bv.of_N 42)] []
        (pcOutOfInstrs_exitCond init_addr [ADDI X2 X0 (bv.of_N 42)])
        3.

    Lemma valid_set_X2_to_42 : ValidCFGVerifierContract set_X2_to_42.
    Proof. vm_compute. solve_vc. Qed.

    (* ===== Phase 4.2 proof-of-concept — genuine symbolic placement term_var "p" =====
       Unlike gen_contract (which hardwires cfg_placement := term_val (bv.of_N
       init_addr) and Σ := [ctx]), this contract lives at Σ = ["p"∷ty_xlenbits]
       and uses the *term variable* term_var "p" as the base — the only base
       formulation the VC can discharge, because it keeps every bv.of_N applied
       to concrete offsets (a Coq-N base lifted via term_val (bv.of_N n) makes
       vm_compute diverge on bv.of_N of a symbolic N at width 32; see the
       divergent gen_contract-based valid_cmovznz4_cfg_contract_at_start).

       Two things a parameterized contract needs that the concrete ones don't:
       (1) a precondition BOUND on the base — `unsigned p + 4·len ≤ 1024` — so
           the instruction-fetch upper bound is dischargeable (this is the
           `(bound)` premise the ∀ init_addr noninterference theorem carries);
       (2) a manual tail closing the offset-0 fetch LOWER bound: at the first
           instruction the pc is the bare base p (offset 0 collapses
           bvadd (of_N 0) p → p), so the Phase-0 fetch-bound helpers — written
           for the bvadd (of_N c) base shape — don't fire.  Generalizing
           solve_vc to absorb this tail (and confirming the bvadd-wrapped
           bounds fire for k>0) is the open work for the full cmovznz4 case. *)
    Definition set_X2_to_42_param (ia : N) : @CFGVerifierContract ["p" :: ty_xlenbits] :=
      gen_contract_param ia [(X2, false, None)] []
        [ADDI X2 X0 (bv.of_N 42)] []
        (pcOutOfInstrs_exitCond ia [ADDI X2 X0 (bv.of_N 42)]) 3.

    Lemma valid_set_X2_to_42_param (ia : N) :
      ValidCFGVerifierContract (set_X2_to_42_param ia).
    Proof.
      intros. vm_compute. solve_vc.
      (* offset-0 bare-base fetch lower bound: base is SyncVal (from secLeak) *)
      match goal with
        Hs : RiscvPmpSignature.secLeak ?x |- _ =>
          destruct x as [? | ? ?]; [ | destruct Hs ]
      end; cbn; unfold bv.unsigned; lia.
    Qed.
    (* ===== end Phase 4.2 proof-of-concept ===== *)
