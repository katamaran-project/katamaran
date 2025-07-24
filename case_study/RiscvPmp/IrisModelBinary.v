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

From Katamaran Require Import
     Bitvector
     Environment
     trace
     Iris.Base
     Iris.BinaryResources
     RiscvPmp.Machine
     RiscvPmp.IrisModel
     RiscvPmp.IrisInstance.
From iris Require Import
     base_logic.lib.gen_heap
     proofmode.tactics.

Set Implicit Arguments.

Import RiscvPmpProgram.

(* Instantiate the Iris framework solely using the operational semantics. At
   this point we do not commit to a set of contracts nor to a set of
   user-defined predicates. *)
Module RiscvPmpIrisBase2 <: IrisBase2 RiscvPmpBase RiscvPmpProgram RiscvPmpSemantics.
  (* Pull in the definition of the LanguageMixin and register ghost state. *)
  Include RiscvPmpIrisBase.
  Import RiscvPmpIrisAdeqParameters.

  (* Defines the memory ghost state. *)
  Section RiscvPmpIrisParams2.
    Import bv.

    Class mcMemGS2 Σ :=
      McMemGS2 {
          (* two copies of the unary ghost variables *)
          mc_ghGS2_left : RiscvPmpIrisBase.mcMemGS Σ
        ; mc_ghGS2_right : RiscvPmpIrisBase.mcMemGS Σ
        }.

    Definition memGS2 : gFunctors -> Set := mcMemGS2.
    Existing Class memGS2.
    Definition memGS2_memGS_left : forall `{mG : memGS2 Σ}, memGS Σ := @mc_ghGS2_left.
    Definition memGS2_memGS_right : forall `{mG : memGS2 Σ}, memGS Σ := @mc_ghGS2_right.
    Definition mem_inv2 : forall {Σ}, memGS2 Σ -> Memory -> Memory -> iProp Σ :=
      fun {Σ} hG μ1 μ2 =>
        (RiscvPmpIrisBase.mem_inv memGS2_memGS_left μ1 ∗ RiscvPmpIrisBase.mem_inv memGS2_memGS_right μ2)%I.
    Lemma mem_inv2_mem_inv :
      forall `{mG : memGS2 Σ} (μ1 μ2 : Memory),
        mem_inv2 mG μ1 μ2 ⊣⊢ mem_inv memGS2_memGS_left μ1 ∗ mem_inv memGS2_memGS_right μ2.
    Proof. by unfold mem_inv2. Qed.

    Definition memGS2_gtGS2_left `{mG : memGS2 Σ} : traceG Trace Σ :=
      @mc_gtGS _ memGS2_memGS_left.
    Definition memGS2_gtGS2_right `{mG : memGS2 Σ} : traceG Trace Σ :=
      @mc_gtGS _ memGS2_memGS_right.
  End RiscvPmpIrisParams2.

  Include IrisResources2 RiscvPmpBase RiscvPmpProgram RiscvPmpSemantics.
End RiscvPmpIrisBase2.

