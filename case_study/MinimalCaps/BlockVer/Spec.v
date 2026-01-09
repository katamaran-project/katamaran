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

From Coq Require Import
     ZArith.ZArith
     Strings.String
     Lists.List.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Iris.Instance
     Iris.Base
     Notations
     Bitvector
     Sep.Hoare
     Specification
     MicroSail.ShallowExecutor
     MicroSail.ShallowSoundness
     MicroSail.SymbolicExecutor
     MicroSail.RefineExecutor
     MicroSail.Soundness.

From Katamaran.MinimalCaps Require Import
     Machine
     Sig
     Model.
From Katamaran.MinimalCaps.Contracts Require Import
     Notations
     Definitions
     Verification
     Statistics.
From iris.program_logic Require Import total_lifting.

Import ListNotations.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import env.notations.

Module MinCapsBlockVerifSpec <: Specification MinCapsBase MinCapsSignature MinCapsProgram.
  Include SpecificationMixin MinCapsBase MinCapsSignature MinCapsProgram.

  Definition CEnv : SepContractEnv :=
    fun Δ τ f =>
      match f with
      | _ => None
      end.

  Import MinCapsSignature.

  Definition CEnvEx : SepContractEnvEx.
    refine (
    fun Δ τ f =>
      match f with
      | _ => MkSepContract _ _ _ _ (asn.formula formula_true) "dummy" (asn.formula formula_true)
      end).
    Admitted.

   Definition LEnv : LemmaEnv.
     refine (
     fun Δ l =>
       match l with
         | _ => _
       end).
     Admitted.

End MinCapsBlockVerifSpec.

Module MinCapsBlockVerifShalExecutor :=
  MakeShallowExecutor MinCapsBase MinCapsSignature MinCapsProgram MinCapsBlockVerifSpec.
Module MinCapsBlockVerifExecutor :=
  MakeExecutor MinCapsBase MinCapsSignature MinCapsProgram MinCapsBlockVerifSpec.

Module MinCapsSpecVerif.
  Import MinCapsBlockVerifSpec.
  Import MinCapsBlockVerifExecutor.Symbolic.

  (* TODO: Proofs... *)

End MinCapsSpecVerif.
