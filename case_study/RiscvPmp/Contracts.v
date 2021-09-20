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
     Strings.String.
From RiscvPmp Require Import
     Machine.
From MicroSail Require Import
     Symbolic.Mutator
     Sep.Spec
     Syntax.
From Equations Require Import
     Equations.

Set Implicit Arguments.
Import CtxNotations.
Import EnvNotations.
Open Scope string_scope.
Open Scope ctx_scope.
Open Scope Z_scope.

Inductive Predicate : Set :=.

Section TransparentObligations.
  Local Set Transparent Obligations.

  Derive NoConfusion for Predicate.

End TransparentObligations.

Derive EqDec for Predicate.

Module Export RiscvPmpAssertionKit <: (AssertionKit RiscvPmpTermKit RiscvPmpProgramKit).
  Export RiscvPmpProgramKit.

  Definition 𝑷 := Predicate.
  Definition 𝑷_Ty (p : 𝑷) : Ctx Ty :=
    match p with
    end.

  Instance 𝑷_is_dup : IsDuplicable Predicate := {
    is_duplicable p :=
      match p with
      end
    }.
  Instance 𝑷_eq_dec : EqDec 𝑷 := Predicate_eqdec.
End RiscvPmpAssertionKit.

Module RiscvPmpSymbolicContractKit <: (SymbolicContractKit RiscvPmpTermKit
                                                           RiscvPmpProgramKit
                                                           RiscvPmpAssertionKit).
  Module Export ASS := Assertions RiscvPmpTermKit
                                  RiscvPmpProgramKit
                                  RiscvPmpAssertionKit.

  Import RiscvPmpVariableNotation.

  Definition SepContractFun {Δ τ} (f : Fun Δ τ) : Type :=
    SepContract Δ τ.

  Definition sep_contract_execute_RTYPE : SepContractFun execute_RTYPE :=
    {| sep_contract_logic_variables := [rs2 ∶ ty_regidx, rs1 ∶ ty_regidx, rd ∶ ty_regidx, op ∶ ty_rop];
       sep_contract_localstore      := [term_var rs2, term_var rs1, term_var rd, term_var op]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_execute_RTYPE";
       sep_contract_postcondition   := asn_true;
    |}.

  Definition CEnv : SepContractEnv :=
    fun Δ τ f =>
      match f with
      | execute_RTYPE => Some sep_contract_execute_RTYPE
      | _             => None
      end.

  Definition CEnvEx : SepContractEnvEx :=
    fun Δ τ f =>
      match f with
      end.

  Definition LEnv : LemmaEnv :=
    fun Δ l =>
      match l with
      end.

  Lemma linted_cenvex :
    forall Δ τ (f : FunX Δ τ),
      Linted (CEnvEx f).
  Proof.
    intros ? ? []; try constructor.
  Qed.
End RiscvPmpSymbolicContractKit.

Module RiscvPmpMutators :=
  Mutators
    RiscvPmpTermKit
    RiscvPmpProgramKit
    RiscvPmpAssertionKit
    RiscvPmpSymbolicContractKit.
Import RiscvPmpMutators.
Import SMut.

Definition ValidContract {Δ τ} (f : Fun Δ τ) : Prop :=
  match CEnv f with
  | Some c => ValidContractReflect c (Pi f)
  | None => False
  end.

Lemma valid_contract_execute_RTYPE : ValidContract execute_RTYPE.
Proof. Admitted.
