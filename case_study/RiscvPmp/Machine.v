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
From Equations Require Import
     Equations.
From MicroSail Require Import
     Syntax.
From RiscvPmp Require Export
     Values.

Set Implicit Arguments.
Import CtxNotations.
Import EnvNotations.
Open Scope string_scope.

Module RiscvPmpTermKit <: TermKit.
  Module valuekit := RiscvPmpValueKit.
  Module Export VAL := Syntax.Values.Values valuekit.

  (** Variables **)
  Definition 𝑿        := string.
  Definition 𝑿_eq_dec := string_dec.
  Definition 𝑺        := string.
  Definition 𝑺_eq_dec := string_dec.

  Notation PCtx := (NCtx 𝑿 Ty).
  Notation LCtx := (NCtx 𝑺 Ty).

  Definition 𝑿to𝑺 (x : 𝑿) : 𝑺 := x.
  Definition fresh := Context.fresh (T := Ty).

  Module RiscvPmpVariableNotation.
    Notation "'rs1'" := "rs1" : string_scope.
    Notation "'rs2'" := "rs2" : string_scope.
    Notation "'rd'"  := "rd" : string_scope.
    Notation "'op'"  := "op" : string_scope.
  End RiscvPmpVariableNotation.
  Import RiscvPmpVariableNotation.

  (** Functions **)
  Inductive Fun : PCtx -> Ty -> Set :=
  | execute_RTYPE : Fun [rs2 ∶ ty_regidx, rs1 ∶ ty_regidx, rd ∶ ty_regidx, op ∶ ty_rop] ty_retired.

  Inductive FunX : PCtx -> Ty -> Set :=.

  Inductive Lem : PCtx -> Set :=. 

  Definition 𝑭  : PCtx -> Ty -> Set := Fun.
  Definition 𝑭𝑿  : PCtx -> Ty -> Set := FunX.
  Definition 𝑳  : PCtx -> Set := Lem.

  Inductive Reg : Ty -> Set :=
  | pc   : Reg ty_word
  | x1 : Reg ty_word
  | x2 : Reg ty_word.

  Section TransparentObligations.
    Local Set Transparent Obligations.
    Derive Signature NoConfusion for Reg.
  End TransparentObligations.

  Definition 𝑹𝑬𝑮 : Ty -> Set := Reg.
  Definition 𝑹𝑬𝑮_eq_dec : EqDec (sigT Reg).
  Proof.
    intros [? []] [? []]; cbn;
      first
        [ left; now apply eq_refl
        | right; intros e; dependent elimination e
        ].
  Defined.
End RiscvPmpTermKit.

Module RiscvPmpProgramKit <: (ProgramKit RiscvPmpTermKit).
  Module Export TM := Terms RiscvPmpTermKit.

  Import RiscvPmpVariableNotation.

  (** Functions **)
  Definition fun_execute_RTYPE : Stm [rs2 ∶ ty_regidx, rs1 ∶ ty_regidx, rd ∶ ty_regidx, op ∶ ty_rop] ty_retired := stm_lit ty_retired RETIRE_SUCCESS.

  Definition RegStore := GenericRegStore.
  Definition read_register := generic_read_register.
  Definition write_register := generic_write_register.
  Definition read_write := generic_read_write.
  Definition read_write_distinct := generic_read_write_distinct.
  Definition write_read := generic_write_read.
  Definition write_write := generic_write_write.

  (* Memory *)
  Definition Memory := Addr -> Word.

  Definition ForeignCall {σs σ} (f : 𝑭𝑿 σs σ) :
    forall (args : NamedEnv Lit σs) (res : string + Lit σ) (γ γ' : RegStore) (μ μ' : Memory), Prop :=
    match f with
    end.

  Lemma ForeignProgress {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Lit σs) γ μ :
    exists γ' μ' res, ForeignCall f args res γ γ' μ μ'.
  Proof.
    destruct f.
  Qed.


  Definition Pi {Δ τ} (f : Fun Δ τ) : Stm Δ τ :=
    match f with
    | execute_RTYPE => fun_execute_RTYPE
    end.

End RiscvPmpProgramKit.
