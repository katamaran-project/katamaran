(******************************************************************************)
(* Copyright (c) 2019 Steven Keuchel                                          *)
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

From Coq Require Export
     Numbers.BinNums.

From Katamaran Require Export
     Context
     Environment
     Prelude
     Syntax.Registers
     Syntax.TypeDecl
     Syntax.TypeDef
     Syntax.Variables
     Tactics.
From Katamaran Require Import
     Syntax.BinOps
     Syntax.Expressions
     Syntax.Patterns
     Syntax.Terms
     Symbolic.Instantiation
     Symbolic.OccursCheck
     Symbolic.PartialEvaluation.

Module Type BaseMixin (Import TY : Types).
  Include
    BinOpsOn TY <+ ExpressionsOn TY <+
    TermsOn TY <+ PatternsOn TY <+
    OccursCheckOn TY <+ InstantiationOn TY <+
    PartialEvaluationOn TY.

  Lemma 𝑼_fold_inj {U} (v1 v2 : {K : 𝑼𝑲 U & Val (𝑼𝑲_Ty K)}) :
    𝑼_fold v1 = 𝑼_fold v2 <-> v1 = v2.
  Proof.
    split; try congruence. intros H.
    apply (f_equal (@𝑼_unfold U)) in H.
    now rewrite ?𝑼_unfold_fold in H.
  Qed.

  Lemma 𝑼_unfold_inj {U} (v1 v2 : Val (ty_union U)) :
    𝑼_unfold v1 = 𝑼_unfold v2 <-> v1 = v2.
  Proof.
    split; try congruence. intros H.
    apply (f_equal (@𝑼_fold U)) in H.
    now rewrite ?𝑼_fold_unfold in H.
  Qed.

  Notation PCtx := (NCtx 𝑿 Ty).
  Notation LCtx := (NCtx 𝑺 Ty).
  Notation Valuation Σ := (@Env (Binding 𝑺 Ty) (fun xt : Binding 𝑺 Ty => Val (@type 𝑺 Ty xt)) Σ).
  Notation CStore := (@NamedEnv 𝑿 Ty Val).
End BaseMixin.

Module Type Base := Types <+ RegDeclKit <+ BaseMixin.

Module DefaultBase <: Base :=
  DefaultVarKit <+ DefaultTypeDecl <+ DefaultTypeDefKit <+ DefaultRegDeclKit <+ BaseMixin.
