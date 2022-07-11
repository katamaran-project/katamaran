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
    ExpressionsOn TY <+
    TermsOn TY <+ PatternsOn TY <+
    OccursCheckOn TY <+ InstantiationOn TY <+
    PartialEvaluationOn TY.

  Notation PCtx := (NCtx PVar Ty).
  Notation LCtx := (NCtx LVar Ty).
  Notation Valuation Σ := (@Env (Binding LVar Ty) (fun xt : Binding LVar Ty => Val (@type LVar Ty xt)) Σ).
  Notation CStore := (@NamedEnv PVar Ty Val).

  (* Preciseness for spatial predicates *)
  Record Precise {P : Set} (F : P -> Ctx Ty) (p : P) : Set :=
    MkPrecise
      { prec_input  : Ctx Ty;
        prec_output : Ctx Ty;
        prec_inout  : F p = ctx.cat prec_input prec_output;
      }.
  Arguments MkPrecise {_ _ _} & _ _ _.

End BaseMixin.

Module Type Base := Types <+ RegDeclKit <+ BaseMixin.

Module DefaultBase <: Base.

  #[export] Instance typedeclkit : TypeDeclKit := DefaultTypeDeclKit.
  #[export] Instance typedenotekit : TypeDenoteKit typedeclkit := DefaultTypeDenoteKit.
  #[export] Instance typedefkit : TypeDefKit typedenotekit := DefaultTypeDefKit.
  #[export] Instance varkit : VarKit := DefaultVarKit.

  Include DefaultRegDeclKit.
  Include BaseMixin.

End DefaultBase.
