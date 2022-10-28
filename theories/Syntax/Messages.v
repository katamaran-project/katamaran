(******************************************************************************)
(* Copyright (c) 2022 Steven Keuchel                                          *)
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
     Bool.Bool
     Classes.Morphisms
     Classes.RelationClasses
     Program.Basics
     Program.Tactics
     ZArith.

From Katamaran Require Import
     Context
     Environment
     Notations
     Prelude
     Symbolic.OccursCheck
     Syntax.BinOps
     Syntax.Terms
     Syntax.TypeDecl
     Syntax.Variables
     Tactics.

From Equations Require Import
     Equations.

Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.

Module Type MessagesOn
  (Import TY : Types)
  (Import TM : TermsOn TY)
  (Import OC : OccursCheckOn TY TM).

  Local Notation LCtx := (NCtx LVar Ty).

  Module amsg.
    Inductive AMessage (Σ : LCtx) : Type :=
    | mk {M} {subM : Subst M} {subLM : SubstLaws M} {occM: OccursCheck M} (msg : M Σ)
    | there {b} (msg : AMessage (Σ ▻ b)).
    #[global] Arguments mk {_ _ _ _ _} msg.
    #[global] Arguments there {_ _} msg.

    Fixpoint close {Σ ΣΔ} {struct ΣΔ} : AMessage (Σ ▻▻ ΣΔ) -> AMessage Σ :=
      match ΣΔ with
      | []      => fun msg => msg
      | ΣΔ  ▻ b => fun msg => close (there msg)
      end%ctx.

    #[export] Instance subst_amessage : Subst AMessage :=
      fix sub {Σ} m {Σ2} ζ {struct m} :=
        match m with
        | mk msg    => mk (subst msg ζ)
        | there msg => there (sub msg (sub_up1 ζ))
        end.

    #[export] Instance substlaws_amessage : SubstLaws AMessage.
    Proof.
      constructor.
      - intros ? m. induction m; cbn; f_equal;
          rewrite ?sub_up1_id; auto using subst_sub_id.
      - intros ? ? ? ? ? m. revert Σ1 ζ1 Σ2 ζ2.
        induction m; cbn; intros; f_equal;
          rewrite ?sub_up1_comp; auto using subst_sub_comp.
    Qed.

    Import option.notations.
    #[export] Instance occurscheck_amessage : OccursCheck AMessage :=
      fix oc {Σ x} xIn m {struct m} :=
        match m with
        | mk msg    => mk <$> occurs_check xIn msg
        | there msg => there <$> oc (ctx.in_succ xIn) msg
        end.

  End amsg.
  Export amsg (AMessage).
  Export (hints) amsg.

End MessagesOn.
