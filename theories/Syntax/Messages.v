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

From Katamaran Require Import
     Context
     Prelude
     Symbolic.Instantiation
     Symbolic.OccursCheck
     Syntax.Terms
     Syntax.TypeDecl
     Syntax.Variables.

Import ctx.notations.
Import option.notations.

Module Type MessagesOn
  (Import TY : Types)
  (Import TM : TermsOn TY)
  (Import IN : InstantiationOn TY TM)
  (Import OC : OccursCheckOn TY TM).

  #[local] Notation LCtx := (NCtx LVar Ty).

  Module amsg.
    Inductive CloseMessage (M : LCtx -> Type) (Σ : LCtx) : Type :=
    | there {b} (msg : M (Σ ▻ b)).
    #[global] Arguments there {_ _ _} msg.

    (* Without the precedence, typeclass resolution sometimes mysteriously enters a loop... *)
    #[export] Instance subst_closemessage `{Subst M} : Subst (CloseMessage M) | 2 :=
      fun {Σ} m {Σ2} ζ =>
        match m with
        | there msg => there (subst msg (sub_up1 ζ))
        end.

    #[export] Instance substlaws_closemessage `{SubstLaws M} : SubstLaws (CloseMessage M) | 2.
    Proof.
      constructor.
      - intros ? m. destruct m; cbn; f_equal;
          rewrite ?sub_up1_id; auto using subst_sub_id.
      - intros ? ? ? ? ? m. revert Σ1 ζ1 Σ2 ζ2.
        destruct m; cbn; intros; f_equal;
          rewrite ?sub_up1_comp; auto using subst_sub_comp.
    Qed.

    (* Without the precedence, typeclass resolution sometimes mysteriously enters a loop... *)
    #[export] Instance occurscheck_closemessage `{OccursCheck M} : OccursCheck (CloseMessage M) | 2 :=
      fun {Σ x} xIn m =>
        match m with
        | there msg => there <$> occurs_check (ctx.in_succ xIn) msg
        end.

    Inductive AMessage (Σ : LCtx) : Type :=
    | mk {M} {subM : Subst M} {subLM : SubstLaws M} {occM: OccursCheck M} (msg : M Σ).
    #[global] Arguments mk {_ _ _ _ _} msg.

    Definition empty {Σ} : AMessage Σ := mk (M := Unit) tt.

    Fixpoint closeAux {Σ ΣΔ} {struct ΣΔ} : forall {M} {subM : Subst M} {subLM : SubstLaws M} {occM: OccursCheck M}, M (Σ ▻▻ ΣΔ) -> AMessage Σ :=
      match ΣΔ with
      | []      => fun _ _ _ _ msg => mk msg
      | ΣΔ  ▻ b => fun _ _ _ _ msg => closeAux (there msg)
      end%ctx.

    Definition close {Σ ΣΔ} (msg : AMessage (Σ ▻▻ ΣΔ)) : AMessage Σ :=
      match msg with mk msg => closeAux msg end.

    #[export] Instance subst_amessage : Subst AMessage :=
      fix sub {Σ} m {Σ2} ζ {struct m} :=
        match m with
        | mk msg    => mk (subst msg ζ)
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

    #[export] Instance occurscheck_amessage : OccursCheck AMessage :=
      fix oc {Σ x} xIn m {struct m} :=
        match m with
        | mk msg    => mk <$> occurs_check xIn msg
        end.

    #[export] Instance instprop_amessage : InstProp AMessage :=
      fun _ _ _ => True.

    #[export] Instance instpropsubst_amessage : InstPropSubst AMessage.
    Proof. easy. Qed.

  End amsg.
  Export amsg (AMessage).
  Export (hints) amsg.

End MessagesOn.
