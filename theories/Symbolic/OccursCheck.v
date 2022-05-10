(******************************************************************************)
(* Copyright (c) 2019 Dominique Devriese, Georgy Lukyanov,                    *)
(*   Sander Huyghebaert, Steven Keuchel                                       *)
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

From Equations Require Import
     Equations.
From Katamaran Require Import
     Context
     Environment
     Notations
     Prelude
     Syntax.BinOps
     Syntax.Terms
     Syntax.TypeDef
     Tactics.

Import ctx.notations.
Import env.notations.
Import option.
Import option.notations.

Local Set Implicit Arguments.

Module Type OccursCheckOn
  (Import TY : Types)
  (Import BO : BinOpsOn TY)
  (Import TM : TermsOn TY BO).

  Local Notation LCtx := (NCtx 𝑺 Ty).

  Class OccursCheck (T : LCtx -> Type) : Type :=
    occurs_check : forall {Σ x} (xIn : x ∈ Σ) (t : T Σ), option (T (Σ - x)).

  #[export] Instance occurs_check_env {I : Set} {T : LCtx -> I -> Set}
         {OCT : forall i, OccursCheck (fun Σ => T Σ i)} :
    forall {Γ : Ctx I}, OccursCheck (fun Σ => Env (T Σ) Γ) :=
    fix oc {Γ Σ x} xIn ts {struct ts} :=
      match ts with
      | env.nil         => Some env.nil
      | env.snoc ts _ t =>
          ts' <- occurs_check (OccursCheck := @oc _) xIn ts;;
          t'  <- occurs_check xIn t;;
          Some (env.snoc ts' _ t')
      end.

  #[export] Instance occurs_check_term : forall σ, OccursCheck (fun Σ => Term Σ σ) :=
    fix occurs_check_term {τ Σ x} xIn (t : Term Σ τ) {struct t} : option (Term (Σ - x) τ) :=
      match t with
      | @term_var _ y _ yIn => match ctx.occurs_check_var xIn yIn with
                              | inl _    => None
                              | inr yIn' => Some (term_var y)
                              end
      | term_val σ v => Some (term_val σ v)
      | term_binop op t1 t2 =>
          t1' <- occurs_check_term xIn t1;;
          t2' <- occurs_check_term xIn t2;;
          Some (term_binop op t1' t2')
      | term_neg t => term_neg <$> occurs_check_term xIn t
      | term_not t => term_not <$> occurs_check_term xIn t
      | term_inl t => term_inl <$> occurs_check_term xIn t
      | term_inr t => term_inr <$> occurs_check_term xIn t
      | term_union U K t0 => term_union U K <$> occurs_check_term xIn t0
      | term_record R ts =>
        let OCTerm xt := @occurs_check_term (@type 𝑹𝑭 Ty xt) in
        term_record R <$> occurs_check (OccursCheck := occurs_check_env (OCT := OCTerm)) xIn ts
      end.

  #[export] Instance occurs_check_list {T : LCtx -> Type} `{OccursCheck T} :
    OccursCheck (List T) :=
    fun _ _ xIn => traverse_list (occurs_check xIn).

  #[export] Instance occurs_check_sub {Σ} : OccursCheck (Sub Σ) :=
    occurs_check_env.

  #[export] Instance occurs_check_pair {AT BT} `{OccursCheck AT, OccursCheck BT} :
    OccursCheck (Pair AT BT) :=
    fun _ _ xIn '(a,b) =>
      a' <- occurs_check xIn a ;;
      b' <- occurs_check xIn b ;;
      Some (a', b').

  #[export] Instance occurs_check_option {AT} `{OccursCheck AT} :
    OccursCheck (Option AT) :=
    fun _ _ xIn ma =>
      match ma with
      | Some a => option.map Some (occurs_check xIn a)
      | None   => Some None
      end.

  #[export] Instance occurs_check_unit : OccursCheck Unit :=
    fun _ _ _ t => match t with tt => Some tt end.

  Definition OccursCheckShiftPoint {T} {subT : Subst T} {ocT : OccursCheck T} :
    forall {Σ x} (xIn : x ∈ Σ) (t : T (Σ - x)), Prop :=
    fun Σ x xIn t => wp (eq t) (occurs_check xIn (subst t (sub_shift xIn))).

  Definition OccursCheckSoundPoint {T} {subT : Subst T} {ocT : OccursCheck T} :
    forall {Σ x} (xIn : x ∈ Σ) (t : T Σ) , Prop :=
    fun Σ x xIn t => wlp (fun t' => t = subst t' (sub_shift xIn)) (occurs_check xIn t).

  Class OccursCheckLaws (T : LCtx -> Type) `{Subst T, OccursCheck T} : Prop :=
    { occurs_check_shift {Σ x} (xIn : x ∈ Σ) (t : T (Σ - x)) : OccursCheckShiftPoint xIn t;
      occurs_check_sound {Σ x} (xIn : x ∈ Σ) (t : T Σ) : OccursCheckSoundPoint xIn t;
    }.
  Global Arguments OccursCheckLaws T {_ _}.

  Ltac occurs_check_mixin :=
    match goal with
    | H: ?P |- ?P => exact H
    | |- ?x = ?x => refine eq_refl
    | |- ?x = ?y =>
        let hx := head x in
        let hy := head y in
        is_constructor hx; is_constructor hy;
        first [ subst; refine eq_refl (* | f_equal *) ]
    | |- wlp _ (occurs_check ?xIn ?t) =>
        generalize (occurs_check_sound xIn t);
        apply wlp_monotonic; intros ? ->
    | |- wp _ (occurs_check ?xIn (subst ?t _)) =>
        generalize (occurs_check_shift xIn t);
        apply wp_monotonic; intros ? <-
    | |- OccursCheckLaws _ =>
        constructor; unfold OccursCheckShiftPoint, OccursCheckSoundPoint;
        let x := fresh in
        intros ? ? ? x; induction x
    end.

  Ltac occurs_check_derive :=
    repeat
      (try progress cbn;
       first
         [ option.tactics.mixin
         | occurs_check_mixin]);
    try progress cbn; try easy.
  Local Ltac derive := occurs_check_derive.

  Lemma occurs_check_env_shift_point {B : Set} {T : LCtx -> B -> Set}
    {subT: forall b : B, Subst (fun Σ => T Σ b)}
    {ocT : forall b : B, OccursCheck (fun Σ => T Σ b)}
    {Σ : LCtx} {x} (xIn : x ∈ Σ)
    {Γ : Ctx B} (ts : Env (T (Σ - x)) Γ) :
    env.All (fun b => OccursCheckShiftPoint xIn) ts ->
    OccursCheckShiftPoint xIn ts.
  Proof. unfold OccursCheckShiftPoint. induction 1; derive. Qed.

  Lemma occurs_check_env_sound_point {B : Set} {T : LCtx -> B -> Set}
    {subT: forall b : B, Subst (fun Σ => T Σ b)}
    {ocT : forall b : B, OccursCheck (fun Σ => T Σ b)}
    {Σ : LCtx} {x} (xIn : x ∈ Σ)
    {Γ : Ctx B} (ts : Env (T Σ) Γ) :
    env.All (fun b t => OccursCheckSoundPoint xIn t) ts ->
    OccursCheckSoundPoint xIn ts.
  Proof. unfold OccursCheckSoundPoint; induction 1; derive. Qed.

  #[export] Instance occurs_check_laws_term {τ} :
    OccursCheckLaws (fun Σ => Term Σ τ).
  Proof.
    derive.
    - unfold sub_shift. rewrite env.lookup_tabulate. cbn.
      now rewrite ctx.occurs_check_shift_var.
    - generalize (occurs_check_env_shift_point IH).
      apply wp_monotonic. intros ? <-. reflexivity.
    - pose proof (ctx.occurs_check_var_spec xIn ςInΣ) as H.
      destruct (ctx.occurs_check_var xIn ςInΣ); constructor; cbn.
      destruct H as [H1 H2]. subst. unfold sub_shift.
      now rewrite env.lookup_tabulate.
    - generalize (occurs_check_env_sound_point IH).
      apply wlp_monotonic. now intros ts' ->.
  Qed.

  #[export] Instance occurs_check_laws_list {T : LCtx -> Type} `{OccursCheckLaws T} :
    OccursCheckLaws (fun Σ => list (T Σ)).
  Proof. derive. Qed.

  #[export] Instance occurs_check_laws_env {I : Set} {T : LCtx -> I -> Set}
   {_ : forall i : I, Subst (fun Σ => T Σ i)}
   {_ : forall i : I, OccursCheck (fun Σ => T Σ i)}
   {_ : forall i : I, OccursCheckLaws (fun Σ => T Σ i)}
   {Γ : Ctx I} :
    OccursCheckLaws (fun Σ => Env (T Σ) Γ).
  Proof. derive. Qed.

  #[export] Instance occurs_check_laws_sub {Σ} : OccursCheckLaws (Sub Σ) :=
    occurs_check_laws_env.

  #[export] Instance occurs_check_laws_pair {AT BT} `{OccursCheckLaws AT, OccursCheckLaws BT} :
    OccursCheckLaws (Pair AT BT).
  Proof. derive. Qed.

  #[export] Instance occurs_check_laws_option {AT} `{OccursCheckLaws AT} :
    OccursCheckLaws (Option AT).
  Proof. derive. Qed.

  #[export] Instance occurs_check_laws_unit : OccursCheckLaws Unit.
  Proof. derive. Qed.

End OccursCheckOn.
