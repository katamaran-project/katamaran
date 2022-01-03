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

From Coq Require Import
     Program.Tactics.

From Equations Require Import
     Equations.
From Katamaran Require Import
     Context
     Environment
     Notation
     Prelude
     Syntax.BinOps
     Syntax.Terms
     Syntax.TypeDef
     Tactics.

Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.

Module Type OccursCheckOn
  (Import TY : Types)
  (Import BO : BinOpsOn TY)
  (Import TM : TermsOn TY BO).

  Local Notation LCtx := (NCtx 𝑺 Ty).

  Class OccursCheck (T : LCtx -> Type) : Type :=
    occurs_check : forall {Σ x} (xIn : x ∈ Σ) (t : T Σ), option (T (Σ - x)%ctx).
  Class OccursCheckLaws (T : LCtx -> Type) `{Subst T, OccursCheck T} : Prop :=
    { occurs_check_shift {Σ x σ} (xIn : x∷σ ∈ Σ) (t : T (Σ - x∷σ)) :
        occurs_check xIn (subst t (sub_shift xIn)) = Some t;
      occurs_check_sound {Σ x} (xIn : x ∈ Σ) (t : T Σ) (t' : T (Σ - x)) :
        occurs_check xIn t = Some t' -> t = subst t' (sub_shift xIn);
    }.
  Global Arguments OccursCheckLaws T {_ _}.

  Import stdpp.base.

  Fixpoint occurs_check_term {Σ x} (xIn : x ∈ Σ) {σ} (t : Term Σ σ) : option (Term (Σ - x) σ) :=
    match t with
    | @term_var _ ς σ0 ςInΣ =>
      match ctx.occurs_check_var xIn ςInΣ with
      | inl e     => None
      | inr ςInΣ' => Some (@term_var _ _ _ ςInΣ')
      end
    | term_val σ0 v => Some (term_val σ0 v)
    | term_binop op t1 t2 =>
      t1' ← occurs_check_term xIn t1; t2' ← occurs_check_term xIn t2; Some (term_binop op t1' t2')
    | term_neg t => option_map term_neg (occurs_check_term xIn t)
    | term_not t => option_map term_not (occurs_check_term xIn t)
    | term_inl t => option_map term_inl (occurs_check_term xIn t)
    | term_inr t => option_map term_inr (occurs_check_term xIn t)
    | @term_projtup _ σs t n σ p =>
      option_map (fun t' => @term_projtup _ _ t' n _ p) (occurs_check_term xIn t)
    | term_union U K t => option_map (term_union U K) (occurs_check_term xIn t)
    | term_record R es => option_map (term_record R) (env.traverse (fun _ => occurs_check_term xIn) es)
    (* | term_projrec t rf => option_map (fun t' => term_projrec t' rf) (occurs_check_term xIn t) *)
    end.

  Global Instance OccursCheckTerm {σ} : OccursCheck (fun Σ => Term Σ σ) :=
    fun _ _ xIn => occurs_check_term xIn.

  Global Instance OccursCheckList {T : LCtx -> Type} `{OccursCheck T} :
    OccursCheck (List T) :=
    fun _ _ xIn => traverse_list (occurs_check xIn).

  Global Instance OccursCheckEnv {I : Set} {T : LCtx -> I -> Set}
         {_ : forall i : I, OccursCheck (fun Σ => T Σ i)}
         {Γ : Ctx I} :
    OccursCheck (fun Σ => Env (T Σ) Γ) :=
    fun _ _ xIn => env.traverse (fun i => occurs_check (T := fun Σ => T Σ i) xIn).

  Global Instance OccursCheckSub {Σ} : OccursCheck (Sub Σ) :=
    OccursCheckEnv.

  Lemma option_map_eq_some {A B} (f : A -> B) (o : option A) (a : A) :
    o = Some a ->
    option_map f o = Some (f a).
  Proof. now intros ->. Qed.

  Lemma option_map_eq_some' {A B} (f : A -> B) (o : option A) (b : B) :
    option_map f o = Some b <->
    exists a, o = Some a /\ f a = b.
  Proof.
    split.
    - destruct o as [a|].
      + intros H. apply noConfusion_inv in H. cbn in H.
        exists a. split; congruence.
      + discriminate.
    - now intros (a & -> & <-).
  Qed.

  Lemma option_bind_eq_some {A B} (f : A -> option B) (o : option A) (b : B) :
    (exists a, o = Some a /\ f a = Some b) <->
    option.option_bind A B f o = Some b.
  Proof.
    split.
    - now intros (a & -> & <-).
    - destruct o as [a|]; [ now exists a | discriminate ].
  Qed.

  Local Ltac solve :=
    repeat
      match goal with
      | H: Some _ = Some _ |- _ =>
        apply noConfusion_inv in H; cbn in H; subst
      | H: base.mbind _ _ = Some _ |- _ =>
        apply option_bind_eq_some in H; cbn in H; destruct_conjs; subst
      | H: option_map _ _ = Some _ |- _ =>
        apply option_map_eq_some' in H; cbn in H; destruct_conjs; subst

      | |- match occurs_check_term ?xIn ?t with _ => _ end = _ =>
        destruct (occurs_check_term xIn t); try discriminate
      | |- match occurs_check ?xIn ?t with _ => _ end = _ =>
        destruct (occurs_check xIn t); try discriminate
      | |- base.mbind _ _ = Some _ =>
        apply option_bind_eq_some; eexists; split; [ eassumption; fail | idtac ]
      | |- option_map ?f _ = Some (?f _) =>
        apply option_map_eq_some
      | |- option_map _ _ = Some _ =>
        apply option_map_eq_some'; eexists; split; [ eassumption; fail | idtac ]
      | |- _ =>
        unfold base.mret, option.option_ret in *; cbn in *; try congruence
      end.

  Global Instance OccursCheckLawsTerm {τ} : OccursCheckLaws (fun Σ => Term Σ τ).
  Proof.
    constructor.
    - intros; unfold occurs_check, OccursCheckTerm, subst, SubstTerm.
      induction t; cbn.
      + unfold sub_shift. rewrite env.lookup_tabulate.
        cbv [occurs_check_term base.mbind option.option_bind].
        now rewrite ctx.occurs_check_shift_var.
      + solve.
      + solve.
      + solve.
      + solve.
      + solve.
      + solve.
      + solve.
      + solve.
      + solve.
        induction es; destruct X; cbn.
        * reflexivity.
        * now rewrite IHes, e0.
      (* + solve. *)
    - unfold occurs_check, OccursCheckTerm, subst, SubstTerm.
      intros ? ? ? t t' H1.
      induction t; cbn in H1.
      + pose proof (ctx.occurs_check_var_spec xIn ςInΣ) as H2.
        destruct (ctx.occurs_check_var xIn ςInΣ); apply noConfusion_inv in H1;
          cbn in H1; try contradiction; subst; cbn.
        destruct H2 as [H2 H3]. subst. unfold sub_shift.
        now rewrite env.lookup_tabulate.
      + solve.
      + solve. f_equal; auto.
      + solve. f_equal; auto.
      + solve. f_equal; auto.
      + solve. f_equal; auto.
      + solve. f_equal; auto.
      + solve. f_equal. auto.
      + solve. f_equal. auto.
      + apply option_map_eq_some' in H1 as [ts [H ?]]. subst. cbn. f_equal.
        change (es = subst ts (sub_shift xIn)).
        induction es; destruct X; cbn.
        * destruct (env.nilView ts). reflexivity.
        * destruct (env.snocView ts).
          change (es ► (b ↦ db) = subst E (sub_shift xIn) ► (b ↦ subst v (sub_shift xIn))).
          cbn in H.
          apply option.bind_Some in H.
          destruct H as [E' [HE H]].
          apply option.bind_Some in H.
          destruct H as [t' [? Heq]].
          unfold base.mret in Heq.
          apply noConfusion_inv in Heq.
          cbn in Heq.
          apply env.inversion_eq_snoc in Heq.
          destruct Heq; subst.
          f_equal.
          apply IHes; auto.
          apply e0; auto.
  Qed.

  Global Instance OccursCheckLawsList {T : LCtx -> Type} `{OccursCheckLaws T} :
    OccursCheckLaws (fun Σ => list (T Σ)).
  Proof.
    constructor.
    - intros. induction t; cbn.
      + reflexivity.
      + cbv [base.mbind option.option_bind].
        now rewrite occurs_check_shift, IHt.
    - intros ? ? ? t. induction t; cbn; intros t' Heq.
      + solve.
      + solve. apply occurs_check_sound in H2.
        f_equal; auto.
  Qed.

  Global Instance OccursCheckLawsEnv {I : Set} {T : LCtx -> I -> Set}
         {_ : forall i : I, Subst (fun Σ => T Σ i)}
         {_ : forall i : I, OccursCheck (fun Σ => T Σ i)}
         {_ : forall i : I, OccursCheckLaws (fun Σ => T Σ i)}
         {Γ : Ctx I} :
    OccursCheckLaws (fun Σ => Env (T Σ) Γ).
  Proof.
    constructor.
    - intros. induction t.
      + reflexivity.
      + unfold occurs_check, OccursCheckEnv, subst, SubstEnv in IHt.
        cbn. cbv [base.mbind option.option_ret option.option_bind] in *.
        now rewrite IHt, occurs_check_shift.
    - intros ? ? ? E. induction E; cbn; intros E' Heq.
      + solve. reflexivity.
      + solve. apply (occurs_check_sound (T := fun Σ => T Σ _)) in H2.
        f_equal.
        * now apply IHE.
        * auto.
  Qed.

  Global Instance OccursCheckLawsSub {Σ} : OccursCheckLaws (Sub Σ) :=
    OccursCheckLawsEnv.

  Global Instance OccursCheckPair {AT BT} `{OccursCheck AT, OccursCheck BT} :
    OccursCheck (Pair AT BT) :=
    fun _ _ xIn '(a,b) =>
      match occurs_check xIn a, occurs_check xIn b with
      | Some a' , Some b' => Some (a', b')
      | _       , _       => None
      end.

  Global Instance OccursCheckLawsPair {AT BT} `{OccursCheckLaws AT, OccursCheckLaws BT} :
    OccursCheckLaws (Pair AT BT).
  Proof.
    constructor.
    - intros. destruct t as [a b]; cbn.
      now rewrite ?occurs_check_shift.
    - intros ? ? ? [a b] [a' b']; cbn.
      destruct (occurs_check xIn a) eqn:Heq1; intros; try discriminate.
      destruct (occurs_check xIn b) eqn:Heq2; intros; try discriminate.
      apply occurs_check_sound in Heq1.
      apply occurs_check_sound in Heq2.
      congruence.
  Qed.

  Global Instance OccursCheckOption {AT} `{OccursCheck AT} :
    OccursCheck (Option AT) :=
    fun _ _ xIn ma =>
      match ma with
      | Some a => option_map Some (occurs_check xIn a)
      | None   => Some None
      end.

  Global Instance OccursCheckLawsOption {AT} `{OccursCheckLaws AT} :
    OccursCheckLaws (Option AT).
  Proof.
    constructor.
    { intros. destruct t as [a|]; cbn.
      - now rewrite ?occurs_check_shift.
      - reflexivity.
    }
    { intros ? ? ? [a|] mt' Heq; cbn.
      - apply option_map_eq_some' in Heq. destruct Heq as [t' [Heq <-]].
        apply occurs_check_sound in Heq. subst. reflexivity.
      - apply noConfusion_inv in Heq. cbn in Heq. subst. reflexivity.
    }
  Qed.

  Global Instance OccursCheckUnit : OccursCheck Unit :=
    fun _ _ _ _ => Some tt.
  Global Instance OccursCheckLawsUnit : OccursCheckLaws Unit.
  Proof.
    constructor; cbn.
    - destruct t; reflexivity.
    - destruct t, t'; reflexivity.
  Qed.

End OccursCheckOn.
