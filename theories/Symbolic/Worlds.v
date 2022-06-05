(******************************************************************************)
(* Copyright (c) 2020 Dominique Devriese, Georgy Lukyanov,                    *)
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

From Katamaran Require Import
     Prelude
     Notations
     Syntax.Formulas
     Syntax.Predicates
     Base.

Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.
Local Obligation Tactic := idtac.

Module Type WorldsOn
  (Import B : Base)
  (Import P : PredicateKit B)
  (Import F : FormulasOn B P).

  Section Worlds.

    (* A World consists of a logic variable context [wctx]
       and a path constraint [wco] with variables in [wctx]. *)
    Record World : Type :=
      MkWorld
        { wctx :> LCtx;
          wco  : PathCondition wctx;
        }.
    Global Arguments MkWorld _ _%list_scope : clear implicits.

    (* The empty world without logic variables and constraints. *)
    Definition wnil : World := @MkWorld ctx.nil nil.

    (* This adds one new logic variable binding [b] to the world, i.e. after
       "allocating" it in a quantifier in the proposition. *)
    Definition wsnoc (w : World) (b : 𝑺 ∷ Ty) : World :=
      @MkWorld (wctx w ▻ b) (subst (wco w) sub_wk1).
    (* Add [Δ] many logic variables to the world [w]. *)
    Definition wcat (w : World) (Δ : LCtx) : World :=
      @MkWorld (wctx w ▻▻ Δ) (subst (wco w) (sub_cat_left Δ)).

    (* Adds a new assume or asserted formula [f] to the world [w]. *)
    Definition wformula (w : World) (f : Formula w) : World :=
      @MkWorld (wctx w) (cons f (wco w)).
    (* Add all the formulas [fmls] to the world [w]. *)
    Definition wformulas (w : World) (fmls : List Formula w) : World :=
      @MkWorld (wctx w) (app fmls (wco w)).

    (* Change the world after a unifying variable [x] with term [t]. *)
    Definition wsubst (w : World) x {σ} {xIn : x∷σ ∈ w} (t : Term (w - x∷σ) σ) : World :=
      {| wctx := wctx w - x∷σ; wco := subst (wco w) (sub_single xIn t) |}.
    Global Arguments wsubst w x {σ xIn} t.

    (* Define a shorthand [TYPE] for the category of world indexed types. *)
    Definition TYPE : Type := World -> Type.
    Bind Scope modal_scope with TYPE.
    Definition Valid (A : TYPE) : Type :=
      forall w, A w.
    Definition Impl (A B : TYPE) : TYPE :=
      fun w => A w -> B w.
    Definition Forall {I : Type} (A : I -> TYPE) : TYPE :=
      fun w => forall i : I, A i w.
    (* Definition Cat (A : TYPE) (Δ : LCtx) : TYPE := *)
    (*   fun w => A (wcat w Δ). *)

  End Worlds.

  (* A definition of triangular substitutions presented as a proof relevant
     relation between worlds. This is a sub-relation of the accessibility
     relation that we define below. Normally it would be sufficient to define
     triangular substitutions on logic contexts, however that entails that we
     have to calculate the "result" world of a triangular substitution. The
     definition here seems more convenient. However, it also makes some
     operations more cumbersome like unification which now has to apply
     substitutions to path constraints as well. We might want to revisit this. *)
  Section TriangularSubstitutions.

    Ltac rew := rewrite ?subst_sub_comp, ?subst_shift_single, ?subst_sub_id, ?sub_comp_id_right,
        ?sub_comp_id_left, ?inst_sub_id, ?inst_sub_id.

    Inductive Tri (w : World) : World -> Type :=
    | tri_id        : Tri w w
    | tri_cons {w' x σ}
        (xIn : x∷σ ∈ w) (t : Term (wctx w - x∷σ) σ)
        (ν : Tri (wsubst w x t) w') : Tri w w'.
    Global Arguments tri_id {_}.
    Global Arguments tri_cons {_ _} x {_ _} t ν.

    Fixpoint tri_comp {w1 w2 w3} (ν12 : Tri w1 w2) : Tri w2 w3 -> Tri w1 w3 :=
      match ν12 with
      | tri_id           => fun ν => ν
      | tri_cons x t ν12 => fun ν => tri_cons x t (tri_comp ν12 ν)
      end.

    Fixpoint sub_triangular {w1 w2} (ζ : Tri w1 w2) : Sub w1 w2 :=
      match ζ with
      | tri_id         => sub_id _
      | tri_cons x t ζ => subst (sub_single _ t) (sub_triangular ζ)
      end.

    Lemma sub_triangular_comp {w0 w1 w2} (ν01 : Tri w0 w1) (ν12 : Tri w1 w2) :
      sub_triangular (tri_comp ν01 ν12) =
      subst (sub_triangular ν01) (sub_triangular ν12).
    Proof.
      induction ν01; cbn [sub_triangular tri_comp].
      - now rew.
      - now rewrite sub_comp_assoc, IHν01.
    Qed.

    Fixpoint sub_triangular_inv {w1 w2} (ζ : Tri w1 w2) : Sub w2 w1 :=
      match ζ with
      | tri_id         => sub_id _
      | tri_cons x t ζ => subst (sub_triangular_inv ζ) (sub_shift _)
      end.

    Lemma sub_triangular_inv_comp {w0 w1 w2} (ν01 : Tri w0 w1) (ν12 : Tri w1 w2) :
      sub_triangular_inv (tri_comp ν01 ν12) =
      subst (sub_triangular_inv ν12) (sub_triangular_inv ν01).
    Proof.
      induction ν01; cbn.
      - now rew.
      - now rewrite IHν01, sub_comp_assoc.
    Qed.

    Fixpoint inst_triangular {w0 w1} (ζ : Tri w0 w1) (ι : Valuation w0) : Prop :=
      match ζ with
      | tri_id => True
      | @tri_cons _ Σ' x σ xIn t ζ0 =>
        let ι' := env.remove (x∷σ) ι xIn in
        env.lookup ι xIn = inst t ι' /\ inst_triangular ζ0 ι'
      end.

    Lemma inst_triangular_left_inverse {w1 w2 : World} (ι2 : Valuation w2) (ν : Tri w1 w2) :
      inst (sub_triangular_inv ν) (inst (sub_triangular ν) ι2) = ι2.
    Proof. rewrite <- inst_subst. induction ν; cbn - [subst]; now rew. Qed.

    Lemma inst_triangular_right_inverse {w1 w2 : World} (ι1 : Valuation w1) (ζ : Tri w1 w2) :
      inst_triangular ζ ι1 ->
      inst (sub_triangular ζ) (inst (sub_triangular_inv ζ) ι1) = ι1.
    Proof.
      intros Hζ. induction ζ; cbn - [subst].
      - now rew.
      - cbn in Hζ. rewrite <- inst_sub_shift in Hζ. destruct Hζ as [? Hζ].
        rewrite ?inst_subst, IHζ, inst_sub_single_shift; auto.
    Qed.

    (* Forward entailment *)
    Lemma entails_triangular_inv {w0 w1} (ν : Tri w0 w1) (ι0 : Valuation w0) :
      inst_triangular ν ι0 ->
      instpc (wco w0) ι0 ->
      instpc (wco w1) (inst (sub_triangular_inv ν) ι0).
    Proof.
      induction ν; cbn.
      - cbn. rewrite inst_sub_id. auto.
      - rewrite <- inst_sub_shift, inst_subst. intros [Heqx Heq'] Hpc0.
        apply IHν; cbn; auto.
        rewrite inst_subst, inst_sub_single_shift; auto.
    Qed.

    Lemma inst_triangular_valid {w0 w1} (ζ01 : Tri w0 w1) (ι1 : Valuation w1) :
      inst_triangular ζ01 (inst (sub_triangular ζ01) ι1).
    Proof.
      induction ζ01; cbn; auto.
      rewrite <- inst_lookup, lookup_sub_comp. rewrite lookup_sub_single_eq.
      rewrite <- inst_sub_shift. rewrite <- ?inst_subst.
      rewrite subst_sub_comp.
      rewrite subst_shift_single.
      split; auto.
      rewrite <- ?sub_comp_assoc.
      rewrite sub_comp_shift_single.
      rewrite sub_comp_id_left.
      auto.
    Qed.

    Lemma inst_tri_comp {w0 w1 w2} (ν01 : Tri w0 w1) (ν12 : Tri w1 w2) (ι0 : Valuation w0) :
      inst_triangular (tri_comp ν01 ν12) ι0 <->
      inst_triangular ν01 ι0 /\ inst_triangular ν12 (inst (sub_triangular_inv ν01) ι0).
    Proof.
      induction ν01; cbn.
      - rewrite inst_sub_id; intuition.
      - rewrite ?inst_subst, ?inst_sub_shift. split.
        + intros (Heq & Hwp). apply IHν01 in Hwp. now destruct Hwp.
        + intros ([Heq Hν01] & Hwp). split; auto. apply IHν01; auto.
    Qed.

  End TriangularSubstitutions.

  Section Accessibility.

    Import Entailment.

    Inductive Acc (w1 : World) : World -> Type :=
    (* We special case the reflexivity case of accessibility, because there are
       many computations that don't change the world and we would therefore
       often run the identity substitution over the entire state. *)
    | acc_refl : Acc w1 w1
    | acc_sub {w2 : World} (ζ : Sub w1 w2) (ent : wco w2 ⊢ subst (wco w1) ζ) : Acc w1 w2.
    Global Arguments acc_refl {w} : rename.
    Global Arguments acc_sub {w1 w2} ζ ent.
    Notation "w1 ⊒ w2" := (Acc w1 w2) (at level 80).

    Equations(noeqns) acc_trans {w0 w1 w2} (ω01 : w0 ⊒ w1) (ω12 : w1 ⊒ w2) : w0 ⊒ w2 :=
    | acc_refl         | ω12              := ω12;
    | ω01              | acc_refl         := ω01;
    | acc_sub ζ01 ent1 | acc_sub ζ12 ent2 := acc_sub (subst (T := Sub _) ζ01 ζ12) _.
    Next Obligation.
      intros w0 w1 w2 ζ01 Hpc01 ζ12 Hpc12. transitivity (subst (wco w1) ζ12); auto.
      rewrite subst_sub_comp. now apply proper_subst_entails.
    Qed.
    Global Arguments acc_trans {w0 w1 w2} !ω01 !ω12.

    Definition sub_acc {w1 w2} (ω : w1 ⊒ w2) : Sub (wctx w1) (wctx w2) :=
      match ω with
      | acc_refl    => sub_id _
      | acc_sub ζ _ => ζ
      end.

    Lemma sub_acc_trans {w0 w1 w2} (ω01 : w0 ⊒ w1) (ω12 : w1 ⊒ w2) :
      sub_acc (acc_trans ω01 ω12) = subst (sub_acc ω01) (sub_acc ω12).
    Proof.
      destruct ω01, ω12; cbn - [subst];
        now rewrite ?sub_comp_id_left, ?sub_comp_id_right.
    Qed.

    Definition Box (A : TYPE) : TYPE :=
      fun w0 => forall w1, w0 ⊒ w1 -> A w1.

    Lemma ent_acc_sub {w1 w2} (ω : w1 ⊒ w2) :
      wco w2 ⊢ subst (wco w1) (sub_acc ω).
    Proof. destruct ω; cbn; now rewrite ?subst_sub_id. Qed.

    Definition acc_snoc_right {w} {b : 𝑺 ∷ Ty} : w ⊒ wsnoc w b :=
      @acc_sub w (wsnoc w b) sub_wk1 (entails_refl (subst (wco w) sub_wk1)).

    Program Definition acc_snoc_left {w1 w2} (ω12 : w1 ⊒ w2) (b : 𝑺 ∷ Ty) (t : Term w2 (type b)) :
      wsnoc w1 b ⊒ w2 := acc_sub (sub_snoc (sub_acc ω12) b t) _.
    Next Obligation.
    Proof.
      intros *. unfold wsnoc. cbn [wctx wco].
      rewrite subst_wk1_snoc.
      apply ent_acc_sub.
    Qed.

    Definition acc_snoc_left' {w : World} b (t : Term w (type b)) :
      wsnoc w b ⊒ w := acc_snoc_left acc_refl b t.

    Program Definition acc_cat_left {w1 w2} (ω12 : w1 ⊒ w2) {Δ : LCtx} (ζ : Sub Δ w2) :
      wcat w1 Δ ⊒ w2 := acc_sub (sub_acc ω12 ►► ζ) _.
    Next Obligation.
    Proof.
      intros *. unfold wcat. cbn [wctx wco].
      rewrite <- subst_sub_comp.
      rewrite sub_comp_cat_left.
      apply ent_acc_sub.
    Qed.

    Program Definition acc_formula_right {w : World} (f : Formula w) : w ⊒ wformula w f :=
      @acc_sub w (wformula w f) (sub_id (wctx w)) _.
    Next Obligation.
    Proof.
      intros * ι. unfold wformula. cbn.
      rewrite subst_sub_id.
      now intros [].
    Qed.

    Program Definition acc_formulas_right (w : World) (fmls : List Formula w) :
      w ⊒ wformulas w fmls :=
      @acc_sub w (wformulas w fmls) (sub_id (wctx w)) _.
    Next Obligation.
    Proof.
      intros w fmls ι. cbn.
      rewrite subst_sub_id.
      rewrite inst_pathcondition_app.
      now intros [].
    Qed.

    Definition acc_subst_right {w : World} x {σ} {xIn : x∷σ ∈ w} (t : Term (w - x∷σ) σ) :
      w ⊒ wsubst w x t :=
      let ζ  := sub_single xIn t in
      let w' := {| wctx := w - x∷σ; wco := subst (wco w) ζ |}  in
      @acc_sub w w' ζ (entails_refl (wco w')).
    Arguments acc_subst_right {w} x {σ xIn} t.

    Fixpoint acc_triangular {w1 w2} (ν : Tri w1 w2) : w1 ⊒ w2 :=
      match ν with
      | tri_id         => acc_refl
      | tri_cons x t ν => acc_trans (acc_subst_right x t) (acc_triangular ν)
      end.

    Lemma sub_acc_triangular {w1 w2} (ζ : Tri w1 w2) :
      sub_acc (acc_triangular ζ) = sub_triangular ζ.
    Proof.
      induction ζ; cbn.
      - reflexivity.
      - now rewrite sub_acc_trans, IHζ.
    Qed.

    (* Lemma acc_triangular_app {w0 w1 w2} (ν01 : Tri w0 w1) (ν12 : Tri w1 w2) : *)
    (*   wsub (acc_triangular (tri_comp ν01 ν12)) = *)
    (*   subst (sub_acc (acc_triangular ν01)) (sub_acc (acc_triangular ν12)). *)
    (* Proof. *)
    (*   induction ν01; cbn - [SubstEnv]. *)
    (*   - now rewrite sub_comp_id_left. *)
    (*   - rewrite <- subst_sub_comp. now f_equal. *)
    (* Qed. *)

  End Accessibility.

  Instance preorder_acc : CRelationClasses.PreOrder Acc :=
    CRelationClasses.Build_PreOrder Acc (@acc_refl) (@acc_trans).

  Declare Scope modal.
  Delimit Scope modal with modal.

  Section S4.

    Notation "⊢ A" := (Valid A%modal) (at level 100).
    Notation "A -> B" := (Impl A%modal B%modal) : modal.
    Notation "□ A" := (Box A%modal) (at level 9, format "□ A", right associativity) : modal.

    Definition K {A B} :
      ⊢ □(A -> B) -> (□A -> □B) :=
      fun w0 f a w1 ω01 =>
        f w1 ω01 (a w1 ω01).
    Definition T {A} :
      ⊢ □A -> A :=
      fun w0 a => a w0 acc_refl.
    Definition four {A} :
      ⊢ □A -> □□A :=
      fun w0 a w1 ω01 w2 ω12 =>
        a w2 (acc_trans ω01 ω12).
    Global Arguments four : simpl never.

    (* faster version of (four _ sub_wk1) *)
    (* Definition four_wk1 {A} : *)
    (*   ⊢ □A -> ∀ b, Snoc (□A) b := *)
    (*   fun w0 a b w1 ω01 => a w1 (env_tail ω01). *)
    (* Arguments four_wk1 {A Σ0} pc0 a b [Σ1] ζ01 : rename. *)

    Definition valid_box {A} :
      (⊢ A) -> (⊢ □A) :=
      fun a w0 w1 ω01 => a w1.
    Global Arguments valid_box {A} a {w} [w1].

    Definition fmap_box {A B} (f : ⊢ A -> B) : ⊢ □A -> □B :=
      fun w0 a w1 ω01 => f w1 (a w1 ω01).
    Definition extend_box {A B} (f : ⊢ □A -> B) : ⊢ □A -> □B :=
      fun w0 a w1 ω01 => f w1 (four a ω01).
    Definition comp {A B C} :
      ⊢ (B -> C) -> (A -> B) -> (A -> C) :=
      fun w0 => Basics.compose.

  End S4.

  Module ModalNotations.

    Notation "⊢ A" := (Valid A%modal) (at level 100).
    Notation "A -> B" := (Impl A%modal B%modal) : modal.
    Notation "□ A" := (Box A%modal) (at level 9, format "□ A", right associativity) : modal.
    Notation "⌜ A ⌝" := (fun (w : World) => Const A%type w) (at level 0, format "⌜ A ⌝") : modal.
    Notation "'∀' x .. y , P " :=
      (Forall (fun x => .. (Forall (fun y => P%modal)) ..))
        (at level 99, x binder, y binder, right associativity)
      : modal.
    Notation "w1 ⊒ w2" := (Acc w1 w2) (at level 80).
    Notation "f <$> a" := (fmap_box f a) (at level 40, left associativity).
    Notation "f <*> a" := (K f a) (at level 40, left associativity).
    Notation "ω1 ∘ ω2" := (acc_trans ω1 ω2) (at level 40, left associativity).
  End ModalNotations.
  Open Scope modal.

  Section Persistence.

    Import Entailment.
    Import ModalNotations.

    Class Persistent (A : TYPE) (* `{LogicalRelation.LR A} *) : Type :=
      persist     : ⊢ A -> □A.
        (* persist_lr  : forall w0 (a : A w0) w1 (ω01 : w0 ⊒ w1), *)
        (*     LogicalRelation.lr ω01 a (persist a ω01); *)
        (* persist_dcl : *)
        (*   forall w (a : A w), *)
        (*     LogicalRelation.dcl (persist a) *)
    (* Global Arguments Persistent A {_}. *)

    Global Instance persistent_box {A} : Persistent □A := four.

    Global Instance persistent_subst {A} `{Subst A} : Persistent A :=
      fun w0 x w1 ω01 =>
        match ω01 with
        | acc_refl => x
        | @acc_sub _ w2 ζ _ => subst x ζ
        end.

    Lemma persist_subst {A} `{SubstLaws A} {w1 w2} {ω : w1 ⊒ w2} {a : A w1} :
      persist a ω = subst a (sub_acc ω).
    Proof. destruct ω; cbn; now rewrite ?subst_sub_id. Qed.

    Lemma persist_trans {A} `{SubstLaws A} {w0 w1 w2} {ω1 : w0 ⊒ w1} {ω2 : w1 ⊒ w2} {a : A w0} :
      persist a (acc_trans ω1 ω2) = persist (persist a ω1) ω2.
    Proof. now rewrite ?persist_subst, sub_acc_trans, subst_sub_comp. Qed.

    Lemma inst_persist {AT A} `{InstSubst AT A} `{@SubstLaws AT _} {w1 w2} (ω : w1 ⊒ w2) :
      forall (ι : Valuation w2) (t : AT w1),
        inst (persist t ω) ι = inst t (inst (sub_acc ω) ι).
    Proof. intros. now rewrite persist_subst, inst_subst. Qed.

    Lemma ent_acc {w1 w2} (ω : w1 ⊒ w2) :
      wco w2 ⊢ persist (wco w1) ω.
    Proof. destruct ω; cbn; now rewrite ?subst_sub_id. Qed.

    (* Program Definition acc_snoc {w0 w1} (ω01 : w0 ⊒ w1) (b : 𝑺 * Ty) : *)
    (*   wsnoc w0 b ⊒ wsnoc w1 b := *)
    (*   match ω01 in _ ⊒ w return wsnoc w0 b ⊒ wsnoc w b with *)
    (*   | acc_refl            => acc_refl *)
    (*   | @acc_sub _ w2 ζ ent => @acc_sub _ (wsnoc _ b) (sub_up1 ζ) _ *)
    (*   end. *)
    (* Next Obligation. *)
    (* Proof. *)
    (*   intros. unfold wsnoc; cbn. *)
    (*   rewrite <- subst_sub_comp. *)
    (*   rewrite sub_comp_wk1_comm. *)
    (*   rewrite subst_sub_comp. *)
    (*   now apply proper_subst_entails. *)
    (* Qed. *)

    (* Program Definition acc_formula {w0 w1} (ω01 : w0 ⊒ w1) (fml : Formula w0) : *)
    (*   wformula w0 fml ⊒ wformula w1 (persist fml ω01) := *)
    (*   @acc_sub (MkWorld (cons fml (wco w0))) (MkWorld (cons (persist fml ω01) (wco w1))) (sub_acc ω01) _. *)
    (* Next Obligation. *)
    (*   intros ? ? ? ? ι. *)
    (*   unfold wformula in *. *)
    (*   cbn [wco wctx] in *. cbn. *)
    (*   destruct ω01; cbn. *)
    (*   - now rewrite ?subst_sub_id. *)
    (*   - rewrite ?inst_pathcondition_cons. *)
    (*     intuition. *)
    (* Qed. *)

  End Persistence.

  Notation WList A := (fun w : World => list (A w)).
  Notation WTerm σ := (fun w : World => Term (wctx w) σ).
  Notation STerm σ := (fun Σ => Term Σ σ).

  (* A Notation for Terms because this seems to always gets messed up because of
     the [WTerm] / [STerm] Schizophrenia, *)
  Notation persist__term t :=
    (@persist (WTerm _) (@persistent_subst (STerm _) (@SubstTerm _)) _ t).

  (* TODO: Move *)
  Definition Solver : Type :=
    forall w0 (fmls0 : WList Formula w0),
      option { w1 & Tri w0 w1 * List Formula w1 }%type.

  Definition SolverSpec (s : Solver) : Prop :=
    forall w0 (fmls0 : WList Formula w0),
      option.spec
        (fun '(existT w1 (ζ, fmls1)) =>
           forall ι0,
             instpc (wco w0) ι0 ->
             (instpc fmls0 ι0 -> inst_triangular ζ ι0) /\
               (forall ι1,
                   instpc (wco w1) ι1 ->
                   ι0 = inst (sub_triangular ζ) ι1 ->
                   instpc fmls0 ι0 <-> inst fmls1 ι1))
        (forall ι, instpc (wco w0) ι -> ~ instpc fmls0 ι)
        (s w0 fmls0).

  Definition solver_null : Solver :=
    fun w fmls => Some (existT w (tri_id , fmls)).

  Lemma solver_null_spec : SolverSpec solver_null.
  Proof.
    intros w fmls. constructor. cbn. intros ι Hpc. split. auto.
    intros ι' Hpc' ->. now rewrite inst_sub_id.
  Qed.

  Definition SolverUserOnly : Type :=
    forall Σ (p : 𝑷), Env (Term Σ) (𝑷_Ty p) -> option (List Formula Σ).

  Definition SolverUserOnlySpec (s : SolverUserOnly) : Prop :=
    forall Σ (p : 𝑷) (ts : Env (Term Σ) (𝑷_Ty p)),
      option.spec
        (fun r : List Formula Σ =>
           forall ι : Valuation Σ,
             inst (formula_user p ts) ι <-> instpc r ι)
        (forall ι : Valuation Σ, ~ inst (formula_user p ts) ι)
        (s Σ p ts).

  Section SimplifyAll.
    Import option.notations.
    Context {Σ} (g : Formula Σ -> List Formula Σ -> option (List Formula Σ)).

    Definition simplify_all {Σ} (g : Formula Σ -> List Formula Σ -> option (List Formula Σ)) :=
      fix simplify_all (fmls k : List Formula Σ) {struct fmls} : option (List Formula Σ) :=
        match fmls with
        | nil => Some k
        | cons fml0 fmls =>
          k' <- simplify_all fmls k ;;
          g fml0 k'
        end.

    Context (g_spec : forall f k,
                option.spec
                  (fun r : List Formula Σ =>
                     forall ι : Valuation Σ,
                       instpc (cons f k)%list ι <-> instpc r ι)
                  (forall ι : Valuation Σ, ~ inst f ι)
                  (g f k)).

    Lemma simplify_all_spec (fmls k : List Formula Σ) :
      option.spec
        (fun r : List Formula Σ =>
           forall ι : Valuation Σ,
             instpc (fmls ++ k)%list ι <-> instpc r ι)
        (forall ι : Valuation Σ, ~ instpc fmls ι)
        (simplify_all g fmls k).
    Proof.
      induction fmls; cbn; [constructor; reflexivity|].
      apply option.spec_bind. revert IHfmls.
      apply option.spec_monotonic.
      - intros tmp Htmp. specialize (g_spec a tmp). revert g_spec.
        apply option.spec_monotonic.
        + intros res Hres ι. rewrite (Htmp ι). apply (Hres ι).
        + intros Hna ι [Ha ?]. now apply (Hna ι).
      - intros Hnfmls ι [Ha Hfmls]. now apply (Hnfmls ι).
    Qed.

  End SimplifyAll.

  Section WithUserOnlySolver.

    Context (user : SolverUserOnly).

    Definition solveruseronly_simplify_formula {Σ} (f : Formula Σ) (k : List Formula Σ) : option (List Formula Σ) :=
      match f with
      | formula_user p ts => option.map (fun r => app r k) (user ts)
      | f                 => Some (cons f k)
      end.

    Definition solveruseronly_to_solver : Solver :=
      fun w fmls =>
        option_map
          (fun l => existT w (tri_id, l))
          (simplify_all solveruseronly_simplify_formula fmls nil).

    Context (user_spec : SolverUserOnlySpec user).

    Lemma solveruseronly_simplify_formula_spec {Σ} (f : Formula Σ) (k : List Formula Σ) :
      option.spec
        (fun r : List Formula Σ =>
           forall ι : Valuation Σ,
             instpc (cons f k)%list ι <-> instpc r ι)
        (forall ι : Valuation Σ, ~ inst f ι)
        (solveruseronly_simplify_formula f k).
    Proof.
      destruct f; try (constructor; reflexivity).
      cbn [solveruseronly_simplify_formula]. apply option.spec_map.
      generalize (user_spec ts).
      apply option.spec_monotonic.
      - intros ? H ?. rewrite inst_pathcondition_app.
        apply and_iff_compat_r'. intros ?. apply H.
      - auto.
    Qed.

    Lemma solveruseronly_to_solver_spec : SolverSpec solveruseronly_to_solver.
    Proof.
      intros w0 fmls. unfold solveruseronly_to_solver.
      apply option.spec_map.
      generalize (simplify_all_spec solveruseronly_simplify_formula solveruseronly_simplify_formula_spec fmls nil).
      apply option.spec_monotonic.
      - intros r H ι Hpc. split; [constructor|].
        specialize (H ι). rewrite inst_pathcondition_app in H.
        cbn in H. rewrite rightid_and_true in H.
        intros ι' Hpc'. cbn. rewrite inst_sub_id. intros. now subst.
      - intros Hnf ι Hpc. apply Hnf.
    Qed.

  End WithUserOnlySolver.

End WorldsOn.
