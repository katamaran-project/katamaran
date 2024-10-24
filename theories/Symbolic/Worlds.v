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
     Syntax.Chunks
     Syntax.Formulas
     Syntax.Predicates
     Base.
From stdpp Require Import base.

Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.
Local Obligation Tactic := idtac.

Declare Scope rel_scope.
Delimit Scope rel_scope with R.

Declare Scope pred_scope.
Delimit Scope pred_scope with P.

Module Type WorldsOn
  (Import B : Base)
  (Import P : PredicateKit B)
  (Import F : FormulasOn B P)
  (Import C : ChunksOn B P F).

  Section Worlds.

    (* A World consists of a logic variable context [wctx]
       and a path constraint [wco] with variables in [wctx]. *)
    Record World : Type :=
      MkWorld
        { wctx :> LCtx;
          wco  : PathCondition wctx;
        }.
    #[global] Arguments MkWorld : clear implicits.

    (* The empty world without logic variables and constraints. *)
    Definition wnil : World := @MkWorld ctx.nil ctx.nil.
    Definition wlctx : LCtx -> World := fun Σ => MkWorld Σ [ctx].

    (* This adds one new logic variable binding [b] to the world, i.e. after
       "allocating" it in a quantifier in the proposition. *)
    Definition wsnoc (w : World) (b : LVar ∷ Ty) : World :=
      @MkWorld (wctx w ▻ b) (subst (wco w) sub_wk1).
    Definition term_var_zero {Σ} {b} : Term (Σ ▻ b) (type b) :=
      @term_var (Σ ▻ b) (name b) (type b) ctx.in_zero.
    Definition wlet (w : World) (b : LVar ∷ Ty) (v : Val (type b)): World :=
      @MkWorld  (wctx w ▻ b) (subst (wco w) sub_wk1 ▻ 
                                formula_relop bop.eq (term_var_zero) (term_val _ v)).

    (* Add [Δ] many logic variables to the world [w]. *)
    Definition wcat (w : World) (Δ : LCtx) : World :=
      @MkWorld (wctx w ▻▻ Δ) (subst (wco w) (sub_cat_left Δ)).

    (* Adds a new assume or asserted formula [f] to the world [w]. *)
    Definition wformula (w : World) (f : Formula w) : World :=
      @MkWorld (wctx w) (ctx.snoc (wco w) f).
    (* Add all the formulas [C] to the world [w]. *)
    Definition wpathcondition (w : World) (C : PathCondition w) : World :=
      @MkWorld (wctx w) (ctx.cat (wco w) C).

    (* Change the world after a unifying variable [x] with term [t]. *)
    Definition wsubst (w : World) x {σ} {xIn : (x∷σ ∈ w)%katamaran} (t : Term (w - x∷σ) σ) : World :=
      {| wctx := (wctx w - x∷σ); wco := subst (wco w) (sub_single xIn t) |}.
    Global Arguments wsubst w x {σ xIn} t.

    Definition wmatch (w : World) {σ} (s : Term w σ) (p : @Pattern LVar σ)
      (pc : PatternCase p) : World :=
      let Δ   : LCtx           := PatternCaseCtx pc in
      let w1  : World          := wcat w Δ in
      let ts  : Sub Δ (w ▻▻ Δ) := sub_cat_right Δ in
      let F1  : Formula w1     := formula_relop bop.eq
                                    (subst s (sub_cat_left Δ))
                                    (pattern_match_term_reverse _ pc ts) in
      wformula (wcat w Δ) F1.

    Definition wmatchvar_patternvars {Σ : LCtx} {x σ} {xIn : (x∷σ ∈ Σ)%katamaran}
      {p : @Pattern LVar σ} (pc : PatternCase p) : Sub (PatternCaseCtx pc) ((Σ ▻▻ PatternCaseCtx pc) - x∷σ) :=
      let Δ   : LCtx           := PatternCaseCtx pc in
      let Σ1  : LCtx              := Σ ▻▻ Δ in
      let eq : ((Σ ▻▻ Δ) - x∷σ) = (Σ - x∷σ ▻▻ Δ) := ctx.remove_in_cat_left xIn in
      let ts  : Sub Δ (Σ - x∷σ ▻▻ Δ) := sub_cat_right Δ in
      eq_rect (Σ - x∷σ ▻▻ Δ) (fun Σ => Sub Δ Σ) ts ((Σ ▻▻ Δ) - x∷σ) (eq_sym eq).

    Definition wmatchvar (w : World) {x σ} (xIn : (x∷σ ∈ w)%katamaran) (p : @Pattern LVar σ)
      (pc : PatternCase p) : World :=
      let Δ   : LCtx           := PatternCaseCtx pc in
      let w1  : World          := wcat w Δ in
      let t'   : Term ((w ▻▻ Δ) - x∷σ) σ := pattern_match_term_reverse _ pc (wmatchvar_patternvars pc) in
      wsubst w1 x t'.

    (* Define a shorthand [TYPE] for the category of world indexed types. *)
    Definition TYPE : Type := World -> Type.
    Bind Scope modal_scope with TYPE.
    Definition Valid (A : TYPE) : Type :=
      forall w, A w.
    Definition Impl (A B : TYPE) : TYPE :=
      fun w => A w -> B w.
    Definition Forall {I : Type} (A : I -> TYPE) : TYPE :=
      fun w => forall i : I, A i w.

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
        (xIn : (x∷σ ∈ w)%katamaran) (t : Term (wctx w - x∷σ) σ)
        (ν : Tri (wsubst w x t) w') : Tri w w'.
    Global Arguments tri_id {_}.
    Global Arguments tri_cons {_ _} x {_ _} t ν.

    Fixpoint tri_comp {w1 w2 w3} (ν12 : Tri w1 w2) : Tri w2 w3 -> Tri w1 w3 :=
      match ν12 with
      | tri_id           => fun ν => ν
      | tri_cons x t ν12 => fun ν => tri_cons x t (tri_comp ν12 ν)
      end.

    Definition sub_wmatch_patctx {w : World} {σ} {s : Term w σ} {p : @Pattern LVar σ} (pc : PatternCase p) : Sub (PatternCaseCtx pc) (wmatch w s p pc) :=
      sub_cat_right (PatternCaseCtx pc).

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
      instprop (wco w0) ι0 ->
      instprop (wco w1) (inst (sub_triangular_inv ν) ι0).
    Proof.
      induction ν; cbn.
      - cbn. rewrite inst_sub_id. auto.
      - rewrite <- inst_sub_shift, inst_subst. intros [Heqx Heq'] Hpc0.
        apply IHν; cbn; auto.
        rewrite instprop_subst, inst_sub_single_shift; auto.
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

    Definition acc_wnil_init {w} : Acc wnil w :=
      @acc_sub wnil w [env] entails_nil.

    Definition acc_wlctx_valuation {Σ} : Valuation Σ -> Acc (wlctx Σ) wnil :=
      fun ι => @acc_sub (wlctx Σ) wnil (lift ι) entails_nil.

    Definition acc_snoc_right {w} {b : LVar ∷ Ty} : w ⊒ wsnoc w b :=
      @acc_sub w (wsnoc w b) sub_wk1 (entails_refl (subst (wco w) sub_wk1)).

    Definition acc_cat_right w (Δ : LCtx) : w ⊒ wcat w Δ :=
      @acc_sub w (wcat w Δ) (@sub_cat_left w Δ)
        (entails_refl (subst (wco w) (sub_cat_left Δ))).

    Program Definition acc_snoc_left {w1 w2} (ω12 : w1 ⊒ w2) (b : LVar ∷ Ty) (t : Term w2 (type b)) :
      wsnoc w1 b ⊒ w2 := acc_sub (sub_snoc (sub_acc ω12) b t) _.
    Next Obligation.
    Proof.
      intros *. unfold wsnoc. cbn [wctx wco].
      rewrite subst_wk1_snoc.
      apply ent_acc_sub.
    Qed.

    Definition acc_snoc_left' {w : World} b (t : Term w (type b)) :
      wsnoc w b ⊒ w := acc_snoc_left acc_refl b t.

    (* Lemma acc_snoc_left_right_iso {w : World} {b} {t : Term w (type b)}: *)
    (*   IsIsomorphism acc_snoc_right (acc_snoc_left' b t). *)
    (* Proof. *)
    (*   constructor. *)
    (*   - intros. simpl. *)
    (*     now rewrite inst_sub_snoc, inst_sub_id, inst_sub_wk1. *)
    (*   - intros. simpl. *)
    (*     rewrite inst_sub_snoc, inst_sub_id. *)
    (*     (* Not true. The world `wsnoc w b` lacks a path condition saying that the extra variable is equal to t. *) *)
    (* Admitted. *)

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

    Program Definition acc_pathcondition_right (w : World) (C : PathCondition w) :
      w ⊒ wpathcondition w C :=
      @acc_sub w (wpathcondition w C) (sub_id (wctx w)) _.
    Next Obligation.
    Proof. intros w C ι H%instprop_cat. now rewrite subst_sub_id. Qed.

    Definition acc_subst_right {w : World} x {σ} {xIn : (x∷σ ∈ w)%katamaran} (t : Term (w - x∷σ) σ) :
      w ⊒ wsubst w x t :=
      let ζ  := sub_single xIn t in
      let w' := {| wctx := w - x∷σ; wco := subst (wco w) ζ |}  in
      @acc_sub w w' ζ (entails_refl (wco w')).
    Arguments acc_subst_right {w} x {σ xIn} t.

    Definition acc_match_right {w : World} {σ} {s : Term w σ}
      {p : @Pattern LVar σ} (pc : PatternCase p) : w ⊒ wmatch w s p pc :=
      @acc_sub w (wmatch w s p pc) (sub_cat_left (PatternCaseCtx pc))
        (fun ι HCι => proj1 HCι).

    Definition sub_matchvar_right {w : World} {x σ} {xIn : (x∷σ ∈ w)%katamaran}
        {p : @Pattern LVar σ} (pc : PatternCase p) : Sub w (wmatchvar w xIn p pc) :=
        let Δ   : LCtx           := PatternCaseCtx pc in
        let w1  : World          := wcat w Δ in
        let t   : Term ((w ▻▻ Δ) - x∷σ) σ := pattern_match_term_reverse _ pc (wmatchvar_patternvars pc) in
        let wmv : World          := wsubst w1 x t in
        let sub₁ : Sub w (w ▻▻ Δ) := sub_cat_left Δ in
        let sub₂ : Sub (w ▻▻ Δ) ((w ▻▻ Δ) - x∷σ) := sub_single _ t in
        subst sub₁ sub₂.
    Arguments sub_matchvar_right {w} {x σ xIn p} pc : simpl never.

    Program Definition acc_matchvar_right {w : World} {x σ} {xIn : (x∷σ ∈ w)%katamaran}
      {p : @Pattern LVar σ} (pc : PatternCase p) : w ⊒ wmatchvar w xIn p pc :=
      let Δ   : LCtx           := PatternCaseCtx pc in
      let w1  : World          := wcat w Δ in
      let t   : Term ((w ▻▻ Δ) - x∷σ) σ := pattern_match_term_reverse _ pc (wmatchvar_patternvars pc) in
      let wmv : World          := wsubst w1 x t in
      let sub : Sub w wmv := sub_matchvar_right pc in
      @acc_sub w wmv sub _.
    Next Obligation.
      intros. cbn -[sub_single].
      now rewrite <-subst_sub_comp.
    Qed.
    Arguments acc_matchvar_right {w} {x σ xIn p} pc : simpl never.

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

    (* Lemma sub_triangular_left_inverse2 {w1 w2} (ζ : Tri w1 w2) : Inverse (sub_triangular_inv ζ)  (sub_triangular ζ). *)
    (* Proof. *)
    (*   intros ι Hpc. now rewrite inst_triangular_left_inverse. *)
    (* Qed. *)
  End Accessibility.

  #[export] Instance preorder_acc : CRelationClasses.PreOrder Acc :=
    CRelationClasses.Build_PreOrder Acc (@acc_refl) (@acc_trans).

  Section S4.

    Notation "⊢ A" := (Valid A%modal) (at level 20, A at level 200).
    Notation "A -> B" := (Impl A%modal B%modal) : modal_scope.
    Notation "□ A" := (Box A%modal) (at level 20, format "□ A", right associativity) : modal_scope.

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

  Module Import ModalNotations.

    Notation "⊢ A" := (Valid A%modal) (at level 20, A at level 200) : modal_scope.
    Notation "A -> B" := (Impl A%modal B%modal) : modal_scope.
    Notation "□ A" := (Box A%modal) (at level 20, format "□ A", right associativity) : modal_scope.
    Notation "⌜ A ⌝" := (fun (w : World) => Const A%type w) (at level 1, A at level 200, format "⌜ A ⌝") : modal_scope.
    Notation "'∀' x .. y , P " :=
      (Forall (fun x => .. (Forall (fun y => P%modal)) ..))
        (at level 200, x binder, y binder, right associativity)
      : modal_scope.
    Notation "w1 ⊒ w2" := (Acc w1 w2) (at level 80).
    Notation "f <$> a" := (fmap_box f a).
    Notation "f <*> a" := (K f a).
    Notation "ω1 ∘ ω2" := (acc_trans ω1 ω2) (at level 40, left associativity).
  End ModalNotations.
  Open Scope modal.

  Section Persistence.

    Import Entailment.
    Import ModalNotations.

    Class Persistent (A : TYPE) : Type :=
      persist : ⊢ A -> □A.

    #[export] Instance persistent_box {A} : Persistent (□A) := four.

    #[export] Instance persistent_subst {A} `{Subst A} : Persistent A :=
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

    Lemma inst_persist `{InstSubst AT A, !SubstLaws AT} {w1 w2} (ω : w1 ⊒ w2) :
      forall (ι : Valuation w2) (t : AT w1),
        inst (persist t ω) ι = inst t (inst (sub_acc ω) ι).
    Proof. intros. now rewrite persist_subst, inst_subst. Qed.

    Lemma instprop_persist `{InstPropSubst AT, !SubstLaws AT} {w1 w2} (ω : w1 ⊒ w2) :
      forall (ι : Valuation w2) (t : AT w1),
        instprop (persist t ω) ι <-> instprop t (inst (sub_acc ω) ι).
    Proof. intros. now rewrite persist_subst, instprop_subst. Qed.

    Lemma ent_acc {w1 w2} (ω : w1 ⊒ w2) :
      wco w2 ⊢ persist (A := PathCondition) (wco w1) ω.
    Proof. destruct ω; cbn; now rewrite ?subst_sub_id. Qed.

  End Persistence.

  Notation WProd A B := (fun w : World => A w * B w)%type.
  Notation WList A := (fun w : World => list (A w)).
  Notation WTerm σ := (fun w : World => Term (wctx w) σ).
  Notation STerm σ := (fun Σ => Term Σ σ).

  (* A Notation for Terms because this seems to always gets messed up because of
     the [WTerm] / [STerm] Schizophrenia, *)
  Notation persist__term t :=
    (@persist (WTerm _) (@persistent_subst (STerm _) (@SubstTerm _)) _ t).

  Definition Pred : TYPE := fun w => (Valuation w -> Prop)%type.

  Bind Scope pred_scope with Pred.

  Definition Tm (A : LCtx -> Type) : TYPE :=
    fun w => A w.

  Definition eqₚ {T : LCtx -> Type} {A : Type} {instTA : Inst T A} : ⊢ Tm T -> Tm T -> Pred :=
    fun w t1 t2 ι => (inst t1 ι = inst t2 ι)%type.
  #[global] Arguments eqₚ {T A _} [w] _ _ _/.

  Definition repₚ {T : LCtx -> Type} {A : Type} {instTA : Inst T A} : A -> ⊢ Tm T -> Pred :=
    fun t2 w t1 ι => (inst t1 ι = t2)%type.
  #[global] Arguments repₚ {T A _} _ [w] _ _/.

  Inductive DebugPred (B : LCtx -> Type) {w : World} (b : B w) (P : Pred w) : Pred w := 
    MkDebugPred : forall ι, P ι -> DebugPred B b P ι.

  Definition empₚ {w} : Pred w := fun _ => True.
  Arguments empₚ {w} ι /.
  Definition sepₚ {w} (P Q : Pred w) : Pred w := fun ι => P ι /\ Q ι.
  Arguments sepₚ {w} P Q ι /.
  Definition wandₚ {w} (P Q : Pred w) : Pred w := fun ι => (P ι -> Q ι)%type.
  Arguments wandₚ {w} P Q ι /.
  Definition persistently {w : World} (P : Pred w) : Pred w := P.
  Arguments persistently {w} P ι /.
  (* Iris defines [bi_later_mixin_id] for BI algebras without later. However,
     the identity function as later still causes some later-specific
     typeclasses to be picked. We just define our own trivial modality and
     mixin to avoid that. *)
  Variant laterₚ {w} (P : Pred w) (ι : Valuation w) : Prop :=
    MkLater : P ι -> laterₚ P ι.

  Lemma sepₚ_unfold {w} {P Q : Pred w} {ι} : (sepₚ P Q) ι <-> P ι /\ Q ι.
  Proof.
    split.
    - now destruct 1 as [HP HQ].
    - now constructor.
  Qed.

  Section EntailmentDefinitions.

    Context {w : World}.

    Record bientails (P Q : Pred w) : Prop :=
      MkBientails { fromBientails : forall ι, instprop (wco w) ι -> P ι <-> Q ι }.
    Record entails (P Q : Pred w) : Prop :=
      MkEntails { fromEntails : forall ι, instprop (wco w) ι -> P ι -> Q ι }.

    #[export] Instance pred_equiv : Equiv (Pred w) := bientails.

  End EntailmentDefinitions.

  #[export] Ltac crushPredEntailsMatch1 :=
    match goal with
    | [ H : ?P /\ ?Q |- _ ] => destruct H
    | [ H : ?P \/ ?Q |- _ ] => destruct H
    | [ H: entails ?x ?y, ι : Valuation ?w, Hpc : instprop ?pc ?ι |- _ ] => (pose proof (fromEntails H ι Hpc); clear H)
    | [ H: equiv ?x ?y, ι : Valuation ?w, Hpc : instprop ?pc ?ι |- _ ] => (pose proof (fromBientails H ι Hpc); clear H)
    | [ H: bientails ?x ?y, ι : Valuation ?w, Hpc : instprop ?pc ?ι |- _ ] => (pose proof (fromBientails H ι Hpc); clear H)
    end.
  Ltac crushPredEntails1 := repeat constructor; intros; cbn in *; repeat crushPredEntailsMatch1; intuition.

  Section RewriteRelations.
    Context {w : World}.

    #[export] Instance pred_equivalence : Equivalence (≡@{Pred w}).
    Proof. crushPredEntails1. Qed.

    #[export] Instance preorder_entails : RelationClasses.PreOrder (entails (w := w)).
    Proof. crushPredEntails1. Qed.
    #[export] Instance subrelation_bientails_entails :
      subrelation (≡@{Pred w}) entails.
    Proof. crushPredEntails1. Qed.
    #[export] Instance subrelation_bientails_flip_entails :
      subrelation (≡@{Pred w}) (Basics.flip entails).
    Proof. crushPredEntails1. Qed.

    #[export] Instance entails_rewriterelation : RewriteRelation (@entails w) := {}.

    #[export] Instance proper_bientails :
      Proper (@bientails w ==> @bientails w ==> iff) bientails.
    Proof. crushPredEntails1. Qed.
    #[export] Instance proper_entails_bientails :
      Proper ((≡@{Pred w}) ==> (≡@{Pred w}) ==> iff) entails.
    Proof. crushPredEntails1. Qed.
    #[export] Instance proper_entails_entails :
      Proper (Basics.flip (entails (w := w)) ==> (entails (w := w)) ==> Basics.impl) entails.
    Proof. crushPredEntails1. Qed.

  End RewriteRelations.
  #[global] Arguments bientails {w} (_ _)%P.
  #[global] Arguments entails {w} (_ _)%P.

  Import iris.bi.interface.
(* Note domi: This tactic is defined specifically to prove bi_pred below because firstorder enters a rabbit hole somewhere.
     Note: order of matches is important.
   *)
  #[export] Ltac crushPredEntailsMatch2 :=
      match goal with
      | [ |- True ] => constructor
      | [ H : dist _ _ _ |- _ ] => cbv in H
      | [ H : ?P |- ?P \/ _ ] => left
      | [ H : ?P |- _ \/ ?P ] => right
      | [ |- iff _ _ ] => split
      | [ |- _ -> _ ] => intro
      | [ |- _ /\ _ ] => split
      | [ |- forall P, _ ] => intro
      | [ H1: instprop ?pc ?ι -> ?Q, H2 : instprop ?pc ?ι |- _ ] => specialize (H1 H2)
      | [ |- Reflexive _] => intro
      | [ |- Transitive _] => intro
      | [ |- PreOrder _] => constructor
      | [ |- entails _ _] => constructor
      | [ |- bientails _ _] => constructor
      | [ |- equiv _ _] => constructor
      | [ H : ?H |- ?H ] => assumption
      | [ H1 : ?P1 -> ?P2, H2: ?P1  |- ?P2 ] => apply (H1 H2)
      | [ H : ?H1 <-> ?H2 |- ?H2 ] => apply (proj1 H); clear H
      | [ H : ?H1 <-> ?H2 |- ?H1 ] => apply (proj2 H); clear H
      | [ H : ?P1 <-> ?P2, H2 : ?P1 |- _ ] => apply (proj1 H) in H2; clear H
      | [ H : ?P1 <-> ?P2, H2 : ?P2 |- _ ] => apply (proj2 H) in H2; clear H
      | [ |- Proper _ _ ] => intro; intros
      | [ |- dist _ ?P ?Q ] => change (equiv P Q)
      | [ |- respectful _ _ ?P ?Q ] => intro; intro; intro
      | [ H1 : pointwise_relation ?A _ _ _, H2: ?A |- _ ] => specialize (H1 H2)
      | [ H1 : (forall (a : ?A), _), H2: ?A |- _ ] => specialize (H1 H2)
      | [ H1 : (exists (a : ?A), _) |- _ ] => destruct H1
      | [ a : ?A |- exists (a : ?A), _ ] => exists a
      | [ H : sepₚ _ _ _ |- _ ] => destruct H
      | [ |- sepₚ _ _ _ ] => split
      | [ |- eqₚ ?t1 ?t2 ?ι ] => intro
      (* | [ |- ∀ₚ _ ] => intro *)
      | [ |- wandₚ _ _ _ ] => intro
      | [ H : wandₚ _ _ _ |- _ ] => cbn in H
      | [ H : (fun x => _) _ |- _ ] => cbn in H
      | [ |- True ] => trivial
      | [ |- empₚ _ ] => constructor
      | [ |- persistently _ _ ] => unfold persistently
      | [ H: persistently _ _ |- _ ] => unfold persistently in H
      | [ |- laterₚ _ _ ] => constructor
      | [ H: laterₚ _ _ |- _ ] => destruct H
      | [ |- laterₚ (λ _ , False) _ ∨ _ ] => right
      end.
  Ltac crushPredEntails2 := cbn; intros; cbn in *; repeat (crushPredEntailsMatch1 || crushPredEntailsMatch2); intuition.

  Section proofmode.

    Import iris.bi.extensions.

    #[export] Instance ofe_dist_pred {w} : ofe.Dist (Pred w) :=
      ofe.discrete_dist.

    Canonical bi_pred {w : World} : bi.
    Proof.
      refine
        {| bi_car := Pred w;
          bi_entails := entails;
          bi_emp := empₚ;
          bi_pure P _ := P;
          bi_and P Q ι := (P ι /\ Q ι)%type;
          bi_or P Q ι := (P ι \/ Q ι)%type;
          bi_impl P Q ι := (P ι -> Q ι)%type;
          bi_forall A f ι :=  (forall a, f a ι)%type;
          bi_exist A f ι := (exists a, f a ι)%type;
          bi_sep := sepₚ;
          bi_wand := wandₚ;
          bi_persistently := persistently;
          bi_later := laterₚ;
        |}.
      - constructor; crushPredEntails2.
        apply H1; crushPredEntails2.
      - constructor; crushPredEntails2.
      - constructor; crushPredEntails2.
    Defined.

    Lemma bi_sep_unfold {w} {P Q : Pred w} {ι} : (bi_sep P Q) ι <-> P ι /\ Q ι.
    Proof.
      apply sepₚ_unfold.
    Qed.

    Lemma bi_or_unfold {w} {P Q : Pred w} {ι} : (bi_or P Q) ι <-> P ι \/ Q ι.
    Proof. by cbn. Qed.

    #[export] Instance persistent_pred {w} {P : Pred w} :
      derived_connectives.Persistent P.
    Proof. constructor. now intros ι HP. Qed.

    #[export] Instance affine_pred {w} {P : Pred w} :
      derived_connectives.Affine P.
    Proof. constructor. intros ι HP. now constructor. Qed.


    #[export] Instance pred_pure_forall {w} : BiPureForall (Pred w).
    Proof. constructor. crushPredEntails2. Qed.

  End proofmode.

  Section modalities.
    Import iris.bi.interface.
    (* update: better/more standard names? *)
    Definition assuming {w1 w2 : World } (ω : w2 ⊒ w1) : Pred w1 -> Pred w2 :=
      fun Rpast ι => forall (ιpast : Valuation w1), inst (sub_acc ω) ιpast = ι -> instprop (wco w1) ιpast -> Rpast ιpast.
    Definition knowing {w1 w2 : World} (ω : w2 ⊒ w1) : Pred w1 -> Pred w2 :=
      fun Rpast ι => (exists (ιpast : Valuation w1), inst (sub_acc ω) ιpast = ι /\ instprop (wco w1) ιpast /\ Rpast ιpast)%type.
    Definition forgetting {w1 w2 : World} (ω : w1 ⊒ w2) : Pred w1 -> Pred w2 :=
      fun Rfut ι => Rfut (inst (sub_acc ω) ι).
    Definition unconditionally {w : World} : (□ Pred) w -> Pred w :=
      fun P => (∀ {w2} (ω : w ⊒ w2), assuming ω (P w2 ω))%I.

    Lemma knowing_id {w} {P : Pred w} : knowing acc_refl P ⊣⊢ P.
    Proof.
      rewrite /knowing.
      crushPredEntails2.
      - rewrite inst_sub_id in H0. now subst.
      - now rewrite inst_sub_id.
    Qed.

    (* TODO: turn this into a Proper instance? *)
    Lemma knowing_resp_sub_acc {w1 w2 : World} (ω1 ω2 : w2 ⊒ w1) {P} :
      sub_acc ω1 = sub_acc ω2 -> knowing ω1 P ⊣⊢ knowing ω2 P.
    Proof.
      intros Heq.
      unfold knowing.
      now rewrite Heq.
    Qed.

  End modalities.

  Section InstPred.
    Import iris.bi.interface.

    Class InstPred (T : LCtx -> Type) : Type :=
      MkInstPred
        {  instpred_instprop :: InstProp T
        ;  instpred : forall {w : World}, T w -> Pred w
        ;  instpred_prop : forall {w : World} (ι : Valuation w) (t : T w), instpred t ι <-> instprop t ι
        }.

    Class InstPredSubst (T : LCtx -> Type) `{InstPred T, Subst T} : Prop :=
      { instpred_subst : forall {w w' : World} (ζ : w ⊒ w') (t : T w),
          instpred (persist (A := fun w : World => T w) t ζ) ⊣⊢ forgetting ζ (instpred t)
      ; instpredsubst_instpropsubst :: InstPropSubst T
      }.

    #[global] Arguments instpred {T _ w} !_.
    #[global] Arguments instpred_instprop {T} !_.
    #[global] Arguments MkInstPred [T] {_} instpred%I _.
    #[global] Arguments InstPredSubst T {_ _}.

    #[export] Instance instpred_proper_bientails {w : World} `{InstPred A} : Proper (Entailment.bientails ==> equiv) (instpred (w := w)).
    Proof.
      intros P Q HPQ.
      constructor; intros.
      rewrite !instpred_prop.
      now apply HPQ.
    Qed.

    #[export] Program Instance instpred_option `{InstPred A} : InstPred (Option A) :=
      MkInstPred
        (fun Σ o =>
           match o with
           | Some C => instpred C
           | None   => False%I
           end) _.
    Next Obligation.
      intros. destruct t; cbn; last done. now apply instpred_prop.
    Qed.

    #[export] Program Instance instpred_pair `{InstPred A, InstPred B} : InstPred (Pair A B) :=
      MkInstPred (fun Σ '(a,b) => instpred a ∗ instpred b)%I _.
    Next Obligation.
      intros. destruct t; cbn; now rewrite bi_sep_unfold !instpred_prop.
    Qed.

    (* #[export] Instance instpredsubst_pair `{InstPredSubst A, InstPredSubst B} : InstPredSubst (Pair A B). *)
    (* Proof. hnf. intros ? ? ζ [a b]. rewrite forgetting_sepₚ. apply and_iff_morphism; apply instpred_subst. Qed. *)

    Fixpoint instpred_ctx `{InstPred A} {w : World} (xs : Ctx (A w)) :=
      match xs with
      | ctx.nil       => emp%I
      | ctx.snoc xs x => (instpred_ctx xs ∗ instpred x)%I
      end.

    #[export] Program Instance instpred_ctx_inst `{InstPred A} : InstPred (fun Σ => Ctx (A Σ)) :=
      MkInstPred (fun w => instpred_ctx) _.
    Next Obligation.
      intros. induction t; cbn; first done.
      now rewrite bi_sep_unfold instpred_prop IHt.
    Qed.

    Lemma instpred_nil `{InstPred A} {w} :
      instpred (w := w) ctx.nil ⊣⊢ True%I.
    Proof. reflexivity. Qed.

    Lemma instpred_snoc `{InstPred A} {w : World} (xs : Ctx (A w)) (x : A w) :
      instpred (xs ▻ x) ⊣⊢ instpred xs ∗ instpred x.
    Proof. reflexivity. Qed.

    Lemma instpred_cat `{InstPred A} {w : World} (x y : Ctx (A w)) :
      instpred (x ▻▻ y) ⊣⊢
        instpred x ∗ instpred y.
    Proof. induction y.
           - now rewrite ?derived_laws.bi.sep_emp.
           - change (instpred (x ▻▻ y) ∗ instpred b ⊣⊢ instpred x ∗ (instpred y ∗ instpred b)).
             now rewrite IHy derived_laws.bi.sep_assoc.
    Qed.

    Lemma instpred_singleton {w : World} `{InstPred A} (x : A w) : instpred (w := w) [x]%ctx ⊣⊢ instpred x.
    Proof. cbn. now rewrite derived_laws.bi.emp_sep. Qed.

    #[export] Program Instance instpred_formula : InstPred Formula :=
      MkInstPred (fix inst_formula {w : World} (fml : Formula w) :=
        match fml with
        | formula_user p ts      => fun ι => env.uncurry (𝑷_inst p) (inst ts ι)
        | formula_bool t         => repₚ true (A := Val ty.bool) t 
        | formula_prop ζ P       => fun ι => uncurry_named P (inst ζ ι)
        | formula_relop op t1 t2 => fun ι => bop.eval_relop_prop op (inst t1 ι) (inst t2 ι)
        | formula_true           => True%I
        | formula_false          => False%I
        | formula_and F1 F2      => (inst_formula F1 ∗ inst_formula F2)%I
        | formula_or F1 F2       => (inst_formula F1 ∨ inst_formula F2)%I
        end) _.
    Next Obligation.
      intros.
      induction t;
        unfold repₚ, eqₚ;
        rewrite ?bi_sep_unfold ?bi_or_unfold;
        crushPredEntails2.
    Qed.

    #[export] Instance instpred_subst_formula : InstPredSubst Formula.
    Admitted.
    (* Proof. *)
    (*   constructor; last by typeclasses eauto. *)
    (*   intros ? ? ? f. constructor; intros ι Hpc. *)
    (*   unfold forgetting. *)
    (*   induction f; cbn; *)
    (*     rewrite ?inst_subst ?bi_sep_unfold; auto. *)
    (*   now apply Morphisms_Prop.and_iff_morphism. *)
    (*   now apply Morphisms_Prop.or_iff_morphism. *)
    (* Qed. *)

    Lemma wco_valid {w : World} : ⊢ instpred (w := w) (wco w).
    Proof. constructor. crushPredEntails2. now rewrite instpred_prop. Qed.

    Import iris.bi.extensions.
    Definition proprepₚ {T : LCtx -> Type} {instTA : InstPred T} : Prop -> forall w, Tm T w -> Pred w :=
      fun t2 w t1 => (instpred t1 ∗-∗ bi_pure t2)%I.
    #[global] Arguments proprepₚ {T _} _ [w] _ _/.

  End InstPred.


  Section SolverInterface.
    Import Entailment.

    Definition Solver : Type :=
      forall (w0 : World) (C0 : PathCondition w0),
        option { w1 & Tri w0 w1 * PathCondition w1 }%type.

    Definition solver_null : Solver :=
      fun w C => Some (existT w (tri_id , C)).

    Definition SolverUserOnly : Type :=
      forall Σ (p : 𝑷), Env (Term Σ) (𝑷_Ty p) -> Option PathCondition Σ.

    Definition SolverUserOnlySpec (s : SolverUserOnly) : Prop :=
      forall Σ (p : 𝑷) (ts : Env (Term Σ) (𝑷_Ty p)),
        s Σ p ts ⊣⊢ Some [formula_user p ts]%ctx.

    Section SimplifyAll.
      Import option.notations.
      Context {Σ} (g : Formula Σ -> PathCondition Σ -> option (PathCondition Σ)).

      Definition simplify_all {Σ} (g : Formula Σ -> PathCondition Σ -> option (PathCondition Σ)) :=
        fix simplify_all (C k : PathCondition Σ) {struct C} : option (PathCondition Σ) :=
          match C with
          | ctx.nil => Some k
          | ctx.snoc C F  =>
              k' <- simplify_all C k ;;
              g F k'
          end.
    End SimplifyAll.

    Section SimplifyAllSpec.
      Import option.notations.
      Import iris.bi.interface.
      Import iris.proofmode.tactics.
      Context {w : World} (g : Formula w -> PathCondition w -> option (PathCondition w)).
      Context (g_spec : forall F k,
                  option.spec
                    (fun r : PathCondition w =>
                       instpred (w := w) (k ▻ F) ⊣⊢ instpred r)
                    (instpred F ⊢ False)
                    (g F k)).

      Lemma simplify_all_spec (C k : PathCondition w) :
        option.spec
          (fun r : PathCondition w =>
             instpred (w := w) (k ▻▻ C) ⊣⊢ instpred r)%I
          (instpred (w := w) C ⊢ False)%I
          (simplify_all g C k).
      Proof.
        induction C as [|C IHC F]; cbn; [constructor; reflexivity|].
        apply option.spec_bind. revert IHC.
        apply option.spec_monotonic.
        - intros tmp Htmp. specialize (g_spec F tmp). revert g_spec.
          apply option.spec_monotonic.
          + iIntros (res Hres).
            now rewrite -Hres instpred_snoc -Htmp.
          + iIntros (HnF) "[HC HF]".
            now iApply (HnF with "HF").
        - iIntros (HnC) "[HC HF]".
          now iApply HnC.
      Qed.

    End SimplifyAllSpec.

    Section SolverSpec.
      Require Import iris.bi.interface.
      Definition SolverSpec (s : Solver) : Prop :=
        forall (w : World) (C0 : PathCondition w),
          option.spec
            (fun '(existT w1 (ζ, C1)) =>
               (knowing (acc_triangular ζ) (instpred C1)) ⊣⊢ (instpred C0))%I
            ((instpred C0) ⊢ False)%I
            (s w C0).

      Lemma solver_null_spec : SolverSpec solver_null.
      Proof.
        intros w C. constructor.
        unfold knowing; crushPredEntails2.
        - rewrite inst_sub_id in H0.
          now subst.
        - now rewrite inst_sub_id.
      Qed.
    End SolverSpec.


    Section WithUserOnlySolver.

      Context (user : SolverUserOnly).

      Definition solveruseronly_simplify_formula {Σ} (F : Formula Σ) (k : PathCondition Σ) : option (PathCondition Σ) :=
        match F with
        | formula_user p ts => option.map (fun r => k ▻▻ r) (user ts)
        | F                 => Some (k ▻ F)
        end.

      Definition solveruseronly_to_solver : Solver :=
        fun w C =>
          option_map
            (fun l => existT w (tri_id, l))
            (simplify_all solveruseronly_simplify_formula C ctx.nil).

      Context (user_spec : SolverUserOnlySpec user).

      Import Entailment.
      Import iris.bi.interface.
      Import iris.proofmode.tactics.

      Lemma solveruseronly_simplify_formula_spec {w : World} (F : Formula w) (k : PathCondition w) :
        option.spec
          (fun r : PathCondition w =>
             instpred (k ▻ F) ⊣⊢ instpred r)%I
          (instpred (w := w) F ⊢ False)%I
          (solveruseronly_simplify_formula F k).
      Proof.
        destruct F; try (constructor; reflexivity). apply option.spec_map.
        specialize (user_spec ts).
        destruct user; constructor; cbn in *.
        - change (λ ι : Valuation w, env.uncurry (𝑷_inst p) (inst ts ι))
            with (instpred (formula_user p ts)).
          rewrite (instpred_cat k p0).
          change (instpred p0) with (instpred (T := PathCondition) p0).
          change (bientails p0 [formula_user p ts]%ctx) in user_spec.
          now rewrite user_spec instpred_singleton.
        - change (fun ι' => env.uncurry (𝑷_inst p) (inst ts ι'))
            with (instpred (formula_user p ts)).
          rewrite <-instpred_singleton.
          change (instpred (Some [formula_user p ts]%ctx) ⊢ False)%stdpp.
          now rewrite <-user_spec.
      Qed.

      Lemma solveruseronly_to_solver_spec : SolverSpec solveruseronly_to_solver.
      Proof.
        iIntros (w0 C). unfold solveruseronly_to_solver.
        apply option.spec_map.
        generalize (simplify_all_spec (w := w0) solveruseronly_simplify_formula solveruseronly_simplify_formula_spec C ctx.nil).
        apply option.spec_monotonic; last done.
        iIntros (r H).
        rewrite knowing_id.
        rewrite instpred_cat in H.
        now rewrite bi.emp_sep in H.
      Qed.

    End WithUserOnlySolver.

  End SolverInterface.

  Section SolverCompose.
    Definition solver_compose (s1 s2 : Solver) : Solver :=
      fun w0 fmls0 =>
        option.bind
          (s1 _ fmls0)
          (fun '(existT w1 (ν01 , fmls1)) =>
             option.map
               (fun '(existT w2 (ν12 , fmls2)) =>
                  existT w2 (tri_comp ν01 ν12 , fmls2))
               (s2 _ fmls1)).

  End SolverCompose.

  Ltac wsimpl :=
    repeat
      (try change (wctx (wsnoc ?w ?b)) with (wctx w ▻ b);
       try change (wco (wsnoc ?w ?b)) with (subst (wco w) (sub_wk1 (b:=b)));
       try change (sub_acc (@acc_refl ?w)) with (sub_id (wctx w));
       try change (wctx (wformula ?w ?fml)) with (wctx w);
       try change (sub_acc (@acc_formula_right ?w ?fml)) with (sub_id (wctx w));
       try change (sub_acc (@acc_pathcondition_right ?w ?fmls)) with (sub_id (wctx w));
       try change (wco (wformula ?w ?fml)) with (cons fml (wco w));
       try change (wco (@wsubst ?w _ _ ?xIn ?t)) with (subst (wco w) (sub_single xIn t));
       try change (wctx (@wsubst ?w _ _ ?xIn ?t)) with (ctx.remove xIn);
       try change (sub_acc (@acc_subst_right ?w _ _ ?xIn ?t)) with (sub_single xIn t);
       rewrite <- ?sub_comp_wk1_tail, ?inst_subst, ?subst_sub_id,
         ?inst_sub_id, ?inst_sub_wk1, ?inst_sub_snoc,
         ?inst_lift, ?inst_sub_single_shift, ?instprop_snoc,
         ?sub_acc_trans, ?sub_acc_triangular, ?inst_triangular_right_inverse).

End WorldsOn.

Module Type WorldsMixin (B : Base) (PK : PredicateKit B) :=
  FormulasOn B PK <+ ChunksOn B PK <+ WorldsOn B PK.

Module Type SolverKit (B : Base) (P : PredicateKit B) (Import W : WorldsMixin B P).
  Local Set Implicit Arguments.

  Parameter solver      : Solver.
  Parameter solver_spec : SolverSpec solver.
End SolverKit.

Module DefaultSolverKit (B : Base) (P : PredicateKit B)
  (Import W : WorldsMixin B P) <: SolverKit B P W.

  Definition solver : Solver := solver_null.
  Definition solver_spec : SolverSpec solver := solver_null_spec.

End DefaultSolverKit.
