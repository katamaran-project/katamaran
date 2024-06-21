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

Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.
Local Obligation Tactic := idtac.

Declare Scope rel_scope.
Delimit Scope rel_scope with R.

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
    Definition wsubst (w : World) x {σ} {xIn : x∷σ ∈ w} (t : Term (w - x∷σ) σ) : World :=
      {| wctx := wctx w - x∷σ; wco := subst (wco w) (sub_single xIn t) |}.
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

    Definition wmatchvar (w : World) {x σ} (xIn : x∷σ ∈ w) (p : @Pattern LVar σ)
      (pc : PatternCase p) : World :=
      let Δ   : LCtx           := PatternCaseCtx pc in
      let w1  : World          := wcat w Δ in
      let eq : ((w ▻▻ Δ) - x∷σ) = (w - x∷σ ▻▻ Δ) := ctx.remove_in_cat_left xIn in
      let ts  : Sub Δ (w - x∷σ ▻▻ Δ) := sub_cat_right Δ in
      let t   : Term (w - x∷σ ▻▻ Δ) σ := pattern_match_term_reverse _ pc ts in
      let t'   : Term ((w ▻▻ Δ) - x∷σ) σ := eq_rect (w - x∷σ ▻▻ Δ) (fun Σ => Term Σ σ) (pattern_match_term_reverse _ pc ts) ((w ▻▻ Δ) - x∷σ) (eq_sym eq) in
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
        (xIn : x∷σ ∈ w) (t : Term (wctx w - x∷σ) σ)
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


    Record IsIsomorphism {w1 w2} (ω12 : w1 ⊒ w2) (ω21 : w2 ⊒ w1) :=
      MkIsIsomorphism {
          wiso_there : forall ι, instprop (wco w1) ι -> inst (sub_acc ω12) (inst (sub_acc ω21) ι) = ι;
          wiso_back : forall ι, instprop (wco w2) ι -> inst (sub_acc ω21) (inst (sub_acc ω12) ι) = ι
        }.

    Lemma iso_symm {w1 w2} {ω12 : w1 ⊒ w2} {ω21 : w2 ⊒ w1} :
      IsIsomorphism ω12 ω21 -> IsIsomorphism ω21 ω12.
    Proof.
      intros [Ht Hb].
      now constructor.
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

    Program Definition acc_let_right {w} (b : LVar ∷ Ty) v : w ⊒ wlet w b v :=
      @acc_sub w (wlet w b v) sub_wk1 _.
    Next Obligation.
      intros * ι Hpc.
      now apply proj1 in Hpc.
    Defined.

    Program Definition acc_let_left {w} (b : LVar ∷ Ty) v : wlet w b v ⊒ w :=
      acc_sub (sub_snoc (sub_id w) b (term_val _ v)) _.
    Next Obligation.
      intros * ι Hpc.
      split; last reflexivity.
      change (subst_ctx ?pc ?ς)
        with (subst pc ς).
      now rewrite <-subst_sub_comp, sub_comp_wk1_tail, subst_sub_id.
    Defined.

    Program Definition acc_let_snoc {w} (b : LVar ∷ Ty) v : wsnoc w b ⊒ wlet w b v :=
      acc_sub (sub_id (w ▻ b) : Sub (wsnoc w b) (wlet w b v)) _.
    Next Obligation.
      intros * ι.
      destruct (env.view ι) as [ι v'].
      unfold wlet; simpl.
      intros Hpc.
      destruct (proj1 (instprop_snoc _ _ _) Hpc) as [Hpc' H].
      now rewrite instprop_subst, inst_sub_id.
    Defined.
    
    Lemma acc_let_iso w b v : IsIsomorphism (@acc_let_right w b v) (acc_let_left b v).
    Proof.
      constructor; intros; simpl.
      - now rewrite inst_sub_snoc, inst_sub_id, inst_sub_wk1.
      - rewrite inst_sub_snoc, inst_sub_id.
        destruct (env.view ι) as (ι & v').
        destruct H as (Hpc & Hbv); cbn in Hbv.
        subst.
        now rewrite inst_sub_wk1.
    Qed.

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

    Definition acc_subst_right {w : World} x {σ} {xIn : x∷σ ∈ w} (t : Term (w - x∷σ) σ) :
      w ⊒ wsubst w x t :=
      let ζ  := sub_single xIn t in
      let w' := {| wctx := w - x∷σ; wco := subst (wco w) ζ |}  in
      @acc_sub w w' ζ (entails_refl (wco w')).
    Arguments acc_subst_right {w} x {σ xIn} t.

    Definition acc_match_right {w : World} {σ} {s : Term w σ}
      {p : @Pattern LVar σ} (pc : PatternCase p) : w ⊒ wmatch w s p pc :=
      @acc_sub w (wmatch w s p pc) (sub_cat_left (PatternCaseCtx pc))
        (fun ι HCι => proj1 HCι).

    Program Definition acc_matchvar_right {w : World} {x σ} {xIn : x∷σ ∈ w}
      {p : @Pattern LVar σ} (pc : PatternCase p) : w ⊒ wmatchvar w xIn p pc :=
      let Δ   : LCtx           := PatternCaseCtx pc in
      let w1  : World          := wcat w Δ in
      let eq : ((w ▻▻ Δ) - x∷σ) = (w - x∷σ ▻▻ Δ) := ctx.remove_in_cat_left xIn in
      let ts  : Sub Δ (w - x∷σ ▻▻ Δ) := sub_cat_right Δ in
      let t   : Term (w - x∷σ ▻▻ Δ) σ := pattern_match_term_reverse _ pc ts in
      let t'   : Term ((w ▻▻ Δ) - x∷σ) σ := eq_rect (w - x∷σ ▻▻ Δ) (fun Σ => Term Σ σ) (pattern_match_term_reverse _ pc ts) ((w ▻▻ Δ) - x∷σ) (eq_sym eq) in
      let wmv : World          := wsubst w1 x t' in
      let sub₁ : Sub w (w ▻▻ Δ) := sub_cat_left Δ in
      let sub₂ : Sub (w ▻▻ Δ) ((w ▻▻ Δ) - x∷σ) := sub_single _ t' in
      let sub : Sub w wmv := subst sub₁ sub₂ in
      @acc_sub w wmv sub _.
    Next Obligation.
      intros. cbn -[sub_single].
      now rewrite <-subst_sub_comp.
    Qed.

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

  Section SolverInterface.
    Import Entailment.

    Definition Solver : Type :=
      forall (w0 : World) (C0 : PathCondition w0),
        option { w1 & Tri w0 w1 * PathCondition w1 }%type.

    Definition SolverSpec (s : Solver) : Prop :=
      forall (w0 : World) (C0 : PathCondition w0),
        option.spec
          (fun '(existT w1 (ζ, C1)) =>
             forall ι0,
               instprop (wco w0) ι0 ->
               (instprop C0 ι0 -> inst_triangular ζ ι0) /\
                 (forall ι1,
                     instprop (wco w1) ι1 ->
                     ι0 = inst (sub_triangular ζ) ι1 ->
                     instprop C0 ι0 <-> instprop C1 ι1))
          (forall ι, instprop (wco w0) ι -> ~ instprop C0 ι)
          (s w0 C0).

    Definition solver_null : Solver :=
      fun w C => Some (existT w (tri_id , C)).

    Lemma solver_null_spec : SolverSpec solver_null.
    Proof.
      intros w C. constructor. cbn. intros ι Hpc. split. auto.
      intros ι' Hpc' ->. now rewrite inst_sub_id.
    Qed.

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

      Context (g_spec : forall F k,
                  option.spec
                    (fun r : PathCondition Σ =>
                       forall ι : Valuation Σ,
                         instprop (k ▻ F) ι <-> instprop r ι)
                    (forall ι : Valuation Σ, ~ instprop F ι)
                    (g F k)).

      Lemma simplify_all_spec (C k : PathCondition Σ) :
        option.spec
          (fun r : PathCondition Σ =>
             forall ι : Valuation Σ,
               instprop (k ▻▻ C) ι <-> instprop r ι)
          (forall ι : Valuation Σ, ~ instprop C ι)
          (simplify_all g C k).
      Proof.
        induction C as [|C IHC F]; cbn; [constructor; reflexivity|].
        apply option.spec_bind. revert IHC.
        apply option.spec_monotonic.
        - intros tmp Htmp. specialize (g_spec F tmp). revert g_spec.
          apply option.spec_monotonic.
          + intros res Hres ι. rewrite (Htmp ι). apply (Hres ι).
          + intros HnF ι [HCι HFι]. now apply (HnF ι).
        - intros HnC ι [HCι HFι]. now apply (HnC ι).
      Qed.

    End SimplifyAll.

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

      Lemma solveruseronly_simplify_formula_spec {Σ} (F : Formula Σ) (k : PathCondition Σ) :
        option.spec
          (fun r : PathCondition Σ =>
             forall ι : Valuation Σ,
               instprop (k ▻ F) ι <-> instprop r ι)
          (forall ι : Valuation Σ, ~ instprop F ι)
          (solveruseronly_simplify_formula F k).
      Proof.
        destruct F; try (constructor; reflexivity). apply option.spec_map.
        specialize (user_spec ts).
        destruct user; constructor; intros ι; specialize (@user_spec ι); cbn in *.
        - unfold PathCondition. rewrite instprop_cat. intuition.
        - intuition.
      Qed.

      Lemma solveruseronly_to_solver_spec : SolverSpec solveruseronly_to_solver.
      Proof.
        intros w0 C. unfold solveruseronly_to_solver.
        apply option.spec_map.
        generalize (simplify_all_spec solveruseronly_simplify_formula solveruseronly_simplify_formula_spec C ctx.nil).
        apply option.spec_monotonic.
        - intros r H ι Hpc. split; [constructor|].
          specialize (H ι). unfold PathCondition in H.
          rewrite instprop_cat in H. cbn in H. rewrite leftid_true_and in H.
          intros ι' Hpc'. cbn. rewrite inst_sub_id. intros. now subst.
        - intros Hnf ι Hpc. apply Hnf.
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

    Lemma solver_compose_spec {s1 s2} (spec1 : SolverSpec s1) (spec2 : SolverSpec s2) : SolverSpec (solver_compose s1 s2).
    Proof.
      unfold SolverSpec, solver_compose. intros w0 fmls0.
      apply option.spec_bind.
      generalize (spec1 _ fmls0); clear spec1.
      apply option.spec_monotonic; auto.
      intros (w1 & ν01 & fmls1) H1.
      apply option.spec_map.
      generalize (spec2 _ fmls1); clear spec2.
      apply option.spec_monotonic; auto.
      - intros (w2 & ν12 & fmls2) H2. intros ι0 Hpc0.
        specialize (H1 ι0 Hpc0). destruct H1 as [H01 H10].
        rewrite inst_tri_comp. split.
        + intros Hfmls0. split; auto.
          remember (inst (sub_triangular_inv ν01) ι0) as ι1.
          assert (instprop (wco w1) ι1) as Hpc1 by
              (subst; apply entails_triangular_inv; auto).
          apply H2; auto. apply H10; auto.
          subst; rewrite inst_triangular_right_inverse; auto.
        + intros ι2 Hpc2 Hι0. rewrite sub_triangular_comp, inst_subst in Hι0.
          remember (inst (sub_triangular ν12) ι2) as ι1.
          assert (instprop (wco w1) ι1) as Hpc1 by
              (revert Hpc2; subst; rewrite <- sub_acc_triangular, <- instprop_persist; apply ent_acc).
          rewrite H10; eauto. apply H2; auto.
      - intros Hfmls1 ι0 Hpc0 Hfmls0. specialize (H1 ι0 Hpc0).
        destruct H1 as [H01 H10]. inster H01 by auto.
        pose (inst (sub_triangular_inv ν01) ι0) as ι1.
        assert (instprop (wco w1) ι1) as Hpc1 by
            (subst; apply entails_triangular_inv; auto).
        apply (Hfmls1 ι1 Hpc1). revert Hfmls0.
        apply H10; auto. subst ι1.
        now rewrite inst_triangular_right_inverse.
    Qed.
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
