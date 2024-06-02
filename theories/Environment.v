(******************************************************************************)
(* Copyright (c) 2019 Steven Keuchel, Dominique Devriese, Georgy Lukyanov     *)
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
     Bool.Bool.
From Equations Require Import Equations.
From Katamaran Require Import
     Prelude Context Notations.
Import ctx.notations.

Local Set Implicit Arguments.
Local Open Scope lazy_bool_scope.

Declare Scope env_scope.
Delimit Scope env_scope with env.
Declare Scope dep_pattern_scope.
Delimit Scope dep_pattern_scope with dep_pattern.

Module env.

Section WithBinding.
  Context {B : Set}.

  Section WithDom.
    Context {D : B -> Set}.

    Inductive Env : Ctx B -> Set :=
    | nil                                     : Env []
    | snoc {Γ} (E : Env Γ) {b : B} (db : D b) : Env (Γ ▻ b).

    Variant NilView : Env [] -> Set :=
      isNil : NilView nil.

    Variant SnocView {Γ b} : Env (Γ ▻ b) -> Set :=
      isSnoc (E : Env Γ) (v : D b) : SnocView (snoc E v).

    Definition view (Γ : Ctx B) (E : Env Γ) :
      match Γ with
      | [ctx] => NilView
      | Γ ▻ b => SnocView
      end E :=
      match E with
      | nil      => isNil
      | snoc E v => isSnoc E v
      end.

    Fixpoint cat {Γ Δ} (EΓ : Env Γ) (EΔ : Env Δ) : Env (Γ ▻▻ Δ) :=
      match EΔ with
      | nil       => EΓ
      | snoc E db => snoc (cat EΓ E) db
      end.

    Variant CatView {Γ Δ} : Env (Γ ▻▻ Δ) -> Set :=
      isCat (EΓ : Env Γ) (EΔ : Env Δ) : CatView (cat EΓ EΔ).

    Fixpoint catView {Γ Δ} : forall E : Env (Γ ▻▻ Δ), CatView E :=
      match Δ as c return (forall E : Env (Γ ▻▻ c), CatView E) with
      | [ctx] => fun EΓ : Env Γ => isCat EΓ nil
      | Δ ▻ b => fun EΓΔb : Env (Γ ▻▻ Δ ▻ b) =>
                   let '(isSnoc EΓΔ v) := view EΓΔb in
                   let '(isCat EΓ EΔ)  := catView EΓΔ in
                   isCat EΓ (snoc EΔ v)
      end.

    Lemma catView_cat {Γ Δ} (EΓ : Env Γ) (EΔ : Env Δ) :
      catView (cat EΓ EΔ) = isCat EΓ EΔ.
    Proof. induction EΔ; cbn; now rewrite ?IHEΔ. Qed.

    Ltac destroy x :=
      try (progress cbn in x);
      lazymatch type of x with
      | Env []       => destruct (view x)
      | Env (_ ▻ _)  => destruct (view x) as [x]; destroy x
      | Env (_ ▻▻ _) => let E1 := fresh in
                        let E2 := fresh in
                        destruct (catView x) as [E1 E2];
                        destroy E1; destroy E2
      | _ ∈ []       => destruct (ctx.view x)
      | _ ∈ _ ▻ _    => destruct (ctx.view x)
      | _            => idtac
      end.

    Section TransparentObligations.
      Local Set Transparent Obligations.
      Derive Signature NoConfusion NoConfusionHom for Env.

      Context {eqdec_b : EqDec B}.
      Context {eqdec_d : forall b, EqDec (D b) }.

      Instance eq_dec_env {Γ} : EqDec (Env Γ).
      Proof. eqdec_proof. Defined.

    End TransparentObligations.

    Section Inversions.

      Lemma inversion_eq_snoc {Γ : Ctx B} {b : B} (E1 E2 : Env Γ) (v1 v2 : D b) :
        snoc E1 v1 = snoc E2 v2 <->
        E1 = E2 /\ v1 = v2.
      Proof.
        split.
        - intros H. now dependent elimination H.
        - intros []; congruence.
      Qed.

      Lemma inversion_eq_cat {Γ Δ : Ctx B} (EΓ1 EΓ2 : Env Γ) (EΔ1 EΔ2 : Env Δ) :
        cat EΓ1 EΔ1 = cat EΓ2 EΔ2 <->
        EΓ1 = EΓ2 /\ EΔ1 = EΔ2.
      Proof.
        induction EΔ1; destroy EΔ2; cbn; [easy|].
        rewrite !inversion_eq_snoc, IHEΔ1. intuition auto.
      Qed.

    End Inversions.

    Fixpoint lookup {Γ} (E : Env Γ) : forall {b}, b ∈ Γ -> D b :=
      match E with
      | nil      => fun _ bIn => match ctx.view bIn with end
      | snoc E v => fun _ bIn =>
        match ctx.view bIn with
        | ctx.isZero   => v
        | ctx.isSucc i => lookup E i
        end
      end.

    Inductive All (Q : forall b, D b -> Type) : forall {Γ}, Env Γ -> Type :=
    | all_nil : All Q nil
    | all_snoc {Γ E b d} : @All Q Γ E -> Q b d -> All Q (snoc E d).

    #[derive(equations=no)]
    Equations all_snoc_inv_1 {Q : forall b, D b -> Type} {Γ b} {E : Env Γ} {d : D b} :
      All Q (snoc E d) -> All Q E := | all_snoc QE _ => QE.

    #[derive(equations=no)]
    Equations all_snoc_inv_2 {Q : forall b, D b -> Type} {Γ b} {E : Env Γ} {d : D b} :
      All Q (snoc E d) -> Q b d := | all_snoc _ Qd => Qd.

    Lemma all_intro {Q : forall [b], D b -> Type} (HQ : forall b (d : D b), Q d) :
      forall Γ (E : Env Γ), All Q E.
    Proof. intros ? E. induction E; constructor; auto. Defined.

    Lemma all_elim {Q : forall [b], D b -> Type} {Γ} {E : Env Γ} (HE : All Q E) :
      forall b (bIn : b ∈ Γ), Q (lookup E bIn).
    Proof. induction HE; intros x xIn; destruct (ctx.view xIn); cbn; auto. Defined.

    Section HomEquality.

      Variable eqb : forall [b], D b -> D b -> bool.

      Equations(noeqns) eqb_hom {Γ} (δ1 δ2 : Env Γ) : bool :=
      | nil         | nil         := true;
      | snoc δ1 db1 | snoc δ2 db2 := eqb db1 db2 &&& eqb_hom δ1 δ2.

      Lemma eqb_hom_spec_point (Γ : Ctx B) (xs : Env Γ)
        (HYP : All (fun b => EqbSpecPoint (@eqb b)) xs) :
        EqbSpecPoint eqb_hom xs.
      Proof.
        induction xs; intros ys; destroy ys; cbn.
        - do 2 constructor.
        - specialize (IHxs (all_snoc_inv_1 HYP)). pose proof (all_snoc_inv_2 HYP) as IHb.
          destruct (IHb v); subst.
          + destruct IHxs with ys; constructor.
            * subst; auto.
            * intros ?%inversion_eq_snoc. intuition.
          + constructor. intros ?%inversion_eq_snoc. intuition.
      Qed.

      Variable eqb_spec : forall b (x y : D b),
        reflect (x = y) (eqb x y).

      Lemma eqb_hom_spec {Γ} (δ1 δ2 : Env Γ) :
        reflect (δ1 = δ2) (eqb_hom δ1 δ2).
      Proof. apply eqb_hom_spec_point, all_intro; auto. Qed.

    End HomEquality.

    Fixpoint tabulate {Γ} : (forall b, b ∈ Γ -> D b) -> Env Γ :=
      match Γ with
      | []    => fun _ => nil
      | Γ ▻ b => fun EΓb =>
        snoc (tabulate (fun y yIn => EΓb y (ctx.in_succ yIn))) (EΓb _ ctx.in_zero)
      end.

    Fixpoint update {Γ} (E : Env Γ) {struct E} :
      forall {b} (bIn : b ∈ Γ) (new : D b), Env Γ :=
      match E with
      | nil        => fun _ bIn => match ctx.view bIn with end
      | snoc E old => fun _ bIn =>
        match ctx.view bIn with
        | ctx.isZero     => snoc E
        | ctx.isSucc bIn => fun new => snoc (update E bIn new) old
        end
      end.

    Definition head {Γ b} (E : Env (Γ ▻ b)) : D b :=
      match E in Env Γb
      return match Γb with
             | []    => unit
             | Γ ▻ b => D b
             end
      with
      | nil => tt
      | snoc E db => db
      end.

    Definition tail {Γ b} (E : Env (Γ ▻ b)) : Env Γ :=
      match E in Env Γb
      return match Γb with
             | []    => unit
             | Γ ▻ _ => Env Γ
             end
      with
      | nil => tt
      | snoc E _ => E
      end.

    Fixpoint take {Γ} Δ (E : Env (Γ ▻▻ Δ)) : Env Δ :=
      match Δ , E with
      | []    , E => nil
      | Δ ▻ b , E => snoc (take Δ (tail E)) (head E)
      end.

    Fixpoint drop {Γ} Δ (E : Env (Γ ▻▻ Δ)) : Env Γ :=
      match Δ , E with
      | []    , E => E
      | Δ ▻ _ , E => drop Δ (tail E)
      end.

    Fixpoint remove {Γ b} (E : Env Γ) : forall (bIn : b ∈ Γ), Env (Γ - b) :=
      match E with
      | nil      => fun bIn => match ctx.view bIn with end
      | snoc E v => fun bIn =>
        match ctx.view bIn in ctx.SnocView bIn return Env (ctx.remove bIn) with
        | ctx.isZero     => E
        | ctx.isSucc bIn => snoc (remove E bIn) v
        end
      end.
    Global Arguments remove {_} b%ctx E.

    Fixpoint insert b {Γ : Ctx B} (bIn : b ∈ Γ) {struct Γ} :
      forall (E : Env (Γ - b)) (v : D b), Env Γ :=
      ctx.In_case (fun b Γ bIn => Env (Γ - b) -> D b -> Env Γ)
        (fun b Γ E v => snoc E v)
        (fun b' Γ b bIn E v => let (E,v') := view E in
                               snoc (insert bIn E v) v')
        bIn.

    Lemma remove_insert {b} {Γ} (bIn : b ∈ Γ) (v : D b) (E : Env (Γ - b)) :
      remove b (insert bIn E v) bIn = E.
    Proof. induction Γ; destroy bIn; destroy E; cbn; now f_equal. Qed.

    Lemma insert_remove {b} {Γ} (bIn : b ∈ Γ) (E : Env Γ) :
      insert bIn (remove b E bIn) (lookup E bIn) = E.
    Proof. induction E; destroy bIn; cbn; now f_equal. Qed.

    Lemma lookup_insert {b Γ} (bIn : b ∈ Γ) (v : D b) (E : Env (Γ - b)) :
      lookup (insert bIn E v) bIn = v.
    Proof. induction Γ; destroy bIn; destroy E; cbn; auto. Qed.

    Lemma lookup_drop {b Σ Γ} (bIn : b ∈ Γ) (E : Env (Γ ▻▻ Σ)) :
      lookup (drop Σ E) bIn = lookup E (ctx.in_cat_left Σ bIn).
    Proof. induction Σ; destroy bIn; destroy E; cbn; auto. Qed.

    Lemma lookup_take {b Σ Γ} (bIn : b ∈ Σ) (E : Env (Γ ▻▻ Σ)) :
      lookup (take Σ E) bIn = lookup E (ctx.in_cat_right bIn).
    Proof. induction Σ; destroy bIn; destroy E; cbn; auto. Qed.

    Lemma lookup_remove {x b Γ} (xIn : x ∈ Γ) (bIn : b ∈ Γ - x) (E : Env Γ) :
      lookup (remove x E xIn) bIn = lookup E (ctx.shift_var xIn bIn).
    Proof. induction Γ; destroy xIn; destroy bIn; destroy E; cbn; auto. Qed.

    Lemma lookup_insert_shift {b Γ} {bIn : b ∈ Γ}
          {E : Env (Γ - b)} {v : D b}
          (b' : B) (i : b' ∈ Γ - b) :
      lookup (insert bIn E v) (ctx.shift_var bIn i) = lookup E i.
    Proof.
      induction Γ; destroy bIn; destroy E; destroy i; auto.
      exact (IHΓ _ _ _).
    Qed.

    (* Slower implementation of insert that is easier to reason about. *)
    Definition insert' {Γ : Ctx B} {b} (bIn : b ∈ Γ) (E : Env (Γ - b)) (v : D b) : Env Γ :=
      tabulate (fun x xIn =>
                  match ctx.occurs_check_view bIn xIn with
                  | ctx.Same _      => v
                  | ctx.Diff _ xIn' => lookup E xIn'
                  end).

    (* Slower implementation of remove that is easier to reason about. *)
    Definition remove' {Γ b} (E : Env Γ) (bIn : b ∈ Γ) : Env (Γ - b) :=
      tabulate (fun x xIn => lookup E (ctx.shift_var bIn xIn)).
    Global Arguments remove' {_} b E.

    Lemma lookup_update {Γ} (E : Env Γ) :
      forall {b} (bInΓ : b ∈ Γ) (db : D b),
        lookup (update E bInΓ db) bInΓ = db.
    Proof.
      induction E; intros ? [n e]; try destruct e;
        destruct n; cbn in *; subst; auto.
    Qed.

    Lemma drop_cat {Γ Δ} (δΔ : Env Δ) (δΓ : Env Γ) :
      drop Δ (cat δΓ δΔ) = δΓ.
    Proof. induction δΔ; cbn; auto. Qed.

    Lemma drop_take {Γ Δ} (δ : Env (Γ ▻▻ Δ)) :
      cat (drop Δ δ) (take Δ δ) = δ.
    Proof.
      induction Δ; [easy|].
      destroy δ.
      cbn.
      now rewrite IHΔ.
    Qed.

    Lemma update_update {Γ} (E : Env Γ) :
      forall {b} (bInΓ : b ∈ Γ) (d1 d2 : D b),
        update (update E bInΓ d1) bInΓ d2 =
        update E bInΓ d2.
    Proof.
      induction E; intros ? [n e]; [ contradiction e | destruct n ].
      - destruct e; reflexivity.
      - cbn. intros. f_equal. auto.
    Qed.

    Lemma update_lookup {Γ} (E : Env Γ) :
      forall {b} (bInΓ : b ∈ Γ),
        update E bInΓ (lookup E bInΓ) = E.
    Proof.
      induction E; intros ? [n e]; [ contradiction e | destruct n ].
      - destruct e; reflexivity.
      - cbn. intros. f_equal. auto.
    Qed.

    Lemma lookup_extensional {Γ} (E1 E2 : Env Γ) :
      (forall {b} (bInΓ : b ∈ Γ), lookup E1 bInΓ = lookup E2 bInΓ) ->
      E1 = E2.
    Proof.
      induction E1 as [|Γ E1 HE1 b v1]; destroy E2; [easy|].
      intros Heq. f_equal.
      - eapply HE1. intros b' bInΓ.
        apply (Heq b' (ctx.in_succ bInΓ)).
      - apply (Heq _ ctx.in_zero).
    Qed.

    Lemma lookup_tabulate {Γ} (g : forall b, b ∈ Γ -> D b) :
      forall {b} (bInΓ : b ∈ Γ),
        lookup (tabulate g) bInΓ = g b bInΓ.
    Proof.
      induction Γ; intros ? bIn; destroy bIn; [easy|].
      apply (IHΓ (fun b bInΓ => g b (ctx.in_succ _))).
    Qed.

    Lemma remove_remove' {Γ x} (E : Env Γ) (xIn : x ∈ Γ) :
      remove x E xIn = remove' x E xIn.
    Proof.
      unfold remove'. induction E; destroy xIn; cbn.
      - apply lookup_extensional; intros.
        now rewrite lookup_tabulate.
      - f_equal. apply IHE.
    Qed.

    Lemma insert_insert' {Γ x} (xIn : x ∈ Γ) (E : Env (Γ - x)) (v : D x) :
      insert xIn E v = insert' xIn E v.
    Proof.
      unfold insert'. eapply lookup_extensional. intros b' bIn.
      rewrite lookup_tabulate. destruct ctx.occurs_check_view.
      - now rewrite lookup_insert.
      - now rewrite lookup_insert_shift.
    Qed.

    Lemma lookup_cat_left {Γ1 Γ2 x} (xIn : x ∈ Γ1) (E1 : Env Γ1) (E2 : Env Γ2) :
      lookup (cat E1 E2) (ctx.in_cat_left Γ2 xIn) = lookup E1 xIn.
    Proof. induction E2; auto. Qed.

    Lemma lookup_cat_right {Γ1 Γ2 x} (xIn : x ∈ Γ2) (E1 : Env Γ1) (E2 : Env Γ2) :
      lookup (cat E1 E2) (ctx.in_cat_right xIn) = lookup E2 xIn.
    Proof. induction E2; destroy xIn; cbn; auto. Qed.

    Lemma snoc_eq_rect {Γ1 Γ2 b v} (e : Γ1 = Γ2) (E : Env Γ1) :
      snoc (eq_rect Γ1 Env E Γ2 e) v =
      eq_rect Γ1 (fun Γ => Env (Γ ▻ b)) (snoc E v) Γ2 e.
    Proof. now destruct e. Qed.

    Lemma snoc_eq_rect2 {Γ1 Γ2 b v} (e : Γ1 = Γ2) (E : Env Γ1) :
      snoc (eq_rect Γ1 Env E Γ2 e) v =
      eq_rect (Γ1 ▻ b) Env (snoc E v) (Γ2 ▻ b) (ctx.f_equal_snoc b e).
    Proof. now destruct e. Qed.

    Lemma remove_drop {x Γ Δ} {E : Env (Γ ▻▻ Δ)} (xIn : x ∈ Γ):
      remove x (drop Δ E) xIn = drop Δ (eq_rect ((Γ ▻▻ Δ) - x) Env (remove x E (ctx.in_cat_left Δ xIn)) ((Γ - x) ▻▻ Δ) (ctx.remove_in_cat_left xIn)).
    Proof.
      induction Δ; cbn; [ easy |].
      rewrite IHΔ.
      destroy E.
      cbn.
      change (drop Δ ?E) with (drop Δ (tail (snoc E v))) at 1.
      now rewrite snoc_eq_rect2.
    Qed.

    Lemma remove_cat_right {Γ1 Γ2 x} (xIn : x ∈ Γ2) (E1 : Env Γ1) (E2 : Env Γ2) :
      remove x (cat E1 E2) (ctx.in_cat_right xIn) =
      eq_rect _ _  (cat E1 (remove x E2 xIn)) _ (eq_sym (ctx.remove_in_cat_right xIn)).
    Proof.
      induction xIn using ctx.In_ind; destruct (view E2); cbn; [easy|].
      ctx.tactics.fold_in. rewrite IHxIn, snoc_eq_rect.
      now rewrite ctx.eq_sym_map_snoc_distr, ctx.map_snoc_subst_map.
    Qed.

    Lemma remove_cat_left {Γ1 Γ2 x} (xIn : x ∈ Γ1) (E1 : Env Γ1) (E2 : Env Γ2) :
      remove x (cat E1 E2) (ctx.in_cat_left Γ2 xIn) =
      eq_rect _ _ (cat (remove x E1 xIn) E2) _ (eq_sym (ctx.remove_in_cat_left xIn)).
    Proof.
      induction E2; cbn; [easy|].
      ctx.tactics.fold_in. rewrite IHE2, snoc_eq_rect.
      now rewrite ctx.eq_sym_map_snoc_distr, ctx.map_snoc_subst_map.
    Qed.

    Lemma cat_remove_left {Γ1 Γ2 x} (xIn : x ∈ Γ1) (E1 : Env Γ1) (E2 : Env Γ2) :
      cat (remove x E1 xIn) E2 =
      eq_rect _ _ (remove x (cat E1 E2) _) _ (ctx.remove_in_cat_left xIn).
    Proof.
      induction E2; cbn; [easy|]. ctx.tactics.fold_in.
      now rewrite IHE2, snoc_eq_rect, ctx.map_snoc_subst_map.
    Qed.

    Lemma insert_cat_right {Γ1 Γ2 b} (bIn : b ∈ Γ2) (d : D b) (E1 : Env Γ1) (E2 : Env (Γ2 - b)) :
      cat E1 (insert bIn E2 d) =
      insert (ctx.in_cat_right bIn)
        (eq_rect _ _ (cat E1 E2) _ (eq_sym (ctx.remove_in_cat_right bIn))) d.
    Proof.
      induction bIn using ctx.In_ind; cbn in *; [easy|]. ctx.tactics.fold_in.
      rewrite ctx.eq_sym_map_snoc_distr, ctx.map_snoc_subst_map.
      destruct (view E2) as [E2]. cbn. rewrite <- snoc_eq_rect. cbn.
      now rewrite IHbIn.
    Qed.

    Lemma insert_cat_left {Γ1 Γ2 b} (bIn : b ∈ Γ1) (d : D b) (E1 : Env (Γ1 - b)) (E2 : Env Γ2) :
      cat (insert bIn E1 d) E2 =
      insert (ctx.in_cat_left Γ2 bIn)
        (eq_rect _ _ (cat E1 E2) _ (eq_sym (ctx.remove_in_cat_left bIn))) d.
    Proof.
      induction E2; cbn; [easy|]. ctx.tactics.fold_in.
      rewrite ctx.eq_sym_map_snoc_distr, ctx.map_snoc_subst_map.
      rewrite <- snoc_eq_rect. cbn. now rewrite IHE2.
    Qed.

    Fixpoint abstract (Δ : Ctx B) (r : Type) {struct Δ} : Type :=
      match Δ with
      | []    => r
      | Δ ▻ σ => abstract Δ (D σ -> r)
      end.

    Fixpoint uncurry {Δ : Ctx B} {r : Type} (f : abstract Δ r) (δ : Env Δ) {struct δ} : r :=
      match δ in Env Δ return forall r : Type, abstract Δ r -> r with
      | nil       => fun _ v => v
      | snoc δ db => fun r (f : abstract _ (D _ -> r)) => uncurry f δ db
      end r f.

    Fixpoint curry {Δ : Ctx B} {r : Type} (f : Env Δ -> r) {struct Δ} : abstract Δ r :=
      match Δ return forall r : Type, (Env Δ -> r) -> abstract Δ r with
      | []    => fun r f => f nil
      | Δ ▻ σ => fun r f => @curry Δ (D σ -> r) (fun E d => f (snoc E d))
      end r f.

    Fixpoint Forall (Δ : Ctx B) {struct Δ} : (Env Δ -> Prop) -> Prop :=
      match Δ return (Env Δ -> Prop) -> Prop with
      | []    => fun P => P nil
      | Δ ▻ b => fun P => Forall (fun δ => forall v, P (snoc δ v))
      end.

    Lemma Forall_forall (Δ : Ctx B) (P : Env Δ -> Prop) :
      (Forall P) <-> (forall E : Env Δ, P E).
    Proof.
      split.
      - induction Δ; intros hyp E; destroy E; [easy|].
        apply (IHΔ (fun E => forall v, P (snoc E v))).
        apply hyp.
      - induction Δ; cbn; [easy|]. intros hyp.
        now apply (IHΔ (fun E => forall v, P (snoc E v))).
    Qed.

    Fixpoint Exists (Δ : Ctx B) {struct Δ} : (Env Δ -> Prop) -> Prop :=
      match Δ return (Env Δ -> Prop) -> Prop with
      | []    => fun P => P nil
      | Δ ▻ b => fun P => Exists (fun δ => exists v, P (snoc δ v))
      end.

    Lemma Exists_exists (Δ : Ctx B) (P : Env Δ -> Prop) :
      (Exists P) <-> (exists E : Env Δ, P E).
    Proof.
      split.
      - induction Δ; cbn; intros hyp.
        + now exists nil.
        + apply IHΔ in hyp. destruct hyp as (E & v & hyp).
          now exists (snoc E v).
      - induction Δ; cbn; intros (E & hyp); destroy E; [easy|].
        apply IHΔ. now exists E, v.
    Qed.

    Lemma uncurry_curry (Δ : Ctx B) (r : Type) (f : Env Δ -> r) :
      forall δ, uncurry (curry f) δ = f δ.
    Proof.
      intros δ. revert r f.
      induction δ; cbn; intros; [easy|].
      now rewrite IHδ.
    Qed.

    Definition kvsnoc {Γ} (E : Env Γ) (kv : sigT D) : Env (Γ ▻ projT1 kv) :=
      match kv with
      | existT k v => @snoc Γ E k v
      end.

  End WithDom.

  Arguments Env : clear implicits.
  Arguments abstract : clear implicits.

  Section Map.

    Context {D1 D2 : B -> Set}.
    Variable f : forall b, D1 b -> D2 b.

    Fixpoint map {Γ} (E : Env D1 Γ) : Env D2 Γ :=
      match E with
      | nil       => nil
      | snoc E db => snoc (map E) (f db)
      end.

    Lemma map_cat {Γ1 Γ2} (E1 : Env D1 Γ1) (E2 : Env D1 Γ2) :
      map (cat E1 E2) = cat (map E1) (map E2).
    Proof. induction E2; cbn; congruence. Qed.

    Lemma map_drop {Γ Δ} (EΓΔ : Env D1 (Γ ▻▻ Δ)) :
      map (drop Δ EΓΔ) = drop Δ (map EΓΔ).
    Proof.
      induction Δ; intros; cbn in *.
      - reflexivity.
      - dependent elimination EΓΔ; apply IHΔ.
    Qed.

    Lemma map_update {Γ} (E : Env D1 Γ) :
      forall {b} (bInΓ : b ∈ Γ) (db : D1 b),
        map (update E bInΓ db) = update (map E) bInΓ (f db).
    Proof.
      induction E; intros ? [n e]; try destruct e.
      destruct n; cbn in *; subst; cbn; congruence.
    Qed.

    Lemma map_tabulate {Γ} (g : forall b, b ∈ Γ -> D1 b) :
      map (tabulate g) = tabulate (fun b bInΓ => f (g b bInΓ)).
    Proof.
      induction Γ; intros; cbn in *.
      - reflexivity.
      - f_equal; apply IHΓ.
    Qed.

    Lemma lookup_map {Γ} (E : Env D1 Γ) :
      forall {b} (bInΓ : b ∈ Γ),
        lookup (map E) bInΓ = f (lookup E bInΓ).
    Proof.
      induction E; intros ? [n e]; try destruct e;
        destruct n; cbn in *; subst; auto.
    Qed.

    Lemma remove_map {b Γ} (E : Env D1 Γ) (bIn : b ∈ Γ) :
      map (remove b E bIn) = remove b (map E) bIn.
    Proof.
      rewrite !remove_remove'.
      unfold remove'.
      apply lookup_extensional.
      intros.
      now rewrite lookup_map, !lookup_tabulate, lookup_map.
    Qed.

  End Map.

  Section WithD123.

    Context {D1 D2 D3 : B -> Set}.
    Variable f : forall b, D1 b -> D2 b.
    Variable g : forall b, D2 b -> D3 b.

    Lemma map_map {Γ} (E : Env D1 Γ) :
      map g (map f E) = map (fun b d => g (f d)) E.
    Proof. induction E; cbn; f_equal; assumption. Qed.

  End WithD123.

  Lemma map_id_eq {D : B -> Set} {Γ : Ctx B} (f : forall b, D b -> D b) (E : Env D Γ) (hyp_f : forall b d, f b d = d) :
    map f E = E.
  Proof. induction E; cbn; congruence. Qed.

  Lemma map_id {D : B -> Set} {Γ : Ctx B} (E : Env D Γ) :
    map (fun _ d => d) E = E.
  Proof. now apply map_id_eq. Qed.

  Lemma map_ext {D1 D2 : B -> Set} (f1 f2 : forall b, D1 b -> D2 b) {Γ} (E : Env D1 Γ) :
    (forall b d, f1 b d = f2 b d) -> map f1 E = map f2 E.
  Proof.
    intros HYP.
    apply lookup_extensional.
    intros.
    now rewrite ?lookup_map.
  Qed.

End WithBinding.

Arguments Env {B} D Γ.
Arguments nil {B D}.
Arguments snoc {B%type D%function Γ%ctx} E%env b%ctx & db.
Arguments lookup {B D Γ} E%env [_] x%ctx.
Arguments update {B}%type {D}%function {Γ}%ctx E%env {b}%ctx.
(* Arguments tabulate {_ _} _. *)
(* Arguments tail {_ _ _} / _. *)
Arguments abstract {B} D.

Module notations.

  Open Scope dep_pattern_scope.
  Open Scope env_scope.

  Notation "δ ► ( x ↦ u )" := (snoc δ x u) : env_scope.
  Notation "δ1 '►►' δ2" := (cat δ1 δ2) : env_scope.
  Notation "δ ⟪ x ↦ v ⟫" := (@update _ _ _ δ (x∷_) _ v) : env_scope.
  (* Based on and compatible with ssrnotations, also used in math-comp finmap.  *)
  Notation "e .[ i ]" := (@lookup _ _ _ e _ i)
    (at level 2, left associativity, format "e .[ i ]").
  (* Based on and compatible with the math-comp finmap notation. *)
  Notation "e .[? k ]" := (@lookup _ _ _ e k _)
    (at level 2, k at level 200, format "e .[?  k ]").
  (* Variant of the above if you don't want to specify the type. *)
  Notation "e .[?? x ]" := (@lookup _ _ _ e (x∷_) _)
    (at level 2, x at level 200, only parsing).

  (* #[deprecated(since="20220528", note="Use the specific [env] notation instead.")] *)
  Notation "[ ]" := nil (only parsing) : env_scope.
  Notation "[env]" := nil : env_scope.
  Notation "[ x ]" := (snoc nil _ x) : env_scope.
  Notation "[ E & x ; y ; .. ; z ]" :=
    (snoc .. (snoc (snoc E _ x) _ y) .. _ z)
    (format "[ '['  E  &  x ;  '/' y ;  '/' .. ;  '/' z ']' ]") : env_scope.
  Notation "[ x ; y ; .. ; z ]" :=
    (snoc .. (snoc (snoc nil _ x) _ y) .. _ z)
    (format "[ '[' x ;  '/' y ;  '/' .. ;  '/' z ']' ]") : env_scope.
  Notation "[ 'env' x ]" :=
    (snoc nil _ x)
    (only parsing) : env_scope.
  Notation "[ 'env' x ; y ; .. ; z ]" :=
    (snoc .. (snoc (snoc nil _ x) _ y) .. _ z)
    (only parsing) : env_scope.
    (* (format "[ 'env'  '[' x ;  '/' y ;  '/' .. ;  '/' z ']' ]") : env_scope. *)
  Notation "[ 'nenv' x ]" :=
    (snoc nil (_∷_) x)
    (only parsing) : env_scope.
  Notation "[ 'nenv' x ; y ; .. ; z ]" :=
    (snoc .. (snoc (snoc nil (_∷_) x) (_∷_) y) .. (_∷_) z)
    (only parsing) : env_scope.
    (* (format "[ 'nenv'  '[' x ;  '/' y ;  '/' .. ;  '/' z ']' ]") : env_scope. *)

  (* Notations for NamedEnvs. Unfortunately we cannot (I think) define notations
     with multiple iterators of a recursive pattern, such as for instance the
     names of bindings and the value contained in the environment. Instead we
     define non-recursive notations. *)
  Notation "E .[ k ↦ v ]" :=
    (@env.snoc (Binding _ _) _ _ E k v)
    (at level 2, k at level 50, left associativity, format "E '/' .[ k  ↦  v ]") : env_scope.

  (* Sometimes it is necessary to specify both, the element of the context and
     of the environment in cases where the type-checker would otherwise be
     blocked on a higher-order unification problem. The list-like notations
     below allow the user to do so using sigma types. *)
  Notation "[ 'kv' x ]" := (kvsnoc env.nil x)
    (format "[ 'kv'  x ]") : env_scope.
  Notation "[ 'kv' x ; y ; .. ; z ]" :=
    (kvsnoc .. (kvsnoc (kvsnoc env.nil x) y) .. z)
    (format "[ 'kv'  '[' x ;  '/' y ;  '/' .. ;  '/' z ']' ]") : env_scope.

  (* Notation "'depmatchenv' e 'with' p => rhs 'end'" := *)
  (*   (match view e with p%dep_pattern => rhs end) *)
  (*   (at level 0, p pattern, format *)
  (*    "'[hv' 'depmatchenv'  e  'with'  '/  ' p  =>  '/    ' rhs  '/' 'end' ']'"). *)
  (* Notation "[ 'env' x ; .. ; z ]" := *)
  (*   (dsnoc _ .. (dsnoc _ isNil x) .. z) *)
  (*   (at level 0, format "[ 'env'  x ;  .. ;  z ]") : dep_pattern_scope. *)

End notations.

Local Ltac destroy_env_eq H :=
  lazymatch type of H with
  | @eq (Env _ (ctx.snoc _ _)) _ _ =>
      apply env.inversion_eq_snoc in H;
      let H1 := fresh in
      let H2 := fresh in
      destruct H as [H1 H2];
      destroy_env_eq H1
  | @eq (Env _ ctx.nil) env.nil env.nil => clear H
  | @eq (Env _ ctx.nil) _ _ => idtac
  end.

Ltac destroy x :=
  try (progress hnf in x);
  lazymatch type of x with
  | Env _ []       => destruct (view x)
  | Env _ (_ ▻ _)  => destruct (view x) as [x]; destroy x
  | Env _ (_ ▻▻ _) => let E1 := fresh in
                      let E2 := fresh in
                      destruct (catView x) as [E1 E2];
                      destroy E1; destroy E2
  | _ ∈ []         => destruct (ctx.view x)
  | _ ∈ _ ▻ _      => destruct (ctx.view x)
  | @eq ?A ?y ?z   => let A := eval hnf in A in
                        change_no_check (@eq A y z) in x;
                        destroy_env_eq x
  | _              => idtac
  end.

End env.
Export env (Env).
#[export] Existing Instance env.eq_dec_env.
Bind Scope env_scope with Env.
Import env.

Module envrec.
Section WithBinding.

  Local Set Universe Polymorphism.
  Context {B : Set}.

  Definition EnvRec (D : B -> Type) : Ctx B -> Type :=
    fix EnvRec (σs : Ctx B) {struct σs} : Type :=
      match σs with
      | []     => unit
      | σs ▻ σ => EnvRec σs * D σ
      end%type.

  Section WithD.
    (* TODO: Make this into Type. *)
    Context {D : B -> Set}.

    Fixpoint to_env (σs : Ctx B) {struct σs} : EnvRec D σs -> Env D σs :=
      match σs with
      | []     => fun _ => nil
      | σs ▻ σ => fun e => snoc (to_env σs (fst e)) _ (snd e)
      end.

    Fixpoint of_env (σs : Ctx B) (e : Env D σs) : EnvRec D σs :=
      match e with
      | nil        => tt
      | snoc E σ v => (of_env E, v)
      end.

    Lemma to_of_env (σs : Ctx B) (e : Env D σs) :
      to_env σs (of_env e) = e.
    Proof. induction e; cbn; f_equal; eauto. Qed.

    Lemma of_to_env (σs : Ctx B) (e : EnvRec D σs) :
      of_env (to_env σs e) = e.
    Proof. induction σs; destruct e; cbn; now f_equal. Qed.

    Variable eqd : forall b, D b -> D b -> bool.
    Fixpoint eqb {Γ : Ctx B} : forall (δ1 δ2 : EnvRec D Γ), bool :=
      match Γ with
      | []    => fun _ _ => true
      | _ ▻ b => fun '(E1,d1) '(E2,d2) => eqd d1 d2 &&& eqb E1 E2
      end.

    Lemma of_env_inj (σs : Ctx B) (e1 e2 : Env D σs) :
      of_env e1 = of_env e2 <-> e1 = e2.
    Proof.
      split; intro HYP; [|now f_equal].
      apply (f_equal (@to_env _)) in HYP.
      now rewrite !to_of_env in HYP.
    Qed.

    Lemma to_env_inj (σs : Ctx B) (e1 e2 : EnvRec D σs) :
      to_env _ e1 = to_env _ e2 <-> e1 = e2.
    Proof.
      split; intro HYP; [|now f_equal].
      apply (f_equal (@of_env _)) in HYP.
      now rewrite !of_to_env in HYP.
    Qed.

  End WithD.

End WithBinding.
End envrec.

Notation EnvRec := envrec.EnvRec.
Bind Scope env_scope with EnvRec.

Definition NamedEnv {X T : Set} (D : T -> Set) (Γ : NCtx X T) : Set :=
  Env (fun xt => D (type xt)) Γ.
Bind Scope env_scope with NamedEnv.

Section Named.

  Context {X T : Set} (D : T -> Set) (Δ : NCtx X T).

  Definition abstract_named (r : Type) : Type :=
    abstract (fun xt => D (type xt)) Δ r.

  Definition uncurry_named {r : Type} (f : abstract_named r) (δ : NamedEnv D Δ) : r :=
    uncurry f δ.

  Definition curry_named{r : Type} (f : NamedEnv D Δ -> r) : abstract_named r :=
    curry f.

  Definition ForallNamed : (NamedEnv D Δ -> Prop) -> Prop :=
    @Forall (X ∷ T) (fun xt => D (type xt)) Δ.

End Named.

(* Module nenv. *)
(*   Context {N T : Set}. *)

(*   Section WithD. *)
(*     Context {D : T -> Set}. *)

(*     Inductive NEnv : NCtx N T -> Set := *)
(*     | nil                                               : NEnv ε *)
(*     | snoc {Γ} (E : NEnv Γ) (b : N∷T) (db : D (type b)) : NEnv (Γ ▻ b). *)

(*   End WithD. *)

(* End nenv. *)
