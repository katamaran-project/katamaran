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
(* TO, THE IMPLIED WARRANTgIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR *)
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
     Classes.Morphisms
     Classes.Morphisms_Prop
     Relations.Relation_Definitions
     Program.Basics.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Prelude
     Sep.Logic
     Signature
     Shallow.MonadInterface
     Base.

Import ctx.notations.
Import env.notations.
Import SignatureNotations.

Set Implicit Arguments.

Module Type ShallowMonadInstancesOn
  (Import B : Base)
  (Import SIG : Signature B).

  (* The pure backwards predicate transformer monad. We use this monad in some
     of the definition of primitives that do no need access to the store or heap
     and that can later be lifted to the proper monad. *)
  Definition CPureSpec (A : Type) : Type :=
    (A -> Prop) -> Prop.

  #[export] Instance RCPureSpec : RelM CPureSpec :=
    fun A RA => ((RA ==> impl) ==> impl)%signature.

  (* For counting the different execution paths of the shallow executor we use
     different aliases for False and True to distinguish between them. TRUE
     and FALSE represent execution paths that are pruned, i.e. do not reach
     the end of a function, and FINISH encodes the successful execution
     case. *)
  Definition FALSE : Prop := False.
  Definition TRUE : Prop := True.
  Definition FINISH : Prop := True.
  #[global] Typeclasses Opaque TRUE.
  #[global] Typeclasses Opaque FALSE.
  #[global] Typeclasses Opaque FINISH.

  Module CPureSpec.

    Import CPureSpecM.

    Definition pure {A : Type} : A -> CPureSpec A :=
      fun a Φ => Φ a.

    Definition bind {A B} :
      CPureSpec A -> (A -> CPureSpec B) -> CPureSpec B :=
      fun m f Φ => m (fun a1 => f a1 Φ).
    #[global] Arguments bind {A B} m f _ /.

    #[local] Notation "' x <- ma ;; mb" :=
      (bind ma (fun x => mb))
        (at level 80, x pattern, ma at next level, mb at level 200, right associativity,
          format "' x  <-  ma  ;;  mb").
    #[local] Notation "x <- ma ;; mb" :=
      (bind ma (fun x => mb))
        (at level 80, ma at level 90, mb at level 200, right associativity).
    #[local] Notation "ma ;; mb" := (bind ma (fun _ => mb)).

    Definition error {A} : CPureSpec A :=
      fun Φ => False.
    Definition block {A} : CPureSpec A :=
      fun Φ => True.

    Definition angelic (σ : Ty) : CPureSpec (Val σ) :=
      fun Φ => exists (v : Val σ), Φ v.
    Definition demonic (σ : Ty) : CPureSpec (Val σ) :=
      fun Φ => forall (v : Val σ), Φ v.

    Definition angelic_ctx {N : Set} :
      forall Δ : NCtx N Ty, CPureSpec (NamedEnv Val Δ) :=
      fix rec Δ {struct Δ} :=
        match Δ with
        | []%ctx  => pure []
        | Δ ▻ x∷σ => vs <- rec Δ;;
                     v  <- angelic σ;;
                     pure (vs ► (x∷σ ↦ v))
        end.
    #[global] Arguments angelic_ctx {N} Δ.

    Definition demonic_ctx {N : Set} :
      forall Δ : NCtx N Ty, CPureSpec (NamedEnv Val Δ) :=
      fix rec Δ {struct Δ} :=
        match Δ with
        | []      => pure env.nil
        | Δ ▻ x∷σ => vs <- rec Δ;;
                     v  <- demonic σ;;
                     pure (vs ► (x∷σ ↦ v))
        end%ctx.
    #[global] Arguments demonic_ctx {N} Δ.

    Definition assert_pathcondition : Prop -> CPureSpec unit :=
      fun C Φ => C /\ Φ tt.
    Definition assume_pathcondition : Prop -> CPureSpec unit :=
      fun C Φ => C -> Φ tt.

    Definition assume_formula : Prop -> CPureSpec unit :=
      fun fml => assume_pathcondition fml.
    Definition assert_formula : Prop -> CPureSpec unit :=
      fun fml => assert_pathcondition fml.

    Definition angelic_binary {A} :
      CPureSpec A -> CPureSpec A -> CPureSpec A :=
      fun m1 m2 Φ => m1 Φ \/ m2 Φ.
    Definition demonic_binary {A} :
      CPureSpec A -> CPureSpec A -> CPureSpec A :=
      fun m1 m2 Φ => m1 Φ /\ m2 Φ.

    Definition angelic_list' {A} :
      A -> list A -> CPureSpec A :=
      fix rec d xs :=
        match xs with
        | nil        => pure d
        | cons x xs  => angelic_binary (pure d) (rec x xs)
        end.

    Definition angelic_list {A} (xs : list A) : CPureSpec A :=
      match xs with
      | nil => error
      | cons x xs => angelic_list' x xs
      end.

    Definition demonic_list' {A} :
      A -> list A -> CPureSpec A :=
      fix rec d xs :=
        match xs with
        | nil        => pure d
        | cons x xs  => demonic_binary (pure d) (rec x xs)
        end.

    Definition demonic_list {A} (xs : list A) : CPureSpec A :=
      match xs with
      | nil => block
      | cons x xs => demonic_list' x xs
      end.

    Definition angelic_finite F `{finite.Finite F} : CPureSpec F :=
      angelic_list (finite.enum F).
    #[global] Arguments angelic_finite F {_ _}.

    Definition demonic_finite F `{finite.Finite F} : CPureSpec F :=
      demonic_list (finite.enum F).
    #[global] Arguments demonic_finite F {_ _}.

    Section PatternMatching.

      Context {N : Set}.

      Definition angelic_pattern_match {σ} (pat : @Pattern N σ)
        (v : Val σ) : CPureSpec (MatchResult pat) :=
        pc <- angelic_finite (PatternCase pat);;
        vs <- angelic_ctx (PatternCaseCtx pc) ;;
        _  <- assert_formula (pattern_match_val_reverse pat pc vs = v);;
        pure (existT pc vs).

      Definition demonic_pattern_match {σ} (pat : @Pattern N σ)
        (v : Val σ) : CPureSpec (MatchResult pat) :=
        pc <- demonic_finite (PatternCase pat);;
        vs <- demonic_ctx (PatternCaseCtx pc) ;;
        _  <- assume_formula (pattern_match_val_reverse pat pc vs = v);;
        pure (existT pc vs).

      Definition new_pattern_match {σ} (pat : @Pattern N σ)
        (v : Val σ) : CPureSpec (MatchResult pat) :=
        pure (pattern_match_val pat v).

    End PatternMatching.

    #[export] Instance purespecm : CPureSpecM CPureSpec :=
      {| CPureSpecM.pure                  := @pure;
         CPureSpecM.bind                  := @bind;
         CPureSpecM.error                 := @error;
         CPureSpecM.block                 := @block;
         CPureSpecM.angelic               := @angelic;
         CPureSpecM.demonic               := @demonic;
         CPureSpecM.angelic_ctx           := @angelic_ctx;
         CPureSpecM.demonic_ctx           := @demonic_ctx;
         CPureSpecM.assert_pathcondition  := @assert_pathcondition;
         CPureSpecM.assert_formula        := @assert_formula;
         CPureSpecM.assume_pathcondition  := @assume_pathcondition;
         CPureSpecM.assume_formula        := @assume_formula;
         CPureSpecM.angelic_binary        := @angelic_binary;
         CPureSpecM.demonic_binary        := @demonic_binary;
         CPureSpecM.angelic_pattern_match := @angelic_pattern_match;
         CPureSpecM.demonic_pattern_match := @demonic_pattern_match;
         CPureSpecM.new_pattern_match     := @new_pattern_match;
         CPureSpecM.debug                 := fun _ m => m;
      |}.

    #[global] Arguments CPureSpec.pure {_} _ /.
    #[global] Arguments CPureSpec.error {_} /.
    #[global] Arguments CPureSpec.bind {_ _} _ _ _ /.
    #[global] Arguments CPureSpec.assert_formula _ /.
    #[global] Arguments CPureSpec.assert_pathcondition _ /.
    #[global] Arguments CPureSpec.assume_formula _ /.
    #[global] Arguments CPureSpec.assume_pathcondition _ /.
    #[global] Arguments CPureSpec.angelic_binary {_} _ _ /.
    #[global] Arguments CPureSpec.demonic_binary {_} _ _ /.

    #[local] Instance mon_pure `{RA : relation A} :
      Monotonic (RA ==> RM RA) pure.
    Proof. firstorder. Qed.

    #[local] Instance mon_pure' `{RA : relation A} x :
      Monotonic RA x -> Monotonic (RM RA) (pure x).
    Proof. firstorder. Qed.

    #[local] Instance mon_bind `{RA : relation A, RB : relation B} :
      Monotonic (RM RA ==> (RA ==> RM RB) ==> RM RB) bind.
    Proof.
      intros ? ? rm ? ? rf ? ? rΦ. apply rm.
      intros ? ? ra. apply rf. apply ra. apply rΦ.
    Qed.

    #[export] Instance mon_bind' `{RA : relation A, RB : relation B}
      (m : CPureSpec A) (f : A -> CPureSpec B) :
      Monotonic (RM RA) m -> Monotonic (RA ==> RM RB) f -> Monotonic (RM RB) (bind m f).
    Proof. intros rm rf. eapply mon_bind; eauto. Qed.

    #[local] Instance mon_error `{RA : relation A} :
      Monotonic (RM RA) error.
    Proof. firstorder. Qed.

    #[local] Instance mon_block `{RA : relation A} :
      Monotonic (RM RA) block.
    Proof. firstorder. Qed.

    #[local] Instance mon_angelic {σ} :
      Monotonic (RM eq) (angelic σ).
    Proof. intros ? ? Φ. apply ex_impl_morphism; firstorder. Qed.

    #[local] Instance mon_demonic {σ} :
      Monotonic (RM eq) (demonic σ).
    Proof. intros ? ? Φ. apply all_impl_morphism; firstorder. Qed.

    #[local] Instance mon_angelic_ctx {N : Set} {Δ} :
      Monotonic (RM eq) (@angelic_ctx N Δ).
    Proof.
      induction Δ; cbn.
      - now apply mon_pure.
      - eapply mon_bind. apply IHΔ. intros ? ? ?.
        eapply mon_bind. apply mon_angelic. intros ? ? ?.
        apply mon_pure. now f_equal.
    Qed.

    #[local] Instance mon_demonic_ctx {N : Set} {Δ} :
      Monotonic (RM eq) (@demonic_ctx N Δ).
    Proof.
      induction Δ; cbn.
      - now apply mon_pure.
      - eapply mon_bind. apply IHΔ. intros ? ? ?.
        eapply mon_bind. apply mon_demonic. intros ? ? ?.
        apply mon_pure. now f_equal.
    Qed.

    #[local] Instance mon_assert_formula fml :
      Monotonic (RM eq) (assert_formula fml).
    Proof. firstorder. Qed.

    #[local] Instance mon_assume_formula fml :
      Monotonic (RM eq) (assume_formula fml).
    Proof. firstorder. Qed.

    #[local] Instance mon_angelic_binary `{RA : relation A} m1 m2 :
      Monotonic (RM RA) m1 -> Monotonic (RM RA) m2 ->
      Monotonic (RM RA) (angelic_binary m1 m2).
    Proof. firstorder. Qed.

    #[local] Instance mon_demonic_binary `{RA : relation A} m1 m2 :
      Monotonic (RM RA) m1 -> Monotonic (RM RA) m2 ->
      Monotonic (RM RA) (demonic_binary m1 m2).
    Proof. firstorder. Qed.

    #[export] Instance mon_angelic_list' {A} {x : A} {xs : list A} :
      Monotonic (RM eq) (angelic_list' x xs).
    Proof. revert x; induction xs; cbn; typeclasses eauto. Qed.

    #[export] Instance mon_angelic_list {A} {xs : list A} :
      Monotonic (RM eq) (angelic_list xs).
    Proof. destruct xs; cbn; typeclasses eauto. Qed.

    #[export] Instance mon_demonic_list' {A} {x : A} {xs : list A} :
      Monotonic (RM eq) (demonic_list' x xs).
    Proof. revert x; induction xs; cbn; typeclasses eauto. Qed.

    #[export] Instance mon_demonic_list {A} {xs : list A} :
      Monotonic (RM eq) (demonic_list xs).
    Proof. induction xs; cbn; try typeclasses eauto. Qed.

    #[export] Instance mon_angelic_finite F `{finite.Finite F} :
      Monotonic (RM eq) (angelic_finite F).
    Proof. typeclasses eauto. Qed.

    #[export] Instance mon_demonic_finite F `{finite.Finite F} :
      Monotonic (RM eq) (demonic_finite F).
    Proof. typeclasses eauto. Qed.

    #[local] Instance mon_angelic_pattern_match {N σ} (pat : @Pattern N σ) v :
      Monotonic (RM eq) (@angelic_pattern_match _ _ pat v).
    Proof. typeclasses eauto. Qed.

    #[local] Instance mon_demonic_pattern_match {N σ} (pat : @Pattern N σ) v :
      Monotonic (RM eq) (@demonic_pattern_match _ _ pat v).
    Proof. typeclasses eauto. Qed.

    #[local] Instance mon_new_pattern_match {N σ} (pat : @Pattern N σ) v :
      Monotonic (RM eq) (@new_pattern_match _ _ pat v).
    Proof. typeclasses eauto. Qed.

    #[export] Instance mon_purespecm : MPureSpecM CPureSpec.
    Proof. constructor; try typeclasses eauto. Qed.

    Lemma wp_angelic_ctx {N : Set} {Δ : NCtx N Ty} (POST : NamedEnv Val Δ -> Prop) :
      angelic_ctx Δ POST <-> exists vs : NamedEnv Val Δ, POST vs.
    Proof.
      induction Δ; cbn.
      - split.
        + now exists env.nil.
        + intros [vs ?]. now destruct (env.view vs).
      - destruct b as [x σ]. cbv [angelic bind pure]. split.
        + intros (vs & v & Hwp)%IHΔ.
          now exists (env.snoc vs (x∷σ) v).
        + intros [vs Hwp]. destruct (env.view vs) as [vs v].
          apply IHΔ. now exists vs, v.
    Qed.

    Lemma wp_demonic_ctx {N : Set} {Δ : NCtx N Ty} (POST : NamedEnv Val Δ -> Prop) :
      demonic_ctx Δ POST <-> forall vs : NamedEnv Val Δ, POST vs.
    Proof.
      induction Δ; cbn.
      - split.
        + intros ? vs.
          now destruct (env.view vs).
        + intros Hpost. apply Hpost.
      - destruct b as [x σ]. cbv [demonic bind pure]. split.
        + intros Hwp vs.
          destruct (env.view vs) as [vs v].
          now apply (IHΔ (fun vs => forall v, POST (env.snoc vs _ v))).
        + intros HPost. apply IHΔ. intros. apply HPost.
    Qed.

    Lemma wp_angelic_list' {A} (xs : list A) (POST : A -> Prop) :
      forall d,
        angelic_list' d xs POST <->
          exists x : A, List.In x (cons d xs) /\ POST x.
    Proof.
      induction xs; cbn; intros d.
      - firstorder. now subst.
      - firstorder. left. now subst.
    Qed.

    Lemma wp_angelic_list {A} (xs : list A) (POST : A -> Prop) :
      angelic_list xs POST <->
      exists x : A, List.In x xs /\ POST x.
    Proof. destruct xs; cbn; [firstorder|apply wp_angelic_list']. Qed.

    Lemma wp_demonic_list' {A} (xs : list A) (POST : A -> Prop) :
      forall d,
        demonic_list' d xs POST <->
          forall x : A, List.In x (cons d xs) -> POST x.
    Proof.
      induction xs; cbn; intros d.
      - firstorder. now subst.
      - firstorder. now subst.
    Qed.

    Lemma wp_demonic_list {A} (xs : list A) (POST : A -> Prop) :
      demonic_list xs POST <->
      forall x : A, List.In x xs -> POST x.
    Proof. destruct xs; cbn; [firstorder|apply wp_demonic_list']. Qed.

    Lemma wp_angelic_pattern_match {N σ} (pat : @Pattern N σ) v
      (Φ : MatchResult pat -> Prop) :
      angelic_pattern_match v Φ <-> Φ (pattern_match_val pat v).
    Proof.
      unfold angelic_pattern_match, angelic_finite. cbn.
      rewrite wp_angelic_list. setoid_rewrite wp_angelic_ctx.
      split.
      - intros (pc & Hin & δpc & <- & Hwp).
        now rewrite pattern_match_val_inverse_right.
      - set (mr := pattern_match_val pat v). intros HΦ.
        exists (projT1 mr). split.
        { rewrite <- base.elem_of_list_In. apply finite.elem_of_enum. }
        exists (projT2 mr). split.
        { subst mr. apply pattern_match_val_inverse_left. }
        destruct mr. apply HΦ.
    Qed.

    Lemma wp_demonic_pattern_match {N σ} (pat : @Pattern N σ) v
      (Φ : MatchResult pat -> Prop) :
      demonic_pattern_match v Φ <-> Φ (pattern_match_val pat v).
    Proof.
      unfold demonic_pattern_match, demonic_finite. cbn.
      rewrite wp_demonic_list. setoid_rewrite wp_demonic_ctx.
      split.
      - set (mr := pattern_match_val pat v). intros HΦ.
        specialize (HΦ (projT1 mr)).
        rewrite <- base.elem_of_list_In in HΦ.
        specialize (HΦ (finite.elem_of_enum _) (projT2 mr)).
        specialize (HΦ (pattern_match_val_inverse_left pat v)).
        now destruct mr.
      - intros HΦ pc Hin δpc <-. revert HΦ.
        now rewrite pattern_match_val_inverse_right.
    Qed.

    Lemma wp_assert_eq_env {Δ : Ctx Ty} (δ δ' : Env Val Δ) :
      forall Φ,
        CPureSpecM.assert_eq_env δ δ' Φ <-> δ = δ' /\ Φ tt.
    Proof.
      induction δ; intros Φ; destruct (env.view δ'); cbn.
      - intuition auto.
      - now rewrite IHδ env.inversion_eq_snoc.
    Qed.

    Lemma wp_assert_eq_nenv {N} {Δ : NCtx N Ty} (δ δ' : NamedEnv Val Δ) :
      forall Φ,
        CPureSpecM.assert_eq_nenv δ δ' Φ <-> δ = δ' /\ Φ tt.
    Proof.
      induction δ; intros Φ; destruct (env.view δ'); cbn; unfold NamedEnv.
      - intuition auto.
      - now rewrite IHδ env.inversion_eq_snoc.
    Qed.

    #[local] Set Equations With UIP.

    Lemma wp_assert_eq_chunk (c c' : SCChunk) :
      forall Φ,
        CPureSpecM.assert_eq_chunk c c' Φ
        <-> c = c' /\ Φ tt.
    Proof.
      revert c'. induction c; intros c' Φ; destruct c'; cbn in *;
        (* unfold error, FALSE, assert_formula;  *)
        try (intuition discriminate).
      - destruct eq_dec as [e|n]; cbn.
        + rewrite wp_assert_eq_env. apply and_iff_compat_r'.
          intros ?. destruct e; cbn. split; intros Heq.
          * now f_equal.
          * now dependent elimination Heq.
        + split; try contradiction. intros [Heq Hwp]. apply n.
          now dependent elimination Heq.
      - destruct eq_dec_het as [e|n]; cbn.
        + apply and_iff_compat_r'. intros ?.
          dependent elimination e; cbn.
          split; intros Heq.
          * now f_equal.
          * now dependent elimination Heq.
        + split; try contradiction. intros [Heq Hwp]. apply n.
          now dependent elimination Heq.
      - rewrite IHc1 IHc2. intuition congruence.
      - rewrite IHc1 IHc2. intuition congruence.
    Qed.

  End CPureSpec.
  Export (hints) CPureSpec.

  Definition CHeapSpec (A : Type) : Type :=
    (A -> SCHeap -> Prop) -> SCHeap -> Prop.
  Bind Scope mut_scope with CHeapSpec.

  #[export] Instance RCHeapSpec : RelM CHeapSpec :=
    fun A RA => ((RA ==> SCHeap ::> impl) ==> SCHeap ::> impl)%signature.

  Module CHeapSpec.

    Import CPureSpecM CPureSpecM.notations CHeapSpecM.

    Definition run : CHeapSpec unit -> Prop :=
      fun m => m (fun _ h1 => True) List.nil.

    Definition lift_purespec {A : Type} :
      CPureSpec A -> CHeapSpec A :=
      fun m Φ h0 => m (fun a1 => Φ a1 h0).

    (* Definition map {A B} : (A -> B) -> CHeapSpec A -> CHeapSpec B := *)
    (*   fun f m Φ => m (fun a1 => Φ (f a1)). *)

    Definition bind {A B} : CHeapSpec A -> (A -> CHeapSpec B) -> CHeapSpec B :=
      fun m f Φ => m (fun a1 => f a1 Φ).

    Definition angelic_binary {A} : CHeapSpec A -> CHeapSpec A -> CHeapSpec A :=
      fun m1 m2 Φ h => m1 Φ h \/ m2 Φ h.

    Definition demonic_binary {A} : CHeapSpec A -> CHeapSpec A -> CHeapSpec A :=
      fun m1 m2 Φ h => m1 Φ h /\ m2 Φ h.

    #[global] Arguments CHeapSpec.bind {_ _} _ _ _ /.
    #[global] Arguments CHeapSpec.angelic_binary {_} _ _ /.
    #[global] Arguments CHeapSpec.demonic_binary {_} _ _ /.
    #[global] Arguments CHeapSpec.lift_purespec {_} _ _ /.

    #[export] Instance purespecm : CPureSpecM CHeapSpec :=
      {| CPureSpecM.pure  A a              := lift_purespec (CPureSpecM.pure a);
         CPureSpecM.bind                   := @bind;
         CPureSpecM.error A                := lift_purespec CPureSpecM.error;
         CPureSpecM.block A                := lift_purespec CPureSpecM.block;
         CPureSpecM.angelic σ              := lift_purespec (CPureSpecM.angelic σ);
         CPureSpecM.demonic σ              := lift_purespec (CPureSpecM.demonic σ);
         CPureSpecM.angelic_ctx N Δ        := lift_purespec (CPureSpecM.angelic_ctx Δ);
         CPureSpecM.demonic_ctx N Δ        := lift_purespec (CPureSpecM.demonic_ctx Δ);
         CPureSpecM.assert_pathcondition C := lift_purespec (CPureSpecM.assert_pathcondition C);
         CPureSpecM.assert_formula fml     := lift_purespec (CPureSpecM.assert_formula fml);
         CPureSpecM.assume_pathcondition C := lift_purespec (CPureSpecM.assume_pathcondition C);
         CPureSpecM.assume_formula fml     := lift_purespec (CPureSpecM.assume_formula fml);
         CPureSpecM.angelic_binary         := @angelic_binary;
         CPureSpecM.demonic_binary         := @demonic_binary;
         CPureSpecM.angelic_pattern_match N σ pat v := lift_purespec (CPureSpecM.angelic_pattern_match pat v);
         CPureSpecM.demonic_pattern_match N σ pat v := lift_purespec (CPureSpecM.demonic_pattern_match pat v);
         CPureSpecM.new_pattern_match N σ pat v := lift_purespec (CPureSpecM.new_pattern_match pat v);
         CPureSpecM.debug := fun _ m => m;
      |}.

    Lemma wp_assert_eq_env {Δ : Ctx Ty} (δ δ' : Env Val Δ) (h : SCHeap) :
      forall Φ,
        CPureSpecM.assert_eq_env δ δ' Φ h <-> δ = δ' /\ Φ tt h.
    Proof.
      induction δ; intros Φ; destruct (env.view δ'); cbn.
      - intuition auto.
      - now rewrite IHδ env.inversion_eq_snoc.
    Qed.

    Lemma wp_assert_eq_nenv {N} {Δ : NCtx N Ty} (δ δ' : NamedEnv Val Δ) h :
      forall Φ,
        CPureSpecM.assert_eq_nenv δ δ' Φ h <-> δ = δ' /\ Φ tt h.
    Proof.
      induction δ; intros Φ; destruct (env.view δ'); cbn; unfold NamedEnv.
      - intuition auto.
      - now rewrite IHδ env.inversion_eq_snoc.
    Qed.

    Import CPureSpecM.notations.

    Definition get_heap : CHeapSpec SCHeap :=
      fun Φ h => Φ h h.
    Definition put_heap : SCHeap -> CHeapSpec unit :=
      fun h Φ _ => Φ tt h.

    Definition produce_chunk : SCChunk -> CHeapSpec unit :=
      fun c Φ h => Φ tt (cons c h).

    Definition consume_chunk (c : SCChunk) : CHeapSpec unit :=
      h         <- get_heap ;;
      '(c', h') <- lift_purespec (CPureSpec.angelic_list (heap_extractions h)) ;;
      lift_purespec (assert_eq_chunk c c') ;;
      put_heap h'.

    #[export] Instance heapspecm : CHeapSpecM CHeapSpec :=
      {| CHeapSpecM.produce_chunk := produce_chunk;
         CHeapSpecM.consume_chunk := consume_chunk;
      |}.

    #[export] Instance mon_lift_purespec `{RA : relation A} :
      Monotonic (RM RA ==> RM RA) (lift_purespec).
    Proof. intros ? ? rm ? ? rΦ h. apply rm. intros ? ? ra. now apply rΦ. Qed.

    #[export] Instance mon_lift_purespec' `{RA : relation A} m :
      Monotonic (RM RA) m -> Monotonic (RM RA) (lift_purespec m).
    Proof. intros rm. now apply mon_lift_purespec. Qed.

    (* #[local] Instance mon_map `{RA : relation A, RB : relation B} f m : *)
    (*   Monotonic (RA ==> RB) f -> Monotonic (RM RA) m -> *)
    (*   Monotonic (RM RB) (map f m). *)
    (* Proof. intros rf rm ? ? rΦ. apply rm. intros ? ? ra. apply rΦ, rf, ra. Qed. *)

    #[local] Instance mon_bind `{RA : relation A, RB : relation B} :
      Monotonic (RM RA ==> (RA ==> RM RB) ==> RM RB) bind.
    Proof.
      intros ? ? rm ? ? rf ? ? rΦ. apply rm. intros ? ? ra.
      apply rf. apply ra. intros ? ? rb. apply rΦ, rb.
    Qed.

    #[export] Instance mon_purespecm : MPureSpecM CHeapSpec.
    Proof.
      constructor; cbn - [CPureSpec.purespecm]; try typeclasses eauto.
      - intros * ? ? ra. now apply mon_lift_purespec, mon_pure.
      - intros * rm1 rm2 ? ? rΦ h. apply or_impl_morphism.
        now apply rm1. now apply rm2.
      - intros * rm1 rm2 ? ? rΦ h. apply and_impl_morphism.
        now apply rm1. now apply rm2.
    Qed.

    #[export] Instance mon_get_heap : Monotonic (RM eq) get_heap.
    Proof. firstorder. Qed.

    #[export] Instance mon_put_heap h : Monotonic (RM eq) (put_heap h).
    Proof. firstorder. Qed.

    #[export] Instance mon_heapspecm : MHeapSpecM CHeapSpec.
    Proof.
      constructor.
      - firstorder.
      - intros c.
        eapply mon_bind. apply mon_get_heap. intros h ? <-.
        eapply mon_bind. apply mon_lift_purespec.
        apply CPureSpec.mon_angelic_list. intros [c' h'] ? <-.
        eapply mon_bind.
        apply mon_lift_purespec. apply mon_assert_eq_chunk.
        intros _ _ _.
        apply mon_put_heap.
    Qed.

    Section WithBI.

      Import iris.bi.interface iris.bi.extensions.

      Context {L} {biA : BiAffine L} {PI : PredicateDef L}.

      Lemma wp_consume_chunk (c : SCChunk)
        (Φ : unit -> SCHeap -> Prop) :
        forall h,
          consume_chunk c Φ h ->
          (interpret_scheap h ⊢ interpret_scchunk c ∗
            (∃ h' : SCHeap, interpret_scheap h' ∧ ⌜Φ tt h'⌝))%I.
      Proof.
        intros ?. cbn. rewrite CPureSpec.wp_angelic_list.
        intros ([c' h'] & HIn & H). cbn in H.
        rewrite CPureSpec.wp_assert_eq_chunk in H.
        destruct H as [Heq Hput]. subst. hnf in Hput.
        apply in_heap_extractions in HIn. rewrite HIn.
        apply bi.sep_mono'; [easy|].
        apply bi.exist_intro' with h'.
        apply bi.and_intro; auto.
      Qed.
      #[global] Arguments CHeapSpec.consume_chunk : simpl never.

      Lemma wp_produce_chunk (c : SCChunk) (Φ : unit -> SCHeap -> Prop) h :
        produce_chunk c Φ h ->
        (interpret_scheap h ⊢
           interpret_scchunk c -∗ ∃ h', interpret_scheap h' ∧ ⌜Φ tt h'⌝).
      Proof.
        cbn. intros HΦ. apply wand_sep_adjoint.
        apply bi.exist_intro' with (c :: h), bi.and_intro.
        - now rewrite bi.sep_comm.
        - now apply bi.pure_intro.
      Qed.
      #[global] Arguments CHeapSpec.produce_chunk : simpl never.

      Lemma cconsume_sound {Σ} {ι : Valuation Σ} {asn : Assertion Σ} :
        forall (Φ : unit -> SCHeap -> Prop) h,
          cconsume asn ι Φ h ->
          (interpret_scheap h ⊢ asn.interpret asn ι ∗ ∃ h', interpret_scheap h' ∧ ⌜ Φ tt h' ⌝)%I.
      Proof.
        induction asn; cbn - [inst inst_term]; intros Φ h1.
        - intros [Hfmle HΦ]. rewrite <-bi.emp_sep at 1. apply bi.sep_mono'.
          + rewrite bi.and_emp; auto.
          + apply bi.exist_intro' with h1. apply bi.and_intro; auto.
        - intros ->%wp_consume_chunk. now rewrite interpret_scchunk_inst.
        - intros ->%wp_consume_chunk. now rewrite interpret_scchunk_inst.
        - rewrite CPureSpec.wp_angelic_pattern_match.
          destruct pattern_match_val; auto.
        - intros ->%IHasn1. rewrite -bi.sep_assoc. apply bi.sep_mono'; [easy|].
          apply bi.exist_elim. intros h2. apply bi.pure_elim_r. apply IHasn2.
        - intros [->%IHasn1 | ->%IHasn2]; apply bi.sep_mono'; auto.
        - intros (v & ->%IHasn). apply bi.sep_mono'; [|easy].
          now apply bi.exist_intro' with v.
        - intros HΦ. rewrite bi.emp_sep. apply bi.exist_intro' with h1.
          apply bi.and_intro; auto.
      Qed.

      Lemma cproduce_sound {Σ} {ι : Valuation Σ} {asn : Assertion Σ} :
        forall (Φ : unit -> SCHeap -> Prop) h,
          cproduce asn ι Φ h ->
          (interpret_scheap h ⊢
             asn.interpret asn ι -∗ ∃ h', interpret_scheap h' ∧ ⌜Φ tt h'⌝).
      Proof.
        induction asn; cbn - [CPureSpec.assume_formula inst inst_term]; intros Φ h1.
        - cbn. intros HΦ. rewrite bi.and_emp.
          apply wand_sep_adjoint. rewrite bi.sep_comm. apply wand_sep_adjoint.
          apply bi.pure_elim'. intros Hfml.
          apply wand_sep_adjoint. rewrite bi.True_sep.
          apply bi.exist_intro' with h1.
          apply bi.and_intro; auto.
        - intros ->%wp_produce_chunk; now rewrite interpret_scchunk_inst.
        - intros ->%wp_produce_chunk; now rewrite interpret_scchunk_inst.
        - rewrite CPureSpec.wp_demonic_pattern_match.
          destruct pattern_match_val; auto.
        - intros ->%IHasn1. rewrite -bi.wand_curry. apply bi.wand_mono'; [easy|].
          apply bi.exist_elim. intros h2.
          apply bi.pure_elim_r. apply IHasn2.
        - intros [HΦ1%IHasn1 HΦ2%IHasn2].
          apply wand_sep_adjoint. rewrite bi.sep_or_l.
          apply bi.or_elim; now apply wand_sep_adjoint.
        - intros HΦ.
          apply wand_sep_adjoint. rewrite bi.sep_comm. apply wand_sep_adjoint.
          apply bi.exist_elim. intros v.
          apply wand_sep_adjoint. rewrite bi.sep_comm. apply wand_sep_adjoint.
          apply IHasn, HΦ.
        - intros HΦ. rewrite bi.emp_wand.
          apply bi.exist_intro' with h1.
          apply bi.and_intro. reflexivity.
          now apply bi.pure_intro.
      Qed.

    End WithBI.

  End CHeapSpec.
  Export (hints) CHeapSpec.

  Module Statistics.

    Inductive PropShape : Type :=
    | psfork (P Q : PropShape)
    | psquant (P : PropShape)
    | pspruned
    | psfinish
    | psother.

    Fixpoint shape_to_stats (s : PropShape) : Stats :=
      match s with
      | psfork p q => plus_stats (shape_to_stats p) (shape_to_stats q)
      | psquant p  => shape_to_stats p
      | pspruned   => {| branches := 1; pruned := 1 |}
      | psfinish   => {| branches := 1; pruned := 0 |}
      | psother     => {| branches := 0; pruned := 0 |}
      end.

    (* See: Building a Reification Tactic that Recurses Under Binders *)
    (*          http://adam.chlipala.net/cpdt/html/Cpdt.Reflection.html *)

    (*          This calculates a deeply-embedded PropShape for a given Prop P *)
    (*          for which we can then run shape_to_stats to calculate the *)
    (*          number of different kinds of execution paths. *)
    Ltac reifyProp P :=
      match eval simpl in P with
      | forall (x : ?T), TRUE => pspruned
      | forall (x : ?T), FALSE => pspruned
      | forall (x : ?T), FINISH => psfinish
      | forall (x : ?T), True => psother
      | forall (x : ?T), False => psother
      | forall (x : ?T), @?P1 x /\ @?P2 x =>
          let t1 := reifyProp (forall x : T, P1 x) in
          let t2 := reifyProp (forall x : T, P2 x) in
          constr:(psfork t1 t2)
      | forall (x : ?T), @?P1 x \/ @?P2 x =>
          let t1 := reifyProp (forall x : T, P1 x) in
          let t2 := reifyProp (forall x : T, P2 x) in
          constr:(psfork t1 t2)
      | forall (x : ?T), @?P1 x -> @?P2 x =>
          let t1 := reifyProp (forall x : T, P1 x) in
          let t2 := reifyProp (forall x : T, P2 x) in
          constr:(psfork t1 t2)
      | forall (x : ?T), forall (v : ?U), @?P x v =>
          let t := reifyProp (forall xv : T * U, P (fst xv) (snd xv)) in
          constr:(psquant t)
      | forall (x : ?T), exists (v : ?U), @?P x v =>
          let t := reifyProp (forall xv : T * U, P (fst xv) (snd xv)) in
          constr:(psquant t)
      | forall (x : ?T), _ = _ => psother
      | forall (x : ?T), Z.le _ _ => psother
                                       (* | _ => constr:(sprop P) *)
      end.

    (* This typeclass approach seems to be much faster than the reifyProp *)
    (*       tactic above. *)
    Class ShallowStats (P : Prop) :=
      stats : Stats.
    Arguments stats P {_}.

    (* We make these instances global so that users can simply use the *)
    (*          calc tactic qualified without importing the rest of this module. *)
    #[global] Instance stats_true : ShallowStats TRUE :=
      {| branches := 1; pruned := 1 |}.
    #[global] Instance stats_false : ShallowStats FALSE :=
      {| branches := 1; pruned := 1 |}.
    #[global] Instance stats_finish : ShallowStats FINISH :=
      {| branches := 1; pruned := 0 |}.
    (* We do not count regular True and False towards the statistics *)
    (*          because they do not (should not) represent leaves of the shallow *)
    (*          execution. *)
    #[global] Instance stats_true' : ShallowStats True :=
      {| branches := 0; pruned := 0 |}.
    #[global] Instance stats_false' : ShallowStats False :=
      {| branches := 0; pruned := 0 |}.

    #[global] Instance stats_eq {A} {x y : A} : ShallowStats (x = y) :=
      {| branches := 0; pruned := 0 |}.
    #[global] Instance stats_zle {x y : Z} : ShallowStats (Z.le x y) :=
      {| branches := 0; pruned := 0 |}.

    #[global] Instance stats_and `{ShallowStats P, ShallowStats Q} :
      ShallowStats (P /\ Q) := plus_stats (stats P) (stats Q).
    #[global] Instance stats_or `{ShallowStats P, ShallowStats Q} :
      ShallowStats (P \/ Q) := plus_stats (stats P) (stats Q).
    #[global] Instance stats_impl `{ShallowStats P, ShallowStats Q} :
      ShallowStats (P -> Q) := plus_stats (stats P) (stats Q).

    Axiom undefined : forall A, A.

    #[global] Instance stats_forall {A} {B : A -> Prop} {SP : forall a, ShallowStats (B a)} :
      ShallowStats (forall a : A, B a) := SP (undefined A).
    #[global] Instance stats_exists {A} {B : A -> Prop} {SP : forall a, ShallowStats (B a)} :
      ShallowStats (exists a : A, B a) := SP (undefined A).

  End Statistics.

End ShallowMonadInstancesOn.
