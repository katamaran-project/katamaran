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
  Classes.RelationClasses
  NArith.BinNat
  Program.Basics
  Relations.Relation_Definitions
  ZArith.BinInt.
From Equations Require Import
  Equations.
From Katamaran Require Import
  Prelude
  Base
  Syntax.Assertions
  Syntax.Chunks
  Syntax.Predicates
  Symbolic.Propositions
  Symbolic.Worlds.

Import Katamaran.Sep.Logic (wand_sep_adjoint).
Import ctx.notations.
Import env.notations.
Import SignatureNotations.

Set Implicit Arguments.

(* A copy of [Proper] to be used in monotonicity proofs. Most of the instances
   we define allow for more automation, but are weaker than what one would
   normally use for [Proper] instances, hence the different type class. *)
Section Monotonic.
  Let U := Type.
  Context {A B : U}.

  Class Monotonic (R : relation A) (m : A) : Prop :=
    monotonic_prf : R m m.
End Monotonic.

#[export] Hint Extern 1 (Monotonic _ (match ?p with existT _ _ => _ end)) =>
  destruct p : typeclass_instances.
#[export] Hint Extern 1 (Monotonic _ (match ?p with pair _ _ => _ end)) =>
  destruct p : typeclass_instances.
#[export] Hint Extern 1 (Monotonic _ (match ?p with left _ => _ | right _ => _ end)) =>
  destruct p : typeclass_instances.

#[export] Instance monotonic_eq_elim
  {A B} {MB : relation B} {f : A -> B} :
  (forall a, Monotonic MB (f a)) -> Monotonic (eq ==> MB) f.
Proof. unfold Monotonic. intros pf ? ? <-. auto. Qed.

#[export] Instance monotonic_eq_refl {A} {a : A} :
  Monotonic eq a.
Proof. easy. Qed.

(* Class RelM (M : Type -> Type) := *)
(*   RM : forall {A}, relation A -> relation (M A). *)
(* Arguments RM {_ _ _} _%signature_scope. *)

Module Type ShallowMonadsOn
  (Import B : Base)
  (Import PK : PredicateKit B)
  (Import WR : WorldsMixin B PK)
  (Import AS : AssertionsOn B PK WR)
  (Import SP : SymPropOn B PK WR).

  (* This is used by potentially multiple instances, but ultimately should be
     moved somewhere else. *)
  Section WithBI.

    Import iris.bi.interface iris.bi.extensions iris.bi.derived_laws.

    Context {L} {biA : BiAffine L} {PI : PredicateDef L}.

    Lemma scchunk_duplicate (c : SCChunk) :
      is_duplicable c = true ->
      interpret_scchunk c ⊣⊢@{L} interpret_scchunk c ∗ interpret_scchunk c.
    Proof.
      destruct c; cbn; try discriminate; intros H.
      apply bi.entails_anti_sym.
      - now apply lduplicate.
      - transitivity (luser p vs ∗ emp)%I.
        + apply bi.sep_mono'; auto.
        + now rewrite bi.sep_emp.
    Qed.

    Lemma in_heap_extractions {h : SCHeap} {c1 h1}
      (hyp : List.In (c1 , h1) (heap_extractions h)) :
      interpret_scheap h ⊣⊢@{L} interpret_scchunk c1 ∗ interpret_scheap h1.
    Proof.
      revert c1 h1 hyp.
      induction h; cbn -[is_duplicable]; intros.
      - contradict hyp.
      - destruct hyp as [hyp|hyp].
        + destruct (is_duplicable a) eqn:Heqdup;
            inversion hyp; subst; clear hyp; cbn.
          * rewrite bi.sep_assoc -scchunk_duplicate; auto.
          * reflexivity.
        + cbn in *.
          apply List.in_map_iff in hyp.
          destruct hyp as [[c2 h2] [H1 H2]].
          inversion H1; subst; clear H1; cbn.
          apply IHh in H2; rewrite H2; clear IHh H2.
          rewrite !bi.sep_assoc.
          apply bi.sep_proper; [|easy].
          now rewrite bi.sep_comm.
    Qed.

  End WithBI.

    (* The pure backwards predicate transformer monad. We use this monad in some
     of the definition of primitives that do no need access to the store or heap
     and that can later be lifted to the proper monad. *)
  Definition CPureSpec (A : Type) : Type :=
    (A -> Prop) -> Prop.

  Definition MPureSpec [A] (MA : relation A) : relation (CPureSpec A) :=
    (MA ==> impl) ==> impl.

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

    Definition run : CPureSpec unit -> Prop :=
      fun m => m (fun _ => True).

    Definition pure {A : Type} : A -> CPureSpec A :=
      fun a Φ => Φ a.

    Definition bind {A B} :
      CPureSpec A -> (A -> CPureSpec B) -> CPureSpec B :=
      fun m f Φ => m (fun a1 => f a1 Φ).
    #[global] Arguments bind {A B} m f _ /.

    Module Import notations.
      Notation "' x <- ma ;; mb" :=
        (bind ma (fun x => mb))
          (at level 80, x pattern, ma at next level, mb at level 200, right associativity,
             format "' x  <-  ma  ;;  mb").
      Notation "x <- ma ;; mb" :=
        (bind ma (fun x => mb))
          (at level 80, ma at level 90, mb at level 200, right associativity).
      Notation "ma ;; mb" := (bind ma (fun _ => mb)).
    End notations.

    Definition block {A} : CPureSpec A :=
      fun Φ => TRUE.
    Definition error {A} : CPureSpec A :=
      fun Φ => FALSE.

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

    Definition assert_formula : Prop -> CPureSpec unit :=
      fun fml => assert_pathcondition fml.
    Definition assume_formula : Prop -> CPureSpec unit :=
      fun fml => assume_pathcondition fml.

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
      #[global] Arguments angelic_pattern_match {σ} pat v.

      Definition demonic_pattern_match {σ} (pat : @Pattern N σ)
        (v : Val σ) : CPureSpec (MatchResult pat) :=
        pc <- demonic_finite (PatternCase pat);;
        vs <- demonic_ctx (PatternCaseCtx pc) ;;
        _  <- assume_formula (pattern_match_val_reverse pat pc vs = v);;
        pure (existT pc vs).
      #[global] Arguments demonic_pattern_match {σ} pat v.

      Definition new_pattern_match {σ} (pat : @Pattern N σ)
        (v : Val σ) : CPureSpec (MatchResult pat) :=
        pure (pattern_match_val pat v).
      #[global] Arguments new_pattern_match {σ} pat v _.

    End PatternMatching.

    Definition debug {A} : CPureSpec A -> CPureSpec A :=
      fun m => m.

    (* #[export] Instance purespecm : CPureSpecM CPureSpec := *)
    (*   {| CPureSpecM.pure                  := @pure; *)
    (*      CPureSpecM.bind                  := @bind; *)
    (*      CPureSpecM.error                 := @error; *)
    (*      CPureSpecM.block                 := @block; *)
    (*      CPureSpecM.angelic               := @angelic; *)
    (*      CPureSpecM.demonic               := @demonic; *)
    (*      CPureSpecM.angelic_ctx           := @angelic_ctx; *)
    (*      CPureSpecM.demonic_ctx           := @demonic_ctx; *)
    (*      CPureSpecM.assert_pathcondition  := @assert_pathcondition; *)
    (*      CPureSpecM.assert_formula        := @assert_formula; *)
    (*      CPureSpecM.assume_pathcondition  := @assume_pathcondition; *)
    (*      CPureSpecM.assume_formula        := @assume_formula; *)
    (*      CPureSpecM.angelic_binary        := @angelic_binary; *)
    (*      CPureSpecM.demonic_binary        := @demonic_binary; *)
    (*      CPureSpecM.angelic_pattern_match := @angelic_pattern_match; *)
    (*      CPureSpecM.demonic_pattern_match := @demonic_pattern_match; *)
    (*      CPureSpecM.new_pattern_match     := @new_pattern_match; *)
    (*      CPureSpecM.debug                 := fun _ m => m; *)
    (*   |}. *)

    (* #[global] Arguments CPureSpec.pure {_} _ /. *)
    (* #[global] Arguments CPureSpec.error {_} /. *)
    (* #[global] Arguments CPureSpec.bind {_ _} _ _ _ /. *)
    (* #[global] Arguments CPureSpec.assert_formula _ /. *)
    (* #[global] Arguments CPureSpec.assert_pathcondition _ /. *)
    (* #[global] Arguments CPureSpec.assume_formula _ /. *)
    (* #[global] Arguments CPureSpec.assume_pathcondition _ /. *)
    (* #[global] Arguments CPureSpec.angelic_binary {_} _ _ /. *)
    (* #[global] Arguments CPureSpec.demonic_binary {_} _ _ /. *)

    Lemma mon_pure' `{MA : relation A} :
      Monotonic (MA ==> MPureSpec MA) pure.
    Proof. firstorder. Qed.

    #[export] Instance mon_pure `{MA : relation A} x :
      Monotonic MA x -> Monotonic (MPureSpec MA) (pure x).
    Proof. firstorder. Qed.

    Lemma mon_bind' `{MA : relation A, RB : relation B} :
      Monotonic (MPureSpec MA ==> (MA ==> MPureSpec RB) ==> MPureSpec RB) bind.
    Proof.
      intros ? ? rm ? ? rf ? ? rΦ. apply rm.
      intros ? ? ra. apply rf. apply ra. apply rΦ.
    Qed.

    #[export] Instance mon_bind `{MA : relation A, RB : relation B}
      (m : CPureSpec A) (f : A -> CPureSpec B) :
      Monotonic (MPureSpec MA) m ->
      Monotonic (MA ==> MPureSpec RB) f ->
      Monotonic (MPureSpec RB) (bind m f).
    Proof. intros rm rf. eapply mon_bind'; eauto. Qed.

    #[export] Instance mon_error `{MA : relation A} :
      Monotonic (MPureSpec MA) error.
    Proof. firstorder. Qed.
    #[export] Instance mon_block `{MA : relation A} :
      Monotonic (MPureSpec MA) block.
    Proof. firstorder. Qed.

    #[export] Instance mon_angelic {σ} :
      Monotonic (MPureSpec eq) (angelic σ).
    Proof. intros ? ? Φ. apply ex_impl_morphism; firstorder. Qed.
    #[export] Instance mon_demonic {σ} :
      Monotonic (MPureSpec eq) (demonic σ).
    Proof. intros ? ? Φ. apply all_impl_morphism; firstorder. Qed.

    #[export] Instance mon_angelic_ctx {N : Set} {Δ} :
      Monotonic (MPureSpec eq) (@angelic_ctx N Δ).
    Proof. induction Δ; cbn [angelic_ctx]; typeclasses eauto. Qed.
    #[export] Instance mon_demonic_ctx {N : Set} {Δ} :
      Monotonic (MPureSpec eq) (@demonic_ctx N Δ).
    Proof. induction Δ; cbn [demonic_ctx]; typeclasses eauto. Qed.

    #[export] Instance mon_assert_formula fml :
      Monotonic (MPureSpec eq) (assert_formula fml).
    Proof. firstorder. Qed.
    #[export] Instance mon_assume_formula fml :
      Monotonic (MPureSpec eq) (assume_formula fml).
    Proof. firstorder. Qed.

    #[export] Instance mon_angelic_binary `{MA : relation A} m1 m2 :
      Monotonic (MPureSpec MA) m1 -> Monotonic (MPureSpec MA) m2 ->
      Monotonic (MPureSpec MA) (angelic_binary m1 m2).
    Proof. firstorder. Qed.
    #[export] Instance mon_demonic_binary `{MA : relation A} m1 m2 :
      Monotonic (MPureSpec MA) m1 -> Monotonic (MPureSpec MA) m2 ->
      Monotonic (MPureSpec MA) (demonic_binary m1 m2).
    Proof. firstorder. Qed.

    #[export] Instance mon_angelic_list' {A} {x : A} {xs : list A} :
      Monotonic (MPureSpec eq) (angelic_list' x xs).
    Proof. revert x; induction xs; cbn [angelic_list']; typeclasses eauto. Qed.
    #[export] Instance mon_angelic_list {A} {xs : list A} :
      Monotonic (MPureSpec eq) (angelic_list xs).
    Proof. destruct xs; typeclasses eauto. Qed.
    #[export] Instance mon_demonic_list' {A} {x : A} {xs : list A} :
      Monotonic (MPureSpec eq) (demonic_list' x xs).
    Proof. revert x; induction xs; cbn [demonic_list']; typeclasses eauto. Qed.
    #[export] Instance mon_demonic_list {A} {xs : list A} :
      Monotonic (MPureSpec eq) (demonic_list xs).
    Proof. induction xs; typeclasses eauto. Qed.

    #[export] Instance mon_angelic_finite F `{finite.Finite F} :
      Monotonic (MPureSpec eq) (angelic_finite F).
    Proof. typeclasses eauto. Qed.
    #[export] Instance mon_demonic_finite F `{finite.Finite F} :
      Monotonic (MPureSpec eq) (demonic_finite F).
    Proof. typeclasses eauto. Qed.

    #[export] Instance mon_angelic_pattern_match {N σ} (pat : @Pattern N σ) v :
      Monotonic (MPureSpec eq) (@angelic_pattern_match _ _ pat v).
    Proof. typeclasses eauto. Qed.
    #[export] Instance mon_demonic_pattern_match {N σ} (pat : @Pattern N σ) v :
      Monotonic (MPureSpec eq) (@demonic_pattern_match _ _ pat v).
    Proof. typeclasses eauto. Qed.

    #[export] Instance mon_new_pattern_match {N σ} (pat : @Pattern N σ) v :
      Monotonic (MPureSpec eq) (@new_pattern_match _ _ pat v).
    Proof. typeclasses eauto. Qed.

    #[export] Instance mon_debug `{MA : relation A} m :
      Monotonic (MPureSpec MA) m -> Monotonic (MPureSpec MA) (debug m).
    Proof. now unfold debug. Qed.
    #[global] Typeclasses Opaque debug.

    (* #[export] Instance mon_purespecm : MPureSpecM CPureSpec. *)
    (* Proof. constructor; try typeclasses eauto. Qed. *)

    (* The paper uses asserted equalities between multiple types, but the
       symbolic executor can in fact only assert equalities between symbolic
       terms. We mirror the structure of the symbolic execution and also
       traverse (the statically known parts) of other data structures. *)
    Equations(noeqns) assert_eq_env [Δ : Ctx Ty]
      (δ δ' : Env Val Δ) : CPureSpec unit :=
      assert_eq_env env.nil          env.nil            := pure tt;
      assert_eq_env (env.snoc δ _ t) (env.snoc δ' _ t') :=
        bind (assert_eq_env δ δ') (fun _ => assert_formula (t = t')).

    Equations(noeqns) assert_eq_nenv {N : Set} [Δ : NCtx N Ty]
      (δ δ' : NamedEnv Val Δ) : CPureSpec unit :=
      assert_eq_nenv env.nil          env.nil            := pure tt;
      assert_eq_nenv (env.snoc δ _ t) (env.snoc δ' _ t') :=
        bind (assert_eq_nenv δ δ') (fun _ => assert_formula (t = t')).

    Equations(noeqns) assume_eq_env [Δ : Ctx Ty]
      (δ δ' : Env Val Δ) : CPureSpec unit :=
      assume_eq_env env.nil          env.nil            := pure tt;
      assume_eq_env (env.snoc δ _ t) (env.snoc δ' _ t') :=
        bind (assume_eq_env δ δ') (fun _ => assume_formula (t = t')).

    Equations(noeqns) assume_eq_nenv {N : Set} [Δ : NCtx N Ty]
      (δ δ' : NamedEnv Val Δ) : CPureSpec unit :=
      assume_eq_nenv env.nil          env.nil            := pure tt;
      assume_eq_nenv (env.snoc δ _ t) (env.snoc δ' _ t') :=
        bind (assume_eq_nenv δ δ') (fun _ => assume_formula (t = t')).

    Fixpoint assert_eq_chunk (c1 c2 : SCChunk) : CPureSpec unit :=
      match c1 , c2 with
      | scchunk_user p1 vs1 , scchunk_user p2 vs2 =>
          match eq_dec p1 p2 with
          | left e => assert_eq_env (eq_rect p1 (fun p => Env Val (𝑯_Ty p)) vs1 p2 e) vs2
          | right _ => error
          end
      | scchunk_ptsreg r1 v1 , scchunk_ptsreg r2 v2 =>
          match eq_dec_het r1 r2 with
          | left e => assert_formula (eq_rect _ Val v1 _ (f_equal projT1 e) = v2)
          | right _ => error
          end
      | scchunk_conj c11 c12 , scchunk_conj c21 c22 =>
          assert_eq_chunk c11 c21 ;; assert_eq_chunk c12 c22
      | scchunk_wand c11 c12 , scchunk_wand c21 c22 =>
          assert_eq_chunk c11 c21 ;; assert_eq_chunk c12 c22
      | _ , _ => error
      end.

    #[export] Instance mon_assert_eq_env {Δ E1 E2} :
      Monotonic (MPureSpec eq) (@assert_eq_env Δ E1 E2).
    Proof. induction E1; env.destroy E2; cbn; typeclasses eauto. Qed.

    #[export] Instance mon_assert_eq_nenv {N Δ E1 E2} :
      Monotonic (MPureSpec eq) (@assert_eq_nenv N Δ E1 E2).
    Proof. induction E1; env.destroy E2; cbn; typeclasses eauto. Qed.

    #[export] Instance mon_assume_eq_env {Δ E1 E2} :
      Monotonic (MPureSpec eq) (@assume_eq_env Δ E1 E2).
    Proof. induction E1; env.destroy E2; cbn; typeclasses eauto. Qed.

    #[export] Instance mon_assume_eq_nenv {N Δ E1 E2} :
      Monotonic (MPureSpec eq) (@assume_eq_nenv N Δ E1 E2).
    Proof. induction E1; env.destroy E2; cbn; typeclasses eauto. Qed.

    #[export] Instance mon_assert_eq_chunk {c1 c2} :
      Monotonic (MPureSpec eq) (@assert_eq_chunk c1 c2).
    Proof. revert c2; induction c1; intros []; cbn; typeclasses eauto. Qed.

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
      angelic_pattern_match pat v Φ <-> Φ (pattern_match_val pat v).
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
      demonic_pattern_match pat v Φ <-> Φ (pattern_match_val pat v).
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
        assert_eq_env δ δ' Φ <-> δ = δ' /\ Φ tt.
    Proof.
      induction δ; intros Φ; destruct (env.view δ'); cbn.
      - intuition auto.
      - rewrite IHδ, env.inversion_eq_snoc.
        now unfold assert_formula, assert_pathcondition.
    Qed.

    Lemma wp_assert_eq_nenv {N} {Δ : NCtx N Ty} (δ δ' : NamedEnv Val Δ) :
      forall Φ,
        assert_eq_nenv δ δ' Φ <-> δ = δ' /\ Φ tt.
    Proof.
      induction δ; intros Φ; destruct (env.view δ'); cbn; unfold NamedEnv.
      - intuition auto.
      - rewrite IHδ, env.inversion_eq_snoc.
        now unfold assert_formula, assert_pathcondition.
    Qed.

    #[local] Set Equations With UIP.

    Lemma wp_assert_eq_chunk (c c' : SCChunk) :
      forall Φ,
        assert_eq_chunk c c' Φ <-> c = c' /\ Φ tt.
    Proof.
      revert c'. induction c; intros c' Φ; destruct c'; cbn in *;
        unfold error, FALSE; try (intuition discriminate).
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
      - rewrite IHc1, IHc2. intuition congruence.
      - rewrite IHc1, IHc2. intuition congruence.
    Qed.

  End CPureSpec.
  Export (hints) CPureSpec.

  Definition CHeapSpec (A : Type) : Type :=
    (A -> SCHeap -> Prop) -> SCHeap -> Prop.

  Definition MHeapSpec [A] (MA : relation A) : relation (CHeapSpec A) :=
    (MA ==> SCHeap ::> impl) ==> SCHeap ::> impl.

  Module CHeapSpec.

    Definition run : CHeapSpec unit -> Prop :=
      fun m => m (fun _ h1 => True) List.nil.

    Definition lift_purespec {A : Type} :
      CPureSpec A -> CHeapSpec A :=
      fun m Φ h0 => m (fun a1 => Φ a1 h0).

    Definition bind {A B} : CHeapSpec A -> (A -> CHeapSpec B) -> CHeapSpec B :=
      fun m f Φ h => m (fun a1 => f a1 Φ) h.

    Definition angelic_binary {A} : CHeapSpec A -> CHeapSpec A -> CHeapSpec A :=
      fun m1 m2 Φ h => m1 Φ h \/ m2 Φ h.

    Definition demonic_binary {A} : CHeapSpec A -> CHeapSpec A -> CHeapSpec A :=
      fun m1 m2 Φ h => m1 Φ h /\ m2 Φ h.

    Module Import notations.
      Notation "' x <- ma ;; mb" :=
        (bind ma (fun x => mb))
          (at level 80, x pattern, ma at next level, mb at level 200, right associativity,
             format "' x  <-  ma  ;;  mb").
      Notation "x <- ma ;; mb" :=
        (bind ma (fun x => mb))
          (at level 80, ma at level 90, mb at level 200, right associativity).
      Notation "ma ;; mb" := (bind ma (fun _ => mb)).
    End notations.

    Definition pure {A} a := lift_purespec (@CPureSpec.pure A a).
    (* Definition error A                := lift_purespec (@CPureSpec.error A). *)
    (* Definition block A                := lift_purespec (@CPureSpec.block A). *)
    (* Definition angelic σ              := lift_purespec (@CPureSpec.angelic σ). *)
    (* Definition demonic σ              := lift_purespec (@CPureSpec.demonic σ). *)
    (* Definition angelic_ctx N Δ        := lift_purespec (@CPureSpec.angelic_ctx N Δ). *)
    (* Definition demonic_ctx N Δ        := lift_purespec (@CPureSpec.demonic_ctx N Δ). *)
    (* Definition assert_pathcondition C := lift_purespec (@CPureSpec.assert_pathcondition C). *)
    (* Definition assert_formula F       := lift_purespec (@CPureSpec.assert_formula F). *)
    (* Definition assume_pathcondition C := lift_purespec (@CPureSpec.assume_pathcondition C). *)
    (* Definition assume_formula F       := lift_purespec (@CPureSpec.assume_formula F). *)
    (* Definition angelic_pattern_match N σ pat v := lift_purespec (@CPureSpec.angelic_pattern_match N σ pat v). *)
    (* Definition demonic_pattern_match N σ pat v := lift_purespec (@CPureSpec.demonic_pattern_match N σ pat v). *)
    (* Definition new_pattern_match N σ pat v     := lift_purespec (@CPureSpec.new_pattern_match N σ pat v). *)
    Definition debug {A} : CHeapSpec A -> CHeapSpec A :=
      fun m => m.
    (* #[global] Arguments angelic_ctx {N} Δ. *)
    (* #[global] Arguments demonic_ctx {N} Δ. *)
    (* #[global] Arguments angelic_pattern_match {N σ} pat v _. *)
    (* #[global] Arguments demonic_pattern_match {N σ} pat v _. *)
    (* #[global] Arguments new_pattern_match {N σ} pat v _. *)

    Lemma mon_pure' `{MA : relation A} :
      Monotonic (MA ==> MHeapSpec MA) pure.
    Proof. firstorder. Qed.

    #[export] Instance mon_pure `{MA : relation A} x :
      Monotonic MA x -> Monotonic (MHeapSpec MA) (pure x).
    Proof. firstorder. Qed.

    Lemma mon_bind' `{MA : relation A, RB : relation B} :
      Monotonic (MHeapSpec MA ==> (MA ==> MHeapSpec RB) ==> MHeapSpec RB) bind.
    Proof.
      intros ? ? rm ? ? rf ? ? rΦ. apply rm. intros ? ? ra.
      apply rf. apply ra. intros ? ? rb. apply rΦ, rb.
    Qed.

    #[export] Instance mon_bind `{MA : relation A, RB : relation B}
      (m : CHeapSpec A) (f : A -> CHeapSpec B) :
      Monotonic (MHeapSpec MA) m ->
      Monotonic (MA ==> MHeapSpec RB) f ->
      Monotonic (MHeapSpec RB) (bind m f).
    Proof. intros rm rf. eapply mon_bind'; eauto. Qed.

    Lemma mon_lift_purespec' `{MA : relation A} :
      Monotonic (MPureSpec MA ==> MHeapSpec MA) (lift_purespec).
    Proof. intros ? ? rm ? ? rΦ h. apply rm. intros ? ? ra. now apply rΦ. Qed.

    #[export] Instance mon_lift_purespec `{MA : relation A} m :
      Monotonic (MPureSpec MA) m -> Monotonic (MHeapSpec MA) (lift_purespec m).
    Proof. intros rm. now apply mon_lift_purespec'. Qed.

    #[export] Instance mon_angelic_binary `{MA : relation A} m1 m2 :
      Monotonic (MHeapSpec MA) m1 -> Monotonic (MHeapSpec MA) m2 ->
      Monotonic (MHeapSpec MA) (angelic_binary m1 m2).
    Proof. firstorder. Qed.

    #[export] Instance mon_demonic_binary `{MA : relation A} m1 m2 :
      Monotonic (MHeapSpec MA) m1 -> Monotonic (MHeapSpec MA) m2 ->
      Monotonic (MHeapSpec MA) (demonic_binary m1 m2).
    Proof. firstorder. Qed.

    #[export] Instance mon_debug `{MA : relation A} m :
      Monotonic (MHeapSpec MA) m -> Monotonic (MHeapSpec MA) (debug m).
    Proof. now unfold debug. Qed.
    #[global] Typeclasses Opaque debug.

    (* #[export] Instance purespecm : CPureSpecM CHeapSpec := *)
    (*   {| CPureSpecM.pure  A a              := lift_purespec (CPureSpecM.pure a); *)
    (*      CPureSpecM.bind                   := @bind; *)
    (*      CPureSpecM.error A                := lift_purespec CPureSpecM.error; *)
    (*      CPureSpecM.block A                := lift_purespec CPureSpecM.block; *)
    (*      CPureSpecM.angelic σ              := lift_purespec (CPureSpecM.angelic σ); *)
    (*      CPureSpecM.demonic σ              := lift_purespec (CPureSpecM.demonic σ); *)
    (*      CPureSpecM.angelic_ctx N Δ        := lift_purespec (CPureSpecM.angelic_ctx Δ); *)
    (*      CPureSpecM.demonic_ctx N Δ        := lift_purespec (CPureSpecM.demonic_ctx Δ); *)
    (*      CPureSpecM.assert_pathcondition C := lift_purespec (CPureSpecM.assert_pathcondition C); *)
    (*      CPureSpecM.assert_formula fml     := lift_purespec (CPureSpecM.assert_formula fml); *)
    (*      CPureSpecM.assume_pathcondition C := lift_purespec (CPureSpecM.assume_pathcondition C); *)
    (*      CPureSpecM.assume_formula fml     := lift_purespec (CPureSpecM.assume_formula fml); *)
    (*      CPureSpecM.angelic_binary         := @angelic_binary; *)
    (*      CPureSpecM.demonic_binary         := @demonic_binary; *)
    (*      CPureSpecM.angelic_pattern_match N σ pat v := lift_purespec (CPureSpecM.angelic_pattern_match pat v); *)
    (*      CPureSpecM.demonic_pattern_match N σ pat v := lift_purespec (CPureSpecM.demonic_pattern_match pat v); *)
    (*      CPureSpecM.new_pattern_match N σ pat v := lift_purespec (CPureSpecM.new_pattern_match pat v); *)
    (*      CPureSpecM.debug := fun _ m => m; *)
    (*   |}. *)

    (* Lemma wp_assert_eq_env {Δ : Ctx Ty} (δ δ' : Env Val Δ) (h : SCHeap) : *)
    (*   forall Φ, *)
    (*     CPureSpecM.assert_eq_env δ δ' Φ h <-> δ = δ' /\ Φ tt h. *)
    (* Proof. *)
    (*   induction δ; intros Φ; destruct (env.view δ'); cbn. *)
    (*   - intuition auto. *)
    (*   - now rewrite IHδ env.inversion_eq_snoc. *)
    (* Qed. *)

    (* Lemma wp_assert_eq_nenv {N} {Δ : NCtx N Ty} (δ δ' : NamedEnv Val Δ) h : *)
    (*   forall Φ, *)
    (*     CPureSpecM.assert_eq_nenv δ δ' Φ h <-> δ = δ' /\ Φ tt h. *)
    (* Proof. *)
    (*   induction δ; intros Φ; destruct (env.view δ'); cbn; unfold NamedEnv. *)
    (*   - intuition auto. *)
    (*   - now rewrite IHδ env.inversion_eq_snoc. *)
    (* Qed. *)

    (* Import CPureSpecM.notations. *)

    Definition get_heap : CHeapSpec SCHeap :=
      fun Φ h => Φ h h.
    Definition put_heap : SCHeap -> CHeapSpec unit :=
      fun h Φ _ => Φ tt h.

    #[export] Instance mon_get_heap : Monotonic (MHeapSpec eq) get_heap.
    Proof. firstorder. Qed.

    #[export] Instance mon_put_heap h : Monotonic (MHeapSpec eq) (put_heap h).
    Proof. firstorder. Qed.

    Definition produce_chunk : SCChunk -> CHeapSpec unit :=
      fun c Φ h => Φ tt (cons c h).

    Definition consume_chunk (c : SCChunk) : CHeapSpec unit :=
      h         <- get_heap ;;
      '(c', h') <- lift_purespec (CPureSpec.angelic_list (heap_extractions h)) ;;
      lift_purespec (CPureSpec.assert_eq_chunk c c') ;;
      put_heap h'.

    #[export] Instance mon_produce_chunk c : Monotonic (MHeapSpec eq) (produce_chunk c).
    Proof. firstorder. Qed.
    #[export] Instance mon_consume_chunk c : Monotonic (MHeapSpec eq) (consume_chunk c).
    Proof. unfold consume_chunk. typeclasses eauto. Qed.

    Fixpoint cproduce {Σ} (asn : Assertion Σ) (ι : Valuation Σ) : CHeapSpec unit :=
      match asn with
      | asn.formula fml =>
          lift_purespec (CPureSpec.assume_formula (instprop fml ι))
      | asn.chunk c =>
          produce_chunk (inst c ι)
      | asn.chunk_angelic c =>
          produce_chunk (inst c ι)
      | asn.pattern_match s pat rhs =>
          '(existT pc δpc) <- lift_purespec (CPureSpec.demonic_pattern_match pat (inst s ι)) ;;
          cproduce (rhs pc) (ι ►► δpc)
      | asn.sep a1 a2 =>
          _ <- cproduce a1 ι ;;
          cproduce a2 ι
      | asn.or a1 a2 =>
          demonic_binary (cproduce a1 ι) (cproduce a2 ι)
      | asn.exist ς τ a =>
          t <- lift_purespec (CPureSpec.demonic τ) ;;
          cproduce a (env.snoc ι (ς∷τ) t)
      | asn.debug =>
          debug (pure tt)
      end.

    Fixpoint cconsume {Σ} (asn : Assertion Σ) (ι : Valuation Σ) : CHeapSpec unit :=
      match asn with
      | asn.formula fml =>
          lift_purespec (CPureSpec.assert_formula (instprop fml ι))
      | asn.chunk c =>
          consume_chunk (inst c ι)
      | asn.chunk_angelic c =>
          consume_chunk (inst c ι)
      | asn.pattern_match s pat rhs =>
          '(existT pc δpc) <- lift_purespec (CPureSpec.angelic_pattern_match pat (inst s ι)) ;;
          cconsume (rhs pc) (ι ►► δpc)
      | asn.sep a1 a2 =>
          _ <- cconsume a1 ι ;;
          cconsume a2 ι
      | asn.or a1 a2 =>
          angelic_binary (cconsume a1 ι) (cconsume a2 ι)
      | asn.exist ς τ a =>
          t <- lift_purespec (CPureSpec.angelic τ) ;;
          cconsume a (env.snoc ι (ς∷τ) t)
      | asn.debug =>
          debug (pure tt)
      end.

    Definition ccall_contract [Δ τ] (c : SepContract Δ τ) (args : CStore Δ) : CHeapSpec (Val τ) :=
      match c with
      | MkSepContract _ _ Σe δ req result ens =>
          ι <- lift_purespec (CPureSpec.angelic_ctx Σe) ;;
          lift_purespec (CPureSpec.assert_eq_nenv (inst δ ι) args) ;;
          cconsume req ι ;;
          v <- lift_purespec (CPureSpec.demonic τ) ;;
          cproduce ens (env.snoc ι (result∷τ) v) ;;
          pure v
      end.

    Definition ccall_lemma [Δ] (lem : Lemma Δ) (vs : CStore Δ) : CHeapSpec unit :=
      match lem with
      | MkLemma _ Σe δ req ens =>
          ι <- lift_purespec (CPureSpec.angelic_ctx Σe) ;;
          lift_purespec (CPureSpec.assert_eq_nenv (inst δ ι) vs) ;;
          cconsume req ι ;;
          cproduce ens ι
      end.

    (* Context {relM : RelM M} {mpureM : MHeapSpecM M} {mheapM : MHeapSpecM M}. *)

    #[export] Instance mon_produce {Σ} (asn : Assertion Σ) ι :
      Monotonic (MHeapSpec eq) (cproduce asn ι).
    Proof. induction asn; cbn; typeclasses eauto. Qed.

    #[export] Instance mon_consume {Σ} (asn : Assertion Σ) ι :
      Monotonic (MHeapSpec eq) (cconsume asn ι).
    Proof. induction asn; cbn; typeclasses eauto. Qed.

    #[export] Instance mon_call_contract
      [Δ τ] (c : SepContract Δ τ) (args : CStore Δ) :
      Monotonic (MHeapSpec eq) (ccall_contract c args).
    Proof. destruct c; typeclasses eauto. Qed.

    #[export] Instance mon_call_lemma
      [Δ] (lem : Lemma Δ) (vs : CStore Δ) :
      Monotonic (MHeapSpec eq) (ccall_lemma lem vs).
    Proof. destruct lem; typeclasses eauto. Qed.

    Definition read_register {τ} (reg : 𝑹𝑬𝑮 τ) : CHeapSpec (Val τ) :=
      v <- lift_purespec (CPureSpec.angelic _) ;;
      _ <- consume_chunk (scchunk_ptsreg reg v) ;;
      _ <- produce_chunk (scchunk_ptsreg reg v) ;;
      pure v.

    Definition write_register {τ} (reg : 𝑹𝑬𝑮 τ) (vnew : Val τ) : CHeapSpec (Val τ) :=
      vold <- lift_purespec (CPureSpec.angelic _) ;;
      _    <- consume_chunk (scchunk_ptsreg reg vold) ;;
      _    <- produce_chunk (scchunk_ptsreg reg vnew) ;;
      pure vnew.

    (* #[export] Instance heapspecm : CHeapSpecM CHeapSpec := *)
    (*   {| CHeapSpecM.produce_chunk := produce_chunk; *)
    (*      CHeapSpecM.consume_chunk := consume_chunk; *)
    (*   |}. *)


    (* #[export] Instance mon_purespecm : MHeapSpecM CHeapSpec. *)
    (* Proof. *)
    (*   constructor; cbn - [CPureSpec.purespecm]; try typeclasses eauto. *)
    (*   - intros * ? ? ra. now apply mon_lift_purespec, mon_pure. *)
    (*   - intros * rm1 rm2 ? ? rΦ h. apply or_impl_morphism. *)
    (*     now apply rm1. now apply rm2. *)
    (*   - intros * rm1 rm2 ? ? rΦ h. apply and_impl_morphism. *)
    (*     now apply rm1. now apply rm2. *)
    (* Qed. *)


    (* #[export] Instance mon_heapspecm : MHeapSpecM CHeapSpec. *)
    (* Proof. *)
    (*   constructor. *)
    (*   - firstorder. *)
    (*   - intros c. *)
    (*     eapply mon_bind. apply mon_get_heap. intros h ? <-. *)
    (*     eapply mon_bind. apply mon_lift_purespec. *)
    (*     apply CPureSpec.mon_angelic_list. intros [c' h'] ? <-. *)
    (*     eapply mon_bind. *)
    (*     apply mon_lift_purespec. apply mon_assert_eq_chunk. *)
    (*     intros _ _ _. *)
    (*     apply mon_put_heap. *)
    (* Qed. *)


    Section WithBI.

      Import iris.bi.interface iris.bi.derived_laws iris.bi.extensions.

      Context {L} {biA : BiAffine L} {PI : PredicateDef L}.

      #[local] Arguments CHeapSpec.bind {_ _} _ _ _ /.
      #[local] Arguments CHeapSpec.angelic_binary {_} _ _ /.
      #[local] Arguments CHeapSpec.demonic_binary {_} _ _ /.
      #[local] Arguments CHeapSpec.lift_purespec {_} _ _ /.

      Lemma wp_consume_chunk (c : SCChunk)
        (Φ : unit -> SCHeap -> Prop) :
        forall h,
          consume_chunk c Φ h ->
          (interpret_scheap h ⊢ interpret_scchunk c ∗
            (∃ h' : SCHeap, interpret_scheap h' ∧ ⌜Φ tt h'⌝))%I.
      Proof.
        intros ?. cbn. unfold consume_chunk, get_heap. cbn.
        rewrite CPureSpec.wp_angelic_list.
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


  (* Module Import CPureSpecM. *)

  (*   Class CPureSpecM (M : Type -> Type) : Type := *)
  (*     { pure {A} :  A -> M A; *)
  (*       bind {A B} : M A -> (A -> M B) -> M B; *)
  (*       error {A} : M A; *)
  (*       block {A} : M A; *)
  (*       angelic (σ : Ty) : M (Val σ); *)
  (*       demonic (σ : Ty) : M (Val σ); *)
  (*       angelic_ctx {N : Set} (Δ : NCtx N Ty) : M (NamedEnv Val Δ); *)
  (*       demonic_ctx {N : Set} (Δ : NCtx N Ty) : M (NamedEnv Val Δ); *)
  (*       assert_pathcondition : Prop -> M unit; *)
  (*       assert_formula : Prop -> M unit; *)
  (*       assume_pathcondition : Prop -> M unit; *)
  (*       assume_formula : Prop -> M unit; *)
  (*       angelic_binary {A} : M A -> M A -> M A; *)
  (*       demonic_binary {A} : M A -> M A -> M A; *)
  (*       angelic_pattern_match {N σ} (pat : @Pattern N σ) : *)
  (*         Val σ -> M (MatchResult pat); *)
  (*       demonic_pattern_match {N σ} (pat : @Pattern N σ) : *)
  (*         Val σ -> M (MatchResult pat); *)
  (*       new_pattern_match {N σ} (pat : @Pattern N σ) : *)
  (*         Val σ -> M (MatchResult pat); *)
  (*       debug {A} : M A -> M A; *)
  (*     }. *)

  (*   #[global] Arguments pure {M CPureSpecM A} _. *)
  (*   #[global] Arguments bind {M CPureSpecM A B} m f. *)
  (*   #[global] Arguments block {M CPureSpecM A}. *)
  (*   #[global] Arguments angelic {M CPureSpecM} σ. *)
  (*   #[global] Arguments demonic {M CPureSpecM} σ. *)
  (*   #[global] Arguments angelic_binary {M CPureSpecM A} _ _. *)
  (*   #[global] Arguments demonic_binary {M CPureSpecM A} _ _. *)

  (*   Module Import notations. *)
  (*     Notation "x <- ma ;; mb" := *)
  (*       (bind ma (fun x => mb)) *)
  (*         (at level 80, ma at level 90, mb at level 200, right associativity). *)
  (*     Notation "' x <- ma ;; mb" := *)
  (*       (bind ma (fun x => mb)) *)
  (*         (at level 80, x pattern, *)
  (*          ma at next level, mb at level 200, *)
  (*          right associativity). *)
  (*     Notation "ma ;; mb" := (bind ma (fun _ => mb)). *)
  (*   End notations. *)

  (*   (* Class MHeapSpecM M {pureM : CPureSpecM M} {relM : RelM M} : Type := *) *)
  (*   (*   { mon_pure `{MA : relation A} :: *) *)
  (*   (*       Monotonic (MA ==> MHeapSpec MA) pure; *) *)
  (*   (*     mon_bind `{MA : relation A, RB : relation B} :: *) *)
  (*   (*       Monotonic (MHeapSpec MA ==> (MA ==> RM RB) ==> RM RB) bind; *) *)
  (*   (*     mon_error `{MA : relation A} :: *) *)
  (*   (*       Monotonic (MHeapSpec MA) error; *) *)
  (*   (*     mon_block `{MA : relation A} :: *) *)
  (*   (*       Monotonic (MHeapSpec MA) block; *) *)
  (*   (*     mon_angelic (σ : Ty) :: *) *)
  (*   (*       Monotonic (MHeapSpec eq) (angelic σ); *) *)
  (*   (*     mon_demonic (σ : Ty) :: *) *)
  (*   (*       Monotonic (MHeapSpec eq) (demonic σ); *) *)
  (*   (*     mon_angelic_ctx {N : Set} {Δ} :: *) *)
  (*   (*       Monotonic (MHeapSpec eq) (@angelic_ctx _ _ N Δ); *) *)
  (*   (*     mon_demonic_ctx {N : Set} {Δ} :: *) *)
  (*   (*       Monotonic (MHeapSpec eq) (@demonic_ctx _ _ N Δ); *) *)
  (*   (*     mon_assert_pathcondition pc :: *) *)
  (*   (*       Monotonic (MHeapSpec eq) (assert_pathcondition pc); *) *)
  (*   (*     mon_assert_formula fml :: *) *)
  (*   (*       Monotonic (MHeapSpec eq) (assert_formula fml); *) *)
  (*   (*     mon_assume_pathcondition pc :: *) *)
  (*   (*       Monotonic (MHeapSpec eq) (assume_pathcondition pc); *) *)
  (*   (*     mon_assume_formula fml :: *) *)
  (*   (*       Monotonic (MHeapSpec eq) (assume_formula fml); *) *)
  (*   (*     mon_angelic_binary `{MA : relation A} m1 m2 :: *) *)
  (*   (*       Monotonic (MHeapSpec MA) m1 -> Monotonic (MHeapSpec MA) m2 -> *) *)
  (*   (*        Monotonic (MHeapSpec MA) (angelic_binary m1 m2); *) *)
  (*   (*     mon_demonic_binary `{MA : relation A} m1 m2 :: *) *)
  (*   (*       Monotonic (MHeapSpec MA) m1 -> Monotonic (MHeapSpec MA) m2 -> *) *)
  (*   (*       Monotonic (MHeapSpec MA) (demonic_binary m1 m2); *) *)
  (*   (*     mon_angelic_pattern_match {N σ} (pat : @Pattern N σ) (v : Val σ) :: *) *)
  (*   (*       Monotonic (MHeapSpec eq) (angelic_pattern_match pat v); *) *)
  (*   (*     mon_demonic_pattern_match {N σ} (pat : @Pattern N σ) (v : Val σ) :: *) *)
  (*   (*       Monotonic (MHeapSpec eq) (demonic_pattern_match pat v); *) *)
  (*   (*     mon_new_pattern_match {N σ} (pat : @Pattern N σ) (v : Val σ) :: *) *)
  (*   (*       Monotonic (MHeapSpec eq) (new_pattern_match pat v); *) *)
  (*   (*     mon_debug `{MA : relation A} m :: *) *)
  (*   (*       Monotonic (MHeapSpec MA) m -> Monotonic (MHeapSpec MA) (debug m); *) *)
  (*   (*   }. *) *)
  (*   (* #[global] Arguments MHeapSpecM _ {_ _}. *) *)

  (*   (* #[export] Instance mon_pure' `{MHeapSpecM M, MA : relation A} (a : A) : *) *)
  (*   (*   Monotonic MA a -> Monotonic (MHeapSpec MA) (pure a). *) *)
  (*   (* Proof. intros ra. now apply mon_pure. Qed. *) *)

  (*   (* #[export] Instance mon_bind' `{MHeapSpecM M, MA : relation A, RB : relation B} *) *)
  (*   (*   (m : M A) (f : A -> M B) : *) *)
  (*   (*   Monotonic (MHeapSpec MA) m -> Monotonic (MA ==> RM RB) f -> Monotonic (RM RB) (bind m f). *) *)
  (*   (* Proof. intros rm rf. eapply mon_bind; eauto. Qed. *) *)

  (* End CPureSpecM. *)

  (* Module Import CHeapSpecM. *)

  (*   (* Import CPureSpecM CPureSpecM.notations. *) *)

  (*   (* Class CHeapSpecM (M : Type -> Type) : Type := *) *)
  (*   (*   { produce_chunk : SCChunk -> M unit; *) *)
  (*   (*     consume_chunk : SCChunk -> M unit; *) *)
  (*   (*   }. *) *)

  (*   (* Class MHeapSpecM M {heapM : CHeapSpecM M} {relM : RelM M} : Type := *) *)
  (*   (*   { mon_produce_chunk c :: Monotonic (MHeapSpec eq) (produce_chunk c); *) *)
  (*   (*     mon_consume_chunk c :: Monotonic (MHeapSpec eq) (consume_chunk c); *) *)
  (*   (*   }. *) *)
  (*   (* #[global] Arguments MHeapSpecM M {_ _}. *) *)

  (* End CHeapSpecM. *)

  Section Replay.

    Import CPureSpec CPureSpec.notations.

    Definition creplay :
      forall {Σ} (s : 𝕊 Σ) (ι : Valuation Σ), CPureSpec unit :=
      fix replay {Σ} s ι :=
        match s with
        | SymProp.angelic_binary o1 o2 =>
            angelic_binary (replay o1 ι) (replay o2 ι)
        | SymProp.demonic_binary o1 o2 =>
            demonic_binary (replay o1 ι) (replay o2 ι)
        | SymProp.block =>
            block
        | SymProp.error msg =>
            error
        | SymProp.assertk fml msg k =>
            assert_formula (instprop fml ι) ;;
            replay k ι
        | SymProp.assumek fml k =>
            assume_formula (instprop fml ι) ;;
            replay k ι
        | SymProp.angelicv b k =>
            v <- angelic _ ;;
            replay k (env.snoc ι b v)
        | SymProp.demonicv b k =>
            v <- demonic _ ;;
            replay k (env.snoc ι b v )
        | @SymProp.assert_vareq _ x σ xIn t msg k =>
            let ι' := env.remove (x ∷ σ) ι xIn in
            let x' := ι.[? x∷σ] in
            let t' := inst t ι' in
            assert_formula (x' = t') ;;
            replay k ι'
        | @SymProp.assume_vareq _ x σ xIn t k =>
            let ι' := env.remove (x ∷ σ) ι xIn in
            let x' := ι.[? x∷σ] in
            let t' := inst t ι' in
            assume_formula (x' = t') ;;
            replay k ι'
        | SymProp.pattern_match s pat rhs =>
            error
        | SymProp.pattern_match_var x pat rhs =>
            error
        | SymProp.debug b k =>
            debug (replay k ι)
        end.

  End Replay.


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
    (* tactic above. *)
    Class ShallowStats (P : Prop) :=
      stats : Stats.
    Arguments stats P {_}.

    (* We make these instances global so that users can simply use the *)
    (* calc tactic qualified without importing the rest of this module. *)
    #[global] Instance stats_true : ShallowStats TRUE :=
      {| branches := 1; pruned := 1 |}.
    #[global] Instance stats_false : ShallowStats FALSE :=
      {| branches := 1; pruned := 1 |}.
    #[global] Instance stats_finish : ShallowStats FINISH :=
      {| branches := 1; pruned := 0 |}.
    (* We do not count regular True and False towards the statistics *)
    (* because they do not (should not) represent leaves of the shallow *)
    (* execution. *)
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

End ShallowMonadsOn.
