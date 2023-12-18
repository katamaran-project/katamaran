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

From Coq Require Import
  Classes.Morphisms
  Classes.Morphisms_Prop
  Program.Basics
  Relations.Relation_Definitions.
From Equations Require Import
  Equations.
From Katamaran Require Import
  Prelude
  Base
  Syntax.Chunks
  Syntax.Predicates
  Symbolic.Propositions
  Symbolic.Worlds.

Import SignatureNotations ctx.notations env.notations.

#[local] Set Implicit Arguments.

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

#[export] Instance monotonic_eq_elim {A B} {MB : relation B} {f : A -> B} :
  (forall a, Monotonic MB (f a)) -> Monotonic (eq ==> MB) f.
Proof. unfold Monotonic. intros pf ? ? <-. auto. Qed.

#[export] Instance monotonic_pointwise {A B} {MB : relation B} {f : A -> B} :
  (forall a, Monotonic MB (f a)) -> Monotonic (A ::> MB) f.
Proof. intros pf a. apply pf. Qed.

#[export] Instance monotonic_eq_refl {A} {a : A} :
  Monotonic eq a.
Proof. easy. Qed.

Module Type ShallowMonadsOn (Import B : Base) (Import P : PredicateKit B)
  (Import W : WorldsMixin B P) (Import SP : SymPropOn B P W).

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
        + apply List.in_map_iff in hyp.
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
        | [ctx]   => pure [env]
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

    Definition replay_aux :
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

    Definition replay [Σ] (P : 𝕊 Σ) (ι : Valuation Σ) :Prop :=
      run (replay_aux P ι).

    #[export] Instance mon_run :
      Monotonic (MPureSpec eq ==> impl) run.
    Proof. firstorder. Qed.

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
    #[global] Typeclasses Opaque bind.

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

    #[export] Instance mon_replay_aux {Σ} (P : 𝕊 Σ) (ι : Valuation Σ) :
      Monotonic (MPureSpec eq) (replay_aux P ι).
    Proof. induction P; typeclasses eauto. Qed.

    #[export] Instance mon_replay {Σ} (P : 𝕊 Σ) :
      Monotonic (Valuation Σ ::> impl) (replay P).
    Proof.
      apply monotonic_pointwise. intros ι.
      apply mon_run, mon_replay_aux.
    Qed.

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
        unfold assert_formula, assert_pathcondition.
        intuition auto.
    Qed.

    Lemma wp_assert_eq_nenv {N} {Δ : NCtx N Ty} (δ δ' : NamedEnv Val Δ) :
      forall Φ,
        assert_eq_nenv δ δ' Φ <-> δ = δ' /\ Φ tt.
    Proof.
      induction δ; intros Φ; destruct (env.view δ'); cbn; unfold NamedEnv.
      - intuition auto.
      - rewrite IHδ, env.inversion_eq_snoc.
        unfold assert_formula, assert_pathcondition.
        intuition auto.
    Qed.

    (* For heap predicates and types of registers. *)
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

    Lemma replay_sound {Σ} (s : 𝕊 Σ) (ι : Valuation Σ) :
      replay s ι -> SymProp.safe s ι.
    Proof.
      unfold replay, run.
      induction s; cbn.
      - intros [|]; intuition auto.
      - intros []; intuition auto.
      - inversion 1.
      - auto.
      - intros []. intuition auto.
      - intuition auto.
      - apply ex_impl_morphism. intros v; red; apply IHs.
      - apply all_impl_morphism. intros v; red; apply IHs.
      - intros []. intuition auto.
      - intuition auto.
      - inversion 1.
      - inversion 1.
      - unfold debug. apply IHs.
    Qed.

  End CPureSpec.
  Export (hints) CPureSpec.

End ShallowMonadsOn.
