(******************************************************************************)
(* Copyright (c) 2020 Dominique Devriese, Sander Huyghebaert, Steven Keuchel  *)
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
     Bool.Bool
     Lists.List
     NArith.NArith
     Program.Tactics
     Strings.String
     ZArith.BinInt.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Notations
     Prelude
     Signature
     Symbolic.Propositions
     Specification.

From stdpp Require base list option.

Import ctx.notations.
Import env.notations.
Import ListNotations.
Import SigTNotations.

Set Implicit Arguments.

Module Type ShallowExecOn
  (Import B : Base)
  (Import PROG : Program B)
  (Import SIG : Signature B)
  (Import SPEC : Specification B PROG SIG).

  (* The pure backwards predicate transformer monad. We use this monad in some
     of the definition of primitives that do no need access to the store or heap
     and that can later be lifted to the proper monad. *)
  Definition CPureSpecM (A : Type) : Type :=
    (A -> Prop) -> Prop.

  Module CPureSpecM.

    Definition pure {A : Type} :
      A -> CPureSpecM A :=
      fun a POST => POST a.

    Definition map {A B} :
      (A -> B) -> CPureSpecM A -> CPureSpecM B :=
      fun f m POST => m (Basics.compose POST f).

    Definition bind {A B} :
      CPureSpecM A -> (A -> CPureSpecM B) -> CPureSpecM B :=
      fun m f POST => m (fun a1 => f a1 POST).

    Local Notation "x <- ma ;; mb" :=
      (bind ma (fun x => mb))
        (at level 80, ma at level 90, mb at level 200, right associativity).
    Local Notation "ma ;; mb" := (bind ma (fun _ => mb)).

    (* For counting the different execution paths of the shallow executor we use
       different aliases for False and True to distinguish between them. TRUE
       and FALSE represent execution paths that are pruned, i.e. do not reach
       the end of a function, and FINISH encodes the successful execution
       case. *)
    Definition FALSE : Prop := False.
    Definition TRUE : Prop := True.
    Definition FINISH : Prop := True.
    Global Typeclasses Opaque TRUE.
    Global Typeclasses Opaque FALSE.
    Global Typeclasses Opaque FINISH.

    Definition error {A} : CPureSpecM A :=
      fun POST => FALSE.
    Definition block {A} : CPureSpecM A :=
      fun POST => TRUE.

    Definition angelic (σ : Ty) : CPureSpecM (Val σ) :=
      fun POST => exists v : Val σ, POST v.

    Definition angelic_ctx {N : Set} :
      forall Δ : NCtx N Ty, CPureSpecM (NamedEnv Val Δ) :=
      fix rec Δ {struct Δ} :=
        match Δ with
        | []%ctx  => pure []
        | Δ ▻ x∷σ => vs <- rec Δ;;
                     v  <- angelic σ;;
                     pure (vs ► (x∷σ ↦ v))
        end.
    Arguments angelic_ctx {N} Δ.

    Definition demonic σ : CPureSpecM (Val σ) :=
      fun POST => forall v : Val σ, POST v.

    Definition demonic_ctx {N : Set} :
      forall Δ : NCtx N Ty, CPureSpecM (NamedEnv Val Δ) :=
      fix rec Δ {struct Δ} :=
        match Δ with
        | []      => pure env.nil
        | Δ ▻ x∷σ => vs <- rec Δ;;
                     v  <- demonic σ;;
                     pure (vs ► (x∷σ ↦ v))
        end%ctx.
    Arguments demonic_ctx {N} Δ.

    Definition assume_formula (fml : Prop) : CPureSpecM unit :=
      fun POST => fml -> POST tt.

    Definition assert_formula (fml : Prop) : CPureSpecM unit :=
      fun POST => fml /\ POST tt.

    (* The paper uses asserted equalities between multiple types, but the
       symbolic executor can in fact only assert equalities between symbolic
       terms. We mirror the structure of the symbolic execution and also
       traverse (the statically known parts) of other data structures. *)
    Equations(noeqns) assert_eq_env [Δ : Ctx Ty]
      (δ δ' : Env Val Δ) : CPureSpecM unit :=
      assert_eq_env env.nil          env.nil            := pure tt;
      assert_eq_env (env.snoc δ _ t) (env.snoc δ' _ t') :=
        bind (assert_eq_env δ δ') (fun _ => assert_formula (t = t')).

    Equations(noeqns) assert_eq_nenv {N : Set} [Δ : NCtx N Ty]
      (δ δ' : NamedEnv Val Δ) : CPureSpecM unit :=
      assert_eq_nenv env.nil          env.nil            := pure tt;
      assert_eq_nenv (env.snoc δ _ t) (env.snoc δ' _ t') :=
        bind (assert_eq_nenv δ δ') (fun _ => assert_formula (t = t')).

    Equations(noeqns) assume_eq_env [Δ : Ctx Ty]
      (δ δ' : Env Val Δ) : CPureSpecM unit :=
      assume_eq_env env.nil          env.nil            := pure tt;
      assume_eq_env (env.snoc δ _ t) (env.snoc δ' _ t') :=
        bind (assume_eq_env δ δ') (fun _ => assume_formula (t = t')).

    Equations(noeqns) assume_eq_nenv {N : Set} [Δ : NCtx N Ty]
      (δ δ' : NamedEnv Val Δ) : CPureSpecM unit :=
      assume_eq_nenv env.nil          env.nil            := pure tt;
      assume_eq_nenv (env.snoc δ _ t) (env.snoc δ' _ t') :=
        bind (assume_eq_nenv δ δ') (fun _ => assume_formula (t = t')).

    Definition angelic_binary {A} :
      CPureSpecM A -> CPureSpecM A -> CPureSpecM A :=
      fun m1 m2 POST =>
        m1 POST \/ m2 POST.
    Definition demonic_binary {A} :
      CPureSpecM A -> CPureSpecM A -> CPureSpecM A :=
      fun m1 m2 POST =>
        m1 POST /\ m2 POST.

    Definition angelic_list' {A} :
      A -> list A -> CPureSpecM A :=
      fix rec d xs :=
        match xs with
        | nil        => pure d
        | cons x xs  => angelic_binary (pure d) (rec x xs)
        end.

    Definition angelic_list {A} (xs : list A) : CPureSpecM A :=
      match xs with
      | nil => fun POST => False
      | cons x xs => angelic_list' x xs
      end.

    Definition demonic_list' {A} :
      A -> list A -> CPureSpecM A :=
      fix rec d xs :=
        match xs with
        | nil        => pure d
        | cons x xs  => demonic_binary (pure d) (rec x xs)
        end.

    Definition demonic_list {A} (xs : list A) : CPureSpecM A :=
      match xs with
      | nil => fun POST => True
      | cons x xs => demonic_list' x xs
      end.

    Definition angelic_finite F `{finite.Finite F} :
      CPureSpecM F :=
      angelic_list (finite.enum F).
    #[global] Arguments angelic_finite F {_ _}.

    Definition demonic_finite F `{finite.Finite F} :
      CPureSpecM F :=
      demonic_list (finite.enum F).
    #[global] Arguments demonic_finite F {_ _}.

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
      - cbv [angelic_binary pure].
        rewrite IHxs; clear IHxs.
        firstorder. left. now subst.
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
      - cbv [demonic_binary pure].
        rewrite IHxs; clear IHxs.
        firstorder. now subst.
    Qed.

    Lemma wp_demonic_list {A} (xs : list A) (POST : A -> Prop) :
      demonic_list xs POST <->
      forall x : A, List.In x xs -> POST x.
    Proof. destruct xs; cbn; [firstorder|apply wp_demonic_list']. Qed.

    Lemma wp_assert_eq_env {Δ : Ctx Ty} (δ δ' : Env Val Δ) :
      forall POST,
        assert_eq_env δ δ' POST <-> δ = δ' /\ POST tt.
    Proof.
      induction δ; intros POST.
      - destruct (env.view δ'). intuition auto.
      - destruct (env.view δ'); cbn.
        unfold bind, assert_formula.
        now rewrite IHδ, env.inversion_eq_snoc.
    Qed.

    Lemma wp_assert_eq_nenv {N} {Δ : NCtx N Ty} (δ δ' : NamedEnv Val Δ) :
      forall POST,
        assert_eq_nenv δ δ' POST <-> δ = δ' /\ POST tt.
    Proof.
      induction δ; intros POST.
      - destruct (env.view δ'). intuition auto.
      - destruct (env.view δ') as [δ']; cbn in *.
        unfold bind, assert_formula.
        now rewrite IHδ, (@env.inversion_eq_snoc _ _ _ b δ δ').
    Qed.

    Lemma wp_assume_eq_env {Δ : Ctx Ty} (δ δ' : Env Val Δ) :
      forall POST,
        assume_eq_env δ δ' POST <-> (δ = δ' -> POST tt).
    Proof.
      induction δ; intros POST.
      - destruct (env.view δ'). intuition auto.
      - destruct (env.view δ'); cbn.
        unfold bind, assume_formula.
        rewrite IHδ, env.inversion_eq_snoc.
        intuition auto.
    Qed.

    Lemma wp_assume_eq_nenv {N} {Δ : NCtx N Ty} (δ δ' : NamedEnv Val Δ) :
      forall POST,
        assume_eq_nenv δ δ' POST <-> (δ = δ' -> POST tt).
    Proof.
      induction δ; intros POST.
      - destruct (env.view δ'). intuition auto.
      - destruct (env.view δ') as [δ']; cbn in *.
        unfold bind, assume_formula.
        rewrite IHδ, (@env.inversion_eq_snoc _ _ _ b δ δ').
        intuition auto.
    Qed.

    Definition angelic_pattern_match {N : Set} {A σ} (pat : @Pattern N σ)
      (v : Val σ)
      (k : forall (c : PatternCase pat), NamedEnv Val (PatternCaseCtx c) -> CPureSpecM A) :
      CPureSpecM A :=
      pc <- angelic_finite (PatternCase pat);;
      vs <- angelic_ctx (PatternCaseCtx pc) ;;
      _  <- assert_formula (pattern_match_val_reverse pat pc vs = v);;
      k pc vs.

    Definition demonic_pattern_match {N : Set} {A σ} (pat : @Pattern N σ)
      (v : Val σ)
      (k : forall (c : PatternCase pat), NamedEnv Val (PatternCaseCtx c) -> CPureSpecM A) :
      CPureSpecM A :=
      pc <- demonic_finite (PatternCase pat);;
      vs <- demonic_ctx (PatternCaseCtx pc) ;;
      _  <- assume_formula (pattern_match_val_reverse pat pc vs = v);;
      k pc vs.

    Definition pattern_match {N σ} (pat : @Pattern N σ) (v : Val σ) :
      CPureSpecM (MatchResult pat) := pure (pattern_match_val pat v).
    #[global] Arguments pattern_match {N σ} pat v.

    Fixpoint assert_eq_chunk (c1 c2 : SCChunk) : CPureSpecM unit :=
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

    Local Set Equations With UIP.
    Lemma wp_assert_eq_chunk (c c' : SCChunk) :
      forall POST,
        assert_eq_chunk c c' POST <-> c = c' /\ POST tt.
    Proof.
      revert c'. induction c; intros c' POST; destruct c'; cbn in *;
        unfold error, FALSE, assert_formula; try (intuition discriminate).
      - destruct eq_dec as [e|n].
        + rewrite wp_assert_eq_env. apply and_iff_compat_r'.
          intros ?. destruct e; cbn. split; intros Heq.
          * now f_equal.
          * now dependent elimination Heq.
        + split; try contradiction. intros [Heq Hwp]. apply n.
          now dependent elimination Heq.
      - destruct eq_dec_het as [e|n].
        + apply and_iff_compat_r'. intros ?.
          dependent elimination e; cbn.
          split; intros Heq.
          * now f_equal.
          * now dependent elimination Heq.
        + split; try contradiction. intros [Heq Hwp]. apply n.
          now dependent elimination Heq.
      - unfold bind. rewrite IHc1, IHc2. intuition congruence.
      - unfold bind. rewrite IHc1, IHc2. intuition congruence.
    Qed.

  End CPureSpecM.

  (* The main specification monad that we use for execution. It is indexed by
     two program variable contexts Γ1 Γ2 that encode the shape of the program
     variable store before and after execution. *)
  Definition CHeapSpecM (Γ1 Γ2 : PCtx) (A : Type) : Type :=
    (A -> CStore Γ2 -> SCHeap -> Prop) -> CStore Γ1 -> SCHeap -> Prop.
  Bind Scope mut_scope with CHeapSpecM.

  Local Open Scope mut_scope.

  Module CHeapSpecM.

    Section Basic.

      Definition lift_purem {Γ} {A : Type} :
        CPureSpecM A -> CHeapSpecM Γ Γ A :=
        fun m POST δ h => m (fun a => POST a δ h).

      Definition pure {Γ A} (a : A) : CHeapSpecM Γ Γ A :=
        fun POST => POST a.
      Definition bind {Γ1 Γ2 Γ3 A B} (ma : CHeapSpecM Γ1 Γ2 A) (f : A -> CHeapSpecM Γ2 Γ3 B) : CHeapSpecM Γ1 Γ3 B :=
        fun POST => ma (fun a => f a POST).
      Definition bind_right {Γ1 Γ2 Γ3 A B} (ma : CHeapSpecM Γ1 Γ2 A) (mb : CHeapSpecM Γ2 Γ3 B) : CHeapSpecM Γ1 Γ3 B :=
        bind ma (fun _ => mb).
      Definition map {Γ1 Γ2 A B} (f : A -> B) (ma : CHeapSpecM Γ1 Γ2 A) : CHeapSpecM Γ1 Γ2 B :=
        fun POST => ma (fun a => POST (f a)).

      Definition error {Γ1 Γ2 A} : CHeapSpecM Γ1 Γ2 A :=
        fun POST δ h => CPureSpecM.FALSE.
      Definition block {Γ1 Γ2 A} : CHeapSpecM Γ1 Γ2 A :=
        fun POST δ h => CPureSpecM.TRUE.

      Definition demonic_binary {Γ1 Γ2 A} (m1 m2 : CHeapSpecM Γ1 Γ2 A) : CHeapSpecM Γ1 Γ2 A :=
        fun POST δ h => m1 POST δ h /\ m2 POST δ h.
      Definition angelic_binary {Γ1 Γ2 A} (m1 m2 : CHeapSpecM Γ1 Γ2 A) : CHeapSpecM Γ1 Γ2 A :=
        fun POST δ h => m1 POST δ h \/ m2 POST δ h.

      Definition demonic {Γ} (σ : Ty) : CHeapSpecM Γ Γ (Val σ) :=
        lift_purem (CPureSpecM.demonic σ).
      Definition angelic {Γ} (σ : Ty) : CHeapSpecM Γ Γ (Val σ) :=
        lift_purem (CPureSpecM.angelic σ).

      Definition angelic_ctx {N : Set} {Γ} :
        forall Δ : NCtx N Ty, CHeapSpecM Γ Γ (NamedEnv Val Δ) :=
        fun Δ => lift_purem (CPureSpecM.angelic_ctx Δ).
      #[global] Arguments angelic_ctx {N Γ} Δ.

      Definition angelic_list {A Γ} (xs : list A) : CHeapSpecM Γ Γ A :=
        lift_purem (CPureSpecM.angelic_list xs).

      Definition angelic_finite F `{finite.Finite F} {Γ} : CHeapSpecM Γ Γ F :=
        lift_purem (CPureSpecM.angelic_finite F).
      #[global] Arguments angelic_finite F {_ _ Γ}.

      Definition demonic_finite F `{finite.Finite F} {Γ} : CHeapSpecM Γ Γ F :=
        lift_purem (CPureSpecM.demonic_finite F).
      #[global] Arguments demonic_finite F {_ _ Γ}.

      Definition demonic_ctx {N : Set} {Γ} :
        forall Δ : NCtx N Ty, CHeapSpecM Γ Γ (NamedEnv Val Δ) :=
        fun Δ => lift_purem (CPureSpecM.demonic_ctx Δ).
      #[global] Arguments demonic_ctx {N Γ} Δ.

    End Basic.

    Module CHeapSpecMNotations.

      Infix "⊗" := demonic_binary (at level 40, left associativity) : mut_scope.
      Infix "⊕" := angelic_binary (at level 50, left associativity) : mut_scope.

      Notation "' x <- ma ;; mb" :=
        (bind ma (fun x => mb))
          (at level 80, x pattern, ma at next level, mb at level 200, right associativity,
           format "' x  <-  ma  ;;  mb") : mut_scope.
      Notation "x <- ma ;; mb" :=
        (bind ma (fun x => mb))
          (at level 80, ma at level 90, mb at level 200, right associativity) : mut_scope.
      (* Notation "ma >>= f" := (bind ma f) (at level 50, left associativity) : mut_scope. *)
      Notation "ma ;; mb" := (bind_right ma mb) : mut_scope.

    End CHeapSpecMNotations.
    Import CHeapSpecMNotations.
    Local Open Scope mut_scope.

    Section AssumeAssert.

      Definition assume_formula {Γ} (fml : Prop) : CHeapSpecM Γ Γ unit :=
        lift_purem (CPureSpecM.assume_formula fml).
      Definition assert_formula {Γ} (fml : Prop) : CHeapSpecM Γ Γ unit :=
        lift_purem (CPureSpecM.assert_formula fml).
      Definition assert_eq_env {Γ} {Δ : Ctx Ty} (δ δ' : Env Val Δ) : CHeapSpecM Γ Γ unit :=
        lift_purem (CPureSpecM.assert_eq_env δ δ').
      Definition assert_eq_nenv {N Γ} {Δ : NCtx N Ty} (δ δ' : NamedEnv Val Δ) : CHeapSpecM Γ Γ unit :=
        lift_purem (CPureSpecM.assert_eq_nenv δ δ').
      Definition assert_eq_chunk {Γ} (c c' : SCChunk) : CHeapSpecM Γ Γ unit :=
        lift_purem (CPureSpecM.assert_eq_chunk c c').

    End AssumeAssert.

    Section PatternMatching.

      Definition angelic_pattern_match {N : Set} {Γ1 Γ2 A σ} (pat : @Pattern N σ)
        (v : Val σ)
        (k : forall (c : PatternCase pat), NamedEnv Val (PatternCaseCtx c) -> CHeapSpecM Γ1 Γ2 A) :
        CHeapSpecM Γ1 Γ2 A :=
        pc <- angelic_finite (PatternCase pat);;
        vs <- angelic_ctx (PatternCaseCtx pc) ;;
        _  <- assert_formula (pattern_match_val_reverse pat pc vs = v);;
        k pc vs.

      Definition demonic_pattern_match {N : Set} {Γ1 Γ2 A σ} (pat : @Pattern N σ)
        (v : Val σ)
        (k : forall (c : PatternCase pat), NamedEnv Val (PatternCaseCtx c) -> CHeapSpecM Γ1 Γ2 A) :
        CHeapSpecM Γ1 Γ2 A :=
        pc <- demonic_finite (PatternCase pat);;
        vs <- demonic_ctx (PatternCaseCtx pc) ;;
        _  <- assume_formula (pattern_match_val_reverse pat pc vs = v);;
        k pc vs.

      Lemma wp_angelic_pattern_match {N : Set} {Γ1 Γ2 A σ} (pat : @Pattern N σ)
        (v : Val σ)
        (k : forall (c : PatternCase pat), NamedEnv Val (PatternCaseCtx c) -> CHeapSpecM Γ1 Γ2 A)
        (POST : A -> CStore Γ2 -> SCHeap -> Prop) (δ : CStore Γ1) (h : SCHeap) :
        angelic_pattern_match pat v k POST δ h <->
          let c := pattern_match_val pat v in
          k (projT1 c) (projT2 c) POST δ h.
      Proof.
        cbv [angelic_pattern_match bind angelic_finite lift_purem angelic_ctx
               CPureSpecM.angelic_finite assert_formula CPureSpecM.assert_formula].
        rewrite CPureSpecM.wp_angelic_list.
        setoid_rewrite CPureSpecM.wp_angelic_ctx.
        split.
        - intros (pc & Hin & δpc & <- & Hwp).
          now rewrite pattern_match_val_inverse_right.
        - intros Hwp.
          exists (pattern_match_val pat v).1.
          split.
          rewrite <- base.elem_of_list_In.
          apply finite.elem_of_enum.
          exists (pattern_match_val pat v).2.
          split.
          apply pattern_match_val_inverse_left.
          apply Hwp.
      Qed.

      Lemma wp_demonic_pattern_match {N : Set} {Γ1 Γ2 A σ} (pat : @Pattern N σ)
        (v : Val σ)
        (k : forall (c : PatternCase pat), NamedEnv Val (PatternCaseCtx c) -> CHeapSpecM Γ1 Γ2 A)
        (POST : A -> CStore Γ2 -> SCHeap -> Prop) (δ : CStore Γ1) (h : SCHeap) :
        demonic_pattern_match pat v k POST δ h <->
          let c := pattern_match_val pat v in
          k (projT1 c) (projT2 c) POST δ h.
      Proof.
        cbv [demonic_pattern_match bind demonic_finite lift_purem demonic_ctx
               CPureSpecM.demonic_finite assume_formula CPureSpecM.assume_formula].
        rewrite CPureSpecM.wp_demonic_list.
        setoid_rewrite CPureSpecM.wp_demonic_ctx.
        split.
        - intros Hwp. apply Hwp.
          rewrite <- base.elem_of_list_In.
          apply finite.elem_of_enum.
          apply pattern_match_val_inverse_left.
        - intros Hwp pc Hin δpc <-. revert Hwp.
          now rewrite pattern_match_val_inverse_right.
      Qed.

    End PatternMatching.

    Section State.

      Definition pushpop {A Γ1 Γ2 x σ} (v : Val σ)
        (d : CHeapSpecM (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) A) : CHeapSpecM Γ1 Γ2 A :=
        fun POST δ0 => d (fun a δ1 => POST a (env.tail δ1)) (δ0 ► (x∷σ ↦ v)).
      Definition pushspops {A} {Γ1 Γ2 Δ} (δΔ : CStore Δ)
        (d : CHeapSpecM (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) A) : CHeapSpecM Γ1 Γ2 A :=
        fun POST δ0 => d (fun a δ1 => POST a (env.drop Δ δ1)) (δ0 ►► δΔ).
      Definition get_local {Γ} : CHeapSpecM Γ Γ (CStore Γ) :=
        fun POST δ => POST δ δ.
      Definition put_local {Γ1 Γ2} (δ : CStore Γ2) : CHeapSpecM Γ1 Γ2 unit :=
        fun POST _ => POST tt δ.
      Definition get_heap {Γ} : CHeapSpecM Γ Γ SCHeap :=
        fun POST δ h => POST h δ h.
      Definition put_heap {Γ} (h : SCHeap) : CHeapSpecM Γ Γ unit :=
        fun POST δ _ => POST tt δ h.

      Definition eval_exp {Γ σ} (e : Exp Γ σ) : CHeapSpecM Γ Γ (Val σ) :=
        fun POST δ => POST (eval e δ) δ.
      Definition eval_exps {Γ} {σs : PCtx} (es : NamedEnv (Exp Γ) σs) : CHeapSpecM Γ Γ (CStore σs) :=
        fun POST δ => POST (evals es δ) δ.
      Definition assign {Γ} x {σ} {xIn : x∷σ ∈ Γ} (v : Val σ) : CHeapSpecM Γ Γ unit :=
        fun POST δ => POST tt (δ ⟪ x ↦ v ⟫).
      Global Arguments assign {Γ} x {σ xIn} v.

    End State.

    Section ProduceConsume.

      Definition produce_chunk {Γ} (c : SCChunk) : CHeapSpecM Γ Γ unit :=
        fun POST δ h => POST tt δ (cons c h).

      Definition consume_chunk {Γ} (c : SCChunk) : CHeapSpecM Γ Γ unit :=
        h         <- get_heap ;;
        '(c', h') <- angelic_list (heap_extractions h) ;;
        assert_eq_chunk c c' ;;
        put_heap h'.

      Global Arguments produce_chunk {Γ} _.
      Global Arguments consume_chunk {Γ} _.

      Fixpoint produce {Γ Σ} (ι : Valuation Σ) (asn : Assertion Σ) : CHeapSpecM Γ Γ unit :=
        match asn with
        | asn.formula fml => assume_formula (instprop fml ι)
        | asn.chunk c     => produce_chunk (inst c ι)
        | asn.chunk_angelic c => produce_chunk (inst c ι)
        | asn.pattern_match s pat rhs =>
          demonic_pattern_match
            pat (inst (T := fun Σ => Term Σ _) s ι)
            (fun pc δpc => produce (ι ►► δpc) (rhs pc))
            (* let v := inst (T := fun Σ => Term Σ _) s ι in *)
            (* '(existT pc vs) <- lift_purem (CPureSpecM.pattern_match pat v) ;; *)
            (* produce (ι ►► vs) (rhs pc) *)
        | asn.sep a1 a2   => _ <- produce ι a1 ;; produce ι a2
        | asn.or a1 a2 =>
          demonic_binary (produce ι a1)
                         (produce ι a2)
        | asn.exist ς τ a =>
          v <- demonic τ ;;
          produce (env.snoc ι (ς∷τ) v) a
        | asn.debug => pure tt
        end.

      Fixpoint consume {Γ Σ} (ι : Valuation Σ) (asn : Assertion Σ) : CHeapSpecM Γ Γ unit :=
        match asn with
        | asn.formula fml => assert_formula (instprop fml ι)
        | asn.chunk c     => consume_chunk (inst c ι)
        | asn.chunk_angelic c     => consume_chunk (inst c ι)
        | asn.pattern_match s pat rhs =>
          angelic_pattern_match
            pat (inst (T := fun Σ => Term Σ _) s ι)
            (fun pc δpc => consume (ι ►► δpc) (rhs pc))
            (* let v := inst (T := fun Σ => Term Σ _) s ι in *)
            (* '(existT pc vs) <- lift_purem (CPureSpecM.pattern_match pat v) ;; *)
            (* consume (ι ►► vs) (rhs pc) *)
        | asn.sep a1 a2   => _ <- consume ι a1;; consume ι a2
        | asn.or a1 a2 =>
          angelic_binary (consume ι a1)
                         (consume ι a2)
        | asn.exist ς τ a =>
          v <- angelic τ ;;
          consume (env.snoc ι (ς∷τ) v) a
        | asn.debug => pure tt
        end.

    End ProduceConsume.

    Section Exec.

      Definition call_contract {Γ Δ τ} (contract : SepContract Δ τ) (args : CStore Δ) : CHeapSpecM Γ Γ (Val τ) :=
        match contract with
        | MkSepContract _ _ Σe δ req result ens =>
          ι <- angelic_ctx Σe ;;
          assert_eq_nenv (inst δ ι) args ;;
          consume ι req  ;;
          v <- demonic τ ;;
          produce (env.snoc ι (result∷τ) v) ens ;;
          pure v
        end.

      Definition call_lemma {Γ Δ} (lem : Lemma Δ) (vs : CStore Δ) : CHeapSpecM Γ Γ unit :=
        match lem with
        | MkLemma _ Σe δ req ens =>
          ι <- angelic_ctx Σe ;;
          assert_eq_nenv (inst δ ι) vs ;;
          consume ι req ;;
          produce ι ens
        end.

      (* The paper discusses the case that a function call is replaced by
         interpreting the contract instead. However, this is not always
         convenient. We therefore make contracts for functions optional and if a
         function does not have a contract, we continue executing the body of
         the called function. A parameter [inline_fuel] bounds the number of
         allowed levels before failing execution. Therefore, we write the
         executor in an open-recusion style and [Exec] is the closed type of
         such an executor. *)
      Definition Exec := forall Γ τ (s : Stm Γ τ), CHeapSpecM Γ Γ (Val τ).

      Section ExecAux.

        (* The executor for "inlining" a call. *)
        Variable rec : Exec.

        (* The openly-recursive executor. *)
        Definition exec_aux : Exec :=
          fix exec_aux {Γ τ} (s : Stm Γ τ) : CHeapSpecM Γ Γ (Val τ) :=
            match s with
            | stm_val _ l => pure l
            | stm_exp e => eval_exp e
            | stm_let x σ s k =>
              v <- exec_aux s ;;
              pushpop v (exec_aux k)
            | stm_block δ k =>
              pushspops δ (exec_aux k)
            | stm_assign x e =>
              v <- exec_aux e ;;
              _ <- assign x v ;;
              pure v
            | stm_call f es =>
              args <- eval_exps es ;;
              match CEnv f with
              | Some c => call_contract c args
              | None   => fun POST δ => rec (FunDef f) (fun v _ => POST v δ) args
              end
            | stm_foreign f es =>
              ts <- eval_exps es ;;
              call_contract (CEnvEx f) ts
            | stm_lemmak l es k =>
              ts <- eval_exps es ;;
              _  <- call_lemma (LEnv l) ts ;;
              exec_aux k
            | stm_call_frame δ' s =>
              δ <- get_local ;;
              _ <- put_local δ' ;;
              v <- exec_aux s ;;
              _ <- put_local δ ;;
              pure v
            | stm_seq e k => _ <- exec_aux e ;; exec_aux k
            | stm_assertk e1 _ k =>
              v <- eval_exp e1 ;;
              _ <- assume_formula (v = true) ;;
              exec_aux k
            | stm_fail _ s =>
              block
            | stm_pattern_match s pat rhs =>
              v  <- exec_aux s ;;
              demonic_pattern_match pat v
                (fun pc δpc => pushspops δpc (exec_aux (rhs pc)))
              (* v <- exec_aux s ;; *)
              (* '(existT pc δpc) <- lift_purem (CPureSpecM.pattern_match pat v) ;; *)
              (* pushspops δpc (exec_aux (rhs pc)) *)
            | stm_read_register reg =>
              v <- angelic τ ;;
              let c := scchunk_ptsreg reg v in
              _ <- consume_chunk c ;;
              _ <- produce_chunk c ;;
              pure v
            | stm_write_register reg e =>
              v__old <- angelic τ ;;
              _    <- consume_chunk (scchunk_ptsreg reg v__old) ;;
              v__new <- eval_exp e ;;
              _    <- produce_chunk (scchunk_ptsreg reg v__new) ;;
              pure v__new
            | stm_bind s k =>
              v <- exec_aux s ;;
              exec_aux (k v)
            | stm_debugk k =>
              exec_aux k
            end.

      End ExecAux.

      (* The constructed closed executor. *)
      Fixpoint exec (inline_fuel : nat) : Exec :=
        match inline_fuel with
        | O   => fun _ _ _ => error
        | S n => @exec_aux (@exec n)
        end.
      Global Arguments exec _ {_ _} s _ _ _.

    End Exec.

    Section WithFuel.

      Variable inline_fuel : nat.

      Definition exec_contract {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) :
       Valuation (sep_contract_logic_variables c) -> CHeapSpecM Δ Δ unit :=
        match c with
        | MkSepContract _ _ _ _ req result ens =>
          fun ι =>
          _ <- produce ι req ;;
          v <- exec inline_fuel s ;;
          consume (env.snoc ι (result∷τ) v) ens
        end%mut.

      Definition vcgen {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
        ForallNamed (fun ι : Valuation (sep_contract_logic_variables c) =>
          let δΔ : CStore Δ := inst (sep_contract_localstore c) ι in
          (* We use the FINISH alias of True for the purpose of counting
             nodes in a shallowly-generated VC. *)
          exec_contract c body ι (fun _ _ _ => CPureSpecM.FINISH) δΔ nil).

    End WithFuel.

  End CHeapSpecM.

  Module Replay.
    Import SymProp.
    Import CPureSpecM.

    Definition replay_aux : forall {Σ} (ι : Valuation Σ) (s : 𝕊 Σ),
        CPureSpecM unit :=
      fix replay {Σ} ι s :=
        match s with
        | SymProp.angelic_binary o1 o2 =>
            angelic_binary (replay ι o1) (replay ι o2)
        | SymProp.demonic_binary o1 o2 =>
            demonic_binary (replay ι o1) (replay ι o2)
        | SymProp.block =>
            block
        | SymProp.error msg =>
            error
        | SymProp.assertk fml msg k =>
            bind (assert_formula (instprop fml ι))
              (fun _ => replay ι k)
        | SymProp.assumek fml k =>
            bind (assume_formula (instprop fml ι))
              (fun _ => replay ι k)
        | SymProp.angelicv b k =>
            bind (angelic _)
              (fun v => replay (env.snoc ι b v) k)
        | SymProp.demonicv b k =>
            bind (demonic _)
              (fun v => replay (env.snoc ι b v ) k)
        | @SymProp.assert_vareq _ x σ xIn t msg k =>
            let ι' := env.remove (x ∷ σ) ι xIn in
            let x' := ι.[? x∷σ] in
            let t' := inst t ι' in
            bind (assert_formula (x' = t'))
                 (fun _ => replay ι' k)
        | @SymProp.assume_vareq _ x σ xIn t k =>
            let ι' := env.remove (x ∷ σ) ι xIn in
            let x' := ι.[? x∷σ] in
            let t' := inst t ι' in
            bind (assume_formula (x' = t'))
                 (fun _ => replay ι' k)
        | SymProp.pattern_match s pat rhs =>
            error
        | SymProp.pattern_match_var x pat rhs =>
            error
        | SymProp.debug b k =>
            replay ι k
        end.

    Definition replay {Σ} (ι : Valuation Σ) (s : 𝕊 Σ) : Prop :=
      replay_aux ι s (fun _ => TRUE).
  End Replay.

  Module Shallow.

    Definition ValidContractWithFuel {Δ τ} (fuel : nat) (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      CHeapSpecM.vcgen fuel c body.

    Definition ValidContract {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      (* Use inline_fuel = 1 by default. *)
      ValidContractWithFuel 1 c body.

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

      (* See: Building a Reification Tactic that Recurses Under Binders
         http://adam.chlipala.net/cpdt/html/Cpdt.Reflection.html

         This calculates a deeply-embedded PropShape for a given Prop P
         for which we can then run shape_to_stats to calculate the
         number of different kinds of execution paths. *)
      Ltac reifyProp P :=
        match eval simpl in P with
        | forall (x : ?T), CPureSpecM.TRUE => pspruned
        | forall (x : ?T), CPureSpecM.FALSE => pspruned
        | forall (x : ?T), CPureSpecM.FINISH => psfinish
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

      (* This typeclass approach seems to be much faster than the reifyProp
      tactic above. *)
      Class ShallowStats (P : Prop) :=
        stats : Stats.
      Arguments stats P {_}.

      (* We make these instances global so that users can simply use the
         calc tactic qualified without importing the rest of this module. *)
      #[global] Instance stats_true : ShallowStats CPureSpecM.TRUE :=
        {| branches := 1; pruned := 1 |}.
      #[global] Instance stats_false : ShallowStats CPureSpecM.FALSE :=
        {| branches := 1; pruned := 1 |}.
      #[global] Instance stats_finish : ShallowStats CPureSpecM.FINISH :=
        {| branches := 1; pruned := 0 |}.
      (* We do not count regular True and False towards the statistics
         because they do not (should not) represent leaves of the shallow
         execution. *)
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

      Ltac calc fnc :=
        let P := eval compute - [CPureSpecM.FALSE CPureSpecM.TRUE CPureSpecM.FINISH
                                 negb Z.mul Z.opp Z.compare Z.add Z.geb Z.eqb
                                 Z.leb Z.gtb Z.ltb Z.le Z.lt Z.gt Z.ge Z.of_nat
                                 List.app List.length rev rev_append
            ] in
                   (match CEnv fnc with
                    | Some c => Shallow.ValidContract c (FunDef fnc)
                    | None => False
                    end) in
        let s := eval compute in (stats P) in s.

    End Statistics.

  End Shallow.

End ShallowExecOn.

Module MakeShallowExecutor
  (Import B    : Base)
  (Import PROG : Program B)
  (Import SIG : Signature B)
  (Import SPEC : Specification B PROG SIG).

  Include ShallowExecOn B PROG SIG SPEC.

End MakeShallowExecutor.
