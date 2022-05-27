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
     Program.Tactics
     Strings.String
     ZArith.BinInt.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Notations
     Prelude
     Specification.

From stdpp Require base list option.

Import ctx.notations.
Import env.notations.
Import ListNotations.

Set Implicit Arguments.

Module Type SemiConcrete (Import B : Base) (Import SIG : ProgramLogicSignature B) (Import SPEC : Specification B SIG).

  Definition CDijkstra (A : Type) : Type :=
    (A -> Prop) -> Prop.

  Module CDijk.

    Definition pure {A : Type} :
      A -> CDijkstra A :=
      fun a POST => POST a.

    Definition map {A B} :
      (A -> B) -> CDijkstra A -> CDijkstra B :=
      fun f m POST => m (Basics.compose POST f).

    Definition bind {A B} :
      CDijkstra A -> (A -> CDijkstra B) -> CDijkstra B :=
      fun m f POST => m (fun a1 => f a1 POST).

    Local Notation "x <- ma ;; mb" :=
      (bind ma (fun x => mb))
        (at level 80, ma at level 90, mb at level 200, right associativity).

    Definition angelic σ : CDijkstra (Val σ) :=
      fun POST => exists v : Val σ, POST v.

    Definition angelic_ctx {N : Set} :
      forall Δ : NCtx N Ty, CDijkstra (NamedEnv Val Δ) :=
      fix rec Δ {struct Δ} :=
        match Δ with
        | []%ctx  => pure []
        | Δ ▻ x∷σ => v  <- angelic σ;;
                     vs <- rec Δ;;
                     pure (vs ► (x∷σ ↦ v))
        end.
    Arguments angelic_ctx {N} Δ.

    Definition demonic σ : CDijkstra (Val σ) :=
      fun POST => forall v : Val σ, POST v.

    Definition demonic_ctx {N : Set} :
      forall Δ : NCtx N Ty, CDijkstra (NamedEnv Val Δ) :=
      fix rec Δ {struct Δ} :=
        match Δ with
        | []      => fun k => k env.nil
        | Δ ▻ x∷σ => fun k =>
            demonic σ (fun v => rec Δ (fun EΔ => k (EΔ ► (x∷σ ↦ v))))
        end%ctx.
    Arguments demonic_ctx {N} Δ.

    Definition assume_formula (fml : Prop) : CDijkstra unit :=
      fun POST => fml -> POST tt.

    Definition assert_formula (fml : Prop) : CDijkstra unit :=
      fun POST => fml /\ POST tt.

    Definition assume_formulas {Σ} (ι : Valuation Σ) : List Formula Σ -> CDijkstra unit.
      refine (
        fix assumes fmls0 :=
        match fmls0 with
        | nil           => pure tt
        | cons fml fmls1 => _
        end).
      eapply bind.
      apply (assumes fmls1).
      intros _.
      apply assume_formula.
      apply (inst fml ι).
    Defined.

    Definition assert_formulas {Σ} (ι : Valuation Σ) : List Formula Σ -> CDijkstra unit.
      refine (
        fix asserts fmls0 :=
        match fmls0 with
        | nil           => pure tt
        | cons fml fmls1 => _
        end).
      eapply bind.
      apply (asserts fmls1).
      intros _.
      apply assert_formula.
      apply (inst fml ι).
    Defined.

    Definition angelic_binary {A} :
      CDijkstra A -> CDijkstra A -> CDijkstra A :=
      fun m1 m2 POST =>
        m1 POST \/ m2 POST.
    Definition demonic_binary {A} :
      CDijkstra A -> CDijkstra A -> CDijkstra A :=
      fun m1 m2 POST =>
        m1 POST /\ m2 POST.

    Definition angelic_list {A} :
      list A -> CDijkstra A :=
      fix rec xs :=
        match xs with
        | nil        => fun POST => False
        | cons x xs  => angelic_binary (pure x) (rec xs)
        end.

    Definition demonic_list {A} :
      list A -> CDijkstra A :=
      fix rec xs :=
        match xs with
        | nil        => fun POST => True
        | cons x xs  => demonic_binary (pure x) (rec xs)
        end.

    Definition angelic_finite F `{finite.Finite F} :
      CDijkstra F :=
      angelic_list (finite.enum F).

    Definition demonic_finite F `{finite.Finite F} :
      CDijkstra F :=
      demonic_list (finite.enum F).

    Definition angelic_match_bool :
      Val ty.bool -> CDijkstra bool :=
      fun v =>
        angelic_binary
          (bind
             (assert_formula (v = true))
             (fun _ => pure true))
          (bind
             (assert_formula (v = false))
             (fun _ => pure false)).

    Definition demonic_match_bool :
      Val ty.bool -> CDijkstra bool :=
      fun v =>
        demonic_binary
          (bind
             (assume_formula (v = true))
             (fun _ => pure true))
          (bind
             (assume_formula (v = false))
             (fun _ => pure false)).

    Lemma wp_angelic_ctx {N : Set} {Δ : NCtx N Ty} (POST : NamedEnv Val Δ -> Prop) :
      angelic_ctx Δ POST <-> exists vs : NamedEnv Val Δ, POST vs.
    Proof.
      induction Δ; cbn.
      - split.
        + now exists env.nil.
        + intros [vs ?]. now destruct (env.nilView vs).
      - destruct b as [x σ].
        unfold angelic. split.
        + intros [v Hwp]. apply IHΔ in Hwp.
          destruct Hwp as [vs HPOST].
          now exists (env.snoc vs (x∷σ) v).
        + intros [vs Hwp]. destruct (env.snocView vs) as [vs v].
          exists v. apply IHΔ. now exists vs.
    Qed.

    Lemma wp_demonic_ctx {N : Set} {Δ : NCtx N Ty} (POST : NamedEnv Val Δ -> Prop) :
      demonic_ctx Δ POST <-> forall vs : NamedEnv Val Δ, POST vs.
    Proof.
      induction Δ; cbn.
      - split.
        + intros ? vs.
          now destruct (env.nilView vs).
        + now intuition.
      - destruct b as [x σ].
        unfold demonic. split.
        + intros Hwp vs.
          destruct (env.snocView vs) as [vs v].
          now eapply (IHΔ (fun vs => POST (env.snoc vs _ v))).
        + intros HPost v.
          now eapply (IHΔ (fun vs => POST (env.snoc vs (x∷σ) v))).
    Qed.

    Lemma wp_angelic_list {A} (xs : list A) (POST : A -> Prop) :
      angelic_list xs POST <->
      exists x : A, List.In x xs /\ POST x.
    Proof.
      induction xs; cbn.
      - firstorder.
      - cbv [angelic_binary pure].
        rewrite IHxs; clear IHxs.
        firstorder. left. now subst.
    Qed.

    Lemma wp_demonic_list {A} (xs : list A) (POST : A -> Prop) :
      demonic_list xs POST <->
      forall x : A, List.In x xs -> POST x.
    Proof.
      induction xs; cbn.
      - firstorder.
      - cbv [demonic_binary pure].
        rewrite IHxs; clear IHxs.
        firstorder. now subst.
    Qed.

    Lemma wp_assume_formulas {Σ} (ι : Valuation Σ) (fmls : List Formula Σ) :
      forall POST,
        assume_formulas ι fmls POST <->
        (instpc fmls ι -> POST tt).
    Proof.
      induction fmls; cbn; cbv [pure bind].
      - intuition.
      - intros POST.
        rewrite IHfmls.
        unfold assume_formula.
        intuition.
    Qed.

    Lemma wp_assert_formulas {Σ} (ι : Valuation Σ) (fmls : List Formula Σ) :
      forall POST,
        assert_formulas ι fmls POST <->
        (instpc fmls ι /\ POST tt).
    Proof.
      induction fmls; cbn; cbv [pure bind].
      - cbv. intuition.
      - intros POST.
        rewrite IHfmls.
        unfold assert_formula.
        intuition.
    Qed.

  End CDijk.

  Definition CMut (Γ1 Γ2 : PCtx) (A : Type) : Type :=
    (A -> CStore Γ2 -> SCHeap -> Prop) -> CStore Γ1 -> SCHeap -> Prop.
  Bind Scope mut_scope with CMut.

  Local Open Scope mut_scope.

  Module CMut.

    Section Basic.

      Definition dijkstra {Γ} {A : Type} :
        CDijkstra A -> CMut Γ Γ A :=
        fun m POST δ h => m (fun a => POST a δ h).

      Definition pure {Γ A} (a : A) : CMut Γ Γ A :=
        fun POST => POST a.
      Definition bind {Γ1 Γ2 Γ3 A B} (ma : CMut Γ1 Γ2 A) (f : A -> CMut Γ2 Γ3 B) : CMut Γ1 Γ3 B :=
        fun POST => ma (fun a => f a POST).
      Definition bind_right {Γ1 Γ2 Γ3 A B} (ma : CMut Γ1 Γ2 A) (mb : CMut Γ2 Γ3 B) : CMut Γ1 Γ3 B :=
        bind ma (fun _ => mb).
      Definition bind_left {Γ1 Γ2 Γ3 A B} (ma : CMut Γ1 Γ2 A) (mb : CMut Γ2 Γ3 B) : CMut Γ1 Γ3 A :=
        bind ma (fun a => bind mb (fun _ => pure a)).
      Definition map {Γ1 Γ2 A B} (f : A -> B) (ma : CMut Γ1 Γ2 A) : CMut Γ1 Γ2 B :=
        fun POST => ma (fun a => POST (f a)).

      Definition error {Γ1 Γ2 A} (msg : string) : CMut Γ1 Γ2 A :=
        fun POST δ h => False.
      Definition block {Γ1 Γ2 A} : CMut Γ1 Γ2 A :=
        fun POST δ h => True.

      Definition demonic_binary {Γ1 Γ2 A} (m1 m2 : CMut Γ1 Γ2 A) : CMut Γ1 Γ2 A :=
        fun POST δ h => m1 POST δ h /\ m2 POST δ h.
      Definition angelic_binary {Γ1 Γ2 A} (m1 m2 : CMut Γ1 Γ2 A) : CMut Γ1 Γ2 A :=
        fun POST δ h => m1 POST δ h \/ m2 POST δ h.

      (* Definition demonic {Γ1 Γ2 I A} (ms : I -> CMut Γ1 Γ2 A) : CMut Γ1 Γ2 A := *)
      (*   fun POST δ h => forall i : I, ms i POST δ h. *)
      Definition demonic {Γ} (σ : Ty) : CMut Γ Γ (Val σ) :=
        fun POST δ h => forall v : Val σ, POST v δ h.
      Definition angelic {Γ} (σ : Ty) : CMut Γ Γ (Val σ) :=
        fun POST δ h => exists v : Val σ, POST v δ h.
      (* Definition angelic {Γ1 Γ2 I A} (ms : I -> CMut Γ1 Γ2 A) : CMut Γ1 Γ2 A := *)
      (*   fun POST δ h => exists i : I, ms i POST δ h. *)

      Definition angelic_ctx {N : Set} {Γ} :
        forall Δ : NCtx N Ty, CMut Γ Γ (NamedEnv Val Δ).
      Proof.
        intros Δ. apply dijkstra.
        apply (CDijk.angelic_ctx Δ).
      Defined.
      Global Arguments angelic_ctx {N Γ} Δ.

      Definition angelic_list {A Γ} (xs : list A) : CMut Γ Γ A :=
        dijkstra (CDijk.angelic_list xs).

      Definition angelic_finite {Γ} F `{finite.Finite F} : CMut Γ Γ F :=
        dijkstra (CDijk.angelic_finite (F:=F)).

      Definition demonic_finite {Γ} F `{finite.Finite F} : CMut Γ Γ F :=
        dijkstra (CDijk.demonic_finite (F:=F)).

      Definition demonic_ctx {N : Set} {Γ} :
        forall Δ : NCtx N Ty, CMut Γ Γ (NamedEnv Val Δ).
      Proof.
        intros Δ. apply dijkstra.
        apply (CDijk.demonic_ctx Δ).
      Defined.
      Global Arguments demonic_ctx {N Γ} Δ.

    End Basic.

    Module CMutNotations.

      (* Notation "'⨂' x .. y => F" := *)
      (*   (cmut_demonic (fun x => .. (cmut_demonic (fun y => F)) .. )) : mut_scope. *)

      (* Notation "'⨁' x .. y => F" := *)
      (*   (cmut_angelic (fun x => .. (cmut_angelic (fun y => F)) .. )) : mut_scope. *)

      Infix "⊗" := demonic_binary (at level 40, left associativity) : mut_scope.
      Infix "⊕" := angelic_binary (at level 50, left associativity) : mut_scope.

      Notation "' x <- ma ;; mb" :=
        (bind ma (fun x => mb))
          (at level 80, x pattern, ma at next level, mb at level 200, right associativity,
           format "' x  <-  ma  ;;  mb") : mut_scope.
      Notation "x <- ma ;; mb" :=
        (bind ma (fun x => mb))
          (at level 80, ma at level 90, mb at level 200, right associativity) : mut_scope.
      Notation "ma >>= f" := (bind ma f) (at level 50, left associativity) : mut_scope.
      Notation "m1 ;; m2" := (bind_right m1 m2) : mut_scope.
      Notation "ma *> mb" := (bind_right ma mb) (at level 50, left associativity) : mut_scope.
      Notation "ma <* mb" := (bind_left ma mb) (at level 50, left associativity) : mut_scope.

    End CMutNotations.
    Import CMutNotations.
    Local Open Scope mut_scope.

    Section AssumeAssert.

      Definition assume_formula {Γ} (fml : Prop) : CMut Γ Γ unit :=
        dijkstra (CDijk.assume_formula fml).
      Definition assert_formula {Γ} (fml : Prop) : CMut Γ Γ unit :=
        dijkstra (CDijk.assert_formula fml).
      Definition assume_formulas {Γ Σ} (ι : Valuation Σ) (fmls : list (Formula Σ)) : CMut Γ Γ unit :=
        dijkstra (CDijk.assume_formulas ι fmls).
      Definition assert_formulas {Γ Σ} (ι : Valuation Σ) (fmls : list (Formula Σ)) : CMut Γ Γ unit :=
        dijkstra (CDijk.assert_formulas ι fmls).

    End AssumeAssert.

    Section PatternMatching.

      Definition angelic_match_bool {A Γ1 Γ2} (v : Val ty.bool) (kt kf : CMut Γ1 Γ2 A) : CMut Γ1 Γ2 A.
      Proof.
        apply angelic_binary.
        - eapply bind_right.
          apply assert_formula.
          apply (v = true).
          apply kt.
        - eapply bind_right.
          apply assert_formula.
          apply (v = false).
          apply kf.
      Defined.

      Lemma wp_angelic_match_bool {A Γ1 Γ2} (v : Val ty.bool) (kt kf : CMut Γ1 Γ2 A) :
        forall POST δ h,
          angelic_match_bool v kt kf POST δ h <->
          if v then kt POST δ h else kf POST δ h.
      Proof.
        cbv [angelic_match_bool angelic_binary bind_right bind assert_formula
             dijkstra CDijk.assert_formula is_true negb].
        destruct v; intuition; discriminate.
      Qed.

      Definition demonic_match_bool {A Γ1 Γ2} (v : Val ty.bool) (kt kf : CMut Γ1 Γ2 A) : CMut Γ1 Γ2 A.
      Proof.
        apply demonic_binary.
        - eapply bind_right.
          apply assume_formula.
          apply (v = true).
          apply kt.
        - eapply bind_right.
          apply assume_formula.
          apply (v = false).
          apply kf.
      Defined.

      Lemma wp_demonic_match_bool {A Γ1 Γ2} (v : Val ty.bool) (kt kf : CMut Γ1 Γ2 A) :
        forall POST δ h,
          demonic_match_bool v kt kf POST δ h <->
          if v then kt POST δ h else kf POST δ h.
      Proof.
        cbv [demonic_match_bool demonic_binary bind_right bind assume_formula
             dijkstra CDijk.assume_formula is_true negb].
        destruct v; intuition; discriminate.
      Qed.

      Definition angelic_match_enum {A E} {Γ1 Γ2} :
        Val (ty.enum E) -> (enumt E -> CMut Γ1 Γ2 A) -> CMut Γ1 Γ2 A.
      Proof.
        intros v cont.
        eapply bind.
        apply (angelic_finite (F := enumt E)).
        intros EK.
        eapply bind_right.
        apply (assert_formula (v = EK)).
        apply (cont EK).
      Defined.

      Definition demonic_match_enum {A E} {Γ1 Γ2} :
        Val (ty.enum E) -> (enumt E -> CMut Γ1 Γ2 A) -> CMut Γ1 Γ2 A.
      Proof.
        intros v cont.
        eapply bind.
        apply (demonic_finite (F := enumt E)).
        intros EK.
        eapply bind_right.
        apply (assume_formula (v = EK)).
        apply (cont EK).
      Defined.

      Lemma wp_angelic_match_enum {A E Γ1 Γ2} (v : Val (ty.enum E)) (k : enumt E -> CMut Γ1 Γ2 A) :
        forall POST δ h,
          angelic_match_enum v k POST δ h <-> k v POST δ h.
      Proof.
        cbv [assert_formula bind bind_right angelic_match_enum angelic_finite
             dijkstra CDijk.angelic_finite CDijk.assert_formula].
        intros. rewrite CDijk.wp_angelic_list.
        split; intros; destruct_conjs; subst; auto.
        exists v. split; auto.
        rewrite <- base.elem_of_list_In.
        apply finite.elem_of_enum.
      Qed.

      Lemma wp_demonic_match_enum {A E Γ1 Γ2} (v : Val (ty.enum E)) (k : enumt E -> CMut Γ1 Γ2 A) :
        forall POST δ h,
          demonic_match_enum v k POST δ h <-> k v POST δ h.
      Proof.
        cbv [assume_formula bind bind_right demonic_match_enum demonic_finite
             dijkstra CDijk.demonic_finite CDijk.assume_formula].
        intros. rewrite CDijk.wp_demonic_list.
        split; intros; subst; auto.
        apply H; auto.
        rewrite <- base.elem_of_list_In.
        apply finite.elem_of_enum.
      Qed.

      Definition angelic_match_sum {A Γ1 Γ2} {σ τ} :
        Val (ty.sum σ τ) -> (Val σ -> CMut Γ1 Γ2 A) -> (Val τ -> CMut Γ1 Γ2 A) -> CMut Γ1 Γ2 A.
      Proof.
        intros v kinl kinr.
        apply angelic_binary.
        - eapply bind.
          apply (angelic σ).
          intros v1.
          eapply bind_right.
          apply assert_formula.
          apply (inl v1 = v).
          apply kinl. auto.
        - eapply bind.
          apply (angelic τ).
          intros v1.
          eapply bind_right.
          apply assert_formula.
          apply (inr v1 = v).
          apply kinr. auto.
      Defined.

      Definition demonic_match_sum {A Γ1 Γ2} {σ τ} :
        Val (ty.sum σ τ) -> (Val σ -> CMut Γ1 Γ2 A) -> (Val τ -> CMut Γ1 Γ2 A) -> CMut Γ1 Γ2 A.
      Proof.
        intros v kinl kinr.
        apply demonic_binary.
        - eapply bind.
          apply (demonic σ).
          intros v1.
          eapply bind_right.
          apply assume_formula.
          apply (inl v1 = v).
          apply kinl. auto.
        - eapply bind.
          apply (demonic τ).
          intros v1.
          eapply bind_right.
          apply assume_formula.
          apply (inr v1 = v).
          apply kinr. auto.
      Defined.

      Lemma wp_angelic_match_sum {A Γ1 Γ2} {σ τ}
        (v : Val (ty.sum σ τ)) (kinl : Val σ -> CMut Γ1 Γ2 A) (kinr : Val τ -> CMut Γ1 Γ2 A) POST δ h :
        angelic_match_sum v kinl kinr POST δ h <->
        match v with
        | inl v => kinl v POST δ h
        | inr v => kinr v POST δ h
        end.
      Proof.
        cbv [angelic_match_sum bind_right bind angelic angelic_binary
             assert_formula dijkstra CDijk.assert_formula].
        split.
        - intros []; destruct_conjs; subst; auto.
        - destruct v as [v|v]; [left|right]; exists v; intuition.
      Qed.

      Lemma wp_demonic_match_sum {A Γ1 Γ2} {σ τ}
        (v : Val (ty.sum σ τ)) (kinl : Val σ -> CMut Γ1 Γ2 A) (kinr : Val τ -> CMut Γ1 Γ2 A) POST δ h :
        demonic_match_sum v kinl kinr POST δ h <->
        match v with
        | inl v => kinl v POST δ h
        | inr v => kinr v POST δ h
        end.
      Proof.
        cbv [demonic_match_sum bind_right bind demonic demonic_binary
             assume_formula dijkstra CDijk.assume_formula].
        split.
        - destruct v; intuition.
        - destruct v; intuition; try discriminate;
            match goal with
            | H: inl _ = inl _ |- _ => apply noConfusion_inv in H; cbn in H; subst
            | H: inr _ = inr _ |- _ => apply noConfusion_inv in H; cbn in H; subst
            end; auto.
      Qed.

      Definition angelic_match_prod {A Γ1 Γ2} {σ τ} :
        Val (ty.prod σ τ) -> (Val σ -> Val τ -> CMut Γ1 Γ2 A) -> CMut Γ1 Γ2 A :=
        fun v k =>
          v1 <- angelic σ ;;
          v2 <- angelic τ ;;
          assert_formula ((v1,v2) = v) ;;
          k v1 v2.

      Lemma wp_angelic_match_prod {A Γ1 Γ2} {σ τ}
        (v : Val (ty.prod σ τ)) (k : Val σ -> Val τ -> CMut Γ1 Γ2 A) POST δ h :
        angelic_match_prod v k POST δ h <->
        match v with
        | pair v1 v2 => k v1 v2 POST δ h
        end.
      Proof.
        cbv [angelic_match_prod bind_right bind angelic angelic_binary
             assert_formula dijkstra CDijk.assert_formula].
        destruct v; intuition.
        - destruct H as (v1 & v2 & eq & H).
          inversion eq; now subst.
        - now exists v, v0.
      Qed.

      Definition demonic_match_prod {A Γ1 Γ2} {σ τ} :
        Val (ty.prod σ τ) -> (Val σ -> Val τ -> CMut Γ1 Γ2 A) -> CMut Γ1 Γ2 A :=
        fun v k =>
          v1 <- demonic σ ;;
          v2 <- demonic τ ;;
          assume_formula ((v1,v2) = v) ;;
          k v1 v2.

      Lemma wp_demonic_match_prod {A Γ1 Γ2} {σ τ}
        (v : Val (ty.prod σ τ)) (k : Val σ -> Val τ -> CMut Γ1 Γ2 A) POST δ h :
        demonic_match_prod v k POST δ h <->
        match v with
        | pair v1 v2 => k v1 v2 POST δ h
        end.
      Proof.
        cbv [demonic_match_prod bind_right bind demonic demonic_binary
             assume_formula dijkstra CDijk.assume_formula].
        destruct v; intuition.
      Qed.

      Definition angelic_match_list {A Γ1 Γ2} {σ} :
        Val (ty.list σ) -> (CMut Γ1 Γ2 A) -> (Val σ -> Val (ty.list σ) -> CMut Γ1 Γ2 A) -> CMut Γ1 Γ2 A.
      Proof.
        intros v knil kcons.
        apply angelic_binary.
        - eapply bind_right.
          apply assert_formula.
          apply (nil = v).
          apply knil.
        - eapply bind.
          apply (angelic σ).
          intros vhead.
          eapply bind.
          apply (angelic (ty.list σ)).
          intros vtail.
          eapply bind_right.
          apply assert_formula.
          apply (cons vhead vtail = v).
          apply (kcons vhead vtail).
      Defined.

      Lemma wp_angelic_match_list {A Γ1 Γ2} {σ}
        (v : Val (ty.list σ)) (knil : CMut Γ1 Γ2 A) (kcons : Val σ -> Val (ty.list σ) -> CMut Γ1 Γ2 A) POST δ h :
        angelic_match_list v knil kcons POST δ h <->
        match v with
        | nil => knil POST δ h
        | cons vh vt => kcons vh vt POST δ h
        end.
      Proof.
        cbv [angelic_match_list bind_right bind angelic angelic_binary
             assert_formula dijkstra CDijk.assert_formula].
        split.
        - intros []; destruct_conjs; subst; auto.
        - destruct v as [|vh vt]; [left;auto|right].
          exists vh, vt. auto.
      Qed.

      Definition demonic_match_list {A Γ1 Γ2} {σ} :
        Val (ty.list σ) -> (CMut Γ1 Γ2 A) -> (Val σ -> Val (ty.list σ) -> CMut Γ1 Γ2 A) -> CMut Γ1 Γ2 A.
      Proof.
        intros v knil kcons.
        apply demonic_binary.
        - eapply bind_right.
          apply assume_formula.
          apply (nil = v).
          apply knil.
        - eapply bind.
          apply (demonic σ).
          intros vhead.
          eapply bind.
          apply (demonic (ty.list σ)).
          intros vtail.
          eapply bind_right.
          apply assume_formula.
          apply (cons vhead vtail = v).
          apply (kcons vhead vtail).
      Defined.

      Lemma wp_demonic_match_list {A Γ1 Γ2} {σ}
        (v : Val (ty.list σ)) (knil : CMut Γ1 Γ2 A) (kcons : Val σ -> Val (ty.list σ) -> CMut Γ1 Γ2 A) POST δ h :
        demonic_match_list v knil kcons POST δ h <->
        match v with
        | nil => knil POST δ h
        | cons vh vt => kcons vh vt POST δ h
        end.
      Proof.
        cbv [demonic_match_list bind_right bind demonic demonic_binary
             assume_formula dijkstra CDijk.assume_formula].
        split.
        - destruct v; intuition.
        - destruct v; intuition; try discriminate.
      Qed.

      Definition angelic_match_record {N : Set} {A R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (recordf_ty R) Δ) :
        (Val (ty.record R)) ->
        (NamedEnv Val Δ -> CMut Γ1 Γ2 A) ->
        CMut Γ1 Γ2 A :=
        fun v k =>
          args <- angelic_ctx Δ ;;
          assert_formula (recordv_fold R (record_pattern_match_env_reverse p args) = v) ;;
          k args.

      Lemma wp_angelic_match_record {N : Set} {A R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (recordf_ty R) Δ)
        (v : Val (ty.record R))
        (k : NamedEnv Val Δ -> CMut Γ1 Γ2 A)
        POST δ h :
        angelic_match_record p v k POST δ h <->
        k (record_pattern_match_val p v) POST δ h.
      Proof.
        cbv [angelic_match_record bind_right bind angelic_ctx dijkstra assert_formula CDijk.assert_formula].
        rewrite CDijk.wp_angelic_ctx; intuition.
        - destruct H as (vs & <- & H).
          unfold record_pattern_match_val.
          now rewrite recordv_unfold_fold, record_pattern_match_env_inverse_right.
        - exists (record_pattern_match_val p v).
          unfold record_pattern_match_val.
          now rewrite record_pattern_match_env_inverse_left, recordv_fold_unfold.
      Qed.

      Definition demonic_match_record {N : Set} {A R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (recordf_ty R) Δ) :
        (Val (ty.record R)) ->
        (NamedEnv Val Δ -> CMut Γ1 Γ2 A) ->
        CMut Γ1 Γ2 A :=
        fun v k =>
          args <- demonic_ctx Δ ;;
          assume_formula (recordv_fold R (record_pattern_match_env_reverse p args) = v) ;;
          k args.

      Lemma wp_demonic_match_record {N : Set} {A R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (recordf_ty R) Δ)
        (v : Val (ty.record R))
        (k : NamedEnv Val Δ -> CMut Γ1 Γ2 A)
        POST δ h :
        demonic_match_record p v k POST δ h <->
        k (record_pattern_match_val p v) POST δ h.
      Proof.
        cbv [demonic_match_record bind_right bind demonic_ctx dijkstra assume_formula CDijk.assume_formula].
        rewrite CDijk.wp_demonic_ctx; intuition; eauto.
        eapply H.
        - unfold record_pattern_match_val.
          now rewrite record_pattern_match_env_inverse_left, recordv_fold_unfold.
        - unfold record_pattern_match_val in H.
          replace (record_pattern_match_env p (recordv_unfold R v)) with vs in H; [assumption|].
          subst.
          now rewrite recordv_unfold_fold, record_pattern_match_env_inverse_right.
      Qed.

      Definition angelic_match_tuple {N : Set} {A σs Γ1 Γ2} {Δ : NCtx N Ty} (p : TuplePat σs Δ) :
        (Val (ty.tuple σs)) ->
        (NamedEnv Val Δ -> CMut Γ1 Γ2 A) ->
        CMut Γ1 Γ2 A :=
        fun v k =>
          args <- angelic_ctx Δ ;;
          assert_formula (tuple_pattern_match_val p v = args) ;;
          k args.

      Lemma wp_angelic_match_tuple {N : Set} {A σs Γ1 Γ2} {Δ : NCtx N Ty} (p : TuplePat σs Δ)
        (v : Val (ty.tuple σs))
        (k : NamedEnv Val Δ -> CMut Γ1 Γ2 A)
        POST δ h :
        angelic_match_tuple p v k POST δ h <->
        k (tuple_pattern_match_val p v) POST δ h.
      Proof.
        cbv [angelic_match_tuple bind_right bind angelic_ctx dijkstra assert_formula CDijk.assert_formula].
        rewrite CDijk.wp_angelic_ctx; intuition.
        - now destruct H as (vs & <- & H).
        - exists (tuple_pattern_match_val p v).
          split; auto.
      Qed.

      Definition demonic_match_tuple {N : Set} {A σs Γ1 Γ2} {Δ : NCtx N Ty} (p : TuplePat σs Δ) :
        (Val (ty.tuple σs)) ->
        (NamedEnv Val Δ -> CMut Γ1 Γ2 A) ->
        CMut Γ1 Γ2 A :=
        fun v k =>
          args <- demonic_ctx Δ ;;
          assume_formula (tuple_pattern_match_val p v = args) ;;
          k args.

      Lemma wp_demonic_match_tuple {N : Set} {A σs Γ1 Γ2} {Δ : NCtx N Ty} (p : TuplePat σs Δ)
        (v : Val (ty.tuple σs))
        (k : NamedEnv Val Δ -> CMut Γ1 Γ2 A)
        POST δ h :
        demonic_match_tuple p v k POST δ h <->
        k (tuple_pattern_match_val p v) POST δ h.
      Proof.
        cbv [demonic_match_tuple bind_right bind demonic_ctx dijkstra assume_formula CDijk.assume_formula].
        rewrite CDijk.wp_demonic_ctx; intuition; subst; auto.
      Qed.

      Definition angelic_match_pattern {N : Set} {σ} {Δ : NCtx N Ty} (p : Pattern Δ σ) {Γ} :
        Val σ -> CMut Γ Γ (NamedEnv Val Δ).
      Proof.
        intros v.
        eapply bind.
        apply (angelic_ctx Δ).
        intros vs.
        eapply bind_right.
        apply assert_formula.
        apply (pattern_match_val p v = vs).
        apply pure.
        apply vs.
      Defined.

      Lemma wp_angelic_match_pattern {N : Set} {σ Γ} {Δ : NCtx N Ty} (p : Pattern Δ σ)
        (v : Val σ)
        POST δ h :
        angelic_match_pattern (Γ := Γ) p v POST δ h <->
        POST (pattern_match_val p v) δ h.
      Proof.
        cbv [angelic_match_pattern bind pure angelic_ctx bind_right assert_formula
             dijkstra CDijk.assert_formula].
        rewrite CDijk.wp_angelic_ctx.
        split.
        - now intros (vs & <- & H).
        - intros ?. exists (pattern_match_val p v).
          split; auto.
      Qed.

      Definition demonic_match_pattern {N : Set} {σ} {Δ : NCtx N Ty} (p : Pattern Δ σ) {Γ} :
        Val σ -> CMut Γ Γ (NamedEnv Val Δ).
      Proof.
        intros v.
        eapply bind.
        apply (demonic_ctx Δ).
        intros vs.
        eapply bind_right.
        apply assume_formula.
        apply (pattern_match_val p v = vs).
        apply pure.
        apply vs.
      Defined.

      Lemma wp_demonic_match_pattern {N : Set} {σ Γ} {Δ : NCtx N Ty} (p : Pattern Δ σ)
        (v : Val σ)
        POST δ h :
        demonic_match_pattern (Γ := Γ) p v POST δ h <->
        POST (pattern_match_val p v) δ h.
      Proof.
        cbv [demonic_match_pattern bind pure demonic_ctx bind_right assume_formula
             dijkstra CDijk.assume_formula].
        rewrite CDijk.wp_demonic_ctx.
        intuition; subst; auto.
      Qed.

      Definition angelic_match_union {N : Set} {A Γ1 Γ2 U}
        {Δ : unionk U -> NCtx N Ty} (p : forall K : unionk U, Pattern (Δ K) (unionk_ty U K)) :
        Val (ty.union U) -> (forall K, NamedEnv Val (Δ K) -> CMut Γ1 Γ2 A) -> CMut Γ1 Γ2 A.
      Proof.
        intros v k.
        eapply bind.
        apply (angelic_finite (F := unionk U)).
        intros UK.
        eapply bind.
        apply (angelic (unionk_ty U UK)).
        intros v__field.
        eapply bind_right.
        apply assert_formula.
        apply (unionv_fold U (existT UK v__field) = v).
        eapply bind.
        apply (angelic_match_pattern (p UK)).
        apply v__field.
        apply (k UK).
      Defined.

      Lemma wp_angelic_match_union {N : Set} {A Γ1 Γ2 U}
        {Δ : unionk U -> NCtx N Ty} (p : forall K : unionk U, Pattern (Δ K) (unionk_ty U K))
        (v : Val (ty.union U)) (k : forall K, NamedEnv Val (Δ K) -> CMut Γ1 Γ2 A)
        POST δ h :
        angelic_match_union p v k POST δ h <->
        let (UK , vf) := unionv_unfold U v in
        k UK (pattern_match_val (p UK) vf) POST δ h.
      Proof.
        cbv [angelic_match_union bind bind_right angelic_finite assert_formula angelic
             dijkstra CDijk.angelic_finite CDijk.assert_formula].
        rewrite CDijk.wp_angelic_list.
        split.
        - intros (UK & HIn & vf & Heq & Hwp).
          rewrite wp_angelic_match_pattern in Hwp.
          subst v. now rewrite unionv_unfold_fold.
        - destruct (unionv_unfold U v) as [UK vf] eqn:Heq.
          intros Hwp.
          exists UK. split.
          rewrite <- base.elem_of_list_In.
          apply finite.elem_of_enum.
          exists vf. rewrite <- Heq.
          rewrite wp_angelic_match_pattern.
          rewrite unionv_fold_unfold. split; auto.
      Qed.

      Definition demonic_match_union {N : Set} {A Γ1 Γ2 U}
        {Δ : unionk U -> NCtx N Ty} (p : forall K : unionk U, Pattern (Δ K) (unionk_ty U K)) :
        Val (ty.union U) -> (forall K, NamedEnv Val (Δ K) -> CMut Γ1 Γ2 A) -> CMut Γ1 Γ2 A.
      Proof.
        intros v k.
        eapply bind.
        apply (demonic_finite (F := unionk U)).
        intros UK.
        eapply bind.
        apply (demonic (unionk_ty U UK)).
        intros v__field.
        eapply bind_right.
        apply assume_formula.
        apply (unionv_fold U (existT UK v__field) = v).
        eapply bind.
        apply (demonic_match_pattern (p UK)).
        apply v__field.
        apply (k UK).
      Defined.

      Lemma wp_demonic_match_union {N : Set} {A Γ1 Γ2 U}
        {Δ : unionk U -> NCtx N Ty} (p : forall K : unionk U, Pattern (Δ K) (unionk_ty U K))
        (v : Val (ty.union U)) (k : forall K, NamedEnv Val (Δ K) -> CMut Γ1 Γ2 A)
        POST δ h :
        demonic_match_union p v k POST δ h <->
        let (UK , vf) := unionv_unfold U v in
        k UK (pattern_match_val (p UK) vf) POST δ h.
      Proof.
        cbv [demonic_match_union bind bind_right demonic_finite assume_formula demonic
             dijkstra CDijk.demonic_finite CDijk.assume_formula].
        rewrite CDijk.wp_demonic_list.
        split.
        - destruct (unionv_unfold U v) as [UK vf] eqn:Heq.
          intros HYP. specialize (HYP UK).
          inster HYP by
              rewrite <- base.elem_of_list_In; apply finite.elem_of_enum.
          specialize (HYP vf).
          rewrite wp_demonic_match_pattern in HYP.
          apply HYP.
          now rewrite <- Heq, unionv_fold_unfold.
        - intros HYP UK HIn vf <-.
          rewrite unionv_unfold_fold in HYP.
          now rewrite wp_demonic_match_pattern.
      Qed.

      Definition demonic_match_bvec {A n} {Γ1 Γ2} :
        Val (ty.bvec n) -> (bv n -> CMut Γ1 Γ2 A) -> CMut Γ1 Γ2 A.
      Proof.
        intros v cont.
        eapply bind.
        apply (demonic_finite (F := bv n)).
        intros u.
        eapply bind_right.
        apply (assume_formula (v = u)).
        apply (cont u).
      Defined.
      Global Arguments demonic_match_bvec : simpl never.

      Lemma wp_demonic_match_bvec {A n Γ1 Γ2} (v : Val (ty.bvec n)) (k : bv n -> CMut Γ1 Γ2 A) :
        forall POST δ h,
          demonic_match_bvec v k POST δ h <-> k v POST δ h.
      Proof.
        cbv [assume_formula bind bind_right demonic_match_bvec demonic_finite
             dijkstra CDijk.demonic_finite CDijk.assume_formula].
        intros. rewrite CDijk.wp_demonic_list.
        split; intros; subst; auto.
        apply H; auto.
        rewrite <- base.elem_of_list_In.
        apply finite.elem_of_enum.
      Qed.

    End PatternMatching.

    Section State.

      Definition pushpop {A Γ1 Γ2 x σ} (v : Val σ)
        (d : CMut (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) A) : CMut Γ1 Γ2 A :=
        fun POST δ0 => d (fun a δ1 => POST a (env.tail δ1)) (δ0 ► (x∷σ ↦ v)).
      Definition pushspops {A} {Γ1 Γ2 Δ} (δΔ : CStore Δ)
        (d : CMut (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) A) : CMut Γ1 Γ2 A :=
        fun POST δ0 => d (fun a δ1 => POST a (env.drop Δ δ1)) (δ0 ►► δΔ).
      Definition get_local {Γ} : CMut Γ Γ (CStore Γ) :=
        fun POST δ => POST δ δ.
      Definition put_local {Γ1 Γ2} (δ : CStore Γ2) : CMut Γ1 Γ2 unit :=
        fun POST _ => POST tt δ.
      Definition get_heap {Γ} : CMut Γ Γ SCHeap :=
        fun POST δ h => POST h δ h.
      Definition put_heap {Γ} (h : SCHeap) : CMut Γ Γ unit :=
        fun POST δ _ => POST tt δ h.

      Definition eval_exp {Γ σ} (e : Exp Γ σ) : CMut Γ Γ (Val σ) :=
        fun POST δ => POST (eval e δ) δ.
      Definition eval_exps {Γ} {σs : PCtx} (es : NamedEnv (Exp Γ) σs) : CMut Γ Γ (CStore σs) :=
        fun POST δ => POST (evals es δ) δ.
      Definition assign {Γ} x {σ} {xIn : x∷σ ∈ Γ} (v : Val σ) : CMut Γ Γ unit :=
        fun POST δ => POST tt (δ ⟪ x ↦ v ⟫).
      Global Arguments assign {Γ} x {σ xIn} v.

    End State.

    (* Module NewProduceConsumeChunk. *)

    (*   Definition angelic_heap {Γ} : CMut Γ Γ SCHeap := *)
    (*     fun POST δ h => exists h', POST h' δ h. *)

    (*   Definition demonic_heap {Γ} : CMut Γ Γ SCHeap := *)
    (*     fun POST δ h => forall h', POST h' δ h. *)

    (*   Section WithHeaplet. *)

    (*     Context `{HL: IHeaplet L}. *)

    (*     Open Scope logic. *)
    (*     Import LogicNotations. *)

    (*     Fixpoint interpret_scchunk (c : SCChunk) : L := *)
    (*       match c with *)
    (*       | scchunk_user p vs => luser p vs *)
    (*       | scchunk_ptsreg r v => lptsreg r v *)
    (*       | scchunk_conj c1 c2 => sepcon (interpret_scchunk c1) (interpret_scchunk c2) *)
    (*       | scchunk_wand c1 c2 => wand (interpret_scchunk c1) (interpret_scchunk c2) *)
    (*       end. *)

    (*     Definition interpret_scheap : SCHeap -> L := *)
    (*       List.fold_right (fun c h => interpret_scchunk c ✱ h) emp. *)
    (*     Global Arguments interpret_scheap !h. *)

    (*     Definition produce_chunk {Γ} (c : SCChunk) : CMut Γ Γ unit := *)
    (*       h  <- get_heap ;; *)
    (*       h' <- demonic_heap ;; *)
    (*       assume_formula (interpret_scchunk c ✱ interpret_scheap h ⊢ interpret_scheap h') ;; *)
    (*       put_heap h'. *)

    (*     Definition consume_chunk {Γ} (c : SCChunk) : CMut Γ Γ unit := *)
    (*       h  <- get_heap ;; *)
    (*       h' <- angelic_heap ;; *)
    (*       assert_formula (interpret_scheap h ⊢ interpret_scchunk c ✱ interpret_scheap h') ;; *)
    (*       put_heap h'. *)

    (*   End WithHeaplet. *)

    (* End NewProduceConsumeChunk. *)

    Section ProduceConsume.

      Definition produce_chunk {Γ} (c : SCChunk) : CMut Γ Γ unit :=
        fun POST δ h => POST tt δ (cons c h).
      Definition consume_chunk {Γ} (c : SCChunk) : CMut Γ Γ unit :=
        h         <- get_heap ;;
        '(c', h') <- angelic_list (heap_extractions h) ;;
        assert_formula (c' = c) ;;
        put_heap h'.

      Global Arguments produce_chunk {Γ} _.
      Global Arguments consume_chunk {Γ} _.

      Fixpoint produce {Γ Σ} (ι : Valuation Σ) (asn : Assertion Σ) : CMut Γ Γ unit :=
        match asn with
        | asn_formula fml => assume_formula (inst fml ι)
        | asn_chunk c     => produce_chunk (inst c ι)
        | asn_chunk_angelic c => produce_chunk (inst c ι)
        | asn_if b a1 a2  => demonic_match_bool (inst b ι) (produce ι a1) (produce ι a2)
        | asn_match_enum E k alts =>
          demonic_match_enum
            (inst (T := fun Σ => Term Σ _) k ι)
            (fun K => produce ι (alts K))
        | asn_match_sum σ τ s xl alt_inl xr alt_inr =>
          demonic_match_sum
            (inst (T := fun Σ => Term Σ _) s ι)
            (fun v => produce (env.snoc ι (xl∷σ) v) alt_inl)
            (fun v => produce (env.snoc ι (xr∷τ) v) alt_inr)
        | asn_match_list s alt_nil xh xt alt_cons =>
          demonic_match_list
            (inst (T := fun Σ => Term Σ _) s ι)
            (produce ι alt_nil)
            (fun vh vt => produce (ι ► (xh∷_ ↦ vh) ► (xt∷ty.list _ ↦ vt)) alt_cons)
        | asn_match_prod s xl xr rhs =>
          demonic_match_prod
            (inst (T := fun Σ => Term Σ _) s ι)
            (fun vl vr => produce (ι ► (xl∷_ ↦ vl) ► (xr∷_ ↦ vr)) rhs)
        | asn_match_tuple s p rhs =>
          demonic_match_tuple p
            (inst (T := fun Σ => Term Σ _) s ι)
            (fun ι' => produce (ι ►► ι') rhs)
        | asn_match_record R s p rhs =>
          demonic_match_record p
            (inst (T := fun Σ => Term Σ _) s ι)
            (fun ι' => produce (ι ►► ι') rhs)
        | asn_match_union U s alt__ctx alt__pat alt__rhs =>
          demonic_match_union
            alt__pat (inst (T := fun Σ => Term Σ _) s ι)
            (fun UK ι' => produce (ι ►► ι') (alt__rhs UK))
        | asn_sep a1 a2   => produce ι a1 *> produce ι a2
        | asn_or a1 a2 =>
          demonic_binary (produce ι a1)
                         (produce ι a2)
        | asn_exist ς τ a =>
          v <- demonic τ ;;
          produce (env.snoc ι (ς∷τ) v) a
        | asn_debug => pure tt
        end.

      Fixpoint consume {Γ Σ} (ι : Valuation Σ) (asn : Assertion Σ) : CMut Γ Γ unit :=
        match asn with
        | asn_formula fml => assert_formula (inst fml ι)
        | asn_chunk c     => consume_chunk (inst c ι)
        | asn_chunk_angelic c     => consume_chunk (inst c ι)
        | asn_if b a1 a2  => angelic_match_bool (inst b ι) (consume ι a1) (consume ι a2)
        | asn_match_enum E k alts =>
          angelic_match_enum
            (inst (T := fun Σ => Term Σ _) k ι)
            (fun K => consume ι (alts K))
        | asn_match_sum σ τ s xl alt_inl xr alt_inr =>
          angelic_match_sum
            (inst (T := fun Σ => Term Σ _) s ι)
            (fun v => consume (env.snoc ι (xl∷σ) v) alt_inl)
            (fun v => consume (env.snoc ι (xr∷τ) v) alt_inr)
        | asn_match_list s alt_nil xh xt alt_cons =>
          angelic_match_list
            (inst (T := fun Σ => Term Σ _) s ι)
            (consume ι alt_nil)
            (fun vh vt => consume (ι ► (xh∷_ ↦ vh) ► (xt∷ty.list _ ↦ vt)) alt_cons)
        | asn_match_prod s xl xr rhs =>
          angelic_match_prod
            (inst (T := fun Σ => Term Σ _) s ι)
            (fun vl vr => consume (ι ► (xl∷_ ↦ vl) ► (xr∷_ ↦ vr)) rhs)
        | asn_match_tuple s p rhs =>
          angelic_match_tuple p
            (inst (T := fun Σ => Term Σ _) s ι)
            (fun ι' => consume (ι ►► ι') rhs)
        | asn_match_record R s p rhs =>
          angelic_match_record p
            (inst (T := fun Σ => Term Σ _) s ι)
            (fun ι' => consume (ι ►► ι') rhs)
        | asn_match_union U s alt__ctx alt__pat alt__rhs =>
          angelic_match_union
            alt__pat (inst (T := fun Σ => Term Σ _) s ι)
            (fun UK ι' => consume (ι ►► ι') (alt__rhs UK))
        | asn_sep a1 a2   => consume ι a1 *> consume ι a2
        | asn_or a1 a2 =>
          angelic_binary (consume ι a1)
                         (consume ι a2)
        | asn_exist ς τ a =>
          v <- angelic τ ;;
          consume (env.snoc ι (ς∷τ) v) a
        | asn_debug => pure tt
        end.

    End ProduceConsume.

    Section Exec.

      Definition call_contract {Γ Δ τ} (contract : SepContract Δ τ) (vs : CStore Δ) : CMut Γ Γ (Val τ) :=
        match contract with
        | MkSepContract _ _ Σe δ req result ens =>
          ι <- angelic_ctx Σe ;;
          assert_formula (inst δ ι = vs) ;;
          consume ι req  ;;
          v <- demonic τ ;;
          produce (env.snoc ι (result∷τ) v) ens ;;
          pure v
        end.

      Definition call_lemma {Γ Δ} (lem : Lemma Δ) (vs : CStore Δ) : CMut Γ Γ unit :=
        match lem with
        | MkLemma _ Σe δ req ens =>
          ι <- angelic_ctx Σe ;;
          assert_formula (inst δ ι = vs) ;;
          consume ι req ;;
          produce ι ens
        end.

      Definition Exec := forall Γ τ (s : Stm Γ τ), CMut Γ Γ (Val τ).

      Section ExecAux.

        Variable rec : Exec.

        Definition exec_aux : Exec :=
          fix exec_aux {Γ τ} (s : Stm Γ τ) : CMut Γ Γ (Val τ) :=
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
              assign x v ;;
              pure v
            | stm_call f es =>
              args <- eval_exps es ;;
              match CEnv f with
              | Some c => call_contract c args
              | None   => fun POST δ => rec (FunDef f) (fun v _ => POST v δ) args
              end
            | stm_foreign f es =>
              eval_exps es >>= call_contract (CEnvEx f)
            | stm_lemmak l es k =>
              eval_exps es >>= call_lemma (LEnv l) ;;
              exec_aux k
            | stm_call_frame δ' s =>
              δ <- get_local ;;
              put_local δ' ;;
              v <- exec_aux s ;;
              put_local δ ;;
              pure v
            | stm_if e s1 s2 =>
              v <- eval_exp e ;;
              demonic_match_bool v (exec_aux s1) (exec_aux s2)
            | stm_seq e k => exec_aux e ;; exec_aux k
            | stm_assertk e1 _ k =>
              v <- eval_exp e1 ;;
              assume_formula (v = true) ;;
              exec_aux k
            | stm_fail _ s =>
              block
            | stm_match_enum E e alts =>
              v <- eval_exp e ;;
              demonic_match_enum
                v
                (fun EK => exec_aux (alts EK))
            | stm_read_register reg =>
              v <- angelic τ ;;
              let c := scchunk_ptsreg reg v in
              consume_chunk c ;;
              produce_chunk c ;;
              pure v
            | stm_write_register reg e =>
              v__old <- angelic τ ;;
              consume_chunk (scchunk_ptsreg reg v__old) ;;
              v__new <- eval_exp e ;;
              produce_chunk (scchunk_ptsreg reg v__new) ;;
              pure v__new
            | @stm_match_list _ _ σ e s1 xh xt s2 =>
              v <- eval_exp e ;;
              demonic_match_list v
                (exec_aux s1)
                (fun h t =>
                   pushspops
                     (env.snoc (env.snoc env.nil (xh∷σ) h) (xt∷ty.list σ) t)
                     (exec_aux s2))
            | stm_match_sum e xinl s1 xinr s2 =>
              v <- eval_exp e ;;
              demonic_match_sum
                v
                (fun v => pushpop v (exec_aux s1))
                (fun v => pushpop v (exec_aux s2))
            | stm_match_prod e xl xr s =>
              v <- eval_exp e ;;
              demonic_match_prod
                v
                (fun vl vr =>
                   pushspops
                     (env.snoc (env.snoc env.nil (xl∷_) vl) (xr∷_) vr)
                     (exec_aux s))
            | stm_match_tuple e p rhs =>
              v <- eval_exp e ;;
              demonic_match_tuple p v
                (fun δΔ => pushspops δΔ (exec_aux rhs))
            | stm_match_union U e alt__pat alt__rhs =>
              v <- eval_exp e ;;
              demonic_match_union alt__pat v (fun UK vs => pushspops vs (exec_aux (alt__rhs UK)))
            | stm_match_record R e p rhs =>
              v <- eval_exp e ;;
              demonic_match_record p v (fun vs => pushspops vs (exec_aux rhs))
            | stm_match_bvec n e rhs =>
              v <- eval_exp e ;;
              demonic_match_bvec
                v
                (fun u => exec_aux (rhs u))
            | stm_bind s k =>
              v <- exec_aux s ;;
              exec_aux (k v)
            | stm_debugk k =>
              exec_aux k
            end.

      End ExecAux.

      Fixpoint exec (inline_fuel : nat) : Exec :=
        match inline_fuel with
        | O   => fun _ _ _ => error "CMut.exec: out of fuel for inlining"
        | S n => @exec_aux (@exec n)
        end.
      Global Arguments exec _ {_ _} s _ _ _.

      (* Definition leakcheck {Γ} : CMut Γ Γ unit := *)
      (*   get_heap >>= fun h => *)
      (*   match h with *)
      (*   | nil => pure tt *)
      (*   | _   => error "Err [cmut_leakcheck]: heap leak" *)
      (*   end. *)

    End Exec.

    Section WithFuel.

      Variable inline_fuel : nat.

      Definition exec_contract {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) :
       Valuation (sep_contract_logic_variables c) -> CMut Δ Δ unit :=
        match c with
        | MkSepContract _ _ _ _ req result ens =>
          fun ι =>
          produce ι req ;;
          exec inline_fuel s >>= fun v =>
          consume (env.snoc ι (result∷τ) v) ens
          (* cmut_block *)
          (* cmut_leakcheck *)
        end%mut.

      Definition ValidContract {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
        ForallNamed (fun ι : Valuation (sep_contract_logic_variables c) =>
          let δΔ : CStore Δ := inst (sep_contract_localstore c) ι in
          exec_contract c body ι (fun _ _ _ => True) δΔ nil).

    End WithFuel.

  End CMut.

End SemiConcrete.
