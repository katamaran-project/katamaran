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
        | Δ ▻ x∷σ => v  <- angelic σ;;
                     vs <- rec Δ;;
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
        | Δ ▻ x∷σ => v  <- demonic σ;;
                     vs <- rec Δ;;
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
    Equations(noeqns) assert_eq_env {Δ : Ctx Ty}
      (δ δ' : Env Val Δ) : CPureSpecM unit :=
      assert_eq_env env.nil          env.nil            := pure tt;
      assert_eq_env (env.snoc δ _ t) (env.snoc δ' _ t') :=
        bind (assert_eq_env δ δ') (fun _ => assert_formula (t = t')).

    Equations(noeqns) assert_eq_nenv {N : Set} {Δ : NCtx N Ty}
      (δ δ' : NamedEnv Val Δ) : CPureSpecM unit :=
      assert_eq_nenv env.nil          env.nil            := pure tt;
      assert_eq_nenv (env.snoc δ _ t) (env.snoc δ' _ t') :=
        bind (assert_eq_nenv δ δ') (fun _ => assert_formula (t = t')).

    Definition angelic_binary {A} :
      CPureSpecM A -> CPureSpecM A -> CPureSpecM A :=
      fun m1 m2 POST =>
        m1 POST \/ m2 POST.
    Definition demonic_binary {A} :
      CPureSpecM A -> CPureSpecM A -> CPureSpecM A :=
      fun m1 m2 POST =>
        m1 POST /\ m2 POST.

    Definition angelic_list {A} :
      list A -> CPureSpecM A :=
      fix rec xs :=
        match xs with
        | nil        => fun POST => False
        | cons x xs  => angelic_binary (pure x) (rec xs)
        end.

    Definition demonic_list {A} :
      list A -> CPureSpecM A :=
      fix rec xs :=
        match xs with
        | nil        => fun POST => True
        | cons x xs  => demonic_binary (pure x) (rec xs)
        end.

    Definition angelic_finite F `{finite.Finite F} :
      CPureSpecM F :=
      angelic_list (finite.enum F).
    #[global] Arguments angelic_finite F {_ _}.

    Definition demonic_finite F `{finite.Finite F} :
      CPureSpecM F :=
      demonic_list (finite.enum F).
    #[global] Arguments demonic_finite F {_ _}.

    Definition angelic_match_bool :
      Val ty.bool -> CPureSpecM bool :=
      fun v =>
        angelic_binary
          (bind
             (assert_formula (v = true))
             (fun _ => pure true))
          (bind
             (assert_formula (v = false))
             (fun _ => pure false)).

    Definition demonic_match_bool :
      Val ty.bool -> CPureSpecM bool :=
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
      - destruct b as [x σ]. cbv [angelic bind pure]. split.
        + intros [v Hwp%IHΔ]. destruct Hwp as [vs HPOST].
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
      - destruct b as [x σ]. cbv [demonic bind pure]. split.
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

    Lemma wp_assert_eq_env {Δ : Ctx Ty} (δ δ' : Env Val Δ) :
      forall POST,
        assert_eq_env δ δ' POST <-> δ = δ' /\ POST tt.
    Proof.
      induction δ; intros POST.
      - destruct (env.nilView δ'). intuition.
      - destruct (env.snocView δ'); cbn.
        unfold bind, assert_formula.
        now rewrite IHδ, env.inversion_eq_snoc.
    Qed.

    Lemma wp_assert_eq_nenv {N} {Δ : NCtx N Ty} (δ δ' : NamedEnv Val Δ) :
      forall POST,
        assert_eq_nenv δ δ' POST <-> δ = δ' /\ POST tt.
    Proof.
      induction δ; intros POST.
      - destruct (env.nilView δ'). intuition.
      - destruct (env.snocView δ') as [δ']; cbn in *.
        unfold bind, assert_formula.
        now rewrite IHδ, (@env.inversion_eq_snoc _ _ _ b δ δ').
    Qed.

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
      - unfold bind. rewrite IHc1, IHc2. intuition.
      - unfold bind. rewrite IHc1, IHc2. intuition.
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
        fun POST δ h => forall v : Val σ, POST v δ h.
      Definition angelic {Γ} (σ : Ty) : CHeapSpecM Γ Γ (Val σ) :=
        fun POST δ h => exists v : Val σ, POST v δ h.

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

      Definition angelic_match_bool {A Γ1 Γ2} (v : Val ty.bool) (kt kf : CHeapSpecM Γ1 Γ2 A) : CHeapSpecM Γ1 Γ2 A :=
        (assert_formula (v = true);; kt) ⊕ (assert_formula (v = false);; kf).

      Lemma wp_angelic_match_bool {A Γ1 Γ2} (v : Val ty.bool) (kt kf : CHeapSpecM Γ1 Γ2 A) :
        forall POST δ h,
          angelic_match_bool v kt kf POST δ h <->
          if v then kt POST δ h else kf POST δ h.
      Proof.
        cbv [angelic_match_bool angelic_binary bind_right bind assert_formula
             lift_purem CPureSpecM.assert_formula is_true negb].
        destruct v; intuition; discriminate.
      Qed.

      Definition demonic_match_bool {A Γ1 Γ2} (v : Val ty.bool) (kt kf : CHeapSpecM Γ1 Γ2 A) : CHeapSpecM Γ1 Γ2 A :=
        (assume_formula (v = true);; kt) ⊗ (assume_formula (v = false);; kf).

      Lemma wp_demonic_match_bool {A Γ1 Γ2} (v : Val ty.bool) (kt kf : CHeapSpecM Γ1 Γ2 A) :
        forall POST δ h,
          demonic_match_bool v kt kf POST δ h <->
          if v then kt POST δ h else kf POST δ h.
      Proof.
        cbv [demonic_match_bool demonic_binary bind_right bind assume_formula
             lift_purem CPureSpecM.assume_formula is_true negb].
        destruct v; intuition; discriminate.
      Qed.

      Definition angelic_match_enum {A E} {Γ1 Γ2} (v : Val (ty.enum E))
        (cont : enumt E -> CHeapSpecM Γ1 Γ2 A) : CHeapSpecM Γ1 Γ2 A :=
        EK <- angelic_finite (enumt E);;
        assert_formula (v = EK);;
        cont EK.

      Definition demonic_match_enum {A E} {Γ1 Γ2} (v : Val (ty.enum E))
        (cont : enumt E -> CHeapSpecM Γ1 Γ2 A) : CHeapSpecM Γ1 Γ2 A :=
        EK <- demonic_finite (enumt E);;
        assume_formula (v = EK);;
        cont EK.

      Lemma wp_angelic_match_enum {A E Γ1 Γ2} (v : Val (ty.enum E)) (k : enumt E -> CHeapSpecM Γ1 Γ2 A) :
        forall POST δ h,
          angelic_match_enum v k POST δ h <-> k v POST δ h.
      Proof.
        cbv [assert_formula bind bind_right angelic_match_enum angelic_finite
             lift_purem CPureSpecM.angelic_finite CPureSpecM.assert_formula].
        intros. rewrite CPureSpecM.wp_angelic_list.
        split; intros; destruct_conjs; subst; auto.
        exists v. split; auto.
        rewrite <- base.elem_of_list_In.
        apply finite.elem_of_enum.
      Qed.

      Lemma wp_demonic_match_enum {A E Γ1 Γ2} (v : Val (ty.enum E)) (k : enumt E -> CHeapSpecM Γ1 Γ2 A) :
        forall POST δ h,
          demonic_match_enum v k POST δ h <-> k v POST δ h.
      Proof.
        cbv [assume_formula bind bind_right demonic_match_enum demonic_finite
             lift_purem CPureSpecM.demonic_finite CPureSpecM.assume_formula].
        intros. rewrite CPureSpecM.wp_demonic_list.
        split; intros; subst; auto.
        apply H; auto.
        rewrite <- base.elem_of_list_In.
        apply finite.elem_of_enum.
      Qed.

      Definition angelic_match_sum {A Γ1 Γ2} {σ τ} (v : Val (ty.sum σ τ))
        (kinl : Val σ -> CHeapSpecM Γ1 Γ2 A) (kinr : Val τ -> CHeapSpecM Γ1 Γ2 A) :
        CHeapSpecM Γ1 Γ2 A :=
        (v1 <- angelic σ;; assert_formula (inl v1 = v);; kinl v1) ⊕
        (v1 <- angelic τ;; assert_formula (inr v1 = v);; kinr v1).

      Definition demonic_match_sum {A Γ1 Γ2} {σ τ} (v : Val (ty.sum σ τ))
        (kinl : Val σ -> CHeapSpecM Γ1 Γ2 A) (kinr : Val τ -> CHeapSpecM Γ1 Γ2 A) :
        CHeapSpecM Γ1 Γ2 A :=
        (v1 <- demonic σ;; assume_formula (inl v1 = v);; kinl v1) ⊗
        (v1 <- demonic τ;; assume_formula (inr v1 = v);; kinr v1).

      Lemma wp_angelic_match_sum {A Γ1 Γ2} {σ τ}
        (v : Val (ty.sum σ τ)) (kinl : Val σ -> CHeapSpecM Γ1 Γ2 A) (kinr : Val τ -> CHeapSpecM Γ1 Γ2 A) POST δ h :
        angelic_match_sum v kinl kinr POST δ h <->
        match v with
        | inl v => kinl v POST δ h
        | inr v => kinr v POST δ h
        end.
      Proof.
        cbv [angelic_match_sum bind_right bind angelic angelic_binary
             assert_formula lift_purem CPureSpecM.assert_formula].
        split.
        - intros []; destruct_conjs; subst; auto.
        - destruct v as [v|v]; [left|right]; exists v; intuition.
      Qed.

      Lemma wp_demonic_match_sum {A Γ1 Γ2} {σ τ}
        (v : Val (ty.sum σ τ)) (kinl : Val σ -> CHeapSpecM Γ1 Γ2 A) (kinr : Val τ -> CHeapSpecM Γ1 Γ2 A) POST δ h :
        demonic_match_sum v kinl kinr POST δ h <->
        match v with
        | inl v => kinl v POST δ h
        | inr v => kinr v POST δ h
        end.
      Proof.
        cbv [demonic_match_sum bind_right bind demonic demonic_binary
             assume_formula lift_purem CPureSpecM.assume_formula].
        split.
        - destruct v; intuition.
        - destruct v; intuition; try discriminate;
            match goal with
            | H: inl _ = inl _ |- _ => apply noConfusion_inv in H; cbn in H; subst
            | H: inr _ = inr _ |- _ => apply noConfusion_inv in H; cbn in H; subst
            end; auto.
      Qed.

      Definition angelic_match_prod {A Γ1 Γ2} {σ τ} :
        Val (ty.prod σ τ) -> (Val σ -> Val τ -> CHeapSpecM Γ1 Γ2 A) -> CHeapSpecM Γ1 Γ2 A :=
        fun v k =>
          v1 <- angelic σ ;;
          v2 <- angelic τ ;;
          assert_formula ((v1,v2) = v) ;;
          k v1 v2.

      Lemma wp_angelic_match_prod {A Γ1 Γ2} {σ τ}
        (v : Val (ty.prod σ τ)) (k : Val σ -> Val τ -> CHeapSpecM Γ1 Γ2 A) POST δ h :
        angelic_match_prod v k POST δ h <->
        match v with
        | pair v1 v2 => k v1 v2 POST δ h
        end.
      Proof.
        cbv [angelic_match_prod bind_right bind angelic angelic_binary
             assert_formula lift_purem CPureSpecM.assert_formula].
        destruct v; intuition.
        - destruct H as (v1 & v2 & eq & H).
          inversion eq; now subst.
        - now exists v, v0.
      Qed.

      Definition demonic_match_prod {A Γ1 Γ2} {σ τ} :
        Val (ty.prod σ τ) -> (Val σ -> Val τ -> CHeapSpecM Γ1 Γ2 A) -> CHeapSpecM Γ1 Γ2 A :=
        fun v k =>
          v1 <- demonic σ ;;
          v2 <- demonic τ ;;
          assume_formula ((v1,v2) = v) ;;
          k v1 v2.

      Lemma wp_demonic_match_prod {A Γ1 Γ2} {σ τ}
        (v : Val (ty.prod σ τ)) (k : Val σ -> Val τ -> CHeapSpecM Γ1 Γ2 A) POST δ h :
        demonic_match_prod v k POST δ h <->
        match v with
        | pair v1 v2 => k v1 v2 POST δ h
        end.
      Proof.
        cbv [demonic_match_prod bind_right bind demonic demonic_binary
             assume_formula lift_purem CPureSpecM.assume_formula].
        destruct v; intuition.
      Qed.

      Definition angelic_match_list {A Γ1 Γ2} {σ} (v : Val (ty.list σ))
        (knil : CHeapSpecM Γ1 Γ2 A)
        (kcons : Val σ -> Val (ty.list σ) -> CHeapSpecM Γ1 Γ2 A) :
        CHeapSpecM Γ1 Γ2 A :=
        (assert_formula (nil = v);; knil) ⊕
        (vhead <- angelic σ;;
         vtail <- angelic (ty.list σ);;
         assert_formula (cons vhead vtail = v);;
         kcons vhead vtail).

      Lemma wp_angelic_match_list {A Γ1 Γ2} {σ}
        (v : Val (ty.list σ)) (knil : CHeapSpecM Γ1 Γ2 A) (kcons : Val σ -> Val (ty.list σ) -> CHeapSpecM Γ1 Γ2 A) POST δ h :
        angelic_match_list v knil kcons POST δ h <->
        match v with
        | nil => knil POST δ h
        | cons vh vt => kcons vh vt POST δ h
        end.
      Proof.
        cbv [angelic_match_list bind_right bind angelic angelic_binary
             assert_formula lift_purem CPureSpecM.assert_formula].
        split.
        - intros []; destruct_conjs; subst; auto.
        - destruct v as [|vh vt]; [left;auto|right].
          exists vh, vt. auto.
      Qed.

      Definition demonic_match_list {A Γ1 Γ2} {σ} (v : Val (ty.list σ))
        (knil : CHeapSpecM Γ1 Γ2 A)
        (kcons : Val σ -> Val (ty.list σ) -> CHeapSpecM Γ1 Γ2 A) :
        CHeapSpecM Γ1 Γ2 A :=
        (assume_formula (nil = v);; knil) ⊗
        (vhead <- demonic σ;;
         vtail <- demonic (ty.list σ);;
         assume_formula (cons vhead vtail = v);;
         kcons vhead vtail).

      Lemma wp_demonic_match_list {A Γ1 Γ2} {σ}
        (v : Val (ty.list σ)) (knil : CHeapSpecM Γ1 Γ2 A) (kcons : Val σ -> Val (ty.list σ) -> CHeapSpecM Γ1 Γ2 A) POST δ h :
        demonic_match_list v knil kcons POST δ h <->
        match v with
        | nil => knil POST δ h
        | cons vh vt => kcons vh vt POST δ h
        end.
      Proof.
        cbv [demonic_match_list bind_right bind demonic demonic_binary
             assume_formula lift_purem CPureSpecM.assume_formula].
        split.
        - destruct v; intuition.
        - destruct v; intuition; try discriminate.
      Qed.

      Definition angelic_match_record {N : Set} {A R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (recordf_ty R) Δ) :
        (Val (ty.record R)) ->
        (NamedEnv Val Δ -> CHeapSpecM Γ1 Γ2 A) ->
        CHeapSpecM Γ1 Γ2 A :=
        fun v k =>
          args <- angelic_ctx Δ ;;
          assert_formula (recordv_fold R (record_pattern_match_env_reverse p args) = v) ;;
          k args.

      Lemma wp_angelic_match_record {N : Set} {A R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (recordf_ty R) Δ)
        (v : Val (ty.record R))
        (k : NamedEnv Val Δ -> CHeapSpecM Γ1 Γ2 A)
        POST δ h :
        angelic_match_record p v k POST δ h <->
        k (record_pattern_match_val p v) POST δ h.
      Proof.
        cbv [angelic_match_record bind_right bind angelic_ctx lift_purem assert_formula CPureSpecM.assert_formula].
        rewrite CPureSpecM.wp_angelic_ctx; intuition.
        - destruct H as (vs & <- & H).
          unfold record_pattern_match_val.
          now rewrite recordv_unfold_fold, record_pattern_match_env_inverse_right.
        - exists (record_pattern_match_val p v).
          unfold record_pattern_match_val.
          now rewrite record_pattern_match_env_inverse_left, recordv_fold_unfold.
      Qed.

      Definition demonic_match_record {N : Set} {A R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (recordf_ty R) Δ) :
        (Val (ty.record R)) ->
        (NamedEnv Val Δ -> CHeapSpecM Γ1 Γ2 A) ->
        CHeapSpecM Γ1 Γ2 A :=
        fun v k =>
          args <- demonic_ctx Δ ;;
          assume_formula (recordv_fold R (record_pattern_match_env_reverse p args) = v) ;;
          k args.

      Lemma wp_demonic_match_record {N : Set} {A R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (recordf_ty R) Δ)
        (v : Val (ty.record R))
        (k : NamedEnv Val Δ -> CHeapSpecM Γ1 Γ2 A)
        POST δ h :
        demonic_match_record p v k POST δ h <->
        k (record_pattern_match_val p v) POST δ h.
      Proof.
        cbv [demonic_match_record bind_right bind demonic_ctx lift_purem assume_formula CPureSpecM.assume_formula].
        rewrite CPureSpecM.wp_demonic_ctx; intuition; eauto.
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
        (NamedEnv Val Δ -> CHeapSpecM Γ1 Γ2 A) ->
        CHeapSpecM Γ1 Γ2 A :=
        fun v k =>
          args <- angelic_ctx Δ ;;
          assert_formula (tuple_pattern_match_val p v = args) ;;
          k args.

      Lemma wp_angelic_match_tuple {N : Set} {A σs Γ1 Γ2} {Δ : NCtx N Ty} (p : TuplePat σs Δ)
        (v : Val (ty.tuple σs))
        (k : NamedEnv Val Δ -> CHeapSpecM Γ1 Γ2 A)
        POST δ h :
        angelic_match_tuple p v k POST δ h <->
        k (tuple_pattern_match_val p v) POST δ h.
      Proof.
        cbv [angelic_match_tuple bind_right bind angelic_ctx lift_purem assert_formula CPureSpecM.assert_formula].
        rewrite CPureSpecM.wp_angelic_ctx; intuition.
        - now destruct H as (vs & <- & H).
        - exists (tuple_pattern_match_val p v).
          split; auto.
      Qed.

      Definition demonic_match_tuple {N : Set} {A σs Γ1 Γ2} {Δ : NCtx N Ty} (p : TuplePat σs Δ) :
        (Val (ty.tuple σs)) ->
        (NamedEnv Val Δ -> CHeapSpecM Γ1 Γ2 A) ->
        CHeapSpecM Γ1 Γ2 A :=
        fun v k =>
          args <- demonic_ctx Δ ;;
          assume_formula (tuple_pattern_match_val p v = args) ;;
          k args.

      Lemma wp_demonic_match_tuple {N : Set} {A σs Γ1 Γ2} {Δ : NCtx N Ty} (p : TuplePat σs Δ)
        (v : Val (ty.tuple σs))
        (k : NamedEnv Val Δ -> CHeapSpecM Γ1 Γ2 A)
        POST δ h :
        demonic_match_tuple p v k POST δ h <->
        k (tuple_pattern_match_val p v) POST δ h.
      Proof.
        cbv [demonic_match_tuple bind_right bind demonic_ctx lift_purem assume_formula CPureSpecM.assume_formula].
        rewrite CPureSpecM.wp_demonic_ctx; intuition; subst; auto.
      Qed.

      Definition angelic_match_pattern {N : Set} {σ} {Δ : NCtx N Ty}
        (p : Pattern Δ σ) {Γ} (v : Val σ) : CHeapSpecM Γ Γ (NamedEnv Val Δ) :=
        vs <- angelic_ctx Δ ;;
        assert_formula (pattern_match_val p v = vs) ;;
        pure vs.

      Lemma wp_angelic_match_pattern {N : Set} {σ Γ} {Δ : NCtx N Ty} (p : Pattern Δ σ)
        (v : Val σ)
        POST δ h :
        angelic_match_pattern (Γ := Γ) p v POST δ h <->
        POST (pattern_match_val p v) δ h.
      Proof.
        cbv [angelic_match_pattern bind pure angelic_ctx assert_formula
             lift_purem CPureSpecM.assert_formula].
        rewrite CPureSpecM.wp_angelic_ctx.
        split.
        - now intros (vs & <- & H).
        - intros ?. exists (pattern_match_val p v).
          split; auto.
      Qed.

      Definition demonic_match_pattern {N : Set} {σ} {Δ : NCtx N Ty}
        (p : Pattern Δ σ) {Γ} (v : Val σ) : CHeapSpecM Γ Γ (NamedEnv Val Δ) :=
        vs <- demonic_ctx Δ ;;
        assume_formula (pattern_match_val p v = vs) ;;
        pure vs.

      Lemma wp_demonic_match_pattern {N : Set} {σ Γ} {Δ : NCtx N Ty} (p : Pattern Δ σ)
        (v : Val σ)
        POST δ h :
        demonic_match_pattern (Γ := Γ) p v POST δ h <->
        POST (pattern_match_val p v) δ h.
      Proof.
        cbv [demonic_match_pattern bind pure demonic_ctx bind_right assume_formula
             lift_purem CPureSpecM.assume_formula].
        rewrite CPureSpecM.wp_demonic_ctx.
        intuition; subst; auto.
      Qed.

      Definition angelic_match_union {N : Set} {A Γ1 Γ2 U}
        {Δ : unionk U -> NCtx N Ty} (p : forall K : unionk U, Pattern (Δ K) (unionk_ty U K)) :
        Val (ty.union U) -> (forall K, NamedEnv Val (Δ K) -> CHeapSpecM Γ1 Γ2 A) -> CHeapSpecM Γ1 Γ2 A :=
        fun v POST =>
          UK     <- angelic_finite (unionk U);;
          v__field <- angelic (unionk_ty U UK);;
          assert_formula (unionv_fold U (existT UK v__field) = v);;
          x      <- angelic_match_pattern (p UK) v__field;;
          POST UK x.

      Lemma wp_angelic_match_union {N : Set} {A Γ1 Γ2 U}
        {Δ : unionk U -> NCtx N Ty} (p : forall K : unionk U, Pattern (Δ K) (unionk_ty U K))
        (v : Val (ty.union U)) (k : forall K, NamedEnv Val (Δ K) -> CHeapSpecM Γ1 Γ2 A)
        POST δ h :
        angelic_match_union p v k POST δ h <->
        let (UK , vf) := unionv_unfold U v in
        k UK (pattern_match_val (p UK) vf) POST δ h.
      Proof.
        cbv [angelic_match_union bind bind_right angelic_finite assert_formula angelic
             lift_purem CPureSpecM.angelic_finite CPureSpecM.assert_formula].
        rewrite CPureSpecM.wp_angelic_list.
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
        Val (ty.union U) -> (forall K, NamedEnv Val (Δ K) -> CHeapSpecM Γ1 Γ2 A) -> CHeapSpecM Γ1 Γ2 A :=
        fun v POST =>
          UK     <- demonic_finite (unionk U);;
          v__field <- demonic (unionk_ty U UK);;
          assume_formula (unionv_fold U (existT UK v__field) = v);;
          x      <- demonic_match_pattern (p UK) v__field;;
          POST UK x.

      Lemma wp_demonic_match_union {N : Set} {A Γ1 Γ2 U}
        {Δ : unionk U -> NCtx N Ty} (p : forall K : unionk U, Pattern (Δ K) (unionk_ty U K))
        (v : Val (ty.union U)) (k : forall K, NamedEnv Val (Δ K) -> CHeapSpecM Γ1 Γ2 A)
        POST δ h :
        demonic_match_union p v k POST δ h <->
        let (UK , vf) := unionv_unfold U v in
        k UK (pattern_match_val (p UK) vf) POST δ h.
      Proof.
        cbv [demonic_match_union bind bind_right demonic_finite assume_formula demonic
             lift_purem CPureSpecM.demonic_finite CPureSpecM.assume_formula].
        rewrite CPureSpecM.wp_demonic_list.
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
        Val (ty.bvec n) -> (bv n -> CHeapSpecM Γ1 Γ2 A) -> CHeapSpecM Γ1 Γ2 A :=
        fun v k =>
          u <- demonic_finite (bv n);;
          assume_formula (v = u);;
          k u.
      #[global] Arguments demonic_match_bvec : simpl never.

      Lemma wp_demonic_match_bvec {A n Γ1 Γ2} (v : Val (ty.bvec n)) (k : bv n -> CHeapSpecM Γ1 Γ2 A) :
        forall POST δ h,
          demonic_match_bvec v k POST δ h <-> k v POST δ h.
      Proof.
        cbv [assume_formula bind bind_right demonic_match_bvec demonic_finite
             lift_purem CPureSpecM.demonic_finite CPureSpecM.assume_formula].
        intros. rewrite CPureSpecM.wp_demonic_list.
        split; intros; subst; auto.
        apply H; auto.
        rewrite <- base.elem_of_list_In.
        apply finite.elem_of_enum.
      Qed.

      Definition demonic_match_bvec_split {A m n} {Γ1 Γ2} :
        Val (ty.bvec (m + n)) ->
        (bv m -> bv n -> CHeapSpecM Γ1 Γ2 A) -> CHeapSpecM Γ1 Γ2 A :=
        fun v k =>
          v1 <- demonic (ty.bvec m) ;;
          v2 <- demonic (ty.bvec n) ;;
          assume_formula (bv.app v1 v2 = v) ;;
          k v1 v2.
      #[global] Arguments demonic_match_bvec_split : simpl never.

      Lemma wp_demonic_match_bvec_split {A m n Γ1 Γ2}
        (v : Val (ty.bvec (m + n))) (k : bv m -> bv n -> CHeapSpecM Γ1 Γ2 A) :
        forall POST δ h,
          demonic_match_bvec_split v k POST δ h <->
          match bv.appView m n v with
          | bv.isapp xs ys => k xs ys POST δ h
          end.
      Proof.
        intros POST δ h.
        cbv [demonic_match_bvec_split bind demonic bind_right
           assume_formula lift_purem CPureSpecM.assume_formula].
        destruct (bv.appView m n v) as [v1 v2].
        split; [auto|]. now intros ? * [-> ->]%bv.app_inj.
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
        | asn.formula fml => assume_formula (inst fml ι)
        | asn.chunk c     => produce_chunk (inst c ι)
        | asn.chunk_angelic c => produce_chunk (inst c ι)
        | asn.match_bool b a1 a2  => demonic_match_bool (inst b ι) (produce ι a1) (produce ι a2)
        | asn.match_enum E k alts =>
          demonic_match_enum
            (inst (T := fun Σ => Term Σ _) k ι)
            (fun K => produce ι (alts K))
        | asn.match_sum σ τ s xl alt_inl xr alt_inr =>
          demonic_match_sum
            (inst (T := fun Σ => Term Σ _) s ι)
            (fun v => produce (env.snoc ι (xl∷σ) v) alt_inl)
            (fun v => produce (env.snoc ι (xr∷τ) v) alt_inr)
        | asn.match_list s alt_nil xh xt alt_cons =>
          demonic_match_list
            (inst (T := fun Σ => Term Σ _) s ι)
            (produce ι alt_nil)
            (fun vh vt => produce (ι ► (xh∷_ ↦ vh) ► (xt∷ty.list _ ↦ vt)) alt_cons)
        | asn.match_prod s xl xr rhs =>
          demonic_match_prod
            (inst (T := fun Σ => Term Σ _) s ι)
            (fun vl vr => produce (ι ► (xl∷_ ↦ vl) ► (xr∷_ ↦ vr)) rhs)
        | asn.match_tuple s p rhs =>
          demonic_match_tuple p
            (inst (T := fun Σ => Term Σ _) s ι)
            (fun ι' => produce (ι ►► ι') rhs)
        | asn.match_record R s p rhs =>
          demonic_match_record p
            (inst (T := fun Σ => Term Σ _) s ι)
            (fun ι' => produce (ι ►► ι') rhs)
        | asn.match_union U s alt__ctx alt__pat alt__rhs =>
          demonic_match_union
            alt__pat (inst (T := fun Σ => Term Σ _) s ι)
            (fun UK ι' => produce (ι ►► ι') (alt__rhs UK))
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
        | asn.formula fml => assert_formula (inst fml ι)
        | asn.chunk c     => consume_chunk (inst c ι)
        | asn.chunk_angelic c     => consume_chunk (inst c ι)
        | asn.match_bool b a1 a2  => angelic_match_bool (inst b ι) (consume ι a1) (consume ι a2)
        | asn.match_enum E k alts =>
          angelic_match_enum
            (inst (T := fun Σ => Term Σ _) k ι)
            (fun K => consume ι (alts K))
        | asn.match_sum σ τ s xl alt_inl xr alt_inr =>
          angelic_match_sum
            (inst (T := fun Σ => Term Σ _) s ι)
            (fun v => consume (env.snoc ι (xl∷σ) v) alt_inl)
            (fun v => consume (env.snoc ι (xr∷τ) v) alt_inr)
        | asn.match_list s alt_nil xh xt alt_cons =>
          angelic_match_list
            (inst (T := fun Σ => Term Σ _) s ι)
            (consume ι alt_nil)
            (fun vh vt => consume (ι ► (xh∷_ ↦ vh) ► (xt∷ty.list _ ↦ vt)) alt_cons)
        | asn.match_prod s xl xr rhs =>
          angelic_match_prod
            (inst (T := fun Σ => Term Σ _) s ι)
            (fun vl vr => consume (ι ► (xl∷_ ↦ vl) ► (xr∷_ ↦ vr)) rhs)
        | asn.match_tuple s p rhs =>
          angelic_match_tuple p
            (inst (T := fun Σ => Term Σ _) s ι)
            (fun ι' => consume (ι ►► ι') rhs)
        | asn.match_record R s p rhs =>
          angelic_match_record p
            (inst (T := fun Σ => Term Σ _) s ι)
            (fun ι' => consume (ι ►► ι') rhs)
        | asn.match_union U s alt__ctx alt__pat alt__rhs =>
          angelic_match_union
            alt__pat (inst (T := fun Σ => Term Σ _) s ι)
            (fun UK ι' => consume (ι ►► ι') (alt__rhs UK))
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
            | stm_if e s1 s2 =>
              v <- eval_exp e ;;
              demonic_match_bool v (exec_aux s1) (exec_aux s2)
            | stm_seq e k => _ <- exec_aux e ;; exec_aux k
            | stm_assertk e1 _ k =>
              v <- eval_exp e1 ;;
              _ <- assume_formula (v = true) ;;
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
              _ <- consume_chunk c ;;
              _ <- produce_chunk c ;;
              pure v
            | stm_write_register reg e =>
              v__old <- angelic τ ;;
              _    <- consume_chunk (scchunk_ptsreg reg v__old) ;;
              v__new <- eval_exp e ;;
              _    <- produce_chunk (scchunk_ptsreg reg v__new) ;;
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
            | stm_match_bvec_split m n e xl xr rhs =>
              v <- eval_exp e ;;
              demonic_match_bvec_split
                v
                (fun vl vr =>
                   pushspops
                     [kv (xl∷ty.bvec m; vl); (xr∷ty.bvec n; vr)]
                     (exec_aux rhs))
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

  Module Shallow.

    Definition ValidContract {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      (* Use inline_fuel = 1 by default. *)
      CHeapSpecM.vcgen 1 c body.

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
