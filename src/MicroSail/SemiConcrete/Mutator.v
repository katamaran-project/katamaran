(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel                                          *)
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
     Logic.EqdepFacts
     Program.Equality
     Program.Tactics
     Strings.String
     Arith.PeanoNat
     ZArith.ZArith.

From Equations Require Import Equations.

From MicroSail Require Import
     Sep.Spec
     SemiConcrete.Outcome
     Syntax.

From stdpp Require Import base list option.

Import CtxNotations.
Import EnvNotations.
Import ListNotations.
Import OutcomeNotations.

Set Implicit Arguments.

Delimit Scope mutator_scope with mut.
Delimit Scope dmut_scope with dmut.

Module SemiConcrete
       (termkit : TermKit)
       (progkit : ProgramKit termkit)
       (assertkit : AssertionKit termkit progkit)
       (symcontractkit : SymbolicContractKit termkit progkit assertkit).

  Export symcontractkit.

  Section ChunkExtraction.

    Equations(noeqns) match_scchunk_eqb (ce : SCChunk) (cr : SCChunk) : bool :=
      match_scchunk_eqb (scchunk_user p1 vs1) (scchunk_user p2 vs2)
      with eq_dec p1 p2 => {
        match_scchunk_eqb (scchunk_user p1 vs1) (scchunk_user p2 vs2) (left eq_refl) := env_eqb_hom Lit_eqb vs1 vs2;
        match_scchunk_eqb (scchunk_user p1 vs1) (scchunk_user p2 vs2) (right _) := false
      };
      match_scchunk_eqb (scchunk_ptsreg r1 t1) (scchunk_ptsreg r2 t2)
      with eq_dec_het r1 r2 => {
        match_scchunk_eqb (scchunk_ptsreg r1 v1) (scchunk_ptsreg r2 v2) (left eq_refl) := Lit_eqb _ v1 v2;
        match_scchunk_eqb (scchunk_ptsreg r1 v1) (scchunk_ptsreg r2 v2) (right _)      := false
      };
      match_scchunk_eqb _ _  := false.

    Local Set Equations With UIP.
    Lemma match_scchunk_eqb_spec (c1 c2 : SCChunk) :
      reflect (c1 = c2) (match_scchunk_eqb c1 c2).
    Proof.
      destruct c1 as [p1 vs1|r1], c2 as [p2 vs2|r2]; cbn.
      - destruct (eq_dec p1 p2); cbn.
        + dependent elimination e; cbn.
          destruct (env_eqb_hom_spec _ Lit_eqb_spec vs1 vs2); constructor.
          * congruence.
          * intros e. now dependent elimination e.
        + constructor; intro e.
          now dependent elimination e.
      - constructor. discriminate.
      - constructor. discriminate.
      - destruct (eq_dec_het r r0); cbn.
        + dependent elimination e; cbn.
          apply (ssrbool.iffP (Lit_eqb_spec _ _ _));
            intro e; now dependent elimination e.
        + constructor.
          intro e; now dependent elimination e.
    Qed.

    Definition extract_scchunk_eqb (ce : SCChunk) (h : SCHeap) : list SCHeap :=
      List.map snd (List.filter (fun '(cr,_) => match_scchunk_eqb ce cr) (heap_extractions h)).

  End ChunkExtraction.

  Section SemiConcreteMutatorResult.

    (* Local Set Primitive Projections. *)
    Local Set Maximal Implicit Insertion.

    Record CMutResult (Γ : PCtx) (A : Type) : Type :=
      MkCMutResult {
          scmutres_value : A;
          scmutres_store : LocalStore Γ;
          scmutres_heap  : SCHeap;
        }.

  End SemiConcreteMutatorResult.

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

    Definition angelic σ : CDijkstra (Lit σ) :=
      fun POST => exists v : Lit σ, POST v.

    Definition angelic_ctx {N : Set} :
      ∀ Δ : NCtx N Ty, CDijkstra (NamedEnv Lit Δ) :=
      fix rec Δ {struct Δ} :=
        match Δ with
        | ctx_nil             => fun k => k env_nil
        | ctx_snoc Δ (x :: σ) =>
          fun k =>
            angelic σ (fun v =>
              rec Δ (fun EΔ =>
                k (EΔ ► (x :: σ ↦ v))))
        end.
    Arguments angelic_ctx {N} Δ.

    Definition demonic σ : CDijkstra (Lit σ) :=
      fun POST => forall v : Lit σ, POST v.

    Definition assume_formula (fml : Prop) : CDijkstra unit :=
      fun POST => fml -> POST tt.

    Definition assert_formula (fml : Prop) : CDijkstra unit :=
      fun POST => fml /\ POST tt.

    Definition assume_formulas {Σ} (ι : SymInstance Σ) : List Formula Σ -> CDijkstra unit.
      refine (
        fix assumes fmls0 :=
        match fmls0 with
        | nil           => pure tt
        | cons fml fmls1 => _
          (* fun w1 ω01 => *)
            (* assume_formulak *)
            (*   (subst fml ω01) *)
            (*   (four (assumes fmls k) ω01) *)
        end).
      eapply bind.
      apply (assumes fmls1).
      intros _.
      apply assume_formula.
      apply (inst fml ι).
    Defined.

    Definition angelic_list {A} :
      list A -> CDijkstra A :=
      fix rec xs POST :=
        match xs with
        | nil        => False
        | cons x nil => POST x
        | cons x xs  => POST x \/ rec xs POST
        end.

    Definition demonic_list {A} :
      list A -> CDijkstra A :=
      fix rec xs POST :=
        match xs with
        | nil        => True
        | cons x nil => POST x
        | cons x xs  => POST x /\ rec xs POST
        end.

    Definition angelic_finite F `{finite.Finite F} :
      CDijkstra F :=
      angelic_list (finite.enum F).

    Definition demonic_finite F `{finite.Finite F} :
      CDijkstra F :=
      demonic_list (finite.enum F).

    Lemma wp_angelic_ctx {N : Set} {Δ : NCtx N Ty} (POST : NamedEnv Lit Δ -> Prop) :
      angelic_ctx Δ POST <-> exists vs : NamedEnv Lit Δ, POST vs.
    Proof.
      induction Δ; cbn.
      - split.
        + now exists env_nil.
        + intros [vs ?]. now destruct (nilView vs).
      - destruct b as [x σ].
        unfold angelic. split.
        + intros [v Hwp]. apply IHΔ in Hwp.
          destruct Hwp as [vs HPOST].
          now exists (env_snoc vs (x :: σ) v).
        + intros [vs Hwp]. destruct (snocView vs) as [vs v].
          exists v. apply IHΔ. now exists vs.
    Qed.

    Lemma wp_angelic_list {A} (xs : list A) (POST : A -> Prop) :
      angelic_list xs POST <->
      exists x : A, List.In x xs /\ POST x.
    Proof.
      induction xs; cbn.
      - firstorder.
      - destruct xs; cbn in *.
        + firstorder. now subst.
        + rewrite IHxs. clear IHxs.
          firstorder. left. now subst.
    Qed.

  End CDijk.

  Definition CMut (Γ1 Γ2 : PCtx) (A : Type) : Type :=
    (A -> LocalStore Γ2 -> SCHeap -> Prop) -> LocalStore Γ1 -> SCHeap -> Prop.
  Bind Scope mutator_scope with CMut.

  Local Opaque instantiate_env.
  Local Opaque instantiate_term.
  Local Open Scope mutator_scope.

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
        fun POST δ h => Outcome.Error msg.
      Definition block {Γ1 Γ2 A} : CMut Γ1 Γ2 A :=
        fun POST δ h => True.

      Definition demonic_binary {Γ1 Γ2 A} (m1 m2 : CMut Γ1 Γ2 A) : CMut Γ1 Γ2 A :=
        fun POST δ h => m1 POST δ h /\ m2 POST δ h.
      Definition angelic_binary {Γ1 Γ2 A} (m1 m2 : CMut Γ1 Γ2 A) : CMut Γ1 Γ2 A :=
        fun POST δ h => m1 POST δ h \/ m2 POST δ h.

      (* Definition demonic {Γ1 Γ2 I A} (ms : I -> CMut Γ1 Γ2 A) : CMut Γ1 Γ2 A := *)
      (*   fun POST δ h => forall i : I, ms i POST δ h. *)
      Definition demonic {Γ} (σ : Ty) : CMut Γ Γ (Lit σ) :=
        fun POST δ h => forall v : Lit σ, POST v δ h.
      Definition angelic {Γ} (σ : Ty) : CMut Γ Γ (Lit σ) :=
        fun POST δ h => exists v : Lit σ, POST v δ h.
      (* Definition angelic {Γ1 Γ2 I A} (ms : I -> CMut Γ1 Γ2 A) : CMut Γ1 Γ2 A := *)
      (*   fun POST δ h => exists i : I, ms i POST δ h. *)

      Definition angelic_ctx {N : Set} {Γ} :
        ∀ Δ : NCtx N Ty, CMut Γ Γ (NamedEnv Lit Δ).
      Proof.
        intros Δ. apply dijkstra.
        apply (CDijk.angelic_ctx Δ).
      Defined.
      Global Arguments angelic_ctx {N Γ} Δ.

    End Basic.

    Module CMutNotations.

      (* Notation "'⨂' x .. y => F" := *)
      (*   (cmut_demonic (fun x => .. (cmut_demonic (fun y => F)) .. )) : mutator_scope. *)

      (* Notation "'⨁' x .. y => F" := *)
      (*   (cmut_angelic (fun x => .. (cmut_angelic (fun y => F)) .. )) : mutator_scope. *)

      Infix "⊗" := demonic_binary (at level 40, left associativity) : mutator_scope.
      Infix "⊕" := angelic_binary (at level 50, left associativity) : mutator_scope.

      Notation "x <- ma ;; mb" :=
        (bind ma (fun x => mb))
          (at level 80, ma at level 90, mb at level 200, right associativity) : mutator_scope.
      Notation "ma >>= f" := (bind ma f) (at level 50, left associativity) : mutator_scope.
      Notation "m1 ;; m2" := (bind_right m1 m2) : mutator_scope.
      Notation "ma *> mb" := (bind_right ma mb) (at level 50, left associativity) : mutator_scope.
      Notation "ma <* mb" := (bind_left ma mb) (at level 50, left associativity) : mutator_scope.

    End CMutNotations.
    Import CMutNotations.
    Local Open Scope mutator_scope.

    Section AssumeAssert.

      Definition assume_formula {Γ} (fml : Prop) : CMut Γ Γ unit :=
        dijkstra (CDijk.assume_formula fml).
      (* Definition assume_term {Γ Σ} (ι : SymInstance Σ) (t : Term Σ ty_bool) : CMut Γ Γ unit := *)
      (*   assume_formula ι (formula_bool t). *)
      Definition assert_formula {Γ Σ} (ι : SymInstance Σ) (fml : Formula Σ) : CMut Γ Γ unit :=
        fun POST δ h => inst fml ι /\ POST tt δ h.
      Definition assert_formulak {A Γ1 Γ2 Σ} (ι : SymInstance Σ) (fml : Formula Σ) (k : CMut Γ1 Γ2 A) : CMut Γ1 Γ2 A :=
        fun POST δ h => inst fml ι /\ k POST δ h.
      Definition assert_formulas {Γ Σ} (ι : SymInstance Σ) (fmls : list (Formula Σ)) : CMut Γ Γ unit :=
        fun POST δ h => inst fmls ι /\ POST tt δ h.

        (* fix assert fmls := *)
        (*   match fmls with *)
        (*   | nil => pure tt *)
        (*   | cons fml fmls => assert fmls ;; assert_formula ι fml *)
        (*   end. *)
      Definition assert_formulask {A Γ1 Γ2 Σ} (ι : SymInstance Σ) (fmls : list (Formula Σ)) (k : CMut Γ1 Γ2 A) : CMut Γ1 Γ2 A :=
        fold_right (assert_formulak ι) k fmls.


    End AssumeAssert.

    Section PatternMatching.

      Definition demonic_match_bool {A Γ1 Γ2} (v : Lit ty_bool) (kt kf : CMut Γ1 Γ2 A) : CMut Γ1 Γ2 A.
      Proof.
        apply demonic_binary.
        - eapply bind_right.
          apply assume_formula.
          apply (is_true v).
          apply kt.
        - eapply bind_right.
          apply assume_formula.
          apply (is_true (negb v)).
          apply kf.
      Defined.

      Definition match_bool {A Γ1 Γ2} (v : Lit ty_bool) (kt kf : CMut Γ1 Γ2 A) : CMut Γ1 Γ2 A :=
        if v then kt else kf.

      Definition match_sum {A} {Γ1 Γ2 σ τ} (v : Lit σ + Lit τ)
        (sinl : Lit σ -> CMut Γ1 Γ2 A) (sinr : Lit τ -> CMut Γ1 Γ2 A) : CMut Γ1 Γ2 A :=
        match v with
        | inl v => sinl v
        | inr v => sinr v
        end.

      Definition match_prod {A} {Γ1 Γ2 σ τ} (v : Lit σ * Lit τ)
        (m : Lit σ -> Lit τ -> CMut Γ1 Γ2 A) : CMut Γ1 Γ2 A :=
        match v with (vl,vr) => m vl vr end.

      Definition match_enum {A E} {Γ1 Γ2} (v : 𝑬𝑲 E)
        (m : 𝑬𝑲 E -> CMut Γ1 Γ2 A) : CMut Γ1 Γ2 A :=
        m v.

      Definition match_record {A R} {Γ1 Γ2 Δ} (p : RecordPat (𝑹𝑭_Ty R) Δ) (t : Lit (ty_record R))
        (m : SymInstance Δ -> CMut Γ1 Γ2 A) : CMut Γ1 Γ2 A :=
        m (record_pattern_match_lit p t).

    End PatternMatching.

    Section State.

      Definition state {Γ Γ' A} (f : LocalStore Γ -> SCHeap -> CMutResult Γ' A) : CMut Γ Γ' A :=
        fun POST δ h =>
          match f δ h with
          | MkCMutResult a δ1 h1 => POST a δ1 h1
          end.

      Definition put_local {Γ Γ'} (δ : LocalStore Γ') : CMut Γ Γ' unit :=
        state (fun _ h => MkCMutResult tt δ h).
      Definition get_local {Γ} : CMut Γ Γ (LocalStore Γ) :=
        state (fun δ h => MkCMutResult δ δ h).
      Definition pop_local {Γ x σ} : CMut (Γ ▻ (x :: σ)) Γ unit :=
        state (fun δ h => MkCMutResult () (env_tail δ) h).
      Definition pops_local {Γ} Δ : CMut (Γ ▻▻ Δ) Γ unit :=
        state (fun δ h => MkCMutResult () (env_drop Δ δ) h).
      Definition push_local {Γ x σ} (v : Lit σ) : CMut Γ (Γ ▻ (x :: σ)) unit :=
        state (fun δ h => MkCMutResult () (env_snoc δ (x :: σ) v) h).
      Global Arguments push_local {Γ _ _} _.
      Definition pushs_local {Γ Δ} (δΔ : LocalStore Δ) : CMut Γ (Γ ▻▻ Δ) unit :=
        state (fun δ h => MkCMutResult () (env_cat δ δΔ) h).
      Definition pushpop {A} {Γ1 Γ2 x σ} (v : Lit σ) (d : CMut (Γ1 ▻ (x :: σ)) (Γ2 ▻ (x :: σ)) A) :
        CMut Γ1 Γ2 A :=
        push_local v ;; bind_left d pop_local.
      Definition pushspops {A} {Γ1 Γ2 Δ} (δΔ : LocalStore Δ) (d : CMut (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) A) :
        CMut Γ1 Γ2 A :=
        pushs_local δΔ ;; bind_left d (pops_local Δ).
      Definition get_heap {Γ} : CMut Γ Γ SCHeap :=
        state (fun δ h => MkCMutResult h δ h).
      Definition put_heap {Γ} (h : SCHeap) : CMut Γ Γ unit :=
        state (fun δ _ => MkCMutResult tt δ h).

      Definition eval_exp {Γ σ} (e : Exp Γ σ) : CMut Γ Γ (Lit σ) :=
        state (fun δ h => MkCMutResult (eval e δ) δ h).
      Definition eval_exps {Γ} {σs : PCtx} (es : NamedEnv (Exp Γ) σs) : CMut Γ Γ (LocalStore σs) :=
        state (fun δ h => MkCMutResult (env_map (fun _ e => eval e δ) es) δ h).

    End State.

    Section ProduceConsume.

      Definition produce_chunk {Γ} (c : SCChunk) : CMut Γ Γ unit :=
        state (fun δ h => MkCMutResult () δ (cons c h)).
      Definition consume_chunk {Γ} (c : SCChunk) : CMut Γ Γ unit :=
        (* "Err [consume_chunk]: empty extraction" *)
        fun POST δ0 h0 => CDijk.angelic_list (extract_scchunk_eqb c h0) (POST tt δ0).
      Global Arguments produce_chunk {Γ} _.
      Global Arguments consume_chunk {Γ} _.

      Fixpoint produce {Γ Σ} (ι : SymInstance Σ) (asn : Assertion Σ) : CMut Γ Γ unit :=
        match asn with
        | asn_formula fml => assume_formula (inst fml ι)
        | asn_chunk c     => produce_chunk (inst c ι)
        | asn_if b a1 a2  => demonic_match_bool (inst b ι) (produce ι a1) (produce ι a2)
        | asn_match_enum E k alts =>
          match_enum
            (inst (T := fun Σ => Term Σ _) k ι)
            (fun K => produce ι (alts K))
        | asn_match_sum σ τ s xl alt_inl xr alt_inr =>
          match_sum
            (inst (T := fun Σ => Term Σ _) s ι)
            (fun v => produce (env_snoc ι (xl :: σ) v) alt_inl)
            (fun v => produce (env_snoc ι (xr :: τ) v) alt_inr)
        | asn_match_list s alt_nil xh xt alt_cons =>
          match inst (T := fun Σ => Term Σ _) s ι with
          | nil        => produce ι alt_nil
          | cons vh vt => produce (ι ► (xh :: _ ↦ vh) ► (xt :: ty_list _ ↦ vt)) alt_cons
          end
        | asn_match_prod s xl xr rhs =>
          match_prod
            (inst (T := fun Σ => Term Σ _) s ι)
            (fun vl vr => produce (ι ► (xl :: _ ↦ vl) ► (xr :: _ ↦ vr)) rhs)
        | asn_match_tuple s p rhs =>
          let t := inst (T := fun Σ => Term Σ _) s ι in
          let ι' := tuple_pattern_match_lit p t in
          produce (ι ►► ι') rhs
        | asn_match_record R s p rhs =>
          match_record p
            (inst (T := fun Σ => Term Σ _) s ι)
            (fun ι' => produce (ι ►► ι') rhs)
        | asn_match_union U s alt__ctx alt__pat alt__rhs =>
          let t := inst (T := fun Σ => Term Σ _) s ι in
          let (K , v) := 𝑼_unfold t in
          let ι' := pattern_match_lit (alt__pat K) v in
          produce (ι ►► ι') (alt__rhs K)
        | asn_sep a1 a2   => produce ι a1 *> produce ι a2
        | asn_exist ς τ a =>
          v <- demonic τ ;;
          produce (env_snoc ι (ς :: τ) v) a
        | asn_debug => pure tt
        end.

      Fixpoint consume {Γ Σ} (ι : SymInstance Σ) (asn : Assertion Σ) : CMut Γ Γ unit :=
        match asn with
        | asn_formula fml => assert_formula ι fml
        | asn_chunk c     => consume_chunk (inst c ι)
        | asn_if b a1 a2  => match_bool (inst b ι) (consume ι a1) (consume ι a2)
        | asn_match_enum E k alts =>
          match_enum
            (inst (T := fun Σ => Term Σ _) k ι)
            (fun K => consume ι (alts K))
        | asn_match_sum σ τ s xl alt_inl xr alt_inr =>
          match_sum
            (inst (T := fun Σ => Term Σ _) s ι)
            (fun v => consume (env_snoc ι (xl :: σ) v) alt_inl)
            (fun v => consume (env_snoc ι (xr :: τ) v) alt_inr)
        | asn_match_list s alt_nil xh xt alt_cons =>
          match inst (T := fun Σ => Term Σ _) s ι with
          | nil        => consume ι alt_nil
          | cons vh vt => consume (ι ► (xh :: _ ↦ vh) ► (xt :: ty_list _ ↦ vt)) alt_cons
          end
        | asn_match_prod s xl xr rhs =>
          match_prod
            (inst (T := fun Σ => Term Σ _) s ι)
            (fun vl vr => consume (ι ► (xl :: _ ↦ vl) ► (xr :: _ ↦ vr)) rhs)
        | asn_match_tuple s p rhs =>
          let t := inst (T := fun Σ => Term Σ _) s ι in
          let ι' := tuple_pattern_match_lit p t in
          consume (ι ►► ι') rhs
        | asn_match_record R s p rhs =>
          match_record p
            (inst (T := fun Σ => Term Σ _) s ι)
            (fun ι' => consume (ι ►► ι') rhs)
        | asn_match_union U s alt__ctx alt__pat alt__rhs =>
          let t := inst (T := fun Σ => Term Σ _) s ι in
          let (K , v) := 𝑼_unfold t in
          let ι' := pattern_match_lit (alt__pat K) v in
          consume (ι ►► ι') (alt__rhs K)
        | asn_sep a1 a2   => consume ι a1 *> consume ι a2
        | asn_exist ς τ a =>
          v <- angelic τ ;;
          consume (env_snoc ι (ς :: τ) v) a
        | asn_debug => pure tt
        end.

    End ProduceConsume.

    Section Exec.

      Definition call_contract {Γ Δ τ} (contract : SepContract Δ τ) (vs : LocalStore Δ) : CMut Γ Γ (Lit τ) :=
        match contract with
        | MkSepContract _ _ Σe δ req result ens =>
          ι <- angelic_ctx Σe ;;
          assert_formulas ι (formula_eqs δ (lift vs)) ;;
          consume ι req  ;;
          v <- demonic τ ;;
          produce (env_snoc ι (result::τ) v) ens ;;
          pure v
        end.

      Fixpoint exec {Γ τ} (s : Stm Γ τ) : CMut Γ Γ (Lit τ) :=
        match s with
        | stm_lit _ l => pure l
        | stm_exp e => eval_exp e
        | stm_let x σ s k =>
          v <- exec s ;;
          pushpop v (exec k)
        | stm_block δ k =>
          pushspops δ (exec k)
        | stm_assign x e =>
          v <- exec e ;;
          state (fun δ h => MkCMutResult tt (δ ⟪ x ↦ v ⟫)%env h) ;;
          pure v
        | stm_call f es =>
          args <- eval_exps es ;;
          match CEnv f with
          | Some c => call_contract c args
          | None   => error "Err [cmut_exec]: Function call without contract"
          end
        | stm_call_external f es =>
          eval_exps es >>= call_contract (CEnvEx f)
        | stm_call_frame δ' s =>
          δ <- get_local ;;
          put_local δ' ;;
          v <- exec s ;;
          put_local δ ;;
          pure v
        | stm_if e s1 s2 =>
          v <- eval_exp e ;;
          demonic_match_bool v (exec s1) (exec s2)
        | stm_seq e k => exec e ;; exec k
        | stm_assertk e1 _ k =>
          v <- eval_exp e1 ;;
          if v
          then exec k
          else block
        | stm_fail _ s =>
          block
        | stm_match_enum E e alts =>
          K <- eval_exp e ;;
          match_enum
            K
            (fun K => exec (alts K))
        | stm_read_register reg =>
          v <- angelic τ ;;
          let c := scchunk_ptsreg reg v in
          consume_chunk c ;;
          produce_chunk c ;;
          pure v
        | stm_write_register reg e =>
          v__new <- eval_exp e ;;
          v__old <- angelic τ ;;
          consume_chunk (scchunk_ptsreg reg v__old) ;;
          produce_chunk (scchunk_ptsreg reg v__new) ;;
          pure v__new
        | @stm_match_list _ _ σ e s1 xh xt s2 =>
          v <- eval_exp e ;;
          match v : list (Lit σ) with
          | nil => exec s1
          | cons h t =>
            pushspops
              (env_snoc (env_snoc env_nil (xh :: σ) h) (xt :: ty_list σ) t)
              (exec s2)
          end
        | stm_match_sum e xinl s1 xinr s2 =>
          v <- eval_exp e ;;
          match_sum
            v
            (fun v => pushpop v (exec s1))
            (fun v => pushpop v (exec s2))
        | stm_match_prod e xl xr s =>
          v <- eval_exp e ;;
          match_prod
            v
            (fun vl vr =>
               pushspops
                 (env_snoc (env_snoc env_nil (xl :: _) vl) (xr :: _) vr)
                 (exec s))
        | stm_match_tuple e p rhs =>
          v <- eval_exp e ;;
          pushs_local (tuple_pattern_match_lit p v) ;;
          exec rhs <*
          pops_local _
        | stm_match_union U e alt__pat alt__rhs =>
          v <- eval_exp e ;;
          let (K , v) := 𝑼_unfold v in
          pushspops (pattern_match_lit (alt__pat K) v) (exec (alt__rhs K))
        | stm_match_record R e p rhs =>
          v <- eval_exp e ;;
          pushspops (record_pattern_match_lit p v) (exec rhs)
        | stm_bind s k =>
          v <- exec s ;;
          exec (k v)
        | stm_debugk k =>
          exec k
        end.

      Definition leakcheck {Γ} : CMut Γ Γ unit :=
        get_heap >>= fun h =>
        match h with
        | nil => pure tt
        | _   => error "Err [cmut_leakcheck]: heap leak"
        end.

    End Exec.

    Definition exec_contract {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) :
     SymInstance (sep_contract_logic_variables c) -> CMut Δ Δ unit :=
      match c with
      | MkSepContract _ _ Σ δ req result ens =>
        fun ι =>
        produce ι req ;;
        exec s >>= fun v =>
        consume (env_snoc ι (result::τ) v) ens
        (* cmut_block *)
        (* cmut_leakcheck *)
      end%mut.

    Definition ValidContract {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      forall ι : SymInstance (sep_contract_logic_variables c),
        let δΔ : LocalStore Δ := inst (sep_contract_localstore c) ι in
        exec_contract c body ι (fun _ _ _ => True) δΔ nil.

  End CMut.

  (* Section SemiConcreteWP. *)

  (*   Definition SCProp (Γ : PCtx) : Type := *)
  (*     LocalStore Γ -> SCHeap -> Prop. *)

  (*   Definition cmut_wp {Γ1 Γ2 A} (m : CMut Γ1 Γ2 A) (POST : A -> SCProp Γ2) : SCProp Γ1 := *)
  (*     m POST. *)
  (*   Global Arguments cmut_wp : simpl never. *)

  (*   Lemma cmut_wp_monotonic {A} {Γ1 Γ2} (m : CMut Γ1 Γ2 A) *)
  (*     (P Q : A -> SCProp Γ2) (PQ : forall a δ h, P a δ h -> Q a δ h) : *)
  (*     forall δ h, *)
  (*       cmut_wp m P δ h -> cmut_wp m Q δ h. *)
  (*   Proof. *)
  (*   Admitted. *)
  (*   (*   unfold cmut_wp. intros ? ?. *) *)
  (*   (*   unfold CMut in m. *) *)
  (*   (*   apply outcome_satisfy_monotonic; intros []; apply PQ. *) *)
  (*   (* Qed. *) *)

  (*   (* Lemma cmut_wp_equiv {A} {Γ1 Γ2} (m : CMut Γ1 Γ2 A) *) *)
  (*   (*   (P Q : A -> SCProp Γ2) (PQ : forall a δ h, P a δ h <-> Q a δ h) : *) *)
  (*   (*   forall δ h, cmut_wp m P δ h <-> cmut_wp m Q δ h. *) *)
  (*   (* Proof. split; apply cmut_wp_monotonic; apply PQ. Qed. *) *)

  (*   Lemma cmut_wp_pure {A Γ} (a : A) (POST : A -> SCProp Γ) : *)
  (*     forall δ h, *)
  (*       cmut_wp (cmut_pure a) POST δ h <-> *)
  (*       POST a δ h. *)
  (*   Proof. reflexivity. Qed. *)

  (*   Lemma cmut_wp_bind {Γ1 Γ2 Γ3 A B} (ma : CMut Γ1 Γ2 A) (f : A -> CMut Γ2 Γ3 B) *)
  (*     (POST : B -> SCProp Γ3) : *)
  (*     forall δ h, *)
  (*       cmut_wp (cmut_bind ma f) POST δ h <-> *)
  (*       cmut_wp ma (fun a => cmut_wp (f a) POST) δ h. *)
  (*   Proof. reflexivity. Qed. *)

  (*   Lemma cmut_wp_demonic {Γ τ} (POST : Lit τ -> SCProp Γ) : *)
  (*     forall δ h, *)
  (*       cmut_wp (cmut_demonic τ) POST δ h <-> forall v, POST v δ h. *)
  (*   Proof. reflexivity. Qed. *)

  (*   Lemma cmut_wp_demonic_binary {Γ1 Γ2 A} (sm1 sm2 : CMut Γ1 Γ2 A) (POST : A -> SCProp Γ2) : *)
  (*     forall δ h, *)
  (*       cmut_wp (cmut_demonic_binary sm1 sm2) POST δ h <-> *)
  (*       cmut_wp sm1 POST δ h /\ cmut_wp sm2 POST δ h. *)
  (*   Proof. reflexivity. Qed. *)

  (*   Lemma cmut_wp_angelic {Γ τ} (POST : Lit τ -> SCProp Γ) : *)
  (*     forall δ h, *)
  (*       cmut_wp (cmut_angelic τ) POST δ h <-> exists v, POST v δ h. *)
  (*   Proof. reflexivity. Qed. *)

  (*   Lemma cmut_wp_angelic_ctx {N : Set} {Γ : PCtx} {Δ : NCtx N Ty} (POST : NamedEnv Lit Δ -> SCProp Γ) : *)
  (*     forall δ h, *)
  (*       cmut_wp (cmut_angelic_ctx Δ) POST δ h <-> exists vs : NamedEnv Lit Δ, POST vs δ h. *)
  (*   Proof. *)
  (*     unfold cmut_wp, cmut_angelic_ctx, cmut_dijkstra. *)
  (*     intros δ h. rewrite CDijk.wp_angelic_ctx. reflexivity. *)
  (*   Qed. *)

  (*   Lemma cmut_wp_angelic_binary {Γ1 Γ2 A} (sm1 sm2 : CMut Γ1 Γ2 A) (POST : A -> SCProp Γ2) : *)
  (*     forall δ h, *)
  (*       cmut_wp (cmut_angelic_binary sm1 sm2) POST δ h <-> *)
  (*       cmut_wp sm1 POST δ h \/ cmut_wp sm2 POST δ h. *)
  (*   Proof. reflexivity. Qed. *)

  (*   Lemma cmut_wp_state {Γ1 Γ2 A} (f : LocalStore Γ1 -> SCHeap -> CMutResult Γ2 A) (POST : A -> SCProp Γ2) : *)
  (*     forall δ h, *)
  (*       cmut_wp (cmut_state f) POST δ h <-> *)
  (*       match f δ h with *)
  (*       | MkCMutResult a δ' h' => POST a δ' h' *)
  (*       end. *)
  (*   Proof. reflexivity. Qed. *)

  (*   Lemma cmut_wp_bind_right {Γ1 Γ2 Γ3 A B} (ma : CMut Γ1 Γ2 A) (mb : CMut Γ2 Γ3 B) *)
  (*     (POST : B -> SCProp Γ3) : *)
  (*     forall δ h, *)
  (*       cmut_wp (cmut_bind_right ma mb) POST δ h <-> *)
  (*       cmut_wp ma (fun _ => cmut_wp mb POST) δ h. *)
  (*   Proof. reflexivity. Qed. *)

  (*   Lemma cmut_wp_assert_formula {Γ Σ} {ι : SymInstance Σ} {fml : Formula Σ} *)
  (*     (POST : unit -> SCProp Γ ) : *)
  (*     forall δ h, *)
  (*       cmut_wp (cmut_assert_formula ι fml) POST δ h <-> *)
  (*       inst fml ι /\ POST tt δ h. *)
  (*   Proof. reflexivity. Qed. *)

  (*   Lemma cmut_wp_assume_formula {Γ Σ} {ι : SymInstance Σ} {fml : Formula Σ} *)
  (*     (POST : unit -> SCProp Γ ) : *)
  (*     forall δ h, *)
  (*       cmut_wp (cmut_assume_formula (inst fml ι)) POST δ h <-> *)
  (*       (inst (A := Prop) fml ι -> POST tt δ h). *)
  (*   Proof. reflexivity. Qed. *)

  (*   Lemma cmut_wp_assert_formulak {A Γ1 Γ2 Σ} {ι : SymInstance Σ} {fml : Formula Σ} *)
  (*     {k : CMut Γ1 Γ2 A} (POST : A -> SCProp Γ2) : *)
  (*     forall δ h, *)
  (*       cmut_wp (cmut_assert_formulak ι fml k) POST δ h <-> *)
  (*       inst fml ι /\ cmut_wp k POST δ h. *)
  (*   Proof. reflexivity. Qed. *)

  (*   Lemma cmut_wp_assert_formulas {Γ Σ} {ι : SymInstance Σ} {fmls : list (Formula Σ)} *)
  (*     (POST : unit -> SCProp Γ) : *)
  (*     forall δ h, *)
  (*       cmut_wp (cmut_assert_formulas ι fmls) POST δ h <-> *)
  (*       inst fmls ι /\ POST tt δ h. *)
  (*   Proof. *)
  (*     reflexivity. *)
  (*     (* intros δ h. revert POST. *) *)
  (*     (* induction fmls; cbn; intros. *) *)
  (*     (* - rewrite cmut_wp_pure. intuition. constructor. *) *)
  (*     (* - rewrite cmut_wp_bind_right, IHfmls. *) *)
  (*     (*   rewrite inst_pathcondition_cons, cmut_wp_assert_formula. *) *)
  (*     (*   intuition. *) *)
  (*   Qed. *)

  (*   Lemma cmut_wp_assert_formulask {A Γ1 Γ2 Σ} {ι : SymInstance Σ} {fmls : list (Formula Σ)} *)
  (*     {k : CMut Γ1 Γ2 A} (POST : A -> SCProp Γ2) : *)
  (*     forall δ h, *)
  (*       cmut_wp (cmut_assert_formulask ι fmls k) POST δ h <-> *)
  (*       inst (T := PathCondition) fmls ι /\ cmut_wp k POST δ h. *)
  (*   Proof. *)
  (*     intros δ h. unfold cmut_assert_formulask. *)
  (*     induction fmls; cbn. *)
  (*     - clear. intuition. constructor. *)
  (*     - rewrite inst_pathcondition_cons, cmut_wp_assert_formulak, IHfmls. *)
  (*       clear. intuition. *)
  (*   Qed. *)

  (*   Lemma cmut_wp_demonic_match_bool {A Γ1 Γ2} (v : Lit ty_bool) (kt kf : CMut Γ1 Γ2 A) : *)
  (*     forall POST δ h, *)
  (*       cmut_wp (cmut_demonic_match_bool v kt kf) POST δ h <-> *)
  (*       if v *)
  (*       then cmut_wp kt POST δ h *)
  (*       else cmut_wp kf POST δ h. *)
  (*   Proof. *)
  (*     intros. *)
  (*     cbv [cmut_wp cmut_demonic_match_bool cmut_bind_right cmut_demonic_binary *)
  (*                  cmut_assume_formula cmut_bind cmut_dijkstra CDijk.assume_formula is_true negb]. *)
  (*     destruct v; intuition; discriminate. *)
  (*   Qed. *)

  (*   Lemma cmut_wp_match_sum {A Γ1 Γ2 σ τ} (v : Lit σ + Lit τ) *)
  (*     (kl : Lit σ -> CMut Γ1 Γ2 A) (kr : Lit τ -> CMut Γ1 Γ2 A) : *)
  (*     forall POST δ h, *)
  (*       cmut_wp (cmut_match_sum v kl kr) POST δ h <-> *)
  (*       match v with *)
  (*       | inl v => cmut_wp (kl v) POST δ h *)
  (*       | inr v => cmut_wp (kr v) POST δ h *)
  (*       end. *)
  (*   Proof. destruct v; reflexivity. Qed. *)

  (*   Lemma cmut_wp_match_prod {A Γ1 Γ2 σ τ} (v : Lit σ * Lit τ) *)
  (*     (k : Lit σ -> Lit τ -> CMut Γ1 Γ2 A) : *)
  (*     forall POST δ h, *)
  (*       cmut_wp (cmut_match_prod v k) POST δ h <-> *)
  (*       match v with *)
  (*       | (vl,vr) => cmut_wp (k vl vr) POST δ h *)
  (*       end. *)
  (*   Proof. destruct v; reflexivity. Qed. *)

  (*   Lemma cmut_wp_match_record {A R Γ1 Γ2 Δ} (p : RecordPat (𝑹𝑭_Ty R) Δ) (v : Lit (ty_record R)) *)
  (*         (k : SymInstance Δ → CMut Γ1 Γ2 A) : *)
  (*     forall POST δ h, *)
  (*       cmut_wp (cmut_match_record p v k) POST δ h <-> *)
  (*       forall vs : NamedEnv Lit (𝑹𝑭_Ty R), *)
  (*         v = 𝑹_fold vs -> *)
  (*         cmut_wp (k (record_pattern_match_env p vs)) POST δ h. *)
  (*   Proof. *)
  (*     intros. unfold cmut_match_record. *)
  (*     split; intros Hwp. *)
  (*     - intros vs ->. *)
  (*       unfold record_pattern_match_lit in Hwp. *)
  (*       now rewrite 𝑹_unfold_fold in Hwp. *)
  (*     - specialize (Hwp (𝑹_unfold v)). *)
  (*       rewrite 𝑹_fold_unfold in Hwp. *)
  (*       now apply Hwp. *)
  (*   Qed. *)

  (* End SemiConcreteWP. *)

End SemiConcrete.
