(******************************************************************************)
(* Copyright (c) 2019 Steven Keuchel                                          *)
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
     Program.Equality
     Program.Tactics
     ZArith.ZArith
     Strings.String
     Classes.Morphisms
     Classes.Morphisms_Prop
     Classes.Morphisms_Relations.

From Equations Require Import
     Equations.

From MicroSail Require Import
     Sep.Spec
     Sep.Logic
     Sep.Hoare
     Syntax
     Tactics
     Symbolic.Mutator
     Symbolic.Outcome.
From MicroSail Require
     SemiConcrete.Mutator
     SemiConcrete.Sound.

Set Implicit Arguments.

Import CtxNotations.
Import EnvNotations.

Module Soundness
       (Import termkit : TermKit)
       (Import progkit : ProgramKit termkit)
       (Import assertkit : AssertionKit termkit progkit)
       (Import contractkit : SymbolicContractKit termkit progkit assertkit).
  Module MUT := Mutators termkit progkit assertkit contractkit.
  Import MUT.
  Module LOG := ProgramLogic termkit progkit assertkit contractkit.
  Import LOG.
  Module SCMUT := SemiConcrete.Sound.Soundness termkit progkit assertkit contractkit.
  Import SCMUT.MUT.

  Program Instance proper_sub_comp {Σ1 Σ2 Σ3} : Proper (eq ==> eq ==> eq) (@sub_comp Σ1 Σ2 Σ3).
  Admit Obligations.

  Module DynMutV1Soundness.

    Import DynMutV1.

    Section WithSemantics.

      Definition semiconcretize_heap {Σ} (ι : SymInstance Σ) (h : SymbolicHeap Σ) : SCHeap :=
        List.map (inst_chunk ι) h.

      Definition represents {Γ Σ} (ι : SymInstance Σ) (s__sym : SymbolicState Γ Σ) (s__sc : SCState Γ) : Prop :=
        semiconcretize_heap ι (symbolicstate_heap s__sym)       = scstate_heap s__sc /\
        inst_localstore     ι (symbolicstate_localstore s__sym) = scstate_localstore s__sc /\
        inst_pathcondition  ι (symbolicstate_pathcondition s__sym).

      Definition syminstance_rel {Σ1 Σ2} (ζ : Sub Σ1 Σ2) (ι1 : SymInstance Σ1) (ι2 : SymInstance Σ2) : Prop :=
        ι1 = env_map (fun _ => inst_term ι2) ζ.

      Lemma syminstance_rel_refl {Σ} (ι : SymInstance Σ) :
        syminstance_rel (sub_id Σ) ι ι.
      Proof.
        unfold SymInstance, NamedEnv, syminstance_rel, sub_id in *.
        apply env_lookup_extensional.
        intros [x τ] ?.
        now rewrite env_map_tabulate, env_lookup_tabulate.
      Qed.

      Lemma syminstance_rel_snoc {Σ1 Σ2 x τ} (ζ : Sub Σ1 Σ2) (ι1 : SymInstance Σ1) ι2 :
        forall v,
          syminstance_rel ζ ι1 ι2 <->
          syminstance_rel (env_snoc ζ (x,τ) (term_lit τ v)) (env_snoc ι1 (x,τ) v) ι2.
      Proof.
        unfold SymInstance, Sub, NamedEnv, syminstance_rel in *. intros. split.
        - cbn; intros; subst; now cbn.
        - cbn; intros.
          now dependent elimination H.
      Qed.

      Lemma represents_rel {Γ Σ} (ι : SymInstance Σ) (s__sym : SymbolicState Γ Σ) (s__sc : SCState Γ) :
        forall Σ1 (ζ : Sub Σ Σ1) (ι2 : SymInstance Σ1),
          syminstance_rel ζ ι ι2 ->
          represents ι s__sym s__sc ->
          represents ι2 (subst ζ s__sym) s__sc.
      Proof.
      Admitted.

      Definition scmut_wp {Γ1 Γ2 A}
        (m : SCMut Γ1 Γ2 A)
        (POST : A -> SCState Γ2 -> Prop)
        (s1 : SCState Γ1) : Prop :=
        outcome_satisfy (m s1) (fun r => POST (scmutres_value r) (scmutres_state r)).

      Definition dmut_wp {Γ1 Γ2 Σ0 A}
        (m : DynamicMutator Γ1 Γ2 A Σ0)
        (POST : forall Σ1, Sub Σ0 Σ1 -> A Σ1 -> SymbolicState Γ2 Σ1 -> Prop)
        (s1 : SymbolicState Γ1 Σ0) : Prop :=
        forall Σ1 (ζ1 : Sub Σ0 Σ1),
          outcome_satisfy
            (m Σ1 ζ1 (subst ζ1 s1))
            (fun '(@MkDynMutResult _ _ _ Σ2 ζ2 r) =>
               POST
                 Σ2
                 (sub_comp ζ1 ζ2)
                 (mutator_result_value r)
                 (mutator_result_state r) /\
               valid_obligations
                 (mutator_result_obligations r)).

      Definition approximates {Γ1 Γ2 Σ} (ι : SymInstance Σ) (dm : DynamicMutator Γ1 Γ2 Unit Σ) (sm : SCMut Γ1 Γ2 unit) : Prop :=
        forall (s__sym : SymbolicState Γ1 Σ) (s__sc : SCState Γ1) (POST : unit -> SCState Γ2 -> Prop),
          represents ι s__sym s__sc ->
          dmut_wp
            dm
            (fun Σ1 ζ1 v1 s__sym1 =>
               forall ι1 s__sc1,
                 syminstance_rel ζ1 ι ι1 ->
                 represents ι1 s__sym1 s__sc1 ->
                 POST v1 s__sc1)
            s__sym ->
          scmut_wp sm POST s__sc.

      Lemma scmut_wp_demonic_binary {Γ1 Γ2 A} (sm1 sm2 : SCMut Γ1 Γ2 A) (s__sc : SCState Γ1) (POST : A -> SCState Γ2 -> Prop) :
        scmut_wp (scmut_demonic_binary sm1 sm2) POST s__sc <-> scmut_wp sm1 POST s__sc /\ scmut_wp sm2 POST s__sc.
      Proof. unfold scmut_wp, scmut_demonic_binary; cbn; intuition. Qed.

      Lemma dmut_wp_demonic_binary {Γ1 Γ2 Σ A} (m1 m2 : DynamicMutator Γ1 Γ2 A Σ)
        (POST : forall Σ', Sub Σ Σ' -> A Σ' -> SymbolicState Γ2 Σ' -> Prop) (s : SymbolicState Γ1 Σ) :
          dmut_wp (dmut_demonic_binary m1 m2) POST s <->
          dmut_wp m1 POST s /\ dmut_wp m2 POST s.
      Proof. unfold dmut_wp, dmut_demonic_binary; cbn; intuition. Qed.

      Lemma approximates_demonic_binary {Γ1 Γ2 Σ} (ι : SymInstance Σ)
            (dm1 dm2 : DynamicMutator Γ1 Γ2 Unit Σ) (sm1 sm2 : SCMut Γ1 Γ2 unit) :
        approximates ι dm1 sm1 ->
        approximates ι dm2 sm2 ->
        approximates ι (dmut_demonic_binary dm1 dm2) (scmut_demonic_binary sm1 sm2).
      Proof.
        intros H1 H2 ? ? ? H__s H.
        apply scmut_wp_demonic_binary.
        apply dmut_wp_demonic_binary in H.
        split.
        now apply (H1 _ _ _ H__s).
        now apply (H2 _ _ _ H__s).
      Qed.

      Lemma scmut_wp_demonic {Γ1 Γ2 A B} (sm : B -> SCMut Γ1 Γ2 A) (s__sc : SCState Γ1) (POST : A -> SCState Γ2 -> Prop) :
        scmut_wp (scmut_demonic sm) POST s__sc <-> forall v, scmut_wp (sm v) POST s__sc.
      Proof. unfold scmut_wp, scmut_demonic; cbn; intuition. Qed.

      Lemma dmut_wp_demonic {Γ1 Γ2 Σ A B} (m : B -> DynamicMutator Γ1 Γ2 A Σ)
        (POST : forall Σ', Sub Σ Σ' -> A Σ' -> SymbolicState Γ2 Σ' -> Prop) (s : SymbolicState Γ1 Σ) :
          dmut_wp (dmut_demonic m) POST s <->
          forall b, dmut_wp (m b) POST s.
      Proof. unfold dmut_wp, dmut_demonic; cbn; intuition. Qed.

      Lemma dmut_produce_chunk_sound {Γ Σ} (ι : SymInstance Σ) (c : Chunk Σ) :
        approximates
          (Γ1 := Γ) (Γ2 := Γ) ι
          (dmut_produce_chunk c)
          (scmut_produce_chunk (inst_chunk ι c)).
      Proof.
        intros [pc δ__sym h__sym] [δ__sc h__sc] ? (H__h & H__δ & H__pc); cbn in *.
        intros; destruct_conjs.
        specialize (H Σ (sub_id Σ)). cbn in H.
        destruct H as [H _]. apply (H ι); clear H.
        rewrite sub_comp_id_left.
        apply syminstance_rel_refl.
        unfold represents; cbn.
        now rewrite ?subst_sub_id, H__h.
      Qed.

      Lemma dmut_assume_term_sound {Γ Σ} (ι : SymInstance Σ) (b : Term Σ ty_bool) :
        approximates
          (Γ1 := Γ) (Γ2 := Γ) ι
          (dmut_assume_term b)
          (scmut_assume_term ι b).
      Proof.
        intros ? ? ? H__state H.
        unfold dmut_wp, dmut_assume_term, dmut_assume_formula in H.
        specialize (H Σ (sub_id Σ)).
        change (sub_formula (sub_id Σ) (formula_bool b))
          with (subst (sub_id Σ) (formula_bool b)) in H.
        rewrite ?subst_sub_id in H.
        unfold scmut_assume_term.
        destruct (try_solve_formula (formula_bool b)) eqn:?.
        - destruct (try_solve_formula_spec _ Heqo ι); clear Heqo.
          + cbn in *. destruct H as [H _].
            rewrite i. cbn. apply (H ι).
            rewrite sub_comp_id_left.
            apply syminstance_rel_refl.
            assumption.
          + cbn in n. destruct (inst_term ι b); intuition.
        - clear Heqo.
          destruct (inst_term ι b) eqn:?; cbn.
          * cbn in *. destruct H as [H _].
            apply (H ι).
            rewrite sub_comp_id_left.
            apply syminstance_rel_refl.
            revert H__state Heql. clear.
            unfold represents; destruct s__sym;
              cbn; intuition.
          * trivial.
      Qed.

      Opaque dmut_assume_term.

      Definition dmutres_geq {Γ A Σ} `{Subst A} (r1 r2 : DynamicMutatorResult Γ A Σ) : Prop :=
        match r1 , r2 with
        | MkDynMutResult ζ1 (MkMutResult a1 s1 w1), MkDynMutResult ζ2 (MkMutResult a2 s2 w2) =>
          exists ζ12, (ζ2 = sub_comp ζ1 ζ12 /\ a2 = subst ζ12 a1 /\ s2 = subst ζ12 s1 /\ w1 = w2)
        end.

      Definition dmutres_pred_monotonic {Γ A Σ} `{Subst A} (p : DynamicMutatorResult Γ A Σ -> Prop) : Prop :=
        forall (r1 r2 : DynamicMutatorResult Γ A Σ),
          dmutres_geq r1 r2 -> p r1 -> p r2.

      Definition dmutres_sub {Γ A Σ1 Σ2} (ζ : Sub Σ1 Σ2) (r : DynamicMutatorResult Γ A Σ2) :
        DynamicMutatorResult Γ A Σ1 :=
        match r with
        | @MkDynMutResult _ _ _ Σ3 ζ3 r =>
          @MkDynMutResult _ _ _ Σ3 (sub_comp ζ ζ3) r
        end.

      Definition substpred {Γ A Σ1 Σ2} (ζ : Sub Σ1 Σ2) :
        (DynamicMutatorResult Γ A Σ1 -> Prop) ->
        (DynamicMutatorResult Γ A Σ2 -> Prop) :=
        fun p r => p (dmutres_sub ζ r).

      Definition dmut_wf {Γ1 Γ2 A Σ0} `{Subst A} (d : DynamicMutator Γ1 Γ2 A Σ0) : Prop :=
        forall Σ1 Σ2 (ζ1 : Sub Σ0 Σ1) (ζ2 : Sub Σ1 Σ2) (s1 : SymbolicState Γ1 Σ1)
               (POST : DynamicMutatorResult Γ2 A Σ1 -> Prop) (POST_mon : dmutres_pred_monotonic POST),
          outcome_satisfy (d Σ1 ζ1 s1) POST ->
          outcome_satisfy (d Σ2 (subst ζ2 ζ1) (subst ζ2 s1)) (substpred ζ2 POST).

      Lemma dmut_wf_pure {Γ A Σ} {subA: Subst A} {sublA: SubstLaws A} (a : A Σ) :
        dmut_wf (dmut_pure (Γ := Γ) a).
      Proof.
        unfold dmut_wf, substpred; cbn; intros.
        revert H.
        apply POST_mon.
        unfold dmutres_geq.
        exists ζ2; cbn.
        fold (sub_comp ζ1 ζ2).
        rewrite sub_comp_id_right, sub_comp_id_left, subst_sub_comp.
        intuition.
      Qed.

      Definition dmut_pred_monotonic {Γ Σ0 A} `{Subst A} (p : forall Σ1, Sub Σ0 Σ1 -> A Σ1 -> SymbolicState Γ Σ1 -> Prop) : Prop :=
        forall Σ1 Σ2 (ζ1 : Sub Σ0 Σ1) (ζ2 : Sub Σ1 Σ2) (a1 : A Σ1) (s1 : SymbolicState Γ _),
          p Σ1 ζ1 a1 s1 ->
          p Σ2 (sub_comp ζ1 ζ2) (subst ζ2 a1) (subst ζ2 s1).

      Definition dmut_wf' {Γ1 Γ2 A Σ0} `{Subst A} (d : DynamicMutator Γ1 Γ2 A Σ0) : Prop :=
        forall (POST : forall Σ1, Sub Σ0 Σ1 -> A Σ1 -> SymbolicState Γ2 Σ1 -> Prop)
               (POST_mon : dmut_pred_monotonic POST)
               (s : SymbolicState Γ1 Σ0) Σ1 (ζ : Sub Σ0 Σ1),
          dmut_wp d POST s ->
          dmut_wp (dmut_sub ζ d) (fun Σ2 ζ2 => POST Σ2 (sub_comp ζ ζ2)) (subst ζ s).

      Lemma dmut_wf'_pure {Γ A Σ} `{Subst A} (a : A Σ) :
        dmut_wf' (dmut_pure (Γ := Γ) a).
      Proof.
        unfold dmut_wf', dmut_wp, dmut_sub, dmut_pure; cbn; intros.
        split; auto.
        destruct (H0 Σ0 (sub_comp ζ ζ1)).
        rewrite <- subst_sub_comp.
        rewrite sub_comp_id_right.
        rewrite sub_comp_id_right in H1.
        assumption.
      Qed.

      Opaque sub_comp.

      Lemma dmut_wp_fresh {Γ Σ0 A x τ} `{Subst A}
            (d : DynamicMutator Γ Γ A (Σ0 ▻ (x,τ))%ctx)
            (POST : forall Σ1, Sub Σ0 Σ1 -> A Σ1 -> SymbolicState Γ Σ1 -> Prop)
            (POST_mon : dmut_pred_monotonic POST)
            (s : SymbolicState Γ Σ0) (wfd : dmut_wf d) :
        dmut_wp (dmut_fresh (x,τ) d) POST s <->
        dmut_wp d (fun Σ1 ζ1 a1 s1 => POST Σ1 (env_tail ζ1) a1 s1) (wk1_symbolicstate s).
      Proof.
        unfold dmut_wp, dmut_fresh; cbn; split; intros HYP ? ?.
        - dependent elimination ζ1 as [@env_snoc Σ0 ζ1 _ v]. cbn in v.
          specialize (HYP Σ1 ζ1).
          rewrite outcome_satisfy_map in HYP; cbn in *.
          eapply (@wfd _ Σ1 _ (env_snoc (sub_id _) (_,τ) v)) in HYP. clear wfd.
          unfold wk1_symbolicstate in *.
          rewrite <- subst_sub_comp in *.
          rewrite <- (subst_sub_comp ζ1 (sub_comp sub_wk1 (sub_id Σ1 ► (x ∶ τ ↦ v)))%env s) in HYP.
          rewrite sub_comp_wk1. cbn.
          rewrite sub_comp_wk1 in HYP.
          match goal with
          | H: outcome_satisfy (d ?Σ ?ζ1 _) _ |- outcome_satisfy (d ?Σ ?ζ2 _) _ =>
            replace ζ1 with ζ2 in H
          end.
          2: {
            cbn.
            f_equal.
            unfold subst at 2.
            unfold SubstEnv.
            rewrite env_map_map.
            symmetry.
            apply env_map_id_eq.
            intros [] ?.
            rewrite <- subst_sub_comp.
            rewrite sub_comp_wk1.
            cbn.
            now rewrite subst_sub_id.
          }
          match goal with
          | H: outcome_satisfy (d ?Σ ?ζ ?s1) _ |- outcome_satisfy (d ?Σ ?ζ ?s2) _ =>
            replace s1 with s2 in H
          end.
          2: {
            clear.
            cbn.
            now rewrite sub_comp_id_right.
          }
          refine (outcome_satisfy_monotonic _ _ HYP).
          intros [Σ2 ζ2 r2]. cbn. clear.
          intuition.
          match goal with
          | H: POST _ ?ζ1 _ _ |- POST _ ?ζ2 _ _ =>
            replace ζ1 with ζ2 in H
          end.
          intuition.
          clear.
          rewrite sub_comp_wk1; cbn.
          Transparent sub_comp. cbn.
          change (env_map (fun (b : 𝑺 * Ty) (a : Term Σ1 (snd b)) => subst (T:= fun _ => Term _ _) ζ2 a) (sub_id Σ1))
            with (sub_comp (sub_id Σ1) ζ2).
          now rewrite sub_comp_id_left.
          revert POST_mon; clear.
          unfold dmutres_pred_monotonic.
          intros ? [Σ2 ζ2 [a2 s2 w2]] [Σ3 ζ3 [a3 s3 w3]]; cbn.
          intros [ζ12]; intuition. subst.
          apply (POST_mon _ _ _ ζ12) in H0.
          rewrite !sub_comp_assoc in H0.
          exact H0.
        - rewrite outcome_satisfy_map.
          specialize (HYP (Σ1 ▻ (x,τ)) (subst sub_wk1 ζ1 ► (x ∶ τ ↦ @term_var _ x τ inctx_zero))).
          unfold wk1_symbolicstate in *.
          rewrite <- subst_sub_comp in *.
          rewrite sub_comp_wk1 in HYP.
          cbn in HYP.
          refine (outcome_satisfy_monotonic _ _ HYP).
          intros [Σ2 ζ2 r2]. clear.
          dependent elimination ζ2 as [@env_snoc Σ1 ζ2 _ t].
          cbn in *.
          rewrite sub_comp_wk1. cbn.
          intuition.
          match goal with
          | H: POST _ ?ζ1 _ _ |- POST _ ?ζ2 _ _ =>
            replace ζ1 with ζ2 in H
          end.
          auto.
          clear.
          unfold subst at 2, SubstEnv.
          rewrite env_map_map.
          apply env_map_ext.
          intros [y σ] ?.
          rewrite <- subst_sub_comp.
          now rewrite sub_comp_wk1.
      Qed.

      (* Lemma dmut_wp_fresh' {Γ Σ0 A x τ} *)
      (*       (d : DynamicMutator Γ Γ A (Σ0 ▻ (x,τ))%ctx) (wfd : dmut_wf d) *)
      (*       (POST : forall Σ1, Sub Σ0 Σ1 -> A Σ1 -> SymbolicState Γ Σ1 -> Prop) *)
      (*       (s : SymbolicState Γ Σ0) : *)
      (*   dmut_wp (dmut_fresh (x,τ) d) POST s <-> *)
      (*   forall v, *)
      (*     dmut_wp (dmut_sub (env_snoc (sub_id Σ0) (x,τ) (term_lit τ v)) d) POST s. *)
      (* Proof. *)
      (*   unfold dmut_wp, dmut_fresh, dmut_sub; cbn. split; intro HYP. *)
      (*   - intros. *)
      (*     specialize (HYP Σ1 ζ1). *)
      (*     rewrite outcome_satisfy_map in HYP; cbn in *. *)
      (*     admit. *)
      (*   - intros ? ?. *)
      (*     rewrite outcome_satisfy_map. *)
      (* Admitted. *)

      (* Lemma dmut_wp_fresh_demonic {Γ Σ A x τ} *)
      (*       (d__d : Lit τ -> DynamicMutator Γ Γ A Σ) *)
      (*       (d__f : DynamicMutator Γ Γ A (Σ ▻ (x,τ))%ctx) : *)
      (*   (forall v POST s, *)
      (*       dmut_wp (d__d v) POST s <-> *)
      (*       dmut_wp *)
      (*         (dmut_sub (env_snoc (sub_id Σ) (x,τ) (term_lit τ v)) d__f) POST s) -> *)
      (*   (forall *)
      (*       (POST : forall Σ', Sub Σ Σ' -> A Σ' -> SymbolicState Γ Σ' -> Prop) *)
      (*       (s : SymbolicState Γ Σ), *)
      (*       dmut_wp (dmut_fresh (x,τ) d__f) POST s <-> *)
      (*       dmut_wp (dmut_demonic d__d) POST s). *)
      (* Proof. *)
      (*   intros; split; intro HYP. *)
      (*   - apply dmut_wp_demonic. intros. *)
      (*     apply H. clear H. revert HYP. clear. *)
      (*     unfold dmut_wp, dmut_fresh, dmut_sub; cbn; intros. *)
      (*     specialize (HYP Σ1 ζ1). *)
      (*     rewrite outcome_satisfy_map in HYP. *)
      (* Admitted. *)


      Lemma dmut_fresh_sound {Γ Σ ς τ} (ι : SymInstance Σ)
            (dm : DynamicMutator Γ Γ Unit (Σ ▻ (ς,τ))) (wfdm : dmut_wf dm)
            (sm : Lit τ -> SCMut Γ Γ unit) :
        (forall v, approximates (env_snoc ι _ v) dm (sm v)) ->
        approximates ι
          (dmut_fresh (ς,τ) dm)
          (scmut_demonic sm).
      Proof.
        intros HYP.
        unfold approximates; cbn.
        intros ? ? ? H__state H.
        apply scmut_wp_demonic. intros v.
        apply (HYP v (wk1_symbolicstate s__sym) s__sc POST).
        - revert H__state. clear.
          destruct s__sym, s__sc; unfold represents; cbn.
          intros; destruct_conjs; repeat split.
          + rewrite <- H. clear.
            unfold subst, SubstList.
            rewrite List.map_map.
            apply List.map_ext.
            intros.
            admit.
          + rewrite <- H0. clear.
            unfold subst, subst_localstore, SubstEnv.
            rewrite env_map_map.
            apply env_map_ext.
            intros [] ?; cbn in *.
            admit.
          + revert H1; clear.
            unfold subst, SubstList.
            match goal with
            | |- context[List.map ?f ?l] =>
              change (List.map f l) with (base.fmap f l)
            end.
            rewrite list.foldr_fmap.
            admit.
        - (* unfold dmut_wp, dmut_fresh in *. *)
          (* intros ? ?. *)
          (* dependent elimination ζ1 as [@env_snoc Σ ζ1 _ v]. cbn in v. *)
          (* specialize (H Σ1 ζ1). *)
          (* rewrite outcome_satisfy_map in H. *)
          apply (@dmut_wp_fresh Γ Σ Unit ς τ SubstUnit) in H.
          + admit.
          + unfold dmut_pred_monotonic; intros. destruct a1; cbn.
            revert H__state H1 H2. clear. intros.
            assert (exists ι2, syminstance_rel ζ1 ι ι2) as [ι2 Hι2] by admit.
            apply (represents_rel Hι2) in H__state.
            apply (H1 ι2 s__sc1 Hι2).
            admit.
          + exact wfdm.
      Admitted.

      Lemma dmut_produce_sound {Γ Σ} (asn : Assertion Σ) (ι : SymInstance Σ) :
        approximates
          (Γ1 := Γ) (Γ2 := Γ) ι
          (dmut_produce asn)
          (scmut_produce ι asn).
      Proof.
        induction asn; cbn.
        - apply dmut_assume_term_sound.
        - admit. (* Not implemented in SC. OOPS *)
        - apply dmut_produce_chunk_sound.
        - enough
            (approximates  (Γ1 := Γ) (Γ2 := Γ) ι
               (dmut_demonic_binary
                  (dmut_bind_right (dmut_assume_term b)            (dmut_produce asn1))
                  (dmut_bind_right (dmut_assume_term (term_not b)) (dmut_produce asn2)))
               (scmut_demonic_binary
                  (scmut_bind_right (scmut_assume_term ι b)            (scmut_produce ι asn1))
                  (scmut_bind_right (scmut_assume_term ι (term_not b)) (scmut_produce ι asn2)))) by admit.
          apply approximates_demonic_binary.
          + admit.
          + admit.
        - admit.
        - admit.
        - apply dmut_fresh_sound.
          + admit.
          + intros. apply IHasn.
      Admitted.

      Opaque dmut_wp.
      Opaque scmut_wp.

      Context `{HL: IHeaplet L} {SLL: ISepLogicLaws L}.

      Definition inst_heap {Σ} (ι : SymInstance Σ) (h : SymbolicHeap Σ) : L :=
        List.fold_right (fun c h => ASS.inst_chunk ι c ∧ h) ltrue h.

      (*   Definition rhoI {Γ Σ0} (ι0 : SymInstance Σ0) (s__sym : SymbolicState Γ Σ0) : *)
      (*     Outcome (SCMutResult Γ { Σ : Ctx (𝑺 * Ty) & Sub Σ0 Σ * SymInstance Σ }%type) := *)
      (*     ⨂ (Σ1 : Ctx (𝑺 * Ty)) *)
      (*       (ζ1 : Sub Σ0 Σ1) *)
      (*       (ι1 : SymInstance Σ1) *)
      (*       (s__sc : SCState Γ) *)
      (*       (_ : syminstance_rel ζ1 ι0 ι1) *)
      (*       (_ : represents ι1 (subst ζ1 s__sym) s__sc) => *)
      (*     outcome_pure *)
      (*       {| scmutres_value := existT Σ1 (ζ1,ι1); *)
      (*          scmutres_state := s__sc *)
      (*       |}. *)
      (* End Bla. *)

      (* Definition approximates {Γ1 Γ2 Σ} (ι : SymInstance Σ) (dm : DynamicMutator Γ1 Γ2 Unit Σ) (sm : SCMut Γ1 Γ2 unit) : Prop. *)
      (* Proof. *)
      (*   refine ( *)
      (*   forall s__sym : SymbolicState Γ1 Σ, *)
      (*     outcome_cover *)
      (*       (outcome_bind (dm Σ (sub_id _) s__sym) _) *)
      (*       (outcome_bind (rhoI ι s__sym) (fun r__sc => sm (scmutres_state r__sc))) *)
      (*     ). *)
      (*   intros [Σ1 ζ1 [_ s__sym' x]]. *)
      (*   eapply outcome_bind. *)
      (*   eapply (rhoI ι). *)
      (*   admit. *)
      (*   intros [? s__sc']. *)
      (*   apply outcome_pure. *)
      (*   constructor. *)
      (*   constructor. *)
      (*   apply s__sc'. *)
      (*   Show Proof. *)

      Ltac sauto :=
        repeat
          match goal with
          | [ |- ?P ⊢ ?P ] =>
            apply entails_refl
          | [ |- ?P ∧ _ ⊢ ?P ∧ _ ] =>
            apply land_right; [ apply land_left1, entails_refl | idtac ]
          | [ |- _ ⊢ _ ∧ !!(?x = ?x) ] =>
            apply land_right; [ idtac | apply lprop_right; reflexivity ]
          | [ |- !! _ ⊢ _ ] =>
            apply lprop_right; intro
          | [ H: ?P |- _ ⊢ !!?P ] =>
            apply lprop_right; exact H
          end.

      Local Ltac sound_inster :=
        match goal with
        | [ IH: outcome_satisfy (dmut_exec ?s _ _) |-
            outcome_satisfy (dmut_exec ?s _ _) _ ] =>
          refine (outcome_satisfy_monotonic _ _ IH); clear IH
        | [ IH: context[_ -> outcome_satisfy (dmut_exec ?s _ _) _] |-
            outcome_satisfy (dmut_exec ?s _ _) _ ] =>
          microsail_insterU (fail) IH; refine (outcome_satisfy_monotonic _ _ IH); clear IH
        end.

      Lemma subst_lookup {Γ Σ Σ' x σ} (xInΓ : (x ∶ σ)%ctx ∈ Γ) (ζ : Sub Σ Σ') (δ : SymbolicLocalStore Γ Σ) :
        (subst ζ (δ ‼ x)%exp = (subst ζ δ ‼ x)%exp).
      Proof.
        unfold subst at 2, subst_localstore, SubstEnv.
        now rewrite env_lookup_map.
      Qed.

      Lemma subst_symboliceval {Γ τ Σ Σ'} (e : Exp Γ τ) (ζ : Sub Σ Σ') (δ : SymbolicLocalStore Γ Σ) :
        subst (T := fun Σ => Term Σ _) ζ (symbolic_eval_exp δ e) = symbolic_eval_exp (subst ζ δ) e.
      Proof.
        induction e; cbn; f_equal; auto.
        { now rewrite (subst_lookup xInΓ). }
        all: induction es; cbn in *; destruct_conjs; f_equal; auto.
      Qed.

      Lemma eval_exp_inst {Γ Σ τ} (ι : SymInstance Σ) (δΓΣ : SymbolicLocalStore Γ Σ) (e : Exp Γ τ) :
        eval e (inst_localstore ι δΓΣ) = inst_term ι (symbolic_eval_exp δΓΣ e).
      Proof.
        induction e; cbn; repeat f_equal; auto.
        { unfold inst_localstore; now rewrite env_lookup_map. }
        2: {
          induction es as [|eb n es IHes]; cbn in *.
          { reflexivity. }
          { destruct X as [-> Heqs].
            destruct (inst_term ι (symbolic_eval_exp δΓΣ eb));
              cbn; f_equal; auto.
          }
        }
        all: induction es; cbn in *; destruct_conjs; f_equal; auto.
      Qed.

      Local Opaque inst_heap.

      Opaque env_tail.

      Notation "'dmutres_pathcondition' res" := (symbolicstate_pathcondition (mutator_result_state (dmutres_result res))) (at level 10).
      Notation "'dmutres_heap' res" := (symbolicstate_heap (mutator_result_state (dmutres_result res))) (at level 10).
      Notation "'dmutres_localstore' res" := (symbolicstate_localstore (mutator_result_state (dmutres_result res))) (at level 10).

      Lemma dmut_exec_sound {Γ σ} (POST : Lit σ -> LocalStore Γ -> L) (s : Stm Γ σ) :
        forall Σ0 Σ1  (ι : SymInstance Σ1) (ζ1 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (δ1 : SymbolicLocalStore Γ Σ1) (h1 : SymbolicHeap Σ1),
          let δ       := inst_localstore ι δ1 in
          let pre__pc   := inst_pathcondition ι pc1 in
          let pre__heap := inst_heap ι h1 in
          outcome_satisfy
            (dmut_exec s ζ1 (MkSymbolicState pc1 δ1 h1))
            (fun '(@MkDynMutResult _ _ _ Σ2 ζ2 (MkMutResult t (MkSymbolicState pc2 δ2 h2) x)) =>
               forall (ι' : SymInstance Σ2),
                 ι = env_map (fun _ => inst_term ι') ζ2 ->
                 let post__pc   := inst_pathcondition ι' pc2 in
                 let post__heap := inst_heap ι' h2 in
                 !! post__pc ∧ post__heap ⊢ POST (inst_term ι' t) (inst_localstore ι' δ2)) ->
          pre__pc ->
          outcome_satisfy
            (scmut_exec s (MkSCState δ (semiconcretize_heap ι h1)))
            (fun '(MkSCMutResult v2 (MkSCState δ2 h2)) =>
               SCMUT.inst_scheap h2 ⊢ POST v2 δ2).
      Proof.
        intros ? ? ? ? ? ? ?; cbn.
        revert pc1 h1.
        induction s.

        - cbn. intros.
          assert (ι = env_map (fun b : 𝑺 * Ty => inst_term ι) (sub_id Σ1)) as Heqι by admit.
          specialize (H ι Heqι); clear Heqι.
          refine (entails_trans _ _ _ _ H).
          apply land_right.
          + now apply lprop_right.
          + admit.

        - cbn. intros.
          assert (ι = env_map (fun b : 𝑺 * Ty => inst_term ι) (sub_id Σ1)) as Heqι by admit.
          specialize (H ι Heqι); clear Heqι.
          rewrite eval_exp_inst.
          refine (entails_trans _ _ _ _ H).
          apply land_right.
          + now apply lprop_right.
          + admit.

        - repeat (unfold dmut_bind_right, dmut_sub, dmut_bind, scmut_bind,
                  scmut_bind_left; cbn).
          repeat
            (repeat setoid_rewrite outcome_satisfy_bind;
             repeat setoid_rewrite outcome_satisfy_map; cbn).
          intros.

      Admitted.

      Lemma dmut_contract_sound {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
        ValidContractDynMut c body ->
        ValidContract c body.
      Proof.
      Admitted.

    End WithSemantics.

  End DynMutV1Soundness.

End Soundness.
