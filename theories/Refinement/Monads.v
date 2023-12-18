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
     Classes.Morphisms.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Prelude
     Base
     Shallow.Monads
     Symbolic.Monads
     Symbolic.Propositions
     Symbolic.Solver
     Symbolic.Worlds
     Syntax.Chunks
     Syntax.Formulas
     Syntax.Predicates.

Import ctx.notations.
Import env.notations.

Set Implicit Arguments.

Module Type RefinementMonadsOn
  (Import B : Base)
  (Import PK : PredicateKit B)
  (Import WR : WorldsMixin B PK)
  (Import SK : SolverKit B PK WR)
  (Import SP : SymPropOn B PK WR)
  (Import GS : GenericSolverOn B PK WR SK)
  (Import SHAL : ShallowMonadsOn B PK WR)
  (Import SYMB : SymbolicMonadsOn B PK WR SK SP GS).

  Import ModalNotations logicalrelation logicalrelation.notations.

  #[export] Instance RPureSpec [SA CA] (RA : Rel SA CA) :
    Rel (SPureSpec SA) (CPureSpec CA) := □(RA -> ℙ) -> ℙ.

  #[local] Ltac rsolve :=
    repeat
      match goal with
      | |- RValid _ (fun w => _) _ => intros ?w ?ι ?Hpc
      | |- RValid (RMsg _ _) _ _ => intros ?w ?ι ?Hpc ?msg
      | |- RSat (RImpl _ _) _ (fun x => _) (fun y => _) => intros ?t ?v ?Htv
      | |- RSat (RMsg _ _) ?ι _ _ => intros ?msg
      | |- RSat _ _ (T _) _ => apply refine_T
      | |- RSat (RBox _) _ (fun w r => _) _ => intros ?w ?r ?ι ?Hι ?Hpc
      | Hι: _ = inst (sub_acc ?r) ?ι |- RSat (RBox _) ?ι (four _ ?r) _ =>
          apply (refine_four r Hι)
      end; auto.

  Module RPureSpec.

    Lemma refine_run :
      ℛ⟦RPureSpec RUnit -> ℙ⟧ SPureSpec.run CPureSpec.run.
    Proof.
      unfold SPureSpec.run, CPureSpec.run.
      intros w ι Hpc ms mc Hm. now apply Hm.
    Qed.

    Lemma refine_pure `{RA : Rel SA CA} :
      ℛ⟦RA -> RPureSpec RA⟧ SPureSpec.pure CPureSpec.pure.
    Proof.
      unfold RPureSpec, SPureSpec.pure, CPureSpec.pure.
      rsolve. eapply refine_apply; rsolve.
    Qed.

    Lemma refine_bind `{RA : Rel SA CA, RB : Rel SB CB} :
      ℛ⟦RPureSpec RA -> □(RA -> RPureSpec RB) -> RPureSpec RB⟧
        SPureSpec.bind CPureSpec.bind.
    Proof.
      unfold RPureSpec, SPureSpec.bind, CPureSpec.bind.
      intros. rsolve. do 3 (eapply refine_apply; rsolve).
    Qed.

    Lemma refine_block `{R : Rel AT A} :
      ℛ⟦RPureSpec R⟧ (@SPureSpec.block AT) CPureSpec.block.
    Proof. constructor. Qed.

    Lemma refine_error `{RA : Rel AT A} m :
      ℛ⟦RMsg _ (RPureSpec RA)⟧ (@SPureSpec.error _) m.
    Proof. intros w ι Hpc msg sΦ cΦ rΦ. inversion 1. Qed.

    Lemma refine_angelic (x : option LVar) :
      ℛ⟦∀ σ, RPureSpec (RVal σ)⟧ (SPureSpec.angelic x) CPureSpec.angelic.
    Proof.
      intros w0 ι0 Hpc0 σ sΦ cΦ rΦ.
      intros [v HΦ]. exists v. revert HΦ.
      apply rΦ; cbn; eauto.
      - now rewrite inst_sub_wk1.
      - now rewrite instprop_subst, inst_sub_wk1.
    Qed.

    Lemma refine_demonic (x : option LVar) :
      ℛ⟦∀ σ, RPureSpec (RVal σ)⟧ (SPureSpec.demonic x) CPureSpec.demonic.
    Proof.
      intros w0 ι0 Hpc0 σ sΦ cΦ rΦ.
      intros HΦ v. cbn in HΦ. specialize (HΦ v).
      remember (fresh_lvar w0 x) as ℓ.
      revert HΦ. apply rΦ;
        [ (* Boilerplate #1 *) cbn; now rewrite inst_sub_wk1
        | (* Boilerplate #2 *) cbn; now rewrite instprop_subst, inst_sub_wk1
        | ].
      reflexivity.
    Qed.

    Lemma refine_angelic_ctx {N : Set} {n : N -> LVar} :
      ℛ⟦∀ Δ, RPureSpec (RNEnv Δ)⟧
        (SPureSpec.angelic_ctx n) CPureSpec.angelic_ctx.
    Proof.
      intros w ι Hpc Δ; revert w ι Hpc; induction Δ as [|Δ IHΔ [x σ]];
        intros w0 ι0 Hpc0; cbn [SPureSpec.angelic_ctx CPureSpec.angelic_ctx].
      - now apply refine_pure.
      - apply refine_bind; auto.
        intros w1 ω01 ι1 Hι1 Hpc1.
        intros svs cvs rvs.
        eapply refine_bind; auto.
        apply refine_angelic; auto.
        intros w2 ω12 ι2 Hι2 Hpc2.
        intros sv cv rv.
        apply refine_pure; auto.
        apply refine_env_snoc; auto.
        eapply refine_inst_persist; eauto.
    Qed.

    Lemma refine_demonic_ctx {N : Set} {n : N -> LVar} :
      ℛ⟦∀ Δ : NCtx N Ty, RPureSpec (RNEnv Δ)⟧
        (SPureSpec.demonic_ctx n) CPureSpec.demonic_ctx.
    Proof.
      intros w ι Hpc Δ; revert w ι Hpc; induction Δ as [|Δ IHΔ [x σ]];
        intros w0 ι0 Hpc0; cbn [SPureSpec.demonic_ctx CPureSpec.demonic_ctx].
      - now apply refine_pure.
      - eapply refine_bind; auto.
        intros w1 ω01 ι1 Hι1 Hpc1.
        intros svs cvs rvs.
        eapply refine_bind; auto.
        apply refine_demonic; auto.
        intros w2 ω12 ι2 Hι2 Hpc2.
        intros sv cv rv.
        apply refine_pure; auto.
        apply refine_env_snoc; auto.
        eapply refine_inst_persist; eauto.
    Qed.

    Lemma refine_assert_pathcondition :
      ℛ⟦RMsg _ (RPathCondition -> RPureSpec RUnit)⟧
        SPureSpec.assert_pathcondition CPureSpec.assert_formula.
    Proof.
      unfold SPureSpec.assert_pathcondition, CPureSpec.assert_formula.
      intros w0 ι0 Hpc0 msg sC cC rC sΦ cΦ rΦ HΦ.
      destruct (combined_solver_spec _ sC) as [[w1 [ζ sc1]] Hsolver|Hsolver].
      - specialize (Hsolver ι0 Hpc0). destruct Hsolver as [_ Hsolver].
        rewrite SymProp.safe_assert_triangular in HΦ. destruct HΦ as [Hν HΦ].
        rewrite SymProp.safe_assert_pathcondition_without_solver in HΦ.
        destruct HΦ as [HC HΦ].
        split.
        + apply Hsolver in HC; rewrite ?inst_triangular_right_inverse; auto.
          now apply rC.
          now apply entails_triangular_inv.
        + revert HΦ. unfold four.
          apply rΦ; cbn; wsimpl; eauto.
          unfold PathCondition. rewrite instprop_cat. split; auto.
          now apply entails_triangular_inv.
      - contradict HΦ.
    Qed.

    Lemma refine_assume_pathcondition :
      ℛ⟦RPathCondition -> RPureSpec RUnit⟧
        SPureSpec.assume_pathcondition CPureSpec.assume_formula.
    Proof.
      unfold SPureSpec.assume_pathcondition, CPureSpec.assume_formula.
      intros w0 ι0 Hpc0 sC cC rC sΦ cΦ rΦ HΦ HC. apply rC in HC.
      destruct (combined_solver_spec _ sC) as [[w1 [ζ sc1]] Hsolver|Hsolver].
      - specialize (Hsolver ι0 Hpc0).
        destruct Hsolver as [Hν Hsolver]. inster Hν by auto.
        specialize (Hsolver (inst (sub_triangular_inv ζ) ι0)).
        rewrite inst_triangular_right_inverse in Hsolver; auto.
        inster Hsolver by now try apply entails_triangular_inv.
        destruct Hsolver as [Hsolver _]. inster Hsolver by auto.
        rewrite SymProp.safe_assume_triangular,
          SymProp.safe_assume_pathcondition_without_solver in HΦ.
        specialize (HΦ Hν Hsolver). revert HΦ.
        unfold four. apply rΦ; cbn; wsimpl; auto.
        unfold PathCondition. rewrite instprop_cat. split; auto.
        now apply entails_triangular_inv.
      - now apply Hsolver in HC.
    Qed.

    Lemma refine_assert_formula :
      ℛ⟦RMsg _ (RFormula -> RPureSpec RUnit)⟧
        SPureSpec.assert_formula CPureSpec.assert_formula.
    Proof.
      unfold RPureSpec, SPureSpec.assert_formula, CPureSpec.assert_formula.
      rsolve. apply refine_assert_pathcondition; auto. cbn in *. intuition auto.
    Qed.

    Lemma refine_assume_formula :
      ℛ⟦RFormula -> RPureSpec RUnit⟧
        SPureSpec.assume_formula CPureSpec.assume_formula.
    Proof.
      unfold RPureSpec, SPureSpec.assume_formula, CPureSpec.assume_formula.
      rsolve. apply refine_assume_pathcondition; cbn in *; intuition auto.
    Qed.

    Lemma refine_angelic_binary `{RA : Rel SA CA} :
      ℛ⟦RPureSpec RA -> RPureSpec RA -> RPureSpec RA⟧
          SPureSpec.angelic_binary CPureSpec.angelic_binary.
    Proof.
      unfold RPureSpec, SPureSpec.angelic_binary, CPureSpec.angelic_binary.
      rsolve. apply refine_symprop_angelic_binary; rsolve.
    Qed.

    Lemma refine_demonic_binary `{RA : Rel SA CA} :
      ℛ⟦RPureSpec RA -> RPureSpec RA -> RPureSpec RA⟧
          SPureSpec.demonic_binary CPureSpec.demonic_binary.
    Proof.
      unfold RPureSpec, SPureSpec.demonic_binary, CPureSpec.demonic_binary.
      rsolve. apply refine_symprop_demonic_binary; rsolve.
    Qed.

    Lemma refine_angelic_list' `{RA : Rel SA CA} :
      ℛ⟦RA -> RList RA -> RPureSpec RA⟧
        SPureSpec.angelic_list' CPureSpec.angelic_list'.
    Proof.
      intros w ι Hpc sv cv rv svs cvs rvs. revert sv cv rv.
      induction rvs; cbn [SPureSpec.angelic_list' CPureSpec.angelic_list'].
      - now apply refine_pure.
      - intros sv cv rv. apply refine_angelic_binary; auto.
        now apply refine_pure.
    Qed.

    Lemma refine_angelic_list `{RA : Rel SA CA} :
      ℛ⟦RMsg _ (RList RA -> RPureSpec RA)⟧
        SPureSpec.angelic_list CPureSpec.angelic_list.
    Proof.
      intros w ι Hpc msg sv cv [].
      - now apply refine_error.
      - now apply refine_angelic_list'.
    Qed.

    Lemma refine_demonic_list' `{RA : Rel SA CA} :
      ℛ⟦RA -> RList RA -> RPureSpec RA⟧
        SPureSpec.demonic_list' CPureSpec.demonic_list'.
    Proof.
      intros w ι Hpc sv cv rv svs cvs rvs. revert sv cv rv.
      induction rvs; cbn [SPureSpec.demonic_list' CPureSpec.demonic_list'].
      - now apply refine_pure.
      - intros sv cv rv. apply refine_demonic_binary; auto. now apply refine_pure.
    Qed.

    Lemma refine_demonic_list `{RA : Rel SA CA} :
      ℛ⟦RList RA -> RPureSpec RA⟧
        SPureSpec.demonic_list CPureSpec.demonic_list.
    Proof.
      intros w ι Hpc sv cv [].
      - now apply refine_block.
      - now apply refine_demonic_list'.
    Qed.

    Lemma refine_angelic_finite {F} `{finite.Finite F} :
      ℛ⟦RMsg _ (RPureSpec (RConst F))⟧
        (@SPureSpec.angelic_finite F _ _) (CPureSpec.angelic_finite F).
    Proof.
      intros w ι Hpc msg. apply refine_angelic_list; auto.
      induction (finite.enum F); now constructor.
    Qed.

    Lemma refine_demonic_finite {F} `{finite.Finite F} :
      ℛ⟦RPureSpec (RConst F)⟧
        (@SPureSpec.demonic_finite F _ _) (CPureSpec.demonic_finite F).
    Proof.
      intros w ι Hpc. apply refine_demonic_list; auto.
      induction (finite.enum F); now constructor.
    Qed.

    Lemma refine_angelic_pattern_match' {N : Set} (n : N -> LVar)
      {σ} (pat : @Pattern N σ) :
      ℛ⟦RMsg _ (RVal σ -> RPureSpec (RMatchResult pat))⟧
        (SPureSpec.angelic_pattern_match' n pat)
        (CPureSpec.angelic_pattern_match pat).
    Proof.
      intros w ι Hpc msg t v ->.
      unfold SPureSpec.angelic_pattern_match'.
      unfold CPureSpec.angelic_pattern_match.
      apply refine_bind; auto.
      { now apply refine_angelic_finite. }
      intros w1 r01 ι1 Hι1 Hpc1.
      intros pc ? ->.
      apply refine_bind; auto.
      { now apply refine_angelic_ctx. }
      intros w2 r12 ι2 Hι2 Hpc2.
      intros ts vs Htvs.
      apply refine_bind; auto.
      { apply refine_assert_formula; try assumption. cbn.
        rewrite (inst_persist (AT := fun Σ => Term Σ _)).
        rewrite !sub_acc_trans, inst_subst.
        rewrite inst_pattern_match_term_reverse.
        hnf in Htvs. subst. reflexivity.
      }
      intros w3 r23 ι3 Hι3 Hpc3 _ _ _.
      apply refine_pure; auto.
      exists eq_refl. eapply refine_inst_persist; eauto.
    Qed.
    #[global] Arguments refine_angelic_pattern_match' {N} n {σ} pat.

    Lemma refine_demonic_pattern_match' {N : Set} (n : N -> LVar)
      {σ} (pat : @Pattern N σ) :
      ℛ⟦RVal σ -> RPureSpec (RMatchResult pat)⟧
        (SPureSpec.demonic_pattern_match' n pat)
        (CPureSpec.demonic_pattern_match pat).
    Proof.
      intros w ι Hpc t v ->.
      unfold SPureSpec.demonic_pattern_match'.
      unfold CPureSpec.demonic_pattern_match.
      apply refine_bind; auto.
      { now apply refine_demonic_finite. }
      intros w1 r01 ι1 Hι1 Hpc1.
      intros pc ? ->.
      apply refine_bind; auto.
      { now apply refine_demonic_ctx. }
      intros w2 r12 ι2 Hι2 Hpc2.
      intros ts vs Htvs.
      apply refine_bind; auto.
      { apply refine_assume_formula; try assumption. cbn.
        rewrite (inst_persist (AT := fun Σ => Term Σ _)).
        rewrite !sub_acc_trans, inst_subst.
        rewrite inst_pattern_match_term_reverse.
        hnf in Htvs. subst. reflexivity.
      }
      intros w3 r23 ι3 Hι3 Hpc3 _ _ _.
      apply refine_pure; auto.
      exists eq_refl. eapply refine_inst_persist; eauto.
    Qed.
    #[global] Arguments refine_demonic_pattern_match' {N} n {σ} pat.

    Lemma refine_angelic_pattern_match {N : Set} (n : N -> LVar)
      {σ} (pat : @Pattern N σ) :
      ℛ⟦RMsg _ (RVal σ -> RPureSpec (RMatchResult pat))⟧
        (SPureSpec.angelic_pattern_match n pat)
        (CPureSpec.angelic_pattern_match pat).
    Proof.
      induction pat; cbn - [Val]; intros w ι Hpc.
      - intros msg sv cv -> sΦ cΦ rΦ. hnf.
        rewrite CPureSpec.wp_angelic_pattern_match.
        apply rΦ; cbn; rewrite ?inst_sub_id; auto.
        now exists eq_refl.
      - intros msg sv cv ->.
        destruct (term_get_val_spec sv); subst.
        + intros sΦ cΦ rΦ. hnf.
          rewrite CPureSpec.wp_angelic_pattern_match; cbn.
          apply rΦ; cbn; rewrite ?inst_sub_id; auto.
          now exists eq_refl.
        + now apply (refine_angelic_pattern_match' n pat_bool).
      - apply (refine_angelic_pattern_match' n (pat_list σ x y)); auto.
      - intros msg sv cv ->.
        destruct (term_get_pair_spec sv) as [[svl svr] Heq|]; subst.
        + rewrite Heq. intros sΦ cΦ rΦ. hnf.
          rewrite CPureSpec.wp_angelic_pattern_match. cbn.
          apply rΦ; cbn; rewrite ?inst_sub_id; auto.
          now exists eq_refl.
        + now apply (refine_angelic_pattern_match' n (pat_pair _ _)); auto.
      - intros msg sv cv ->.
        destruct (term_get_sum_spec sv) as [[svl|svr] Heq|]; subst.
        + rewrite Heq. intros sΦ cΦ rΦ. hnf.
          rewrite CPureSpec.wp_angelic_pattern_match. cbn.
          apply rΦ; cbn; rewrite ?inst_sub_id; auto.
          now exists eq_refl.
        + rewrite Heq. intros sΦ cΦ rΦ. hnf.
          rewrite CPureSpec.wp_angelic_pattern_match. cbn.
          apply rΦ; cbn; rewrite ?inst_sub_id; auto.
          now exists eq_refl.
        + now apply (refine_angelic_pattern_match' n (pat_sum _ _ _ _)); auto.
      - intros msg sv cv -> sΦ cΦ rΦ. hnf.
        rewrite CPureSpec.wp_angelic_pattern_match.
        apply rΦ; cbn; rewrite ?inst_sub_id; auto.
        now exists eq_refl.
      - intros msg sv cv ->.
        destruct (term_get_val_spec sv); subst.
        + intros sΦ cΦ rΦ. hnf.
          rewrite CPureSpec.wp_angelic_pattern_match. cbn.
          apply rΦ; cbn; rewrite ?inst_sub_id; auto.
          now exists eq_refl.
        + now apply (refine_angelic_pattern_match' n (pat_enum E)); auto.
      - apply (refine_angelic_pattern_match' n (pat_bvec_split _ _ x y)); auto.
      - intros msg sv cv ->.
        destruct (term_get_val_spec sv); subst.
        + intros sΦ cΦ rΦ. hnf.
          rewrite CPureSpec.wp_angelic_pattern_match. cbn.
          apply rΦ; cbn; rewrite ?inst_sub_id; auto.
          now exists eq_refl.
        + now apply (refine_angelic_pattern_match' n (pat_bvec_exhaustive m)); auto.
      - apply (refine_angelic_pattern_match' n (pat_tuple p)); auto.
      - intros msg sv cv ->.
        destruct (term_get_record_spec sv) as [svs Heq|]; subst.
        + rewrite Heq. intros sΦ cΦ rΦ. hnf.
          rewrite CPureSpec.wp_angelic_pattern_match. cbn.
          apply rΦ; cbn; rewrite ?inst_sub_id; auto.
          exists eq_refl. cbn.
          unfold record_pattern_match_val.
          rewrite recordv_unfold_fold.
          symmetry. apply inst_record_pattern_match.
        + now apply (refine_angelic_pattern_match' n (pat_record _ _ _)); auto.
      - intros msg sv cv ->.
        destruct (term_get_union_spec sv) as [[K scr'] Heq|]; subst.
        + rewrite Heq. intros sΦ cΦ rΦ. hnf.
          specialize (H K w ι Hpc msg scr' (inst scr' ι) eq_refl).
          intros Hwp. eapply H in Hwp; eauto. revert Hwp. cbn.
          Unshelve.
          3: {
            intros [pc δpc]. apply cΦ. now exists (existT K pc).
          }
          * rewrite ?CPureSpec.wp_angelic_pattern_match. cbn.
            rewrite unionv_unfold_fold.
            now destruct pattern_match_val; cbn.
          * intros ? ? ? ? ? [] [] [e Hmr]. apply rΦ; auto.
            rewrite H0. rewrite sub_acc_trans; cbn.
            now rewrite inst_subst, inst_sub_id.
            subst. now exists eq_refl.
        + now apply (refine_angelic_pattern_match' n (pat_union _ _)); auto.
    Qed.
    #[global] Arguments refine_angelic_pattern_match' {N} n {σ} pat.

    Lemma refine_demonic_pattern_match {N : Set} (n : N -> LVar)
      {σ} (pat : @Pattern N σ) :
      ℛ⟦RVal σ -> RPureSpec (RMatchResult pat)⟧
        (SPureSpec.demonic_pattern_match n pat)
        (CPureSpec.demonic_pattern_match pat).
    Proof.
      induction pat; cbn - [Val]; intros w ι Hpc.
      - intros sv cv -> sΦ cΦ rΦ. hnf.
        rewrite CPureSpec.wp_demonic_pattern_match.
        apply rΦ; cbn; rewrite ?inst_sub_id; auto.
        now exists eq_refl.
      - intros sv cv ->.
        destruct (term_get_val_spec sv); subst.
        + intros sΦ cΦ rΦ. hnf.
          rewrite CPureSpec.wp_demonic_pattern_match; cbn.
          apply rΦ; cbn; rewrite ?inst_sub_id; auto.
          now exists eq_refl.
        + now apply (refine_demonic_pattern_match' n pat_bool).
      - apply (refine_demonic_pattern_match' n (pat_list σ x y)); auto.
      - intros sv cv ->.
        destruct (term_get_pair_spec sv) as [[svl svr] Heq|]; subst.
        + rewrite Heq. intros sΦ cΦ rΦ. hnf.
          rewrite CPureSpec.wp_demonic_pattern_match. cbn.
          apply rΦ; cbn; rewrite ?inst_sub_id; auto.
          now exists eq_refl.
        + now apply (refine_demonic_pattern_match' n (pat_pair _ _)); auto.
      - intros sv cv ->.
        destruct (term_get_sum_spec sv) as [[svl|svr] Heq|]; subst.
        + rewrite Heq. intros sΦ cΦ rΦ. hnf.
          rewrite CPureSpec.wp_demonic_pattern_match. cbn.
          apply rΦ; cbn; rewrite ?inst_sub_id; auto.
          now exists eq_refl.
        + rewrite Heq. intros sΦ cΦ rΦ. hnf.
          rewrite CPureSpec.wp_demonic_pattern_match. cbn.
          apply rΦ; cbn; rewrite ?inst_sub_id; auto.
          now exists eq_refl.
        + now apply (refine_demonic_pattern_match' n (pat_sum _ _ _ _)); auto.
      - intros sv cv -> sΦ cΦ rΦ. hnf.
        rewrite CPureSpec.wp_demonic_pattern_match.
        apply rΦ; cbn; rewrite ?inst_sub_id; auto.
        now exists eq_refl.
      - intros sv cv ->.
        destruct (term_get_val_spec sv); subst.
        + intros sΦ cΦ rΦ. hnf.
          rewrite CPureSpec.wp_demonic_pattern_match. cbn.
          apply rΦ; cbn; rewrite ?inst_sub_id; auto.
          now exists eq_refl.
        + now apply (refine_demonic_pattern_match' n (pat_enum E)); auto.
      - apply (refine_demonic_pattern_match' n (pat_bvec_split _ _ x y)); auto.
      - intros sv cv ->.
        destruct (term_get_val_spec sv); subst.
        + intros sΦ cΦ rΦ. hnf.
          rewrite CPureSpec.wp_demonic_pattern_match. cbn.
          apply rΦ; cbn; rewrite ?inst_sub_id; auto.
          now exists eq_refl.
        + now apply (refine_demonic_pattern_match' n (pat_bvec_exhaustive m)); auto.
      - apply (refine_demonic_pattern_match' n (pat_tuple p)); auto.
      - intros sv cv ->.
        destruct (term_get_record_spec sv) as [svs Heq|]; subst.
        + rewrite Heq. intros sΦ cΦ rΦ. hnf.
          rewrite CPureSpec.wp_demonic_pattern_match. cbn.
          apply rΦ; cbn; rewrite ?inst_sub_id; auto.
          exists eq_refl. cbn.
          unfold record_pattern_match_val.
          rewrite recordv_unfold_fold.
          symmetry. apply inst_record_pattern_match.
        + now apply (refine_demonic_pattern_match' n (pat_record _ _ _)); auto.
      - intros sv cv ->.
        destruct (term_get_union_spec sv) as [[K scr'] Heq|]; subst.
        + rewrite Heq. intros sΦ cΦ rΦ. hnf.
          specialize (H K w ι Hpc scr' (inst scr' ι) eq_refl).
          intros Hwp. eapply H in Hwp; eauto. revert Hwp. cbn.
          Unshelve.
          3: {
            intros [pc δpc]. apply cΦ. now exists (existT K pc).
          }
          * rewrite ?CPureSpec.wp_demonic_pattern_match. cbn.
            rewrite unionv_unfold_fold.
            now destruct pattern_match_val; cbn.
          * intros ? ? ? ? ? [] [] [e Hmr]. apply rΦ; auto.
            rewrite H0. rewrite sub_acc_trans; cbn.
            now rewrite inst_subst, inst_sub_id.
            subst. now exists eq_refl.
        + now apply (refine_demonic_pattern_match' n (pat_union _ _)); auto.
    Qed.
    #[global] Arguments refine_demonic_pattern_match' {N} n {σ} pat.

    Lemma refine_new_pattern_match_regular {N : Set} n σ (pat : @Pattern N σ) :
      ℛ⟦RVal σ -> RPureSpec (RMatchResult pat)⟧
        (SPureSpec.new_pattern_match_regular n pat)
        (CPureSpec.new_pattern_match pat).
    Proof.
      unfold SPureSpec.new_pattern_match_regular.
      intros w0 ι0 Hpc0 sv cv rv spost cpost rpost.
      unfold CPureSpec.new_pattern_match.
      rewrite <- (pattern_match_val_freshen n pat (Σ := w0)).
      pose proof (pattern_match_val_inverse_left (freshen_pattern n w0 pat) (inst sv ι0)).
      cbn in rv. subst. cbn.
      destruct pattern_match_val as [pc vs]. cbn in H. cbn - [acc_trans].
      unfold pattern_match_val_reverse' in H. cbn in H.
      apply rpost; cbn - [sub_cat_left sub_cat_right sub_id];
        rewrite ?inst_subst, ?instprop_subst, ?inst_sub_id, ?inst_sub_cat_left; try easy.
      - rewrite inst_pattern_match_term_reverse. split; auto. rewrite <- H.
        f_equal. symmetry. apply inst_sub_cat_right.
      - exists eq_refl. cbn. symmetry. etransitivity.
        apply inst_unfreshen_patterncaseenv. f_equal.
        apply inst_sub_cat_right.
    Qed.

    Lemma refine_pattern_match_var {N : Set} n {x σ} (pat : @Pattern N σ) :
      ℛ⟦RIn (x∷σ) -> RPureSpec (RMatchResult pat)⟧
        (SPureSpec.new_pattern_match_var n pat)
        (CPureSpec.new_pattern_match pat).
    Proof.
      intros w0 ι0 Hpc0 sv cv rv spost cpost rpost.
      unfold SPureSpec.new_pattern_match_var. hnf.
      intros Hsafe. hnf. cbn in rv. subst cv.
      rewrite <- (pattern_match_val_freshen n pat (Σ := w0)).
    Admitted.

    Lemma refine_new_pattern_match' {N : Set} n σ (pat : @Pattern N σ) :
      ℛ⟦RVal σ -> RPureSpec (RMatchResult pat)⟧
        (SPureSpec.new_pattern_match' n pat)
        (CPureSpec.new_pattern_match pat).
    Proof.
      unfold SPureSpec.new_pattern_match'.
      intros w0 ι0 Hpc0 sv cv rv.
      destruct sv. now apply refine_pattern_match_var.
      all: now apply refine_new_pattern_match_regular.
    Qed.

    Lemma refine_new_pattern_match {N : Set} n σ (pat : @Pattern N σ) :
      ℛ⟦RVal σ -> RPureSpec (RMatchResult pat)⟧ (SPureSpec.new_pattern_match n pat)
        (CPureSpec.new_pattern_match pat).
    Proof.
      induction pat; cbn [SPureSpec.new_pattern_match];
        intros w0 ι0 Hpc0 sv cv ->.
      - unfold CPureSpec.new_pattern_match.
        apply refine_pure; auto. now exists eq_refl.
      - destruct (term_get_val_spec sv) as [cv ?|].
        + apply refine_pure; auto. subst. now exists eq_refl.
        + now apply refine_new_pattern_match' with (pat := pat_bool).
      - now apply refine_new_pattern_match'.
      - destruct (term_get_pair_spec sv) as [[? ?] ->|].
        + apply refine_pure; auto. now exists eq_refl.
        + now apply refine_new_pattern_match' with (pat := pat_pair _ _).
      - destruct (term_get_sum_spec sv) as [[] ->|].
        + apply refine_pure; auto. now exists eq_refl.
        + apply refine_pure; auto. now exists eq_refl.
        + now apply refine_new_pattern_match' with (pat := pat_sum _ _ _ _).
      - apply refine_pure; auto. now exists eq_refl.
      - destruct (term_get_val_spec sv) as [? ->|].
        + apply refine_pure; auto. now exists eq_refl.
        + now apply refine_new_pattern_match' with (pat := pat_enum E).
      - now apply refine_new_pattern_match'.
      - destruct (term_get_val_spec sv) as [? ->|].
        + apply refine_pure; auto. now exists eq_refl.
        + now apply refine_new_pattern_match' with (pat := pat_bvec_exhaustive m).
      - destruct (term_get_tuple_spec sv) as [? ->|].
        + apply refine_pure; auto. exists eq_refl. cbn.
          unfold tuple_pattern_match_val.
          rewrite envrec.to_of_env. symmetry.
          apply inst_tuple_pattern_match.
        + now apply refine_new_pattern_match'.
      - destruct (term_get_record_spec sv) as [? ->|].
        + apply refine_pure; auto. exists eq_refl. cbn.
          unfold record_pattern_match_val.
          rewrite recordv_unfold_fold. symmetry.
          apply inst_record_pattern_match.
        + now apply refine_new_pattern_match'.
      - destruct (term_get_union_spec sv) as [[K tf] Heq|].
        + intros spost cpost rpost. cbn. intros Hsafe.
          specialize (H K w0 ι0 Hpc0 tf (inst tf ι0) eq_refl).
          rewrite Heq. hnf. cbn. rewrite unionv_unfold_fold.
          unfold CPureSpec.new_pattern_match in H.
          clear Heq.
          destruct (pattern_match_val (p K) (inst tf ι0)) as [pc δpc] eqn:?.
          eapply H in Hsafe; eauto.
          Unshelve.
          3: {
            intros mr. apply cpost.  cbn. destruct mr as [pc' δpc'].
            exists (existT K pc'). apply δpc'.
          }
          exact Hsafe.
          intros w1 θ1 ι1 Heq1 Hpc1 [spc sδ] [cpc cδ] [rpc rδ].
          subst. cbn in rδ. subst. cbn. cbv [SPureSpec.pure four T]. cbn.
          intros Hsafe'. eapply rpost; eauto. Unshelve.
          3: {
            exists (existT K cpc). apply sδ.
          }
          exists eq_refl; cbn. reflexivity.
          now destruct θ1.
        + now apply refine_new_pattern_match'.
    Qed.

    Lemma refine_debug `{RA : Rel SA CA} :
      ℛ⟦RMsg _ (RPureSpec RA -> RPureSpec RA)⟧
        SPureSpec.debug CPureSpec.debug.
    Proof.
      intros w0 ι0 Hpc0 msg sm cm rm. cbn - [RSat].
      intros sΦ cΦ rΦ [HΦ]. revert HΦ. now apply rm.
    Qed.

    #[local] Opaque RPureSpec.

    Lemma refine_assert_eq_nenv {N : Set} :
      ℛ⟦∀ Δ : NCtx N Ty, RMsg _ (RNEnv Δ -> RNEnv Δ -> RPureSpec RUnit)⟧
        SPureSpec.assert_eq_nenv CPureSpec.assert_eq_nenv.
    Proof.
      intros w0 ι0 Hpc0 Δ msg E1 ? -> E2 ? ->.
      induction E1; env.destroy E2; cbn - [RSat].
      - now apply refine_pure.
      - eapply refine_bind; eauto.
        intros w1 ω01 ι1 Hι1 Hpc1 _ _ _.
        apply refine_assert_formula; auto.
        eapply refine_formula_persist; eauto.
        cbn. reflexivity.
    Qed.

    Lemma refine_assert_eq_env :
      ℛ⟦∀ Δ, RMsg _ (REnv Δ -> REnv Δ -> RPureSpec RUnit)⟧
        SPureSpec.assert_eq_env CPureSpec.assert_eq_env.
    Proof.
      intros w0 ι0 Hpc0 Δ msg E1 ? -> E2 ? ->.
      induction E1; env.destroy E2; cbn - [RSat].
      - now apply refine_pure.
      - eapply refine_bind; eauto.
        intros w1 ω01 ι1 Hι1 Hpc1 _ _ _.
        apply refine_assert_formula; auto.
        eapply refine_formula_persist; eauto.
        cbn. reflexivity.
    Qed.

    Lemma refine_assert_eq_chunk :
      ℛ⟦RMsg _ (RChunk -> RChunk -> □(RPureSpec RUnit))⟧
        SPureSpec.assert_eq_chunk CPureSpec.assert_eq_chunk.
    Proof.
      intros w0 ι0 Hpc0 msg c ? -> c' ? ->. revert c'.
      induction c; intros [] w1 ω01 ι1 Hι1 Hpc1; cbn;
        auto; try (now apply refine_error).
      - destruct eq_dec.
        + destruct e; cbn.
          apply refine_assert_eq_env; auto.
          eapply refine_inst_persist; eauto; easy.
          eapply refine_inst_persist; eauto; easy.
        + now apply refine_error.
      - destruct eq_dec_het.
        + dependent elimination e; cbn.
          apply refine_assert_formula; auto. subst.
          now do 2 rewrite <- inst_persist.
        + now apply refine_error.
      - eapply refine_bind; eauto. apply IHc1; auto.
        intros w2 ω12 ι2 Hι2 Hpc2 _ _ _. apply IHc2; auto.
        subst. now rewrite sub_acc_trans, inst_subst, <- inst_persist.
      - eapply refine_bind; eauto. apply IHc1; auto.
        intros w2 ω12 ι2 Hι2 Hpc2 _ _ _. apply IHc2; auto.
        subst. now rewrite sub_acc_trans, inst_subst, <- inst_persist.
    Qed.

  End RPureSpec.

End RefinementMonadsOn.
