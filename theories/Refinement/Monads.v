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
     Syntax.Assertions
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
  (Import AS : AssertionsOn B PK WR)
  (Import SP : SymPropOn B PK WR)
  (Import GS : GenericSolverOn B PK WR SK)
  (Import SHAL : ShallowMonadsOn B PK WR AS SP)
  (Import SYMB : SymbolicMonadsOn B PK WR SK AS SP GS).

  Import ModalNotations.
  Import logicalrelation.
  Import logicalrelation.notations.

  #[export] Instance RPureSpec [SA CA] (RA : Rel SA CA) :
    Rel (SPureSpec SA) (CPureSpec CA) := □(RA -> ℙ) -> ℙ.

  Module RPureSpec.

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

    Lemma rrun :
      ℛ⟦RPureSpec RUnit -> ℙ⟧ SPureSpec.run CPureSpec.run.
    Proof.
      unfold SHeapSpec.run, CHeapSpec.run.
      intros w ι Hpc ms mc Hm.
      apply Hm; easy.
    Qed.

    Lemma rpure `{RA : Rel SA CA} :
      ℛ⟦RA -> RPureSpec RA⟧ SPureSpec.pure CPureSpec.pure.
    Proof.
      unfold RPureSpec, SPureSpec.pure, CPureSpec.pure.
      rsolve. eapply refine_apply; rsolve.
    Qed.

    Lemma rbind `{RA : Rel SA CA, RB : Rel SB CB} :
      ℛ⟦RPureSpec RA -> □(RA -> RPureSpec RB) -> RPureSpec RB⟧
        SPureSpec.bind CPureSpec.bind.
    Proof.
      unfold RPureSpec, SPureSpec.bind, CPureSpec.bind.
      intros. rsolve. do 3 (eapply refine_apply; rsolve).
    Qed.

    Lemma rblock `{R : Rel AT A} :
      ℛ⟦RPureSpec R⟧ (@SPureSpec.block AT) CPureSpec.block.
    Proof. constructor. Qed.

    Lemma rerror `{RA : Rel AT A} m :
      ℛ⟦RMsg □AMessage (RPureSpec RA)⟧ (@SPureSpec.error _) m.
    Proof. intros w ι Hpc msg sΦ cΦ rΦ. inversion 1. Qed.

    Lemma rangelic (x : option LVar) :
      ℛ⟦∀ σ, RPureSpec (RVal σ)⟧ (SPureSpec.angelic x) CPureSpec.angelic.
    Proof.
      intros w0 ι0 Hpc0 σ sΦ cΦ rΦ.
      intros [v HΦ]. exists v. revert HΦ.
      apply rΦ; cbn; eauto.
      - now rewrite inst_sub_wk1.
      - now rewrite instprop_subst, inst_sub_wk1.
    Qed.

    Lemma rdemonic (x : option LVar) :
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

    Lemma rangelic_ctx {N : Set} {n : N -> LVar} :
      ℛ⟦∀ Δ, RPureSpec (RNEnv Δ)⟧
        (SPureSpec.angelic_ctx n) CPureSpec.angelic_ctx.
    Proof.
      intros w ι Hpc Δ; revert w ι Hpc; induction Δ as [|Δ IHΔ [x σ]];
        intros w0 ι0 Hpc0; cbn [SPureSpec.angelic_ctx CPureSpec.angelic_ctx].
      - now apply rpure.
      - apply rbind; auto.
        intros w1 ω01 ι1 Hι1 Hpc1.
        intros svs cvs rvs.
        eapply rbind; auto.
        apply rangelic; auto.
        intros w2 ω12 ι2 Hι2 Hpc2.
        intros sv cv rv.
        apply rpure; auto.
        apply refine_env_snoc; auto.
        eapply refine_inst_persist; eauto.
    Qed.

    Lemma rdemonic_ctx {N : Set} {n : N -> LVar} :
      ℛ⟦∀ Δ : NCtx N Ty, RPureSpec (RNEnv Δ)⟧
        (SPureSpec.demonic_ctx n) CPureSpec.demonic_ctx.
    Proof.
      intros w ι Hpc Δ; revert w ι Hpc; induction Δ as [|Δ IHΔ [x σ]];
        intros w0 ι0 Hpc0; cbn [SPureSpec.demonic_ctx CPureSpec.demonic_ctx].
      - now apply rpure.
      - eapply rbind; auto.
        intros w1 ω01 ι1 Hι1 Hpc1.
        intros svs cvs rvs.
        eapply rbind; auto.
        apply rdemonic; auto.
        intros w2 ω12 ι2 Hι2 Hpc2.
        intros sv cv rv.
        apply rpure; auto.
        apply refine_env_snoc; auto.
        eapply refine_inst_persist; eauto.
    Qed.

    Lemma rassert_pathcondition :
      ℛ⟦RMsg (Box AMessage) (RPathCondition -> RPureSpec RUnit)⟧
        SPureSpec.assert_pathcondition CPureSpec.assert_formula.
    Proof.
      unfold SPureSpec.assert_pathcondition, symprop_assert_pathcondition,
        CPureSpec.assert_formula.
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

    Lemma rassume_pathcondition :
      ℛ⟦RPathCondition -> RPureSpec RUnit⟧
        SPureSpec.assume_pathcondition CPureSpec.assume_formula.
    Proof.
      unfold SPureSpec.assume_pathcondition, symprop_assume_pathcondition.
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

    Lemma rassert_formula :
      ℛ⟦RMsg (Box AMessage) (RFormula -> RPureSpec RUnit)⟧
        SPureSpec.assert_formula CPureSpec.assert_formula.
    Proof.
      unfold RPureSpec, SPureSpec.assert_formula, CPureSpec.assert_formula.
      rsolve. apply rassert_pathcondition; auto. cbn in *. intuition auto.
    Qed.

    Lemma rassume_formula :
      ℛ⟦RFormula -> RPureSpec RUnit⟧
        SPureSpec.assume_formula CPureSpec.assume_formula.
    Proof.
      unfold RPureSpec, SPureSpec.assume_formula, CPureSpec.assume_formula.
      rsolve. apply rassume_pathcondition; cbn in *; intuition auto.
    Qed.

    Lemma rangelic_binary `{RA : Rel SA CA} :
      ℛ⟦RPureSpec RA -> RPureSpec RA -> RPureSpec RA⟧
          SPureSpec.angelic_binary CPureSpec.angelic_binary.
    Proof.
      unfold RPureSpec, SPureSpec.angelic_binary, CPureSpec.angelic_binary.
      rsolve. apply refine_symprop_angelic_binary; rsolve.
    Qed.

    Lemma rdemonic_binary `{RA : Rel SA CA} :
      ℛ⟦RPureSpec RA -> RPureSpec RA -> RPureSpec RA⟧
          SPureSpec.demonic_binary CPureSpec.demonic_binary.
    Proof.
      unfold RPureSpec, SPureSpec.demonic_binary, CPureSpec.demonic_binary.
      rsolve. apply refine_symprop_demonic_binary; rsolve.
    Qed.

    Lemma rangelic_list' `{RA : Rel SA CA} :
      ℛ⟦RA -> RList RA -> RPureSpec RA⟧
        SPureSpec.angelic_list' CPureSpec.angelic_list'.
    Proof.
      intros w ι Hpc sv cv rv svs cvs rvs. revert sv cv rv.
      induction rvs; cbn [SPureSpec.angelic_list' CPureSpec.angelic_list'].
      - now apply rpure.
      - intros sv cv rv. apply rangelic_binary; auto. now apply rpure.
    Qed.

    Lemma rangelic_list `{RA : Rel SA CA} :
      ℛ⟦RMsg (Box AMessage) (RList RA -> RPureSpec RA)⟧
        SPureSpec.angelic_list CPureSpec.angelic_list.
    Proof.
      intros w ι Hpc msg sv cv [].
      - now apply rerror.
      - now apply rangelic_list'.
    Qed.

    Lemma rdemonic_list' `{RA : Rel SA CA} :
      ℛ⟦RA -> RList RA -> RPureSpec RA⟧
        SPureSpec.demonic_list' CPureSpec.demonic_list'.
    Proof.
      intros w ι Hpc sv cv rv svs cvs rvs. revert sv cv rv.
      induction rvs; cbn [SPureSpec.demonic_list' CPureSpec.demonic_list'].
      - now apply rpure.
      - intros sv cv rv. apply rdemonic_binary; auto. now apply rpure.
    Qed.

    Lemma rdemonic_list `{RA : Rel SA CA} :
      ℛ⟦RList RA -> RPureSpec RA⟧
        SPureSpec.demonic_list CPureSpec.demonic_list.
    Proof.
      intros w ι Hpc sv cv [].
      - now apply rblock.
      - now apply rdemonic_list'.
    Qed.

    Lemma rangelic_finite {F} `{finite.Finite F} :
      ℛ⟦RMsg _ (RPureSpec (RConst F))⟧
        (@SPureSpec.angelic_finite F _ _) (CPureSpec.angelic_finite F).
    Proof.
      intros w ι Hpc msg. apply rangelic_list; auto.
      induction (finite.enum F); now constructor.
    Qed.

    Lemma rdemonic_finite {F} `{finite.Finite F} :
      ℛ⟦RPureSpec (RConst F)⟧
        (@SPureSpec.demonic_finite F _ _) (CPureSpec.demonic_finite F).
    Proof.
      intros w ι Hpc. apply rdemonic_list; auto.
      induction (finite.enum F); now constructor.
    Qed.

    Lemma rangelic_pattern_match' {N : Set} (n : N -> LVar)
      {σ} (pat : @Pattern N σ) :
      ℛ⟦RMsg _ (RVal σ -> RPureSpec (RMatchResult pat))⟧
        (SPureSpec.angelic_pattern_match' n pat)
        (CPureSpec.angelic_pattern_match pat).
    Proof.
      intros w ι Hpc msg t v ->.
      unfold SPureSpec.angelic_pattern_match'.
      unfold CPureSpec.angelic_pattern_match.
      apply rbind; auto.
      { now apply rangelic_finite. }
      intros w1 r01 ι1 Hι1 Hpc1.
      intros pc ? ->.
      apply rbind; auto.
      { now apply rangelic_ctx. }
      intros w2 r12 ι2 Hι2 Hpc2.
      intros ts vs Htvs.
      apply rbind; auto.
      { apply rassert_formula; try assumption. cbn.
        rewrite (inst_persist (AT := fun Σ => Term Σ _)).
        rewrite !sub_acc_trans, inst_subst.
        rewrite inst_pattern_match_term_reverse.
        hnf in Htvs. subst. reflexivity.
      }
      intros w3 r23 ι3 Hι3 Hpc3 _ _ _.
      apply rpure; auto.
      exists eq_refl. eapply refine_inst_persist; eauto.
    Qed.
    #[global] Arguments rangelic_pattern_match' {N} n {σ} pat.

    Lemma rdemonic_pattern_match' {N : Set} (n : N -> LVar)
      {σ} (pat : @Pattern N σ) :
      ℛ⟦RVal σ -> RPureSpec (RMatchResult pat)⟧
        (SPureSpec.demonic_pattern_match' n pat)
        (CPureSpec.demonic_pattern_match pat).
    Proof.
      intros w ι Hpc t v ->.
      unfold SPureSpec.demonic_pattern_match'.
      unfold CPureSpec.demonic_pattern_match.
      apply rbind; auto.
      { now apply rdemonic_finite. }
      intros w1 r01 ι1 Hι1 Hpc1.
      intros pc ? ->.
      apply rbind; auto.
      { now apply rdemonic_ctx. }
      intros w2 r12 ι2 Hι2 Hpc2.
      intros ts vs Htvs.
      apply rbind; auto.
      { apply rassume_formula; try assumption. cbn.
        rewrite (inst_persist (AT := fun Σ => Term Σ _)).
        rewrite !sub_acc_trans, inst_subst.
        rewrite inst_pattern_match_term_reverse.
        hnf in Htvs. subst. reflexivity.
      }
      intros w3 r23 ι3 Hι3 Hpc3 _ _ _.
      apply rpure; auto.
      exists eq_refl. eapply refine_inst_persist; eauto.
    Qed.
    #[global] Arguments rdemonic_pattern_match' {N} n {σ} pat.

    Lemma rangelic_pattern_match {N : Set} (n : N -> LVar)
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
        + now apply (rangelic_pattern_match' n pat_bool).
      - apply (rangelic_pattern_match' n (pat_list σ x y)); auto.
      - intros msg sv cv ->.
        destruct (term_get_pair_spec sv) as [[svl svr] Heq|]; subst.
        + rewrite Heq. intros sΦ cΦ rΦ. hnf.
          rewrite CPureSpec.wp_angelic_pattern_match. cbn.
          apply rΦ; cbn; rewrite ?inst_sub_id; auto.
          now exists eq_refl.
        + now apply (rangelic_pattern_match' n (pat_pair _ _)); auto.
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
        + now apply (rangelic_pattern_match' n (pat_sum _ _ _ _)); auto.
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
        + now apply (rangelic_pattern_match' n (pat_enum E)); auto.
      - apply (rangelic_pattern_match' n (pat_bvec_split _ _ x y)); auto.
      - intros msg sv cv ->.
        destruct (term_get_val_spec sv); subst.
        + intros sΦ cΦ rΦ. hnf.
          rewrite CPureSpec.wp_angelic_pattern_match. cbn.
          apply rΦ; cbn; rewrite ?inst_sub_id; auto.
          now exists eq_refl.
        + now apply (rangelic_pattern_match' n (pat_bvec_exhaustive m)); auto.
      - apply (rangelic_pattern_match' n (pat_tuple p)); auto.
      - intros msg sv cv ->.
        destruct (term_get_record_spec sv) as [svs Heq|]; subst.
        + rewrite Heq. intros sΦ cΦ rΦ. hnf.
          rewrite CPureSpec.wp_angelic_pattern_match. cbn.
          apply rΦ; cbn; rewrite ?inst_sub_id; auto.
          exists eq_refl. cbn.
          unfold record_pattern_match_val.
          rewrite recordv_unfold_fold.
          symmetry. apply inst_record_pattern_match.
        + now apply (rangelic_pattern_match' n (pat_record _ _ _)); auto.
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
        + now apply (rangelic_pattern_match' n (pat_union _ _)); auto.
    Qed.
    #[global] Arguments rangelic_pattern_match' {N} n {σ} pat.

    Lemma rdemonic_pattern_match {N : Set} (n : N -> LVar)
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
        + now apply (rdemonic_pattern_match' n pat_bool).
      - apply (rdemonic_pattern_match' n (pat_list σ x y)); auto.
      - intros sv cv ->.
        destruct (term_get_pair_spec sv) as [[svl svr] Heq|]; subst.
        + rewrite Heq. intros sΦ cΦ rΦ. hnf.
          rewrite CPureSpec.wp_demonic_pattern_match. cbn.
          apply rΦ; cbn; rewrite ?inst_sub_id; auto.
          now exists eq_refl.
        + now apply (rdemonic_pattern_match' n (pat_pair _ _)); auto.
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
        + now apply (rdemonic_pattern_match' n (pat_sum _ _ _ _)); auto.
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
        + now apply (rdemonic_pattern_match' n (pat_enum E)); auto.
      - apply (rdemonic_pattern_match' n (pat_bvec_split _ _ x y)); auto.
      - intros sv cv ->.
        destruct (term_get_val_spec sv); subst.
        + intros sΦ cΦ rΦ. hnf.
          rewrite CPureSpec.wp_demonic_pattern_match. cbn.
          apply rΦ; cbn; rewrite ?inst_sub_id; auto.
          now exists eq_refl.
        + now apply (rdemonic_pattern_match' n (pat_bvec_exhaustive m)); auto.
      - apply (rdemonic_pattern_match' n (pat_tuple p)); auto.
      - intros sv cv ->.
        destruct (term_get_record_spec sv) as [svs Heq|]; subst.
        + rewrite Heq. intros sΦ cΦ rΦ. hnf.
          rewrite CPureSpec.wp_demonic_pattern_match. cbn.
          apply rΦ; cbn; rewrite ?inst_sub_id; auto.
          exists eq_refl. cbn.
          unfold record_pattern_match_val.
          rewrite recordv_unfold_fold.
          symmetry. apply inst_record_pattern_match.
        + now apply (rdemonic_pattern_match' n (pat_record _ _ _)); auto.
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
        + now apply (rdemonic_pattern_match' n (pat_union _ _)); auto.
    Qed.
    #[global] Arguments rdemonic_pattern_match' {N} n {σ} pat.

    Lemma rnew_pattern_match_regular {N : Set} n σ (pat : @Pattern N σ) :
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

    Lemma rpattern_match_var {N : Set} n {x σ} (pat : @Pattern N σ) :
      ℛ⟦RIn (x∷σ) -> RPureSpec (RMatchResult pat)⟧
        (SPureSpec.new_pattern_match_var n pat)
        (CPureSpec.new_pattern_match pat).
    Proof.
      intros w0 ι0 Hpc0 sv cv rv spost cpost rpost.
      unfold SPureSpec.new_pattern_match_var. hnf.
      intros Hsafe. hnf. cbn in rv. subst cv.
      rewrite <- (pattern_match_val_freshen n pat (Σ := w0)).
    Admitted.

    Lemma rnew_pattern_match' {N : Set} n σ (pat : @Pattern N σ) :
      ℛ⟦RVal σ -> RPureSpec (RMatchResult pat)⟧
        (SPureSpec.new_pattern_match' n pat)
        (CPureSpec.new_pattern_match pat).
    Proof.
      unfold SPureSpec.new_pattern_match'.
      intros w0 ι0 Hpc0 sv cv rv.
      destruct sv. now apply rpattern_match_var.
      all: now apply rnew_pattern_match_regular.
    Qed.

    Lemma rnew_pattern_match {N : Set} n σ (pat : @Pattern N σ) :
      ℛ⟦RVal σ -> RPureSpec (RMatchResult pat)⟧ (SPureSpec.new_pattern_match n pat)
        (CPureSpec.new_pattern_match pat).
    Proof.
      induction pat; cbn [SPureSpec.new_pattern_match];
        intros w0 ι0 Hpc0 sv cv ->.
      - unfold CPureSpec.new_pattern_match.
        apply rpure; auto. now exists eq_refl.
      - destruct (term_get_val_spec sv) as [cv ?|].
        + apply rpure; auto. subst. now exists eq_refl.
        + now apply rnew_pattern_match' with (pat := pat_bool).
      - now apply rnew_pattern_match'.
      - destruct (term_get_pair_spec sv) as [[? ?] ->|].
        + apply rpure; auto. now exists eq_refl.
        + now apply rnew_pattern_match' with (pat := pat_pair _ _).
      - destruct (term_get_sum_spec sv) as [[] ->|].
        + apply rpure; auto. now exists eq_refl.
        + apply rpure; auto. now exists eq_refl.
        + now apply rnew_pattern_match' with (pat := pat_sum _ _ _ _).
      - apply rpure; auto. now exists eq_refl.
      - destruct (term_get_val_spec sv) as [? ->|].
        + apply rpure; auto. now exists eq_refl.
        + now apply rnew_pattern_match' with (pat := pat_enum E).
      - now apply rnew_pattern_match'.
      - destruct (term_get_val_spec sv) as [? ->|].
        + apply rpure; auto. now exists eq_refl.
        + now apply rnew_pattern_match' with (pat := pat_bvec_exhaustive m).
      - destruct (term_get_tuple_spec sv) as [? ->|].
        + apply rpure; auto. exists eq_refl. cbn.
          unfold tuple_pattern_match_val.
          rewrite envrec.to_of_env. symmetry.
          apply inst_tuple_pattern_match.
        + now apply rnew_pattern_match'.
      - destruct (term_get_record_spec sv) as [? ->|].
        + apply rpure; auto. exists eq_refl. cbn.
          unfold record_pattern_match_val.
          rewrite recordv_unfold_fold. symmetry.
          apply inst_record_pattern_match.
        + now apply rnew_pattern_match'.
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
        + now apply rnew_pattern_match'.
    Qed.

    Lemma rdebug `{RA : Rel SA CA} :
      ℛ⟦RMsg _ (RPureSpec RA -> RPureSpec RA)⟧
        SPureSpec.debug CPureSpec.debug.
    Proof.
      intros w0 ι0 Hpc0 msg sm cm rm. cbn - [RSat].
      intros sΦ cΦ rΦ [HΦ]. revert HΦ. now apply rm.
    Qed.

    Opaque RPureSpec.

    Lemma rassert_eq_nenv {N : Set} :
      ℛ⟦∀ Δ : NCtx N Ty, RMsg _ (RNEnv Δ -> RNEnv Δ -> RPureSpec RUnit)⟧
        SPureSpec.assert_eq_nenv CPureSpec.assert_eq_nenv.
    Proof.
      intros w0 ι0 Hpc0 Δ msg E1 ? -> E2 ? ->.
      induction E1; env.destroy E2; cbn - [RSat].
      - now apply rpure.
      - eapply rbind; eauto.
        intros w1 ω01 ι1 Hι1 Hpc1 _ _ _.
        apply rassert_formula; auto.
        eapply refine_formula_persist; eauto.
        cbn. reflexivity.
    Qed.

    Lemma rassert_eq_env :
      ℛ⟦∀ Δ, RMsg _ (REnv Δ -> REnv Δ -> RPureSpec RUnit)⟧
        SPureSpec.assert_eq_env CPureSpec.assert_eq_env.
    Proof.
      intros w0 ι0 Hpc0 Δ msg E1 ? -> E2 ? ->.
      induction E1; env.destroy E2; cbn - [RSat].
      - now apply rpure.
      - eapply rbind; eauto.
        intros w1 ω01 ι1 Hι1 Hpc1 _ _ _.
        apply rassert_formula; auto.
        eapply refine_formula_persist; eauto.
        cbn. reflexivity.
    Qed.

    Lemma rassert_eq_chunk :
      ℛ⟦RMsg _ (RChunk -> RChunk -> □(RPureSpec RUnit))⟧
        SPureSpec.assert_eq_chunk CPureSpec.assert_eq_chunk.
    Proof.
      intros w0 ι0 Hpc0 msg c ? -> c' ? ->. revert c'.
      induction c; intros [] w1 ω01 ι1 Hι1 Hpc1; cbn;
        auto; try (now apply rerror).
      - destruct eq_dec.
        + destruct e; cbn.
          apply rassert_eq_env; auto.
          eapply refine_inst_persist; eauto; easy.
          eapply refine_inst_persist; eauto; easy.
        + now apply rerror.
      - destruct eq_dec_het.
        + dependent elimination e; cbn.
          apply rassert_formula; auto. subst.
          now do 2 rewrite <- inst_persist.
        + now apply rerror.
      - eapply rbind; eauto. apply IHc1; auto.
        intros w2 ω12 ι2 Hι2 Hpc2 _ _ _. apply IHc2; auto.
        subst. now rewrite sub_acc_trans, inst_subst, <- inst_persist.
      - eapply rbind; eauto. apply IHc1; auto.
        intros w2 ω12 ι2 Hι2 Hpc2 _ _ _. apply IHc2; auto.
        subst. now rewrite sub_acc_trans, inst_subst, <- inst_persist.
    Qed.

  End RPureSpec.

  (* Section RPureSpecM. *)
  (*   Import SPureSpecM (SPureSpecM) CPureSpecM (CPureSpecM). *)

  (*   Context {MT : TYPE -> TYPE} {M : Type -> Type} *)
  (*     {pureMT : SPureSpecM MT} {pureM : CPureSpecM M} *)
  (*     (RM : forall {AT A} (R : Rel AT A), Rel (MT AT) (M A)). *)

  (*   Class RPureSpecM : Type := { *)
  (*       rel_pure `{R : Rel AT A} : *)
  (*       ℛ⟦R -> RM R⟧ SPureSpecM.pure CPureSpecM.pure; *)
  (*       rel_bind `{RA : Rel AT A, RB : Rel BT B} : *)
  (*       ℛ⟦RM RA -> □(RA -> RM RB) -> RM RB⟧ SPureSpecM.bind CPureSpecM.bind; *)
  (*       rel_error `{RA : Rel AT A} m : *)
  (*       ℛ⟦RMsg □(SHeap -> AMessage) (RM RA)⟧ SPureSpecM.error m; *)
  (*       rel_block `{R : Rel AT A} : *)
  (*       ℛ⟦RM R⟧ (@SPureSpecM.block MT _ AT) CPureSpecM.block; *)
  (*       rel_angelic (x : option LVar) : *)
  (*       ℛ⟦∀ σ, RM (RVal σ)⟧ (SPureSpecM.angelic x) CPureSpecM.angelic; *)
  (*       rel_demonic (x : option LVar) : *)
  (*       ℛ⟦∀ σ, RM (RVal σ)⟧ (SPureSpecM.demonic x) CPureSpecM.demonic; *)
  (*       rel_angelic_ctx {N : Set} {n : N -> LVar} : *)
  (*       ℛ⟦∀ Δ, RM (RNEnv Δ)⟧ (SPureSpecM.angelic_ctx n) CPureSpecM.angelic_ctx; *)
  (*       rel_demonic_ctx {N : Set} {n : N -> LVar} : *)
  (*       ℛ⟦∀ Δ : NCtx N Ty, RM (RNEnv Δ)⟧ (SPureSpecM.demonic_ctx n) CPureSpecM.demonic_ctx; *)
  (*       rel_assert_pathcondition : *)
  (*       ℛ⟦RMsg □(SHeap -> AMessage) (RPathCondition -> RM RUnit)⟧ SPureSpecM.assert_pathcondition CPureSpecM.assert_formula; *)
  (*       rel_assert_formula : *)
  (*       ℛ⟦RMsg □(SHeap -> AMessage) (RFormula -> RM RUnit)⟧ SPureSpecM.assert_formula CPureSpecM.assert_formula; *)
  (*       rel_assume_pathcondition : *)
  (*       ℛ⟦RPathCondition -> RM RUnit⟧ SPureSpecM.assume_pathcondition CPureSpecM.assume_formula; *)
  (*       rel_assume_formula : *)
  (*       ℛ⟦RFormula -> RM RUnit⟧ SPureSpecM.assume_formula CPureSpecM.assume_formula; *)
  (*       rel_angelic_binary `{R : Rel AT A} : *)
  (*       ℛ⟦RM R -> RM R -> RM R⟧ SPureSpecM.angelic_binary CPureSpecM.angelic_binary; *)
  (*       rel_demonic_binary `{R : Rel AT A} : *)
  (*       ℛ⟦RM R -> RM R -> RM R⟧ SPureSpecM.demonic_binary CPureSpecM.demonic_binary; *)
  (*       rel_angelic_pattern_match {N : Set} (n : N -> LVar) {σ} (pat : @Pattern N σ) : *)
  (*       ℛ⟦RMsg _ (RVal σ -> RM (RMatchResult pat))⟧ (SPureSpecM.angelic_pattern_match n pat) (CPureSpecM.angelic_pattern_match pat); *)
  (*       rel_demonic_pattern_match {N : Set} (n : N -> LVar) {σ} (pat : @Pattern N σ) : *)
  (*       ℛ⟦RVal σ -> RM (RMatchResult pat)⟧ (SPureSpecM.demonic_pattern_match n pat) (CPureSpecM.demonic_pattern_match pat); *)
  (*       rel_new_pattern_match {N : Set} (n : N -> LVar) {σ} (pat : @Pattern N σ) : *)
  (*       ℛ⟦RVal σ -> RM (RMatchResult pat)⟧ (SPureSpecM.new_pattern_match n pat) (CPureSpecM.new_pattern_match pat); *)
  (*       rel_debug `{R : Rel AT A} : *)
  (*       ℛ⟦RMsg _ (RM R -> RM R)⟧ SPureSpecM.debug CPureSpecM.debug; *)
  (*     }. *)

  (*   Context {rspecM : RPureSpecM}. *)

  (* End RPureSpecM. *)
  (* #[global] Arguments RPureSpecM {MT M _ _} RM. *)

  (* Section RHeapSpecM. *)
  (*   Import SPureSpecM (SPureSpecM) CPureSpecM (CPureSpecM). *)
  (*   Import SHeapSpecM (SHeapSpecM) CHeapSpecM (CHeapSpecM). *)

  (*   Context {MT : TYPE -> TYPE} {M : Type -> Type} *)
  (*     {pureMT : SPureSpecM MT} {heapMT : SHeapSpecM MT} *)
  (*     {pureM : CPureSpecM M} {heapM : CHeapSpecM M} *)
  (*     (RM : forall {AT A} (R : Rel AT A), Rel (MT AT) (M A)). *)

  (*   Class RHeapSpecM : Type := { *)
  (*     rel_produce_chunk : *)
  (*       ℛ⟦RChunk -> RM RUnit⟧ SHeapSpecM.produce_chunk CHeapSpecM.produce_chunk; *)
  (*     rel_consume_chunk : *)
  (*       ℛ⟦RChunk -> RM RUnit⟧ SHeapSpecM.consume_chunk CHeapSpecM.consume_chunk; *)
  (*     rel_consume_chunk_angelic : *)
  (*       ℛ⟦RChunk -> RM RUnit⟧ SHeapSpecM.consume_chunk_angelic CHeapSpecM.consume_chunk; *)
  (*   }. *)

  (* End RHeapSpecM. *)
  (* #[global] Arguments RHeapSpecM {MT M _ _} RM. *)

  (* (* Module RReaderT. *) *)
  (* (*   Section RReaderT. *) *)

  (* (*     Context {RT R} {persR : Persistent RT} {RR : Rel RT R}. *) *)
  (* (*     Context `{spureM : SPureSpecM MT, sheapm : SHeapSpecM MT, *) *)
  (* (*               cpureM : CPureSpecM M, cheapM : CHeapSpecM M} *) *)
  (* (*              (RM : forall {AT A} (R : Rel AT A), Rel (MT AT) (M A)). *) *)

  (* (*     #[export] Instance RReaderT `{RA : Rel AT A} : *) *)
  (* (*       Rel (ReaderT RT MT AT) (CReaderT R M A) := *) *)
  (* (*       RR -> RM RA. *) *)

  (* (*     #[export] Instance rpurespecm : RPureSpecM (@RReaderT). *) *)
  (* (*     Proof. *) *)
  (* (*     Admitted. *) *)

  (* (*     #[export] Instance rheapspecm : RHeapSpecM (@RReaderT). *) *)
  (* (*     Proof. *) *)
  (* (*     Admitted. *) *)

  (* (*   End RReaderT. *) *)
  (* (*   #[global] Arguments RReaderT {RT R} RR {MT M} RM {AT A} RA. *) *)
  (* (* End RReaderT. *) *)
  (* (* Export (hints) RReaderT. *) *)
  (* (* Export RReaderT (RReaderT). *) *)

  (* Section ProduceConsume. *)

  (*   Context {MT M} {spureMT : SPureSpecM MT} {cpureM : CPureSpecM M}. *)
  (*   Context {sheapM : SHeapSpecM MT} {cheapM : CHeapSpecM M}. *)
  (*   Context {RM : forall {AT A} (R : Rel AT A), Rel (MT AT) (M A)}. *)
  (*   Context {rpureM : RPureSpecM RM} {rheapM : RHeapSpecM RM}. *)

  (*   Lemma rproduce {Σ} (asn : Assertion Σ) : *)
  (*     ℛ⟦RInst (Sub Σ) (Valuation Σ) -> RM RUnit⟧ *)
  (*       (sproduce asn) (cproduce asn). *)
  (*   Proof. *)
  (*     induction asn; cbn [sproduce cproduce]; intros w0 ι0 Hpc0 sδ cδ Hδ. *)
  (*     - apply rel_assume_formula; auto. *)
  (*       now apply rformula_subst. *)
  (*     - apply rel_produce_chunk; eauto. *)
  (*       hnf. now rewrite inst_subst, Hδ. *)
  (*     - apply rel_produce_chunk; eauto. *)
  (*       hnf. now rewrite inst_subst, Hδ. *)
  (*     - eapply rel_bind; auto. *)
  (*       apply rel_demonic_pattern_match; auto. *)
  (*       hnf. now rewrite inst_subst, Hδ. *)
  (*       intros w1 θ1 ι1 -> Hpc1 [] [] []. subst. cbn in H0. subst. *)
  (*       eapply H; eauto. hnf. hnf in Hδ. subst. *)
  (*       symmetry. etransitivity. *)
  (*       refine (inst_env_cat (persist sδ θ1) n ι1). *)
  (*       f_equal. apply inst_persist. *)
  (*     - eapply rel_bind; auto. *)
  (*       apply IHasn1; auto. intros w1 θ1 ι1 ? Hpc1 _ _ _. *)
  (*       apply IHasn2; auto. eapply rinst_persist; eauto. *)
  (*     - eapply rel_demonic_binary; eauto. *)
  (*       apply IHasn1; auto. apply IHasn2; auto. *)
  (*     - eapply rel_bind; auto. apply rel_demonic; auto. *)
  (*       intros w1 θ1 ι1 -> Hpc1 t v ->. apply IHasn; auto. *)
  (*       cbn - [inst]. cbn in Hδ. subst. *)
  (*       now rewrite <- inst_persist. *)
  (*     - apply rel_debug; auto. apply rel_pure; auto. *)
  (*       constructor. *)
  (*   Qed. *)

  (*   Lemma rconsume {Σ} (asn : Assertion Σ) : *)
  (*     ℛ⟦RInst (Sub Σ) (Valuation Σ) -> RM RUnit⟧ *)
  (*       (sconsume asn) (cconsume asn). *)
  (*   Proof. *)
  (*     induction asn; cbn [sconsume cconsume]; intros w0 ι0 Hpc0 sδ cδ Hδ. *)
  (*     - apply rel_assert_formula; auto. *)
  (*       now apply rformula_subst. *)
  (*     - apply rel_consume_chunk; eauto. *)
  (*       hnf. now rewrite inst_subst, Hδ. *)
  (*     - apply rel_consume_chunk_angelic; eauto. *)
  (*       hnf. now rewrite inst_subst, Hδ. *)
  (*     - eapply rel_bind; auto. *)
  (*       apply rel_angelic_pattern_match; auto. *)
  (*       hnf. now rewrite inst_subst, Hδ. *)
  (*       intros w1 θ1 ι1 -> Hpc1 [] [] []. subst. cbn in H0. subst. *)
  (*       eapply H; eauto. hnf. hnf in Hδ. subst. *)
  (*       symmetry. etransitivity. *)
  (*       refine (inst_env_cat (persist sδ θ1) n ι1). *)
  (*       f_equal. apply inst_persist. *)
  (*     - eapply rel_bind; auto. *)
  (*       apply IHasn1; auto. intros w1 θ1 ι1 ? Hpc1 _ _ _. *)
  (*       apply IHasn2; auto. eapply rinst_persist; eauto. *)
  (*     - eapply rel_angelic_binary; eauto. *)
  (*       apply IHasn1; auto. apply IHasn2; auto. *)
  (*     - eapply rel_bind; auto. apply rel_angelic; auto. *)
  (*       intros w1 θ1 ι1 -> Hpc1 t v ->. apply IHasn; auto. *)
  (*       cbn - [inst]. cbn in Hδ. subst. *)
  (*       now rewrite <- inst_persist. *)
  (*     - apply rel_debug; auto. apply rel_pure; auto. *)
  (*       constructor. *)
  (*   Qed. *)

  (*   Lemma rcall_contract {Δ τ} (c : SepContract Δ τ) : *)
  (*     ℛ⟦RInst (SStore Δ) (CStore Δ) -> RM (RVal τ)⟧ *)
  (*       (scall_contract c) (ccall_contract c). *)
  (*   Proof. *)
  (*     intros w0 ι0 Hpc0 sδ cδ rδ. *)
  (*     destruct c as [lvars pats req res ens]; cbn. *)
  (*     eapply rel_bind; auto. *)
  (*     { apply rel_angelic_ctx; auto. } *)
  (*     intros w1 θ1 ι1 Heq1 Hpc1 slenv clenv rlenv. *)
  (*     eapply rel_bind; auto. *)
  (*     { apply rassert_eq_nenv; auto. *)
  (*       rewrite rlenv. hnf. now rewrite inst_subst. *)
  (*       eapply rinst_persist; eauto. } *)
  (*     intros w2 θ2 ι2 Heq2 Hpc2 _ _ _. *)
  (*     eapply rel_bind; auto. *)
  (*     { apply rconsume; auto. rewrite rlenv. *)
  (*       hnf. subst. now rewrite <- inst_persist. } *)
  (*     intros w3 θ3 ι3 Heq3 Hpc3 _ _ _. *)
  (*     eapply rel_bind; auto. *)
  (*     { apply rel_demonic; auto. } *)
  (*     intros w4 θ4 ι4 Heq4 Hpc4 t v Htv. *)
  (*     eapply rel_bind; auto. *)
  (*     { apply rproduce; auto. *)
  (*       cbn - [inst_env sub_snoc]. *)
  (*       rewrite inst_sub_snoc, inst_persist. *)
  (*       rewrite sub_acc_trans. *)
  (*       rewrite inst_subst. *)
  (*       cbn in rlenv, Htv. subst. *)
  (*       now rewrite inst_persist. *)
  (*     } *)
  (*     intros w5 θ5 ι5 Heq5 Hpc5 _ _ _. *)
  (*     apply rel_pure; auto. *)
  (*     eapply rinst_persist; eauto. *)
  (*   Qed. *)

  (*   Lemma rcall_lemma {Δ} (lem : Lemma Δ) : *)
  (*     ℛ⟦RInst (SStore Δ) (CStore Δ) -> RM RUnit⟧ *)
  (*       (scall_lemma lem) (ccall_lemma lem). *)
  (*   Proof. *)
  (*     intros w0 ι0 Hpc0 sδ cδ rδ. *)
  (*     destruct lem as [lvars pats req ens]; cbn. *)
  (*     eapply rel_bind; auto. *)
  (*     { apply rel_angelic_ctx; auto. } *)
  (*     intros w1 θ1 ι1 Heq1 Hpc1 slenv clenv rlenv. *)
  (*     eapply rel_bind; auto. *)
  (*     { apply rassert_eq_nenv; auto. *)
  (*       rewrite rlenv. hnf. now rewrite inst_subst. *)
  (*       eapply rinst_persist; eauto. } *)
  (*     intros w2 θ2 ι2 Heq2 Hpc2 _ _ _. *)
  (*     eapply rel_bind; auto. *)
  (*     { apply rconsume; auto. rewrite rlenv. *)
  (*       hnf. subst. now rewrite <- inst_persist. } *)
  (*     intros w3 θ3 ι3 Heq3 Hpc3 _ _ _. *)
  (*     apply rproduce; auto. *)
  (*     cbn - [inst_env sub_snoc]. *)
  (*     rewrite !inst_persist. *)
  (*     cbn in rlenv. now subst. *)
  (*   Qed. *)

  (* End ProduceConsume. *)

End RefinementMonadsOn.
