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
     Signature
     Base
     Shallow.MonadInstances
     Symbolic.MonadInstances.

Import ctx.notations.
Import env.notations.

Set Implicit Arguments.

Module Type RefinementMonadInstancesOn
  (Import B : Base)
  (Import SIG : Signature B)
  (Import SOLV : SolverKit B SIG)
  (Import SHAL : ShallowMonadInstancesOn B SIG)
  (Import SYMB : SymbolicMonadInstancesOn B SIG SOLV).

  Import ModalNotations.
  Import Postprocessing.
  Import logicalrelation.
  Import logicalrelation.notations.

  #[export] Instance RPureSpec {AT A} (R : Rel AT A) :
    Rel (SPureSpec AT) (CPureSpec A) := □(R -> ℙ) -> ℙ.

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

  Module PureSpec.

    Lemma refine_pure {AT A} {R : Rel AT A} :
      ℛ⟦R -> RPureSpec R⟧ SPureSpecM.pure CPureSpecM.pure.
    Proof.
      unfold RPureSpec.
      unfold SPureSpecM.pure, SPureSpec.purespecm, SPureSpec.pure.
      unfold CPureSpecM.pure, CPureSpec.purespecm, CPureSpec.pure.
      rsolve. eapply refine_apply; rsolve.
    Qed.

    Lemma refine_bind `{RA : Rel AT A, RB : Rel BT B} :
      forall {w : World} (ι : Valuation w),
        ℛ⟦RPureSpec RA -> □(RA -> RPureSpec RB) -> RPureSpec RB⟧@{ι}
          (SPureSpecM.bind (w:=w))
          CPureSpecM.bind.
    Proof.
      unfold RPureSpec.
      unfold SPureSpecM.bind, SPureSpec.purespecm, SPureSpec.bind.
      unfold CPureSpecM.bind, CPureSpec.purespecm, CPureSpec.bind.
      intros. rsolve.
      eapply refine_apply; rsolve.
      eapply refine_apply; rsolve.
      eapply refine_apply; rsolve.
    Qed.

    (* This lemma has a nicer type, but an unused assumption. *)
    Lemma refine_bind' `{RA : Rel AT A, RB : Rel BT B} :
      ℛ⟦RPureSpec RA -> □(RA -> RPureSpec RB) -> RPureSpec RB⟧
        SPureSpecM.bind CPureSpecM.bind.
    Proof. intros ? ? _. apply refine_bind. Qed.

    Lemma refine_error `{RA : Rel AT A} :
      ℛ⟦RMsg (Box (Impl SHeap AMessage)) (RPureSpec RA)⟧ SPureSpecM.error CPureSpecM.error.
    Proof. intros w ι Hpc m POST__s POST__c HPOST. inversion 1. Qed.

    Lemma refine_angelic (x : option LVar) :
      ℛ⟦∀ σ, RPureSpec (RVal σ)⟧ (SPureSpecM.angelic x) CPureSpecM.angelic.
    Proof.
      intros w0 ι0 Hpc0 σ POST__s POST__c HPOST.
      intros [v Hwp]. exists v. revert Hwp.
      apply HPOST; cbn; eauto.
      now rewrite inst_sub_wk1.
      now rewrite instprop_subst, inst_sub_wk1.
    Qed.

    Lemma refine_angelic_ctx {N : Set} {n : N -> LVar} :
      ℛ⟦∀ Δ, RPureSpec (RNEnv Δ)⟧
        (SPureSpecM.angelic_ctx n) CPureSpecM.angelic_ctx.
    Proof.
      intros w ι Hpc Δ; revert w ι Hpc; induction Δ as [|Δ IHΔ [x σ]];
        intros w0 ι0 Hpc0; cbn [SPureSpecM.angelic_ctx CPureSpecM.angelic_ctx].
      - now apply refine_pure.
      - apply refine_bind; auto.
        intros w1 ω01 ι1 Hι1 Hpc1.
        intros ts vs Htvs.
        eapply refine_bind.
        apply refine_angelic; auto.
        intros w2 ω12 ι2 Hι2 Hpc2.
        intros t v Htv.
        apply refine_pure; auto.
        apply refine_env_snoc; auto.
        eapply refine_inst_persist; eauto.
    Qed.

    Lemma refine_demonic (x : option LVar) :
      ℛ⟦∀ σ, RPureSpec (RVal σ)⟧ (SPureSpecM.demonic x) CPureSpecM.demonic.
    Proof.
      intros w0 ι0 Hpc0 σ POST__s POST__c HPOST.
      intros Hwp v. cbn in Hwp. specialize (Hwp v).
      remember (fresh_lvar w0 x) as ℓ.
      revert Hwp. apply HPOST;
        [ (* Boilerplate #1 *) cbn; now rewrite inst_sub_wk1
        | (* Boilerplate #2 *) cbn; now rewrite instprop_subst, inst_sub_wk1
        | ].
      reflexivity.
    Qed.

    Lemma refine_demonic_ctx {N : Set} {n : N -> LVar} :
      ℛ⟦∀ Δ : NCtx N Ty, RPureSpec (RNEnv Δ)⟧
        (SPureSpecM.demonic_ctx n) CPureSpecM.demonic_ctx.
    Proof.
      intros w ι Hpc Δ; revert w ι Hpc; induction Δ as [|Δ IHΔ [x σ]];
        intros w0 ι0 Hpc0; cbn [SPureSpecM.demonic_ctx CPureSpecM.demonic_ctx].
      - now apply refine_pure.
      - eapply refine_bind; auto.
        intros w1 ω01 ι1 Hι1 Hpc1.
        intros ts vs Htvs.
        eapply refine_bind.
        apply refine_demonic; auto.
        intros w2 ω12 ι2 Hι2 Hpc2.
        intros t v Htv.
        apply refine_pure; auto.
        apply refine_env_snoc; auto.
        eapply refine_inst_persist; eauto.
    Qed.

    Lemma refine_assume_pathcondition :
      ℛ⟦RPathCondition -> RPureSpec RUnit⟧
        SPureSpecM.assume_pathcondition CPureSpecM.assume_formula.
    Proof.
      unfold SPureSpecM.assume_pathcondition, SPureSpec.purespecm,
        SPureSpec.assume_pathcondition, symprop_assume_pathcondition.
      intros w0 ι0 Hpc0 fmls0 p Heq POST__s POST__c HPOST.
      intros Hwp Hfmls0. apply Heq in Hfmls0.
      destruct (solver_spec _ fmls0) as [[w1 [ζ fmls1]] Hsolver|Hsolver].
      - specialize (Hsolver ι0 Hpc0).
        destruct Hsolver as [Hν Hsolver]. inster Hν by auto.
        specialize (Hsolver (inst (sub_triangular_inv ζ) ι0)).
        rewrite inst_triangular_right_inverse in Hsolver; auto.
        inster Hsolver by now try apply entails_triangular_inv.
        destruct Hsolver as [Hsolver _]. inster Hsolver by auto.
        rewrite SymProp.safe_assume_triangular,
          SymProp.safe_assume_pathcondition_without_solver in Hwp.
        specialize (Hwp Hν Hsolver). revert Hwp.
        unfold four. apply HPOST; cbn; wsimpl; auto.
        unfold PathCondition. rewrite instprop_cat. split; auto.
        now apply entails_triangular_inv.
      - now apply Hsolver in Hfmls0.
    Qed.

    Lemma refine_assume_formula :
      ℛ⟦RFormula -> RPureSpec RUnit⟧
        SPureSpecM.assume_formula CPureSpecM.assume_formula.
    Proof.
      unfold RPureSpec.
      unfold SPureSpecM.assume_formula, SPureSpec.purespecm, SPureSpec.assume_formula.
      unfold CPureSpecM.assume_formula, CPureSpec.purespecm, CPureSpec.assume_formula.
      rsolve. apply refine_assume_pathcondition; cbn in *; intuition auto.
    Qed.

    Lemma refine_assert_pathcondition :
      ℛ⟦RMsg (Box (Impl SHeap AMessage)) (RPathCondition -> RPureSpec RUnit)⟧
        SPureSpecM.assert_pathcondition CPureSpecM.assert_formula.
    Proof.
      unfold SPureSpecM.assert_pathcondition, SPureSpec.purespecm,
        SPureSpec.assert_pathcondition, symprop_assert_pathcondition,
        CPureSpecM.assert_formula.
      intros w0 ι0 Hpc0 msg fmls0 p Heq POST__s POST__c HPOST Hwp.
      destruct (solver_spec _ fmls0) as [[w1 [ζ fmls1]] Hsolver|Hsolver].
      - specialize (Hsolver ι0 Hpc0). destruct Hsolver as [_ Hsolver].
        rewrite SymProp.safe_assert_triangular in Hwp. destruct Hwp as [Hν Hwp].
        rewrite SymProp.safe_assert_pathcondition_without_solver in Hwp.
        destruct Hwp as [Hfmls Hwp].
        split.
        + apply Hsolver in Hfmls; rewrite ?inst_triangular_right_inverse; auto.
          now apply Heq.
          now apply entails_triangular_inv.
        + revert Hwp. unfold four.
          apply HPOST; cbn; wsimpl; eauto.
          unfold PathCondition. rewrite instprop_cat. split; auto.
          now apply entails_triangular_inv.
      - contradict Hwp.
    Qed.

    Lemma refine_assert_formula :
      ℛ⟦RMsg (Box (Impl SHeap AMessage)) (RFormula -> RPureSpec RUnit)⟧
        SPureSpec.assert_formula CPureSpecM.assert_formula.
    Proof.
      unfold RPureSpec.
      unfold SPureSpecM.assert_formula, SPureSpec.purespecm, SPureSpec.assert_formula.
      unfold CPureSpecM.assert_formula, CPureSpec.purespecm, CPureSpec.assert_formula.
      rsolve. apply refine_assert_pathcondition; auto. cbn in *. intuition auto.
    Qed.

    Lemma refine_angelic_binary `{R : Rel AT A} :
      ℛ⟦RPureSpec R -> RPureSpec R -> RPureSpec R⟧
          SPureSpecM.angelic_binary CPureSpecM.angelic_binary.
    Proof.
      unfold RPureSpec.
      unfold SPureSpecM.angelic_binary, SPureSpec.purespecm, SPureSpec.angelic_binary.
      unfold CPureSpecM.angelic_binary, CPureSpec.purespecm, CPureSpec.angelic_binary.
      rsolve. apply refine_symprop_angelic_binary; rsolve.
    Qed.

    Lemma refine_demonic_binary `{R : Rel AT A} :
      ℛ⟦RPureSpec R -> RPureSpec R -> RPureSpec R⟧
          SPureSpecM.demonic_binary CPureSpecM.demonic_binary.
    Proof.
      unfold RPureSpec.
      unfold SPureSpecM.demonic_binary, SPureSpec.purespecm, SPureSpec.demonic_binary.
      unfold CPureSpecM.demonic_binary, CPureSpec.purespecm, CPureSpec.demonic_binary.
      rsolve. apply refine_symprop_demonic_binary; rsolve.
    Qed.

    Lemma refine_block `{R : Rel AT A} :
      ℛ⟦RPureSpec R⟧ (@SPureSpec.block AT) CPureSpecM.block.
    Proof. constructor. Qed.

    Opaque RPureSpec.

    Lemma refine_assert_eq_nenv {N : Set} :
      ℛ⟦∀ Δ : NCtx N Ty, RMsg _ (RNEnv Δ -> RNEnv Δ -> RPureSpec RUnit)⟧
        SPureSpecM.assert_eq_nenv CPureSpecM.assert_eq_nenv.
    Proof.
      intros w0 ι0 Hpc0 Δ msg E1 ? -> E2 ? ->.
      induction E1; env.destroy E2; cbn - [RSat].
      - now apply refine_pure.
      - eapply refine_bind; first apply IHE1.
        intros w1 ω01 ι1 Hι1 Hpc1 _ _ _.
        apply refine_assert_formula; auto.
        eapply refine_formula_persist; eauto.
        cbn. reflexivity.
    Qed.

    Lemma refine_assert_eq_env :
      ℛ⟦∀ Δ, RMsg _ (REnv Δ -> REnv Δ -> RPureSpec RUnit)⟧
        SPureSpecM.assert_eq_env CPureSpecM.assert_eq_env.
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
        SPureSpecM.assert_eq_chunk CPureSpecM.assert_eq_chunk.
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
      - eapply refine_bind. apply IHc1; auto.
        intros w2 ω12 ι2 Hι2 Hpc2 _ _ _. apply IHc2; auto.
        subst. now rewrite sub_acc_trans, inst_subst, <- inst_persist.
      - eapply refine_bind. apply IHc1; auto.
        intros w2 ω12 ι2 Hι2 Hpc2 _ _ _. apply IHc2; auto.
        subst. now rewrite sub_acc_trans, inst_subst, <- inst_persist.
    Qed.

    Lemma refine_angelic_list' `{R : Rel AT A} :
      ℛ⟦R -> RList R -> RPureSpec R⟧
        SPureSpec.angelic_list' CPureSpec.angelic_list'.
    Proof.
      intros w ι Hpc t v Htv ts vs Htvs. revert t v Htv.
      induction Htvs; cbn; intros ?t ?v ?Htv.
      - now apply refine_pure.
      - apply refine_angelic_binary; auto.
        now apply refine_pure.
    Qed.

    Lemma refine_angelic_list `{R : Rel AT A} :
      ℛ⟦RMsg (Box (Impl SHeap AMessage)) (RList R -> RPureSpec R)⟧
        SPureSpec.angelic_list CPureSpec.angelic_list.
    Proof.
      intros w ι Hpc msg ts vs [].
      - now apply refine_error.
      - now apply refine_angelic_list'.
    Qed.

    Lemma refine_demonic_list' `{R : Rel AT A} :
      ℛ⟦R -> RList R -> RPureSpec R⟧
        SPureSpec.demonic_list' CPureSpec.demonic_list'.
    Proof.
      intros w ι Hpc t v Htv ts vs Htvs. revert t v Htv.
      induction Htvs; cbn; intros ?t ?v ?Htv.
      - now apply refine_pure.
      - apply refine_demonic_binary; auto.
        now apply refine_pure.
    Qed.

    Lemma refine_demonic_list `{R : Rel AT A} :
      ℛ⟦RList R -> RPureSpec R⟧
        SPureSpec.demonic_list CPureSpec.demonic_list.
    Proof.
      intros w ι Hpc ts vs [].
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
        (CPureSpecM.angelic_pattern_match pat).
    Proof.
      intros w ι Hpc msg t v ->.
      unfold SPureSpec.angelic_pattern_match'.
      unfold CPureSpecM.angelic_pattern_match, CPureSpec.purespecm,
        CPureSpec.angelic_pattern_match.
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
    Arguments refine_angelic_pattern_match' {N} n {σ} pat.

    Lemma refine_demonic_pattern_match' {N : Set} (n : N -> LVar)
      {σ} (pat : @Pattern N σ) :
      ℛ⟦RVal σ -> RPureSpec (RMatchResult pat)⟧
        (SPureSpec.demonic_pattern_match' n pat)
        (CPureSpecM.demonic_pattern_match pat).
    Proof.
      intros w ι Hpc t v ->.
      unfold SPureSpec.demonic_pattern_match'.
      unfold CPureSpecM.demonic_pattern_match, CPureSpec.purespecm,
        CPureSpec.demonic_pattern_match.
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
    Arguments refine_demonic_pattern_match' {N} n {σ} pat.

    Transparent RPureSpec.

    Lemma refine_angelic_pattern_match {N : Set} (n : N -> LVar)
      {σ} (pat : @Pattern N σ) :
      ℛ⟦RMsg _ (RVal σ -> RPureSpec (RMatchResult pat))⟧
        (SPureSpecM.angelic_pattern_match n pat)
        (CPureSpecM.angelic_pattern_match pat).
    Proof.
      unfold SPureSpecM.angelic_pattern_match,
        SPureSpec.purespecm.
      induction pat; cbn - [Val]; intros w ι Hpc.
      - intros msg t v ->.
        intros POST__s POST__c HPOST. hnf.
        rewrite CPureSpec.wp_angelic_pattern_match.
        apply HPOST; cbn; rewrite ?inst_sub_id; auto.
        now exists eq_refl.
      - intros msg t v ->.
        destruct (term_get_val_spec t); subst.
        + intros POST__s POST__c HPOST. hnf.
          rewrite CPureSpec.wp_angelic_pattern_match; cbn.
          apply HPOST; cbn; rewrite ?inst_sub_id; auto.
          now exists eq_refl.
        + now apply (refine_angelic_pattern_match' n pat_bool).
      - apply (refine_angelic_pattern_match' n (pat_list σ x y)); auto.
      - intros msg t v ->.
        destruct (term_get_pair_spec t) as [[tl tr] Heq|]; subst.
        + rewrite Heq. intros POST__s POST__c HPOST. hnf.
          rewrite CPureSpec.wp_angelic_pattern_match. cbn.
          apply HPOST; cbn; rewrite ?inst_sub_id; auto.
          now exists eq_refl.
        + now apply (refine_angelic_pattern_match' n (pat_pair _ _)); auto.
      - intros msg t v ->.
        destruct (term_get_sum_spec t) as [[tl|tr] Heq|]; subst.
        + rewrite Heq. intros POST__s POST__c HPOST. hnf.
          rewrite CPureSpec.wp_angelic_pattern_match. cbn.
          apply HPOST; cbn; rewrite ?inst_sub_id; auto.
          now exists eq_refl.
        + rewrite Heq. intros POST__s POST__c HPOST. hnf.
          rewrite CPureSpec.wp_angelic_pattern_match. cbn.
          apply HPOST; cbn; rewrite ?inst_sub_id; auto.
          now exists eq_refl.
        + now apply (refine_angelic_pattern_match' n (pat_sum _ _ _ _)); auto.
      - intros msg t v ->.
        intros POST__s POST__c HPOST. hnf.
        rewrite CPureSpec.wp_angelic_pattern_match.
        apply HPOST; cbn; rewrite ?inst_sub_id; auto.
        now exists eq_refl.
      - intros msg t v ->.
        destruct (term_get_val_spec t); subst.
        + intros POST__s POST__c HPOST. hnf.
          rewrite CPureSpec.wp_angelic_pattern_match. cbn.
          apply HPOST; cbn; rewrite ?inst_sub_id; auto.
          now exists eq_refl.
        + now apply (refine_angelic_pattern_match' n (pat_enum E)); auto.
      - apply (refine_angelic_pattern_match' n (pat_bvec_split _ _ x y)); auto.
      - intros msg t v ->.
        destruct (term_get_val_spec t); subst.
        + intros POST__s POST__c HPOST. hnf.
          rewrite CPureSpec.wp_angelic_pattern_match. cbn.
          apply HPOST; cbn; rewrite ?inst_sub_id; auto.
          now exists eq_refl.
        + now apply (refine_angelic_pattern_match' n (pat_bvec_exhaustive m)); auto.
      - apply (refine_angelic_pattern_match' n (pat_tuple p)); auto.
      - intros msg t v ->.
        destruct (term_get_record_spec t) as [ts Heq|]; subst.
        + rewrite Heq. intros POST__s POST__c HPOST. hnf.
          rewrite CPureSpec.wp_angelic_pattern_match. cbn.
          apply HPOST; cbn; rewrite ?inst_sub_id; auto.
          exists eq_refl. cbn.
          unfold record_pattern_match_val.
          rewrite recordv_unfold_fold.
          symmetry. apply inst_record_pattern_match.
        + now apply (refine_angelic_pattern_match' n (pat_record _ _ _)); auto.
      - intros msg t v ->.
        destruct (term_get_union_spec t) as [[K scr'] Heq|]; subst.
        + rewrite Heq. intros POST__s POST__c HPOST. hnf.
          specialize (H K w ι Hpc msg scr' (inst scr' ι) eq_refl).
          intros Hwp. eapply H in Hwp; eauto. revert Hwp. cbn.
          Unshelve.
          3: {
            intros [pc δpc]. apply POST__c. now exists (existT K pc).
          }
          * rewrite ?CPureSpec.wp_angelic_pattern_match. cbn.
            rewrite unionv_unfold_fold.
            now destruct pattern_match_val; cbn.
          * intros ? ? ? ? ? [] [] [e Hmr]. apply HPOST; auto.
            rewrite H0. rewrite sub_acc_trans; cbn.
            now rewrite inst_subst, inst_sub_id.
            subst. now exists eq_refl.
        + now apply (refine_angelic_pattern_match' n (pat_union _ _)); auto.
    Qed.

    Lemma refine_demonic_pattern_match {N : Set} (n : N -> LVar)
      {σ} (pat : @Pattern N σ) :
      ℛ⟦RVal σ -> RPureSpec (RMatchResult pat)⟧
        (SPureSpecM.demonic_pattern_match n pat)
        (CPureSpecM.demonic_pattern_match pat).
    Proof.
      induction pat; cbn; intros w ι Hpc.
      - intros t v ->.
        intros POST__s POST__c HPOST. hnf.
        rewrite CPureSpec.wp_demonic_pattern_match.
        apply HPOST; cbn; rewrite ?inst_sub_id; auto.
        now exists eq_refl.
      - intros t v ->.
        destruct (term_get_val_spec t); subst.
        + intros POST__s POST__c HPOST. hnf.
          rewrite CPureSpec.wp_demonic_pattern_match; cbn.
          apply HPOST; cbn; rewrite ?inst_sub_id; auto.
          now exists eq_refl.
        + now apply (refine_demonic_pattern_match' n pat_bool).
      - apply (refine_demonic_pattern_match' n (pat_list σ x y)); auto.
      - intros t v ->.
        destruct (term_get_pair_spec t) as [[tl tr] Heq|]; subst.
        + rewrite Heq. intros POST__s POST__c HPOST. hnf.
          rewrite CPureSpec.wp_demonic_pattern_match. cbn.
          apply HPOST; cbn; rewrite ?inst_sub_id; auto.
          now exists eq_refl.
        + now apply (refine_demonic_pattern_match' n (pat_pair _ _)); auto.
      - intros t v ->.
        destruct (term_get_sum_spec t) as [[tl|tr] Heq|]; subst.
        + rewrite Heq. intros POST__s POST__c HPOST. hnf.
          rewrite CPureSpec.wp_demonic_pattern_match. cbn.
          apply HPOST; cbn; rewrite ?inst_sub_id; auto.
          now exists eq_refl.
        + rewrite Heq. intros POST__s POST__c HPOST. hnf.
          rewrite CPureSpec.wp_demonic_pattern_match. cbn.
          apply HPOST; cbn; rewrite ?inst_sub_id; auto.
          now exists eq_refl.
        + now apply (refine_demonic_pattern_match' n (pat_sum _ _ _ _)); auto.
      - intros t v ->.
        intros POST__s POST__c HPOST. hnf.
        rewrite CPureSpec.wp_demonic_pattern_match.
        apply HPOST; cbn; rewrite ?inst_sub_id; auto.
        now exists eq_refl.
      - intros t v ->.
        destruct (term_get_val_spec t); subst.
        + intros POST__s POST__c HPOST. hnf.
          rewrite CPureSpec.wp_demonic_pattern_match. cbn.
          apply HPOST; cbn; rewrite ?inst_sub_id; auto.
          now exists eq_refl.
        + now apply (refine_demonic_pattern_match' n (pat_enum E)); auto.
      - apply (refine_demonic_pattern_match' n (pat_bvec_split _ _ x y)); auto.
      - intros t v ->.
        destruct (term_get_val_spec t); subst.
        + intros POST__s POST__c HPOST. hnf.
          rewrite CPureSpec.wp_demonic_pattern_match. cbn.
          apply HPOST; cbn; rewrite ?inst_sub_id; auto.
          now exists eq_refl.
        + now apply (refine_demonic_pattern_match' n (pat_bvec_exhaustive m)); auto.
      - apply (refine_demonic_pattern_match' n (pat_tuple p)); auto.
      - intros t v ->.
        destruct (term_get_record_spec t) as [ts Heq|]; subst.
        + rewrite Heq. intros POST__s POST__c HPOST. hnf.
          rewrite CPureSpec.wp_demonic_pattern_match. cbn.
          apply HPOST; cbn; rewrite ?inst_sub_id; auto.
          exists eq_refl. cbn.
          unfold record_pattern_match_val.
          rewrite recordv_unfold_fold.
          symmetry. apply inst_record_pattern_match.
        + now apply (refine_demonic_pattern_match' n (pat_record _ _ _)); auto.
      - intros t v ->.
        destruct (term_get_union_spec t) as [[K scr'] Heq|]; subst.
        + rewrite Heq. intros POST__s POST__c HPOST. hnf.
          specialize (H K w ι Hpc scr' (inst scr' ι) eq_refl).
          intros Hwp. eapply H in Hwp; eauto. revert Hwp. cbn.
          Unshelve.
          3: {
            intros [pc δpc]. apply POST__c. now exists (existT K pc).
          }
          * rewrite ?CPureSpec.wp_demonic_pattern_match. cbn.
            rewrite unionv_unfold_fold.
            now destruct pattern_match_val; cbn.
          * intros ? ? ? ? ? [] [] [e Hmr]. apply HPOST; auto.
            rewrite H0. rewrite sub_acc_trans; cbn.
            now rewrite inst_subst, inst_sub_id.
            subst. now exists eq_refl.
        + now apply (refine_demonic_pattern_match' n (pat_union _ _)); auto.
    Qed.

    (* Lemma refine_pattern_match_regular {N : Set} (n : N -> LVar) {σ} (p : @Pattern N σ) : *)
    (*   ℛ⟦RVal σ -> RPureSpec (RMatchResult p)⟧ *)
    (*     (SPureSpecM.pattern_match_regular n p) *)
    (*     (CPureSpecM.pattern_match p). *)
    (* Proof. *)
    (*   cbv beta delta [RPureSpec SPureSpecM.pattern_match_regular *)
    (*                     CPureSpecM.pattern_match CPureSpecM.pure] iota. *)
    (*   intros w ι Hpc t v -> POST__s POST__c HPOST. hnf. cbn beta delta [wsafe] iota. *)
    (*   rewrite <- (pattern_match_val_freshen n p (Σ := w)). *)
    (*   pose proof (pattern_match_val_inverse_left (freshen_pattern n w p) (inst t ι)). *)
    (*   destruct pattern_match_val as [pc vs]. cbn - [acc_trans]. *)
    (*   unfold pattern_match_val_reverse' in H. cbn in H. *)
    (*   intros Hsafe. refine (HPOST _ _ _ _ _ _ _ _ Hsafe); clear Hsafe; *)
    (*     cbn - [sub_cat_left sub_cat_right sub_id]; *)
    (*     rewrite ?inst_subst, ?instprop_subst, ?inst_sub_id, ?inst_sub_cat_left; try easy. *)
    (*   - rewrite inst_pattern_match_term_reverse. split; auto. rewrite <- H. *)
    (*     f_equal. symmetry. apply inst_sub_cat_right. *)
    (*   - exists eq_refl; cbn. rewrite inst_unfreshen_patterncaseenv. *)
    (*     f_equal. symmetry. apply inst_sub_cat_right. *)
    (* Qed. *)

    (* Lemma refine_pattern_match_var {N : Set} (n : N -> LVar) {σ} (p : @Pattern N σ) : *)
    (*   ℛ⟦∀ x, RIn (x∷σ) -> RPureSpec (RMatchResult p)⟧ *)
    (*     (SPureSpecM.pattern_match_var n p) *)
    (*     (fun x => CPureSpecM.pattern_match p). *)
    (* Proof. *)
    (* Admitted. *)

    (* Lemma refine_pattern_match_basic {N : Set} (n : N -> LVar) {σ} (p : @Pattern N σ) : *)
    (*   ℛ⟦RVal σ -> RPureSpec (RMatchResult p)⟧ *)
    (*     (SPureSpecM.pattern_match_basic n p) *)
    (*     (CPureSpecM.pattern_match p). *)
    (* Proof. *)
    (*   intros w ι HCι t v Htv. destruct t; cbn. *)
    (*   now apply refine_pattern_match_var. *)
    (*   all: now apply refine_pattern_match_regular. *)
    (* Qed. *)

    (* Lemma refine_pattern_match {N : Set} (n : N -> LVar) {σ} (p : @Pattern N σ) : *)
    (*   ℛ⟦RVal σ -> RPureSpec (RMatchResult p)⟧ *)
    (*     (SPureSpecM.pattern_match n p) *)
    (*     (CPureSpecM.pattern_match p). *)
    (* Proof. *)
    (*   induction p; intros w ι HCι t v ->; cbn [SPureSpecM.pattern_match]. *)
    (*   - apply refine_pure; auto. exists eq_refl; cbn; auto. *)
    (*   - destruct (term_get_val_spec t) as [? ->|]; cbn. *)
    (*     + apply refine_pure; auto. exists eq_refl; cbn; auto. *)
    (*     + now apply refine_pattern_match_basic with (p := pat_bool). *)
    (*   - now apply refine_pattern_match_basic. *)
    (*   - destruct (term_get_pair_spec t) as [[t1 t2] ->|]; cbn. *)
    (*     + apply refine_pure; auto. exists eq_refl; cbn; auto. *)
    (*     + now apply refine_pattern_match_basic with (p := pat_pair _ _). *)
    (*   - destruct (term_get_sum_spec t) as [[] ->|]; cbn. *)
    (*     + apply refine_pure; auto. exists eq_refl; cbn; auto. *)
    (*     + apply refine_pure; auto. exists eq_refl; cbn; auto. *)
    (*     + now apply refine_pattern_match_basic with (p := pat_sum _ _ _ _). *)
    (*   - apply refine_pure; auto. exists eq_refl; cbn; auto. *)
    (*   - destruct (term_get_val_spec t) as [? ->|]; cbn. *)
    (*     + apply refine_pure; auto. exists eq_refl; cbn; auto. *)
    (*     + now apply refine_pattern_match_basic with (p := pat_enum E). *)
    (*   - now apply refine_pattern_match_basic. *)
    (*   - destruct (term_get_val_spec t) as [? ->|]; cbn. *)
    (*     + apply refine_pure; auto. exists eq_refl; cbn; auto. *)
    (*     + now apply refine_pattern_match_basic with (p := pat_bvec_exhaustive m). *)
    (*   - destruct (term_get_tuple_spec t) as [ts ->|]. *)
    (*     + apply refine_pure; auto. exists eq_refl; cbn; auto. *)
    (*       unfold tuple_pattern_match_val. *)
    (*       now rewrite envrec.to_of_env, inst_tuple_pattern_match. *)
    (*     + now apply refine_pattern_match_basic. *)
    (*   - destruct (term_get_record_spec t) as [ts ->|]. *)
    (*     + apply refine_pure; auto. exists eq_refl; cbn; auto. *)
    (*       unfold record_pattern_match_val. *)
    (*       rewrite recordv_unfold_fold. symmetry. *)
    (*       apply inst_record_pattern_match. *)
    (*     + now apply refine_pattern_match_basic. *)
    (*   - destruct (term_get_union_spec t) as [[K tf] Heq|]. *)
    (*     + specialize (H K w ι HCι tf (inst tf ι) eq_refl). *)
    (*       change (base.equiv t (term_union U K tf)) in Heq. *)
    (*       admit. *)
    (*     + now apply refine_pattern_match_basic. *)
    (* Admitted. *)

    (* Lemma refine_debug {AT A} `{R : Rel AT A} *)
    (*   {Γ} {w0 : World} (ι0 : Valuation w0) *)
    (*       (Hpc : instprop (wco w0) ι0) f ms mc : *)
    (*   ℛ⟦RMsg _ (RPureSpec R -> RPureSpec R)⟧@{ι0} ms mc -> *)
    (*   ℛ⟦RPureSpec R⟧@{ι0} (@SPureSpecM.debug AT w0 msg ms) mc. *)
    (* Proof. *)
    (*   intros Hap POST__s POST__c HPOST δs0 δc0 Hδ0 hs0 hc0 Hh0. *)
    (*   intros [HP]. revert HP. apply Hap; auto. *)
    (* Qed. *)

  End PureSpec.

  #[export] Instance RHeap : Rel SHeap SCHeap :=
    RInst SHeap SCHeap.

  #[export] Instance RHeapSpec {AT A} (R : Rel AT A) :
    Rel (SHeapSpec AT) (CHeapSpec A) := □(R -> RHeap -> ℙ) -> RHeap -> ℙ.

  Module HeapSpec.

    Lemma refine_run :
      ℛ⟦RHeapSpec RUnit -> ℙ⟧ SHeapSpec.run CHeapSpec.run.
    Proof.
      unfold RPureSpec, RHeapSpec.
      unfold SHeapSpec.run, CHeapSpec.run.
      intros w ι Hpc ms mc Hm.
      apply Hm; easy.
    Qed.

    Lemma refine_lift_purespec `{R : Rel AT A} :
      ℛ⟦RPureSpec R -> RHeapSpec R⟧
        SHeapSpec.lift_purespec CHeapSpec.lift_purespec.
    Proof.
      unfold RPureSpec, RHeapSpec.
      unfold SHeapSpec.lift_purespec, CHeapSpec.lift_purespec.
      intros w ι Hpc ms mc Hm POST__s POST__c HPOST.
      intros hs hc Hh. apply Hm.
      intros w1 r01 ι1 Hι1 Hpc1 a1 a Ha.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      eapply refine_inst_persist; eauto.
    Qed.

    Lemma refine_bind `{RA : Rel AT A, RB : Rel BT B} :
      forall (w : World) (ι : Valuation w),
        ℛ⟦RHeapSpec RA -> □(RA -> RHeapSpec RB) -> RHeapSpec RB⟧@{ι}
          (SHeapSpec.bind (w := w)) CHeapSpec.bind.
    Proof.
      intros w ι ms mc Hm fs fc Hf POST__s POST__c HPOST hs hc Hh.
      apply Hm; eauto. intros w1 r01 ι1 Hι1 Hpc1 t v Htv.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      eapply refine_four; eauto.
    Qed.

    Lemma refine_bind' `{RA : Rel AT A, RB : Rel BT B} :
      ℛ⟦RHeapSpec RA -> □(RA -> RHeapSpec RB) -> RHeapSpec RB⟧
        SHeapSpec.bind CHeapSpec.bind.
    Proof. intros ? ? _. apply refine_bind. Qed.

    Lemma refine_angelic_binary {AT A} `{R : Rel AT A} :
      ℛ⟦RHeapSpec R -> RHeapSpec R -> RHeapSpec R⟧
        SPureSpecM.angelic_binary CHeapSpec.angelic_binary.
    Proof.
      intros w ι Hpc ms1 mc1 Hm1 ms2 mc2 Hm2.
      intros POST__s POST__c HPOST hs0 hc0 Hh0.
      unfold SPureSpecM.angelic_binary, SHeapSpec.purespecm,
        SHeapSpec.angelic_binary, CHeapSpec.angelic_binary.
      apply refine_symprop_angelic_binary; auto.
      apply Hm1; auto. apply Hm2; auto.
    Qed.

    Lemma refine_demonic_binary {AT A} `{R : Rel AT A} :
      ℛ⟦RHeapSpec R -> RHeapSpec R -> RHeapSpec R⟧
        SPureSpecM.demonic_binary CHeapSpec.demonic_binary.
    Proof.
      intros w ι Hpc ms1 mc1 Hm1 ms2 mc2 Hm2.
      intros POST__s POST__c HPOST hs0 hc0 Hh0.
      unfold SPureSpecM.demonic_binary, SHeapSpec.purespecm,
        SHeapSpec.demonic_binary, CHeapSpec.demonic_binary.
      apply refine_symprop_demonic_binary; auto.
      apply Hm1; auto. apply Hm2; auto.
    Qed.

    Lemma refine_pure `{R : Rel AT A} :
      ℛ⟦R -> RHeapSpec R⟧ SPureSpecM.pure CPureSpecM.pure.
    Proof.
      unfold SPureSpecM.pure, SHeapSpec.purespecm.
      unfold CPureSpecM.pure, CHeapSpec.purespecm.
      intros w ι Hpc t v Htv.
      apply refine_lift_purespec; auto.
      now apply PureSpec.refine_pure.
    Qed.

    Lemma refine_error `{RA : Rel AT A} :
      ℛ⟦RMsg (Box (Impl SHeap AMessage)) (RHeapSpec RA)⟧ SPureSpecM.error CPureSpecM.error.
    Proof.
      intros w ι Hpc m.
      apply refine_lift_purespec; auto.
      now apply PureSpec.refine_error.
    Qed.

    Lemma refine_debug {AT A} `{R : Rel AT A}
      {w0 : World} (ι0 : Valuation w0)
          (Hpc : instprop (wco w0) ι0) f ms mc :
      ℛ⟦RHeapSpec R⟧@{ι0} ms mc ->
      ℛ⟦RHeapSpec R⟧@{ι0} (@SHeapSpec.debug AT w0 f ms) mc.
    Proof.
      intros Hap POST__s POST__c HPOST hs0 hc0 Hh0.
      intros [HP]. revert HP. apply Hap; auto.
    Qed.

    Lemma refine_block  `{R : Rel AT A} :
      ℛ⟦RHeapSpec R⟧ (@SPureSpecM.block SHeapSpec _ AT) CPureSpecM.block.
    Proof. constructor. Qed.

    Lemma refine_angelic (x : option LVar) :
      ℛ⟦∀ σ, RHeapSpec (RVal σ)⟧ (SPureSpecM.angelic x) CPureSpecM.angelic.
    Proof.
      intros w ι Hpc σ.
      apply refine_lift_purespec; auto.
      now apply PureSpec.refine_angelic.
    Qed.

    Lemma refine_demonic (x : option LVar) :
      ℛ⟦∀ σ, RHeapSpec (RVal σ)⟧ (SPureSpecM.demonic x) CPureSpecM.demonic.
    Proof.
      intros w ι Hpc σ.
      apply refine_lift_purespec; auto.
      now apply PureSpec.refine_demonic.
    Qed.

    Lemma refine_angelic_ctx {N : Set} {n : N -> LVar} :
      ℛ⟦∀ Δ, RHeapSpec (RNEnv Δ)⟧
        (SPureSpecM.angelic_ctx n) CPureSpecM.angelic_ctx.
    Proof.
      intros w ι Hpc Δ.
      apply refine_lift_purespec; auto.
      now apply PureSpec.refine_angelic_ctx.
    Qed.

    Lemma refine_demonic_ctx {N : Set} {n : N -> LVar} :
      ℛ⟦∀ Δ, RHeapSpec (RNEnv Δ)⟧
        (SPureSpecM.demonic_ctx n) CPureSpecM.demonic_ctx.
    Proof.
      intros w ι Hpc Δ.
      apply refine_lift_purespec; auto.
      now apply PureSpec.refine_demonic_ctx.
    Qed.

    Lemma refine_assert_pathcondition :
      ℛ⟦RMsg _ (RPathCondition -> RHeapSpec RUnit)⟧
        SPureSpecM.assert_pathcondition CPureSpecM.assert_formula.
    Proof.
      intros w ι Hpc msg Ps ps Hps.
      apply refine_lift_purespec; auto.
      now apply PureSpec.refine_assert_pathcondition.
    Qed.

    Lemma refine_assert_formula :
      ℛ⟦RMsg _ (RFormula -> RHeapSpec RUnit)⟧
        SPureSpecM.assert_formula CPureSpecM.assert_formula.
    Proof.
      intros w ι Hpc msg P p Hp.
      apply refine_lift_purespec; auto.
      now apply PureSpec.refine_assert_formula.
    Qed.

    Lemma refine_assume_pathcondition :
      ℛ⟦RPathCondition -> RHeapSpec RUnit⟧
        SPureSpecM.assume_pathcondition CPureSpecM.assume_formula.
    Proof.
      intros w ι Hpc P p Hp.
      apply refine_lift_purespec; auto.
      now apply PureSpec.refine_assume_pathcondition.
    Qed.

    Lemma refine_assume_formula :
      ℛ⟦RFormula -> RHeapSpec RUnit⟧
        SPureSpecM.assume_formula CPureSpecM.assume_formula.
    Proof.
      intros w ι Hpc P p Hp.
      apply refine_lift_purespec; auto.
      now apply PureSpec.refine_assume_formula.
    Qed.

    Lemma refine_angelic_pattern_match {N : Set} (n : N -> LVar)
      {σ} (pat : @Pattern N σ) :
      ℛ⟦RMsg _ (RVal σ -> RHeapSpec (RMatchResult pat))⟧
        (SPureSpecM.angelic_pattern_match n pat)
        (CPureSpecM.angelic_pattern_match pat).
    Proof.
      intros w ι Hpc msg t v Htv.
      apply refine_lift_purespec; auto.
      now apply PureSpec.refine_angelic_pattern_match.
    Qed.

    Lemma refine_demonic_pattern_match {N : Set} (n : N -> LVar)
      {σ} (pat : @Pattern N σ) :
      ℛ⟦RVal σ -> RHeapSpec (RMatchResult pat)⟧
        (SPureSpecM.demonic_pattern_match n pat)
        (CPureSpecM.demonic_pattern_match pat).
    Proof.
      intros w ι Hpc t v Htv.
      apply refine_lift_purespec; auto.
      now apply PureSpec.refine_demonic_pattern_match.
    Qed.

    Lemma refine_get_heap :
      ℛ⟦RHeapSpec RHeap⟧ SHeapSpec.get_heap CHeapSpec.get_heap.
    Proof.
      intros w ι Hpc POST__s POST__c HPOST hs0 hc0 Hh0.
      unfold SHeapSpec.get_heap, CHeapSpec.get_heap.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      apply refine_T; eauto.
    Qed.

    Lemma refine_put_heap :
      ℛ⟦RHeap -> RHeapSpec RUnit⟧ SHeapSpec.put_heap CHeapSpec.put_heap.
    Proof.
      intros w ι Hpc hs hc Hh POST__s POST__c HPOST hs0 hc0 Hh0.
      unfold SHeapSpec.put_heap, CHeapSpec.put_heap.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      apply refine_T; eauto.
      reflexivity.
    Qed.

    Lemma refine_produce_chunk :
      ℛ⟦RChunk -> RHeapSpec RUnit⟧ SHeapSpecM.produce_chunk CHeapSpecM.produce_chunk.
    Proof.
      intros w ι Hpc cs cc -> POST__s POST__c HPOST hs0 hc0 Hh0.
      unfold SHeapSpecM.produce_chunk, SHeapSpec.heapspecm, SHeapSpec.produce_chunk.
      unfold CHeapSpecM.produce_chunk, CHeapSpec.heapspecm, CHeapSpec.produce_chunk.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      apply refine_T; eauto.
      reflexivity.
      cbn. rewrite peval_chunk_sound. now f_equal.
    Qed.

    Lemma try_consume_chunk_exact_spec {Σ} (h : SHeap Σ) (c : Chunk Σ) :
      option.wlp
        (fun h' => List.In (c , h') (heap_extractions h))
        (SHeapSpec.try_consume_chunk_exact h c).
    Proof.
      induction h as [|c' h].
      - now constructor.
      - cbn -[is_duplicable].
        destruct (chunk_eqb_spec c c').
        + constructor. left. subst.
          remember (is_duplicable c') as dup.
          destruct dup; reflexivity.
        + apply option.wlp_map. revert IHh.
          apply option.wlp_monotonic; auto.
          intros h' HIn. right.
          rewrite List.in_map_iff.
          exists (c,h'). auto.
    Qed.

    Lemma inst_is_duplicable {w : World} (c : Chunk w) (ι : Valuation w) :
      is_duplicable (inst c ι) = is_duplicable c.
    Proof.
      destruct c; now cbn.
    Qed.

    Lemma inst_eq_rect {I} {T : I -> LCtx -> Type} {A : I -> Type}
      {instTA : forall i, Inst (T i) (A i)} (i j : I) (e : j = i) :
      forall Σ (t : T j Σ) (ι : Valuation Σ),
        inst (eq_rect j (fun i => T i Σ) t i e) ι =
          eq_rect j A (inst t ι) i e.
    Proof. now destruct e. Qed.

    Lemma inst_eq_rect_r {I} {T : I -> LCtx -> Type} {A : I -> Type}
      {instTA : forall i, Inst (T i) (A i)} (i j : I) (e : i = j) :
      forall Σ (t : T j Σ) (ι : Valuation Σ),
        inst (eq_rect_r (fun i => T i Σ) t e) ι = eq_rect_r A (inst t ι) e.
    Proof. now destruct e. Qed.

    Lemma find_chunk_user_precise_spec {Σ p ΔI ΔO} (prec : 𝑯_Ty p = ΔI ▻▻ ΔO) (tsI : Env (Term Σ) ΔI) (tsO : Env (Term Σ) ΔO) (h : SHeap Σ) :
      option.wlp
        (fun '(h', eqs) =>
           forall ι : Valuation Σ,
             instprop eqs ι ->
             List.In
               (inst (chunk_user p (eq_rect_r (fun c : Ctx Ty => Env (Term Σ) c) (tsI ►► tsO) prec)) ι, inst h' ι)
               (heap_extractions (inst h ι)))
        (SHeapSpec.find_chunk_user_precise prec tsI tsO h).
    Proof.
      induction h as [|c h]; [now constructor|]. cbn [SHeapSpec.find_chunk_user_precise].
      destruct SHeapSpec.match_chunk_user_precise as [eqs|] eqn:?.
      - clear IHh. constructor. intros ι Heqs. left.
        destruct c; try discriminate Heqo. cbn in *.
        destruct (eq_dec p p0); cbn in Heqo; try discriminate Heqo. destruct e.
        remember (eq_rect (𝑯_Ty p) (Env (Term Σ)) ts (ΔI ▻▻ ΔO) prec) as ts'.
        destruct (env.catView ts') as [tsI' tsO'].
        destruct (env.eqb_hom_spec Term_eqb (@Term_eqb_spec Σ) tsI tsI'); try discriminate.
        apply noConfusion_inv in Heqo. cbn in Heqo. subst.
        apply instprop_formula_eqs_ctx in Heqs.
        rewrite (@inst_eq_rect_r (Ctx Ty) (fun Δ Σ => Env (Term Σ) Δ) (Env Val)).
        rewrite inst_env_cat. rewrite Heqs. rewrite <- inst_env_cat.
        change (env.cat ?A ?B) with (env.cat A B). rewrite Heqts'.
        rewrite (@inst_eq_rect (Ctx Ty) (fun Δ Σ => Env (Term Σ) Δ) (Env Val)).
        rewrite rew_opp_l. now destruct is_duplicable.
      - apply option.wlp_map. revert IHh. apply option.wlp_monotonic; auto.
        intros [h' eqs] HYP ι Heqs. specialize (HYP ι Heqs).
        remember (inst (chunk_user p (eq_rect_r (fun c0 : Ctx Ty => Env (Term Σ) c0) (tsI ►► tsO) prec)) ι) as c'.
        change (inst (cons c h) ι) with (cons (inst c ι) (inst h ι)).
        cbn [fst heap_extractions]. right. apply List.in_map_iff.
        eexists (c', inst h' ι); auto.
    Qed.

    Lemma find_chunk_ptsreg_precise_spec {Σ σ} (r : 𝑹𝑬𝑮 σ) (t : Term Σ σ) (h : SHeap Σ) :
      option.wlp
        (fun '(h', eqs) =>
           forall ι : Valuation Σ,
             instprop eqs ι ->
             List.In
               (inst (chunk_ptsreg r t) ι, inst h' ι)
               (heap_extractions (inst h ι)))
        (SHeapSpec.find_chunk_ptsreg_precise r t h).
    Proof.
      induction h; cbn [SHeapSpec.find_chunk_ptsreg_precise]; [now constructor|].
      destruct SHeapSpec.match_chunk_ptsreg_precise eqn:?.
      - constructor. intros ι [Hpc Hf]. clear IHh.
        destruct a; cbn in Heqo; try discriminate Heqo.
        destruct (eq_dec_het r r0); try discriminate Heqo.
        dependent elimination e. cbn in Heqo. dependent elimination Heqo.
        change (inst (cons ?c ?h) ι) with (cons (inst c ι) (inst h ι)).
        cbn. left. f_equal. f_equal. symmetry. exact Hf.
      - apply option.wlp_map. revert IHh. apply option.wlp_monotonic; auto.
        intros [h' eqs] HYP ι Heqs. specialize (HYP ι Heqs).
        remember (inst (chunk_ptsreg r t) ι) as c'.
        change (inst (cons ?c ?h) ι) with (cons (inst c ι) (inst h ι)).
        cbn [fst heap_extractions]. right. apply List.in_map_iff.
        eexists (c', inst h' ι); auto.
    Qed.

    Lemma refine_consume_chunk :
      ℛ⟦RChunk -> RHeapSpec RUnit⟧
        SHeapSpecM.consume_chunk CHeapSpecM.consume_chunk.
    Proof.
      intros w0 ι0 Hpc0 cs cc ->.
      unfold SHeapSpecM.consume_chunk, SHeapSpec.heapspecm, SHeapSpec.consume_chunk.
      unfold CHeapSpecM.consume_chunk, CHeapSpec.heapspecm, CHeapSpec.consume_chunk.
      apply refine_bind; auto.
      apply refine_get_heap; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros hs hc ->.
      remember (peval_chunk (persist cs ω01)) as c1.
      destruct (try_consume_chunk_exact_spec hs c1) as [h' HIn|].
      { intros POST__s POST__c HPOST.
        intros hs' hc' ->.
        cbn. intros Hwp.
        rewrite CPureSpec.wp_angelic_list.
        change (SHeap w1) in h'.
        exists (inst c1 ι1, inst h' ι1).
        split.
        - unfold inst at 3, inst_heap, inst_list.
          rewrite heap_extractions_map, List.in_map_iff.
          + exists (c1 , h'). split. reflexivity. assumption.
          + eauto using inst_is_duplicable.
        - cbn. rewrite CPureSpec.wp_assert_eq_chunk. subst.
          rewrite peval_chunk_sound, inst_persist.
          split; auto. revert Hwp.
          apply HPOST; wsimpl; auto; reflexivity.
      }
      destruct (SHeapSpec.try_consume_chunk_precise hs c1) as [[h' eqs]|] eqn:?.
      { intros POST__s POST__c HPOST.
        intros hs' hc' Hh'.
        cbn. intros Hwp.
        eapply (refine_assert_pathcondition Hpc1) in Hwp; eauto.
        2: cbn; reflexivity.
        2: cbn; reflexivity.
        destruct Hwp as [Heqs HPOST1].
        rewrite CPureSpec.wp_angelic_list.
        destruct c1; cbn in Heqo; try discriminate Heqo; cbn.
        - destruct (𝑯_precise p) as [[ΔI ΔO prec]|]; try discriminate Heqo.
          remember (eq_rect (𝑯_Ty p) (Env (Term w1)) ts (ΔI ▻▻ ΔO) prec) as ts'.
          destruct (env.catView ts') as [tsI tsO].
          destruct (find_chunk_user_precise_spec prec tsI tsO hs) as [[h'' eqs''] HIn|];
            inversion Heqo; subst; clear Heqo.
          specialize (HIn ι1 Heqs). rewrite Heqts' in HIn.
          rewrite rew_opp_l in HIn. rewrite Heqc1 in HIn.
          rewrite peval_chunk_sound in HIn.
          eexists; split; eauto. clear HIn.
          hnf. rewrite CPureSpec.wp_assert_eq_chunk.
          split; auto. now rewrite <- inst_persist.
        - destruct (find_chunk_ptsreg_precise_spec r t hs) as [[h'' eqs''] HIn|];
            inversion Heqo; subst; clear Heqo.
          specialize (HIn ι1 Heqs). rewrite Heqc1 in HIn.
          rewrite peval_chunk_sound in HIn.
          eexists; split; eauto. clear HIn.
          hnf. rewrite CPureSpec.wp_assert_eq_chunk.
          split; auto. now rewrite <- inst_persist.
      }
      { intros POST__s POST__c HPOST.
        intros hs' hc' ? [].
      }
    Qed.

    Lemma refine_consume_chunk_angelic :
      ℛ⟦RChunk -> RHeapSpec RUnit⟧
        SHeapSpec.consume_chunk_angelic CHeapSpecM.consume_chunk.
    Proof.
      intros w0 ι0 Hpc0 cs cc ->.
      unfold SHeapSpec.consume_chunk_angelic, CHeapSpecM.consume_chunk.
      apply refine_bind; auto.
      apply refine_get_heap; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros hs hc ->.
      remember (peval_chunk (persist cs ω01)) as c1.
      destruct (try_consume_chunk_exact_spec hs c1) as [h' HIn|].
      { intros POST__s POST__c HPOST.
        intros hs' hc' ->.
        intros Hwp. cbn.
        rewrite CPureSpec.wp_angelic_list.
        change (SHeap w1) in h'.
        exists (inst c1 ι1, inst h' ι1).
        split.
        - unfold inst at 3, inst_heap, inst_list.
          rewrite heap_extractions_map, List.in_map_iff.
          + exists (c1 , h'). split. reflexivity. assumption.
          + eauto using inst_is_duplicable.
        - hnf. subst. rewrite peval_chunk_sound, inst_persist.
          rewrite CPureSpec.wp_assert_eq_chunk.
          split; auto. revert Hwp. apply HPOST; wsimpl; auto; reflexivity.
      }
      destruct (SHeapSpec.try_consume_chunk_precise hs c1) as [[h' eqs]|] eqn:?.
      { intros POST__s POST__c HPOST.
        intros hs' hc' ->. cbn. intros Hwp.
        eapply (refine_assert_pathcondition Hpc1) in Hwp; eauto.
        2: cbn; reflexivity.
        2: cbn; reflexivity.
        destruct Hwp as [Heqs HPOST1].
        rewrite CPureSpec.wp_angelic_list.
        destruct c1; cbn in Heqo; try discriminate Heqo; cbn.
        - destruct (𝑯_precise p) as [[ΔI ΔO prec]|]; try discriminate Heqo.
          remember (eq_rect (𝑯_Ty p) (Env (Term w1)) ts (ΔI ▻▻ ΔO) prec) as ts'.
          destruct (env.catView ts') as [tsI tsO].
          destruct (find_chunk_user_precise_spec prec tsI tsO hs) as [[h'' eqs''] HIn|];
            inversion Heqo; subst; clear Heqo.
          specialize (HIn ι1 Heqs). rewrite Heqts' in HIn.
          rewrite rew_opp_l in HIn. rewrite Heqc1 in HIn.
          rewrite peval_chunk_sound in HIn.
          eexists; split; eauto. clear HIn.
          hnf. rewrite CPureSpec.wp_assert_eq_chunk.
          split; auto. now rewrite <- inst_persist.
        - destruct (find_chunk_ptsreg_precise_spec r t hs) as [[h'' eqs''] HIn|];
            inversion Heqo; subst.
          specialize (HIn ι1 Heqs). rewrite Heqc1 in HIn.
          rewrite peval_chunk_sound in HIn.
          eexists; split; eauto. clear HIn.
          hnf. rewrite CPureSpec.wp_assert_eq_chunk.
          split; auto. now rewrite <- inst_persist.
      }
      { apply refine_bind; auto.
        apply refine_lift_purespec; auto.
        apply PureSpec.refine_angelic_list; auto.
        { hnf. unfold inst at 1, inst_heap, inst_list.
          rewrite heap_extractions_map.
          { clear. induction (heap_extractions hs) as [|[]];
              cbn; constructor; cbn; auto. }
          eauto using inst_is_duplicable.
        }
        clear Heqo.
        intros w2 ω12 ι2 -> Hpc2.
        intros [cs' hs'] [cc' hc']. intros Hch'.
        inversion Hch'; subst; clear Hch'.
        apply refine_bind; auto.
        - apply refine_lift_purespec; auto.
          eapply PureSpec.refine_assert_eq_chunk; cbn; eauto.
          now rewrite inst_persist, peval_chunk_sound, inst_persist.
          now rewrite inst_sub_id.
        - intros w3 ω23 ι3 -> Hpc3 _ _ _.
          apply refine_put_heap; auto.
          eapply refine_inst_persist; eauto.
      }
    Qed.

    #[export] Instance RPureSpec {AT A} (R : Rel AT A) :
      Rel (SPureSpec AT) (CPureSpec A) := □(R -> ℙ) -> ℙ.

    Lemma refine_produce {Σ0} (asn : Assertion Σ0) : Prop.
      Search CReaderT.

        ℛ⟦□(RHeapSpec RUnit)⟧@{ι0}
          (produce (w:=w0) asn)
          (cproduce asn ι0).
    Proof.
      induction asn; intros w0 * Hpc; cbn - [RSat wctx Val].
      - now apply refine_box_assume_formula.
      - intros w1 ω01 ι1 -> Hpc1.
        apply refine_produce_chunk; auto.
        eapply refine_inst_persist; auto.
        reflexivity.
      - intros w1 ω01 ι1 -> Hpc1.
        apply refine_produce_chunk; auto.
        eapply refine_inst_persist; auto.
        reflexivity.
      - intros w1 ω01 ι1 -> Hpc1.
        apply refine_bind; eauto.
        apply refine_lift_purespec; eauto.
        apply PureSpec.refine_demonic_pattern_match; eauto.
        eapply refine_inst_persist; auto.
        reflexivity.
        intros w2 ω12 ι2 -> Hpc2.
        intros [] [pc] [Heq1 Heq2]. subst. cbn in Heq2. subst.
        apply H; cbn - [Sub inst sub_wk1 sub_id sub_cat_left]; wsimpl; auto.
        { rewrite <- !inst_subst.
          unfold NamedEnv.
          fold (@inst_sub (PatternCaseCtx pc)).
          fold (Sub (PatternCaseCtx pc)).
          rewrite <- inst_sub_cat.
          rewrite <- instprop_subst.
          rewrite <- subst_sub_comp.
          rewrite sub_comp_cat_left.
          now rewrite instprop_subst, inst_subst.
        }
        now rewrite inst_sub_cat, inst_subst.
      - intros w1 ω01 ι1 -> Hpc1.
        apply refine_bind.
        apply IHasn1; auto.
        intros ? ? ? -> ? _ _ _.
        apply IHasn2; auto.
        rewrite ?inst_sub_snoc, ?sub_acc_trans, ?inst_subst, ?inst_sub_wk1; eauto.
      - intros w1 ω01 ι1 -> Hpc1.
        apply refine_demonic_binary;
          try apply IHasn1; try apply IHasn2;
          cbn - [inst sub_wk1];
          rewrite ?inst_sub_snoc, ?sub_acc_trans, ?inst_subst, ?inst_sub_wk1; eauto.
      - intros w1 ω01 ι1 -> Hpc1.
        apply refine_bind.
        apply refine_demonic; auto.
        intros w2 ω02 ι2 -> Hpc2. intros t v ->.
        apply IHasn; cbn - [inst sub_wk1];
          rewrite ?inst_sub_snoc, ?sub_acc_trans, ?instprop_subst, ?inst_subst, ?inst_sub_wk1; eauto.
      - intros w1 ω01 ι1 -> Hpc1.
        apply refine_debug; auto.
        apply refine_pure; auto.
        reflexivity.
    Qed.

    Lemma refine_consume {Σ0 pc0} (asn : Assertion Σ0) :
      let w0 := @MkWorld Σ0 pc0 in
      forall
        (ι0 : Valuation w0)
        (Hpc0 : instprop (wco w0) ι0),
        ℛ⟦□(RHeapSpec RUnit)⟧@{ι0}
          (SHeapSpecM.consume (w := w0) asn) (CHeapSpecM.consume asn ι0 ).
    Proof.
      induction asn; intros w0 * Hpc; cbn - [RSat wctx Val].
      - now apply refine_box_assert_formula.
      - intros w1 ω01 ι1 -> Hpc1.
        apply refine_consume_chunk; auto.
        eapply refine_inst_persist; auto.
        reflexivity.
      - intros w1 ω01 ι1 -> Hpc1.
        apply refine_consume_chunk_angelic; auto.
        eapply refine_inst_persist; auto.
        reflexivity.
      - intros w1 ω01 ι1 -> Hpc1.
        apply refine_bind; eauto.
        apply refine_lift_purespec; eauto.
        apply PureSpec.refine_angelic_pattern_match; eauto.
        eapply refine_inst_persist; auto.
        reflexivity.
        intros w2 ω12 ι2 -> Hpc2.
        intros [] [pc] [Heq1 Heq2]. subst. cbn in Heq2. subst.
        apply H; cbn - [Sub inst sub_wk1 sub_id sub_cat_left]; wsimpl; auto.
        { rewrite <- !inst_subst.
          unfold NamedEnv.
          fold (@inst_sub (PatternCaseCtx pc)).
          fold (Sub (PatternCaseCtx pc)).
          rewrite <- inst_sub_cat.
          rewrite <- instprop_subst.
          rewrite <- subst_sub_comp.
          rewrite sub_comp_cat_left.
          now rewrite instprop_subst, inst_subst.
        }
        now rewrite inst_sub_cat, inst_subst.
      - intros w1 ω01 ι1 -> Hpc1.
        apply refine_bind.
        apply IHasn1; auto.
        intros ? ? ? -> ? _ _ _.
        apply IHasn2; auto.
        rewrite ?inst_sub_snoc, ?sub_acc_trans, ?inst_subst, ?inst_sub_wk1; eauto.
      - intros w1 ω01 ι1 -> Hpc1.
        apply refine_angelic_binary;
          try apply IHasn1; try apply IHasn2;
          cbn - [inst sub_wk1];
          rewrite ?inst_sub_snoc, ?sub_acc_trans, ?inst_subst, ?inst_sub_wk1; eauto.
      - intros w1 ω01 ι1 -> Hpc1.
        apply refine_bind; auto.
        apply refine_angelic; auto.
        intros w2 ω02 ι2 -> Hpc2. intros t v ->.
        apply IHasn; cbn - [inst sub_wk1];
          rewrite ?inst_sub_snoc, ?sub_acc_trans, ?instprop_subst, ?inst_subst, ?inst_sub_wk1; eauto.
      - intros w1 ω01 ι1 -> Hpc1.
        apply refine_debug; auto.
        apply refine_pure; auto.
        reflexivity.
    Qed.

  End HeapSpec.

End RefinementMonadInstancesOn.
