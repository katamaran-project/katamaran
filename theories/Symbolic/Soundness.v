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
     Program.Tactics
     ZArith.ZArith
     Strings.String
     Classes.Morphisms
     Classes.RelationClasses
     Classes.Morphisms_Prop
     Classes.Morphisms_Relations.
Require Import Basics.

From Coq Require Lists.List.

From Equations Require Import
     Equations.

From Katamaran Require Import
     Signature
     Shallow.Executor
     Specification
     Symbolic.Executor
     Program
     Tactics.

Set Implicit Arguments.

Import ctx.notations.
Import env.notations.

Module Soundness
  (Import B    : Base)
  (Import SIG  : Signature B)
  (Import PROG : Program B)
  (Import SPEC : Specification B SIG PROG)
  (Import SHAL : ShallowExecOn B SIG PROG SPEC)
  (Import SYMB : SymbolicExecOn B SIG PROG SPEC).

  Import ModalNotations.
  Import SymProp.
  Import logicalrelation logicalrelation.notations.

  Section Basics.

    #[export] Instance RStore (Γ : PCtx) : Rel (SStore Γ) (CStore Γ) :=
      RInst (SStore Γ) (CStore Γ).

    #[export] Instance RStoreSpec Γ1 Γ2 `(R : Rel AT A) :
      Rel (SStoreSpec Γ1 Γ2 AT) (CStoreSpec Γ1 Γ2 A) :=
      □(R -> RStore Γ2 -> RHeap -> ℙ) -> RStore Γ1 -> RHeap -> ℙ.

    Lemma refine_lift_purem {Γ} `{R : Rel AT A} :
      ℛ⟦RPureSpec R -> RStoreSpec Γ Γ R⟧
        SStoreSpec.lift_purem CStoreSpec.lift_purem.
    Proof.
      unfold RPureSpec, RStoreSpec, SStoreSpec.lift_purem, CStoreSpec.lift_purem.
      intros w ι Hpc ms mc Hm POST__s POST__c HPOST.
      intros δs δc Hδ hs hc Hh. apply Hm.
      intros w1 r01 ι1 Hι1 Hpc1 a1 a Ha.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      eapply refine_inst_persist; eauto.
      eapply refine_inst_persist; eauto.
    Qed.

    Lemma refine_block {Γ1 Γ2} `{R : Rel AT A} :
      ℛ⟦RStoreSpec Γ1 Γ2 R⟧ SStoreSpec.block CStoreSpec.block.
    Proof. constructor. Qed.

    Lemma refine_error `{Subst M, OccursCheck M, R : Rel AT A} {Γ1 Γ2} :
      forall (cm : CStoreSpec Γ1 Γ2 A),
        ℛ⟦RMsg _ (RStoreSpec Γ1 Γ2 R)⟧ SStoreSpec.error cm.
    Proof. intros cm w ι Hpc msg POST__s POST__c HPOST δs δc Hδ hs hc Hh []. Qed.

    Lemma refine_pure `{R : Rel AT A} {Γ} :
      ℛ⟦R -> RStoreSpec Γ Γ R⟧ SStoreSpec.pure CStoreSpec.pure.
    Proof.
      unfold SStoreSpec.pure, CStoreSpec.pure.
      intros w ι Hpc t v Htv POST__s POST__c HPOST.
      eapply refine_apply; eauto.
      eapply refine_T; eauto.
    Qed.

    Lemma refine_bind `{RA : Rel AT A, RB : Rel BT B} {Γ1 Γ2 Γ3} :
      forall (w : World) (ι : Valuation w),
        ℛ⟦RStoreSpec Γ1 Γ2 RA -> □(RA -> RStoreSpec Γ2 Γ3 RB) -> RStoreSpec Γ1 Γ3 RB⟧@{ι}
          (SStoreSpec.bind (w := w)) CStoreSpec.bind.
    Proof.
      unfold SStoreSpec.bind, CStoreSpec.bind.
      intros w ι ms mc Hm fs fc Hf POST__s POST__c HPOST δs δc Hδ hs hc Hh.
      apply Hm; eauto. intros w1 r01 ι1 Hι1 Hpc1 t v Htv.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      eapply refine_four; eauto.
    Qed.

    Lemma refine_bind' `{RA : Rel AT A, RB : Rel BT B} {Γ1 Γ2 Γ3} :
      ℛ⟦RStoreSpec Γ1 Γ2 RA -> □(RA -> RStoreSpec Γ2 Γ3 RB) -> RStoreSpec Γ1 Γ3 RB⟧
        SStoreSpec.bind CStoreSpec.bind.
    Proof. intros ? ? _. apply refine_bind. Qed.

    Lemma refine_angelic (x : option LVar) {Γ} :
      ℛ⟦∀ σ, RStoreSpec Γ Γ (RVal σ)⟧ (SStoreSpec.angelic x) CStoreSpec.angelic.
    Proof.
      unfold SStoreSpec.angelic, CStoreSpec.angelic.
      intros w ι Hpc σ. apply refine_lift_purem; auto.
      apply RPureSpec.refine_angelic; auto.
    Qed.

    Lemma refine_demonic (x : option LVar) {Γ} :
      ℛ⟦∀ σ, RStoreSpec Γ Γ (RVal σ)⟧ (SStoreSpec.demonic x) CStoreSpec.demonic.
    Proof.
      unfold SStoreSpec.demonic, CStoreSpec.demonic.
      intros w ι Hpc σ. apply refine_lift_purem; auto.
      apply RPureSpec.refine_demonic; auto.
    Qed.

    Lemma refine_angelic_ctx {N : Set} {n : N -> LVar} {Γ} :
      ℛ⟦∀ Δ, RStoreSpec Γ Γ (RNEnv Δ)⟧
        (SStoreSpec.angelic_ctx n) CStoreSpec.angelic_ctx.
    Proof.
      unfold SStoreSpec.angelic_ctx, CStoreSpec.angelic_ctx.
      intros w ι Hpc Δ. apply refine_lift_purem; auto.
      apply RPureSpec.refine_angelic_ctx; auto.
    Qed.

    Lemma refine_demonic_ctx {N : Set} {n : N -> LVar} {Γ} :
      ℛ⟦∀ Δ, RStoreSpec Γ Γ (RNEnv Δ)⟧
        (SStoreSpec.demonic_ctx n) CStoreSpec.demonic_ctx.
    Proof.
      unfold SStoreSpec.demonic_ctx, CStoreSpec.demonic_ctx.
      intros w ι Hpc Δ. apply refine_lift_purem; auto.
      apply RPureSpec.refine_demonic_ctx; auto.
    Qed.

    Lemma refine_debug {AT A} `{R : Rel AT A}
      {Γ1 Γ2} {w0 : World} (ι0 : Valuation w0)
          (Hpc : instprop (wco w0) ι0) f ms mc :
      ℛ⟦RStoreSpec Γ1 Γ2 R⟧@{ι0} ms mc ->
      ℛ⟦RStoreSpec Γ1 Γ2 R⟧@{ι0} (@SStoreSpec.debug AT Γ1 Γ2 w0 f ms) mc.
    Proof.
      intros Hap POST__s POST__c HPOST δs0 δc0 Hδ0 hs0 hc0 Hh0.
      intros [HP]. revert HP. apply Hap; auto.
    Qed.

    Lemma refine_angelic_binary {AT A} `{R : Rel AT A} {Γ1 Γ2} :
      ℛ⟦RStoreSpec Γ1 Γ2 R -> RStoreSpec Γ1 Γ2 R -> RStoreSpec Γ1 Γ2 R⟧
        SStoreSpec.angelic_binary CStoreSpec.angelic_binary.
    Proof.
      intros w ι Hpc ms1 mc1 Hm1 ms2 mc2 Hm2.
      intros POST__s POST__c HPOST δs0 δc0 Hδ0 hs0 hc0 Hh0.
      unfold SStoreSpec.angelic_binary, CStoreSpec.angelic_binary.
      apply refine_symprop_angelic_binary; auto.
      apply Hm1; auto. apply Hm2; auto.
    Qed.

    Lemma refine_demonic_binary {AT A} `{R : Rel AT A} {Γ1 Γ2} :
      ℛ⟦RStoreSpec Γ1 Γ2 R -> RStoreSpec Γ1 Γ2 R -> RStoreSpec Γ1 Γ2 R⟧
        SStoreSpec.demonic_binary CStoreSpec.demonic_binary.
    Proof.
      intros w ι Hpc ms1 mc1 Hm1 ms2 mc2 Hm2.
      intros POST__s POST__c HPOST δs0 δc0 Hδ0 hs0 hc0 Hh0.
      unfold SStoreSpec.angelic_binary, CStoreSpec.angelic_binary.
      apply refine_symprop_demonic_binary; auto.
      apply Hm1; auto. apply Hm2; auto.
    Qed.

    Lemma refine_angelic_list `{Subst M, OccursCheck M, R : Rel AT A} {Γ} :
      ℛ⟦RMsg _ (RList R -> RStoreSpec Γ Γ R)⟧
        SStoreSpec.angelic_list CStoreSpec.angelic_list.
    Proof.
      intros w ι Hpc msg ls lc Hl.
      intros POST__s POST__c HPOST δs0 δc0 Hδ0 hs0 hc0 Hh0.
      unfold SStoreSpec.angelic_list, CStoreSpec.angelic_list.
      apply refine_lift_purem; auto.
      apply RPureSpec.refine_angelic_list; auto.
    Qed.

    Lemma refine_angelic_finite `{finite.Finite F} {Γ} :
      ℛ⟦RMsg _ (RStoreSpec Γ Γ (RConst F))⟧
        (@SStoreSpec.angelic_finite F _ _ Γ)
        (CStoreSpec.angelic_finite F).
    Proof.
      intros w ι Hpc msg.
      intros POST__s POST__c HPOST δs0 δc0 Hδ0 hs0 hc0 Hh0.
      unfold SStoreSpec.angelic_finite, CStoreSpec.angelic_finite.
      eapply refine_lift_purem; eauto.
      apply RPureSpec.refine_angelic_finite; auto.
    Qed.

  End Basics.

  Section AssumeAssert.

    Lemma refine_assume_formula {Γ} :
      ℛ⟦RFormula -> RStoreSpec Γ Γ RUnit⟧
        SStoreSpec.assume_formula CStoreSpec.assume_formula.
    Proof.
      unfold SStoreSpec.assume_formula, CStoreSpec.assume_formula.
      intros w ι Hpc P p Hp. apply refine_lift_purem; auto.
      apply RPureSpec.refine_assume_formula; auto.
    Qed.

    Lemma refine_box_assume_formula {Γ} :
      ℛ⟦RFormula -> □(RStoreSpec Γ Γ RUnit)⟧
        SStoreSpec.box_assume_formula CStoreSpec.assume_formula.
    Proof.
      unfold SStoreSpec.box_assume_formula, fmap_box.
      intros w0 ι0 Hpc0 P p Hp w1 r01 ι1 Hι1 Hpc1.
      apply refine_assume_formula; auto.
      eapply refine_formula_persist; eauto.
    Qed.

    Lemma refine_assert_formula {Γ} :
      ℛ⟦RFormula -> RStoreSpec Γ Γ RUnit⟧
        SStoreSpec.assert_formula CStoreSpec.assert_formula.
    Proof.
      intros w ι Hpc P p Hp.
      unfold SStoreSpec.assert_formula, CStoreSpec.assert_formula.
      intros POST__s POST__c HPOST δs δc Hδ hs hc Hh.
      apply refine_lift_purem; auto.
      now apply RPureSpec.refine_assert_formula.
    Qed.

    Lemma refine_box_assert_formula {Γ} :
      ℛ⟦RFormula -> □(RStoreSpec Γ Γ RUnit)⟧
        SStoreSpec.box_assert_formula CStoreSpec.assert_formula.
    Proof.
      unfold SStoreSpec.box_assert_formula, fmap_box.
      intros w0 ι0 Hpc0 P p Hp w1 r01 ι1 Hι1 Hpc1.
      apply refine_assert_formula; auto.
      eapply refine_formula_persist; eauto.
    Qed.

    Lemma refine_assert_pathcondition {Γ} :
      ℛ⟦RPathCondition -> RStoreSpec Γ Γ RUnit⟧
        SStoreSpec.assert_pathcondition CStoreSpec.assert_formula.
    Proof.
      intros w ι Hpc Ps ps Hps POST__s POST__c HPOST δs δc Hδ hs hc Hh.
      apply refine_lift_purem; auto.
      now apply RPureSpec.refine_assert_pathcondition.
    Qed.

    Lemma refine_assert_eq_nenv {N Γ} (Δ : NCtx N Ty) :
      ℛ⟦RNEnv Δ -> RNEnv Δ -> RStoreSpec Γ Γ RUnit⟧
        SStoreSpec.assert_eq_nenv CStoreSpec.assert_eq_nenv.
    Proof.
      intros w ι Hpc E1 ? ? E2 ? ? POST__s POST__c HPOST δs δc Hδ hs hc Hh.
      unfold SStoreSpec.assert_eq_nenv, CStoreSpec.assert_eq_nenv.
      apply refine_lift_purem; auto.
      apply RPureSpec.refine_assert_eq_nenv; auto.
    Qed.

    Lemma refine_assert_eq_chunk {Γ} :
      ℛ⟦RChunk -> RChunk -> RStoreSpec Γ Γ RUnit⟧
        SStoreSpec.assert_eq_chunk CStoreSpec.assert_eq_chunk.
    Proof.
      intros w ι Hpc c1 ? ? E2 ? ? POST__s POST__c HPOST δs δc Hδ hs hc Hh.
      unfold SStoreSpec.assert_eq_chunk, CStoreSpec.assert_eq_chunk.
      apply refine_lift_purem; auto. apply refine_T; auto.
      apply RPureSpec.refine_assert_eq_chunk; cbn; eauto.
    Qed.

  End AssumeAssert.

  Section PatternMatching.

    Lemma refine_angelic_pattern_match {N : Set} (n : N -> LVar) {Γ σ} (pat : @Pattern N σ) :
      ℛ⟦RVal σ -> RStoreSpec Γ Γ (RMatchResult pat)⟧
        (SStoreSpec.angelic_pattern_match n pat)
        (CStoreSpec.angelic_pattern_match pat).
    Proof.
      intros w ι Hpc sv cv rv sΦ cΦ rΦ sδ cδ rδ sh ch rh.
      unfold SStoreSpec.angelic_pattern_match, CStoreSpec.angelic_pattern_match, CStoreSpec.lift_purem.
      apply RPureSpec.refine_angelic_pattern_match; auto.
      intros w1 θ1 ι1 Heq1 Hpc1 smr cmr rmr. apply rΦ; auto.
      eapply refine_inst_persist; eauto.
      eapply refine_inst_persist; eauto.
    Qed.

    Lemma refine_demonic_pattern_match {N : Set} (n : N -> LVar) {Γ σ} (pat : @Pattern N σ) :
      ℛ⟦RVal σ -> RStoreSpec Γ Γ (RMatchResult pat)⟧
        (SStoreSpec.demonic_pattern_match n pat)
        (CStoreSpec.demonic_pattern_match pat).
    Proof.
      intros w ι Hpc sv cv rv sΦ cΦ rΦ sδ cδ rδ sh ch rh.
      unfold SStoreSpec.demonic_pattern_match, CStoreSpec.demonic_pattern_match, CStoreSpec.lift_purem.
      apply RPureSpec.refine_demonic_pattern_match; auto.
      intros w1 θ1 ι1 Heq1 Hpc1 smr cmr rmr. apply rΦ; auto.
      eapply refine_inst_persist; eauto.
      eapply refine_inst_persist; eauto.
    Qed.

  End PatternMatching.

  Section State.

    Lemma refine_pushpop `{R : Rel AT A} {Γ1 Γ2 x σ} :
      ℛ⟦RVal σ -> RStoreSpec (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) R -> RStoreSpec Γ1 Γ2 R⟧
        SStoreSpec.pushpop CStoreSpec.pushpop.
    Proof.
      intros w0 ι0 Hpc0 t v Htv ms mc Hm.
      unfold SStoreSpec.pushpop, CStoreSpec.pushpop.
      intros POST__s POST__c HPOST δs0 δc0 Hδ0 hs0 hc0 Hh0.
      apply Hm; eauto.
      - intros w1 r01 ι1 Hι1 Hpc1 a1 a Ha δs1 δc1 -> hs1 hc1 Hh1.
        apply HPOST; auto. now destruct (env.view δs1).
      - now apply refine_env_snoc.
    Qed.

    Lemma refine_pushspops `{R : Rel AT A} {Γ1 Γ2 Δ} :
      ℛ⟦RStore Δ -> RStoreSpec (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) R -> RStoreSpec Γ1 Γ2 R⟧
        SStoreSpec.pushspops CStoreSpec.pushspops.
    Proof.
      intros w0 ι0 Hpc0 ts vs -> ms mc Hm.
      intros POST__s POST__c HPOST δs0 δc0 -> hs0 hc0 Hh0.
      unfold SStoreSpec.pushspops, CStoreSpec.pushspops.
      apply Hm; auto.
      - intros w1 ω01 ι1 Hι1 Hpc1 a1 a Ha δs1 δc1 -> hs1 hc1 Hh1.
        apply HPOST; auto.
        destruct (env.catView δs1).
        unfold inst, inst_store, inst_env at 1.
        rewrite <- env.map_drop.
        rewrite ?env.drop_cat.
        reflexivity.
      - cbn.
        unfold inst, inst_store, inst_env at 3.
        now rewrite env.map_cat.
    Qed.

    Lemma refine_get_local {Γ} :
      ℛ⟦RStoreSpec Γ Γ (RStore Γ)⟧
        SStoreSpec.get_local CStoreSpec.get_local.
    Proof.
      intros w ι Hpc POST__s POST__c HPOST.
      intros δs0 δc0 Hδ hs0 hc0 Hh0.
      unfold SStoreSpec.get_local, CStoreSpec.get_local.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      apply refine_T; eauto.
    Qed.

    Lemma refine_put_local {Γ1 Γ2} :
      ℛ⟦RStore Γ2 -> RStoreSpec Γ1 Γ2 RUnit⟧
        SStoreSpec.put_local CStoreSpec.put_local.
    Proof.
      intros w ι Hpc δs2 δc2 Hδ2 POST__s POST__c HPOST.
      intros δs0 δc0 Hδ hs0 hc0 Hh0.
      unfold SStoreSpec.put_local, CStoreSpec.put_local.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      apply refine_T; eauto.
      reflexivity.
    Qed.

    Lemma refine_get_heap {Γ} :
      ℛ⟦RStoreSpec Γ Γ RHeap⟧ SStoreSpec.get_heap CStoreSpec.get_heap.
    Proof.
      intros w ι Hpc POST__s POST__c HPOST δs0 δc0 Hδ hs0 hc0 Hh0.
      unfold SStoreSpec.get_heap, CStoreSpec.get_heap.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      apply refine_T; eauto.
    Qed.

    Lemma refine_put_heap {Γ} :
      ℛ⟦RHeap -> RStoreSpec Γ Γ RUnit⟧ SStoreSpec.put_heap CStoreSpec.put_heap.
    Proof.
      intros w ι Hpc hs hc Hh POST__s POST__c HPOST δs0 δc0 Hδ hs0 hc0 Hh0.
      unfold SStoreSpec.put_heap, CStoreSpec.put_heap.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      apply refine_T; eauto.
      reflexivity.
    Qed.

    Lemma refine_peval {w : World} {ι : Valuation w} {σ} t v :
      ℛ⟦RVal σ⟧@{ι} t v -> ℛ⟦RVal σ⟧@{ι} (peval t) v.
    Proof. intros ->. symmetry. apply peval_sound. Qed.

    Lemma refine_eval_exp {Γ σ} (e : Exp Γ σ) :
      ℛ⟦RStoreSpec Γ Γ (RVal σ)⟧ (SStoreSpec.eval_exp e) (CStoreSpec.eval_exp e).
    Proof.
      intros w ι Hpc POST__s POST__c HPOST δs0 δc0 Hδ0 hs0 hc0 Hh.
      unfold SStoreSpec.eval_exp, CStoreSpec.eval_exp.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      apply refine_T; eauto.
      apply refine_peval.
      cbn. rewrite <- eval_exp_inst.
      f_equal. exact Hδ0.
    Qed.

    Lemma refine_eval_exps {Γ Δ} (es : NamedEnv (Exp Γ) Δ) :
      ℛ⟦RStoreSpec Γ Γ (RStore Δ)⟧
        (SStoreSpec.eval_exps es) (CStoreSpec.eval_exps es).
    Proof.
      intros w ι Hpc POST__s POST__c HPOST δs0 δc0 Hδ0 hs0 hc0 Hh.
      unfold SStoreSpec.eval_exps, CStoreSpec.eval_exps.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      apply refine_T; eauto.
      apply env.lookup_extensional; cbn; intros [x σ] xIn.
      unfold evals, inst, inst_store, inst_env. rewrite ?env.lookup_map.
      symmetry. etransitivity. apply peval_sound.
      rewrite <- eval_exp_inst. f_equal. symmetry. exact Hδ0.
    Qed.

    Lemma refine_env_update {Γ x σ} (xIn : x∷σ ∈ Γ) (w : World) (ι : Valuation w)
      (t : Term w σ) (v : Val σ) (Htv : ℛ⟦RVal σ⟧@{ι} t v)
      (δs : SStore Γ w) (δc : CStore Γ) (Hδ : ℛ⟦RStore Γ⟧@{ι} δs δc) :
      ℛ⟦RStore Γ⟧@{ι} (δs ⟪ x ↦ t ⟫) (δc ⟪ x ↦ v ⟫).
    Proof.
      cbn in *. subst.
      unfold inst, inst_store, inst_env.
      now rewrite env.map_update.
    Qed.

    Lemma refine_assign {Γ x σ} {xIn : x∷σ ∈ Γ} :
      ℛ⟦RVal σ -> RStoreSpec Γ Γ RUnit⟧
        (SStoreSpec.assign x) (CStoreSpec.assign x).
    Proof.
      intros w ι Hpc t v Htv POST__s POST__c HPOST δs0 δc0 Hδ0 hs0 hc0 Hh.
      unfold SStoreSpec.assign, CStoreSpec.assign.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      apply refine_T; eauto.
      reflexivity.
      now apply refine_env_update.
    Qed.

  End State.

  Lemma refine_produce_chunk {Γ} {w0 : World} (ι0 : Valuation w0)
    (Hpc0 : instprop (wco w0) ι0) :
    ℛ⟦_⟧@{ι0} (@SStoreSpec.produce_chunk Γ w0) (CStoreSpec.produce_chunk).
  Proof.
    intros cs cc ->.
    intros POST__s POST__c HPOST.
    intros δs δc -> hs hc ->.
    unfold SStoreSpec.produce_chunk, CStoreSpec.produce_chunk.
    apply HPOST; cbn; rewrite ?inst_sub_id; auto.
    hnf. cbn. now rewrite peval_chunk_sound.
  Qed.

  Local Hint Unfold RSat : core.
  Local Hint Unfold RInst : core.

  Lemma refine_produce {Γ Σ0 pc0} (asn : Assertion Σ0) :
    let w0 := @MkWorld Σ0 pc0 in
    forall
      (ι0 : Valuation w0)
      (Hpc0 : instprop (wco w0) ι0),
      ℛ⟦□(RStoreSpec Γ Γ RUnit)⟧@{ι0} (@SStoreSpec.produce Γ w0 asn) (CStoreSpec.produce ι0 asn).
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
      apply refine_bind.
      apply refine_demonic_pattern_match; eauto.
      eapply refine_inst_persist; auto.
      reflexivity.
      intros w2 ω12 ι2 -> Hpc2.
      intros [? ?] [pc vs] [-> ->].
      apply H; cbn - [Sub inst sub_wk1 sub_id sub_cat_left]; wsimpl; auto.
      { rewrite <- ?inst_subst.
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

  Lemma try_consume_chunk_exact_spec {Σ} (h : SHeap Σ) (c : Chunk Σ) :
    option.wlp
      (fun h' => List.In (c , h') (heap_extractions h))
      (SStoreSpec.try_consume_chunk_exact h c).
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

  Lemma find_chunk_user_precise_spec {Σ p ΔI ΔO} (prec : 𝑯_Ty p = ΔI ▻▻ ΔO) (tsI : Env (Term Σ) ΔI) (tsO : Env (Term Σ) ΔO) (h : SHeap Σ) :
    option.wlp
      (fun '(h', eqs) =>
         forall ι : Valuation Σ, instprop eqs ι ->
           List.In
             (inst (chunk_user p (eq_rect_r (fun c : Ctx Ty => Env (Term Σ) c) (tsI ►► tsO) prec)) ι, inst h' ι)
             (heap_extractions (inst h ι)))
      (SStoreSpec.find_chunk_user_precise prec tsI tsO h).
  Proof.
    induction h as [|c h]; [now constructor|]. cbn [SStoreSpec.find_chunk_user_precise].
    destruct SStoreSpec.match_chunk_user_precise as [eqs|] eqn:?.
    - clear IHh. constructor. intros ι Heqs. left.
      destruct c; try discriminate Heqo. cbn in *.
      destruct (eq_dec p p0); cbn in Heqo; try discriminate Heqo. destruct e.
      remember (eq_rect (𝑯_Ty p) (Env (Term Σ)) ts (ΔI ▻▻ ΔO) prec) as ts'.
      destruct (env.catView ts') as [tsI' tsO'].
      destruct (env.eqb_hom_spec Term_eqb (@Term_eqb_spec Σ) tsI tsI'); try discriminate.
      apply noConfusion_inv in Heqo. cbn in Heqo. subst.
      apply instprop_formula_eqs_ctx in Heqs.
      rewrite (@inst_eq_rect_indexed_r (Ctx Ty) (fun Δ Σ => Env (Term Σ) Δ) (Env Val)).
      rewrite inst_env_cat. rewrite Heqs. rewrite <- inst_env_cat.
      change (env.cat ?A ?B) with (env.cat A B). rewrite Heqts'.
      rewrite (@inst_eq_rect_indexed (Ctx Ty) (fun Δ Σ => Env (Term Σ) Δ) (Env Val)).
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
         forall ι : Valuation Σ, instprop eqs ι ->
           List.In
             (inst (chunk_ptsreg r t) ι, inst h' ι)
             (heap_extractions (inst h ι)))
      (SStoreSpec.find_chunk_ptsreg_precise r t h).
  Proof.
    induction h; cbn [SStoreSpec.find_chunk_ptsreg_precise]; [now constructor|].
    destruct SStoreSpec.match_chunk_ptsreg_precise eqn:?.
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

  Lemma refine_consume_chunk {Γ} :
    ℛ⟦RChunk -> RStoreSpec Γ Γ RUnit⟧
      SStoreSpec.consume_chunk CStoreSpec.consume_chunk.
  Proof.
    intros w0 ι0 Hpc0 cs cc ->.
    unfold SStoreSpec.consume_chunk, CStoreSpec.consume_chunk.
    apply refine_bind; auto.
    apply refine_get_heap; auto.
    intros w1 ω01 ι1 -> Hpc1.
    intros hs hc ->.
    remember (peval_chunk (persist cs ω01)) as c1.
    destruct (try_consume_chunk_exact_spec hs c1) as [h' HIn|].
    { intros POST__s POST__c HPOST.
      intros δs δc -> hs' hc' ->.
      cbn. intros Hwp.
      cbv [CStoreSpec.assert_formula CStoreSpec.assert_eq_chunk CStoreSpec.bind
           SStoreSpec.put_heap CStoreSpec.put_heap T
           CStoreSpec.angelic_list CStoreSpec.lift_purem ].
      rewrite CPureSpec.wp_angelic_list.
      change (SHeap w1) in h'.
      exists (inst c1 ι1, inst h' ι1).
      split.
      - unfold inst at 3, inst_heap, inst_list.
        rewrite heap_extractions_map, List.in_map_iff.
        + exists (c1 , h'). split. reflexivity. assumption.
        + eauto using inst_is_duplicable.
      - rewrite CPureSpec.wp_assert_eq_chunk. subst.
        rewrite peval_chunk_sound, inst_persist.
        split; auto. revert Hwp.
        apply HPOST; wsimpl; auto; reflexivity.
    }
    destruct (SStoreSpec.try_consume_chunk_precise hs c1) as [[h' eqs]|] eqn:?.
    { intros POST__s POST__c HPOST.
      intros δs δc Hδ hs' hc' Hh'.
      cbv [SStoreSpec.put_heap SStoreSpec.bind T]. cbn. intros Hwp.
      eapply (refine_assert_pathcondition Hpc1 (ta := eqs)) in Hwp; eauto.
      2: cbn; reflexivity.
      2: cbn; reflexivity.
      destruct Hwp as [Heqs HPOST1].
      cbv [CStoreSpec.bind CStoreSpec.put_heap CStoreSpec.assert_formula
           T CStoreSpec.angelic_list CStoreSpec.lift_purem].
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
      intros δs δc ? hs' hc' ? [].
    }
  Qed.

  Lemma refine_consume_chunk_angelic {Γ} :
    ℛ⟦RChunk -> RStoreSpec Γ Γ RUnit⟧
      SStoreSpec.consume_chunk_angelic CStoreSpec.consume_chunk.
  Proof.
    intros w0 ι0 Hpc0 cs cc ->.
    unfold SStoreSpec.consume_chunk_angelic, CStoreSpec.consume_chunk.
    apply refine_bind; auto.
    apply refine_get_heap; auto.
    intros w1 ω01 ι1 -> Hpc1.
    intros hs hc ->.
    remember (peval_chunk (persist cs ω01)) as c1.
    destruct (try_consume_chunk_exact_spec hs c1) as [h' HIn|].
    { intros POST__s POST__c HPOST.
      intros δs δc -> hs' hc' ->.
      cbv [SStoreSpec.put_heap CStoreSpec.bind CStoreSpec.put_heap CStoreSpec.assert_formula
                         T CStoreSpec.angelic_list CStoreSpec.lift_purem].
      intros Hwp.
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
    destruct (SStoreSpec.try_consume_chunk_precise hs c1) as [[h' eqs]|] eqn:?.
    { intros POST__s POST__c HPOST.
      intros δs δc -> hs' hc' ->.
      cbv [SStoreSpec.put_heap T]. cbn. intros Hwp.
      eapply (refine_assert_pathcondition Hpc1) in Hwp; eauto.
      2: cbn; reflexivity.
      2: cbn; reflexivity.
      2: cbn; reflexivity.
      destruct Hwp as [Heqs HPOST1].
      cbv [CStoreSpec.bind CStoreSpec.put_heap CStoreSpec.assert_formula
           T CStoreSpec.angelic_list CStoreSpec.lift_purem].
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
      apply refine_angelic_list; auto.
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
      - apply refine_assert_eq_chunk; auto. hnf.
        now rewrite peval_chunk_sound, inst_persist, sub_acc_trans, inst_subst.
      - intros w3 ω23 ι3 -> Hpc3 _ _ _.
        apply refine_put_heap; auto.
        eapply refine_inst_persist; eauto.
    }
  Qed.

  Lemma refine_consume {Γ Σ0 pc0} (asn : Assertion Σ0) :
    let w0 := @MkWorld Σ0 pc0 in
    forall
      (ι0 : Valuation w0)
      (Hpc0 : instprop (wco w0) ι0),
      ℛ⟦□(RStoreSpec Γ Γ RUnit)⟧@{ι0}
        (@SStoreSpec.consume Γ w0 asn) (CStoreSpec.consume ι0 asn).
  Proof.
    induction asn; intros w0 * Hpc; cbn - [RSat wctx Val].
    - now apply refine_box_assert_formula.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      now apply refine_consume_chunk.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      now apply refine_consume_chunk_angelic.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply refine_bind.
      apply refine_angelic_pattern_match; eauto.
      cbn. reflexivity.
      intros w2 ω12 ι2 -> Hpc2.
      intros [? ?] [pc vs] [-> ->].
      apply H; cbn - [Sub inst sub_wk1 sub_id sub_cat_left]; wsimpl; auto.
      { rewrite <- ?inst_subst.
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

  Lemma refine_call_contract {Γ Δ τ} (c : SepContract Δ τ) :
    ℛ⟦RStore Δ -> RStoreSpec Γ Γ (RVal τ)⟧
      (SStoreSpec.call_contract c) (CStoreSpec.call_contract c).
  Proof.
    intros w0 ι0 Hpc0 args__s args__c Hargs.
    destruct c; cbv [SStoreSpec.call_contract CStoreSpec.call_contract].
    apply refine_bind; auto.
    apply refine_angelic_ctx; auto.
    intros w1 ω01 ι1 -> Hpc1 evars__s evars__c Hevars.
    apply refine_bind; auto.
    { apply refine_assert_eq_nenv; auto; hnf.
      now rewrite -> Hevars, inst_subst.
      now rewrite -> Hargs, inst_persist.
    }
    intros w2 ω12 ι2 -> Hpc2 _ _ _.
    apply refine_bind; auto.
    { apply refine_consume; wsimpl; auto.
      constructor.
    }
    intros w3 ω23 ι3 -> Hpc3 _ _ _.
    apply refine_bind; auto.
    { apply refine_demonic; auto. }
    intros w4 ω34 ι4 -> Hpc4.
    intros res__s res__c Hres.
    apply refine_bind; auto.
    { apply refine_produce; auto.
      constructor.
      cbn - [inst_env sub_snoc].
      rewrite inst_sub_snoc, inst_persist, ?sub_acc_trans, ?inst_subst.
      now rewrite Hevars, Hres.
    }
    intros w5 ω45 ι5 -> Hpc5 _ _ _.
    apply refine_pure; auto.
    rewrite Hres. rewrite <- inst_persist.
    reflexivity.
  Qed.

  Lemma refine_call_lemma {Γ Δ : PCtx} (lem : Lemma Δ) :
    ℛ⟦RStore Δ -> RStoreSpec Γ Γ RUnit⟧
      (SStoreSpec.call_lemma lem) (CStoreSpec.call_lemma lem).
  Proof.
    destruct lem; cbv [SStoreSpec.call_lemma CStoreSpec.call_lemma].
    intros w0 ι0 Hpc0.
    intros args__s args__c Hargs.
    apply refine_bind; auto.
    apply refine_angelic_ctx; auto.
    intros w1 ω01 ι1 -> Hpc1.
    intros evars__s evars__c Hevars.
    apply refine_bind; auto.
    { apply refine_assert_eq_nenv; auto; hnf.
      now rewrite Hevars, inst_subst.
      now rewrite Hargs, inst_persist.
    }
    intros w2 ω12 ι2 -> Hpc2 _ _ _.
    apply refine_bind; auto.
    { apply refine_consume; wsimpl; auto.
      constructor.
    }
    intros w3 ω23 ι3 -> Hpc3 _ _ _.
    { apply refine_produce; auto.
      constructor.
      cbn - [inst_env sub_snoc].
      rewrite inst_persist, sub_acc_trans, inst_subst.
      now rewrite Hevars.
    }
  Qed.

  Definition ExecRefine (sexec : SStoreSpec.Exec) (cexec : CStoreSpec.Exec) :=
    forall Γ τ (s : Stm Γ τ),
      ℛ⟦RStoreSpec Γ Γ (RVal τ)⟧ (@sexec Γ τ s) (cexec Γ τ s).

  Lemma refine_exec_aux {cfg} srec crec (HYP : ExecRefine srec crec) :
    ExecRefine (@SStoreSpec.exec_aux cfg srec) (@CStoreSpec.exec_aux crec).
  Proof.
    unfold ExecRefine.
    induction s; cbn; intros * w0 ι0 Hpc0.
    - apply refine_pure; auto. reflexivity.
    - now apply refine_eval_exp.
    - apply refine_bind; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v Htv.
      apply refine_pushpop; auto.
    - apply refine_pushspops; auto.
      apply refine_lift.
    - apply refine_bind; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v ->.
      apply refine_bind; auto.
      apply refine_assign; auto.
      reflexivity.
      intros w2 ω12 ι2 -> Hpc2 _ _ _.
      apply refine_pure; auto.
      hnf in H. now rewrite <- inst_persist in H.
    - apply refine_bind; auto.
      apply refine_eval_exps; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros args__s args__c Hargs.
      destruct (CEnv f).
      + unfold SStoreSpec.call_contract_debug.
        destruct (config_debug_function cfg f).
        apply refine_debug; auto.
        apply refine_call_contract; auto.
        apply refine_call_contract; auto.
      + intros POST__s POST__c HPOST.
        intros δs1 δc1 ->.
        apply HYP; auto.
        intros w2 ω12 ι2 -> Hpc2.
        intros t v ->.
        intros _ _ _.
        apply HPOST; auto.
        reflexivity.
        rewrite <- inst_persist.
        reflexivity.
    - apply refine_bind; auto.
      apply refine_get_local; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros δs1 δc1 ->.
      apply refine_bind; auto.
      apply refine_put_local; auto.
      apply refine_lift.
      intros w2 ω12 ι2 -> Hpc2 _ _ _.
      apply refine_bind; auto.
      intros w3 ω23 ι3 -> Hpc3.
      intros t v ->.
      apply refine_bind; auto.
      apply refine_put_local; auto.
      rewrite persist_subst.
      hnf. rewrite sub_acc_trans, ?inst_subst; auto.
      intros w4 ω34 ι4 -> Hpc4 _ _ _.
      apply refine_pure; auto.
      eapply refine_inst_persist; eauto.
      reflexivity.
    - apply refine_bind; auto.
      apply refine_eval_exps; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros args__s args__c Hargs.
      apply refine_call_contract; auto.
    - apply refine_bind; auto.
      apply refine_eval_exps; auto.
      intros w1 ω01 ι1 -> Hpc1 δΔ ? ?.
      apply refine_bind; auto.
      apply refine_call_lemma; auto.
      intros w2 ω12 ι2 -> Hpc2 _ _ _; auto.
    - apply refine_bind; auto.
      intros ? ? ? -> ? _ _ _; auto.
    - apply refine_bind; auto.
      apply (refine_eval_exp e1); auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v ->.
      apply refine_bind; auto.
      apply refine_assume_formula; auto.
      cbn. reflexivity.
      intros w2 ω12 ι2 -> Hpc2 _ _ _.
      now apply IHs.
    - apply refine_block; auto.
    - apply refine_bind; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v Htv.
      apply refine_bind; auto.
      apply refine_demonic_pattern_match; auto.
      intros w2 r12 ι2 -> Hpc2.
      intros [? ?] [pc vs] [-> ?].
      apply refine_pushspops; auto.
      apply H; auto.
    - apply refine_bind; auto.
      apply refine_angelic; auto.
      intros w1 ω01 ι1 -> Hpc1 t v Htv. hnf in Htv; subst.
      apply refine_bind; auto.
      apply refine_consume_chunk; auto.
      cbn. reflexivity.
      intros w2 ω12 ι2 -> Hpc2 _ _ _.
      apply refine_bind; auto.
      apply refine_produce_chunk; auto.
      rewrite <- inst_persist; auto.
      cbn. reflexivity.
      intros w3 ω23 ι3 -> Hpc3 _ _ _.
      apply refine_pure; auto.
      rewrite (persist_trans (A := STerm _)).
      now rewrite <- ?inst_persist.
    - apply refine_bind; auto.
      apply refine_angelic; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros told v ->.
      apply refine_bind; auto.
      apply refine_consume_chunk; auto.
      cbn. reflexivity.
      intros w2 ω12 ι2 -> Hpc2 _ _ _.
      apply refine_bind; auto.
      apply (refine_eval_exp e); auto.
      intros w3 ω23 ι3 -> Hpc3.
      intros tnew v Htnew. hnf in Htnew. subst v.
      apply refine_bind; auto.
      apply refine_produce_chunk; auto.
      cbn. reflexivity.
      intros w4 ω34 ι4 -> Hpc4 _ _ _.
      apply refine_pure; auto.
      now rewrite <- inst_persist.
    - apply refine_error; auto.
    - apply refine_debug; auto.
  Qed.

  Lemma refine_exec {cfg n} :
    ExecRefine (@SStoreSpec.exec cfg n) (@CStoreSpec.exec n).
  Proof.
    induction n; cbn.
    - unfold ExecRefine. intros Γ τ s w ι Hpc.
      apply refine_error; auto.
    - now apply refine_exec_aux.
  Qed.

  Lemma refine_exec_contract {cfg : Config} n {Γ τ} (c : SepContract Γ τ) (s : Stm Γ τ) :
    let w0 := {| wctx := sep_contract_logic_variables c; wco := ctx.nil |} in
    forall (ι0 : Valuation w0),
      ℛ⟦RStoreSpec Γ Γ RUnit⟧@{ι0}
        (SStoreSpec.exec_contract cfg n c s) (CStoreSpec.exec_contract n c s ι0).
  Proof.
    unfold SStoreSpec.exec_contract, CStoreSpec.exec_contract;
      destruct c as [Σ δ pre result post]; cbn - [RSat] in *.
    intros ι0.
    apply refine_bind.
    apply refine_produce; wsimpl; cbn; auto.
    intros w1 ω01 ι1 -> Hpc1 _ _ _.
    apply refine_bind; auto.
    apply refine_exec; auto.
    intros w2 ω12 ι2 -> Hpc2.
    intros res__s res__c Hres.
    apply refine_consume; cbn - [inst]; wsimpl; auto.
    f_equal; auto.
  Qed.

  Lemma refine_demonic_close {w : World} (P : 𝕊 w) (p : Valuation w -> Prop) :
    (forall (ι : Valuation w), ℛ⟦_⟧@{ι} P (p ι)) ->
    RSat RProp (w := wnil) env.nil (demonic_close P) (ForallNamed p).
  Proof.
    intros HYP Hwp. unfold ForallNamed.
    rewrite env.Forall_forall. intros ι.
    apply HYP. revert Hwp. clear.
    rewrite ?wsafe_safe, ?safe_debug_safe.
    intros Hwp. now apply safe_demonic_close.
  Qed.

  Lemma refine_vcgen {Γ τ} n (c : SepContract Γ τ) (body : Stm Γ τ) :
    RSat RProp (w := wnil) env.nil (SStoreSpec.vcgen default_config n c body) (CStoreSpec.vcgen n c body).
  Proof.
    unfold SStoreSpec.vcgen, CStoreSpec.vcgen.
    apply (refine_demonic_close
             (w := {| wctx := sep_contract_logic_variables c; wco := ctx.nil |})).
    intros ι.
    apply refine_exec_contract; auto.
    now intros w1 ω01 ι1 -> Hpc1.
    reflexivity.
    reflexivity.
  Qed.

  Lemma replay_sound {w : World} (s : 𝕊 w) ι (Hpc : instprop (wco w) ι) :
    safe (SPureSpec.replay s) ι -> safe s ι.
  Proof.
    intros H.
    apply CPureSpec.replay_sound, RPureSpec.refine_replay; auto.
    now rewrite wsafe_safe, safe_debug_safe.
  Qed.

  Lemma symbolic_vcgen_soundness {Γ τ} (c : SepContract Γ τ) (body : Stm Γ τ) :
    Symbolic.ValidContract c body ->
    Shallow.ValidContract c body.
  Proof.
    unfold Symbolic.ValidContract. intros [Hwp%postprocess_sound].
    apply (replay_sound (w:=wnil)) in Hwp; [|easy].
    apply postprocess_sound in Hwp. apply refine_vcgen.
    now rewrite wsafe_safe, safe_debug_safe.
  Qed.

  Lemma symbolic_vcgen_fuel_soundness {Γ τ} (fuel : nat) (c : SepContract Γ τ) (body : Stm Γ τ) :
    Symbolic.ValidContractWithFuel fuel c body ->
    Shallow.ValidContractWithFuel fuel c body.
  Proof.
    unfold Symbolic.ValidContractWithFuel. intros [Hwp%postprocess_sound].
    apply (replay_sound (w:=wnil)) in Hwp; [|easy].
    apply postprocess_sound in Hwp. apply refine_vcgen.
    now rewrite wsafe_safe, safe_debug_safe.
  Qed.

  (* Print Assumptions symbolic_vcgen_soundness. *)

End Soundness.

Module MakeSymbolicSoundness
  (Import B    : Base)
  (Import SIG  : Signature B)
  (Import PROG : Program B)
  (Import SPEC : Specification B SIG PROG)
  (Import SHAL : ShallowExecOn B SIG PROG SPEC)
  (Import SYMB : SymbolicExecOn B SIG PROG SPEC).

  Include Soundness B SIG PROG SPEC SHAL SYMB.
End MakeSymbolicSoundness.
