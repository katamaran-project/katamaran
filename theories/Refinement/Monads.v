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
     Classes.Morphisms_Prop.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Prelude
     Base
     Shallow.Monads
     Symbolic.Monads
     Symbolic.Propositions
     Symbolic.Solver
     Symbolic.UnifLogic
     Symbolic.Worlds
     Syntax.Assertions
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
  (Import UL : UnifLogicOn B PK WR)
  (Import LSP : LogSymPropOn B PK WR SP UL)
  (Import GS : GenericSolverOn B PK WR SK SP UL LSP)
  (Import AS : AssertionsOn B PK WR)
  (Import SHAL : ShallowMonadsOn B PK WR SP AS)
  (Import SYMB : SymbolicMonadsOn B PK WR SK SP UL LSP GS AS).

  Import ModalNotations.
  Import LogicalSoundness.
  Import SymProp.

  Import logicalrelation logicalrelation.notations proofmode.
  Import iris.bi.interface iris.proofmode.tactics.

  Definition RPureSpec [SA CA] (RA : Rel SA CA) :
    Rel (SPureSpec SA) (CPureSpec CA) := □ᵣ(RA -> ℙ) -> ℙ.

  Module PureSpec.

    Definition RPureSpec [SA CA] (RA : Rel SA CA) :
      Rel (SPureSpec SA) (CPureSpec CA) := □ᵣ(RA -> RProp) -> RProp.

    Lemma refine_run {w} :
      ⊢ ℛ⟦RPureSpec RUnit -> RProp ⟧ CPureSpec.run (SPureSpec.run (w := w)).
    Proof.
      iIntros (c cs) "Hc".
      unfold CPureSpec.run.
      iApply "Hc".
      now iIntros (w2 ω) "!> %k %K _".
    Qed.

    Lemma refine_pure `{RA : Rel SA CA} {w} :
      ⊢ ℛ⟦RA -> RPureSpec RA⟧ CPureSpec.pure (SPureSpec.pure (w := w)).
    Proof.
      iIntros (v va) "Hv".
      iIntros (k K) "Hk".
      iMod "Hk".
      unfold CPureSpec.pure.
      now iApply "Hk".
    Qed.

    Lemma refine_bind `{RA : Rel SA CA, RB : Rel SB CB} {w} :
      ⊢ ℛ⟦RPureSpec RA -> □ᵣ(RA -> RPureSpec RB) -> RPureSpec RB⟧
        CPureSpec.bind (SPureSpec.bind (w := w)).
    Proof.
      iIntros (c cs) "Hc".
      iIntros (k ks) "Hk".
      iIntros (kk kks) "Hkk".
      unfold CPureSpec.bind, SPureSpec.bind.
      iApply "Hc".
      iIntros (w2 ω2) "!>".
      iIntros (v vs) "Hv".
      iApply ("Hk" with "Hv").
      now iApply (refine_four with "Hkk").
    Qed.

    Lemma refine_block `{R : Rel AT A} {w} :
      ⊢ ℛ⟦RPureSpec R⟧ CPureSpec.block (@SPureSpec.block AT w).
    Proof. done. Qed.

    Lemma refine_error `{RA : Rel AT A} {w} m :
      ⊢ ℛ⟦RMsg _ (RPureSpec RA)⟧ m (@SPureSpec.error _ w).
    Proof.
      unfold RMsg, RPureSpec, RProp; cbn.
      iIntros (msg k K) "Hk".
      now cbn.
    Qed.

    Lemma refine_angelic (x : option LVar) σ {w} :
      ⊢ ℛ⟦RPureSpec (RVal σ)⟧ (CPureSpec.angelic σ) (SPureSpec.angelic (w := w) x σ).
    Proof.
      unfold CPureSpec.angelic, SPureSpec.angelic; simpl.
      iIntros (k K) "HK".
      rewrite knowing_acc_snoc_right.
      iIntros "[%v HSP]".
      iSpecialize ("HK" $! _ acc_snoc_right).
      rewrite assuming_acc_snoc_right.
      iSpecialize ("HK" $! v).
      rewrite <-(forgetting_pure (acc_snoc_left' (fresh_lvar w x∷σ) (term_val _ v))).
      iPoseProof forgetting_acc_snoc_left_repₚ as "Hrep".
      iModIntro.
      iDestruct ("HK" with "Hrep HSP") as "%Hkv".
      now iExists v.
    Qed.

    Lemma refine_demonic (x : option LVar) σ {w} :
      ⊢ ℛ⟦RPureSpec (RVal σ)⟧ (CPureSpec.demonic σ) (SPureSpec.demonic (w := w) x σ).
    Proof.
      unfold CPureSpec.demonic, SPureSpec.angelic; simpl.
      iIntros (k K) "HK HSP".
      iIntros (v).
      iSpecialize ("HK" $! _ (acc_snoc_right (b := fresh_lvar w x∷σ))).
      rewrite !assuming_acc_snoc_right.
      iPoseProof forgetting_acc_snoc_left_repₚ as "Hrep".
      iSpecialize ("HK" $! v).
      iSpecialize ("HSP" $! v).
      rewrite <-(forgetting_pure (acc_snoc_left' (fresh_lvar w x∷σ) (term_val _ v))).
      iModIntro.
      now iApply ("HK" with "Hrep HSP").
    Qed.

    Lemma refine_angelic_ctx {N : Set} {n : N -> LVar} {w} :
      ⊢ ℛ⟦∀ᵣ Δ, RPureSpec (RNEnv N Δ)⟧
        CPureSpec.angelic_ctx (SPureSpec.angelic_ctx (w := w) n).
    Proof.
      iIntros (Δ).
      iInduction Δ as [|Δ IHΔ b] "Hind";
        unfold SPureSpec.angelic_ctx, CPureSpec.angelic_ctx.
      - iApply (refine_pure (RA := RNEnv N [ctx])).
        now iApply (repₚ_triv (T := λ Σ, NamedEnv (Term Σ) [ctx])).
      - iApply (refine_bind (RA := RNEnv N Δ) (RB := RNEnv N (Δ ▻ b)) with "Hind []").
        iIntros (w1 ω1) "!> %v %vs Hv".
        iApply (refine_bind (RA := RVal (type b)) (RB := RNEnv N (Δ ▻ b))).
        { now iApply refine_angelic. }
        iIntros (w2 ω2) "!> %v2 %vs2 Hv2".
        iApply (refine_pure (RA := RNEnv N (Δ ▻ b))).
        iApply (refine_namedenv_snoc with "[$Hv2 Hv]").
        now iApply (forgetting_repₚ with "Hv").
    Qed.

    Lemma refine_demonic_ctx {N : Set} {n : N -> LVar} {w} :
      ⊢ ℛ⟦∀ᵣ Δ : NCtx N Ty, RPureSpec (RNEnv N Δ)⟧
        CPureSpec.demonic_ctx (SPureSpec.demonic_ctx (w := w) n).
    Proof.
      iIntros (Δ).
      iInduction Δ as [|Δ IHΔ b] "Hind";
        unfold SPureSpec.demonic_ctx, CPureSpec.demonic_ctx.
      - iApply (refine_pure (RA := RNEnv N [ctx])).
        now iApply (repₚ_triv (T := λ Σ, NamedEnv (Term Σ) [ctx])).
      - iApply (refine_bind (RA := RNEnv N Δ) (RB := RNEnv N (Δ ▻ b)) with "Hind []").
        iIntros (w1 ω1) "!> %v %vs Hv".
        iApply (refine_bind (RA := RVal (type b)) (RB := RNEnv N (Δ ▻ b))).
        { now iApply refine_demonic. }
        iIntros (w2 ω2) "!> %v2 %vs2 Hv2".
        iApply (refine_pure (RA := RNEnv N (Δ ▻ b))).
        iApply (refine_namedenv_snoc with "[$Hv2 Hv]").
        now iApply (forgetting_repₚ with "Hv").
    Qed.

    Lemma obligation_equiv {w : World} (msg : AMessage w) (fml : Formula w) :
      (Obligation msg fml : Pred w) ⊣⊢ instprop fml.
    Proof. crushPredEntails3.
           - now destruct H0. 
           - now constructor.
    Qed.

    Lemma obligation_equiv_pred {w : World} (msg : AMessage w) (fml : Formula w) :
      (Obligation msg fml : Pred w) ⊣⊢ instpred fml.
    Proof. crushPredEntails3.
           - rewrite ?instpred_prop. now destruct H0.
           - rewrite instpred_prop in H0. now constructor.
    Qed.

    Lemma safe_assume_triangular {w0 w1} (ζ : Tri w0 w1) (o : 𝕊 w1) :
      (psafe (assume_triangular ζ o) ⊣⊢ (assuming (acc_triangular ζ) (psafe o))).
    Proof.
      induction ζ; first by rewrite assuming_id.
      cbn [sub_triangular].
      rewrite (assuming_trans (ω23 := acc_triangular ζ)).
      cbn.
      now rewrite IHζ.
    Qed.

    Lemma safe_assume_pathcondition_without_solver {w : World}
      (C : PathCondition w) (p : 𝕊 w) :
      psafe (assume_pathcondition_without_solver C p) ⊣⊢
        (instpred C -∗ psafe (w := wpathcondition w C) p).
    Proof.
      revert p. induction C; cbn; intros p.
      - destruct w. (* needed to make coq see that wpathcondition w0 [ctx] is the same as w0 *)
        now rewrite bi.emp_wand.
      - rewrite IHC.
        cbn.
        change (instpred_ctx C) with (instpred C).
        rewrite <-bi.wand_curry.
        (* Coq doesn't see that instpred is parametric in the world. Fortunately,
         * instpred_prop happens to imply this.
         *)
        enough (instpred (w := w) b ⊣⊢ instpred (w := wpathcondition w C) b) as H by now rewrite H.
        constructor; intros.
        now rewrite !instpred_prop.
    Qed.

    (* TODO: more logical inst_triangular *)
    Lemma safe_assert_triangular {w0 w1} msg (ζ : Tri w0 w1)
      (o : AMessage w1 -> 𝕊 w1) :
      (psafe (assert_triangular msg ζ o) ⊣⊢
         (knowing (acc_triangular ζ) (psafe (o (subst msg (sub_triangular ζ)))))).
    Proof.
      revert o. induction ζ; intros o.
      - now rewrite knowing_id subst_sub_id.
      - cbn [psafe assert_triangular acc_triangular].
        rewrite obligation_equiv.
        cbn [sub_triangular].
        rewrite (knowing_trans (w2 := wsubst _ _ _)).
        rewrite subst_sub_comp.
        rewrite (IHζ (subst msg (sub_single xIn t)) o).
        now rewrite knowing_acc_subst_right.
    Qed.

    Lemma safe_assert_pathcondition_without_solver {w0 : World}
      (msg : AMessage w0) (C : PathCondition w0) (p : 𝕊 w0) :
      psafe (assert_pathcondition_without_solver msg C p) ⊣⊢
        (instpred C ∗ psafe (w := wpathcondition w0 C) p).
    Proof.
      unfold assert_pathcondition_without_solver. revert p.
      induction C; cbn; intros p.
      - rewrite bi.True_sep.
        now destruct w0.
      - rewrite IHC; cbn.
        rewrite bi.sep_assoc.
        now rewrite <-obligation_equiv_pred.
    Qed.

    Lemma refine_assert_pathcondition {w} :
      ⊢ ℛ⟦RMsg _ (RPathCondition -> RPureSpec RUnit)⟧
        CPureSpec.assert_pathcondition (SPureSpec.assert_pathcondition (w := w)).
    Proof.
      unfold SPureSpec.assert_pathcondition, CPureSpec.assert_pathcondition.
      iIntros (msg cC sC) "HC %cΦ %sΦ rΦ HΦ".
      destruct (combined_solver_spec w sC) as [[w1 [ζ sc1]] Hsolver|Hsolver].
      - rewrite safe_assert_triangular.
        rewrite safe_assert_pathcondition_without_solver.
        iSplit.
        + iDestruct (knowing_sepₚ with "HΦ") as "[Hsc1 _]".
          rewrite Hsolver.
          iDestruct "HC" as "[HC1 _]".
          iApply ("HC1" with "Hsc1").
        + iSpecialize ("rΦ" $! (wpathcondition w1 sc1) (acc_trans (acc_triangular ζ) (acc_pathcondition_right w1 sc1))).
          rewrite assuming_trans.
          iPoseProof (knowing_assuming (acc_triangular ζ) with "[$HΦ $rΦ]") as "H".
          iApply knowing_pure.
          iApply (knowing_proper with "H").
          iIntros "((Hsc1 & HsΦ) & HΦ)".
          iPoseProof (assuming_acc_pathcondition_right with "[$HΦ $Hsc1]") as "HΦ".
          unfold RImpl, RProp; cbn.
          repeat change (@bi_forall (@bi_pred (wpathcondition w1 sc1)) ?A ?P) with (@bi_forall (@bi_pred w1) A P).
          repeat change (@bi_wand (@bi_pred (wpathcondition w1 sc1)) ?P ?Q) with (@bi_wand (@bi_pred w1) P Q).
          repeat change (@repₚ ?T  ?A ?instTA ?t1 (wpathcondition w1 sc1) ?t2) with (@repₚ T A instTA t1 w1 t2).
          iApply ("HΦ" with "[] HsΦ").
          now iApply refine_unit.
      - cbn.
        iDestruct "HΦ" as "%fls".
        destruct fls.
    Qed.

    Lemma refine_assume_pathcondition {w} :
      ⊢ ℛ⟦RPathCondition -> RPureSpec RUnit⟧
        CPureSpec.assume_pathcondition (SPureSpec.assume_pathcondition (w := w)).
    Proof.
      unfold SPureSpec.assume_pathcondition, CPureSpec.assume_pathcondition.
      iIntros "%C %Cs HC %Φ %Φs HΦ Hsp %HC".
      destruct (combined_solver_spec _ Cs) as [[w1 [ζ sc1]] Hsolver|Hsolver].
      - rewrite safe_assume_triangular.
        rewrite safe_assume_pathcondition_without_solver.
        iDestruct "HC" as "[_ HC2]".
        iSpecialize ("HC2" $! HC).
        rewrite <-Hsolver.
        iSpecialize ("HΦ" $! _ (acc_trans (acc_triangular ζ) (acc_pathcondition_right w1 sc1))).
        rewrite assuming_trans.
        iDestruct (assuming_sepₚ with "[HΦ Hsp]") as "H".
        { now iSplitL "HΦ". }
        iDestruct (knowing_assuming with "[$HC2 $H]") as "H".
        iApply knowing_pure.
        iApply (knowing_proper with "H").
        iIntros "(#Hsc1 & H & HΦ)".
        iDestruct (@assuming_acc_pathcondition_right w1 with "[$Hsc1 $H]") as "H".
        iSpecialize ("HΦ" with "Hsc1").
        unfold RImpl, RProp; cbn.
        repeat change (@bi_forall (@bi_pred (wpathcondition w1 sc1)) ?A ?P) with (@bi_forall (@bi_pred w1) A P).
        repeat change (@bi_wand (@bi_pred (wpathcondition w1 sc1)) ?P ?Q) with (@bi_wand (@bi_pred w1) P Q).
        repeat change (@repₚ ?T  ?A ?instTA ?t1 (wpathcondition w1 sc1) ?t2) with (@repₚ T A instTA t1 w1 t2).
        iApply ("H" with "[] HΦ").
        now iApply refine_unit.
      - iExFalso.
        iApply Hsolver.
        iDestruct "HC" as "[_ HC2]".
        now iApply "HC2".
    Qed.

    Lemma refine_assert_formula {w} :
      ⊢ ℛ⟦RMsg _ (RFormula -> RPureSpec RUnit)⟧
        CPureSpec.assert_formula (SPureSpec.assert_formula (w := w)).
    Proof.
      unfold RPureSpec, SPureSpec.assert_formula, CPureSpec.assert_formula.
      iIntros "%msg %fml %fmls Hfml".
      iApply refine_assert_pathcondition.
      iApply (proprepₚ_cong (T2 := PathCondition) with "Hfml").
      intros. cbn. now apply bi.emp_sep.
    Qed.

    Lemma refine_assume_formula {w} :
      ⊢ ℛ⟦RFormula -> RPureSpec RUnit⟧
        CPureSpec.assume_formula (SPureSpec.assume_formula (w := w)).
    Proof.
      unfold RPureSpec, SPureSpec.assume_formula, CPureSpec.assume_formula.
      iIntros "%fml %fmls Hfml".
      iApply refine_assume_pathcondition.
      iApply (proprepₚ_cong (T2 := PathCondition) with "Hfml").
      intros. cbn. now apply bi.emp_sep.
    Qed.

    Lemma refine_angelic_binary `{RA : Rel SA CA} {w} :
      ⊢ ℛ⟦RPureSpec RA -> RPureSpec RA -> RPureSpec RA⟧
        CPureSpec.angelic_binary (SPureSpec.angelic_binary (w := w)).
    Proof.
      unfold CPureSpec.angelic_binary, SPureSpec.angelic_binary.
      iIntros (c1 cs1) "#Hc1 %c2 %cs2 #Hc2 %k %ks #Hk".
      iApply refine_symprop_angelic_binary.
      - now iApply "Hc1".
      - now iApply "Hc2".
    Qed.

    Lemma refine_demonic_binary `{RA : Rel SA CA} {w} :
      ⊢ ℛ⟦RPureSpec RA -> RPureSpec RA -> RPureSpec RA⟧
        CPureSpec.demonic_binary (SPureSpec.demonic_binary (w := w)).
    Proof.
      unfold CPureSpec.demonic_binary, SPureSpec.demonic_binary. simpl.
      iIntros (c1 cs1) "#Hc1 %c2 %cs2 #Hc2 %k %ks #Hk".
      iApply refine_symprop_demonic_binary.
      - now iApply "Hc1".
      - now iApply "Hc2".
    Qed.

    Lemma refine_angelic_list' `{RA : Rel SA CA} {w} :
      ⊢ ℛ⟦RA -> RList RA -> RPureSpec RA⟧
        CPureSpec.angelic_list' (SPureSpec.angelic_list' (w := w)).
    Proof.
      iIntros "%v %sv Hv %vs %svs Hvs".
      iRevert (v sv) "Hv".
      iApply (RList_ind (R := RA) (MkRel (fun vs w svs => ∀ (v : CA) (sv : SA w), ℛ⟦RA⟧ v sv -∗ ℛ⟦RPureSpec RA⟧ (CPureSpec.angelic_list' v vs) (SPureSpec.angelic_list' (w := w) sv svs))%I) w with "[] Hvs"); cbn.
      iSplit.
      - iApply refine_pure.
      - clear. iIntros (v sv vs svs) "Hv Hvs IHvs %v2 %sv2 Hv2".
        iApply (refine_angelic_binary with "[Hv2]").
        + now iApply refine_pure.
        + now iApply "IHvs".
    Qed.

    Lemma refine_angelic_list `{RA : Rel SA CA} {w} :
      ⊢ ℛ⟦RMsg _ (RList RA -> RPureSpec RA)⟧
        CPureSpec.angelic_list (SPureSpec.angelic_list (w := w)).
    Proof.
      iIntros (msg vs svs) "Hvs".
      iApply (RList_ind (R := RA) (MkRel (fun vs w svs => ∀ msg, ℛ⟦RPureSpec RA⟧ (CPureSpec.angelic_list vs) (SPureSpec.angelic_list (w := w) msg svs))%I) w with "[] Hvs"); cbn.
      clear.
      iSplit.
      - now iApply refine_error.
      - iIntros (v svs vs sv) "Hv Hvs _ %msg".
        cbn -[RSat].
        now iApply (refine_angelic_list' with "Hv Hvs").
    Qed.

    Lemma refine_demonic_list' `{RA : Rel SA CA} {w} :
      ⊢ ℛ⟦RA -> RList RA -> RPureSpec RA⟧
        CPureSpec.demonic_list' (SPureSpec.demonic_list' (w := w)).
    Proof.
      iIntros "%v %sv Hv %vs %svs Hvs".
      iRevert (v sv) "Hv".
      iApply (RList_ind (R := RA) (MkRel (fun vs w svs => ∀ (v : CA) (sv : SA w), ℛ⟦RA⟧ v sv -∗ ℛ⟦RPureSpec RA⟧ (CPureSpec.demonic_list' v vs) (SPureSpec.demonic_list' (w := w) sv svs))%I) w with "[] Hvs"); cbn.
      iSplit.
      - iApply refine_pure.
      - clear. iIntros (v sv vs svs) "Hv Hvs IHvs %v2 %sv2 Hv2".
        iApply (refine_demonic_binary with "[Hv2]").
        + now iApply refine_pure.
        + now iApply "IHvs".
    Qed.

    Lemma refine_demonic_list `{RA : Rel SA CA} {w} :
      ⊢ ℛ⟦RList RA -> RPureSpec RA⟧
        CPureSpec.demonic_list (SPureSpec.demonic_list (w := w)).
    Proof.
      iIntros (vs svs) "Hvs".
      iApply (RList_ind (R := RA) (MkRel (fun vs w svs => ℛ⟦RPureSpec RA⟧ (CPureSpec.demonic_list vs) (SPureSpec.demonic_list (w := w) svs))%I) w with "[] Hvs"); cbn.
      clear.
      iSplit.
      - now iApply refine_block.
      - iIntros (v svs vs sv) "Hv Hvs _".
        now iApply (refine_demonic_list' with "Hv Hvs").
    Qed.

    Lemma refine_angelic_finite {F} `{finite.Finite F} {w} :
      ⊢ ℛ⟦RMsg _ (RPureSpec (RConst F))⟧
        (CPureSpec.angelic_finite F) (@SPureSpec.angelic_finite F _ _ w).
    Proof.
      iIntros (msg).
      unfold CPureSpec.angelic_finite, SPureSpec.angelic_finite.
      iApply (refine_angelic_list (RA := RConst F)).
      iStopProof.
      crushPredEntails3.
      induction (finite.enum F); now constructor.
    Qed.

    Lemma refine_demonic_finite {F} `{finite.Finite F} {w} :
      ⊢ ℛ⟦RPureSpec (RConst F)⟧
        (CPureSpec.demonic_finite F) (@SPureSpec.demonic_finite F _ _ w).
    Proof.
      unfold CPureSpec.demonic_finite, SPureSpec.demonic_finite.
      iApply (refine_demonic_list (RA := RConst F)).
      iStopProof.
      crushPredEntails3.
      induction (finite.enum F); now constructor.
    Qed.

    Lemma refine_angelic_pattern_match' {N : Set} (n : N -> LVar)
      {σ} (pat : @Pattern N σ) {w} :
      ⊢ ℛ⟦RMsg _ (RVal σ -> RPureSpec (RMatchResult pat))⟧
        (CPureSpec.angelic_pattern_match pat)
        (SPureSpec.angelic_pattern_match' (w := w) n pat).
    Proof.
      iIntros (msg v t) "Hv".
      unfold SPureSpec.angelic_pattern_match'.
      unfold CPureSpec.angelic_pattern_match.
      iApply (refine_bind (RA := RConst _) (RB := RMatchResult _)).
      { now iApply refine_angelic_finite. }
      iIntros (w1 r01) "!> %ι1 %sι1 Hι1".
      unfold RConst, RInst; cbn.
      rewrite repₚ_const.
      iDestruct "Hι1" as "<-".
      iApply (refine_bind (RA := RNEnv _ (PatternCaseCtx _)) (RB := RMatchResult pat)).
      { now iApply refine_angelic_ctx. }
      iIntros (w2 r12) "!> %vs %svs #Hvs".
      iApply (refine_bind (RA := RUnit) (RB := RMatchResult _) with "[Hv Hvs]").
      { iApply refine_assert_formula.
        unfold RVal, RInst; cbn.
        rewrite <-forgetting_repₚ.
        iApply (proprepₚ_cong₂ (T1 := STerm σ) (T2 := fun w => NamedEnv (Term w) _) (T3 := Formula) (fun v vs => pattern_match_val_reverse pat sι1 vs = v) (fun v vs => formula_relop bop.eq (pattern_match_term_reverse pat sι1 vs) v) with "[$Hv $Hvs]").
        intros; cbn; now rewrite inst_pattern_match_term_reverse.
      }
      iIntros (w3 r23) "!> %u %su _".
      iApply (refine_pure (RA := RMatchResult _)).
      iExists eq_refl; cbn.
      unfold RNEnv, RInst; cbn.
      now rewrite <-forgetting_repₚ.
    Qed.
    #[global] Arguments refine_angelic_pattern_match' {N} n {σ} pat.

    Lemma refine_demonic_pattern_match' {N : Set} (n : N -> LVar)
      {σ} (pat : @Pattern N σ) {w} :
      ⊢ ℛ⟦RVal σ -> RPureSpec (RMatchResult pat)⟧
        (CPureSpec.demonic_pattern_match pat)
        (SPureSpec.demonic_pattern_match' (w := w) n pat).
    Proof.
      iIntros (v t) "Hv".
      unfold SPureSpec.demonic_pattern_match'.
      unfold CPureSpec.demonic_pattern_match.
      iApply (refine_bind (RA := RConst _) (RB := RMatchResult _)).
      { now iApply refine_demonic_finite. }
      iIntros (w1 r01) "!> %ι1 %sι1 Hι1".
      unfold RConst, RInst; cbn.
      rewrite repₚ_const.
      iDestruct "Hι1" as "<-".
      iApply (refine_bind (RA := RNEnv _ (PatternCaseCtx _)) (RB := RMatchResult pat)).
      { now iApply refine_demonic_ctx. }
      iIntros (w2 r12) "!> %vs %svs #Hvs".
      iApply (refine_bind (RA := RUnit) (RB := RMatchResult _) with "[Hv Hvs]").
      { iApply refine_assume_formula.
        unfold RVal, RInst; cbn.
        rewrite <-forgetting_repₚ.
        iApply (proprepₚ_cong₂ (T1 := STerm σ) (T2 := fun w => NamedEnv (Term w) _) (T3 := Formula) (fun v vs => pattern_match_val_reverse pat sι1 vs = v) (fun v vs => formula_relop bop.eq (pattern_match_term_reverse pat sι1 vs) v) with "[$Hv $Hvs]").
        intros; cbn; now rewrite inst_pattern_match_term_reverse.
      }
      iIntros (w3 r23) "!> %u %su _".
      iApply (refine_pure (RA := RMatchResult _)).
      iExists eq_refl; unfold RNEnv, RInst; cbn.
      now rewrite <-forgetting_repₚ.
    Qed.
    #[global] Arguments refine_demonic_pattern_match' {N} n {σ} pat.

    Lemma refine_angelic_pattern_match {N : Set} (n : N -> LVar)
      {σ} (pat : @Pattern N σ) {w} :
      ⊢ ℛ⟦RMsg _ (RVal σ -> RPureSpec (RMatchResult pat))⟧
        (CPureSpec.angelic_pattern_match pat)
        (SPureSpec.angelic_pattern_match (w := w) n pat).
    Proof.
      induction pat; cbn - [RSat].
      - iIntros (msg v sv) "Hv %Φ %sΦ rΦ HSP". 
        rewrite CPureSpec.wp_angelic_pattern_match.
        iApply ("rΦ" with "[Hv] HSP").
        iExists eq_refl.
        iApply (repₚ_cong (T1 := STerm σ) (T2 := fun w => NamedEnv (Term w) _) with "Hv").
        now intros.
      - iIntros (msg v sv) "Hv".
        destruct (term_get_val_spec sv); subst.
        + iIntros (Φ sΦ) "rΦ HSP".
          rewrite CPureSpec.wp_angelic_pattern_match; cbn.
          iApply ("rΦ" with "[Hv] HSP").
          iDestruct (repₚ_elim (a := a) with "Hv") as "<-".
          { now intros. }
          iExists eq_refl; cbn.
          now iApply (repₚ_triv (T := fun w => NamedEnv (Term w) _)).
        + now iApply (refine_angelic_pattern_match' n pat_bool).
      - iApply (refine_angelic_pattern_match' n (pat_list σ x y)).
      - iIntros (msg v sv) "Hv".
        destruct (term_get_pair_spec sv) as [[svl svr] Heq|]; subst.
        + iIntros (Φ sΦ) "rΦ HSP".
          rewrite CPureSpec.wp_angelic_pattern_match.
          iApply ("rΦ" with "[Hv] HSP").
          destruct v as (v1 & v2); cbn.
          iExists eq_refl; cbn.
          iPoseProof (eqₚ_triv (vt2 := term_binop bop.pair svl svr : STerm (ty.prod σ τ) w) Heq) as "Heq".
          iDestruct (repₚ_eqₚ (T := STerm (ty.prod σ τ)) with "[$Heq $Hv]") as "Hv12".
          iDestruct (repₚ_term_prod with "Hv12") as "(Hv1 & Hv2)".
          iApply (repₚ_cong₂ (T1 := STerm σ) (T2 := STerm τ) (T3 := fun w => NamedEnv (Term w) [x∷σ; y ∷τ]) (fun v1 v2 => [env].[x∷σ↦ v1].[y∷τ ↦ v2]) (fun v1 v2 => [env].[x∷σ↦ v1].[y∷τ ↦ v2] : NamedEnv (Term w) _) with "[Hv1 Hv2]").
          { now intros. }
          now iFrame.
        + now iApply (refine_angelic_pattern_match' n (pat_pair _ _)).
      - iIntros (msg v sv) "Hv".
        destruct (term_get_sum_spec sv) as [[svl|svr] Heq|]; subst.
        + iPoseProof (eqₚ_triv (vt2 := term_inl svl : STerm (ty.sum σ τ) w) Heq) as "Heq".
          iDestruct (repₚ_eqₚ (T := STerm (ty.sum _ _)) with "[$Heq $Hv]") as "Hv'".
          iIntros (Φ sΦ) "rΦ HSP".
          rewrite CPureSpec.wp_angelic_pattern_match.
          iApply ("rΦ" with "[Hv'] HSP").
          iDestruct (repₚ_inversion_term_inl with "Hv'") as "(%vl & -> & Hvl)".
          iExists eq_refl.
          cbn -[RSat].
          now iApply refine_namedenv_singleton.
        + iPoseProof (eqₚ_triv (vt2 := term_inr svr : STerm (ty.sum σ τ) w) Heq) as "Heq".
          iDestruct (repₚ_eqₚ (T := STerm (ty.sum _ _)) with "[$Heq $Hv]") as "Hv'".
          iIntros (Φ sΦ) "rΦ HSP".
          rewrite CPureSpec.wp_angelic_pattern_match.
          iApply ("rΦ" with "[Hv'] HSP").
          iDestruct (repₚ_inversion_term_inr with "Hv'") as "(%vr & -> & Hvr)".
          iExists eq_refl.
          now iApply refine_namedenv_singleton.
        + now iApply (refine_angelic_pattern_match' n (pat_sum _ _ _ _)).
      - iIntros (msg v sv) "Hv %Φ %sΦ rΦ HSP".
        rewrite CPureSpec.wp_angelic_pattern_match.
        iApply ("rΦ" with "[Hv] HSP").
        destruct v.
        iExists eq_refl.
        iApply (repₚ_triv (T := fun w => NamedEnv (Term w) _)).
        now intros.
      - iIntros (msg v sv) "Hv".
        destruct (term_get_val_spec sv); subst.
        + iIntros (Φ sΦ) "rΦ HSP".
          rewrite CPureSpec.wp_angelic_pattern_match.
          iApply ("rΦ" with "[Hv] HSP").
          iDestruct (repₚ_elim (a := a) with "Hv") as "->".
          { now intros. }
          iExists eq_refl.
          iApply (repₚ_triv (T := fun w => NamedEnv (Term w) _)).
          now intros.
        + now iApply (refine_angelic_pattern_match' n (pat_enum E)).
      - iApply (refine_angelic_pattern_match' n (pat_bvec_split _ _ x y)).
      - iIntros (msg v sv) "Hv".
        destruct (term_get_val_spec sv); subst.
        + iIntros (Φ sΦ) "rΦ HSP".
          rewrite CPureSpec.wp_angelic_pattern_match.
          iApply ("rΦ" with "[Hv] HSP").
          iDestruct (repₚ_elim (a := a) with "Hv") as "->".
          { now intros. }
          iExists eq_refl.
          iApply (repₚ_triv (T := fun w => NamedEnv (Term w) _)).
          now intros.
        + now iApply (refine_angelic_pattern_match' n (pat_bvec_exhaustive m)).
      - iApply (refine_angelic_pattern_match' n (pat_tuple p)).
      - iIntros (msg v sv) "Hv".
        destruct (term_get_record_spec sv) as [svs Heq|]; subst.
        + iPoseProof (eqₚ_triv (vt2 := term_record R svs : STerm (ty.record R) w) Heq) as "Heq".
          iDestruct (repₚ_eqₚ (T := STerm (ty.record _)) with "[$Heq $Hv]") as "Hv".
          iIntros (Φ sΦ) "rΦ HSP".
          rewrite CPureSpec.wp_angelic_pattern_match.
          iApply ("rΦ" with "[Hv] HSP").
          iDestruct (repₚ_inversion_record p with "Hv") as "(%vs & -> & Hvs)".
          iExists eq_refl.
          unfold record_pattern_match_val.
          rewrite recordv_unfold_fold.
          iApply (repₚ_cong (T1 := fun w => NamedEnv (Term w) _) (T2 := fun w => NamedEnv (Term w) _) with "Hvs").
          intros.
          now rewrite inst_record_pattern_match.
        + now iApply (refine_angelic_pattern_match' n (pat_record _ _ _)).
      - iIntros (msg v sv) "Hv".
        destruct (term_get_union_spec sv) as [[K scr'] Heq|]; subst.
        + iIntros (Φ sΦ) "rΦ".
          iPoseProof (eqₚ_triv (vt2 := term_union U K scr' : STerm (ty.union U) w) Heq) as "Heq".
          iDestruct (repₚ_eqₚ (T := STerm (ty.union _)) with "[$Heq $Hv]") as "Hv".
          iDestruct (repₚ_inversion_union with "Hv") as "(%t & -> & Hv)".
          iIntros "HSP".
          rewrite CPureSpec.wp_angelic_pattern_match.
          cbn -[RSat].
          rewrite unionv_unfold_fold.
          rewrite -(CPureSpec.wp_angelic_pattern_match _ (fun v => Φ (let (pc, δpc) := v in _))).
          iApply (H with "Hv [rΦ] HSP").
          iIntros (w2 ω2) "!> %mr %smr Hmr".
          destruct mr, smr.
          iDestruct "Hmr" as "(%e & Hmr)".
          subst x0.
          rewrite forgetting_unconditionally.
          iApply ("rΦ" with "[Hmr]").
          now iExists eq_refl.
        + now iApply (refine_angelic_pattern_match' n (pat_union _ _)).
    Qed.
    #[global] Arguments refine_angelic_pattern_match' {N} n {σ} pat.

    Lemma refine_demonic_pattern_match {N : Set} (n : N -> LVar)
      {σ} (pat : @Pattern N σ) {w} :
      ⊢ ℛ⟦RVal σ -> RPureSpec (RMatchResult pat)⟧
        (CPureSpec.demonic_pattern_match pat)
        (SPureSpec.demonic_pattern_match n pat (w := w)).
    Proof.
      induction pat; cbn - [RSat].
      - iIntros (v sv) "Hv %Φ %sΦ rΦ HSP". 
        rewrite CPureSpec.wp_demonic_pattern_match.
        iApply ("rΦ" with "[Hv] HSP").
        iExists eq_refl.
        iApply (repₚ_cong (T1 := STerm σ) (T2 := fun w => NamedEnv (Term w) _) with "Hv").
        now intros.
      - iIntros (v sv) "Hv".
        destruct (term_get_val_spec sv); subst.
        + iIntros (Φ sΦ) "rΦ HSP".
          rewrite CPureSpec.wp_demonic_pattern_match; cbn.
          iApply ("rΦ" with "[Hv] HSP").
          iDestruct (repₚ_elim (a := a) with "Hv") as "<-".
          { now intros. }
          iExists eq_refl; cbn.
          now iApply (repₚ_triv (T := fun w => NamedEnv (Term w) _)).
        + now iApply (refine_demonic_pattern_match' n pat_bool).
      - iApply (refine_demonic_pattern_match' n (pat_list σ x y)).
      - iIntros (v sv) "Hv".
        destruct (term_get_pair_spec sv) as [[svl svr] Heq|]; subst.
        + iIntros (Φ sΦ) "rΦ HSP".
          rewrite CPureSpec.wp_demonic_pattern_match.
          iApply ("rΦ" with "[Hv] HSP").
          destruct v as (v1 & v2); cbn.
          iExists eq_refl; cbn.
          iPoseProof (eqₚ_triv (vt2 := term_binop bop.pair svl svr : STerm (ty.prod σ τ) w) Heq) as "Heq".
          iDestruct (repₚ_eqₚ (T := STerm (ty.prod σ τ)) with "[$Heq $Hv]") as "Hv12".
          iDestruct (repₚ_term_prod with "Hv12") as "(Hv1 & Hv2)".
          iApply (repₚ_cong₂ (T1 := STerm σ) (T2 := STerm τ) (T3 := fun w => NamedEnv (Term w) [x∷σ; y ∷τ]) (fun v1 v2 => [env].[x∷σ↦ v1].[y∷τ ↦ v2]) (fun v1 v2 => [env].[x∷σ↦ v1].[y∷τ ↦ v2] : NamedEnv (Term w) _) with "[Hv1 Hv2]").
          { now intros. }
          now iFrame.
        + now iApply (refine_demonic_pattern_match' n (pat_pair _ _)).
      - iIntros (v sv) "Hv".
        destruct (term_get_sum_spec sv) as [[svl|svr] Heq|]; subst.
        + iPoseProof (eqₚ_triv (vt2 := term_inl svl : STerm (ty.sum σ τ) w) Heq) as "Heq".
          iDestruct (repₚ_eqₚ (T := STerm (ty.sum _ _)) with "[$Heq $Hv]") as "Hv'".
          iIntros (Φ sΦ) "rΦ HSP".
          rewrite CPureSpec.wp_demonic_pattern_match.
          iApply ("rΦ" with "[Hv'] HSP").
          iDestruct (repₚ_inversion_term_inl with "Hv'") as "(%vl & -> & Hvl)".
          iExists eq_refl.
          iApply (repₚ_cong (T1 := STerm σ) (A2 := NamedEnv Val _) (T2 := fun w => NamedEnv (Term w) _) (fun vl => [env].[x∷σ ↦ vl]) (fun svl => [env].[x∷σ ↦ svl]) with "Hvl").
          now intros.
        + iPoseProof (eqₚ_triv (vt2 := term_inr svr : STerm (ty.sum σ τ) w) Heq) as "Heq".
          iDestruct (repₚ_eqₚ (T := STerm (ty.sum _ _)) with "[$Heq $Hv]") as "Hv'".
          iIntros (Φ sΦ) "rΦ HSP".
          rewrite CPureSpec.wp_demonic_pattern_match.
          iApply ("rΦ" with "[Hv'] HSP").
          iDestruct (repₚ_inversion_term_inr with "Hv'") as "(%vr & -> & Hvr)".
          iExists eq_refl.
          iApply (repₚ_cong (T1 := STerm _) (A2 := NamedEnv Val _) (T2 := fun w => NamedEnv (Term w) _) (fun vr => [env].[y∷τ ↦ vr]) (fun svr => [env].[y∷τ ↦ svr]) with "Hvr").
          now intros.
        + now iApply (refine_demonic_pattern_match' n (pat_sum _ _ _ _)).
      - iIntros (v sv) "Hv %Φ %sΦ rΦ HSP".
        rewrite CPureSpec.wp_demonic_pattern_match.
        iApply ("rΦ" with "[Hv] HSP").
        destruct v.
        iExists eq_refl.
        iApply (repₚ_triv (T := fun w => NamedEnv (Term w) _)).
        now intros.
      - iIntros (v sv) "Hv".
        destruct (term_get_val_spec sv); subst.
        + iIntros (Φ sΦ) "rΦ HSP".
          rewrite CPureSpec.wp_demonic_pattern_match.
          iApply ("rΦ" with "[Hv] HSP").
          iDestruct (repₚ_elim (a := a) with "Hv") as "->".
          { now intros. }
          iExists eq_refl.
          iApply (repₚ_triv (T := fun w => NamedEnv (Term w) _)).
          now intros.
        + now iApply (refine_demonic_pattern_match' n (pat_enum E)).
      - iApply (refine_demonic_pattern_match' n (pat_bvec_split _ _ x y)).
      - iIntros (v sv) "Hv".
        destruct (term_get_val_spec sv); subst.
        + iIntros (Φ sΦ) "rΦ HSP".
          rewrite CPureSpec.wp_demonic_pattern_match.
          iApply ("rΦ" with "[Hv] HSP").
          iDestruct (repₚ_elim (a := a) with "Hv") as "->".
          { now intros. }
          iExists eq_refl.
          iApply (repₚ_triv (T := fun w => NamedEnv (Term w) _)).
          now intros.
        + now iApply (refine_demonic_pattern_match' n (pat_bvec_exhaustive m)).
      - iApply (refine_demonic_pattern_match' n (pat_tuple p)).
      - iIntros (v sv) "Hv".
        destruct (term_get_record_spec sv) as [svs Heq|]; subst.
        + iPoseProof (eqₚ_triv (vt2 := term_record R svs : STerm (ty.record R) w) Heq) as "Heq".
          iDestruct (repₚ_eqₚ (T := STerm (ty.record _)) with "[$Heq $Hv]") as "Hv".
          iIntros (Φ sΦ) "rΦ HSP".
          rewrite CPureSpec.wp_demonic_pattern_match.
          iApply ("rΦ" with "[Hv] HSP").
          iDestruct (repₚ_inversion_record p with "Hv") as "(%vs & -> & Hvs)".
          iExists eq_refl.
          unfold record_pattern_match_val.
          rewrite recordv_unfold_fold.
          iApply (repₚ_cong (T1 := fun w => NamedEnv (Term w) _) (T2 := fun w => NamedEnv (Term w) _) with "Hvs").
          intros.
          now rewrite inst_record_pattern_match.
        + now iApply (refine_demonic_pattern_match' n (pat_record _ _ _)).
      - iIntros (v sv) "Hv".
        destruct (term_get_union_spec sv) as [[K scr'] Heq|]; subst.
        + iIntros (Φ sΦ) "rΦ".
          iPoseProof (eqₚ_triv (vt2 := term_union U K scr' : STerm (ty.union U) w) Heq) as "Heq".
          iDestruct (repₚ_eqₚ (T := STerm (ty.union _)) with "[$Heq $Hv]") as "Hv".
          iDestruct (repₚ_inversion_union with "Hv") as "(%t & -> & Hv)".
          iIntros "HSP".
          rewrite CPureSpec.wp_demonic_pattern_match.
          cbn -[RSat].
          rewrite unionv_unfold_fold.
          rewrite -(CPureSpec.wp_demonic_pattern_match _ (fun v => Φ (let (pc, δpc) := v in _))).
          iApply (H with "Hv [rΦ] HSP").
          iIntros (w2 ω2) "!> %mr %smr Hmr".
          destruct mr, smr.
          iDestruct "Hmr" as "(%e & Hmr)".
          subst x0.
          rewrite forgetting_unconditionally.
          iApply ("rΦ" with "[Hmr]").
          now iExists eq_refl.
        + now iApply (refine_demonic_pattern_match' n (pat_union _ _)).
    Qed.
    #[global] Arguments refine_demonic_pattern_match' {N} n {σ} pat.

    Lemma refine_new_pattern_match_regular {N : Set} n σ (pat : @Pattern N σ) {w} :
      ⊢ ℛ⟦RVal σ -> RPureSpec (RMatchResult pat)⟧
        (CPureSpec.new_pattern_match pat)
        (SPureSpec.new_pattern_match_regular (w := w) n pat).
    Proof.
      unfold SPureSpec.new_pattern_match_regular.
      iIntros (v sv) "rv %post %spost rpost Hsp".
      unfold CPureSpec.new_pattern_match.
      rewrite <- (pattern_match_val_freshen n pat (Σ := w)).
      iPoseProof (refine_pattern_match (p := freshen_pattern n w pat) with "rv") as "Hpm".
      destruct pattern_match_val as [pc vs]. cbn - [acc_trans RSat].
      unfold CPureSpec.pure; cbn -[RSat].
      iSpecialize ("Hsp" $! pc).
      iSpecialize ("rpost" $! _ (acc_match_right pc)).
      iDestruct (knowing_assuming with "[$Hpm $Hsp]") as "H".
      iDestruct (knowing_assuming with "[$H $rpost]") as "H".
      iApply (knowing_pure (acc_match_right pc)).
      iApply (knowing_proper (ω := acc_match_right pc) _ _ with "H").
      iIntros "[[Hargs Hsp] rpost]".
      iApply ("rpost" with "[Hargs] Hsp").
      iExists eq_refl.
      now iApply (refine_unfreshen_patterncaseenv with "Hargs").
    Qed.

    Lemma refine_pattern_match_var {N : Set} n {x σ} (pat : @Pattern N σ) {w} :
      ⊢ ℛ⟦RIn (x∷σ) -> RPureSpec (RMatchResult pat)⟧
        (CPureSpec.new_pattern_match pat)
        (SPureSpec.new_pattern_match_var (w := w) n pat).
    Proof.
      iIntros "%v %sv Hv %post %spost Hpost".
      unfold SPureSpec.new_pattern_match_var, CPureSpec.new_pattern_match, CPureSpec.pure.
      iIntros "Hsp".
      iPoseProof (refine_pattern_match_var (p := freshen_pattern n w pat) with "Hv") as "Hpm".
      rewrite <- (pattern_match_val_freshen n pat (Σ := w)).
      destruct pattern_match_val as [pc vs]. cbn - [acc_trans RSat].
      iSpecialize ("Hsp" $! pc).
      iSpecialize ("Hpost" $! _ (acc_matchvar_right pc)).
      iDestruct (knowing_assuming with "[$Hpm $Hsp]") as "H".
      iDestruct (knowing_assuming with "[$H $Hpost]") as "H".
      iApply (knowing_pure (acc_matchvar_right pc)).
      iApply (knowing_proper (ω := acc_matchvar_right pc) _ _ with "H").
      iIntros "[[Hargs Hsp] Hpost]".
      iApply ("Hpost" with "[Hargs] Hsp").
      iExists eq_refl; cbn.
      now iApply (refine_unfreshen_patterncaseenv with "Hargs").
    Qed.

    Lemma refine_new_pattern_match' {N : Set} n σ (pat : @Pattern N σ) {w} :
      ⊢ ℛ⟦RVal σ -> RPureSpec (RMatchResult pat)⟧
        (CPureSpec.new_pattern_match pat)
        (SPureSpec.new_pattern_match' (w := w) n pat).
    Proof.
      unfold SPureSpec.new_pattern_match'.
      iIntros "%v %sv rv".
      destruct sv.
      now iApply refine_pattern_match_var.
      all: now iApply refine_new_pattern_match_regular.
    Qed.

    Lemma refine_new_pattern_match {N : Set} n σ (pat : @Pattern N σ) {w} :
      ⊢ ℛ⟦RVal σ -> RPureSpec (RMatchResult pat)⟧
        (CPureSpec.new_pattern_match pat)
      (SPureSpec.new_pattern_match (w := w) n pat).
    Proof.
      induction pat; cbn [SPureSpec.new_pattern_match];
        iIntros "%v %sv Hv".
      - unfold CPureSpec.new_pattern_match.
        iApply (refine_pure (RA := RMatchResult _) with "[Hv]").
        iExists eq_refl; cbn.
        now iApply (refine_namedenv_singleton with "[Hv]").
      - destruct (term_get_val_spec sv) as [cv ?|].
        + iApply (refine_pure (RA := RMatchResult _) with "[Hv]"); cbn.
          subst. rewrite <-refine_term_val2.
          iDestruct "Hv" as "->".
          iExists eq_refl; cbn.
          iApply refine_namedenv_nil.
        + now iApply (refine_new_pattern_match' with "Hv").
      - now iApply (refine_new_pattern_match' with "Hv").
      - destruct (term_get_pair_spec sv) as [[? ?] eq|].
        + iApply (refine_pure (RA := RMatchResult _) with "[Hv]").
          destruct v as [v1 v2].
          iExists eq_refl; cbn.
          iPoseProof (eqₚ_triv (vt2 := term_binop bop.pair t t0) eq) as "Heq".
          iDestruct (RVal_eqₚ with "[$Hv $Heq]") as "Hv".
          iDestruct (RVal_pair with "Hv") as "[Hv1 Hv2]".
          iApply (refine_namedenv_snoc with "[Hv2 Hv1]"); cbn; iFrame.
          iApply (refine_namedenv_singleton with "Hv1").
        + now iApply (refine_new_pattern_match' with "Hv").
      - destruct (term_get_sum_spec sv) as [[] eq|].
        + iApply (refine_pure (RA := RMatchResult _) with "[Hv]").
          iDestruct (RVal_eqₚ with "[$Hv]") as "Hv".
          { iApply (eqₚ_triv (vt2 := term_inl t) eq). }
          iDestruct (RVal_invert_inl with "Hv") as "[%vl [-> Hv]]".
          iExists eq_refl; cbn.
          iApply (refine_namedenv_singleton with "Hv").
        + iApply (refine_pure (RA := RMatchResult _) with "[Hv]").
          iDestruct (RVal_eqₚ with "[$Hv]") as "Hv".
          { iApply (eqₚ_triv (vt2 := term_inr t) eq). }
          iDestruct (RVal_invert_inr with "Hv") as "[%vl [-> Hv]]".
          iExists eq_refl; cbn.
          iApply (refine_namedenv_singleton with "Hv").
        + now iApply (refine_new_pattern_match' with "Hv").
      - iApply (refine_pure (RA := RMatchResult _) with "[Hv]").
        iExists eq_refl; cbn.
        now iApply refine_namedenv_nil.
      - destruct (term_get_val_spec sv) as [? ->|].
        + iApply (refine_pure (RA := RMatchResult _) with "[Hv]").
          iDestruct (refine_term_val2 with "Hv") as "->".
          iExists eq_refl; cbn.
          iApply refine_namedenv_nil.
        + now iApply (refine_new_pattern_match' with "Hv").
      - now iApply refine_new_pattern_match'.
      - destruct (term_get_val_spec sv) as [? ->|].
        + iApply (refine_pure (RA := RMatchResult _) with "[Hv]").
          iDestruct (refine_term_val2 with "Hv") as "->".
          iExists eq_refl; cbn.
          iApply refine_namedenv_nil.
        + now iApply (refine_new_pattern_match' with "Hv").
      - destruct (term_get_tuple_spec sv) as [? eq|].
        + iApply (refine_pure (RA := RMatchResult _) with "[Hv]"). 
          iExists eq_refl. cbn.
          iDestruct (RVal_eqₚ with "[$Hv]") as "Hv".
          { iApply (eqₚ_triv (vt2 := term_tuple a) eq).  }
          unfold tuple_pattern_match_val.
          iApply (refine_tuple_pattern_match_env with "[Hv]").
          iApply (RVal_tuple with "Hv").
        + now iApply refine_new_pattern_match'.
      - destruct (term_get_record_spec sv) as [? eq|].
        + iApply (refine_pure (RA := RMatchResult _) with "[Hv]").
          iExists eq_refl. cbn.
          unfold record_pattern_match_val.
          iDestruct (RVal_eqₚ with "[$Hv]") as "Hv".
          { iApply (eqₚ_triv (vt2 := term_record R a) eq).  }
          rewrite <-refine_record_pattern_match_env.
          rewrite RVal_record.
          now rewrite recordv_fold_unfold.
        + now iApply refine_new_pattern_match'.
      - destruct (term_get_union_spec sv) as [[K tf] Heq|].
        + iIntros (post spost) "rpost"; cbn.
          iPoseProof (RVal_eqₚ with "[$Hv]") as "Hv".
          { iApply (eqₚ_triv (vt2 := term_union U K tf) Heq). }
          rewrite <-(unionv_fold_unfold U v).
          destruct (unionv_unfold U v) as [K' vf].
          iDestruct (RVal_union_invertK with "Hv") as "->".
          rewrite RVal_union.
          iPoseProof (H K with "Hv") as "H".
          unfold CPureSpec.new_pattern_match; cbn.
          rewrite unionv_unfold_fold; cbn.
          destruct (pattern_match_val (p K) vf) as [pc δpc] eqn:?.
          iApply ("H" $! (fun '(existT pc δpc) => post (existT (existT K pc) δpc)) with "[rpost]").
          clear.
          iIntros (w2 ω2) "!> %mr %smr Hmr".
          destruct mr as [pc' δargs].
          destruct smr as [spc' sδargs].
          iDestruct "Hmr" as "[%eq H2]"; subst; cbn.
          rewrite forgetting_unconditionally.
          iApply ("rpost" with "[H2]").
          now iExists eq_refl.
        + now iApply refine_new_pattern_match'.
    Qed.

    Lemma refine_debug `{RA : Rel SA CA} {w} :
      ⊢ ℛ⟦RMsg _ (RPureSpec RA -> RPureSpec RA)⟧
        CPureSpec.debug (SPureSpec.debug (w := w)).
    Proof.
      iIntros (msg m ms) "Hm %k %ks Hk HSP".
      iApply ("Hm" with "Hk [HSP]").
      now iApply elim_debugPred.
    Qed.

    Lemma refine_assert_eq_nenv {N : Set} {w} :
      ⊢ ℛ⟦∀ᵣ Δ : NCtx N Ty, RMsg _ (RNEnv _ Δ -> RNEnv _ Δ -> RPureSpec RUnit)⟧
        CPureSpec.assert_eq_nenv (SPureSpec.assert_eq_nenv (w := w)).
    Proof.
      iIntros (Δ msg E1 Es1) "HE1 %E2 %Es2 HE2".
      iInduction Es1 as [|Es1] "IHEs1";
        env.destroy Es2; env.destroy E1; env.destroy E2; cbn -[RSat].
      - now iApply (refine_pure (RA := RUnit)).
      - iDestruct (repₚ_invert_snoc with "HE1") as "(HE1 & Hv0db)".
        iDestruct (repₚ_invert_snoc with "HE2") as "(HE2 & Hv1v)".
        iSpecialize ("IHEs1" with "HE1 HE2").
        iApply (refine_bind (RA := RUnit) (RB := RUnit) with "IHEs1").
        iIntros (w2 ω2) "!> %u %us _".
        iApply refine_assert_formula.
        iApply refine_formula_persist.
        iModIntro.
        iApply (proprepₚ_cong₂ (T1 := STerm (type b)) (T2 := STerm (type b)) eq (formula_relop bop.eq) with "[Hv0db Hv1v]").
        { now cbn. }
        now iSplitL "Hv0db". 
    Qed.

    Lemma refine_assert_eq_env {w} :
      ⊢ ℛ⟦∀ᵣ Δ, RMsg _ (REnv Δ -> REnv Δ -> RPureSpec RUnit)⟧
        CPureSpec.assert_eq_env (SPureSpec.assert_eq_env (w := w)).
    Proof.
      iIntros (Δ msg E1 Es1) "HE1 %E2 %Es2 HE2".
      iInduction Es1 as [] "IHE"; env.destroy E1; env.destroy E2; env.destroy Es2; cbn - [RSat].
      - now iApply (refine_pure (RA := RUnit)).
      - iDestruct (repₚ_invert_snoc with "HE1") as "(HE1 & Hvdb)".
        iDestruct (repₚ_invert_snoc with "HE2") as "(HE2 & Hv0v1)".
        iSpecialize ("IHE" with "HE1 HE2").
        iApply (refine_bind (RA := RUnit) (RB := RUnit) with "IHE").
        iIntros (w2 ω2) "!> %u %us _".
        iApply refine_assert_formula.
        iApply refine_formula_persist.
        iModIntro.
        iApply (proprepₚ_cong₂ (T1 := STerm b) (T2 := STerm b) eq (formula_relop bop.eq) with "[Hvdb Hv0v1]").
        { done. }
        now iSplitL "Hvdb".
    Qed.
    
    Lemma RChunk_ind (P : Rel Chunk SCChunk) {w : World} :
      (∀ p args sargs, ℛ⟦ REnv (𝑯_Ty p) ⟧ args sargs -∗ ℛ⟦ P ⟧ (scchunk_user p args) (chunk_user p sargs)) ∗
        (∀ σ r v sv, ℛ⟦ RVal σ ⟧ v sv -∗ ℛ⟦ P ⟧ (scchunk_ptsreg r v) (chunk_ptsreg r sv)) ∗
        (∀ c1 sc1 c2 sc2, ℛ⟦ RChunk ⟧ c1 sc1 -∗ ℛ⟦ RChunk ⟧ c2 sc2 -∗ ℛ⟦ P ⟧ c1 sc1 -∗ ℛ⟦ P ⟧ c2 sc2 -∗ ℛ⟦ P ⟧ (scchunk_conj c1 c2) (chunk_conj sc1 sc2)) ∗
        (∀ c1 sc1 c2 sc2, ℛ⟦ RChunk ⟧ c1 sc1 -∗ ℛ⟦ RChunk ⟧ c2 sc2 -∗ ℛ⟦ P ⟧ c1 sc1 -∗ ℛ⟦ P ⟧ c2 sc2 -∗ ℛ⟦ P ⟧ (scchunk_wand c1 c2) (chunk_wand sc1 sc2))
        ⊢
        ∀ c (sc : Chunk w), ℛ⟦ RChunk ⟧ c sc → ℛ⟦ P ⟧ c sc.
    Proof.
      constructor. intros ι Hpc (Huser & Hptsreg & Hconj & Hwand) c sc Hsc.
      revert c Hsc; induction sc; intros c Hsc; inversion Hsc.
      - now eapply Huser.
      - now eapply Hptsreg.
      - eapply Hconj; try now cbn.
        + now eapply IHsc1.
        + now eapply IHsc2.
      - eapply Hwand; try now cbn.
        + now eapply IHsc1.
        + now eapply IHsc2.
    Qed.

    Lemma RChunk_case (P : Rel Chunk SCChunk) {w : World} :
      (∀ p args sargs, ℛ⟦ REnv (𝑯_Ty p) ⟧ args sargs -∗ ℛ⟦ P ⟧ (scchunk_user p args) (chunk_user p sargs)) ∗
        (∀ σ r v sv, ℛ⟦ RVal σ ⟧ v sv -∗ ℛ⟦ P ⟧ (scchunk_ptsreg r v) (chunk_ptsreg r sv)) ∗
        (∀ c1 sc1 c2 sc2, ℛ⟦ RChunk ⟧ c1 sc1 -∗ ℛ⟦ RChunk ⟧ c2 sc2 -∗ ℛ⟦ P ⟧ (scchunk_conj c1 c2) (chunk_conj sc1 sc2)) ∗
        (∀ c1 sc1 c2 sc2, ℛ⟦ RChunk ⟧ c1 sc1 -∗ ℛ⟦ RChunk ⟧ c2 sc2 -∗ ℛ⟦ P ⟧ (scchunk_wand c1 c2) (chunk_wand sc1 sc2))
        ⊢
        ∀ c (sc : Chunk w), ℛ⟦ RChunk ⟧ c sc → ℛ⟦ P ⟧ c sc.
    Proof.
      iIntros "(Huser & Hptsreg & Hconj & Hwand) %c %sc #Hsc".
      iApply (RChunk_ind P with "[Huser Hptsreg Hconj Hwand] Hsc").
      iSplitL "Huser". { iExact "Huser". }
      iSplitL "Hptsreg". { iExact "Hptsreg". }
      iSplitL "Hconj".
      - iIntros (c1 sc1 c2 sc2) "Hc1 Hc2 _ _". 
        now iApply ("Hconj" with "Hc1 Hc2").
      - iIntros (c1 sc1 c2 sc2) "Hc1 Hc2 _ _". 
        now iApply ("Hwand" with "Hc1 Hc2").
    Qed.

    Lemma refine_assert_eq_chunk {w} :
      ⊢ ℛ⟦RMsg _ (RChunk -> RChunk -> □ᵣ(RPureSpec RUnit))⟧
        CPureSpec.assert_eq_chunk (SPureSpec.assert_eq_chunk (w := w)).
    Proof.
      iIntros (msg c1 sc1) "Hc1".
      iApply (RChunk_ind (MkRel (fun c w sc => ∀ (msg : AMessage w), ℛ⟦RChunk -> □ᵣ (RPureSpec RUnit)⟧ (CPureSpec.assert_eq_chunk c) (SPureSpec.assert_eq_chunk (w := w) msg sc))%I) with "[] Hc1").
      clear.
      repeat iSplit.
      - iIntros (p args sargs) "Hargs %msg %c2 %sc2 Hc2".
        iApply (RChunk_case (MkRel (fun c2 w sc2 => ∀ msg p args sargs, ℛ⟦REnv (𝑯_Ty p)⟧ args sargs -∗ ℛ⟦□ᵣ (RPureSpec RUnit)⟧ (CPureSpec.assert_eq_chunk (scchunk_user p args) c2) (SPureSpec.assert_eq_chunk msg (chunk_user p sargs) sc2))%I) with "[] Hc2 Hargs").
        clear.
        repeat iSplit.
        + iIntros (p args sargs) "Hargs %msg %p2 %args2 %sargs2 Hargs2 %w1 %ω1".
          iModIntro.
          cbn -[RSat].
          destruct (eq_dec p2 p); last by iApply (refine_error (RA := RUnit)).
          subst; unfold REnv, RInst; cbn.
          rewrite <- !forgetting_repₚ.
          now iApply (refine_assert_eq_env with "Hargs2 Hargs").
        + iIntros (σ r v sv) "Hv %msg %p %args %sargs Hargs %w1 %ω1".
          iModIntro.
          iApply (refine_error (RA := RUnit)).
        + iIntros (c1 sc1 c2 sc2) "_ _ %msg %p %args %sargs Hargs %w1 %ω1".
          iModIntro.
          iApply (refine_error (RA := RUnit)).
        + iIntros (c1 sc1 c2 sc2) "_ _ %msg %p %args %sargs Hargs %w1 %ω1".
          iModIntro.
          iApply (refine_error (RA := RUnit)).
      - iIntros (σ r v sv) "Hv %msg %c2 %sc2 Hc2".
        iApply (RChunk_case (MkRel (fun c2 w sc2 => ∀ msg σ r v sv, ℛ⟦RVal σ⟧ v sv -∗ ℛ⟦□ᵣ (RPureSpec RUnit)⟧ (CPureSpec.assert_eq_chunk (scchunk_ptsreg r v) c2) (SPureSpec.assert_eq_chunk msg (chunk_ptsreg r sv) sc2))%I) with "[] Hc2 Hv").
        clear.
        repeat iSplit.
        + iIntros (p args sargs) "Hargs %msg %σ %r %v %sv Hv %w1 %ω1".
          iModIntro.
          iApply (refine_error (RA := RUnit)).
        + iIntros (σ2 r2 v2 sv2) "Hv2 %msg %σ %r %v %sv Hv %w1 %ω1".
          iModIntro.
          cbn -[RSat].
          destruct (eq_dec_het r r2).
          * dependent elimination e; cbn -[RSat].
            iApply refine_assert_formula.
            unfold RVal, RInst; cbn.
            rewrite <-!forgetting_repₚ.
            iApply (proprepₚ_cong₂ (T1 := STerm σ) (T2 := STerm σ) (T3 := Formula) eq (formula_relop bop.eq) with "[Hv2 Hv]").
            { intuition. }
            now iSplitL "Hv".
          * iApply (refine_error (RA := RUnit)).
        + iIntros (c1 sc1 c2 sc2) "Hc1 Hc2 %msg %σ %r %v %sv Hv %w1 %ω1".
          iModIntro.
          iApply (refine_error (RA := RUnit)).
        + iIntros (c1 sc1 c2 sc2) "Hc1 Hc2 %msg %σ %r %v %sv Hv %w1 %ω1".
          iModIntro.
          iApply (refine_error (RA := RUnit)).
      - iIntros (c1 sc1 c2 sc2) "Hc1 Hc2 IHc1 IHc2 %msg %c3 %sc3 Hc3".
        iApply (RChunk_case (MkRel (fun c3 w sc3 => ∀ msg c1 sc1 c2 sc2,
                                        ℛ⟦RChunk⟧ c1 sc1 -∗
                                                            ℛ⟦RChunk -> □ᵣ (RPureSpec RUnit)⟧ (CPureSpec.assert_eq_chunk c1) (SPureSpec.assert_eq_chunk msg sc1) -∗
                                                                                                                                                                    ℛ⟦RChunk⟧ c2 sc2 -∗
                                                                                                                                                                                        ℛ⟦RChunk -> □ᵣ (RPureSpec RUnit)⟧ (CPureSpec.assert_eq_chunk c2) (SPureSpec.assert_eq_chunk msg sc2) -∗
                                                                                                                                                                                                                                                                                                ℛ⟦□ᵣ (RPureSpec RUnit)⟧ (CPureSpec.assert_eq_chunk (scchunk_conj c1 c2) c3) (SPureSpec.assert_eq_chunk msg (chunk_conj sc1 sc2) sc3))%I) with "[] Hc3 Hc1 IHc1 Hc2 IHc2").
        clear. repeat iSplitL.
        + iIntros (p args sargs) "Hargs %msg %c1 %sc1 %c2 %sc2 Hc1 IHc1 Hc2 IHc2 %w1 %ω1 !>".
          iApply (refine_error (RA := RUnit)).
        + iIntros (σ r v sv) "Hv %msg %c1 %sc1 %c2 %sc2 Hc1 IHc1 Hc2 IHc2 %w1 %ω1 !>".
          iApply (refine_error (RA := RUnit)).
        + iIntros (c3 sc3 c4 sc4) "Hc3 Hc4 %msg %c1 %sc1 %c2 %sc2 Hc1 IHc1 Hc2 IHc2 %w1 %ω1 !>".
          iApply (refine_bind (RA := RUnit) (RB := RUnit) with "[Hc1 IHc1 Hc3] [Hc2 IHc2 Hc4]").
          * iSpecialize ("IHc1" with "Hc3").
            now rewrite forgetting_unconditionally_drastic.
          * iIntros (w2 ω2) "!> %u %su _".
            iSpecialize ("IHc2" with "Hc4").
            now rewrite forgetting_unconditionally_drastic.
        + iIntros (c3 sc3 c4 sc4) "Hc3 Hc4 %msg %c1 %sc1 %c2 %sc2 Hc1 IHc1 Hc2 IHc2 %w1 %ω1 !>".
          iApply (refine_error (RA := RUnit)).
      - iIntros (c1 sc1 c2 sc2) "Hc1 Hc2 IHc1 IHc2 %msg %c3 %sc3 Hc3".
        iApply (RChunk_case (MkRel (fun c3 w sc3 => ∀ msg c1 sc1 c2 sc2,
                                        ℛ⟦RChunk⟧ c1 sc1 -∗
                                                            ℛ⟦RChunk -> □ᵣ (RPureSpec RUnit)⟧ (CPureSpec.assert_eq_chunk c1) (SPureSpec.assert_eq_chunk msg sc1) -∗
                                                                                                                                                                    ℛ⟦RChunk⟧ c2 sc2 -∗
                                                                                                                                                                                        ℛ⟦RChunk -> □ᵣ (RPureSpec RUnit)⟧ (CPureSpec.assert_eq_chunk c2) (SPureSpec.assert_eq_chunk msg sc2) -∗
                                                                                                                                                                                                                                                                                                ℛ⟦□ᵣ (RPureSpec RUnit)⟧ (CPureSpec.assert_eq_chunk (scchunk_wand c1 c2) c3) (SPureSpec.assert_eq_chunk msg (chunk_wand sc1 sc2) sc3))%I) with "[] Hc3 Hc1 IHc1 Hc2 IHc2").
        clear. repeat iSplitL.
        + iIntros (p args sargs) "Hargs %msg %c1 %sc1 %c2 %sc2 Hc1 IHc1 Hc2 IHc2 %w1 %ω1 !>".
          iApply (refine_error (RA := RUnit)).
        + iIntros (σ r v sv) "Hv %msg %c1 %sc1 %c2 %sc2 Hc1 IHc1 Hc2 IHc2 %w1 %ω1 !>".
          iApply (refine_error (RA := RUnit)).
        + iIntros (c3 sc3 c4 sc4) "Hc3 Hc4 %msg %c1 %sc1 %c2 %sc2 Hc1 IHc1 Hc2 IHc2 %w1 %ω1 !>".
          iApply (refine_error (RA := RUnit)).
        + iIntros (c3 sc3 c4 sc4) "Hc3 Hc4 %msg %c1 %sc1 %c2 %sc2 Hc1 IHc1 Hc2 IHc2 %w1 %ω1 !>".
          iApply (refine_bind (RA := RUnit) (RB := RUnit) with "[Hc1 IHc1 Hc3] [Hc2 IHc2 Hc4]").
          * iSpecialize ("IHc1" with "Hc3").
            now rewrite forgetting_unconditionally_drastic.
          * iIntros (w2 ω2) "!> %u %su _".
            iSpecialize ("IHc2" with "Hc4").
            now rewrite forgetting_unconditionally_drastic.
    Qed.

    Lemma refine_replay_aux {Σ} (s : 𝕊 Σ) {w} :
      ⊢ ℛ⟦RBox (RNEnv LVar Σ -> RPureSpec RUnit)⟧
        (CPureSpec.replay_aux s) (fun w' (ω : Acc w w') => SPureSpec.replay_aux (w := w') s).
    Proof.
      iInduction s as [] "IH"; iIntros (w' ω) "!> %ι %ιs #Hι";
        cbn -[RSat].
      - iApply (refine_angelic_binary (RA := RUnit)).
        + now iApply "IH".
        + now iApply "IH1".
      - iApply (refine_demonic_binary (RA := RUnit)).
        + now iApply "IH".
        + now iApply "IH1".
      - now iApply (refine_error (RA := RUnit)).
      - now iApply (refine_block (R := RUnit)).
      - iApply (refine_bind (RA := RUnit) (RB := RUnit)).
        + iApply refine_assert_formula.
          now iApply refine_instprop_subst.
        + iIntros (w1 ω1) "!> %u %us _".
          iApply "IH".
          now iApply (refine_inst_persist with "Hι").
      - iApply (refine_bind (RA := RUnit) (RB := RUnit)).
        + iApply refine_assume_formula.
          now iApply refine_instprop_subst.
        + iIntros (w1 ω1) "!> %u %us _".
          iApply "IH".
          now iApply (refine_inst_persist (AT := Sub _) with "Hι").
      - iApply (refine_bind (RA := RInst (STerm (type b)) (Val _)) (RB := RUnit)).
        + iApply refine_angelic.
        + iIntros (w1 ω1) "!> %v %vs Hv".
          iApply "IH".
          iApply (repₚ_cong₂ (T1 := Sub Σ) (T2 := STerm (type b)) (T3 := Sub (Σ ▻ b)) (fun vs v => env.snoc vs b v) (fun vs v => env.snoc vs b v) with "[Hι $Hv]").
          { intros; now cbn. }
          now rewrite forgetting_repₚ.
      - iApply (refine_bind (RA := RInst (STerm (type b)) (Val _)) (RB := RUnit)).
        + iApply refine_demonic.
        + iIntros (w1 ω1) "!> %v %vs Hv".
          iApply "IH".
          iApply (repₚ_cong₂ (T1 := Sub Σ) (T2 := STerm (type b)) (T3 := Sub (Σ ▻ b)) (fun vs v => env.snoc vs b v) (fun vs v => env.snoc vs b v) with "[Hι $Hv]").
          { intros; now cbn. }
          now rewrite forgetting_repₚ.
      - iApply (refine_bind (RA := RUnit) (RB := RUnit)).
        + iApply refine_assert_formula.
          iApply (proprepₚ_cong₂ (T1 := STerm σ) (T2 := STerm σ) eq (formula_relop bop.eq)).
          { intros; now cbn. }
          iSplitL.
          * rewrite <-inst_sub_shift.
            rewrite <-inst_subst.
            iApply (refine_inst_subst (T := STerm σ) with "Hι").
          * iApply (repₚ_cong (T1 := Sub Σ) (T2 := STerm σ) (fun ι => env.lookup ι xIn) (fun ιs => env.lookup ιs xIn) with "Hι").
            intros. now rewrite inst_lookup.
        + iIntros (w1 ω1) "!> %u %us _".
          iApply "IH".
          iApply (repₚ_cong (T1 := Sub Σ) (T2 := Sub (Σ - (x∷σ))) (fun vs => env.remove (x∷σ) vs xIn) (fun vs => env.remove (x∷σ) vs xIn) with "[Hι]").
          { intros. now rewrite <- inst_sub_shift, <- inst_subst, sub_comp_shift. }
          now rewrite forgetting_repₚ.
      - iApply (refine_bind (RA := RUnit) (RB := RUnit)).
        + iApply refine_assume_formula.
          iApply (proprepₚ_cong₂ (T1 := STerm σ) (T2 := STerm σ) eq (formula_relop bop.eq)).
          { intros; now cbn. }
          iSplitL.
          * rewrite <-inst_sub_shift.
            rewrite <-inst_subst.
            iApply (refine_inst_subst (T := STerm σ) with "Hι").
          * iApply (repₚ_cong (T1 := Sub Σ) (T2 := STerm σ) (fun ι => env.lookup ι xIn) (fun ιs => env.lookup ιs xIn) with "Hι").
            intros. now rewrite inst_lookup.
        + iIntros (w1 ω1) "!> %u %us _".
          iApply "IH".
          iApply (repₚ_cong (T1 := Sub Σ) (T2 := Sub (Σ - (x∷σ))) (fun vs => env.remove (x∷σ) vs xIn) (fun vs => env.remove (x∷σ) vs xIn) with "[Hι]").
          { intros. now rewrite <- inst_sub_shift, <- inst_subst, sub_comp_shift. }
          now rewrite forgetting_repₚ.
      - iApply (refine_error (RA := RUnit)).
      - iApply (refine_error (RA := RUnit)).
      - iApply (refine_debug (RA := RUnit)).
        now iApply "IH".
    Qed.

    Lemma refine_replay_aux2 {Σ} (s : 𝕊 Σ) {w} :
      ⊢ ℛ⟦RInst (Sub Σ) (Valuation Σ) -> RPureSpec RUnit⟧
        (CPureSpec.replay_aux s) (SPureSpec.replay_aux (w := w) s).
    Proof.
      iPoseProof (refine_replay_aux s) as "Hreplay".
      iSpecialize ("Hreplay" $! w acc_refl).
      now rewrite assuming_id.
    Qed.

    Lemma refine_replay (s : 𝕊 wnil) :
      ⊢ (ℛ⟦ RProp ⟧ (CPureSpec.replay s [env]) (SPureSpec.replay s)).
    Proof.
      unfold CPureSpec.replay, SPureSpec.replay.
      iApply refine_run.
      iApply (refine_replay_aux2 s).
      now iApply (refine_lift (AT := Sub [ctx])).
    Qed.

    Lemma refine_peval_chunk {w} :
      ⊢ ℛ⟦RChunk -> RChunk⟧ id (peval_chunk : Impl _ _ w).
    Proof.
      unfold RImpl, RChunk, RInst. crushPredEntails3.
      now rewrite peval_chunk_sound.
    Qed.

    Lemma refine_produce_chunk {w} :
      ⊢ ℛ⟦RChunk -> RHeap -> RPureSpec RHeap⟧
        CPureSpec.produce_chunk  (SPureSpec.produce_chunk (w := w)).
    Proof.
      iIntros (c sc) "Hc %h %sh Hh".
      unfold SPureSpec.produce_chunk, CPureSpec.produce_chunk.
      iApply (refine_pure (RA := RHeap)).
      iApply (refine_cons (R := RChunk) with "[Hc] Hh").
      now iApply refine_peval_chunk.
    Qed.

    Lemma refine_is_duplicable {w} :
      ⊢ ℛ⟦ RChunk -> RConst bool ⟧ is_duplicable (@is_duplicable (Chunk w) _ : Impl Chunk (Const bool) w).
    Proof.
      unfold RImpl, RChunk, RConst, RInst; crushPredEntails3; subst.
      now destruct a0.
    Qed.

    Lemma refine_heap_extractions {w} :
      ⊢ ℛ⟦RHeap -> RList (RProd RChunk RHeap)⟧
        (heap_extractions)
        (heap_extractions : Impl SHeap (fun w => list (Chunk w * SHeap w)) w).
    Proof.
      iIntros (h sh) "Hh".
      iApply (RList_ind (MkRel (fun h w sh => ℛ⟦RList (RProd RChunk RHeap)⟧ (heap_extractions h) (heap_extractions sh))) with "[] Hh").
      clear.
      iSplit.
      - iApply (refine_nil (R := RProd RChunk RHeap)).
      - iIntros (v svs vs sv) "#Hv #Hvs IHvs".
        iApply (refine_cons (R := RProd RChunk RHeap) with "[Hv Hvs] [Hvs IHvs]").
        + iSplitL; first done.
          iApply (refine_if (R := RHeap)); last done.
          * now iApply refine_is_duplicable.
          * now iApply (refine_cons (R := RChunk)).
        + iApply (refine_map (R1 := RProd RChunk RHeap) (R2 := RProd RChunk RHeap) with "[] IHvs").
          iIntros ([c1 h1] [sc1 sh1]) "[Hc1 Hh1]".
          iFrame "Hc1".
          now iApply (refine_cons (R := RChunk)).
    Qed.

    Lemma refine_In `{R : Rel AT A} {w} {sv : AT w} {sl l} :
      ⊢ ℛ⟦ RList R ⟧ l sl -∗ ⌜ In sv sl ⌝ -∗ ∃ v, ⌜ In v l ⌝ ∗ ℛ⟦ R ⟧ v sv.
    Proof.
      iIntros "Hl %Hin".
      iApply (RList_ind (R := R) (MkRel (fun l w sl => ∀ sv, ⌜ In sv sl ⌝ -∗ ∃ v, ⌜ In v l ⌝ ∗ ℛ⟦ R ⟧ v sv))%I with "[] Hl [%//]").
      clear.
      iSplit.
      - iIntros "%sv %Hin".
        now inversion Hin.
      - iIntros (v sv vs svs) "Hv Hvs IHvs %sv2 %Hin".
        destruct Hin as [<- | Hin].
        + iExists v.
          iFrame.
          now iLeft.
        + iDestruct ("IHvs" with "[% //]") as "(%v2 & Hin & Hv2)".
          iExists v2. iFrame.
          now iRight.
    Qed.

    Lemma refine_consume_chunk {w} :
      ⊢ ℛ⟦RChunk -> RHeap -> RPureSpec RHeap⟧
        CPureSpec.consume_chunk (SPureSpec.consume_chunk (w := w)).
    Proof.
      iIntros (c sc) "#Hc %h %sh #Hh".
      unfold SPureSpec.consume_chunk.
      iPoseProof (refine_peval_chunk with "Hc") as "Hcp"; cbn -[RSat].
      set (sc1 := peval_chunk sc).
      destruct (try_consume_chunk_exact_spec sh sc1) as [sh' HsIn|].
      iPoseProof (refine_heap_extractions with "Hh") as "Hexts".
      iDestruct (refine_In with "Hexts [%//]") as "(%c1 & %HIn & Hc1)".
      { iIntros "%K %sK HK HSP".
        unfold CPureSpec.consume_chunk.
        unfold CPureSpec.bind.
        rewrite CPureSpec.wp_angelic_list.
        change (SHeap w) in sh'.
        iExists c1.
        iSplit; first done.
        destruct c1.
        iDestruct "Hc1" as "(Hc1 & Hh1)".
        rewrite CPureSpec.wp_assert_eq_chunk.
        iDestruct (repₚ_antisym_left with "Hcp Hc1") as "->".
        iSplitR; first done.
        now iApply (refine_T with "HK Hh1 HSP").
      }
      destruct (try_consume_chunk_precise_spec sh sc1) as [[sh' eqs] HIn|].
      { cbv [SPureSpec.bind SPureSpec.pure].
        assert (⊢ ∀ eq c h' h, proprepₚ eq eqs -∗ repₚ c sc1 -∗ repₚ h' sh' -∗ repₚ h sh -∗ ⌜ eq ⌝ -∗ ⌜In (c , h') (heap_extractions h)⌝)%I as HInLog.
        { clear -HIn. crushPredEntails3. subst. apply HIn. now rewrite instpred_prop in H2. }
        iDestruct (eval_prop eqs) as "(%eq & Heq)".
        iAssert (∃ h', ℛ⟦RHeap⟧ h' sh')%I as "(%h' & Hh')".
        { iDestruct (eval_ex sh') as "(%h' & Heqh')".
          iExists h'.
          now iApply (RList_RInst with "Heqh'"). } 
        match goal with | |- context[amsg.mk ?m] => generalize (amsg.mk m) end.
        iIntros (msg K sK) "HK HSP".
        iAssert (⌜eq /\ K h'⌝)%I with "[HK HSP]" as "%HeqKh'".
        { iPoseProof (refine_assert_pathcondition $! msg eq eqs with "Heq") as "Hapc".
          iApply ("Hapc" $! (fun _ => K h') with "[HK] HSP").
          iIntros (w2 ω2) "!> %u %su _".
          rewrite forgetting_unconditionally.
          iApply (refine_T with "HK").
          rewrite !(RList_RInst h').
          unfold RChunk, RHeap, RInst; cbn.
          now rewrite forgetting_repₚ.
        }
        destruct HeqKh' as (Heq & HKh').
        iPoseProof (HInLog $! eq c h' h with "Heq Hcp [Hh'] [Hh] [// ]") as "HInch'".
        { now rewrite (RList_RInst h').  }
        { now rewrite (RList_RInst h).  }
        unfold CPureSpec.consume_chunk, CPureSpec.bind.
        rewrite CPureSpec.wp_angelic_list.
        iExists (c, h').
        iSplit; first done.
        rewrite CPureSpec.wp_assert_eq_chunk.
        now iSplit.
      }
      now iApply (refine_error (RA := RHeap)).
    Qed.

    Lemma refine_consume_chunk_angelic {w} :
      ⊢ ℛ⟦RChunk -> RHeap -> RPureSpec RHeap⟧
        CPureSpec.consume_chunk (SPureSpec.consume_chunk_angelic (w := w)).
    Proof.
      iIntros (c sc) "Hc %h %sh Hh".
      unfold SPureSpec.consume_chunk_angelic.
      iDestruct (refine_peval_chunk with "Hc") as "Hc1".
      set (sc1 := peval_chunk sc).
      destruct (try_consume_chunk_exact_spec sh sc1) as [sh' HsIn|].
      { change (SHeap w) in sh'.
        iPoseProof (refine_heap_extractions with "Hh") as "Hexts".
        iDestruct (refine_In with "Hexts [//]") as "(%v & %HIn & HH)".
        destruct v as (c1 & h').
        iDestruct "HH" as "(Hc1' & Hh')".
        iIntros (K sK) "HK HSP".
        unfold CPureSpec.consume_chunk, CPureSpec.bind.
        rewrite CPureSpec.wp_angelic_list.
        iDestruct (repₚ_antisym_left with "Hc1 Hc1'") as "<-".
        iExists (c, h').
        iSplit; first done.
        rewrite CPureSpec.wp_assert_eq_chunk.
        iSplit; first done.
        now iApply (refine_T with "HK Hh' HSP").
      }
      destruct (try_consume_chunk_precise_spec sh sc1) as [[sh' eqs] HIn|].
      { cbv [SPureSpec.bind SPureSpec.pure].
        assert (⊢ ∀ eq c h' h, proprepₚ eq eqs -∗ repₚ c sc1 -∗ repₚ h' sh' -∗ repₚ h sh -∗ ⌜ eq ⌝ -∗ ⌜In (c , h') (heap_extractions h)⌝)%I as HInLog.
        { clear -HIn. crushPredEntails3. subst. apply HIn. now rewrite instpred_prop in H2. }
        iDestruct (eval_prop eqs) as "(%eq & Heq)".
        iAssert (∃ h', ℛ⟦RHeap⟧ h' sh')%I as "(%h' & Hh')".
        { iDestruct (eval_ex sh') as "(%h' & Heqh')".
          iExists h'.
          now iApply (RList_RInst with "Heqh'"). } 
        match goal with | |- context[amsg.mk ?m] => generalize (amsg.mk m) end.
        iIntros (msg).
        iIntros (K sK) "HK HSP".
        iAssert (⌜eq /\ K h'⌝)%I with "[HK HSP]" as "%HeqKh'".
        { iPoseProof (refine_assert_pathcondition $! msg eq eqs with "Heq") as "Hapc".
          iApply ("Hapc" $! (fun _ => K h') with "[HK] HSP").
          iIntros (w2 ω2) "!> %u %su _".
          rewrite forgetting_unconditionally.
          iApply (refine_T with "HK").
          rewrite !(RList_RInst h').
          unfold RInst; cbn.
          now rewrite forgetting_repₚ.
        }
        destruct HeqKh' as (Heq & HKh').
        iPoseProof (HInLog $! eq c h' h with "Heq Hc1 [Hh'] [Hh] [// ]") as "HInch'".
        { now rewrite (RList_RInst h').  }
        { now rewrite (RList_RInst h).  }
        unfold CPureSpec.consume_chunk, CPureSpec.bind.
        rewrite CPureSpec.wp_angelic_list.
        iExists (c, h').
        iSplit; first done.
        rewrite CPureSpec.wp_assert_eq_chunk.
        now iSplit.
      }
      { iApply (refine_bind (RA := RProd RChunk RHeap) (RB := RHeap) with "[Hh] [Hc1]").
        { iApply (refine_angelic_list (RA := RProd RChunk RHeap)).
          now iApply refine_heap_extractions.
        }
        iIntros (w2 ω2) "!> %ch %sch Hch".
        destruct ch as (c', h').
        destruct sch as (sc', sh').
        iDestruct "Hch" as "(Hc' & Hh')".
        iApply (refine_bind (RA := RUnit) (RB := RHeap) with "[Hc1 Hc'] [Hh']").
        { change (ℛ⟦RChunk⟧ (id c) sc1) with (repₚ c sc1).
          rewrite <-forgetting_repₚ.
          change (repₚ c (persist sc1 ω2)) with (ℛ⟦RChunk⟧ c (persist sc1 ω2)).
          iPoseProof (refine_assert_eq_chunk with "Hc1 Hc'") as "Haec".
          iApply (refine_T with "Haec").
        }
        iIntros "%w3 %ω3 !> %u %su _".
        iApply (refine_pure (RA := RHeap)).
        rewrite !RList_RInst.
        now iApply (forgetting_repₚ with "Hh'").
      } 
    Qed.

    Lemma refine_read_register {τ} (reg : 𝑹𝑬𝑮 τ) {w} :
      ⊢ ℛ⟦RHeap -> RPureSpec (RProd (RVal τ) RHeap)⟧
        (CPureSpec.read_register reg) (SPureSpec.read_register (w := w) reg).
    Proof.
      unfold SPureSpec.read_register, SPureSpec.pure, T.
      iIntros (h sh) "#Hh %K %sK HK HSP".
      destruct (find_chunk_ptsreg_precise_spec reg sh) as [[st sh'] HIn|].
      - cbv [CPureSpec.read_register CPureSpec.consume_chunk CPureSpec.pure
               CPureSpec.produce_chunk CPureSpec.bind CPureSpec.angelic].
        iDestruct (eval_ex (AT := STerm τ) st) as "(%v & Hv)".
        iDestruct (eval_ex (AT := SHeap) sh') as "(%h' & Hh')".
        iExists v.
        rewrite CPureSpec.wp_angelic_list.
        iExists (scchunk_ptsreg reg v, h').
        iSplitR.
        + rewrite RList_RInst.
          iStopProof.
          unfold RInst.
          crushPredEntails3. now subst. 
        + rewrite CPureSpec.wp_assert_eq_chunk.
          iSplit; first done.
          iApply (refine_T with "HK [Hv Hh'] HSP").
          iSplitL "Hv"; first done.
          iApply (refine_cons (R := RChunk) with "[Hv] [Hh']").
          iApply (repₚ_cong (T1 := STerm τ) (scchunk_ptsreg reg) (chunk_ptsreg reg) with "Hv").
          { now intros. }
          now iApply (RList_RInst with "Hh'").
      - cbn. now iDestruct "HSP" as "%fls".
    Qed.

    Lemma refine_write_register {τ} (reg : 𝑹𝑬𝑮 τ) {w} :
      ⊢ ℛ⟦RVal τ -> RHeap -> RPureSpec (RProd (RVal τ) RHeap)⟧
        (CPureSpec.write_register reg) (SPureSpec.write_register (w := w) reg).
    Proof.
      unfold SPureSpec.write_register, SPureSpec.pure, T.
      iIntros (v sv) "#Hv %h %sh #Hh %K %sK HK HSP".
      destruct (find_chunk_ptsreg_precise_spec reg sh) as [[st sh'] HIn|].
      - cbv [CPureSpec.write_register CPureSpec.consume_chunk CPureSpec.pure
               CPureSpec.produce_chunk CPureSpec.bind CPureSpec.angelic].
        iDestruct (eval_ex (AT := STerm τ) st) as "(%v' & Hv')".
        iDestruct (eval_ex (AT := SHeap) sh') as "(%h' & Hh')".
        iExists v'.
        rewrite CPureSpec.wp_angelic_list.
        iExists (scchunk_ptsreg reg v', h').
        iSplitR.
        + rewrite RList_RInst.
          iStopProof. unfold RInst.
          crushPredEntails3. now subst.
        + rewrite CPureSpec.wp_assert_eq_chunk.
          iSplit; first done.
          iApply (refine_T with "HK [Hv Hh'] HSP").
          iSplitL "Hv"; first done.
          iApply (refine_cons (R := RChunk) with "[Hv] [Hh']").
          iApply (repₚ_cong (T1 := STerm τ) (scchunk_ptsreg reg) (chunk_ptsreg reg) with "Hv").
          { now intros. }
          now iApply (RList_RInst with "Hh'").
      - cbn. now iDestruct "HSP" as "%fls".
    Qed.

  End PureSpec.

  Definition RHeapSpec [SA CA] (RA : Rel SA CA) :
    Rel (SHeapSpec SA) (CHeapSpec CA) :=
    □ᵣ(RA -> RHeap -> ℙ) -> RHeap -> ℙ.

  Module HeapSpec.

    Lemma refine_run {w} :
      ⊢ ℛ⟦RHeapSpec RUnit -> ℙ⟧ CHeapSpec.run (SHeapSpec.run (w := w)).
    Proof.
      unfold CHeapSpec.run, SHeapSpec.run.
      iIntros (m sm) "Hm".
      iApply "Hm".
      - iIntros (w2 ω2) "!> %u %su _ %h %sh Hh _".
        now iPureIntro.
      - now iApply (refine_nil (R := RChunk)).
    Qed.

    Lemma refine_lift_purespec `{RA : Rel SA CA} {w} :
      ⊢ ℛ⟦RPureSpec RA -> RHeapSpec RA⟧
        CHeapSpec.lift_purespec (SHeapSpec.lift_purespec (w := w)).
    Proof.
      unfold SHeapSpec.lift_purespec, CHeapSpec.lift_purespec.
      iIntros (m sm) "Hm %K %sK HK %h %sh Hh".
      iApply "Hm".
      iIntros (w1 ω1) "!> %a %sa Ha".
      iApply ("HK" with "Ha").
      rewrite !RList_RInst.
      now iApply (refine_inst_persist with "Hh").
    Qed.

    Lemma refine_pure `{RA : Rel SA CA} {w} :
      ⊢ ℛ⟦RA -> RHeapSpec RA⟧ CHeapSpec.pure (SHeapSpec.pure (w := w)).
    Proof.
      iIntros (v sv) "rv %Φ %sΦ rΦ %h %sh rh".
      iApply (refine_T with "rΦ rv rh").
    Qed.

    Lemma refine_bind `{RA : Rel SA CA, RB : Rel SB CB} {w} :
      ⊢ ℛ⟦RHeapSpec RA -> □ᵣ(RA -> RHeapSpec RB) -> RHeapSpec RB⟧
        CHeapSpec.bind (SHeapSpec.bind (w := w)).
    Proof.
      iIntros (cm sm) "rm %cf %sf rf %Φ %sΦ rΦ %ch %sh rh".
      unfold SHeapSpec.bind, CHeapSpec.bind. iApply ("rm" with "[rf rΦ] rh").
      iIntros (w1 θ1) "!> %ca %sa ra %ch1 %sh1 rh1".
      iApply ("rf" with "ra [rΦ] rh1").
      now iApply (refine_four with "rΦ").
    Qed.

    Lemma refine_angelic x σ {w} :
      ⊢ ℛ⟦RHeapSpec (RVal σ)⟧
        (CHeapSpec.angelic σ) (SHeapSpec.angelic (w := w) x σ).
    Proof.
      unfold CHeapSpec.angelic, SHeapSpec.angelic.
      iApply (refine_lift_purespec (RA := RVal _)).
      iApply (PureSpec.refine_angelic).
    Qed.

    Lemma refine_demonic x σ {w} :
      ⊢ ℛ⟦RHeapSpec (RVal σ)⟧
        (CHeapSpec.demonic σ) (SHeapSpec.demonic (w := w) x σ).
    Proof.
      unfold CHeapSpec.demonic, SHeapSpec.demonic.
      iApply refine_lift_purespec.
      iApply PureSpec.refine_demonic.
    Qed.

    Lemma refine_angelic_ctx {N : Set} {n : N -> LVar} Δ {w} :
      ⊢ ℛ⟦RHeapSpec (RNEnv N Δ)⟧
          (CHeapSpec.angelic_ctx Δ) (SHeapSpec.angelic_ctx (w := w) n Δ).
    Proof.
      unfold CHeapSpec.angelic_ctx, SHeapSpec.angelic_ctx.
      iApply refine_lift_purespec.
      iApply PureSpec.refine_angelic_ctx.
    Qed.

    Lemma refine_demonic_ctx {N : Set} {n : N -> LVar} Δ {w} :
      ⊢ ℛ⟦RHeapSpec (RNEnv N Δ)⟧
          (CHeapSpec.demonic_ctx Δ) (SHeapSpec.demonic_ctx (w := w) n Δ).
    Proof.
      unfold CHeapSpec.demonic_ctx, SHeapSpec.demonic_ctx.
      iApply refine_lift_purespec.
      iApply PureSpec.refine_demonic_ctx.
    Qed.

    Lemma refine_angelic_binary `{RA : Rel SA CA} {w} :
      ⊢ ℛ⟦RHeapSpec RA -> RHeapSpec RA -> RHeapSpec RA⟧
        CHeapSpec.angelic_binary (SHeapSpec.angelic_binary (w := w)).
    Proof.
      unfold CHeapSpec.angelic_binary, SHeapSpec.angelic_binary.
      iIntros (cm1 sm1) "#rm1 %cm2 %sm2 #rm2 %cΦ %sΦ #rΦ %ch %sh #rh".
      iApply refine_symprop_angelic_binary.
      - now iApply "rm1".
      - now iApply "rm2".
    Qed.

    Lemma refine_demonic_binary `{RA : Rel SA CA} {w} :
      ⊢ ℛ⟦RHeapSpec RA -> RHeapSpec RA -> RHeapSpec RA⟧
        CHeapSpec.demonic_binary (SHeapSpec.demonic_binary (w := w)).
    Proof.
      unfold CHeapSpec.demonic_binary, SHeapSpec.demonic_binary.
      iIntros (cm1 sm1) "#rm1 %cm2 %sm2 #rm2 %cΦ %sΦ #rΦ %ch %sh #rh".
      iApply refine_symprop_demonic_binary.
      - now iApply "rm1".
      - now iApply "rm2".
    Qed.

    Lemma refine_debug `{RA : Rel SA CA} {w} :
      ⊢ ℛ⟦RMsg _ (RHeapSpec RA -> RHeapSpec RA)⟧
        CHeapSpec.debug (SHeapSpec.debug (w := w)).
    Proof.
      unfold CHeapSpec.debug, SHeapSpec.debug.
      iIntros (msg cm sm) "rm %cΦ %sΦ #rΦ %ch %sh rh".
      iApply refine_symprop_debug.
      iApply "rm"; auto.
    Qed.

    Lemma refine_assert_formula {w} :
      ⊢ ℛ⟦RMsg _ (RFormula -> RHeapSpec RUnit)⟧
        CHeapSpec.assert_formula (SHeapSpec.assert_formula (w := w)).
    Proof.
      unfold CHeapSpec.assert_formula, SHeapSpec.assert_formula,
               CHeapSpec.lift_purespec.
      iIntros (msg cF sF) "rF %cΦ %sΦ rΦ %ch %sh rh".
      iApply (PureSpec.refine_assert_formula with "rF").
      iIntros (w1 θ1) "!> %cu %su ru".
      iApply ("rΦ" with "ru").
      rewrite !RList_RInst.
      now iApply (refine_inst_persist with "rh").
    Qed.

    Lemma refine_assume_formula {w} :
      ⊢ ℛ⟦RFormula -> RHeapSpec RUnit⟧
        CHeapSpec.assume_formula (SHeapSpec.assume_formula (w := w)).
    Proof.
      unfold CHeapSpec.assume_formula, SHeapSpec.assume_formula.
      iIntros (cF sF) "rF".
      iApply refine_lift_purespec.
      now iApply PureSpec.refine_assume_formula.
    Qed.

    Lemma refine_produce_chunk {w} :
      ⊢ ℛ⟦RChunk -> RHeapSpec RUnit⟧
        CHeapSpec.produce_chunk (SHeapSpec.produce_chunk (w := w)).
    Proof.
      iIntros (cc sc) "rc %cΦ %sΦ rΦ %ch %sh rh".
      unfold SHeapSpec.produce_chunk, CHeapSpec.produce_chunk.
      iApply (PureSpec.refine_produce_chunk with "rc rh").
      iIntros (w1 θ1) "!>".
      now iApply "rΦ".
    Qed.

    Lemma refine_consume_chunk {w} :
      ⊢ ℛ⟦RChunk -> RHeapSpec RUnit⟧
        CHeapSpec.consume_chunk (SHeapSpec.consume_chunk (w := w)).
    Proof.
      iIntros (cc sc) "rc %cΦ %sΦ rΦ %ch %sh rh".
      unfold SHeapSpec.consume_chunk, CHeapSpec.consume_chunk.
      iApply (PureSpec.refine_consume_chunk with "rc rh").
      iIntros (w1 θ1) "!>".
      now iApply "rΦ".
    Qed.

    Lemma refine_consume_chunk_angelic {w} :
      ⊢ ℛ⟦RChunk -> RHeapSpec RUnit⟧
        CHeapSpec.consume_chunk (SHeapSpec.consume_chunk_angelic (w := w)).
    Proof.
      iIntros (cc sc) "rc %cΦ %sΦ rΦ %ch %sh rh".
      unfold SHeapSpec.consume_chunk_angelic, CHeapSpec.consume_chunk.
      iApply (PureSpec.refine_consume_chunk_angelic with "rc rh").
      iIntros (w1 θ1) "!>".
      now iApply "rΦ".
    Qed.

    Lemma refine_produce {Σ} (asn : Assertion Σ) :
      ∀ w, ⊢ ℛ⟦RInst (Sub Σ) (Valuation Σ) -> RHeapSpec RUnit⟧
               (CHeapSpec.produce asn) (SHeapSpec.produce (w := w) asn).
    Proof.
      induction asn; cbn - [RSat]; iIntros (w δ sδ) "#rδ".
      - iApply refine_assume_formula.
        now iApply refine_instprop_subst.
      - iApply refine_produce_chunk.
        now iApply (refine_inst_subst (T := Chunk)).
      - iApply refine_produce_chunk.
        now iApply (refine_inst_subst (T := Chunk)).
      - iApply (refine_bind (RA := RMatchResult pat) (RB := RUnit)).
        iApply (refine_lift_purespec (RA := RMatchResult pat)).
        { iApply PureSpec.refine_demonic_pattern_match.
          now iApply (refine_inst_subst (T := STerm σ) with "rδ").
        }
        iIntros (w1 θ1) "!> %mr %smr Hmr".
        destruct mr as [pc sub].
        destruct smr as [spc ssub].
        iDestruct "Hmr" as "(%e & Hmr)"; subst; cbn -[RSat].
        iApply H.
        iDestruct (refine_inst_persist with "rδ") as "rδp".
        iApply (repₚ_cong₂ (T1 := Sub _) (T2 := Sub _) (T3 := Sub (Σ ▻▻ PatternCaseCtx pc)) env.cat env.cat with "[$rδp $Hmr]").
        intros. now rewrite inst_env_cat.
      - iApply (refine_bind (RA := RUnit) (RB := RUnit)).
        + now iApply IHasn1.
        + iIntros (w1 θ1) "!> %u %su _".
          iApply IHasn2.
          iApply (refine_inst_persist with "rδ").
      - iApply (refine_demonic_binary (RA := RUnit)).
        + now iApply IHasn1.
        + now iApply IHasn2.
      - iApply (refine_bind (RA := RVal τ) (RB := RUnit)).
        + iApply refine_demonic.
        + iIntros (w3 ω3) "!> %v %sv Hv".
          iApply IHasn.
          iDestruct (refine_inst_persist with "rδ") as "rδp".
          iApply (repₚ_cong₂ (T1 := Sub _) (T2 := STerm _) (T3 := Sub (Σ ▻ ς∷τ)) (fun δ => env.snoc δ (ς∷τ)) (fun δ => env.snoc δ (ς∷τ)) with "[$rδp $Hv]").
          now intros.
      - iApply (refine_debug (RA := RUnit)).
        now iApply (refine_pure (RA := RUnit)).
    Qed.

    Lemma refine_consume {Σ} (asn : Assertion Σ) :
      ∀ w, ⊢ ℛ⟦RInst (Sub Σ) (Valuation Σ) -> RHeapSpec RUnit⟧
               (CHeapSpec.consume asn) (SHeapSpec.consume asn (w := w) ).
    Proof.
      induction asn; cbn - [RSat]; iIntros (w δ sδ) "#rδ".
      - iApply refine_assert_formula.
        now iApply refine_instprop_subst.
      - iApply refine_consume_chunk.
        now iApply (refine_inst_subst (T := Chunk)).
      - iApply refine_consume_chunk_angelic.
        now iApply (refine_inst_subst (T := Chunk)).
      - iApply (refine_bind (RA := RMatchResult pat) (RB := RUnit)).
        iApply (refine_lift_purespec (RA := RMatchResult pat)).
        { iApply PureSpec.refine_angelic_pattern_match.
          now iApply (refine_inst_subst (T := STerm σ) with "rδ").
        }
        iIntros (w1 θ1) "!> %mr %smr Hmr".
        destruct mr as [pc sub].
        destruct smr as [spc ssub].
        iDestruct "Hmr" as "(%e & Hmr)"; subst; cbn -[RSat].
        iDestruct (refine_inst_persist with "rδ") as "rδp".
        iApply H.
        iApply (repₚ_cong₂ (T1 := Sub _) (T2 := Sub _) (T3 := Sub (Σ ▻▻ PatternCaseCtx pc)) env.cat env.cat with "[$rδp $Hmr]").
        intros. now rewrite inst_env_cat.
      - iApply (refine_bind (RA := RUnit) (RB := RUnit)).
        + now iApply IHasn1.
        + iIntros (w1 θ1) "!> %u %su _".
          iApply IHasn2.
          iApply (refine_inst_persist with "rδ").
      - iApply (refine_angelic_binary (RA := RUnit)).
        + now iApply IHasn1.
        + now iApply IHasn2.
      - iApply (refine_bind (RA := RVal τ) (RB := RUnit)).
        + iApply refine_angelic.
        + iIntros (w3 ω3) "!> %v %sv Hv".
          iApply IHasn.
          iDestruct (refine_inst_persist with "rδ") as "rδp".
          iApply (repₚ_cong₂ (T1 := Sub _) (T2 := STerm _) (T3 := Sub (Σ ▻ ς∷τ)) (fun δ => env.snoc δ (ς∷τ)) (fun δ => env.snoc δ (ς∷τ)) with "[$rδp $Hv]").
          now intros.
      - iApply (refine_debug (RA := RUnit)).
        now iApply (refine_pure (RA := RUnit)).
    Qed.

    Lemma refine_read_register {τ} (reg : 𝑹𝑬𝑮 τ) {w} :
      ⊢ ℛ⟦RHeapSpec (RVal τ)⟧ (CHeapSpec.read_register reg) (SHeapSpec.read_register reg (w := w)).
    Proof.
      iIntros (Φ sΦ) "rΦ %ch %sh rh".
      unfold CHeapSpec.read_register, SHeapSpec.read_register.
      iApply (PureSpec.refine_read_register with "rh").
      iIntros (w1 θ1) "!> %vh %svh  Hvh".
      destruct vh as [v h2].
      destruct svh as [sv sh2].
      iDestruct "Hvh" as "[Hv Hh2]".
      now iApply ("rΦ" with "Hv").
    Qed.

    Lemma refine_write_register {τ} (reg : 𝑹𝑬𝑮 τ) {w} :
      ⊢ ℛ⟦RVal τ -> RHeapSpec (RVal τ)⟧ (CHeapSpec.write_register reg) (SHeapSpec.write_register reg (w := w)).
    Proof.
      iIntros (v sv) "rv %Φ %sΦ rΦ %h %sh rh".
      unfold CHeapSpec.write_register, SHeapSpec.write_register.
      iApply (PureSpec.refine_write_register with "rv rh").
      iIntros (w1 θ1) "!> %vh %svh Hvh".
      destruct vh as [v2 h2].
      destruct svh as [sv2 sh2].
      iDestruct "Hvh" as "[Hv2 Hh2]".
      now iApply ("rΦ" with "Hv2").
    Qed.

    Lemma refine_call_contract {Δ τ} (c : SepContract Δ τ) {w} :
      ⊢  ℛ⟦RInst (SStore Δ) (CStore Δ) -> RHeapSpec (RVal τ)⟧
        (CHeapSpec.call_contract c) (SHeapSpec.call_contract c (w := w)).
    Proof.
      iIntros (cδ sδ) "#rδ".
      destruct c as [lvars pats req res ens]; cbn.
      iApply refine_bind.
      iApply refine_lift_purespec.
      iApply PureSpec.refine_angelic_ctx.
      iIntros (w1 θ1)  "!> %cevars %sevars #revars".
      iApply refine_bind.
      iApply refine_lift_purespec.
      iApply PureSpec.refine_assert_eq_nenv.
      iApply (refine_inst_subst (T := (SStore Δ))); auto.
      iApply (refine_inst_persist (AT := SStore Δ)); auto.
      iIntros (w2 θ2) "!> %cu %su _". clear cu su.
      iApply refine_bind.
      iApply refine_consume.
      iApply (refine_inst_persist (AT := Sub lvars)); auto.
      iIntros (w3 θ3) "!> %cu %su _". clear cu su.
      iApply refine_bind.
      iApply refine_demonic.
      iIntros (w4 θ4) "!> %v %sv #rv".
      iApply refine_bind.
      iApply refine_produce.
      iApply refine_sub_snoc.
      iSplit; auto.
      rewrite !forgetting_trans.
      rewrite persist_trans.
      iApply (refine_inst_persist (AT := Sub lvars)). iModIntro.
      iApply (refine_inst_persist (AT := Sub lvars)). iModIntro.
      iApply (refine_inst_persist (AT := Sub lvars)). auto.
      iIntros (w5 θ5) "!> %cu %su #_". clear cu su.
      iApply refine_pure.
      iApply (refine_inst_persist (AT := STerm _) (A := Val _)).
      auto.
      Unshelve.
      all: eauto with typeclass_instances.
    Qed.

    Lemma refine_call_lemma {Δ} (lem : Lemma Δ) w :
      ⊢ ℛ⟦RInst (SStore Δ) (CStore Δ) -> RHeapSpec RUnit⟧
          (CHeapSpec.call_lemma lem) (SHeapSpec.call_lemma lem (w := w)).
    Proof.
      iIntros (cδ sδ) "#rδ".
      destruct lem as [lvars pats req ens]; cbn.
      iApply refine_bind.
      iApply refine_lift_purespec.
      iApply PureSpec.refine_angelic_ctx.
      iIntros (w1 θ1)  "!> %cevars %sevars #revars".
      iApply refine_bind.
      iApply refine_lift_purespec.
      iApply PureSpec.refine_assert_eq_nenv.
      iApply (refine_inst_subst (T := (SStore Δ))); auto.
      iApply (refine_inst_persist (AT := SStore Δ)); auto.
      iIntros (w2 θ2) "!> %cu %su _". clear cu su.
      iApply refine_bind.
      iApply refine_consume.
      iApply (refine_inst_persist (AT := Sub lvars)); auto.
      iIntros (w3 θ3) "!> %cu %su _". clear cu su.
      iApply refine_produce.
      rewrite !forgetting_trans.
      iApply (refine_inst_persist (AT := Sub lvars)). iModIntro.
      iApply (refine_inst_persist (AT := Sub lvars)). auto.
    Qed.

  End HeapSpec.

  Class RefineCompat `(R : Rel AT A) (v : A)  w (vs : AT w) (Ob : Pred w) :=
    MkRefineCompat {
        refine_compat_lemma : Ob ⊢ ℛ⟦ R ⟧ v vs
      }.
  #[export] Hint Mode RefineCompat - - - + + + - : typeclass_instances.
  #[global] Arguments refine_compat_lemma {AT A R v w vs Ob} rci : rename.
  #[global] Arguments RefineCompat {AT A} R v w vs Ob%I.
  #[global] Arguments MkRefineCompat {AT A R v w vs Ob%I} rci : rename.

  Program Definition refine_compat_impl `{RA : Rel AT A} `{RB : Rel BT B} {f v w fs vs} {Pf}
    (compatf : RefineCompat (RA -> RB) f w fs Pf) : RefineCompat RB (f v) w (fs vs) (Pf ∗ RSat RA v vs) :=
    MkRefineCompat _.
  Next Obligation.
    iIntros (AT A RA BT B RB f v w fs vs Pf compatf) "[Hcf Hv]".
    now iApply (refine_compat_lemma compatf with "Hcf").
  Qed.
  (* The Hint Resolve used "simple apply", which wasn't instantiating evars sufficiently strongly. Hint Extern with eapply works better. *)
  #[export] Hint Extern 1 (RefineCompat ?RB (?f ?v) ?w (?fs ?vs) _) => eapply (refine_compat_impl (RB := RB) (fs := fs) (vs := vs) (f := f) (v := v) (w := w)) : typeclass_instances.

  #[export] Program Instance refine_compat_forall {𝑲} {AT : forall K : 𝑲, TYPE} {A : forall K : 𝑲, Type} (RA : forall K, Rel (AT K) (A K)) {f w fs k P}
    (compatf : RefineCompat (RForall RA) f w fs P) : RefineCompat (RA k) (f k) w (fs k) P :=
    MkRefineCompat _.
  Next Obligation.
    iIntros (𝑲 AT A RA f w fs k P compatf) "Hcf".
    now iApply (refine_compat_lemma compatf with "Hcf").
  Qed.

  Definition refine_compat_inst_persist {AT A} `{InstSubst AT A, @SubstLaws AT _} {v} {w1 w2} {ω : Acc w1 w2} {t} :
    RefineCompat (RInst AT A) v w2 (persist t ω) _ :=
    MkRefineCompat (refine_inst_persist _).
  #[global] Opaque refine_compat_inst_persist.
  #[export] Hint Extern 0 (RefineCompat _ ?v _ (persist ?t ?ω) _) => refine (refine_compat_inst_persist (v := v) (t := t) (ω := ω)) : typeclass_instances.

  #[export] Instance refine_compat_inst_persist_term {σ} {v} {w1 w2} {ω : Acc w1 w2} {t} :
    RefineCompat (RVal σ) v w2 (persist__term t ω) _ :=
    MkRefineCompat (refine_inst_persist _).

  #[export] Instance refine_compat_lift `{InstLift AT A} {w : World} (a : A) :
    RefineCompat (RInst AT A) a w (lift a) _ :=
    MkRefineCompat (refine_lift a).

  #[export] Instance refine_compat_term_val {σ} {v w} : RefineCompat (RVal σ) v w (term_val σ v) _ :=
    MkRefineCompat refine_term_val.

  Definition refine_compat_term_binop {w τ1 τ2 τ3} {op : BinOp τ1 τ2 τ3} {a1 sa1 a2 sa2} :
    RefineCompat (RVal τ3) (bop.eval op a1 a2)  w (term_binop op sa1 sa2) _ :=
    MkRefineCompat refine_term_binop.
  #[global] Opaque refine_compat_term_binop.
  #[export] Hint Extern 0 (RefineCompat (RVal _) _ _ (term_binop ?binop _ _) _) => ( refine (refine_compat_term_binop (op := binop)) ) : typeclass_instances.

  #[export] Instance refine_compat_formula_bool {w : World} {v} {sv : Term w ty.bool} :
    RefineCompat RFormula (v = true) w (formula_bool sv) _ :=
    MkRefineCompat refine_formula_bool.

  Definition refine_compat_formula_relop {w : World} {σ v1 v2} {sv1 sv2 : Term w σ}  {relop : RelOp σ} :
    RefineCompat RFormula (bop.eval_relop_prop relop v1 v2) w (formula_relop relop sv1 sv2) _ :=
    MkRefineCompat refine_formula_relop.
  #[global] Opaque refine_compat_formula_relop.
  #[export] Hint Extern 0 (RefineCompat RFormula _ _ (formula_relop ?relop _ _) _) => ( refine (refine_compat_formula_relop (relop := relop)) ) : typeclass_instances.

  #[export] Instance refine_compat_chunk_ptsreg {w σ} {pc a ta} :
    RefineCompat RChunk (scchunk_ptsreg pc a) w(chunk_ptsreg (σ := σ) pc ta) _ :=
    MkRefineCompat refine_chunk_ptsreg.

  #[export] Instance refine_compat_chunk_user {w c vs svs} :
    RefineCompat RChunk (scchunk_user c vs) w (chunk_user c svs) _ :=
    MkRefineCompat refine_chunk_user.

  #[export] Instance refine_compat_env_snoc {Δ : Ctx Ty} {τ} {w : World} {vs : Env Val Δ} {svs : Env (Term w) Δ} {v : Val τ} {sv : Term w τ} :
    RefineCompat (REnv (Δ ▻ τ)) (vs ► ( τ ↦ v ))%env w (svs ► (τ ↦ sv ))%env _ :=
    MkRefineCompat refine_env_snoc.

  #[export] Instance refine_compat_sub_snoc {τ : Ty} {Γ : LCtx} {x : LVar}
    {w : World} {vs : NamedEnv Val Γ} {svs : NamedEnv (Term w) Γ}
    {v : Val τ} {sv : Term w τ} :
    RefineCompat (RNEnv LVar (Γ ▻ x∷τ)) (vs.[x∷τ ↦ v])%env w (sub_snoc svs (x∷τ) sv) _ :=
    MkRefineCompat refine_sub_snoc.

  #[export] Instance refine_compat_env_nil {w : World} {vs : Env Val [ctx]} {svs : Env (Term w) [ctx]} :
    RefineCompat (REnv [ctx]) vs  w svs _ :=
    MkRefineCompat refine_env_nil.

  #[export] Instance refine_compat_named_env_sub_acc_trans {Σ : LCtx} {w1 w2 : World} {ι : Valuation Σ} {ω1 : wlctx Σ ⊒ w1} {ω2 : w1 ⊒ w2}:
    RefineCompat (RNEnv LVar (wlctx Σ)) ι w2 (sub_acc (acc_trans ω1 ω2)) _ :=
    MkRefineCompat refine_namedenv_sub_acc_trans.

  (* #[export] Instance refine_compat_named_env_sub_acc {Σ : LCtx} {w : World} {ι : Valuation Σ} {ω : wlctx Σ ⊒ w} : *)
  (*   RefineCompat (RNEnv LVar (wlctx Σ)) ι w (sub_acc ω) _ | 10 := *)
  (*   MkRefineCompat refine_namedenv_sub_acc. *)

  #[export] Instance refine_compat_heapspec_pure `{R : Rel AT A} {w} :
    RefineCompat (R -> RHeapSpec R) CHeapSpec.pure w (SHeapSpec.pure (w := w)) _ :=
    MkRefineCompat (HeapSpec.refine_pure (RA := R)).

  #[export] Instance refine_compat_heapspec_bind `{RA : Rel AT A} `{RB : Rel BT B} {w} :
    RefineCompat (RHeapSpec RA -> (□ᵣ (RA -> RHeapSpec RB)) -> RHeapSpec RB)
      CHeapSpec.bind w (SHeapSpec.bind (w := w)) _ | (RefineCompat _ _ _ SHeapSpec.bind _) :=
    MkRefineCompat HeapSpec.refine_bind.

  #[export] Instance refine_compat_heapspec_angelic (x : option LVar) σ {w : World}:
    RefineCompat (RHeapSpec (RVal σ)) (CHeapSpec.angelic σ) w (SHeapSpec.angelic (w := w) x σ) emp :=
    MkRefineCompat (HeapSpec.refine_angelic x σ).

  #[export] Instance refine_compat_heapspec_demonic (x : option LVar) σ {w : World} :
    RefineCompat (RHeapSpec (RVal σ)) (CHeapSpec.demonic σ) w (SHeapSpec.demonic (w := w) x σ) emp :=
    MkRefineCompat (HeapSpec.refine_demonic x σ).

  #[export] Instance refine_compat_heapspec_angelic_ctx {N : Set} (n : N -> LVar) {w : World} Δ :
    RefineCompat (RHeapSpec (RNEnv N Δ)) (CHeapSpec.angelic_ctx Δ) w (SHeapSpec.angelic_ctx (w := w) n Δ) emp :=
    MkRefineCompat (HeapSpec.refine_angelic_ctx Δ).

  #[export] Instance refine_compat_heapspec_demonic_ctx {N : Set} (n : N -> LVar) {w : World} Δ :
    RefineCompat (RHeapSpec (RNEnv N Δ)) (CHeapSpec.demonic_ctx Δ) w (SHeapSpec.demonic_ctx (w := w) n Δ) emp :=
    MkRefineCompat (HeapSpec.refine_demonic_ctx Δ).

  #[export] Instance refine_compat_heapspec_assume_formula {w} :
    RefineCompat (RFormula -> RHeapSpec RUnit) CHeapSpec.assume_formula w (SHeapSpec.assume_formula (w := w)) _ :=
    MkRefineCompat HeapSpec.refine_assume_formula.

  #[export] Instance refine_compat_heapspec_assert_formula {w} :
    RefineCompat (RMsg _ (RFormula -> RHeapSpec RUnit)) CHeapSpec.assert_formula w (SHeapSpec.assert_formula (w := w)) _ :=
    MkRefineCompat HeapSpec.refine_assert_formula.

  #[export] Instance refine_compat_heapspec_produce_chunk {w} :
    RefineCompat (RChunk -> RHeapSpec RUnit) CHeapSpec.produce_chunk w (SHeapSpec.produce_chunk (w := w)) _ :=
    MkRefineCompat HeapSpec.refine_produce_chunk.

  #[export] Instance refine_compat_heapspec_consume_chunk {w} :
    RefineCompat (RChunk -> RHeapSpec RUnit) CHeapSpec.consume_chunk w (SHeapSpec.consume_chunk (w := w)) _ :=
    MkRefineCompat HeapSpec.refine_consume_chunk.

  #[export] Instance refine_compat_heapspec_consume_chunk_angelic {w} :
    RefineCompat (RChunk -> RHeapSpec RUnit) CHeapSpec.consume_chunk w (SHeapSpec.consume_chunk_angelic (w := w)) _ :=
    MkRefineCompat HeapSpec.refine_consume_chunk_angelic.

  #[export] Instance refine_compat_heapspec_produce {Σ} (asn : Assertion Σ) {w} :
    RefineCompat (RNEnv LVar Σ -> RHeapSpec RUnit) (CHeapSpec.produce asn) w (SHeapSpec.produce asn (w := w)) _ :=
    MkRefineCompat (HeapSpec.refine_produce asn w).

  #[export] Instance refine_compat_heapspec_consume {Σ} (asn : Assertion Σ) {w} :
    RefineCompat (RNEnv LVar Σ -> RHeapSpec RUnit) (CHeapSpec.consume asn) w (SHeapSpec.consume asn (w := w)) _ :=
    MkRefineCompat (HeapSpec.refine_consume asn w).

  #[export] Instance refine_compat_heapspec_read_register {τ} (r : 𝑹𝑬𝑮 τ) {w} :
    RefineCompat (RHeapSpec (RVal τ)) (CHeapSpec.read_register r) w (SHeapSpec.read_register r (w := w)) _ :=
    MkRefineCompat (HeapSpec.refine_read_register r).

  #[export] Instance refine_compat_heapspec_write_register {τ} (r : 𝑹𝑬𝑮 τ) {w} :
    RefineCompat (RVal τ -> RHeapSpec (RVal τ)) (CHeapSpec.write_register r) w (SHeapSpec.write_register r (w := w)) _ :=
    MkRefineCompat (HeapSpec.refine_write_register r).

  Class RefineCompatGen (w : World) (P : Pred w) (Ob : Pred w) (withbase : bool):=
    MkRefineCompatGen {
        refine_compat_gen_lemma : Ob ⊢ P
      }.
  #[global] Arguments RefineCompatGen w P%I Ob%I withbase.
  #[global] Arguments MkRefineCompatGen {w} {P} _%I _ {_}.
  #[global] Arguments refine_compat_gen_lemma {w} P%I {Ob} withbase rcg : rename.

  #[export] Program Instance refine_compat_gen_step `(R : Rel AT A) (v : A) (w : World) (vs : AT w) Ob1 Ob2 b
    (rc : RefineCompat R v w vs Ob1)
    (iter : RefineCompatGen Ob1 Ob2 b) :
    RefineCompatGen (ℛ⟦ R ⟧ v vs) Ob2 b := MkRefineCompatGen Ob2 _.
  Next Obligation.
    iIntros (AT A R v w vs Ob1 Ob2 b rc iter) "H".
    iApply (refine_compat_lemma with "[H]").
    now iApply (refine_compat_gen_lemma with "[H]").
  Qed.

  #[export] Program Instance refine_compat_gen_base_true {w} {b} :
    RefineCompatGen (w := w) True emp b := MkRefineCompatGen emp _.
  Next Obligation.
    now iIntros.
  Qed.

  #[export] Program Instance refine_compat_gen_base_emp {w} {b} :
    RefineCompatGen (w := w) emp emp b := MkRefineCompatGen emp _.
  Next Obligation.
    now iIntros.
  Qed.

  #[export] Program Instance refine_compat_gen_base {w} (P : Pred w):
    RefineCompatGen (w := w) P P true | 10 := MkRefineCompatGen P _.
  Next Obligation.
    now iIntros.
  Qed.

  Class ObSep {w} (P1 P2 P3 : Pred w) : Prop :=
    obsep_equiv : P1 ∗ P2 ⊣⊢ P3.
  #[export] Instance obsep_empL {w} {P : Pred w} : ObSep emp%I P P.
  Proof. apply bi.emp_sep. Qed.
  #[export] Instance obsep_empR {w} {P : Pred w} : ObSep P emp%I P.
  Proof. apply bi.sep_emp. Qed.
  #[export] Instance obsep_sep {w} {P1 P2 : Pred w} : ObSep P1 P2 (P1 ∗ P2)%I | 1.
  Proof. done. Qed.

  #[export] Program Instance refine_compat_gen_split {w} {P1 P2 : Pred w} {Ob1 Ob2 Ob} {b}
    (rcg1 : RefineCompatGen P1 Ob1 b) (rcg2 : RefineCompatGen P2 Ob2 b) {_ : ObSep Ob1 Ob2 Ob} :
    RefineCompatGen (w := w) (P1 ∗ P2) Ob b | 1 := MkRefineCompatGen Ob _.
  Next Obligation.
    iIntros (w P1 P2 Ob1 Ob2 Ob b rcg1 rcg2 obsep) "H".
    rewrite -(obsep_equiv (ObSep := obsep)).
    iDestruct "H" as "(H1 & H2)".
    iSplitL "H1".
    - iApply (refine_compat_gen_lemma with "H1").
    - iApply (refine_compat_gen_lemma with "H2").
  Qed.

End RefinementMonadsOn.

(* Local Variables: *)
(* proof-omit-proofs-option: t *)
(* End: *)
