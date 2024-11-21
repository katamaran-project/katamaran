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

  #[export] Instance RPureSpec [AT A] (R : Rel AT A) :
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

  Module RPureSpec.


    #[export] Instance rpurespecm : RPureSpecM RPureSpec.
    Proof.
      constructor.
      - exact @refine_pure.
      - exact @refine_bind'.
      - exact @refine_error.
      - exact @refine_block.
      - exact @refine_angelic.
      - exact @refine_demonic.
      - exact @refine_angelic_ctx.
      - exact @refine_demonic_ctx.
      - exact @refine_assert_pathcondition.
      - exact @refine_assert_formula.
      - exact @refine_assume_pathcondition.
      - exact @refine_assume_formula.
      - exact @refine_angelic_binary.
      - exact @refine_demonic_binary.
      - exact @refine_angelic_pattern_match.
      - exact @refine_demonic_pattern_match.
      - exact @refine_new_pattern_match.
      - exact @refine_debug.
    Qed.

  End RPureSpec.
  Export (hints) RPureSpec.

  #[export] Instance RHeap : Rel SHeap SCHeap :=
    RInst SHeap SCHeap.

  #[export] Instance RHeapSpec [AT A] (R : Rel AT A) :
    Rel (SHeapSpec AT) (CHeapSpec A) := □(R -> RHeap -> ℙ) -> RHeap -> ℙ.

  Module RHeapSpec.

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
      now apply RPureSpec.refine_pure.
    Qed.

    Lemma refine_error `{RA : Rel AT A} m :
      ℛ⟦RMsg (Box (Impl SHeap AMessage)) (RHeapSpec RA)⟧ SPureSpecM.error m.
    Proof.
      intros w ι Hpc msg spost cpost rpost sh ch rh.
      now inversion 1.
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
      now apply RPureSpec.refine_angelic.
    Qed.

    Lemma refine_demonic (x : option LVar) :
      ℛ⟦∀ σ, RHeapSpec (RVal σ)⟧ (SPureSpecM.demonic x) CPureSpecM.demonic.
    Proof.
      intros w ι Hpc σ.
      apply refine_lift_purespec; auto.
      now apply RPureSpec.refine_demonic.
    Qed.

    Lemma refine_angelic_ctx {N : Set} {n : N -> LVar} :
      ℛ⟦∀ Δ, RHeapSpec (RNEnv Δ)⟧
        (SPureSpecM.angelic_ctx n) CPureSpecM.angelic_ctx.
    Proof.
      intros w ι Hpc Δ.
      apply refine_lift_purespec; auto.
      now apply RPureSpec.refine_angelic_ctx.
    Qed.

    Lemma refine_demonic_ctx {N : Set} {n : N -> LVar} :
      ℛ⟦∀ Δ, RHeapSpec (RNEnv Δ)⟧
        (SPureSpecM.demonic_ctx n) CPureSpecM.demonic_ctx.
    Proof.
      intros w ι Hpc Δ.
      apply refine_lift_purespec; auto.
      now apply RPureSpec.refine_demonic_ctx.
    Qed.

    Lemma refine_assert_pathcondition :
      ℛ⟦RMsg _ (RPathCondition -> RHeapSpec RUnit)⟧
        SPureSpecM.assert_pathcondition CPureSpecM.assert_formula.
    Proof.
      intros w ι Hpc msg Ps ps Hps.
      apply refine_lift_purespec; auto.
      now apply RPureSpec.refine_assert_pathcondition.
    Qed.

    Lemma refine_assert_formula :
      ℛ⟦RMsg _ (RFormula -> RHeapSpec RUnit)⟧
        SPureSpecM.assert_formula CPureSpecM.assert_formula.
    Proof.
      intros w ι Hpc msg P p Hp.
      apply refine_lift_purespec; auto.
      now apply RPureSpec.refine_assert_formula.
    Qed.

    Lemma refine_assume_pathcondition :
      ℛ⟦RPathCondition -> RHeapSpec RUnit⟧
        SPureSpecM.assume_pathcondition CPureSpecM.assume_formula.
    Proof.
      intros w ι Hpc P p Hp.
      apply refine_lift_purespec; auto.
      now apply RPureSpec.refine_assume_pathcondition.
    Qed.

    Lemma refine_assume_formula :
      ℛ⟦RFormula -> RHeapSpec RUnit⟧
        SPureSpecM.assume_formula CPureSpecM.assume_formula.
    Proof.
      intros w ι Hpc P p Hp.
      apply refine_lift_purespec; auto.
      now apply RPureSpec.refine_assume_formula.
    Qed.

    Lemma refine_angelic_pattern_match {N : Set} (n : N -> LVar)
      {σ} (pat : @Pattern N σ) :
      ℛ⟦RMsg _ (RVal σ -> RHeapSpec (RMatchResult pat))⟧
        (SPureSpecM.angelic_pattern_match n pat)
        (CPureSpecM.angelic_pattern_match pat).
    Proof.
      intros w ι Hpc msg t v Htv.
      apply refine_lift_purespec; auto.
      now apply RPureSpec.refine_angelic_pattern_match.
    Qed.

    Lemma refine_demonic_pattern_match {N : Set} (n : N -> LVar)
      {σ} (pat : @Pattern N σ) :
      ℛ⟦RVal σ -> RHeapSpec (RMatchResult pat)⟧
        (SPureSpecM.demonic_pattern_match n pat)
        (CPureSpecM.demonic_pattern_match pat).
    Proof.
      intros w ι Hpc t v Htv.
      apply refine_lift_purespec; auto.
      now apply RPureSpec.refine_demonic_pattern_match.
    Qed.

    Lemma refine_new_pattern_match {N : Set} (n : N -> LVar)
      {σ} (pat : @Pattern N σ) :
      ℛ⟦RVal σ -> RHeapSpec (RMatchResult pat)⟧
        (SPureSpecM.new_pattern_match n pat)
        (CPureSpecM.new_pattern_match pat).
    Proof.
      intros w ι Hpc t v Htv.
      apply refine_lift_purespec; auto.
      now apply RPureSpec.refine_new_pattern_match.
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
        apply RPureSpec.refine_angelic_list; auto.
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
          eapply RPureSpec.refine_assert_eq_chunk; cbn; eauto.
          now rewrite inst_persist, peval_chunk_sound, inst_persist.
          now rewrite inst_sub_id.
        - intros w3 ω23 ι3 -> Hpc3 _ _ _.
          apply refine_put_heap; auto.
          eapply refine_inst_persist; eauto.
      }
    Qed.

    #[export] Instance rpurespecm : RPureSpecM RHeapSpec.
    Proof.
      constructor.
      - exact @refine_pure.
      - exact @refine_bind'.
      - exact @refine_error.
      - exact @refine_block.
      - exact @refine_angelic.
      - exact @refine_demonic.
      - exact @refine_angelic_ctx.
      - exact @refine_demonic_ctx.
      - exact @refine_assert_pathcondition.
      - exact @refine_assert_formula.
      - exact @refine_assume_pathcondition.
      - exact @refine_assume_formula.
      - exact @refine_angelic_binary.
      - exact @refine_demonic_binary.
      - exact @refine_angelic_pattern_match.
      - exact @refine_demonic_pattern_match.
      - exact @refine_new_pattern_match.
      - exact @refine_debug.
    Qed.

    #[export] Instance rheapspecm : RHeapSpecM RHeapSpec.
    Proof.
      constructor.
      - exact @refine_produce_chunk.
      - exact @refine_consume_chunk.
      - exact @refine_consume_chunk_angelic.
    Qed.

  End RHeapSpec.
  Export (hints) RHeapSpec.

End RefinementMonadInstancesOn.
