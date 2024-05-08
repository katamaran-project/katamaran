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

From iris Require bi.interface proofmode.tactics.

From Katamaran Require Import
     Signature
     Shallow.Executor
     Specification
     Symbolic.Executor
     Staging.UnifLogic
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

  Import iris.bi.interface iris.proofmode.tactics.
  Import SymProp.
  Module Import P := Pred B SIG SIG.
  Import ufl_notations.
  Import proofmode.

  Section logicalrelation.
    Import SymProp logicalrelation logicalrelation.notations ufl_notations.
    Import ModalNotations.
    Import iris.bi.interface.

    Definition sub_wmatch_patctx {w : World} {σ} {s : Term w σ} {p : @Pattern LVar σ} (pc : PatternCase p) : Sub (PatternCaseCtx pc) (wmatch w s p pc) :=
      sub_cat_right (PatternCaseCtx pc).

    Inductive DebugPred (B : LCtx → Type) {w : World} (b : B w) (P : Pred w) : Pred w := 
        MkDebugPred : ∀ w, P w -> DebugPred B b P w.

    (* nicer version of wsafe *)
    Fixpoint psafe {w : World} (p : SymProp w) : Pred w := 
      (match p with
       | angelic_binary o1 o2 => psafe o1 ∨ psafe o2
       | demonic_binary o1 o2 => psafe o1 ∧ psafe o2
       | error msg => False
       | SymProp.block => True
       | assertk fml msg o =>
           (Obligation msg fml : Pred w) ∧ forgetting (acc_formula_right fml) (psafe o)
       | assumek fml o => (instprop fml : Pred w) → forgetting (acc_formula_right fml) (psafe o)
       | angelicv b k => ∃ v, forgetting (acc_snoc_left' b v) (@psafe (wsnoc w b) k)
       | demonicv b k => ∀ v, forgetting (acc_snoc_left' b v) (@psafe (wsnoc w b) k)
       | @assert_vareq _ x σ xIn t msg k =>
          (let ζ := sub_shift xIn in
           Obligation (subst msg ζ) (formula_relop bop.eq (term_var x) (subst t ζ)) : Pred w) ∧
            assuming (acc_subst_right (xIn := xIn) t) (psafe (w := wsubst w x t) k)
       | @assume_vareq _ x σ xIn t k =>
           eqₚ (term_var x (ςInΣ := xIn)) (subst t (sub_shift xIn)) →
           let ω := acc_subst_right (xIn := xIn) t in
           assuming ω (psafe (w := wsubst w x t) k)
        | pattern_match s pat rhs =>
            ∀ (pc : PatternCase pat), 
              let ω : w ⊒ wmatch w s pat pc := acc_match_right pc in
              assuming ω (eqₚ (persist s ω) (pattern_match_term_reverse pat pc (sub_wmatch_patctx pc)) →
                        psafe (w := wmatch w s pat pc) (rhs pc))
        | pattern_match_var x pat rhs => False
          (* | pattern_match_var x pat rhs => *)
        (*   let v    : Val _        := ι.[?? x] in *)
        (*   let (c,ι__pat)            := pattern_match_val pat v in *)
        (*   let Δ    : LCtx         := PatternCaseCtx c in *)
        (*   let w1   : World        := wcat w Δ in *)
        (*   let xIn1 : x∷_ ∈ w1     := ctx.in_cat_left Δ _ in *)
        (*   let ι1   : Valuation w1 := ι ►► ι__pat in *)
        (*   let w2   : World        := wsubst w1 x (lift v) in *)
        (*   let ι2   : Valuation w2 := env.remove (x∷_) ι1 xIn1 in *)
        (*   @psafe w2 (rhs c) ι2 *)
        | debug d k => DebugPred _ d (psafe k)
        end)%I.
    #[global] Arguments psafe {w} p ι.

    (* Relatedness of symbolic and shallow propositions. The driving base case! *)
    #[export] Instance RProp : Rel SymProp Prop :=
      MkRel (fun P w SP => (psafe SP → ⌜ P ⌝)%I).

    Lemma refine_symprop_angelic_binary {w : World} :
      ⊢ ℛ⟦RProp -> RProp -> RProp⟧ (@or) (@angelic_binary w).
    Proof.
      iIntros (PC1 PS1) "#HP1 %PC2 %PS2 #HP2 #HPS"; cbn.
      iDestruct "HPS" as "[HPS1 | HPS2]".
      - iLeft. now iApply "HP1".
      - iRight. now iApply "HP2".
    Qed.

    Lemma refine_symprop_demonic_binary {w : World} :
      ⊢ ℛ⟦RProp -> RProp -> RProp⟧ (@and) (@demonic_binary w).
    Proof.
      iIntros (PC1 PS1) "#HP1 %PC2 %PS2 #HP2 #HPS"; cbn.
      iDestruct "HPS" as "[HPS1 HPS2]".
      iSplitL "HP1 HPS1".
      - now iApply "HP1".
      - now iApply "HP2".
    Qed.

    Global Instance frompure_RProp_block {w} {P} :
      FromPure false (RSat RProp P (w := w) SymProp.block) P.
    Proof. now constructor. Qed.
  End logicalrelation.
  Notation "'ℙ'" := (RProp) : rel_scope.

  Section Monads.

    Import logicalrelation.
    Import ufl_notations.

    #[export] Instance RPureSpec [SA CA] (RA : Rel SA CA) :
      Rel (SPureSpec SA) (CPureSpec CA) := □ᵣ(RA -> ℙ) -> ℙ.

    Import iris.bi.interface iris.proofmode.tactics.
    Lemma refine_run {w} :
      ⊢ ℛ⟦RPureSpec RUnit -> ℙ⟧ CPureSpec.run (SPureSpec.run (w := w)).
    Proof.
      iIntros (c cs) "Hc".
      iApply "Hc".
      iIntros (w2 ω).
      iModIntro.
      iIntros (k K) "_".
      now iPureIntro.
    Qed.

    Lemma refine_pure `{RA : Rel SA CA} {w} :
      ⊢ ℛ⟦RA -> RPureSpec RA⟧ CPureSpec.pure (SPureSpec.pure (w := w)).
    Proof.
      iIntros (v va) "Hv".
      iIntros (k K) "Hk".
      iMod "Hk".
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
      iIntros (w2 ω2).
      iSpecialize ("Hk" $! _ ω2).
      iModIntro.
      iIntros (v vs) "Hv".
      iApply ("Hk" with "Hv").
      rewrite !forgetting_unconditionally.
      iIntros (w3 ω3).
      iApply "Hkk".
    Qed.

    (* Lemma refine_block `{R : Rel AT A} : *)
    (*   ℛ⟦RPureSpec R⟧ (@SPureSpec.block AT) CPureSpec.block. *)
    (* Proof. constructor. Qed. *)

    (* Lemma refine_error `{RA : Rel AT A} m : *)
    (*   ℛ⟦RMsg _ (RPureSpec RA)⟧ (@SPureSpec.error _) m. *)
    (* Proof. intros w ι Hpc msg sΦ cΦ rΦ. inversion 1. Qed. *)

    (* Lemma refine_angelic (x : option LVar) : *)
    (*   ℛ⟦∀ σ, RPureSpec (RVal σ)⟧ (SPureSpec.angelic x) CPureSpec.angelic. *)
    (* Proof. *)
    (*   intros w0 ι0 Hpc0 σ sΦ cΦ rΦ. *)
    (*   intros [v HΦ]. exists v. revert HΦ. *)
    (*   apply rΦ; cbn; eauto. *)
    (*   - now rewrite inst_sub_wk1. *)
    (*   - now rewrite instprop_subst, inst_sub_wk1. *)
    (* Qed. *)

    (* Lemma refine_demonic (x : option LVar) : *)
    (*   ℛ⟦∀ σ, RPureSpec (RVal σ)⟧ (SPureSpec.demonic x) CPureSpec.demonic. *)
    (* Proof. *)
    (*   intros w0 ι0 Hpc0 σ sΦ cΦ rΦ. *)
    (*   intros HΦ v. cbn in HΦ. specialize (HΦ v). *)
    (*   remember (fresh_lvar w0 x) as ℓ. *)
    (*   revert HΦ. apply rΦ; *)
    (*     [ (* Boilerplate #1 *) cbn; now rewrite inst_sub_wk1 *)
    (*     | (* Boilerplate #2 *) cbn; now rewrite instprop_subst, inst_sub_wk1 *)
    (*     | ]. *)
    (*   reflexivity. *)
    (* Qed. *)

  End Monads.
    
  (* Section Basics. *)

  (*     Import logicalrelation. *)
  (*   Import ufl_notations. *)

  (*   #[export] Instance RStore (Γ : PCtx) : Rel (SStore Γ) (CStore Γ) := *)
  (*     RInst (SStore Γ) (CStore Γ). *)

  (*   #[export] Instance RStoreSpec Γ1 Γ2 `(R : Rel AT A) : *)
  (*     Rel (SStoreSpec Γ1 Γ2 AT) (CStoreSpec Γ1 Γ2 A) := *)
  (*     □ᵣ (R -> RStore Γ2 -> RHeap -> ℙ) -> RStore Γ1 -> RHeap -> ℙ. *)

  (*   Lemma refine_evalStoreSpec {Γ1 Γ2} `{RA : Rel SA CA} {w : World} : *)
  (*     ⊢ ℛ⟦RStoreSpec Γ1 Γ2 RA -> RStore Γ1 -> RHeapSpec RA⟧ *)
  (*       CStoreSpec.evalStoreSpec w (fun w => SStoreSpec.evalStoreSpec w). *)
  (*   Proof. *)
  (*     unfold SStoreSpec.evalStoreSpec, CStoreSpec.evalStoreSpec. *)
  (*     iIntros. *)
  (*     intros w ι Hpc sm cm rm sδ cδ rδ sΦ cΦ rΦ. apply rm; auto. *)
  (*     intros w1 r01 ι1 Hι1 Hpc1 sa ca ra _ _ _. apply rΦ; auto. *)
  (*   Qed. *)

  (*   Lemma refine_lift_purem {Γ} `{R : Rel AT A} : *)
  (*     ℛ⟦RPureSpec R -> RStoreSpec Γ Γ R⟧ *)
  (*       SStoreSpec.lift_purem CStoreSpec.lift_purem. *)
  (*   Proof. *)
  (*     unfold RPureSpec, RStoreSpec, SStoreSpec.lift_purem, CStoreSpec.lift_purem. *)
  (*     intros w ι Hpc ms mc Hm POST__s POST__c HPOST. *)
  (*     intros δs δc Hδ hs hc Hh. apply Hm. *)
  (*     intros w1 r01 ι1 Hι1 Hpc1 a1 a Ha. *)
  (*     eapply refine_apply; eauto. *)
  (*     eapply refine_apply; eauto. *)
  (*     eapply refine_apply; eauto. *)
  (*     eapply refine_inst_persist; eauto. *)
  (*     eapply refine_inst_persist; eauto. *)
  (*   Qed. *)

  (*   Lemma refine_block {Γ1 Γ2} `{R : Rel AT A} : *)
  (*     ℛ⟦RStoreSpec Γ1 Γ2 R⟧ SStoreSpec.block CStoreSpec.block. *)
  (*   Proof. constructor. Qed. *)

  (*   Lemma refine_error `{Subst M, OccursCheck M, R : Rel AT A} {Γ1 Γ2} : *)
  (*     forall (cm : CStoreSpec Γ1 Γ2 A), *)
  (*       ℛ⟦RMsg _ (RStoreSpec Γ1 Γ2 R)⟧ SStoreSpec.error cm. *)
  (*   Proof. intros cm w ι Hpc msg POST__s POST__c HPOST δs δc Hδ hs hc Hh []. Qed. *)

  (*   Lemma refine_pure `{R : Rel AT A} {Γ} : *)
  (*     ℛ⟦R -> RStoreSpec Γ Γ R⟧ SStoreSpec.pure CStoreSpec.pure. *)
  (*   Proof. *)
  (*     unfold SStoreSpec.pure, CStoreSpec.pure. *)
  (*     intros w ι Hpc t v Htv POST__s POST__c HPOST. *)
  (*     eapply refine_apply; eauto. *)
  (*     eapply refine_T; eauto. *)
  (*   Qed. *)

  (*   Lemma refine_bind `{RA : Rel AT A, RB : Rel BT B} {Γ1 Γ2 Γ3} : *)
  (*     forall (w : World) (ι : Valuation w), *)
  (*       ℛ⟦RStoreSpec Γ1 Γ2 RA -> □(RA -> RStoreSpec Γ2 Γ3 RB) -> RStoreSpec Γ1 Γ3 RB⟧@{ι} *)
  (*         (SStoreSpec.bind (w := w)) CStoreSpec.bind. *)
  (*   Proof. *)
  (*     unfold SStoreSpec.bind, CStoreSpec.bind. *)
  (*     intros w ι ms mc Hm fs fc Hf POST__s POST__c HPOST δs δc Hδ hs hc Hh. *)
  (*     apply Hm; eauto. intros w1 r01 ι1 Hι1 Hpc1 t v Htv. *)
  (*     eapply refine_apply; eauto. *)
  (*     eapply refine_apply; eauto. *)
  (*     eapply refine_four; eauto. *)
  (*   Qed. *)

  (*   Lemma refine_bind' `{RA : Rel AT A, RB : Rel BT B} {Γ1 Γ2 Γ3} : *)
  (*     ℛ⟦RStoreSpec Γ1 Γ2 RA -> □(RA -> RStoreSpec Γ2 Γ3 RB) -> RStoreSpec Γ1 Γ3 RB⟧ *)
  (*       SStoreSpec.bind CStoreSpec.bind. *)
  (*   Proof. intros ? ? _. apply refine_bind. Qed. *)

  (*   Lemma refine_angelic (x : option LVar) {Γ} : *)
  (*     ℛ⟦∀ σ, RStoreSpec Γ Γ (RVal σ)⟧ (SStoreSpec.angelic x) CStoreSpec.angelic. *)
  (*   Proof. *)
  (*     unfold SStoreSpec.angelic, CStoreSpec.angelic. *)
  (*     intros w ι Hpc σ. apply refine_lift_purem; auto. *)
  (*     apply RPureSpec.refine_angelic; auto. *)
  (*   Qed. *)

  (*   Lemma refine_demonic (x : option LVar) {Γ} : *)
  (*     ℛ⟦∀ σ, RStoreSpec Γ Γ (RVal σ)⟧ (SStoreSpec.demonic x) CStoreSpec.demonic. *)
  (*   Proof. *)
  (*     unfold SStoreSpec.demonic, CStoreSpec.demonic. *)
  (*     intros w ι Hpc σ. apply refine_lift_purem; auto. *)
  (*     apply RPureSpec.refine_demonic; auto. *)
  (*   Qed. *)

  (*   Lemma refine_angelic_ctx {N : Set} {n : N -> LVar} {Γ} : *)
  (*     ℛ⟦∀ Δ, RStoreSpec Γ Γ (RNEnv Δ)⟧ *)
  (*       (SStoreSpec.angelic_ctx n) CStoreSpec.angelic_ctx. *)
  (*   Proof. *)
  (*     unfold SStoreSpec.angelic_ctx, CStoreSpec.angelic_ctx. *)
  (*     intros w ι Hpc Δ. apply refine_lift_purem; auto. *)
  (*     apply RPureSpec.refine_angelic_ctx; auto. *)
  (*   Qed. *)

  (*   Lemma refine_demonic_ctx {N : Set} {n : N -> LVar} {Γ} : *)
  (*     ℛ⟦∀ Δ, RStoreSpec Γ Γ (RNEnv Δ)⟧ *)
  (*       (SStoreSpec.demonic_ctx n) CStoreSpec.demonic_ctx. *)
  (*   Proof. *)
  (*     unfold SStoreSpec.demonic_ctx, CStoreSpec.demonic_ctx. *)
  (*     intros w ι Hpc Δ. apply refine_lift_purem; auto. *)
  (*     apply RPureSpec.refine_demonic_ctx; auto. *)
  (*   Qed. *)

  (*   Lemma refine_debug {AT A} `{R : Rel AT A} *)
  (*     {Γ1 Γ2} {w0 : World} (ι0 : Valuation w0) *)
  (*         (Hpc : instprop (wco w0) ι0) f ms mc : *)
  (*     ℛ⟦RStoreSpec Γ1 Γ2 R⟧@{ι0} ms mc -> *)
  (*     ℛ⟦RStoreSpec Γ1 Γ2 R⟧@{ι0} (@SStoreSpec.debug AT Γ1 Γ2 w0 f ms) mc. *)
  (*   Proof. *)
  (*     intros Hap POST__s POST__c HPOST δs0 δc0 Hδ0 hs0 hc0 Hh0. *)
  (*     intros [HP]. revert HP. apply Hap; auto. *)
  (*   Qed. *)

  (*   Lemma refine_angelic_binary {AT A} `{R : Rel AT A} {Γ1 Γ2} : *)
  (*     ℛ⟦RStoreSpec Γ1 Γ2 R -> RStoreSpec Γ1 Γ2 R -> RStoreSpec Γ1 Γ2 R⟧ *)
  (*       SStoreSpec.angelic_binary CStoreSpec.angelic_binary. *)
  (*   Proof. *)
  (*     intros w ι Hpc ms1 mc1 Hm1 ms2 mc2 Hm2. *)
  (*     intros POST__s POST__c HPOST δs0 δc0 Hδ0 hs0 hc0 Hh0. *)
  (*     unfold SStoreSpec.angelic_binary, CStoreSpec.angelic_binary. *)
  (*     apply refine_symprop_angelic_binary; auto. *)
  (*     apply Hm1; auto. apply Hm2; auto. *)
  (*   Qed. *)

  (*   Lemma refine_demonic_binary {AT A} `{R : Rel AT A} {Γ1 Γ2} : *)
  (*     ℛ⟦RStoreSpec Γ1 Γ2 R -> RStoreSpec Γ1 Γ2 R -> RStoreSpec Γ1 Γ2 R⟧ *)
  (*       SStoreSpec.demonic_binary CStoreSpec.demonic_binary. *)
  (*   Proof. *)
  (*     intros w ι Hpc ms1 mc1 Hm1 ms2 mc2 Hm2. *)
  (*     intros POST__s POST__c HPOST δs0 δc0 Hδ0 hs0 hc0 Hh0. *)
  (*     unfold SStoreSpec.angelic_binary, CStoreSpec.angelic_binary. *)
  (*     apply refine_symprop_demonic_binary; auto. *)
  (*     apply Hm1; auto. apply Hm2; auto. *)
  (*   Qed. *)

  (* End Basics. *)

  (* Section AssumeAssert. *)

  (*   Lemma refine_assume_formula {Γ} : *)
  (*     ℛ⟦RFormula -> RStoreSpec Γ Γ RUnit⟧ *)
  (*       SStoreSpec.assume_formula CStoreSpec.assume_formula. *)
  (*   Proof. *)
  (*     unfold SStoreSpec.assume_formula, CStoreSpec.assume_formula. *)
  (*     intros w ι Hpc P p Hp. apply refine_lift_purem; auto. *)
  (*     apply RPureSpec.refine_assume_formula; auto. *)
  (*   Qed. *)

  (*   Lemma refine_assert_formula {Γ} : *)
  (*     ℛ⟦RFormula -> RStoreSpec Γ Γ RUnit⟧ *)
  (*       SStoreSpec.assert_formula CStoreSpec.assert_formula. *)
  (*   Proof. *)
  (*     intros w ι Hpc P p Hp. *)
  (*     unfold SStoreSpec.assert_formula, CStoreSpec.assert_formula. *)
  (*     intros POST__s POST__c HPOST δs δc Hδ hs hc Hh. *)
  (*     apply refine_lift_purem; auto. *)
  (*     now apply RPureSpec.refine_assert_formula. *)
  (*   Qed. *)

  (*   Lemma refine_assert_pathcondition {Γ} : *)
  (*     ℛ⟦RPathCondition -> RStoreSpec Γ Γ RUnit⟧ *)
  (*       SStoreSpec.assert_pathcondition CStoreSpec.assert_formula. *)
  (*   Proof. *)
  (*     intros w ι Hpc Ps ps Hps POST__s POST__c HPOST δs δc Hδ hs hc Hh. *)
  (*     apply refine_lift_purem; auto. *)
  (*     now apply RPureSpec.refine_assert_pathcondition. *)
  (*   Qed. *)

  (*   Lemma refine_assert_eq_nenv {N Γ} (Δ : NCtx N Ty) : *)
  (*     ℛ⟦RNEnv Δ -> RNEnv Δ -> RStoreSpec Γ Γ RUnit⟧ *)
  (*       SStoreSpec.assert_eq_nenv CStoreSpec.assert_eq_nenv. *)
  (*   Proof. *)
  (*     intros w ι Hpc E1 ? ? E2 ? ? POST__s POST__c HPOST δs δc Hδ hs hc Hh. *)
  (*     unfold SStoreSpec.assert_eq_nenv, CStoreSpec.assert_eq_nenv. *)
  (*     apply refine_lift_purem; auto. *)
  (*     apply RPureSpec.refine_assert_eq_nenv; auto. *)
  (*   Qed. *)

  (* End AssumeAssert. *)

  (* Section PatternMatching. *)

  (*   Lemma refine_demonic_pattern_match {N : Set} (n : N -> LVar) {Γ σ} (pat : @Pattern N σ) : *)
  (*     ℛ⟦RVal σ -> RStoreSpec Γ Γ (RMatchResult pat)⟧ *)
  (*       (SStoreSpec.demonic_pattern_match n pat) *)
  (*       (CStoreSpec.demonic_pattern_match pat). *)
  (*   Proof. *)
  (*     intros w ι Hpc sv cv rv sΦ cΦ rΦ sδ cδ rδ sh ch rh. *)
  (*     unfold SStoreSpec.demonic_pattern_match, CStoreSpec.demonic_pattern_match, CStoreSpec.lift_purem. *)
  (*     apply RPureSpec.refine_demonic_pattern_match; auto. *)
  (*     intros w1 θ1 ι1 Heq1 Hpc1 smr cmr rmr. apply rΦ; auto. *)
  (*     eapply refine_inst_persist; eauto. *)
  (*     eapply refine_inst_persist; eauto. *)
  (*   Qed. *)

  (* End PatternMatching. *)

  (* Section State. *)

  (*   Lemma refine_pushpop `{R : Rel AT A} {Γ1 Γ2 x σ} : *)
  (*     ℛ⟦RVal σ -> RStoreSpec (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) R -> RStoreSpec Γ1 Γ2 R⟧ *)
  (*       SStoreSpec.pushpop CStoreSpec.pushpop. *)
  (*   Proof. *)
  (*     intros w0 ι0 Hpc0 t v Htv ms mc Hm. *)
  (*     unfold SStoreSpec.pushpop, CStoreSpec.pushpop. *)
  (*     intros POST__s POST__c HPOST δs0 δc0 Hδ0 hs0 hc0 Hh0. *)
  (*     apply Hm; eauto. *)
  (*     - intros w1 r01 ι1 Hι1 Hpc1 a1 a Ha δs1 δc1 -> hs1 hc1 Hh1. *)
  (*       apply HPOST; auto. now destruct (env.view δs1). *)
  (*     - now apply refine_env_snoc. *)
  (*   Qed. *)

  (*   Lemma refine_pushspops `{R : Rel AT A} {Γ1 Γ2 Δ} : *)
  (*     ℛ⟦RStore Δ -> RStoreSpec (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) R -> RStoreSpec Γ1 Γ2 R⟧ *)
  (*       SStoreSpec.pushspops CStoreSpec.pushspops. *)
  (*   Proof. *)
  (*     intros w0 ι0 Hpc0 ts vs -> ms mc Hm. *)
  (*     intros POST__s POST__c HPOST δs0 δc0 -> hs0 hc0 Hh0. *)
  (*     unfold SStoreSpec.pushspops, CStoreSpec.pushspops. *)
  (*     apply Hm; auto. *)
  (*     - intros w1 ω01 ι1 Hι1 Hpc1 a1 a Ha δs1 δc1 -> hs1 hc1 Hh1. *)
  (*       apply HPOST; auto. *)
  (*       destruct (env.catView δs1). *)
  (*       unfold inst, inst_store, inst_env at 1. *)
  (*       rewrite <- env.map_drop. *)
  (*       rewrite ?env.drop_cat. *)
  (*       reflexivity. *)
  (*     - cbn. *)
  (*       unfold inst, inst_store, inst_env at 3. *)
  (*       now rewrite env.map_cat. *)
  (*   Qed. *)

  (*   Lemma refine_get_local {Γ} : *)
  (*     ℛ⟦RStoreSpec Γ Γ (RStore Γ)⟧ *)
  (*       SStoreSpec.get_local CStoreSpec.get_local. *)
  (*   Proof. *)
  (*     intros w ι Hpc POST__s POST__c HPOST. *)
  (*     intros δs0 δc0 Hδ hs0 hc0 Hh0. *)
  (*     unfold SStoreSpec.get_local, CStoreSpec.get_local. *)
  (*     eapply refine_apply; eauto. *)
  (*     eapply refine_apply; eauto. *)
  (*     eapply refine_apply; eauto. *)
  (*     apply refine_T; eauto. *)
  (*   Qed. *)

  (*   Lemma refine_put_local {Γ1 Γ2} : *)
  (*     ℛ⟦RStore Γ2 -> RStoreSpec Γ1 Γ2 RUnit⟧ *)
  (*       SStoreSpec.put_local CStoreSpec.put_local. *)
  (*   Proof. *)
  (*     intros w ι Hpc δs2 δc2 Hδ2 POST__s POST__c HPOST. *)
  (*     intros δs0 δc0 Hδ hs0 hc0 Hh0. *)
  (*     unfold SStoreSpec.put_local, CStoreSpec.put_local. *)
  (*     eapply refine_apply; eauto. *)
  (*     eapply refine_apply; eauto. *)
  (*     eapply refine_apply; eauto. *)
  (*     apply refine_T; eauto. *)
  (*     reflexivity. *)
  (*   Qed. *)

  (*   Lemma refine_peval {w : World} {ι : Valuation w} {σ} t v : *)
  (*     ℛ⟦RVal σ⟧@{ι} t v -> ℛ⟦RVal σ⟧@{ι} (peval t) v. *)
  (*   Proof. intros ->. symmetry. apply peval_sound. Qed. *)

  (*   Lemma refine_eval_exp {Γ σ} (e : Exp Γ σ) : *)
  (*     ℛ⟦RStoreSpec Γ Γ (RVal σ)⟧ (SStoreSpec.eval_exp e) (CStoreSpec.eval_exp e). *)
  (*   Proof. *)
  (*     intros w ι Hpc POST__s POST__c HPOST δs0 δc0 Hδ0 hs0 hc0 Hh. *)
  (*     unfold SStoreSpec.eval_exp, CStoreSpec.eval_exp. *)
  (*     eapply refine_apply; eauto. *)
  (*     eapply refine_apply; eauto. *)
  (*     eapply refine_apply; eauto. *)
  (*     apply refine_T; eauto. *)
  (*     apply refine_peval. *)
  (*     cbn. rewrite <- eval_exp_inst. *)
  (*     f_equal. exact Hδ0. *)
  (*   Qed. *)

  (*   Lemma refine_eval_exps {Γ Δ} (es : NamedEnv (Exp Γ) Δ) : *)
  (*     ℛ⟦RStoreSpec Γ Γ (RStore Δ)⟧ *)
  (*       (SStoreSpec.eval_exps es) (CStoreSpec.eval_exps es). *)
  (*   Proof. *)
  (*     intros w ι Hpc POST__s POST__c HPOST δs0 δc0 Hδ0 hs0 hc0 Hh. *)
  (*     unfold SStoreSpec.eval_exps, CStoreSpec.eval_exps. *)
  (*     eapply refine_apply; eauto. *)
  (*     eapply refine_apply; eauto. *)
  (*     eapply refine_apply; eauto. *)
  (*     apply refine_T; eauto. *)
  (*     apply env.lookup_extensional; cbn; intros [x σ] xIn. *)
  (*     unfold evals, inst, inst_store, inst_env. rewrite ?env.lookup_map. *)
  (*     symmetry. etransitivity. apply peval_sound. *)
  (*     rewrite <- eval_exp_inst. f_equal. symmetry. exact Hδ0. *)
  (*   Qed. *)

  (*   Lemma refine_env_update {Γ x σ} (xIn : x∷σ ∈ Γ) (w : World) (ι : Valuation w) *)
  (*     (t : Term w σ) (v : Val σ) (Htv : ℛ⟦RVal σ⟧@{ι} t v) *)
  (*     (δs : SStore Γ w) (δc : CStore Γ) (Hδ : ℛ⟦RStore Γ⟧@{ι} δs δc) : *)
  (*     ℛ⟦RStore Γ⟧@{ι} (δs ⟪ x ↦ t ⟫) (δc ⟪ x ↦ v ⟫). *)
  (*   Proof. *)
  (*     cbn in *. subst. *)
  (*     unfold inst, inst_store, inst_env. *)
  (*     now rewrite env.map_update. *)
  (*   Qed. *)

  (*   Lemma refine_assign {Γ x σ} {xIn : x∷σ ∈ Γ} : *)
  (*     ℛ⟦RVal σ -> RStoreSpec Γ Γ RUnit⟧ *)
  (*       (SStoreSpec.assign x) (CStoreSpec.assign x). *)
  (*   Proof. *)
  (*     intros w ι Hpc t v Htv POST__s POST__c HPOST δs0 δc0 Hδ0 hs0 hc0 Hh. *)
  (*     unfold SStoreSpec.assign, CStoreSpec.assign. *)
  (*     eapply refine_apply; eauto. *)
  (*     eapply refine_apply; eauto. *)
  (*     eapply refine_apply; eauto. *)
  (*     apply refine_T; eauto. *)
  (*     reflexivity. *)
  (*     now apply refine_env_update. *)
  (*   Qed. *)

  (* End State. *)

  (* Local Hint Unfold RSat : core. *)
  (* Local Hint Unfold RInst : core. *)

  (* Lemma refine_produce_chunk {Γ} : *)
  (*   ℛ⟦RChunk -> RStoreSpec Γ Γ RUnit⟧ *)
  (*     SStoreSpec.produce_chunk CStoreSpec.produce_chunk. *)
  (* Proof. *)
  (*   intros w0 ι0 Hpc0 sc cc rc sΦ cΦ rΦ sδ cδ rδ sh ch rh. *)
  (*   apply RHeapSpec.refine_produce_chunk; auto. *)
  (*   intros w1 θ1 ι1 Hι1 Hpc1 su cu ru. apply rΦ; auto. *)
  (*   eapply refine_inst_persist; eauto. *)
  (* Qed. *)

  (* Lemma refine_consume_chunk {Γ} : *)
  (*   ℛ⟦RChunk -> RStoreSpec Γ Γ RUnit⟧ *)
  (*     SStoreSpec.consume_chunk CStoreSpec.consume_chunk. *)
  (* Proof. *)
  (*   intros w0 ι0 Hpc0 sc cc rc sΦ cΦ rΦ sδ cδ rδ sh ch rh. *)
  (*   apply RHeapSpec.refine_consume_chunk; auto. *)
  (*   intros w1 θ1 ι1 Hι1 Hpc1 su cu ru. apply rΦ; auto. *)
  (*   eapply refine_inst_persist; eauto. *)
  (* Qed. *)

  (* Lemma refine_consume_chunk_angelic {Γ} : *)
  (*   ℛ⟦RChunk -> RStoreSpec Γ Γ RUnit⟧ *)
  (*     SStoreSpec.consume_chunk_angelic CStoreSpec.consume_chunk. *)
  (* Proof. *)
  (*   intros w0 ι0 Hpc0 sc cc rc sΦ cΦ rΦ sδ cδ rδ sh ch rh. *)
  (*   apply RHeapSpec.refine_consume_chunk_angelic; auto. *)
  (*   intros w1 θ1 ι1 Hι1 Hpc1 su cu ru. apply rΦ; auto. *)
  (*   eapply refine_inst_persist; eauto. *)
  (* Qed. *)

  (* Lemma refine_produce {Γ Σ0 pc0} (asn : Assertion Σ0) : *)
  (*   let w0 := @MkWorld Σ0 pc0 in *)
  (*   forall *)
  (*     (ι0 : Valuation w0) *)
  (*     (Hpc0 : instprop (wco w0) ι0), *)
  (*     ℛ⟦□(RStoreSpec Γ Γ RUnit)⟧@{ι0} (@SStoreSpec.produce Γ w0 asn) (CStoreSpec.produce ι0 asn). *)
  (* Proof. *)
  (*   unfold SStoreSpec.produce, CStoreSpec.produce. *)
  (*   intros ι0 Hpc0 w1 θ1 ι1 Hι1 Hpc1 sΦ cΦ rΦ sδ cδ rδ sh ch rh. *)
  (*   apply RHeapSpec.refine_produce; auto. *)
  (*   intros w2 θ2 ι2 Hι2 Hpc2 su cu ru. apply rΦ; auto. *)
  (*   eapply refine_inst_persist; eauto. *)
  (* Qed. *)

  (* Lemma refine_consume {Γ Σ0 pc0} (asn : Assertion Σ0) : *)
  (*   let w0 := @MkWorld Σ0 pc0 in *)
  (*   forall *)
  (*     (ι0 : Valuation w0) *)
  (*     (Hpc0 : instprop (wco w0) ι0), *)
  (*     ℛ⟦□(RStoreSpec Γ Γ RUnit)⟧@{ι0} (@SStoreSpec.consume Γ w0 asn) (CStoreSpec.consume ι0 asn). *)
  (* Proof. *)
  (*   unfold SStoreSpec.consume, CStoreSpec.consume. *)
  (*   intros ι0 Hpc0 w1 θ1 ι1 Hι1 Hpc1 sΦ cΦ rΦ sδ cδ rδ sh ch rh. *)
  (*   apply RHeapSpec.refine_consume; auto. *)
  (*   intros w2 θ2 ι2 Hι2 Hpc2 su cu ru. apply rΦ; auto. *)
  (*   eapply refine_inst_persist; eauto. *)
  (* Qed. *)


  (* Lemma refine_read_register {Γ τ} (reg : 𝑹𝑬𝑮 τ) : *)
  (*   ℛ⟦RStoreSpec Γ Γ (RVal τ)⟧ *)
  (*     (@SStoreSpec.read_register Γ τ reg) (CStoreSpec.read_register reg). *)
  (* Proof. *)
  (*   intros w0 ι0 Hpc0 sΦ cΦ rΦ sδ cδ rδ sh ch rh. *)
  (*   apply RHeapSpec.refine_read_register; auto. *)
  (*   intros w1 θ1 ι1 Hι1 Hpc1 sv cv rv. apply rΦ; auto. *)
  (*   eapply refine_inst_persist; eauto. *)
  (* Qed. *)

  (* Lemma refine_write_register {Γ τ} (reg : 𝑹𝑬𝑮 τ) : *)
  (*   ℛ⟦RVal τ -> RStoreSpec Γ Γ (RVal τ)⟧ *)
  (*     (@SStoreSpec.write_register Γ τ reg) (CStoreSpec.write_register reg). *)
  (* Proof. *)
  (*   intros w0 ι0 Hpc0 svnew cvnew rvnew sΦ cΦ rΦ sδ cδ rδ sh ch rh. *)
  (*   apply RHeapSpec.refine_write_register; auto. *)
  (*   intros w1 θ1 ι1 Hι1 Hpc1 sv cv rv. apply rΦ; auto. *)
  (*   eapply refine_inst_persist; eauto. *)
  (* Qed. *)

  (* Lemma refine_call_contract {Γ Δ τ} (c : SepContract Δ τ) : *)
  (*   ℛ⟦RStore Δ -> RStoreSpec Γ Γ (RVal τ)⟧ *)
  (*     (SStoreSpec.call_contract c) (CStoreSpec.call_contract c). *)
  (* Proof. *)
  (*   intros w0 ι0 Hpc0 args__s args__c Hargs. *)
  (*   destruct c; cbv [SStoreSpec.call_contract CStoreSpec.call_contract]. *)
  (*   apply refine_bind; auto. *)
  (*   apply refine_angelic_ctx; auto. *)
  (*   intros w1 ω01 ι1 -> Hpc1 evars__s evars__c Hevars. *)
  (*   apply refine_bind; auto. *)
  (*   { apply refine_assert_eq_nenv; auto; hnf. *)
  (*     now rewrite -> Hevars, inst_subst. *)
  (*     now rewrite -> Hargs, inst_persist. *)
  (*   } *)
  (*   intros w2 ω12 ι2 -> Hpc2 _ _ _. *)
  (*   apply refine_bind; auto. *)
  (*   { apply refine_consume; wsimpl; auto. *)
  (*     constructor. *)
  (*   } *)
  (*   intros w3 ω23 ι3 -> Hpc3 _ _ _. *)
  (*   apply refine_bind; auto. *)
  (*   { apply refine_demonic; auto. } *)
  (*   intros w4 ω34 ι4 -> Hpc4. *)
  (*   intros res__s res__c Hres. *)
  (*   apply refine_bind; auto. *)
  (*   { apply refine_produce; auto. *)
  (*     constructor. *)
  (*     cbn - [inst_env sub_snoc]. *)
  (*     rewrite inst_sub_snoc, inst_persist, ?sub_acc_trans, ?inst_subst. *)
  (*     now rewrite Hevars, Hres. *)
  (*   } *)
  (*   intros w5 ω45 ι5 -> Hpc5 _ _ _. *)
  (*   apply refine_pure; auto. *)
  (*   rewrite Hres. rewrite <- inst_persist. *)
  (*   reflexivity. *)
  (* Qed. *)

  (* Lemma refine_call_lemma {Γ Δ : PCtx} (lem : Lemma Δ) : *)
  (*   ℛ⟦RStore Δ -> RStoreSpec Γ Γ RUnit⟧ *)
  (*     (SStoreSpec.call_lemma lem) (CStoreSpec.call_lemma lem). *)
  (* Proof. *)
  (*   destruct lem; cbv [SStoreSpec.call_lemma CStoreSpec.call_lemma]. *)
  (*   intros w0 ι0 Hpc0. *)
  (*   intros args__s args__c Hargs. *)
  (*   apply refine_bind; auto. *)
  (*   apply refine_angelic_ctx; auto. *)
  (*   intros w1 ω01 ι1 -> Hpc1. *)
  (*   intros evars__s evars__c Hevars. *)
  (*   apply refine_bind; auto. *)
  (*   { apply refine_assert_eq_nenv; auto; hnf. *)
  (*     now rewrite Hevars, inst_subst. *)
  (*     now rewrite Hargs, inst_persist. *)
  (*   } *)
  (*   intros w2 ω12 ι2 -> Hpc2 _ _ _. *)
  (*   apply refine_bind; auto. *)
  (*   { apply refine_consume; wsimpl; auto. *)
  (*     constructor. *)
  (*   } *)
  (*   intros w3 ω23 ι3 -> Hpc3 _ _ _. *)
  (*   { apply refine_produce; auto. *)
  (*     constructor. *)
  (*     cbn - [inst_env sub_snoc]. *)
  (*     rewrite inst_persist, sub_acc_trans, inst_subst. *)
  (*     now rewrite Hevars. *)
  (*   } *)
  (* Qed. *)

  (* Definition ExecRefine (sexec : SStoreSpec.Exec) (cexec : CStoreSpec.Exec) := *)
  (*   forall Γ τ (s : Stm Γ τ), *)
  (*     ℛ⟦RStoreSpec Γ Γ (RVal τ)⟧ (@sexec Γ τ s) (cexec Γ τ s). *)

  (* Lemma refine_exec_aux {cfg} srec crec (HYP : ExecRefine srec crec) : *)
  (*   ExecRefine (@SStoreSpec.exec_aux cfg srec) (@CStoreSpec.exec_aux crec). *)
  (* Proof. *)
  (*   unfold ExecRefine. *)
  (*   induction s; cbn; intros * w0 ι0 Hpc0. *)
  (*   - apply refine_pure; auto. reflexivity. *)
  (*   - now apply refine_eval_exp. *)
  (*   - apply refine_bind; auto. *)
  (*     intros w1 ω01 ι1 -> Hpc1. *)
  (*     intros t v Htv. *)
  (*     apply refine_pushpop; auto. *)
  (*   - apply refine_pushspops; auto. *)
  (*     apply refine_lift. *)
  (*   - apply refine_bind; auto. *)
  (*     intros w1 ω01 ι1 -> Hpc1. *)
  (*     intros t v ->. *)
  (*     apply refine_bind; auto. *)
  (*     apply refine_assign; auto. *)
  (*     reflexivity. *)
  (*     intros w2 ω12 ι2 -> Hpc2 _ _ _. *)
  (*     apply refine_pure; auto. *)
  (*     hnf in H. now rewrite <- inst_persist in H. *)
  (*   - apply refine_bind; auto. *)
  (*     apply refine_eval_exps; auto. *)
  (*     intros w1 ω01 ι1 -> Hpc1. *)
  (*     intros args__s args__c Hargs. *)
  (*     destruct (CEnv f). *)
  (*     + unfold SStoreSpec.call_contract_debug. *)
  (*       destruct (config_debug_function cfg f). *)
  (*       apply refine_debug; auto. *)
  (*       apply refine_call_contract; auto. *)
  (*       apply refine_call_contract; auto. *)
  (*     + intros POST__s POST__c HPOST. *)
  (*       intros δs1 δc1 ->. *)
  (*       apply HYP; auto. *)
  (*       intros w2 ω12 ι2 -> Hpc2. *)
  (*       intros t v ->. *)
  (*       intros _ _ _. *)
  (*       apply HPOST; auto. *)
  (*       reflexivity. *)
  (*       rewrite <- inst_persist. *)
  (*       reflexivity. *)
  (*   - apply refine_bind; auto. *)
  (*     apply refine_get_local; auto. *)
  (*     intros w1 ω01 ι1 -> Hpc1. *)
  (*     intros δs1 δc1 ->. *)
  (*     apply refine_bind; auto. *)
  (*     apply refine_put_local; auto. *)
  (*     apply refine_lift. *)
  (*     intros w2 ω12 ι2 -> Hpc2 _ _ _. *)
  (*     apply refine_bind; auto. *)
  (*     intros w3 ω23 ι3 -> Hpc3. *)
  (*     intros t v ->. *)
  (*     apply refine_bind; auto. *)
  (*     apply refine_put_local; auto. *)
  (*     rewrite persist_subst. *)
  (*     hnf. rewrite sub_acc_trans, ?inst_subst; auto. *)
  (*     intros w4 ω34 ι4 -> Hpc4 _ _ _. *)
  (*     apply refine_pure; auto. *)
  (*     eapply refine_inst_persist; eauto. *)
  (*     reflexivity. *)
  (*   - apply refine_bind; auto. *)
  (*     apply refine_eval_exps; auto. *)
  (*     intros w1 ω01 ι1 -> Hpc1. *)
  (*     intros args__s args__c Hargs. *)
  (*     apply refine_call_contract; auto. *)
  (*   - apply refine_bind; auto. *)
  (*     apply refine_eval_exps; auto. *)
  (*     intros w1 ω01 ι1 -> Hpc1 δΔ ? ?. *)
  (*     apply refine_bind; auto. *)
  (*     apply refine_call_lemma; auto. *)
  (*     intros w2 ω12 ι2 -> Hpc2 _ _ _; auto. *)
  (*   - apply refine_bind; auto. *)
  (*     intros ? ? ? -> ? _ _ _; auto. *)
  (*   - apply refine_bind; auto. *)
  (*     apply (refine_eval_exp e1); auto. *)
  (*     intros w1 ω01 ι1 -> Hpc1. *)
  (*     intros t v ->. *)
  (*     apply refine_bind; auto. *)
  (*     apply refine_assume_formula; auto. *)
  (*     cbn. reflexivity. *)
  (*     intros w2 ω12 ι2 -> Hpc2 _ _ _. *)
  (*     now apply IHs. *)
  (*   - apply refine_block; auto. *)
  (*   - apply refine_bind; auto. *)
  (*     intros w1 ω01 ι1 -> Hpc1. *)
  (*     intros t v Htv. *)
  (*     apply refine_bind; auto. *)
  (*     apply refine_demonic_pattern_match; auto. *)
  (*     intros w2 r12 ι2 -> Hpc2. *)
  (*     intros [? ?] [pc vs] [-> ?]. *)
  (*     apply refine_pushspops; auto. *)
  (*     apply H; auto. *)
  (*   - now apply refine_read_register. *)
  (*   - apply refine_bind; auto. *)
  (*     apply (refine_eval_exp e); auto. *)
  (*     intros w1 ω01 ι1 -> Hpc1 svnew cvnew rvnew. *)
  (*     now apply refine_write_register. *)
  (*   - apply refine_error; auto. *)
  (*   - apply refine_debug; auto. *)
  (* Qed. *)

  (* Lemma refine_exec {cfg n} : *)
  (*   ExecRefine (@SStoreSpec.exec cfg n) (@CStoreSpec.exec n). *)
  (* Proof. *)
  (*   induction n; cbn. *)
  (*   - unfold ExecRefine. intros Γ τ s w ι Hpc. *)
  (*     apply refine_error; auto. *)
  (*   - now apply refine_exec_aux. *)
  (* Qed. *)

  (* Lemma refine_exec_contract {cfg : Config} n {Γ τ} (c : SepContract Γ τ) (s : Stm Γ τ) : *)
  (*   let w0 := {| wctx := sep_contract_logic_variables c; wco := ctx.nil |} in *)
  (*   forall (ι0 : Valuation w0), *)
  (*     ℛ⟦RStoreSpec Γ Γ RUnit⟧@{ι0} *)
  (*       (SStoreSpec.exec_contract cfg n c s) (CStoreSpec.exec_contract n c s ι0). *)
  (* Proof. *)
  (*   unfold SStoreSpec.exec_contract, CStoreSpec.exec_contract; *)
  (*     destruct c as [Σ δ pre result post]; cbn - [RSat] in *. *)
  (*   intros ι0. *)
  (*   apply refine_bind. *)
  (*   apply refine_produce; wsimpl; cbn; auto. *)
  (*   intros w1 ω01 ι1 -> Hpc1 _ _ _. *)
  (*   apply refine_bind; auto. *)
  (*   apply refine_exec; auto. *)
  (*   intros w2 ω12 ι2 -> Hpc2. *)
  (*   intros res__s res__c Hres. *)
  (*   apply refine_consume; cbn - [inst]; wsimpl; auto. *)
  (*   f_equal; auto. *)
  (* Qed. *)

  (* Lemma refine_demonic_close {w : World} (P : 𝕊 w) (p : Valuation w -> Prop) : *)
  (*   (forall (ι : Valuation w), ℛ⟦_⟧@{ι} P (p ι)) -> *)
  (*   RSat RProp (w := wnil) env.nil (demonic_close P) (ForallNamed p). *)
  (* Proof. *)
  (*   intros HYP Hwp. unfold ForallNamed. *)
  (*   rewrite env.Forall_forall. intros ι. *)
  (*   apply HYP. revert Hwp. clear. *)
  (*   rewrite ?wsafe_safe, ?safe_debug_safe. *)
  (*   intros Hwp. now apply safe_demonic_close. *)
  (* Qed. *)

  (* Lemma refine_vcgen {Γ τ} n (c : SepContract Γ τ) (body : Stm Γ τ) : *)
  (*   RSat RProp (w := wnil) env.nil (SStoreSpec.vcgen default_config n c body) (CStoreSpec.vcgen n c body). *)
  (* Proof. *)
  (*   unfold SStoreSpec.vcgen, CStoreSpec.vcgen. *)
  (*   apply (refine_demonic_close *)
  (*            (w := {| wctx := sep_contract_logic_variables c; wco := ctx.nil |})). *)
  (*   intros ι. *)
  (*   apply refine_exec_contract; auto. *)
  (*   now intros w1 ω01 ι1 -> Hpc1. *)
  (*   reflexivity. *)
  (*   reflexivity. *)
  (* Qed. *)

  (* Lemma replay_sound {w : World} (s : 𝕊 w) ι (Hpc : instprop (wco w) ι) : *)
  (*   safe (SPureSpec.replay s) ι -> safe s ι. *)
  (* Proof. *)
  (*   intros H. *)
  (*   apply CPureSpec.replay_sound, RPureSpec.refine_replay; auto. *)
  (*   now rewrite wsafe_safe, safe_debug_safe. *)
  (* Qed. *)

  (* Lemma symbolic_vcgen_soundness {Γ τ} (c : SepContract Γ τ) (body : Stm Γ τ) : *)
  (*   Symbolic.ValidContract c body -> *)
  (*   Shallow.ValidContract c body. *)
  (* Proof. *)
  (*   unfold Symbolic.ValidContract. intros [Hwp%postprocess_sound]. *)
  (*   apply (replay_sound (w:=wnil)) in Hwp; [|easy]. *)
  (*   apply postprocess_sound in Hwp. apply refine_vcgen. *)
  (*   now rewrite wsafe_safe, safe_debug_safe. *)
  (* Qed. *)

  (* Lemma symbolic_vcgen_fuel_soundness {Γ τ} (fuel : nat) (c : SepContract Γ τ) (body : Stm Γ τ) : *)
  (*   Symbolic.ValidContractWithFuel fuel c body -> *)
  (*   Shallow.ValidContractWithFuel fuel c body. *)
  (* Proof. *)
  (*   unfold Symbolic.ValidContractWithFuel. intros [Hwp%postprocess_sound]. *)
  (*   apply (replay_sound (w:=wnil)) in Hwp; [|easy]. *)
  (*   apply postprocess_sound in Hwp. apply refine_vcgen. *)
  (*   now rewrite wsafe_safe, safe_debug_safe. *)
  (* Qed. *)

  (* Print Assumptions symbolic_vcgen_soundness. *)

End Soundness.

(* Module MakeSymbolicSoundness *)
(*   (Import B    : Base) *)
(*   (Import SIG  : Signature B) *)
(*   (Import PROG : Program B) *)
(*   (Import SPEC : Specification B SIG PROG) *)
(*   (Import SHAL : ShallowExecOn B SIG PROG SPEC) *)
(*   (Import SYMB : SymbolicExecOn B SIG PROG SPEC). *)

(*   Include Soundness B SIG PROG SPEC SHAL SYMB. *)
(* End MakeSymbolicSoundness. *)
