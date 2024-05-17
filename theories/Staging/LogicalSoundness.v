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
       | angelicv b k => knowing acc_snoc_right (@psafe (wsnoc w b) k)
       | demonicv b k => assuming acc_snoc_right (@psafe (wsnoc w b) k)
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
      MkRel (fun P w SP => (psafe SP -∗ ⌜ P ⌝)%I).

    Lemma refine_symprop_angelic_binary {w : World} :
      ⊢ ℛ⟦RProp -> RProp -> RProp⟧ (@or) (@angelic_binary w).
    Proof.
      iIntros (PC1 PS1) "#HP1 %PC2 %PS2 #HP2 #HPS"; cbn.
      iDestruct "HPS" as "[HPS1 | HPS2]".
      - iLeft. now iApply "HP1".
      - iRight. now iApply "HP2".
    Qed.

    Lemma evalTerm {σ} {w : World} (t : Term w σ) :
      ⊢ ∃ v, repₚ v (w := w) t.
    Proof. crushPredEntails3. now eexists. Qed.

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

    Lemma refine_block `{R : Rel AT A} {w} :
      ⊢ ℛ⟦RPureSpec R⟧ CPureSpec.block (@SPureSpec.block AT w).
    Proof. done. Qed.

    Lemma refine_error `{RA : Rel AT A} {w} m :
      ⊢ ℛ⟦RMsg _ (RPureSpec RA)⟧ m (@SPureSpec.error _ w).
    Proof.
      unfold RMsg. cbn.
      iIntros (msg k K) "Hk %abs".
      inversion abs.
    Qed.

    Lemma refine_angelic (x : option LVar) {w} :
      ⊢ ℛ⟦∀ᵣ σ, RPureSpec (RVal σ)⟧ CPureSpec.angelic (SPureSpec.angelic (w := w) x).
    Proof.
      unfold SPureSpec.angelic; simpl.
      iIntros (σ k K) "HK".
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

    Lemma refine_demonic (x : option LVar) {w} :
      ⊢ ℛ⟦∀ᵣ σ, RPureSpec (RVal σ)⟧ CPureSpec.demonic (SPureSpec.demonic (w := w) x).
    Proof.
      unfold SPureSpec.angelic; simpl.
      iIntros (σ k K) "HK HSP".
      iIntros (v).
      iSpecialize ("HK" $! _ (acc_snoc_right (b := fresh_lvar w x∷σ))).
      rewrite !assuming_acc_snoc_right.
      iPoseProof forgetting_acc_snoc_left_repₚ as "Hrep".
      iSpecialize ("HK" $! v).
      iSpecialize ("HSP" $! v).
      rewrite <-(forgetting_pure (acc_snoc_left' (fresh_lvar w x∷σ) (term_val _ v))).
      iModIntro.
      now iSpecialize ("HK" with "Hrep HSP").
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
        simpl. rewrite <-forgetting_repₚ.
        iApply (repₚ_cong₂ (T1 := λ Σ, NamedEnv (Term Σ) Δ) (T2 := fun Σ => Term Σ (type b))
                  (T3 := λ Σ, NamedEnv (Term Σ) (Δ ▻ b))
                  (fun v v2 => v.[b ↦ v2]) (fun vs vs2 => vs.[ b ↦ vs2 ])
                 with "[$Hv $Hv2]"
               ).
        intros. now rewrite inst_env_snoc.
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
        simpl.
        rewrite <-forgetting_repₚ.
        iApply (repₚ_cong₂ (T1 := λ Σ, NamedEnv (Term Σ) Δ) (T2 := fun Σ => Term Σ (type b))
                  (T3 := λ Σ, NamedEnv (Term Σ) (Δ ▻ b))
                  (fun v v2 => v.[b ↦ v2]) (fun vs vs2 => vs.[ b ↦ vs2 ])
                 with "[$Hv $Hv2]"
               ).
        intros.
        now rewrite inst_env_snoc.
    Qed.

    (* Lemma refine_assert_pathcondition : *)
    (*   ℛ⟦RMsg _ (RPathCondition -> RPureSpec RUnit)⟧ *)
    (*     SPureSpec.assert_pathcondition CPureSpec.assert_formula. *)
    (* Proof. *)
    (*   unfold SPureSpec.assert_pathcondition, CPureSpec.assert_formula. *)
    (*   intros w0 ι0 Hpc0 msg sC cC rC sΦ cΦ rΦ HΦ. *)
    (*   destruct (combined_solver_spec _ sC) as [[w1 [ζ sc1]] Hsolver|Hsolver]. *)
    (*   - specialize (Hsolver ι0 Hpc0). destruct Hsolver as [_ Hsolver]. *)
    (*     rewrite SymProp.safe_assert_triangular in HΦ. destruct HΦ as [Hν HΦ]. *)
    (*     rewrite SymProp.safe_assert_pathcondition_without_solver in HΦ. *)
    (*     destruct HΦ as [HC HΦ]. *)
    (*     split. *)
    (*     + apply Hsolver in HC; rewrite ?inst_triangular_right_inverse; auto. *)
    (*       now apply rC. *)
    (*       now apply entails_triangular_inv. *)
    (*     + revert HΦ. unfold four. *)
    (*       apply rΦ; cbn; wsimpl; eauto. *)
    (*       unfold PathCondition. rewrite instprop_cat. split; auto. *)
    (*       now apply entails_triangular_inv. *)
    (*   - contradict HΦ. *)
    (* Qed. *)

    (* Lemma refine_assume_pathcondition : *)
    (*   ℛ⟦RPathCondition -> RPureSpec RUnit⟧ *)
    (*     SPureSpec.assume_pathcondition CPureSpec.assume_formula. *)
    (* Proof. *)
    (*   unfold SPureSpec.assume_pathcondition, CPureSpec.assume_formula. *)
    (*   intros w0 ι0 Hpc0 sC cC rC sΦ cΦ rΦ HΦ HC. apply rC in HC. *)
    (*   destruct (combined_solver_spec _ sC) as [[w1 [ζ sc1]] Hsolver|Hsolver]. *)
    (*   - specialize (Hsolver ι0 Hpc0). *)
    (*     destruct Hsolver as [Hν Hsolver]. inster Hν by auto. *)
    (*     specialize (Hsolver (inst (sub_triangular_inv ζ) ι0)). *)
    (*     rewrite inst_triangular_right_inverse in Hsolver; auto. *)
    (*     inster Hsolver by now try apply entails_triangular_inv. *)
    (*     destruct Hsolver as [Hsolver _]. inster Hsolver by auto. *)
    (*     rewrite SymProp.safe_assume_triangular, *)
    (*       SymProp.safe_assume_pathcondition_without_solver in HΦ. *)
    (*     specialize (HΦ Hν Hsolver). revert HΦ. *)
    (*     unfold four. apply rΦ; cbn; wsimpl; auto. *)
    (*     unfold PathCondition. rewrite instprop_cat. split; auto. *)
    (*     now apply entails_triangular_inv. *)
    (*   - now apply Hsolver in HC. *)
    (* Qed. *)

    (* Lemma refine_assert_formula : *)
    (*   ℛ⟦RMsg _ (RFormula -> RPureSpec RUnit)⟧ *)
    (*     SPureSpec.assert_formula CPureSpec.assert_formula. *)
    (* Proof. *)
    (*   unfold RPureSpec, SPureSpec.assert_formula, CPureSpec.assert_formula. *)
    (*   rsolve. apply refine_assert_pathcondition; auto. cbn in *. intuition auto. *)
    (* Qed. *)

    (* Lemma refine_assume_formula : *)
    (*   ℛ⟦RFormula -> RPureSpec RUnit⟧ *)
    (*     SPureSpec.assume_formula CPureSpec.assume_formula. *)
    (* Proof. *)
    (*   unfold RPureSpec, SPureSpec.assume_formula, CPureSpec.assume_formula. *)
    (*   rsolve. apply refine_assume_pathcondition; cbn in *; intuition auto. *)
    (* Qed. *)

    (* Lemma refine_angelic_binary `{RA : Rel SA CA} : *)
    (*   ℛ⟦RPureSpec RA -> RPureSpec RA -> RPureSpec RA⟧ *)
    (*       SPureSpec.angelic_binary CPureSpec.angelic_binary. *)
    (* Proof. *)
    (*   unfold RPureSpec, SPureSpec.angelic_binary, CPureSpec.angelic_binary. *)
    (*   rsolve. apply refine_symprop_angelic_binary; rsolve. *)
    (* Qed. *)

    (* Lemma refine_demonic_binary `{RA : Rel SA CA} : *)
    (*   ℛ⟦RPureSpec RA -> RPureSpec RA -> RPureSpec RA⟧ *)
    (*       SPureSpec.demonic_binary CPureSpec.demonic_binary. *)
    (* Proof. *)
    (*   unfold RPureSpec, SPureSpec.demonic_binary, CPureSpec.demonic_binary. *)
    (*   rsolve. apply refine_symprop_demonic_binary; rsolve. *)
    (* Qed. *)

    (* Lemma refine_angelic_list' `{RA : Rel SA CA} : *)
    (*   ℛ⟦RA -> RList RA -> RPureSpec RA⟧ *)
    (*     SPureSpec.angelic_list' CPureSpec.angelic_list'. *)
    (* Proof. *)
    (*   intros w ι Hpc sv cv rv svs cvs rvs. revert sv cv rv. *)
    (*   induction rvs; cbn [SPureSpec.angelic_list' CPureSpec.angelic_list']. *)
    (*   - now apply refine_pure. *)
    (*   - intros sv cv rv. apply refine_angelic_binary; auto. *)
    (*     now apply refine_pure. *)
    (* Qed. *)

    (* Lemma refine_angelic_list `{RA : Rel SA CA} : *)
    (*   ℛ⟦RMsg _ (RList RA -> RPureSpec RA)⟧ *)
    (*     SPureSpec.angelic_list CPureSpec.angelic_list. *)
    (* Proof. *)
    (*   intros w ι Hpc msg sv cv []. *)
    (*   - now apply refine_error. *)
    (*   - now apply refine_angelic_list'. *)
    (* Qed. *)

    (* Lemma refine_demonic_list' `{RA : Rel SA CA} : *)
    (*   ℛ⟦RA -> RList RA -> RPureSpec RA⟧ *)
    (*     SPureSpec.demonic_list' CPureSpec.demonic_list'. *)
    (* Proof. *)
    (*   intros w ι Hpc sv cv rv svs cvs rvs. revert sv cv rv. *)
    (*   induction rvs; cbn [SPureSpec.demonic_list' CPureSpec.demonic_list']. *)
    (*   - now apply refine_pure. *)
    (*   - intros sv cv rv. apply refine_demonic_binary; auto. now apply refine_pure. *)
    (* Qed. *)

    (* Lemma refine_demonic_list `{RA : Rel SA CA} : *)
    (*   ℛ⟦RList RA -> RPureSpec RA⟧ *)
    (*     SPureSpec.demonic_list CPureSpec.demonic_list. *)
    (* Proof. *)
    (*   intros w ι Hpc sv cv []. *)
    (*   - now apply refine_block. *)
    (*   - now apply refine_demonic_list'. *)
    (* Qed. *)

    (* Lemma refine_angelic_finite {F} `{finite.Finite F} : *)
    (*   ℛ⟦RMsg _ (RPureSpec (RConst F))⟧ *)
    (*     (@SPureSpec.angelic_finite F _ _) (CPureSpec.angelic_finite F). *)
    (* Proof. *)
    (*   intros w ι Hpc msg. apply refine_angelic_list; auto. *)
    (*   induction (finite.enum F); now constructor. *)
    (* Qed. *)

    (* Lemma refine_demonic_finite {F} `{finite.Finite F} : *)
    (*   ℛ⟦RPureSpec (RConst F)⟧ *)
    (*     (@SPureSpec.demonic_finite F _ _) (CPureSpec.demonic_finite F). *)
    (* Proof. *)
    (*   intros w ι Hpc. apply refine_demonic_list; auto. *)
    (*   induction (finite.enum F); now constructor. *)
    (* Qed. *)

    (* Lemma refine_angelic_pattern_match' {N : Set} (n : N -> LVar) *)
    (*   {σ} (pat : @Pattern N σ) : *)
    (*   ℛ⟦RMsg _ (RVal σ -> RPureSpec (RMatchResult pat))⟧ *)
    (*     (SPureSpec.angelic_pattern_match' n pat) *)
    (*     (CPureSpec.angelic_pattern_match pat). *)
    (* Proof. *)
    (*   intros w ι Hpc msg t v ->. *)
    (*   unfold SPureSpec.angelic_pattern_match'. *)
    (*   unfold CPureSpec.angelic_pattern_match. *)
    (*   apply refine_bind; auto. *)
    (*   { now apply refine_angelic_finite. } *)
    (*   intros w1 r01 ι1 Hι1 Hpc1. *)
    (*   intros pc ? ->. *)
    (*   apply refine_bind; auto. *)
    (*   { now apply refine_angelic_ctx. } *)
    (*   intros w2 r12 ι2 Hι2 Hpc2. *)
    (*   intros ts vs Htvs. *)
    (*   apply refine_bind; auto. *)
    (*   { apply refine_assert_formula; try assumption. cbn. *)
    (*     rewrite (inst_persist (AT := fun Σ => Term Σ _)). *)
    (*     rewrite !sub_acc_trans, inst_subst. *)
    (*     rewrite inst_pattern_match_term_reverse. *)
    (*     hnf in Htvs. subst. reflexivity. *)
    (*   } *)
    (*   intros w3 r23 ι3 Hι3 Hpc3 _ _ _. *)
    (*   apply refine_pure; auto. *)
    (*   exists eq_refl. eapply refine_inst_persist; eauto. *)
    (* Qed. *)
    (* #[global] Arguments refine_angelic_pattern_match' {N} n {σ} pat. *)

    (* Lemma refine_demonic_pattern_match' {N : Set} (n : N -> LVar) *)
    (*   {σ} (pat : @Pattern N σ) : *)
    (*   ℛ⟦RVal σ -> RPureSpec (RMatchResult pat)⟧ *)
    (*     (SPureSpec.demonic_pattern_match' n pat) *)
    (*     (CPureSpec.demonic_pattern_match pat). *)
    (* Proof. *)
    (*   intros w ι Hpc t v ->. *)
    (*   unfold SPureSpec.demonic_pattern_match'. *)
    (*   unfold CPureSpec.demonic_pattern_match. *)
    (*   apply refine_bind; auto. *)
    (*   { now apply refine_demonic_finite. } *)
    (*   intros w1 r01 ι1 Hι1 Hpc1. *)
    (*   intros pc ? ->. *)
    (*   apply refine_bind; auto. *)
    (*   { now apply refine_demonic_ctx. } *)
    (*   intros w2 r12 ι2 Hι2 Hpc2. *)
    (*   intros ts vs Htvs. *)
    (*   apply refine_bind; auto. *)
    (*   { apply refine_assume_formula; try assumption. cbn. *)
    (*     rewrite (inst_persist (AT := fun Σ => Term Σ _)). *)
    (*     rewrite !sub_acc_trans, inst_subst. *)
    (*     rewrite inst_pattern_match_term_reverse. *)
    (*     hnf in Htvs. subst. reflexivity. *)
    (*   } *)
    (*   intros w3 r23 ι3 Hι3 Hpc3 _ _ _. *)
    (*   apply refine_pure; auto. *)
    (*   exists eq_refl. eapply refine_inst_persist; eauto. *)
    (* Qed. *)
    (* #[global] Arguments refine_demonic_pattern_match' {N} n {σ} pat. *)

    (* Lemma refine_angelic_pattern_match {N : Set} (n : N -> LVar) *)
    (*   {σ} (pat : @Pattern N σ) : *)
    (*   ℛ⟦RMsg _ (RVal σ -> RPureSpec (RMatchResult pat))⟧ *)
    (*     (SPureSpec.angelic_pattern_match n pat) *)
    (*     (CPureSpec.angelic_pattern_match pat). *)
    (* Proof. *)
    (*   induction pat; cbn - [Val]; intros w ι Hpc. *)
    (*   - intros msg sv cv -> sΦ cΦ rΦ. hnf. *)
    (*     rewrite CPureSpec.wp_angelic_pattern_match. *)
    (*     apply rΦ; cbn; rewrite ?inst_sub_id; auto. *)
    (*     now exists eq_refl. *)
    (*   - intros msg sv cv ->. *)
    (*     destruct (term_get_val_spec sv); subst. *)
    (*     + intros sΦ cΦ rΦ. hnf. *)
    (*       rewrite CPureSpec.wp_angelic_pattern_match; cbn. *)
    (*       apply rΦ; cbn; rewrite ?inst_sub_id; auto. *)
    (*       now exists eq_refl. *)
    (*     + now apply (refine_angelic_pattern_match' n pat_bool). *)
    (*   - apply (refine_angelic_pattern_match' n (pat_list σ x y)); auto. *)
    (*   - intros msg sv cv ->. *)
    (*     destruct (term_get_pair_spec sv) as [[svl svr] Heq|]; subst. *)
    (*     + rewrite Heq. intros sΦ cΦ rΦ. hnf. *)
    (*       rewrite CPureSpec.wp_angelic_pattern_match. cbn. *)
    (*       apply rΦ; cbn; rewrite ?inst_sub_id; auto. *)
    (*       now exists eq_refl. *)
    (*     + now apply (refine_angelic_pattern_match' n (pat_pair _ _)); auto. *)
    (*   - intros msg sv cv ->. *)
    (*     destruct (term_get_sum_spec sv) as [[svl|svr] Heq|]; subst. *)
    (*     + rewrite Heq. intros sΦ cΦ rΦ. hnf. *)
    (*       rewrite CPureSpec.wp_angelic_pattern_match. cbn. *)
    (*       apply rΦ; cbn; rewrite ?inst_sub_id; auto. *)
    (*       now exists eq_refl. *)
    (*     + rewrite Heq. intros sΦ cΦ rΦ. hnf. *)
    (*       rewrite CPureSpec.wp_angelic_pattern_match. cbn. *)
    (*       apply rΦ; cbn; rewrite ?inst_sub_id; auto. *)
    (*       now exists eq_refl. *)
    (*     + now apply (refine_angelic_pattern_match' n (pat_sum _ _ _ _)); auto. *)
    (*   - intros msg sv cv -> sΦ cΦ rΦ. hnf. *)
    (*     rewrite CPureSpec.wp_angelic_pattern_match. *)
    (*     apply rΦ; cbn; rewrite ?inst_sub_id; auto. *)
    (*     now exists eq_refl. *)
    (*   - intros msg sv cv ->. *)
    (*     destruct (term_get_val_spec sv); subst. *)
    (*     + intros sΦ cΦ rΦ. hnf. *)
    (*       rewrite CPureSpec.wp_angelic_pattern_match. cbn. *)
    (*       apply rΦ; cbn; rewrite ?inst_sub_id; auto. *)
    (*       now exists eq_refl. *)
    (*     + now apply (refine_angelic_pattern_match' n (pat_enum E)); auto. *)
    (*   - apply (refine_angelic_pattern_match' n (pat_bvec_split _ _ x y)); auto. *)
    (*   - intros msg sv cv ->. *)
    (*     destruct (term_get_val_spec sv); subst. *)
    (*     + intros sΦ cΦ rΦ. hnf. *)
    (*       rewrite CPureSpec.wp_angelic_pattern_match. cbn. *)
    (*       apply rΦ; cbn; rewrite ?inst_sub_id; auto. *)
    (*       now exists eq_refl. *)
    (*     + now apply (refine_angelic_pattern_match' n (pat_bvec_exhaustive m)); auto. *)
    (*   - apply (refine_angelic_pattern_match' n (pat_tuple p)); auto. *)
    (*   - intros msg sv cv ->. *)
    (*     destruct (term_get_record_spec sv) as [svs Heq|]; subst. *)
    (*     + rewrite Heq. intros sΦ cΦ rΦ. hnf. *)
    (*       rewrite CPureSpec.wp_angelic_pattern_match. cbn. *)
    (*       apply rΦ; cbn; rewrite ?inst_sub_id; auto. *)
    (*       exists eq_refl. cbn. *)
    (*       unfold record_pattern_match_val. *)
    (*       rewrite recordv_unfold_fold. *)
    (*       symmetry. apply inst_record_pattern_match. *)
    (*     + now apply (refine_angelic_pattern_match' n (pat_record _ _ _)); auto. *)
    (*   - intros msg sv cv ->. *)
    (*     destruct (term_get_union_spec sv) as [[K scr'] Heq|]; subst. *)
    (*     + rewrite Heq. intros sΦ cΦ rΦ. hnf. *)
    (*       specialize (H K w ι Hpc msg scr' (inst scr' ι) eq_refl). *)
    (*       intros Hwp. eapply H in Hwp; eauto. revert Hwp. cbn. *)
    (*       Unshelve. *)
    (*       3: { *)
    (*         intros [pc δpc]. apply cΦ. now exists (existT K pc). *)
    (*       } *)
    (*       * rewrite ?CPureSpec.wp_angelic_pattern_match. cbn. *)
    (*         rewrite unionv_unfold_fold. *)
    (*         now destruct pattern_match_val; cbn. *)
    (*       * intros ? ? ? ? ? [] [] [e Hmr]. apply rΦ; auto. *)
    (*         rewrite H0. rewrite sub_acc_trans; cbn. *)
    (*         now rewrite inst_subst, inst_sub_id. *)
    (*         subst. now exists eq_refl. *)
    (*     + now apply (refine_angelic_pattern_match' n (pat_union _ _)); auto. *)
    (* Qed. *)
    (* #[global] Arguments refine_angelic_pattern_match' {N} n {σ} pat. *)

    (* Lemma refine_demonic_pattern_match {N : Set} (n : N -> LVar) *)
    (*   {σ} (pat : @Pattern N σ) : *)
    (*   ℛ⟦RVal σ -> RPureSpec (RMatchResult pat)⟧ *)
    (*     (SPureSpec.demonic_pattern_match n pat) *)
    (*     (CPureSpec.demonic_pattern_match pat). *)
    (* Proof. *)
    (*   induction pat; cbn - [Val]; intros w ι Hpc. *)
    (*   - intros sv cv -> sΦ cΦ rΦ. hnf. *)
    (*     rewrite CPureSpec.wp_demonic_pattern_match. *)
    (*     apply rΦ; cbn; rewrite ?inst_sub_id; auto. *)
    (*     now exists eq_refl. *)
    (*   - intros sv cv ->. *)
    (*     destruct (term_get_val_spec sv); subst. *)
    (*     + intros sΦ cΦ rΦ. hnf. *)
    (*       rewrite CPureSpec.wp_demonic_pattern_match; cbn. *)
    (*       apply rΦ; cbn; rewrite ?inst_sub_id; auto. *)
    (*       now exists eq_refl. *)
    (*     + now apply (refine_demonic_pattern_match' n pat_bool). *)
    (*   - apply (refine_demonic_pattern_match' n (pat_list σ x y)); auto. *)
    (*   - intros sv cv ->. *)
    (*     destruct (term_get_pair_spec sv) as [[svl svr] Heq|]; subst. *)
    (*     + rewrite Heq. intros sΦ cΦ rΦ. hnf. *)
    (*       rewrite CPureSpec.wp_demonic_pattern_match. cbn. *)
    (*       apply rΦ; cbn; rewrite ?inst_sub_id; auto. *)
    (*       now exists eq_refl. *)
    (*     + now apply (refine_demonic_pattern_match' n (pat_pair _ _)); auto. *)
    (*   - intros sv cv ->. *)
    (*     destruct (term_get_sum_spec sv) as [[svl|svr] Heq|]; subst. *)
    (*     + rewrite Heq. intros sΦ cΦ rΦ. hnf. *)
    (*       rewrite CPureSpec.wp_demonic_pattern_match. cbn. *)
    (*       apply rΦ; cbn; rewrite ?inst_sub_id; auto. *)
    (*       now exists eq_refl. *)
    (*     + rewrite Heq. intros sΦ cΦ rΦ. hnf. *)
    (*       rewrite CPureSpec.wp_demonic_pattern_match. cbn. *)
    (*       apply rΦ; cbn; rewrite ?inst_sub_id; auto. *)
    (*       now exists eq_refl. *)
    (*     + now apply (refine_demonic_pattern_match' n (pat_sum _ _ _ _)); auto. *)
    (*   - intros sv cv -> sΦ cΦ rΦ. hnf. *)
    (*     rewrite CPureSpec.wp_demonic_pattern_match. *)
    (*     apply rΦ; cbn; rewrite ?inst_sub_id; auto. *)
    (*     now exists eq_refl. *)
    (*   - intros sv cv ->. *)
    (*     destruct (term_get_val_spec sv); subst. *)
    (*     + intros sΦ cΦ rΦ. hnf. *)
    (*       rewrite CPureSpec.wp_demonic_pattern_match. cbn. *)
    (*       apply rΦ; cbn; rewrite ?inst_sub_id; auto. *)
    (*       now exists eq_refl. *)
    (*     + now apply (refine_demonic_pattern_match' n (pat_enum E)); auto. *)
    (*   - apply (refine_demonic_pattern_match' n (pat_bvec_split _ _ x y)); auto. *)
    (*   - intros sv cv ->. *)
    (*     destruct (term_get_val_spec sv); subst. *)
    (*     + intros sΦ cΦ rΦ. hnf. *)
    (*       rewrite CPureSpec.wp_demonic_pattern_match. cbn. *)
    (*       apply rΦ; cbn; rewrite ?inst_sub_id; auto. *)
    (*       now exists eq_refl. *)
    (*     + now apply (refine_demonic_pattern_match' n (pat_bvec_exhaustive m)); auto. *)
    (*   - apply (refine_demonic_pattern_match' n (pat_tuple p)); auto. *)
    (*   - intros sv cv ->. *)
    (*     destruct (term_get_record_spec sv) as [svs Heq|]; subst. *)
    (*     + rewrite Heq. intros sΦ cΦ rΦ. hnf. *)
    (*       rewrite CPureSpec.wp_demonic_pattern_match. cbn. *)
    (*       apply rΦ; cbn; rewrite ?inst_sub_id; auto. *)
    (*       exists eq_refl. cbn. *)
    (*       unfold record_pattern_match_val. *)
    (*       rewrite recordv_unfold_fold. *)
    (*       symmetry. apply inst_record_pattern_match. *)
    (*     + now apply (refine_demonic_pattern_match' n (pat_record _ _ _)); auto. *)
    (*   - intros sv cv ->. *)
    (*     destruct (term_get_union_spec sv) as [[K scr'] Heq|]; subst. *)
    (*     + rewrite Heq. intros sΦ cΦ rΦ. hnf. *)
    (*       specialize (H K w ι Hpc scr' (inst scr' ι) eq_refl). *)
    (*       intros Hwp. eapply H in Hwp; eauto. revert Hwp. cbn. *)
    (*       Unshelve. *)
    (*       3: { *)
    (*         intros [pc δpc]. apply cΦ. now exists (existT K pc). *)
    (*       } *)
    (*       * rewrite ?CPureSpec.wp_demonic_pattern_match. cbn. *)
    (*         rewrite unionv_unfold_fold. *)
    (*         now destruct pattern_match_val; cbn. *)
    (*       * intros ? ? ? ? ? [] [] [e Hmr]. apply rΦ; auto. *)
    (*         rewrite H0. rewrite sub_acc_trans; cbn. *)
    (*         now rewrite inst_subst, inst_sub_id. *)
    (*         subst. now exists eq_refl. *)
    (*     + now apply (refine_demonic_pattern_match' n (pat_union _ _)); auto. *)
    (* Qed. *)
    (* #[global] Arguments refine_demonic_pattern_match' {N} n {σ} pat. *)

    (* Lemma refine_new_pattern_match_regular {N : Set} n σ (pat : @Pattern N σ) : *)
    (*   ℛ⟦RVal σ -> RPureSpec (RMatchResult pat)⟧ *)
    (*     (SPureSpec.new_pattern_match_regular n pat) *)
    (*     (CPureSpec.new_pattern_match pat). *)
    (* Proof. *)
    (*   unfold SPureSpec.new_pattern_match_regular. *)
    (*   intros w0 ι0 Hpc0 sv cv rv spost cpost rpost. *)
    (*   unfold CPureSpec.new_pattern_match. *)
    (*   rewrite <- (pattern_match_val_freshen n pat (Σ := w0)). *)
    (*   pose proof (pattern_match_val_inverse_left (freshen_pattern n w0 pat) (inst sv ι0)). *)
    (*   cbn in rv. subst. cbn. *)
    (*   destruct pattern_match_val as [pc vs]. cbn in H. cbn - [acc_trans]. *)
    (*   unfold pattern_match_val_reverse' in H. cbn in H. *)
    (*   apply rpost; cbn - [sub_cat_left sub_cat_right sub_id]; *)
    (*     rewrite ?inst_subst, ?instprop_subst, ?inst_sub_id, ?inst_sub_cat_left; try easy. *)
    (*   - rewrite inst_pattern_match_term_reverse. split; auto. rewrite <- H. *)
    (*     f_equal. symmetry. apply inst_sub_cat_right. *)
    (*   - exists eq_refl. cbn. symmetry. etransitivity. *)
    (*     apply inst_unfreshen_patterncaseenv. f_equal. *)
    (*     apply inst_sub_cat_right. *)
    (* Qed. *)

    (* Lemma refine_pattern_match_var {N : Set} n {x σ} (pat : @Pattern N σ) : *)
    (*   ℛ⟦RIn (x∷σ) -> RPureSpec (RMatchResult pat)⟧ *)
    (*     (SPureSpec.new_pattern_match_var n pat) *)
    (*     (CPureSpec.new_pattern_match pat). *)
    (* Proof. *)
    (*   intros w0 ι0 Hpc0 sv cv rv spost cpost rpost. *)
    (*   unfold SPureSpec.new_pattern_match_var. hnf. *)
    (*   intros Hsafe. hnf. cbn in rv. subst cv. *)
    (*   rewrite <- (pattern_match_val_freshen n pat (Σ := w0)). *)
    (* Admitted. *)

    (* Lemma refine_new_pattern_match' {N : Set} n σ (pat : @Pattern N σ) : *)
    (*   ℛ⟦RVal σ -> RPureSpec (RMatchResult pat)⟧ *)
    (*     (SPureSpec.new_pattern_match' n pat) *)
    (*     (CPureSpec.new_pattern_match pat). *)
    (* Proof. *)
    (*   unfold SPureSpec.new_pattern_match'. *)
    (*   intros w0 ι0 Hpc0 sv cv rv. *)
    (*   destruct sv. now apply refine_pattern_match_var. *)
    (*   all: now apply refine_new_pattern_match_regular. *)
    (* Qed. *)

    (* Lemma refine_new_pattern_match {N : Set} n σ (pat : @Pattern N σ) : *)
    (*   ℛ⟦RVal σ -> RPureSpec (RMatchResult pat)⟧ (SPureSpec.new_pattern_match n pat) *)
    (*     (CPureSpec.new_pattern_match pat). *)
    (* Proof. *)
    (*   induction pat; cbn [SPureSpec.new_pattern_match]; *)
    (*     intros w0 ι0 Hpc0 sv cv ->. *)
    (*   - unfold CPureSpec.new_pattern_match. *)
    (*     apply refine_pure; auto. now exists eq_refl. *)
    (*   - destruct (term_get_val_spec sv) as [cv ?|]. *)
    (*     + apply refine_pure; auto. subst. now exists eq_refl. *)
    (*     + now apply refine_new_pattern_match' with (pat := pat_bool). *)
    (*   - now apply refine_new_pattern_match'. *)
    (*   - destruct (term_get_pair_spec sv) as [[? ?] ->|]. *)
    (*     + apply refine_pure; auto. now exists eq_refl. *)
    (*     + now apply refine_new_pattern_match' with (pat := pat_pair _ _). *)
    (*   - destruct (term_get_sum_spec sv) as [[] ->|]. *)
    (*     + apply refine_pure; auto. now exists eq_refl. *)
    (*     + apply refine_pure; auto. now exists eq_refl. *)
    (*     + now apply refine_new_pattern_match' with (pat := pat_sum _ _ _ _). *)
    (*   - apply refine_pure; auto. now exists eq_refl. *)
    (*   - destruct (term_get_val_spec sv) as [? ->|]. *)
    (*     + apply refine_pure; auto. now exists eq_refl. *)
    (*     + now apply refine_new_pattern_match' with (pat := pat_enum E). *)
    (*   - now apply refine_new_pattern_match'. *)
    (*   - destruct (term_get_val_spec sv) as [? ->|]. *)
    (*     + apply refine_pure; auto. now exists eq_refl. *)
    (*     + now apply refine_new_pattern_match' with (pat := pat_bvec_exhaustive m). *)
    (*   - destruct (term_get_tuple_spec sv) as [? ->|]. *)
    (*     + apply refine_pure; auto. exists eq_refl. cbn. *)
    (*       unfold tuple_pattern_match_val. *)
    (*       rewrite envrec.to_of_env. symmetry. *)
    (*       apply inst_tuple_pattern_match. *)
    (*     + now apply refine_new_pattern_match'. *)
    (*   - destruct (term_get_record_spec sv) as [? ->|]. *)
    (*     + apply refine_pure; auto. exists eq_refl. cbn. *)
    (*       unfold record_pattern_match_val. *)
    (*       rewrite recordv_unfold_fold. symmetry. *)
    (*       apply inst_record_pattern_match. *)
    (*     + now apply refine_new_pattern_match'. *)
    (*   - destruct (term_get_union_spec sv) as [[K tf] Heq|]. *)
    (*     + intros spost cpost rpost. cbn. intros Hsafe. *)
    (*       specialize (H K w0 ι0 Hpc0 tf (inst tf ι0) eq_refl). *)
    (*       rewrite Heq. hnf. cbn. rewrite unionv_unfold_fold. *)
    (*       unfold CPureSpec.new_pattern_match in H. *)
    (*       clear Heq. *)
    (*       destruct (pattern_match_val (p K) (inst tf ι0)) as [pc δpc] eqn:?. *)
    (*       eapply H in Hsafe; eauto. *)
    (*       Unshelve. *)
    (*       3: { *)
    (*         intros mr. apply cpost.  cbn. destruct mr as [pc' δpc']. *)
    (*         exists (existT K pc'). apply δpc'. *)
    (*       } *)
    (*       exact Hsafe. *)
    (*       intros w1 θ1 ι1 Heq1 Hpc1 [spc sδ] [cpc cδ] [rpc rδ]. *)
    (*       subst. cbn in rδ. subst. cbn. cbv [SPureSpec.pure four T]. cbn. *)
    (*       intros Hsafe'. eapply rpost; eauto. Unshelve. *)
    (*       3: { *)
    (*         exists (existT K cpc). apply sδ. *)
    (*       } *)
    (*       exists eq_refl; cbn. reflexivity. *)
    (*       now destruct θ1. *)
    (*     + now apply refine_new_pattern_match'. *)
    (* Qed. *)

    (* Lemma refine_debug `{RA : Rel SA CA} : *)
    (*   ℛ⟦RMsg _ (RPureSpec RA -> RPureSpec RA)⟧ *)
    (*     SPureSpec.debug CPureSpec.debug. *)
    (* Proof. *)
    (*   intros w0 ι0 Hpc0 msg sm cm rm. cbn - [RSat]. *)
    (*   intros sΦ cΦ rΦ [HΦ]. revert HΦ. now apply rm. *)
    (* Qed. *)

    (* Lemma refine_assert_eq_nenv {N : Set} : *)
    (*   ℛ⟦∀ Δ : NCtx N Ty, RMsg _ (RNEnv Δ -> RNEnv Δ -> RPureSpec RUnit)⟧ *)
    (*     SPureSpec.assert_eq_nenv CPureSpec.assert_eq_nenv. *)
    (* Proof. *)
    (*   intros w0 ι0 Hpc0 Δ msg E1 ? -> E2 ? ->. *)
    (*   induction E1; env.destroy E2; cbn - [RSat]. *)
    (*   - now apply refine_pure. *)
    (*   - eapply refine_bind; eauto. *)
    (*     intros w1 ω01 ι1 Hι1 Hpc1 _ _ _. *)
    (*     apply refine_assert_formula; auto. *)
    (*     eapply refine_formula_persist; eauto. *)
    (*     cbn. reflexivity. *)
    (* Qed. *)

    (* Lemma refine_assert_eq_env : *)
    (*   ℛ⟦∀ Δ, RMsg _ (REnv Δ -> REnv Δ -> RPureSpec RUnit)⟧ *)
    (*     SPureSpec.assert_eq_env CPureSpec.assert_eq_env. *)
    (* Proof. *)
    (*   intros w0 ι0 Hpc0 Δ msg E1 ? -> E2 ? ->. *)
    (*   induction E1; env.destroy E2; cbn - [RSat]. *)
    (*   - now apply refine_pure. *)
    (*   - eapply refine_bind; eauto. *)
    (*     intros w1 ω01 ι1 Hι1 Hpc1 _ _ _. *)
    (*     apply refine_assert_formula; auto. *)
    (*     eapply refine_formula_persist; eauto. *)
    (*     cbn. reflexivity. *)
    (* Qed. *)

    (* Lemma refine_assert_eq_chunk : *)
    (*   ℛ⟦RMsg _ (RChunk -> RChunk -> □(RPureSpec RUnit))⟧ *)
    (*     SPureSpec.assert_eq_chunk CPureSpec.assert_eq_chunk. *)
    (* Proof. *)
    (*   intros w0 ι0 Hpc0 msg c ? -> c' ? ->. revert c'. *)
    (*   induction c; intros [] w1 ω01 ι1 Hι1 Hpc1; cbn - [RSat]; *)
    (*     auto; try (now apply refine_error). *)
    (*   - destruct eq_dec. *)
    (*     + destruct e; cbn. *)
    (*       apply refine_assert_eq_env; auto. *)
    (*       eapply refine_inst_persist; eauto; easy. *)
    (*       eapply refine_inst_persist; eauto; easy. *)
    (*     + now apply refine_error. *)
    (*   - destruct eq_dec_het. *)
    (*     + dependent elimination e; cbn. *)
    (*       apply refine_assert_formula; auto. subst. *)
    (*       now do 2 rewrite <- inst_persist. *)
    (*     + now apply refine_error. *)
    (*   - eapply refine_bind; eauto. apply IHc1; auto. *)
    (*     intros w2 ω12 ι2 Hι2 Hpc2 _ _ _. apply IHc2; auto. *)
    (*     subst. now rewrite sub_acc_trans, inst_subst, <- inst_persist. *)
    (*   - eapply refine_bind; eauto. apply IHc1; auto. *)
    (*     intros w2 ω12 ι2 Hι2 Hpc2 _ _ _. apply IHc2; auto. *)
    (*     subst. now rewrite sub_acc_trans, inst_subst, <- inst_persist. *)
    (* Qed. *)

    (* Lemma refine_replay_aux {Σ} (s : 𝕊 Σ) : *)
    (*   ℛ⟦RInst (Sub Σ) (Valuation Σ) -> RPureSpec RUnit⟧ *)
    (*     (SPureSpec.replay_aux s) (CPureSpec.replay_aux s). *)
    (* Proof. *)
    (*   unfold RValid, RImpl. cbn - [RPureSpec]. *)
    (*   induction s; cbn [SPureSpec.replay_aux CPureSpec.replay_aux]; *)
    (*     intros w ι Hpc sδ cδ rδ. *)
    (*   - apply refine_angelic_binary; auto. *)
    (*   - apply refine_demonic_binary; auto. *)
    (*   - apply refine_error; auto. *)
    (*   - apply refine_block; auto. *)
    (*   - eapply refine_bind; auto. *)
    (*     + apply refine_assert_formula; auto. *)
    (*       now apply refine_formula_subst. *)
    (*     + intros w1 θ1 ι1 Hι1 Hpc1 _ _ _. *)
    (*       apply IHs; auto. subst. *)
    (*       now rewrite <- inst_persist. *)
    (*   - eapply refine_bind; auto. *)
    (*     + apply refine_assume_formula; auto. *)
    (*       now apply refine_formula_subst. *)
    (*     + intros w1 θ1 ι1 Hι1 Hpc1 _ _ _. *)
    (*       apply IHs; auto. subst. *)
    (*       now rewrite <- inst_persist. *)
    (*   - eapply refine_bind; auto. *)
    (*     + apply refine_angelic; auto. *)
    (*     + intros w1 θ1 ι1 Hι1 Hpc1 t v ->. *)
    (*       apply IHs; auto. subst. *)
    (*       now rewrite <- inst_persist. *)
    (*   - eapply refine_bind; auto. *)
    (*     + apply refine_demonic; auto. *)
    (*     + intros w1 θ1 ι1 Hι1 Hpc1 t v ->. *)
    (*       apply IHs; auto. subst. *)
    (*       now rewrite <- inst_persist. *)
    (*   - eapply refine_bind; auto. *)
    (*     + apply refine_assert_formula; auto. *)
    (*       cbn. subst. *)
    (*       rewrite !inst_subst. *)
    (*       rewrite inst_sub_shift. *)
    (*       now rewrite <- inst_lookup. *)
    (*     + intros w1 θ1 ι1 Hι1 Hpc1 _ _ _. *)
    (*       apply IHs; auto. subst. *)
    (*       rewrite <- inst_subst. *)
    (*       rewrite <- persist_subst. *)
    (*       rewrite <- inst_sub_shift. *)
    (*       rewrite <- inst_subst. *)
    (*       rewrite sub_comp_shift. *)
    (*       reflexivity. *)
    (*   - eapply refine_bind; auto. *)
    (*     + apply refine_assume_formula; auto. *)
    (*       cbn. subst. *)
    (*       rewrite !inst_subst. *)
    (*       rewrite inst_sub_shift. *)
    (*       now rewrite <- inst_lookup. *)
    (*     + intros w1 θ1 ι1 Hι1 Hpc1 _ _ _. *)
    (*       apply IHs; auto. subst. *)
    (*       rewrite <- inst_subst. *)
    (*       rewrite <- persist_subst. *)
    (*       rewrite <- inst_sub_shift. *)
    (*       rewrite <- inst_subst. *)
    (*       rewrite sub_comp_shift. *)
    (*       reflexivity. *)
    (*   - apply refine_error; auto. *)
    (*   - apply refine_error; auto. *)
    (*   - apply refine_debug; auto. *)
    (* Qed. *)

    (* Lemma refine_replay {w : World} (s : 𝕊 w) ι (Hpc : instprop (wco w) ι) : *)
    (*   ℛ⟦ℙ⟧@{ι} (SPureSpec.replay s) (CPureSpec.replay s ι). *)
    (* Proof. *)
    (*   apply refine_run; auto. *)
    (*   apply refine_replay_aux; auto. *)
    (*   cbn. now rewrite inst_sub_id. *)
    (* Qed. *)

    (* Lemma refine_produce_chunk : *)
    (*   ℛ⟦RChunk -> RHeap -> RPureSpec RHeap⟧ *)
    (*     SPureSpec.produce_chunk CPureSpec.produce_chunk. *)
    (* Proof. *)
    (*   intros w ι Hpc sc cc rc sh ch rh. *)
    (*   unfold SPureSpec.produce_chunk, CPureSpec.produce_chunk. *)
    (*   apply refine_pure; auto. cbn. *)
    (*   rewrite peval_chunk_sound. now f_equal. *)
    (* Qed. *)

    (* Lemma refine_consume_chunk : *)
    (*   ℛ⟦RChunk -> RHeap -> RPureSpec RHeap⟧ *)
    (*     SPureSpec.consume_chunk CPureSpec.consume_chunk. *)
    (* Proof. *)
    (*   intros w0 ι0 Hpc0 cs cc -> sh ch ->. *)
    (*   unfold SPureSpec.consume_chunk. *)
    (*   set (c1 := peval_chunk cs). *)
    (*   destruct (try_consume_chunk_exact_spec sh c1) as [sh' HIn|]. *)
    (*   { intros POST__s POST__c HPOST. *)
    (*     unfold CPureSpec.consume_chunk. *)
    (*     cbn. intros Hwp. *)
    (*     rewrite CPureSpec.wp_angelic_list. *)
    (*     change (SHeap w0) in sh'. *)
    (*     exists (inst c1 ι0, inst sh' ι0). *)
    (*     split. *)
    (*     - unfold inst at 3, inst_heap, inst_list. *)
    (*       rewrite heap_extractions_map, List.in_map_iff. *)
    (*       + exists (c1 , sh'). split. reflexivity. assumption. *)
    (*       + eauto using inst_is_duplicable. *)
    (*     - cbn. rewrite CPureSpec.wp_assert_eq_chunk. subst. *)
    (*       split; auto. *)
    (*       + subst c1. now rewrite peval_chunk_sound. *)
    (*       + revert Hwp. apply HPOST; now wsimpl. *)
    (*   } *)
    (*   destruct (try_consume_chunk_precise_spec sh c1) as [[sh' eqs] HIn|]. *)
    (*   { cbv [SPureSpec.bind SPureSpec.pure]. *)
    (*     intros POST__s POST__c HPOST. *)
    (*     match goal with | |- context[amsg.mk ?m] => generalize (amsg.mk m) end. *)
    (*     intros msg Hwp. *)
    (*     pose proof (refine_assert_pathcondition Hpc0 msg (ta := eqs)) as Hassert. *)
    (*     inster Hassert by (cbn; reflexivity). *)
    (*     match goal with *)
    (*     | H: SymProp.wsafe (SPureSpec.assert_pathcondition msg eqs ?P) _ |- _ => *)
    (*         specialize (Hassert P (fun _ => POST__c (inst sh' ι0))) *)
    (*     end. *)
    (*     apply Hassert in Hwp; clear Hassert. *)
    (*     - destruct Hwp as [Heqs HP]. *)
    (*       unfold CPureSpec.consume_chunk, CPureSpec.bind, CPureSpec.pure. *)
    (*       rewrite CPureSpec.wp_angelic_list. *)
    (*       exists (inst c1 ι0, inst sh' ι0). split; [auto|]. subst c1. *)
    (*       now rewrite CPureSpec.wp_assert_eq_chunk, peval_chunk_sound. *)
    (*     - intros w1 θ1 ι1 -> Hpc1 _ _ _. unfold T, four. *)
    (*       apply HPOST; auto. *)
    (*       + rewrite sub_acc_trans. cbn. now rewrite subst_sub_id. *)
    (*       + now eapply refine_inst_persist; eauto. *)
    (*   } *)
    (*   { intros POST__s POST__c HPOST. now apply refine_error. } *)
    (* Qed. *)

    (* Lemma refine_heap_extractions : *)
    (*   ℛ⟦RHeap -> RList (RProd RChunk RHeap)⟧ *)
    (*     (fun w h => heap_extractions h) *)
    (*     (heap_extractions). *)
    (* Proof. *)
    (*   intros w0 ι0 Hpc0 sh ch ->. hnf. *)
    (*   unfold inst, inst_heap, inst_list. *)
    (*   rewrite heap_extractions_map. *)
    (*   { clear. induction (heap_extractions sh) as [|[]]; *)
    (*       cbn; constructor; cbn; auto. } *)
    (*   eauto using inst_is_duplicable. *)
    (* Qed. *)

    (* Lemma refine_consume_chunk_angelic : *)
    (*   ℛ⟦RChunk -> RHeap -> RPureSpec RHeap⟧ *)
    (*     SPureSpec.consume_chunk_angelic CPureSpec.consume_chunk. *)
    (* Proof. *)
    (*   intros w0 ι0 Hpc0 cs cc -> sh ch ->. *)
    (*   unfold SPureSpec.consume_chunk_angelic. *)
    (*   set (c1 := peval_chunk cs). *)
    (*   destruct (try_consume_chunk_exact_spec sh c1) as [sh' HIn|]. *)
    (*   { intros POST__s POST__c HPOST. *)
    (*     unfold CPureSpec.consume_chunk. *)
    (*     cbn. intros Hwp. *)
    (*     rewrite CPureSpec.wp_angelic_list. *)
    (*     change (SHeap w0) in sh'. *)
    (*     exists (inst c1 ι0, inst sh' ι0). *)
    (*     split. *)
    (*     - unfold inst at 3, inst_heap, inst_list. *)
    (*       rewrite heap_extractions_map, List.in_map_iff. *)
    (*       + exists (c1 , sh'). split. reflexivity. assumption. *)
    (*       + eauto using inst_is_duplicable. *)
    (*     - cbn. rewrite CPureSpec.wp_assert_eq_chunk. subst. *)
    (*       split; auto. *)
    (*       + subst c1. now rewrite peval_chunk_sound. *)
    (*       + revert Hwp. apply HPOST; now wsimpl. *)
    (*   } *)
    (*   destruct (try_consume_chunk_precise_spec sh c1) as [[sh' eqs] HIn|]. *)
    (*   { cbv [SPureSpec.bind SPureSpec.pure]. *)
    (*     intros POST__s POST__c HPOST. *)
    (*     match goal with | |- context[amsg.mk ?m] => generalize (amsg.mk m) end. *)
    (*     intros msg Hwp. *)
    (*     pose proof (refine_assert_pathcondition Hpc0 msg (ta := eqs)) as Hassert. *)
    (*     inster Hassert by (cbn; reflexivity). *)
    (*     match goal with *)
    (*     | H: SymProp.wsafe (SPureSpec.assert_pathcondition msg eqs ?P) _ |- _ => *)
    (*         specialize (Hassert P (fun _ => POST__c (inst sh' ι0))) *)
    (*     end. *)
    (*     apply Hassert in Hwp; clear Hassert. *)
    (*     - destruct Hwp as [Heqs HP]. *)
    (*       unfold CPureSpec.consume_chunk, CPureSpec.bind, CPureSpec.pure. *)
    (*       rewrite CPureSpec.wp_angelic_list. *)
    (*       exists (inst c1 ι0, inst sh' ι0). split; [auto|]. subst c1. *)
    (*       now rewrite CPureSpec.wp_assert_eq_chunk, peval_chunk_sound. *)
    (*     - intros w1 θ1 ι1 -> Hpc1 _ _ _. unfold T, four. *)
    (*       apply HPOST; auto. *)
    (*       + rewrite sub_acc_trans. cbn. now rewrite subst_sub_id. *)
    (*       + now eapply refine_inst_persist; eauto. *)
    (*   } *)
    (*   { apply refine_bind; auto. *)
    (*     apply refine_angelic_list; auto. *)
    (*     now apply refine_heap_extractions. *)
    (*     intros w2 ω12 ι2 -> Hpc2. *)
    (*     intros [sc' sh'] [cc' ch'] [rc rh']. *)
    (*     apply refine_bind; auto. *)
    (*     - eapply refine_assert_eq_chunk; eauto. *)
    (*       + eapply refine_inst_persist; eauto. *)
    (*         subst c1. cbn. *)
    (*         now rewrite peval_chunk_sound. *)
    (*       + cbn. now rewrite inst_sub_id. *)
    (*     - intros w3 ω23 ι3 -> Hpc3 _ _ _. *)
    (*       apply refine_pure; auto. *)
    (*       eapply refine_inst_persist; eauto. *)
    (*   } *)
    (* Qed. *)

    (* Lemma refine_read_register {τ} (reg : 𝑹𝑬𝑮 τ) : *)
    (*   ℛ⟦RHeap -> RPureSpec (RProd (RVal τ) RHeap)⟧ *)
    (*     (SPureSpec.read_register reg) (CPureSpec.read_register reg). *)
    (* Proof. *)
    (*   unfold SPureSpec.read_register, SPureSpec.pure, T. *)
    (*   intros w0 ι0 Hpc0 sh ch -> sΦ cΦ rΦ HΦ. *)
    (*   destruct (find_chunk_ptsreg_precise_spec reg sh) as [[st sh'] HIn|]. *)
    (*   - cbv [CPureSpec.read_register CPureSpec.consume_chunk CPureSpec.pure *)
    (*            CPureSpec.produce_chunk CPureSpec.bind CPureSpec.angelic]. *)
    (*     set (v := inst (T := STerm τ) st ι0). exists v. *)
    (*     rewrite CPureSpec.wp_angelic_list. *)
    (*     exists (scchunk_ptsreg reg v, inst sh' ι0). *)
    (*     split. apply HIn. *)
    (*     rewrite CPureSpec.wp_assert_eq_chunk. split. easy. *)
    (*     revert HΦ. apply rΦ; cbn; auto. *)
    (*     now rewrite inst_sub_id. *)
    (*   - inversion HΦ. *)
    (* Qed. *)

    (* Lemma refine_write_register {τ} (reg : 𝑹𝑬𝑮 τ) : *)
    (*   ℛ⟦RVal τ -> RHeap -> RPureSpec (RProd (RVal τ) RHeap)⟧ *)
    (*     (SPureSpec.write_register reg) (CPureSpec.write_register reg). *)
    (* Proof. *)
    (*   unfold SPureSpec.write_register, SPureSpec.pure, T. *)
    (*   intros w0 ι0 Hpc0 sv cv rv sh ch rh sΦ cΦ rΦ HΦ. *)
    (*   destruct (find_chunk_ptsreg_precise_spec reg sh) as [[st sh'] HIn|]. *)
    (*   - cbv [CPureSpec.write_register CPureSpec.consume_chunk CPureSpec.pure *)
    (*            CPureSpec.produce_chunk CPureSpec.bind CPureSpec.angelic]. *)
    (*     set (vold := inst (T := STerm τ) st ι0). exists vold. *)
    (*     rewrite CPureSpec.wp_angelic_list. *)
    (*     exists (scchunk_ptsreg reg vold, inst sh' ι0). *)
    (*     split. rewrite rh. apply HIn. *)
    (*     rewrite CPureSpec.wp_assert_eq_chunk. split. easy. *)
    (*     revert HΦ. apply rΦ; auto. *)
    (*     + cbn. now rewrite inst_sub_id. *)
    (*     + constructor; auto. cbn. now do 2 f_equal. *)
    (*   - inversion HΦ. *)
    (* Qed. *)

  End Monads.
    
  Section Basics.

    Import logicalrelation.
    Import ufl_notations.

    #[export] Instance RHeapSpec [SA CA] (RA : Rel SA CA) :
      Rel (SHeapSpec SA) (CHeapSpec CA) := □ᵣ(RA -> RHeap -> ℙ) -> RHeap -> ℙ.

    #[export] Instance RStore (Γ : PCtx) : Rel (SStore Γ) (CStore Γ) :=
      RInst (SStore Γ) (CStore Γ).

    #[export] Instance RStoreSpec Γ1 Γ2 `(R : Rel AT A) :
      Rel (SStoreSpec Γ1 Γ2 AT) (CStoreSpec Γ1 Γ2 A) :=
      □ᵣ (R -> RStore Γ2 -> RHeap -> ℙ) -> RStore Γ1 -> RHeap -> ℙ.

    Lemma refine_evalStoreSpec {Γ1 Γ2} `{RA : Rel SA CA} {w : World} :
      ⊢ (ℛ⟦RStoreSpec Γ1 Γ2 RA -> RStore Γ1 -> RHeapSpec RA⟧
           CStoreSpec.evalStoreSpec (fun w => SStoreSpec.evalStoreSpec w) : Pred w).
    Proof.
      unfold SStoreSpec.evalStoreSpec, CStoreSpec.evalStoreSpec.
      iIntros (ss tss) "Hss".
      iIntros (s ts) "Hs".
      iIntros (k ks) "Hk".
      iIntros (h hs) "Hh".
      iIntros "Hsym".
      iApply ("Hss" with "[Hk] Hs Hh Hsym").
      iIntros (w' ω).
      iSpecialize ("Hk" $! _ ω).
      iModIntro.
      iIntros (a ta) "Ha".
      iIntros (s2 ts2) "Hs2".
      iIntros (h2 th2) "Hh2".
      now iApply ("Hk" with "Ha Hh2").
    Qed.

    Lemma refine_lift_purem {Γ} `(R : Rel AT A) {w : World}:
      ⊢ ℛ⟦RPureSpec R -> RStoreSpec Γ Γ R⟧
        CStoreSpec.lift_purem (SStoreSpec.lift_purem (w := w)).
    Proof.
      unfold RPureSpec, RStoreSpec, SStoreSpec.lift_purem, CStoreSpec.lift_purem.
      iIntros (p ps) "Hp".
      iIntros (k ks) "Hk".
      iIntros (s ss) "Hs".
      iIntros (h hs) "Hh".
      iApply "Hp".
      iIntros (w' ω).
      iSpecialize ("Hk" $! _ ω).
      iModIntro.
      iIntros (k2 k2s) "Hk2".
      iApply ("Hk" with "Hk2 [Hs]").
      - iApply (refine_inst_persist s).
        now iModIntro.
      - iApply (refine_inst_persist h).
        now iModIntro.
    Qed.

    Lemma refine_block_store {Γ1 Γ2} `{R : Rel AT A} {w : World} :
      ⊢ ℛ⟦RStoreSpec Γ1 Γ2 R⟧ CStoreSpec.block (SStoreSpec.block (w := w)).
    Proof.
      iIntros (k ks) "Hk".
      iIntros (s ss) "Hs".
      iIntros (h hs) "Hh _".
      now iPureIntro.
    Qed.

    Lemma refine_error_ss `{Subst M, OccursCheck M, R : Rel AT A} {Γ1 Γ2} {w : World} :
      forall (cm : CStoreSpec Γ1 Γ2 A),
        ⊢ ℛ⟦RMsg _ (RStoreSpec Γ1 Γ2 R)⟧ cm (SStoreSpec.error (w := w)).
    Proof.
      iIntros (cm msg k ks) "Hk".
      iIntros (s ss) "Hs".
      iIntros (h hs) "Hh []".
    Qed.

    Lemma refine_pure_ss `{R : Rel AT A} {Γ} {w : World} :
      ⊢ ℛ⟦R -> RStoreSpec Γ Γ R⟧ CStoreSpec.pure (SStoreSpec.pure (w := w)).
    Proof.
      unfold SStoreSpec.pure, CStoreSpec.pure.
      iIntros (r rs) "Hr".
      iIntros (k ks) "Hk".
      iIntros (s ss) "Hs".
      iIntros (h hs) "Hh HPS".
      iMod "Hk".
      now iApply ("Hk" with "Hr Hs Hh HPS").
    Qed.

    Lemma refine_bind_ss `{RA : Rel AT A, RB : Rel BT B} {Γ1 Γ2 Γ3} {w : World} :
      ⊢ ℛ⟦RStoreSpec Γ1 Γ2 RA -> □ᵣ(RA -> RStoreSpec Γ2 Γ3 RB) -> RStoreSpec Γ1 Γ3 RB⟧
        CStoreSpec.bind (SStoreSpec.bind (w := w)).
    Proof.
      unfold SStoreSpec.bind, CStoreSpec.bind.
      iIntros (m ms) "Hm".
      iIntros (c cs) "Hc".
      iIntros (k ks) "Hk".
      iIntros (s ss) "Hs".
      iIntros (h hs) "Hh HPS".
      iApply ("Hm" with "[Hk Hc] Hs Hh HPS").
      iIntros (w' ω).
      iModIntro.
      iPoseProof (forgetting_unconditionally_drastic with "Hc") as "Hc".
      iPoseProof (forgetting_unconditionally with "Hk") as "Hk".
      iIntros (a aas) "Ha".
      iIntros (s2 s2s) "Hs".
      iIntros (h2 h2s) "Hh".
      now iApply ("Hc" with "Ha Hk Hs Hh").
    Qed.

    Lemma refine_angelic_ss (x : option LVar) {Γ} {w : World} :
      ⊢ ℛ⟦∀ᵣ σ, RStoreSpec Γ Γ (RVal σ)⟧ CStoreSpec.angelic (SStoreSpec.angelic (w := w) x).
    Proof.
      unfold SStoreSpec.angelic, CStoreSpec.angelic.
      iIntros (σ).
      iApply (refine_lift_purem (RVal σ)).
      now iApply refine_angelic.
    Qed.

    Lemma refine_demonic_ss (x : option LVar) {Γ} {w : World} :
      ⊢ ℛ⟦∀ᵣ σ, RStoreSpec Γ Γ (RVal σ)⟧ CStoreSpec.demonic (SStoreSpec.demonic (w := w) x).
    Proof.
      unfold SStoreSpec.angelic, CStoreSpec.angelic.
      iIntros (σ).
      iApply (refine_lift_purem (RVal σ)).
      now iApply refine_demonic.
    Qed.

    Lemma refine_angelic_ctx_ss {N : Set} {n : N -> LVar} {Γ} {w} :
      ⊢ ℛ⟦∀ᵣ Δ, RStoreSpec Γ Γ (RNEnv N Δ)⟧
        CStoreSpec.angelic_ctx (SStoreSpec.angelic_ctx (w := w) n).
    Proof.
      unfold SStoreSpec.angelic_ctx, CStoreSpec.angelic_ctx.
      iIntros (Δ).
      iApply (refine_lift_purem (RNEnv N Δ)).
      iApply refine_angelic_ctx.
    Qed.

    Lemma refine_demonic_ctx_ss {N : Set} {n : N -> LVar} {Γ} {w} :
      ⊢ ℛ⟦∀ᵣ Δ, RStoreSpec Γ Γ (RNEnv N Δ)⟧
        CStoreSpec.demonic_ctx (SStoreSpec.demonic_ctx (w := w) n).
    Proof.
      unfold SStoreSpec.demonic_ctx, CStoreSpec.demonic_ctx.
      iIntros (Δ).
      iApply (refine_lift_purem (RNEnv N Δ)).
      iApply refine_demonic_ctx.
    Qed.

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

  End Basics.

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
