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
  Module Import P := Pred B SIG.
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

    Section DebugPred.
      Lemma elim_debugPred {B : LCtx → Type} {w : World} {b : B w} {P : Pred w} :
        DebugPred B b P ⊢ P.
      Proof.
        crushPredEntails3.
        now destruct H0.
      Qed.
    End DebugPred.


    (* nicer version of wsafe *)
    Fixpoint psafe {w : World} (p : SymProp w) : Pred w := 
      (match p with
       | angelic_binary o1 o2 => psafe o1 ∨ psafe o2
       | demonic_binary o1 o2 => psafe o1 ∗ psafe o2
       | error msg => False
       | SymProp.block => True
       | assertk fml msg o =>
           (Obligation msg fml : Pred w) ∗ psafe (w := wformula w fml) o
       | assumek fml o => (instprop fml : Pred w) -∗ psafe (w := wformula w fml) o
       | angelicv b k => knowing acc_snoc_right (@psafe (wsnoc w b) k)
       | demonicv b k => assuming acc_snoc_right (@psafe (wsnoc w b) k)
       | @assert_vareq _ x σ xIn t msg k =>
          (let ζ := sub_shift xIn in
           Obligation (subst msg ζ) (formula_relop bop.eq (term_var x) (subst t ζ)) : Pred w) ∗
            assuming (acc_subst_right (xIn := xIn) t) (psafe (w := wsubst w x t) k)
       | @assume_vareq _ x σ xIn t k =>
           (* eqₚ (term_var x (ςInΣ := xIn)) (subst t (sub_shift xIn)) -∗ *)
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

    Lemma psafe_safe {w p} : psafe (w := w) p ⊣⊢ safe p.
    Proof.
      refine (SymProp_ind (fun Σ p => forall (w : World) (eq : Σ = w), (psafe (w := w) (eq_rect Σ 𝕊 p w eq) : Pred w) ⊣⊢ safe (eq_rect Σ 𝕊 p w eq)) _ _ _ _ _ _ _ _ _ _ _ _ _ p w eq_refl);
        clear; intros; subst; cbn.
      5, 6:  specialize (H (wformula w fml) eq_refl); cbn in H.
      7, 8:  specialize (H (wsnoc w b) eq_refl); cbn in H.
      9, 10: specialize (H (wsubst w x t)%ctx eq_refl); cbn in H.
      all: crushPredEntails3.
      all: repeat match goal with
        [ H : forall (x : @eq ?A ?y ?y), _ |- _ ] => specialize (H eq_refl); cbn in H
      end; crushPredEntails3.
      - now rewrite obligation_equiv in H1.
      - apply H; last done.
        split; first done.
        now rewrite obligation_equiv in H1.
      - now rewrite obligation_equiv.
      - apply H; last done.
        now split.
      - apply H; last done.
        now split.
      - apply H; last done.
        now split.
      - destruct H1 as (ι' & <- & Hpc' & Hsafe).
        destruct (env.view ι') as [ι v].
        exists v.
        apply H; cbn; now rewrite ?instprop_subst inst_sub_wk1.
      - exists (ι.[b ↦ x]).
        split.
        + apply inst_sub_wk1.
        + split; cbn.
          * now rewrite instprop_subst inst_sub_wk1.
          * apply H; last done.
            now rewrite instprop_subst inst_sub_wk1.
      - apply H; cbn.
        + now rewrite instprop_subst inst_sub_wk1.
        + apply H1; cbn; now rewrite ?instprop_subst inst_sub_wk1.
      - intros ιpast <- Hpc2.
        apply H; first done.
        destruct (env.view ιpast) as [ι v].
        specialize (H1 v); cbn in H1.
        now rewrite inst_sub_wk1 in H1.
      - rewrite <-inst_sub_shift.
        rewrite obligation_equiv in H1; cbn in H1.
        now rewrite <-inst_subst.
      - rewrite <-inst_sub_shift.
        rewrite obligation_equiv in H1; cbn in H1.
        rewrite inst_subst in H1.
        assert (instprop (wco (wsubst w x t)) (inst (sub_shift xIn) ι)).
        { rewrite instprop_subst.
          now rewrite inst_sub_single_shift.
        }
        apply H; first done.
        apply H2; last done.
        now rewrite inst_sub_single_shift.
      - rewrite obligation_equiv.
        cbn.
        now rewrite inst_subst inst_sub_shift.
      - intros ιpast <- Hpc2.
        apply H; first done.
        cbn in H2.
        now rewrite <-inst_sub_shift, <-inst_subst, sub_comp_shift_single, inst_sub_id in H2.
      - rewrite <-inst_sub_shift.
        rewrite <-inst_sub_shift in H2.
        assert (instprop (wco (wsubst w x t)) (inst (sub_shift xIn) ι)).
        { rewrite instprop_subst.
          now rewrite inst_sub_single_shift.
        }
        apply H; first done.
        apply H1; last done.
        now rewrite inst_sub_single_shift.
      - intros ιpast <- Hpc.
        apply H; first done.
        rewrite <-inst_sub_shift in H1.
        rewrite <-!inst_subst in H1.
        rewrite sub_comp_shift_single inst_sub_id in H1.
        apply H1.
        rewrite <-inst_lookup.
        rewrite lookup_sub_single_eq.
        rewrite <-subst_sub_comp.
        now rewrite sub_comp_shift_single subst_sub_id.
      - admit.
      - admit.
      - admit.
      - now destruct H1.
      - now constructor.
    Admitted.


    #[export] Instance proper_psafe: ∀ {w : World}, Proper (sequiv w ==> entails (w := w)) psafe.
    Proof.
      intros w P sP HP.
      rewrite !psafe_safe.
      constructor.
      intros.
      now apply HP.
    Qed.

    (* Relatedness of symbolic and shallow propositions. The driving base case! *)
    #[export] Instance RProp : Rel SymProp Prop :=
      MkRel (fun P w SP => (psafe SP -∗ ⌜ P ⌝)%I).

    #[export] Instance rprop_proper {w : World} : Proper (impl ==> sequiv _ ==> entails (w := w)) (fun P => ℛ⟦ RProp ⟧ P).
    Proof.
      iIntros (P1 P2 HP sP1 sP2 HsP) "H1 HSP".
      rewrite <-HsP.
      iDestruct ("H1" with "HSP") as "%HP1".
      iPureIntro.
      now apply HP.
    Qed.


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

  Section SolverSpec.
    (* Try a relatively direct translation first.
     * TODO: looks more like a knowing modality actually.
     *)
    Definition SolverSpec (s : Solver) (w : World) : Prop :=
      forall (C0 : PathCondition w),
        option.spec
          (fun '(existT w1 (ζ, C1)) =>
             (knowing (acc_triangular ζ) (instprop C1)) ⊣⊢ (instprop C0 : Pred w))%I
          ((instprop C0 : Pred w) ⊢ False)%I
          (s w C0).

    Lemma SolverSpec_old_to_logical {s} : SIG.SolverSpec s -> forall w, SolverSpec s w.
    Proof.
      unfold SIG.SolverSpec.
      intros oldspec w C.
      destruct (oldspec w C) as [(w1 & (ζ , C1)) | H];
        cbn in *;
        constructor;
        unfold forgetting, assuming, knowing;
        crushPredEntails3.
      - apply H2; last done.
        now rewrite sub_acc_triangular in H1.
      - exists (inst (sub_triangular_inv ζ) ι).
        rewrite sub_acc_triangular.
        rewrite inst_triangular_right_inverse; last done.
        repeat split.
        + now apply entails_triangular_inv.
        + apply H2; last done.
          * now apply entails_triangular_inv. 
          * now rewrite inst_triangular_right_inverse.
    Qed.

  End SolverSpec.

  Module PureSpec.
    Section Monads.

    Import logicalrelation.
    Import ufl_notations.

    #[export] Instance RPureSpec [SA CA] (RA : Rel SA CA) :
      Rel (SPureSpec SA) (CPureSpec CA) := □ᵣ(RA -> RProp) -> RProp.

    Import iris.bi.interface iris.proofmode.tactics.
    Lemma refine_run {w} :
      ⊢ ℛ⟦RPureSpec RUnit -> RProp ⟧ CPureSpec.run (SPureSpec.run (w := w)).
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

    Lemma obligation_equiv {w : World} (msg : AMessage w) (fml : Formula w) :
      (Obligation msg fml : Pred w) ⊣⊢ instprop fml.
    Proof. crushPredEntails3.
           - now destruct H0. 
           - now constructor.
    Qed.

    Lemma safe_assume_triangular {w0 w1} (ζ : Tri w0 w1) (o : 𝕊 w1) :
      (psafe (assume_triangular ζ o) ⊣⊢ (assuming (acc_triangular ζ) (psafe o))).
    Proof.
      induction ζ; first by rewrite assuming_refl.
      rewrite assuming_trans.
      cbn.
      now rewrite IHζ.
    Qed.

    Lemma safe_assume_pathcondition_without_solver {w0 : World}
        (C : PathCondition w0) (p : 𝕊 w0) :
      psafe (assume_pathcondition_without_solver C p) ⊣⊢
        ((instprop C : Pred w0) -∗ psafe (w := wpathcondition w0 C) p).
    Proof.
      revert p. induction C; cbn; intros p.
      - change (λ _ : Valuation w0, True%type) with (True%I : Pred w0).
        destruct w0. (* needed to make coq see that wpathcondition w0 [ctx] is the same as w0 *)
        iSplit.
        + now iIntros "$ _".
        + iIntros "H". now iApply "H".
      - rewrite IHC.
        change (λ ι : Valuation w0, (instprop C ι /\ instprop b ι)) with ((instprop C : Pred w0) ∗ instprop b)%I.
        now rewrite <-bi.wand_curry.
    Qed.

    (* TODO: more logical inst_triangular *)
    Lemma safe_assert_triangular {w0 w1} msg (ζ : Tri w0 w1)
      (o : AMessage w1 -> 𝕊 w1) :
      (psafe (assert_triangular msg ζ o) ⊣⊢
         (knowing (acc_triangular ζ) (psafe (o (subst msg (sub_triangular ζ)))))).
    Proof.
      revert o. induction ζ; intros o.
      - now rewrite knowing_refl subst_sub_id.
      - cbn [psafe assert_triangular acc_triangular].
        rewrite obligation_equiv.
        rewrite knowing_trans.
        rewrite subst_sub_comp.
        rewrite (IHζ (subst msg (sub_single xIn t)) o).
        now rewrite knowing_acc_subst_right.
    Qed.

    Lemma safe_assert_pathcondition_without_solver {w0 : World}
        (msg : AMessage w0) (C : PathCondition w0) (p : 𝕊 w0) :
      psafe (assert_pathcondition_without_solver msg C p) ⊣⊢
        ((instprop C : Pred w0) ∗ psafe (w := wpathcondition w0 C) p).
    Proof.
      unfold assert_pathcondition_without_solver. revert p.
      induction C; cbn; intros p.
      - rewrite bi.True_sep.
        now destruct w0.
      - rewrite IHC; cbn.
        change (λ ι : Valuation _, (instprop C ι ∧ instprop b ι)%type) with ((instprop C : Pred _) ∧ instprop b)%I.
        rewrite <-sep_is_and, <-bi.sep_assoc.
        change (@bi_sep (@bi_pred (wpathcondition w0 C)) ?P ?Q) with (@sepₚ w0 P Q).
        now rewrite obligation_equiv.
    Qed.

      Lemma refine_assert_pathcondition {w} :
        ⊢ ℛ⟦RMsg _ (RPathCondition -> RPureSpec RUnit)⟧
          CPureSpec.assert_formula (SPureSpec.assert_pathcondition (w := w)).
      Proof.
        unfold SPureSpec.assert_pathcondition, CPureSpec.assert_formula, CPureSpec.assert_pathcondition.
        iIntros (msg cC sC) "HC %cΦ %sΦ rΦ HΦ".
        destruct (SolverSpec_old_to_logical combined_solver_spec w sC) as [[w1 [ζ sc1]] Hsolver|Hsolver].
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
            cbn.
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
        CPureSpec.assume_formula (SPureSpec.assume_pathcondition (w := w)).
    Proof.
      unfold SPureSpec.assume_pathcondition, CPureSpec.assume_formula, CPureSpec.assume_pathcondition.
      iIntros "%C %Cs HC %Φ %Φs HΦ Hsp %HC".
      destruct (SolverSpec_old_to_logical combined_solver_spec _ Cs) as [[w1 [ζ sc1]] Hsolver|Hsolver].
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
        cbn.
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
      cbn. intuition.
    Qed.

    Lemma refine_assume_formula {w} :
      ⊢ ℛ⟦RFormula -> RPureSpec RUnit⟧
        CPureSpec.assume_formula (SPureSpec.assume_formula (w := w)).
    Proof.
      unfold RPureSpec, SPureSpec.assume_formula, CPureSpec.assume_formula.
      iIntros "%fml %fmls Hfml".
      iApply refine_assume_pathcondition.
      iApply (proprepₚ_cong (T2 := PathCondition) with "Hfml").
      cbn. intuition.
    Qed.

    Lemma refine_angelic_binary `{RA : Rel SA CA} {w} :
      ⊢ ℛ⟦RPureSpec RA -> RPureSpec RA -> RPureSpec RA⟧
        CPureSpec.angelic_binary (SPureSpec.angelic_binary (w := w)).
    Proof.
      iIntros (c1 cs1) "Hc1 %c2 %cs2 Hc2 %k %ks Hk [HSP | HSP]".
      - iLeft. iApply ("Hc1" with "Hk HSP").
      - iRight. iApply ("Hc2" with "Hk HSP").
    Qed.

    Lemma refine_demonic_binary `{RA : Rel SA CA} {w} :
      ⊢ ℛ⟦RPureSpec RA -> RPureSpec RA -> RPureSpec RA⟧
        CPureSpec.demonic_binary (SPureSpec.demonic_binary (w := w)).
    Proof.
      iIntros (c1 cs1) "Hc1 %c2 %cs2 Hc2 %k %ks #Hk [HSP1 HSP2]".
      iSplitL "Hc1 HSP1".
      - iApply ("Hc1" with "Hk HSP1").
      - iApply ("Hc2" with "Hk HSP2").
    Qed.

    Lemma refine_angelic_list' `{RA : Rel SA CA} {w} :
      ⊢ ℛ⟦RA -> RList RA -> RPureSpec RA⟧
        CPureSpec.angelic_list' (SPureSpec.angelic_list' (w := w)).
    Proof.
      iIntros "%v %sv Hv %vs %svs Hvs".
      iRevert (v sv) "Hv".
      iApply (RList_ind (R := RA) (MkRel (fun vs w svs => ∀ (v : CA) (sv : SA w), ℛ⟦RA⟧ v sv -∗ ℛ⟦RPureSpec RA⟧ (CPureSpec.angelic_list' v vs) (SPureSpec.angelic_list' (w := w) sv svs))%I) w with "[] Hvs").
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
      iApply (RList_ind (R := RA) (MkRel (fun vs w svs => ∀ msg, ℛ⟦RPureSpec RA⟧ (CPureSpec.angelic_list vs) (SPureSpec.angelic_list (w := w) msg svs))%I) w with "[] Hvs").
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
      iApply (RList_ind (R := RA) (MkRel (fun vs w svs => ∀ (v : CA) (sv : SA w), ℛ⟦RA⟧ v sv -∗ ℛ⟦RPureSpec RA⟧ (CPureSpec.demonic_list' v vs) (SPureSpec.demonic_list' (w := w) sv svs))%I) w with "[] Hvs").
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
      iApply (RList_ind (R := RA) (MkRel (fun vs w svs => ℛ⟦RPureSpec RA⟧ (CPureSpec.demonic_list vs) (SPureSpec.demonic_list (w := w) svs))%I) w with "[] Hvs").
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
      unfold CPureSpec.angelic_finite, SPureSpec.angelic_finite.
      iApply (refine_demonic_list (RA := RConst F)).
      iStopProof.
      crushPredEntails3.
      induction (finite.enum F); now constructor.
    Qed.

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
      - iApply (refine_pure (RA := RUnit)).
        now iApply refine_unit.
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
      - iApply (refine_pure (RA := RUnit)).
        now iApply refine_unit.
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
            subst; cbn.
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
              cbn.
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
          + iIntros (p args sargs) "Hargs %msg %c1 %sc1 %c2 %sc2 Hc1 IHc1 Hc2 IHc2 %w1 %ω1".
            iModIntro.
            iApply (refine_error (RA := RUnit)).
          + iIntros (σ r v sv) "Hv %msg %c1 %sc1 %c2 %sc2 Hc1 IHc1 Hc2 IHc2 %w1 %ω1".
            iModIntro.
            iApply (refine_error (RA := RUnit)).
          + iIntros (c3 sc3 c4 sc4) "Hc3 Hc4 %msg %c1 %sc1 %c2 %sc2 Hc1 IHc1 Hc2 IHc2 %w1 %ω1".
            iModIntro.
            iApply (refine_bind (RA := RUnit) (RB := RUnit) with "[Hc1 IHc1 Hc3] [Hc2 IHc2 Hc4]").
            * unfold RSat at 2; cbn -[RSat].
              iSpecialize ("IHc1" with "Hc3").
              now rewrite forgetting_unconditionally_drastic.
            * iIntros (w2 ω2) "!> %u %su _".
              iSpecialize ("IHc2" with "Hc4").
              now rewrite forgetting_unconditionally_drastic.
          + iIntros (c3 sc3 c4 sc4) "Hc3 Hc4 %msg %c1 %sc1 %c2 %sc2 Hc1 IHc1 Hc2 IHc2 %w1 %ω1".
            iModIntro.
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
            * unfold RSat at 2; cbn -[RSat].
              iSpecialize ("IHc1" with "Hc3").
              now rewrite forgetting_unconditionally_drastic.
            * iIntros (w2 ω2) "!> %u %su _".
              unfold RSat at 2; cbn -[RSat].
              iSpecialize ("IHc2" with "Hc4").
              now rewrite forgetting_unconditionally_drastic.
    Qed.

    Lemma refine_replay_aux {Σ} (s : 𝕊 Σ) {w} :
      ⊢ ℛ⟦RBox (RInst (Sub Σ) (Valuation Σ) -> RPureSpec RUnit)⟧
        (CPureSpec.replay_aux s) (fun w' (ω : Acc w w') => SPureSpec.replay_aux (w := w') s).
    Proof.
      iInduction s as [] "IH"; iIntros (w' ω) "!> %ι %ιs #Hι";
        cbn -[RSat].
      - iApply (refine_angelic_binary (RA := RUnit)).
        + now iApply (forgetting_unconditionally_drastic with "IH").
        + now iApply (forgetting_unconditionally_drastic with "IH1").
      - iApply (refine_demonic_binary (RA := RUnit)).
        + now iApply (forgetting_unconditionally_drastic with "IH").
        + now iApply (forgetting_unconditionally_drastic with "IH1").
      - now iApply (refine_error (RA := RUnit)).
      - now iApply (refine_block (R := RUnit)).
      - iApply (refine_bind (RA := RUnit) (RB := RUnit)).
        + iApply refine_assert_formula.
          now iApply refine_instprop_subst.
        + iIntros (w1 ω1) "!> %u %us _".
          iApply (forgetting_unconditionally_drastic with "IH").
          now iApply (refine_inst_persist (AT := Sub _)).
      - iApply (refine_bind (RA := RUnit) (RB := RUnit)).
        + iApply refine_assume_formula.
          now iApply refine_instprop_subst.
        + iIntros (w1 ω1) "!> %u %us _".
          iApply (forgetting_unconditionally_drastic with "IH").
          now iApply (refine_inst_persist (AT := Sub _)).
      - iApply (refine_bind (RA := RInst (STerm (type b)) (Val _)) (RB := RUnit)).
        + iApply refine_angelic.
        + iIntros (w1 ω1) "!> %v %vs Hv".
          iApply (forgetting_unconditionally_drastic with "IH").
          iApply (repₚ_cong₂ (T1 := Sub Σ) (T2 := STerm (type b)) (T3 := Sub (Σ ▻ b)) (fun vs v => env.snoc vs b v) (fun vs v => env.snoc vs b v) with "[Hι $Hv]").
          { intros; now cbn. }
          now rewrite forgetting_repₚ.
      - iApply (refine_bind (RA := RInst (STerm (type b)) (Val _)) (RB := RUnit)).
        + iApply refine_demonic.
        + rewrite forgetting_unconditionally.
          iIntros (w1 ω1) "!> %v %vs Hv".
          iApply (forgetting_unconditionally_drastic with "IH").
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
        + rewrite forgetting_unconditionally.
          iIntros (w1 ω1) "!> %u %us _".
          iApply (forgetting_unconditionally_drastic with "IH").
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
        + rewrite forgetting_unconditionally.
          iIntros (w1 ω1) "!> %u %us _".
          iApply (forgetting_unconditionally_drastic with "IH").
          iApply (repₚ_cong (T1 := Sub Σ) (T2 := Sub (Σ - (x∷σ))) (fun vs => env.remove (x∷σ) vs xIn) (fun vs => env.remove (x∷σ) vs xIn) with "[Hι]").
          { intros. now rewrite <- inst_sub_shift, <- inst_subst, sub_comp_shift. }
          now rewrite forgetting_repₚ.
      - iApply (refine_error (RA := RUnit)).
      - iApply (refine_error (RA := RUnit)).
      - iApply (refine_debug (RA := RUnit)).
        now iApply (forgetting_unconditionally_drastic with "IH").
    Qed.

    Lemma refine_replay_aux2 {Σ} (s : 𝕊 Σ) {w} :
      ⊢ ℛ⟦RInst (Sub Σ) (Valuation Σ) -> RPureSpec RUnit⟧
        (CPureSpec.replay_aux s) (SPureSpec.replay_aux (w := w) s).
    Proof.
      iPoseProof (refine_replay_aux s) as "Hreplay".
      iSpecialize ("Hreplay" $! w acc_refl).
      now rewrite assuming_refl.
    Qed.

    Lemma refine_replay {w : World} (s : 𝕊 w) ι (Hpc : instprop (wco w) ι) :
      (ℛ⟦ RProp ⟧ (CPureSpec.replay s ι) (SPureSpec.replay s)) ι.
    Proof.
      eapply refine_run; try done.
      eapply (refine_replay_aux2 s); try done.
      cbn. now apply refine_rinst_sub_initial.
    Qed.

    Lemma refine_peval_chunk {w} :
      ⊢ ℛ⟦RChunk -> RChunk⟧ id (peval_chunk : Impl _ _ w).
    Proof.
      crushPredEntails3.
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
      crushPredEntails3; subst.
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
        { clear -HIn. crushPredEntails3. now subst. }
        iDestruct (eval_prop eqs) as "(%eq & Heq)".
        iAssert (∃ h', ℛ⟦RHeap⟧ h' sh')%I as "(%h' & Hh')".
        { iDestruct (eval sh') as "(%h' & Heqh')".
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
          cbn.
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
        { clear -HIn. crushPredEntails3. now subst. }
        iDestruct (eval_prop eqs) as "(%eq & Heq)".
        iAssert (∃ h', ℛ⟦RHeap⟧ h' sh')%I as "(%h' & Hh')".
        { iDestruct (eval sh') as "(%h' & Heqh')".
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
          cbn.
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
        now iApply forgetting_repₚ. 
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
        iDestruct (eval (AT := STerm τ) st) as "(%v & Hv)".
        iDestruct (eval (AT := SHeap) sh') as "(%h' & Hh')".
        iExists v.
        rewrite CPureSpec.wp_angelic_list.
        iExists (scchunk_ptsreg reg v, h').
        iSplitR.
        + rewrite RList_RInst.
          iStopProof. crushPredEntails3. now subst. 
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
        iDestruct (eval (AT := STerm τ) st) as "(%v' & Hv')".
        iDestruct (eval (AT := SHeap) sh') as "(%h' & Hh')".
        iExists v'.
        rewrite CPureSpec.wp_angelic_list.
        iExists (scchunk_ptsreg reg v', h').
        iSplitR.
        + rewrite RList_RInst.
          iStopProof. crushPredEntails3. now subst.
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

  End Monads.
  End PureSpec.
    
  Module HeapSpec.
    Section WithNotations.
      Import logicalrelation.
      Import ufl_notations.
      Import PureSpec.

      #[export] Instance RHeapSpec [SA CA] (RA : Rel SA CA) :
      Rel (SHeapSpec SA) (CHeapSpec CA) := □ᵣ(RA -> RHeap -> ℙ) -> RHeap -> ℙ.

      Lemma refine_run {w} :
        ⊢ ℛ⟦RHeapSpec RUnit -> ℙ⟧ CHeapSpec.run (SHeapSpec.run (w := w)).
      Proof. iIntros (m sm) "Hm".
             iApply "Hm".
             - iIntros (w2 ω2) "!> %u %su _ %h %sh Hh _".
               now iPureIntro.
             - now iApply (refine_nil (R := RChunk)).
      Qed.

    Lemma refine_lift_purespec `{RA : Rel SA CA} {w} :
      ⊢ ℛ⟦RPureSpec RA -> RHeapSpec RA⟧
        CHeapSpec.lift_purespec (SHeapSpec.lift_purespec (w := w)).
    Proof.
      unfold RPureSpec, RHeapSpec.
      unfold SHeapSpec.lift_purespec, CHeapSpec.lift_purespec.
      iIntros (m sm) "Hm %K %sK HK %h %sh Hh".
      iApply "Hm".
      iIntros (w1 ω1) "!> %a %sa Ha".
      rewrite forgetting_unconditionally_drastic.
      iApply ("HK" with "Ha").
      rewrite !RList_RInst.
      now iApply (refine_inst_persist).
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
      rewrite forgetting_unconditionally_drastic.
      iApply ("rf" with "ra [rΦ] rh1").
      now iApply refine_four.
    Qed.

    Lemma refine_angelic x {w} :
      ⊢ ℛ⟦∀ᵣ σ, RHeapSpec (RVal σ)⟧
        (CHeapSpec.angelic) (SHeapSpec.angelic (w := w) x).
    Proof.
      iIntros (σ).
      iApply (refine_lift_purespec (RA := RVal _)).
      iApply (PureSpec.refine_angelic).
    Qed.

    Lemma refine_demonic x {w} :
      ⊢ ℛ⟦∀ᵣ σ, RHeapSpec (RVal σ)⟧
        (CHeapSpec.demonic) (SHeapSpec.demonic (w := w) x).
    Proof.
      iIntros (σ).
      iApply (refine_lift_purespec (RA := RVal _)).
      iApply PureSpec.refine_demonic.
    Qed.

    Lemma refine_angelic_binary `{RA : Rel SA CA} {w} :
      ⊢ ℛ⟦RHeapSpec RA -> RHeapSpec RA -> RHeapSpec RA⟧
        CHeapSpec.angelic_binary (SHeapSpec.angelic_binary (w := w)).
    Proof.
      iIntros (cm1 sm1) "rm1 %cm2 %sm2 rm2 %cΦ %sΦ #rΦ %ch %sh rh HSP".
      iDestruct "HSP" as "[HSP|HSP]"; [iLeft|iRight].
      - now iApply ("rm1" with "rΦ rh HSP").
      - now iApply ("rm2" with "rΦ rh HSP").
    Qed.

    Lemma refine_demonic_binary `{RA : Rel SA CA} {w} :
      ⊢ ℛ⟦RHeapSpec RA -> RHeapSpec RA -> RHeapSpec RA⟧
        CHeapSpec.demonic_binary (SHeapSpec.demonic_binary (w := w)).
    Proof.
      iIntros (cm1 sm1) "rm1 %cm2 %sm2 rm2 %cΦ %sΦ #rΦ %ch %sh #rh HSP".
      iDestruct "HSP" as "[HSP1 HSP2]"; iSplitL "HSP1 rm1".
      - now iApply ("rm1" with "rΦ rh HSP1").
      - now iApply ("rm2" with "rΦ rh HSP2").
    Qed.

    Lemma refine_debug `{RA : Rel SA CA} {w} :
      ⊢ ℛ⟦RMsg _ (RHeapSpec RA -> RHeapSpec RA)⟧
        CHeapSpec.debug (SHeapSpec.debug (w := w)).
    Proof.
      iIntros (msg cm sm) "rm %cΦ %sΦ rΦ %ch %sh rh HΦ".
      iDestruct (elim_debugPred with "HΦ") as "HΦ".
      now iApply ("rm" with "rΦ rh HΦ").
    Qed.

    Lemma refine_assert_formula {w} :
      ⊢ ℛ⟦RMsg _ (RFormula -> RHeapSpec RUnit)⟧
        CHeapSpec.assert_formula (SHeapSpec.assert_formula (w := w)).
    Proof.
      iIntros (msg cF sF) "rF %cΦ %sΦ rΦ %ch %sh rh".
      iApply (PureSpec.refine_assert_formula with "rF").
      iIntros (w1 θ1) "!> %cu %su ru".
      rewrite forgetting_unconditionally_drastic.
      iApply ("rΦ" with "ru").
      rewrite !RList_RInst.
      now iApply refine_inst_persist.
    Qed.

    Lemma refine_assume_formula {w} :
      ⊢ ℛ⟦RFormula -> RHeapSpec RUnit⟧
        CHeapSpec.assume_formula (SHeapSpec.assume_formula (w := w)).
    Proof.
      iIntros (cF sF) "rF".
      iApply (refine_lift_purespec (RA := RUnit)).
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
      rewrite forgetting_unconditionally_drastic.
      iApply "rΦ".
      now iApply refine_unit.
    Qed.

    Lemma refine_consume_chunk {w} :
      ⊢ ℛ⟦RChunk -> RHeapSpec RUnit⟧
        CHeapSpec.consume_chunk (SHeapSpec.consume_chunk (w := w)).
    Proof.
      iIntros (cc sc) "rc %cΦ %sΦ rΦ %ch %sh rh".
      unfold SHeapSpec.consume_chunk, CHeapSpec.consume_chunk.
      iApply (PureSpec.refine_consume_chunk with "rc rh").
      iIntros (w1 θ1) "!>".
      rewrite forgetting_unconditionally_drastic.
      iApply "rΦ".
      now iApply refine_unit.
    Qed.

    Lemma refine_consume_chunk_angelic {w} :
      ⊢ ℛ⟦RChunk -> RHeapSpec RUnit⟧
        CHeapSpec.consume_chunk (SHeapSpec.consume_chunk_angelic (w := w)).
    Proof.
      iIntros (cc sc) "rc %cΦ %sΦ rΦ %ch %sh rh".
      unfold SHeapSpec.consume_chunk_angelic, CHeapSpec.consume_chunk.
      iApply (PureSpec.refine_consume_chunk_angelic with "rc rh").
      iIntros (w1 θ1) "!>".
      rewrite forgetting_unconditionally_drastic.
      iApply "rΦ".
      now iApply refine_unit.
    Qed.

    Lemma refine_produce {Σ} (asn : Assertion Σ) {w} :
      ⊢ ℛ⟦ □ᵣ (RInst (Sub Σ) (Valuation Σ) -> RHeapSpec RUnit)⟧
        (CHeapSpec.produce asn) (fun w' (ω : Acc w w') => SHeapSpec.produce (w := w') asn).
    Proof.
      iInduction asn as [*|*|*|*|*|*|*|*] "IHasn"; iIntros (w2 ω2) "!> %cδ %sδ #rδ"; cbn - [RSat].
      - iApply refine_assume_formula.
        now iApply refine_instprop_subst.
      - iApply refine_produce_chunk.
        now iApply (refine_inst_subst (T := Chunk)).
      - iApply refine_produce_chunk.
        now iApply (refine_inst_subst (T := Chunk)).
      - iApply (refine_bind (RA := RMatchResult pat) (RB := RUnit)).
        iApply (refine_lift_purespec (RA := RMatchResult pat)).
        admit.
        iIntros (w1 θ1) "!> %mr %smr Hmr".
        destruct mr as [pc sub].
        destruct smr as [spc ssub].
        iDestruct "Hmr" as "(%e & Hmr)"; subst; cbn -[RSat].
        iDestruct (refine_inst_persist with "rδ") as "rδp".
        iSpecialize ("IHasn" $! pc).
        rewrite forgetting_unconditionally.
        rewrite forgetting_unconditionally_drastic.
        iApply "IHasn".
        iApply (repₚ_cong₂ (T1 := Sub _) (T2 := Sub _) (T3 := Sub (Σ ▻▻ PatternCaseCtx pc)) env.cat env.cat with "[$rδp $Hmr]").
        intros. now rewrite inst_env_cat.
      - iApply (refine_bind (RA := RUnit) (RB := RUnit)).
        + rewrite forgetting_unconditionally_drastic.
          now iApply "IHasn".
        + iIntros (w1 θ1) "!> %u %su _".
          rewrite forgetting_unconditionally forgetting_unconditionally_drastic.
          rewrite forgetting_unconditionally forgetting_unconditionally_drastic.
          iApply "IHasn1".
          iApply (refine_inst_persist with "rδ").
      - iApply (refine_demonic_binary (RA := RUnit)).
        + rewrite forgetting_unconditionally_drastic.
          now iApply "IHasn".
        + rewrite !forgetting_unconditionally_drastic.
          now iApply "IHasn1".
      - iApply (refine_bind (RA := RVal τ) (RB := RUnit)).
        + iApply refine_demonic.
        + iIntros (w3 ω3) "!> %v %sv Hv".
          rewrite forgetting_unconditionally forgetting_unconditionally_drastic.
          iApply "IHasn".
          iDestruct (refine_inst_persist with "rδ") as "rδp".
          iApply (repₚ_cong₂ (T1 := Sub _) (T2 := STerm _) (T3 := Sub (Σ ▻ ς∷τ)) (fun δ => env.snoc δ (ς∷τ)) (fun δ => env.snoc δ (ς∷τ)) with "[$rδp $Hv]").
          now intros.
      - iApply (refine_debug (RA := RUnit)).
        iApply (refine_pure (RA := RUnit)).
        iApply refine_unit.
    Admitted.

    Lemma refine_consume {Σ} (asn : Assertion Σ) {w} :
      ⊢ ℛ⟦□ᵣ (RInst (Sub Σ) (Valuation Σ) -> RHeapSpec RUnit)⟧
        (CHeapSpec.consume asn) (fun w' (ω : Acc w w') => SHeapSpec.consume (w := w') asn).
    Proof.
      iInduction asn as [*|*|*|*|*|*|*|*] "IHasn"; iIntros (w2 ω2) "!> %cδ %sδ #rδ"; cbn - [RSat].
      - iApply refine_assert_formula.
        now iApply refine_instprop_subst.
      - iApply refine_consume_chunk.
        now iApply (refine_inst_subst (T := Chunk)).
      - iApply refine_consume_chunk_angelic.
        now iApply (refine_inst_subst (T := Chunk)).
      - iApply (refine_bind (RA := RMatchResult pat) (RB := RUnit)).
        iApply (refine_lift_purespec (RA := RMatchResult pat)).
        admit.
        iIntros (w1 θ1) "!> %mr %smr Hmr".
        destruct mr as [pc sub].
        destruct smr as [spc ssub].
        iDestruct "Hmr" as "(%e & Hmr)"; subst; cbn -[RSat].
        iDestruct (refine_inst_persist with "rδ") as "rδp".
        iSpecialize ("IHasn" $! pc).
        rewrite forgetting_unconditionally.
        rewrite forgetting_unconditionally_drastic.
        iApply "IHasn".
        iApply (repₚ_cong₂ (T1 := Sub _) (T2 := Sub _) (T3 := Sub (Σ ▻▻ PatternCaseCtx pc)) env.cat env.cat with "[$rδp $Hmr]").
        intros. now rewrite inst_env_cat.
      - iApply (refine_bind (RA := RUnit) (RB := RUnit)).
        + rewrite forgetting_unconditionally_drastic.
          now iApply "IHasn".
        + iIntros (w1 θ1) "!> %u %su _".
          rewrite forgetting_unconditionally forgetting_unconditionally_drastic.
          rewrite forgetting_unconditionally forgetting_unconditionally_drastic.
          iApply "IHasn1".
          iApply (refine_inst_persist with "rδ").
      - iApply (refine_angelic_binary (RA := RUnit)).
        + rewrite forgetting_unconditionally_drastic.
          now iApply "IHasn".
        + rewrite !forgetting_unconditionally_drastic.
          now iApply "IHasn1".
      - iApply (refine_bind (RA := RVal τ) (RB := RUnit)).
        + iApply refine_angelic.
        + iIntros (w3 ω3) "!> %v %sv Hv".
          rewrite forgetting_unconditionally forgetting_unconditionally_drastic.
          iApply "IHasn".
          iDestruct (refine_inst_persist with "rδ") as "rδp".
          iApply (repₚ_cong₂ (T1 := Sub _) (T2 := STerm _) (T3 := Sub (Σ ▻ ς∷τ)) (fun δ => env.snoc δ (ς∷τ)) (fun δ => env.snoc δ (ς∷τ)) with "[$rδp $Hv]").
          now intros.
      - iApply (refine_debug (RA := RUnit)).
        iApply (refine_pure (RA := RUnit)).
        iApply refine_unit.
    Admitted.

    Lemma refine_read_register {τ} (reg : 𝑹𝑬𝑮 τ) {w} :
      ⊢ ℛ⟦RHeapSpec (RVal τ)⟧ (CHeapSpec.read_register reg) (SHeapSpec.read_register reg (w := w)).
    Proof.
      iIntros (Φ sΦ) "rΦ %ch %sh rh".
      iApply (PureSpec.refine_read_register with "rh").
      iIntros (w1 θ1) "!> %vh %svh  Hvh".
      destruct vh as [v h2].
      destruct svh as [sv sh2].
      iDestruct "Hvh" as "[Hv Hh2]".
      rewrite forgetting_unconditionally_drastic.
      now iApply ("rΦ" with "Hv").
    Qed.

    Lemma refine_write_register {τ} (reg : 𝑹𝑬𝑮 τ) {w} :
      ⊢ ℛ⟦RVal τ -> RHeapSpec (RVal τ)⟧ (CHeapSpec.write_register reg) (SHeapSpec.write_register reg (w := w)).
    Proof.
      iIntros (v sv) "rv %Φ %sΦ rΦ %h %sh rh".
      iApply (PureSpec.refine_write_register with "rv rh").
      iIntros (w1 θ1) "!> %vh %svh Hvh".
      destruct vh as [v2 h2].
      destruct svh as [sv2 sh2].
      iDestruct "Hvh" as "[Hv2 Hh2]".
      rewrite forgetting_unconditionally_drastic.
      now iApply ("rΦ" with "Hv2").
    Qed.
    End WithNotations.
  End HeapSpec.

  Module StoreSpec.
    Section Basics.

    Import logicalrelation.
    Import ufl_notations.
    Import PureSpec.
    Import HeapSpec.

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
      - now iApply (refine_inst_persist s).
      - rewrite !RList_RInst.
        now iApply refine_inst_persist.
    Qed.

    Lemma refine_block_store {Γ1 Γ2} `{R : Rel AT A} {w : World} :
      ⊢ ℛ⟦RStoreSpec Γ1 Γ2 R⟧ CStoreSpec.block (SStoreSpec.block (w := w)).
    Proof.
      iIntros (k ks) "Hk".
      iIntros (s ss) "Hs".
      iIntros (h hs) "Hh _".
      now iPureIntro.
    Qed.

    Lemma refine_error `{Subst M, OccursCheck M, R : Rel AT A} {Γ1 Γ2} {w : World} :
      forall (cm : CStoreSpec Γ1 Γ2 A),
        ⊢ ℛ⟦RMsg _ (RStoreSpec Γ1 Γ2 R)⟧ cm (SStoreSpec.error (w := w)).
    Proof.
      iIntros (cm msg k ks) "Hk".
      iIntros (s ss) "Hs".
      iIntros (h hs) "Hh []".
    Qed.

    Lemma refine_pure `{R : Rel AT A} {Γ} {w : World} :
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

    Lemma refine_bind `{RA : Rel AT A, RB : Rel BT B} {Γ1 Γ2 Γ3} {w : World} :
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

    Lemma refine_angelic (x : option LVar) {Γ} {w : World} :
      ⊢ ℛ⟦∀ᵣ σ, RStoreSpec Γ Γ (RVal σ)⟧ CStoreSpec.angelic (SStoreSpec.angelic (w := w) x).
    Proof.
      unfold SStoreSpec.angelic, CStoreSpec.angelic.
      iIntros (σ).
      iApply (refine_lift_purem (RVal σ)).
      now iApply PureSpec.refine_angelic.
    Qed.

    Lemma refine_demonic (x : option LVar) {Γ} {w : World} :
      ⊢ ℛ⟦∀ᵣ σ, RStoreSpec Γ Γ (RVal σ)⟧ CStoreSpec.demonic (SStoreSpec.demonic (w := w) x).
    Proof.
      unfold SStoreSpec.angelic, CStoreSpec.angelic.
      iIntros (σ).
      iApply (refine_lift_purem (RVal σ)).
      now iApply PureSpec.refine_demonic.
    Qed.

    Lemma refine_angelic_ctx {N : Set} {n : N -> LVar} {Γ} {w} :
      ⊢ ℛ⟦∀ᵣ Δ, RStoreSpec Γ Γ (RNEnv N Δ)⟧
        CStoreSpec.angelic_ctx (SStoreSpec.angelic_ctx (w := w) n).
    Proof.
      unfold SStoreSpec.angelic_ctx, CStoreSpec.angelic_ctx.
      iIntros (Δ).
      iApply (refine_lift_purem (RNEnv N Δ)).
      iApply refine_angelic_ctx.
    Qed.

    Lemma refine_demonic_ctx {N : Set} {n : N -> LVar} {Γ} {w} :
      ⊢ ℛ⟦∀ᵣ Δ, RStoreSpec Γ Γ (RNEnv N Δ)⟧
        CStoreSpec.demonic_ctx (SStoreSpec.demonic_ctx (w := w) n).
    Proof.
      unfold SStoreSpec.demonic_ctx, CStoreSpec.demonic_ctx.
      iIntros (Δ).
      iApply (refine_lift_purem (RNEnv N Δ)).
      iApply refine_demonic_ctx.
    Qed.

    Lemma refine_debug {AT A} `{R : Rel AT A}
      {Γ1 Γ2} {w0 : World} :
      ⊢ ∀ f ms mc, ℛ⟦RStoreSpec Γ1 Γ2 R⟧ mc ms →
                   ℛ⟦RStoreSpec Γ1 Γ2 R⟧ mc (@SStoreSpec.debug AT Γ1 Γ2 w0 f ms).
    Proof.
      iIntros (f ms mc) "Hm %K %Ks HK %s %ss Hs %h %hs Hh HSP".
      iApply ("Hm" with "HK Hs Hh [HSP]").
      now iApply elim_debugPred.
    Qed.

    Lemma refine_angelic_binary {AT A} `{R : Rel AT A} {Γ1 Γ2} {w} :
      ⊢ ℛ⟦RStoreSpec Γ1 Γ2 R -> RStoreSpec Γ1 Γ2 R -> RStoreSpec Γ1 Γ2 R⟧
        CStoreSpec.angelic_binary (SStoreSpec.angelic_binary (w := w)).
    Proof.
      iIntros (c1 cs1) "Hc1 %c2 %cs2 Hc2 %K %Ks #HK %s %ss #Hs %h %hs #Hh".
      unfold SStoreSpec.angelic_binary, CStoreSpec.angelic_binary.
      iApply (refine_symprop_angelic_binary with "[Hc1] [Hc2]").
      - now iApply "Hc1".
      - now iApply "Hc2".
    Qed.

    Lemma refine_demonic_binary {AT A} `{R : Rel AT A} {Γ1 Γ2} {w} :
      ⊢ ℛ⟦RStoreSpec Γ1 Γ2 R -> RStoreSpec Γ1 Γ2 R -> RStoreSpec Γ1 Γ2 R⟧
        CStoreSpec.demonic_binary (SStoreSpec.demonic_binary (w := w)).
    Proof.
      iIntros (c1 cs1) "Hc1 %c2 %cs2 Hc2 %K %Ks #HK %s %ss #Hs %h %hs #Hh".
      unfold SStoreSpec.angelic_binary, CStoreSpec.angelic_binary.
      iApply (refine_symprop_demonic_binary with "[Hc1] [Hc2]").
      - now iApply "Hc1".
      - now iApply "Hc2".
    Qed.

  End Basics.

  Section AssumeAssert.
    Import logicalrelation.
    Import ufl_notations.
    
    Lemma refine_assume_formula {Γ} {w} :
      ⊢ ℛ⟦RFormula -> RStoreSpec Γ Γ RUnit⟧
        CStoreSpec.assume_formula (SStoreSpec.assume_formula (w := w)).
    Proof.
      unfold SStoreSpec.assume_formula, CStoreSpec.assume_formula.
      iIntros (fml fmls) "Hfml %K %Ks HK %s %ss Hs %h %hs Hh".
      iApply (refine_lift_purem with "[Hfml] HK Hs Hh").
      iApply (PureSpec.refine_assume_formula with "Hfml").
    Qed.

    Lemma refine_assert_formula {Γ} {w} :
      ⊢ ℛ⟦RFormula -> RStoreSpec Γ Γ RUnit⟧
        CStoreSpec.assert_formula (SStoreSpec.assert_formula (w := w)).
    Proof.
      unfold SStoreSpec.assert_formula, CStoreSpec.assert_formula.
      iIntros (fml fmls) "Hfml %K %Ks HK %s %ss Hs %h %hs Hh".
      iApply (refine_lift_purem with "[Hfml] HK Hs Hh").
      iApply (PureSpec.refine_assert_formula with "Hfml").
    Qed.

    Lemma refine_assert_pathcondition {Γ} {w} :
      ⊢ ℛ⟦RPathCondition -> RStoreSpec Γ Γ RUnit⟧
        CStoreSpec.assert_formula (SStoreSpec.assert_pathcondition (w := w)).
    Proof.
      iIntros (pc pcs) "Hpc %K %Ks HK %δ %δs Hδ %h %hs Hh".
      iApply (refine_lift_purem with "[Hpc] HK Hδ Hh").
      now iApply PureSpec.refine_assert_pathcondition.
    Qed.

    Lemma refine_assert_eq_nenv {N Γ} (Δ : NCtx N Ty) {w} :
      ⊢ ℛ⟦RNEnv N Δ -> RNEnv N Δ -> RStoreSpec Γ Γ RUnit⟧
        CStoreSpec.assert_eq_nenv (SStoreSpec.assert_eq_nenv (w := w)).
    Proof.
      iIntros (E1 sE1) "HE1 %E2 %sE2 HE2 %K %sK HK %δ %sδ Hδ %h %sh Hh".
      iApply (refine_lift_purem RUnit $! _ _ with "[HE1 HE2] HK Hδ Hh").
      now iApply (PureSpec.refine_assert_eq_nenv with "HE1 HE2").
    Qed.

  End AssumeAssert.

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

  Section State.
    Import logicalrelation.
    Lemma refine_pushpop `{R : Rel AT A} {Γ1 Γ2 x σ} {w} :
      ⊢ ℛ⟦RVal σ -> RStoreSpec (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) R -> RStoreSpec Γ1 Γ2 R⟧
        CStoreSpec.pushpop (SStoreSpec.pushpop (w := w)).
    Proof.
      iIntros (v sv) "Hv %m %sm Hm %K %sK HK %δ %sδ Hδ %h %sh Hh".
      unfold SStoreSpec.pushpop, CStoreSpec.pushpop.
      iApply ("Hm" with "[HK] [Hδ Hv] Hh").
      - clear.
        iIntros (w2 ω2) "!> %v %sv Hv %δ %sδ Hδ".
        iApply (forgetting_unconditionally_drastic with "HK Hv").
        iApply (repₚ_cong (T1 := SStore (Γ2 ▻ x∷σ)) (T2 := SStore Γ2) env.tail env.tail with "Hδ").
        intros. now env.destroy vs1.
      - iApply (repₚ_cong₂ (T1 := SStore Γ1) (T2 := STerm σ) (T3 := SStore (Γ1 ▻ x∷σ)) (fun δ v => δ.[x∷σ ↦ v]) (w := w) (fun δ v => δ.[x∷σ ↦ v]) with "[$Hδ $Hv]").
        now intros.
    Qed.

    Lemma refine_pushspops `{R : Rel AT A} {Γ1 Γ2 Δ} {w} :
      ⊢ ℛ⟦RStore Δ -> RStoreSpec (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) R -> RStoreSpec Γ1 Γ2 R⟧
        CStoreSpec.pushspops (SStoreSpec.pushspops (w := w)).
    Proof.
      iIntros (c sc) "Hc %m %sm Hm %K %sK HK %δ %sδ Hδ %h %sh Hh".
      unfold SStoreSpec.pushspops, CStoreSpec.pushspops.
      iApply ("Hm" with "[HK] [Hδ Hc] Hh").
      - iIntros (w1 ω1) "!> %v %sv Hv %δ1 %sδ1 Hδ1 %h1 %sh1 Hh1".
        iApply (forgetting_unconditionally_drastic with "HK Hv [Hδ1] Hh1").
        iApply (repₚ_cong (T1 := SStore (Γ2 ▻▻ Δ)) (T2 := SStore Γ2) (env.drop Δ) (env.drop Δ) with "Hδ1").
        intros. env.destroy vs1.
        now rewrite inst_env_cat !env.drop_cat.
      - iApply (repₚ_cong₂ (T1 := SStore Γ1) (T2 := SStore Δ) (T3 := SStore (Γ1 ▻▻ Δ)) env.cat env.cat with "[$Hδ $Hc]").
        intros; now rewrite inst_env_cat.
    Qed.

    Lemma refine_get_local {Γ} {w} :
      ⊢ ℛ⟦RStoreSpec Γ Γ (RStore Γ)⟧ CStoreSpec.get_local (SStoreSpec.get_local (w := w)).
    Proof.
      iIntros (K sK) "HK %δ %sδ #Hδ %h %sh Hh".
      unfold SStoreSpec.get_local, CStoreSpec.get_local.
      now iApply (refine_T with "HK Hδ Hδ Hh").
    Qed.

    Lemma refine_put_local {Γ1 Γ2} {w} :
      ⊢ ℛ⟦RStore Γ2 -> RStoreSpec Γ1 Γ2 RUnit⟧
        CStoreSpec.put_local (SStoreSpec.put_local (w := w)).
    Proof.
      iIntros (δ2 sδ2) "Hδ2 %K %sK HK %δ %sδ Hδ %h %sh Hh".
      unfold SStoreSpec.put_local, CStoreSpec.put_local.
      iApply (refine_T with "HK [] Hδ2 Hh").
      now iApply refine_unit.
    Qed.

    Lemma refine_peval {w : World} {σ} (t : STerm σ w) v :
      ℛ⟦RVal σ⟧ v t ⊢ ℛ⟦RVal σ⟧ v (peval t).
    Proof. crushPredEntails3. now rewrite peval_sound. Qed.

    Lemma refine_seval_exp {Γ σ} (e : Exp Γ σ) {w : World} {δ} {sδ : SStore Γ w} :
      ℛ⟦ RStore Γ ⟧ δ sδ ⊢ ℛ⟦RVal σ⟧ (B.eval e δ) (seval_exp sδ e).
    Proof.
      crushPredEntails3.
      rewrite <-eval_exp_inst.
      now subst.
    Qed.

    Lemma refine_seval_exps {Γ Δ : PCtx} {es : NamedEnv (Exp Γ) Δ} {w : World} {δ : CStore Γ} {sδ : SStore Γ w} :
      ℛ⟦RStore Γ⟧ δ sδ ⊢ ℛ⟦RStore Δ⟧ (evals es δ) (seval_exps sδ es).
    Proof.
      crushPredEntails3.
      unfold seval_exps, inst, inst_store, inst_env, evals.
      rewrite env.map_map.
      apply env.map_ext.
      intros.
      rewrite peval_sound.
      now apply refine_seval_exp.
    Qed.
       
    Lemma refine_eval_exp {Γ σ} (e : Exp Γ σ) {w} :
        ⊢ ℛ⟦RStoreSpec Γ Γ (RVal σ)⟧ (CStoreSpec.eval_exp e) (SStoreSpec.eval_exp (w := w) e).
    Proof.
      iIntros (K sK) "HK %δ0 %sδ0 #Hδ0 %h0 %sh0 Hh0".
      unfold SStoreSpec.eval_exp, CStoreSpec.eval_exp.
      iApply (refine_T with "HK [Hδ0] Hδ0 Hh0").
      iApply refine_peval.
      now iApply refine_seval_exp.
    Qed.

    Lemma refine_eval_exps {Γ Δ} (es : NamedEnv (Exp Γ) Δ) {w} :
      ⊢ ℛ⟦RStoreSpec Γ Γ (RStore Δ)⟧
        (CStoreSpec.eval_exps es) (SStoreSpec.eval_exps (w := w) es).
    Proof.
      iIntros (K sK) "HK %δ0 %sδ0 #Hδ0 %h0 %sh0 Hh0".
      unfold SStoreSpec.eval_exps, CStoreSpec.eval_exps.
      iApply (refine_T with "HK [Hδ0] Hδ0 Hh0").
      now iApply refine_seval_exps.
    Qed.

    Lemma refine_env_update {Γ x σ} (xIn : (x∷σ ∈ Γ)%katamaran) (w : World)
      (t : Term w σ) (v : Val σ) (δs : SStore Γ w) (δc : CStore Γ) :
      ℛ⟦RVal σ⟧ v t ∗ ℛ⟦RStore Γ⟧ δc δs ⊢ ℛ⟦RStore Γ⟧ (δc ⟪ x ↦ v ⟫) (δs ⟪ x ↦ t ⟫).
    Proof.
      crushPredEntails3; subst.
      unfold inst, inst_store, inst_env.
      now rewrite env.map_update.
    Qed.

    Lemma refine_assign {Γ x σ} {xIn : (x∷σ ∈ Γ)%katamaran} {w} :
      ⊢ ℛ⟦RVal σ -> RStoreSpec Γ Γ RUnit⟧
        (CStoreSpec.assign x) (SStoreSpec.assign (w := w) x).
    Proof.
      iIntros (v sv) "Hv %K %sK HK %δ %sδ Hδ %h %sh Hh".
      unfold SStoreSpec.assign, CStoreSpec.assign.
      iApply (refine_T with "HK [] [Hv Hδ] Hh").
      { iApply refine_unit. }
      now iApply (refine_env_update with "[$Hv $Hδ]").
    Qed.

  End State.

  (* Local Hint Unfold RSat : core. *)
  (* Local Hint Unfold RInst : core. *)

  Import logicalrelation.
  Import ufl_notations.

  Lemma refine_produce_chunk {Γ} {w} :
    ⊢ ℛ⟦RChunk -> RStoreSpec Γ Γ RUnit⟧
      CStoreSpec.produce_chunk (SStoreSpec.produce_chunk (w := w)).
  Proof.
    iIntros (c sc) "Hc %Φ %sΦ HΦ %δ %sδ Hδ %h %sh Hh".
    iApply (PureSpec.refine_produce_chunk with "Hc Hh [HΦ Hδ]").
    iIntros (w2 ω2) "!> %h2 %sh2 Hh2".
    iApply (forgetting_unconditionally_drastic with "HΦ [] [Hδ] Hh2").
    - now iApply refine_unit.
    - now iApply (refine_inst_persist (AT := SStore Γ)).
  Qed.

  Lemma refine_consume_chunk {Γ} {w} :
    ⊢ ℛ⟦RChunk -> RStoreSpec Γ Γ RUnit⟧
      CStoreSpec.consume_chunk (SStoreSpec.consume_chunk (w := w)).
  Proof.
    iIntros (c sc) "Hc %Φ %sΦ HΦ %δ %sδ Hδ %h %sh Hh".
    iApply (PureSpec.refine_consume_chunk with "Hc Hh").
    iIntros (w2 ω2) "!> %h2 %sh2 Hh2".
    iApply (forgetting_unconditionally_drastic with "HΦ [] [Hδ] Hh2").
    - now iApply refine_unit.
    - now iApply (refine_inst_persist (AT := SStore Γ)).
  Qed.

  Lemma refine_consume_chunk_angelic {Γ} {w} :
    ⊢ ℛ⟦RChunk -> RStoreSpec Γ Γ RUnit⟧
      CStoreSpec.consume_chunk (SStoreSpec.consume_chunk_angelic (w := w)).
  Proof.
    iIntros (c sc) "Hc %Φ %sΦ HΦ %δ %sδ Hδ %h %sh Hh".
    iApply (PureSpec.refine_consume_chunk_angelic with "Hc Hh").
    iIntros (w2 ω2) "!> %h2 %sh2 Hh2".
    iApply (forgetting_unconditionally_drastic with "HΦ [] [Hδ] Hh2").
    - now iApply refine_unit.
    - now iApply (refine_inst_persist with "Hδ").
  Qed.

  Lemma refine_produce {Γ} {w : World} (asn : Assertion w) {ι : Valuation w} :
    curval ι ⊢ ℛ⟦□ᵣ(RStoreSpec Γ Γ RUnit)⟧ (CStoreSpec.produce ι asn) (@SStoreSpec.produce Γ w asn).
  Proof.
    unfold SStoreSpec.produce, CStoreSpec.produce.
    iIntros "Hι %w2 %ω2 !> %K %sK HK %δ %sδ Hδ".
    iPoseProof (HeapSpec.refine_produce asn) as "Hprod".
    iApply (refine_T with "Hprod [Hι]").
    { now iApply forgetting_curval. }
    iIntros (w3 ω3) "!> %u %su _".
    iApply (forgetting_unconditionally_drastic with "HK [] [Hδ]").
    - now iApply refine_unit.
    - now iApply (refine_inst_persist with "Hδ").
  Qed.

  Lemma refine_consume {Γ} {w : World} (asn : Assertion w) {ι}:
    curval ι ⊢ ℛ⟦□ᵣ(RStoreSpec Γ Γ RUnit)⟧ (CStoreSpec.consume ι asn) (SStoreSpec.consume (w := w) asn).
  Proof.
    unfold SStoreSpec.consume, CStoreSpec.consume.
    iIntros "Hι %w2 %ω2 !> %Φ %sΦ rΦ %δ %sδ rδ".
    iPoseProof (HeapSpec.refine_consume asn) as "Hcons".
    iApply (refine_T with "Hcons [Hι]").
    { now iApply forgetting_curval. }
    iIntros (w3 ω3) "!> %u %su _".
    iApply (forgetting_unconditionally_drastic with "rΦ [] [rδ]").
    - now iApply refine_unit.
    - now iApply (refine_inst_persist with "rδ").
  Qed.

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

  End StoreSpec.

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
