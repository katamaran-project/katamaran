From MicroSail Require Import
     Notation
     Syntax
     Environment
     Context
     SmallStep.Step
     SmallStep.Inversion
     .

Require Import Coq.Program.Equality.

From Equations Require Import Equations Signature.

From iris.bi Require Export interface.
From iris.algebra Require Export gmap excl auth.
From iris.base_logic Require Export lib.fancy_updates.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import tactics.

Require Import MicroSail.Sep.Spec.
Require Import MicroSail.Sep.Hoare.
(* can't import: overlapping notations *)
Require MicroSail.Sep.Logic.
Module logic := MicroSail.Sep.Logic.

Set Implicit Arguments.

Module ValsAndTerms
       (Import typekit : TypeKit)
       (Import termkit : TermKit typekit)
       (Import progkit : ProgramKit typekit termkit).

  Inductive Tm (Γ : Ctx (𝑿 * Ty)) τ : Type :=
  | MkTm (δ : LocalStore Γ) (s : Stm Γ τ) : Tm Γ τ.

  (* remainng obligations? *)
  (* Derive NoConfusion for Tm. *)

  Inductive Val (Γ : Ctx (𝑿 * Ty)) τ : Type :=
    (* we only keep the store around for technical reasons, essentially to be able to prove of_to_val. *)
  | MkVal (δ : LocalStore Γ) (v : Lit τ) : Val Γ τ.

  Definition val_to_lit {Γ} {τ} : Val Γ τ -> Lit τ := fun v => match v with | MkVal _ _ v' => v' end.

  Definition of_val {Γ} {τ} (v : Val Γ τ) : Tm Γ τ :=
    match v with
      MkVal _ δ v => MkTm δ (stm_lit _ v)
    end.

  Definition to_val {Γ} {τ} (t : Tm Γ τ) : option (Val Γ τ) :=
    (* easier way to do the dependent pattern match here? *)
    match t with
    | MkTm δ s => match s with
                   stm_lit τ l => Some (MkVal _ δ l)
                 | _ => None
                 end
    end.

  Lemma to_of_val {Γ} {τ} (v : Val Γ τ) : to_val (of_val v) = Some v.
  Proof.
    by induction v.
  Qed.

  Lemma of_to_val {Γ} {τ} (e : Tm Γ τ) v : to_val e = Some v → of_val v = e.
  Proof.
    induction e.
    induction s; try done.
    by intros [= <-].
  Qed.

  Module Inv := Inversion typekit termkit progkit.
  Export Inv.
  Export SS.

  Lemma val_head_stuck_step {τ} {Γ : Ctx (𝑿 * Ty)} γ1 γ2 μ1 μ2 (δ1 : LocalStore Γ) δ2 (s1 : Stm Γ τ) s2 :
    Step γ1 γ2 μ1 μ2 δ1 δ2 s1 s2 -> to_val (MkTm δ1 s1) = None.
    by induction 1.
  Qed.
End ValsAndTerms.

Module IrisInstance
       (Import typekit : TypeKit)
       (Import termkit : TermKit typekit)
       (Import progkit : ProgramKit typekit termkit)
       (Import assertkit : AssertionKit typekit termkit progkit)
       (Import contractkit : SymbolicContractKit typekit termkit progkit assertkit)
       (Import heapkit : logic.HeapKit typekit termkit progkit assertkit contractkit).


  Import CtxNotations.
  Import EnvNotations.

  Module VT := ValsAndTerms typekit termkit progkit.
  Import VT.

  Module PL := ProgramLogic typekit termkit progkit assertkit contractkit heapkit.
  Import PL.

  Definition Val := VT.Val.
  Definition Tm := VT.Tm.

  Definition observation := Empty_set.

  Definition State := prod RegStore Memory.

  Inductive prim_step {Γ τ} : Tm Γ τ -> State -> Tm Γ τ -> State -> list (VT.Tm Γ τ) -> Prop :=
  | mk_prim_step γ1 γ2 μ1 μ2 (δ1 : LocalStore Γ) (δ2 : LocalStore Γ) s1 s2 :
      SS.Step γ1 γ2 μ1 μ2 δ1 δ2 s1 s2 ->
      prim_step (VT.MkTm δ1 s1) (γ1 , μ1) (VT.MkTm δ2 s2) (γ2 , μ2) nil
  .

  Lemma val_head_stuck {Γ τ} (e1 : Tm Γ τ) s1 e2 s2 {ks} : prim_step e1 s1 e2 s2 ks → VT.to_val e1 = None.
  Proof.
    induction 1.
    by eapply VT.val_head_stuck_step.
  Qed.

  Lemma microsail_lang_mixin Γ τ : @LanguageMixin (VT.Tm Γ τ) (VT.Val Γ τ) State Empty_set VT.of_val VT.to_val (fun e1 s1 ls e2 s2 ks => prim_step e1 s1 e2 s2 ks).
  Proof.
    split.
    - eauto using VT.to_of_val, VT.of_to_val, val_head_stuck.
    - eauto using VT.to_of_val, VT.of_to_val, val_head_stuck.
    - eauto using VT.to_of_val, VT.of_to_val, val_head_stuck.
  Qed.

  Canonical Structure stateO := leibnizO State.
  Canonical Structure valO {Γ τ} := leibnizO (Val Γ τ).
  Canonical Structure exprO {Γ τ} := leibnizO (Tm Γ τ).

  Canonical Structure microsail_lang Γ τ : language := Language (microsail_lang_mixin Γ τ).

  Instance intoVal_lit {Γ τ} : IntoVal (VT.MkTm (Γ := Γ) (τ := τ) δ (stm_lit _ l)) (VT.MkVal _ δ l).
  intros; eapply VT.of_to_val; by cbn.
  Defined.

  Inductive SomeReg : Type :=
  | mkSomeReg {τ} : 𝑹𝑬𝑮 τ -> SomeReg
  .
  Inductive SomeLit : Type :=
  | mkSomeLit {τ} : Lit τ -> SomeLit
  .

  Section TransparentObligations.
    Local Set Transparent Obligations.
    Derive NoConfusion for SomeReg.
    Derive NoConfusion for SomeLit.
    Derive NoConfusion for excl.
  End TransparentObligations.

  Instance eqDec_SomeReg : EqDecision SomeReg.
  Proof.
    - intros [τ1 r1] [τ2 r2].
      destruct (𝑹𝑬𝑮_eq_dec r1 r2).
      + left.
        dependent elimination t.
        dependent elimination eqi.
        now f_equal.
      + right.
        intros Heq.
        dependent elimination Heq.
        apply n.
        constructor 1 with eq_refl.
        reflexivity.
  Qed.

  Instance countable_SomeReg : Countable SomeReg.
  Admitted.

  Instance eqDec_SomeLit : EqDecision SomeLit.
  Proof.
    intros [τ1 v1] [τ2 v2].
    destruct (Ty_eq_dec τ1 τ2).
    - subst.
      destruct (Lit_eqb_spec _ v1 v2).
      + left. congruence.
      + right. intros H.
        Local Set Equations With UIP.
        dependent elimination H.
        congruence.
    - right. intros H.
      dependent elimination H.
      congruence.
  Qed.

  Definition regUR := authR (gmapUR SomeReg (exclR (leibnizO SomeLit))).

  Class sailG Σ := SailG { (* resources for the implementation side *)
                       sailG_invG : invG Σ; (* for fancy updates, invariants... *)

                       (* ghost variable for tracking state of registers *)
                       reg_inG : inG Σ regUR;
                       reg_gv_name : gname;

                       (* ghost variable for tracking state of memory cells *)
                       mem_inG : inG Σ regUR;
                       mem_gv_name : gname
                     }.

  Definition reg_pointsTo `{sailG Σ} {τ} (r : 𝑹𝑬𝑮 τ) (v : Lit τ) : iProp Σ :=
    own (i := reg_inG) reg_gv_name (◯ {[ mkSomeReg r := Excl (mkSomeLit v) ]}).

  Definition regs_inv `{sailG Σ} (regstore : RegStore) : iProp Σ :=
    (∃ regsmap,
        own (i := reg_inG) reg_gv_name (● regsmap) ∗
        bi_pure (map_Forall (fun reg v => match reg with | mkSomeReg reg => Excl (mkSomeLit (read_register regstore reg)) = v end ) regsmap)
        (* sigh why can't I use ⌈ ... ⌉ notation? *)
    )%I.

  Instance sailG_irisG {Γ τ} `{sailG Σ} : irisG (microsail_lang Γ τ) Σ := {
    iris_invG := sailG_invG;
    state_interp σ κs _ := regs_inv σ.1;
    fork_post _ := True%I; (* no threads forked in sail, so this is fine *)
                                                   }.
  Global Opaque iris_invG.

  Context `{sailG Σ}.

  Instance iris_ILogic : logic.ILogic (iProp Σ) :=
  { land := bi_and;
    lor  := bi_or;
    (* existential quantification *)
    lex := fun _ => bi_exist;
    (* universal quantification *)
    lall := fun _ => bi_forall;
    limpl := bi_impl;

    (* Prop embedding *)
    lprop := bi_pure;
    (* P ⊢ Q *)
    lentails := bi_entails;

    ltrue := True%I;
    lfalse := False%I
  }.

  Program Instance iProp_ILogicLaws : @logic.ILogicLaws (iProp Σ) iris_ILogic.
  Next Obligation.
    iIntros; iFrame.
  Qed.
  Next Obligation.
    eapply (PreOrder_Transitive (R := bi_entails)); eauto.
  Qed.
  Next Obligation.
    iIntros. iPureIntro; auto.
  Qed.
  Next Obligation.
    iIntros (P f).
    destruct f.
  Qed.
  Next Obligation.
    iIntros (X P Q XP XQ).
    apply bi.and_intro; auto.
  Qed.
  Next Obligation.
    iIntros (P Q R PR) "PQ".
    iApply PR.
    iApply bi.and_elim_l.
    iFrame.
  Qed.
  Next Obligation.
    iIntros (P Q R QR) "PQ".
    iApply QR.
    iApply bi.and_elim_r.
    iFrame.
  Qed.
  Next Obligation.
    iIntros (P Q R PR QR) "PQ".
    iApply bi.or_elim.
    - iApply PR.
    - iApply QR.
    - iFrame.
  Qed.
  Next Obligation.
    iIntros (P Q R PQ) "P".
    iApply bi.or_intro_l.
    iApply PQ; iFrame.
  Qed.
  Next Obligation.
    iIntros (P Q R PR) "P".
    iApply bi.or_intro_r.
    iApply PR; iFrame.
  Qed.
  Next Obligation.
    iIntros (B x P Q PQ) "P".
    iExists x.
    iApply (PQ with "P").
  Qed.
  Next Obligation.
    iIntros (B P Q M).
    apply bi.exist_elim.
    iIntros (a) "Pa".
    iApply (M a); iFrame.
  Qed.
  Next Obligation.
    iIntros (B P x Q PxQ) "AP".
    iApply PxQ.
    iApply bi.forall_elim; iFrame.
  Qed.
  Next Obligation.
    iIntros (B P Q APQ).
    apply bi.forall_intro; auto.
  Qed.
  Next Obligation.
    intros P Q R.
    split.
    - apply bi.impl_intro_r.
    - apply bi.impl_elim_l'.
  Qed.
  Next Obligation.
    iIntros (P Q PTQ) "%".
    by iApply PTQ.
  Qed.
  Next Obligation.
    iIntros (P Q p) "Q".
    by iPureIntro.
  Qed.

  Program Instance iris_ISepLogic : logic.ISepLogic (iProp Σ) :=
  { logic.emp := emp%I;
    logic.sepcon P Q := (P ∗ Q)%I;
    logic.wand P Q := (P -∗ Q)%I
  }.

  Program Instance iProp_ISepLogicLaws : @logic.ISepLogicLaws (iProp Σ) iris_ISepLogic.
  Next Obligation.
    intros P Q R. split.
    - eapply bi.sep_assoc'.
    - cbn. rewrite bi.sep_assoc.
      iIntros "PQR"; iAssumption.
  Qed.
  Next Obligation.
    intros P Q. split; eapply bi.sep_comm'.
  Qed.
  Next Obligation.
    intros P Q R. split.
    - eapply bi.wand_intro_r.
    - eapply bi.wand_elim_l'.
  Qed.
  Next Obligation.
    intros P R Q. split.
    - iIntros "[P [% R]]".
      iSplit.
      + by iPureIntro.
      + iFrame.
    - iIntros "[% [P R]]".
      iSplitL "P"; iFrame.
      by iPureIntro.
  Qed.
  Next Obligation.
    iIntros (P P' Q Q' PP QQ) "[P Q]".
    iSplitL "P".
    - by iApply PP.
    - by iApply QQ.
  Qed.

  Instance iris_IHeapLet : IHeaplet (iProp Σ) :=
    { is_ISepLogic := iris_ISepLogic;
      (* TODO: should be user-defined... *)
      pred p ts := False%I;
      ptsreg σ r t := reg_pointsTo r t
    }.

  Lemma reg_valid regstore {τ} (r : 𝑹𝑬𝑮 τ) (v : Lit τ) :
    ⊢ (regs_inv regstore -∗ reg_pointsTo r v -∗ ⌜read_register regstore r = v⌝)%I.
  Proof.
    iDestruct 1 as (regsmap) "[Hregs %]".
    iIntros "Hreg".
    rewrite /reg_pointsTo.
    iDestruct (own_valid_2 with "Hregs Hreg") as %[Hl regsv]%auth_both_valid.
    iPureIntro.
    rewrite (singleton_included_l regsmap (mkSomeReg r) _) in Hl *.
    destruct 1 as [y [eq1%leibniz_equiv eq2]].
    specialize (regsv (mkSomeReg r)).
    rewrite eq1 in regsv.
    destruct y as [y|]; [|inversion regsv].
    rewrite Excl_included in eq2 *.
    intros <-%leibniz_equiv.
    specialize (H0 (mkSomeReg r) (Excl (mkSomeLit v)) eq1); cbn in H0.
    by dependent destruction H0.
  Qed.

  Lemma regs_inv_update {τ} {r} {v : Lit τ} {regsmap : gmapUR SomeReg (exclR (leibnizO SomeLit))} {regstore : RegStore} :
    map_Forall (λ r' v', match r' with
                         | @mkSomeReg τ r'' => Excl (mkSomeLit (read_register regstore r'')) = v'
                         end) regsmap ->
    (own (i := reg_inG) reg_gv_name (● <[mkSomeReg r:=Excl (mkSomeLit v)]> regsmap)) -∗ regs_inv (write_register regstore r v).
  Proof.
    iIntros (regseq) "Hownregs".
    rewrite /regs_inv.
    iExists (<[mkSomeReg r:=Excl (mkSomeLit v)]> regsmap).
    iFrame.
    iPureIntro.
    apply (map_Forall_lookup_2 _ (<[mkSomeReg r:=Excl (mkSomeLit v)]> regsmap)).
    intros [τ' r'] x eq1.
    destruct (𝑹𝑬𝑮_eq_dec r r') as [eq2|neq].
    + dependent destruction eq2.
      destruct eqi, eqf; cbn in *.
      rewrite (lookup_insert regsmap (mkSomeReg r) (Excl (mkSomeLit v))) in eq1.
      apply (inj Some) in eq1.
      by rewrite <- eq1, (read_write regstore r v).
    + assert (mkSomeReg r ≠ mkSomeReg r') as neq2.
      * intros eq2.
        dependent destruction eq2.
        destruct (neq (teq_refl r' eq_refl eq_refl)).
      * rewrite (lookup_insert_ne _ _ _ _ neq2) in eq1.
        rewrite (read_write_distinct _ neq).
        apply (map_Forall_lookup_1 _ _ _ _ regseq eq1).
  Qed.

  Lemma reg_update regstore {τ} r (v1 v2 : Lit τ) :
    regs_inv regstore -∗ reg_pointsTo r v1 ==∗ regs_inv (write_register regstore r v2) ∗ reg_pointsTo r v2.
  Proof.
    iDestruct 1 as (regsmap) "[Hregs %]".
    rewrite /reg_pointsTo.
    iIntros "Hreg".
    iDestruct (own_valid_2 with "Hregs Hreg") as %[Hl regsmapv]%auth_both_valid.
    rewrite (singleton_included_l regsmap (mkSomeReg r) _) in Hl *.
    destruct 1 as [y [eq1%leibniz_equiv eq2]].
    specialize (regsmapv (mkSomeReg r)).
    rewrite eq1 in regsmapv.
    destruct y as [y|]; inversion regsmapv.
    iMod (own_update_2 with "Hregs Hreg") as "[Hregs Hreg]".
    {
      eapply auth_update.
      apply (singleton_local_update regsmap (mkSomeReg r) (Excl y) (Excl (mkSomeLit v1)) (Excl (mkSomeLit v2)) (Excl (mkSomeLit v2)) eq1).
      by eapply exclusive_local_update.
    }
    iModIntro.
    iFrame.
    iApply (regs_inv_update H0); iFrame.
  Qed.

  Lemma rule_stm_read_register {Γ τ} (r : 𝑹𝑬𝑮 τ) (v : Lit τ) {δ : LocalStore Γ} :
    ⊢ (reg_pointsTo r v -∗
                    WP (VT.MkTm δ (stm_read_register r)) {{ w, reg_pointsTo r v ∗ bi_pure (VT.val_to_lit w = v) }}
      )%I.
  Proof.
    iIntros "Hreg".
    iApply (wp_mask_mono _ empty); auto.
    rewrite wp_unfold; cbn.
    iIntros (σ _ _ n) "Hregs".
    iDestruct (@reg_valid with "Hregs Hreg") as %<-.
    iModIntro.
    iSplit.
    - iPureIntro.
      destruct σ as [regs heap].
      exists nil. repeat eexists.
      apply step_stm_read_register.
    - iIntros (e2 σ2 efs) "%".
      remember (VT.MkTm δ (stm_read_register r)) as t.
      destruct a as [γ1 γ2 σ1 σ2 δ1 δ2 s1 s2 step].
      dependent destruction Heqt.
      destruct (steps_inversion_read_register step) as [<- [<- [<- ->]]].
      iModIntro. iModIntro. iModIntro.
      iFrame. iSplitR ""; auto.
      by iApply wp_value.
  Qed.

  Lemma rule_stm_write_register {Γ} {τ} (r : 𝑹𝑬𝑮 τ) (δ : LocalStore Γ) (v1 v2 : Lit τ) :
    ⊢ (reg_pointsTo r v1 -∗
                  WP (VT.MkTm δ (stm_write_register r (exp_lit _ _ v2)) : expr (microsail_lang Γ τ)) {{ w, reg_pointsTo r v2 ∗ bi_pure (v2 = VT.val_to_lit w) }}
    )%I.
  Proof.
    iIntros "Hreg".
    iApply (wp_mask_mono _ empty); auto.
    rewrite wp_unfold; cbn.
    iIntros (σ _ _ n) "Hregs".
    iMod (reg_update σ.1 r v1 v2 with "Hregs Hreg") as "[Hregs Hreg]".
    iModIntro.
    iSplitR.
    - iPureIntro.
      destruct σ as [regs heap].
      exists nil. repeat eexists.
      apply step_stm_write_register.
    - iIntros (e2 σ2 efs) "%".
      dependent destruction a.
      destruct (steps_inversion_write_register H0) as [-> [<- [<- ->]]].
      iModIntro. iModIntro. iModIntro.
      iFrame. iSplitR; auto.
      by iApply wp_value.
  Qed.

  Definition semTriple {Γ τ} (δ : LocalStore Γ)
             (PRE : iProp Σ) (s : Stm Γ τ) (POST : Lit τ -> LocalStore Γ -> iProp Σ) :=
    ⊢ PRE -∗ WP (MkTm δ s : expr (microsail_lang Γ τ)) {{ v, match v with MkVal _ δ' v => POST v δ' end }}.
  (* always modality needed? perhaps not because sail not higher-order? *)

  Lemma sound {Γ} {τ} (s : Stm Γ τ) {δ : LocalStore Γ}:
    forall (PRE : iProp Σ) (POST : Lit τ -> LocalStore Γ -> iProp Σ)
      (triple : δ ⊢ ⦃ PRE ⦄ s ⦃ POST ⦄),
      semTriple δ PRE s POST.
  Proof.
    intros PRE POST triple.
    induction triple.
    - iIntros "P".
      cbn in H0, H1.
      iApply (wp_mono _ _ _ (fun v => match v with MkVal _ δ' v => Q' v δ' end)).
      + intros [δ' v]; cbn.
        apply H1.
      + iApply IHtriple.
        iApply H0; iFrame.
    - 

End IrisInstance.
