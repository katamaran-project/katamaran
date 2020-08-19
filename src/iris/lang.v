From MicroSail Require Import
     Notation
     Syntax
     Environment
     Context
     SmallStep.Step
     SmallStep.Inversion
     SmallStep.Progress
     .

Require Import Coq.Program.Equality.

From Equations Require Import Equations Signature.

From iris.bi Require Import interface.
From iris.algebra Require Import gmap excl auth.
From iris.base_logic Require Import lib.fancy_updates.
From iris.program_logic Require Import weakestpre hoare.
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

  Module Prog := Progress typekit termkit progkit.

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
                    WP (VT.MkTm δ (stm_read_register r)) ?{{ w, reg_pointsTo r v ∗ bi_pure (w = VT.MkVal _ δ v) }}
      )%I.
  Proof.
    iIntros "Hreg".
    iApply (wp_mask_mono _ empty); auto.
    rewrite wp_unfold; cbn.
    iIntros (σ _ _ n) "Hregs".
    iDestruct (@reg_valid with "Hregs Hreg") as %<-.
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 σ2 efs) "%".
    remember (VT.MkTm δ (stm_read_register r)) as t.
    destruct a as [γ1 γ2 σ1 σ2 δ1 δ2 s1 s2 step].
    dependent destruction Heqt.
    destruct (steps_inversion_read_register step) as [<- [<- [<- ->]]].
    iModIntro. iModIntro. iModIntro.
    iFrame. iSplitR ""; auto.
    by iApply wp_value.
  Qed.

  Lemma rule_stm_write_register {Γ} {τ} (r : 𝑹𝑬𝑮 τ) (δ : LocalStore Γ) (v : Lit τ) e :
    ⊢ (reg_pointsTo r v -∗
                    WP (VT.MkTm δ (stm_write_register r e) : expr (microsail_lang Γ τ)) ?{{ w, reg_pointsTo r (eval e δ) ∗ bi_pure (w = VT.MkVal _ δ (eval e δ)) }}
    )%I.
  Proof.
    iIntros "Hreg".
    iApply (wp_mask_mono _ empty); auto.
    rewrite wp_unfold; cbn.
    iIntros (σ _ _ n) "Hregs".
    iMod (reg_update σ.1 r v (eval e δ) with "Hregs Hreg") as "[Hregs Hreg]".
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 σ2 efs) "%".
    dependent destruction a.
    destruct (steps_inversion_write_register H0) as [-> [<- [<- ->]]].
    iModIntro. iModIntro. iModIntro.
    iFrame. iSplitR; auto.
    by iApply wp_value.
  Qed.

  Definition semTriple {Γ τ} (δ : LocalStore Γ)
             (PRE : iProp Σ) (s : Stm Γ τ) (POST : Lit τ -> LocalStore Γ -> iProp Σ) :=
    ⊢ PRE -∗ WP (MkTm δ s : expr (microsail_lang Γ τ)) ?{{ v, match v with MkVal _ δ' v => POST v δ' end }}.
  (* always modality needed? perhaps not because sail not higher-order? *)

  Lemma iris_rule_consequence {Γ σ} {δ : LocalStore Γ}
        {P P'} {Q Q' : Lit σ -> LocalStore Γ -> iProp Σ} {s : Stm Γ σ} :
        (P ⊢ P') -> (forall v δ', Q' v δ' ⊢ Q v δ') -> semTriple δ P' s Q' -> semTriple δ P s Q.
  Proof.
    iIntros (PP QQ trip) "P".
    iApply (wp_mono _ _ _ (fun v => match v with MkVal _ δ' v => Q' v δ' end)).
    + intros [δ' v]; cbn.
      apply QQ.
    + iApply trip.
      iApply PP; iFrame.
  Qed.

  Lemma iris_rule_frame {Γ σ} {δ : LocalStore Γ}
        (R P : iProp Σ) (Q : Lit σ -> LocalStore Γ -> iProp Σ) (s : Stm Γ σ) :
        semTriple δ P s Q -> semTriple δ (R ∗ P) s (fun v δ' => R ∗ Q v δ')%I.
  Proof.
    iIntros (trip) "[HR HP]".
    iApply (wp_mono _ _ _ (fun v => R ∗ match v with MkVal _ δ' v => Q v δ' end)%I).
    - iIntros (v) "[R Q]".
      destruct v.
      by iFrame.
    - iApply (wp_frame_l _ _ (MkTm δ s) (fun v => match v with MkVal _ δ' v => Q v δ' end) R).
      iFrame.
      by iApply trip.
  Qed.

  Lemma iris_rule_pull {σ Γ} (δ : LocalStore Γ) (s : Stm Γ σ)
        (P : iProp Σ) (Q : Prop) (R : Lit σ -> LocalStore Γ -> iProp Σ) :
        (Q -> semTriple δ P s R) ->
        semTriple δ (P ∧ bi_pure Q)%I s R.
  Proof.
    iIntros (QP) "[P %]".
    by iApply QP.
  Qed.

  Lemma iris_rule_exist {σ Γ} (δ : LocalStore Γ)
        (s : Stm Γ σ) {A : Type} {P : A -> iProp Σ}
        {Q :  Lit σ -> LocalStore Γ -> iProp Σ} :
        (forall x, semTriple δ (P x) s Q) ->
        semTriple δ (∃ x, P x) s Q.
  Proof.
    iIntros (Atrip) "Px".
    iDestruct "Px" as (x) "Px".
    by iApply Atrip.
  Qed.

  (* following rule is dubious, re discussion about conjunction rule *)
  Lemma iris_rule_forall {σ Γ} (δ : LocalStore Γ)
        {s : Stm Γ σ} {A : Type} {P : iProp Σ}
        {Q : A -> Lit σ -> LocalStore Γ -> iProp Σ}
        (hyp : forall x, semTriple δ P s (Q x)) (x : A) :
        semTriple δ P s (fun v δ' => ∀ x, Q x v δ')%I.
  Proof.
  Admitted.

  Lemma iris_rule_stm_lit {Γ} (δ : LocalStore Γ)
        {τ : Ty} {l : Lit τ}
        {P : iProp Σ} {Q : Lit τ -> LocalStore Γ -> iProp Σ} :
        (P ⊢ Q l δ)%I ->
        semTriple δ P (stm_lit τ l) Q.
  Proof.
    iIntros (PQ) "P".
    iApply wp_value.
    by iApply PQ.
  Qed.

  Lemma iris_rule_stm_exp {Γ} (δ : LocalStore Γ)
        {τ : Ty} {e : Exp Γ τ}
        {P : iProp Σ} {Q : Lit τ -> LocalStore Γ -> iProp Σ} :
        (P ⊢ Q (eval e δ) δ)%I ->
        semTriple δ P (stm_exp e) Q.
  Proof.
    iIntros (PQ) "P".
    iApply (wp_mask_mono _ empty); auto.
    rewrite wp_unfold.
    iIntros ([regs μ] ks1 ks n) "Hregs".
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 σ2 efs) "%".
    remember (MkTm δ (stm_exp e)) as t.
    destruct a.
    inversion Heqt.
    dependent destruction H0; inversion H3.
    iModIntro. iModIntro. iModIntro.
    rewrite H2.
    dependent destruction H1.
    iFrame.
    iSplitL; trivial.
    iApply (wp_value _ _ (fun v => match v with | MkVal _ δ' v' => Q v' δ' end) (MkTm δ (stm_lit σ (eval e δ)))).
    by iApply PQ.
  Qed.

  Lemma wp_compat_fail {Γ τ} {s} {δ} {Q : Val Γ τ -> iProp Σ} :
    (⊢ WP (MkTm δ (stm_fail _ s)) ?{{ v, Q v }})%I.
  Proof.
    rewrite wp_unfold.
    iIntros (σ ks1 ks n) "Hregs".
    iMod (fupd_intro_mask' _ empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 σ2 efs) "%".
    remember (MkTm δ (fail s)) as s1.
    destruct a.
    inversion Heqs1.
    destruct H0; inversion H3.
  Qed.


  Lemma wp_compat_block {Γ Δ} {τ : Ty} {δ : LocalStore Γ}
        (δΔ : LocalStore Δ) (k : Stm (Γ ▻▻ Δ) τ) (Q : Val Γ τ -> iProp Σ) :
    ⊢ (WP (MkTm (δ ►► δΔ) k) ?{{ v, match v with MkVal _ δ' v => Q (MkVal _ (env_drop Δ δ') v) end }} -∗
          WP (MkTm δ (stm_block δΔ k)) ?{{ v, Q v }})%I.
  Proof.
    iRevert (δ δΔ k Q).
    iLöb as "IH".
    iIntros (δ δΔ k Q) "wpk".
    rewrite ?wp_unfold.
    cbn.
    iIntros (σ ks1 ks n) "Hregs".
    remember (language.to_val (MkTm (δ ►► δΔ) k)) as kval.
    destruct kval.
    - rewrite /wp_pre.
      rewrite <- Heqkval.
      destruct v.
      assert (eqk := of_to_val _ (eq_sym Heqkval)).
      inversion eqk.
      rewrite <-?H2 in *; clear H2.
      iMod "wpk" as "H".
      iMod (fupd_intro_mask' _ empty) as "Hclose"; first set_solver.
      iSplitR; [trivial|].
      iModIntro.
      iIntros (e2 σ2 efs) "%".
      iModIntro. iModIntro.
      iMod "Hclose" as "e".
      iDestruct "e" as "_".
      iModIntro.
      dependent destruction a.
      dependent destruction H0.
      + rewrite env_drop_cat.
        iFrame.
        iSplitL; [|trivial].
        by iApply wp_value.
      + dependent destruction H0.
    - rewrite /wp_pre.
      rewrite <-Heqkval.
      iMod (fupd_intro_mask' _ empty) as "Hclose"; first set_solver.
      iModIntro.
      iSplitR; [trivial|].
      iIntros (e2 σ2 efs2) "%".
      dependent destruction a.
      dependent destruction H0.
      + iModIntro. iModIntro.
        iMod "Hclose" as "_".
        iFrame.
        iModIntro.
        iSplitL; [|trivial].
        iApply wp_compat_fail.
      + iMod "Hclose" as "_".
        iMod ("wpk" $! (γ , μ) ks1 ks n with "Hregs") as "[% wpk]".
        iMod ("wpk" $! _ _ _ (mk_prim_step H0)) as "wpk".
        iModIntro. iModIntro.
        iMod "wpk" as "[Hregs [wpk' _]]".
        iModIntro.
        iFrame.
        iSplitL; [|trivial].
        iApply "IH".
        iFrame.
  Qed.

  Lemma iris_rule_stm_let {Γ} (δ : LocalStore Γ)
        (x : 𝑿) (σ τ : Ty) (s : Stm Γ σ) (k : Stm (ctx_snoc Γ (x , σ)) τ)
        (P : iProp Σ) (Q : Lit σ -> LocalStore Γ -> iProp Σ)
        (R : Lit τ -> LocalStore Γ -> iProp Σ) :
        semTriple δ P s Q ->
        (forall (v : Lit σ) (δ' : LocalStore Γ),
            semTriple (env_snoc δ' (x,σ) v) (Q v δ') k (fun v δ'' => R v (env_tail δ'')) ) ->
        semTriple δ P (let: x := s in k) R.
  Proof.
    iIntros (trips tripk) "P".
    iPoseProof (trips with "P") as "wpv". clear trips.
    iRevert (s δ) "wpv".
    iLöb as "IH".
    iIntros (s δ) "wpv".
    rewrite (wp_unfold _ _ (MkTm _ (stm_let _ _ _ k))).
    iIntros ([regs μ] ks1 ks n) "Hregs".
    iMod (fupd_intro_mask' _ empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 σ2 efs) "%".
    remember (MkTm δ (let: x ∶ σ := s in k)) as t.
    destruct σ2 as [regs2 μ2].
    unfold language.prim_step in a; cbn in a.
    dependent destruction a.
    dependent destruction H0.
    cbn.
    + iPoseProof (wp_value_inv' _ _ _ (MkVal _ _ v) with "wpv") as "Qv".
      iModIntro. iModIntro.
      iMod "Hclose" as "_".
      iMod "Qv" as "Qv".
      iPoseProof (tripk v δ with "Qv") as "wpk".
      iModIntro.
      iFrame; iSplitL; auto.
      by iApply (wp_compat_block (env_snoc env_nil (x , σ) v) k (fun v0 => match v0 with | MkVal _ δ' v1 => R v1 δ' end )).
    + iModIntro. iModIntro.
      iMod "Hclose" as "_".
      cbn.
      iFrame; iSplitL; auto.
      by iApply wp_compat_fail.
    + cbn.
      rewrite wp_unfold.
      unfold wp_pre.
      rewrite (val_stuck (MkTm δ s) (γ , μ) [] (MkTm δ' s') (γ' , μ') [] (mk_prim_step H0)).
      iSpecialize ("wpv" $! (γ , μ) nil nil n with "Hregs").
      iMod "Hclose".
      iMod "wpv" as "[_ wpv]".
      iSpecialize ("wpv" $! (MkTm δ' s') (γ' , μ') nil (mk_prim_step H0)).
      iMod "wpv" as "wpv".
      iModIntro. iModIntro.
      iMod "wpv" as "[Hregs [wps _]]".
      iModIntro.
      cbn.
      iFrame.
      by iApply "IH".
  Qed.

  Lemma iris_rule_stm_let_forwards {Γ} (δ : LocalStore Γ)
        (x : 𝑿) (σ τ : Ty) (s : Stm Γ σ) (k : Stm (ctx_snoc Γ (x , σ)) τ)
        (P : iProp Σ) (Q : Lit σ -> LocalStore Γ -> iProp Σ)
        (R : Lit τ -> LocalStore (Γ ▻ (x,σ)) -> iProp Σ) :
        semTriple δ P s Q ->
        (forall (v : Lit σ) (δ' : LocalStore Γ),
            semTriple (env_snoc δ' (x,σ) v) (Q v δ') k R ) ->
        semTriple δ P (let: x := s in k) (fun v δ' => ∃ v__let, R v (env_snoc δ' (x,σ) v__let))%I.
  Proof.
    (* proof should be generalizable beyond Iris model? *)
    iIntros (trips tripk).
    apply (iris_rule_stm_let (δ := δ) (s := s) (k := k) (P := P) (Q := Q) (fun v δ' => ∃ v__let, R v (env_snoc δ' (x,σ) v__let))%I trips).
    iIntros (v δ') "Qv".
    iPoseProof (tripk with "Qv") as "wpk".
    iApply (wp_mono with "wpk").
    iIntros (v') "Rv".
    destruct v'.
    iExists (env_head δ0).
    by dependent destruction δ0.
  Qed.

  Lemma iris_rule_stm_block {Γ} (δ : LocalStore Γ)
        (Δ : Ctx (𝑿 * Ty)) (δΔ : LocalStore Δ)
        (τ : Ty) (k : Stm (ctx_cat Γ Δ) τ)
        (P : iProp Σ) (R : Lit τ -> LocalStore Γ -> iProp Σ) :
        (semTriple (δ ►► δΔ) P k (fun v δ'' => R v (env_drop Δ δ''))) ->
        semTriple δ P (stm_block δΔ k) R.
  Proof.
    iIntros (tripk) "P".
    iPoseProof (tripk with "P") as "wpk".
    by iApply (wp_compat_block δΔ k (fun v => match v with | MkVal _ δ' v' => R v' δ' end) with "wpk").
  Qed.

  Lemma iris_rule_stm_if {Γ} (δ : LocalStore Γ)
        (τ : Ty) (e : Exp Γ ty_bool) (s1 s2 : Stm Γ τ)
        (P : iProp Σ) (Q : Lit τ -> LocalStore Γ -> iProp Σ) :
        semTriple δ (P ∧ bi_pure (eval e δ = true)) s1 Q ->
        semTriple δ (P ∧ bi_pure (eval e δ = false)) s2 Q ->
        semTriple δ P (stm_if e s1 s2) Q.
  Admitted.
  Lemma iris_rule_stm_if_backwards {Γ} (δ : LocalStore Γ)
        (τ : Ty) (e : Exp Γ ty_bool) (s1 s2 : Stm Γ τ)
        (P1 P2 : iProp Σ) (Q : Lit τ -> LocalStore Γ -> iProp Σ) :
        semTriple δ P1 s1 Q -> semTriple δ P2 s2 Q ->
        semTriple δ (bi_impl (bi_pure (eval e δ = true)) P1 ∧
                     bi_impl (bi_pure (eval e δ = false)) P2)%I
            (stm_if e s1 s2) Q.
  Proof.
    (* generalize proof to non-iris models *)
    iIntros (trips1 trips2).
    apply (iris_rule_stm_if e
                            (bi_impl (bi_pure (eval e δ = true)) P1 ∧ bi_impl (bi_pure (eval e δ = false)) P2)).
    - iIntros "[P' %]".
      iApply trips1.
      by iApply (bi.and_elim_l with "P'").
    - iIntros "[P' %]".
      iApply trips2.
      by iApply (bi.and_elim_r with "P'").
  Qed.

  Lemma iris_rule_stm_seq {Γ} (δ : LocalStore Γ)
        (τ : Ty) (s1 : Stm Γ τ) (σ : Ty) (s2 : Stm Γ σ)
        (P : iProp Σ) (Q : LocalStore Γ -> iProp Σ) (R : Lit σ -> LocalStore Γ -> iProp Σ) :
        semTriple δ P s1 (fun _ => Q) ->
        (forall δ', semTriple δ' (Q δ') s2 R) ->
        semTriple δ P (s1 ;; s2) R.
  Admitted.

  Lemma iris_rule_stm_assert {Γ} (δ : LocalStore Γ)
        (e1 : Exp Γ ty_bool) (e2 : Exp Γ ty_string)
                      (P : iProp Σ) :
        semTriple δ P (stm_assert e1 e2) (fun v δ' => bi_pure (δ = δ' /\ eval e1 δ' = v /\ v = true) ∧ P)%I.
  Admitted.

  Lemma iris_rule_stm_fail {Γ} (δ : LocalStore Γ)
        (τ : Ty) (s : Lit ty_string) :
        forall (Q : Lit τ -> LocalStore Γ -> iProp Σ),
          semTriple δ True%I (stm_fail τ s) Q.
  Proof.
    iIntros (Q) "_".
    iApply wp_compat_fail.
  Qed.

  Lemma iris_rule_stm_match_list {Γ} (δ : LocalStore Γ)
        {σ τ : Ty} (e : Exp Γ (ty_list σ)) (alt_nil : Stm Γ τ)
        (xh xt : 𝑿) (alt_cons : Stm (ctx_snoc (ctx_snoc Γ (xh , σ)) (xt , ty_list σ)) τ)
        (Pnil : iProp Σ) (Pcons : iProp Σ) (Q : Lit τ -> LocalStore Γ -> iProp Σ) :
        semTriple δ Pnil alt_nil (fun v' δ' => Q v' δ') ->
        (forall v vs, env_snoc (env_snoc δ (xh,σ) v) (xt,ty_list σ) vs ⊢
                        ⦃ Pcons ⦄ alt_cons ⦃ fun v' δ' => Q v' (env_tail (env_tail δ')) ⦄) ->
        semTriple δ (bi_impl (bi_pure (eval e δ = nil)) Pnil
                     ∧ (∀ v vs, bi_impl (bi_pure (eval e δ = cons v vs)) Pcons))%I
                  (stm_match_list e alt_nil xh xt alt_cons) Q.
  Admitted.
  Lemma iris_rule_stm_match_sum {Γ} (δ : LocalStore Γ)
        (σinl σinr τ : Ty) (e : Exp Γ (ty_sum σinl σinr))
                         (xinl : 𝑿) (alt_inl : Stm (ctx_snoc Γ (xinl , σinl)) τ)
                         (xinr : 𝑿) (alt_inr : Stm (ctx_snoc Γ (xinr , σinr)) τ)
                         (Pinl : iProp Σ)
                         (Pinr : iProp Σ)
                         (Q : Lit τ -> LocalStore Γ -> iProp Σ) :
        (forall v, semTriple (env_snoc δ (xinl,σinl) v) Pinl alt_inl (fun v' δ' => Q v' (env_tail δ'))) ->
        (forall v, semTriple (env_snoc δ (xinr,σinr) v) Pinr alt_inr (fun v' δ' => Q v' (env_tail δ'))) ->
        semTriple δ ((∀ x, bi_impl (bi_pure (eval e δ = inl x)) Pinl)
                     ∧ (∀ x, bi_impl (bi_pure (eval e δ = inr x)) Pinr))%I
            (stm_match_sum e xinl alt_inl xinr alt_inr) Q.
  Admitted.
  Lemma iris_rule_stm_match_pair {Γ} (δ : LocalStore Γ)
        {σ1 σ2 τ : Ty} (e : Exp Γ (ty_prod σ1 σ2))
        (xl xr : 𝑿) (rhs : Stm (ctx_snoc (ctx_snoc Γ (xl , σ1)) (xr , σ2)) τ)
        (P : iProp Σ) (Q : Lit τ -> LocalStore Γ -> iProp Σ) :
        (forall vl vr,
            semTriple (env_snoc (env_snoc δ (xl, σ1) vl) (xr, σ2) vr)
              P rhs (fun v δ' => Q v (env_tail (env_tail δ')))) ->
        semTriple δ P (stm_match_pair e xl xr rhs) Q.
  Admitted.
  Lemma iris_rule_stm_match_enum {Γ} (δ : LocalStore Γ)
        {E : 𝑬} (e : Exp Γ (ty_enum E)) {τ : Ty}
        (alts : forall (K : 𝑬𝑲 E), Stm Γ τ)
        (P : iProp Σ) (Q : Lit τ -> LocalStore Γ -> iProp Σ) :
        (forall K, semTriple δ P (alts K) Q) ->
        semTriple δ P (stm_match_enum E e alts) Q.
  Admitted.
  Lemma iris_rule_stm_match_tuple {Γ} (δ : LocalStore Γ)
        {σs : Ctx Ty} {Δ : Ctx (𝑿 * Ty)} (e : Exp Γ (ty_tuple σs))
        (p : TuplePat σs Δ) {τ : Ty} (rhs : Stm (ctx_cat Γ Δ) τ)
        (P : iProp Σ) (Q : Lit τ -> LocalStore Γ -> iProp Σ) :
        (forall (δΔ : LocalStore Δ),
            semTriple (env_cat δ δΔ) P rhs (fun v δ' => Q v (env_drop Δ δ'))) ->
        semTriple δ P (stm_match_tuple e p rhs) Q.
  Admitted.
  Lemma iris_rule_stm_match_union {Γ} (δ : LocalStore Γ)
        {U : 𝑼} (e : Exp Γ (ty_union U)) {σ τ : Ty}
        (alt__Δ : forall (K : 𝑼𝑲 U), Ctx (𝑿 * Ty))
        (alt__p : forall (K : 𝑼𝑲 U), Pattern (alt__Δ K) (𝑼𝑲_Ty K))
        (alt__r : forall (K : 𝑼𝑲 U), Stm (ctx_cat Γ (alt__Δ K)) τ)
        (P : forall (K : 𝑼𝑲 U), iProp Σ) (Q : Lit τ -> LocalStore Γ -> iProp Σ) :
        (forall (K : 𝑼𝑲 U) (δΔ : LocalStore (alt__Δ K)),
            semTriple (env_cat δ δΔ) (P K) (alt__r K) (fun v δ' => Q v (env_drop (alt__Δ K) δ'))) ->
        semTriple δ
          (∀ (K : 𝑼𝑲 U) (v : Lit (𝑼𝑲_Ty K)), bi_impl (bi_pure (eval e δ = 𝑼_fold (existT K v))) (P K))
          (stm_match_union U e (fun K => @alt Γ (𝑼𝑲_Ty K) τ (alt__Δ K) (alt__p K) (alt__r K)))
          Q.
  Admitted.
  Lemma iris_rule_stm_match_record {Γ} (δ : LocalStore Γ)
        {R : 𝑹} {Δ : Ctx (𝑿 * Ty)} (e : Exp Γ (ty_record R))
        (p : RecordPat (𝑹𝑭_Ty R) Δ) {τ : Ty} (rhs : Stm (ctx_cat Γ Δ) τ)
        (P : iProp Σ) (Q : Lit τ -> LocalStore Γ -> iProp Σ) :
        (forall (δΔ : LocalStore Δ),
            semTriple (env_cat δ δΔ) P rhs (fun v δ' => Q v (env_drop Δ δ'))) ->
        semTriple δ P (stm_match_record R e p rhs) Q.
  Admitted.

  Lemma iris_rule_stm_read_register {Γ} (δ : LocalStore Γ)
        {σ : Ty} (r : 𝑹𝑬𝑮 σ) (v : Lit σ) :
        semTriple δ (r ↦ v) (stm_read_register r)
                  (fun v' δ' => bi_pure (δ' = δ) ∧ bi_pure (v' = v) ∧ r ↦ v)%I.
  Proof.
    iIntros "Hreg".
    iApply wp_mono; [| iApply (rule_stm_read_register with "Hreg") ].
    iIntros ([δ' v']) "[Hreg %]".
    inversion H0.
    by iFrame.
  Qed.

  Lemma iris_rule_stm_write_register {Γ} (δ : LocalStore Γ)
        {σ : Ty} (r : 𝑹𝑬𝑮 σ) (w : Exp Γ σ)
                              (Q : Lit σ -> LocalStore Γ -> iProp Σ)
                              (v : Lit σ) :
        semTriple δ (r ↦ v) (stm_write_register r w)
                  (fun v' δ' => bi_pure (δ' = δ) ∧ bi_pure (v' = eval w δ) ∧ r ↦ v')%I.
  Proof.
    iIntros "Hreg".
    iApply wp_mono; [|iApply (rule_stm_write_register with "Hreg")].
    iIntros (v') "[Hreg %]".
    rewrite H0.
    by iFrame.
  Qed.

  Lemma iris_rule_stm_assign_backwards {Γ} (δ : LocalStore Γ)
        (x : 𝑿) (σ : Ty) (xIn : (x,σ) ∈ Γ) (s : Stm Γ σ)
        (P : iProp Σ) (R : Lit σ -> LocalStore Γ -> iProp Σ) :
        semTriple δ P s (fun v δ' => R v (@env_update _ _ _ δ' (x , _) _ v)) ->
        semTriple δ P (stm_assign x s) R.
  Admitted.
  Lemma iris_rule_stm_assign_forwards {Γ} (δ : LocalStore Γ)
        (x : 𝑿) (σ : Ty) (xIn : (x,σ) ∈ Γ) (s : Stm Γ σ)
        (P : iProp Σ) (R : Lit σ -> LocalStore Γ -> iProp Σ) :
        semTriple δ P s R ->
        semTriple δ P (stm_assign x s) (fun v__new δ' => ∃ v__old, R v__new (@env_update _ _ _ δ' (x , _)  _ v__old))%I.
  Proof.
    intros trips.
    apply iris_rule_stm_assign_backwards.
    iIntros "P".
    iPoseProof (trips with "P") as "wps".
    iApply (wp_mono with "wps").
    iIntros ([δ' v']) "Rv".
    iExists (env_lookup δ' xIn).
    by rewrite env_update_update env_update_lookup.
  Qed.

  Lemma iris_rule_stm_call_forwards {Γ} (δ : LocalStore Γ)
        {Δ σ} (f : 𝑭 Δ σ) (es : NamedEnv (Exp Γ) Δ)
        (P : iProp Σ)
        (Q : Lit σ -> iProp Σ) :
        CTriple Δ (evals es δ) P Q (CEnv f) ->
        semTriple δ P (stm_call f es) (fun v δ' => Q v ∧ bi_pure (δ = δ'))%I.
  Admitted.
  Lemma iris_rule_stm_call_frame {Γ} (δ : LocalStore Γ)
        (Δ : Ctx (𝑿 * Ty)) (δΔ : LocalStore Δ) (τ : Ty) (s : Stm Δ τ)
        (P : iProp Σ) (Q : Lit τ -> LocalStore Γ -> iProp Σ) :
        semTriple δΔ P s (fun v _ => Q v δ) ->
        semTriple δ P (stm_call_frame Δ δΔ τ s) Q.
  Admitted.
  Lemma iris_rule_stm_bind {Γ} (δ : LocalStore Γ)
        {σ τ : Ty} (s : Stm Γ σ) (k : Lit σ -> Stm Γ τ)
        (P : iProp Σ) (Q : Lit σ -> LocalStore Γ -> iProp Σ)
        (R : Lit τ -> LocalStore Γ -> iProp Σ) :
        semTriple δ P s Q ->
        (forall (v__σ : Lit σ) (δ' : LocalStore Γ),
            semTriple δ' (Q v__σ δ') (k v__σ) R) ->
        semTriple δ P (stm_bind s k) R.
  Admitted.

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
  Admitted.

End IrisInstance.
