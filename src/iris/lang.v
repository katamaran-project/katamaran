From MicroSail Require Import
     Notation
     Syntax
     Context
     SmallStep.Step
     SmallStep.Inversion
     .

Require Import Coq.Program.Equality.

From Equations Require Import Equations Signature.

From iris.bi Require Export interface.
From iris.algebra Require Export gmap excl auth.
From iris.base_logic Require Export gen_heap lib.fancy_updates lib.fancy_updates_from_vs lib.invariants.
From iris.program_logic Require Export language ectx_language ectxi_language.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import tactics.

Set Implicit Arguments.

Module ValsAndTerms
       (Import typekit : TypeKit)
       (Import termkit : TermKit typekit)
       (Import progkit : ProgramKit typekit termkit).

  Inductive Tm σ : Type :=
  | MkTm {Γ : Ctx (𝑿 * Ty)} (δ : LocalStore Γ) (s : Stm Γ σ) : Tm σ.

  (* remainng obligations? *)
  (* Derive NoConfusion for Tm. *)

  Inductive Val σ : Type :=
    (* we only keep the store around for technical reasons, essentially to be able to prove of_to_val. *)
  | MkVal {Γ : Ctx (𝑿 * Ty)} (δ : LocalStore Γ) (v : Lit σ) : Val σ.

  Definition val_to_lit {σ} : Val σ -> Lit σ := fun v => match v with | MkVal _ _ v' => v' end.

  Definition of_val {σ} (v : Val σ) : Tm σ :=
    match v with
      MkVal _ δ v => MkTm δ (stm_lit _ v)
    end.

  Definition to_val {σ} (t : Tm σ) : option (Val σ) :=
    (* easier way to do the dependent pattern match here? *)
    match t with
    | MkTm δ s => match s with
                   stm_lit τ l => Some (MkVal _ δ l)
                 | _ => None
                 end
    end.

  Lemma to_of_val {σ} (v : Val σ) : to_val (of_val v) = Some v.
  Proof.
    by induction v.
  Qed.

  Lemma of_to_val {σ} (e : Tm σ) v : to_val e = Some v → of_val v = e.
  Proof.
    induction e.
    induction s; try done.
    by intros [= <-].
  Qed.

  Module Inv := Inversion typekit termkit progkit.
  Export Inv.
  Export SS.

  Lemma val_head_stuck_step {σ} {Γ : Ctx (𝑿 * Ty)} γ1 γ2 μ1 μ2 (δ1 : LocalStore Γ) δ2 (s1 : Stm Γ σ) s2 :
    Step γ1 γ2 μ1 μ2 δ1 δ2 s1 s2 -> to_val (MkTm δ1 s1) = None.
    by induction 1.
  Qed.
End ValsAndTerms.

Module IrisInstance
       (Import typekit : TypeKit)
       (Import termkit : TermKit typekit)
       (Import progkit : ProgramKit typekit termkit).

  Import CtxNotations.
  Import EnvNotations.

  Definition σt : Ty := ty_bool.

  Module VT := ValsAndTerms typekit termkit progkit.
  Import VT.

  Definition Val := VT.Val σt.
  Definition Tm := VT.Tm σt.

  Definition observation := Empty_set.

  Definition State := prod RegStore Memory.

  Inductive prim_step : Tm -> State -> Tm -> State -> list (VT.Tm σt) -> Prop :=
  | mk_prim_step {Γ  : Ctx (𝑿 * Ty)} γ1 γ2 μ1 μ2 (δ1 : LocalStore Γ) (δ2 : LocalStore Γ) s1 s2 :
      SS.Step γ1 γ2 μ1 μ2 δ1 δ2 s1 s2 ->
      prim_step (VT.MkTm δ1 s1) (γ1 , μ1) (VT.MkTm δ2 s2) (γ2 , μ2) nil
  .

  Lemma val_head_stuck e1 s1 e2 s2 (ks : list (VT.Tm σt)) : prim_step e1 s1 e2 s2 ks → VT.to_val e1 = None.
  Proof.
    induction 1.
    by eapply VT.val_head_stuck_step.
  Qed.

  Lemma microsail_lang_mixin : @LanguageMixin (VT.Tm σt) (VT.Val σt) State Empty_set VT.of_val VT.to_val (fun e1 s1 ls e2 s2 ks => prim_step e1 s1 e2 s2 ks).
  Proof.
    split.
    - eauto using VT.to_of_val, VT.of_to_val, val_head_stuck.
    - eauto using VT.to_of_val, VT.of_to_val, val_head_stuck.
    - eauto using VT.to_of_val, VT.of_to_val, val_head_stuck.

  Qed.

  Canonical Structure stateO := leibnizO State.
  Canonical Structure valO := leibnizO Val.
  Canonical Structure exprO := leibnizO Tm.

  Canonical Structure microsail_lang : language := Language microsail_lang_mixin.

  Instance intoVal_lit {Γ} : IntoVal (VT.MkTm (Γ := Γ) δ (stm_lit _ l)) (VT.MkVal _ δ l).
  intros; eapply VT.of_to_val; by cbn.
  Qed.

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
    - intros [σ r1] [τ r2].
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
    intros [σ v1] [τ v2].
    destruct (Ty_eq_dec σ τ).
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

  Instance sailG_irisG `{sailG Σ} : irisG microsail_lang Σ := {
    iris_invG := sailG_invG;
    state_interp σ κs _ := regs_inv σ.1;
    fork_post _ := True%I; (* no threads forked in sail, so this is fine *)
                                                   }.
  Global Opaque iris_invG.

  Context `{sailG Σ}.

  (* Definition test : iProp Σ := WP (VT.MkTm env_nil (stm_lit ty_bool true)) {{ v, True }}%I. *)

  (* Lemma testHolds : ⊢ test. *)
  (*   by iApply wp_value. *)
  (* Qed. *)
  Set Equations With UIP.

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

  Lemma regs_inv_update `{inG Σ (authR (gmapUR SomeReg (exclR (leibnizO SomeLit))))} {τ} {r} {v : Lit τ} {regsmap : gmapUR SomeReg (exclR (leibnizO SomeLit))} {regstore : RegStore} :
    map_Forall (λ r' v', match r' with
                         | @mkSomeReg τ r'' => Excl (mkSomeLit (read_register regstore r'')) = v'
                         end) regsmap ->
    (own reg_gv_name (● <[mkSomeReg r:=Excl (mkSomeLit v)]> regsmap)) -∗ regs_inv (write_register regstore r v).
  Proof.
    iIntros (regseq) "Hownregs".
    rewrite /regs_inv.
    iExists (<[mkSomeReg r:=Excl (mkSomeLit v)]> regsmap).
    iSplitL "Hownregs".
    - (* iFrame "Hownregs". *)
      (* huh, what's wrong here? *)
      admit.
    - iPureIntro.
      apply (map_Forall_lookup_2 (λ (reg : SomeReg) (v0 : excl SomeLit),
       match reg with
       | @mkSomeReg τ0 reg0 => Excl (mkSomeLit (read_register (write_register regstore r v) reg0)) = v0
       end)).
      intros [τ' r'] x eq1.
      destruct (𝑹𝑬𝑮_eq_dec r r') as [eq2|neq].
      + dependent destruction eq2.
        destruct eqi, eqf; cbn in *.
        rewrite (lookup_insert regsmap (mkSomeReg r) (Excl (mkSomeLit v))) in eq1.
        apply (inj Some) in eq1.
        rewrite <- eq1.
        by rewrite (read_write regstore r v).
      + assert (mkSomeReg r ≠ mkSomeReg r') as neq2.
        * intros eq2.
          dependent destruction eq2.
          destruct (neq (teq_refl r' eq_refl eq_refl)).
        * rewrite (lookup_insert_ne regsmap (mkSomeReg r) (mkSomeReg r') (Excl (mkSomeLit v)) neq2) in eq1.
          rewrite (read_write_distinct regstore neq v).
          exact (map_Forall_lookup_1 (λ (r' : SomeReg) (v' : excl SomeLit),
                match r' with
                | @mkSomeReg τ r'' => Excl (mkSomeLit (read_register regstore r'')) = v'
                end) regsmap (mkSomeReg r') x regseq eq1).
  Admitted.

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

  Lemma rule_stm_read_register (r : 𝑹𝑬𝑮 σt) (v : Lit σt) {Γ} {δ : LocalStore Γ} :
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
      destruct a as [Γ2 γ1 γ2 σ1 σ2 δ1 δ2 s1 s2 step].
      dependent destruction Heqt.
      destruct (steps_inversion_read_register step) as [<- [<- [<- ->]]].
      iModIntro. iModIntro. iModIntro.
      iFrame. iSplitR ""; auto.
      by iApply wp_value.
  Qed.

  Lemma rule_stm_write_register (r : 𝑹𝑬𝑮 σt) (v1 v2 : Lit σt) :
    ⊢ (reg_pointsTo r v1 -∗
                  WP (VT.MkTm env_nil (stm_write_register r (exp_lit ctx_nil σt v2)) : expr microsail_lang) {{ w, reg_pointsTo r v2 ∗ bi_pure (v2 = VT.val_to_lit w) }}
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
      iFrame. iSplitR ""; auto.
      by iApply wp_value.
  Qed.
End IrisInstance.
