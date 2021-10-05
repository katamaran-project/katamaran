(******************************************************************************)
(* Copyright (c) 2020 Dominique Devriese                                      *)
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
Require Import Equations.Prop.EqDec.

From stdpp Require finite gmap list.

From iris.bi Require Import interface.
From iris.algebra Require Import gmap excl auth.
From iris.bi Require Import big_op.
From iris.base_logic Require Import lib.fancy_updates lib.own lib.gen_heap.
From iris.program_logic Require Import weakestpre adequacy.
From iris.proofmode Require Import tactics.

Require Import MicroSail.Sep.Spec.
Require Import MicroSail.Sep.Hoare.
(* can't import: overlapping notations *)
Require MicroSail.Sep.Logic.
Module logic := MicroSail.Sep.Logic.

Set Implicit Arguments.

Module ValsAndTerms
       (Import termkit : TermKit)
       (Import progkit : ProgramKit termkit).

  Inductive Tm (Γ : PCtx) τ : Type :=
  | MkTm (δ : CStore Γ) (s : Stm Γ τ) : Tm Γ τ.

  Section TransparentObligations.
    Local Set Transparent Obligations.
    Derive NoConfusion for Tm.
  End TransparentObligations.

  Inductive Val (Γ : PCtx) τ : Type :=
    (* we only keep the store around for technical reasons, essentially to validate of_to_val. *)
  | MkVal (δ : CStore Γ) (v : Lit τ) : Val Γ τ.

  Definition val_to_lit {Γ} {τ} : Val Γ τ -> Lit τ := fun v => match v with | MkVal _ _ v' => v' end.

  Definition of_val {Γ} {τ} (v : Val Γ τ) : Tm Γ τ :=
    match v with
      MkVal _ δ v => MkTm δ (stm_lit _ v)
    end.

  Definition to_val {Γ} {τ} (t : Tm Γ τ) : option (Val Γ τ) :=
    match t with
    | MkTm δ s => match s with
                   stm_lit _ l => Some (MkVal _ δ l)
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

  Module Inv := Inversion termkit progkit.
  Export Inv.
  Export SS.

  Lemma val_head_stuck_step {τ} {Γ : PCtx} γ1 γ2 μ1 μ2 (δ1 : CStore Γ) δ2 (s1 : Stm Γ τ) s2 :
    ⟨ γ1, μ1, δ1, s1 ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩ -> to_val (MkTm δ1 s1) = None.
  Proof.
    by induction 1.
  Qed.

  Definition observation := Empty_set.

  Definition State := prod RegStore Memory.

  Inductive prim_step {Γ τ} : Tm Γ τ -> State -> Tm Γ τ -> State -> list (Tm Γ τ) -> Prop :=
  | mk_prim_step γ1 γ2 μ1 μ2 (δ1 : CStore Γ) (δ2 : CStore Γ) s1 s2 :
      ⟨ γ1, μ1, δ1, s1 ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩ ->
      prim_step (MkTm δ1 s1) (γ1 , μ1) (MkTm δ2 s2) (γ2 , μ2) nil
  .

  Lemma val_head_stuck {Γ τ} (e1 : Tm Γ τ) s1 e2 s2 {ks} : prim_step e1 s1 e2 s2 ks → to_val e1 = None.
  Proof.
    induction 1.
    by eapply val_head_stuck_step.
  Qed.

  Lemma microsail_lang_mixin Γ τ : @LanguageMixin (Tm Γ τ) (Val Γ τ) State Empty_set of_val to_val (fun e1 s1 ls e2 s2 ks => prim_step e1 s1 e2 s2 ks).
  Proof.
    split; eauto using to_of_val, of_to_val, val_head_stuck.
  Qed.

  Canonical Structure stateO := leibnizO State.
  Canonical Structure valO {Γ τ} := leibnizO (Val Γ τ).
  Canonical Structure exprO {Γ τ} := leibnizO (Tm Γ τ).

  Canonical Structure microsail_lang Γ τ : language := Language (microsail_lang_mixin Γ τ).

  Instance intoVal_lit {Γ τ δ l} : IntoVal (MkTm (Γ := Γ) (τ := τ) δ (stm_lit _ l)) (MkVal _ δ l).
  intros; eapply of_to_val; by cbn.
  Defined.

  Definition SomeReg : Type := sigT 𝑹𝑬𝑮.
  Definition SomeLit : Type := sigT Lit.

  Section TransparentObligations.
    Local Set Transparent Obligations.
    (* Derive NoConfusion for SomeReg. *)
    (* Derive NoConfusion for SomeLit. *)
    Derive NoConfusion for excl.
  End TransparentObligations.

  Instance eqDec_SomeReg : EqDec SomeReg.
  Proof.
    intros [? r1] [? r2].
    destruct (eq_dec_het r1 r2).
    - left. now dependent elimination e.
    - right. intros e; now dependent elimination e.
  Defined.

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
        by dependent elimination H.
    - right. intros H.
      by dependent elimination H.
  Qed.

  Definition regUR := authR (gmapUR SomeReg (exclR (leibnizO SomeLit))).

End ValsAndTerms.

Module IrisRegisters
       (Import termkit : TermKit)
       (Import progkit : ProgramKit termkit)
       (Import assertkit : AssertionKit termkit progkit)
       (Import contractkit : SymbolicContractKit termkit progkit assertkit)
       .

  Import CtxNotations.
  Import EnvNotations.

  Module PL := ProgramLogic termkit progkit assertkit contractkit.
  Export PL.

  Module VT := ValsAndTerms termkit progkit.
  Export VT.


  Class sailRegG Σ := SailRegG {
                          (* ghost variable for tracking state of registers *)
                          reg_inG :> inG Σ regUR;
                          reg_gv_name : gname;
                        }.

  Definition reg_pointsTo `{sailRegG Σ} {τ} (r : 𝑹𝑬𝑮 τ) (v : Lit τ) : iProp Σ :=
    own reg_gv_name (◯ {[ existT _ r := Excl (existT _ v) ]}).

  Definition regs_inv `{sailRegG Σ} (regstore : RegStore) : iProp Σ :=
    (∃ regsmap,
        own reg_gv_name (● regsmap) ∗
        ⌜ map_Forall (K := SomeReg) (A := excl SomeLit) (fun reg v => match reg with | existT _ reg => Excl (existT _ (read_register regstore reg)) = v end ) regsmap ⌝
    )%I.

End IrisRegisters.

Module Type IrisHeapKit
       (Import termkit : TermKit)
       (Import progkit : ProgramKit termkit)
       (Import assertkit : AssertionKit termkit progkit)
       (Import contractkit : SymbolicContractKit termkit progkit assertkit)
       .

  Import CtxNotations.
  Import EnvNotations.

  Module IrisRegs := IrisRegisters termkit progkit assertkit contractkit.
  Export IrisRegs.

  Parameter Inline memPreG : gFunctors -> Set.
  Parameter Inline memG : gFunctors -> Set.
  Parameter Inline memΣ : gFunctors.

  Parameter Inline memΣ_PreG : forall {Σ}, subG memΣ Σ -> memPreG Σ.

  Parameter Inline mem_inv : forall {Σ}, memG Σ -> Memory -> iProp Σ.
  Parameter Inline mem_res : forall {Σ}, memG Σ -> Memory -> iProp Σ.

  (* Definition mem_inv `{sailG Σ} (μ : Z -> option Z) : iProp Σ := *)
  (*   (∃ memmap, gen_heap_ctx memmap ∗ *)
  (*      ⌜ map_Forall (fun (a : Z) v => μ a = Some v) memmap ⌝ *)
  (*   )%I. *)

  Parameter Inline mem_inv_init : forall Σ (μ : Memory), memPreG Σ -> ⊢ |==> ∃ memG : memG Σ, (mem_inv memG μ ∗ mem_res memG μ)%I.

  Parameter luser_inst : forall `{sRG : sailRegG Σ} `{invG Σ} (p : 𝑷) (ts : Env Lit (𝑷_Ty p)), memG Σ -> iProp Σ.

  Parameter lduplicate_inst : forall `{sRG : sailRegG Σ} `{invG Σ} (p : 𝑷) (ts : Env Lit (𝑷_Ty p))
      (mG : memG Σ),
      is_duplicable p = true -> bi_entails (luser_inst (p := p) ts mG) (luser_inst (p := p) ts mG ∗ luser_inst (p := p) ts mG).

End IrisHeapKit.

Module IrisInstance
       (Import termkit : TermKit)
       (Import progkit : ProgramKit termkit)
       (Import assertkit : AssertionKit termkit progkit)
       (Import contractkit : SymbolicContractKit termkit progkit assertkit)
       (Import irisheapkit : IrisHeapKit termkit progkit assertkit contractkit).

  Import CtxNotations.
  Import EnvNotations.

  Section IrisInstance.

  Class sailPreG Σ := SailPreG { (* resources for the implementation side *)
                       sailG_invPreG :> invPreG Σ; (* for fancy updates, invariants... *)

                       (* ghost variable for tracking state of registers *)
                       reg_pre_inG :> inG Σ regUR;

                       (* ghost variable for tracking state of memory cells *)
                       sailPreG_gen_memPreG :> memPreG Σ
                     }.
  Class sailG Σ := SailG { (* resources for the implementation side *)
                       sailG_invG :> invG Σ; (* for fancy updates, invariants... *)
                       sailG_sailRegG :> sailRegG Σ;

                       (* ghost variable for tracking state of memory cells *)
                       sailG_memG :> memG Σ
                     }.

  Global Instance sailG_irisG {Γ τ} `{sailG Σ} : irisG (microsail_lang Γ τ) Σ := {
    iris_invG := sailG_invG;
    state_interp σ ns κs := (regs_inv σ.1 ∗ mem_inv sailG_memG σ.2)%I;
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
  }.

  Global Program Instance iProp_ILogicLaws : @logic.ILogicLaws (iProp Σ) iris_ILogic.
  Next Obligation.
    iIntros; iFrame.
  Qed.
  Next Obligation.
    eapply (PreOrder_Transitive (R := bi_entails)); eauto.
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

  Global Program Instance iris_ISepLogic : logic.ISepLogic (iProp Σ) :=
  { logic.emp := emp%I;
    logic.sepcon P Q := (P ∗ Q)%I;
    logic.wand P Q := (P -∗ Q)%I
  }.

  Global Program Instance iProp_ISepLogicLaws : @logic.ISepLogicLaws (iProp Σ) iris_ISepLogic.
  Next Obligation.
    intros P Q R. split.
    - eapply bi.sep_assoc'.
    - iIntros "[P [Q R]]".
      iFrame.
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
      by iSplit; iFrame.
    - iIntros "[% [P R]]".
      by iFrame.
  Qed.
  Next Obligation.
    iIntros (P P' Q Q' PP QQ) "[P Q]".
    iSplitL "P".
    - by iApply PP.
    - by iApply QQ.
  Qed.
  Next Obligation.
    intros P. split.
    - iIntros "[P _]".
      iFrame.
    - iIntros "P".
      by iSplit; iFrame.
  Qed.
  Next Obligation.
    now iIntros (P) "HP".
  Qed.

  Global Instance iris_IHeapLet : IHeaplet (iProp Σ) :=
    { is_ISepLogic := iris_ISepLogic;
      (* TODO: should be user-defined... *)
      luser p ts := luser_inst ts sailG_memG;
      lptsreg σ r t := reg_pointsTo r t;
      lduplicate p ts := fun hdup => lduplicate_inst (p := p) ts sailG_memG hdup
    }.

  End IrisInstance.
End IrisInstance.

Module IrisSoundness
       (Import termkit : TermKit)
       (Import progkit : ProgramKit termkit)
       (Import assertkit : AssertionKit termkit progkit)
       (Import contractkit : SymbolicContractKit termkit progkit assertkit)
       (Import irisheapkit : IrisHeapKit termkit progkit assertkit contractkit).

  Module Inst := IrisInstance termkit progkit assertkit contractkit irisheapkit.
  Export Inst.
  Import CtxNotations.
  Import EnvNotations.

  Section IrisSoundness.

  Context `{sailG Σ}.

  Lemma reg_valid regstore {τ} (r : 𝑹𝑬𝑮 τ) (v : Lit τ) :
    ⊢ (regs_inv regstore -∗ reg_pointsTo r v -∗ ⌜read_register regstore r = v⌝)%I.
  Proof.
    iDestruct 1 as (regsmap) "[Hregs %]".
    iIntros "Hreg".
    iDestruct (own_valid_2 with "Hregs Hreg") as %[Hl regsv]%auth_both_valid.
    iPureIntro.
    specialize (Hl 0).
    rewrite (singleton_includedN_l 0 regsmap (existT _ r) _) in Hl *.
    destruct 1 as [y [eq1%discrete%leibniz_equiv eq2%cmra_discrete_included_r]];
      auto with typeclass_instances.
    specialize (regsv (existT _ r)).
    rewrite eq1 in regsv.
    destruct y as [y|]; [|inversion regsv].
    rewrite Excl_included in eq2 *.
    intros <-%leibniz_equiv.
    specialize (H0 (existT _ r) (Excl (existT _ v)) eq1); cbn in H0.
    Local Set Equations With UIP.
    by dependent elimination H0.
  Qed.

  Lemma regs_inv_update {τ} {r} {v : Lit τ} {regsmap : gmapUR SomeReg (exclR (leibnizO SomeLit))} {regstore : RegStore} :
    map_Forall (K := SomeReg) (A := excl SomeLit) (λ r' v', match r' with
                         | existT τ r'' => Excl (existT _ (read_register regstore r'')) = v'
                         end) regsmap ->
    (own reg_gv_name (● <[existT _ r:=Excl (existT _ v)]> regsmap)) -∗ regs_inv (write_register regstore r v).
  Proof.
    iIntros (regseq) "Hownregs".
    iExists (<[existT _ r:=Excl (existT _ v)]> regsmap).
    iFrame.
    iPureIntro.
    apply (map_Forall_lookup_2 _ (<[existT _ r:=Excl (existT _ v)]> regsmap)).
    intros [τ' r'] x eq1.
    destruct (eq_dec_het r r') as [eq2|neq].
    + dependent elimination eq2.
      rewrite lookup_insert in eq1.
      apply (inj Some) in eq1.
      by rewrite <- eq1, (read_write regstore r v).
    + assert (existT _ r ≠ existT _ r') as neq2.
      * intros eq2.
        dependent elimination eq2.
        now apply neq.
      * rewrite (lookup_insert_ne _ _ _ _ neq2) in eq1.
        rewrite (read_write_distinct _ _ neq).
        apply (map_Forall_lookup_1 _ _ _ _ regseq eq1).
  Qed.

  Lemma reg_update regstore {τ} r (v1 v2 : Lit τ) :
    regs_inv regstore -∗ reg_pointsTo r v1 ==∗ regs_inv (write_register regstore r v2) ∗ reg_pointsTo r v2.
  Proof.
    iDestruct 1 as (regsmap) "[Hregs %]".
    rewrite /reg_pointsTo.
    iIntros "Hreg".
    iDestruct (own_valid_2 with "Hregs Hreg") as %[Hl%cmra_discrete_included_r regsmapv]%auth_both_valid.
    rewrite (singleton_included_l regsmap (existT _ r) _) in Hl *.
    destruct 1 as [y [eq1%leibniz_equiv eq2]].
    specialize (regsmapv (existT _ r)).
    rewrite eq1 in regsmapv.
    destruct y as [y|]; inversion regsmapv.
    iMod (own_update_2 with "Hregs Hreg") as "[Hregs Hreg]".
    {
      eapply auth_update.
      apply (singleton_local_update regsmap (existT _ r) (Excl y) (Excl (existT _ v1)) (Excl (existT _ v2)) (Excl (existT _ v2)) eq1).
      by eapply exclusive_local_update.
    }
    iModIntro.
    iFrame.
    iApply (regs_inv_update H0); iFrame.
  Qed.

  Lemma rule_stm_read_register {Γ τ} (r : 𝑹𝑬𝑮 τ) (v : Lit τ) {δ : CStore Γ} :
    ⊢ (reg_pointsTo r v -∗
                    WP (VT.MkTm δ (stm_read_register r)) ?{{ w, reg_pointsTo r v ∗ ⌜ w = VT.MkVal _ δ v ⌝ }}
      )%I.
  Proof.
    iIntros "Hreg".
    iApply (wp_mask_mono _ empty); auto.
    rewrite wp_unfold; cbn.
    iIntros (σ _ _ n) "[Hregs Hmem]".
    iDestruct (@reg_valid with "Hregs Hreg") as %<-.
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 σ2 efs) "%".
    remember (VT.MkTm δ (stm_read_register r)) as t.
    destruct H0 as [γ1 γ2 σ1 σ2 δ1 δ2 s1 s2 step].
    dependent elimination Heqt.
    destruct (steps_inversion_read_register step) as [<- [<- [<- ->]]].
    iModIntro. iModIntro. iModIntro.
    iFrame. iSplitR ""; auto.
    by iApply wp_value.
  Qed.

  Lemma rule_stm_write_register {Γ} {τ} (r : 𝑹𝑬𝑮 τ) (δ : CStore Γ) (v : Lit τ) e :
    ⊢ (reg_pointsTo r v -∗
                    WP (VT.MkTm δ (stm_write_register r e) : expr (microsail_lang Γ τ)) ?{{ w, reg_pointsTo r (eval e δ) ∗ bi_pure (w = VT.MkVal _ δ (eval e δ)) }}
    )%I.
  Proof.
    iIntros "Hreg".
    iApply (wp_mask_mono _ empty); auto.
    rewrite wp_unfold; cbn.
    iIntros (σ _ _ n) "[Hregs Hmem]".
    iMod (reg_update σ.1 r v (eval e δ) with "Hregs Hreg") as "[Hregs Hreg]".
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 σ2 efs) "%".
    dependent elimination H0.
    destruct (steps_inversion_write_register s) as [-> [<- [<- ->]]].
    iModIntro. iModIntro. iModIntro.
    iFrame. iSplitR; auto.
    by iApply wp_value.
  Qed.

  Definition semTriple {Γ τ} (δ : CStore Γ)
             (PRE : iProp Σ) (s : Stm Γ τ) (POST : Lit τ -> CStore Γ -> iProp Σ) : iProp Σ :=
    PRE -∗ WP (MkTm δ s : expr (microsail_lang Γ τ)) ?{{ v, match v with MkVal _ δ' v => POST v δ' end }}.
  (* always modality needed? perhaps not because sail not higher-order? *)

  Lemma iris_rule_consequence {Γ σ} {δ : CStore Γ}
        {P P'} {Q Q' : Lit σ -> CStore Γ -> iProp Σ} {s : Stm Γ σ} :
        (P ⊢ P') -> (forall v δ', Q' v δ' ⊢ Q v δ') ->
        semTriple δ P' s Q' -∗ semTriple δ P s Q.
  Proof.
    iIntros (PP QQ) "trips P".
    iApply (wp_mono _ _ _ (fun v => match v with MkVal _ δ' v => Q' v δ' end)).
    + intros [δ' v]; cbn.
      apply QQ.
    + iApply "trips".
      iApply PP; iFrame.
  Qed.

  Lemma iris_rule_frame {Γ σ} {δ : CStore Γ}
        (R P : iProp Σ) (Q : Lit σ -> CStore Γ -> iProp Σ) (s : Stm Γ σ) :
        (⊢ semTriple δ P s Q -∗ semTriple δ (R ∗ P) s (fun v δ' => R ∗ Q v δ'))%I.
  Proof.
    iIntros "trips [HR HP]".
    iApply (wp_mono _ _ _ (fun v => R ∗ match v with MkVal _ δ' v => Q v δ' end)%I).
    - iIntros (v) "[R Q]".
      destruct v.
      by iFrame.
    - iApply (wp_frame_l _ _ (MkTm δ s) (fun v => match v with MkVal _ δ' v => Q v δ' end) R).
      iFrame.
      by iApply "trips".
  Qed.

  Lemma iris_rule_pull {σ Γ} (δ : CStore Γ) (s : Stm Γ σ)
        (P : iProp Σ) (Q : Prop) (R : Lit σ -> CStore Γ -> iProp Σ) :
        (⊢ (⌜ Q ⌝ → semTriple δ P s R) -∗ semTriple δ (P ∧ bi_pure Q) s R)%I.
  Proof.
    iIntros "QP [P %]".
    by iApply "QP".
  Qed.

  Lemma iris_rule_exist {σ Γ} (δ : CStore Γ)
        (s : Stm Γ σ) {A : Type} {P : A -> iProp Σ}
        {Q :  Lit σ -> CStore Γ -> iProp Σ} :
        ⊢ ((∀ x, semTriple δ (P x) s Q) -∗ semTriple δ (∃ x, P x) s Q)%I.
  Proof.
    iIntros "trips Px".
    iDestruct "Px" as (x) "Px".
    by iApply "trips".
  Qed.

  (* (* following rule is dubious, re discussion about conjunction rule *) *)
  (* Lemma iris_rule_forall {σ Γ} (δ : CStore Γ) *)
  (*       {s : Stm Γ σ} {A : Type} {P : iProp Σ} *)
  (*       {Q : A -> Lit σ -> CStore Γ -> iProp Σ} *)
  (*       (x : A) : *)
  (*   ⊢ ((∀ x, semTriple δ P s (Q x)) -∗ semTriple δ P s (fun v δ' => ∀ x, Q x v δ'))%I. *)
  (* Proof. *)
  (* Admitted. *)

  Lemma iris_rule_stm_lit {Γ} (δ : CStore Γ)
        {τ : Ty} {l : Lit τ}
        {P : iProp Σ} {Q : Lit τ -> CStore Γ -> iProp Σ} :
        ⊢ ((P -∗ Q l δ)%I -∗ semTriple δ P (stm_lit τ l) Q)%I.
  Proof.
    iIntros "PQ P".
    iApply wp_value.
    by iApply "PQ".
  Qed.

  Lemma iris_rule_stm_exp {Γ} (δ : CStore Γ)
        {τ : Ty} {e : Exp Γ τ}
        {P : iProp Σ} {Q : Lit τ -> CStore Γ -> iProp Σ} :
        ⊢ ((P -∗ Q (eval e δ) δ) -∗ semTriple δ P (stm_exp e) Q)%I.
  Proof.
    iIntros "PQ P".
    iApply (wp_mask_mono _ empty); auto.
    rewrite wp_unfold.
    iIntros ([regs μ] ns ks n) "[Hregs Hmem]".
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 σ2 efs) "%".
    remember (MkTm δ (stm_exp e)) as t.
    destruct H0.
    dependent elimination Heqt.
    dependent elimination H0.
    iModIntro. iModIntro. iModIntro.
    iFrame.
    iSplitL; cbn; trivial.
    iApply (wp_value _ _ (fun v => match v with | MkVal _ δ' v' => Q v' δ' end) (MkTm δ1 (stm_lit _ (eval e0 δ1)))).
    by iApply "PQ".
  Qed.

  Lemma wp_compat_fail {Γ τ} {s} {δ} {Q : Val Γ τ -> iProp Σ} :
    (⊢ WP (MkTm δ (stm_fail _ s)) ?{{ v, Q v }})%I.
  Proof.
    rewrite wp_unfold.
    iIntros (σ ks1 ks n) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 σ2 efs) "%".
    remember (MkTm δ (fail s)) as s1.
    destruct H0.
    inversion Heqs1.
    destruct H0; inversion H3.
  Qed.

  Lemma wp_compat_block {Γ Δ} {τ : Ty} {δ : CStore Γ}
        (δΔ : CStore Δ) (k : Stm (Γ ▻▻ Δ) τ) (Q : Val Γ τ -> iProp Σ) :
    ⊢ (WP (MkTm (δ ►► δΔ) k) ?{{ v, match v with MkVal _ δ' v => Q (MkVal _ (env_drop Δ δ') v) end }} -∗
          WP (MkTm δ (stm_block δΔ k)) ?{{ v, Q v }})%I.
  Proof.
    iRevert (δ δΔ k Q).
    iLöb as "IH".
    iIntros (δ δΔ k Q) "wpk".
    rewrite ?wp_unfold.
    cbn.
    iIntros (σ ks1 ks n) "state_inv".
    remember (language.to_val (MkTm (δ ►► δΔ) k)) as kval.
    destruct kval.
    - rewrite /wp_pre.
      rewrite <- Heqkval.
      destruct v.
      assert (eqk := of_to_val _ (eq_sym Heqkval)).
      inversion eqk.
      rewrite <-?H2 in *; clear H2.
      iMod "wpk" as "H".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iSplitR; [trivial|].
      iModIntro.
      iIntros (e2 σ2 efs) "%".
      iModIntro. iModIntro.
      iMod "Hclose" as "e".
      iDestruct "e" as "_".
      iModIntro.
      dependent elimination H0.
      dependent elimination s; subst δ0.
      + rewrite env_drop_cat.
        iFrame.
        iSplitL; [|trivial].
        by iApply wp_value.
      + revert s4.
        generalize (δ1 ►► δΔ2) as δ1'.
        generalize (δ'0 ►► δΔ') as δ0'.
        intros δ0' δ1' step.
        dependent elimination step.
    - rewrite /wp_pre.
      rewrite <-Heqkval.
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro.
      iSplitR; [trivial|].
      iIntros (e2 σ2 efs2) "%".
      dependent elimination H0.
      dependent elimination s.
      + inversion Heqkval.
      + iModIntro. iModIntro.
        iMod "Hclose" as "_".
        iFrame.
        iModIntro.
        iSplitL; [|trivial].
        iApply wp_compat_fail.
      + iMod "Hclose" as "_".
        cbn.
        iMod ("wpk" $! (γ1 , μ1) ks1 ks n with "state_inv") as "[% wpk]".
        iMod ("wpk" $! _ _ _ (mk_prim_step s4)) as "wpk".
        iModIntro. iModIntro.
        iMod "wpk" as "[Hregs [wpk' _]]".
        iModIntro.
        iFrame.
        iSplitL; [|trivial].
        iApply "IH".
        iFrame.
  Qed.

  Lemma iris_rule_stm_let {Γ} (δ : CStore Γ)
        (x : 𝑿) (σ τ : Ty) (s : Stm Γ σ) (k : Stm (ctx_snoc Γ (x , σ)) τ)
        (P : iProp Σ) (Q : Lit σ -> CStore Γ -> iProp Σ)
        (R : Lit τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ P s Q -∗
                     (∀ (v : Lit σ) (δ' : CStore Γ),
                         semTriple (env_snoc δ' (x,σ) v) (Q v δ') k (fun v δ'' => R v (env_tail δ'')) ) -∗
                     semTriple δ P (let: x := s in k) R).
  Proof.
    iIntros "trips tripk P".
    iPoseProof ("trips" with "P") as "wpv".
    iRevert (s δ) "wpv".
    iLöb as "IH".
    iIntros (s δ) "wpv".
    rewrite (wp_unfold _ _ (MkTm _ (stm_let _ _ _ k))).
    iIntros ([regs μ] ks1 ks n) "state_inv".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 [regs2 μ2] efs) "%".
    unfold language.prim_step in H0; cbn in H0.
    dependent elimination H0.
    dependent elimination s0.
    cbn.
    + rewrite wp_unfold. cbn.
      iModIntro. iModIntro.
      iMod "Hclose" as "_".
      iMod "wpv".
      iPoseProof ("tripk" $! v _ with "wpv") as "wpk".
      iModIntro.
      iFrame; iSplitL; auto.
      by iApply (wp_compat_block (env_snoc env_nil (x0 , σ0) v) _ (fun v0 => match v0 with | MkVal _ δ' v1 => R v1 δ' end )).
    + iModIntro. iModIntro.
      iMod "Hclose" as "_".
      cbn.
      iFrame; iSplitL; auto.
      by iApply wp_compat_fail.
    + cbn.
      rewrite wp_unfold.
      unfold wp_pre.
      rewrite (val_stuck (MkTm δ1 s1) _ [] _ _ [] (mk_prim_step s3)).
      iSpecialize ("wpv" $! (γ1 , μ1) nil nil n with "state_inv").
      iMod "Hclose" as "_".
      iMod "wpv" as "[_ wpv]".
      iSpecialize ("wpv" $! (MkTm δ' s') _ nil (mk_prim_step s3)).
      iMod "wpv" as "wpv".
      iModIntro. iModIntro.
      iMod "wpv" as "[Hregs [wps _]]".
      iModIntro.
      iFrame.
      iSpecialize ("IH" with "tripk").
      iSpecialize ("IH" with "wps").
      iFrame.
  Qed.

  Lemma iris_rule_stm_let_forwards {Γ} (δ : CStore Γ)
        (x : 𝑿) (σ τ : Ty) (s : Stm Γ σ) (k : Stm (ctx_snoc Γ (x , σ)) τ)
        (P : iProp Σ) (Q : Lit σ -> CStore Γ -> iProp Σ)
        (R : Lit τ -> CStore (Γ ▻ (x,σ)) -> iProp Σ) :
        ⊢ (semTriple δ P s Q -∗
                     (∀ (v : Lit σ) (δ' : CStore Γ), semTriple (env_snoc δ' (x,σ) v) (Q v δ') k R ) -∗
                     semTriple δ P (let: x := s in k) (fun v δ' => ∃ v__let, R v (env_snoc δ' (x,σ) v__let)))%I.
  Proof.
    (* proof should be generalizable beyond Iris model? *)
    iIntros "trips tripk".
    iApply (iris_rule_stm_let δ s k P Q (fun v δ' => ∃ v__let, R v (env_snoc δ' (x,σ) v__let))%I with "trips").
    iIntros (v δ') "Qv".
    iPoseProof ("tripk" with "Qv") as "wpk".
    iApply (wp_mono with "wpk").
    iIntros (v') "Rv".
    destruct v'.
    iExists (env_head δ0).
    by dependent elimination δ0.
  Qed.

  Lemma iris_rule_stm_block {Γ} (δ : CStore Γ)
        (Δ : PCtx) (δΔ : CStore Δ)
        (τ : Ty) (k : Stm (ctx_cat Γ Δ) τ)
        (P : iProp Σ) (R : Lit τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple (δ ►► δΔ) P k (fun v δ'' => R v (env_drop Δ δ'')) -∗
                   semTriple δ P (stm_block δΔ k) R)%I.
  Proof.
    iIntros "tripk P".
    iPoseProof ("tripk" with "P") as "wpk".
    by iApply (wp_compat_block δΔ k (fun v => match v with | MkVal _ δ' v' => R v' δ' end) with "wpk").
  Qed.

  Lemma iris_rule_stm_if {Γ} (δ : CStore Γ)
        (τ : Ty) (e : Exp Γ ty_bool) (s1 s2 : Stm Γ τ)
        (P : iProp Σ) (Q : Lit τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ (P ∧ ⌜ eval e δ = true ⌝) s1 Q -∗
                   semTriple δ (P ∧ ⌜ eval e δ = false ⌝) s2 Q -∗
                   semTriple δ P (stm_if e s1 s2) Q)%I.
  Proof.
    iIntros "trips1 trips2 P".
    rewrite wp_unfold.
    iIntros (σ ks1 ks n) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e2 σ2 efs) "%".
    unfold language.prim_step in H0; cbn in H0.
    dependent elimination H0.
    dependent elimination s.
    iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro; iFrame.
    iSplitL; [|trivial].
    destruct (eval e1 δ1).
    - iApply "trips1".
      by iFrame.
    - iApply "trips2".
      by iFrame.
  Qed.

  Lemma iris_rule_stm_if_backwards {Γ} (δ : CStore Γ)
        (τ : Ty) (e : Exp Γ ty_bool) (s1 s2 : Stm Γ τ)
        (P1 P2 : iProp Σ) (Q : Lit τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ P1 s1 Q -∗ semTriple δ P2 s2 Q -∗
        semTriple δ (bi_impl (⌜ eval e δ = true ⌝) P1 ∧
                     bi_impl (⌜ eval e δ = false ⌝) P2)%I
            (stm_if e s1 s2) Q)%I.
  Proof.
    (* generalize proof to non-iris models *)
    iIntros "trips1 trips2".
    iApply (iris_rule_stm_if δ e s1 s2
                             ((⌜ eval e δ = true ⌝ → P1) ∧ (⌜ eval e δ = false ⌝ → P2))%I Q with "[trips1]").
    - iIntros "[P' %]".
      iApply "trips1".
      by iApply (bi.and_elim_l with "P'").
    - iIntros "[P' %]".
      iApply "trips2".
      by iApply (bi.and_elim_r with "P'").
  Qed.

  Lemma iris_rule_stm_seq {Γ} (δ : CStore Γ)
        (τ : Ty) (s1 : Stm Γ τ) (σ : Ty) (s2 : Stm Γ σ)
        (P : iProp Σ) (Q : CStore Γ -> iProp Σ) (R : Lit σ -> CStore Γ -> iProp Σ) :
    ⊢ (semTriple δ P s1 (fun _ => Q) -∗
                 (∀ δ', semTriple δ' (Q δ') s2 R) -∗
                 semTriple δ P (s1 ;; s2) R)%I.
  Proof.
    iIntros "trips1 trips2 P".
    iPoseProof ("trips1" with "P") as "wps1".
    iRevert (s1 δ) "wps1".
    iLöb as "IH".
    iIntros (s1 δ) "wps1".
    rewrite (wp_unfold _ _ (MkTm _ (stm_seq _ _))).
    iIntros ([regs μ] ks1 ks n) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 σ2 efs) "%".
    unfold language.prim_step in H0; cbn in H0.
    dependent elimination H0.
    dependent elimination s; cbn.
    + rewrite wp_unfold.
      unfold wp_pre.
      rewrite (val_stuck (MkTm δ1 s7) (γ1 , μ1) [] _ _ [] (mk_prim_step s8)).
      iSpecialize ("wps1" $! (γ1 , μ1) nil nil n with "Hregs").
      iMod "Hclose" as "_".
      iMod "wps1" as "[_ wps1]".
      iMod ("wps1" $! (MkTm δ'1 s'0) _ nil (mk_prim_step s8))  as "wps1".
      iModIntro. iModIntro.
      iMod "wps1" as "[Hregs [wps' _]]".
      iFrame.
      iSplitL; [|trivial].
      iModIntro.
      iSpecialize ("IH" with "trips2").
      by iApply "IH".
    + rewrite wp_unfold; cbn.
      iModIntro. iModIntro.
      iMod "Hclose" as "_".
      iMod "wps1" as "wps1".
      iPoseProof ("trips2" $! δ1 with "wps1") as "wps2".
      by iFrame.
    + iModIntro. iModIntro.
      iMod "Hclose" as "_".
      iFrame; iSplitL; auto.
      by iApply wp_compat_fail.
  Qed.

  Lemma iris_rule_stm_assertk {Γ τ} (δ : CStore Γ)
        (e1 : Exp Γ ty_bool) (e2 : Exp Γ ty_string) (k : Stm Γ τ)
                      (P : iProp Σ) (Q : Lit τ -> CStore Γ -> iProp Σ) :
    ⊢ (semTriple δ (P ∧ ⌜ eval e1 δ = true ⌝) k Q -∗
       semTriple δ P (stm_assertk e1 e2 k) Q)%I.
  Proof.
    iIntros "tripk P".
    rewrite wp_unfold.
    iIntros (σ ks1 ks n) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e3 σ2 efs) "%".
    unfold language.prim_step in H0; cbn in H0.
    dependent elimination H0.
    dependent elimination s.
    iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro; iFrame.
    iSplitL; [|trivial].
    destruct (eval e3 δ1) eqn:Heqc.
    - iApply "tripk".
      by iFrame.
    - iApply wp_compat_fail.
  Qed.

  Lemma iris_rule_stm_fail {Γ} (δ : CStore Γ)
        (τ : Ty) (s : Lit ty_string) :
        forall (Q : Lit τ -> CStore Γ -> iProp Σ),
          ⊢ semTriple δ True%I (stm_fail τ s) Q.
  Proof.
    iIntros (Q) "_".
    iApply wp_compat_fail.
  Qed.

  Lemma iris_rule_stm_match_list {Γ} (δ : CStore Γ)
        {σ τ : Ty} (e : Exp Γ (ty_list σ)) (alt_nil : Stm Γ τ)
        (xh xt : 𝑿) (alt_cons : Stm (ctx_snoc (ctx_snoc Γ (xh , σ)) (xt , ty_list σ)) τ)
        (P : iProp Σ) (Q : Lit τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ (P ∧ bi_pure (eval e δ = [])) alt_nil (fun v' δ' => Q v' δ') -∗
                     (∀ v vs, semTriple (env_snoc (env_snoc δ (xh,σ) v) (xt,ty_list σ) vs) (P ∧ bi_pure (eval e δ = cons v vs)) alt_cons (fun v' δ' => Q v' (env_tail (env_tail δ')))) -∗
                     semTriple δ P (stm_match_list e alt_nil xh xt alt_cons) Q)%I.
  Proof.
    iIntros "tripnil tripcons P".
    rewrite wp_unfold.
    iIntros (σ1 ks1 ks n) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e3 σ2 efs) "%".
    unfold language.prim_step in H0; cbn in H0.
    dependent elimination H0.
    dependent elimination s.
    remember (eval e4 δ1) as scrutinee.
    destruct scrutinee as [|l ls].
    - iModIntro. iModIntro.
      iMod "Hclose" as "_".
      iModIntro. iFrame.
      iSplitL; [|trivial].
      iApply "tripnil".
      by iFrame.
    - iModIntro. iModIntro.
      iMod "Hclose" as "_".
      iModIntro.
      iFrame.
      iSplitL; [|trivial].
      iApply (wp_compat_block (env_snoc (env_snoc env_nil (pair xh0 σ6) l) (pair xt0 (ty_list σ6)) ls)).
      iApply "tripcons".
      by iFrame.
  Qed.

  Lemma iris_rule_stm_match_sum {Γ} (δ : CStore Γ)
        (σinl σinr τ : Ty) (e : Exp Γ (ty_sum σinl σinr))
                         (xinl : 𝑿) (alt_inl : Stm (ctx_snoc Γ (xinl , σinl)) τ)
                         (xinr : 𝑿) (alt_inr : Stm (ctx_snoc Γ (xinr , σinr)) τ)
                         (P : iProp Σ)
                         (Q : Lit τ -> CStore Γ -> iProp Σ) :
        ⊢ ((∀ v, semTriple (env_snoc δ (xinl,σinl) v) (P ∧ ⌜ eval e δ = inl v ⌝) alt_inl (fun v' δ' => Q v' (env_tail δ'))) -∗
           (∀ v, semTriple (env_snoc δ (xinr,σinr) v) (P ∧ ⌜ eval e δ = inr v ⌝) alt_inr (fun v' δ' => Q v' (env_tail δ'))) -∗
        semTriple δ P (stm_match_sum e xinl alt_inl xinr alt_inr) Q)%I.
  Proof.
    iIntros "tripinl tripinr P".
    rewrite wp_unfold.
    iIntros (σ1 ks1 ks n) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e2 σ2 efs) "%".
    unfold language.prim_step in H0; cbn in H0.
    dependent elimination H0.
    dependent elimination s.
    remember (eval e5 δ1) as scrutinee.
    destruct scrutinee as [v1|v2].
    - iModIntro. iModIntro.
      iMod "Hclose" as "_".
      iModIntro. iFrame.
      iSplitL; [|trivial].
      iApply (wp_compat_block (env_snoc env_nil (pair xinl0 σinl0) v1)).
      iApply ("tripinl" $! v1).
      by iFrame.
    - iModIntro. iModIntro.
      iMod "Hclose" as "_".
      iModIntro. iFrame.
      iSplitL; [|trivial].
      iApply (wp_compat_block (env_snoc env_nil (pair xinr0 σinr0) v2)).
      iApply ("tripinr" $! v2).
      by iFrame.
  Qed.

  Lemma iris_rule_stm_match_prod {Γ} (δ : CStore Γ)
        {σ1 σ2 τ : Ty} (e : Exp Γ (ty_prod σ1 σ2))
        (xl xr : 𝑿) (rhs : Stm (ctx_snoc (ctx_snoc Γ (xl , σ1)) (xr , σ2)) τ)
        (P : iProp Σ) (Q : Lit τ -> CStore Γ -> iProp Σ) :
        ⊢ ((∀ vl vr,
            semTriple (env_snoc (env_snoc δ (xl, σ1) vl) (xr, σ2) vr)
              (P ∧ bi_pure (eval e δ = (vl,vr))) rhs (fun v δ' => Q v (env_tail (env_tail δ')))) -∗
          semTriple δ P (stm_match_prod e xl xr rhs) Q)%I.
  Proof.
    iIntros "trippair P".
    rewrite wp_unfold.
    iIntros (σ ks1 ks n) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e2 σ' efs) "%".
    unfold language.prim_step in H0; cbn in H0.
    dependent elimination H0.
    dependent elimination s.
    remember (eval e6 δ1) as scrutinee.
    destruct scrutinee as [v1 v2].
    iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro. iFrame.
    iSplitL; [|trivial].
    iApply (wp_compat_block (env_snoc (env_snoc env_nil (pair xl0 σ8) v1) (pair xr0 σ9) v2)).
    iApply ("trippair" $! v1 v2).
    by iFrame.
  Qed.

  Lemma iris_rule_stm_match_enum {Γ} (δ : CStore Γ)
        {E : 𝑬} (e : Exp Γ (ty_enum E)) {τ : Ty}
        (alts : forall (K : 𝑬𝑲 E), Stm Γ τ)
        (P : iProp Σ) (Q : Lit τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ P (alts (eval e δ)) Q -∗
          semTriple δ P (stm_match_enum E e alts) Q)%I.
  Proof.
    iIntros "tripalt P".
    rewrite wp_unfold.
    iIntros (σ ks1 ks n) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e2 σ' efs) "%".
    unfold language.prim_step in H0; cbn in H0.
    dependent elimination H0.
    dependent elimination s.
    iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro. iFrame.
    iSplitL; [|trivial].
    by iApply "tripalt".
  Qed.

  Lemma iris_rule_stm_match_tuple {Γ} (δ : CStore Γ)
        {σs : Ctx Ty} {Δ : PCtx} (e : Exp Γ (ty_tuple σs))
        (p : TuplePat σs Δ) {τ : Ty} (rhs : Stm (ctx_cat Γ Δ) τ)
        (P : iProp Σ) (Q : Lit τ -> CStore Γ -> iProp Σ) :
    ⊢ ((semTriple (env_cat δ (tuple_pattern_match_lit p (eval e δ))) P rhs (fun v δ' => Q v (env_drop Δ δ'))) -∗
       semTriple δ P (stm_match_tuple e p rhs) Q)%I.
  Proof.
    iIntros "triptup P".
    rewrite wp_unfold.
    iIntros (σ ks1 ks n) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e2 σ' efs) "%".
    unfold language.prim_step in H0; cbn in H0.
    dependent elimination H0.
    dependent elimination s.
    iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro. iFrame.
    iSplitL; [|trivial].
    iApply (wp_compat_block (tuple_pattern_match_lit p0 (eval e8 δ1))).
    by iApply "triptup".
  Qed.

  Lemma iris_rule_stm_match_union {Γ} (δ : CStore Γ)
        {U : 𝑼} (e : Exp Γ (ty_union U)) {σ τ : Ty}
        (alt__Δ : forall (K : 𝑼𝑲 U), PCtx)
        (alt__p : forall (K : 𝑼𝑲 U), Pattern (alt__Δ K) (𝑼𝑲_Ty K))
        (alt__r : forall (K : 𝑼𝑲 U), Stm (ctx_cat Γ (alt__Δ K)) τ)
        (P : iProp Σ) (Q : Lit τ -> CStore Γ -> iProp Σ) :
        ⊢ ((∀ (K : 𝑼𝑲 U) (v : Lit (𝑼𝑲_Ty K)),
               semTriple (env_cat δ (pattern_match_lit (alt__p K) v)) (P ∧ bi_pure (eval e δ = 𝑼_fold (existT K v))) (alt__r K) (fun v δ' => Q v (env_drop (alt__Δ K) δ'))) -∗
               semTriple δ P (stm_match_union U e alt__p alt__r) Q
          )%I.
  Proof.
    iIntros "tripunion P".
    rewrite wp_unfold.
    iIntros (σ1 ks1 ks n) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e2 σ2 efs) "%".
    unfold language.prim_step in H0; cbn in H0.
    dependent elimination H0.
    dependent elimination s.
    iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro. iFrame.
    iSplitL; [|trivial].
    remember (𝑼_unfold (eval e9 δ1)) as scrutinee.
    destruct scrutinee as [K v].
    iApply (wp_compat_block (pattern_match_lit (alt__pat K) v)).
    iSpecialize ("tripunion" $! K v).
    rewrite Heqscrutinee.
    rewrite 𝑼_fold_unfold.
    iApply "tripunion".
    by iFrame.
  Qed.

  Lemma iris_rule_stm_match_record {Γ} (δ : CStore Γ)
        {R : 𝑹} {Δ : PCtx} (e : Exp Γ (ty_record R))
        (p : RecordPat (𝑹𝑭_Ty R) Δ) {τ : Ty} (rhs : Stm (ctx_cat Γ Δ) τ)
        (P : iProp Σ) (Q : Lit τ -> CStore Γ -> iProp Σ) :
        ⊢ ((semTriple (env_cat δ (record_pattern_match_lit p (eval e δ))) P rhs (fun v δ' => Q v (env_drop Δ δ'))) -∗
        semTriple δ P (stm_match_record R e p rhs) Q)%I.
  Proof.
    iIntros "triprec P".
    rewrite wp_unfold.
    iIntros (σ1 ks1 ks n) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e2 σ2 efs) "%".
    unfold language.prim_step in H0; cbn in H0.
    dependent elimination H0.
    dependent elimination s.
    iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro. iFrame.
    iSplitL; [|trivial].
    iApply (wp_compat_block (record_pattern_match_lit p1 (eval e10 δ1))).
    by iApply "triprec".
  Qed.

  Lemma iris_rule_stm_read_register {Γ} (δ : CStore Γ)
        {σ : Ty} (r : 𝑹𝑬𝑮 σ) (v : Lit σ) :
        ⊢ (semTriple δ (lptsreg r v) (stm_read_register r) (fun v' δ' => (⌜ δ' = δ ⌝ ∧ ⌜ v' = v ⌝) ∧ lptsreg r v))%I.
  Proof.
    iIntros "Hreg".
    iApply wp_mono; [| iApply (rule_stm_read_register with "Hreg") ].
    iIntros ([δ' v']) "[Hreg %]".
    inversion H0.
    by iFrame.
  Qed.

  Lemma iris_rule_stm_write_register {Γ} (δ : CStore Γ)
        {σ : Ty} (r : 𝑹𝑬𝑮 σ) (w : Exp Γ σ)
                              (Q : Lit σ -> CStore Γ -> iProp Σ)
                              (v : Lit σ) :
        ⊢ semTriple δ (lptsreg r v) (stm_write_register r w)
                  (fun v' δ' => (bi_pure (δ' = δ) ∧ bi_pure (v' = eval w δ)) ∧ lptsreg r v')%I.
  Proof.
    iIntros "Hreg".
    iApply wp_mono; [|iApply (rule_stm_write_register with "Hreg")].
    iIntros (v') "[Hreg %]".
    rewrite H0.
    by iFrame.
  Qed.

  Lemma iris_rule_stm_assign_forwards {Γ} (δ : CStore Γ)
        (x : 𝑿) (σ : Ty) (xIn : (x,σ) ∈ Γ) (s : Stm Γ σ)
        (P : iProp Σ) (R : Lit σ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ P s R -∗
                     semTriple δ P (stm_assign x s) (fun v__new δ' => ∃ v__old, R v__new (@env_update _ _ _ δ' (x , _)  _ v__old) ∧ bi_pure (env_lookup δ' xIn = v__new)))%I.
  Proof.
    iIntros "trips P".
    iPoseProof ("trips" with "P") as "wpv".
    iRevert (s δ) "wpv".
    iLöb as "IH".
    iIntros (s δ) "wpv".
    rewrite (wp_unfold _ _ (MkTm _ (stm_assign _ s))).
    iIntros ([regs μ] ks1 ks n) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 [regs2 μ2] efs) "%".
    unfold language.prim_step in H0; cbn in H0.
    dependent elimination H0.
    dependent elimination s0.
    cbn.
    + rewrite wp_unfold; cbn.
      iModIntro. iModIntro.
      iMod "Hclose" as "_".
      iMod "wpv" as "wpv".
      iModIntro.
      iFrame.
      iSplitL; [|trivial].
      iApply wp_value.
      cbn.
      iExists (env_lookup δ1 xInΓ).
      rewrite env_update_update env_update_lookup env_lookup_update.
      by iFrame.
    + iModIntro. iModIntro.
      iMod "Hclose" as "_".
      cbn.
      iFrame; iSplitL; auto.
      by iApply wp_compat_fail.
    + rewrite wp_unfold.
      unfold wp_pre.
      rewrite (val_stuck (MkTm δ1 s13) _ [] _ _ [] (mk_prim_step s14)).
      iSpecialize ("wpv" $! _ nil nil n with "Hregs").
      iMod "Hclose".
      iMod "wpv" as "[_ wpv]".
      iSpecialize ("wpv" $! _ _ nil (mk_prim_step s14)).
      iMod "wpv" as "wpv".
      iModIntro. iModIntro.
      iMod "wpv" as "[Hregs [wps _]]".
      iModIntro.
      iFrame.
      iSplitL; [|trivial].
      by iApply "IH".
  Qed.

  Lemma iris_rule_stm_assign_backwards {Γ} (δ : CStore Γ)
        (x : 𝑿) (σ : Ty) (xIn : (x,σ) ∈ Γ) (s : Stm Γ σ)
        (P : iProp Σ) (R : Lit σ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ P s (fun v δ' => R v (@env_update _ _ _ δ' (x , _) _ v)) -∗
           semTriple δ P (stm_assign x s) R)%I.
  Proof.
    iIntros "trips P".
    iPoseProof (iris_rule_stm_assign_forwards _ with "trips P") as "wpas".
    iApply (wp_mono with "wpas").
    iIntros ([δ' v']) "Rv".
    iDestruct "Rv" as (v__old) "[Rv %]".
    rewrite <-H0.
    by rewrite env_update_update env_update_lookup.
  Qed.


  Definition ValidContractEnvSem (cenv : SepContractEnv) : iProp Σ :=
    (∀ σs σ (f : 𝑭 σs σ),
      match cenv σs σ f with
      | Some (MkSepContract _ _ ctxΣ θΔ pre result post) =>
        ∀ (ι : SymInstance ctxΣ),
          semTriple (inst θΔ ι) (interpret_assertion (L:=iProp Σ) pre ι) (Pi f)
                    (fun v δ' => interpret_assertion post (env_snoc ι (result , σ) v))
      | None => True
      end)%I.

  Lemma wp_compat_call_frame {Γ Δ} {τ : Ty} {δ : CStore Γ}
        (δΔ : CStore Δ) (s : Stm Δ τ) (Q : Val Γ τ -> iProp Σ) :
    ⊢ (WP (MkTm δΔ s) ?{{ v, match v with MkVal _ δ' v => Q (MkVal _ δ v) end }} -∗
          WP (MkTm δ (stm_call_frame δΔ s)) ?{{ v, Q v }})%I.
  Proof.
    iRevert (δ δΔ s Q).
    iLöb as "IH".
    iIntros (δ δΔ s Q) "wpk".
    rewrite ?wp_unfold.
    cbn.
    iIntros (σ ks1 ks n) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; first trivial.
    iIntros (e2 σ2 efs) "%".
    dependent elimination H0.
    dependent elimination s0.
    - iMod "Hclose" as "_".
      rewrite {1}/wp_pre.
      rewrite (val_stuck (MkTm δΔ3 s9) (γ1 , μ1) [] _ _ [] (mk_prim_step s10)).
      iMod ("wpk" $! (γ1 , μ1) ks1 ks n with "Hregs") as "[% wpk]".
      iMod ("wpk" $! _ _ _ (mk_prim_step s10)) as "wpk".
      iModIntro. iModIntro.
      iMod "wpk" as "[Hregs [wpk' _]]".
      iModIntro.
      iFrame.
      iSplitL; last trivial.
      iApply "IH".
      iFrame.
    - cbn.
      iModIntro. iModIntro.
      iMod "Hclose" as "_".
      iMod "wpk" as "Qv".
      iModIntro.
      iFrame.
      iSplitL; last trivial.
      by iApply wp_value.
    - iModIntro. iModIntro.
      iMod "Hclose" as "_".
      iFrame.
      iModIntro.
      iSplitL; [|trivial].
      iApply wp_compat_fail.
  Qed.

  Lemma iris_rule_stm_call_forwards {Γ} (δ : CStore Γ)
        {Δ σ} (f : 𝑭 Δ σ) (c : SepContract Δ σ) (es : NamedEnv (Exp Γ) Δ)
        (P : iProp Σ)
        (Q : Lit σ -> iProp Σ) :
        CEnv f = Some c ->
        CTriple (evals es δ) P Q c ->
        (⊢ ▷ ValidContractEnvSem CEnv -∗
           semTriple δ P (stm_call f es) (fun v δ' => Q v ∧ bi_pure (δ = δ')))%I.
  Proof.
    iIntros (ceq ctrip) "cenv P".
    rewrite wp_unfold.
    iIntros ([regs μ] ks1 ks n) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 [regs2 μ2] efs) "%".
    unfold language.prim_step in H0; cbn in H0.
    dependent elimination H0.
    dependent elimination s.
    iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro.
    iFrame.
    iSplitL; [|trivial].
    destruct ctrip.
    iPoseProof (H1 with "P") as "[fr req]".
    iApply wp_compat_call_frame.
    rewrite H0.
    iApply (wp_mono _ _ _ (fun v => frame ∗ match v with
                                            | MkVal _ _ v => interpret_assertion ens (env_snoc ι (result,σ) v)
                                            end)%I).
    - intros [δ' v]; cbn.
      iIntros "[fr ens]".
      iSplitL; [|trivial].
      iApply (H2 v).
      by iFrame.
    - iSpecialize ("cenv" $! _ _ f0).
      rewrite ceq.
      iSpecialize ("cenv" $! ι with "req").
      iApply wp_frame_l.
      by iFrame.
  Qed.

  Lemma iris_rule_stm_call_frame {Γ} (δ : CStore Γ)
        (Δ : PCtx) (δΔ : CStore Δ) (τ : Ty) (s : Stm Δ τ)
        (P : iProp Σ) (Q : Lit τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δΔ P s (fun v _ => Q v δ) -∗
           semTriple δ P (stm_call_frame δΔ s) Q)%I.
  Proof.
    iIntros "trips P".
    iSpecialize ("trips" with "P").
    by iApply wp_compat_call_frame.
  Qed.

  Lemma iris_rule_stm_bind {Γ} (δ : CStore Γ)
        {σ τ : Ty} (s : Stm Γ σ) (k : Lit σ -> Stm Γ τ)
        (P : iProp Σ) (Q : Lit σ -> CStore Γ -> iProp Σ)
        (R : Lit τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ P s Q -∗
           (∀ (v__σ : Lit σ) (δ' : CStore Γ),
               semTriple δ' (Q v__σ δ') (k v__σ) R) -∗
           semTriple δ P (stm_bind s k) R)%I.
  Proof.
    iIntros "trips tripk P".
    iPoseProof ("trips" with "P") as "wpv".
    iRevert (s δ) "wpv".
    iLöb as "IH".
    iIntros (s δ) "wpv".
    rewrite (wp_unfold _ _ (MkTm _ (stm_bind _ k))).
    iIntros ([regs μ] ks1 ks n) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 [regs2 μ2] efs) "%".
    unfold language.prim_step in H0; cbn in H0.
    dependent elimination H0.
    dependent elimination s0.
    cbn.
    + rewrite wp_unfold.
      unfold wp_pre.
      rewrite (val_stuck (MkTm δ1 s17) (γ1 , μ1) [] _ _ [] (mk_prim_step s18)).
      iSpecialize ("wpv" $! (γ1 , μ1) nil nil n with "Hregs").
      iMod "Hclose".
      iMod "wpv" as "[_ wpv]".
      iSpecialize ("wpv" $! _ _ nil (mk_prim_step s18)).
      iMod "wpv" as "wpv".
      iModIntro. iModIntro.
      iMod "wpv" as "[Hregs [wps _]]".
      iModIntro.
      iFrame.
      iApply ("IH" with "tripk wps").
    + iModIntro. iModIntro.
      iMod "Hclose" as "_".
      rewrite wp_unfold; cbn.
      iMod "wpv" as "wpv".
      iPoseProof ("tripk" with "wpv") as "wpk".
      iModIntro.
      by iFrame.
    + iModIntro. iModIntro.
      iMod "Hclose" as "_".
      cbn.
      iFrame; iSplitL; auto.
      by iApply wp_compat_fail.
  Qed.

  Lemma iris_rule_stm_call_inline
    {Γ} (δ : CStore Γ)
    {Δ σ} (f : 𝑭 Δ σ) (es : NamedEnv (Exp Γ) Δ) (c : SepContract Δ σ)
    (P : iProp Σ) (Q : Lit σ -> iProp Σ) :
    ⊢ semTriple (evals es δ) P (Pi f) (fun v _ => Q v) -∗
      semTriple δ P (stm_call f es) (fun v δ' => Q v ∧ bi_pure (δ = δ')).
  Proof.
    iIntros "tripbody P".
    rewrite wp_unfold.
    iIntros (σ' ks1 ks n) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e2 σ'' efs) "%".
    cbn in H0.
    dependent elimination H0.
    dependent elimination s.
    iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro. iFrame.
    iSplitL; [|trivial].
    iApply wp_compat_call_frame.
    iApply (wp_mono _ _ _ (fun v => match v with MkVal _ _ v0 => Q v0 end)).
    {
      iIntros ([σ' v]) "Qv".
      by iFrame.
    }
    iApply ("tripbody" with "P").
  Qed.

  Definition ForeignSem :=
    ∀ (Γ : NCtx 𝑿 Ty) (τ : Ty)
      (Δ : NCtx 𝑿 Ty) f (es : NamedEnv (Exp Γ) Δ) (δ : CStore Γ),
      match CEnvEx f with
      | MkSepContract _ _ Σ' θΔ req result ens =>
        forall (ι : SymInstance Σ'),
        evals es δ = inst θΔ ι ->
        ⊢ semTriple δ (interpret_assertion req ι) (stm_foreign f es)
          (fun v δ' => interpret_assertion ens (env_snoc ι (result :: τ) v) ∗ bi_pure (δ' = δ))
      end.

  Lemma iris_rule_stm_foreign
    {Γ} (δ : CStore Γ) {τ} {Δ} (f : 𝑭𝑿 Δ τ) (es : NamedEnv (Exp Γ) Δ)
    (P : iProp Σ) (Q : Lit τ -> CStore Γ -> iProp Σ) :
    ForeignSem ->
    CTriple (evals es δ) P (λ v : Lit τ, Q v δ) (CEnvEx f) ->
    ⊢ semTriple δ P (stm_foreign f es) Q.
  Proof.
    iIntros (extSem ctrip).
    specialize (extSem _ _ _ f es δ).
    revert ctrip extSem.
    generalize (CEnvEx f) as contractF.
    intros contractF ctrip extSem.
    dependent elimination ctrip; cbn in extSem.
    iIntros "P".
    iPoseProof (l with "P") as "[frm pre]".
    iApply (wp_mono _ _ _ (fun v => frame0 ∗ match v with | MkVal _ δ' v => interpret_assertion ens (env_snoc ι (result :: τ) v) ∗ bi_pure (δ' = δ) end)%I).
    - intros v.
      destruct v.
      iIntros "[frame [pre %]]".
      subst.
      iApply l0.
      by iFrame.
    - iApply wp_frame_l.
      iFrame.
      by iApply (extSem ι e).
  Qed.

  Definition ValidLemma {Δ} (lem : Lemma Δ) : Prop :=
    match lem with
      {| lemma_logic_variables := Σ;
         lemma_patterns        := θΔ;
         lemma_precondition    := req;
         lemma_postcondition   := ens;
      |} =>
      forall (ι : SymInstance Σ),
        ⊢ interpret_assertion req ι -∗
          interpret_assertion ens ι
    end.

  Definition LemmaSem : Prop :=
    forall (Δ : NCtx 𝑿 Ty) (l : 𝑳 Δ),
      ValidLemma (LEnv l).

  Lemma iris_rule_stm_lemmak
    {Γ} (δ : CStore Γ) {τ} {Δ} (l : 𝑳 Δ) (es : NamedEnv (Exp Γ) Δ) (k : Stm Γ τ)
    (P Q : iProp Σ) (R : Lit τ -> CStore Γ -> iProp Σ) :
    LemmaSem ->
    LTriple (evals es δ) P Q (LEnv l) ->
    ⊢ semTriple δ Q k R -∗
      semTriple δ P (stm_lemmak l es k) R.
  Proof.
    iIntros (lemSem ltrip).
    specialize (lemSem _ l).
    revert ltrip lemSem.
    generalize (LEnv l) as contractL.
    intros contractL ltrip lemSem.
    dependent elimination ltrip; cbn in lemSem.
    specialize (lemSem ι).
    iIntros "tripk P".
    rewrite wp_unfold.
    iIntros (σ ks1 ks n) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e3 σ2 efs) "%".
    unfold language.prim_step in H0; cbn in H0.
    dependent elimination H0.
    dependent elimination s.
    iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro; iFrame.
    iSplitL; [|trivial].
    iApply "tripk".
    iApply l1.
    iPoseProof (l0 with "P") as "[frm pre]".
    iFrame.
    by iApply lemSem.
  Qed.

  Lemma iris_rule_stm_debugk
    {Γ τ} (δ : CStore Γ) (k : Stm Γ τ)
    (P : iProp Σ) (Q : Lit τ -> CStore Γ -> iProp Σ) :
    ⊢ (semTriple δ P k Q -∗
       semTriple δ P (stm_debugk k) Q)%I.
  Proof.
    iIntros "tripk P".
    rewrite wp_unfold.
    iIntros (σ ks1 ks n) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e3 σ2 efs) "%".
    unfold language.prim_step in H0; cbn in H0.
    dependent elimination H0.
    dependent elimination s.
    iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro; iFrame.
    iSplitL; [|trivial].
    iApply "tripk".
    by iFrame.
  Qed.

  Lemma iris_rule_noop {Γ σ} {δ : CStore Γ}
        {P} {Q : Lit σ -> CStore Γ -> iProp Σ} {s : Stm Γ σ} :
    language.to_val (MkTm δ s) = None ->
    (forall {s' γ γ' μ μ' δ'}, ⟨ γ, μ, δ, s ⟩ ---> ⟨ γ', μ', δ', s' ⟩ ->
                            (γ' = γ) /\ (μ' = μ) /\ (δ' = δ) /\
                            ((exists v, s' = stm_lit _ v) \/ (exists msg, s' = stm_fail _ msg))) ->
    (∀ v, P ={⊤}=∗ Q v δ) -∗
                 semTriple δ P s Q.
  Proof.
    iIntros (Hnv Hnoop) "HPQ HP".
    rewrite wp_unfold.
    unfold wp_pre.
    rewrite Hnv.
    iIntros (σ' ks1 ks n) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; first done.
    iIntros (e2 σ'' efs) "%".
    cbn in H0.
    dependent elimination H0.
    destruct (Hnoop _ _ _ _ _ _ s0) as (-> & -> & -> & [[v ->]|[msg ->]]).
    - do 2 iModIntro.
      iMod "Hclose" as "_".
      iMod ("HPQ" with "HP") as "HQ".
      iModIntro.
      iFrame.
      iSplitL; trivial.
      now iApply wp_value.
    - do 2 iModIntro.
      iMod "Hclose" as "_".
      iModIntro.
      iFrame.
      iSplitL; trivial.
      now iApply wp_compat_fail.
  Qed.

  Lemma sound_stm {Γ} {τ} (s : Stm Γ τ) {δ : CStore Γ}:
    forall (PRE : iProp Σ) (POST : Lit τ -> CStore Γ -> iProp Σ),
      ForeignSem ->
      LemmaSem ->
      δ ⊢ ⦃ PRE ⦄ s ⦃ POST ⦄ ->
      ⊢ (□ ▷ ValidContractEnvSem CEnv -∗
          semTriple δ PRE s POST)%I.
  Proof.
    iIntros (PRE POST extSem lemSem triple) "#vcenv".
    iInduction triple as [x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x] "trips".
    - by iApply iris_rule_consequence.
    - by iApply iris_rule_frame.
    - by iApply iris_rule_pull.
    - by iApply iris_rule_exist.
    - iApply iris_rule_stm_lit.
      by iApply H0.
    - iApply iris_rule_stm_exp.
      by iApply H0.
    - by iApply iris_rule_stm_let.
    - by iApply iris_rule_stm_block.
    - by iApply iris_rule_stm_if.
    - by iApply iris_rule_stm_seq.
    - by iApply iris_rule_stm_assertk.
    - by iApply iris_rule_stm_fail.
    - by iApply iris_rule_stm_match_list.
    - by iApply iris_rule_stm_match_sum.
    - by iApply iris_rule_stm_match_prod.
    - by iApply iris_rule_stm_match_enum.
    - by iApply iris_rule_stm_match_tuple.
    - by iApply iris_rule_stm_match_union.
    - by iApply iris_rule_stm_match_record.
    - by iApply iris_rule_stm_read_register.
    - by iApply iris_rule_stm_write_register.
    - by iApply iris_rule_stm_assign_backwards.
    - by iApply iris_rule_stm_assign_forwards.
    - by iApply iris_rule_stm_call_forwards.
    - by iApply iris_rule_stm_call_inline.
    - by iApply iris_rule_stm_call_frame.
    - by iApply iris_rule_stm_foreign.
    - by iApply iris_rule_stm_lemmak.
    - by iApply iris_rule_stm_bind.
    - by iApply iris_rule_stm_debugk.
  Qed.

  Lemma sound {Γ} {τ} (s : Stm Γ τ) {δ : CStore Γ}:
    ForeignSem -> LemmaSem -> ValidContractEnv CEnv ->
    ⊢ ValidContractEnvSem CEnv.
  Proof.
    intros extSem lemSem vcenv.
    iLöb as "IH".
    iIntros (σs σ f).
    specialize (vcenv σs σ f).
    destruct (CEnv f) as [[]|];[|trivial].
    specialize (vcenv _ eq_refl).
    iIntros (ι).
    iApply (sound_stm extSem lemSem); [|trivial].
    apply (vcenv ι).
  Qed.

  End IrisSoundness.
End IrisSoundness.

Module Adequacy
       (Import termkit : TermKit)
       (Import progkit : ProgramKit termkit)
       (Import assertkit : AssertionKit termkit progkit)
       (Import contractkit : SymbolicContractKit termkit progkit assertkit)
       (Import irisheapkit : IrisHeapKit termkit progkit assertkit contractkit).

  Import CtxNotations.
  Import EnvNotations.

  Module PL := ProgramLogic termkit progkit assertkit contractkit.
  Import PL.

  (* Module IrisRegs := IrisRegisters typekit termkit progkit assertkit contractkit. *)
  (* Import IrisRegs. *)

  Module Snd := IrisSoundness termkit progkit assertkit contractkit irisheapkit.
  Import Snd.

  Definition sailΣ : gFunctors := #[ memΣ ; invΣ ; GFunctor regUR].

  Instance subG_sailPreG {Σ} : subG sailΣ Σ -> sailPreG Σ.
  Proof.
    intros.
    lazymatch goal with
    | H:subG ?xΣ _ |- _ => try unfold xΣ in H
    end.
    repeat match goal with
           | H:subG (gFunctors.app _ _) _ |- _ => apply subG_inv in H; destruct H
           end.
    split; eauto using memΣ_PreG, subG_invΣ.
    solve_inG.
 Qed.

  Definition RegStore_to_map (γ : RegStore) : gmap SomeReg (exclR (leibnizO SomeLit)) :=
    list_to_map (K := SomeReg)
                (fmap (fun x => match x with
                              existT _ r =>
                                pair (existT _ r) (Excl (existT _ (read_register γ r)))
                            end)
                     (finite.enum (sigT 𝑹𝑬𝑮))).

  Lemma RegStore_to_map_Forall (γ : RegStore) :
    map_Forall (K := SomeReg)
      (fun reg v => match reg with | existT _ reg => Excl (existT _ (read_register γ reg)) = v end)
      (RegStore_to_map γ).
  Proof.
    eapply map_Forall_lookup_2.
    intros [σ r] x eq.
    unfold RegStore_to_map in eq.
    remember (list_to_map _ !! _) as o in eq.
    destruct o; inversion eq; subst.
    assert (eq' := eq_sym Heqo).
    rewrite <-elem_of_list_to_map in eq'.
    - eapply elem_of_list_fmap_2 in eq'.
      destruct eq' as ([σ' r'] & eq2 & eq3).
      now inversion eq2.
    - rewrite <-list_fmap_compose.
      rewrite (list_fmap_ext (compose fst (λ x : {H : Ty & 𝑹𝑬𝑮 H},
          let (x0, r0) := x in (existT x0 r0 :: Excl (existT x0 (read_register γ r0)))%ctx)) id _ _ _ eq_refl).
      + rewrite list_fmap_id.
        eapply finite.NoDup_enum.
      + now intros [σ' r'].
  Qed.

  Lemma RegStore_to_map_valid (γ : RegStore) :
    valid (RegStore_to_map γ).
  Proof.
    intros i.
    cut (exists v, RegStore_to_map γ !! i = Some (Excl v)).
    - intros [v eq].
      now rewrite eq.
    - destruct i as [σ r].
      exists (existT _ (read_register γ r)).
      eapply elem_of_list_to_map_1'.
      + intros y eq.
        eapply elem_of_list_fmap_2 in eq.
        destruct eq as ([σ2 r2] & eq1 & eq2).
        now inversion eq1.
      + refine (elem_of_list_fmap_1 _ _ (existT _ r) _).
        eapply finite.elem_of_enum.
  Qed.

  Lemma steps_to_erased {σ Γ γ μ δ} (s : Stm Γ σ) {γ' μ' δ' s'}:
    ⟨ γ, μ, δ, s ⟩ --->* ⟨ γ', μ', δ', s' ⟩ ->
    rtc erased_step (cons (MkTm δ s) nil :: (γ :: μ))%ctx (cons (MkTm δ' s') nil :: (γ' :: μ'))%ctx.
  Proof.
    induction 1; first done.
    refine (rtc_l _ _ _ _ _ IHSteps).
    exists nil.
    refine (step_atomic _ _ _ _ _ nil nil eq_refl eq_refl _).
    by eapply mk_prim_step.
  Qed.

  Lemma own_RegStore_to_map_reg_pointsTos `{sailRegG Σ'} {γ : RegStore} {l : list (sigT 𝑹𝑬𝑮)} :
    NoDup l ->
    ⊢ own reg_gv_name (◯ list_to_map (K := SomeReg)
                         (fmap (fun x => match x with existT _ r =>
                                                     pair (existT _ r) (Excl (existT _ (read_register γ r)))
                                      end) l)) -∗
      [∗ list] x ∈ l,
        let (x0, r) := (x : sigT 𝑹𝑬𝑮) in reg_pointsTo r (read_register γ r).
    Proof.
      iIntros (nodups) "Hregs".
      iInduction l as [|[x r]] "IH".
      - now iFrame.
      - cbn.
        rewrite (insert_singleton_op (A := exclR (leibnizO SomeLit)) (list_to_map (_ <$> l))  (existT x r) (Excl (existT _ (read_register γ r)))).
        rewrite auth_frag_op.
        iPoseProof (own_op with "Hregs") as "[Hreg Hregs]".
        iFrame.
        iApply "IH".
        + iPureIntro.
          refine (NoDup_cons_1_2 (existT x r) l nodups).
        + iFrame.
        + destruct (proj1 (NoDup_cons (existT x r) _) nodups) as [notin _].
          refine (not_elem_of_list_to_map_1 _ (existT x r) _).
          rewrite <-list_fmap_compose.
          rewrite (list_fmap_ext (compose fst (λ x : {H : Ty & 𝑹𝑬𝑮 H},
                                                  let (x0, r0) := x in (existT x0 r0 :: Excl (existT x0 (read_register γ r0)))%ctx)) id _ _ _ eq_refl).
          now rewrite list_fmap_id.
          now intros [σ2 r2].
    Qed.

  Lemma adequacy {Γ σ} (s : Stm Γ σ) {γ γ'} {μ μ'}
        {δ δ' : CStore Γ} {s' : Stm Γ σ} {Q : Lit σ -> Prop} :
    ⟨ γ, μ, δ, s ⟩ --->* ⟨ γ', μ', δ', s' ⟩ -> Final s' ->
    (forall `{sailG Σ'},
        ⊢ semTriple (Σ := Σ') δ
          (mem_res sailG_memG μ ∗
           [∗ list] _ ↦ x ∈ finite.enum (sigT 𝑹𝑬𝑮),
              match x with | existT _ r => reg_pointsTo r (read_register γ r) end
          )%I s (fun v δ' => bi_pure (Q v)))%I ->
    ResultOrFail s' Q.
  Proof.
    intros steps fins trips.
    cut (adequate MaybeStuck (MkTm δ s) (γ,μ)
             (λ (v : val (microsail_lang Γ σ)) (_ : state (microsail_lang Γ σ)),
                (λ v0 : val (microsail_lang Γ σ), match v0 with
                                                  | MkVal _ _ v' => Q v'
                                                  end) v)).
    - destruct s'; cbn in fins; destruct fins; last done.
      intros adeq.
      apply (adequate_result MaybeStuck (MkTm δ s) (γ , μ) (fun v _ => match v with | MkVal _ δ' v' => Q v' end) adeq nil (γ' , μ') (MkVal _ δ' l)).
      by apply steps_to_erased.
    - constructor; last done.
      intros t2 σ2 [δ2 v2] eval.
      assert (eq := RegStore_to_map_Forall γ).
      assert (regsmapv := RegStore_to_map_valid γ).
      pose proof (wp_adequacy sailΣ (microsail_lang Γ σ) MaybeStuck (MkTm δ s) (γ , μ) (fun v => match v with | MkVal _ δ' v' => Q v' end)) as adeq.
      refine (adequate_result _ _ _ _ (adeq _) _ _ _ eval); clear adeq.
      iIntros (Hinv κs) "".
      iMod (own_alloc ((● RegStore_to_map γ ⋅ ◯ RegStore_to_map γ ) : regUR)) as (spec_name) "[Hs1 Hs2]";
        first by apply auth_both_valid.
      pose proof (memΣ_PreG (Σ := sailΣ) _) as mPG.
      iMod (mem_inv_init μ mPG) as (memG) "[Hmem Rmem]".
      iModIntro.
      iExists (fun σ _ => regs_inv (H := (SailRegG _ spec_name)) (σ.1) ∗ mem_inv memG (σ.2))%I.
      iExists _.
      iSplitR "Hs2 Rmem".
      * iSplitL "Hs1".
        + iExists (RegStore_to_map γ).
          by iFrame.
        + iFrame.
      * iPoseProof (trips sailΣ (SailG Hinv (SailRegG reg_pre_inG spec_name) memG) with "[Rmem Hs2]") as "trips'".
        + iFrame.
          unfold RegStore_to_map.
          iApply (own_RegStore_to_map_reg_pointsTos (H := SailRegG reg_pre_inG spec_name)(γ := γ) (l := finite.enum (sigT 𝑹𝑬𝑮)) with "Hs2").
          Locate NoDup.
          eapply finite.NoDup_enum.
        + iApply (wp_mono with "trips'").
          by iIntros ([δ3 v]).
  Qed.
End Adequacy.
