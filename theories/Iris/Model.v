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

From Equations Require Import
     Equations Signature.
Require Import Equations.Prop.EqDec.

From stdpp Require finite gmap list.

From iris Require Import
     algebra.auth
     algebra.excl
     algebra.gmap
     base_logic.lib.fancy_updates
     base_logic.lib.gen_heap
     base_logic.lib.own
     bi.big_op
     bi.interface
     program_logic.adequacy
     program_logic.weakestpre
     proofmode.tactics.

From Katamaran Require Import
     SmallStep.Step
     SmallStep.Inversion
     Sep.Logic
     Sep.Hoare
     Specification
     Semantics
     Prelude.

Import ctx.notations.
Import env.notations.

Set Implicit Arguments.

Section TransparentObligations.
  Local Set Transparent Obligations.
  (* Derive NoConfusion for SomeReg. *)
  (* Derive NoConfusion for SomeVal. *)
  Derive NoConfusion for iris.algebra.excl.excl.
End TransparentObligations.

Program Definition IProp Σ : SepLogic :=
  {| lcar              := iProp Σ;
     lentails          := bi_entails;
     sep.land          := bi_and;
     sep.lor           := bi_or;
     limpl             := bi_impl;
     lprop             := bi_pure;
     lex               := @bi_exist _;
     lall              := @bi_forall _;
     lemp              := bi_emp;
     lsep              := bi_sep;
     lwand             := bi_wand;
     lentails_preorder := bi.entails_po;
     land_right        := bi.and_intro;
     land_left1        := bi.and_elim_l';
     land_left2        := bi.and_elim_r';
     lor_left          := bi.or_elim;
     lor_right1        := bi.or_intro_l';
     lor_right2        := bi.or_intro_r';
     lex_right         := fun B x P Q => @bi.exist_intro' _ B P Q x;
     lex_left          := @bi.exist_elim _;
     lall_left         := fun B x P Q => transitivity (bi.forall_elim x);
     lall_right        := fun B => bi.forall_intro;
     limpl_and_adjoint := fun P Q R => conj (bi.impl_intro_r P Q R) (bi.impl_elim_l' P Q R);
     lprop_left        := bi.pure_elim';
     lprop_right       := bi.pure_intro;
     lsep_assoc        := fun P Q R => proj1 (bi.equiv_entails _ _) (bi.sep_assoc P Q R);
     lsep_comm         := fun P Q => proj1 (bi.equiv_entails _ _) (bi.sep_comm P Q);
     lwand_sep_adjoint := fun P Q R => conj (bi.wand_intro_r P Q R) (bi.wand_elim_l' P Q R);
     lsep_andp_prop    := _;
     lsep_entails      := fun P P' Q Q' => bi.sep_mono P Q P' Q';
     lsep_emp          := fun P => proj1 (bi.equiv_entails _ _) (bi.sep_emp P);
     lsep_leak         := _;
  |}.
Next Obligation.
  intros Σ P R Q. split.
  - iIntros "[P [% R]]".
    by iSplit; iFrame.
  - iIntros "[% [P R]]".
    by iFrame.
Qed.
Next Obligation.
  now iIntros (Σ P) "HP".
Qed.
Canonical IProp.

Module IrisPrelims
    (Import B    : Base)
    (Import P    : Program B)
    (Import SpecMixin : ProgSpecMixinOn B P)
    (Import SEM  : Semantics B P).

  Import SmallStepNotations.

  Section Language.

    (* The "expressions" of the LanguageMixin are configurations consisting of a
       statement and a local variable store. *)
    Record Conf (Γ : PCtx) τ : Type :=
      MkConf
        { conf_stm   : Stm Γ τ;
          conf_store : CStore Γ
        }.

    Section TransparentObligations.
      Local Set Transparent Obligations.
      Derive NoConfusion for Conf.
    End TransparentObligations.

    (* The "values" of the LanguageMixin are final configurations consisting of a
       value and a store. We only keep the store around for technical reasons,
       essentially to validate of_to_val. *)
    Section ValConf.
      Local Set Primitive Projections.
      Record ValConf (Γ : PCtx) τ : Type :=
        MkValConf
          { valconf_val   : Val τ;
            valconf_store : CStore Γ
          }.
    End ValConf.

    Definition of_val {Γ} {τ} (v : ValConf Γ τ) : Conf Γ τ :=
      match v with
        MkValConf _ v δ => MkConf (stm_val _ v) δ
      end.

    Definition to_val {Γ} {τ} (t : Conf Γ τ) : option (ValConf Γ τ) :=
      match t with
      | MkConf (stm_val _ v) δ => Some (MkValConf _ v δ)
      | _                      => None
      end.

    Lemma to_of_val {Γ} {τ} (v : ValConf Γ τ) : to_val (of_val v) = Some v.
    Proof.
      by destruct v.
    Qed.

    Lemma of_to_val {Γ} {τ} (s : Conf Γ τ) v : to_val s = Some v → of_val v = s.
    Proof.
      destruct s as [s δ]; destruct s; try done.
      by intros [= <-].
    Qed.

    Lemma val_head_stuck_step {τ} {Γ : PCtx} γ1 γ2 μ1 μ2 (δ1 : CStore Γ) δ2 (s1 : Stm Γ τ) s2 :
      ⟨ γ1, μ1, δ1, s1 ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩ -> to_val (MkConf s1 δ1) = None.
    Proof.
      by induction 1.
    Qed.

    Definition observation := Empty_set.

    Definition State := prod RegStore Memory.

    Inductive prim_step {Γ τ} : Conf Γ τ -> State -> list Empty_set -> Conf Γ τ -> State -> list (Conf Γ τ) -> Prop :=
    | mk_prim_step γ1 γ2 μ1 μ2 (δ1 : CStore Γ) (δ2 : CStore Γ) s1 s2 :
        ⟨ γ1, μ1, δ1, s1 ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩ ->
        prim_step (MkConf s1 δ1) (γ1 , μ1) nil (MkConf s2 δ2) (γ2 , μ2) nil
    .

    Lemma val_head_stuck {Γ τ} (e1 : Conf Γ τ) s1 ls e2 s2 {ks} : prim_step e1 s1 ls e2 s2 ks → to_val e1 = None.
    Proof.
      induction 1.
      by eapply val_head_stuck_step.
    Qed.

    Lemma microsail_lang_mixin Γ τ : LanguageMixin of_val to_val (@prim_step Γ τ).
    Proof. split; eauto using to_of_val, of_to_val, val_head_stuck. Qed.

    Canonical Structure microsail_lang Γ τ : language := Language (microsail_lang_mixin Γ τ).

    Global Instance intoVal_valconf {Γ τ δ v} : IntoVal (MkConf (Γ := Γ) (τ := τ) (stm_val _ v) δ) (MkValConf _ v δ).
      intros; eapply of_to_val; by cbn.
    Defined.

  End Language.

  Section Registers.

    Definition SomeReg : Type := sigT 𝑹𝑬𝑮.
    Definition SomeVal : Type := sigT Val.

    Global Instance eqDec_SomeReg : EqDec SomeReg := 𝑹𝑬𝑮_eq_dec.
    Global Instance countable_SomeReg : countable.Countable SomeReg := finite.finite_countable.

    Global Instance eqDec_SomeVal : EqDec SomeVal.
    Proof.
      intros [τ1 v1] [τ2 v2].
      destruct (Ty_eq_dec τ1 τ2).
      - subst.
        destruct (Val_eqb_spec _ v1 v2).
        + left. congruence.
        + right. intros H.
          Local Set Equations With UIP.
          by dependent elimination H.
      - right. intros H.
        by dependent elimination H.
    Qed.

    Definition regUR := authR (gmapUR SomeReg (exclR (leibnizO SomeVal))).
    (* Definition regUR' : cmra := *)
    (*   authR (discrete_funUR (A := SomeReg) *)
    (*            (fun '(existT σ r) => excl_auth.excl_authUR (leibnizO (Val σ)))). *)

    Class sailRegGS Σ := SailRegGS {
                            (* ghost variable for tracking state of registers *)
                            reg_inG :> inG Σ regUR;
                            reg_gv_name : gname;
                          }.

    Definition reg_pointsTo `{sailRegGS Σ} {τ} (r : 𝑹𝑬𝑮 τ) (v : Val τ) : iProp Σ :=
      own reg_gv_name (◯ {[ existT _ r := Excl (existT _ v) ]}).

    Definition regs_inv `{sailRegGS Σ} (regstore : RegStore) : iProp Σ :=
      (∃ regsmap,
          own reg_gv_name (● regsmap) ∗
          ⌜ map_Forall (K := SomeReg) (A := excl SomeVal) (fun reg v => match reg with | existT _ reg => Excl (existT _ (read_register regstore reg)) = v end ) regsmap ⌝
      )%I.

  End Registers.
End IrisPrelims.


Module Type IrisParameters
  (Import B    : Base)
  (Import P : Program B)
  (Import SIG : ProgramLogicSignature B)
  (Import SEM  : Semantics B P).
  Include IrisPrelims B P SIG SEM.
  Parameter memGpreS : gFunctors -> Set.
  Parameter memGS : gFunctors -> Set.
  Parameter memΣ : gFunctors.
  Parameter memΣ_GpreS : forall {Σ}, subG memΣ Σ -> memGpreS Σ.
  Parameter mem_inv : forall {Σ}, memGS Σ -> Memory -> iProp Σ.
  Parameter mem_res : forall {Σ}, memGS Σ -> Memory -> iProp Σ.

    (* Definition mem_inv `{sailG Σ} (μ : Z -> option Z) : iProp Σ := *)
    (*   (∃ memmap, gen_heap_ctx memmap ∗ *)
    (*      ⌜ map_Forall (fun (a : Z) v => μ a = Some v) memmap ⌝ *)
    (*   )%I. *)

  Parameter mem_inv_init : forall Σ (μ : Memory), memGpreS Σ ->
                                         ⊢ |==> ∃ mG : memGS Σ, (mem_inv mG μ ∗ mem_res mG μ)%I.

  Parameter luser_inst : forall `{sRG : sailRegGS Σ} `{invGS Σ} (mG : memGS Σ) (p : 𝑯) (ts : Env Val (𝑯_Ty p)), iProp Σ.
  Parameter lduplicate_inst : forall `{sRG : sailRegGS Σ} `{invGS Σ} (mG : memGS Σ) (p : 𝑯) (ts : Env Val (𝑯_Ty p)),
      is_duplicable p = true -> bi_entails (luser_inst (sRG := sRG) mG ts) (luser_inst (sRG := sRG) mG ts ∗ luser_inst (sRG := sRG) mG ts).
End IrisParameters.


(*
 * The following module defines the Iris model depending solely on the ProgramLogicSignature, not only the Specification.
 * This allows us to use multiple different specifications with the same Iris model, so that the resulting triples can be combined.
 * This is important particularly in the RiscvPmp.BlockVerification proofs.
 *)
Module Type IrisInstance
  (Import B    : Base)
  (Import SIG : ProgramLogicSignature B)
  (Import SEM  : Semantics B SIG.PROG)
  (Import IParam  : IrisParameters B SIG.PROG SIG SEM).
Section Soundness.

  Class sailGpreS Σ := SailGpreS { (* resources for the implementation side *)
                       sailGpresS_invGpreS :> invGpreS Σ; (* for fancy updates, invariants... *)

                       (* ghost variable for tracking state of registers *)
                       reg_pre_inG :> inG Σ regUR;

                       (* ghost variable for tracking state of memory cells *)
                       sailPreG_gen_memGpreS :> memGpreS Σ
                     }.
  Class sailGS Σ := SailGS { (* resources for the implementation side *)
                       sailGS_invGS :> invGS Σ; (* for fancy updates, invariants... *)
                       sailGS_sailRegGS :> sailRegGS Σ;

                       (* ghost variable for tracking state of memory cells *)
                       sailGS_memGS :> memGS Σ
                     }.

  Global Instance sailGS_irisGS {Γ τ} `{sailGS Σ} : irisGS (microsail_lang Γ τ) Σ := {
    iris_invGS := sailGS_invGS;
    state_interp σ ns κs nt := (regs_inv σ.1 ∗ mem_inv sailGS_memGS σ.2)%I;
    fork_post _ := True%I; (* no threads forked in sail, so this is fine *)
    num_laters_per_step _ := 0;
    state_interp_mono _ _ _ _ := fupd_intro _ _;
                                                                                }.
  Global Opaque iris_invGS.

  Context `{sG : sailGS Σ}.

  Global Instance PredicateDefIProp : PredicateDef (IProp Σ) :=
    {| lptsreg σ r v        := reg_pointsTo r v;
       luser p ts           := luser_inst sailGS_memGS ts;
       lduplicate p ts Hdup := lduplicate_inst (sRG := sailGS_sailRegGS) sailGS_memGS ts Hdup
    |}.

  Lemma reg_valid regstore {τ} (r : 𝑹𝑬𝑮 τ) (v : Val τ) :
    ⊢ (regs_inv regstore -∗ reg_pointsTo r v -∗ ⌜read_register regstore r = v⌝)%I.
  Proof.
    iDestruct 1 as (regsmap) "[Hregs %]".
    iIntros "Hreg".
    iDestruct (own_valid_2 with "Hregs Hreg") as %[Hl regsv]%auth_both_valid.
    iPureIntro.
    specialize (Hl 0).
    setoid_rewrite (singleton_includedN_l 0 regsmap (existT _ r) _) in Hl.
    destruct Hl as [y [eq1%discrete%leibniz_equiv eq2%cmra_discrete_included_r]];
      auto with typeclass_instances.
    specialize (regsv (existT _ r)).
    rewrite eq1 in regsv.
    destruct y as [y|]; [|inversion regsv].
    setoid_rewrite Excl_included in eq2.
    apply leibniz_equiv in eq2. subst.
    specialize (H (existT _ r) (Excl (existT _ v)) eq1); cbn in H.
    Local Set Equations With UIP.
    by dependent elimination H.
  Qed.

  Lemma regs_inv_update {τ} {r} {v : Val τ} {regsmap : gmapUR SomeReg (exclR (leibnizO SomeVal))} {regstore : RegStore} :
    map_Forall (K := SomeReg) (A := excl SomeVal) (λ r' v', match r' with
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

  Lemma reg_update regstore {τ} r (v1 v2 : Val τ) :
    regs_inv regstore -∗ reg_pointsTo r v1 ==∗ regs_inv (write_register regstore r v2) ∗ reg_pointsTo r v2.
  Proof.
    iDestruct 1 as (regsmap) "[Hregs %]".
    rewrite /reg_pointsTo.
    iIntros "Hreg".
    iDestruct (own_valid_2 with "Hregs Hreg") as %[Hl%cmra_discrete_included_r regsmapv]%auth_both_valid.
    setoid_rewrite (singleton_included_l regsmap (existT _ r) _) in Hl.
    destruct Hl as [y [eq1%leibniz_equiv eq2]].
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
    iApply (regs_inv_update H); iFrame.
  Qed.

  Lemma iris_rule_stm_read_register_wp {Γ τ} (r : 𝑹𝑬𝑮 τ) (v : Val τ) {δ : CStore Γ} :
    ⊢ (lptsreg r v -∗
                    WP (MkConf (stm_read_register r) δ) ?{{ w, lptsreg r v ∗ ⌜ w = MkValConf _ v δ ⌝ }}
      )%I.
  Proof.
    iIntros "Hreg".
    iApply (wp_mask_mono _ empty); auto.
    rewrite wp_unfold; cbn.
    iIntros (σ _ ls _ n) "[Hregs Hmem]".
    iDestruct (@reg_valid with "Hregs Hreg") as %<-.
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 σ2 efs) "%".
    remember (MkConf (stm_read_register r) δ) as t.
    destruct H as [γ1 γ2 σ1 σ2 δ1 δ2 s1 s2 step].
    dependent elimination Heqt.
    destruct (steps_inversion_read_register step) as [<- [<- [<- ->]]].
    iModIntro. iModIntro. iModIntro.
    iFrame. iSplitR ""; auto.
    by iApply wp_value.
  Qed.

  Lemma iris_rule_stm_write_register_wp {Γ} {τ} (r : 𝑹𝑬𝑮 τ) (δ : CStore Γ) (v : Val τ) e :
    ⊢ (reg_pointsTo r v -∗
                    WP (MkConf (stm_write_register r e) δ : expr (microsail_lang Γ τ)) ?{{ w, reg_pointsTo r (eval e δ) ∗ bi_pure (w = MkValConf _ (eval e δ) δ) }}
    )%I.
  Proof.
    iIntros "Hreg".
    iApply (wp_mask_mono _ empty); auto.
    rewrite wp_unfold; cbn.
    iIntros (σ _ ls _ n) "[Hregs Hmem]".
    iMod (reg_update σ.1 r v (eval e δ) with "Hregs Hreg") as "[Hregs Hreg]".
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 σ2 efs) "%".
    dependent elimination H.
    destruct (steps_inversion_write_register s) as [-> [<- [<- ->]]].
    iModIntro. iModIntro. iModIntro.
    iFrame. iSplitR; auto.
    by iApply wp_value.
  Qed.

  Definition semTriple {Γ τ} (δ : CStore Γ)
             (PRE : iProp Σ) (s : Stm Γ τ) (POST : Val τ -> CStore Γ -> iProp Σ) : iProp Σ :=
    PRE -∗ WP (MkConf s δ : expr (microsail_lang Γ τ)) ?{{ v, match v with MkValConf _ v δ' => POST v δ' end }}.
  (* always modality needed? perhaps not because sail not higher-order? *)

  Lemma iris_rule_consequence {Γ σ} {δ : CStore Γ}
        {P P'} {Q Q' : Val σ -> CStore Γ -> iProp Σ} {s : Stm Γ σ} :
        (P ⊢ P') -> (forall v δ', Q' v δ' ⊢ Q v δ') ->
        semTriple δ P' s Q' -∗ semTriple δ P s Q.
  Proof.
    iIntros (PP QQ) "trips P".
    iApply (wp_mono _ _ _ (fun v => match v with MkValConf _ v δ' => Q' v δ' end)).
    + intros [v δ']; cbn.
      apply QQ.
    + iApply "trips".
      iApply PP; iFrame.
  Qed.

  Lemma iris_rule_frame {Γ σ} {δ : CStore Γ}
        (R P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ) (s : Stm Γ σ) :
        (⊢ semTriple δ P s Q -∗ semTriple δ (R ∗ P) s (fun v δ' => R ∗ Q v δ'))%I.
  Proof.
    iIntros "trips [HR HP]".
    iApply (wp_mono _ _ _ (fun v => R ∗ match v with MkValConf _ v δ' => Q v δ' end)%I).
    - iIntros (v) "[R Q]".
      destruct v.
      by iFrame.
    - iApply (wp_frame_l _ _ (MkConf s δ) (fun v => match v with MkValConf _ v δ' => Q v δ' end) R).
      iFrame.
      by iApply "trips".
  Qed.

  Lemma iris_rule_pull {σ Γ} (δ : CStore Γ) (s : Stm Γ σ)
        (P : iProp Σ) (Q : Prop) (R : Val σ -> CStore Γ -> iProp Σ) :
        (⊢ (⌜ Q ⌝ → semTriple δ P s R) -∗ semTriple δ (P ∧ bi_pure Q) s R)%I.
  Proof.
    iIntros "QP [P %]".
    by iApply "QP".
  Qed.

  Lemma iris_rule_exist {σ Γ} (δ : CStore Γ)
        (s : Stm Γ σ) {A : Type} {P : A -> iProp Σ}
        {Q :  Val σ -> CStore Γ -> iProp Σ} :
        ⊢ ((∀ x, semTriple δ (P x) s Q) -∗ semTriple δ (∃ x, P x) s Q)%I.
  Proof.
    iIntros "trips Px".
    iDestruct "Px" as (x) "Px".
    by iApply "trips".
  Qed.

  Lemma iris_rule_stm_val {Γ} (δ : CStore Γ)
        {τ : Ty} {v : Val τ}
        {P : iProp Σ} {Q : Val τ -> CStore Γ -> iProp Σ} :
        ⊢ ((P -∗ Q v δ)%I -∗ semTriple δ P (stm_val τ v) Q)%I.
  Proof.
    iIntros "PQ P".
    iApply wp_value.
    by iApply "PQ".
  Qed.

  Lemma iris_rule_stm_exp {Γ} (δ : CStore Γ)
        {τ : Ty} {e : Exp Γ τ}
        {P : iProp Σ} {Q : Val τ -> CStore Γ -> iProp Σ} :
        ⊢ ((P -∗ Q (eval e δ) δ) -∗ semTriple δ P (stm_exp e) Q)%I.
  Proof.
    iIntros "PQ P".
    iApply (wp_mask_mono _ empty); auto.
    rewrite wp_unfold.
    iIntros ([regs μ] ns k ks nt) "[Hregs Hmem]".
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 σ2 efs) "%".
    remember (MkConf (stm_exp e) δ) as t.
    destruct H.
    dependent elimination Heqt.
    dependent elimination H.
    iModIntro. iModIntro. iModIntro.
    iFrame.
    iSplitL; cbn; trivial.
    iApply (wp_value _ _ (fun v => match v with | MkValConf _ v' δ' => Q v' δ' end) (MkConf (stm_val _ (eval e0 δ1)) δ1)).
    by iApply "PQ".
  Qed.

  Lemma wp_compat_fail {Γ τ} {s} {δ} {Q : ValConf Γ τ -> iProp Σ} :
    (⊢ WP (MkConf (stm_fail _ s) δ) ?{{ v, Q v }})%I.
  Proof.
    rewrite wp_unfold. cbn.
    iIntros (σ _ ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 σ2 efs) "%".
    remember (MkConf (fail s) δ) as s1.
    destruct H.
    inversion Heqs1. subst.
    inversion H.
  Qed.

  Lemma wp_compat_block {Γ Δ} {τ : Ty} {δ : CStore Γ}
        (δΔ : CStore Δ) (k : Stm (Γ ▻▻ Δ) τ) (Q : ValConf Γ τ -> iProp Σ) :
    ⊢ (WP (MkConf k (δ ►► δΔ)) ?{{ v, match v with MkValConf _ v δ' => Q (MkValConf _ v (env.drop Δ δ')) end }} -∗
          WP (MkConf (stm_block δΔ k) δ) ?{{ v, Q v }})%I.
  Proof.
    iRevert (δ δΔ k Q).
    iLöb as "IH".
    iIntros (δ δΔ k Q) "wpk".
    rewrite ?wp_unfold. cbn.
    iIntros (σ _ ks1 ks nt) "state_inv".
    rewrite /wp_pre.
    destruct (language.to_val (MkConf k (δ ►► δΔ))) eqn:Heqkval.
    - destruct v as [v δ0]. apply language.of_to_val in Heqkval.
      inversion Heqkval. subst. clear Heqkval.
      rewrite env.drop_cat.
      iMod "wpk" as "H".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iSplitR; [trivial|].
      iModIntro.
      iIntros (e2 σ2 efs) "%".
      iModIntro. iModIntro. iModIntro.
      iMod "Hclose" as "e".
      iDestruct "e" as "_".
      iModIntro.
      dependent elimination H.
      dependent elimination s.
      + iFrame.
        iSplitL; [|trivial].
        by iApply wp_value.
      + inversion s4.
    - iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro.
      iSplitR; [trivial|].
      iIntros (e2 σ2 efs2) "%".
      dependent elimination H.
      dependent elimination s.
      + discriminate Heqkval.
      + iModIntro. iModIntro. iModIntro.
        iMod "Hclose" as "_".
        iFrame.
        iModIntro.
        iSplitL; [|trivial].
        iApply wp_compat_fail.
      + iMod "Hclose" as "_".
        cbn.
        iMod ("wpk" $! (γ1 , μ1) 0 nil ks nt with "state_inv") as "[% wpk]".
        iMod ("wpk" $! _ _ _ (mk_prim_step s4)) as "wpk".
        iModIntro. iModIntro.
        iMod "wpk".
        iModIntro.
        iMod "wpk" as "[Hregs [wpk' _]]".
        iModIntro.
        iFrame.
        iSplitL; [|trivial].
        iApply "IH".
        iFrame.
  Qed.

  Lemma iris_rule_stm_let {Γ} (δ : CStore Γ)
        (x : 𝑿) (σ τ : Ty) (s : Stm Γ σ) (k : Stm (Γ ▻ x∷σ) τ)
        (P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ)
        (R : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ P s Q -∗
                     (∀ (v : Val σ) (δ' : CStore Γ),
                         semTriple (env.snoc δ' (x∷σ) v) (Q v δ') k (fun v δ'' => R v (env.tail δ'')) ) -∗
                     semTriple δ P (let: x := s in k) R).
  Proof.
    iIntros "trips tripk P".
    iPoseProof ("trips" with "P") as "wpv".
    iRevert (s δ) "wpv".
    iLöb as "IH".
    iIntros (s δ) "wpv".
    rewrite (wp_unfold _ _ (MkConf (stm_let _ _ _ k) _)). cbn.
    iIntros ([regs μ] ns ks1 ks nt) "state_inv".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 [regs2 μ2] efs) "%".
    unfold language.prim_step in H; cbn in H.
    dependent elimination H.
    dependent elimination s0.
    + cbn. rewrite wp_unfold. cbn.
      iModIntro. iModIntro. iModIntro.
      iMod "Hclose" as "_".
      iMod "wpv".
      iPoseProof ("tripk" $! v _ with "wpv") as "wpk".
      iModIntro.
      iFrame; iSplitL; auto.
      by iApply (wp_compat_block (env.snoc env.nil (x0∷σ0) v) _ (fun v0 => match v0 with | MkValConf _ v1 δ' => R v1 δ' end )).
    + iModIntro. iModIntro. iModIntro.
      iMod "Hclose" as "_".
      iFrame; iSplitL; auto.
      by iApply wp_compat_fail.
    + cbn.
      rewrite wp_unfold.
      unfold wp_pre.
      rewrite (val_stuck (MkConf s1 δ1) _ [] _ _ [] (mk_prim_step s3)).
      iSpecialize ("wpv" $! (γ1 , μ1) ns nil nil nt with "state_inv"). cbn.
      iMod "Hclose" as "_".
      iMod "wpv" as "[_ wpv]".
      iSpecialize ("wpv" $! (MkConf s' δ') _ nil (mk_prim_step s3)). cbn.
      iMod "wpv".
      iModIntro. iModIntro.
      iMod "wpv".
      iModIntro.
      iMod "wpv" as "[Hregs [wps _]]".
      iModIntro.
      iFrame.
      iSpecialize ("IH" with "tripk").
      iSpecialize ("IH" with "wps").
      iFrame.
  Qed.

  Lemma iris_rule_stm_let_forwards {Γ} (δ : CStore Γ)
        (x : 𝑿) (σ τ : Ty) (s : Stm Γ σ) (k : Stm (Γ ▻ x∷σ) τ)
        (P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ)
        (R : Val τ -> CStore (Γ ▻ x∷σ) -> iProp Σ) :
        ⊢ (semTriple δ P s Q -∗
                     (∀ (v : Val σ) (δ' : CStore Γ), semTriple (env.snoc δ' (x∷σ) v) (Q v δ') k R ) -∗
                     semTriple δ P (let: x := s in k) (fun v δ' => ∃ v__let, R v (env.snoc δ' (x∷σ) v__let)))%I.
  Proof.
    (* proof should be generalizable beyond Iris model? *)
    iIntros "trips tripk".
    iApply (iris_rule_stm_let δ s k P Q (fun v δ' => ∃ v__let, R v (env.snoc δ' (x∷σ) v__let))%I with "trips").
    iIntros (v δ') "Qv".
    iPoseProof ("tripk" with "Qv") as "wpk".
    iApply (wp_mono with "wpk").
    iIntros (v') "Rv".
    destruct v' as [v0 δ0].
    iExists (env.head δ0).
    by dependent elimination δ0.
  Qed.

  Lemma iris_rule_stm_block {Γ} (δ : CStore Γ)
        (Δ : PCtx) (δΔ : CStore Δ)
        (τ : Ty) (k : Stm (Γ ▻▻ Δ) τ)
        (P : iProp Σ) (R : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple (δ ►► δΔ) P k (fun v δ'' => R v (env.drop Δ δ'')) -∗
                   semTriple δ P (stm_block δΔ k) R)%I.
  Proof.
    iIntros "tripk P".
    iPoseProof ("tripk" with "P") as "wpk".
    by iApply (wp_compat_block δΔ k (fun v => match v with | MkValConf _ v' δ' => R v' δ' end) with "wpk").
  Qed.

  Lemma iris_rule_stm_if {Γ} (δ : CStore Γ)
        (τ : Ty) (e : Exp Γ ty_bool) (s1 s2 : Stm Γ τ)
        (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ (P ∧ ⌜ eval e δ = true ⌝) s1 Q -∗
                   semTriple δ (P ∧ ⌜ eval e δ = false ⌝) s2 Q -∗
                   semTriple δ P (stm_if e s1 s2) Q)%I.
  Proof.
    iIntros "trips1 trips2 P".
    rewrite wp_unfold. cbn.
    iIntros (σ _ ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e2 σ2 efs) "%".
    unfold language.prim_step in H; cbn in H.
    dependent elimination H.
    dependent elimination s.
    iModIntro. iModIntro. iModIntro.
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
        (P1 P2 : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
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
        (P : iProp Σ) (Q : CStore Γ -> iProp Σ) (R : Val σ -> CStore Γ -> iProp Σ) :
    ⊢ (semTriple δ P s1 (fun _ => Q) -∗
                 (∀ δ', semTriple δ' (Q δ') s2 R) -∗
                 semTriple δ P (s1 ;; s2) R)%I.
  Proof.
    iIntros "trips1 trips2 P".
    iPoseProof ("trips1" with "P") as "wps1".
    iRevert (s1 δ) "wps1".
    iLöb as "IH".
    iIntros (s1 δ) "wps1".
    rewrite (wp_unfold _ _ (MkConf (stm_seq _ _) _)). cbn.
    iIntros ([regs μ] ns ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 σ2 efs) "%".
    unfold language.prim_step in H; cbn in H.
    dependent elimination H.
    dependent elimination s; cbn.
    + rewrite wp_unfold.
      unfold wp_pre.
      rewrite (val_stuck (MkConf s7 δ1) (γ1 , μ1) [] _ _ [] (mk_prim_step s8)).
      iSpecialize ("wps1" $! (γ1 , μ1) ns nil nil nt with "Hregs"). cbn.
      iMod "Hclose" as "_".
      iMod "wps1" as "[_ wps1]". cbn.
      iMod ("wps1" $! (MkConf s'0 δ'1) _ nil (mk_prim_step s8)) as "wps1".
      iModIntro. iModIntro. iModIntro.
      iMod "wps1".
      iMod "wps1" as "[Hregs [wps' _]]".
      iFrame.
      iSplitL; [|trivial].
      iModIntro.
      iSpecialize ("IH" with "trips2").
      by iApply "IH".
    + rewrite wp_unfold; cbn.
      iModIntro. iModIntro. iModIntro.
      iMod "Hclose" as "_".
      iMod "wps1" as "wps1".
      iPoseProof ("trips2" $! δ1 with "wps1") as "wps2".
      by iFrame.
    + iModIntro. iModIntro. iModIntro.
      iMod "Hclose" as "_".
      iFrame; iSplitL; auto.
      by iApply wp_compat_fail.
  Qed.

  Lemma iris_rule_stm_assertk {Γ τ} (δ : CStore Γ)
        (e1 : Exp Γ ty_bool) (e2 : Exp Γ ty_string) (k : Stm Γ τ)
                      (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
    ⊢ (semTriple δ (P ∧ ⌜ eval e1 δ = true ⌝) k Q -∗
       semTriple δ P (stm_assertk e1 e2 k) Q)%I.
  Proof.
    iIntros "tripk P".
    rewrite wp_unfold. cbn.
    iIntros (σ ns ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e3 σ2 efs) "%".
    unfold language.prim_step in H; cbn in H.
    dependent elimination H.
    dependent elimination s.
    iModIntro. iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro; iFrame.
    iSplitL; [|trivial].
    destruct (eval e3 δ1) eqn:Heqc.
    - iApply "tripk".
      by iFrame.
    - iApply wp_compat_fail.
  Qed.

  Lemma iris_rule_stm_fail {Γ} (δ : CStore Γ)
        (τ : Ty) (s : Val ty_string) :
        forall (Q : Val τ -> CStore Γ -> iProp Σ),
          ⊢ semTriple δ True%I (stm_fail τ s) Q.
  Proof.
    iIntros (Q) "_".
    iApply wp_compat_fail.
  Qed.

  Lemma iris_rule_stm_match_list {Γ} (δ : CStore Γ)
        {σ τ : Ty} (e : Exp Γ (ty_list σ)) (alt_nil : Stm Γ τ)
        (xh xt : 𝑿) (alt_cons : Stm (Γ ▻ xh∷σ ▻ xt∷ty_list σ) τ)
        (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ (P ∧ bi_pure (eval e δ = []%list)) alt_nil (fun v' δ' => Q v' δ') -∗
                     (∀ v vs, semTriple (env.snoc (env.snoc δ (xh∷σ) v) (xt∷ty_list σ) vs) (P ∧ bi_pure (eval e δ = cons v vs)) alt_cons (fun v' δ' => Q v' (env.tail (env.tail δ')))) -∗
                     semTriple δ P (stm_match_list e alt_nil xh xt alt_cons) Q)%I.
  Proof.
    iIntros "tripnil tripcons P".
    rewrite wp_unfold. cbn.
    iIntros (σ1 _ ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e3 σ2 efs) "%".
    unfold language.prim_step in H; cbn in H.
    dependent elimination H.
    dependent elimination s.
    remember (eval e4 δ1) as scrutinee.
    destruct scrutinee as [|l ls].
    - iModIntro. iModIntro. iModIntro.
      iMod "Hclose" as "_".
      iModIntro. iFrame.
      iSplitL; [|trivial].
      iApply "tripnil".
      by iFrame.
    - iModIntro. iModIntro. iModIntro.
      iMod "Hclose" as "_".
      iModIntro.
      iFrame.
      iSplitL; [|trivial].
      iApply (wp_compat_block (env.snoc (env.snoc env.nil (xh0∷σ6) l) (xt0∷ty_list σ6) ls)).
      iApply "tripcons".
      by iFrame.
  Qed.

  Lemma iris_rule_stm_match_sum {Γ} (δ : CStore Γ)
        (σinl σinr τ : Ty) (e : Exp Γ (ty_sum σinl σinr))
                         (xinl : 𝑿) (alt_inl : Stm (Γ ▻ xinl∷σinl) τ)
                         (xinr : 𝑿) (alt_inr : Stm (Γ ▻ xinr∷σinr) τ)
                         (P : iProp Σ)
                         (Q : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ ((∀ v, semTriple (env.snoc δ (xinl∷σinl) v) (P ∧ ⌜ eval e δ = inl v ⌝) alt_inl (fun v' δ' => Q v' (env.tail δ'))) -∗
           (∀ v, semTriple (env.snoc δ (xinr∷σinr) v) (P ∧ ⌜ eval e δ = inr v ⌝) alt_inr (fun v' δ' => Q v' (env.tail δ'))) -∗
        semTriple δ P (stm_match_sum e xinl alt_inl xinr alt_inr) Q)%I.
  Proof.
    iIntros "tripinl tripinr P".
    rewrite wp_unfold. cbn.
    iIntros (σ1 _ ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e2 σ2 efs) "%".
    unfold language.prim_step in H; cbn in H.
    dependent elimination H.
    dependent elimination s.
    remember (eval e5 δ1) as scrutinee.
    destruct scrutinee as [v1|v2].
    - iModIntro. iModIntro. iModIntro.
      iMod "Hclose" as "_".
      iModIntro. iFrame.
      iSplitL; [|trivial].
      iApply (wp_compat_block (env.snoc env.nil (xinl0∷σinl0) v1)).
      iApply ("tripinl" $! v1).
      by iFrame.
    - iModIntro. iModIntro. iModIntro.
      iMod "Hclose" as "_".
      iModIntro. iFrame.
      iSplitL; [|trivial].
      iApply (wp_compat_block (env.snoc env.nil (xinr0∷σinr0) v2)).
      iApply ("tripinr" $! v2).
      by iFrame.
  Qed.

  Lemma iris_rule_stm_match_prod {Γ} (δ : CStore Γ)
        {σ1 σ2 τ : Ty} (e : Exp Γ (ty_prod σ1 σ2))
        (xl xr : 𝑿) (rhs : Stm (Γ ▻ xl∷σ1 ▻ xr∷σ2) τ)
        (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ ((∀ vl vr,
            semTriple (env.snoc (env.snoc δ (xl∷σ1) vl) (xr∷σ2) vr)
              (P ∧ bi_pure (eval e δ = (vl,vr))) rhs (fun v δ' => Q v (env.tail (env.tail δ')))) -∗
          semTriple δ P (stm_match_prod e xl xr rhs) Q)%I.
  Proof.
    iIntros "trippair P".
    rewrite wp_unfold. cbn.
    iIntros (σ _ ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e2 σ' efs) "%".
    unfold language.prim_step in H; cbn in H.
    dependent elimination H.
    dependent elimination s.
    remember (eval e6 δ1) as scrutinee.
    destruct scrutinee as [v1 v2].
    iModIntro. iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro. iFrame.
    iSplitL; [|trivial].
    iApply (wp_compat_block (env.snoc (env.snoc env.nil (xl0∷σ8) v1) (xr0∷σ9) v2)).
    iApply ("trippair" $! v1 v2).
    by iFrame.
  Qed.

  Lemma iris_rule_stm_match_enum {Γ} (δ : CStore Γ)
        {E : 𝑬} (e : Exp Γ (ty_enum E)) {τ : Ty}
        (alts : forall (K : 𝑬𝑲 E), Stm Γ τ)
        (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ P (alts (eval e δ)) Q -∗
          semTriple δ P (stm_match_enum E e alts) Q)%I.
  Proof.
    iIntros "tripalt P".
    rewrite wp_unfold. cbn.
    iIntros (σ _ ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e2 σ' efs) "%".
    unfold language.prim_step in H; cbn in H.
    dependent elimination H.
    dependent elimination s.
    iModIntro. iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro. iFrame.
    iSplitL; [|trivial].
    by iApply "tripalt".
  Qed.

  Lemma iris_rule_stm_match_tuple {Γ} (δ : CStore Γ)
        {σs : Ctx Ty} {Δ : PCtx} (e : Exp Γ (ty_tuple σs))
        (p : TuplePat σs Δ) {τ : Ty} (rhs : Stm (Γ ▻▻ Δ) τ)
        (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
    ⊢ ((semTriple (env.cat δ (tuple_pattern_match_val p (eval e δ))) P rhs (fun v δ' => Q v (env.drop Δ δ'))) -∗
       semTriple δ P (stm_match_tuple e p rhs) Q)%I.
  Proof.
    iIntros "triptup P".
    rewrite wp_unfold. cbn.
    iIntros (σ ns ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e2 σ' efs) "%".
    unfold language.prim_step in H; cbn in H.
    dependent elimination H.
    dependent elimination s.
    iModIntro. iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro. iFrame.
    iSplitL; [|trivial].
    iApply (wp_compat_block (tuple_pattern_match_val p0 (eval e8 δ1))).
    by iApply "triptup".
  Qed.

  Lemma iris_rule_stm_match_union {Γ} (δ : CStore Γ)
        {U : 𝑼} (e : Exp Γ (ty_union U)) {σ τ : Ty}
        (alt__Δ : forall (K : 𝑼𝑲 U), PCtx)
        (alt__p : forall (K : 𝑼𝑲 U), Pattern (alt__Δ K) (𝑼𝑲_Ty K))
        (alt__r : forall (K : 𝑼𝑲 U), Stm (Γ ▻▻ alt__Δ K) τ)
        (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ ((∀ (K : 𝑼𝑲 U) (v : Val (𝑼𝑲_Ty K)),
               semTriple (env.cat δ (pattern_match_val (alt__p K) v)) (P ∧ bi_pure (eval e δ = 𝑼_fold (existT K v))) (alt__r K) (fun v δ' => Q v (env.drop (alt__Δ K) δ'))) -∗
               semTriple δ P (stm_match_union U e alt__p alt__r) Q
          )%I.
  Proof.
    iIntros "tripunion P".
    rewrite wp_unfold. cbn.
    iIntros (σ1 ns ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e2 σ2 efs) "%".
    unfold language.prim_step in H; cbn in H.
    dependent elimination H.
    dependent elimination s.
    iModIntro. iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro. iFrame.
    iSplitL; [|trivial].
    remember (𝑼_unfold (eval e9 δ1)) as scrutinee.
    destruct scrutinee as [K v].
    iApply (wp_compat_block (pattern_match_val (alt__pat K) v)).
    iSpecialize ("tripunion" $! K v).
    rewrite Heqscrutinee.
    rewrite 𝑼_fold_unfold.
    iApply "tripunion".
    by iFrame.
  Qed.

  Lemma iris_rule_stm_match_record {Γ} (δ : CStore Γ)
        {R : 𝑹} {Δ : PCtx} (e : Exp Γ (ty_record R))
        (p : RecordPat (𝑹𝑭_Ty R) Δ) {τ : Ty} (rhs : Stm (Γ ▻▻ Δ) τ)
        (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ ((semTriple (env.cat δ (record_pattern_match_val p (eval e δ))) P rhs (fun v δ' => Q v (env.drop Δ δ'))) -∗
        semTriple δ P (stm_match_record R e p rhs) Q)%I.
  Proof.
    iIntros "triprec P".
    rewrite wp_unfold. cbn.
    iIntros (σ1 ns ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e2 σ2 efs) "%".
    unfold language.prim_step in H; cbn in H.
    dependent elimination H.
    dependent elimination s.
    iModIntro. iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro. iFrame.
    iSplitL; [|trivial].
    iApply (wp_compat_block (record_pattern_match_val p1 (eval e10 δ1))).
    by iApply "triprec".
  Qed.

  Lemma iris_rule_stm_match_bvec {Γ} (δ : CStore Γ)
        {n : nat} (e : Exp Γ (ty_bvec n)) {τ : Ty}
        (rhs : forall (v : bv n), Stm Γ τ)
        (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ P (rhs (eval e δ)) Q -∗
          semTriple δ P (stm_match_bvec n e rhs) Q)%I.
  Proof.
    iIntros "triprhs P".
    rewrite wp_unfold. cbn.
    iIntros (σ _ ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e2 σ' efs) "%".
    unfold language.prim_step in H; cbn in H.
    dependent elimination H.
    dependent elimination s.
    iModIntro. iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro. iFrame.
    iSplitL; [|trivial].
    by iApply "triprhs".
  Qed.

  Lemma iris_rule_stm_read_register {Γ} (δ : CStore Γ)
        {σ : Ty} (r : 𝑹𝑬𝑮 σ) (v : Val σ) :
        ⊢ (semTriple δ (lptsreg r v) (stm_read_register r) (fun v' δ' => ⌜ δ' = δ ⌝ ∧ ⌜ v' = v ⌝ ∧ lptsreg r v))%I.
  Proof.
    iIntros "Hreg".
    iApply wp_mono; [| iApply (iris_rule_stm_read_register_wp with "Hreg") ].
    iIntros ([δ' v']) "[Hreg %]".
    inversion H.
    by iFrame.
  Qed.

  Lemma iris_rule_stm_write_register {Γ} (δ : CStore Γ)
        {σ : Ty} (r : 𝑹𝑬𝑮 σ) (w : Exp Γ σ)
                              (Q : Val σ -> CStore Γ -> iProp Σ)
                              (v : Val σ) :
        ⊢ semTriple δ (lptsreg r v) (stm_write_register r w)
                  (fun v' δ' => ⌜δ' = δ⌝ ∧ ⌜v' = eval w δ⌝ ∧ lptsreg r v')%I.
  Proof.
    iIntros "Hreg".
    iApply wp_mono; [|iApply (iris_rule_stm_write_register_wp with "Hreg")].
    iIntros (v') "[Hreg %]".
    rewrite H.
    by iFrame.
  Qed.

  Lemma iris_rule_stm_assign_forwards {Γ} (δ : CStore Γ)
        (x : 𝑿) (σ : Ty) (xIn : x∷σ ∈ Γ) (s : Stm Γ σ)
        (P : iProp Σ) (R : Val σ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ P s R -∗
                     semTriple δ P (stm_assign x s) (fun v__new δ' => ∃ v__old, R v__new (@env.update _ _ _ δ' (x∷_)  _ v__old) ∧ bi_pure (env.lookup δ' xIn = v__new)))%I.
  Proof.
    iIntros "trips P".
    iPoseProof ("trips" with "P") as "wpv".
    iRevert (s δ) "wpv".
    iLöb as "IH".
    iIntros (s δ) "wpv".
    rewrite (wp_unfold _ _ (MkConf (stm_assign _ s) _)). cbn.
    iIntros ([regs μ] ns ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 [regs2 μ2] efs) "%".
    unfold language.prim_step in H; cbn in H.
    dependent elimination H.
    dependent elimination s0.
    cbn.
    + rewrite wp_unfold; cbn.
      iModIntro. iModIntro. iModIntro.
      iMod "Hclose" as "_".
      iMod "wpv" as "wpv".
      iModIntro.
      iFrame.
      iSplitL; [|trivial].
      iApply wp_value.
      cbn.
      iExists (env.lookup δ1 xInΓ).
      rewrite env.update_update env.update_lookup env.lookup_update.
      by iFrame.
    + iModIntro. iModIntro. iModIntro.
      iMod "Hclose" as "_".
      cbn.
      iFrame; iSplitL; auto.
      by iApply wp_compat_fail.
    + rewrite wp_unfold.
      unfold wp_pre.
      rewrite (val_stuck (MkConf s13 δ1) _ [] _ _ [] (mk_prim_step s14)).
      iSpecialize ("wpv" $! _ ns nil nil nt with "Hregs"). cbn.
      iMod "Hclose".
      iMod "wpv" as "[_ wpv]".
      iSpecialize ("wpv" $! _ _ nil (mk_prim_step s14)).
      iMod "wpv" as "wpv".
      iModIntro. iModIntro.
      iMod "wpv".
      iModIntro.
      iMod "wpv" as "[Hregs [wps _]]".
      iModIntro.
      iFrame.
      by iApply "IH".
  Qed.

  Lemma iris_rule_stm_assign_backwards {Γ} (δ : CStore Γ)
        (x : 𝑿) (σ : Ty) (xIn : x∷σ ∈ Γ) (s : Stm Γ σ)
        (P : iProp Σ) (R : Val σ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ P s (fun v δ' => R v (@env.update _ _ _ δ' (x∷_) _ v)) -∗
           semTriple δ P (stm_assign x s) R)%I.
  Proof.
    iIntros "trips P".
    iPoseProof (iris_rule_stm_assign_forwards _ with "trips P") as "wpas".
    iApply (wp_mono with "wpas").
    iIntros ([v' δ']) "Rv".
    iDestruct "Rv" as (v__old) "[Rv %]".
    rewrite <-H.
    by rewrite env.update_update env.update_lookup.
  Qed.

  Fixpoint Forall {Δ : LCtx} {struct Δ} : (Valuation Δ -> iProp Σ) -> iProp Σ :=
    match Δ return (Valuation Δ -> iProp Σ) -> iProp Σ with
    | ctx.nil      => fun P => P env.nil
    | ctx.snoc Δ b => fun P => Forall (fun δ => ∀ (v : Val (type b)), P (env.snoc δ b v))
    end%I.

  Definition ValidContractSemCurried {Δ σ} (body : Stm Δ σ) (contract : SepContract Δ σ) : iProp Σ :=
    match contract with
    | MkSepContract _ _ ctxΣ θΔ pre result post =>
      Forall (fun (ι : Valuation ctxΣ) =>
        semTriple (inst θΔ ι) (interpret_assertion pre ι) body
                  (fun v δ' => interpret_assertion post (env.snoc ι (result∷σ) v)))
    end%I.

  Definition ValidContractSem {Δ σ} (body : Stm Δ σ) (contract : SepContract Δ σ) : iProp Σ :=
    match contract with
    | MkSepContract _ _ ctxΣ θΔ pre result post =>
      ∀ (ι : Valuation ctxΣ),
        semTriple (inst θΔ ι) (interpret_assertion pre ι) body
                  (fun v δ' => interpret_assertion post (env.snoc ι (result∷σ) v))
    end%I.

  Definition ValidContractEnvSem (cenv : SepContractEnv) : iProp Σ :=
    (∀ σs σ (f : 𝑭 σs σ),
      match cenv σs σ f with
      | Some c => ValidContractSem (FunDef f) c
      | None => True
      end)%I.

  Lemma wp_compat_call_frame {Γ Δ} {τ : Ty} {δ : CStore Γ}
        (δΔ : CStore Δ) (s : Stm Δ τ) (Q : ValConf Γ τ -> iProp Σ) :
    ⊢ (WP (MkConf s δΔ) ?{{ v, match v with MkValConf _ v δ' => Q (MkValConf _ v δ) end }} -∗
          WP (MkConf (stm_call_frame δΔ s) δ) ?{{ v, Q v }})%I.
  Proof.
    iRevert (δ δΔ s Q).
    iLöb as "IH".
    iIntros (δ δΔ s Q) "wpk".
    rewrite ?wp_unfold.
    cbn.
    iIntros (σ ns ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; first trivial.
    iIntros (e2 σ2 efs) "%".
    dependent elimination H.
    dependent elimination s0.
    - iMod "Hclose" as "_".
      rewrite {1}/wp_pre.
      rewrite (val_stuck (MkConf s9 δΔ3) (γ1 , μ1) [] _ _ [] (mk_prim_step s10)).
      iMod ("wpk" $! (γ1 , μ1) ns nil ks nt with "Hregs") as "[% wpk]". cbn.
      iMod ("wpk" $! _ _ _ (mk_prim_step s10)) as "wpk".
      iModIntro. iModIntro.
      iMod "wpk".
      iModIntro.
      iMod "wpk" as "[Hregs [wpk' _]]".
      iModIntro.
      iFrame.
      iSplitL; last trivial.
      iApply "IH".
      iFrame.
    - cbn.
      iModIntro. iModIntro. iModIntro.
      iMod "Hclose" as "_".
      iMod "wpk" as "Qv".
      iModIntro.
      iFrame.
      iSplitL; last trivial.
      by iApply wp_value.
    - iModIntro. iModIntro. iModIntro.
      iMod "Hclose" as "_".
      iFrame.
      iModIntro.
      iSplitL; [|trivial].
      iApply wp_compat_fail.
  Qed.

  Lemma iris_rule_stm_bind {Γ} (δ : CStore Γ)
        {σ τ : Ty} (s : Stm Γ σ) (k : Val σ -> Stm Γ τ)
        (P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ)
        (R : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ P s Q -∗
           (∀ (v__σ : Val σ) (δ' : CStore Γ),
               semTriple δ' (Q v__σ δ') (k v__σ) R) -∗
           semTriple δ P (stm_bind s k) R)%I.
  Proof.
    iIntros "trips tripk P".
    iPoseProof ("trips" with "P") as "wpv".
    iRevert (s δ) "wpv".
    iLöb as "IH".
    iIntros (s δ) "wpv".
    rewrite (wp_unfold _ _ (MkConf (stm_bind _ k) _)). cbn.
    iIntros ([regs μ] ns ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 [regs2 μ2] efs) "%".
    unfold language.prim_step in H; cbn in H.
    dependent elimination H.
    dependent elimination s0.
    + rewrite wp_unfold. cbn.
      unfold wp_pre.
      rewrite (val_stuck (MkConf s17 δ1) (γ1 , μ1) [] _ _ [] (mk_prim_step s18)).
      iSpecialize ("wpv" $! (γ1 , μ1) ns nil nil nt with "Hregs"). cbn.
      iMod "Hclose".
      iMod "wpv" as "[_ wpv]".
      iSpecialize ("wpv" $! _ _ nil (mk_prim_step s18)).
      iMod "wpv" as "wpv".
      iModIntro. iModIntro.
      iMod "wpv".
      iModIntro.
      iMod "wpv" as "[Hregs [wps _]]".
      iModIntro.
      iFrame.
      iApply ("IH" with "tripk wps").
    + iModIntro. iModIntro. iModIntro.
      iMod "Hclose" as "_".
      rewrite wp_unfold; cbn.
      iMod "wpv" as "wpv".
      iPoseProof ("tripk" with "wpv") as "wpk".
      iModIntro.
      by iFrame.
    + iModIntro. iModIntro. iModIntro.
      iMod "Hclose" as "_".
      cbn.
      iFrame; iSplitL; auto.
      by iApply wp_compat_fail.
  Qed.

  Lemma iris_rule_stm_call_inline_later
    {Γ} (δ : CStore Γ)
    {Δ σ} (f : 𝑭 Δ σ) (es : NamedEnv (Exp Γ) Δ)
    (P : iProp Σ) (Q : Val σ -> iProp Σ) :
    ⊢ ▷ semTriple (evals es δ) P (FunDef f) (fun v _ => Q v) -∗
      semTriple δ P (stm_call f es) (fun v δ' => Q v ∧ bi_pure (δ = δ')).
  Proof.
    iIntros "tripbody P".
    rewrite wp_unfold. cbn.
    iIntros (σ' ns ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e2 σ'' efs) "%".
    dependent elimination H.
    dependent elimination s.
    iModIntro. iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro. iFrame.
    iSplitL; [|trivial].
    iApply wp_compat_call_frame.
    iApply (wp_mono _ _ _ (fun v => match v with MkValConf _ v0 _ => Q v0 end)).
    {
      iIntros ([σ' v]) "Qv".
      by iFrame.
    }
    iApply ("tripbody" with "P").
  Qed.

  Lemma iris_rule_stm_call_inline
    {Γ} (δ : CStore Γ)
    {Δ σ} (f : 𝑭 Δ σ) (es : NamedEnv (Exp Γ) Δ)
    (P : iProp Σ) (Q : Val σ -> iProp Σ) :
    ⊢ semTriple (evals es δ) P (FunDef f) (fun v _ => Q v) -∗
      semTriple δ P (stm_call f es) (fun v δ' => Q v ∧ bi_pure (δ = δ')).
  Proof.
    iIntros "Hdef".
    iApply (iris_rule_stm_call_inline_later with "Hdef").
  Qed.

  Definition ValidLemma {Δ} (lem : Lemma Δ) : Prop :=
    match lem with
      {| lemma_logic_variables := Σ;
         lemma_patterns        := θΔ;
         lemma_precondition    := req;
         lemma_postcondition   := ens;
      |} =>
      forall (ι : Valuation Σ),
        ⊢ interpret_assertion req ι -∗
          interpret_assertion ens ι
    end.

  Lemma iris_rule_stm_debugk
    {Γ τ} (δ : CStore Γ) (k : Stm Γ τ)
    (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
    ⊢ (semTriple δ P k Q -∗
       semTriple δ P (stm_debugk k) Q)%I.
  Proof.
    iIntros "tripk P".
    rewrite wp_unfold. cbn.
    iIntros (σ ns ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e3 σ2 efs) "%".
    dependent elimination H.
    dependent elimination s.
    iModIntro. iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro; iFrame.
    iSplitL; [|trivial].
    iApply "tripk".
    by iFrame.
  Qed.

  Lemma iris_rule_noop {Γ σ} {δ : CStore Γ}
        {P} {Q : Val σ -> CStore Γ -> iProp Σ} {s : Stm Γ σ} :
    language.to_val (MkConf s δ) = None ->
    (forall {s' γ γ' μ μ' δ'}, ⟨ γ, μ, δ, s ⟩ ---> ⟨ γ', μ', δ', s' ⟩ ->
                            (γ' = γ) /\ (μ' = μ) /\ (δ' = δ) /\
                            ((exists v, s' = stm_val _ v) \/ (exists msg, s' = stm_fail _ msg))) ->
    (∀ v, P ={⊤}=∗ Q v δ) -∗
                 semTriple δ P s Q.
  Proof.
    iIntros (Hnv Hnoop) "HPQ HP".
    rewrite wp_unfold.
    unfold wp_pre.
    rewrite Hnv. cbn.
    iIntros (σ' ns ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; first done.
    iIntros (e2 σ'' efs) "%".
    dependent elimination H.
    destruct (Hnoop _ _ _ _ _ _ s0) as (-> & -> & -> & [[v ->]|[msg ->]]).
    - do 3 iModIntro.
      iMod "Hclose" as "_".
      iMod ("HPQ" with "HP") as "HQ".
      iModIntro.
      iFrame.
      iSplitL; trivial.
      now iApply wp_value.
    - do 3 iModIntro.
      iMod "Hclose" as "_".
      iModIntro.
      iFrame.
      iSplitL; trivial.
      now iApply wp_compat_fail.
  Qed.

End Soundness.

Section Adequacy.

  Import SmallStepNotations.

  Definition sailΣ : gFunctors := #[ memΣ ; invΣ ; GFunctor regUR].

  Instance subG_sailGpreS {Σ} : subG sailΣ Σ -> sailGpreS Σ.
  Proof.
    intros.
    lazymatch goal with
    | H:subG ?xΣ _ |- _ => try unfold xΣ in H
    end.
    repeat match goal with
           | H:subG (gFunctors.app _ _) _ |- _ => apply subG_inv in H; destruct H
           end.
    split; eauto using memΣ_GpreS, subG_invΣ.
    solve_inG.
 Qed.

  Definition RegStore_to_map (γ : RegStore) : gmap SomeReg (exclR (leibnizO SomeVal)) :=
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
          let (x0, r0) := x in (existT x0 r0 , Excl (existT x0 (read_register γ r0))))) id _ _ _ eq_refl).
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
    rtc erased_step (cons (MkConf s δ) nil, (γ,μ)) (cons (MkConf s' δ') nil, (γ',μ')).
  Proof.
    induction 1; first done.
    refine (rtc_l _ _ _ _ _ IHSteps).
    exists nil.
    refine (step_atomic _ _ _ _ _ nil nil eq_refl eq_refl _).
    by eapply mk_prim_step.
  Qed.

  Lemma own_RegStore_to_map_reg_pointsTos `{sailRegGS Σ'} {γ : RegStore} {l : list (sigT 𝑹𝑬𝑮)} :
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
    - rewrite big_sepL_cons. cbn.
      rewrite (insert_singleton_op (A := exclR (leibnizO SomeVal)) (list_to_map (_ <$> l))  (existT x r) (Excl (existT _ (read_register γ r)))).
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
          let (x0, r0) := x in (existT x0 r0, Excl (existT x0 (read_register γ r0))))) id _ _ _ eq_refl).
        now rewrite list_fmap_id.
        now intros [σ2 r2].
  Qed.

  Lemma adequacy {Γ σ} (s : Stm Γ σ) {γ γ'} {μ μ'}
        {δ δ' : CStore Γ} {s' : Stm Γ σ} {Q : Val σ -> Prop} :
    ⟨ γ, μ, δ, s ⟩ --->* ⟨ γ', μ', δ', s' ⟩ -> Final s' ->
    (forall `{sailGS Σ'},
        ⊢ semTriple (Σ := Σ') δ
          (mem_res sailGS_memGS μ ∗
           [∗ list] _ ↦ x ∈ finite.enum (sigT 𝑹𝑬𝑮),
              match x with | existT _ r => reg_pointsTo r (read_register γ r) end
          )%I s (fun v δ' => bi_pure (Q v)))%I ->
    ResultOrFail s' Q.
  Proof.
    intros steps fins trips.
    cut (adequate MaybeStuck (MkConf s δ) (γ,μ)
             (λ (v : val (microsail_lang Γ σ)) (_ : state (microsail_lang Γ σ)),
                (λ v0 : val (microsail_lang Γ σ), match v0 with
                                                  | MkValConf _ v' _ => Q v'
                                                  end) v)).
    - destruct s'; cbn in fins; destruct fins; last done.
      intros adeq.
      apply (adequate_result MaybeStuck (MkConf s δ) (γ , μ) (fun v _ => match v with | MkValConf _ v' δ' => Q v' end) adeq nil (γ' , μ') (MkValConf _ v δ')).
      by apply steps_to_erased.
    - constructor; last done.
      intros t2 σ2 [v2 δ2] eval.
      assert (eq := RegStore_to_map_Forall γ).
      assert (regsmapv := RegStore_to_map_valid γ).
      pose proof (wp_adequacy sailΣ (microsail_lang Γ σ) MaybeStuck (MkConf s δ) (γ , μ) (fun v => match v with | MkValConf _ v' δ' => Q v' end)) as adeq.
      refine (adequate_result _ _ _ _ (adeq _) _ _ _ eval); clear adeq.
      iIntros (Hinv κs) "".
      iMod (own_alloc ((● RegStore_to_map γ ⋅ ◯ RegStore_to_map γ ) : regUR)) as (spec_name) "[Hs1 Hs2]";
        first by apply auth_both_valid.
      pose proof (memΣ_GpreS (Σ := sailΣ) _) as mPG.
      iMod (mem_inv_init μ mPG) as (memG) "[Hmem Rmem]".
      iModIntro.
      iExists (fun σ _ => regs_inv (H := (SailRegGS _ spec_name)) (σ.1) ∗ mem_inv memG (σ.2))%I.
      iExists _.
      iSplitR "Hs2 Rmem".
      * iSplitL "Hs1".
        + iExists (RegStore_to_map γ).
          by iFrame.
        + iFrame.
      * iPoseProof (trips sailΣ (SailGS Hinv (SailRegGS reg_pre_inG spec_name) memG) with "[Rmem Hs2]") as "trips'".
        + iFrame.
          unfold RegStore_to_map.
          iApply (own_RegStore_to_map_reg_pointsTos (H := SailRegGS reg_pre_inG spec_name)(γ := γ) (l := finite.enum (sigT 𝑹𝑬𝑮)) with "Hs2").
          eapply finite.NoDup_enum.
        + iApply (wp_mono with "trips'").
          by iIntros ([δ3 v]).
  Qed.
End Adequacy.
End IrisInstance.

(*
 * The following module defines the parts of the Iris model that must depend on the Specification, not just on the ProgramLogicSignature.
 * This is kept to a minimum (see comment for the IrisInstance module).
 *)
Module IrisInstanceWithContracts
  (Import B    : Base)
  (Import SIG  : ProgramLogicSignature B)
  (Import SPEC  : Specification B SIG)
  (Import SEM  : Semantics B SIG.PROG)
  (Import IP   : IrisParameters B SIG.PROG SIG SEM)
  (Import II   : IrisInstance B SIG SEM IP)
  (Import PLOG : ProgramLogicOn B SIG SPEC).

  Context `{sailGS Σ}.

  Definition ForeignSem :=
    ∀ (Γ : NCtx 𝑿 Ty) (τ : Ty)
      (Δ : NCtx 𝑿 Ty) f (es : NamedEnv (Exp Γ) Δ) (δ : CStore Γ),
      match CEnvEx f with
      | MkSepContract _ _ Σ' θΔ req result ens =>
        forall (ι : Valuation Σ'),
        evals es δ = inst θΔ ι ->
        ⊢ semTriple δ (interpret_assertion req ι) (stm_foreign f es)
          (fun v δ' => interpret_assertion ens (env.snoc ι (result∷τ) v) ∗ bi_pure (δ' = δ))
      end.

  Definition LemmaSem : Prop :=
    forall (Δ : NCtx 𝑿 Ty) (l : 𝑳 Δ),
      ValidLemma (LEnv l).

  Lemma iris_rule_stm_call_forwards `{sG : sailGS Σ} {Γ} (δ : CStore Γ)
        {Δ σ} (f : 𝑭 Δ σ) (c : SepContract Δ σ) (es : NamedEnv (Exp Γ) Δ)
        (P : iProp Σ)
        (Q : Val σ -> iProp Σ) :
        CEnv f = Some c ->
        CTriple (evals es δ) P Q c ->
        (⊢ ▷ ValidContractEnvSem CEnv -∗
           semTriple δ P (stm_call f es) (fun v δ' => Q v ∧ bi_pure (δ = δ')))%I.
  Proof.
    iIntros (ceq ctrip) "cenv P".
    rewrite wp_unfold. cbn.
    iIntros ([regs μ] ns ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; [trivial|].
    iIntros (e2 [regs2 μ2] efs) "%".
    unfold language.prim_step in H0; cbn in H0.
    dependent elimination H0.
    dependent elimination s.
    iModIntro. iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro.
    iFrame.
    iSplitL; [|trivial].
    destruct ctrip.
    iPoseProof (H1 with "P") as "[fr req]".
    iApply wp_compat_call_frame.
    rewrite H0.
    iApply (wp_mono _ _ _ (fun v => frame ∗ match v with
                                            | MkValConf _ v _ => interpret_assertion ens (env.snoc ι (result∷σ) v)
                                            end)%I).
    - intros [v δ']; cbn.
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
        (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δΔ P s (fun v _ => Q v δ) -∗
           semTriple δ P (stm_call_frame δΔ s) Q)%I.
  Proof.
    iIntros "trips P".
    iSpecialize ("trips" with "P").
    by iApply wp_compat_call_frame.
  Qed.

  Lemma iris_rule_stm_foreign
    {Γ} (δ : CStore Γ) {τ} {Δ} (f : 𝑭𝑿 Δ τ) (es : NamedEnv (Exp Γ) Δ)
    (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
    ForeignSem ->
    CTriple (evals es δ) P (λ v : Val τ, Q v δ) (CEnvEx f) ->
    ⊢ semTriple δ P (stm_foreign f es) Q.
  Proof.
    iIntros (extSem ctrip).
    specialize (extSem _ _ _ f es δ).
    revert ctrip extSem.
    generalize (CEnvEx f) as contractF.
    intros contractF ctrip extSem.
    destruct ctrip; cbn in extSem.
    iIntros "P".
    iPoseProof (H1 with "P") as "[frm pre]".
    iApply (wp_mono _ _ _ (fun v => frame ∗ match v with MkValConf _ v δ' => interpret_assertion (HProp := IProp Σ) ens (env.snoc ι (result∷τ) v) ∗ bi_pure (δ' = δ) end)%I).
    - intros v.
      destruct v.
      iIntros "[frame [pre %]]".
      subst.
      iApply H2.
      by iFrame.
    - iApply wp_frame_l.
      iFrame.
      by iApply (extSem ι H0).
  Qed.

  Lemma iris_rule_stm_lemmak
    {Γ} (δ : CStore Γ) {τ} {Δ} (l : 𝑳 Δ) (es : NamedEnv (Exp Γ) Δ) (k : Stm Γ τ)
    (P Q : iProp Σ) (R : Val τ -> CStore Γ -> iProp Σ) :
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
    rewrite wp_unfold. cbn.
    iIntros (σ ns ks1 ks nt) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iSplitR; [trivial|].
    iIntros (e3 σ2 efs) "%".
    dependent elimination H0.
    dependent elimination s.
    iModIntro. iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro; iFrame.
    iSplitL; [|trivial].
    iApply "tripk".
    iApply l1.
    iPoseProof (l0 with "P") as "[frm pre]".
    iFrame.
    by iApply lemSem.
  Qed.

  Lemma sound_stm
    {Γ} {τ} (s : Stm Γ τ) {δ : CStore Γ}:
    forall (PRE : iProp Σ) (POST : Val τ -> CStore Γ -> iProp Σ),
      ForeignSem ->
      LemmaSem ->
      ⦃ PRE ⦄ s ; δ ⦃ POST ⦄ ->
      ⊢ (□ ▷ ValidContractEnvSem CEnv -∗
          semTriple δ PRE s POST)%I.
  Proof.
    iIntros (PRE POST extSem lemSem triple) "#vcenv".
    iInduction triple as [x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x] "trips".
    - by iApply iris_rule_consequence.
    - by iApply iris_rule_frame.
    - by iApply iris_rule_pull.
    - by iApply iris_rule_exist.
    - iApply iris_rule_stm_val.
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
    - by iApply iris_rule_stm_match_bvec.
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

  Lemma sound :
    ForeignSem -> LemmaSem -> ValidContractCEnv ->
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

End IrisInstanceWithContracts.
