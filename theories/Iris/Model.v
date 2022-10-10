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

From iris Require Import
     algebra.auth
     algebra.excl
     algebra.gmap
     program_logic.adequacy
     program_logic.weakestpre
     proofmode.tactics.

From Katamaran Require Import
     Prelude
     Sep.Logic
     Semantics.

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

(* TODO: export, back to module instead of module type *)
Module Type IrisPrelims
    (Import B    : Base)
    (Import PROG : Program B)
    (Import SEM  : Semantics B PROG).

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

    #[export] Instance intoVal_valconf {Γ τ δ v} : IntoVal (MkConf (Γ := Γ) (τ := τ) (stm_val _ v) δ) (MkValConf _ v δ).
      intros; eapply of_to_val; by cbn.
    Defined.

  End Language.

  Section Registers.

    Definition SomeReg : Type := sigT 𝑹𝑬𝑮.
    Definition SomeVal : Type := sigT Val.

    #[export] Instance eqDec_SomeReg : EqDec SomeReg := 𝑹𝑬𝑮_eq_dec.
    #[export] Instance countable_SomeReg : countable.Countable SomeReg := finite.finite_countable.

    #[export] Instance eqDec_SomeVal : EqDec SomeVal.
    Proof.
      intros [τ1 v1] [τ2 v2].
      destruct (eq_dec τ1 τ2).
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
                            reg_inG : inG Σ regUR;
                            reg_gv_name : gname;
                          }.
    #[export] Existing Instance reg_inG.

    Context `{srGS: sailRegGS Σ}.
    Definition reg_pointsTo {τ} (r : 𝑹𝑬𝑮 τ) (v : Val τ) : iProp Σ :=
      own reg_gv_name (◯ {[ existT _ r := Excl (existT _ v) ]}).

    Definition regs_inv (regstore : RegStore) : iProp Σ :=
      (∃ regsmap,
          own reg_gv_name (● regsmap) ∗
          ⌜ map_Forall (K := SomeReg) (A := excl SomeVal) (fun reg v => match reg with | existT _ reg => Excl (existT _ (read_register regstore reg)) = v end ) regsmap ⌝
      )%I.

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

  End Registers.
End IrisPrelims.

Module Type IrisParameters
  (Import B    : Base)
  (Import PROG : Program B)
  (Import SEM  : Semantics B PROG)
  (Import IP   : IrisPrelims B PROG SEM).
  Parameter memGpreS : gFunctors -> Set.
  (* The memGS field will normally always be instantiated to a type class. We
     inline this field, so that instances declared by the library, e.g. the
     [sailGS_memGS] superclass instance below, will always be instances for the
     user-provided class instead of the [memGS] alias. In your client code, you
     should always refer to your typeclass and refrain from using the [memGS]
     alias completely. *)
  Parameter Inline memGS : gFunctors -> Set.
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
End IrisParameters.

Module Type IrisResources
  (Import B    : Base)
  (Import PROG : Program B)
  (Import SEM  : Semantics B PROG)
  (Import IPre : IrisPrelims B PROG SEM)
  (Import IP   : IrisParameters B PROG SEM IPre).
  Class sailGpreS Σ := SailGpreS { (* resources for the implementation side *)
                       sailGpresS_invGpreS : invGpreS Σ; (* for fancy updates, invariants... *)

                       (* ghost variable for tracking state of registers *)
                       reg_pre_inG : inG Σ regUR;

                       (* ghost variable for tracking state of memory cells *)
                       sailPreG_gen_memGpreS : memGpreS Σ
                     }.
  #[export] Existing Instance sailGpresS_invGpreS.
  #[export] Existing Instance reg_pre_inG.
  Class sailGS Σ := SailGS { (* resources for the implementation side *)
                       sailGS_invGS : invGS Σ; (* for fancy updates, invariants... *)
                       sailGS_sailRegGS : sailRegGS Σ;

                       (* ghost variable for tracking state of memory cells *)
                       sailGS_memGS : memGS Σ
                     }.
  #[export] Existing Instance sailGS_invGS.
  #[export] Existing Instance sailGS_sailRegGS.

  (* We declare the memGS field as a class so that we can define the
     [sailGS_memGS] field as an instance as well. Currently, the [Existing
     Class] command does not support specifying a locality
     (local/export/global), so it is not clear what the scope of this command
     is. Because [memGS] will be inline on module functor applications, the
     [sailGS_memGS] instance will refer to the user-provided class instead of
     the [memGS] field. *)
  Existing Class memGS.
  #[export] Existing Instance sailGS_memGS.

  #[export] Instance sailGS_irisGS {Γ τ} `{sailGS Σ} : irisGS (microsail_lang Γ τ) Σ := {
    iris_invGS := sailGS_invGS;
    state_interp σ ns κs nt := (regs_inv σ.1 ∗ mem_inv sailGS_memGS σ.2)%I;
    fork_post _ := True%I; (* no threads forked in sail, so this is fine *)
    num_laters_per_step _ := 0;
    state_interp_mono _ _ _ _ := fupd_intro _ _;
                                                                                }.
  Global Opaque iris_invGS.

  Definition semWP {Σ} `{sG : sailGS Σ} [Γ τ] (s : Stm Γ τ)
    (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ) : iProp Σ :=
    WP {| conf_stm := s; conf_store := δ |} ?{{ v, Q (valconf_val v) (valconf_store v) }}.

  Definition semTriple {Σ} `{sG : sailGS Σ} {Γ τ} (δ : CStore Γ) (PRE : iProp Σ) (s : Stm Γ τ)
    (POST : Val τ -> CStore Γ -> iProp Σ) : iProp Σ :=
    PRE -∗ semWP s POST δ.
  (* always modality needed? perhaps not because sail not higher-order? *)

  Ltac fold_semWP :=
    first
      [ progress
          change_no_check
          (wp MaybeStuck top
              {| conf_stm := ?s; conf_store := ?δ |}
              (fun v => ?Q (valconf_val v) (valconf_store v)))
        with (semWP s Q δ)
      | progress
          change_no_check
          (wp MaybeStuck top
              {| conf_stm := ?s; conf_store := ?δ |}
              ?Q)
        with (semWP s (fun v δ' => Q (MkValConf _ v δ')) δ);
        try (progress (cbn [valconf_val valconf_store]))
      ].

  Section WeakestPre.

    Context `{sG : sailGS Σ}.

    Lemma semWP_mono [Γ τ] (s : Stm Γ τ) (P Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ) :
      ⊢ (semWP s P δ -∗ (∀ v δ, P v δ -∗ Q v δ) -∗ semWP s Q δ).
    Proof.
      unfold semWP. iIntros "WP PQ".
      iApply (wp_strong_mono with "WP"); auto.
      iIntros ([v δΓ]) "X"; cbn.
      iModIntro. by iApply "PQ".
    Qed.

    Lemma semWP_val {Γ τ} (v : Val τ) (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ) :
      semWP (stm_val τ v) Q δ ⊣⊢ |={⊤}=> Q v δ.
    Proof. unfold semWP. rewrite wp_unfold. reflexivity. Qed.

    Lemma semWP_fail {Γ τ s} (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ) :
      semWP (stm_fail _ s) Q δ ⊣⊢ True.
    Proof.
      apply bi.entails_anti_sym.
      - auto.
      - iIntros "_".
        unfold semWP. rewrite wp_unfold. cbn.
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

    Lemma semWP_exp {Γ τ} (e : Exp Γ τ) :
      ⊢ ∀ (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ),
          Q (eval e δ) δ -∗ semWP (stm_exp e) Q δ.
    Proof.
      iIntros (Q δ) "P". unfold semWP.
      iApply (wp_mask_mono _ empty); auto.
      rewrite wp_unfold.
      iIntros ([regs μ] ns k ks nt) "[Hregs Hmem]".
      iModIntro.
      iSplitR; [trivial|].
      iIntros (e2 σ2 efs) "%".
      remember (MkConf (stm_exp e) δ) as t.
      destruct H.
      dependent elimination Heqt.
      dependent elimination H. cbn.
      iModIntro. iModIntro. iModIntro.
      iFrame.
      iSplitL; trivial.
      by iApply wp_value.
    Qed.

    Lemma semWP_block {Γ τ Δ} (δΔ : CStore Δ) (s : Stm (Γ ▻▻ Δ) τ) :
      ⊢ ∀ (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ),
          semWP s (fun v δ1 => Q v (env.drop Δ δ1)) (δ ►► δΔ) -∗
          semWP (stm_block δΔ s) Q δ.
    Proof.
      iIntros (Q). iRevert (δΔ s).
      iLöb as "IH". iIntros (δΔ k δΓ) "WPk".
      unfold semWP at 4. rewrite wp_unfold. cbn.
      iIntros (σ ns ks1 ks nt) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro.
      iSplitR; [trivial|].
      iIntros (e2 [regs2 μ2] efs) "%".
      dependent elimination H.
      fold_semWP.
      dependent elimination s.
      - iModIntro. iModIntro. iModIntro.
        iMod "Hclose" as "_".
        rewrite semWP_val.
        rewrite env.drop_cat.
        iMod "WPk" as "WPk".
        iModIntro.
        iFrame.
        iSplitL; [|trivial].
        by iApply semWP_val.
      - iModIntro. iModIntro. iModIntro.
        iMod "Hclose" as "_".
        iFrame; iSplitL; auto.
        by iApply semWP_fail.
      - unfold semWP at 3. rewrite wp_unfold. cbn.
        unfold wp_pre.
        rewrite (val_stuck (MkConf k1 _) (γ1 , μ1) [] _ _ [] (mk_prim_step s1)).
        iSpecialize ("WPk" $! (γ1 , μ1) ns nil nil nt with "state_inv"). cbn.
        iMod "Hclose".
        iMod "WPk" as "[_ WPk]".
        iSpecialize ("WPk" $! _ _ nil (mk_prim_step s1)).
        iMod "WPk" as "WPk".
        iModIntro. iModIntro.
        iMod "WPk".
        iModIntro.
        iMod "WPk" as "[Hregs [wps _]]".
        fold_semWP.
        iModIntro.
        iFrame.
        by iApply "IH".
    Qed.

    Lemma semWP_call_frame {Γ τ Δ} (δΔ : CStore Δ) (s : Stm Δ τ) :
      ⊢ ∀ (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ),
          semWP s (fun v _ => Q v δ) δΔ -∗
          semWP (stm_call_frame δΔ s) Q δ.
    Proof.
      iIntros (Q δΓ). iRevert (δΔ s).
      iLöb as "IH". iIntros (δΔ s) "WPs".
      unfold semWP at 4. rewrite wp_unfold. cbn.
      iIntros (σ ns ks1 ks nt) "Hregs".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro.
      iSplitR; first trivial.
      iIntros (e2 σ2 efs) "%".
      dependent elimination H.
      fold_semWP.
      dependent elimination s0.
      - iMod "Hclose" as "_".
        unfold semWP at 3.
        rewrite wp_unfold.
        rewrite {1}/wp_pre.
        rewrite (val_stuck (MkConf s5 _) (γ1 , μ1) [] _ _ [] (mk_prim_step s6)).
        iMod ("WPs" $! (γ1 , μ1) ns nil ks nt with "Hregs") as "[% WPs]". cbn.
        iMod ("WPs" $! _ _ _ (mk_prim_step s6)) as "WPs".
        fold_semWP.
        iModIntro. iModIntro.
        iMod "WPs".
        iModIntro.
        iMod "WPs" as "[Hregs [WPs' _]]".
        iModIntro.
        iFrame.
        iSplitL; last trivial.
        by iApply "IH".
      - iModIntro. iModIntro. iModIntro.
        iMod "Hclose" as "_".
        iModIntro.
        iFrame.
        iSplitL; last trivial.
        by rewrite !semWP_val.
      - iModIntro. iModIntro. iModIntro.
        iMod "Hclose" as "_".
        iFrame.
        iModIntro.
        iSplitL; [|trivial].
        by iApply semWP_fail.
    Qed.

    Lemma semWP_call_inline_later {Γ τ Δ} (f : 𝑭 Δ τ) (es : NamedEnv (Exp Γ) Δ) :
      ⊢ ∀ (Q : Val τ → CStore Γ → iProp Σ) (δΓ : CStore Γ),
          ▷ semWP (FunDef f) (fun vτ _ => Q vτ δΓ) (evals es δΓ) -∗
          semWP (stm_call f es) Q δΓ.
    Proof.
      iIntros (Q δΓ) "wpbody".
      unfold semWP at 2.
      rewrite wp_unfold. cbn.
      iIntros (σ' ns ks1 ks nt) "Hregs".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro. iSplitR; [trivial|].
      iIntros (e2 σ'' efs) "%".
      dependent elimination H.
      dependent elimination s.
      fold_semWP.
      iModIntro. iModIntro. iModIntro.
      iMod "Hclose" as "_".
      iModIntro. iFrame.
      iSplitL; [|trivial].
      by iApply semWP_call_frame.
    Qed.

    Lemma semWP_call_inline {Γ τ Δ} (f : 𝑭 Δ τ) (es : NamedEnv (Exp Γ) Δ) :
      ⊢ ∀ (Q : Val τ → CStore Γ → iProp Σ) (δΓ : CStore Γ),
          semWP (FunDef f) (fun vτ _ => Q vτ δΓ) (evals es δΓ) -∗
          semWP (stm_call f es) Q δΓ.
    Proof.
      iIntros (Q δΓ) "wpbody".
      by iApply semWP_call_inline_later.
    Qed.

    Lemma semWP_bind {Γ τ σ} (s : Stm Γ σ) (k : Val σ → Stm Γ τ) :
      ⊢ ∀ (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ),
          semWP s (fun v => semWP (k v) Q) δ -∗ semWP (stm_bind s k) Q δ.
    Proof.
      iIntros (Q). iRevert (s). iLöb as "IH". iIntros (s δ) "WPs".
      unfold semWP at 6. rewrite wp_unfold. cbn.
      iIntros ([regs μ] ns ks1 ks nt) "Hregs".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro.
      iSplitR; [trivial|].
      iIntros (e2 [regs2 μ2] efs) "%".
      dependent elimination H.
      fold_semWP.
      dependent elimination s0.
      + unfold semWP at 4. rewrite wp_unfold.
        unfold wp_pre.
        rewrite (val_stuck (MkConf s11 δ1) (γ1 , μ1) [] _ _ [] (mk_prim_step s12)).
        iSpecialize ("WPs" $! (γ1 , μ1) ns nil nil nt with "Hregs"). cbn.
        iMod "Hclose".
        iMod "WPs" as "[_ WPs]".
        iSpecialize ("WPs" $! _ _ nil (mk_prim_step s12)).
        iMod "WPs" as "WPs".
        iModIntro. iModIntro.
        iMod "WPs".
        iModIntro.
        iMod "WPs" as "[Hregs [wps _]]".
        fold_semWP.
        iModIntro.
        iFrame.
        by iApply "IH".
      + iModIntro. iModIntro. iModIntro.
        iMod "Hclose" as "_".
        rewrite semWP_val.
        iMod "WPs" as "WPs".
        iModIntro.
        by iFrame.
      + iModIntro. iModIntro. iModIntro.
        iMod "Hclose" as "_".
        iFrame; iSplitL; auto.
        by iApply semWP_fail.
    Qed.

    Lemma semWP_let {Γ τ x σ} (s1 : Stm Γ σ) (s2 : Stm (Γ ▻ x∷σ) τ) :
      ⊢ ∀ (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ),
          semWP s1 (fun v1 δ1 => semWP s2 (fun v2 δ2 => Q v2 (env.tail δ2)) δ1.[x∷σ ↦ v1]) δ -∗
          semWP (let: x ∷ σ := s1 in s2) Q δ.
    Proof.
      iIntros (Q δ) "WPs".
      unfold semWP at 3.
      rewrite wp_unfold. cbn.
      iIntros ([regs μ] ns ks1 ks nt) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro.
      iSplitR; [trivial|].
      iIntros (e2 [regs2 μ2] efs) "%".
      dependent elimination H.
      fold_semWP.
      dependent elimination s.
      iModIntro. iModIntro. iModIntro.
      iMod "Hclose" as "_".
      iModIntro.
      iFrame; iSplitL; auto.
      iApply semWP_bind.
      iApply (semWP_mono with "WPs"); cbn.
      iIntros (v δ) "wpk".
      by iApply (semWP_block [env].[_∷_ ↦ v]).
    Qed.

    Lemma semWP_seq {Γ τ σ} (s1 : Stm Γ σ) (s2 : Stm Γ τ) :
      ⊢ ∀ (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ),
          semWP s1 (fun _ => semWP s2 Q) δ -∗ semWP (s1;;s2) Q δ.
    Proof.
      iIntros (Q δ) "WPs1". unfold semWP at 3. rewrite wp_unfold. cbn.
      iIntros ([regs μ] ns ks1 ks nt) "Hregs".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro.
      iSplitR; [trivial|].
      iIntros (e2 σ2 efs) "%".
      dependent elimination H.
      fold_semWP.
      dependent elimination s.
      iModIntro. iModIntro. iModIntro.
      iMod "Hclose" as "_". iFrame.
      iModIntro.
      iSplitL; [|trivial].
      by iApply semWP_bind.
    Qed.

    Lemma semWP_assertk {Γ τ} (e1 : Exp Γ ty.bool) (e2 : Exp Γ ty.string) (k : Stm Γ τ) :
      ⊢ ∀ (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ),
          (⌜eval e1 δ = true⌝ → semWP k Q δ) -∗ semWP (stm_assertk e1 e2 k) Q δ.
    Proof.
      iIntros (Q δ) "WPs". unfold semWP at 2. rewrite wp_unfold. cbn.
      iIntros (σ ns ks1 ks nt) "Hregs".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro. iSplitR; [trivial|].
      iIntros (e3 σ2 efs) "%".
      dependent elimination H.
      fold_semWP.
      dependent elimination s.
      iModIntro. iModIntro. iModIntro.
      iMod "Hclose" as "_".
      iModIntro; iFrame.
      iSplitL; [|trivial].
      destruct eval.
      - by iApply "WPs".
      - by iApply semWP_fail.
    Qed.

    Lemma semWP_read_register {Γ τ} (reg : 𝑹𝑬𝑮 τ) :
      ⊢ ∀ (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ),
          (∃ v : Val τ, reg_pointsTo reg v ∗ (reg_pointsTo reg v -∗ Q v δ)) -∗
          semWP (stm_read_register reg) Q δ.
    Proof.
      iIntros (Q δ) "[% [Hreg HP]]"; cbn.
      unfold semWP. iApply (wp_mask_mono _ empty); auto.
      rewrite wp_unfold; cbn.
      iIntros (σ _ ls _ n) "[Hregs Hmem]".
      iDestruct (@reg_valid with "Hregs Hreg") as %<-.
      iModIntro.
      iSplitR; [trivial|].
      iIntros (e2 σ2 efs) "%".
      dependent elimination H.
      dependent elimination s.
      iModIntro. iModIntro. iModIntro.
      iFrame. iSplitR ""; auto.
      iModIntro.
      iApply wp_value.
      by iApply "HP".
    Qed.

    Lemma semWP_write_register {Γ τ} (reg : 𝑹𝑬𝑮 τ) (e : Exp Γ τ) :
      ⊢ ∀ (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ),
          (∃ v : Val τ, reg_pointsTo reg v ∗ (reg_pointsTo reg (eval e δ) -∗ Q (eval e δ) δ)) -∗
          semWP (stm_write_register reg e) Q δ.
    Proof.
      iIntros (Q δ) "[% [Hreg HP]]"; cbn.
      unfold semWP. iApply (wp_mask_mono _ empty); auto.
      rewrite wp_unfold; cbn.
      iIntros (σ _ ls _ n) "[Hregs Hmem]".
      iMod (reg_update σ.1 reg v (eval e δ) with "Hregs Hreg") as "[Hregs Hreg]".
      iModIntro.
      iSplitR; [trivial|].
      iIntros (e2 σ2 efs) "%".
      dependent elimination H.
      destruct (steps_inversion_write_register s) as [-> [<- [<- ->]]].
      iModIntro. iModIntro. iModIntro.
      iFrame. iSplitL; auto.
      iApply wp_value.
      by iApply "HP".
    Qed.

    Lemma semWP_assign {Γ τ x} (xInΓ : x∷τ ∈ Γ) (s : Stm Γ τ) :
      ⊢ ∀ (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ),
          semWP s (λ (a : Val τ) (δ0 : CStore Γ), Q a (δ0 ⟪ x ↦ a ⟫)) δ -∗
          semWP (x <- s) Q δ.
    Proof.
      iIntros (Q). iRevert (s). iLöb as "IH". iIntros (s δ) "WPs".
      unfold semWP at 4. rewrite wp_unfold. cbn.
      iIntros ([regs μ] ns ks1 ks nt) "Hregs".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro.
      iSplitR; [trivial|].
      iIntros (e2 [regs2 μ2] efs) "%".
      dependent elimination H.
      fold_semWP.
      dependent elimination s0.
      + iModIntro. iModIntro. iModIntro.
        rewrite semWP_val.
        iMod "Hclose" as "_".
        iMod "WPs" as "WPs".
        iModIntro.
        iFrame.
        iSplitL; [|trivial].
        by iApply semWP_val.
      + iModIntro. iModIntro. iModIntro.
        iMod "Hclose" as "_".
        iFrame; iSplitL; auto.
        by iApply semWP_fail.
      + unfold semWP at 3. rewrite wp_unfold. unfold wp_pre.
        rewrite (val_stuck (MkConf s9 δ1) _ [] _ _ [] (mk_prim_step s10)).
        iSpecialize ("WPs" $! _ ns nil nil nt with "Hregs"). cbn.
        iMod "Hclose".
        iMod "WPs" as "[_ WPs]".
        iSpecialize ("WPs" $! _ _ nil (mk_prim_step s10)).
        fold_semWP.
        iMod "WPs" as "WPs".
        iModIntro. iModIntro.
        iMod "WPs".
        iModIntro.
        iMod "WPs" as "[Hregs [WPs _]]".
        iModIntro.
        iFrame.
        by iApply "IH".
    Qed.

    Lemma semWP_pattern_match {Γ τ σ} (s : Stm Γ σ) (pat : Pattern σ)
      (rhs : ∀ pc : PatternCase pat, Stm (Γ ▻▻ PatternCaseCtx pc) τ) :
      ⊢ ∀ (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ),
      semWP s
        (fun vσ δ1 =>
           let (pc,δpc) := pattern_match_val pat vσ in
           semWP (rhs pc)
             (fun vτ δ2 => Q vτ (env.drop (PatternCaseCtx pc) δ2))
             (δ1 ►► δpc)) δ -∗
      semWP (stm_pattern_match s pat rhs) Q δ.
    Proof.
      iIntros (Q δ) "WPs". unfold semWP at 3. rewrite wp_unfold. cbn.
      iIntros (? ns ks1 ks nt) "state_inv".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro.
      iSplitR; [trivial|].
      iIntros (e2 σ' efs) "%".
      dependent elimination H.
      fold_semWP.
      dependent elimination s0.
      iModIntro. iModIntro. iModIntro.
      iMod "Hclose" as "_".
      iModIntro.
      iFrame; iSplitL; auto.
      iApply semWP_bind.
      iApply (semWP_mono with "WPs"); cbn.
      clear - sG.
      iIntros (v δ) "WPrhs".
      destruct pattern_match_val.
      by iApply semWP_block.
    Qed.

  End WeakestPre.

  Module wptactics.
    Ltac kEval :=
      match goal with
      | |- environments.envs_entails ?ctx (semWP ?s ?post ?store) =>
          let s' := eval compute - [Val] in s in
          let store' := eval compute - [Val] in store in
          change_no_check (environments.envs_entails ctx (semWP s' post store'))
      end.

    Ltac kStep :=
      match goal with
      | |- environments.envs_entails ?ctx (semWP ?stm ?post ?store) =>
          match stm with
          | stm_val ?τ ?v => iApply semWP_val
          | stm_exp ?e => iApply (semWP_exp e)
          | stm_let ?x ?τ ?s1 ?s2 => iApply (semWP_let s1 s2)
          | stm_pattern_match ?scrut ?pat ?rhs =>
              iApply (semWP_pattern_match scrut pat rhs)
          | match ?x with _ => _ end => destruct x eqn:?
          end
      end.
  End wptactics.

End IrisResources.

Module Type IrisBase (B : Base) (PROG : Program B) (SEM : Semantics B PROG) :=
  IrisPrelims B PROG SEM <+ IrisParameters B PROG SEM <+ IrisResources B PROG SEM.
