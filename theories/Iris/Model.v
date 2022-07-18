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
End IrisResources.

Module Type IrisBase (B : Base) (PROG : Program B) (SEM : Semantics B PROG) :=
  IrisPrelims B PROG SEM <+ IrisParameters B PROG SEM <+ IrisResources B PROG SEM.
