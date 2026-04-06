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
  Program.Equality.
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
     Iris.Base
     Iris.Instance
     Prelude
     Semantics
     Sep.Hoare
     Signature
     SmallStep.Step
     Specification
     BinaryResources
     BinaryWeakestPre.

Import ctx.notations.
Import env.notations.

Set Implicit Arguments.

Module Type IrisAdeqParameters2
  (Import B    : Base)
  (Import PROG : Program B)
  (Import SEM  : Semantics B PROG)
  (Import IPre : IrisPrelims B PROG SEM)
  (Import IP   : IrisParameters B)
  (Import IPP  : IrisParameters2 B IP).

  Parameter Inline memGpreS2 : gFunctors -> Set.
  Parameter memΣ2 : gFunctors.
  Parameter memΣ_GpreS2 : forall {Σ}, subG memΣ2 Σ -> memGpreS2 Σ.
  Parameter mem_res2 : forall `{mG : memGS2 Σ}, Memory -> Memory -> iProp Σ.

    (* Definition mem_inv `{sailG Σ} (μ : Z -> option Z) : iProp Σ := *)
    (*   (∃ memmap, gen_heap_ctx memmap ∗ *)
    (*      ⌜ map_Forall (fun (a : Z) v => μ a = Some v) memmap ⌝ *)
    (*   )%I. *)

  Parameter mem_init2 : forall `{mGS : memGpreS2 Σ} (μ1 μ2 : Memory),
                                         ⊢ |==> ∃ mG : memGS2 Σ, (mem_inv2 (mG := mG) μ1 μ2 ∗ mem_res2 (mG := mG) μ1 μ2)%I.

End IrisAdeqParameters2.

Module Type IrisAdequacy2
  (Import B      : Base)
  (Import SIG    : Signature B)
  (Import PROG   : Program B)
  (Import FL     : FailLogic)
  (Import SEM    : Semantics B PROG)
  (Import IB2    : IrisBase2 B PROG SEM)
  (Import IAP    : IrisAdeqParameters2 B PROG SEM IB2 IB2 IB2)
  (Import IPred  : IrisPredicates2 B SIG PROG SEM IB2)
  (Import IRules : IrisSignatureRules2 B SIG PROG FL SEM IB2 IPred).

  Import SmallStepNotations.

  Class sailGpreS2 Σ := SailGpreS2 { (* resources for the implementation side *)
                       sailGpresS_invGpreS2 : invGpreS Σ; (* for fancy updates, invariants... *)

                       (* ghost variables for tracking state of registers *)
                       reg_pre_inG2_left : inG Σ regUR;
                       reg_pre_inG2_right : inG Σ regUR;

                       (* ghost variable for tracking state of memory cells *)
                       sailPreG_gen_memGpreS2 : memGpreS2 Σ
                     }.

  #[local] Existing Instance sailGpresS_invGpreS2.

  Definition sailΣ2 : gFunctors := #[ memΣ2 ; invΣ ; GFunctor regUR; GFunctor regUR].

  #[local] Instance subG_sailGpreS {Σ} : subG sailΣ2 Σ -> sailGpreS2 Σ.
  Proof.
    intros.
    lazymatch goal with
    | H:subG ?xΣ _ |- _ => try unfold xΣ in H
    end.
    repeat match goal with
           | H:subG (gFunctors.app _ _) _ |- _ => apply subG_inv in H; destruct H
           end.
    split; eauto using memΣ_GpreS2, subG_invΣ.
    - clear s2. solve_inG.
    - clear s1. solve_inG.
 Qed.

  Lemma steps_to_erased {σ Γ γ μ δ} (s : Stm Γ σ) {γ' μ' δ' s'}:
    ⟨ γ, μ, δ, s ⟩ --->* ⟨ γ', μ', δ', s' ⟩ ->
    rtc erased_step ([MkConf s δ]%list, (γ,μ)) ([MkConf s' δ']%list, (γ',μ')).
  Proof.
    induction 1; first done.
    refine (rtc_l _ _ _ _ _ IHSteps).
    exists nil.
    refine (step_atomic _ _ _ _ _ nil nil eq_refl eq_refl _).
    by eapply mk_prim_step.
  Qed.

  Lemma steps_to_nsteps {σ Γ γ μ δ} (s : Stm Γ σ) {γ' μ' δ' s'}:
    ⟨ γ, μ, δ, s ⟩ --->* ⟨ γ', μ', δ', s' ⟩ ->
    exists n, language.nsteps n ([MkConf s δ]%list , (γ,μ)) [] ([MkConf s' δ']%list , (γ',μ')).
  Proof.
    induction 1.
    - exists 0. now constructor.
    - destruct IHSteps as [n steps].
      exists (S n).
      refine (language.nsteps_l _ _ _ _ [] _ _ steps).
      refine (step_atomic _ _ _ _ _ nil nil eq_refl eq_refl _).
      now eapply mk_prim_step.
  Qed.

  Lemma own_RegStore_to_map_reg_pointsTos `{sailGS2 Σ} {γ1 γ2 : RegStore} {l : list (sigT 𝑹𝑬𝑮)} :
    NoDup l ->
    ⊢ own (A := regUR) (inG0 := @reg_inG _ sailRegGS2_sailRegGS_left) (@reg_gv_name _ sailRegGS2_sailRegGS_left) (◯ list_to_map (K := SomeReg)
                         (fmap (fun x => match x with existT _ r =>
                                                     pair (existT _ r) (Excl (existT _ (read_register γ1 r)))
                                      end) l)) ∗
      own (A := regUR) (inG0 := @reg_inG _ sailRegGS2_sailRegGS_right) (@reg_gv_name _ sailRegGS2_sailRegGS_right) (◯ list_to_map (K := SomeReg)
                         (fmap (fun x => match x with existT _ r =>
                                                     pair (existT _ r) (Excl (existT _ (read_register γ2 r)))
                                      end) l))
    -∗
      [∗ list] x ∈ l,
        let (x0, r) := (x : sigT 𝑹𝑬𝑮) in reg_pointsTo2 r (read_register γ1 r) (read_register γ2 r).
  Proof.
    iIntros (nodups) "[Hregs1 Hregs2]".
    iInduction l as [|[x r]] "IH".
    - now iFrame.
    - rewrite big_sepL_cons. cbn.
      rewrite (insert_singleton_op (A := exclR (leibnizO SomeVal)) (list_to_map (_ <$> l))  (existT x r) (Excl (existT _ (read_register γ1 r)))).
      rewrite (insert_singleton_op (A := exclR (leibnizO SomeVal)) (list_to_map (_ <$> l))  (existT x r) (Excl (existT _ (read_register γ2 r)))).
      rewrite ?auth_frag_op.
      iPoseProof (own_op reg_gv_name with "Hregs1") as "[Hreg1 Hregs1]".
      iDestruct (own_op reg_gv_name with "Hregs2") as "[Hreg2 Hregs2]".
      iFrame.
      iApply ("IH" with "[%] [$Hregs1] [$Hregs2]").
      + refine (NoDup_cons_1_2 (existT x r) l nodups).
      + destruct (proj1 (NoDup_cons (existT x r) _) nodups) as [notin _].
        refine (not_elem_of_list_to_map_1 _ (existT x r) _).
        rewrite <-list_fmap_compose.
        rewrite (list_fmap_ext _ id).
        now rewrite list_fmap_id.
        now intros i [σ2 r2].
      + destruct (proj1 (NoDup_cons (existT x r) _) nodups) as [notin _].
        refine (not_elem_of_list_to_map_1 _ (existT x r) _).
        rewrite <-list_fmap_compose.
        rewrite (list_fmap_ext _ id).
        now rewrite list_fmap_id.
        now intros i [σ2 r2].
  Qed.

  Definition own_regstore2 `{sailGS2 Σ} (γ1 γ2 : RegStore) : iProp Σ :=
    [∗ list] _ ↦ x ∈ finite.enum (sigT 𝑹𝑬𝑮),
      match x with | existT _ r => reg_pointsTo2 r (read_register γ1 r) (read_register γ2 r) end.

  Inductive NSteps {Γ : PCtx} {σ : Ty} (γ1 : RegStore) (μ1 : Memory) (δ1 : CStore Γ) (s1 : Stm Γ σ) : RegStore -> Memory -> CStore Γ -> Stm Γ σ -> nat -> Prop :=
  | nstep_refl : NSteps γ1 μ1 δ1 s1 γ1 μ1 δ1 s1 0
  | nstep_trans {n} {γ2 γ3 : RegStore} {μ2 μ3 : Memory} {δ2 δ3 : CStore Γ} {s2 s3 : Stm Γ σ} :
      Step γ1 μ1 δ1 γ2 μ2 δ2 s1 s2 -> NSteps γ2 μ2 δ2 s2 γ3 μ3 δ3 s3 n -> NSteps γ1 μ1 δ1 s1 γ3 μ3 δ3 s3 (S n).

  Lemma nsteps_to_steps {Γ : PCtx} {σ : Ty} {γ1 γ2 : RegStore} {μ1 μ2 : Memory} {δ1 δ2 : CStore Γ} {s1 s2 : Stm Γ σ} {n} :
    NSteps γ1 μ1 δ1 s1 γ2 μ2 δ2 s2 n -> Steps γ1 μ1 δ1 s1 γ2 μ2 δ2 s2.
  Proof.
    induction 1; econstructor; eassumption.
  Qed.

  (* TODO: move following 3 to where stm_val_stuck is defined? *)
  Lemma final_val_and_fail_None : forall {Γ τ} (s : Stm Γ τ),
      Final s -> stm_to_val s = None -> stm_to_fail s = None -> False.
  Proof. intros ? ? s. by destruct s. Qed.

  Lemma is_not_final : forall {Γ τ} (s : Stm Γ τ),
      stm_to_val s = None ->
      stm_to_fail s = None ->
      ~ Final s.
  Proof. intros ? ? s ? ? ?. by destruct s. Qed.

  Lemma can_step : forall {Γ τ} (s : Stm Γ τ) γ μ δ,
      ~ Final s ->
      ∃ γ' μ' δ' s', ⟨ γ, μ, δ, s ⟩ ---> ⟨ γ', μ', δ', s' ⟩.
  Proof.
    intros ? ? s **.
    pose proof (progress s) as [|Hprogress];
      first intuition.
    by apply Hprogress.
  Qed.

  Lemma not_stuck_ever {Γ τ} :
    ∀ (e : expr (microsail_lang Γ τ)) σ,
      not_stuck e σ.
  Proof.
    intros [s δ] [γ μ]. unfold not_stuck. cbn. destruct (stm_to_val s) eqn:Es.
    - left. auto.
    - right. apply reducible_not_val. auto.
  Qed.

  Definition ResultOrFail2 {Γ1 Γ2 τ} (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ) :
    (Val τ -> Prop) -> Prop :=
    match s1, s2 with
    | stm_val _ v1, stm_val _ v2 => λ POST, v1 = v2 ∧ POST v1
    | stm_fail _ m1, stm_fail _ m2 => λ _, True
    | _, _ => λ _, False
    end.

  (* TODO: give this some more thought. Feels icky that the RHS doesn't play
           a role in deriving φ. Another question is why we generalize over
           a postcond Q, it doesn't relate to φ in any way?
           Definitely check out how this is done in ReLoC. *)
  Lemma wp2_adequacy {Γ1 Γ2 τ} (s1 s1' : Stm Γ1 τ) (s2 s2' : Stm Γ2 τ)
    {γ1 γ1' γ2 γ2' : RegStore} {μ1 μ1' μ2 μ2' : Memory}
    {δ1 δ1' : CStore Γ1} {δ2 δ2' : CStore Γ2}
    {Q : ∀ `{sailGS2 Σ}, IVal τ -> CStore Γ1 -> IVal τ -> CStore Γ2 -> iProp Σ}
    {φ : Prop} :
    ⟨ γ1, μ1, δ1, s1 ⟩ --->* ⟨ γ1', μ1', δ1', s1' ⟩ ->
    (* ⟨ γ2, μ2, δ2, s2 ⟩ --->* ⟨ γ2', μ2', δ2', s2' ⟩ -> *)
    (* semWP2 already gives the above hypo, don't need it here (wrong res) *)
    (forall `{sailGS2 Σ},
        mem_res2 μ1 μ2 ∗ own_regstore2 γ1 γ2
          ⊢ semWP2 δ1 δ2 s1 s2 Q ∗ (mem_inv(*2*) (mG := memGS2_memGS_left)  μ1' (*μ2'*) ={⊤,∅}=∗ ⌜φ⌝))%I ->
    (* Just mem_inv should be enough, for the RHS, it is part of semWP2, so
       this should be okay. *)
    φ.
  Proof.
    intros [n1 steps1]%steps_to_nsteps (* Hs2 *) H.
    refine (wp_strong_adequacy sailΣ2 (microsail_lang Γ1 τ) _ _ _ _ _ _ _ _ (fun _ => 0) _ steps1).
    iIntros (Hinv).
    assert (regsmapv1 := RegStore_to_map_valid γ1).
    assert (regsmapv2 := RegStore_to_map_valid γ2).
    iMod (own_alloc ((● RegStore_to_map γ1 ⋅ ◯ RegStore_to_map γ1 ) : regUR)) as (spec_name1) "[H1γ1 H2γ1]";
      first by apply auth_both_valid.
    iMod (own_alloc ((● RegStore_to_map γ2 ⋅ ◯ RegStore_to_map γ2 ) : regUR)) as (spec_name2) "[H1γ2 H2γ2]";
      first by apply auth_both_valid.
    pose proof (memΣ_GpreS2 (Σ := sailΣ2) _) as mGS.
    iMod (mem_init2 (mGS := mGS) μ1 μ2) as (memG) "[Hmem Rmem]".
    set (regsG_left := {| reg_inG := @reg_pre_inG2_left sailΣ2 (@subG_sailGpreS sailΣ2 (subG_refl sailΣ2)); reg_gv_name := spec_name1 |}).
    set (regsG_right := {| reg_inG := @reg_pre_inG2_right sailΣ2 (@subG_sailGpreS sailΣ2 (subG_refl sailΣ2)); reg_gv_name := spec_name2 |}).
    set (sailG_left  := SailGS Hinv regsG_left  (@memGS2_memGS_left _ memG)).
    set (sailG_right := SailGS Hinv regsG_right (@memGS2_memGS_right _ memG)).
    set (gs2 := SailGS2 Hinv (SailRegGS2 (@sailGS_sailRegGS _ sailG_left) (@sailGS_sailRegGS _ sailG_right)) memG).
    iModIntro.
    iExists (λ σ _ _ _, regs_inv (srGS := regsG_left) (σ.1) ∗ @mem_inv _ (@memGS2_memGS_left _ memG) (σ.2))%I.
    iExists [_]%list, _, _. cbn.
    rewrite mem_inv2_mem_inv. iDestruct "Hmem" as "($ & Hmem)".
    iSplitL "H1γ1".
    { now iApply (@own_RegStore_to_regs_inv _ regsG_left γ1). }
    iPoseProof (H _ gs2 with "[$Rmem H2γ1 H2γ2]") as "(H & HΦ)".
    { iApply (own_RegStore_to_map_reg_pointsTos (l := finite.enum (sigT 𝑹𝑬𝑮))).
      eapply finite.NoDup_enum. iFrame "H2γ1". iApply "H2γ2". }
    rewrite /semWP2 /semWP.
    iDestruct ("H" with "[H1γ2 $Hmem]") as "$".
    { now iApply own_RegStore_to_regs_inv. }
    iIntros (es' t2') "_ _ _ [Hregs Hmem] _ _".
    now iApply "HΦ".
    (* iIntros (es' t2') "%Happ %Hlen %Hns [Hregs Hmem] H _". *)
    (* destruct es'; try discriminate. *)
    (* inversion Happ; subst. simpl. *)
    (* iDestruct "H" as "(H & _)". *)
    (* specialize (Hns (MkConf s1' δ1') eq_refl (elem_of_list_here _ _)). *)
    (* destruct Hns as [Hns|Hns]. *)
    (* - cbn in Hns. destruct Hns as [(v1' & δ1'') Hns]. rewrite Hns. simpl. *)
    (*   iDestruct "H" as "(% & % & % & % & % & ? & ? & ? & Hmem22 & ?)". *)
    (*   iApply "HΦ". *)
  Qed.


  Lemma wp2_adequacy' {Γ1 Γ2 τ} (s1 : Stm Γ1 τ) (s2 : Stm Γ2 τ)
    {γ1 γ2 : RegStore} {μ1 μ2 : Memory}
    {δ1 : CStore Γ1} {δ2 : CStore Γ2}
    {Q : IVal τ -> CStore Γ1 -> IVal τ -> CStore Γ2 -> Prop} :
    (forall `{sailGS2 Σ},
        ⊢ mem_res2 μ1 μ2 ∗ own_regstore2 γ1 γ2 -∗ semWP2 δ1 δ2 s1 s2 (λ v1 δ1 v2 δ2, ⌜Q v1 δ1 v2 δ2⌝)) ->
    adequate NotStuck (MkConf s1 δ1) (γ1, μ1)
      (λ v1 _, ∃ s2' δ2' γ2' μ2', rtc erased_step ([MkConf s2 δ2]%list, (γ2, μ2)) ([MkConf s2' δ2']%list, (γ2', μ2')) ∧ Final s2' ∧ match s2' with
                                                                                                                                    | stm_val _ v2 => Q (valconf_val v1) (valconf_store v1) (inl v2) δ2'
                                                                                                                                    | stm_fail _ m2 => Q (valconf_val v1) (valconf_store v1) (inr m2) δ2'
                                                                                                                                    | _ => False
                                                                                                                                    end).
  Proof.
    intros wp2.
    apply (wp_adequacy sailΣ2 (microsail_lang Γ1 τ) NotStuck (MkConf s1 δ1) (γ1, μ1)).
    iIntros (Hinv κs).
    assert (regsmapv1 := RegStore_to_map_valid γ1).
    assert (regsmapv2 := RegStore_to_map_valid γ2).
    iMod (own_alloc ((● RegStore_to_map γ1 ⋅ ◯ RegStore_to_map γ1 ) : regUR)) as (spec_name1) "[H1γ1 H2γ1]";
      first by apply auth_both_valid.
    iMod (own_alloc ((● RegStore_to_map γ2 ⋅ ◯ RegStore_to_map γ2 ) : regUR)) as (spec_name2) "[H1γ2 H2γ2]";
      first by apply auth_both_valid.
    pose proof (memΣ_GpreS2 (Σ := sailΣ2) _) as mGS.
    iMod (mem_init2 (mGS := mGS) μ1 μ2) as (memG) "[Hmem Rmem]".
    set (regsG_left := {| reg_inG := @reg_pre_inG2_left sailΣ2 (@subG_sailGpreS sailΣ2 (subG_refl sailΣ2)); reg_gv_name := spec_name1 |}).
    set (regsG_right := {| reg_inG := @reg_pre_inG2_right sailΣ2 (@subG_sailGpreS sailΣ2 (subG_refl sailΣ2)); reg_gv_name := spec_name2 |}).
    set (sailG_left  := SailGS Hinv regsG_left  (@memGS2_memGS_left _ memG)).
    set (sailG_right := SailGS Hinv regsG_right (@memGS2_memGS_right _ memG)).
    set (gs2 := SailGS2 Hinv (SailRegGS2 (@sailGS_sailRegGS _ sailG_left) (@sailGS_sailRegGS _ sailG_right)) memG).
    iModIntro.
    iExists (fun σ _ => regs_inv (srGS := regsG_left) (σ.1) ∗ @mem_inv _ (@memGS2_memGS_left _ memG) (σ.2))%I.
    iExists _.
    rewrite mem_inv2_mem_inv. cbn. iDestruct "Hmem" as "($ & Hmem)".
    iSplitL "H1γ1".
    { now iApply (@own_RegStore_to_regs_inv _ regsG_left γ1). }
    iPoseProof (wp2 _ gs2 with "[$Rmem H2γ1 H2γ2]") as "H".
    { iApply (own_RegStore_to_map_reg_pointsTos (l := finite.enum (sigT 𝑹𝑬𝑮))).
      eapply finite.NoDup_enum.
      iSplitL "H2γ1". iApply "H2γ1". iApply "H2γ2". }
    rewrite /semWP2 /semWP.
    iSpecialize ("H" with "[H1γ2 $Hmem]").
    { now iApply own_RegStore_to_regs_inv. }
    iApply (wp_mono with "H").
    iIntros (v1) "(%γ2' & %μ2' & %δ2' & %s2' & %v2 & %Hstep & %Heq & Hreg & Hmem & %HQ)".
    iExists s2', δ2', γ2', μ2'. destruct v1 as [[v1|m1] δ1']; simpl in *;
      iPureIntro; repeat split.
    - now apply steps_to_erased.
    - apply (stm_to_val_Final Heq).
    - destruct (stm_to_val_Some_cases Heq) as [(v' & -> & ->)|(m' & -> & ->)]; auto.
    - now apply steps_to_erased.
    - apply (stm_to_val_Final Heq).
    - destruct (stm_to_val_Some_cases Heq) as [(v' & -> & ->)|(m' & -> & ->)]; auto.
  Qed.

  (* NOTE: more general stmt, generalized over diff programs (in terms of the actual program logic, instead of the semTriple) *)
  Lemma adequacy {Γ τ} (s : Stm Γ τ)
    {γ1 γ2 : RegStore} {μ1 μ2 : Memory}
    {δ : CStore Γ}
    {Q : Val τ -> Prop} :
    (forall `{sailGS2 Σ},
        ⊢ semTriple δ (mem_res2 μ1 μ2 ∗ own_regstore2 γ1 γ2) s (fun v _ => ⌜Q v⌝)) ->
    adequate NotStuck (MkConf s δ) (γ1, μ1)
             (λ v _, ∃ s' δ' γ2' μ2', rtc erased_step ([MkConf s δ]%list, (γ2, μ2)) ([MkConf s' δ']%list, (γ2', μ2')) ∧ Final s' ∧ @ResultOrFail2 Γ _ _ (of_ival (valconf_val v)) s' Q).
  Proof.
    intros trips.
    apply (wp_adequacy sailΣ2 (microsail_lang Γ τ) NotStuck (MkConf s δ) (γ1, μ1)).
    iIntros (Hinv κs).
    assert (regsmapv1 := RegStore_to_map_valid γ1).
    assert (regsmapv2 := RegStore_to_map_valid γ2).
    iMod (own_alloc ((● RegStore_to_map γ1 ⋅ ◯ RegStore_to_map γ1 ) : regUR)) as (spec_name1) "[H1γ1 H2γ1]";
      first by apply auth_both_valid.
    iMod (own_alloc ((● RegStore_to_map γ2 ⋅ ◯ RegStore_to_map γ2 ) : regUR)) as (spec_name2) "[H1γ2 H2γ2]";
      first by apply auth_both_valid.
    pose proof (memΣ_GpreS2 (Σ := sailΣ2) _) as mGS.
    iMod (mem_init2 (mGS := mGS) μ1 μ2) as (memG) "[Hmem Rmem]".
    set (regsG_left := {| reg_inG := @reg_pre_inG2_left sailΣ2 (@subG_sailGpreS sailΣ2 (subG_refl sailΣ2)); reg_gv_name := spec_name1 |}).
    set (regsG_right := {| reg_inG := @reg_pre_inG2_right sailΣ2 (@subG_sailGpreS sailΣ2 (subG_refl sailΣ2)); reg_gv_name := spec_name2 |}).
    set (sailG_left  := SailGS Hinv regsG_left  (@memGS2_memGS_left _ memG)).
    set (sailG_right := SailGS Hinv regsG_right (@memGS2_memGS_right _ memG)).
    set (gs2 := SailGS2 Hinv (SailRegGS2 (@sailGS_sailRegGS _ sailG_left) (@sailGS_sailRegGS _ sailG_right)) memG).
    iModIntro.
    iExists (fun σ _ => regs_inv (srGS := regsG_left) (σ.1) ∗ @mem_inv _ (@memGS2_memGS_left _ memG) (σ.2))%I.
    iExists _.
    rewrite mem_inv2_mem_inv. cbn. iDestruct "Hmem" as "($ & Hmem)".
    iSplitL "H1γ1".
    { now iApply (@own_RegStore_to_regs_inv _ regsG_left γ1). }
    iPoseProof (trips _ gs2 with "[$Rmem H2γ1 H2γ2]") as "H".
    { iApply (own_RegStore_to_map_reg_pointsTos (l := finite.enum (sigT 𝑹𝑬𝑮))).
      eapply finite.NoDup_enum.
      iSplitL "H2γ1". iApply "H2γ1". iApply "H2γ2". }
    rewrite /semWP2 /semWP.
    iSpecialize ("H" with "[H1γ2 $Hmem]").
    { now iApply own_RegStore_to_regs_inv. }
    iApply (wp_mono with "H").
    iIntros (v1) "(%γ2' & %μ2' & %δ2' & %s2' & %v2 & %Hstep & %Heq & Hreg & Hmem & %Hvaleq & %Hstoreeq & H)".
    iExists s2', δ2', γ2', μ2'. destruct fail_rule_pre, v1 as [[v1|m1] δ1']; simpl in *;
      auto; iDestruct "H" as "%H"; iPureIntro; repeat split.
    - now apply steps_to_erased.
    - apply (stm_to_val_Final Heq).
    - destruct (stm_to_val_Some_cases Heq) as [(v' & -> & ->)|(m' & -> & ->)].
      + inversion Hvaleq; subst; auto.
      + discriminate.
    - now apply steps_to_erased.
    - apply (stm_to_val_Final Heq).
    - destruct (stm_to_val_Some_cases Heq) as [(v' & -> & ->)|(m' & -> & ->)].
      + discriminate.
      + inversion Hvaleq; subst; auto.
    - now apply steps_to_erased.
    - apply (stm_to_val_Final Heq).
    - destruct (stm_to_val_Some_cases Heq) as [(v' & -> & ->)|(m' & -> & ->)].
      + inversion Hvaleq; subst; auto.
      + discriminate.
  Qed.

  (* Lemma adequacy_gen {Γ1 Γ2 τ} (s11 s12 : Stm Γ1 τ) (s21 s22 : Stm Γ2 τ) *)
  (*   {γ11 γ12 γ21 γ22 : RegStore} {μ11 μ12 μ21 μ22 : Memory} *)
  (*   {δ11 δ12 : CStore Γ1} {δ21 δ22 : CStore Γ2} *)
  (*   {Q : forall `{sailGS2 Σ}, Val τ -> CStore Γ1 -> Val τ -> CStore Γ2 -> iProp Σ} (φ : Prop) : *)
  (*   ⟨ γ11, μ11, δ11, s11 ⟩ --->* ⟨ γ12, μ12, δ12, s12 ⟩ -> *)
  (*   ⟨ γ21, μ21, δ21, s21 ⟩ --->* ⟨ γ22, μ22, δ22, s22 ⟩ -> *)
  (*   (forall `{sailGS2 Σ}, *)
  (*       mem_res2 μ11 μ21 ∗ own_regstore2 γ11 γ21 ⊢ *)
  (*                semWp2 δ11 δ21 s11 s21 Q ∗ (mem_inv2 μ11 μ21 ={⊤,∅}=∗ ⌜φ⌝)) -> *)
  (*   φ. *)
  (*   Admitted. *)
End IrisAdequacy2.
