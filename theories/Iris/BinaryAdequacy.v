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
     Iris.Model
     Iris.Instance
     Prelude
     Semantics
     Sep.Hoare
     Sep.Logic
     Signature
     SmallStep.Step
     Specification
     BinaryModel
     BinaryWP.

Import ctx.notations.
Import env.notations.

Set Implicit Arguments.

Module Type IrisAdeqParameters2
  (Import B     : Base)
  (Import IPP  : IrisParameters2 B)
  (Import PROG : Program B)
  (Import SEM  : Semantics B PROG)
  (Import IP   : IrisPrelims B PROG SEM).

  Parameter Inline memGpreS2 : gFunctors -> Set.
  Parameter memΣ2 : gFunctors.
  Parameter memΣ_GpreS2 : forall {Σ}, subG memΣ2 Σ -> memGpreS2 Σ.
  Parameter mem_res2 : forall `{mG : memGS2 Σ}, Memory -> Memory -> iProp Σ.

    (* Definition mem_inv `{sailG Σ} (μ : Z -> option Z) : iProp Σ := *)
    (*   (∃ memmap, gen_heap_ctx memmap ∗ *)
    (*      ⌜ map_Forall (fun (a : Z) v => μ a = Some v) memmap ⌝ *)
    (*   )%I. *)

  Parameter mem_inv_init2 : forall `{mGS : memGpreS2 Σ} (μ1 μ2 : Memory),
                                         ⊢ |==> ∃ mG : memGS2 Σ, (mem_inv2 (mG := mG) μ1 μ2 ∗ mem_res2 (mG := mG) μ1 μ2)%I.

End IrisAdeqParameters2.

Module Type IrisAdequacy2
  (Import B     : Base)
  (Import SIG   : Signature B)
  (Import PROG  : Program B)
  (Import SEM   : Semantics B PROG)
  (Import IB    : IrisBase2 B PROG SEM)
  (Import IAP   : IrisAdeqParameters2 B IB PROG SEM IB)
  (Import IPred : IrisPredicates2 B SIG PROG SEM IB)
  (Import IWP   : IrisBinaryWPParameters B SIG PROG SEM IB IPred)
  (Import IRules : IrisSignatureRules2 B SIG PROG SEM IB IPred IWP).

  Import SmallStepNotations.

  Class sailGpreS2 Σ := SailGpreS2 { (* resources for the implementation side *)
                       sailGpresS_invGpreS2 : invGpreS Σ; (* for fancy updates, invariants... *)

                       (* ghost variables for tracking state of registers *)
                       reg_pre_inG2_left : inG Σ regUR;
                       reg_pre_inG2_right : inG Σ regUR;

                       (* ghost variable for tracking state of memory cells *)
                       sailPreG_gen_memGpreS2 : memGpreS2 Σ
                     }.

  Existing Instance sailGpresS_invGpreS2.

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

(*   Lemma steps_to_erased {σ Γ γ μ δ} (s : Stm Γ σ) {γ' μ' δ' s'}: *)
(*     ⟨ γ, μ, δ, s ⟩ --->* ⟨ γ', μ', δ', s' ⟩ -> *)
(*     rtc erased_step ([MkConf s δ]%list, (γ,μ)) ([MkConf s' δ']%list, (γ',μ')). *)
(*   Proof. *)
(*     induction 1; first done. *)
(*     refine (rtc_l _ _ _ _ _ IHSteps). *)
(*     exists nil. *)
(*     refine (step_atomic _ _ _ _ _ nil nil eq_refl eq_refl _). *)
(*     by eapply mk_prim_step. *)
(*   Qed. *)

(*   Lemma steps_to_nsteps {σ Γ γ μ δ} (s : Stm Γ σ) {γ' μ' δ' s'}: *)
(*     ⟨ γ, μ, δ, s ⟩ --->* ⟨ γ', μ', δ', s' ⟩ -> *)
(*     exists n, language.nsteps n ([MkConf s δ]%list , (γ,μ)) [] ([MkConf s' δ']%list , (γ',μ')). *)
(*   Proof. *)
(*     induction 1. *)
(*     - exists 0. now constructor. *)
(*     - destruct IHSteps as [n steps]. *)
(*       exists (S n). *)
(*       refine (language.nsteps_l _ _ _ _ [] _ _ steps). *)
(*       refine (step_atomic _ _ _ _ _ nil nil eq_refl eq_refl _). *)
(*       now eapply mk_prim_step. *)
(*   Qed. *)

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

  Lemma steps_to_nsteps {Γ : PCtx} {σ : Ty} {γ1 γ2 : RegStore} {μ1 μ2 : Memory} {δ1 δ2 : CStore Γ} {s1 s2 : Stm Γ σ} :
    Steps γ1 μ1 δ1 s1 γ2 μ2 δ2 s2 -> exists n, NSteps γ1 μ1 δ1 s1 γ2 μ2 δ2 s2 n.
  Proof.
    induction 1 as [|γ1 μ1 δ1 s1 γ2 γ3 μ2 μ3 δ2 δ3 s2 s3 eval evals [n nsteps]].
    - exists 0. constructor.
    - exists (S n). econstructor; eassumption.
  Qed.

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

  (* TODO: redefine adequacy for our binary program logic *)
  Lemma adequacy {Γ} {σ} (s11 s21 : Stm Γ σ) {γ11 γ21 γ12} {μ11 μ21 μ12}
        {δ11 δ21 δ12 : CStore Γ} {s12 : Stm Γ σ} {Q : Val σ -> Val σ -> Prop} :
    ⟨ γ11, μ11, δ11, s11 ⟩ --->* ⟨ γ12, μ12, δ12, s12 ⟩ -> Final s12 ->
    (* TODO: add following: *)
    (* ⟨ γ21, μ21, δ21, s21 ⟩ --->* ⟨ γ22, μ22, δ22, s22 ⟩ -> Final s22 -> *)
    (forall {Σ} `{sailGS2 Σ}, mem_res2 μ11 μ21 ∗ own_regstore2 γ11 γ21 ⊢ semWp2 δ11 δ21 s11 s21 (fun v1 _ v2 _ => ⌜ Q v1 v2 ⌝)) ->
    ResultOrFail s12 (fun v12 =>
                        exists γ22 μ22 δ22 v22,
                          ⟨ γ21, μ21, δ21, s21 ⟩ --->* ⟨ γ22, μ22, δ22, stm_val _ v22 ⟩ /\
                            Q v12 v22).
  Proof.
  Admitted.

End IrisAdequacy2.
