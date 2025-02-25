(******************************************************************************)
(* Copyright (c) 2020 Aïna Linn Georges, Armaël Guéneau, Thomas Van Strydonck,*)
(* Amin Timany, Alix Trieu, Dominique Devriese, Lars Birkedal                 *)
(* Copyright (c) 2023 Steven Keuchel, Dominique Devriese, Sander Huyghebaert  *)
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
(* 3. Neither the name of the copyright holder nor the names of its           *)
(*    contributors may be used to endorse or promote products derived from    *)
(*    this software without specific prior written permission.                *)
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
     Classes.EquivDec
     Init.Nat
     Program.Tactics
     Strings.String
     ZArith.ZArith
     ZArith.Znat
     micromega.Lia.

From Equations Require Import
     Equations.

From Katamaran Require Import
     Environment
     Iris.Instance
     Iris.Base
     Semantics
     Sep.Hoare
     Specification
     MicroSail.ShallowExecutor
     MicroSail.ShallowSoundness
     MicroSail.SymbolicExecutor
     MicroSail.RefineExecutor
     MinimalCaps.Machine
     MinimalCaps.Sig
     MinimalCaps.Contracts.Definitions
     MinimalCaps.Contracts.Verification.

From iris.base_logic Require lib.gen_heap lib.iprop.
From iris.base_logic Require Export invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac.
From iris.program_logic Require Import weakestpre adequacy.
From iris.proofmode Require Import string_ident tactics.
From stdpp Require namespaces fin_maps.

Set Implicit Arguments.

Module gh := iris.base_logic.lib.gen_heap.

Module MinCapsSemantics <: Semantics MinCapsBase MinCapsProgram :=
  MakeSemantics MinCapsBase MinCapsProgram.

(* destruct_syminstance is a tactic that destructs the given symbolic instance
   ι. It uses views to get information about ι. *)
Ltac destruct_syminstance ι :=
  cbn in ι;
  repeat
    match type of ι with
    | Env _ (ctx.snoc _ (MkB ?s _)) =>
        string_to_ident_cps s
          ltac:(fun id =>
                  let fr := fresh id in
                  destruct (env.view ι) as [ι fr];
                  destruct_syminstance ι)
    | Env _ ctx.nil => destruct (env.view ι)
    | _ => idtac
    end.

(* destruct_syminstances searches for the ι and applies the destruct_syminstance
   tactic on it. *)
Ltac destruct_syminstances :=
  repeat
    match goal with
    | ι : Env _ (ctx.snoc _ _) |- _ => destruct_syminstance ι
    | ι : Env _ ctx.nil        |- _ => destruct_syminstance ι
    end.

Import MinCapsBase.
Import MinCapsSignature.
Import MinCapsProgram.
Import MinCapsSpecification.

Module Import MinCapsIrisBase <: IrisBase MinCapsBase MinCapsProgram MinCapsSemantics.
  Include IrisPrelims MinCapsBase MinCapsProgram MinCapsSemantics.

  (* eliminate_prim_step eliminate a Step in the assumptions to enable further
     progress in the proof. *)
  Ltac eliminate_prim_step Heq :=
    let f := fresh "f" in
    match goal with
    | H: MinCapsSemantics.Step _ _ _ _ _ _ _ _ |- _ =>
        dependent elimination H as [MinCapsSemantics.st_foreign _ _ f];
        rewrite Heq in f;
        cbn in f;
        dependent elimination f;
        cbn
    | H: prim_step _ _ _ _ _ _ |- _ =>
          let s := fresh "s" in
          dependent elimination H as [mk_prim_step s];
          dependent elimination s as [MinCapsSemantics.st_foreign _ _ f];
          rewrite Heq in f;
          cbn in f;
          dependent elimination f;
          cbn
    end.

  Parameter maxAddr : nat.

  Section WithIrisNotations.
    Import iris.bi.interface.
    Import iris.bi.big_op.
    Import iris.base_logic.lib.iprop.
    Import iris.base_logic.lib.gen_heap.

    Definition MemVal : Set := Z + Capability.

    Class mcMemGS Σ := McMemGS {
                          (* ghost variable for tracking state of registers *)
                          mc_ghG :: gh.gen_heapGS Z MemVal Σ;
                          mc_invNs : namespace
                        }.
    #[export] Existing Instance mc_ghG.

    Definition memGS : gFunctors -> Set := mcMemGS.

    Definition mem_inv `{mG : mcMemGS Σ} (μ : Memory) : iProp Σ :=
        (∃ memmap, gen_heap_interp (hG := mc_ghG (mcMemGS := mG)) memmap ∗
          ⌜ map_Forall (fun a v => μ a = v) memmap ⌝
        )%I.

    Definition liveAddrs : list Addr := seqZ 0 maxAddr.
    Definition initMemMap μ := (list_to_map (map (fun a => (a , μ a)) liveAddrs) : gmap Addr MemVal).

    Lemma initMemMap_works μ : map_Forall (λ (a : Addr) (v : MemVal), μ a = v) (initMemMap μ).
    Proof.
      unfold initMemMap.
      rewrite map_Forall_to_list.
      rewrite Forall_forall.
      intros (a , v).
      rewrite elem_of_map_to_list.
      intros el.
      apply elem_of_list_to_map_2 in el.
      apply elem_of_list_In in el.
      apply in_map_iff in el.
      by destruct el as (a' & <- & _).
    Qed.

  End WithIrisNotations.

  Include IrisResources MinCapsBase MinCapsProgram MinCapsSemantics.
  Include IrisWeakestPre MinCapsBase MinCapsProgram MinCapsSemantics.
  Include IrisTotalWeakestPre MinCapsBase MinCapsProgram MinCapsSemantics.
  Include IrisTotalPartialWeakestPre MinCapsBase MinCapsProgram MinCapsSemantics.
End MinCapsIrisBase.

Module MinCapsIrisAdeqParameters <: IrisAdeqParameters MinCapsBase MinCapsIrisBase.
  Import iris.base_logic.lib.gen_heap.

  Definition memGpreS : gFunctors -> Set := fun Σ => gh.gen_heapGpreS Z MemVal Σ.
  Definition memΣ : gFunctors := gh.gen_heapΣ Z MemVal.

  Definition memΣ_GpreS : forall {Σ}, subG memΣ Σ -> memGpreS Σ :=
    fun {Σ} => gh.subG_gen_heapGpreS (Σ := Σ) (L := Z) (V := MemVal).

  Definition mem_res `{mG : mcMemGS Σ} (μ : Memory) : iProp Σ :=
      ([∗ map] l↦v ∈ initMemMap μ, pointsto l (DfracOwn 1) v) %I.

  Lemma mem_inv_init `{gHP : memGpreS Σ} (μ : Memory) :
                                              ⊢ |==> ∃ mG : memGS Σ, (mem_inv (mG := mG) μ ∗ mem_res (mG := mG) μ)%I.
  Proof.
    iMod (gen_heap_init (gen_heapGpreS0 := gHP) (L := Addr) (V := MemVal) empty) as (gH) "[inv _]".
    pose (memmap := initMemMap μ).
    iMod (gen_heap_alloc_big empty memmap (map_disjoint_empty_r memmap) with "inv") as "(inv & res & _)".
    iModIntro.

    rewrite (right_id empty union memmap).

    iExists (McMemGS gH (nroot .@ "addr_inv")).
    iFrame.
    iPureIntro.
    apply initMemMap_works.
  Qed.

End MinCapsIrisAdeqParameters.

Module Import MinCapsIrisInstance <: IrisInstance MinCapsBase MinCapsSignature MinCapsProgram MinCapsSemantics MinCapsIrisBase MinCapsIrisAdeqParameters.
  Import env.notations.
  Import iris.bi.interface.
  Import iris.bi.big_op.
  Import iris.base_logic.lib.iprop.
  Import iris.base_logic.lib.gen_heap.

  Section Predicates.
    Context {Σ} `{sailRegGS Σ} `{invGS Σ} {mG : mcMemGS Σ}.

    (* MinCaps_ptsreg returns a pointsto predicate for the given RegName with
       value v. Note that R0 is hardwired to 0 and therefore no pointsto chunk
       can be given for it. *)
    Definition MinCaps_ptsreg (reg : RegName) (v : Z + Capability) : iProp Σ :=
      match reg with
      | R0 => True
      | R1 => reg_pointsTo reg1 v
      | R2 => reg_pointsTo reg2 v
      | R3 => reg_pointsTo reg3 v
      end.

    (* region_addrs computer the list of addresses of the machine between the
       boundary [b, e]. *)
    Definition region_addrs (b e : Addr) : list Addr :=
      filter (fun a => and (b ≤ a)%Z (a ≤ e)%Z) liveAddrs.

    Lemma element_of_region_addrs (a b e : Addr) :
      b ∈ liveAddrs → e ∈ liveAddrs →
      (b <= a)%Z /\ (a <= e)%Z ->
      a ∈ region_addrs b e.
    Proof.
      intros Hb He [Hba Hae].
      apply elem_of_list_filter.
      repeat (split; try assumption).
      apply elem_of_seqZ in Hb.
      apply elem_of_seqZ in He.
      apply elem_of_seqZ.
      lia.
    Qed.

    (* Declare OFE instances for our values *)
    Canonical Structure CapabilityO := leibnizO Capability.
    Canonical Structure MemValO     := leibnizO (sumO ZO CapabilityO).

    (* Types for the interpretation of MemVal and Capabilities *)
    (* TODO: We shouldn't need to write MemValO, there might ba a missing
             typeclass instance? (Proper?) Changing MemValO to MemVal will
             provide problems for interp1, generating an obligation *)
    Definition IMemVal   := MemVal -> iProp Σ.
    Definition IMemValne := MemValO -n> iProp Σ.
    Definition ICap      := Capability -> iProp Σ.
    Definition ICapne    := Capability -n> iProp Σ.
    Implicit Type w : MemValO.

    (* Copied from github.com/logsem/cerise *)
    (* TODO: include copyright notice =) *)
    Ltac auto_equiv :=
      (* Deal with "pointwise_relation" *)
      repeat lazymatch goal with
             | |- pointwise_relation _ _ _ _ => intros ?
             end;
      (* Normalize away equalities. *)
      repeat match goal with
             | H : _ ≡{_}≡ _ |-  _ => apply (discrete_iff _ _) in H
             | H : _ ≡ _ |-  _ => apply leibniz_equiv in H
             | _ => progress simplify_eq
             end;
      (* repeatedly apply congruence lemmas and use the equalities in the hypotheses. *)
      try (f_equiv; fast_done || auto_equiv).

    Ltac solve_proper ::= (repeat intros ?; simpl; auto_equiv).

    (* GPRs is a list of general-purpose registers of the machine. As R0 is
       hardwired to 0, we do not consider it general-purpose. *)
    Definition GPRs : list RegName :=
      filter (fun r => @nequiv_decb _ _ _ RegName_eqdec r R0)
        (finite.enum RegName).

    (* interp_gprs states that we have ownership of all GPRs and that all
       registers contain a safe value (interp). *)
    Program Definition interp_gprs : IMemValne -n> iProp Σ :=
      λne interp, ([∗ list] r ∈ GPRs, (∃ w, MinCaps_ptsreg r w ∗ interp w))%I.
    Solve Obligations with solve_proper.

    (* interp_loop is the weakest precondition of the loop of our machine
       with as postcondition True. *)
    Definition interp_loop `{sg : sailGS Σ} : iProp Σ :=
      (WP (MkConf (FunDef loop) env.nil) {{_, True}})%I.

    (* interp_expr is the expression relation, stating that if we give
       the pointsto chunks for the pc and GPRs, then we still satisfy the
       weakest precondition of the fdeCycle of the machine. *)
    Definition interp_expr (interp : IMemValne) : ICapne :=
      (λne c,
        reg_pointsTo pc c ∗ interp_gprs interp -∗ (interp_loop (sg := SailGS _ _ mG)))%I.

    (* interp_ref_inv states that we have ownership of addr a and that predicate
       P holds for the contents at addr a. *)
    Program Definition interp_ref_inv (a : Addr) : IMemValne -n> iProp Σ :=
      λne P, (∃ w, pointsto a (DfracOwn 1) w ∗ P w)%I.
    Solve Obligations with solve_proper.

    (* interp_cap_inv expresses the safe relation on capabilities. A capability
       is safe if all the addressable locations are safe as well. *)
    Definition interp_cap_inv (c : Capability) (interp : IMemValne) :iProp Σ :=
      match c with
      | MkCap _ b e a =>
          (⌜(b <= e)%Z⌝ →
           ⌜b ∈ liveAddrs /\ e ∈ liveAddrs⌝ ∗
                               [∗ list] a ∈ (region_addrs b e), inv (mc_invNs .@ a) (interp_ref_inv a interp))
          ∨ ⌜(e < b)%Z⌝
      end%I.

    (* interp_cap_O expresses the safety of a null capability, which trivially
       holds as no locations are addressable. *)
    Definition interp_cap_O : IMemVal := λ _, True%I.

    (* interp_cap_R states safety for a readonly capability, which is defined
       using interp_cap_inv. *)
    Definition interp_cap_R (interp : IMemValne) : IMemVal :=
      λ w, (match w with
              | inr (MkCap R b e a) => interp_cap_inv (MkCap R b e a) interp
              |  _                  => False
              end)%I.

    (* interp_cap_R states safety for a readwrite capability, which is defined
       using interp_cap_inv. *)
    Definition interp_cap_RW (interp : IMemValne) : IMemVal :=
      λ w, (match w with
            | inr (MkCap RW b e a) => interp_cap_inv (MkCap RW b e a) interp
            | _                    => False
            end)%I.

    (* enter_cond states that later, the expression relation will (always) hold
       for the readonly capability with the given begin, end and cursor. *)
    Program Definition enter_cond (b e a : Addr) : IMemValne -n> iProp Σ :=
      λne interp, (▷ □ interp_expr interp (MkCap R b e a))%I.
    Solve Obligations with solve_proper.

    (* interp_expression states that the given capability should be readonly
       and that the enter_cond needs to hold for it. *)
    Definition interp_expression (interp : IMemValne) : ICap :=
      λ c, (match c with
            | {| cap_permission := p; cap_begin := b; cap_end := e; cap_cursor := a |} =>
                ⌜p = R⌝ ∧ enter_cond b e a interp
            end)%I.

    (* interp_cap_E implements the safety relation for enter capabilities. *)
    Definition interp_cap_E (interp : IMemValne) : IMemVal :=
      λ w, (match w with
            | inr (MkCap E b e a) => enter_cond b e a interp
            | _                   => False
            end)%I.

    (* interp_z is the safety relation for integers, which holds trivially. Only
       capabilities can be used for interaction with memory on this machine. *)
    Definition interp_z : IMemVal :=
      λ w, ⌜ match w with
             | inl _ => True
             | _     => False
             end ⌝%I.

    (* interp1 maps the different cases to their respective interp functions. *)
    Definition interp1 (interp : IMemValne) : IMemValne :=
      λne w, (match w with
              | inl _                => interp_z w
              | inr (MkCap O _ _ _)  => interp_cap_O w
              | inr (MkCap R _ _ _)  => interp_cap_R interp w
              | inr (MkCap RW _ _ _) => interp_cap_RW interp w
              | inr (MkCap E _ _ _)  => interp_cap_E interp w
              end)%I.

    #[global] Instance interp1_contractive : Contractive interp1.
    Proof. intros ? ? ? ? [|[[] ? ? ?]]; solve_contractive. Qed.

    (* interp is the general definition for our safety relation. *)
    Definition interp : IMemVal :=
      λ w, (fixpoint (interp1)) w.

    Lemma fixpoint_interp1_eq w :
      fixpoint interp1 w ≡ interp1 (fixpoint interp1) w.
    Proof. exact: (fixpoint_unfold interp1 w). Qed.

    Lemma fixpoint_interp_eq w :
      interp w ≡ interp1 (fixpoint interp1) w.
    Proof. by unfold interp; rewrite fixpoint_interp1_eq. Qed.

    Lemma le_liveAddrs (a b e : Addr) :
      b ∈ liveAddrs ∧ e ∈ liveAddrs ->
      (b <= a)%Z ∧ (a <= e)%Z ->
      a ∈ liveAddrs.
    Proof.
      intros [[H0b Hbm]%elem_of_seqZ [H0e Hem]%elem_of_seqZ] [Hba Hae];
        rewrite elem_of_seqZ;
        split; lia.
    Qed.

    Lemma region_addrs_submseteq  (b' e' b e : Addr) :
      ⊢ ⌜ (b <= b')%Z /\ (e' <= e)%Z ⌝ -∗
        ([∗ list] a ∈ (region_addrs b e), inv (mc_invNs .@ a) (∃ w, pointsto a (DfracOwn 1) w ∗ fixpoint interp1 w))%I -∗
        ([∗ list] a ∈ (region_addrs b' e'), inv (mc_invNs .@ a) (∃ w, pointsto a (DfracOwn 1) w ∗ fixpoint interp1 w))%I.
    Proof.
      iIntros "[% %] Hregion".
      iApply (big_sepL_submseteq _ (region_addrs b' e') (region_addrs b e)).
      Unshelve. all: eauto with typeclass_instances.
      unfold region_addrs.
      induction liveAddrs.
      - cbn; trivial.
      - cbn.
        destruct (decide ((b' ≤ a)%Z ∧ (a ≤ e')%Z));
          destruct (decide ((b ≤ a)%Z ∧ (a ≤ e)%Z));
          trivial.
        + apply submseteq_skip; trivial.
        + destruct a0 as [Hb' He']; lia.
        + apply submseteq_cons; trivial.
    Qed.

    Lemma specialize_range (b e addr : Addr) :
      ⊢ ⌜ (b <= addr)%Z /\ (addr <= e)%Z ⌝ -∗
        (⌜ b ∈ liveAddrs /\ e ∈ liveAddrs ⌝ ∗
         [∗ list] a ∈ (region_addrs b e), inv (mc_invNs .@ a) (∃ w, pointsto a (DfracOwn 1) w ∗ fixpoint interp1 w))%I -∗
        (inv (mc_invNs .@ addr) (∃ w, pointsto addr (DfracOwn 1) w ∗ fixpoint interp1 w))%I.
    Proof.
      iIntros "[% %] [[% %] Hrange]".
      iApply (big_sepL_elem_of with "Hrange").
      apply element_of_region_addrs; try assumption.
      split; assumption.
    Qed.

    Global Instance interp_Persistent (w : MemVal) : Persistent (interp w).
    Proof. destruct w; simpl; rewrite fixpoint_interp_eq; simpl; first apply _.
           destruct c; destruct cap_permission; apply _. Qed.

    (* IH is the induction hypothesis for the machine. If we give back ownership
       of the GPRs and the pc, and the pc contains a safe capability, then we
       satisfy the weakest precondition of the loop (with as postcondition
       True) *)
    Definition IH : iProp Σ :=
      (□ ▷ (∀ p b e a,
               interp_gprs interp
            -∗ reg_pointsTo pc (MkCap p b e a)
            -∗ □ interp (inr (MkCap p b e a)) -∗ interp_loop (sg := SailGS _ _ mG))).

    Lemma interp_cap_inv_weakening (b b' e e' : Addr) :
      ∀ p a a',
      (b ≤ b')%Z →
      (e' ≤ e)%Z →
      interp_cap_inv (MkCap p b e a) interp -∗
      interp_cap_inv (MkCap p b' e' a') interp.
    Proof.
      iIntros (p a a' Hb He) "[HA | %HA]".
      - iLeft.
        iIntros (l).
        assert (Hle : (b ≤ e)%Z).
        { eapply Z.le_trans. apply Hb.
          eapply Z.le_trans. apply l. apply He. }
        iSpecialize ("HA" $! Hle).
        iDestruct "HA" as "([%Hbl %Hel] & HA)".
        iSplit.
        + iPureIntro; split; (eapply le_liveAddrs; first apply (conj Hbl Hel); try lia).
        + iApply (region_addrs_submseteq $! (conj Hb He) with "HA").
      - iRight; iPureIntro; lia.
    Qed.

    Lemma interp_subperm_weakening p p' b e a :
      Subperm p' p ->
      IH -∗
      interp (inr (MkCap p b e a)) -∗
      interp (inr (MkCap p' b e a)).
    Proof.
      intros Hp; destruct p'; destruct p eqn:Ep; inversion Hp; auto; iIntros "#IH #HA";
        rewrite !fixpoint_interp_eq; try done.
      - repeat iModIntro.
        iIntros "(Hpc & Hreg1 & Hreg2 & Hreg3 & _)".
        iApply ("IH" with "[-Hpc IH HA] Hpc"); try iFrame.
        done.
        iModIntro.
        rewrite !fixpoint_interp_eq; cbn - [interp_cap_inv].
        iApply (interp_cap_inv_weakening p a a (Z.le_refl b) (Z.le_refl e) with "HA").
      - repeat iModIntro.
        iIntros "(Hpc & Hreg1 & Hreg2 & Hreg3 & _)".
        iApply ("IH" with "[-Hpc IH HA] Hpc"); try iFrame.
        done.
        iModIntro.
        rewrite !fixpoint_interp_eq; cbn - [interp_cap_inv].
        iApply (interp_cap_inv_weakening p a a (Z.le_refl b) (Z.le_refl e) with "HA").
    Qed.

    Lemma interp_weakening p p' b b' e e' a a' :
      p ≠ E ->
      (b ≤ b')%Z ->
      (e' ≤ e)%Z ->
      Subperm p' p ->
      IH -∗
      interp (inr (MkCap p b e a)) -∗
      interp (inr (MkCap p' b' e' a')).
    Proof.
      iIntros (HpnotE Hb He Hsubperm) "#IH #HA".
      destruct p'.
      - rewrite !fixpoint_interp_eq; done.
      - destruct p eqn:Ep; inversion Hsubperm;
          rewrite !fixpoint_interp_eq; cbn - [interp_cap_inv];
          iApply (interp_cap_inv_weakening p a a' Hb He with "HA").
      - destruct p eqn:Ep; inversion Hsubperm;
          rewrite !fixpoint_interp_eq; cbn - [interp_cap_inv];
          iApply (interp_cap_inv_weakening p a a' Hb He with "HA").
      - destruct p eqn:Ep; inversion Hsubperm; last contradiction;
          iApply (interp_subperm_weakening _ _ _ Hsubperm with "IH");
          rewrite !fixpoint_interp_eq;
          iApply (interp_cap_inv_weakening p a a' Hb He with "HA").
    Qed.
  End Predicates.

  Section MinimalCapsPredicates.
    Import env.notations.

    (* luser_inst gives the implementation for the predicates defined for this
       case study. *)
    Equations(noeqns) luser_inst `{sailRegGS Σ, invGS Σ, mcMemGS Σ}
             (p : Predicate) (ts : Env Val (𝑯_Ty p)) : iProp Σ :=
    | ptsto   | [a; v] => pointsto a (DfracOwn 1) v
    | safe    | [c]    => interp c
    | expr    | [c]    => interp_expression interp c
    | gprs    | []     => interp_gprs interp
    | ih      | []     => IH
    | wp_loop | []     => interp_loop (sg := SailGS _ _ _).

    Definition lduplicate_inst `{sailRegGS Σ} `{invGS Σ} (mG : mcMemGS Σ) :
      forall (p : Predicate) (ts : Env Val (𝑯_Ty p)),
        is_duplicable p = true ->
        (luser_inst p ts) ⊢ (luser_inst p ts ∗ luser_inst p ts).
    Proof.
      destruct p; intros ts Heq; try discriminate Heq;
        clear Heq; cbn in *; env.destroy ts; auto.
    Qed.

  End MinimalCapsPredicates.

  Include IrisSignatureRules MinCapsBase MinCapsSignature MinCapsProgram MinCapsSemantics MinCapsIrisBase.
  Include IrisAdequacy MinCapsBase MinCapsSignature MinCapsProgram MinCapsSemantics MinCapsIrisBase MinCapsIrisAdeqParameters.

End MinCapsIrisInstance.

Module MinCapsIrisInstanceWithContracts.
  Include ProgramLogicOn MinCapsBase MinCapsSignature MinCapsProgram MinCapsSpecification.
  Include IrisInstanceWithContracts MinCapsBase MinCapsSignature MinCapsProgram MinCapsSemantics
    MinCapsSpecification MinCapsIrisBase MinCapsIrisAdeqParameters MinCapsIrisInstance.

  Section LemProofs.
    (* In this section we prove that the lemmas we defined in this case study
       are sound. *)
    Context {Σ} `{sg : sailGS Σ}.

    Lemma safe_to_execute_sound :
      ValidLemma lemma_safe_to_execute.
    Proof.
      intros ι. destruct_syminstance ι. cbn.
      iIntros "(#H & [-> _])".
      iFrame.
      rewrite ?fixpoint_interp_eq.
      iSimpl in "H"; auto.
    Qed.

    Lemma open_gprs_sound :
      ValidLemma lemma_open_gprs.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      iIntros "($ & $ & $ & $ & _)".
    Qed.

    Lemma close_gprs_sound :
      ValidLemma lemma_close_gprs.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      by iIntros "($ & $ & $)".
    Qed.

    Lemma int_safe_sound :
      ValidLemma lemma_int_safe.
    Proof.
      intros ι. destruct_syminstance ι. cbn.
      rewrite fixpoint_interp_eq; auto.
    Qed.

    Lemma correctPC_subperm_R_sound :
      ValidLemma lemma_correctPC_subperm_R.
    Proof.
      intros ι. destruct_syminstance ι. cbn.
      iIntros "(%Hpc & _)"; iSplit; auto.
      iPureIntro.
      unfold Subperm.
      unfold CorrectPC in Hpc.
      cbn in *.
      apply andb_prop in Hpc; destruct Hpc as [_ Hpc].
      apply orb_prop in Hpc; destruct Hpc as [H|H];
        destruct p; auto.
    Qed.

    Lemma subperm_not_E_sound :
      ValidLemma lemma_subperm_not_E.
    Proof.
      intros ι. destruct_syminstance ι. cbn.
      iIntros "([[ -> _ ]|[ -> _ ]] & %Hsub & $)";
      iPureIntro;
        unfold Subperm in Hsub;
        intros H; inversion H; subst;
        cbn in Hsub; discriminate.
    Qed.

    Lemma safe_move_cursor_sound :
      ValidLemma lemma_safe_move_cursor.
    Proof.
      intros ι. destruct_syminstance ι. cbn.
      iIntros "(#$ & [[% _] |[% _]])".
      rewrite ?fixpoint_interp_eq.
      destruct p; try now subst.
      exfalso; exact (H eq_refl).
      now subst.
    Qed.

    Lemma safe_sub_perm_sound :
      ValidLemma lemma_safe_sub_perm.
    Proof.
      intros ι. destruct_syminstance ι. cbn.
      iIntros "(#Hsafe & [%Hp _] & #H)".
      iSplit; [done|].
      iApply (interp_subperm_weakening _ _ _ Hp with "H Hsafe").
    Qed.

    Lemma safe_within_range_sound :
      ValidLemma lemma_safe_within_range.
    Proof.
      intros ι. destruct_syminstance ι. cbn.
      iIntros "(#Hsafe & [%Hp _] & #IH & [%Hbounds _])".
      iSplit; first done.
      unfold is_true in Hbounds;
        apply andb_prop in Hbounds;
        destruct Hbounds as [Hb He];
        apply Zle_is_le_bool in Hb;
        apply Zle_is_le_bool in He.
      iApply (interp_weakening _ _ Hp Hb He (Subperm_refl p) with "IH Hsafe").
    Qed.

    Lemma lemSem : LemmaSem.
    Proof.
      intros Δ []; eauto using
        open_gprs_sound, close_gprs_sound, int_safe_sound, correctPC_subperm_R_sound,
        subperm_not_E_sound, safe_move_cursor_sound, safe_sub_perm_sound,
        safe_within_range_sound, safe_to_execute_sound.
    Qed.

  End LemProofs.

  Section ForeignProofs.
    (* In this section we prove that the contracts for the foreign functions
       of this case study are sound. *)
    Context `{sg : sailGS Σ}.

    Lemma dI_sound :
      ValidContractForeign sep_contract_dI dI.
    Proof.
      iIntros (Γ es δ ι Heq) "_".
      destruct_syminstance ι.
      iApply (semWP_foreign (f := dI)).
      iIntros (γ μ) "[Hregs Hmem]".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro.
      iIntros (res γ' μ') "%fcall".
      rewrite Heq in fcall.
      dependent elimination fcall.
      repeat iModIntro.
      iMod "Hclose" as "_".
      iFrame. cbn.
      destruct (pure_decode code).
      - now rewrite semWP_fail.
      - now rewrite semWP_val.
    Qed.

    Import iris.base_logic.lib.gen_heap.

    Lemma extract_ptsto : ∀ (b e a : Addr) (p : Permission),
        ⊢ ⌜b ≤ a⌝%Z -∗
          ⌜a ≤ e⌝%Z -∗
          ⌜Subperm R p ∨ Subperm RW p⌝ -∗
          interp (inr {| cap_permission := p; cap_begin := b; cap_end := e; cap_cursor := a |}) -∗
          inv (mc_invNs.@a) (∃ w, gen_heap.pointsto a (dfrac.DfracOwn 1) w ∗ interp w).
    Proof.
      iIntros (b e a p) "%Hba %Hae %Hsubp #H".
      simpl; rewrite ?fixpoint_interp_eq.
      assert (Hbe: (b <= e)%Z) by (apply (Z.le_trans _ _ _ Hba Hae)).
      destruct p; destruct Hsubp as [|]; try discriminate;
        iDestruct "H" as "[Hsafe | %]"; try lia;
        iSpecialize ("Hsafe" $! Hbe);
        iApply (specialize_range $! (conj Hba Hae) with "Hsafe").
    Qed.

    Lemma later_exists_ptsto : ∀ (a : Addr) (w : MemVal),
        ⊢ gen_heap.pointsto a (dfrac.DfracOwn 1) w -∗
          interp w -∗
          ▷ (∃ w, gen_heap.pointsto a (dfrac.DfracOwn 1) w ∗ interp w).
    Proof. iIntros (a w) "? ?"; iModIntro; iExists _; iAccu. Qed.

    Lemma mem_inv_not_modified : ∀ (μ : Memory) (memmap : gmap Addr MemVal),
        ⊢ ⌜map_Forall (λ (a : Addr) (v : MemVal), μ a = v) memmap⌝ -∗
        gen_heap.gen_heap_interp memmap -∗
        mem_inv μ.
    Proof. iIntros (μ memmap) "Hmap Hmem"; iExists memmap; now iFrame. Qed.

    Lemma map_Forall_update : ∀ (μ : Memory) (memmap : gmap Addr MemVal)
                                (paddr : Addr) (data : MemVal),
        map_Forall (λ (a : Addr) (v : MemVal), μ a = v) memmap ->
        map_Forall (λ (a : Addr) (v : MemVal), fun_wM μ paddr data a = v)
                   (<[paddr:=data]> memmap).
    Proof.
      intros μ memmap paddr data Hmap.
      unfold fun_wM.
      apply map_Forall_lookup.
      intros i x H0.
      destruct (Z.eqb_spec paddr i) as [Heqb|Heqb].
      + subst.
        apply (lookup_insert_rev memmap i); assumption.
      + rewrite -> map_Forall_lookup in Hmap.
        rewrite -> (lookup_insert_ne _ _ _ _ Heqb) in H0.
        apply Hmap; assumption.
    Qed.

    Lemma mem_inv_update : ∀ (μ : Memory) (memmap : gmap Addr MemVal)
                             (paddr : Addr) (data : MemVal),
        ⊢ ⌜map_Forall (λ (a : Addr) (v : MemVal), μ a = v) memmap⌝ -∗
          gen_heap.gen_heap_interp (<[paddr := data]> memmap) -∗
          mem_inv (fun_wM μ paddr data).
    Proof.
      iIntros (μ memmap paddr data) "%Hmap Hmem".
      iExists (<[paddr := data]> memmap); iFrame.
      iPureIntro; apply (map_Forall_update _ _ _ Hmap).
    Qed.

    Lemma rM_sound :
      ValidContractForeign sep_contract_rM rM.
    Proof.
      intros Γ es δ ι Heq; destruct_syminstance ι; cbn in *.
      rename address into a.
      iIntros "(#Hsafe & [%Hsubp _] & [%Hbounds _])".
      apply andb_prop in Hbounds as [Hb%Zle_is_le_bool He%Zle_is_le_bool].
      iApply (semWP_foreign (f := rM)).
      iIntros (γ μ) "[Hregs Hmem]".
      iPoseProof (extract_ptsto b e a p $! Hb He (or_introl Hsubp) with "Hsafe") as "Hown".
      iDestruct "Hmem" as (memmap) "[Hmem' %]".
      iInv "Hown" as "Hinv" "Hclose".
      iMod (fupd_mask_subseteq empty) as "Hclose2"; first set_solver.
      iModIntro.
      iIntros (res γ' μ') "%fcall".
      rewrite Heq in fcall; cbn in fcall.
      dependent elimination fcall.
      repeat iModIntro.
      iDestruct "Hinv" as (v) "Hav".
      iDestruct "Hav" as "[Hav #Hrec]".
      iPoseProof (gen_heap.gen_heap_valid with "Hmem' Hav") as "%".
      iMod "Hclose2" as "_".
      iPoseProof (later_exists_ptsto with "Hav Hrec") as "Hinv".
      iMod ("Hclose" with "Hinv") as "_".
      iModIntro.
      iFrame "Hregs".
      iSplitL "Hmem'".
      iApply (mem_inv_not_modified $! H with "Hmem'").
      iApply wp_value; cbn.
      iSplitL; trivial.
      apply map_Forall_lookup_1 with (i := a) (x := v) in H; auto.
      now subst.
    Qed.

    Lemma wM_sound : ValidContractForeign sep_contract_wM wM.
    Proof.
      intros Γ es δ ι Heq; destruct_syminstance ι; cbn in *.
      rename address into a.
      rename new_value into w.
      iIntros "[#Hwsafe [#Hsafe [[%Hsubp _] [%Hbounds _]]]]".
      apply andb_prop in Hbounds as [Hb%Zle_is_le_bool He%Zle_is_le_bool].
      iApply (semWP_foreign (f := wM)).
      iPoseProof (extract_ptsto b e a p $! Hb He (or_intror Hsubp) with "Hsafe") as "Hown".
      iIntros (γ μ) "[Hregs Hmem]".
      iDestruct "Hmem" as (memmap) "[Hmem' %]".
      iInv "Hown" as "Hinv" "Hclose".
      iMod (fupd_mask_subseteq empty) as "Hclose2"; first set_solver.
      iModIntro.
      iIntros (res γ' μ') "%fcall".
      rewrite Heq in fcall.
      dependent elimination fcall.
      repeat iModIntro.
      iDestruct "Hinv" as (v) "Hav".
      iDestruct "Hav" as "[Hav #Hrec]".
      iMod (gen_heap.gen_heap_update _ _ _ w with "Hmem' Hav") as "[Hmem' Hav]".
      iMod "Hclose2" as "_".
      iPoseProof (later_exists_ptsto with "Hav Hwsafe") as "Hinv".
      iMod ("Hclose" with "Hinv") as "_".
      iModIntro.
      iFrame "Hregs".
      iSplitL.
      iApply (mem_inv_update $! H with "Hmem'").
      now iApply wp_value.
    Qed.

    Lemma foreignSem : ForeignSem.
    Proof.
      intros Δ τ f; destruct f;
        eauto using dI_sound, rM_sound, wM_sound.
    Qed.

  End ForeignProofs.

  (* Import the soundness proofs for the shallow and symbolic executors. *)
  Include MicroSail.RefineExecutor.RefineExecOn MinCapsBase MinCapsSignature
    MinCapsProgram MinCapsSpecification MinCapsShallowExec MinCapsExecutor.
  Include MicroSail.ShallowSoundness.Soundness MinCapsBase MinCapsSignature
    MinCapsProgram MinCapsSpecification MinCapsShallowExec.

  (* contracts_sound proves that all contracts in our contract environment
     are sound. *)
  Lemma contracts_sound `{sg : sailGS Σ} : ⊢ ValidContractEnvSem CEnv.
  Proof.
    apply (sound foreignSem lemSem).
    intros Γ τ f c Heq.
    apply shallow_vcgen_soundness.
    apply symbolic_vcgen_soundness.
    now apply MinCapsValidContracts.ValidContracts.
  Qed.

End MinCapsIrisInstanceWithContracts.
