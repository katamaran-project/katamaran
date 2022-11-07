(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel, Dominique Devriese, Sander Huyghebaert  *)
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
     Iris.Model
     Semantics
     Sep.Hoare
     Sep.Logic
     Specification
     Shallow.Executor
     Shallow.Soundness
     Symbolic.Executor
     Symbolic.Soundness
     MinimalCaps.Machine
     MinimalCaps.Contracts.

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

Ltac destruct_syminstance ι :=
  repeat
    match type of ι with
    | Env _ (ctx.snoc _ (MkB ?s _)) =>
        let id := string_to_ident s in
        let fr := fresh id in
        destruct (env.snocView ι) as [ι fr];
        destruct_syminstance ι
    | Env _ ctx.nil => destruct (env.nilView ι)
    | _ => idtac
    end.

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

  Ltac eliminate_prim_step Heq :=
    let f := fresh "f" in
    match goal with
    | H: MinCapsSemantics.Step _ _ _ _ _ _ _ _ |- _ =>
        dependent elimination H as [MinCapsSemantics.step_stm_foreign _ _ f];
        rewrite Heq in f;
        cbn in f;
        dependent elimination f;
        cbn
    | H: prim_step _ _ _ _ _ _ |- _ =>
          let s := fresh "s" in
          dependent elimination H as [mk_prim_step s];
          dependent elimination s as [MinCapsSemantics.step_stm_foreign _ _ f];
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
                          mc_ghG :> gh.gen_heapGS Z MemVal Σ;
                          mc_invNs : namespace
                        }.
    #[export] Existing Instance mc_ghG.

    Definition memGpreS : gFunctors -> Set := fun Σ => gh.gen_heapGpreS Z MemVal Σ.
    Definition memGS : gFunctors -> Set := mcMemGS.
    Definition memΣ : gFunctors := gh.gen_heapΣ Z MemVal.

    Definition memΣ_GpreS : forall {Σ}, subG memΣ Σ -> memGpreS Σ :=
      fun {Σ} => gh.subG_gen_heapGpreS (Σ := Σ) (L := Z) (V := MemVal).

    Definition mem_inv : forall {Σ}, memGS Σ -> Memory -> iProp Σ :=
      fun {Σ} hG μ =>
        (∃ memmap, gen_heap_interp (hG := mc_ghG (mcMemGS := hG)) memmap ∗
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

    Definition mem_res : forall {Σ}, memGS Σ -> Memory -> iProp Σ :=
      fun {Σ} hG μ =>
        ([∗ map] l↦v ∈ initMemMap μ, mapsto (hG := mc_ghG (mcMemGS := hG)) l (DfracOwn 1) v) %I.

    Lemma mem_inv_init : forall Σ (μ : Memory), memGpreS Σ ->
                                                ⊢ |==> ∃ mG : memGS Σ, (mem_inv mG μ ∗ mem_res mG μ)%I.
    Proof.
      iIntros (Σ μ gHP).

      iMod (gen_heap_init (gen_heapGpreS0 := gHP) (L := Addr) (V := MemVal) empty) as (gH) "[inv _]".
      pose (memmap := initMemMap μ).
      iMod (gen_heap_alloc_big empty memmap (map_disjoint_empty_r memmap) with "inv") as "(inv & res & _)".
      iModIntro.

      rewrite (right_id empty union memmap).

      iExists (McMemGS gH (nroot .@ "addr_inv")).
      iFrame.
      iExists memmap.
      iFrame.
      iPureIntro.
      apply initMemMap_works.
    Qed.
  End WithIrisNotations.

  Include IrisResources MinCapsBase MinCapsProgram MinCapsSemantics.
End MinCapsIrisBase.

Module Import MinCapsIrisInstance <: IrisInstance MinCapsBase MinCapsProgram MinCapsSemantics MinCapsSignature MinCapsIrisBase.
  Import env.notations.
  Import iris.bi.interface.
  Import iris.bi.big_op.
  Import iris.base_logic.lib.iprop.
  Import iris.base_logic.lib.gen_heap.

  Section Predicates.
    Context {Σ} `{sailRegGS Σ} `{invGS Σ} {mG : mcMemGS Σ}.

    Definition MinCaps_ptsreg (reg : RegName) (v : Z + Capability) : iProp Σ :=
      match reg with
      | R0 => reg_pointsTo reg0 v
      | R1 => reg_pointsTo reg1 v
      | R2 => reg_pointsTo reg2 v
      | R3 => reg_pointsTo reg3 v
      end.

    Lemma MinCaps_ptsreg_regtag_to_reg (reg : RegName) (v : Z + Capability) :
      MinCaps_ptsreg reg v = reg_pointsTo (regtag_to_reg reg) v.
    Proof.
      by destruct reg.
    Qed.

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

    (* Notation D := (MemVal -d> iPropO Σ). *)
    (* Notation C := (Capability -d> iPropO Σ). *)
    (* Implicit Type w : MemVal. *)
    Notation D := ((leibnizO MemVal) -n> iPropO Σ). (* TODO: try -d>, drop leibnizO, might not need λne *)
    Notation C := ((leibnizO Capability) -n> iPropO Σ). (* TODO: try -d>, drop leibnizO, might not need λne *)
    Implicit Type w : (leibnizO MemVal).

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

    Definition GPRs : list RegName := finite.enum RegName.

    (* TODO:
       - Make the change to D proposed above, might simplify some stuff
         Need to look into what the difference induced by that change is...
       - make the interp definitions more uniform, i.e., they should all take an
         interp (= safe) and have return type D *)
    Program Definition interp_gprs : D -n> iPropO Σ :=
      λne interp, ([∗ list] r ∈ GPRs, (∃ w, MinCaps_ptsreg r w ∗ interp w))%I.
    Solve Obligations with solve_proper.

    Definition interp_loop `{sg : sailGS Σ} : iProp Σ :=
      (WP (MkConf (FunDef loop) env.nil) ?{{_, True}})%I.

    Definition interp_expr (interp : D) : C :=
      (λne (c : leibnizO Capability),
        reg_pointsTo pc c ∗ interp_gprs interp -∗ (interp_loop (sg := SailGS _ _ mG)))%I.

    (* TODO: Check if I tried changing this one to a discrete one, should remain non-expansive so we can proof contractiveness *)
    Program Definition interp_ref_inv (a : Addr) : D -n> iPropO Σ :=
      λne P, (∃ w, mapsto a (DfracOwn 1) w ∗ P w)%I.
    Solve Obligations with solve_proper.

    Definition interp_cap_inv (c : Capability) (interp : D) :iProp Σ := 
      match c with
      | MkCap _ b e a =>
          (⌜(b <= e)%Z⌝ →
           ⌜b ∈ liveAddrs /\ e ∈ liveAddrs⌝ ∗
                               [∗ list] a ∈ (region_addrs b e), inv (mc_invNs .@ a) (interp_ref_inv a interp))
          ∨ ⌜(e < b)%Z⌝
      end.

    Program Definition interp_cap_O : D := λne _, True%I.

    Program Definition interp_cap_R (interp : D) : D :=
      λne w, (match w with
              | inr (MkCap R b e a) => interp_cap_inv (MkCap R b e a) interp
              | _                   => False
              end)%I.
    Solve Obligations with solve_proper.

    Program Definition interp_cap_RW (interp : D) : D :=
      λne w, (match w with
              | inr (MkCap RW b e a) => interp_cap_inv (MkCap RW b e a) interp
              | _                    => False
              end)%I.
    Solve Obligations with solve_proper.

    Program Definition enter_cond (b e a : Addr) : D -n> iPropO Σ :=
      λne interp, (▷ □ interp_expr interp (MkCap R b e a))%I.
    Solve Obligations with solve_proper.

    Program Definition interp_expression (interp : D) : C :=
      λne c, (match c with
                   | {| cap_permission := p; cap_begin := b; cap_end := e; cap_cursor := a |} =>
                       ⌜p = R⌝ ∧ enter_cond b e a interp
                   end)%I.

    Program Definition interp_cap_E (interp : D) : D :=
      λne w, (match w with
              | inr (MkCap E b e a) => enter_cond b e a interp
              | _                   => False
              end)%I.
    Solve Obligations with solve_proper.

    Program Definition interp_z : D :=
      λne w, ⌜ match w with
               | inl _ => True
               | _     => False
               end ⌝%I.
    Solve Obligations with solve_proper.

    Definition interp1 (interp : D) : D :=
      λne w, (match w with
              | inl _                => interp_z w
              | inr (MkCap O _ _ _)  => interp_cap_O w
              | inr (MkCap R _ _ _)  => interp_cap_R interp w
              | inr (MkCap RW _ _ _) => interp_cap_RW interp w
              | inr (MkCap E _ _ _)  => interp_cap_E interp w
              end)%I.

    Global Instance interp_cap_O_contractive :
      Contractive interp_cap_O.
    Proof. solve_contractive. Qed.
    Global Instance interp_cap_R_contractive :
      Contractive interp_cap_R.
    Proof.
      intros n x y Hdist w.
      destruct w; auto.
      destruct c; destruct cap_permission; solve_contractive.
    Qed.
    Global Instance interp_cap_RW_contractive :
      Contractive interp_cap_RW.
    Proof.
      intros n x y Hdist w.
      destruct w; auto.
      destruct c; destruct cap_permission; solve_contractive.
    Qed.
    Global Instance interp_cap_E_contractive :
      Contractive interp_cap_E.
    Proof.
      intros n x y Hdist w.
      destruct w; auto.
      destruct c; destruct cap_permission; solve_contractive.
    Qed.
    Global Instance interp1_contractive :
      Contractive interp1.
    Proof. solve_contractive. Qed.

    Definition interp : D :=
      λne w, (fixpoint (interp1)) w.

    Lemma fixpoint_interp1_eq w :
      fixpoint interp1 w ≡ interp1 (fixpoint interp1) w.
    Proof. exact: (fixpoint_unfold interp1 w). Qed.

    Lemma le_liveAddrs (a b e : Addr) :
      b ∈ liveAddrs ∧ e ∈ liveAddrs ->
      (b <= a)%Z ∧ (a <= e)%Z ->
      a ∈ liveAddrs.
    Proof.
      intros [Hb He] [Hba Hae].
      apply elem_of_seqZ in Hb.
      apply elem_of_seqZ in He.
      destruct Hb as [H0b Hbm].
      destruct He as [H0e Hem].
      rewrite elem_of_seqZ.
      split; lia.
    Qed.

    Lemma region_addrs_submseteq  (b' e' b e : Addr) :
      ⊢ ⌜ (b <= b')%Z /\ (e' <= e)%Z ⌝ -∗
        ([∗ list] a ∈ (region_addrs b e), inv (mc_invNs .@ a) (∃ w, mapsto a (DfracOwn 1) w ∗ fixpoint interp1 w))%I -∗
        ([∗ list] a ∈ (region_addrs b' e'), inv (mc_invNs .@ a) (∃ w, mapsto a (DfracOwn 1) w ∗ fixpoint interp1 w))%I.
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
         [∗ list] a ∈ (region_addrs b e), inv (mc_invNs .@ a) (∃ w, mapsto a (DfracOwn 1) w ∗ fixpoint interp1 w))%I -∗
        (inv (mc_invNs .@ addr) (∃ w, mapsto addr (DfracOwn 1) w ∗ fixpoint interp1 w))%I.
    Proof.
      iIntros "[% %] [[% %] Hrange]".
      iApply (big_sepL_elem_of with "Hrange").
      apply element_of_region_addrs; try assumption.
      split; assumption.
    Qed.

    Global Instance interp_Persistent (w : leibnizO MemVal) : Persistent (interp w).
    Proof. destruct w; simpl; rewrite fixpoint_interp1_eq; simpl; first apply _.
           destruct c; destruct cap_permission; apply _. Qed.

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
        rewrite !fixpoint_interp1_eq; try done.
      - repeat iModIntro.
        iIntros "(Hpc & Hreg0 & Hreg1 & Hreg2 & Hreg3 & _)".
        iApply ("IH" with "[-Hpc IH HA] Hpc"); try iFrame.
        done.
        iModIntro.
        rewrite !fixpoint_interp1_eq; cbn - [interp_cap_inv].
        iApply (interp_cap_inv_weakening p a a (Z.le_refl b) (Z.le_refl e) with "HA").
      - repeat iModIntro.
        iIntros "(Hpc & Hreg0 & Hreg1 & Hreg2 & Hreg3 & _)".
        iApply ("IH" with "[-Hpc IH HA] Hpc"); try iFrame.
        done.
        iModIntro.
        rewrite !fixpoint_interp1_eq; cbn - [interp_cap_inv].
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
      - rewrite !fixpoint_interp1_eq; done.
      - destruct p eqn:Ep; inversion Hsubperm;
          rewrite !fixpoint_interp1_eq; cbn - [interp_cap_inv];
          iApply (interp_cap_inv_weakening p a a' Hb He with "HA").
      - destruct p eqn:Ep; inversion Hsubperm;
          rewrite !fixpoint_interp1_eq; cbn - [interp_cap_inv];
          iApply (interp_cap_inv_weakening p a a' Hb He with "HA").
      - destruct p eqn:Ep; inversion Hsubperm; last contradiction;
          iApply (interp_subperm_weakening _ _ _ Hsubperm with "IH");
          rewrite !fixpoint_interp1_eq;
          iApply (interp_cap_inv_weakening p a a' Hb He with "HA").
    Qed.
  End Predicates.

  Section MinimalCapsPredicates.
    Import env.notations.

    Equations(noeqns) luser_inst `{sailRegGS Σ, invGS Σ, mcMemGS Σ}
             (p : Predicate) (ts : Env Val (𝑯_Ty p)) : iProp Σ :=
    | ptsreg  | [r; v] => MinCaps_ptsreg r v
    | ptsto   | [a; v] => mapsto a (DfracOwn 1) v
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

  Include IrisSignatureRules MinCapsBase MinCapsProgram MinCapsSemantics MinCapsSignature MinCapsIrisBase.

End MinCapsIrisInstance.

Module MinCapsIrisInstanceWithContracts.
  Include ProgramLogicOn MinCapsBase MinCapsProgram MinCapsSignature MinCapsSpecification.
  Include IrisInstanceWithContracts MinCapsBase MinCapsProgram MinCapsSemantics
    MinCapsSignature MinCapsSpecification MinCapsIrisBase MinCapsIrisInstance.

  Section LemProofs.
    Context {Σ} `{sg : sailGS Σ}.

    Lemma safe_to_execute_sound :
      ValidLemma lemma_safe_to_execute.
    Proof.
      intros ι. destruct_syminstance ι. cbn.
      iIntros "(#H & [-> _])".
      iFrame.
      rewrite ?fixpoint_interp1_eq.
      iSimpl in "H"; auto.
    Qed.

    Lemma open_ptsreg_sound :
      ValidLemma lemma_open_ptsreg.
    Proof.
      intros ι. destruct_syminstance ι. cbn.
      destruct reg; auto.
    Qed.

    Lemma close_ptsreg_sound {R} :
      ValidLemma (lemma_close_ptsreg R).
    Proof.
      intros ι. destruct_syminstance ι. cbn.
      rewrite MinCaps_ptsreg_regtag_to_reg; auto.
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
      iIntros "($ & $ & $ & $)".
    Qed.

    Lemma int_safe_sound :
      ValidLemma lemma_int_safe.
    Proof.
      intros ι. destruct_syminstance ι. cbn.
      rewrite fixpoint_interp1_eq; auto.
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
      iIntros "(%H & %Hsub & $)".
      iPureIntro.
      destruct H as [[-> _]|[-> _]];
        unfold Subperm in Hsub;
        unfold Not_is_perm; destruct p'; auto.
    Qed.

    Lemma safe_move_cursor_sound :
      ValidLemma lemma_safe_move_cursor.
    Proof.
      intros ι. destruct_syminstance ι. cbn.
      iIntros "(#$ & [[% _] |[% _]])".
      rewrite ?fixpoint_interp1_eq.
      destruct p; auto.
      unfold Not_is_perm, MinCapsSignature.is_perm in H.
      discriminate.
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
      iApply (interp_weakening _ _ (Not_is_perm_prop Hp) Hb He (Subperm_refl p) with "IH Hsafe").
    Qed.

    Lemma lemSem : LemmaSem.
    Proof.
      intros Δ []; eauto using
                         open_ptsreg_sound, close_ptsreg_sound,
        open_gprs_sound, close_gprs_sound, int_safe_sound, correctPC_subperm_R_sound,
        subperm_not_E_sound, safe_move_cursor_sound, safe_sub_perm_sound,
        safe_within_range_sound, safe_to_execute_sound.
    Qed.

  End LemProofs.

  Section ForeignProofs.
    Context `{sg : sailGS Σ} `{invGS}.

    Lemma dI_sound :
      ValidContractForeign sep_contract_dI dI.
    Proof.
      iIntros (Γ es δ ι Heq) "_".
      destruct_syminstances.
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
          inv (mc_invNs.@a) (∃ w, gen_heap.mapsto a (dfrac.DfracOwn 1) w ∗ interp w).
    Proof.
      iIntros (b e a p) "%Hba %Hae %Hsubp #H".
      simpl; rewrite ?fixpoint_interp1_eq.
      assert (Hbe: (b <= e)%Z) by (apply (Z.le_trans _ _ _ Hba Hae)).
      destruct p; destruct Hsubp as [|]; try discriminate;
        iDestruct "H" as "[Hsafe | %]"; try lia;
        iSpecialize ("Hsafe" $! Hbe);
        iApply (specialize_range $! (conj Hba Hae) with "Hsafe").
    Qed.

    Lemma later_exists_ptsto : ∀ (a : Addr) (w : MemVal),
        ⊢ gen_heap.mapsto a (dfrac.DfracOwn 1) w -∗
          interp w -∗
          ▷ (∃ w, gen_heap.mapsto a (dfrac.DfracOwn 1) w ∗ interp w).
    Proof. iIntros (a w) "? ?"; iModIntro; iExists _; iAccu. Qed.

    Lemma mem_inv_not_modified : ∀ (μ : Memory) (memmap : gmap Addr MemVal),
        ⊢ ⌜map_Forall (λ (a : Addr) (v : MemVal), μ a = v) memmap⌝ -∗
        gen_heap.gen_heap_interp memmap -∗
        mem_inv sailGS_memGS μ.
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
          mem_inv sailGS_memGS (fun_wM μ paddr data).
    Proof.
      iIntros (μ memmap paddr data) "%Hmap Hmem".
      iExists (<[paddr := data]> memmap); iFrame.
      iPureIntro; apply (map_Forall_update _ _ _ Hmap).
    Qed.

    Lemma rM_sound :
      ValidContractForeign sep_contract_rM rM.
    Proof.
      intros Γ es δ ι Heq; destruct_syminstances; cbn in *.
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
      iFrame.
      iSplitL "Hmem'".
      iApply (mem_inv_not_modified $! H0 with "Hmem'").
      iApply wp_value; cbn.
      iSplitL; trivial.
      apply map_Forall_lookup_1 with (i := a) (x := v) in H0; auto.
      now subst.
    Qed.

    Lemma wM_sound : ValidContractForeign sep_contract_wM wM.
    Proof.
      intros Γ es δ ι Heq; destruct_syminstances; cbn in *.
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
      iSplitL; trivial.
      iFrame.
      iApply (mem_inv_update $! H0 with "Hmem'").
      now iApply wp_value.
    Qed.

    Lemma foreignSem : ForeignSem.
    Proof.
      intros Δ τ f; destruct f;
        eauto using dI_sound, rM_sound, wM_sound.
    Qed.

  End ForeignProofs.

  (* Import the soundness proofs for the shallow and symbolic executors. *)
  Include Symbolic.Soundness.Soundness MinCapsBase MinCapsProgram MinCapsSignature
    MinCapsSpecification MinCapsSolver MinCapsShallowExec MinCapsExecutor.
  Include Shallow.Soundness.Soundness MinCapsBase MinCapsProgram MinCapsSignature
    MinCapsSpecification MinCapsShallowExec.

  Lemma contracts_sound `{sg : sailGS Σ} : ⊢ ValidContractEnvSem CEnv.
  Proof.
    apply (sound foreignSem lemSem).
    intros Γ τ f c Heq.
    apply shallow_vcgen_soundness.
    apply symbolic_vcgen_soundness.
    now apply MinCapsValidContracts.ValidContracts.
  Qed.

End MinCapsIrisInstanceWithContracts.
