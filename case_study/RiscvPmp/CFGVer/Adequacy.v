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


(* ========================================================================= *)
(* Adequacy.v — binary Iris model infrastructure and adequacy.               *)
(*                                                                           *)
(* The myWP2_loop fixpoint, resource creation (create_resources), the        *)
(* semWP2 lockstep/preservation lemmas, the adequacy theorems relating       *)
(* semWP2 to the RiscVNSteps relations of Noninterference.v, and the         *)
(* AdequacyTools section (resource introduction lemmas + the sound_*_myWP2   *)
(* bridge from the verifier's VC to myWP2_loop).                             *)
(* ========================================================================= *)

From Coq Require Import
     ZArith.ZArith
     Lists.List
     micromega.Lia
     Strings.String.
From Katamaran Require Import
     Notations
     Bitvector
     Semantics
     RiscvPmp.CFGVer.Spec
     RiscvPmp.Machine
     RiscvPmp.Sig.
From stdpp Require Import gmap.
From Katamaran Require Import
     RiscvPmp.CFGVer.Verifier
     RiscvPmp.CFGVer.VerifierRel
     RiscvPmp.CFGVer.SpecIris
     RiscvPmp.CFGVer.Noninterference
     RiscvPmp.CFGVer.Tables.
From iris.base_logic Require Import lib.gen_heap lib.iprop invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac big_op.
From iris.program_logic Require weakestpre adequacy.
From iris.proofmode Require string_ident tactics.
From stdpp Require namespaces.
From Equations Require Import Equations.

Import RiscvPmpProgram.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import bv.notations.
Import env.notations.
Import ListNotations.

Import RiscvPmpCFGVerifExecutor.
Import Assembly.
Import RiscvPmp.Sig.
Import iris.proofmode.tactics.
Import iris.proofmode.tactics.
Import IrisInstanceBinary.
Import RiscvPmpIrisInstance2.
Import RiscvPmpSemantics.
Import RiscvPmpIrisAdeqParams2.
Import SmallStepNotations.
Import IrisModelBinary.RiscvPmpIrisBase2.
Import iris.algebra.excl.
Import iris.algebra.gmap.

  Definition asn_regs_ptsto_with_registers γ1 γ2 : Assertion ctx.nil :=
    asn_and_regs
      (fun r => asn.chunk (chunk_ptsreg r (term_relval _ (NonSyncVal (read_register γ1 r) (read_register γ2 r))))).

  Lemma gprs_with_registers_equiv `{sailGS2 Σ} γ1 γ2 :
      interp_gprs_with_registers γ1 γ2 ⊣⊢
        asn.interpret (asn_regs_ptsto_with_registers γ1 γ2) env.nil.
  Proof.
    unfold interp_gprs_with_registers.
    rewrite big_sepS_list_to_set; [|apply bv.finite.nodup_enum].
    cbn. iSplit.
    - iIntros "(_ & H)"; repeat iDestruct "H" as "($ & H)".
    - iIntros "H"; iSplitR; auto.
      repeat iDestruct "H" as "($ & H)"; iFrame.
  Qed.

    Definition myWp2 `{sailGS2 Σ} :=
        iProp Σ.

    Definition myWP2_loop_fix `{sailGS2 Σ} (ExitCond : iProp Σ) (wp : myWp2) :
      myWp2 :=
      (ExitCond ∨
        ∃ v, pc ↦ᵣ SyncVal v ∗
        (pc ↦ᵣ SyncVal v -∗
         semWP2 env.nil env.nil (FunDef step) (FunDef step)
           (fun v1 _ v2 _ =>
              match v1 , v2 with
              | inr _ , inr _ => True
              | inl v1 , inl v2 => ▷ wp
              | _ , _ => False
              end
           )%I))%I.
    (* non-exit branch: pc ↦ᵣ SyncVal v witnesses PC sync at loop boundary;
       wand avoids duplicating the resource for the semWP2 body *)
  
  Global Instance myWP2_loop_fix_Contractive `{sailGS2 Σ} (ExitCond : iProp Σ) :
    Contractive (myWP2_loop_fix ExitCond).
  Proof.
    rewrite /myWP2_loop_fix /= => n wp wp' Hwp.
    f_equiv.
    f_equiv => v.
    f_equiv.
    f_equiv.
    do 7 (f_contractive || f_equiv).
    f_contractive. apply Hwp.
  Qed.

  Definition myWP2_loop `{sailGS2 Σ} (ExitCond : iProp Σ) : myWp2 :=
    fixpoint (myWP2_loop_fix ExitCond).

  Lemma fixpoint_myWP2_loop_fix_eq `{sailGS2 Σ} (ExitCond : iProp Σ) :
    fixpoint (myWP2_loop_fix ExitCond) ≡ myWP2_loop_fix ExitCond (myWP2_loop ExitCond).
  Proof. exact: (fixpoint_unfold (myWP2_loop_fix ExitCond)). Qed.

  Lemma fixpoint_myWP2_loop_eq `{sailGS2 Σ} (ExitCond : iProp Σ) :
    myWP2_loop ExitCond ≡ myWP2_loop_fix ExitCond (myWP2_loop ExitCond).
  Proof. unfold myWP2_loop. rewrite {1}fixpoint_myWP2_loop_fix_eq. unfold myWP2_loop. done.
  Qed.

  Lemma exitCondImpliesMyWP2_loop `{sailGS2 Σ} (ExitCond : iProp Σ) :
    ExitCond ⊢ myWP2_loop ExitCond.
  Proof.
    iIntros "EC". rewrite fixpoint_myWP2_loop_eq. unfold myWP2_loop_fix. iLeft. done.
  Qed.

  Definition pcOutOfInstrs (start : Val ty_word) (instrs : list AST) (pc : Val ty_xlenbits) : Prop :=
      bv.ult pc start \/ bv.uge pc (start + bv.of_N (4 * N.of_nat (length instrs))).

  Definition pcBehindInstrs (start : Val ty_word) (instrs : list AST) (pc : Val ty_xlenbits) : Prop :=
    pc  = (start + bv_instrsize * bv.of_nat (length instrs))%bv.

  Add Ring BitVector : (bv.ring_theory 32).
  Definition pcBehindInstrs_app (start : Val ty_word) (instr : AST) (instrs : list AST) (pc : Val ty_xlenbits) : pcBehindInstrs start (instr :: instrs) pc <-> pcBehindInstrs (start + bv_instrsize)%bv instrs pc.
  Proof.
    unfold pcBehindInstrs.
    split; intro H; rewrite H;
      cbn; rewrite bv.of_nat_S; ring.
  Qed.

    Import IrisModel.RiscvPmpIrisBase.

    Lemma reg2_change `{sailGS2 Σ} {γ1 γ2 γ1' γ2'} :
      own_regstore2 γ1 γ2 ∗ regs_inv2 γ1' γ2' ⊢
        ⌜ read_register γ1 pc = read_register γ1' pc /\ read_register γ2 pc = read_register γ2' pc ⌝.
    Proof.
      iIntros "(HownRegstore & Hinv)".
      unfold own_regstore2; cbn.
      iDestruct "HownRegstore" as "(Hpc & _)".
      iPoseProof (reg_valid2 with "Hinv Hpc") as "(%eq1 & %eq2)".
      cbn in *. rewrite eq1 eq2. done.
    Qed.

    Definition list_sum_plus_one (l : list nat) :=
      foldr (fun a b => a + 1 + b) 0 l.

    Lemma list_sum_plus_one_app : ∀ l1 l2 : list nat, list_sum_plus_one (l1 ++ l2) = list_sum_plus_one l1 + list_sum_plus_one l2.
    Proof.
      unfold list_sum_plus_one.
      induction l1.
      - auto.
      - cbn in *. intro l2. rewrite IHl1. induction l2.
        + lia.
        + cbn. lia.
    Qed.

    Definition memory_in_sync (μ1 μ2 : Memory) (la : list Addr) :=
      Forall (fun a => (memory_ram μ1) a = (memory_ram μ2) a) la.

    Lemma mem_sync_app μ1 μ2 a la1 :
      memory_in_sync μ1 μ2 (a :: la1) <-> (memory_ram μ1) a = (memory_ram μ2) a /\ memory_in_sync μ1 μ2 la1.
    Proof.
      unfold memory_in_sync.
      split.
      - intro H. by inversion H.
      - intros (h & H). by constructor.
    Qed.

        Lemma create_resources Σ {sG' : subG memΣ2 Σ} {sG'' : subG sailΣ2 Σ} (Hinv : invGS Σ) γ1 γ2 μ1 μ2 :
      ⊢ |==>
        ∃ regs1 regs2 memG, let sG := @SailGS2 Σ Hinv (SailRegGS2 (SailRegGS (@reg_pre_inG2_left _ (@subG_sailGpreS _ _)) regs1) (SailRegGS (@reg_pre_inG2_right _ (@subG_sailGpreS _ sG'')) regs2)) memG in
           mem_inv2 (@sailGS2_memGS Σ sG) μ1 μ2 ∗ mem_res2 μ1 μ2 ∗
             @regs_inv2 _ (@sailGS2_regGS2 Σ sG) γ1 γ2 ∗ @own_regstore2 _ sG γ1 γ2.
      Proof.
        iMod (own_alloc ((● RegStore_to_map γ1 ⋅ ◯ RegStore_to_map γ1 ) : regUR)) as (regs1) "[Hregsown1 Hregsinv1]".
    { apply auth_both_valid.
      intuition.
      apply RegStore_to_map_valid. }
    iMod (own_alloc ((● RegStore_to_map γ2 ⋅ ◯ RegStore_to_map γ2 ) : regUR)) as (regs2) "[Hregsown2 Hregsinv2]".
    { apply auth_both_valid.
      intuition.
      apply RegStore_to_map_valid. }
    pose proof (memΣ_GpreS2 (Σ := Σ) _) as mGS.
    iMod (mem_inv_init2 (gHP := mGS) μ1 μ2) as (memG) "[Hmem Rmem]".
    pose (sG := @SailGS2 Σ Hinv (SailRegGS2 (SailRegGS (@reg_pre_inG2_left _ (@subG_sailGpreS _ _)) regs1) (SailRegGS (@reg_pre_inG2_right _ (@subG_sailGpreS _ sG'')) regs2)) memG).
    iAssert (regs_inv2 γ1 γ2) with "[Hregsown1 Hregsown2]" as "Hregs".
    { iSplitL "Hregsown1";
      by iApply own_RegStore_to_regs_inv.
    }
    iAssert (own_regstore2 γ1 γ2) with "[Hregsinv1 Hregsinv2]" as "Rregs".
    { iApply RiscvPmpIrisInstance2.own_RegStore_to_map_reg_pointsTos.
      apply finite.NoDup_enum.
      iSplitR "Hregsinv2"; iAssumption.
    }
    iModIntro. iExists regs1, regs2, memG. iFrame "Hmem Rmem Hregs Rregs".
      Qed.

  (*   Lemma adequacy_gen_RiscVNStepsExitCond l exitCond {γ11 γ12 γ21 γ22} {μ11 μ12 μ21 μ22} *)
  (*   (φ : Prop) : *)
  (*   ⟨ γ11, μ11 ⟩ -l( exitCond , l )->* ⟨ γ12, μ12 ⟩ -> *)
  (*   ⟨ γ21, μ21 ⟩ -l( exitCond , l )->* ⟨ γ22, μ22 ⟩ -> *)
  (*   (forall `{sailGS2 Σ}, *)
  (*       mem_res2 μ11 μ21 ∗ own_regstore2 γ11 γ21 ⊢ *)
  (*         |={⊤}=> myWP2_loop *)
  (*                   (∃ a, pc ↦ᵣ a ∗ *)
  (*                      ⌜ exitCond (ty.projLeft a) ∨ exitCond (ty.projRight a) ⌝) *)
  (*       ∗ (mem_inv2 _ μ12 μ22 ={⊤,∅}=∗ ⌜φ⌝) *)
  (*   )%I -> φ. *)
  (* Proof. *)
  (*   intros Heval1 Heval2 Hwp. *)
  (*   refine (uPred.pure_soundness _ *)
  (*             (step_fupdN_soundness_gen (Σ := sailΣ2) _ HasLc (list_sum_plus_one l) (list_sum_plus_one l) _)). *)
  (*   iIntros (Hinv) "Hcred'". *)
  (*   iMod (create_resources Hinv γ11 γ21 μ11 μ21) as (regs1 regs2 memG) "(Hmem & Rmem & Hregs & Rregs)". *)
  (*   pose (sG := @SailGS2 sailΣ2 Hinv (SailRegGS2 (SailRegGS (@reg_pre_inG2_left _ (@subG_sailGpreS _ _)) regs1) (SailRegGS (@reg_pre_inG2_right _ (@subG_sailGpreS _ _)) regs2)) memG). *)
  (*   specialize (Hwp _ sG). *)
  (*   iPoseProof (Hwp with "[$Rmem $Rregs]") as "Hwp2". *)
  (*   clear Hwp. *)
  (*   iStopProof. *)
  (*   revert Heval1 Heval2. *)
  (*   revert γ11 μ11 γ21 μ21. *)
  (*   induction l; iIntros (γ11 μ11 γ21 μ21 Heval1 Heval2) "(Hcred & Hmem & Hregs & Hwp2)". *)
  (*   - inversion Heval1. inversion Heval2. subst. *)
  (*     iMod "Hwp2" as "[_ Hcont]". *)
  (*     iMod ("Hcont" with "Hmem") as "%Hφ". *)
  (*     cbn. done. *)
  (*   - inversion Heval1 as [ | ? ? γ1 ? μ1 ? nEC1 Hstep1 Hevaln1]. clear Heval1. *)
  (*     inversion Heval2 as [ | ? ? γ2 ? μ2 ? nEC2 Hstep2 Hevaln2]. clear Heval2. subst. *)
  (*     specialize (IHl _ _ _ _ Hevaln1 Hevaln2). *)
  (*     rewrite fixpoint_myWP2_loop_eq. *)
  (*     unfold myWP2_loop_fix. *)
  (*     iMod "Hwp2" as "([H | Hwp2] & Hφ)". *)
  (*     + iDestruct "H" as (a') "(Hpc & %ECs)". *)
  (*       unfold reg_pointsTo2. *)
  (*       iPoseProof (reg_valid2 with "[$Hregs] [$Hpc]") as "(%eq1 & %eq2)". *)
  (*       rewrite eq1 in nEC1. rewrite eq2 in nEC2. tauto. *)
  (*     + iPoseProof (semWP2_preservation Hstep1 Hstep2 with "[$Hmem $Hregs]") as "Hwp". *)
  (*       iSpecialize ("Hwp" with "Hwp2"). *)
  (*       iMod "Hwp". *)
  (*       change (list_sum_plus_one (a :: l)) with (a + 1 + list_sum_plus_one l). *)
  (*       iAssert (|={∅}▷=>^a |={∅}=>  |={∅}▷=> |={∅}▷=>^(list_sum_plus_one l) ⌜φ⌝)%I with "[-]" as "H"; last first. *)
  (*       { do 2 rewrite step_fupdN_add. destruct a. done. by iApply step_fupdN_S_fupd. } *)
  (*       iApply (step_fupdN_wand with "Hwp"). *)
  (*       iIntros ">(Hmem & Hregs & Hwp)". *)
  (*       rewrite semWP2_val. *)
  (*       iMod "Hwp" as "Hwp". *)
  (*       rewrite (into_sep_lc_add (a + 1) (list_sum_plus_one l)). *)
  (*       rewrite (into_sep_lc_add a 1). *)
  (*       iDestruct "Hcred" as "[[Hcreda Hcred1] Hcredl]". *)
  (*       iMod (lc_fupd_elim_later with "Hcred1 Hwp") as "Hwp". *)
  (*       now iMod (IHl with "[$Hmem $Hcredl $Hregs $Hwp $Hφ]") as "IHl". *)
  (* Qed. *)

  From Equations Require Import Equations.

  Lemma nsteps_to_lsteps {γ γ' : RegStore} {μ μ' : Memory} ExitCond n :
    ⟨ γ, μ ⟩ -( ExitCond , n )->* ⟨ γ', μ' ⟩ ->
    ∃ l, length l = n ∧
           ⟨ γ, μ ⟩ -l( ExitCond , l )->* ⟨ γ', μ' ⟩.
  Proof.
    revert γ μ.
    induction n.
    - intros γ μ nsteps. exists []. inversion nsteps. split; auto. constructor.
    - intros γ μ nsteps. dependent elimination nsteps.
      destruct (IHn γ2 μ2 r0) as [l Hl].
      destruct (steps_to_nsteps r) as [n Hn].
      exists (n :: l).
      destruct Hl as [Hlen Hl].
      cbn. split.
      + by rewrite Hlen.
      + econstructor; eauto.
  Qed.

    Lemma semWP2_lockstep `{sailGS2 Σ} {s1 s2}
      {γ1 μ1 δ1 γ1' μ1' n}
      {γ2 μ2 δ2}
      {Q}
      (Hsteps1 : NSteps γ1 μ1 δ1 s1 γ1' μ1' [env] (stm_val ty.unit ()) n) :
      mem_inv2 _ μ1 μ2 ∗
        regs_inv2 γ1 γ2 ∗
        semWP2 δ1 δ2 s1 s2 Q ⊢
        |={⊤,∅}=> |={∅}▷=>^n ⌜ ∃ γ2' μ2', NSteps γ2 μ2 δ2 s2 γ2' μ2' [env] (stm_val ty.unit tt) n ⌝.
    Proof.
      revert s1 s2 γ1 γ1' δ1 μ1 μ1' γ2 δ2 μ2 Hsteps1 Q.
      induction n.
      - intros s1 s2 γ1 γ1' δ1 μ1 μ1' γ2 δ2 μ2 Hsteps1 Q.
        iIntros "(Hmem & Hregs & Hwp)".
        inversion Hsteps1. subst.
        rewrite semWP2_unfold. cbn.
          destruct s2; cbn; iMod "Hwp"; auto.
          iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iPureIntro.
          do 2 eexists. destruct v. env.destroy δ2. constructor.
      - intros s1 s2 γ1 γ1' δ1 μ1 μ1' γ2 δ2 μ2 Hsteps1 Q.
        iIntros "(Hmem & Hregs & Hwp)".
        inversion Hsteps1. subst.
        destruct (stm_to_val s2) as [[v2|m2]|] eqn:Hs2.
        + rewrite semWP2_unfold. rewrite (stm_val_stuck H1). rewrite Hs2. cbn.
          iMod "Hwp". done.
        + rewrite semWP2_unfold. rewrite (stm_val_stuck H1). rewrite Hs2. cbn.
          iMod "Hwp". done.
        + destruct (progress s2) as [Hfinal2 | Hprog2].
          * destruct s2; cbn in *; try contradiction; congruence.
          * specialize (Hprog2 γ2 μ2 δ2) as (γ' & μ' & δ' & s' & Hstep2).
            iPoseProof (semWP2_step H1 Hstep2 with "[$Hregs $Hmem $Hwp]") as "Hwp".
            iMod "Hwp". iModIntro. iMod "Hwp". do 2 iModIntro. do 2 iMod "Hwp".
            iDestruct "Hwp" as "(Hregs & Hmem & Hwp)".
            iMod (IHn s0 s' γ0 γ1' δ0 μ0 μ1' γ' δ' μ' H6 Q
                   with "[$Hmem $Hregs $Hwp]") as "IH".
            iModIntro.
            iApply (step_fupdN_mono with "IH").
            iPureIntro.
            intros (γ2'' & μ2'' & HNSteps).
            eexists γ2'', μ2''.
            exact (nstep_trans Hstep2 HNSteps).
    Qed.

    Lemma strip_step_fupdN_pure `{sailGS2 Σ} (n : nat) (φ : Prop) :
      £ n -∗ (|={∅}▷=>^n ⌜φ⌝) -∗ |={∅}=> ⌜φ⌝.
    Proof.
      induction n as [|k IHk]; simpl.
      - iIntros "_ H". iModIntro. iExact "H".
      - iIntros "Hcred H".
        iDestruct "Hcred" as "[H1 Hk]".
        iMod "H" as "H".
        iMod (lc_fupd_elim_later with "H1 H") as "H".
        iMod "H" as "H".
        iApply (IHk with "Hk H").
    Qed.

    Lemma semWP2_lockstep_plain `{sailGS2 Σ} {s1 s2}
      {γ1 μ1 δ1 γ1' μ1' n}
      {γ2 μ2 δ2}
      {Q}
      (Hsteps1 : NSteps γ1 μ1 δ1 s1 γ1' μ1' [env] (stm_val ty.unit ()) n) :
      £ n ∗ mem_inv2 _ μ1 μ2 ∗
        regs_inv2 γ1 γ2 ∗
        semWP2 δ1 δ2 s1 s2 Q ⊢
        |={⊤,∅}=> ⌜ ∃ γ2' μ2', NSteps γ2 μ2 δ2 s2 γ2' μ2' [env] (stm_val ty.unit tt) n ⌝.
    Proof.
      iIntros "(Hcred & Hmem & Hregs & Hwp)".
      iPoseProof (semWP2_lockstep Hsteps1 with "[$Hmem $Hregs $Hwp]") as "H".
      iMod "H" as "H".
      iApply (strip_step_fupdN_pure with "Hcred H").
    Qed.

    Lemma semWP2_preservation' `{sailGS2 Σ} n {s11 s21} {γ11 γ12 γ21 γ22} {μ11 μ12 μ21 μ22}
    {δ11 δ21}
    {Q}  :
    NSteps γ11 μ11 δ11 s11 γ12 μ12 [env] (stm_val ty.unit ()) n ->
      Steps γ21 μ21 δ21 s21 γ22 μ22 [env] (stm_val ty.unit ()) ->
    mem_inv2 _ μ11 μ21 ∗ regs_inv2 γ11 γ21 -∗
      semWP2 δ11 δ21 s11 s21 Q
    ={⊤,∅}=∗ |={∅}▷=>^(n) |={∅,⊤}=> mem_inv2 _ μ12 μ22 ∗ regs_inv2 γ12 γ22 ∗
                                      semWP2 [env] [env] (stm_val ty.unit ()) (stm_val ty.unit ()) Q.
  Proof.
    revert s11 s21 μ11 μ21 γ11 γ21 μ12 μ22 γ12 γ22 δ11 δ21 Q.
    induction n as [|n IH]=> s11 s21 μ11 μ21 γ11 γ21 μ12 μ22 γ12 γ22 δ11 δ21 Q /=.
    { intros steps1 steps2.
      inversion steps1. inversion steps2; subst; iIntros "(Hmem & Hregs)"; iIntros "Hwp".
      - iFrame.
        by iApply fupd_mask_subseteq.
      - rewrite {1}semWP2_unfold. cbn.
        destruct s21; cbn; iMod "Hwp"; auto.
        + iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iMod "Hclose".
          inversion H4.
    }
    iIntros (steps1 steps2) "(Hmem & Hregs)".
    iIntros " Hwp".
    inversion steps1 as [ | ? γ1 ? μ1 ? ? ? ? ? Hstep1 Hevaln1]. subst.
    inversion steps2; subst.
    { rewrite {1}semWP2_unfold. cbn. 
      destruct s11; cbn; iMod "Hwp"; auto.
      all: inversion Hstep1.
    }
    iPoseProof (semWP2_step Hstep1 H0 with "[$Hmem $Hregs $Hwp]") as "Hwp".
    iMod "Hwp". iModIntro. iMod "Hwp". do 2 iModIntro. do 2 iMod "Hwp".
    iDestruct "Hwp" as "(Hregs & Hmem & Hwp)".
    specialize (IH _ _ _ _ _ _ _ _ _ _ _ _ Q Hevaln1 H1).
    by iApply (IH with "[$Hmem $Hregs]").
  Qed.

      Lemma adequacy_gen_RiscVNStepsExitCond n exitCond {γ11 γ12 γ21 γ22} {μ11 μ12 μ21 μ22}
    (φ : Prop) :
    ⟨ γ11, μ11 ⟩ -( exitCond , n )->* ⟨ γ12, μ12 ⟩ ->
    ⟨ γ21, μ21 ⟩ -( exitCond , n )->* ⟨ γ22, μ22 ⟩ ->
    (forall `{sailGS2 Σ},
        mem_res2 μ11 μ21 ∗ own_regstore2 γ11 γ21 ⊢
          |={⊤}=> myWP2_loop (∃ v, pc ↦ᵣ SyncVal v ∗ ⌜exitCond v⌝)
        ∗ (mem_inv2 _ μ12 μ22 ={⊤,∅}=∗ ⌜φ⌝)
    )%I -> φ.
  Proof.
    intros Heval1 Heval2 Hwp.
    apply nsteps_to_lsteps in Heval1.
    destruct Heval1 as (l1 & Hl1 & Heval1).
    refine (uPred.pure_soundness _
              (step_fupdN_soundness_gen (Σ := sailΣ2) _ HasLc (list_sum_plus_one l1) (list_sum_plus_one l1) _)).
    iIntros (Hinv) "Hcred'".
    iMod (create_resources Hinv γ11 γ21 μ11 μ21) as (regs1 regs2 memG) "(Hmem & Rmem & Hregs & Rregs)".
    pose (sG := @SailGS2 sailΣ2 Hinv (SailRegGS2 (SailRegGS (@reg_pre_inG2_left _ (@subG_sailGpreS _ _)) regs1) (SailRegGS (@reg_pre_inG2_right _ (@subG_sailGpreS _ _)) regs2)) memG).
    specialize (Hwp _ sG).
    iPoseProof (Hwp with "[$Rmem $Rregs]") as "Hwp2".
    clear Hwp.
    iStopProof.
    revert Heval1 Heval2.
    revert γ11 μ11 γ21 μ21 n Hl1.
    induction l1; iIntros (γ11 μ11 γ21 μ21 n Hl1 Heval1 Heval2) "(Hcred & Hmem & Hregs & Hwp2)".
    - inversion Heval1. cbn in Hl1. subst.
      inversion Heval2. subst.
      iMod "Hwp2" as "[_ Hcont]".
      iMod ("Hcont" with "Hmem") as "%Hφ".
      cbn. done.
    - inversion Heval1 as [ | ? ? γ1 ? μ1 ? nEC1 Hstep1 Hevaln1]. clear Heval1. subst.
      inversion Heval2. subst. clear Heval2.
      rename H1 into Hstep2. rename H4 into Hevaln2. rename H0 into nEC2.
      specialize (IHl1 _ _ _ _ _ eq_refl Hevaln1 Hevaln2).
      rewrite fixpoint_myWP2_loop_eq.
      unfold myWP2_loop_fix.
      iMod "Hwp2" as "([H | Hwp2] & Hφ)".
      + iDestruct "H" as (v) "(Hpc & %Hec)".
        unfold reg_pointsTo2.
        iPoseProof (reg_valid2 with "[$Hregs] [$Hpc]") as "(%eq1 & _)".
        rewrite eq1 in nEC1. tauto.
      + iDestruct "Hwp2" as "(%v & Hpc & Hwand)".
        iPoseProof ("Hwand" with "Hpc") as "Hwp2".
        iPoseProof (semWP2_preservation' Hstep1 Hstep2 with "[$Hmem $Hregs]") as "Hwp".
        iSpecialize ("Hwp" with "Hwp2").
        iMod "Hwp".
        change (list_sum_plus_one (a :: l1)) with (a + 1 + list_sum_plus_one l1).
        iAssert (|={∅}▷=>^a |={∅}=>  |={∅}▷=> |={∅}▷=>^(list_sum_plus_one l1) ⌜φ⌝)%I with "[-]" as "H"; last first.
        { do 2 rewrite step_fupdN_add. destruct a. done. by iApply step_fupdN_S_fupd. }
        iApply (step_fupdN_wand with "Hwp").
        iIntros ">(Hmem & Hregs & Hwp)".
        rewrite semWP2_val.
        iMod "Hwp" as "Hwp".
        rewrite (into_sep_lc_add (a + 1) (list_sum_plus_one l1)).
        rewrite (into_sep_lc_add a 1).
        iDestruct "Hcred" as "[[Hcreda Hcred1] Hcredl]".
        iMod (lc_fupd_elim_later with "Hcred1 Hwp") as "Hwp".
        now iMod (IHl1 with "[$Hmem $Hcredl $Hregs $Hwp $Hφ]") as "IHl".        
  Qed.

    Lemma semWP2_preservation_strong `{sailGS2 Σ} n {s11 s21} {γ11 γ12 γ21} {μ11 μ12 μ21}
    {δ11 δ21}
    {Q}  :
    NSteps γ11 μ11 δ11 s11 γ12 μ12 [env] (stm_val ty.unit ()) n ->
    mem_inv2 _ μ11 μ21 ∗ regs_inv2 γ11 γ21 -∗
      semWP2 δ11 δ21 s11 s21 Q
    ={⊤,∅}=∗ |={∅}▷=>^(n) |={∅,⊤}=> ∃ γ22 μ22, mem_inv2 _ μ12 μ22 ∗ regs_inv2 γ12 γ22 ∗
                                      semWP2 [env] [env] (stm_val ty.unit ()) (stm_val ty.unit ()) Q ∗ ⌜ NSteps γ21 μ21 δ21 s21 γ22 μ22 [env] (stm_val ty.unit tt) n ⌝.
  Proof.
    revert s11 s21 μ11 μ21 γ11 γ21 μ12 γ12 δ11 δ21 Q.
    induction n as [|n IH]=> s11 s21 μ11 μ21 γ11 γ21 μ12 γ12 δ11 δ21 Q /=.
    { intros steps1.
      inversion steps1; subst. iIntros "(Hmem & Hregs)"; iIntros "Hwp".
      rewrite {1}semWP2_unfold. cbn.
        destruct s21; cbn; iMod "Hwp"; auto.
        + iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iMod "Hclose".
          iFrame.
          rewrite semWP2_val. env.destroy δ21.
          iModIntro. iSplitL; first iModIntro; destruct v; iFrame.
          iPureIntro. constructor.
    }
    iIntros (steps1) "(Hmem & Hregs)".
    iIntros " Hwp".
    inversion steps1 as [ | ? γ1 ? μ1 ? ? ? ? ? Hstep1 Hevaln1]. subst.
    destruct (stm_to_val s21) as [[v2|m2]|] eqn:Hs21.
    + rewrite semWP2_unfold. rewrite (stm_val_stuck Hstep1). rewrite Hs21. cbn.
      iMod "Hwp". done.
    + rewrite semWP2_unfold. rewrite (stm_val_stuck Hstep1). rewrite Hs21. cbn.
      iMod "Hwp". done.
    + destruct (progress s21) as [Hfinal21 | Hprog21].
      * destruct s21; cbn in *; try contradiction; congruence.
      * specialize (Hprog21 γ21 μ21 δ21) as (γ21' & μ21' & δ21' & s21' & Hstep2).
        iPoseProof (semWP2_step Hstep1 Hstep2 with "[$Hregs $Hmem $Hwp]") as "Hwp".
        iMod "Hwp". iModIntro. iMod "Hwp". do 2 iModIntro. do 2 iMod "Hwp".
        iDestruct "Hwp" as "(Hregs & Hmem & Hwp)".
        specialize (IH s2 s21' μ1 μ21' γ1 γ21' μ12 γ12 δ2 δ21' Q Hevaln1).
        iPoseProof (IH with "[$Hmem $Hregs]") as "IH".
        iMod ("IH" with "Hwp") as "IH".
        iModIntro.
        iApply (step_fupdN_mono with "IH").
        iIntros "H". iMod "H" as (γ22 μ22) "(Hmem & Hregs & Hwp & %HNSteps)".
        iModIntro. iExists γ22, μ22. iFrame. iPureIntro.
        exact (nstep_trans Hstep2 HNSteps).
  Qed.

  Lemma adequacy_gen_RiscVNStepsExitCond_strong n exitCond
      {γ11 γ12 γ21} {μ11 μ12 μ21}
      (φ : RegStore → Memory → Prop) :
      ⟨ γ11, μ11 ⟩ -( exitCond , n )->* ⟨ γ12, μ12 ⟩ ->
      (forall `{sailGS2 Σ},
          mem_res2 μ11 μ21 ∗ own_regstore2 γ11 γ21 ⊢
            |={⊤}=> myWP2_loop (∃ v, pc ↦ᵣ SyncVal v ∗ ⌜exitCond v⌝)
          ∗ (∀ γ22 μ22, mem_inv2 _ μ12 μ22 ={⊤,∅}=∗ ⌜φ γ22 μ22⌝)
      )%I ->
      ∃ γ22 μ22, ⟨ γ21, μ21 ⟩ -( exitCond , n )->* ⟨ γ22, μ22 ⟩ ∧ φ γ22 μ22.
  Proof.
    intros Heval1 Hwp.
    apply nsteps_to_lsteps in Heval1.
    destruct Heval1 as (l1 & Hl1 & Heval1).
    refine (uPred.pure_soundness _
              (step_fupdN_soundness_gen (Σ := sailΣ2) _ HasLc
                 (list_sum_plus_one l1) (list_sum_plus_one l1) _)).
    iIntros (Hinv) "Hcred'".
    iMod (create_resources Hinv γ11 γ21 μ11 μ21) as
      (regs1 regs2 memG) "(Hmem & Rmem & Hregs & Rregs)".
    pose (sG := @SailGS2 sailΣ2 Hinv
      (SailRegGS2
        (SailRegGS (@reg_pre_inG2_left _ (@subG_sailGpreS _ _)) regs1)
        (SailRegGS (@reg_pre_inG2_right _ (@subG_sailGpreS _ _)) regs2))
      memG).
    specialize (Hwp _ sG).
    iPoseProof (Hwp with "[$Rmem $Rregs]") as "Hwp2".
    clear Hwp.
    iStopProof.
    revert Heval1.
    revert γ11 μ11 γ21 μ21 n Hl1.
    induction l1;
      iIntros (γ11 μ11 γ21 μ21 n Hl1 Heval1)
              "(Hcred & Hmem & Hregs & Hwp2)".
    - inversion Heval1. cbn in Hl1. subst.
      iMod "Hwp2" as "[_ Hcont]".
      iMod ("Hcont" with "Hmem") as "%Hφ".
      cbn. iModIntro. iPureIntro. do 2 eexists.
      split; [by constructor | done].
    - inversion Heval1 as [ | ? ? γ1 ? μ1 ? nEC1 Hstep1 Hevaln1].
      clear Heval1. subst.
      rewrite fixpoint_myWP2_loop_eq.
      unfold myWP2_loop_fix.
      iMod "Hwp2" as "([H | Hwp2] & Hφ)".
      + iDestruct "H" as (v) "(Hpc & %Hec)".
        unfold reg_pointsTo2.
        iPoseProof (reg_valid2 with "[$Hregs] [$Hpc]") as "(%eq1 & _)".
        rewrite eq1 in nEC1. tauto.
      + iDestruct "Hwp2" as "(%v & Hpc & Hwand)".
        iPoseProof (reg_valid2_nd with "[$Hregs $Hpc]") as
          "(%eq1 & %eq2 & Hregs & Hpc)".
        have nEC2 : ~ exitCond (read_register γ21 pc).
        { cbn in eq1, eq2. rewrite eq2. rewrite <- eq1. exact nEC1. }
        iPoseProof ("Hwand" with "Hpc") as "Hwp2".
        iPoseProof (semWP2_preservation_strong Hstep1
          with "[$Hmem $Hregs]") as "Hwp".
        iMod ("Hwp" with "Hwp2") as "Hwp".
        change (list_sum_plus_one (a :: l1)) with
          (a + 1 + list_sum_plus_one l1).
        iAssert (|={∅}▷=>^a |={∅}=>
                 |={∅}▷=>
                 |={∅}▷=>^(list_sum_plus_one l1)
                 ⌜∃ γ22 μ22, RiscVNStepsWithExitCond exitCond
                    γ21 μ21 γ22 μ22 (length (a :: l1)) ∧ φ γ22 μ22⌝)%I
          with "[-]" as "H"; last first.
        { do 2 rewrite step_fupdN_add. destruct a. done.
          by iApply step_fupdN_S_fupd. }
        iApply (step_fupdN_wand with "Hwp").
        iIntros ">H".
        iDestruct "H" as (γ21' μ21') "(Hmem & Hregs & Hwp & %HNSteps)".
        rewrite semWP2_val. iMod "Hwp" as "Hwp".
        rewrite (into_sep_lc_add (a + 1) (list_sum_plus_one l1)).
        rewrite (into_sep_lc_add a 1).
        iDestruct "Hcred" as "[[Hcreda Hcred1] Hcredl]".
        iMod (lc_fupd_elim_later with "Hcred1 Hwp") as "Hwp".
        specialize (IHl1 γ1 μ1 γ21' μ21' _ eq_refl Hevaln1).
        iMod (IHl1 with "[$Hmem $Hcredl $Hregs $Hwp $Hφ]") as "IHl".
        { done. }
        iModIntro.
        iApply (step_fupdN_mono with "IHl").
        iPureIntro.
        intros (γ22 & μ22 & HNSteps2 & Hφ2).
        exists γ22, μ22. split; last done.
        exact (riscVNStepWithExitCond_trans nEC2
                 (nsteps_to_steps HNSteps) HNSteps2).
  Qed.

  Lemma constant_time_from_mem_res2_only_leak `{sailGS2 Σ} `{memGS2 Σ} {μ1 μ2 E} :
    leakage_trace μ1 = leakage_trace μ2 -> mem_res2_only_leak μ1 μ2 ⊢ |={E}=> interp_inv_constant_time.
  Proof.
    iIntros (eq_leak) "Hmem".
    unfold interp_inv_constant_time.
    iApply (inv_alloc constant_time_inv_ns E (∃ t : LeakageTrace, trace.tr_frag trace.trace_name t ∗ trace.tr_frag trace.trace_name t) with "[Hmem]").
    iModIntro.
    unfold mem_res2_only_leak, IrisInstance.RiscvPmpIrisAdeqParameters.mem_res_only_leak.
    rewrite eq_leak.
    iFrame.
  Qed.

Section AdequacyTools.

  Context {Σ} {GS : sailGS2 Σ}.
  Lemma regPstsTo_sync_is_nonsync `{sailGS2 Σ} σ r (v : Val σ) : r ↦ᵣ NonSyncVal v v ⊣⊢ r ↦ᵣ SyncVal v.
  Proof.
    unfold reg_pointsTo2. auto.
  Qed.

  Lemma interp_pstsTo_sync_is_nonsync `{sailGS2 Σ} r v : interp_ptsto r (NonSyncVal v v) ∗-∗ interp_ptsto r (SyncVal v).
  Proof.
    unfold interp_ptsto. auto.
  Qed.

  (* Word-level analog of regPstsTo_sync_is_nonsync *)
  Lemma ptstomem_sync_is_nonsync `{sailGS2 Σ} (a w : Val ty_word) :
    interp_ptstomem (width := 4) (SyncVal a) (NonSyncVal w w) ⊣⊢
    interp_ptstomem (width := 4) (SyncVal a) (SyncVal w).
  Proof. unfold interp_ptstomem. auto. Qed.

  Lemma intro_ptstomem_word `{sailGS2 Σ} v0 v1 v2 v3 (a : Val ty_word) :
    @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_left Σ (@sailGS2_memGS Σ H))) (bv.of_Z (0 + bv.unsigned a)) (DfracOwn 1) v0 ∗
      @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_left Σ (@sailGS2_memGS Σ H))) (bv.of_Z (1 + bv.unsigned a)) (DfracOwn 1) v1 ∗
      @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_left Σ (@sailGS2_memGS Σ H))) (bv.of_Z (2 + bv.unsigned a)) (DfracOwn 1) v2 ∗
      @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_left Σ (@sailGS2_memGS Σ H))) (bv.of_Z (3 + bv.unsigned a)) (DfracOwn 1) v3 ∗
      @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_right Σ (@sailGS2_memGS Σ H))) (bv.of_Z (0 + bv.unsigned a)) (DfracOwn 1) v0 ∗
      @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_right Σ (@sailGS2_memGS Σ H))) (bv.of_Z (1 + bv.unsigned a)) (DfracOwn 1) v1 ∗
      @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_right Σ (@sailGS2_memGS Σ H))) (bv.of_Z (2 + bv.unsigned a)) (DfracOwn 1) v2 ∗
      @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_right Σ (@sailGS2_memGS Σ H))) (bv.of_Z (3 + bv.unsigned a)) (DfracOwn 1) v3⊢
      interp_ptstomem (width := 4) (SyncVal a) (SyncVal (bv.app v0 (bv.app v1 (bv.app v2 (bv.app v3 bv.nil))))).
  Proof.
    iIntros "(Hmem1a & Hmem1a1 & Hmem1a2 & Hmem1a3 & Hmem2a & Hmem2a1 & Hmem2a2 & Hmem2a3)".
    unfold interp_ptstomem. unfold IrisInstance.RiscvPmpIrisInstance.interp_ptstomem.
    rewrite ?bv.appView_app.
    replace (@bv.of_Z xlenbits (0 + bv.unsigned a)%Z) with a by now rewrite bv.of_Z_unsigned.
    replace (@bv.of_Z xlenbits (1 + bv.unsigned a)%Z) with (bv.add bv.one a) by now rewrite <-bv.of_Z_add, bv.of_Z_unsigned.
    replace (@bv.of_Z xlenbits (2 + bv.unsigned a)%Z) with (bv.add bv.one (bv.add bv.one a)).
    replace (@bv.of_Z xlenbits (3 + bv.unsigned a)%Z) with (bv.add bv.one (bv.add bv.one (bv.add bv.one a))).
    cbn.
    unfold IrisInstance.RiscvPmpIrisInstance.interp_ptsto.
    iFrame.
    rewrite ?bv.add_assoc.
    change (bv.add _ bv.one) with (@bv.of_Z xlenbits 3).
    now rewrite <-bv.of_Z_add, bv.of_Z_unsigned.
    rewrite ?bv.add_assoc.
    now rewrite <-bv.of_Z_add, bv.of_Z_unsigned.
  Qed.

  Lemma intro_ptstomem_word_nonsync `{sailGS2 Σ}
      v0l v1l v2l v3l v0r v1r v2r v3r (a : Val ty_word) :
    @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_left Σ (@sailGS2_memGS Σ H)))
        (bv.of_Z (0 + bv.unsigned a)) (DfracOwn 1) v0l ∗
    @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_left Σ (@sailGS2_memGS Σ H)))
        (bv.of_Z (1 + bv.unsigned a)) (DfracOwn 1) v1l ∗
    @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_left Σ (@sailGS2_memGS Σ H)))
        (bv.of_Z (2 + bv.unsigned a)) (DfracOwn 1) v2l ∗
    @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_left Σ (@sailGS2_memGS Σ H)))
        (bv.of_Z (3 + bv.unsigned a)) (DfracOwn 1) v3l ∗
    @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_right Σ (@sailGS2_memGS Σ H)))
        (bv.of_Z (0 + bv.unsigned a)) (DfracOwn 1) v0r ∗
    @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_right Σ (@sailGS2_memGS Σ H)))
        (bv.of_Z (1 + bv.unsigned a)) (DfracOwn 1) v1r ∗
    @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_right Σ (@sailGS2_memGS Σ H)))
        (bv.of_Z (2 + bv.unsigned a)) (DfracOwn 1) v2r ∗
    @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_right Σ (@sailGS2_memGS Σ H)))
        (bv.of_Z (3 + bv.unsigned a)) (DfracOwn 1) v3r ⊢
    interp_ptstomem (width := 4) (SyncVal a)
      (NonSyncVal (bv.app v0l (bv.app v1l (bv.app v2l (bv.app v3l bv.nil))))
                  (bv.app v0r (bv.app v1r (bv.app v2r (bv.app v3r bv.nil))))).
  Proof.
    iIntros "(Hl0 & Hl1 & Hl2 & Hl3 & Hr0 & Hr1 & Hr2 & Hr3)".
    unfold interp_ptstomem. unfold IrisInstance.RiscvPmpIrisInstance.interp_ptstomem.
    rewrite ?bv.appView_app.
    replace (@bv.of_Z xlenbits (0 + bv.unsigned a)%Z) with a
      by now rewrite bv.of_Z_unsigned.
    replace (@bv.of_Z xlenbits (1 + bv.unsigned a)%Z) with (bv.add bv.one a)
      by now rewrite <-bv.of_Z_add, bv.of_Z_unsigned.
    replace (@bv.of_Z xlenbits (2 + bv.unsigned a)%Z) with
      (bv.add bv.one (bv.add bv.one a)).
    replace (@bv.of_Z xlenbits (3 + bv.unsigned a)%Z) with
      (bv.add bv.one (bv.add bv.one (bv.add bv.one a))).
    cbn.
    unfold IrisInstance.RiscvPmpIrisInstance.interp_ptsto.
    iFrame "Hl0 Hl1 Hl2 Hl3 Hr0 Hr1 Hr2 Hr3".
    rewrite ?bv.add_assoc.
    change (bv.add _ bv.one) with (@bv.of_Z xlenbits 3).
    now rewrite <-bv.of_Z_add, bv.of_Z_unsigned.
    rewrite ?bv.add_assoc.
    now rewrite <-bv.of_Z_add, bv.of_Z_unsigned.
  Qed.

  Lemma intro_ptstomem_word2 `{sailGS2 Σ} {μ1 μ2 : Memory} {a : Val ty_word} {v : Val ty_word} :
    mem_has_word μ1 a v ->
    mem_has_word μ2 a v ->
    ([∗ list] a' ∈ bv.seqBv a 4,
      @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_left Σ (@sailGS2_memGS Σ H))) a' (DfracOwn 1) (memory_ram μ1 a')) ∗
      ([∗ list] a' ∈ bv.seqBv a 4,
        @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_right Σ (@sailGS2_memGS Σ H))) a' (DfracOwn 1) (memory_ram μ2 a'))
      ⊢ interp_ptstomem (SyncVal a) (SyncVal v).
  Proof.
    iIntros (Hmhw1 Hmhw2) "[Hmem1 Hmem2]".
    destruct Hmhw1 as (v01 & v11 & v21 & v31 & Heqμ1 & Heqv1).
    destruct Hmhw2 as (v02 & v12 & v22 & v32 & Heqμ2 & Heqv2).
    unfold bv.seqBv, seqZ. change (seq 0 ?x) with [0;1;2;3].
    cbn -[bv.add interp_ptstomem word].
    iDestruct "Hmem1" as "(Hmem1a & Hmem1a1 & Hmem1a2 & Hmem1a3 & _)".
    iDestruct "Hmem2" as "(Hmem2a & Hmem2a1 & Hmem2a2 & Hmem2a3 & _)".
    rewrite <- Heqv1 in Heqv2.
    do 4 (apply bv.app_inj in Heqv2; destruct Heqv2 as [? Heqv2]). subst.
    rewrite <- Heqμ1 in Heqμ2.
    inversion Heqμ1; inversion Heqμ2.
    rewrite H5 H6 H7 H8.
    now iApply (intro_ptstomem_word with "[$Hmem1a $Hmem1a1 $Hmem1a2 $Hmem1a3 $Hmem2a $Hmem2a1 $Hmem2a2 $Hmem2a3]").
  Qed.

  Lemma intro_ptstomem_word2_nonsync `{sailGS2 Σ} {μ1 μ2 : Memory}
      {a : Val ty_word} {w1 w2 : Val ty_word} :
    mem_has_word μ1 a w1 →
    mem_has_word μ2 a w2 →
    ([∗ list] a' ∈ bv.seqBv a 4,
      @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_left Σ (@sailGS2_memGS Σ H))) a'
        (DfracOwn 1) (memory_ram μ1 a')) ∗
    ([∗ list] a' ∈ bv.seqBv a 4,
      @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_right Σ (@sailGS2_memGS Σ H))) a'
        (DfracOwn 1) (memory_ram μ2 a'))
    ⊢ interp_ptstomem (width := 4) (SyncVal a) (NonSyncVal w1 w2).
  Proof.
    iIntros (Hmhw1 Hmhw2) "[Hmem1 Hmem2]".
    destruct Hmhw1 as (v01 & v11 & v21 & v31 & Heqμ1 & Heqv1).
    destruct Hmhw2 as (v02 & v12 & v22 & v32 & Heqμ2 & Heqv2).
    unfold bv.seqBv, seqZ. change (seq 0 ?x) with [0;1;2;3].
    cbn -[bv.add interp_ptstomem word].
    iDestruct "Hmem1" as "(Hmem1a & Hmem1a1 & Hmem1a2 & Hmem1a3 & _)".
    iDestruct "Hmem2" as "(Hmem2a & Hmem2a1 & Hmem2a2 & Hmem2a3 & _)".
    inversion Heqμ1. subst v01 v11 v21 v31.
    inversion Heqμ2. subst v02 v12 v22 v32.
    rewrite <- Heqv1, <- Heqv2.
    iApply (intro_ptstomem_word_nonsync with
      "[$Hmem1a $Hmem1a1 $Hmem1a2 $Hmem1a3 $Hmem2a $Hmem2a1 $Hmem2a2 $Hmem2a3]").
  Qed.

  Lemma intro_ptsto_instr `{sailGS2 Σ} {μ1 μ2 : Memory} {a : Val ty_word} w {instr : AST} :
    mem_has_instr μ1 a w instr ->
    mem_has_instr μ2 a w instr ->   
    ([∗ list] a' ∈ bv.seqBv a 4,
      @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_left Σ (@sailGS2_memGS Σ H))) a' (DfracOwn 1) (memory_ram μ1 a')) ∗
      ([∗ list] a' ∈ bv.seqBv a 4,
        @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_right Σ (@sailGS2_memGS Σ H))) a' (DfracOwn 1) (memory_ram μ2 a'))
      ⊢ interp_ptsto_instr (SyncVal a) (SyncVal w) (SyncVal instr).
  Proof.
    iIntros ((Hmhw1 & Heq1) (Hmhw2 & Heq2)) "[Hmem1 Hmem2]".
    (* No `iExists (SyncVal w)` any more: interp_ptsto_instr no longer hides the
       word behind an ∃, it takes it as an argument.  The third conjunct
       (secLeak w) is immediate — a SyncVal word is the same in both worlds. *)
    iSplitL.
    { iApply (intro_ptstomem_word2 Hmhw1 Hmhw2). iFrame. }
    iSplit; cbn; [by rewrite Heq1|done].
  Qed.

  Lemma intro_ptsto_instrs `{sailGS2 Σ} {μ1 μ2 : Memory} {a : Val ty_word} ws {instrs : list AST} :
    (4 * N.of_nat (length instrs) + bv.bin a < lenAddr)%N  ->
      mem_has_instrs μ1 a ws instrs ->
      mem_has_instrs μ2 a ws instrs ->
      ([∗ list] a' ∈ bv.seqBv a (4 * N.of_nat (length instrs)),
        @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_left Σ (@sailGS2_memGS Σ H))) a' (DfracOwn 1) (memory_ram μ1 a')) ∗
        ([∗ list] a' ∈ bv.seqBv a (4 * N.of_nat (length instrs)),
          @pointsto _ _ _ _ _ (@mc_ghGS Σ (@memGS2_memGS_right Σ (@sailGS2_memGS Σ H))) a' (DfracOwn 1) (memory_ram μ2 a'))
        ⊢ Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs_w
            (words_of_list a ws) (instrs_of_list a instrs).
  Proof.
    assert (word > 0) by now compute; Lia.lia.
    iIntros (Hrep Hmeminstrs1 Hmeminstrs2) "[Hmem1 Hmem2]".
    iInduction instrs as [|instr instrs] "IH" forall (a ws Hrep Hmeminstrs1 Hmeminstrs2).
    - (* instrs_of_list a [] = ∅, so ptsto_instrs_w is emp. *)
      unfold Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs_w.
      cbn [instrs_of_list]. rewrite big_sepM_empty. done.
    - rewrite Nat2N.inj_succ in Hrep.
      fold (length instrs) in Hrep.
      replace (4 * N.of_nat (length (instr :: instrs)))%N with (4 + 4 * N.of_nat (length instrs))%N by (cbn; lia).
      rewrite bv.seqBv_app; try (cbn -[N.of_nat N.mul] in *; Lia.lia).
      rewrite big_opL_app.
      (* Name the head word explicitly: it is now needed by the word map. *)
      destruct ws as [|wd ws'].
      { inversion Hmeminstrs1; inversion Hmeminstrs2. }
      destruct Hmeminstrs1 as [Hinstr1 Hmeminstrs1].
      destruct Hmeminstrs2 as [Hinstr2 Hmeminstrs2].
      (* mem_has_instrs states the tail at [bv.of_N 4 + a]; the seqBv/gmap
         tail is at [a + bv.of_N 4].  Commute so the IH's mem hypotheses
         line up. *)
      rewrite (bv.add_comm (x := bv.of_N 4) (y := a)) in Hmeminstrs1, Hmeminstrs2.
      iDestruct "Hmem1" as "[Hmem1a Hmem1a4]".
      iDestruct "Hmem2" as "[Hmem2a Hmem2a4]".
      (* Peel the head instruction off the gmap.  The tail's keys start at
         a+4 (matching bv.seqBv_app), and instrs_of_list_fresh shows a is
         not among them (no 2^xlenbits wraparound under the lenAddr bound). *)
      assert (Hfresh : instrs_of_list (bv.add a (bv.of_N 4)) instrs !! a = None).
      (* `_` for the element type: instrs_of_list(_fresh) became POLYMORPHIC in
         it (Tables.v, AnnotInstr migration), so an @-application's positions
         shifted by one.  Nothing semantic changed here — memory still holds
         AST, and the element type is simply inferred. *)
      { apply (@instrs_of_list_fresh _ instrs a 4); [lia|].
        unfold lenAddr in Hrep. change (2 ^ 10)%N with 1024%N in Hrep.
        (* lia chokes on the 2^32 literal, so bound to <1024 then transit. *)
        assert (Hb : (bv.bin a + 4 + 4 * N.of_nat (length instrs) < 1024)%N) by lia.
        eapply N.lt_trans; [exact Hb|]. reflexivity. }
      unfold Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs_w.
      cbn [instrs_of_list words_of_list].
      rewrite (big_sepM_insert
                 (fun a0 i0 => interp_ptsto_instr (SyncVal a0)
                                 (SyncVal (words_of_list a (wd :: ws') a0)) (SyncVal i0))
                 (instrs_of_list (bv.add a (bv.of_N 4)) instrs) a instr Hfresh).
      iSplitL "Hmem1a Hmem2a".
      + rewrite words_of_list_here.
        iApply (intro_ptsto_instr with "[$Hmem1a $Hmem2a]"); eauto.
      + (* The tail's word function is the head's, which differs only at the head
           address — and that address is fresh for the tail's instruction map. *)
        assert (Hagree : forall a0 i0,
                   instrs_of_list (bv.add a (bv.of_N 4)) instrs !! a0 = Some i0 ->
                   words_of_list (bv.add a (bv.of_N 4)) ws' a0
                   = words_of_list a (wd :: ws') a0).
        { intros a0 i0 Hlk0.
          symmetry.
          apply words_of_list_there.
          intros Heq. subst a0. rewrite Hfresh in Hlk0. discriminate. }
        iApply (Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs_w_agree
                  _ _ _ Hagree).
        iApply ("IH" with "[%] [% //] [% //] [$Hmem1a4] [$Hmem2a4]").
        rewrite bv.bin_add_small;
          cbn -[N.mul] in *.
        now Lia.lia.
        unfold lenAddr in Hrep. lia.
  Qed.

  Lemma instrsMemory `{sailGS2 Σ} {μ1 μ2 : Memory} (start : N) ws instrs :
    (start + 4 * N.of_nat (length instrs) < lenAddr)%N ->
    mem_has_instrs μ1 (bv.of_N start) ws instrs ->
    mem_has_instrs μ2 (bv.of_N start) ws instrs ->
    @mem_res2_without_leak _ sailGS2_memGS μ1 μ2 ⊢ |={⊤}=>
      Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs (instrs_of_list (bv.of_N start) instrs).
  Proof.
    iIntros (Hrep Hinit1 Hinit2) "Hmem".
    unfold mem_res2_without_leak, IrisInstance.RiscvPmpIrisAdeqParameters.mem_res_without_leak.
    replace liveAddrs with
      (bv.seqBv (n := 32) (bv.of_N minAddr) start ++
         bv.seqBv (n := 32) (bv.of_N start) (4 * N.of_nat (length instrs)) ++
         bv.seqBv (n := 32) (bv.of_N start + bv.of_N (4 * N.of_nat (length instrs)))
                  (lenAddr - start - 4 * N.of_nat (length instrs))).
    2: {
      assert (Heq : (bv.of_N minAddr + bv.of_N start : bv 32)%bv = bv.of_N start).
      { rewrite bv.of_N_add. f_equal. }
      rewrite <- Heq.
      rewrite <- !bv.seqBv_app.
      apply f_equal. lia.
    }
    iDestruct "Hmem" as "[[[Hbefore1 [Hinst1 Hrest1]] Htr1] [[Hbefore2 [Hinst2 Hrest2]] Htr2]]".
    iModIntro.
    (* ptsto_instrs is now ∃ words over the word-indexed form; the witness is
       the word list mem_has_instrs already supplies. *)
    iExists (words_of_list (bv.of_N start) ws).
    iApply (intro_ptsto_instrs (μ1 := μ1) (μ2 := μ2)); eauto.
    { match goal with
      | |- (_ + bv.bin ?a < _)%N =>
          assert (Hb : (bv.bin a <= start)%N) by apply bv.bin_of_N_decr
      end.
      (* The gmap import activates a Zify rewrite of bv.bin (bv.of_N _) into
         _ mod 2^word; the huge modulus makes lia's certificate search fail,
         so make the atom opaque first. *)
      set (B := bv.bin (bv.of_N start)) in *; clearbody B. lia. }
    (* `all:` rather than a bare `auto`: the explicit iModIntro above leaves one
       fewer goal than the implicit modality handling did. *)
    iFrame. all: auto.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Public memory Iris predicates                                       *)
  (* ------------------------------------------------------------------ *)

  (* All data specs as NonSyncVal regardless of public flag.
     Used as the intermediate form produced by extracting raw bytes. *)
  Definition interp_mem_with_memory `{sailGS2 Σ}
      (μ1 μ2 : Memory) (specs : list mem_spec) : iProp Σ :=
    [∗ list] spec ∈ specs,
      let '(a, _) := spec in
      interp_ptstomem (width := 4) (SyncVal a)
        (NonSyncVal (get_word μ1 a) (get_word μ2 a)).

  (* Public specs use SyncVal (words must agree); private specs use NonSyncVal *)
  Definition interp_mem_with_public_memory `{sailGS2 Σ}
      (μ1 μ2 : Memory) (specs : list mem_spec) : iProp Σ :=
    [∗ list] spec ∈ specs,
      let '(a, pub) := (spec : mem_spec) in
      if pub
      then interp_ptstomem (width := 4) (SyncVal a) (SyncVal (get_word μ1 a))
      else interp_ptstomem (width := 4) (SyncVal a)
             (NonSyncVal (get_word μ1 a) (get_word μ2 a)).

  (* get_word always witnesses mem_has_word (the four bytes at a..a+3 assemble
     to exactly get_word μ a).  Proof requires unfolding bv.seqBv arithmetic. *)
  Lemma get_word_is_mem_has_word (μ : Memory) (a : Val ty_word) :
    mem_has_word μ a (get_word μ a).
  Proof.
    exists (memory_ram μ a), (memory_ram μ (bv.add bv.one a)),
           (memory_ram μ (bv.add (bv.of_N 2) a)), (memory_ram μ (bv.add (bv.of_N 3) a)).
    split; [| unfold get_word; reflexivity].
    enough (bv.seqBv a 4 = [a; bv.add bv.one a; bv.add (bv.of_N 2) a; bv.add (bv.of_N 3) a])
      as Hseq by now rewrite Hseq.
    unfold bv.seqBv, seqZ.
    change (Z.to_nat (Z.of_N 4)) with 4%nat.
    cbn [seq fmap list_fmap List.map].
    repeat f_equal.
    all: rewrite <- bv.of_Z_add, bv.of_Z_unsigned.
    - apply bv.add_zero_l.
    - change (1%nat : Z) with (Z.of_N 1). now rewrite bv.of_Z_N.
    - change (2%nat : Z) with (Z.of_N 2). now rewrite bv.of_Z_N.
    - change (3%nat : Z) with (Z.of_N 3). now rewrite bv.of_Z_N.
  Qed.

  (* Assembles interp_mem_with_memory from raw byte ownership, by induction
     over the spec list.  Direct analog of intro_ptsto_instrs for data memory. *)
  Lemma intro_mem_with_memory `{sailGS2 Σ} {μ1 μ2 : Memory} (a : bv word)
      (specs : list mem_spec) :
    (∀ i spec, specs !! i = Some spec →
      spec.1 = bv.add a (bv.of_N (4 * N.of_nat i))) →
    ([∗ list] a' ∈ bv.seqBv a (4 * N.of_nat (length specs)),
      @pointsto _ _ _ _ _
        (@mc_ghGS Σ (@memGS2_memGS_left Σ (@sailGS2_memGS Σ H))) a'
        (DfracOwn 1) (memory_ram μ1 a')) ∗
    ([∗ list] a' ∈ bv.seqBv a (4 * N.of_nat (length specs)),
      @pointsto _ _ _ _ _
        (@mc_ghGS Σ (@memGS2_memGS_right Σ (@sailGS2_memGS Σ H))) a'
        (DfracOwn 1) (memory_ram μ2 a'))
    ⊢ interp_mem_with_memory μ1 μ2 specs.
  Proof.
    iIntros (Haddrs) "[H1 H2]".
    iInduction specs as [| spec specs] "IH" forall (a Haddrs).
    { done. }
    destruct spec as [a_s pub].
    assert (Hlen : (4 * N.of_nat (length ((a_s, pub) :: specs)) =
                   4 + 4 * N.of_nat (length specs))%N).
    { cbn [length]. rewrite Nat2N.inj_succ. rewrite N.mul_succ_r. apply N.add_comm. }
    rewrite Hlen.
    rewrite (bv.seqBv_app (n := 32) a 4).
    rewrite !big_opL_app.
    iDestruct "H1" as "[H1h H1t]".
    iDestruct "H2" as "[H2h H2t]".
    cbn [interp_mem_with_memory big_opL].
    iSplitL "H1h H2h".
    { have Ha_s := Haddrs 0 (a_s, pub) eq_refl.
      cbn in Ha_s. rewrite bv.add_zero_r in Ha_s. subst a_s.
      iApply (intro_ptstomem_word2_nonsync (get_word_is_mem_has_word μ1 a)
                                            (get_word_is_mem_has_word μ2 a)).
      iFrame. }
    iApply ("IH" $! (a + bv.of_N 4)%bv with "[%] H1t H2t").
    intros i spec Hlook.
    pose proof (Haddrs (S i) spec Hlook) as Hsi.
    assert (H4 : (4 * N.of_nat (S i) = 4 + 4 * N.of_nat i)%N).
    { rewrite Nat2N.inj_succ. rewrite N.mul_succ_r. apply N.add_comm. }
    rewrite H4 in Hsi. rewrite <- bv.of_N_add in Hsi. rewrite bv.add_assoc in Hsi.
    exact Hsi.
  Qed.

  (* Extract both instruction memory AND data memory from mem_res2_without_leak.
     Data words must occupy the 4*|data_specs| bytes immediately following
     the instruction region (contiguous layout: instructions at [0, 4*n),
     data at [4*n, 4*n + 4*m)).

     The result is the "all-NonSyncVal" form interp_mem_with_memory.
     Use something_memory (outside AdequacyTools) to convert to the
     interp_mem_with_public_memory form.

     Uses intro_mem_with_memory (proved by induction over data_specs) for
     the data region, after a two-way bv.seqBv_app split. *)
  Lemma instrsAndDataMemory `{sailGS2 Σ} {μ1 μ2 : Memory} (start : N) ws_instrs data_specs instrs :
    (start + 4 * N.of_nat (length instrs) +
     4 * N.of_nat (length data_specs) < lenAddr)%N →
    mem_has_instrs μ1 (bv.of_N start) ws_instrs instrs →
    mem_has_instrs μ2 (bv.of_N start) ws_instrs instrs →
    (* data words are at start + 4*|instrs|, start + 4*|instrs| + 4, … *)
    (∀ i spec, data_specs !! i = Some spec →
      spec.1 = bv.of_N (start + 4 * N.of_nat (length instrs)
                         + 4 * N.of_nat i)) →
    @mem_res2_without_leak _ sailGS2_memGS μ1 μ2 ⊢ |={⊤}=>
      Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs (instrs_of_list (bv.of_N start) instrs) ∗
      interp_mem_with_memory μ1 μ2 data_specs.
  Proof.
    iIntros (Hlen HMem1 HMem2 HDataAddrs) "Hmem".
    unfold mem_res2_without_leak,
      IrisInstance.RiscvPmpIrisAdeqParameters.mem_res_without_leak.
    replace liveAddrs with
      (bv.seqBv (n := 32) (bv.of_N minAddr) start ++
       bv.seqBv (n := 32) (bv.of_N start) (4 * N.of_nat (length instrs)) ++
       bv.seqBv (n := 32) (bv.of_N start + bv.of_N (4 * N.of_nat (length instrs)))
                (4 * N.of_nat (length data_specs)) ++
       bv.seqBv (n := 32)
                (bv.of_N start + bv.of_N (4 * N.of_nat (length instrs))
                  + bv.of_N (4 * N.of_nat (length data_specs)))%bv
                (lenAddr - start - 4 * N.of_nat (length instrs)
                  - 4 * N.of_nat (length data_specs))).
    2: {
      assert (Heq : (bv.of_N minAddr + bv.of_N start : bv 32)%bv = bv.of_N start).
      { rewrite bv.of_N_add. f_equal. }
      rewrite <- Heq.
      rewrite <- !bv.seqBv_app.
      apply f_equal. lia.
    }
    iDestruct "Hmem" as
      "[[[Hbefore1 [Hinst1 [Hdata1 Hrest1]]] Htr1]
        [[Hbefore2 [Hinst2 [Hdata2 Hrest2]]] Htr2]]".
    iModIntro.
    iSplitL "Hinst1 Hinst2".
    - iExists (words_of_list (bv.of_N start) ws_instrs).
      iApply (intro_ptsto_instrs (μ1 := μ1) (μ2 := μ2)); eauto.
      { match goal with
        | |- (_ + bv.bin ?a < _)%N =>
            assert (Hb : (bv.bin a <= start)%N) by apply bv.bin_of_N_decr
        end.
        set (B := bv.bin (bv.of_N start)) in *; clearbody B. lia. }
      iFrame.
    - iApply (intro_mem_with_memory
        (a := (bv.of_N start + bv.of_N (4 * N.of_nat (length instrs)))%bv)).
      { intros i spec Hlook.
        have HDA := HDataAddrs i spec Hlook. rewrite HDA.
        rewrite !bv.of_N_add; f_equal; lia. }
      iFrame "Hdata1 Hdata2".
  Qed.

  (* Definition pcOutOfInstrs_WP2_loop `{sailGS2 Σ} instrs := *)
  (*   myWP2_loop *)
  (*   (∃ γ0 γ3 : RegStore, own_regstore2 γ0 γ3 ∗ *)
  (*                          ⌜pcOutOfInstrs (bv.of_N init_addr) instrs (read_register γ0 pc) *)
  (*                        ∨ pcOutOfInstrs (bv.of_N init_addr) instrs (read_register γ3 pc)⌝)%I. *)

  Definition pcOutOfInstrs_WP2_loop `{sailGS2 Σ} instrs :=
    myWP2_loop
      (∃ a, pc ↦ᵣ a ∗
                             ⌜pcOutOfInstrs (bv.of_N init_addr) instrs (ty.projLeft a)
                           ∨ pcOutOfInstrs (bv.of_N init_addr) instrs (ty.projRight a)⌝)%I.

  Definition exitCond_WP2_loop `{sailGS2 Σ} (exitCond : bv xlenbits -> bool) : iProp Σ :=
    myWP2_loop (∃ v, pc ↦ᵣ SyncVal v ∗ ⌜exitCond v⌝)%I.

  Definition pcBehindInstrs_WP2_loop `{sailGS2 Σ} start instrs :=
    myWP2_loop
      (∃ γ0 γ3 : RegStore, own_regstore2 γ0 γ3 ∗
                             ⌜pcBehindInstrs start instrs (read_register γ0 pc)
                           ∨ pcBehindInstrs start instrs (read_register γ3 pc)⌝)%I.

    Import iris.base_logic.lib.iprop iris.proofmode.tactics.
    Import RiscvPmpIrisInstanceWithContracts.
    Import ProgramLogic.
    Import CHeapSpec CHeapSpec.notations.



    (* anp: the current nextpc value.  The PRE holds it exactly (it used to be
       `∃ v, nextpc ↦ᵣ v`, discarding what the epilogue had just established),
       because cexec_cfg_addr now takes it as an argument and the recursive call
       passes `an an` — so the specific value has to match.  The POST below
       keeps its `∃ v`: that side is the shared continuation Hk, identical in
       the IH and in the goal, so it needs no change. *)
    (* words: the per-address instruction words, FIXED for the whole loop.  The
       loop invariant carries the word-INDEXED ownership ptsto_instrs_w, not the
       ∃-form ptsto_instrs, because cexec_cfg_addr looks the word up in this
       specific gmap at every step.  The caller destructs the ∃ once, before
       entering the loop. *)

    (* Chunk GC weakening: sound_exec_cfg_addr_myWP2 to account for the cchunk_gc bind
       introduced in Phase B of the GC refinement.

       interpret_scheap is a fold_right of (_ ∗ _) over the chunk list
       (Chunks.v), so the kept case frames the head and recurses, and the
       dropped case simply DISCARDS the head conjunct — the `_` in
       `iIntros "[_ H]"`.  That step needs the ambient BI to be AFFINE,
       which iProp Σ is but Chunks.v's abstract HProp is not; that is why
       this lemma has to live here and cannot be pushed down next to
       interpret_scheap itself. *)
    Lemma interpret_scheap_gc_heap (h : SCHeap) :
      interpret_scheap h ⊢ interpret_scheap (Katamaran.RiscvPmp.CFGVer.VerifierRel.cgc_heap h).
    Proof.
      induction h as [|c h IH]; cbn; [done|].
      unfold Katamaran.RiscvPmp.CFGVer.VerifierRel.cgc_heap in IH; cbn in IH.
      destruct (is_encodes_instr c); cbn;
        [iIntros "[_ H]" | iIntros "[Hc H]"; iFrame "Hc"]; iApply IH; iExact "H".
    Qed.

    Lemma sound_exec_cfg_addr_myWP2
        {instrs} {words : bv xlenbits -> bv word} {exitCond fuel} (apc anp : RelVal ty_xlenbits)
        (ExitCondIprop : iProp Σ) Φ (h : SCHeap) :
      Katamaran.RiscvPmp.CFGVer.VerifierRel.cexec_cfg_addr instrs words exitCond fuel apc anp Φ h →
      interpret_scheap h ∗ pc ↦ᵣ apc ∗ nextpc ↦ᵣ anp ∗
        (* THE BOUNDARY: the executor's map is AnnotInstr-valued, MEMORY is
           AST-valued — memory holds instructions, not annotations.  This is
           the one place the two views meet, and the projection lives here
           rather than in ptsto_instrs (which the trusted statements name). *)
        Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs_w words
          (ai_instr <$> instrs) ⊢
      (∀ an,
         ⌜match an with SyncVal v => exitCond v = true | NonSyncVal _ _ => False end⌝ ∗
         pc ↦ᵣ an ∗ (∃ v, nextpc ↦ᵣ v) ∗
           Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs_w words
             (ai_instr <$> instrs) ∗
         (∃ h', interpret_scheap h' ∧ ⌜Φ an h'⌝) -∗ ExitCondIprop) -∗
      myWP2_loop ExitCondIprop.
    Proof.
      revert apc anp h.
      induction fuel as [|n' IH]; intros apc anp h Hexec.
      - cbn [Katamaran.RiscvPmp.CFGVer.VerifierRel.cexec_cfg_addr CHeapSpec.error] in Hexec.
        contradiction.
      - destruct apc as [v|v1 v2].
        + cbn [Katamaran.RiscvPmp.CFGVer.VerifierRel.cexec_cfg_addr ty.RVToOption
               CHeapSpec.angelic_binary] in Hexec.
          destruct Hexec as [Hexit | Hexec].
          * destruct (exitCond v) eqn:Hexit_eq.
            -- cbn [CHeapSpec.pure] in Hexit.
               iIntros "(Hh & Hpc & Hnpc & Hinstrs) Hk".
               iApply exitCondImpliesMyWP2_loop.
               iApply ("Hk" $! (SyncVal v)).
               iSplit. { iPureIntro. exact Hexit_eq. }
               iFrame. iPureIntro. exact Hexit.
            -- cbn [CHeapSpec.error] in Hexit. contradiction.
          * (* Execute branch: the instruction is looked up at address v
               directly (instrs !! v).  No alignment / base guard / index
               arithmetic: the gmap key IS the current PC. *)
            destruct (instrs !! v) as [i|] eqn:Hlk.
            ++ unfold bind, CHeapSpec.bind in Hexec.
               (* Phase 4 (chunk GC): Hexec now carries the extra cchunk_gc
                  bind cexec_cfg_addr's step inserts before cexec_instruction.
                  Absorb it first — cgc_binds_heap_fwd rewrites Hexec down
                  to the cexec_instruction call over cgc_heap h — then weaken
                  Hh to match via interpret_scheap_gc_heap (§4: sound because
                  iProp Σ is affine). *)
               apply Katamaran.RiscvPmp.CFGVer.VerifierRel.cgc_binds_heap_fwd in Hexec.
               (* Absorb the two ghost binds the same way, and for the same
                  reason: every ghost is concretely the identity right now, so
                  cexec_ghosts is `pure tt` and its binds collapse.  When
                  Phase 4 gives AnnotLemmaInvocation real semantics this stops
                  holding and genuine lemma soundness is needed here — see
                  cexec_ghosts_pure's own note. *)
               rewrite !Katamaran.RiscvPmp.CFGVer.VerifierRel.cexec_ghosts_pure in Hexec.
               cbn [CHeapSpec.bind CHeapSpec.pure] in Hexec.
               iIntros "(Hh & Hpc & Hnpc & Hinstrs) Hk".
               iDestruct (interpret_scheap_gc_heap h with "Hh") as "Hh".
               (* ptsto_instrs_lookup works on the PROJECTED (AST) map, so the
                  lookup fact has to be projected too: lookup_fmap turns
                  `instrs !! v = Some i` into `(ai_instr <$> instrs) !! v =
                  Some (ai_instr i)`, which is also exactly the instruction
                  cexec_cfg_addr passed to cexec_instruction. *)
               assert (Hlk' : (ai_instr <$> instrs) !! v = Some (ai_instr i))
                 by (rewrite lookup_fmap; rewrite Hlk; reflexivity).
               iPoseProof (Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs_lookup
                             words (ai_instr <$> instrs) v Hlk'
                 with "Hinstrs") as "[Hinstr Hframe]".
               rewrite {1}fixpoint_myWP2_loop_eq. unfold myWP2_loop_fix.
               iRight; iExists v; iSplitL "Hpc". { iExact "Hpc". }
               iIntros "Hpc_wd".
               iApply (semWP2_mono with "[Hh Hnpc Hpc_wd Hinstr]").
               { iApply (Katamaran.RiscvPmp.CFGVer.VerifierRel.sound_exec_instruction Hexec). iFrame. }
               iIntros ([v1|m1] δ1 [v2|m2] δ2); cbn.
               2-3: iIntros "(%δ' & _ & HF)"; auto.
               2: iIntros "_"; done.
               iIntros "(%δ' & eqδ' & %rv & eqrv & ([%an (Hnpc' & Hpc' & (%h' & Hh' & %Hcfg & _))] & Hinstr' & _))".
               iPoseProof ("Hframe" with "Hinstr'") as "Hinstrs'".
               iModIntro.
               iRevert "Hk".
               (* `an an`: the recursive call passes the new pc as both the pc
                  and the incoming nextpc, which is exactly what the epilogue
                  established (pc = nextpc = an).  Hnpc' is framed directly —
                  no `iExists`, since the PRE now names the value. *)
               iApply (IH an an h' Hcfg).
               iFrame "Hh' Hpc' Hinstrs' Hnpc'".
            ++ cbn [CHeapSpec.error] in Hexec. contradiction.
        + cbn [Katamaran.RiscvPmp.CFGVer.VerifierRel.cexec_cfg_addr ty.RVToOption
               CHeapSpec.error] in Hexec.
          contradiction.
    Qed.

    (* ---------------------------------------------------------------- *)
    (* Table-based soundness bridge, built on sound_exec_cfg_addr_myWP2   *)
    (* above (the shared gmap-based executor-loop soundness step) but     *)
    (* starting from the table VC (scfg_verification_condition over      *)
    (* address-term tables) — the only VC any CFGVer example builds, via  *)
    (* Contracts.v's CFG_VC_triple.                                       *)
    (* The Option B guard in cexec_triple_addr surfaces — after      *)
    (* wp_demonic_ctx and specialization to ι — as an                    *)
    (* `itable_rel ∧ etable_rel →` premise, discharged here by the   *)
    (* caller-supplied faithfulness facts at ι.                          *)
    (* ---------------------------------------------------------------- *)
    Lemma sound_cexec_triple_addr_myWP2 {Γ : LCtx} {pre post instrs exitCond fuel}
        (* the ALIASES, never a spelled-out tuple.  This is now the SIXTH
           signature caught with a literal `list (Term _ ty_xlenbits * AST)` in
           it (five in VerifierRel.v), and every one of them silently failed to
           track BOTH table columns added since — the word column and then
           AnnotInstr.  The type error always surfaces far from the cause. *)
        {tbl : Katamaran.RiscvPmp.CFGVer.Verifier.SInstrTable (wlctx Γ)}
        {exits : Katamaran.RiscvPmp.CFGVer.Verifier.SExitTable (wlctx Γ)}
        (ι : Valuation Γ) (ExitCondIprop : iProp Σ)
        (Hif : Katamaran.RiscvPmp.CFGVer.VerifierRel.itable_rel (w := wlctx Γ) instrs tbl ι)
        (Hef : Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx Γ) exitCond exits ι) :
      (* ∀ words: the VC is UNIFORM in the instruction words, because on the
         symbolic side they are demonic.  So the caller proves it once and this
         lemma instantiates it with the actual words carried by ptsto_instrs.

         `ai_instr <$> instrs` for the same reason as in
         sound_exec_cfg_addr_myWP2: the executor's map is AnnotInstr-valued
         and MEMORY is AST-valued.  ptsto_instrs itself keeps its AST type —
         it is what the trusted statements name — so the projection lives at
         every use site rather than inside it. *)
      (forall words : bv xlenbits -> bv word,
         Katamaran.RiscvPmp.CFGVer.VerifierRel.cexec_triple_addr pre instrs words exitCond fuel post tbl exits (λ _ _, True) []) →
      ⊢ ∀ a : RelVal ty_xlenbits,
        asn.interpret pre ι.["a"∷ty_xlenbits ↦ a] ∗ ⌜secLeak a⌝ ∗
        pc ↦ᵣ a ∗ (∃ v, nextpc ↦ᵣ v) ∗
        Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs (ai_instr <$> instrs) -∗
        (∀ an,
           ⌜match an with SyncVal v => exitCond v = true | NonSyncVal _ _ => False end⌝ ∗
           pc ↦ᵣ an ∗ (∃ v, nextpc ↦ᵣ v) ∗
           Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs (ai_instr <$> instrs) -∗ ExitCondIprop) -∗
        myWP2_loop ExitCondIprop.
    Proof.
      cbv [Katamaran.RiscvPmp.CFGVer.VerifierRel.cexec_triple_addr bind demonic_ctx demonic
           CPureSpec.demonic lift_purespec CPureSpec.assume_formula CPureSpec.assume_pathcondition].
      (* The `∃ v, nextpc ↦ᵣ v` STAYS existential in this lemma's PRE — this is
         the outer entry point, and that existential is exactly what
         create_resources / ImplPre provides.  It is destructed HERE and the
         witness npc handed to cexec_triple_addr's single nextpc demonic and to
         sound_exec_cfg_addr_myWP2.  That is why threading the value inward
         costs no change to the trusted surface. *)
      iIntros (Htrip a) "(Hpre & %HsLa & Hpc & [%npc Hnpc] & Hinstrs) Hk".
      (* Name the words the memory actually holds; they instantiate both the
         uniform VC and the word half of cexec_triple_addr's demonic_ctx. *)
      iDestruct "Hinstrs" as (words) "Hinstrs".
      specialize (Htrip words).
      rewrite CPureSpec.wp_demonic_ctx in Htrip.
      specialize (Htrip (env.cat ι (Katamaran.RiscvPmp.CFGVer.VerifierRel.env_of_words
                                      (length tbl) (ty.SyncVal bv.zero)
                                      (Katamaran.RiscvPmp.CFGVer.VerifierRel.cws_of
                                         (w := wlctx Γ) words tbl ι)))).
      (* Split the supplied valuation back into its two halves, exactly as
         cexec_triple_addr does. *)
      rewrite env.drop_cat in Htrip.
      rewrite Katamaran.RiscvPmp.CFGVer.VerifierRel.env_take_cat in Htrip.
      (* `d` is explicit (it cannot be inferred), the length proof follows it. *)
      rewrite (Katamaran.RiscvPmp.CFGVer.VerifierRel.words_of_env_of_words
                 (ty.SyncVal (bv.zero : bv word)) _
                 (Katamaran.RiscvPmp.CFGVer.VerifierRel.cws_of_length (w := wlctx Γ) words tbl ι)) in Htrip.
      (* The word guard is free: cws_of is BUILT from `words` at the table's
         addresses, so wtable_rel holds by construction given itable_rel. *)
      specialize (Htrip (conj Hif (conj Hef
                    (Katamaran.RiscvPmp.CFGVer.VerifierRel.wtable_rel_cws_of words Hif))) a npc).
      apply produce_sound in Htrip.
      iPoseProof (Htrip with "[$] Hpre") as "(%h2 & [Hh2 %Hexec])". clear Htrip.
      iApply (sound_exec_cfg_addr_myWP2 a npc ExitCondIprop _ _ Hexec
        with "[$Hpc $Hnpc $Hinstrs $Hh2]").
      iIntros (an) "(%Hexit & Hpc & Hnpc & Hinstrs & _)".
      iApply ("Hk" $! an).
      iSplit. { iPureIntro. exact Hexit. }
      iFrame "Hpc Hnpc".
      unfold Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs.
      iExists words.
      iFrame "Hinstrs".
    Qed.

    Lemma sound_scfg_verification_condition_myWP2 {Γ pre post instrs exitCond fuel}
        (* the ALIASES, never a spelled-out tuple.  This is now the SIXTH
           signature caught with a literal `list (Term _ ty_xlenbits * AST)` in
           it (five in VerifierRel.v), and every one of them silently failed to
           track BOTH table columns added since — the word column and then
           AnnotInstr.  The type error always surfaces far from the cause. *)
        {tbl : Katamaran.RiscvPmp.CFGVer.Verifier.SInstrTable (wlctx Γ)}
        {exits : Katamaran.RiscvPmp.CFGVer.Verifier.SExitTable (wlctx Γ)}
        (Hverif : safeE (postprocess (
            Katamaran.RiscvPmp.CFGVer.Verifier.scfg_verification_condition
              pre tbl exits fuel post wnil)))
        (ι : Valuation Γ) (ExitCond : iProp Σ)
        (Hif : Katamaran.RiscvPmp.CFGVer.VerifierRel.itable_rel (w := wlctx Γ) instrs tbl ι)
        (Hef : Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx Γ) exitCond exits ι) :
      ⊢ ∀ a : RelVal ty_xlenbits,
          asn.interpret pre (ι.["a"∷ty_xlenbits ↦ a]) ∗ ⌜secLeak a⌝ ∗
          pc ↦ᵣ a ∗ (∃ v, nextpc ↦ᵣ v) ∗
          Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs (ai_instr <$> instrs) -∗
          (∀ an,
             ⌜match an with
               | SyncVal v => exitCond v = true
               | NonSyncVal _ _ => False
               end⌝ ∗
             pc ↦ᵣ an ∗ (∃ v, nextpc ↦ᵣ v) ∗
             Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs (ai_instr <$> instrs) -∗
             ExitCond) -∗
          myWP2_loop ExitCond.
    Proof.
      apply (sound_cexec_triple_addr_myWP2 (post := post) (fuel := fuel) (ι := ι) ExitCond Hif Hef).
      intros words.
      apply (safeE_safe env.nil), postprocess_sound in Hverif.
      apply LogicalSoundness.psafe_safe in Hverif; [|done].
      revert Hverif.
      apply Katamaran.RiscvPmp.CFGVer.VerifierRel.rcfg_verification_condition.
      - easy.
      - constructor.
    Qed.

End AdequacyTools.
