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
(* bare Require, qualified use: only cfg_postprocess (the VC pipeline) *)
From Katamaran Require RiscvPmp.CFGVer.Contracts.
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

  (* ---------------------------------------------------------------- *)
  (* CONTRACT COMPOSITION.  exitCondImpliesMyWP2_loop above is the    *)
  (* UNIT of a monad in ExitCond; myWP2_loop_bind is its BIND, and it  *)
  (* is what lets two separately-verified segment contracts be joined  *)
  (* into one fact about the whole program.  Every flavour of          *)
  (* composition (a straight-line cut, a loop invariant, a function    *)
  (* contract at a call site) is a client of these two.                *)
  (* See plans/PLAN-loop-invariant.md U1/U6.                            *)
  (*                                                                   *)
  (* The directed halves of fixpoint_myWP2_loop_eq are separate lemmas *)
  (* on purpose: a bare `rewrite fixpoint_myWP2_loop_eq` inside the    *)
  (* bind proof also rewrites inside the Lob hypothesis (in IPM the    *)
  (* hypotheses are part of the goal term), after which iApply "IH"    *)
  (* fails with "iSpecialize: cannot instantiate ... with myWP2_loop   *)
  (* E1".  Note also that fixpoint_myWP2_loop_eq mentions the fixpoint *)
  (* on BOTH sides, hence the occurrence selectors.                    *)
  (* ---------------------------------------------------------------- *)
  Lemma myWP2_loop_unfold `{sailGS2 Σ} (E : iProp Σ) :
    myWP2_loop E ⊢ myWP2_loop_fix E (myWP2_loop E).
  Proof. rewrite {1}fixpoint_myWP2_loop_eq. done. Qed.

  Lemma myWP2_loop_fold `{sailGS2 Σ} (E : iProp Σ) :
    myWP2_loop_fix E (myWP2_loop E) ⊢ myWP2_loop E.
  Proof. rewrite {2}fixpoint_myWP2_loop_eq. done. Qed.

  (* If E1 (the first segment's exit assertion) itself implies "keep
     running until E2", then running until E1 and then continuing is
     running until E2. *)
  Lemma myWP2_loop_bind `{sailGS2 Σ} (E1 E2 : iProp Σ) :
    ⊢ (E1 -∗ myWP2_loop E2) -∗ myWP2_loop E1 -∗ myWP2_loop E2.
  Proof.
    iLöb as "IH". iIntros "HE H".
    iDestruct (myWP2_loop_unfold with "H") as "H".
    iEval (rewrite /myWP2_loop_fix) in "H".
    iDestruct "H" as "[HE1 | H]".
    - by iApply "HE".
    - iApply myWP2_loop_fold. iEval (rewrite /myWP2_loop_fix). iRight.
      iDestruct "H" as (v) "[Hpc Hcont]".
      iExists v. iFrame "Hpc". iIntros "Hpc".
      iDestruct ("Hcont" with "Hpc") as "Hwp".
      iApply (semWP2_mono with "Hwp").
      iIntros (v1 ? v2 ?) "Hm".
      destruct v1 as [v1|m1]; destruct v2 as [v2|m2]; try done.
      iNext. iApply ("IH" with "HE Hm").
  Qed.

  (* The form actually used at a cut point: a segment is discharged with
     ExitCond := myWP2_loop <real exit>, which yields a nested loop. *)
  Lemma myWP2_loop_join `{sailGS2 Σ} (E : iProp Σ) :
    myWP2_loop (myWP2_loop E) ⊢ myWP2_loop E.
  Proof.
    iIntros "H". iApply (myWP2_loop_bind (myWP2_loop E) E with "[] H"). auto.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* THE LOOP RULE.  Turns a contract for the loop BODY into a contract *)
  (* for the whole LOOP, back edge included.                            *)
  (*                                                                    *)
  (*   Inv n   = the loop invariant with n trips still to run           *)
  (*   Hstep   = the BODY contract: one trip, n+1 -> n                  *)
  (*   Hexit   = the EXIT contract: the guard fails, leave the loop     *)
  (*                                                                    *)
  (* The caller supplies those two and gets the loop summary; the        *)
  (* induction and the `▷`/fixpoint bookkeeping stay in here.  This is   *)
  (* the whole of what Example/CountdownComposedResult.v and            *)
  (* Example/TwoLoopsComposedResult.v used to hand-roll per loop.       *)
  (* ---------------------------------------------------------------- *)
  Lemma myWP2_loop_induction `{sailGS2 Σ} (Inv : nat -> iProp Σ) (E : iProp Σ) :
    (forall n, Inv (S n) -∗ myWP2_loop (Inv n)) ->
    (Inv 0 -∗ myWP2_loop E) ->
    forall n, Inv n -∗ myWP2_loop E.
  Proof.
    intros Hstep Hexit n. induction n as [|n IH]; iIntros "H".
    - by iApply Hexit.
    - iApply (myWP2_loop_bind (Inv n) E with "[] [H]").
      + iApply IH.
      + by iApply Hstep.
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

  (* RVToOption is an agreement test on the pair: Some v means both sides
     are v (relval-pair). *)
  Lemma RVToOption_some (rv : RelVal ty_xlenbits) (v : bv xlenbits) :
    ty.RVToOption rv = Some v -> rv = ty.SyncVal v.
  Proof.
    destruct rv as [l r]. unfold ty.RVToOption; cbn.
    match goal with |- context[if ?d then _ else _] => destruct d as [<-|] end;
      intros H; [|discriminate H].
    injection H as ->. reflexivity.
  Qed.
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
        (* lia chokes on the 2^32 literal, so bound below lenAddr -- kept
           SYMBOLIC, so this proof does not move when lenAddr does -- and
           transit through Base.v's lenAddr_rep. *)
        assert (Hb : (bv.bin a + 4 + 4 * N.of_nat (length instrs) < lenAddr)%N) by lia.
        eapply N.lt_trans; [exact Hb|]. exact lenAddr_rep. }
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


  (* ---- DATA AT ARBITRARY ADDRESSES (PLAN-general-endtoend.md A1) ------- *)
  (* The data cells may sit ANYWHERE in the address space: each in range,
     each disjoint from the code, pairwise disjoint.  The contiguous layout
     right after the code is one instance (contig_data_layout).  The proof
     does not slice liveAddrs into consecutive ranges: the code bytes plus
     the data bytes are NoDup and live, hence a sub-multiset of liveAddrs,
     and big_sepL_submseteq peels their ownership off (affine). *)
  Lemma exp2_Z (n : nat) : Z.of_N (bv.exp2 n) = (2 ^ Z.of_nat n)%Z.
  Proof. rewrite N2Z.inj_pow nat_N_Z. reflexivity. Qed.

  Lemma elem_seqBv_bin {n} (a x : bv n) (len : N) :
    (bv.bin a + len <= bv.exp2 n)%N ->
    x ∈ bv.seqBv a len -> (bv.bin a <= bv.bin x < bv.bin a + len)%N.
  Proof.
    intros Hb Hx. unfold bv.seqBv in Hx.
    apply list.elem_of_list_fmap_2 in Hx as [z [-> Hz]].
    apply list_numbers.elem_of_seqZ in Hz.
    pose proof (bv.unsigned_bounds a) as Ba. pose proof (exp2_Z n) as Ee.
    assert (E : bv.unsigned (@bv.of_Z n z) = z).
    { rewrite bv.unsigned_of_Z. unfold bv.truncz. apply Z.mod_small. unfold bv.unsigned in *. lia. }
    unfold bv.unsigned in E, Hz. lia.
  Qed.

  Lemma lenAddr_small_word : (lenAddr <= bv.exp2 word)%N.
  Proof. vm_compute. discriminate. Qed.

  (* two data cells do not overlap *)
  Definition data_cell_sep (s t : mem_spec) : Prop :=
    (bv.bin s.1 + 4 <= bv.bin t.1 \/ bv.bin t.1 + 4 <= bv.bin s.1)%N.

  (* THE premise: every cell in range and clear of the code
     [start, start + 4·ncode), the cells pairwise disjoint *)
  Definition data_layout_ok (start : N) (ncode : nat) (specs : list mem_spec) : Prop :=
    Forall (fun s => (bv.bin s.1 + 4 <= lenAddr)%N /\
                     (bv.bin s.1 + 4 <= start \/ start + 4 * N.of_nat ncode <= bv.bin s.1)%N) specs
    /\ ForallOrdPairs data_cell_sep specs.

  Definition data_bytes (specs : list mem_spec) : list (bv word) :=
    concat (List.map (fun s => bv.seqBv s.1 4) specs).

  Lemma data_bytes_elem (specs : list mem_spec) x :
    Forall (fun s => (bv.bin s.1 + 4 <= lenAddr)%N) specs ->
    x ∈ data_bytes specs -> exists s, In s specs /\ (bv.bin s.1 <= bv.bin x < bv.bin s.1 + 4)%N.
  Proof.
    pose proof lenAddr_small_word.
    induction specs as [|s ss IH]; intros Hr Hx; [inversion Hx|].
    inversion Hr as [|? ? Hs Hss]; subst.
    unfold data_bytes in Hx. cbn [List.map concat] in Hx.
    apply elem_of_app in Hx as [Hx|Hx].
    - exists s. split; [left; reflexivity|].
      change (ty.Val ty_word) with (bv word) in *.
      apply elem_seqBv_bin; [lia|exact Hx].
    - destruct (IH Hss Hx) as [t [Ht Hb]]. exists t. split; [right; exact Ht|exact Hb].
  Qed.

  Lemma data_bytes_NoDup (specs : list mem_spec) :
    Forall (fun s => (bv.bin s.1 + 4 <= lenAddr)%N) specs ->
    ForallOrdPairs data_cell_sep specs ->
    NoDup (data_bytes specs).
  Proof.
    pose proof lenAddr_small_word.
    induction specs as [|s ss IH]; intros Hr Hp; [constructor|].
    inversion Hr as [|? ? Hs Hss]; subst. inversion Hp as [|? ? Hsep Hps]; subst.
    unfold data_bytes. cbn [List.map concat]. apply NoDup_app. split; [|split].
    - apply bv.seqBv_NoDup. pose proof (exp2_Z word). unfold bv.unsigned.
      change (ty.Val ty_word) with (bv word) in *. lia.
    - intros x Hx1 Hx2.
      change (ty.Val ty_word) with (bv word) in *.
      apply elem_seqBv_bin in Hx1; [|lia].
      destruct (data_bytes_elem Hss Hx2) as [t [Ht Hb]].
      rewrite Forall_forall in Hsep.
      pose proof (Hsep t ltac:(apply elem_of_list_In; exact Ht)) as Hst.
      unfold data_cell_sep in Hst.
      change (ty.Val ty_word) with (bv word) in *. lia.
    - apply IH; assumption.
  Qed.

  (* intro_mem_with_memory without the contiguity: the bytes of each cell *)
  Lemma intro_mem_with_memory_at `{sailGS2 Σ} {μ1 μ2 : Memory} (specs : list mem_spec) :
    ([∗ list] a' ∈ data_bytes specs,
      @pointsto _ _ _ _ _
        (@mc_ghGS Σ (@memGS2_memGS_left Σ (@sailGS2_memGS Σ H))) a'
        (DfracOwn 1) (memory_ram μ1 a')) ∗
    ([∗ list] a' ∈ data_bytes specs,
      @pointsto _ _ _ _ _
        (@mc_ghGS Σ (@memGS2_memGS_right Σ (@sailGS2_memGS Σ H))) a'
        (DfracOwn 1) (memory_ram μ2 a'))
    ⊢ interp_mem_with_memory μ1 μ2 specs.
  Proof.
    iIntros "[H1 H2]".
    iInduction specs as [| [a pub] specs] "IH"; [done|].
    unfold data_bytes. cbn [List.map concat fst].
    rewrite !big_opL_app.
    iDestruct "H1" as "[H1h H1t]". iDestruct "H2" as "[H2h H2t]".
    cbn [interp_mem_with_memory big_opL].
    iSplitL "H1h H2h".
    { iApply (intro_ptstomem_word2_nonsync (get_word_is_mem_has_word μ1 a)
                                            (get_word_is_mem_has_word μ2 a)).
      iFrame. }
    iApply ("IH" with "H1t H2t").
  Qed.

  (* Extract instruction memory AND data memory from mem_res2_without_leak,
     the data cells anywhere data_layout_ok allows.  The result is the
     all-NonSyncVal form interp_mem_with_memory; something_memory (outside
     AdequacyTools) converts it to interp_mem_with_public_memory. *)
  Lemma instrsAndDataMemory_at `{sailGS2 Σ} {μ1 μ2 : Memory} (start : N) ws_instrs data_specs instrs :
    (start + 4 * N.of_nat (length instrs) < lenAddr)%N →
    mem_has_instrs μ1 (bv.of_N start) ws_instrs instrs →
    mem_has_instrs μ2 (bv.of_N start) ws_instrs instrs →
    data_layout_ok start (length instrs) data_specs →
    @mem_res2_without_leak _ sailGS2_memGS μ1 μ2 ⊢ |={⊤}=>
      Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs (instrs_of_list (bv.of_N start) instrs) ∗
      interp_mem_with_memory μ1 μ2 data_specs.
  Proof.
    iIntros (Hlen HMem1 HMem2 [Hr Hp]) "Hmem".
    pose proof lenAddr_small_word as HL.
    assert (Hrng : Forall (fun s : mem_spec => (bv.bin s.1 + 4 <= lenAddr)%N) data_specs).
    { eapply Forall_impl; [exact Hr|]. intros s [Hs _]. exact Hs. }
    assert (Hst : bv.bin (@bv.of_N word start) = start).
    { apply bv.bin_of_N_small. lia. }
    set (C := bv.seqBv (n := word) (bv.of_N start) (4 * N.of_nat (length instrs))).
    assert (HC : forall x, x ∈ C -> (start <= bv.bin x < start + 4 * N.of_nat (length instrs))%N).
    { intros x Hx. apply elem_seqBv_bin in Hx; [lia|lia]. }
    assert (Hsub : C ++ data_bytes data_specs ⊆+ liveAddrs).
    { apply NoDup_submseteq.
      - apply NoDup_app. split; [|split].
        + apply bv.seqBv_NoDup. pose proof (exp2_Z word). unfold bv.unsigned. rewrite Hst. lia.
        + intros x Hx1 Hx2. apply HC in Hx1.
          destruct (data_bytes_elem Hrng Hx2) as [t [Ht Hb]].
          rewrite Forall_forall in Hr.
          destruct (Hr t ltac:(apply elem_of_list_In; exact Ht)) as [_ Hd].
          change (ty.Val ty_word) with (bv word) in *. lia.
        + apply data_bytes_NoDup; assumption.
      - intros x Hx. unfold liveAddrs. apply bv.in_seqBv'.
        + unfold bv.ule. unfold minAddr; change (bv.bin (bv.of_N 0)) with 0%N. lia.
        + unfold minAddr. change (bv.bin (bv.of_N 0)) with 0%N. rewrite N.add_0_l.
          apply elem_of_app in Hx as [Hx|Hx].
          * apply HC in Hx. change (@bv.bin xlenbits) with (@bv.bin word) in *. lia.
          * destruct (data_bytes_elem Hrng Hx) as [t [Ht Hb]].
            rewrite Forall_forall in Hr.
            destruct (Hr t ltac:(apply elem_of_list_In; exact Ht)) as [Hd _].
            change (ty.Val ty_word) with (bv word) in *.
            change (@bv.bin xlenbits) with (@bv.bin word) in *. lia. }
    unfold mem_res2_without_leak, IrisInstance.RiscvPmpIrisAdeqParameters.mem_res_without_leak.
    iDestruct "Hmem" as "[[H1 Htr1] [H2 Htr2]]".
    iPoseProof (big_sepL_submseteq _ _ _ Hsub with "H1") as "H1".
    iPoseProof (big_sepL_submseteq _ _ _ Hsub with "H2") as "H2".
    rewrite !big_opL_app.
    iDestruct "H1" as "[Hinst1 Hdata1]". iDestruct "H2" as "[Hinst2 Hdata2]".
    iModIntro. iSplitL "Hinst1 Hinst2".
    - iExists (words_of_list (bv.of_N start) ws_instrs).
      iApply (intro_ptsto_instrs (μ1 := μ1) (μ2 := μ2)); eauto.
      { rewrite Hst. lia. }
      iFrame.
    - iApply intro_mem_with_memory_at. iFrame.
  Qed.

  (* the contiguous layout right after the code satisfies data_layout_ok *)
  Lemma contig_data_cells (base : N) (specs : list mem_spec) :
    (base + 4 * N.of_nat (length specs) <= lenAddr)%N ->
    (forall i s, specs !! i = Some s -> bv.bin s.1 = (base + 4 * N.of_nat i)%N) ->
    Forall (fun s : mem_spec => (base <= bv.bin s.1 /\ bv.bin s.1 + 4 <= base + 4 * N.of_nat (length specs))%N) specs
    /\ ForallOrdPairs data_cell_sep specs.
  Proof.
    revert base. induction specs as [|s ss IH]; intros base Hb Hi; [split; constructor|].
    assert (H0 : bv.bin s.1 = base) by (rewrite (Hi 0%nat s eq_refl); lia).
    assert (Hi' : forall i t, ss !! i = Some t -> bv.bin t.1 = ((base + 4) + 4 * N.of_nat i)%N).
    { intros i t Ht. rewrite (Hi (S i) t Ht). lia. }
    cbn [length] in Hb.
    destruct (IH (base + 4)%N ltac:(lia) Hi') as [Hf Hp].
    split.
    - constructor.
      { cbn [length]. change (ty.Val ty_word) with (bv word) in *. lia. }
      eapply Forall_impl; [exact Hf|]. intros t Ht. cbn [length].
      change (ty.Val ty_word) with (bv word) in *. cbv beta in Ht |- *. lia.
    - constructor; [|exact Hp].
      eapply Forall_impl; [exact Hf|]. intros t Ht. cbv beta in Ht. unfold data_cell_sep.
      change (ty.Val ty_word) with (bv word) in *. lia.
  Qed.

  Lemma contig_data_layout (start : N) (instrs : list AST) (specs : list mem_spec) :
    (start + 4 * N.of_nat (length instrs) + 4 * N.of_nat (length specs) < lenAddr)%N ->
    (forall i s, specs !! i = Some s ->
       s.1 = bv.of_N (start + 4 * N.of_nat (length instrs) + 4 * N.of_nat i)) ->
    data_layout_ok start (length instrs) specs.
  Proof.
    intros Hl Ha.
    destruct (contig_data_cells (start + 4 * N.of_nat (length instrs)) specs) as [Hf Hp]; [lia| |].
    { intros i s Hs. rewrite (Ha i s Hs). apply bv.bin_of_N_small.
      pose proof lenAddr_small_word. apply lookup_lt_Some in Hs.
      change (@Datatypes.length (prod (bv word) bool)) with (@Datatypes.length mem_spec) in Hs. lia. }
    split; [|exact Hp].
    eapply Forall_impl; [exact Hf|]. intros s Hs. cbv beta in Hs |- *.
    change (ty.Val ty_word) with (bv word) in *. lia.
  Qed.

  (* The contiguous layout (data words at start + 4·|instrs| + 4·i), as a
     corollary of instrsAndDataMemory_at. *)
  Lemma instrsAndDataMemory `{sailGS2 Σ} {μ1 μ2 : Memory} (start : N) ws_instrs data_specs instrs :
    (start + 4 * N.of_nat (length instrs) +
     4 * N.of_nat (length data_specs) < lenAddr)%N →
    mem_has_instrs μ1 (bv.of_N start) ws_instrs instrs →
    mem_has_instrs μ2 (bv.of_N start) ws_instrs instrs →
    (∀ i spec, data_specs !! i = Some spec →
      spec.1 = bv.of_N (start + 4 * N.of_nat (length instrs)
                         + 4 * N.of_nat i)) →
    @mem_res2_without_leak _ sailGS2_memGS μ1 μ2 ⊢ |={⊤}=>
      Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs (instrs_of_list (bv.of_N start) instrs) ∗
      interp_mem_with_memory μ1 μ2 data_specs.
  Proof.
    intros Hlen HMem1 HMem2 HDataAddrs.
    eapply instrsAndDataMemory_at; [lia|exact HMem1|exact HMem2|].
    apply contig_data_layout; assumption.
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

    (* ---------------------------------------------------------------- *)
    (* Phase 4: ghost soundness.  This REPLACES VerifierRel's deleted        *)
    (* cexec_ghosts_pure, which said `cexec_ghosts gs = pure tt` and was     *)
    (* true only while every ghost was concretely the identity.  With a real *)
    (* call_lemma that is false, and the absorption in                       *)
    (* sound_exec_cfg_addr_myWP2 below has to be a genuine entailment        *)
    (* instead of a rewrite.                                                 *)
    (*                                                                       *)
    (* PLAN-annotinstr.md treats this as the hard, open part of Phase 4.  It *)
    (* is not: both ingredients already exist and neither is CFGVer-specific.*)
    (*  - call_lemma_sound (MicroSail/ShallowSoundness.v) turns the shallow  *)
    (*    executor's call_lemma into an LTriple.  It is stated in a section  *)
    (*    over `{L} {biA : BiAffine L} {PI : PredicateDef L}`, so it applies *)
    (*    verbatim to the BINARY instance — nothing unary about it.          *)
    (*  - lemSemCFGVerif (SpecIris.v) supplies ValidLemma for every entry of *)
    (*    CFGVer's LEnv, which is what discharges the LTriple's `req -∗ ens` *)
    (*    obligation.                                                        *)
    (* The combination is exactly iris_rule_stm_lemmak's three-line move     *)
    (* (Iris/BinaryInstance.v): pose the entailment, apply the continuation, *)
    (* feed it the lemma's semantics.  All this lemma adds is the induction  *)
    (* over the ghost LIST, which is needed for the same reason rexec_ghosts *)
    (* needs one — the list comes out of an opaque `ai`, so no finite set of *)
    (* instances covers it.                                                  *)
    (*                                                                       *)
    (* The debug case needs no content because CHeapSpec.debug is the        *)
    (* identity (Shallow/Monads.v), which is also why the symbolic debug     *)
    (* node carries no soundness obligation.                                 *)
    (* ---------------------------------------------------------------- *)
    Lemma sound_cexec_ghosts (gs : list Annot) :
      forall (Φ : unit -> SCHeap -> Prop) (h : SCHeap),
        Katamaran.RiscvPmp.CFGVer.VerifierRel.cexec_ghosts gs Φ h ->
        interpret_scheap h ⊢ ∃ h' : SCHeap, interpret_scheap h' ∧ ⌜Φ tt h'⌝.
    Proof.
      induction gs as [|a gs IH]; intros Φ h Hexec.
      - iIntros "Hh". iExists h. iSplitL "Hh"; [iExact "Hh"|]. iPureIntro. exact Hexec.
      - destruct a; cbn [Katamaran.RiscvPmp.CFGVer.VerifierRel.cexec_ghosts
                         Katamaran.RiscvPmp.CFGVer.VerifierRel.cexec_ghost] in Hexec.
        + (* AnnotDebugBreak: debug is the identity, so the bind collapses and
             the remaining list is executed on the SAME heap. *)
          now apply IH.
        + (* AnnotLemmaInvocation *)
          unfold bind, CHeapSpec.bind in Hexec.
          apply call_lemma_sound in Hexec.
          pose proof (lemSemCFGVerif l) as lemSem.
          remember (RiscvPmpCFGVerifSpec.LEnv l) as contractL.
          clear HeqcontractL.
          destruct Hexec as [Ψ pats req ens ent]; cbn in lemSem.
          iIntros "Hh".
          iPoseProof (ent with "Hh") as (ι Heq) "[Hreq Hcons]".
          iPoseProof ("Hcons" with "[Hreq]") as "H"; [by iApply lemSem|].
          iDestruct "H" as (h') "[Hh' %Hrest]".
          iApply (IH _ _ Hrest with "Hh'").
        + (* AnnotCLemma: the same move, with the catalogue's clemSem in
             place of lemSemCFGVerif. *)
          unfold bind, CHeapSpec.bind in Hexec.
          apply call_lemma_sound in Hexec.
          pose proof (clemSem k) as lemSem.
          remember (Katamaran.RiscvPmp.CFGVer.Verifier.clem_lemma k) as contractL.
          clear HeqcontractL.
          destruct Hexec as [Ψ pats req ens ent]; cbn in lemSem.
          iIntros "Hh".
          iPoseProof (ent with "Hh") as (ι Heq) "[Hreq Hcons]".
          iPoseProof ("Hcons" with "[Hreq]") as "H"; [by iApply lemSem|].
          iDestruct "H" as (h') "[Hh' %Hrest]".
          iApply (IH _ _ Hrest with "Hh'").
    Qed.

    (* ================================================================ *)
    (* BLOCK SOUNDNESS -- the Iris-level premise the block hook needs.    *)
    (*                                                                   *)
    (* This is the `contractsSound` of executor-level composition: the    *)
    (* executor is allowed to REPLACE the instructions at address v by    *)
    (* b's contract exactly when a real execution entering at v with      *)
    (* b's precondition reaches b's exit (blk_exit) with b's postcondition. *)
    (*                                                                   *)
    (* Stated in continuation-passing form over an ARBITRARY ExitCond,    *)
    (* which is what makes it compose: the caller instantiates ExitCond   *)
    (* with `myWP2_loop <real exit>` and joins the nested loop away with  *)
    (* myWP2_loop_join.  That is the idiom myWP2_loop_bind was written    *)
    (* for, so no new Iris machinery is needed here.                      *)
    (*                                                                   *)
    (* Note what is NOT demanded at the exit: `∃ x, nextpc ↦ᵣ x`, not     *)
    (* `nextpc ↦ᵣ pc`.  A block consumes no instruction epilogue, so      *)
    (* nothing forces the nextpc register, and the executor quantifies it *)
    (* demonically instead (Verifier.v).  This is precisely what          *)
    (* sound_scfg_verification_condition_myWP2 already CONCLUDES, so a    *)
    (* segment's own VC discharges this premise with no strengthening.    *)
    (*                                                                   *)
    (* PERSISTENT (□) on purpose: the executor may pass through the same  *)
    (* block table at every step of the induction.                        *)
    (* ================================================================ *)
    (* WHAT A BLOCK PROMISES, as an Iris fact: entering at v with the block's
       precondition, the machine reaches b's exit (blk_exit b ι) with its
       postcondition.  Continuation-passing over an ARBITRARY ExitCond, which
       is what makes it compose -- the caller instantiates ExitCond with
       `myWP2_loop <real exit>` and discharges the nested loop with
       myWP2_loop_join, the idiom myWP2_loop_bind was written for.

       ONE valuation ι over the block's OWN context serves both pre and post,
       with "a" bound to the entry pc and "an" to the exit: this is literally a
       segment contract's shape (compare sound_scfg_verification_condition_
       myWP2's conclusion), which is what lets a segment's VC discharge it.

       Note what is NOT demanded at the exit: `∃ x, nextpc ↦ᵣ x`, not
       `nextpc ↦ᵣ pc`.  A block consumes no instruction epilogue, so nothing
       forces the nextpc register and the executor quantifies it demonically
       (Verifier.v).  That is exactly what the segment lemma concludes, so no
       strengthening is needed anywhere. *)
    (* THE BLOCK'S OWN SPAN, derived from the annotation ALONE.
       `cfg_instrs (blk_contract b)` is a `list AST` naming the code the block
       stands for, and instrs_of_list is polymorphic, so this is a
       `gmap _ AST` directly -- exactly ptsto_instrs_w's argument type, with no
       coercion and no fmap.  SBlk had no field that could say this, which is
       why the OLD blockSound had to take the enclosing program (and hence
       needed to clear the annotation).  PLAN-contract-ast §2c / §2.7. *)
    Definition blk_span (v : bv xlenbits) (b : Katamaran.RiscvPmp.CFGVer.Verifier.BlkAnnot)
        : gmap (bv xlenbits) AST :=
      Katamaran.RiscvPmp.CFGVer.Tables.instrs_of_list v (Katamaran.RiscvPmp.CFGVer.Verifier.cfg_instrs (Katamaran.RiscvPmp.CFGVer.Verifier.blk_contract b)).

    (* WHERE A BLOCK RESUMES: its contract's single exit, instantiated at the
       valuation that satisfied its precondition (PLAN-exit-targets.md).  It
       replaced `SyncVal (v + blk_off b)`, which computed the same address a
       second way and needed Hexit to show the two agreed.  A RelVal, exactly
       as the executors produce it (sexec_block / cexec_block). *)
    Definition blk_exit (b : Katamaran.RiscvPmp.CFGVer.Verifier.BlkAnnot)
        (ι : Valuation (Katamaran.RiscvPmp.CFGVer.Verifier.blk_ctx b)) : RelVal ty_xlenbits :=
      inst (T := fun Σ => Term Σ ty_xlenbits)
        (Katamaran.RiscvPmp.CFGVer.Verifier.cfg_exit (Katamaran.RiscvPmp.CFGVer.Verifier.blk_contract b)) ι.

    (* Owns ONLY its own span -- note there is no `instrs` parameter.  That is
       the whole of §2c: a block reasons about what is visible inside it, and
       the enclosing program is not visible.  The caller splits its instruction
       ownership with ptsto_instrs_w_split, hands the span over, and rejoins
       from the postcondition; blockSound_span_to_whole below is that step. *)
    Definition blockSound (words : bv xlenbits -> bv word)
        (v : bv xlenbits) (b : Katamaran.RiscvPmp.CFGVer.Verifier.BlkAnnot) : iProp Σ :=
      (∀ (ι : Valuation (Katamaran.RiscvPmp.CFGVer.Verifier.blk_ctx b)) (ExitCond : iProp Σ),
         asn.interpret (Katamaran.RiscvPmp.CFGVer.Verifier.extend_to_minimal_pre (Katamaran.RiscvPmp.CFGVer.Verifier.cfg_precondition (Katamaran.RiscvPmp.CFGVer.Verifier.blk_contract b))) (ι.["a"∷ty_xlenbits ↦ ty.SyncVal v]) ∗
         pc ↦ᵣ ty.SyncVal v ∗ (∃ x, nextpc ↦ᵣ x) ∗
         Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs_w words (blk_span v b) -∗
         (asn.interpret (Katamaran.RiscvPmp.CFGVer.Verifier.cfg_postcondition (Katamaran.RiscvPmp.CFGVer.Verifier.blk_contract b))
            ((ι.["a"∷ty_xlenbits ↦ ty.SyncVal v])
               .["an"∷ty_xlenbits ↦ blk_exit b ι]) ∗
          pc ↦ᵣ blk_exit b ι ∗
          (∃ x, nextpc ↦ᵣ x) ∗
          Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs_w words (blk_span v b) -∗ ExitCond) -∗
         myWP2_loop ExitCond)%I.

    (* Indexed by `instrs` ALONE: the block contract rides in the AnnotInstr
       payload, so there is no second table to index by.  That is also why no
       btable_rel exists -- itable_rel already ties `instrs !! v = Some ai` to
       the matched symbolic entry, and the block comes with it. *)
    (* Every block the executor can apply at `stepped` (Verifier.ai_fire) is
       sound: at `false` only the ai_block annotations, at `true` the ai_loop
       (re-entry) ones as well. *)
    Definition blocksSoundAt (stepped : bool) (words : bv xlenbits -> bv word)
        (instrs : gmap (bv xlenbits) Katamaran.RiscvPmp.CFGVer.Verifier.AnnotInstr)
        : iProp Σ :=
      (* No containment conjunct any more: that the block's span really IS
         this program's code is checked by the VC at the firing site
         (Verifier.blk_code_in, PLAN-valid-blk-annot.md §1c) and read off the
         concrete run (cblk_code_in_sub). *)
      (□ ∀ v ai b, ⌜instrs !! v = Some ai⌝ →
                   ⌜Katamaran.RiscvPmp.CFGVer.Verifier.ai_fire stepped ai = Some b⌝ →
                   blockSound words v b)%I.

    (* ALL of a program's blocks, of both kinds.  This is the premise every
       external bridge takes; only the executor-level lemmas below split it
       into `blocksSoundAt false` (needed now) and `▷ blocksSound` (needed only
       once an instruction has run), which is what lets a loop's re-entry
       block be justified by Löb induction. *)
    Definition blocksSound (words : bv xlenbits -> bv word)
        (instrs : gmap (bv xlenbits) Katamaran.RiscvPmp.CFGVer.Verifier.AnnotInstr)
        : iProp Σ :=
      blocksSoundAt true words instrs.

    #[export] Instance blocksSoundAt_persistent stepped words instrs :
      Persistent (blocksSoundAt stepped words instrs).
    Proof. apply _. Qed.

    #[export] Instance blocksSound_persistent words instrs :
      Persistent (blocksSound words instrs).
    Proof. apply _. Qed.

    (* ai_fire false selects a subset of what ai_fire true does. *)
    Lemma blocksSound_at_false words instrs :
      blocksSound words instrs ⊢ blocksSoundAt false words instrs.
    Proof.
      iIntros "#H !>" (v ai b) "%Hlk %Hb".
      iApply ("H" $! v ai b with "[//] [%]").
      unfold Katamaran.RiscvPmp.CFGVer.Verifier.ai_fire in *.
      destruct (Katamaran.RiscvPmp.CFGVer.Verifier.ai_block ai); [exact Hb|discriminate].
    Qed.

    (* RECOVER THE WHOLE-PROGRAM INTERFACE from the span-only one, given
       containment.  This is the ONLY place the two views meet.

       Note the last line: the remainder `Hrest` is discharged by a plain
       iFrame.  The caller's continuation is an ordinary wand, so it CLOSES
       OVER the remainder from the caller's own spatial context -- the
       remainder never travels through myWP2_loop and there is nothing to frame
       across it.  §2c nominated a myWP2_loop frame rule as the design's
       load-bearing risk; it is not needed here, and that claim is retracted in
       the plan. *)
    Lemma blockSound_span_to_whole (words : bv xlenbits -> bv word)
        (instrs : gmap (bv xlenbits) Katamaran.RiscvPmp.CFGVer.Verifier.AnnotInstr)
        (v : bv xlenbits) (b : Katamaran.RiscvPmp.CFGVer.Verifier.BlkAnnot)
        (ι : Valuation (Katamaran.RiscvPmp.CFGVer.Verifier.blk_ctx b)) (ExitCond : iProp Σ) :
      blk_span v b ⊆ ai_instr <$> instrs ->
      blockSound words v b -∗
      (asn.interpret (Katamaran.RiscvPmp.CFGVer.Verifier.extend_to_minimal_pre (Katamaran.RiscvPmp.CFGVer.Verifier.cfg_precondition (Katamaran.RiscvPmp.CFGVer.Verifier.blk_contract b)))
         (ι.["a"∷ty_xlenbits ↦ ty.SyncVal v]) ∗
       pc ↦ᵣ ty.SyncVal v ∗ (∃ x, nextpc ↦ᵣ x) ∗
       Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs_w words (ai_instr <$> instrs)) -∗
      (asn.interpret (Katamaran.RiscvPmp.CFGVer.Verifier.cfg_postcondition (Katamaran.RiscvPmp.CFGVer.Verifier.blk_contract b))
         ((ι.["a"∷ty_xlenbits ↦ ty.SyncVal v])
            .["an"∷ty_xlenbits ↦ blk_exit b ι]) ∗
       pc ↦ᵣ blk_exit b ι ∗
       (∃ x, nextpc ↦ᵣ x) ∗
       Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs_w words (ai_instr <$> instrs) -∗ ExitCond) -∗
      myWP2_loop ExitCond.
    Proof.
      intros Hsub.
      iIntros "Hb (Hpre & Hpc & Hnpc & Hinstrs) Hk".
      rewrite (Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs_w_split words Hsub).
      iDestruct "Hinstrs" as "[Hspan Hrest]".
      iApply ("Hb" $! ι ExitCond with "[$Hpre $Hpc $Hnpc $Hspan]").
      iIntros "(Hpost & Hpc' & Hnpc' & Hspan')".
      iApply "Hk". iFrame.
    Qed.

    (* THE CONTAINMENT, read off the concrete run: cexec_block_chk asserts
       cblk_code_in, which is pointwise exactly the insert chain
       instrs_of_list builds.  No key-freshness needed -- a later insert at a
       colliding key is still a lookup the premise already covers. *)
    Lemma cblk_code_in_sub
        (instrs : gmap (bv xlenbits) Katamaran.RiscvPmp.CFGVer.Verifier.AnnotInstr)
        (l : list AST) :
      forall v, Katamaran.RiscvPmp.CFGVer.VerifierRel.cblk_code_in instrs v l ->
      Katamaran.RiscvPmp.CFGVer.Tables.instrs_of_list v l ⊆ ai_instr <$> instrs.
    Proof.
      induction l as [|i l IH]; intros v Hc; cbn [Katamaran.RiscvPmp.CFGVer.Tables.instrs_of_list].
      - apply map_empty_subseteq.
      - destruct Hc as [Hv Hc].
        apply insert_subseteq_l; [exact Hv|exact (IH _ Hc)].
    Qed.

    Lemma instrs_of_list_elem_of {A} (base : bv xlenbits) (l : list A) v x :
      Katamaran.RiscvPmp.CFGVer.Tables.instrs_of_list base l !! v = Some x ->
      List.In x l.
    Proof.
      revert base v x. induction l as [|i l IH]; intros base v x H.
      - rewrite lookup_empty in H. discriminate.
      - (* lookup_insert_Some rather than a decide + two rewrites: `rewrite ...
           in H by tac` does not parse here (ssreflect's rewrite is in scope,
           where `by` means something else). *)
        cbn in H. apply lookup_insert_Some in H as [[-> ->]|[Hne H]].
        + now left.
        + right. exact (IH _ _ _ H).
    Qed.

    (* cexec_block's shallow-to-Iris step: the exact analogue of
       call_lemma_sound (MicroSail/ShallowSoundness.v), minus the
       assert_eq_nenv a function call needs and with a fixed result.  The ONE
       angelically-chosen ι serves pre and post, which is what carries a
       block's shared logic variables across the two. *)
    Lemma cexec_block_sound (b : Katamaran.RiscvPmp.CFGVer.Verifier.BlkAnnot) (v : bv xlenbits)
        (Phi : RelVal ty_xlenbits -> SCHeap -> Prop) (h : SCHeap) :
      Katamaran.RiscvPmp.CFGVer.VerifierRel.cexec_block b v Phi h ->
      (interpret_scheap h ⊢
         ∃ ι : Valuation (Katamaran.RiscvPmp.CFGVer.Verifier.blk_ctx b),
           asn.interpret (Katamaran.RiscvPmp.CFGVer.Verifier.extend_to_minimal_pre (Katamaran.RiscvPmp.CFGVer.Verifier.cfg_precondition (Katamaran.RiscvPmp.CFGVer.Verifier.blk_contract b))) (ι.["a"∷ty_xlenbits ↦ ty.SyncVal v]) ∗
           (asn.interpret (Katamaran.RiscvPmp.CFGVer.Verifier.cfg_postcondition (Katamaran.RiscvPmp.CFGVer.Verifier.blk_contract b))
              ((ι.["a"∷ty_xlenbits ↦ ty.SyncVal v])
                 .["an"∷ty_xlenbits ↦ blk_exit b ι]) -∗
            ∃ h', interpret_scheap h' ∧
              ⌜Phi (blk_exit b ι) h'⌝))%I.
    Proof.
      unfold Katamaran.RiscvPmp.CFGVer.VerifierRel.cexec_block.
      unfold CHeapSpec.bind, CHeapSpec.lift_purespec.
      rewrite CPureSpec.wp_angelic_ctx.
      intros [ι Hwp]; revert Hwp.
      intros Hwp%CHeapSpec.consume_sound.
      apply bi.exist_intro' with ι.
      rewrite Hwp. apply bi.sep_mono'; [easy|].
      apply bi.exist_elim. intros h'.
      apply bi.pure_elim_r.
      apply CHeapSpec.produce_sound.
    Qed.

    (* The block premise is split by WHEN it is needed.  `blocksSoundAt
       stepped` pays for the blocks this step may apply; `▷ blocksSound` for
       everything from the next instruction on, because each executed
       instruction strips one later (the iModIntro in the instruction branch).
       At the entry (`stepped = false`) that is exactly "ai_block now, ai_loop
       later" -- which is what lets blockSound_of_vc justify a loop whose head
       carries its own block, by Löb induction. *)
    Lemma sound_exec_cfg_addr_myWP2
        {instrs} {words : bv xlenbits -> bv word} {cexit fuel}
        (stepped : bool)
        (apc anp : RelVal ty_xlenbits)
        (ExitCondIprop : iProp Σ) Φ (h : SCHeap) :
      Katamaran.RiscvPmp.CFGVer.VerifierRel.cexec_cfg_addr instrs words cexit fuel stepped apc anp Φ h →
      blocksSoundAt stepped words instrs ∗ ▷ blocksSound words instrs ∗
      interpret_scheap h ∗ pc ↦ᵣ apc ∗ nextpc ↦ᵣ anp ∗
        (* THE BOUNDARY: the executor's map is AnnotInstr-valued, MEMORY is
           AST-valued — memory holds instructions, not annotations.  This is
           the one place the two views meet, and the projection lives here
           rather than in ptsto_instrs (which the trusted statements name). *)
        Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs_w words
          (ai_instr <$> instrs) ⊢
      (∀ an,
         ⌜∃ v, an = SyncVal v ∧ Katamaran.RiscvPmp.CFGVer.VerifierRel.exit_hit cexit v = true⌝ ∗
         pc ↦ᵣ an ∗ (∃ v, nextpc ↦ᵣ v) ∗
           Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs_w words
             (ai_instr <$> instrs) ∗
         (∃ h', interpret_scheap h' ∧ ⌜Φ an h'⌝) -∗ ExitCondIprop) -∗
      myWP2_loop ExitCondIprop.
    Proof.
      revert stepped apc anp h.
      induction fuel as [|n' IH]; intros stepped apc anp h Hexec.
      - cbn [Katamaran.RiscvPmp.CFGVer.VerifierRel.cexec_cfg_addr CHeapSpec.error] in Hexec.
        contradiction.
      - cbn [Katamaran.RiscvPmp.CFGVer.VerifierRel.cexec_cfg_addr] in Hexec.
        revert Hexec. destruct (ty.RVToOption apc) as [v|] eqn:Hapc; intros Hexec.
        + apply RVToOption_some in Hapc. subst apc.
          cbn [CHeapSpec.angelic_binary] in Hexec.
          destruct Hexec as [Hexit | Hexec].
          * destruct (Katamaran.RiscvPmp.CFGVer.VerifierRel.exit_hit cexit v) eqn:Hexit_eq.
            -- cbn [CHeapSpec.pure] in Hexit.
               iIntros "(#Hb0 & #Hbs & Hh & Hpc & Hnpc & Hinstrs) Hk".
               iApply exitCondImpliesMyWP2_loop.
               iApply ("Hk" $! (SyncVal v)).
               iSplit. { iPureIntro. exists v. split; [reflexivity|exact Hexit_eq]. }
               iFrame. iPureIntro. exact Hexit.
            -- cbn [CHeapSpec.error] in Hexit. contradiction.
          * (* Execute branch: the instruction is looked up at address v
               directly (instrs !! v).  No alignment / base guard / index
               arithmetic: the gmap key IS the current PC. *)
            destruct (instrs !! v) as [i|] eqn:Hlk.
            ++ destruct (Katamaran.RiscvPmp.CFGVer.Verifier.ai_fire stepped i) as [b|] eqn:Hbl.
               { (* ---- BLOCK branch.  The executor replaced this instruction
                    (and however many the block spans) by b's contract, and
                    blocksSound is what pays for that.

                    The step: read `pre ∗ rest` out of the heap
                    (cexec_block_sound), hand `pre` plus the machine resources
                    to blocksSound with ExitCond := myWP2_loop <real exit>, and
                    join the nested loop away.  That instantiation is exactly
                    the idiom myWP2_loop_bind/join were written for, so no new
                    Iris machinery is needed. *)
                 unfold bind, CHeapSpec.bind in Hexec.
                 (* the containment check cexec_block_chk asserted first *)
                 unfold Katamaran.RiscvPmp.CFGVer.VerifierRel.cexec_block_chk,
                   CHeapSpec.bind, CHeapSpec.assert_formula, CHeapSpec.lift_purespec,
                   CPureSpec.assert_formula, CPureSpec.assert_pathcondition in Hexec.
                 destruct Hexec as [Hcode Hexec].
                 pose proof (cblk_code_in_sub instrs _ v Hcode) as Hsub.
                 iIntros "(#Hb0 & #Hbs & Hh & Hpc & Hnpc & Hinstrs) Hk".
                 iDestruct (cexec_block_sound _ _ _ _ Hexec with "Hh")
                   as (ι) "[Hpre Hpost]".
                 iDestruct ("Hb0" $! v i b with "[//] [//]") as "Hb".
                 iApply myWP2_loop_join.
                 (* containment came from the run (Hsub above), soundness from
                    blocksSound; the adapter turns the block's SPAN ownership
                    back into the whole-program ownership this loop carries. *)
                 iApply (blockSound_span_to_whole words instrs v b ι
                           (myWP2_loop ExitCondIprop) Hsub
                           with "Hb [$Hpre $Hpc $Hinstrs Hnpc]").
                 { iExists anp. iExact "Hnpc". }
                 iIntros "(Hpost' & Hpc' & Hnpc' & Hinstrs')".
                 iDestruct ("Hpost" with "Hpost'") as (h') "[Hh' %Hrest]".
                 (* The resumed nextpc is DEMONIC (Verifier.v), so Hrest is
                    universally quantified over it and the block's exit only
                    owes us `∃ x, nextpc ↦ᵣ x`.  Instantiate at whatever x the
                    block actually left. *)
                 iDestruct "Hnpc'" as (x) "Hnpc'".
                 iRevert "Hk".
                 iApply (IH stepped _ x h' (Hrest x)).
                 iFrame "Hb0 Hbs Hh' Hpc' Hinstrs' Hnpc'". }
               unfold bind, CHeapSpec.bind in Hexec.
               (* Phase 4 (chunk GC): Hexec now carries the extra cchunk_gc
                  bind cexec_cfg_addr's step inserts before cexec_instruction.
                  Absorb it first — cgc_binds_heap_fwd rewrites Hexec down
                  to the cexec_instruction call over cgc_heap h — then weaken
                  Hh to match via interpret_scheap_gc_heap (§4: sound because
                  iProp Σ is affine). *)
               apply Katamaran.RiscvPmp.CFGVer.VerifierRel.cgc_binds_heap_fwd in Hexec.
               iIntros "(#Hb0 & #Hbs & Hh & Hpc & Hnpc & Hinstrs) Hk".
               iDestruct (interpret_scheap_gc_heap h with "Hh") as "Hh".
               (* Absorb the BEFORE-ghosts.  This used to be a rewrite with
                  cexec_ghosts_pure; with a real call_lemma the ghosts have a
                  genuine heap effect, so it becomes an entailment that hands
                  back a NEW heap h1 together with the residual execution on
                  it.  Same role chunk_gc's cgc_binds_heap_fwd plays two lines
                  up, just no longer free. *)
               iDestruct (sound_cexec_ghosts _ _ _ Hexec with "Hh") as (h1) "[Hh %Hexec1]".
               clear Hexec.
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
               { iApply (Katamaran.RiscvPmp.CFGVer.VerifierRel.sound_exec_instruction Hexec1). iFrame. iPureIntro. reflexivity. }
               iIntros ([v1|m1] δ1 [v2|m2] δ2); cbn.
               2-3: iIntros "(%δ' & _ & HF)"; auto.
               2: iIntros "_"; done.
               iIntros "(%δ' & eqδ' & %rv & eqrv & ([%an (Hnpc' & Hpc' & (%h' & Hh' & %Hcfg & _))] & Hinstr' & _))".
               iPoseProof ("Hframe" with "Hinstr'") as "Hinstrs'".
               (* Absorb the AFTER-ghosts, same lemma, inside the instruction's
                  postcondition where the new heap h' has just appeared. *)
               iDestruct (sound_cexec_ghosts _ _ _ Hcfg with "Hh'") as (h'') "[Hh' %Hcfg']".
               iModIntro.
               iRevert "Hk".
               (* `an an`: the recursive call passes the new pc as both the pc
                  and the incoming nextpc, which is exactly what the epilogue
                  established (pc = nextpc = an).  Hnpc' is framed directly —
                  no `iExists`, since the PRE now names the value. *)
               (* An instruction has now run: the later on "Hbs" was stripped by
                  the iModIntro above, so every block -- ai_loop included -- is
                  available from here on (stepped = true). *)
               iApply (IH true an an h'' Hcfg').
               iSplitR. { iExact "Hbs". }
               iSplitR. { iNext. iExact "Hbs". }
               iFrame "Hh' Hpc' Hinstrs' Hnpc'".
            ++ cbn [CHeapSpec.error] in Hexec. contradiction.
        + cbn [CHeapSpec.error] in Hexec.
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
    Lemma sound_cexec_triple_addr_myWP2_w {Γ : LCtx} {pre post instrs cexit fuel}
        (words : bv xlenbits -> bv word)
        (* the ALIASES, never a spelled-out tuple.  This is now the SIXTH
           signature caught with a literal `list (Term _ ty_xlenbits * AST)` in
           it (five in VerifierRel.v), and every one of them silently failed to
           track BOTH table columns added since — the word column and then
           AnnotInstr.  The type error always surfaces far from the cause. *)
        {tbl : Katamaran.RiscvPmp.CFGVer.Verifier.SInstrTable (wlctx Γ)}
        {exits : Katamaran.RiscvPmp.CFGVer.Verifier.SExitTable (wlctx Γ)}
        (ι : Valuation Γ) (ExitCondIprop : iProp Σ)
        (Hif : Katamaran.RiscvPmp.CFGVer.VerifierRel.itable_rel (w := wlctx Γ) instrs tbl ι)
        (Hef : Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx Γ) cexit exits ι) :
      (* ∀ words: the VC is UNIFORM in the instruction words, because on the
         symbolic side they are demonic.  So the caller proves it once and this
         lemma instantiates it with the actual words carried by ptsto_instrs.

         `ai_instr <$> instrs` for the same reason as in
         sound_exec_cfg_addr_myWP2: the executor's map is AnnotInstr-valued
         and MEMORY is AST-valued.  ptsto_instrs itself keeps its AST type —
         it is what the trusted statements name — so the projection lives at
         every use site rather than inside it. *)
      (forall words : bv xlenbits -> bv word,
         Katamaran.RiscvPmp.CFGVer.VerifierRel.cexec_triple_addr pre instrs words cexit fuel post tbl exits (λ _ _, True) []) →
      (* The block premise, split by when it is needed (see
         sound_exec_cfg_addr_myWP2): the ai_block annotations now, all of them
         UNDER A LATER.  The later is what blockSound_of_vc's Löb induction can
         supply; the ∃-words form below takes both from ⊢ blocksSound. *)
      ⊢ blocksSoundAt false words instrs -∗ ▷ blocksSound words instrs -∗
        ∀ a : RelVal ty_xlenbits,
        asn.interpret pre ι.["a"∷ty_xlenbits ↦ a] ∗ ⌜secLeak a⌝ ∗
        pc ↦ᵣ a ∗ (∃ v, nextpc ↦ᵣ v) ∗
        Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs_w words (ai_instr <$> instrs) -∗
        (∀ an,
           ⌜∃ v, an = SyncVal v ∧ Katamaran.RiscvPmp.CFGVer.VerifierRel.exit_hit cexit v = true⌝ ∗
           pc ↦ᵣ an ∗ (∃ v, nextpc ↦ᵣ v) ∗
           Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs_w words (ai_instr <$> instrs) ∗
           (* RE-THREADED 2026-09-03; commit 2b6c7753 removed exactly this
              conjunct ("keep post in hypothesis for maximal generality, remove
              asn.interpret post from the continuation").  It is the exit
              assertion, and note WHEN it holds: at the moment the EXIT
              CONDITION holds, not when execution halts -- sexec_cfg_addr
              returns only via its exit branch (out-of-fuel is an emsg), and
              `an` is bound to whichever declared exit was taken.  That is what
              lets one segment's exit feed the next segment's precondition; see
              plans/PLAN-loop-invariant.md U2/U6.  Nothing is proved about the
              RESIDUAL heap (SHeapSpec has no leakcheck), which is why the
              shallow continuation stays `(fun _ _ => True)`. *)
           asn.interpret post (ι.["a"∷ty_xlenbits ↦ a].["an"∷ty_xlenbits ↦ an]) -∗
           ExitCondIprop) -∗
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
      iIntros (Htrip) "#Hb0 #Hbsw".
      iIntros (a) "(Hpre & %HsLa & Hpc & [%npc Hnpc] & Hinstrs) Hk".
      (* Name the words the memory actually holds; they instantiate both the
         uniform VC and the word half of cexec_triple_addr's demonic_ctx. *)
      specialize (Htrip words).
      rewrite CPureSpec.wp_demonic_ctx in Htrip.
      (* env_of_words now CONCATENATES the words into one wide value, so it
         takes the plain-bv list (cws_of_bv) and the default is a bare
         bv.zero rather than a SyncVal one. *)
      specialize (Htrip (env.cat ι (Katamaran.RiscvPmp.CFGVer.VerifierRel.env_of_words
                                      (length tbl) bv.zero
                                      (Katamaran.RiscvPmp.CFGVer.VerifierRel.cws_of_bv
                                         (w := wlctx Γ) words tbl ι)))).
      (* Split the supplied valuation back into its two halves, exactly as
         cexec_triple_addr does. *)
      rewrite env.drop_cat in Htrip.
      rewrite Katamaran.RiscvPmp.CFGVer.VerifierRel.env_take_cat in Htrip.
      (* `d` is explicit (it cannot be inferred), the length proof follows it. *)
      (* The round trip now yields `map SyncVal (cws_of_bv ...)`; cws_of_bv_spec
         folds that back to the cws_of the rest of the proof already speaks. *)
      rewrite (Katamaran.RiscvPmp.CFGVer.VerifierRel.words_of_env_of_words
                 (bv.zero : bv word) _
                 (Katamaran.RiscvPmp.CFGVer.VerifierRel.cws_of_bv_length (w := wlctx Γ) words tbl ι)) in Htrip.
      rewrite (Katamaran.RiscvPmp.CFGVer.VerifierRel.cws_of_bv_spec (w := wlctx Γ) words tbl ι) in Htrip.
      (* The word guard is free: cws_of is BUILT from `words` at the table's
         addresses, so wtable_rel holds by construction given itable_rel. *)
      specialize (Htrip (conj Hif (conj Hef
                    (Katamaran.RiscvPmp.CFGVer.VerifierRel.wtable_rel_cws_of words Hif))) a npc).
      apply produce_sound in Htrip.
      iPoseProof (Htrip with "[$] Hpre") as "(%h2 & [Hh2 %Hexec])". clear Htrip.
      iApply (sound_exec_cfg_addr_myWP2 false a npc ExitCondIprop _ _ Hexec
        with "[$Hb0 $Hbsw $Hpc $Hnpc $Hinstrs $Hh2]").
      (* The fifth conjunct used to be DROPPED (`& _`).  It is
         `∃ h', interpret_scheap h' ∧ ⌜Φ an h'⌝`, and Φ here is
         cexec_triple_addr's `consume ens ι.["a"↦a].["an"↦na]` — so
         consume_sound turns it into the exit assertion.  Same three-line
         pattern as BlockVer/Verifier.v:448-450, which never lost it. *)
      iIntros (an) "(%Hexit & Hpc & Hnpc & Hinstrs & (%h3 & [Hh3 %Hconsume]))".
      apply consume_sound in Hconsume.
      iPoseProof (Hconsume with "Hh3") as "[HPOST _]".
      iApply ("Hk" $! an).
      iSplit. { iPureIntro. exact Hexit. }
      iFrame "Hpc Hnpc HPOST".
      iFrame "Hinstrs".
    Qed.

    (* The ∃-words form, for callers that hold `ptsto_instrs`.  Everything is in
       the _w form above; this only opens the existential on the way in and
       closes it on the way out with the SAME words, which is the whole point --
       the executor's frame carries `ptsto_instrs_w words` and needs that exact
       words back for its induction hypothesis, so a caller that went through
       the ∃ form could not continue. *)
    Lemma sound_cexec_triple_addr_myWP2 {Γ : LCtx} {pre post instrs cexit fuel}
        {tbl : Katamaran.RiscvPmp.CFGVer.Verifier.SInstrTable (wlctx Γ)}
        {exits : Katamaran.RiscvPmp.CFGVer.Verifier.SExitTable (wlctx Γ)}
        (ι : Valuation Γ) (ExitCondIprop : iProp Σ)
        (Hif : Katamaran.RiscvPmp.CFGVer.VerifierRel.itable_rel (w := wlctx Γ) instrs tbl ι)
        (Hef : Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx Γ) cexit exits ι) :
      (forall words : bv xlenbits -> bv word,
         Katamaran.RiscvPmp.CFGVer.VerifierRel.cexec_triple_addr pre instrs words cexit fuel post tbl exits (λ _ _, True) []) →
      (forall words : bv xlenbits -> bv word, ⊢ blocksSound words instrs) →
      ⊢ ∀ a : RelVal ty_xlenbits,
        asn.interpret pre ι.["a"∷ty_xlenbits ↦ a] ∗ ⌜secLeak a⌝ ∗
        pc ↦ᵣ a ∗ (∃ v, nextpc ↦ᵣ v) ∗
        Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs (ai_instr <$> instrs) -∗
        (∀ an,
           ⌜∃ v, an = SyncVal v ∧ Katamaran.RiscvPmp.CFGVer.VerifierRel.exit_hit cexit v = true⌝ ∗
           pc ↦ᵣ an ∗ (∃ v, nextpc ↦ᵣ v) ∗
           Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs (ai_instr <$> instrs) ∗
           asn.interpret post (ι.["a"∷ty_xlenbits ↦ a].["an"∷ty_xlenbits ↦ an]) -∗
           ExitCondIprop) -∗
        myWP2_loop ExitCondIprop.
    Proof.
      iIntros (Htrip Hbs a) "(Hpre & %HsLa & Hpc & Hnpc & Hinstrs) Hk".
      iDestruct "Hinstrs" as (words) "Hinstrs".
      iPoseProof (Hbs words) as "#Hbsw".
      iPoseProof (sound_cexec_triple_addr_myWP2_w words ExitCondIprop Hif Hef
                    Htrip with "[] []") as "Hrun".
      { iApply (blocksSound_at_false with "Hbsw"). }
      { iNext. iExact "Hbsw". }
      iApply ("Hrun" $! a with "[$Hpre $Hpc $Hnpc $Hinstrs]").
      { iPureIntro. exact HsLa. }
      iIntros (an) "(%Hexit & Hpc & Hnpc & Hinstrs & HPOST)".
      iApply ("Hk" $! an). iFrame "Hpc Hnpc HPOST".
      iSplit. { iPureIntro. exact Hexit. }
      unfold Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs. iExists words. iFrame "Hinstrs".
    Qed.

    (* the VC pipeline postprocess o replay o postprocess (Contracts.v) is
       sound: each stage is, replay by the refinement layer's replay_sound *)
    Lemma cfg_postprocess_sound (s : SymProp.SymProp [ctx]) :
      SymProp.safe (Katamaran.RiscvPmp.CFGVer.Contracts.cfg_postprocess s) [env] ->
      SymProp.safe s [env].
    Proof.
      unfold Katamaran.RiscvPmp.CFGVer.Contracts.cfg_postprocess.
      intros H. apply postprocess_sound in H.
      apply RiscvPmpIrisInstanceWithContracts.replay_sound in H.
      now apply postprocess_sound in H.
    Qed.

    Lemma sound_scfg_verification_condition_myWP2_w {Γ pre post instrs cexit fuel}
        (words : bv xlenbits -> bv word)
        (* the ALIASES, never a spelled-out tuple.  This is now the SIXTH
           signature caught with a literal `list (Term _ ty_xlenbits * AST)` in
           it (five in VerifierRel.v), and every one of them silently failed to
           track BOTH table columns added since — the word column and then
           AnnotInstr.  The type error always surfaces far from the cause. *)
        {tbl : Katamaran.RiscvPmp.CFGVer.Verifier.SInstrTable (wlctx Γ)}
        {exits : Katamaran.RiscvPmp.CFGVer.Verifier.SExitTable (wlctx Γ)}
        (Hverif : safeE (Katamaran.RiscvPmp.CFGVer.Contracts.cfg_postprocess (
            Katamaran.RiscvPmp.CFGVer.Verifier.scfg_verification_condition
              pre tbl exits fuel post wnil)))
        (ι : Valuation Γ) (ExitCond : iProp Σ)
        (Hif : Katamaran.RiscvPmp.CFGVer.VerifierRel.itable_rel (w := wlctx Γ) instrs tbl ι)
        (Hef : Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx Γ) cexit exits ι) :
      (* The block premise, split as in sound_cexec_triple_addr_myWP2_w.
         Blocks ride in `instrs` and hence in `tbl`, so this is the ONLY thing
         they add at this level. *)
      ⊢ blocksSoundAt false words instrs -∗ ▷ blocksSound words instrs -∗
        ∀ a : RelVal ty_xlenbits,
          asn.interpret pre (ι.["a"∷ty_xlenbits ↦ a]) ∗ ⌜secLeak a⌝ ∗
          pc ↦ᵣ a ∗ (∃ v, nextpc ↦ᵣ v) ∗
          Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs_w words (ai_instr <$> instrs) -∗
          (∀ an,
             ⌜∃ v, an = SyncVal v ∧ Katamaran.RiscvPmp.CFGVer.VerifierRel.exit_hit cexit v = true⌝ ∗
             pc ↦ᵣ an ∗ (∃ v, nextpc ↦ᵣ v) ∗
             Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs_w words (ai_instr <$> instrs) ∗
             (* the exit assertion — see sound_cexec_triple_addr_myWP2 *)
             asn.interpret post (ι.["a"∷ty_xlenbits ↦ a].["an"∷ty_xlenbits ↦ an]) -∗
             ExitCond) -∗
          myWP2_loop ExitCond.
    Proof.
      apply (sound_cexec_triple_addr_myWP2_w (post := post) (fuel := fuel)
               (ι := ι) words ExitCond Hif Hef).
      intros wds.
      apply (safeE_safe env.nil), cfg_postprocess_sound in Hverif.
      (* the world pinned: cfg_postprocess is stated at [ctx], from which
         `apply` cannot recover wnil (MicroSail's symbolic_vcgen_fuel_soundness
         does the same) *)
      apply (LogicalSoundness.psafe_safe (w := wnil)) in Hverif; [|done].
      revert Hverif.
      apply Katamaran.RiscvPmp.CFGVer.VerifierRel.rcfg_verification_condition.
      - easy.
      - constructor.
    Qed.

    (* ---- THE PLACEMENT PREMISE ------------------------------------------
       A block's contract is verified over a symbolic table, and whether that
       table is FAITHFUL to the program depends on the valuation: for a
       base-relative contract (`cfg_placement (blk_contract b) = term_var "p"`)
       it holds only
       when ι sends "p" to the program's actual base.  But ι is chosen
       ANGELICALLY by sexec_block, so blockSound cannot simply assume it -- as
       stated with an unconditional ∀ι it would be FALSE for every
       base-relative block.

       What pins ι is the PRECONDITION.  A segment contract's asn_init_pc says
       `"a" = cfg_placement (blk_contract b) ⊕ off`, and blockSound's premise
       already binds "a" to the entry pc, so the pre determines
       `inst (cfg_placement (blk_contract b)) ι`.  That
       derivation is a separation-logic entailment, which is why this premise
       is an iProp living here rather than a pure Prop in Contracts.v.

       □ because blocksSound is itself persistent: without it the premise would
       not survive the `iIntros "!>"` that introduces it. *)
    Definition blockFaithful
        (* the BLOCK'S OWN annotated program, not the enclosing one -- §2c:
           a block's verification is self-contained, so the table it was
           checked against is faithful to ITS gmap, and the enclosing program
           never appears here. *)
        (ab : list Katamaran.RiscvPmp.CFGVer.Verifier.AnnotInstr)
        (v : bv xlenbits) (b : Katamaran.RiscvPmp.CFGVer.Verifier.BlkAnnot)
        (tbl : Katamaran.RiscvPmp.CFGVer.Verifier.SInstrTable (wlctx (Katamaran.RiscvPmp.CFGVer.Verifier.blk_ctx b))) : iProp Σ :=
      (□ ∀ ι : Valuation (Katamaran.RiscvPmp.CFGVer.Verifier.blk_ctx b),
         asn.interpret (Katamaran.RiscvPmp.CFGVer.Verifier.extend_to_minimal_pre (Katamaran.RiscvPmp.CFGVer.Verifier.cfg_precondition (Katamaran.RiscvPmp.CFGVer.Verifier.blk_contract b))) (ι.["a"∷ty_xlenbits ↦ ty.SyncVal v]) -∗
         ⌜Katamaran.RiscvPmp.CFGVer.VerifierRel.itable_rel (w := wlctx (Katamaran.RiscvPmp.CFGVer.Verifier.blk_ctx b))
             (Katamaran.RiscvPmp.CFGVer.Tables.instrs_of_list v ab) tbl ι
          /\ Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx (Katamaran.RiscvPmp.CFGVer.Verifier.blk_ctx b))
               (blk_exit b ι) (Katamaran.RiscvPmp.CFGVer.Verifier.cfg_exit (Katamaran.RiscvPmp.CFGVer.Verifier.blk_contract b)) ι⌝)%I.

    (* A VALID CONTRACT IS ALL YOU NEED -- the point Emiel made.  Everything
       Iris-level is already in sound_scfg_verification_condition_myWP2; this
       lemma only specialises it at a := SyncVal v and runs it
       against the BLOCK'S OWN annotated program `ab`.

       SELF-CONTAINED, and that is the point (§2c).  The enclosing program does
       not appear: the block's table is faithful to ITS gmap, its memory is ITS
       span, and its own block premise `Hbs` is over `instrs_of_list v ab` -- a
       STRICTLY SMALLER artifact, which is what makes nesting well-founded on
       nesting depth instead of circular.  The old version ran against the
       ENCLOSING program with every block annotation cleared, and was vacuous
       in its block premise -- exactly what foreclosed nesting. *)
    Lemma blockSound_of_vc (words : bv xlenbits -> bv word)
        (ab : list Katamaran.RiscvPmp.CFGVer.Verifier.AnnotInstr)
        (b : Katamaran.RiscvPmp.CFGVer.Verifier.BlkAnnot)
        (tbl : Katamaran.RiscvPmp.CFGVer.Verifier.SInstrTable (wlctx (Katamaran.RiscvPmp.CFGVer.Verifier.blk_ctx b)))
        (Hv : safeE (Katamaran.RiscvPmp.CFGVer.Contracts.cfg_postprocess (Katamaran.RiscvPmp.CFGVer.Verifier.scfg_verification_condition
                 (Katamaran.RiscvPmp.CFGVer.Verifier.extend_to_minimal_pre (Katamaran.RiscvPmp.CFGVer.Verifier.cfg_precondition (Katamaran.RiscvPmp.CFGVer.Verifier.blk_contract b))) tbl (Katamaran.RiscvPmp.CFGVer.Verifier.cfg_exit (Katamaran.RiscvPmp.CFGVer.Verifier.blk_contract b)) (Katamaran.RiscvPmp.CFGVer.Verifier.cfg_fuel (Katamaran.RiscvPmp.CFGVer.Verifier.blk_contract b))
                 (Katamaran.RiscvPmp.CFGVer.Verifier.cfg_postcondition (Katamaran.RiscvPmp.CFGVer.Verifier.blk_contract b)) wnil)))
        (* NO Hexit any more (PLAN-exit-targets.md): the block resumes at its
           contract's own exit term, which is what the VC's run stops at, so
           there is no second description of the resume point to reconcile. *)
        (* the block's code really is what its contract says: ab strips to
           cfg_instrs, so ai_instr <$> instrs_of_list v ab IS blk_span v b *)
        (Hstrip : Katamaran.RiscvPmp.CFGVer.Verifier.strip ab = Katamaran.RiscvPmp.CFGVer.Verifier.cfg_instrs (Katamaran.RiscvPmp.CFGVer.Verifier.blk_contract b))
        (* the blocks this block's OWN program may apply at its entry
           (ai_block only) are justified outright -- they may fire at step 0,
           before any later has been earned.  From an AnnotInstrV list,
           blocksSoundAt_false_of_V. *)
        (Hbs0 : forall v, (⊢ blocksSoundAt false words (Katamaran.RiscvPmp.CFGVer.Tables.instrs_of_list v ab)))
        (* ALL its blocks are justified, and this premise may ASSUME THIS
           BLOCK: a loop is one block whose head carries that same block as
           ai_loop, so its VC's back edge consumes the block's pre (the
           invariant) and produces its post.  Not circular: ai_loop fires only
           once an instruction has run, i.e. under a later -- which is exactly
           what `iLöb` supplies.  For a block with no self-reference the
           assumption is simply ignored (`iIntros "_"`). *)
        (* The Löb hypothesis is `□ ∀ v', blockSound words v' b` -- this
           block at EVERY entry address (decision (c), PLAN-valid-blk-annot
           Phase 3), not just at v: so a re-entry may fire at any address, and
           the conclusion is exactly Adequacy.blkValid's body. *)
        (Hbs : forall v, □ (∀ v', blockSound words v' b) ⊢
                 blocksSound words (Katamaran.RiscvPmp.CFGVer.Tables.instrs_of_list v ab)) :
      (∀ v, blockFaithful ab v b tbl) ⊢ ∀ v, blockSound words v b.
    Proof.
      iIntros "#Hf".
      iLöb as "IH".
      iIntros (v ι ExitCond) "(Hpre & Hpc & Hnpc & Hinstrs) Hk".
      (* Read the faithfulness facts out of the pre WITHOUT consuming it: the
         conclusion is pure, so `∧` (which duplicates the context under iSplit)
         gives both. *)
      iAssert (⌜Katamaran.RiscvPmp.CFGVer.VerifierRel.itable_rel (w := wlctx (Katamaran.RiscvPmp.CFGVer.Verifier.blk_ctx b))
                   (Katamaran.RiscvPmp.CFGVer.Tables.instrs_of_list v ab) tbl ι
               /\ Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx (Katamaran.RiscvPmp.CFGVer.Verifier.blk_ctx b))
                    (blk_exit b ι) (Katamaran.RiscvPmp.CFGVer.Verifier.cfg_exit (Katamaran.RiscvPmp.CFGVer.Verifier.blk_contract b)) ι⌝
              ∧ asn.interpret (Katamaran.RiscvPmp.CFGVer.Verifier.extend_to_minimal_pre (Katamaran.RiscvPmp.CFGVer.Verifier.cfg_precondition (Katamaran.RiscvPmp.CFGVer.Verifier.blk_contract b)))
                  (ι.["a"∷ty_xlenbits ↦ ty.SyncVal v]))%I
        with "[Hpre]" as "[%Hfi Hpre]".
      { iSplit; [ iApply ("Hf" $! v ι with "Hpre") | iExact "Hpre" ]. }
      destruct Hfi as [Hif Hef].
      (* blk_span v b IS ai_instr <$> instrs_of_list v ab: fmap commutes with
         instrs_of_list (Tables.fmap_instrs_of_list), and strip is that fmap. *)
      unfold blk_span. rewrite <- Hstrip.
      unfold Katamaran.RiscvPmp.CFGVer.Verifier.strip. rewrite <- Katamaran.RiscvPmp.CFGVer.Tables.fmap_instrs_of_list.
      (* the block premise for the block's own program: entry blocks now, all
         of them UNDER THE LATER, where the Löb hypothesis is available *)
      iPoseProof (sound_scfg_verification_condition_myWP2_w words Hv ExitCond Hif Hef
                    with "[] []") as "Hrun".
      { iApply (Hbs0 v). }
      { iNext. iApply (Hbs v). iModIntro. iExact "IH". }
      iApply ("Hrun" $! (ty.SyncVal v) with "[$Hpre $Hpc $Hnpc $Hinstrs]").
      (* `⌜secLeak (SyncVal v)⌝` is `v = v` now, not `True`: iFrame no longer
         closes it on the way in (relval-pair). *)
      { iPureIntro. reflexivity. }
      iIntros (an) "(%Hex & Hpc & Hnpc & Hinstrs & Hpost)".
      destruct Hex as (x & -> & Hex).
      apply Katamaran.RiscvPmp.CFGVer.VerifierRel.exit_hit_spec in Hex.
      rewrite Hex.
      iApply "Hk". iFrame.
    Qed.


    Lemma sound_scfg_verification_condition_myWP2 {Γ pre post instrs cexit fuel}
        (* the ALIASES, never a spelled-out tuple.  This is now the SIXTH
           signature caught with a literal `list (Term _ ty_xlenbits * AST)` in
           it (five in VerifierRel.v), and every one of them silently failed to
           track BOTH table columns added since — the word column and then
           AnnotInstr.  The type error always surfaces far from the cause. *)
        {tbl : Katamaran.RiscvPmp.CFGVer.Verifier.SInstrTable (wlctx Γ)}
        {exits : Katamaran.RiscvPmp.CFGVer.Verifier.SExitTable (wlctx Γ)}
        (Hverif : safeE (Katamaran.RiscvPmp.CFGVer.Contracts.cfg_postprocess (
            Katamaran.RiscvPmp.CFGVer.Verifier.scfg_verification_condition
              pre tbl exits fuel post wnil)))
        (ι : Valuation Γ) (ExitCond : iProp Σ)
        (Hif : Katamaran.RiscvPmp.CFGVer.VerifierRel.itable_rel (w := wlctx Γ) instrs tbl ι)
        (Hef : Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx Γ) cexit exits ι)
        (* The block premise.  With the contract in the AnnotInstr payload this
           is the ONLY thing the hook adds at this level: blocks ride in
           `instrs` and hence in `tbl`, so there is no second VC entry point
           and no second triple-level refinement.  The bridges derive it from
           the sealed contract's annotsValid (blocksSound_of_annotsValid). *)
        (Hbs : forall words : bv xlenbits -> bv word,
                 ⊢ blocksSound words instrs) :
      ⊢ ∀ a : RelVal ty_xlenbits,
          asn.interpret pre (ι.["a"∷ty_xlenbits ↦ a]) ∗ ⌜secLeak a⌝ ∗
          pc ↦ᵣ a ∗ (∃ v, nextpc ↦ᵣ v) ∗
          Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs (ai_instr <$> instrs) -∗
          (∀ an,
             ⌜∃ v, an = SyncVal v ∧ Katamaran.RiscvPmp.CFGVer.VerifierRel.exit_hit cexit v = true⌝ ∗
             pc ↦ᵣ an ∗ (∃ v, nextpc ↦ᵣ v) ∗
             Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs (ai_instr <$> instrs) ∗
             (* the exit assertion — see sound_cexec_triple_addr_myWP2 *)
             asn.interpret post (ι.["a"∷ty_xlenbits ↦ a].["an"∷ty_xlenbits ↦ an]) -∗
             ExitCond) -∗
          myWP2_loop ExitCond.
    Proof.
      apply (sound_cexec_triple_addr_myWP2 (post := post) (fuel := fuel)
               (ι := ι) ExitCond Hif Hef);
        [|exact Hbs].
      intros words.
      apply (safeE_safe env.nil), cfg_postprocess_sound in Hverif.
      (* the world pinned: cfg_postprocess is stated at [ctx], from which
         `apply` cannot recover wnil (MicroSail's symbolic_vcgen_fuel_soundness
         does the same) *)
      apply (LogicalSoundness.psafe_safe (w := wnil)) in Hverif; [|done].
      revert Hverif.
      apply Katamaran.RiscvPmp.CFGVer.VerifierRel.rcfg_verification_condition.
      - easy.
      - constructor.
    Qed.

End AdequacyTools.

(* A BLOCK THAT IS SOUND WHEREVER IT IS PLACED (PLAN-valid-blk-annot.md §1a,
   Phase 2).  A closed Prop (∀ Σ GS, decision V4), so it can ride in an
   annotation as a plain proof field (AnnotInstrV, Phase 3).

   Address-free because a contract carries no load address (its old
   cfg_init_addr field is gone, PLAN-valid-blk-annot §8.2): a block resumes
   at its contract's exit term, pinned by the precondition to the entry pc.

   UNCONDITIONAL in v (decision B, 2026-09-25): no no-wrap premise.  The
   block's own precondition must rule out wrapping -- a generated segment's
   does, via gen_base_bound (`unsigned base + 4·len ≤ lenAddr`, lenAddr = 2^12),
   which GenCompose.seg_pre_bound reads off.  So the firing site needs no
   address arithmetic at all.  Worked example:
   Example/CountdownRecResult.cdRecBlk_valid. *)
Definition blkValid (b : Katamaran.RiscvPmp.CFGVer.Verifier.BlkAnnot) : Prop :=
  forall Σ (GS : sailGS2 Σ) (words : bv xlenbits -> bv word) (v : bv xlenbits),
    ⊢ @blockSound Σ GS words v b.

(* ---- A TOP-LEVEL PROGRAM'S ANNOTATIONS ARE VALID --------------------------
   (PLAN-valid-blk-annot.md Phase 4.)  The condition sealed inside
   EndToEnd.ValidCFGVerifierContract, replacing its old Iris-level blocksSound
   conjunct: every ai_block carries a valid block, and there is NO re-entry
   (ai_loop) at top level -- a whole program re-entering itself would need
   its own contract faithful at every address, which the bridges do not have
   (Phase 4 Decision 1).  A pure Prop, so it says nothing about Σ, words or
   the load address; blocksSound_of_annotsValid turns it into the executor's
   premise at any base. *)
Definition annotsValid (l : list Katamaran.RiscvPmp.CFGVer.Verifier.AnnotInstr) : Prop :=
  List.Forall (fun ai => Katamaran.RiscvPmp.CFGVer.Verifier.ai_loop ai = None /\
                         forall b, Katamaran.RiscvPmp.CFGVer.Verifier.ai_block ai = Some b -> blkValid b) l.

(* A program with no block annotations of either kind: every example written
   as a plain list of ASTs (with Verifier.ai_block_none_of_AST). *)
Lemma annotsValid_of_none (l : list Katamaran.RiscvPmp.CFGVer.Verifier.AnnotInstr) :
  List.Forall (fun ai => Katamaran.RiscvPmp.CFGVer.Verifier.ai_fire true ai = None) l -> annotsValid l.
Proof.
  apply List.Forall_impl. intros ai H. unfold Katamaran.RiscvPmp.CFGVer.Verifier.ai_fire in H.
  destruct (Katamaran.RiscvPmp.CFGVer.Verifier.ai_block ai); [discriminate|].
  split; [exact H | intros b Hb; discriminate].
Qed.

(* ---- blocksSound FROM ANNOTATIONS THAT CARRY THEIR VALIDITY --------------
   (PLAN-valid-blk-annot.md Phase 3.)  For a program written as
   `map (eraseV c) LV`, every block the executor can fire is justified by the
   annotation itself: an ai_block by its vb_ok proof (blkValid, at whatever
   address it fires -- decision B), a re-entry by the Löb hypothesis about
   selfBlk c (at any address -- decision (c)).  A lookup only needs "this is
   an element of the list" (instrs_of_list_elem_of), so there is no key
   inversion, and a block may sit anywhere in the program. *)
Section ValidAnnot.
  Context {Σ} {GS : sailGS2 Σ}.

  (* At a contract's entry only ai_block annotations fire, and each carries
     its own proof. *)
  Lemma blocksSoundAt_false_of_V {R} (c : @Katamaran.RiscvPmp.CFGVer.Verifier.CFGVerifierContract R)
      (words : bv xlenbits -> bv word) (base : bv xlenbits)
      (LV : list (Katamaran.RiscvPmp.CFGVer.Verifier.AnnotInstrV blkValid)) :
    ⊢ blocksSoundAt false words
        (Katamaran.RiscvPmp.CFGVer.Tables.instrs_of_list base (List.map (Katamaran.RiscvPmp.CFGVer.Verifier.eraseV c) LV)).
  Proof.
    iIntros "!>" (v ai b) "%Hlk %Hb".
    apply instrs_of_list_elem_of, List.in_map_iff in Hlk as (a & <- & _).
    unfold Katamaran.RiscvPmp.CFGVer.Verifier.ai_fire, Katamaran.RiscvPmp.CFGVer.Verifier.eraseV in Hb. cbn in Hb.
    destruct (Katamaran.RiscvPmp.CFGVer.Verifier.aiv_block a) as [x|]; cbn in Hb; [|discriminate].
    injection Hb as <-. iApply (Katamaran.RiscvPmp.CFGVer.Verifier.vb_ok x Σ GS words v).
  Qed.

  (* All blocks, re-entries included, given the Löb hypothesis about the
     enclosing contract at every address. *)
  Lemma blocksSound_of_V {R} (c : @Katamaran.RiscvPmp.CFGVer.Verifier.CFGVerifierContract R)
      (words : bv xlenbits -> bv word) (base : bv xlenbits)
      (LV : list (Katamaran.RiscvPmp.CFGVer.Verifier.AnnotInstrV blkValid)) :
    □ (∀ v', blockSound words v' (Katamaran.RiscvPmp.CFGVer.Verifier.selfBlk c))
    ⊢ blocksSound words (Katamaran.RiscvPmp.CFGVer.Tables.instrs_of_list base (List.map (Katamaran.RiscvPmp.CFGVer.Verifier.eraseV c) LV)).
  Proof.
    iIntros "#IH !>" (v ai b) "%Hlk %Hb".
    apply instrs_of_list_elem_of, List.in_map_iff in Hlk as (a & <- & _).
    unfold Katamaran.RiscvPmp.CFGVer.Verifier.ai_fire, Katamaran.RiscvPmp.CFGVer.Verifier.eraseV in Hb. cbn in Hb.
    destruct (Katamaran.RiscvPmp.CFGVer.Verifier.aiv_block a) as [x|]; cbn in Hb.
    - injection Hb as <-. iApply (Katamaran.RiscvPmp.CFGVer.Verifier.vb_ok x Σ GS words v).
    - destruct (Katamaran.RiscvPmp.CFGVer.Verifier.aiv_loop a); [|discriminate].
      injection Hb as <-. iApply "IH".
  Qed.

  (* The executor's premise, from the sealed top-level condition. *)
  Lemma blocksSound_of_annotsValid (words : bv xlenbits -> bv word)
      (base : bv xlenbits) (l : list Katamaran.RiscvPmp.CFGVer.Verifier.AnnotInstr) :
    annotsValid l -> ⊢ blocksSound words (Katamaran.RiscvPmp.CFGVer.Tables.instrs_of_list base l).
  Proof.
    intros Hl. iIntros "!>" (v ai b) "%Hlk %Hb".
    apply instrs_of_list_elem_of in Hlk.
    unfold annotsValid in Hl. rewrite List.Forall_forall in Hl.
    destruct (Hl _ Hlk) as [Hloop Hblk].
    unfold Katamaran.RiscvPmp.CFGVer.Verifier.ai_fire in Hb. destruct (Katamaran.RiscvPmp.CFGVer.Verifier.ai_block ai) as [b'|] eqn:E.
    - injection Hb as <-. iApply (Hblk b' eq_refl Σ GS words v).
    - rewrite Hloop in Hb. discriminate.
  Qed.
End ValidAnnot.
