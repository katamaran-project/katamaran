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

From Stdlib Require Import
     Lists.List.
From Katamaran Require Import
     Bitvector
     Environment
     Iris.Instance
     Iris.Base
     Program
     Semantics
     Sep.Hoare
     Sep.Logic
     MicroSail.ShallowExecutor
     MicroSail.ShallowSoundness
     MicroSail.RefineExecutor
     MicroSail.Soundness
     RiscvPmp.Machine
     RiscvPmp.Logic
     RiscvPmp.PmpCheck
     RiscvPmp.Sig
     RiscvPmp.IrisModelBinary
     RiscvPmp.IrisInstanceBinary
     RiscvPmp.ModelBinary
     RiscvPmp.Contracts
     RiscvPmp.LoopVerification.

From iris.base_logic Require lib.gen_heap lib.iprop.
From iris.base_logic Require Export invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac.
From iris.program_logic Require Import weakestpre adequacy.
From iris.proofmode Require Import string_ident proofmode.

Set Implicit Arguments.
Import ListNotations.
Import RiscvPmpSpecification.
Import RiscvPmpProgram.
Import RiscvPmpIrisBase2.
Import RiscvPmpModel2.
Import RiscvPmpIrisInstance2.
Import RiscvPmpValidContracts.
Import IrisInstance.RiscvPmpIrisInstancePredicates.
Import RiscvPmpIrisInstancePredicates2.
Import RiscvPmpProgramLogic.ProgLog.
Import RiscvPmpShallowSoundness.
Import RiscvPmpSymbolicSoundness.

Import RiscvPmpSignature.

Import ArchState (ArchState, archstate_valuation, archstate_update_pc).

Section Loop.
  Context `{sg : sailGS2 Σ}.

  Definition step_sem_contract :=
    Eval cbn  in ValidContractSemCurried fun_step sep_contract_step.

  Definition Step_pre (archstate : ArchState) : iProp Σ :=
    asn.interpret (sep_contract_precondition sep_contract_step) (archstate_valuation archstate).

  Local Notation "r '↦' val" := (reg_pointsTo21 r val) (at level 70).
  (* Some Iris Proof Mode tactics like (iFrame) try very hard to solve some
     goals. Unfortunately that can result in definitions being unfolded.
     For example the [frame_instances.frame_big_sepL_cons] instance for the
     [Frame] typeclass will look for [IsCons liveAddrs _ _] which will unfold
     [liveAddrs] because the concrete value can indeed be unified with [cons].
     We make liveAddrs opaque to prevent this.
   *)
  Local Opaque liveAddrs.

  Definition PmpEntry : Set := Pmpcfg_ent * Z.
  Definition PtstosPred : Type := Privilege -> Privilege -> Z -> Z -> list PmpEntry -> list PmpEntry -> Privilege -> Z -> Z -> iProp Σ.

  Section TransitionTargets.
    Definition extract_disjunct (archstate : ArchState) (f : Disjuncts -> Disjunct) : iProp Σ :=
      match disjuncts with
      | Some ds => asn.interpret (f ds) (env.snoc (archstate_valuation archstate) (_∷ty.unit) tt)
      | None    => True
      end.

    Definition Execution (archstate : ArchState) : iProp Σ :=
      extract_disjunct archstate D_Execution.
    Definition M_CSRMod (archstate : ArchState) : iProp Σ :=
      extract_disjunct archstate D_M_CSRMod.
    Definition M_Trap (archstate : ArchState) : iProp Σ :=
      extract_disjunct archstate D_M_Trap.
    Definition MRET (archstate : ArchState) : iProp Σ :=
      extract_disjunct archstate D_MRET.
    Definition SRET (archstate : ArchState) : iProp Σ :=
      extract_disjunct archstate D_SRET.
    (* Step_post is not a "TransitionTarget" but simply groups the possibilities
       back together using disjunction. *)
    Definition Step_post (archstate : ArchState) : iProp Σ :=
      Execution archstate
      ∨ M_CSRMod archstate
      ∨ M_Trap archstate
      ∨ MRET archstate
      ∨ SRET archstate.

    Definition Step_exit (archstate : ArchState) : iProp Σ :=
      M_CSRMod archstate
      ∨ M_Trap archstate
      ∨ MRET archstate
      ∨ SRET archstate.

  End TransitionTargets.

  Definition semTriple_step : iProp Σ :=
    (∀ (archstate : ArchState),
        semTriple env.nil (Step_pre archstate)
                  (FunDef step)
                  (fun _ _ => Step_post archstate))%I.

  Definition semTriple_init_model : iProp Σ :=
    semTriple env.nil
              ((∃ p, reg_pointsTo21 cur_privilege p) ∗ (∃ es, interp_pmp_entries es))%I
              (FunDef init_model)
              (fun _ _ => reg_pointsTo21 cur_privilege Machine ∗ (∃ es, interp_pmp_entries es))%I.

  Lemma valid_step_contract : ⊢ ValidContractSem fun_step sep_contract_step.
  Proof.
    iApply (sound $! _ _ step).
    exact foreignSem.
    exact lemSem.
    unfold ValidContractCEnv.
    intros.
    pose (ValidContracts f H) as Hc.
    destruct Hc as [fuel Hc].
    apply shallow_vcgen_fuel_soundness with (fuel := fuel).
    now apply symbolic_vcgen_fuel_soundness.
  Qed.

  Lemma valid_init_model_contract : ⊢ ValidContractSem fun_init_model sep_contract_init_model.
  Proof.
    iApply (sound $! _ _ init_model).
    exact foreignSem.
    exact lemSem.
    unfold ValidContractCEnv.
    intros.
    pose (ValidContracts f H) as Hc.
    destruct Hc as [fuel Hc].
    apply shallow_vcgen_fuel_soundness with (fuel := fuel).
    now apply symbolic_vcgen_fuel_soundness.
  Qed.

  Import env.notations.

  Lemma valid_step_semTriple :
    ⊢ semTriple_step.
  Proof.
    iIntros (archstate) "H".
    iApply (semWP2_mono with "[-]").
    iApply (valid_step_contract with "H").
    iIntros ([[]|e1] δ1 v2 δ2) "(<- & <- & H)"; last auto.
    iSplit; first done. iSplit; first done. iExact "H".
  Qed.

  Lemma init_model_iprop : ⊢ semTriple_init_model.
  Proof.
    iApply (@iris_rule_consequence _ _ _ _ _ env.nil
             ((∃ p : Privilege, cur_privilege ↦ p) ∗
              (∃ es : list PmpEntryCfg, interp_pmp_entries es))
             _ _ _ fun_init_model _ _)%I.
    iApply valid_init_model_contract.
    Unshelve.
    cbn.
    iIntros "(Hcp & Hin)".
    iSplitL "Hcp"; iAssumption.
    cbn.
    iIntros (v δ) "H".
    iDestruct "H" as "([-> _] & Hcp & Hpmp)".
    iFrame "Hcp Hpmp".
    constructor.
  Qed.

  Lemma Step_exit_mstate_determined (a a' : ArchState) :
    ArchState.m a ≠ Machine -> ArchState.m a' ≠ Machine ->
    ArchState.mstate a = ArchState.mstate a' ->
    Step_exit a ⊢ Step_exit a'.
  Proof.
    destruct a as [m ms ss pc0], a' as [m' ms' ss' pc0']; cbn; intros Hm Hm' <-.
    unfold Step_exit, M_CSRMod, M_Trap, MRET, SRET, extract_disjunct; cbn.
    iIntros "[H | [H | [H | H]]]".
    - (* M_CSRMod *)
      iDestruct "H" as "(_ & _ & _ & [%Heq _] & _)".
      exfalso; apply Hm; exact Heq.
    - (* M_Trap *)
      iRight; iLeft.
      iDestruct "H" as "(Hpaa & H)".
      iSplitL "Hpaa"; first by iApply (interp_pmp_addr_access_not_machine with "Hpaa").
      destruct m, m'; try congruence; iExact "H".
    - (* MRET *)
      iDestruct "H" as "(_ & _ & _ & [%Heq _] & _)".
      exfalso; apply Hm; exact Heq.
    - (* SRET *)
      iDestruct "H" as "(_ & _ & _ & [%Heq _] & _)".
      exfalso; apply Hm; exact Heq.
  Qed.

  Lemma Step_exit_update_pc (a : ArchState) (pc' : Xlenbits) :
    Step_exit (archstate_update_pc a pc') ⊢ Step_exit a.
  Proof.
    destruct a as [m ms ss pc0].
    unfold archstate_update_pc, Step_exit, M_CSRMod, M_Trap, MRET, SRET, extract_disjunct.
    destruct m; cbn; iIntros "H"; iExact "H".
  Qed.

  Definition loop_pre (archstate : ArchState) : iProp Σ :=
    (Step_pre archstate ∗ ▷ (Step_exit archstate -∗ WP2_loop))%I.

  Definition semTriple_loop : iProp Σ :=
    (∀ (archstate : ArchState),
        semTriple env.nil (loop_pre archstate)
                  (FunDef loop)
                  (fun _ _ => True))%I.

  Lemma valid_semTriple_loop : ⊢ semTriple_loop.
  Proof.
    iLöb as "H".
    iIntros (archstate) "(HStep & HK)".
    iApply (semWP2_seq (call step) (call step) (call loop) (call loop)).
    iApply semWP2_call_inline_later.
    iApply (semWP2_mono with "[HStep]").
    iApply (valid_step_semTriple with "HStep").
    iModIntro.
    iIntros ([v|e] δ1 v2 δ2) "(<- & <- & HRes)"; last now iApply semWP2_fail.
    iDestruct "HRes" as "[HRes | HRes]".
    - iApply (semWP2_call_inline loop _).
      cbn.
      iDestruct "HRes" as "(Hacc & Hgprs & Hpmp & Hmie & Hmip & (%npc & Hpc & Hnpc) & Hmtvec & Hmepc & Hmideleg & Hmedeleg & Hmscratch & Hmcause & HRes)".
      iDestruct "HRes" as "[HRes | HRes]".
      + iDestruct "HRes" as "([%Hm _] & Hcp & Hstvec & Hmstatus & Hsepc & Hsscratch & Hscause)".
        iApply (semWP2_mono with "[-]").
        { iApply ("H" $! (archstate_update_pc archstate npc)).
          unfold loop_pre.
          iSplitR "HK".
          * unfold Step_pre; cbn.
            rewrite ?Hm.
            now iFrame "Hacc Hgprs Hpmp Hmie Hmip Hcp Hpc Hnpc Hmtvec Hstvec Hmstatus Hmepc Hsepc Hmideleg Hmedeleg Hmscratch Hmcause Hsscratch Hscause".
          * iModIntro. iIntros "Hexit".
            iApply "HK". by iApply (Step_exit_update_pc with "Hexit"). }
        iIntros (? ? ? ?) "(<- & <- & _)"; repeat iSplit; auto.
        by case_match.
      + iDestruct "HRes" as "([%Hm _] & [%m' (Hcp & [%Hm' _] & [%stvec' Hstvec] & [%spp' [%spie' [%sie' Hmstatus]]] & [%sepc' Hsepc] & [%sscratch' Hsscratch] & [%scause' Hscause])])".
        iPoseProof (interp_pmp_addr_access_not_machine _ _ _ Hm Hm' with "Hacc") as "Hacc".
        destruct archstate as [? ms ? ?]; cbn.
        iApply (semWP2_mono with "[-]").
        { iApply ("H" $! (ArchState.mkArchState m' ms (ArchState.mkSState stvec' spp' scause' sscratch' sepc' spie' sie') npc)).
          unfold loop_pre.
          iSplitR "HK".
          * unfold Step_pre; cbn.
            now iFrame "Hacc Hgprs Hpmp Hmie Hmip Hcp Hpc Hnpc Hmtvec Hstvec Hmstatus Hmepc Hsepc Hmideleg Hmedeleg Hmscratch Hmcause Hsscratch Hscause".
          * iModIntro. iIntros "Hexit". iApply "HK".
            by iApply (Step_exit_mstate_determined with "Hexit"). }
        iIntros (? ? ? ?) "(<- & <- & _)"; repeat iSplit; auto.
        by case_match.
    - iApply (semWP2_call_inline loop _).
      iApply (semWP2_mono with "[HK HRes]").
      { iApply ("HK" with "HRes"). }
      iIntros ([] ? ? ?) "(<- & <-)"; auto.
  Qed.
End Loop.
