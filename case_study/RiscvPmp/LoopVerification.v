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
     MicroSail.ShallowExecutor
     MicroSail.ShallowSoundness
     MicroSail.RefineExecutor
     MicroSail.Soundness
     RiscvPmp.Machine
     RiscvPmp.Logic
     RiscvPmp.Sig
     RiscvPmp.IrisModel
     RiscvPmp.IrisInstance
     RiscvPmp.Model
     RiscvPmp.trace
     RiscvPmp.Contracts.

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
Import RiscvPmpIrisBase.
Import RiscvPmpModel2.
Import RiscvPmpIrisInstance.
Import RiscvPmpValidContracts.
Import RiscvPmpIrisInstancePredicates.

Import RiscvPmpSignature.
Import RiscvPmpProgramLogic.

(* We need to provide a SepContract with filled in Δ, τ so we get a more
       computable sep_contract_step version. TODO: maybe fix this directly in
       Contracts.v? *)
#[local] Definition sep_contract_step : SepContractFun step := sep_contract_step.

(* ArchState defines a record that contains all logic variables we will need for the
   LoopVerification. These are based on the logic variables of the step contract,
   as the loop is of the form: step();; loop(). *)
Module ArchState.
  Import env.notations.

  Record MState :=
    mkMState
      { mtvec      : Xlenbits
      ; pmpentries : list (Pmpcfg_ent * Xlenbits)
      ; mpp        : Privilege
      ; mcause     : Xlenbits
      ; mscratch   : Xlenbits
      ; mepc       : Xlenbits
      ; mpie       : bool
      ; mie        : bool
      ; mideleg    : Minterrupts
      ; medeleg    : RMedeleg
      }.

  Record SState :=
    mkSState
      { stvec    : Xlenbits
      ; spp      : Privilege
      ; scause   : Xlenbits
      ; sscratch : Xlenbits
      ; sepc     : Xlenbits
      ; spie     : bool
      ; sie      : bool
      }.

  Record ArchState :=
    mkArchState
      { m      : Privilege
      ; mstate : MState
      ; sstate : SState
      ; pc     : Xlenbits
      }.

  Definition archstate_valuation (archstate : ArchState) : Valuation (sep_contract_logic_variables sep_contract_step) :=
    let ms := mstate archstate in
    let ss := sstate archstate in
    [env].["m"∷ty.enum privilege ↦ m archstate].["mtvec"∷ty.bvec 32 ↦ mtvec ms]
    .["stvec"∷ty.bvec 32 ↦ stvec ss]
    .["pmpentries"∷ty.list (ty.prod (ty.record rpmpcfg_ent) (ty.bvec 32)) ↦ pmpentries ms]
    .["mpp"∷ty.enum privilege ↦ mpp ms].["spp"∷ty.enum privilege ↦ spp ss]
    .["pc"∷ty.bvec 32 ↦ pc archstate].["mcause"∷ty.bvec 32 ↦ mcause ms]
    .["mscratch"∷ty.bvec 32 ↦ mscratch ms].["mepc"∷ty.bvec 32 ↦ mepc ms]
    .["scause"∷ty.bvec 32 ↦ scause ss].["sscratch"∷ty.bvec 32 ↦ sscratch ss]
    .["sepc"∷ty.bvec 32 ↦ sepc ss].["mpie"∷ty.bool ↦ mpie ms]
    .["spie"∷ty.bool ↦ spie ss].["mie"∷ty.bool ↦ mie ms]
    .["sie"∷ty.bool ↦ sie ss]
    .["mideleg"∷ty_Minterrupts ↦ mideleg ms]
    .["medeleg"∷ty_Medeleg ↦ medeleg ms].

  Definition archstate_update_pc (archstate : ArchState) (pc' : Xlenbits) : ArchState :=
    mkArchState (m archstate) (mstate archstate) (sstate archstate) pc'.

  Definition archstate_update_m (archstate : ArchState) (m' : Privilege) : ArchState :=
    mkArchState m' (mstate archstate) (sstate archstate) (pc archstate).
End ArchState.

(* We only import the record type and the valuation conversion function.
   Record fields will need the qualified name, for example: ArchState.mepc to access
   the mepc value. This avoids naming conflicts with the registers. *)
Import ArchState (ArchState, archstate_valuation, archstate_update_pc, archstate_update_m).

Section Loop.
  Context `{sg : sailGS Σ} {rG : trivGS Σ}.
  Definition step_sem_contract :=
    Eval simpl in ValidContractSemCurried fun_step sep_contract_step.

  (* Some Iris Proof Mode tactics like (iFrame) try very hard to solve some
     goals. Unfortunately that can result in definitions being unfolded.
     For example the [frame_instances.frame_big_sepL_cons] instance for the
     [Frame] typeclass will look for [IsCons liveAddrs _ _] which will unfold
     [liveAddrs] because the concrete value can indeed be unified with [cons].
     We make liveAddrs opaque to prevent this.
   *)
  Local Opaque liveAddrs.

  (* TODO: remove? Never used? *)
  Definition PmpEntry : Set := Pmpcfg_ent * Z.
  Definition PtstosPred : Type := Privilege -> Privilege -> Z -> Z -> list PmpEntry -> list PmpEntry -> Privilege -> Z -> Z -> iProp Σ.

  (* For the LoopVerification, we always start with a precondition that needs to
     satisfy the precondition of the step function. We directly interpret this
     from the contract definition of step. *)
  Definition Step_pre (archstate : ArchState) : iProp Σ :=
    asn.interpret (sep_contract_precondition sep_contract_step) (archstate_valuation archstate).

  Local Notation "r '↦' val" := (reg_pointsTo r val) (at level 70).

  Section TransitionTargets.
    (* TransitionTargets defines all targets which we can transition to during
       execution of the machine. These corresponds to the individual disjuncts
       of the postcondition of the step function. *)
    Definition Disjunct := Assertion (ctx.snoc (sep_contract_logic_variables sep_contract_step) (sep_contract_result sep_contract_step∷ty.unit)).
    Record Disjuncts := mkDisjuncts
      { D_Execution : Disjunct
      ; D_M_CSRMod  : Disjunct
      ; D_M_Trap    : Disjunct
      ; D_MRET      : Disjunct
      ; D_SRET      : Disjunct
      }.

    (* We define an extract function that returns the disjuncts, or
       None in case the pattern used doesn't match. *)
    Definition disjuncts : option Disjuncts :=
      match sep_contract_postcondition sep_contract_step with
      | asn.or exe (asn.or m_csrmod (asn.or m_trap (asn.or mret sret))) =>
          Some (mkDisjuncts exe m_csrmod m_trap mret sret)
      | _ => None
      end.

    (* This lemma is a sanity check, if it fails, it most likely means the
       step function was updated so that there are more/less disjuncts and
       the pattern of the disjuncts definition wasn't updated accordingly. *)
    Lemma extract_disjuncts_should_work : disjuncts ≠ None.
    Proof. by simpl. Qed.

    (* We now define convenient names to use later in this file, without needing
       to talk about disjunct anymore. Each definition takes some ArchState and
       interprets the relevant disjunct with those archstate. In case the disjuncts
       were not found, we simply use True. *)
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
              ((∃ p, reg_pointsTo cur_privilege p) ∗ (∃ es, interp_pmp_entries es))%I
              (FunDef init_model)
              (fun _ _ => reg_pointsTo cur_privilege Machine ∗ (∃ es, interp_pmp_entries es))%I.

  Lemma valid_step_contract : ⊢ ValidContractSem fun_step sep_contract_step.
  Proof.
    iApply (sound $! _ _ step).
    exact foreignSem.
    exact lemSem.
    unfold ProgLog.ValidContractCEnv.
    intros Δ τ f c H.
    destruct (ValidContracts f H) as [fuel Hc].
    apply RiscvPmpShallowSoundness.shallow_vcgen_fuel_soundness with (fuel := fuel).
    now apply RiscvPmpSymbolicSoundness.symbolic_vcgen_fuel_soundness.
  Qed.

  Lemma valid_init_model_contract : ⊢ ValidContractSem fun_init_model sep_contract_init_model.
  Proof.
    iApply (sound $! _ _ init_model).
    exact foreignSem.
    exact lemSem.
    unfold ProgLog.ValidContractCEnv.
    intros Δ τ f c H.
    destruct (ValidContracts f H) as [fuel Hc].
    apply RiscvPmpShallowSoundness.shallow_vcgen_fuel_soundness with (fuel := fuel).
    now apply RiscvPmpSymbolicSoundness.symbolic_vcgen_fuel_soundness.
  Qed.

  Import env.notations.

  Lemma valid_step_semTriple :
    ⊢ semTriple_step.
  Proof.
    iIntros (archstate) "H".
    iApply (semWP_mono with "[-]").
    iApply (valid_step_contract with "H").
    iIntros ([[]|e] _); last auto.
    iIntros "H". iExact "H".
  Time Qed.

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
    iIntros (? ?) "(_ & Hcp & Hin)".
    iSplitL "Hcp"; iAssumption.
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
    (Step_pre archstate ∗ ▷ (Step_exit archstate -∗ WP_loop))%I.

  Definition semTriple_loop : iProp Σ :=
    (∀ (archstate : ArchState),
        semTriple env.nil (loop_pre archstate)
                  (FunDef loop)
                  (fun _ _ => True))%I.

  Lemma valid_semTriple_loop : ⊢ semTriple_loop.
  Proof.
    iLöb as "H".
    iIntros (archstate) "(HStep & HK)".
    iApply (semWP_seq (call step) (call loop)).
    iApply semWP_call_inline_later.
    iApply (semWP_mono with "[HStep]").
    iApply (valid_step_semTriple with "HStep").
    iModIntro.
    iIntros ([v|e] δ); last (iIntros "_"; by rewrite semWP_fail).
    iIntros "[HRes | HRes]".
    iApply (semWP_call_inline loop _).
    - cbn.
      iDestruct "HRes" as "(Hacc & Hgprs & Hpmp & Hmie & Hmip & (%npc & Hpc & Hnpc) & Hmtvec & Hmepc & Hmideleg & Hmedeleg & Hmscratch & Hmcause & HRes)".
      iDestruct "HRes" as "[HRes | HRes]".
      + iDestruct "HRes" as "([%Hm _] & Hcp & Hstvec & Hmstatus & Hsepc & Hsscratch & Hscause)".
        iApply ("H" $! (archstate_update_pc archstate npc)).
        unfold loop_pre.
        iSplitR "HK".
        * unfold Step_pre; cbn.
          rewrite ?Hm.
          now iFrame "Hacc Hgprs Hpmp Hmie Hmip Hcp Hpc Hnpc Hmtvec Hstvec Hmstatus Hmepc Hsepc Hmideleg Hmedeleg Hmscratch Hmcause Hsscratch Hscause".
        * iModIntro. iIntros "Hexit".
          iApply "HK". by iApply (Step_exit_update_pc with "Hexit").
      + iDestruct "HRes" as "([%Hm _] & [%m' (Hcp & [%Hm' _] & [%stvec' Hstvec] & [%spp' [%spie' [%sie' Hmstatus]]] & [%sepc' Hsepc] & [%sscratch' Hsscratch] & [%scause' Hscause])])".
        iPoseProof (interp_pmp_addr_access_not_machine _ _ _ Hm Hm' with "Hacc") as "Hacc".
        destruct archstate as [? ms ? ?]; cbn.
        iApply ("H" $! (ArchState.mkArchState m' ms (ArchState.mkSState stvec' spp' scause' sscratch' sepc' spie' sie') npc)).
        unfold loop_pre.
        iSplitR "HK".
        * unfold Step_pre; cbn.
          now iFrame "Hacc Hgprs Hpmp Hmie Hmip Hcp Hpc Hnpc Hmtvec Hstvec Hmstatus Hmepc Hsepc Hmideleg Hmedeleg Hmscratch Hmcause Hsscratch Hscause".
        * iModIntro. iIntros "Hexit". iApply "HK".
          by iApply (Step_exit_mstate_determined with "Hexit").
    - iApply (semWP_call_inline loop _).
      iApply (semWP_mono with "[HK HRes]").
      { iApply ("HK" with "HRes"). }
      iIntros ([] ?); auto.
  Qed.
End Loop.
