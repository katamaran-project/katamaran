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
     Lists.List.
From Katamaran Require Import
     Bitvector
     Environment
     Iris.Instance
     Iris.Base
     Program
     Semantics
     Sep.Hoare
     Specification
     MicroSail.ShallowExecutor
     MicroSail.ShallowSoundness
     MicroSail.RefineExecutor
     MicroSail.Soundness
     RiscvPmp.Machine
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
From iris.proofmode Require Import string_ident tactics.

Set Implicit Arguments.
Import ListNotations.
Import RiscvPmpSpecification.
Import RiscvPmpProgram.
Import RiscvPmpIrisBase.
Import RiscvPmpModel2.
Import RiscvPmpModel2.RiscvPmpIrisInstance.
Import RiscvPmpValidContracts.
Import RiscvPmpIrisInstancePredicates.

Import RiscvPmpSignature.
Module Import RiscvPmpShallowExecutor :=
  MakeShallowExecutor RiscvPmpBase RiscvPmpSignature RiscvPmpProgram DefaultFailLogic RiscvPmpSpecification.

Module Import RiscvPmpShallowSoundness := MakeShallowSoundness RiscvPmpBase RiscvPmpSignature RiscvPmpProgram DefaultFailLogic RiscvPmpSpecification RiscvPmpShallowExecutor RiscvPmpProgramLogic.

Module Import RiscvPmpSymbolic := MakeSymbolicSoundness RiscvPmpBase RiscvPmpSignature RiscvPmpProgram DefaultFailLogic RiscvPmpSpecification RiscvPmpShallowExecutor RiscvPmpExecutor.

Section Loop.
  Context `{sg : sailGS Σ} {rG : trivGS Σ}.
  Definition step_sem_contract :=
    Eval simpl in ValidContractSemCurried fun_step sep_contract_step.

  Local Notation "r '↦' val" := (reg_pointsTo r val) (at level 70).
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

  (* TODO: added some parameters because the interp_pmp_addr_access predicate can get
              "out of sync" with the current state of the machine.

              Might sound odd, but for a given configuration and privilege mode we will
              still have that pmp_addr_access holds, however, it won't match up with
              the current live config (represented by interp_pmp_entries) and so
              contracts regarding PMP checks will have an unsatisfiable precondition
              (i.e., we will not be granted access with an "out of sync" pmp_addr_access
               predicate).

              Maybe sketch a situation that showcases this? *)

  Definition Step_pre (m : Privilege) (h i : Xlenbits) (mpp : Privilege) (entries : list (Pmpcfg_ent * Xlenbits)) :=
    (                   pc            ↦ i                ∗
     (∃ npc : Xlenbits, nextpc        ↦ npc)             ∗
     (∃ mpie mie,       mstatus       ↦ {| MPP := mpp; MPIE := mpie; MIE := mie |}) ∗
                        interp_pmp_addr_access (mG := sailGS_memGS) liveAddrs mmioAddrs entries m ∗
                        interp_gprs ∅ ∗
                        cur_privilege ↦ m                ∗
                        mtvec         ↦ h                ∗
     (∃ mc : Xlenbits,  mcause        ↦ mc)              ∗
     (∃ mi,            mip            ↦ mi)              ∗
     (∃ mi,            mie            ↦ mi)              ∗
     (∃ ms : Xlenbits,  mscratch      ↦ ms)              ∗
     (∃ v : Xlenbits,   mepc          ↦ v)               ∗
                        interp_pmp_entries entries)%I.

  Definition Execution (m : Privilege) (h : Xlenbits) (mpp : Privilege) (entries : list (Pmpcfg_ent * Xlenbits)) :=
    ((∃ v, pc ↦ v ∗
           nextpc ↦ v) ∗
     (∃ mpie mie, mstatus ↦ {| MPP := mpp; MPIE := mpie; MIE := mie |}) ∗
     interp_pmp_addr_access (mG := sailGS_memGS) liveAddrs mmioAddrs entries m ∗
     interp_gprs ∅ ∗
     cur_privilege ↦ m ∗
     mtvec ↦ h ∗
     (∃ mc, mcause ↦ mc) ∗
     (∃ mi, mip ↦ mi) ∗
     (∃ mi, mie ↦ mi) ∗
     (∃ ms : Xlenbits,  mscratch ↦ ms) ∗
     (∃ v, mepc ↦ v) ∗
     interp_pmp_entries entries)%I.

  Definition CSRMod (m : Privilege) (entries : list (Pmpcfg_ent * Xlenbits)) :=
    ((∃ v, pc ↦ v ∗
           nextpc ↦ v) ∗
     (∃ mpp mpie mie, mstatus ↦ {| MPP := mpp; MPIE := mpie; MIE := mie |}) ∗
     interp_pmp_addr_access (mG := sailGS_memGS) liveAddrs mmioAddrs entries m ∗
     interp_gprs ∅ ∗
     ⌜m = Machine⌝ ∗
     cur_privilege ↦ Machine ∗
     (∃ h, mtvec ↦ h) ∗
     (∃ mc, mcause ↦ mc) ∗
     (∃ mi, mip ↦ mi) ∗
     (∃ mi, mie ↦ mi) ∗
     (∃ ms : Xlenbits,  mscratch ↦ ms) ∗
     (∃ mepc_v, mepc ↦ mepc_v) ∗
     (∃ entries, interp_pmp_entries entries))%I.

  Definition Trap (m : Privilege) (h : Xlenbits) (entries : list (Pmpcfg_ent * Xlenbits)) :=
    (pc ↦ h ∗
     nextpc ↦ h ∗
     (∃ mpie , mstatus ↦ {| MPP := m; MPIE := mpie; MIE := false |}) ∗
     interp_pmp_addr_access (mG := sailGS_memGS) liveAddrs mmioAddrs entries m ∗
     interp_gprs ∅ ∗
     cur_privilege ↦ Machine ∗
     mtvec ↦ h ∗
     (∃ mc, mcause ↦ mc) ∗
     (∃ mi, mip ↦ mi) ∗
     (∃ mi, mie ↦ mi) ∗
     (∃ ms : Xlenbits,  mscratch ↦ ms) ∗
     (∃ mepc_v, mepc ↦ mepc_v) ∗
     interp_pmp_entries entries)%I.

  Definition Recover (m : Privilege) (h : Xlenbits) (mpp : Privilege) (entries : list (Pmpcfg_ent * Xlenbits)) :=
    (∃ mepc_v, (
       pc     ↦ mepc_v ∗
       nextpc ↦ mepc_v ∗
       (∃ mpie mie, mstatus ↦ {| MPP := User; MPIE := mpie; MIE := mie |}) ∗
       interp_pmp_addr_access (mG := sailGS_memGS) liveAddrs mmioAddrs entries m ∗
       interp_gprs ∅ ∗
       ⌜m = Machine⌝ ∗
       cur_privilege ↦ mpp ∗
       mtvec ↦ h ∗
       (∃ mc, mcause ↦ mc) ∗
       (∃ mi, mip ↦ mi) ∗
       (∃ mi, mie ↦ mi) ∗
       (∃ ms : Xlenbits,  mscratch ↦ ms) ∗
       mepc   ↦ mepc_v ∗
       interp_pmp_entries entries))%I.

  Definition step_post (m : Privilege) (i h mepc_v : Xlenbits) (mpp : Privilege) (entries : list (Pmpcfg_ent * Xlenbits)) :=
    (Execution m h mpp entries ∨
     CSRMod m entries ∨
     Trap m h entries ∨
     Recover m h mpp entries)%I.

  Definition semTriple_step : iProp Σ :=
    (∀ m i h mepc_v mpp entries,
        semTriple env.nil (Step_pre m h i mpp entries)
                  (FunDef step)
                  (fun _ _ => step_post m i h mepc_v mpp entries))%I.

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
    unfold ProgramLogic.ValidContractCEnv.
    intros Δ τ f c H.
    destruct (ValidContracts f H) as [fuel Hc].
    apply shallow_vcgen_fuel_soundness with (fuel := fuel).
    now apply symbolic_vcgen_fuel_soundness.
  Qed.

  Lemma valid_init_model_contract : ⊢ ValidContractSem fun_init_model sep_contract_init_model.
  Proof.
    iApply (sound $! _ _ init_model).
    exact foreignSem.
    exact lemSem.
    unfold ProgramLogic.ValidContractCEnv.
    intros Δ τ f c H.
    destruct (ValidContracts f H) as [fuel Hc].
    apply shallow_vcgen_fuel_soundness with (fuel := fuel).
    now apply symbolic_vcgen_fuel_soundness.
  Qed.

  Import env.notations.

  Lemma valid_step_semTriple :
    ⊢ semTriple_step.
  Proof.
    iIntros (m i h mepc_v mpp entries) "(Hpc & Hnpc & Hmstatus & Hpaa & Hgprs & Hcp & Hmtvec & Hmc & Hmip & Hmie & Hmscr & Hmepc & Hpe)".
    iApply (semWP_mono with "[-]").
    iApply valid_step_contract.
    Unshelve.
    3: exact [kv existT (_∷ty_privilege) m; existT (_∷ty_xlenbits) h; existT (_∷ty.list ty_pmpentry) entries; existT (_∷ty_privilege) mpp; existT (_∷ty_xlenbits) i]%env.
    cbn.
    iFrame.
    cbn.
    unfold step_post.
    iIntros ([v|e] _); last auto;
      iIntros "[H | [H | [H | H]]]".
    - iLeft; unfold Execution.
      now repeat iDestruct "H" as "($ & H)".
    - iRight; iLeft; unfold CSRMod.
      iDestruct "H" as "($ & $ & $ & [% _] & H)".
      iFrame "%".
      now repeat iDestruct "H" as "($ & H)".
    - iRight; iRight; iLeft; unfold Trap.
      repeat iDestruct "H" as "($ & H)".
      iFrame "H".
    - iRight; iRight; iRight; unfold Recover.
      iDestruct "H" as "($ & $ & $ & [% _] & H)".
      iFrame "%".
      repeat iDestruct "H" as "($ & H)".
      iDestruct "H" as "([% ($ & $ & $)] & $ & $)".
  Qed.

  Lemma init_model_iprop : ⊢ semTriple_init_model.
  Proof.
    iApply (@iris_rule_consequence _ _ _ _ env.nil
             ((∃ p : Privilege, cur_privilege ↦ p) ∗
              (∃ es : list PmpEntryCfg, interp_pmp_entries es))
             _ _ _ fun_init_model _ _).
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

  Definition loop_pre (m : Privilege) (h i : Xlenbits) (mpp : Privilege) (entries : list (Pmpcfg_ent * Addr)) : iProp Σ :=
    (Step_pre m h i mpp entries ∗
     ▷ (CSRMod m entries -∗ WP_loop) ∗
     ▷ (Trap m h entries -∗ WP_loop) ∗
     ▷ (Recover m h mpp entries -∗ WP_loop))%I.

  Definition semTriple_loop : iProp Σ :=
    (∀ (m : Privilege) (h i : Xlenbits) (mpp : Privilege) (entries : list (Pmpcfg_ent * Addr)),
        semTriple env.nil (loop_pre m h i mpp entries)
                  (FunDef loop)
                  (fun _ _ => True))%I.

  Lemma valid_semTriple_loop : ⊢ semTriple_loop.
  Proof.
    iLöb as "H".
    iIntros (m h i mpp entries) "(HStep & HMod & HTrap & HRec)".
    cbn.
    unfold fun_loop.
    iApply (semWP_seq (call step) (call loop)).
    iApply semWP_call_inline_later.
    iApply (semWP_mono with "[HStep]").
    iApply (valid_step_semTriple with "HStep").
    Unshelve. 2: auto.
    iModIntro.
    iIntros ([v|e] δ); last (iIntros "_"; by rewrite semWP_fail);
      iIntros "[HRes | [HRes | [HRes | HRes]]]";
      iApply (semWP_call_inline loop _).
    - iDestruct "HRes" as "([%i' (? & ?)] & ?)".
      iApply ("H" $! m h i' mpp entries).
      now iFrame.
    - iSpecialize ("HMod" with "HRes").
      iApply (semWP_mono with "HMod").
      iIntros ([] ?); auto.
    - iSpecialize ("HTrap" with "HRes").
      iApply (semWP_mono with "HTrap").
      iIntros ([] ?); auto.
    - iSpecialize ("HRec" with "HRes").
      iApply (semWP_mono with "HRec").
      iIntros ([] ?); auto.
  Qed.
End Loop.
