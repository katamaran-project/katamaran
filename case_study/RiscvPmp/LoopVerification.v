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
     Shallow.Executor
     Shallow.Soundness
     Symbolic.Soundness
     Iris.Instance
     Iris.Model
     Program
     Semantics
     Sep.Hoare
     Sep.Logic
     Specification
     RiscvPmp.Machine
     RiscvPmp.Sig
     RiscvPmp.IrisModel
     RiscvPmp.IrisInstance
     RiscvPmp.Model
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
Import RiscvPmpIrisInstance.
Import RiscvPmpModel2.
Import RiscvPmpValidContracts.

Import RiscvPmpSignature.
Module Import RiscvPmpShallowExecutor :=
  MakeShallowExecutor RiscvPmpBase RiscvPmpProgram RiscvPmpSignature RiscvPmpSpecification.

Module Import RiscvPmpShallowSoundness := MakeShallowSoundness RiscvPmpBase RiscvPmpProgram RiscvPmpSignature RiscvPmpSpecification RiscvPmpShallowExecutor RiscvPmpProgramLogic.

Module Import RiscvPmpSymbolic := MakeSymbolicSoundness RiscvPmpBase RiscvPmpProgram RiscvPmpSignature RiscvPmpSpecification RiscvPmpSolver RiscvPmpShallowExecutor RiscvPmpExecutor.

(*** Loop ***)
(* This file proves the universal contract of the RISC-V PMP case study.
   The definition of the fdeCycle (the loop) is defined as:
     step(); loop();
   so in this file we will write the Iris version of the step contract.
   We prove the Iris version sound using the soundness lemmas of Katamaran
   and the already proven contract. *)
Section Loop.
  Context `{sg : sailGS Σ}.
  Definition step_sem_contract :=
    Eval cbn  in ValidContractSemCurried fun_step sep_contract_step.

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

  (* Step_pre defines the precondition of the step contract. The following
     definitions capture the state transitions that can occur on the machine. *)
  Definition Step_pre (m : Privilege) (h i : Xlenbits) (mpp : Privilege) (entries : list (Pmpcfg_ent * Xlenbits)) :=
    (                   cur_privilege ↦ m                ∗
                        mtvec         ↦ h                ∗
                        pc            ↦ i                ∗
     (∃ npc : Xlenbits, nextpc        ↦ npc)             ∗
     (∃ mc : Xlenbits,  mcause        ↦ mc)              ∗
     (∃ v : Xlenbits,   mepc          ↦ v)               ∗
                        mstatus       ↦ {| MPP := mpp |} ∗
                        interp_pmp_entries entries       ∗
                        interp_pmp_addr_access (mG := sailGS_memGS) liveAddrs entries m ∗
                        interp_gprs)%I.

  Definition Execution (m : Privilege) (h : Xlenbits) (mpp : Privilege) (entries : list (Pmpcfg_ent * Xlenbits)) :=
    (interp_pmp_addr_access (mG := sailGS_memGS) liveAddrs entries m ∗
     interp_gprs ∗
     interp_pmp_entries entries ∗
     (∃ mc, mcause ↦ mc) ∗
     cur_privilege ↦ m ∗
     (∃ v, nextpc ↦ v ∗
           pc ↦ v) ∗
     mtvec ↦ h ∗
     mstatus ↦ {| MPP := mpp |} ∗
     (∃ v, mepc ↦ v))%I.

  Definition CSRMod (m : Privilege) (entries : list (Pmpcfg_ent * Xlenbits)) :=
    (interp_pmp_addr_access (mG := sailGS_memGS) liveAddrs entries m ∗
     interp_gprs ∗
     (∃ entries, interp_pmp_entries entries) ∗
     ⌜m = Machine⌝ ∗
     (∃ mc, mcause ↦ mc) ∗
     cur_privilege ↦ Machine ∗
     (∃ v, nextpc ↦ v ∗
           pc ↦ v) ∗
     (∃ h, mtvec ↦ h) ∗
     (∃ mpp, mstatus ↦ {| MPP := mpp |}) ∗
     (∃ mepc_v, mepc ↦ mepc_v))%I.

  Definition Trap (m : Privilege) (h : Xlenbits) (entries : list (Pmpcfg_ent * Xlenbits)) :=
    (interp_pmp_addr_access (mG := sailGS_memGS) liveAddrs entries m ∗
     interp_gprs ∗
     interp_pmp_entries entries ∗
     (∃ mc, mcause ↦ mc) ∗
     cur_privilege ↦ Machine ∗
     nextpc ↦ h ∗
     pc ↦ h ∗
     mtvec ↦ h ∗
     mstatus ↦ {| MPP := m |} ∗
     (∃ mepc_v, mepc ↦ mepc_v))%I.

  Definition Recover (m : Privilege) (h : Xlenbits) (mpp : Privilege) (entries : list (Pmpcfg_ent * Xlenbits)) :=
    (interp_pmp_addr_access (mG := sailGS_memGS) liveAddrs entries m ∗
     interp_gprs ∗
     interp_pmp_entries entries ∗
     ⌜m = Machine⌝ ∗
     (∃ mc, mcause ↦ mc) ∗
     cur_privilege ↦ mpp ∗
     (∃ mepc_v, mepc   ↦ mepc_v ∗
                pc     ↦ mepc_v ∗
                nextpc ↦ mepc_v) ∗
     mtvec ↦ h ∗
     mstatus ↦ {| MPP := User |})%I.

  (* Step_post is the postcondition for the step function, combining the above
     state transitions using disjunctions. *)
  Definition Step_post (m : Privilege) (i h mepc_v : Xlenbits) (mpp : Privilege) (entries : list (Pmpcfg_ent * Xlenbits)) :=
    (Execution m h mpp entries ∨
     CSRMod m entries ∨
     Trap m h entries ∨
     Recover m h mpp entries)%I.

  Definition semTriple_step : iProp Σ :=
    (∀ m i h mepc_v mpp entries,
        semTriple env.nil (Step_pre m h i mpp entries)
                  (FunDef step)
                  (fun _ _ => Step_post m i h mepc_v mpp entries))%I.

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
    unfold ProgramLogic.ValidContractCEnv.
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
    iIntros (m i h mepc_v mpp entries) "H".
    iApply (semWP_mono with "[-]").
    unshelve iApply valid_step_contract.
    exact [kv existT (_∷ty_privilege) m; existT (_∷ty_xlenbits) h; existT (_∷ty.list ty_pmpentry) entries; existT (_∷ty_privilege) mpp; existT (_∷ty_xlenbits) i]%env.
    cbn.
    unfold Step_pre; iFrame.
    cbn.
    iIntros (? ?) "[H | [H | [H | H]]]".
    - now (iLeft; unfold Execution).
    - iDestruct "H" as "(? & ? & ? & [% _] & ?)".
      iRight; iLeft; unfold CSRMod; now iFrame.
    - iRight; iRight; iLeft; unfold Trap.
      iDestruct "H" as "($ & $ & $ & $ & $ & $ & $ & $ & $ & ?)".
      now iExists i.
    - iRight; iRight; iRight; unfold Recover.
      iDestruct "H" as "($ & $ & $ & [% _] & $ & $ & [%a (? & ? & ?)] & $ & $)".
      iSplitR; auto.
      iExists a; iFrame.
  Qed.

  Lemma init_model_iprop : ⊢ semTriple_init_model.
  Proof.
    iApply (@iris_rule_consequence _ _ _ _ env.nil
             ((∃ p : Privilege, cur_privilege ↦ p) ∗
              (∃ es : list RiscvPmpSignature.PmpEntryCfg, interp_pmp_entries es))
             _ _ _ fun_init_model _ _).
    iApply valid_init_model_contract.
    Unshelve.
    done.
    cbn.
    iIntros (? ?) "(_ & $ & $)".
    constructor.
  Qed.

  (* loop_pre is the precondition of the fdeCycle. *)
  Definition loop_pre (m : Privilege) (h i : Xlenbits) (mpp : Privilege) (entries : list (Pmpcfg_ent * Addr)) : iProp Σ :=
    (Step_pre m h i mpp entries ∗
              ▷ (CSRMod m entries -∗ WP_loop) ∗
              ▷ (Trap m h entries -∗ WP_loop) ∗
              ▷ (Recover m h mpp entries -∗ WP_loop))%I.

  (* semTriple_loop is the universal contract for this case study. *)
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
    iIntros (v δ) "[HRes | [HRes | [HRes | HRes]]]";
      iApply (semWP_call_inline loop _).
    - iDestruct "HRes" as "(? & ? & ? & ? & ? & [%i' (? & ?)] & ? & ? & ?)".
      unfold semTriple_loop.
      iApply ("H" $! m h i' mpp entries).
      unfold loop_pre.
      iFrame.
      now iExists i'.
    - iApply ("HMod" with "HRes").
    - iApply ("HTrap" with "HRes").
    - iApply ("HRec" with "HRes").
  Qed.
End Loop.
