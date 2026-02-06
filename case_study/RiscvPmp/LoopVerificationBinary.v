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
     Sep.Logic
     Specification
     MicroSail.ShallowExecutor
     MicroSail.ShallowSoundness
     MicroSail.RefineExecutor
     MicroSail.Soundness
     RiscvPmp.Machine
     RiscvPmp.Sig
     RiscvPmp.IrisModelBinary
     RiscvPmp.IrisInstanceBinary
     RiscvPmp.ModelBinary
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
Import RiscvPmpIrisBase2.
Import RiscvPmpIrisInstance2.
Import RiscvPmpModel2.
Import RiscvPmpValidContracts.

Import RiscvPmpSignature.
Module Import RiscvPmpShallowExecutor :=
  MakeShallowExecutor RiscvPmpBase RiscvPmpSignature RiscvPmpProgram DefaultFailLogic RiscvPmpSpecification.

Module Import RiscvPmpShallowSoundness := MakeShallowSoundness RiscvPmpBase RiscvPmpSignature RiscvPmpProgram DefaultFailLogic RiscvPmpSpecification RiscvPmpShallowExecutor RiscvPmpProgramLogic.

Module Import RiscvPmpSymbolic := MakeSymbolicSoundness RiscvPmpBase RiscvPmpSignature RiscvPmpProgram DefaultFailLogic RiscvPmpSpecification RiscvPmpShallowExecutor RiscvPmpExecutor.

Section Loop.
  Context `{sg : sailGS2 Σ}.

  Definition WP2_loop : iProp Σ :=
    semWP2 env.nil env.nil (FunDef loop) (FunDef loop) (λ v1 δ1 v2 δ2, ⌜v1 = v2⌝ ∗ ⌜δ1 = δ2⌝)%I.

  Definition step_sem_contract :=
    Eval cbn  in ValidContractSemCurried fun_step sep_contract_step.

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
    (                   cur_privilege ↦ m                ∗
                        mtvec         ↦ h                ∗
                        pc            ↦ i                ∗
     (∃ npc : Xlenbits, nextpc        ↦ npc)             ∗
     (∃ mc : Xlenbits,  mcause        ↦ mc)              ∗
     (∃ mi, mip ↦ mi) ∗
     (∃ mi, mie ↦ mi) ∗
     (∃ ms : Xlenbits,  mscratch ↦ ms) ∗
     (∃ v : Xlenbits,   mepc          ↦ v)               ∗
     (∃ mpie mie,       mstatus       ↦ {| MPP := mpp; MPIE := mpie; MIE := mie |}) ∗
                        interp_pmp_entries entries       ∗
                        interp_pmp_addr_access (mG := sailGS2_memGS) liveAddrs mmioAddrs entries m ∗
                        interp_gprs)%I.

  Definition Execution (m : Privilege) (h : Xlenbits) (mpp : Privilege) (entries : list (Pmpcfg_ent * Xlenbits)) :=
    (interp_pmp_addr_access (mG := sailGS2_memGS) liveAddrs mmioAddrs entries m ∗
     interp_gprs ∗
     interp_pmp_entries entries ∗
     (∃ mc, mcause ↦ mc) ∗
     (∃ mi, mip ↦ mi) ∗
     (∃ mi, mie ↦ mi) ∗
     (∃ ms, mscratch ↦ ms) ∗
     cur_privilege ↦ m ∗
     (∃ v, nextpc ↦ v ∗
           pc ↦ v) ∗
     mtvec ↦ h ∗
     (∃ mpie mie, mstatus ↦ {| MPP := mpp; MPIE := mpie; MIE := mie |}) ∗
     (∃ v, mepc ↦ v))%I.

  Definition CSRMod (m : Privilege) (entries : list (Pmpcfg_ent * Xlenbits)) :=
    (interp_pmp_addr_access (mG := sailGS2_memGS) liveAddrs mmioAddrs entries m ∗
     interp_gprs ∗
     (∃ entries, interp_pmp_entries entries) ∗
     ⌜m = Machine⌝ ∗
     (∃ mc, mcause ↦ mc) ∗
     (∃ mi, mip ↦ mi) ∗
     (∃ mi, mie ↦ mi) ∗
     (∃ ms, mscratch ↦ ms) ∗
     cur_privilege ↦ Machine ∗
     (∃ v, nextpc ↦ v ∗
           pc ↦ v) ∗
     (∃ h, mtvec ↦ h) ∗
     (∃ mpp mpie mie, mstatus ↦ {| MPP := mpp; MPIE := mpie; MIE := mie |}) ∗
     (∃ mepc_v, mepc ↦ mepc_v))%I.

  Definition Trap (m : Privilege) (h : Xlenbits) (entries : list (Pmpcfg_ent * Xlenbits)) :=
    (interp_pmp_addr_access (mG := sailGS2_memGS) liveAddrs mmioAddrs entries m ∗
     interp_gprs ∗
     interp_pmp_entries entries ∗
     (∃ mc, mcause ↦ mc) ∗
     (∃ mi, mip ↦ mi) ∗
     (∃ mi, mie ↦ mi) ∗
     (∃ ms, mscratch ↦ ms) ∗
     cur_privilege ↦ Machine ∗
     nextpc ↦ h ∗
     pc ↦ h ∗
     mtvec ↦ h ∗
     (∃ mpie, mstatus ↦ {| MPP := m; MPIE := mpie; MIE := false |}) ∗
     (∃ mepc_v, mepc ↦ mepc_v))%I.

  Definition Recover (m : Privilege) (h : Xlenbits) (mpp : Privilege) (entries : list (Pmpcfg_ent * Xlenbits)) :=
    (interp_pmp_addr_access (mG := sailGS2_memGS) liveAddrs mmioAddrs entries m ∗
     interp_gprs ∗
     interp_pmp_entries entries ∗
     ⌜m = Machine⌝ ∗
     (∃ mc, mcause ↦ mc) ∗
     (∃ mi, mip ↦ mi) ∗
     (∃ mi, mie ↦ mi) ∗
     (∃ ms, mscratch ↦ ms) ∗
     cur_privilege ↦ mpp ∗
     (∃ mepc_v, mepc   ↦ mepc_v ∗
                pc     ↦ mepc_v ∗
                nextpc ↦ mepc_v) ∗
     mtvec ↦ h ∗
     (∃ mpie mie, mstatus ↦ {| MPP := User; MPIE := mpie; MIE := mie |}))%I.

  (* Executing normally *)
  (* TODO: this should be the same as Start of iteration (P), drop one of them *)
  Definition Execution' (m cp : Privilege) (h i : Addr) (entries es : list (Pmpcfg_ent * Addr)) (mpp : Privilege) (mepc_v : Addr) :=
    (            interp_pmp_addr_access (mG := sailGS2_memGS) liveAddrs mmioAddrs entries m ∗
                                        interp_gprs ∗
                                        interp_pmp_entries es ∗
                                        (∃ mc,         mcause        ↦ mc) ∗
                                        (∃ mi, mip ↦ mi) ∗
                                        (∃ mi, mie ↦ mi) ∗
                                        cur_privilege ↦ cp ∗
                                        (∃ npc : Addr, nextpc        ↦ npc) ∗
                                        (∃ cpc : Addr, pc            ↦ cpc) ∗
                                        mtvec         ↦ h ∗
                                        (∃ mpie mie, mstatus       ↦ {| MPP := mpp; MPIE := mpie; MIE := mie |}) ∗
                                        mepc          ↦ mepc_v)%I.

  (* Modified CSRs, requires Machine mode *)
  Definition CSRMod' (m cp : Privilege) (h i : Addr) (entries es : list (Pmpcfg_ent * Addr)) (mpp : Privilege) (mepc_v : Addr) :=
    (                               interp_pmp_addr_access (mG := sailGS2_memGS) liveAddrs mmioAddrs entries m ∗
                                                           interp_gprs ∗
                                                           (∃ es : list (Pmpcfg_ent * Addr), interp_pmp_entries es) ∗
                                                           ⌜m = Machine⌝ ∗
                                                                         (∃ mc : Addr,                  mcause        ↦ mc) ∗
                                                                         (∃ mi, mip ↦ mi) ∗
                                                                         (∃ mi, mie ↦ mi) ∗
                                                                         cur_privilege ↦ Machine ∗
                                                                         (∃ npc : Addr,                 nextpc        ↦ npc ∗
                                                                                                                      pc            ↦ npc) ∗
                                                                         (∃ h : Addr,                   mtvec         ↦ h) ∗
                                                                         (∃ mpp mpie mie,            mstatus       ↦ {| MPP := mpp; MPIE := mpie; MIE := mie |}) ∗
                                                                         (∃ epc : Addr,                 mepc          ↦ epc))%I.

  (* Trap occured -> Go into M-mode *)
  Definition Trap' (m cp : Privilege) (h i : Addr) (entries es : list (Pmpcfg_ent * Addr)) (mpp : Privilege) (mepc_v : Addr) :=
    (interp_pmp_addr_access (mG := sailGS2_memGS) liveAddrs mmioAddrs entries m ∗
                            interp_gprs ∗
                            interp_pmp_entries es ∗
                            (∃ mc, mcause        ↦ mc) ∗
                            (∃ mi, mip ↦ mi) ∗
                            (∃ mi, mie ↦ mi) ∗
                            cur_privilege ↦ Machine ∗
                            nextpc        ↦ h ∗
                            pc            ↦ h ∗
                            mtvec         ↦ h ∗
                            (∃ mpie, mstatus       ↦ {| MPP := m; MPIE := mpie; MIE := false |}) ∗
                            mepc          ↦ i)%I.

  (* MRET = Recover *)
  Definition Recover' (m cp : Privilege) (h i : Addr) (entries es : list (Pmpcfg_ent * Addr)) (mpp : Privilege) (mepc_v : Addr) :=
    (interp_pmp_addr_access (mG := sailGS2_memGS) liveAddrs mmioAddrs entries m ∗
                            interp_gprs ∗
                            interp_pmp_entries es ∗
                            ⌜m = Machine⌝ ∗
                                          (∃ mc, mcause        ↦ mc) ∗
                                          (∃ mi, mip ↦ mi) ∗
                                          (∃ mi, mie ↦ mi) ∗
                                          cur_privilege ↦ mpp ∗
                                          nextpc        ↦ mepc_v ∗
                                          pc            ↦ mepc_v ∗
                                          mtvec         ↦ h ∗
                                          (∃ mpie mie, mstatus       ↦ {| MPP := User; MPIE := mpie; MIE := mie |}) ∗
                                          mepc          ↦ mepc_v)%I.

  Definition step_post' (m cp : Privilege) (h i : Addr) (entries es : list (Pmpcfg_ent * Addr)) (mpp : Privilege) (mepc_v : Addr) : iProp Σ :=
    (Execution' m cp h i entries es mpp mepc_v ∨
     CSRMod'    m cp h i entries es mpp mepc_v ∨
     Trap'      m cp h i entries es mpp mepc_v ∨
     Recover'   m cp h i entries es mpp mepc_v)%I.

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
              ((∃ p, reg_pointsTo21 cur_privilege p) ∗ (∃ es, interp_pmp_entries es))%I
              (FunDef init_model)
              (fun _ _ => reg_pointsTo21 cur_privilege Machine ∗ (∃ es, interp_pmp_entries es))%I.

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
    iIntros (m i h mepc_v mpp entries) "(Hcp & Hmtvec & Hpc & Hnpc & Hmc & Hmscr & Hmepc & Hmstatus & Hpe & Hpaa & Hgprs)".
    iApply (semWP2_mono with "[-]").
    iApply valid_step_contract.
    Unshelve.
    3: exact [kv existT (_∷ty_privilege) m; existT (_∷ty_xlenbits) h; existT (_∷ty.list ty_pmpentry) entries; existT (_∷ty_privilege) mpp; existT (_∷ty_xlenbits) i]%env.
    cbn; now iFrame.
    unfold step_post; cbn.
    iIntros (v1 δ1 v2 δ2) "(<- & <- & H)".
    do 2 (iSplitR; first easy).
    destruct v1 as [v'|m1] eqn:Ev1; auto.
    iDestruct "H" as "[H | [H | [H | H]]]".
    - iDestruct "H" as "(Hpaa & Hgprs & Hmc & Hmie & Hmip & Hmscr & Hpe & Hcp & Hnpc & Hmtvec & Hmstatus & Hmepc)".
      iLeft; unfold Execution; iFrame.
    - iDestruct "H" as "(Hpaa & Hgprs & Hpe & [% _] & Hmc & Hmie & Hmip & Hmscr & Hcp & Hnpc & Hmtvec & Hmstatus & Hmepc)".
      iRight; iLeft; unfold CSRMod; now iFrame.
    - iDestruct "H" as "(Hpaa & Hgprs & Hentries & Hmc & Hmie & Hmip & Hmscr & Hpe & Hcp & Hnpc & Hmtvec & Hmstatus & Hmepc)".
      iRight; iRight; iLeft. unfold Trap; iFrame.
    - iDestruct "H" as "(Hpaa & Hgprs & Hpe & [% _] & Hmc & Hmie & Hmip & Hmscr & Hcp & [% (Hmepc & Hnpc & Hpc)] & Hmtvec & Hmstatus)".
      iRight; iRight; iRight; unfold Recover; by iFrame.
  Qed.

  Lemma init_model_iprop : ⊢ semTriple_init_model.
  Proof.
    iApply (@iris_rule_consequence _ _ _ _ env.nil
             ((∃ p : Privilege, cur_privilege ↦ p) ∗
              (∃ es : list RiscvPmpIrisInstance2.PmpEntryCfg, interp_pmp_entries es))
             _ _ _ fun_init_model _ _).
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

  Definition loop_pre (m : Privilege) (h i : Xlenbits) (mpp : Privilege) (entries : list (Pmpcfg_ent * Addr)) : iProp Σ :=
    (Step_pre m h i mpp entries ∗
              ▷ (CSRMod m entries -∗ WP2_loop) ∗
              ▷ (Trap m h entries -∗ WP2_loop) ∗
              ▷ (Recover m h mpp entries -∗ WP2_loop))%I.

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
    iApply (semWP2_seq (call step) (call step) (call loop) (call loop)).
    iApply semWP2_call_inline_later.
    iApply (semWP2_mono with "[HStep]").
    iApply (valid_step_semTriple with "HStep").
    Unshelve. 2: auto.
    iModIntro.

    iIntros ([v1|m1] δ1 v2 δ2) "(<- & <- & HRes)";
      last now iApply semWP2_fail.
    iDestruct "HRes" as "[HRes | [HRes | [HRes | HRes]]]";
      iApply (semWP2_call_inline loop _).
    - iDestruct "HRes" as "(? & ? & ? & ? & ? & ? & ? & ? & [%i' (? & ?)] & ? & ? & ?)".
      unfold semTriple_loop.
      iSpecialize ("H" $! m h i' mpp entries with "[-]").
      { iFrame. }
      iApply (semWP2_mono with "H").
      iIntros (v δ v' δ') "(<- & <- & _)"; repeat iSplit; auto.
      by case_match.
    - iSpecialize ("HMod" with "HRes").
      iApply (semWP2_mono with "HMod").
      iIntros (v δ v' δ') "(<- & <-)".
      repeat iSplit; auto.
      by case_match.
    - iSpecialize ("HTrap" with "HRes").
      iApply (semWP2_mono with "HTrap").
      iIntros (v δ v' δ') "(<- & <-)".
      repeat iSplit; auto.
      by case_match.
    - iSpecialize ("HRec" with "HRes").
      iApply (semWP2_mono with "HRec").
      iIntros (v δ v' δ') "(<- & <-)".
      repeat iSplit; auto.
      by case_match.
  Qed.
End Loop.
