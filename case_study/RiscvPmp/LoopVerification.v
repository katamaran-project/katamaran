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

Section Loop.
  Context `{sg : sailGS Σ}.
  Definition step_sem_contract :=
    Eval cbn  in ValidContractSemCurried fun_step sep_contract_step.

  Local Notation "r '↦' val" := (reg_pointsTo r val) (at level 70).

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

  Definition Step_pre (m : Privilege) (h i mepc_v : Xlenbits) (mpp : Privilege) (entries : list (Pmpcfg_ent * Xlenbits)) :=
    (                   cur_privilege ↦ m                ∗
                        mtvec         ↦ h                ∗
                        pc            ↦ i                ∗
     (∃ npc : Xlenbits, nextpc        ↦ npc)             ∗
     (∃ mc : Z,         mcause        ↦ mc)              ∗
                        mepc          ↦ mepc_v           ∗
                        mstatus       ↦ {| MPP := mpp |} ∗
                        interp_pmp_entries entries       ∗
                        interp_pmp_addr_access (mG := sailGS_memGS) liveAddrs entries m ∗
                        interp_gprs)%I.

  Definition Execution (m : Privilege) (h mepc_v : Xlenbits) (mpp : Privilege) (entries : list (Pmpcfg_ent * Xlenbits)) :=
    (interp_pmp_addr_access (mG := sailGS_memGS) liveAddrs entries m ∗
     interp_gprs ∗
     interp_pmp_entries entries ∗
     (∃ mc, mcause ↦ mc) ∗
     cur_privilege ↦ m ∗
     (∃ v, nextpc ↦ v ∗
           pc ↦ v) ∗
     mtvec ↦ h ∗
     mstatus ↦ {| MPP := mpp |} ∗
     mepc ↦ mepc_v)%I.

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

  Definition Trap (m : Privilege) (i h mepc_v : Xlenbits) (entries : list (Pmpcfg_ent * Xlenbits)) :=
    (interp_pmp_addr_access (mG := sailGS_memGS) liveAddrs entries m ∗
     interp_gprs ∗
     interp_pmp_entries entries ∗
     (∃ mc, mcause ↦ mc) ∗
     cur_privilege ↦ Machine ∗
     nextpc ↦ h ∗
     pc ↦ h ∗
     mtvec ↦ h ∗
     mstatus ↦ {| MPP := m |} ∗
     mepc ↦ i)%I.

  Definition Recover (m : Privilege) (h mepc_v : Xlenbits) (mpp : Privilege) (entries : list (Pmpcfg_ent * Xlenbits)) :=
    (interp_pmp_addr_access (mG := sailGS_memGS) liveAddrs entries m ∗
     interp_gprs ∗
     interp_pmp_entries entries ∗
     ⌜m = Machine⌝ ∗
     (∃ mc, mcause ↦ mc) ∗
     cur_privilege ↦ mpp ∗
     nextpc ↦ mepc_v ∗
     pc ↦ mepc_v ∗
     mtvec ↦ h ∗
     mstatus ↦ {| MPP := User |} ∗
     mepc ↦ mepc_v)%I.

  (* Executing normally *)
  (* TODO: this should be the same as Start of iteration (P), drop one of them *)
  Definition Execution' (m cp : Privilege) (h i : Z) (entries es : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v : Z) :=
    (            interp_pmp_addr_access (mG := sailGS_memGS) liveAddrs entries m ∗
                                        interp_gprs ∗
                                        interp_pmp_entries es ∗
                                        (∃ mc : Z,  mcause        ↦ mc) ∗
                                        cur_privilege ↦ cp ∗
                                        (∃ npc : Z, nextpc        ↦ npc) ∗
                                        (∃ cpc : Z, pc            ↦ cpc) ∗
                                        mtvec         ↦ h ∗
                                        mstatus       ↦ {| MPP := mpp |} ∗
                                        mepc          ↦ mepc_v)%I.

  (* Modified CSRs, requires Machine mode *)
  Definition CSRMod' (m cp : Privilege) (h i : Z) (entries es : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v : Z) :=
    (                               interp_pmp_addr_access (mG := sailGS_memGS) liveAddrs entries m ∗
                                                           interp_gprs ∗
                                                           (∃ es : list (Pmpcfg_ent * Z), interp_pmp_entries es) ∗
                                                           ⌜m = Machine⌝ ∗
                                                                         (∃ mc : Z,                     mcause        ↦ mc) ∗
                                                                         cur_privilege ↦ Machine ∗
                                                                         (∃ npc : Z,                    nextpc        ↦ npc ∗
                                                                                                                      pc            ↦ npc) ∗
                                                                         (∃ h : Z,                      mtvec         ↦ h) ∗
                                                                         (∃ mpp : Privilege,            mstatus       ↦ {| MPP := mpp |}) ∗
                                                                         (∃ epc : Z,                    mepc          ↦ epc))%I.

  (* Trap occured -> Go into M-mode *)
  Definition Trap' (m cp : Privilege) (h i : Z) (entries es : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v : Z) :=
    (interp_pmp_addr_access (mG := sailGS_memGS) liveAddrs entries m ∗
                            interp_gprs ∗
                            interp_pmp_entries es ∗
                            (∃ mc : Z, mcause        ↦ mc) ∗
                            cur_privilege ↦ Machine ∗
                            nextpc        ↦ h ∗
                            pc            ↦ h ∗
                            mtvec         ↦ h ∗
                            mstatus       ↦ {| MPP := m |} ∗
                            mepc          ↦ i)%I.

  (* MRET = Recover *)
  Definition Recover' (m cp : Privilege) (h i : Z) (entries es : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v : Z) :=
    (interp_pmp_addr_access (mG := sailGS_memGS) liveAddrs entries m ∗
                            interp_gprs ∗
                            interp_pmp_entries es ∗
                            ⌜m = Machine⌝ ∗
                                          (∃ mc : Z, mcause        ↦ mc) ∗
                                          cur_privilege ↦ mpp ∗
                                          nextpc        ↦ mepc_v ∗
                                          pc            ↦ mepc_v ∗
                                          mtvec         ↦ h ∗
                                          mstatus       ↦ {| MPP := User |} ∗
                                          mepc          ↦ mepc_v)%I.

  Definition step_post' (m cp : Privilege) (h i : Z) (entries es : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v : Z) : iProp Σ :=
    (Execution' m cp h i entries es mpp mepc_v ∨
     CSRMod'    m cp h i entries es mpp mepc_v ∨
     Trap'      m cp h i entries es mpp mepc_v ∨
     Recover'   m cp h i entries es mpp mepc_v)%I.

  Definition step_post (m : Privilege) (i h mepc_v : Xlenbits) (mpp : Privilege) (entries : list (Pmpcfg_ent * Xlenbits)) :=
    (Execution m h mepc_v mpp entries ∨
     CSRMod m entries ∨
     Trap m i h mepc_v entries ∨
     Recover m h mepc_v mpp entries)%I.

  Definition semTriple_step' : iProp Σ :=
    (∀ (m cp : Privilege) (h i npc : Z) (entries es : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v : Z),
        semTriple env.nil (Step_pre m h i mepc_v mpp entries) (FunDef step) (fun _ _ => step_post' m cp h i entries es mpp mepc_v))%I.

  Definition semTriple_step : iProp Σ :=
    (∀ m i h mepc_v mpp entries,
        semTriple env.nil (Step_pre m h i mepc_v mpp entries)
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
    intros.
    apply shallow_vcgen_soundness.
    apply symbolic_vcgen_soundness.
    apply ValidContracts; assumption.
  Qed.

  Axiom step_iprop' : ⊢ semTriple_step.

  Lemma valid_init_model_contract : ⊢ ValidContractSem fun_init_model sep_contract_init_model.
  Proof.
    iApply (sound $! _ _ init_model).
    exact foreignSem.
    exact lemSem.
    unfold ProgramLogic.ValidContractCEnv.
    intros.
    apply shallow_vcgen_soundness.
    apply symbolic_vcgen_soundness.
    apply ValidContracts; assumption.
  Qed.

  Import env.notations.

  Lemma valid_step_semTriple :
    ⊢ semTriple_step.
  Proof.
    unfold semTriple_step.
    iIntros.
    iApply (@iris_rule_consequence _ _ _ _ env.nil
                                   (Step_pre m h i mepc_v mpp entries)
                                   _ _ _ fun_step _ _).
    iApply valid_step_contract.
    Unshelve.
    3: exact [kv existT (_∷ty_privilege) m; existT (_∷ty_xlenbits) h; existT (_∷ty.list ty_pmpentry) entries; existT (_∷ty_privilege) mpp; existT (_∷ty_xlenbits) mepc_v; existT (_∷ty_xlenbits) i]%env.
    cbn.
    unfold Step_pre.
    iIntros "(Hcp & Hmtvec & Hpc & Hnpc & Hmc & Hmepc & Hmstatus & Hpe & Hpaa & Hgprs)".
    iAccu.
    cbn.
    unfold step_post.
    iIntros (? ?) "[H | [H | [H | H]]]".
    - iDestruct "H" as "(Hpaa & Hgprs & Hmc & Hpe & Hcp & Hnpc & Hmtvec & Hmstatus & Hmepc)".
      iLeft; unfold Execution; iFrame.
    - iDestruct "H" as "(Hpaa & Hgprs & Hpe & [% _] & Hmc & Hcp & Hnpc & Hmtvec & Hmstatus & Hmepc)".
      iRight; iLeft; unfold CSRMod; now iFrame.
    - iDestruct "H" as "(Hpaa & Hgprs & Hmc & Hpe & Hcp & Hnpc & Hmtvec & Hmstatus & Hmepc)".
      iRight; iRight; iLeft; unfold Trap; iFrame.
    - iDestruct "H" as "(Hpaa & Hgprs & Hpe & [% _] & Hmc & Hcp & Hnpc & Hmtvec & Hmstatus & Hmepc)".
      iRight; iRight; iRight; unfold Recover; now iFrame.
  Qed.

  Lemma valid_step_semTriple' :
    ⊢ semTriple_step'.
  Proof.
    unfold semTriple_step'.
    iIntros.
    iApply (@iris_rule_consequence _ _ _ _ env.nil
                                   (Step_pre m h i mepc_v mpp entries)
                                   _ _ _ fun_step _ _).
    iApply valid_step_contract.
    Unshelve.
    3: exact [kv existT (_∷ty_privilege) m; existT (_∷ty_xlenbits) h; existT (_∷ty.list ty_pmpentry) entries; existT (_∷ty_privilege) mpp; existT (_∷ty_xlenbits) mepc_v; existT (_∷ty_xlenbits) i]%env.
    cbn.
    unfold Step_pre.
    iIntros "(Hcp & Hmtvec & Hpc & Hnpc & Hmc & Hmepc & Hmstatus & Hpe & Hpaa & Hgprs)".
    iAccu.
    cbn.
    intros.
    unfold step_post.
    iIntros "[H | [H | [H | H]]]";
      iDestruct "H" as "(Hpaa & Hgprs & Hmc & Hpe & Hcp & Hpc & Hmtvec & Hmstatus & Hmepc)".
    - iDestruct "Hpc" as "[% (Hnpc & Hpc)]".
      iLeft; unfold Execution'.
      admit.
    - iRight; iLeft; unfold CSRMod'.
      admit.
    - iRight; iRight; iLeft; unfold Trap'.
      admit.
    - iRight; iRight; iRight; unfold Recover'.
      admit.
  Admitted.

  Lemma init_model_iprop : ⊢ semTriple_init_model.
  Proof.
    iApply (@iris_rule_consequence _ _ _ _ env.nil
             ((∃ p : Privilege, cur_privilege ↦ p) ∗
              (∃ es : list RiscvPmpIrisInstance.PmpEntryCfg, interp_pmp_entries es))
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

  Definition loop_pre (m : Privilege) (h i mepc_v : Xlenbits) (mpp : Privilege) (entries : list (Pmpcfg_ent * Z)) : iProp Σ :=
    (Step_pre m h i mepc_v mpp entries ∗
              (Execution m h mepc_v mpp entries -∗ WP_loop) ∗
              (CSRMod m entries -∗ WP_loop) ∗
              (Trap m i h mepc_v entries -∗ WP_loop) ∗
              (Recover m h mepc_v mpp entries -∗ WP_loop))%I.

  Definition semTriple_loop : iProp Σ :=
    (∀ (m : Privilege) (h i mepc_v : Xlenbits) (mpp : Privilege) (entries : list (Pmpcfg_ent * Z)),
        semTriple env.nil (loop_pre m h i mepc_v mpp entries)
                  (FunDef loop)
                  (fun _ _ => True))%I.

  Lemma valid_semTriple_loop : ⊢ semTriple_loop.
  Proof.
    iIntros (m h i mepc_v mpp entries) "(Hsteppre & Hexe & Hcsrmod & Htrap & Hrec)".
    cbn.
    unfold fun_loop.
    iApply ((iris_rule_stm_seq env.nil (stm_call step _) (stm_call loop _) _ _ (fun _ _ => True%I)) with "[] [Hexe Hcsrmod Htrap Hrec] Hsteppre").
    - iApply (iris_rule_stm_call_inline env.nil step env.nil (Step_pre m h i mepc_v mpp entries) (fun _ => step_post m i h mepc_v mpp entries)).
      cbn.
      iApply valid_step_semTriple.
    - iIntros.
      destruct (env.nilView δ').
      unfold semTriple.
      iIntros "(Hpost & %)".
      iRevert "Hpost".
      fold (semTriple [env] (step_post m i h mepc_v mpp entries) (call loop) (fun _ _ => True)%I).
      iApply (@iris_rule_consequence _ _ _ _ _ _ (step_post m i h mepc_v mpp entries) _ (fun v δ => True ∧ ⌜[env] = δ⌝)%I _ _ _).
      iApply (iris_rule_stm_call_inline env.nil loop env.nil (step_post m i h mepc_v mpp entries) (fun _ => True)%I).
      cbn.
      unfold semTriple.
      iIntros "[H | [H | [H | H]]]".
      + iApply ("Hexe" with "H").
      + iApply ("Hcsrmod" with "H").
      + iApply ("Htrap" with "H").
      + iApply ("Hrec" with "H").
        Unshelve.
        iIntros "H"; iExact "H".
        now iIntros.
  Qed.

  Section OldLoop.
    Definition loop_pre' (m cp : Privilege) (h i : Z) (entries es : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v : Z) : iProp Σ :=
      (
        Execution' m cp h i entries es mpp mepc_v ∗
                  ▷ (CSRMod'    m cp h i entries es mpp mepc_v -∗ WP_loop) ∗
                  ▷ (Trap'      m cp h i entries es mpp mepc_v -∗ WP_loop) ∗
                  ▷ (Recover'   m cp h i entries es mpp mepc_v -∗ WP_loop))%I.

    Definition semTriple_loop' : iProp Σ :=
      (∀ (m cp : Privilege) (h i : Z) (entries es : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v : Z),
          semTriple env.nil (loop_pre' m cp h i entries es mpp mepc_v) (FunDef loop) (fun _ _ => True))%I.

    Definition semTriple_main : iProp Σ :=
      (∀ (m cp : Privilege) (h i : Z) (entries es : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v : Z),
          semTriple env.nil (loop_pre' m cp h i entries es mpp mepc_v) (FunDef main) (fun _ _ => True))%I.

    Lemma valid_semTriple_loop' :
      ⊢ semTriple_loop'.
    Proof.
    (*   iIntros. *)
    (*   iLöb as "H". *)
    (*   iIntros (m cp h i entries es mpp mepc_v) "[HP HPwp]". *)
    (*   cbn. *)
    (*   unfold fun_loop. *)
    (*   iApply ((iris_rule_stm_seq env.nil (stm_call step _) (stm_call loop _) _ (fun δ => step_post' m cp h i entries es mpp mepc_v ∧ ⌜env.nil = δ⌝)%I (fun _ _ => True%I)) with "[] [HPwp] HP"). *)
    (*   iApply (iris_rule_stm_call_inline env.nil step env.nil (Execution' m cp h i entries es mpp mepc_v) (fun _ => step_post' m cp h i entries es mpp mepc_v)). *)
    (*   iApply step_iprop.  *)
    (*   iIntros. *)
    (*   iApply iris_rule_consequence. *)
    (*   iIntros "[Hstep _]". *)
    (*   iExact "Hstep". *)
    (*   2: { *)
    (*     destruct (env.nilView δ'). *)
    (*     iApply (iris_rule_stm_call_inline_later env.nil loop env.nil _ (fun _ => True%I)). *)
    (*     iModIntro. *)
    (*     cbn. *)
    (*     unfold semTriple_loop. *)
    (*     unfold loop_pre, step_post. *)
    (*     unfold semTriple. *)
    (*     cbn. *)
    (*     iDestruct "HPwp" as "(H2 & H3 & H4)". *)
    (*     iIntros "[HP|[HP|[HP|HP]]]". *)
    (*     iApply "H". *)
    (*     iSplitL "HP"; try iAssumption. *)
    (*     iSplitL "H2"; try (iModIntro; iAssumption). *)
    (*     iSplitL "H3"; iModIntro; iAssumption. *)
    (*     iApply ("H2" with "HP"). *)
    (*     iApply ("H3" with "HP"). *)
    (*     iApply ("H4" with "HP"). *)
    (*   } *)
    (*   now iIntros (_ δ) "_". *)
    Admitted.

    (* DOMI: some comments:
        - I think a universal contract for main doesn't make sense.
          I don't see when this would ever be used.
          I believe the only UC we need in practice is the one for loop.
          I would propose dropping this?
        - semTriple_main quantifies over two arbitrary pmp configs: one which is currently set in the pmp configuration registers and one for which authority is available.
          However, main will start by setting a third one in the registers.
          I think the contract needs to be adapted to take this into account, by updating at least the pmp configuration that will be set in the contracts for the continuations (i.e. CSRMod, Trap, Recover).
          I suspect this is the problem you're hitting in the (STUCK) case.
     *)
    (* NOTE/TODO: this is quite an ugly and overly explicit proof...
                   I had trouble rewriting sep logic rules (commutativity of ∗)
                   and just "abused" the consequence rules to apply it instead of rewriting *)
    (* TODO: Alternative: contract for loop specified with Katamaran, verify main in Katamaran *)
    Lemma valid_semTriple_main :
      ⊢ semTriple_main. (* main := init_model() ;; loop() *)
    Proof.
      iIntros (m cp h i entries es mpp mepc_v) "Hloop_pre".
      cbn.
      unfold fun_main.
      iApply ((iris_rule_stm_seq env.nil (stm_call init_model _) (stm_call loop _) (loop_pre' m cp h i entries es mpp mepc_v) (fun _ => ∃ es, loop_pre' m Machine h i entries es mpp mepc_v)%I (fun _ _ => True%I)) with "[] [] Hloop_pre").


      2: {
        iIntros.
        destruct (env.nilView δ').
        unfold semTriple.
        iIntros "[%es' H]".
        iRevert "H".
        fold (semTriple env.nil (loop_pre' m Machine h i entries es' mpp mepc_v) (call loop) (fun _ _ => True)%I).
        iApply (@iris_rule_consequence _ _ _ _ _ _ (loop_pre' m Machine h i entries es' mpp mepc_v) _ _ _).
        3: {
          iApply (iris_rule_stm_call_inline env.nil loop env.nil _ (fun _ => True%I)).
          iApply valid_semTriple_loop'.
        }
        now iIntros.
        now iIntros.
      }


      unfold loop_pre'.
      iApply (@iris_rule_consequence _ _ _ _ _ _
                                     (
                                       ∃ es0 : list (Pmpcfg_ent * Z), Execution' m cp h i entries es0 mpp mepc_v ∗
                                                                                ▷ (CSRMod' m cp h i entries es0 mpp mepc_v -∗ WP_loop) ∗
                                                                                ▷ (Trap' m cp h i entries es0 mpp mepc_v -∗ WP_loop) ∗
                                                                                ▷ (Recover' m cp h i entries es0 mpp mepc_v -∗ WP_loop))%I
                                     _
                                     (fun _ _ =>
                                        ∃ es0 : list (Pmpcfg_ent * Z), Execution' m Machine h i entries es0 mpp mepc_v ∗
                                                                                 ▷ (CSRMod' m Machine h i entries es0 mpp mepc_v -∗ WP_loop) ∗
                                                                                 ▷ (Trap' m Machine h i entries es0 mpp mepc_v -∗ WP_loop) ∗
                                                                                 ▷ (Recover' m Machine h i entries es0 mpp mepc_v -∗ WP_loop))%I _).
      iIntros "H".
      iExists es; iFrame.
      now iIntros.
      unfold semTriple.
      iIntros "[%es' H]".
      iRevert "H".
      fold (semTriple env.nil
                      (Execution' m cp h i entries es' mpp mepc_v ∗
                                 ▷ (CSRMod' m cp h i entries es' mpp mepc_v -∗ WP_loop) ∗
                                 ▷ (Trap' m cp h i entries es' mpp mepc_v -∗ WP_loop) ∗
                                 ▷ (Recover' m cp h i entries es' mpp mepc_v -∗ WP_loop))%I (call init_model)
                      (fun _ _ => ∃ es0 : list (Pmpcfg_ent * Z), Execution' m Machine h i entries es0 mpp mepc_v ∗
                                                                           ▷ (CSRMod' m Machine h i entries es0 mpp mepc_v -∗ WP_loop) ∗
                                                                           ▷ (Trap' m Machine h i entries es0 mpp mepc_v -∗ WP_loop) ∗
                                                                           ▷ (Recover' m Machine h i entries es0 mpp mepc_v -∗ WP_loop))%I).
      iApply (@iris_rule_consequence _ _ _ _ _ _ _ _ (fun _ _ =>
                                                        Execution' m Machine h i entries es' mpp mepc_v ∗
                                                                  ▷ (CSRMod' m Machine h i entries es' mpp mepc_v -∗ WP_loop) ∗
                                                                  ▷ (Trap' m Machine h i entries es' mpp mepc_v -∗ WP_loop) ∗
                                                                  ▷ (Recover' m Machine h i entries es' mpp mepc_v -∗ WP_loop))%I _).
      iIntros "H"; iExact "H".
      iIntros (_ _) "H".
      iExists es'; iFrame.

      iApply iris_rule_consequence.
      iIntros "H".
      iApply (bi.sep_comm with "H").
      2: {
        iApply (iris_rule_frame _ _ (fun _ _ => Execution' m Machine h i entries es' mpp mepc_v)%I _).
        iApply (@iris_rule_consequence _ _ _ _ _ _ _ _ (fun _ _ => ∃ es, Execution' m Machine h i entries es mpp mepc_v)%I _).
        iIntros "H"; iExact "H".
        (* STUCK *)
        (* unfold Execution. *)
        (* iApply (@iris_rule_consequence _ _ _ _ _ _ ((reg_pointsTo mtvec h ∗ (∃, reg_pointsTo pc ∗ *)
        (*                                                           reg_pointsTo nextpc) ∗ *)
        (*                                                           (∃ mc : Val ty_exc_code, reg_pointsTo mcause mc ∗ reg_pointsTo mepc mepc_v ∗ *)
        (*                                                                                                 reg_pointsTo mstatus {| MPP := mpp |} ∗  *)
        (*                                                                                                 interp_pmp_addr_access liveAddrs entries m ∗ interp_gprs)) ∗  *)
        (*                                                                                                                                                            (reg_pointsTo cur_privilege cp ∗ ∃ es, interp_pmp_entries es)) _ _ _). *)
        (* iIntros "(Hacc & Hgprs & Hes & (% & Hmc) & Hmepc & (% & Hnpc & Hpc) & Hmt & Hms & Hme)". *)
        (* iFrame. *)
        (* iSplitR "Hes". *)
        (* iSplitL "Hnpc Hpc". *)
        (* iExists0; iFrame. *)
        (* now iExists mc. *)
        (* now iExists es'. *)
        (* 2: { *)
        (*   iApply (iris_rule_frame _ _ (fun _ _ => reg_pointsTo cur_privilege Machine ∗ ∃ es, interp_pmp_entries es)%I _). *)
        (*   iApply iris_rule_consequence. *)
        (*   3: { *)
        (*     iApply (iris_rule_stm_call_inline env.nil init_model env.nil _ (fun _ => _)). *)
        (*     iApply init_model_iprop. *)
        (*   } *)
        (*   iIntros "(HP & Hes)". *)
        (*   iSplitL "HP". *)
        (*   iExists cp; iFrame. *)
        (*   iExact "Hes". *)
        (*   iIntros (_ δ) "((Hcp & Hes) & %)". *)
        (*   iFrame. *)
        (* } *)
        (* iIntros (v δ) "((Hmt & (% & Hpc & Hnpc) & % & Hmc & Hmepc & Hms &Hacc & Hgprs) & (Hcp & [% Hes]))". *)
        (* iFrame. *)
        (* iExists es0; iFrame. *)
        (* iSplitL "Hmc". *)
        (* iExists mc; iFrame. *)
        (* iExists0; iFrame. *)
        admit.
        admit.
      }
      (*   iIntros (v δ) "[Hloop [% HP]]". *)
      (*   iExists es; iFrame. *)
      (*   - iIntros. *)
      (*     destruct (env.nilView δ). *)
      (*     unfold semTriple. *)
      (*     iDestruct "Hloop" as "(HCSRMod & HTrap & HRecover)". *)
      (*     iSplitL "HCSRMod". *)
      (*     unfold CSRMod. *)
      (*     iFrame. *)
      (*     (* pmp_entries es ≠ pmp_entries es0 *) *)

      (*     iIntros "[%es' H]". *)
      (*     iRevert "H". *)
      (*     fold (semTriple env.nil (loop_pre m Machine h i entries es' mpp mepc_v) (call loop) (fun _ _ => True)%I). *)
      (*     iApply (@iris_rule_consequence _ _ _ _ _ _ (loop_pre m Machine h i entries es' mpp mepc_v) _ _ _). *)
      (*     3: { *)
      (*       iApply (iris_rule_stm_call_inline env.nil loop env.nil _ (fun _ => True%I)). *)
      (*       iApply valid_semTriple_loop. *)
      (*     } *)
      (*     now iIntros. *)
      (*     now iIntros. *)
      (* Qed. *)
    Admitted.
  End OldLoop.
End Loop.
