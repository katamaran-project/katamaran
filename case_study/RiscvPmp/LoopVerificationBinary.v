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
Import RiscvPmpModel2.RiscvPmpIrisInstance2.
Import RiscvPmpValidContracts.
Import IrisInstance.RiscvPmpIrisInstancePredicates.
Import RiscvPmpIrisInstancePredicates2.

Import RiscvPmpSignature.
Module Import RiscvPmpShallowExecutor :=
  MakeShallowExecutor RiscvPmpBase RiscvPmpSignature RiscvPmpProgram DefaultFailLogic RiscvPmpSpecification.

Module Import RiscvPmpShallowSoundness := MakeShallowSoundness RiscvPmpBase RiscvPmpSignature RiscvPmpProgram DefaultFailLogic RiscvPmpSpecification RiscvPmpShallowExecutor RiscvPmpProgramLogic.

Module Import RiscvPmpSymbolic := MakeSymbolicSoundness RiscvPmpBase RiscvPmpSignature RiscvPmpProgram DefaultFailLogic RiscvPmpSpecification RiscvPmpShallowExecutor RiscvPmpExecutor.

Import LVars (LVars, lvars_valuation, lvars_update_i).

Section Loop.
  Context `{sg : sailGS2 Σ}.

  Definition step_sem_contract :=
    Eval cbn  in ValidContractSemCurried fun_step sep_contract_step.

  Definition Step_pre (lvars : LVars) : iProp Σ :=
    asn.interpret (sep_contract_precondition sep_contract_step) (lvars_valuation lvars).

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
    Definition extract_disjunct (lvars : LVars) (f : Disjuncts -> Disjunct) : iProp Σ :=
      match disjuncts with
      | Some ds => asn.interpret (f ds) (env.snoc (lvars_valuation lvars) (_∷ty.unit) tt)
      | None    => True
      end.

    Definition Execution (lvars : LVars) : iProp Σ :=
      extract_disjunct lvars D_Execution.
    Definition M_CSRMod (lvars : LVars) : iProp Σ :=
      extract_disjunct lvars D_M_CSRMod.
    Definition S_CSRMod (lvars : LVars) : iProp Σ :=
      extract_disjunct lvars D_S_CSRMod.
    Definition M_Trap (lvars : LVars) : iProp Σ :=
      extract_disjunct lvars D_M_Trap.
    Definition S_Trap (lvars : LVars) : iProp Σ :=
      extract_disjunct lvars D_S_Trap.
    Definition MRET (lvars : LVars) : iProp Σ :=
      extract_disjunct lvars D_MRET.
    Definition SRET (lvars : LVars) : iProp Σ :=
      extract_disjunct lvars D_SRET.
    (* Step_post is not a "TransitionTarget" but simply groups the possibilities
       back together using disjunction. *)
    Definition Step_post (lvars : LVars) : iProp Σ :=
      Execution lvars
      ∨ M_CSRMod lvars
      ∨ S_CSRMod lvars
      ∨ M_Trap lvars
      ∨ S_Trap lvars
      ∨ MRET lvars
      ∨ SRET lvars.

  End TransitionTargets.

  Definition semTriple_step : iProp Σ :=
    (∀ (lvars : LVars),
        semTriple env.nil (Step_pre lvars)
                  (FunDef step)
                  (fun _ _ => Step_post lvars))%I.

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
    iIntros (lvars) "H".
    iApply (semWP2_mono with "[-]").
    iApply (valid_step_contract with "H").
    cbn. unfold Step_post.
    iIntros ([v1|e1] δ1 v2 δ2) "(<- & <- & H)"; auto.
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
    iIntros (v δ) "H".
    iDestruct "H" as "([-> _] & Hcp & Hpmp)".
    iFrame "Hcp Hpmp".
    constructor.
  Qed.

  Definition loop_pre (lvars : LVars) : iProp Σ :=
    (Step_pre lvars ∗
     ▷ (M_CSRMod lvars -∗ WP2_loop) ∗
     ▷ (S_CSRMod lvars -∗ WP2_loop) ∗
     ▷ (M_Trap lvars -∗ WP2_loop) ∗
     ▷ (S_Trap lvars -∗ WP2_loop) ∗
     ▷ (MRET lvars -∗ WP2_loop) ∗
     ▷ (SRET lvars -∗ WP2_loop))%I.

  Definition semTriple_loop : iProp Σ :=
    (∀ (lvars : LVars),
        semTriple env.nil (loop_pre lvars)
                  (FunDef loop)
                  (fun _ _ => True))%I.

  Lemma valid_semTriple_loop : ⊢ semTriple_loop.
  Proof.
    iLöb as "H".
    iIntros (lvars) "(HStep & HM_CSRMod & HS_CSRMod & HM_Trap & HS_Trap & HMRET & HSRET)".
    unfold fun_loop.
    iApply (semWP2_seq (call step) (call step) (call loop) (call loop)).
    iApply semWP2_call_inline_later.
    iApply (semWP2_mono with "[HStep]").
    iApply (valid_step_semTriple with "HStep").
    iModIntro.
    iIntros ([v1|m1] δ1 v2 δ2) "(<- & <- & HRes)";
      last now iApply semWP2_fail.
    iDestruct "HRes" as "[HRes | [HRes | [HRes | [HRes | [HRes | [HRes | HRes]]]]]]";
      iApply (semWP2_call_inline loop _).
    - iDestruct "HRes" as "(? & ? & ? & ? & ? & ? & (%i' & ? & ?) & ?)".
      iSpecialize ("H" $! (lvars_update_i lvars i') with "[-]").
      { unfold loop_pre, lvars_update_i; destruct lvars; cbn; now iFrame. }
      iApply (semWP2_mono with "H").
      iIntros (v δ v' δ') "(<- & <- & _)"; repeat iSplit; auto.
      by case_match.
    - iSpecialize ("HM_CSRMod" with "HRes").
      iApply (semWP2_mono with "HM_CSRMod").
      iIntros ([] ? ? ?) "(<- & <-)"; auto.
    - iSpecialize ("HS_CSRMod" with "HRes").
      iApply (semWP2_mono with "HS_CSRMod").
      iIntros ([] ? ? ?) "(<- & <-)"; auto.
    - iSpecialize ("HM_Trap" with "HRes").
      iApply (semWP2_mono with "HM_Trap").
      iIntros ([] ? ? ?) "(<- & <-)"; auto.
    - iSpecialize ("HS_Trap" with "HRes").
      iApply (semWP2_mono with "HS_Trap").
      iIntros ([] ? ? ?) "(<- & <-)"; auto.
    - iSpecialize ("HMRET" with "HRes").
      iApply (semWP2_mono with "HMRET").
      iIntros ([] ? ? ?) "(<- & <-)"; auto.
    - iSpecialize ("HSRET" with "HRes").
      iApply (semWP2_mono with "HSRET").
      iIntros ([] ? ? ?) "(<- & <-)"; auto.
  Qed.
End Loop.
