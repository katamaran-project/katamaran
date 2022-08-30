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
     MinimalCaps.Machine
     MinimalCaps.Model
     MinimalCaps.Contracts.

From iris.base_logic Require lib.gen_heap lib.iprop.
From iris.base_logic Require Export invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac.
From iris.program_logic Require Import weakestpre adequacy.
From iris.proofmode Require Import string_ident tactics.

Set Implicit Arguments.
Import ListNotations.
Import MinCapsSpecification.
Import MinCapsProgram.
Import MinCapsIrisBase.
Import MinCapsIrisInstance.
Import MinCapsIrisInstanceWithContracts.
Import MinCapsValidContracts.

Import MinCapsSignature.
Module Import MinCapsShallowExecutor :=
  MakeShallowExecutor MinCapsBase MinCapsProgram MinCapsSignature MinCapsSpecification.

Module Import MinCapsShallowSoundness := MakeShallowSoundness MinCapsBase MinCapsProgram MinCapsSignature MinCapsSpecification MinCapsShallowExecutor MinCapsIrisInstanceWithContracts.

Module Import MinCapsSymbolic := MakeSymbolicSoundness MinCapsBase MinCapsProgram MinCapsSignature MinCapsSpecification MinCapsSolver MinCapsShallowExecutor MinCapsExecutor.

Section Loop.
  Context `{sg : sailGS Σ}.
  Import env.notations.

  Definition step_sem_contract :=
    Eval cbn  in ValidContractSemCurried fun_step sep_contract_step.

  Local Notation "r '↦' val" := (reg_pointsTo r val) (at level 70).

  Print step_sem_contract.

  Definition Step_pre : iProp Σ :=
    interp_gprs interp ∗
    (∃ c, pc ↦ c ∗ interp (inr c) ∗ ⌜CorrectPC c⌝) ∗
    IH.

  Definition Step_post : iProp Σ :=
    interp_gprs interp ∗
    ((∃ c, pc ↦ c ∗ interp (inr c))
     ∨
     (∃ c, pc ↦ c ∗ interp_expression interp c)).

  Definition semTriple_step : iProp Σ :=
    semTriple [env] Step_pre (FunDef step) (fun _ _ => Step_post).

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

  Lemma valid_step_semTriple : ⊢ semTriple_step.
  Proof.
    unfold semTriple_step.
    iIntros.
    iApply (@iris_rule_consequence _ _ _ _ [env] Step_pre _ _ _ fun_step _ _).
    iApply valid_step_contract.
    Unshelve.
    3: exact [env].
    unfold Step_pre.
    cbn - [interp_gprs].
    iIntros "(Hgprs & [%c (Hpc & Hsafe & Hcorrect)] & IH)".
    iFrame.
    iExists c; iFrame.
    unfold Step_post.
    iIntros (v _) "(Hgprs & [H|H])";
      cbn - [interp interp_gprs interp_expression]; iFrame.
  Qed.

  Lemma simplify_semTriple_pre_add : forall Γ (e : CStore Γ) τ δ P Q (s : Stm Γ τ),
      (@semTriple _ _ Γ τ δ P s Q) ⊢ (@semTriple _ _ Γ τ δ (P ∧ ⌜e = e⌝) s Q).
  Proof.
    intros; iIntros "H".
    iApply iris_rule_consequence.
    - iIntros "[HP _]"; iExact "HP".
    - auto.
    - iExact "H".
  Qed.

  Lemma simplify_semTriple_pre : forall Γ (e : CStore Γ) τ δ P Q (s : Stm Γ τ),
      (@semTriple _ _ Γ τ δ P s Q) ⊣⊢ (@semTriple _ _ Γ τ δ (P ∧ ⌜e = e⌝) s Q).
  Proof.
    iIntros.
    iSplit; iIntros "H"; first iApply (simplify_semTriple_pre_add with "H").
    iApply (@iris_rule_consequence _ _ _ _ _  _ (P ∧ ⌜e = e⌝) _ _ _ _ _).
    iExact "H".
    Unshelve.
    all: auto.
  Qed.

  Lemma simplify_semTriple_post_add : forall (e : CStore ctx.nil) τ δ P (Q : Val τ → CStore ctx.nil → iProp Σ) (s : Stm ctx.nil τ),
      (@semTriple _ _ ctx.nil τ δ P s Q) ⊢ (@semTriple _ _ ctx.nil τ δ P s (fun v (δ : CStore ctx.nil) => Q v δ ∧ ⌜[env] = δ⌝)).
  Proof.
    intros; iIntros "H".
    iApply iris_rule_consequence.
    iIntros "H"; iExact "H".
    iIntros (v δ') "H".
    iSplit; first iExact "H".
    now destruct (env.nilView δ').
    iApply "H".
  Qed.

  Lemma simplify_semTriple_post_remove : forall (e : CStore ctx.nil) τ δ P (Q : Val τ → CStore ctx.nil → iProp Σ) (s : Stm ctx.nil τ),
       (@semTriple _ _ ctx.nil τ δ P s (fun v (δ : CStore ctx.nil) => Q v δ ∧ ⌜[env] = δ⌝)) ⊢ (@semTriple _ _ ctx.nil τ δ P s Q).
  Proof.
    intros; iIntros "H".
    iApply iris_rule_consequence.
    3: iApply "H".
    done.
    now iIntros (v δ') "[H _]".
  Qed.

  Definition semTriple_loop : iProp Σ :=
    semTriple [env] Step_pre (FunDef loop) (fun _ _ => True%I).

  Lemma valid_semTriple_loop : ⊢ semTriple_loop.
  Proof.
    iLöb as "H".
    Print Step_pre.
    iIntros "(Hgprs & [%c (Hpc & #Hsafe & %Hcor)] & #IH)".
    cbn - [interp interp_gprs].
    unfold fun_loop.
    iApply (iris_rule_stm_seq [env] (stm_call step _) (stm_call loop _)
                                _ (fun δ => Step_post ∧ ⌜[env] = δ⌝)%I (fun _ _ => True%I)).
    - iApply (iris_rule_stm_call_inline [env] step [env] Step_pre (fun _ => Step_post)).
      iApply valid_step_semTriple.
    - iIntros.
      destruct (env.nilView δ').
      iApply simplify_semTriple_pre_add.
      iApply simplify_semTriple_post_remove; first constructor.
      cbn - [interp interp_gprs].
      iIntros "(Hgprs & [[%c' [Hpc' #Hsafe']] | [%c' [Hpc' Hexpr]]])".
      + iApply (iris_rule_stm_call_inline_later [env] loop [env] True%I (fun _ => True%I) with "[Hgprs Hpc']"); auto.
        iModIntro.
        iIntros "_".
        destruct c' as [p b e a]; iApply ("IH" $! p b e a with "Hgprs Hpc' Hsafe'").
      + destruct c' as [p b e a]; cbn - [interp interp_gprs]; iDestruct "Hexpr" as "[%Hp Hexpr]"; try discriminate; subst.
        iApply (iris_rule_stm_call_inline_later [env] loop [env] True%I (fun _ => True%I) with "[Hgprs Hpc' Hexpr]"); auto.
        iModIntro.
        iDestruct "Hexpr" as "#Hexpr".
        iIntros "_". iApply "Hexpr".
        iSplitR "Hgprs".
        iAssumption.
        iAssumption.
    - unfold Step_pre.
      iFrame.
      iSplit; try iAssumption.
      iExists c; iFrame.
      iSplit.
      + iApply "Hsafe".
      + iPureIntro; auto.
  Qed.
End Loop.
