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

  Local Notation "r '↦' val" := (reg_pointsTo r val) (at level 70).

  Definition Step_pre : iProp Σ :=
    interp_gprs interp ∗
    (∃ c, pc ↦ c ∗ interp (inr c) ∗ ⌜CorrectPC c⌝).

  Definition Step_post : iProp Σ :=
    interp_gprs interp ∗
    ((∃ c, pc ↦ c ∗ interp (inr c))
     ∨
     (∃ c, pc ↦ c ∗ interp_expression interp c)).

  Definition semTriple_step : iProp Σ :=
    IH -∗ semTriple [env] Step_pre (FunDef step) (fun _ _ => Step_post).

  Lemma valid_step_contract : ⊢ ValidContractSem fun_step sep_contract_step.
  Proof.
     iApply (contracts_sound $! _ _ step).
  Qed.

  Lemma valid_semTriple_step : ⊢ semTriple_step.
  Proof.
    iIntros "IH (Hregs & [%c (Hpc & Hsafe & Hcorrect)])".
    iApply (valid_step_contract $! [env]).
    cbn - [interp_gprs interp].
    iFrame.
    iExists c; iFrame.
  Qed.

  Definition semTriple_loop : iProp Σ :=
    IH -∗ semTriple [env] Step_pre (FunDef loop) (fun _ _ => True%I).

  Lemma valid_semContract_loop : ⊢ semTriple_loop.
  Proof.
    iIntros "#IH Hpre".
    unfold FunDef, fun_loop.
    iApply (semWP_seq (call step) (call loop)).
    iApply semWP_call_inline.
    iPoseProof (valid_semTriple_step with "IH Hpre") as "trip_step".
    iApply (semWP_mono with "trip_step").
    iIntros (_ _) "Hpost".
    iApply (semWP_call_inline_later loop).
    iDestruct "Hpost" as "(Hgprs & [[%c [Hpc' #Hsafe']] | [%c [Hpc' Hexpr]]])".
    - iModIntro.
      destruct c as [p b e a].
      by iApply ("IH" $! p b e a with "Hgprs Hpc'").
    - destruct c as [p b e a].
      cbn - [interp_gprs interp].
      iDestruct "Hexpr" as "[%Hp Hexpr]".
      subst.
      iModIntro.
      iDestruct "Hexpr" as "#Hexpr".
      iApply "Hexpr".
      iFrame.
  Qed.

  Import ctx.notations.
  Import env.notations.
  Import wptactics.

  Lemma semWP_is_perm {Γ} (e1 e2 : Exp Γ ty.perm) Q δ :
    ⊢ ((⌜eval e1 δ = eval e2 δ⌝ -∗ Q true δ) ∧
      (⌜is_perm (eval e1 δ) (eval e2 δ) = false⌝ -∗ Q false δ)) -∗
      semWP (call MinCapsProgram.is_perm e1 e2) Q δ.
  Proof.
    iIntros "HYP".
    iApply (semWP_call_inline MinCapsProgram.is_perm).
    iPoseProof (contracts_sound $! _ _ MinCapsProgram.is_perm) as "-#His_perm".
    rewrite valid_contract_curry.
    unfold ValidContractSemCurried, sep_contract_is_perm; cbn.
    iPoseProof ("His_perm" $! (eval e1 δ) (eval e2 δ) with "[%]") as "His_perm"; [by auto|].
    iApply (semWP_mono with "His_perm").
    iIntros ([] _) "[%H1 _]"; cbn in *; iApply "HYP".
    - auto.
    - unfold Not_is_perm in H1.
      now rewrite ?negb_true_iff in H1.
  Qed.

  Lemma is_correct_pc_false {c cpc} : decide_correct_pc c = cpc ->
    ⊢ semWP (FunDef is_correct_pc) (fun x y => ⌜ x = cpc ⌝ ) [env].[ "c" ∷ ty.cap ↦ c ].
  Proof.
    destruct c as [p b e a]. cbn.
    intros Heq. iIntros.
    kEval. kStep. kStep. cbn. kStep.
    iApply semWP_is_perm; cbn. iSplit.
    - iIntros "%H1". subst p. cbn in *. kStep.
      iApply semWP_is_perm; cbn. iSplit.
      iIntros "%H1". discriminate.
      iIntros "_". kStep. kStep. cbn.
      kStep; rewrite semWP_val; auto.
    - iIntros "%H1". kStep.
      iApply semWP_is_perm; cbn. iSplit.
      iIntros "%H2". subst p. cbn in *. kStep.
      cbn. kStep. cbn.
      kStep; rewrite semWP_val; auto.
      iIntros "%H2". kStep. kStep. cbn.
      rewrite andb_false_r.
      rewrite semWP_val.
      iPureIntro. subst.
      rewrite H1 H2.
      now rewrite ?andb_false_r.
  Qed.

  Lemma wrongPC_crashes_step {c Q} : decide_correct_pc c = false ->
                              ⊢ semTriple [env] (pc ↦ c) (FunDef step) Q.
  Proof.
    iIntros (wrongPC) "Hpc".
    unfold FunDef, fun_step.
    iApply semWP_let.
    iApply semWP_read_register.
    iExists c; iFrame.
    iIntros "Hpc".
    iApply semWP_let.
    iApply semWP_call_inline.
    cbn.
    iApply (semWP_mono $! (is_correct_pc_false wrongPC)).
    iIntros (? _ Heq). subst.
    unfold stm_if.
    kStep. kStep. kEval.
    now rewrite semWP_fail.
  Qed.

  Lemma wrongPC_crashes {c Q} : decide_correct_pc c = false ->
                              ⊢ semTriple [env] (pc ↦ c) (FunDef loop) Q.
  Proof.
    iIntros (wrongPc) "Hpc".
    unfold FunDef, fun_loop.
    iApply semWP_seq.
    iApply semWP_call_inline.
    now iApply (wrongPC_crashes_step wrongPc).
  Qed.

  (* and now without the IH. *)
  Lemma valid_semContract_loop2 : ⊢ semTriple [env] Step_pre (FunDef loop) (fun _ _ => True%I).
  Proof.
    iIntros.
    iLöb as "IH".
    iApply valid_semContract_loop.
    do 2 iModIntro.
    iIntros (p b e a) "Hgprs Hpc #Hpcvalid".
    remember (decide_correct_pc {| cap_permission := p; cap_begin := b; cap_end := e; cap_cursor := a |}) as dcpc.
    destruct dcpc.
    - iApply "IH".
      iFrame.
      iExists _.
      iFrame.
      iSplitL; try iAssumption.
      iPureIntro.
      now unfold CorrectPC.
    - unfold interp_loop.
      iApply (wrongPC_crashes (Q := fun _ _ => True)%I); try iFrame.
      now symmetry.
  Qed.

End Loop.
