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
     ZArith.ZArith
     Strings.String
     Lists.List.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Iris.Instance
     Iris.Base
     Notations
     Bitvector
     Sep.Hoare
     Specification
     MicroSail.ShallowExecutor
     MicroSail.ShallowSoundness
     MicroSail.SymbolicExecutor
     MicroSail.RefineExecutor
     MicroSail.Soundness
     RiscvPmp.PmpCheck
     RiscvPmp.IrisModelBinary
     RiscvPmp.IrisInstanceBinary
     RiscvPmp.Machine
     RiscvPmp.Sig
     RiscvPmp.Contracts
     RiscvPmp.BlockVer.Spec
     RiscvPmp.BlockVer.TotalVerifier.
From Katamaran Require RiscvPmp.ModelBinary.

Import RiscvPmpProgram.
Import RiscvPmpIrisInstancePredicates2.
Import ListNotations.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import env.notations.

Import RiscvPmpIrisBase2.

Module RiscvPmpBlockVerifIrisInstance2 := RiscvPmpIrisInstance2 RiscvPmpBlockVerifFailLogic.

Module Import BinaryBlockVerifierNotations.
  Notation "a '↦' t" := (reg_pointsTo21 a t) (at level 70).
  Notation "a '↦ₘ' t" := (interp_ptsto a t) (at level 70).
End BinaryBlockVerifierNotations.

Module BinaryBlockVerifier.
  Import iris.base_logic.lib.iprop iris.proofmode.tactics.
  Import RiscvPmpBlockVerifIrisInstance2.

  (* TODO: annoying, but not inj in general (illegal instructions...)
           Decode (at least the Sail one) does seem to be injective
           for legal instructions. Another option would be to
           change interp_ptsto_instr to talk about the *encoding* of an
           instruction and no longer have the existential there.
           Also requires that ∀ i, (decode ∘ encode) i = i *)
  Axiom pure_decode_inr_inj : forall {v1 v2 : bv 32} {instr : AST},
    pure_decode v1 = inr instr ->
    pure_decode v2 = inr instr ->
    v1 = v2.

  Section WithSailGS2.
    Context {Σ} {GS : sailGS2 Σ}.

    Fixpoint ptsto_instrs (a : Val ty_xlenbits) (instrs : list AST) : iProp Σ :=
      match instrs with
      | cons inst insts => (interp_ptsto_instr a inst ∗ ptsto_instrs (bv.add a bv_instrsize) insts)%I
      | nil => True%I
      end.

    Lemma ptsto_instrs_equiv {a : Val ty_xlenbits} {instrs : list AST} :
      ptsto_instrs a instrs ⊣⊢
        @TotalVerifier.ptsto_instrs _ sailGS2_sailGS_left a instrs
        ∗ @TotalVerifier.ptsto_instrs _ sailGS2_sailGS_right a instrs.
    Proof.
      revert a.
      iInduction instrs as [|instr instrs] "IH";
        cbn; auto.
      iIntros (a). iSplit.
      - iIntros "(Hinstr & Hinstrs)".
        iDestruct ("IH" with "Hinstrs") as "($ & $)".
        iDestruct "Hinstr" as "(% & [Hl Hr] & %Hdecode)".
        iSplitL "Hl".
        + iExists _; iFrame "Hl"; auto.
        + iExists _; iFrame "Hr"; auto.
      - iIntros "([Hinstrl Hinstrsl] & [Hinstrr Hinstrsr])".
        iDestruct ("IH" with "[$Hinstrsl $Hinstrsr]") as "$".
        iDestruct "Hinstrl" as "(%vl & Hl & %Hdecodel)".
        iDestruct "Hinstrr" as "(%vr & Hr & %Hdecoder)".
        pose proof (pure_decode_inr_inj Hdecodel Hdecoder) as <-.
        iExists _; iFrame "Hl Hr"; auto.
    Qed.

    Definition exec_instructions_prologue (a : Val ty_xlenbits) (l : list AST) : iProp Σ :=
      pc ↦ a ∗
      ptsto_instrs a l ∗
      ∃ v, nextpc ↦ v.

    Definition exec_instructions_epilogue (a an : Val ty_xlenbits) (l : list AST) : iProp Σ :=
      pc ↦ an ∗
      ptsto_instrs a l ∗
      ∃ v, nextpc ↦ v.

    Fixpoint step_n (instrs : list AST) (ainstr apc : Val ty_xlenbits) (POST : Val ty_xlenbits -> iProp Σ) : iProp Σ :=
      match instrs with
      | []   => POST apc
      | i :: instrs =>
          let Σ := [env].["a"∷ty_xlenbits ↦ ainstr] in
          ⌜ainstr = apc⌝
          ∗ (asn.interpret (exec_instruction_prologue i) Σ  -∗
               semWP2 [env] [env] fun_step fun_step
                 (λ v1 δ1 v2 δ2, ⌜v1 = v2⌝ ∗ ⌜δ1 = δ2⌝ ∗
                     match v1 with
                     | inl v =>
                         ∃ na, asn.interpret (exec_instruction_epilogue i) Σ.["an"∷ty_xlenbits ↦ na]
                               ∗ step_n instrs (bv.add ainstr bv_instrsize) na POST
                     | inr _ =>
                       if RiscvPmpBlockVerifFailLogic.fail_rule_pre
                       then True
                       else False
                      end)%I)
      end.

    Lemma step_n_mono {instrs : list AST} {a apc : Val ty_xlenbits} {POST1 POST2 : Val ty_xlenbits -> iProp Σ} :
      step_n instrs a apc POST1 -∗
      (∀ an, POST1 an -∗ POST2 an) -∗
      step_n instrs a apc POST2.
    Proof.
      revert a apc.
      iInduction instrs as [|instr instrs]; iIntros (a apc) "H HPOSTS".
      - cbn. now iApply "HPOSTS".
      - cbn. iDestruct "H" as "(<- & H)". iSplitR; first auto.
        iIntros "Hpro". iSpecialize ("H" with "Hpro").
        iApply (semWP2_mono with "H").
        iIntros ([] ? ? ?) "(<- & <- & H)"; auto.
        iDestruct "H" as "(%na & $ & H)".
        repeat iSplitR; auto.
        iApply ("IHinstrs" with "H HPOSTS").
    Qed.

    Definition stepTriple (l : list AST) (a apc : Val ty_xlenbits)
      (PRE : Val ty_xlenbits -> iProp Σ) (POST : Val ty_xlenbits -> Val ty_xlenbits -> iProp Σ) : iProp Σ :=
      PRE a -∗
        step_n l a apc (POST a).

    Definition semTripleBlock (PRE : Val ty_xlenbits -> iProp Σ) (a : Val ty_xlenbits) (instrs : list AST) (POST : Val ty_xlenbits -> Val ty_xlenbits -> iProp Σ) : iProp Σ :=
      stepTriple instrs a a PRE POST.

    Lemma WP2_loop_step_once : ∀ POST,
      semWP2 [env] [env] fun_step fun_step (λ v1 δ1 v2 δ2, ⌜v1 = v2⌝ ∗ ⌜δ1 = δ2⌝ ∗ POST v1 δ1 v2 δ2) -∗
      (∀ v1 δ1 v2 δ2, POST v1 δ1 v2 δ2 -∗ WP2_loop) -∗
      WP2_loop.
    Proof.
      iIntros (POST) "H Hk".
      unfold WP2_loop at 2.
      cbn [FunDef]. unfold fun_loop.
      iApply semWP2_seq.
      iApply semWP2_call_inline_later. simpl. iModIntro.
      iApply (semWP2_mono with "H").
      iIntros (? ? [] δ2) "(-> & -> & H)".
      - iApply semWP2_call_inline.
        iSpecialize ("Hk" with "H").
        iApply (semWP2_mono with "Hk").
        now iIntros (? ? ? ?) "(<- & <-)".
      - now iApply semWP2_fail.
    Qed.

    Lemma WP2_loop_semTripleBlock : ∀ PRE a instrs POST,
      (exec_instructions_prologue a instrs) -∗
      (PRE a) -∗
      semTripleBlock PRE a instrs POST -∗
      (∀ an, POST a an ∗ exec_instructions_epilogue a an instrs -∗ WP2_loop) -∗
      WP2_loop.
    Proof.
      iIntros (PRE a instrs).
      iRevert (PRE a).
      iInduction instrs as [|instr instrs] "IH";
        iIntros (PRE a POST) "Hpro HPRE Htrip Hk".
      - cbn. iSpecialize ("Htrip" with "HPRE").
        iApply ("Hk" with "[$Htrip $Hpro]").
      - cbn. iDestruct ("Htrip" with "HPRE") as "(_ & Htrip)". fold step_n.
        iDestruct "Hpro" as "(Hpc & Hinstrs & Hnpc)"; cbn.
        iDestruct "Hinstrs" as "(Hinstr & Hinstrs)".
        iSpecialize ("Htrip" with "[$]").
        unfold WP2_loop at 4.
        cbn [FunDef]. unfold fun_loop.
        iApply semWP2_seq.
        iApply semWP2_call_inline. simpl.
        iApply (semWP2_mono with "Htrip").
        iIntros ([] ? ? ?) "(<- & <- & H)"; auto.
        iDestruct "H" as "(%na & (Hpc & Hinstr & Hnpc) & Htrip)".
        iApply semWP2_call_inline.
        destruct instrs.
        + cbn.
          iSpecialize ("Hk" with "[$Htrip $Hpc $Hinstr $Hnpc]").
          iApply (semWP2_mono with "Hk").
          now iIntros (? ? ? ?) "(<- & <-)".
        + cbn. iDestruct "Htrip" as "(<- & Htrip)".
          iSpecialize ("IH" $! (λ _, True)%I _ (λ a' an, ⌜a' = bv.add a bv_instrsize⌝ ∗ POST a an)%I with "[$Hpc $Hinstrs $Hnpc] [] [Htrip] [Hinstr Hk]"); auto.
          { iIntros "_". iSplitR; first auto. iIntros "H".
            iSpecialize ("Htrip" with "H"). iApply (semWP2_mono with "Htrip").
            iIntros ([] ? ? ?) "(<- & <- & H)"; auto.
            repeat iSplitR; auto.
            iDestruct "H" as "(%na & Hepi & H)". iExists na. iFrame "Hepi".
            iApply (step_n_mono with "H").
            iIntros (an) "$"; auto. }
          { iIntros (an) "([% HPOST] & Hpc & Hinstrs & Hnpc)".
            iApply "Hk". iFrame "HPOST Hpc Hnpc Hinstr Hinstrs". }
          iApply (semWP2_mono with "IH").
          now iIntros (? ? ? ?) "(<- & <-)".
    Qed.

    Lemma WP2_loop_semTripleBlock_later : ∀ PRE a instr instrs POST,
      (exec_instructions_prologue a (instr :: instrs)) -∗
      (PRE a) -∗
      semTripleBlock PRE a (instr :: instrs) POST -∗
      ▷ (∀ an, POST a an ∗ exec_instructions_epilogue a an (instr :: instrs) -∗ WP2_loop) -∗
      WP2_loop.
    Proof.
      iIntros (PRE a instr instrs).
      iRevert (PRE a instr).
      iInduction instrs as [|i instrs] "IH";
        iIntros (PRE a instr POST) "Hpro HPRE Htrip Hk".
      - cbn. iDestruct ("Htrip" with "HPRE") as "(_ & Htrip)".
        iSpecialize ("Htrip" with "[Hpro]").
        { cbn. iDestruct "Hpro" as "($ & [$ _] & $)". }
        unfold WP2_loop at 2.
        cbn [FunDef]. unfold fun_loop.
        iApply semWP2_seq.
        iApply semWP2_call_inline_later.
        iModIntro.
        iApply (semWP2_mono with "Htrip").
        iIntros ([] ? ? ?) "(<- & <- & H)"; auto.
        iDestruct "H" as "(%na & (Hpc & Hinstr & Hnpc) & Htrip)".
        iApply semWP2_call_inline.
        iSpecialize ("Hk" with "[$Htrip $Hpc $Hnpc $Hinstr]").
        iApply (semWP2_mono with "Hk").
        now iIntros (? ? ? ?) "(<- & <-)".
      - cbn. iDestruct ("Htrip" with "HPRE") as "(_ & Htrip)". fold step_n.
        iDestruct "Hpro" as "(Hpc & Hinstrs & Hnpc)"; cbn.
        iDestruct "Hinstrs" as "(Hinstr & Hinstrs)".
        iSpecialize ("Htrip" with "[$]").
        unfold WP2_loop at 4.
        cbn [FunDef]. unfold fun_loop.
        iApply semWP2_seq.
        iApply semWP2_call_inline_later.
        iModIntro.
        iApply (semWP2_mono with "Htrip").
        iIntros ([] ? ? ?) "(<- & <- & H)"; auto.
        iDestruct "H" as "(%na & (Hpc & Hinstr & Hnpc) & Htrip)".
        iApply semWP2_call_inline.
        iDestruct "Htrip" as "(<- & Htrip)".
        iSpecialize ("IH" $! (λ _, True)%I (bv.add a bv_instrsize) i (λ _, POST a) with "[$Hpc $Hinstrs $Hnpc] [] [Htrip] [Hinstr Hk]");
          first auto.
        + iIntros "_".
          iSplitR; first auto. fold step_n.
          iExact "Htrip".
        + iModIntro.
          iIntros (an) "(HPOST & Hepi)".
          iApply ("Hk" with "[$HPOST $Hinstr $Hepi]").
        + iApply (semWP2_mono with "IH").
          now iIntros (? ? ? ?) "(<- & <-)".
    Qed.

    Lemma step_n_focus (instrs : list AST) (ainstr apc : Val ty_xlenbits) (POST1 POST2 POST : Val ty_xlenbits -> iProp Σ) :
      @TotalVerifier.step_n _ sailGS2_sailGS_left instrs ainstr apc POST1 -∗
      @TotalVerifier.step_n _ sailGS2_sailGS_right instrs ainstr apc POST2 -∗
      (∀ na1 na2, POST1 na1 ∗ POST2 na2 -∗ ⌜na1 = na2⌝ ∗ POST na1) -∗
      step_n instrs ainstr apc POST.
    Proof.
      revert ainstr apc.
      iInduction instrs as [|instr instrs] "IH";
        iIntros (ainstr apc) "H1 H2 HPOST".
      - cbn. now iDestruct ("HPOST" with "[$H1 $H2]") as "(_ & $)".
      - cbn.
        iDestruct "H1" as "(<- & H1)".
        iDestruct "H2" as "($ & H2)".
        iIntros "([Hpc1 Hpc2] & (% & [Hinstr1 Hinstr2] & %) & (%npc & Hnpc1 & Hnpc2))".
        iSpecialize ("H1" with "[$Hpc1 Hinstr1 $Hnpc1]").
        { iExists _; now iFrame "Hinstr1". }
        iSpecialize ("H2" with "[$Hpc2 Hinstr2 $Hnpc2]").
        { iExists _; now iFrame "Hinstr2". }
        iApply (semWP2_focus with "H1 H2").
        iIntros ([v1|] δ1 [v2|] δ2) "(H1 & H2)"; auto.
        destruct v1, v2, (env.view δ1), (env.view δ2).
        repeat iSplitR; auto.
        destruct instrs as [|instr' instrs].
        + cbn.
          iDestruct "H1" as "(%na' & (Hpc1 & Hinstr1 & Hnpc1) & HPOST1)".
          iDestruct "H2" as "(% & (Hpc2 & Hinstr2 & Hnpc2) & HPOST2)".
          iDestruct ("HPOST" with "[$HPOST1 $HPOST2]") as "(<- & HPOST)".
          iExists na'. iFrame "Hpc1 Hpc2 Hnpc1 Hnpc2 HPOST".
          unfold interp_ptsto_instr.
          iDestruct "Hinstr1" as "(%v1 & Hinstr1 & %Hdec1)".
          iDestruct "Hinstr2" as "(%v2 & Hinstr2 & %Hdec2)".
          pose proof (pure_decode_inr_inj Hdec1 Hdec2) as <-.
          iExists v1. now iFrame "Hinstr1 Hinstr2".
        + iDestruct "H1" as "(% & (Hpc1 & Hinstr1 & Hnpc1) & <- & H1)".
          iDestruct "H2" as "(% & (Hpc2 & Hinstr2 & Hnpc2) & <- & H2)".
          iExists (bv.add ainstr bv_instrsize).
          iFrame "Hpc1 Hpc2 Hnpc1 Hnpc2".
          iSplitL "Hinstr1 Hinstr2".
          { unfold interp_ptsto_instr.
            iDestruct "Hinstr1" as "(%v1 & Hinstr1 & %Hdec1)".
            iDestruct "Hinstr2" as "(%v2 & Hinstr2 & %Hdec2)".
            pose proof (pure_decode_inr_inj Hdec1 Hdec2) as <-.
            iExists v1. now iFrame "Hinstr1 Hinstr2". }
          iApply ("IH" with "[$H1] [$H2]"); auto.
    Qed.

  End WithSailGS2.
End BinaryBlockVerifier.
