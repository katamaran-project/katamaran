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
From RiscvPmp Require Import
     Machine
     Model
     Contracts.
From Katamaran Require Import
     Bitvector
     Environment
     Program
     Specification
     Sep.Hoare
     Sep.Logic
     Semantics
     Iris.Model.

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
Import RiscvPmpModel.
Import RiscvPmpIrisHeapKit.
Import RiscvPmpIrisInstance.

Section Loop. 
     Context `{sg : sailGS Σ}.
     Context `{mG : memGS Σ}.
     Definition step_sem_contract := 
       Eval cbn  in ValidContractSemCurried fun_step sep_contract_step.

     Local Notation "r '↦' val" := (reg_pointsTo r val).

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

     (* Executing normally *)
     (* TODO: this should be the same as Start of iteration (P), drop one of them *)
     Definition Execution (m cp : Privilege) (h i : Z) (entries es : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v npc : Z) :=
       (            interp_pmp_addr_access liveAddrs entries m ∗
                    interp_gprs ∗
                    interp_pmp_entries es ∗
        (∃ mc : Z,  mcause        ↦ mc) ∗
                    cur_privilege ↦ cp ∗
        (∃ npc : Z, nextpc        ↦ npc ∗
                    pc            ↦ npc) ∗
                    mtvec         ↦ h ∗
                    mstatus       ↦ {| MPP := mpp |} ∗
                    mepc          ↦ mepc_v)%I.

     (* Modified CSRs, requires Machine mode *)
     Definition CSRMod (m cp : Privilege) (h i : Z) (entries es : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v npc : Z) :=
       (                               interp_pmp_addr_access liveAddrs entries m ∗
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
     Definition Trap (m cp : Privilege) (h i : Z) (entries es : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v npc : Z) :=
                  (interp_pmp_addr_access liveAddrs entries m ∗
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
     Definition Recover (m cp : Privilege) (h i : Z) (entries es : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v npc : Z) :=
                  (interp_pmp_addr_access liveAddrs entries m ∗
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

     Definition step_post (m cp : Privilege) (h i : Z) (entries es : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v npc : Z) : iProp Σ :=
        (Execution m cp h i entries es mpp mepc_v npc ∨
         CSRMod    m cp h i entries es mpp mepc_v npc ∨
         Trap      m cp h i entries es mpp mepc_v npc ∨
         Recover   m cp h i entries es mpp mepc_v npc)%I.

     Definition semTriple_step : iProp Σ :=
       (∀ (m cp : Privilege) (h i : Z) (entries es : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v npc : Z),
           semTriple env.nil (Execution m cp h i entries es mpp mepc_v npc) (FunDef step) (fun _ _ => step_post m cp h i entries es mpp mepc_v npc))%I.

     Definition semTriple_init_model : iProp Σ :=
       semTriple env.nil
                 ((∃ p, reg_pointsTo cur_privilege p) ∗ (∃ es, interp_pmp_entries es))%I
                 (FunDef init_model)
                 (fun _ _ => reg_pointsTo cur_privilege Machine ∗ (∃ es, interp_pmp_entries es))%I.

     Axiom step_iprop : ⊢ semTriple_step.
     Axiom init_model_iprop : ⊢ semTriple_init_model.

     Definition WP_loop : iProp Σ :=
       (WP (MkConf (FunDef loop) env.nil) ?{{_, True}})%I.

     Definition loop_pre (m cp : Privilege) (h i : Z) (entries es : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v npc : Z) : iProp Σ :=
         (
          Execution m cp h i entries es mpp mepc_v npc ∗
          ▷ (CSRMod    m cp h i entries es mpp mepc_v npc -∗ WP_loop) ∗
          ▷ (Trap      m cp h i entries es mpp mepc_v npc -∗ WP_loop) ∗
          ▷ (Recover   m cp h i entries es mpp mepc_v npc -∗ WP_loop))%I.

     Definition semTriple_loop : iProp Σ :=
      (∀ (m cp : Privilege) (h i : Z) (entries es : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v npc : Z),
          semTriple env.nil (loop_pre m cp h i entries es mpp mepc_v npc) (FunDef loop) (fun _ _ => True))%I.

     Definition semTriple_main : iProp Σ :=
      (∀ (m cp : Privilege) (h i : Z) (entries es : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v npc : Z),
          semTriple env.nil (loop_pre m cp h i entries es mpp mepc_v npc) (FunDef main) (fun _ _ => True))%I.

     Lemma valid_semTriple_loop :
       ⊢ semTriple_loop.
     Proof.
       iIntros.
       iLöb as "H".
       iIntros (m cp h i entries es mpp mepc_v npc) "[HP HPwp]".
       cbn.
       unfold fun_loop.
       iApply ((iris_rule_stm_seq env.nil (stm_call step _) (stm_call loop _) _ (fun δ => step_post m cp h i entries es mpp mepc_v npc ∧ ⌜env.nil = δ⌝)%I (fun _ _ => True%I)) with "[] [HPwp] HP").
       iApply (iris_rule_stm_call_inline env.nil step env.nil (Execution m cp h i entries es mpp mepc_v npc) (fun _ => step_post m cp h i entries es mpp mepc_v npc)).
       iApply step_iprop. 
       iIntros.
       iApply iris_rule_consequence.
       iIntros "[Hstep _]".
       iExact "Hstep".
       2: {
         destruct (env.nilView δ').
         iApply (iris_rule_stm_call_inline_later env.nil loop env.nil _ (fun _ => True%I)).
         iModIntro.
         cbn.
         unfold semTriple_loop.
         unfold loop_pre, step_post.
         unfold semTriple.
         cbn.
         iDestruct "HPwp" as "(H2 & H3 & H4)".
         iIntros "[HP|[HP|[HP|HP]]]".
         iApply "H".
         iSplitL "HP"; try iAssumption.
         iSplitL "H2"; try (iModIntro; iAssumption).
         iSplitL "H3"; iModIntro; iAssumption.
         iApply ("H2" with "HP").
         iApply ("H3" with "HP").
         iApply ("H4" with "HP").
       }
       now iIntros (_ δ) "_".
     Qed.

     (* NOTE/TODO: this is quite an ugly and overly explicit proof...
                   I had trouble rewriting sep logic rules (commutativity of ∗)
                   and just "abused" the consequence rules to apply it instead of rewriting *)
     (* TODO: Alternative: contract for loop specified with Katamaran, verify main in Katamaran *)
     Lemma valid_semTriple_main :
       ⊢ semTriple_main. (* main := init_model() ;; loop() *)
     Proof.
       iIntros (m cp h i entries es mpp mepc_v npc) "Hloop_pre".
       cbn.
       unfold fun_main.
       iApply ((iris_rule_stm_seq env.nil (stm_call init_model _) (stm_call loop _) (loop_pre m cp h i entries es mpp mepc_v npc) (fun _ => ∃ es, loop_pre m Machine h i entries es mpp mepc_v npc)%I (fun _ _ => True%I)) with "[] [] Hloop_pre").


       2: {
         iIntros.
         destruct (env.nilView δ').
         unfold semTriple.
         iIntros "[%es' H]".
         iRevert "H".
         fold (semTriple env.nil (loop_pre m Machine h i entries es' mpp mepc_v npc) (call loop) (fun _ _ => True)%I).
         iApply (@iris_rule_consequence _ _ _ _ _ _ (loop_pre m Machine h i entries es' mpp mepc_v npc) _ _ _).
         3: {
           iApply (iris_rule_stm_call_inline env.nil loop env.nil _ (fun _ => True%I)).
           iApply valid_semTriple_loop.
         }
         now iIntros.
         now iIntros.
       }


       unfold loop_pre.
       About iris_rule_consequence.
       iApply (@iris_rule_consequence _ _ _ _ _ _
                                      (
       ∃ es0 : list (Pmpcfg_ent * Z), Execution m cp h i entries es0 mpp mepc_v npc ∗
         ▷ (CSRMod m cp h i entries es0 mpp mepc_v npc -∗ WP_loop) ∗
         ▷ (Trap m cp h i entries es0 mpp mepc_v npc -∗ WP_loop) ∗
         ▷ (Recover m cp h i entries es0 mpp mepc_v npc -∗ WP_loop))%I
                                      _
                                      (fun _ _ =>
       ∃ es0 : list (Pmpcfg_ent * Z), Execution m Machine h i entries es0 mpp mepc_v npc ∗
         ▷ (CSRMod m Machine h i entries es0 mpp mepc_v npc -∗ WP_loop) ∗
         ▷ (Trap m Machine h i entries es0 mpp mepc_v npc -∗ WP_loop) ∗
         ▷ (Recover m Machine h i entries es0 mpp mepc_v npc -∗ WP_loop))%I _).
       iIntros "H".
       iExists es; iFrame.
       now iIntros.
       unfold semTriple.
       iIntros "[%es' H]".
       iRevert "H".
       fold (semTriple env.nil
        (Execution m cp h i entries es' mpp mepc_v npc ∗
         ▷ (CSRMod m cp h i entries es' mpp mepc_v npc -∗ WP_loop) ∗
         ▷ (Trap m cp h i entries es' mpp mepc_v npc -∗ WP_loop) ∗
         ▷ (Recover m cp h i entries es' mpp mepc_v npc -∗ WP_loop))%I (call init_model)
        (fun _ _ => ∃ es0 : list (Pmpcfg_ent * Z), Execution m Machine h i entries es0 mpp mepc_v npc ∗
         ▷ (CSRMod m Machine h i entries es0 mpp mepc_v npc -∗ WP_loop) ∗
         ▷ (Trap m Machine h i entries es0 mpp mepc_v npc -∗ WP_loop) ∗
         ▷ (Recover m Machine h i entries es0 mpp mepc_v npc -∗ WP_loop))%I).
       iApply (@iris_rule_consequence _ _ _ _ _ _ _ _ (fun _ _ =>
         Execution m Machine h i entries es' mpp mepc_v npc ∗
         ▷ (CSRMod m Machine h i entries es' mpp mepc_v npc -∗ WP_loop) ∗
         ▷ (Trap m Machine h i entries es' mpp mepc_v npc -∗ WP_loop) ∗
         ▷ (Recover m Machine h i entries es' mpp mepc_v npc -∗ WP_loop))%I _).
       iIntros "H"; iExact "H".
       iIntros (_ _) "H".
       iExists es'; iFrame.

       iApply iris_rule_consequence.
       iIntros "H".
       iApply (bi.sep_comm with "H").
       2: {
         iApply (iris_rule_frame _ _ (fun _ _ => Execution m Machine h i entries es' mpp mepc_v npc)%I _).
         iApply (@iris_rule_consequence _ _ _ _ _ _ _ _ (fun _ _ => ∃ es, Execution m Machine h i entries es mpp mepc_v npc)%I _).
         iIntros "H"; iExact "H".
         (* STUCK *)
         unfold Execution.
         iApply (@iris_rule_consequence _ _ _ _ _ _ ((reg_pointsTo mtvec h ∗ (∃ npc, reg_pointsTo pc npc ∗
                                                                   reg_pointsTo nextpc npc) ∗
                                                                   (∃ mc : Val ty_exc_code, reg_pointsTo mcause mc ∗ reg_pointsTo mepc mepc_v ∗
                                                                                                         reg_pointsTo mstatus {| MPP := mpp |} ∗ 
                                                                                                         interp_pmp_addr_access liveAddrs entries m ∗ interp_gprs)) ∗ 
                                                                                                                                                                    (reg_pointsTo cur_privilege cp ∗ ∃ es, interp_pmp_entries es)) _ _ _).
         iIntros "(Hacc & Hgprs & Hes & (% & Hmc) & Hmepc & (% & Hnpc & Hpc) & Hmt & Hms & Hme)".
         iFrame.
         iSplitR "Hes".
         iSplitL "Hnpc Hpc".
         iExists npc0; iFrame.
         now iExists mc.
         now iExists es'.
         2: {
           iApply (iris_rule_frame _ _ (fun _ _ => reg_pointsTo cur_privilege Machine ∗ ∃ es, interp_pmp_entries es)%I _).
           iApply iris_rule_consequence.
           3: {
             iApply (iris_rule_stm_call_inline env.nil init_model env.nil _ (fun _ => _)).
             iApply init_model_iprop.
           }
           iIntros "(HP & Hes)".
           iSplitL "HP".
           iExists cp; iFrame.
           iExact "Hes".
           iIntros (_ δ) "((Hcp & Hes) & %)".
           iFrame.
         }
         iIntros (v δ) "((Hmt & (% & Hpc & Hnpc) & % & Hmc & Hmepc & Hms &Hacc & Hgprs) & (Hcp & [% Hes]))".
         iFrame.
         iExists es0; iFrame.
         iSplitL "Hmc".
         iExists mc; iFrame.
         iExists npc0; iFrame.
       } *)
       iIntros (v δ) "[Hloop [% HP]]".
       iExists es; iFrame.
       - iIntros.
         destruct (env.nilView δ).
         unfold semTriple.
         iDestruct "Hloop" as "(HCSRMod & HTrap & HRecover)".
         iSplitL "HCSRMod".
         unfold CSRMod.
         iFrame.
         (* pmp_entries es ≠ pmp_entries es0 *)

         iIntros "[%es' H]".
         iRevert "H".
         fold (semTriple env.nil (loop_pre m Machine h i entries es' mpp mepc_v npc) (call loop) (fun _ _ => True)%I).
         iApply (@iris_rule_consequence _ _ _ _ _ _ (loop_pre m Machine h i entries es' mpp mepc_v npc) _ _ _).
         3: {
           iApply (iris_rule_stm_call_inline env.nil loop env.nil _ (fun _ => True%I)).
           iApply valid_semTriple_loop.
         }
         now iIntros.
         now iIntros.
     Qed.
End Loop.
