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

     Print step_sem_contract.

     Definition P₁ (m : Privilege) (h i : Z) (entries : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v npc : Z) :=
          (interp_pmp_addr_access liveAddrs entries m ∗ interp_gprs ∗ (∃ mc : Z, reg_pointsTo mcause mc) ∗
        (interp_pmp_entries entries ∗ reg_pointsTo cur_privilege m ∗ (∃ npc : Z, reg_pointsTo nextpc npc ∗ reg_pointsTo pc npc) ∗ reg_pointsTo mtvec h ∗
         reg_pointsTo mstatus {| MPP := mpp |} ∗ reg_pointsTo mepc mepc_v))%I.

     Definition P (m : Privilege) (h i : Z) (entries : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v npc : Z) :=
                    (reg_pointsTo cur_privilege m ∗
                     reg_pointsTo mtvec         h ∗
                     reg_pointsTo pc            i ∗
                     reg_pointsTo nextpc        npc ∗
         ∃ mc,       reg_pointsTo mcause        mc ∗
                     reg_pointsTo mepc          mepc_v ∗
                     reg_pointsTo mstatus       {| MPP := mpp |} ∗
                     interp_pmp_entries entries ∗
                     interp_pmp_addr_access liveAddrs entries m ∗
                     interp_gprs)%I.

     Definition step_post (m : Privilege) (h i : Z) (entries : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v npc : Z) : iProp Σ :=
                     (interp_pmp_addr_access liveAddrs entries m ∗
                     interp_gprs ∗
                     P₁ m h i entries mpp mepc_v npc)%I.

     Definition semTriple_step : iProp Σ :=
      (∀ (m : Privilege) (h i : Z) (entries : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v npc : Z),
          semTriple env.nil (P m h i entries mpp mepc_v npc) (FunDef step) (fun _ _ => step_post m h i entries mpp mepc_v npc))%I.

     Axiom step_iprop : ⊢ semTriple_step.

     Definition loop_pre (m : Privilege) (h i : Z) (entries : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v npc : Z) : iProp Σ :=
         (
           P m h i entries mpp mepc_v npc ∗
          ▷ (P₁ m h i entries mpp mepc_v npc -∗ WP (MkConf (FunDef loop) env.nil) ?{{ w, True }})
         (* ∨
           (⌜m = Machine⌝ ∧ emp) ∗ (∃ es : list (Pmpcfg_ent * Z), interp_pmp_entries es) ∗ reg_pointsTo cur_privilege Machine ∗
           (∃ npc : Z, reg_pointsTo nextpc npc ∗ reg_pointsTo pc npc) ∗ (∃ h : Z, reg_pointsTo mtvec h) ∗ (∃ mpp : Privilege, reg_pointsTo mstatus {| MPP := mpp |}) ∗
           (∃ mepc_v : Z, reg_pointsTo mepc mepc_v)
         ∨
           interp_pmp_entries entries ∗ reg_pointsTo cur_privilege Machine ∗ reg_pointsTo nextpc v0 ∗ reg_pointsTo pc v0 ∗ reg_pointsTo mtvec v0 ∗ reg_pointsTo mstatus {| MPP := v |} ∗
                                reg_pointsTo mepc mepc_v
         ∨
           interp_pmp_entries entries ∗ (⌜m = Machine⌝ ∧ emp) ∗ reg_pointsTo cur_privilege mpp ∗ reg_pointsTo nextpc mepc_v ∗ reg_pointsTo pc mepc_v ∗
             reg_pointsTo mtvec h ∗ reg_pointsTo mstatus {| MPP := User |} ∗ reg_pointsTo mepc mepc_v)))%I
       )%I. *)
          )%I.

     Definition semTriple_loop : iProp Σ :=
      (∀ (m : Privilege) (h i : Z) (entries : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v npc : Z),
          semTriple env.nil (loop_pre m h i entries mpp mepc_v npc) (FunDef loop) (fun _ _ => True))%I.

     Lemma valid_semTriple_loop :
       ⊢ semTriple_loop.
     Proof.
       iIntros.
       iLöb as "H".
       iIntros (m h i entries mpp mepc_v npc) "[HP HP₁]".
       cbn.
       unfold fun_loop.
       Check iris_rule_stm_seq.
       About iris_rule_stm_seq.
       Check ((iris_rule_stm_seq env.nil (stm_call step _) (stm_call loop _) (P m h i entries mpp mepc_v npc))).
       iApply ((iris_rule_stm_seq env.nil (stm_call step _) (stm_call loop _) (P m h i entries mpp mepc_v npc)) with "[] [HP₁] HP").
       Check (iris_rule_stm_call_inline env.nil step env.nil).
       iApply (iris_rule_stm_call_inline env.nil step env.nil _ (fun _ => _)).
       iApply step_iprop. 
       iIntros.
       Search "iris_".
       Check iris_rule_consequence.
       iApply iris_rule_consequence.
       1: {
         destruct (env.nilView δ').
         iIntros "[Hstep _]".
         iExact "Hstep".
       }
       2: {
         destruct (env.nilView δ').
         Check (iris_rule_stm_call_inline_later env.nil loop env.nil _ _).
         Search "iris_rule".
         iApply (iris_rule_stm_call_inline_later env.nil loop env.nil _ (fun _ => True%I)).
         iModIntro.
         cbn.
         unfold semTriple_loop.
         unfold loop_pre, step_post.
         unfold semTriple.
         iIntros "[Hinterp [Hgprs HP]]".
         cbn.
         iDestruct "HP" as "[Hpac [Hig [Hmcause [Hie [Hcur [[% [Hnpc Hpc]] [Hmtvec [Hmstatus Hmepc]]]]]]]]".
         iSpecialize ("H" $! m h npc0 entries mpp mepc_v npc0).
         iApply "H".
         iSplitR "HP₁".
         + unfold P.
           iFrame.
           iApply "Hmcause".
         + iModIntro.
           unfold fun_loop.
           iApply "HP₁".
       }
       simpl.
       now iIntros (_ δ) "_".
     Qed.

End Loop.
