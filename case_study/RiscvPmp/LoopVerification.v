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

     (* TODO: rename P{,ᵢ} *)
     (* P₁ = Executing normally *)
     Definition P₁ (m cp : Privilege) (h i : Z) (entries es : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v npc : Z) :=
       (            interp_pmp_addr_access liveAddrs entries m ∗
                    interp_gprs ∗
        (∃ mc : Z,  reg_pointsTo mcause mc) ∗
                    interp_pmp_entries es ∗
                    reg_pointsTo cur_privilege cp ∗
        (∃ npc : Z, reg_pointsTo nextpc npc ∗
                    reg_pointsTo pc npc) ∗
                    reg_pointsTo mtvec h ∗
                    reg_pointsTo mstatus {| MPP := mpp |} ∗
                    reg_pointsTo mepc mepc_v)%I.

     (* P₂ = Modified CSRs, requires Machine mode *)
     Definition P₂ (m cp : Privilege) (h i : Z) (entries es : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v npc : Z) :=
       (                               interp_pmp_addr_access liveAddrs entries m ∗
                                       interp_gprs ∗
                                       (⌜m = Machine⌝ ∧ emp) ∗
        (∃ es : list (Pmpcfg_ent * Z), interp_pmp_entries es) ∗
                                       reg_pointsTo cur_privilege Machine ∗
        (∃ mc : Z,                     reg_pointsTo mcause mc) ∗
        (∃ npc : Z,                    reg_pointsTo nextpc npc ∗
                                       reg_pointsTo pc npc) ∗
        (∃ h : Z,                      reg_pointsTo mtvec h) ∗
        (∃ mpp : Privilege,            reg_pointsTo mstatus {| MPP := mpp |}) ∗
        (∃ epc : Z,                    reg_pointsTo mepc epc))%I.

     (* P₃ = Trap occured -> Go into M-mode *)
     Definition P₃ (m cp : Privilege) (h i : Z) (entries es : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v npc : Z) :=
       (interp_pmp_addr_access liveAddrs entries m ∗
        interp_gprs ∗
        interp_pmp_entries es ∗
        reg_pointsTo cur_privilege Machine ∗
        (∃ mc : Z, reg_pointsTo mcause mc) ∗
        reg_pointsTo nextpc h ∗
        reg_pointsTo pc h ∗
        reg_pointsTo mtvec h ∗
        reg_pointsTo mstatus {| MPP := m |} ∗
        reg_pointsTo mepc i)%I.

     (* P₄ = MRET = Recover *)
     Definition P₄ (m cp : Privilege) (h i : Z) (entries es : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v npc : Z) :=
       (interp_pmp_addr_access liveAddrs entries m ∗
        interp_gprs ∗ 
        interp_pmp_entries es ∗
        (⌜m = Machine⌝ ∧ emp) ∗
        reg_pointsTo cur_privilege mpp ∗
        (∃ mc : Z, reg_pointsTo mcause mc) ∗
        reg_pointsTo nextpc mepc_v ∗
        reg_pointsTo pc mepc_v ∗
        reg_pointsTo mtvec h ∗
        reg_pointsTo mstatus {| MPP := User |} ∗
        reg_pointsTo mepc mepc_v)%I.

     Definition P (m cp : Privilege) (h i : Z) (entries es : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v npc : Z) :=
                    (reg_pointsTo cur_privilege cp ∗
                     reg_pointsTo mtvec         h ∗
                     reg_pointsTo pc            i ∗
                     reg_pointsTo nextpc        npc ∗
         ∃ mc,       reg_pointsTo mcause        mc ∗
                     reg_pointsTo mepc          mepc_v ∗
                     reg_pointsTo mstatus       {| MPP := mpp |} ∗
                     interp_pmp_entries es ∗
                     interp_pmp_addr_access liveAddrs entries m ∗
                     interp_gprs)%I.

     Definition step_post (m cp : Privilege) (h i : Z) (entries es : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v npc : Z) : iProp Σ :=
       (* (interp_pmp_addr_access liveAddrs entries m ∗
        interp_gprs ∗ *)
        (P₁ m cp h i entries es mpp mepc_v npc ∨
         P₂ m cp h i entries es mpp mepc_v npc ∨
         P₃ m cp h i entries es mpp mepc_v npc ∨
         P₄ m cp h i entries es mpp mepc_v npc)%I.

     Definition semTriple_step : iProp Σ :=
       (∀ (m cp : Privilege) (h i : Z) (entries es : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v npc : Z),
           semTriple env.nil (P m cp h i entries es mpp mepc_v npc) (FunDef step) (fun _ _ => step_post m cp h i entries es mpp mepc_v npc))%I.

     Definition semTriple_init_model : iProp Σ :=
       semTriple env.nil
                 ((∃ p, reg_pointsTo cur_privilege p) ∗ (∃ es, interp_pmp_entries es))%I
                 (FunDef init_model)
                 (fun _ _ => reg_pointsTo cur_privilege Machine ∗ (∃ es, interp_pmp_entries es))%I.

     Axiom step_iprop : ⊢ semTriple_step.
     Axiom init_model_iprop : ⊢ semTriple_init_model.

     Print ValConf.

     Definition WP_loop : iProp Σ :=
       (wp NotStuck top (MkConf (FunDef loop) env.nil) (fun (v : ValConf ctx.nil ty_unit) => match v with | {| valconf_val := tt |} => True end))%I.

     Definition loop_cond (P : PtstosPred) : iProp Σ :=
       (∃ m cp h i entries es mpp mepc_v npc, P m cp h i entries es mpp mepc_v npc -∗ WP_loop).

     Definition loop_later : iProp Σ :=
       ▷ loop_cond P₁ ∗ ▷ loop_cond P₂ ∗ ▷ loop_cond P₃ ∗ ▷ loop_cond P₄.

     (* TODO: go over this precondition again, introduced existentials but not confident
              that this makes sense. Current reasoning is that *later* we should have
              that Pᵢ holds for the new values, not the ones from *now*.

              This becomes apparent in the proof below, if we end up in Pᵢ, then the
              values m, cp, h, i, ... can/will have been updated in a certain way...*)
     Definition loop_pre (m cp : Privilege) (h i : Z) (entries es : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v npc : Z) : iProp Σ :=
         (
          P m cp h i entries es mpp mepc_v npc ∗
            (* loop_later *)
          ▷ (P₁ m cp h i entries es mpp mepc_v npc -∗ WP_loop) ∗
          ▷ (P₂ m cp h i entries es mpp mepc_v npc -∗ WP_loop) ∗
          ▷ (P₃ m cp h i entries es mpp mepc_v npc -∗ WP_loop) ∗
          ▷ (P₄ m cp h i entries es mpp mepc_v npc -∗ WP_loop)
          (* ▷ (P₁ m h i entries es mpp mepc_v npc -∗ WP_loop) ∗
          ▷ (P₂ m h i entries es mpp mepc_v npc -∗ WP_loop) ∗
          ▷ (P₃ m h i entries es mpp mepc_v npc -∗ WP_loop) *)
          )%I.

     Definition semTriple_loop : iProp Σ :=
      (∀ (m cp : Privilege) (h i : Z) (entries es : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v npc : Z),
          semTriple env.nil (loop_pre m cp h i entries es mpp mepc_v npc) (FunDef loop) (fun _ _ => True))%I.

     Definition semTriple_main : iProp Σ :=
      (∀ (m cp : Privilege) (h i : Z) (entries es : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v npc : Z),
          semTriple env.nil (loop_pre m cp h i entries es mpp mepc_v npc) (FunDef main) (fun _ _ => True))%I.
          (* semTriple env.nil (P m cp h i entries es mpp mepc_v npc) (FunDef main) (fun _ _ => True))%I. *)

     Lemma valid_semTriple_loop :
       ⊢ semTriple_loop.
     Proof.
       iIntros.
       iLöb as "H".
       iIntros (m cp h i entries es mpp mepc_v npc) "[HP HPwp]".
       cbn.
       unfold fun_loop.
       About iris_rule_stm_seq.
       iApply ((iris_rule_stm_seq env.nil (stm_call step _) (stm_call loop _) _ _ (fun _ _ => True%I)) with "[] [HPwp] HP").
       iApply (iris_rule_stm_call_inline env.nil step env.nil _ (fun _ => _)).
       iApply step_iprop. 
       iIntros.
       iApply iris_rule_consequence.
       1: {
         destruct (env.nilView δ').
         iIntros "[Hstep _]".
         iExact "Hstep".
       }
       2: {
         destruct (env.nilView δ').
         iApply (iris_rule_stm_call_inline_later env.nil loop env.nil _ (fun _ => True%I)).
         iModIntro.
         cbn.
         unfold semTriple_loop.
         unfold loop_pre, step_post.
         unfold semTriple.
         cbn.
         iIntros "[HP₁|[HP₂|[HP₃|HP₄]]]".
         iDestruct "HPwp" as "(H1 & H2 & H3 & H4)".
         Unset Printing Records.
         cbn.
         About ValConf.
         About ctx.In.
         unfold WP_loop.
         Print WP_loop.
         iApply ("H1" with "HP₁").
         - iDestruct "HP₁" as "[Hpac [Hig [Hmcause [Hie [Hcur [[% [Hnpc Hpc]] [Hmtvec [Hmstatus Hmepc]]]]]]]]".
           iSpecialize ("H" $! m cp h i entries es mpp mepc_v npc)
           iApply "H".
           iSplitR "HPwp". 
           + iFrame.
             iApply "Hmcause".
           + iDestruct "HPwp" as "[HP₁ [HP₂ [HP₃ HP₄]]]".
             iFrame.
             iSplitL "HP₁"; iModIntro.

         - iDestruct "HP₂" as "[Hpaa [Hig [[-> _] [[%es' Hipe] [Hcur [Hmcause [[%npc0 [Hnextpc Hpc]] [[%h0 Hmtvec] [[%mpp0 Hmstatus] [%epc Hmepc]]]]]]]]]]".
           iSpecialize ("H" $! Machine Machine h0 npc0 entries es' mpp0 epc npc0).
           iApply "H".
           iSplitR "HPwp". 
           + iFrame.
             iApply "Hmcause".
           + iDestruct "HPwp" as "[HP₁ [HP₂ [HP₃ HP₄]]]".
             iFrame.
         - iDestruct "HP₃" as "[Hpaa [Hig [Hipe [Hcur [Hmcause [Hnextpc [Hpc [Hmtvec [Hmstatus Hmepc]]]]]]]]]".
           iSpecialize ("H" $! m Machine h h entries es m i h).
           iApply "H".
           iSplitR "HPwp". 
           + iFrame.
             iApply "Hmcause".
           + iDestruct "HPwp" as "[HP₁ [HP₂ [HP₃ HP₄]]]".
             iFrame.
         - iDestruct "HP₄" as "[Hpaa [Hig [Hipe [[-> _] [Hcur [Hmcause [Hnextpc [Hpc [Hmtvec [Hmstatus Hmepc]]]]]]]]]]".
           iSpecialize ("H" $! Machine Machine h mepc_v entries es User mepc_v mepc_v).
           iApply "H".
           iSplitR "HPwp". 
           + iFrame.
             iApply "Hmcause".
           + iDestruct "HPwp" as "[HP₁ [HP₂ [HP₃ HP₄]]]".
             iFrame.
       }
       simpl.
       now iIntros (_ δ) "_".
     Qed.

     (* NOTE/TODO: this is quite an ugly and overly explicit proof...
                   I had trouble rewriting sep logic rules (commutativity of ∗)
                   and just "abused" the consequence rules to apply it instead of rewriting *)
     Lemma valid_semTriple_main :
       ⊢ semTriple_main.
     Proof.
       iIntros (m cp h i entries es mpp mepc_v npc) "Hloop_pre".
       cbn.
       unfold fun_main.
       iApply ((iris_rule_stm_seq env.nil (stm_call init_model _) (stm_call loop _) (loop_pre m cp h i entries es mpp mepc_v npc) (fun _ => ∃ es, loop_pre m Machine h i entries es mpp mepc_v npc)%I (fun _ _ => True%I)) with "[] [] Hloop_pre").


       - unfold loop_pre.
         iApply iris_rule_consequence.
         iIntros "H".
         iApply (bi.sep_comm with "H").
         2: {
           iApply (iris_rule_frame _ _ (fun _ _ => ∃ es, P m Machine h i entries es mpp mepc_v npc)%I _).
           unfold P.
           iApply (@iris_rule_consequence _ _ _ _ _ _ ((reg_pointsTo mtvec h ∗ reg_pointsTo pc i ∗
     reg_pointsTo nextpc npc ∗
     (∃ mc : Val ty_exc_code, reg_pointsTo mcause mc ∗ reg_pointsTo mepc mepc_v ∗
        reg_pointsTo mstatus {| MPP := mpp |} ∗ 
        interp_pmp_addr_access liveAddrs entries m ∗ interp_gprs)) ∗ 
     (reg_pointsTo cur_privilege cp ∗ interp_pmp_entries es)) _ _ _).
           iIntros "(Hcp & Hmt & Hpc & Hnpc & % & Hmc & Hmepc & Hms & Hes & Hacc & Hgprs)".
           iFrame.
           now iExists mc.
           2: {
             iApply (iris_rule_frame _ _ (fun _ _ => reg_pointsTo cur_privilege Machine ∗ ∃ es, interp_pmp_entries es)%I _).
             iApply iris_rule_consequence.
             3: {
               iApply (iris_rule_stm_call_inline env.nil init_model env.nil _ (fun _ => _));
               iApply init_model_iprop.
             }
             iIntros "(HP & Hes)".
             iSplitL "HP".
             iExists cp; iFrame.
             iExists es; iFrame.
             iIntros (_ δ) "((Hcp & Hes) & %)".
             iFrame.
           }
           iIntros (v δ) "((Hmt & Hpc & Hnpc & % & Hmc & Hmepc & Hms &Hacc & Hgprs) & (Hcp & [% Hes]))".
           iFrame.
           iExists es0, mc; iFrame.
         }
         iIntros (v δ) "[Hloop [% HP]]".
         iExists es0; iFrame.
       - iIntros.
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
     Qed.
End Loop.
