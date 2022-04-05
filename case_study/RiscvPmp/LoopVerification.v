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

(* step: *)
Locate sep_contract_step.
Locate fun_step.

Section Loop. 
     Context `{sg : sailGS Σ}.
     Context `{mG : memGS Σ}.
     Definition step_sem_contract := 
       Eval cbn  in ValidContractSemCurried fun_step sep_contract_step.
     Axiom step_iprop : ⊢ step_sem_contract.

     (* 
     P = 
                     reg_pointsTo cur_privilege (term_var "m") ∗
                     reg_pointsTo mtvec         (term_var "h") ∗
                     reg_pointsTo pc            (term_var "i") ∗
                     reg_pointsTo nextpc        (term_var "npc") ∗
         ∃ "mcause", reg_pointsTo mcause        (term_var "mcause") ∗
                     reg_pointsTo mepc          (term_var "mepc") ∗
                     reg_pointsTo mstatus       (term_record rmstatus [ term_var "mpp" ]) ∗
                     interp_pmp_entries (term_var "entries") ∗
                     interp_pmp_addr_access (term_var "entries") (term_var "m") ∗
                     interp_gprs
     *)

     Definition loop_pre : iProp Σ :=
     (* P ∗ ▷(P₁ -∗ wp loop ⊤) *)
     (∀ (m : Privilege) (h i : Z) (entries : list (Pmpcfg_ent * Z)) (mpp : Privilege) (mepc_v npc : Z),
         ((* P *)
                     reg_pointsTo cur_privilege m ∗
                     reg_pointsTo mtvec         h ∗
                     reg_pointsTo pc            i ∗
                     reg_pointsTo nextpc        npc ∗
         ∃ mc, reg_pointsTo mcause        mc ∗
                     reg_pointsTo mepc          mepc_v ∗
                     reg_pointsTo mstatus       {| MPP := mpp |} ∗
                     interp_pmp_entries entries ∗
                     interp_pmp_addr_access liveAddrs entries m ∗
                     interp_gprs)
          ∗
       )%I.

     Definition semTriple_loop : iProp Σ :=
          semTriple ε loop_pre (FunDef loop) (fun _ _ => True)%I.

     Lemma valid_semTriple_loop :
       ⊢ sem

End Loop.