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

From RiscvPmp Require Import
     Machine
     Contracts.
From Katamaran Require Import
     Environment
     Syntax
     Sep.Logic
     Iris.Model.

From iris.base_logic Require lib.gen_heap lib.iprop.
From iris.base_logic Require Export invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac.
From iris.program_logic Require Import weakestpre adequacy.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.

Set Implicit Arguments.

Module gh := iris.base_logic.lib.gen_heap.

Module RiscvPmpModel.
  Module RiscvPmpIrisHeapKit <: IrisHeapKit RiscvPmpTermKit RiscvPmpProgramKit RiscvPmpAssertionKit RiscvPmpSymbolicContractKit.
    Module IrisRegs := IrisRegisters RiscvPmpTermKit RiscvPmpProgramKit RiscvPmpAssertionKit RiscvPmpSymbolicContractKit.
    Export IrisRegs.

    Section WithIrisNotations.
      Import iris.bi.interface.
      Import iris.bi.big_op.
      Import iris.base_logic.lib.iprop.
      Import iris.base_logic.lib.gen_heap.

      Definition MemVal : Set := Word.

      Class mcMemG Σ := McMemG {
                            (* ghost variable for tracking state of registers *)
                            mc_ghG :> gh.gen_heapG Addr MemVal Σ;
                            mc_invNs : namespace
                          }.

      Definition memPreG : gFunctors -> Set := fun Σ => gh.gen_heapPreG Z MemVal Σ.
      Definition memG : gFunctors -> Set := mcMemG.
      Definition memΣ : gFunctors := gh.gen_heapΣ Addr MemVal.

      Definition memΣ_PreG : forall {Σ}, subG memΣ Σ -> memPreG Σ := fun {Σ} => gh.subG_gen_heapPreG (Σ := Σ) (L := Addr) (V := MemVal).

      Definition mem_inv : forall {Σ}, memG Σ -> Memory -> iProp Σ :=
        fun {Σ} hG μ => (True)%I.

      Definition mem_res : forall {Σ}, memG Σ -> Memory -> iProp Σ :=
        fun {Σ} hG μ => (True)%I.

      Lemma mem_inv_init : forall Σ (μ : Memory), memPreG Σ ->
                                                  ⊢ |==> ∃ memG : memG Σ, (mem_inv memG μ ∗ mem_res memG μ)%I.
      Admitted.

      Import RiscvPmp.Contracts.RiscvPmpSymbolicContractKit.ASS.

      Definition luser_inst `{sailRegG Σ} `{invG Σ} (p : Predicate) (ts : Env Lit (RiscvPmpAssertionKit.𝑯_Ty p)) (mG : memG Σ) : iProp Σ :=
        (match p return Env Lit (RiscvPmpAssertionKit.𝑯_Ty p) -> iProp Σ with
         | pmp_entries => fun ts => let entries_lst := env_head ts in
                                    match entries_lst with
                                    | (cfg0, addr0) :: [] =>
                                      (reg_pointsTo pmp0cfg cfg0 ∗
                                              reg_pointsTo pmpaddr0 addr0)%I
                                    | _ => False%I
                                    end
         end) ts.

    Definition lduplicate_inst `{sailRegG Σ} `{invG Σ} (p : Predicate) (ts : Env Lit (RiscvPmpAssertionKit.𝑯_Ty p)) :
      forall (mG : memG Σ),
        is_duplicable p = true ->
        (luser_inst p ts mG) ⊢ (luser_inst p ts mG ∗ luser_inst p ts mG).
    Proof.
      iIntros (mG hdup) "H".
      destruct p; inversion hdup;
      iDestruct "H" as "#H";
      auto.
    Qed.

    End WithIrisNotations.
  End RiscvPmpIrisHeapKit.

  Module Soundness := IrisSoundness RiscvPmpTermKit RiscvPmpProgramKit RiscvPmpAssertionKit RiscvPmpSymbolicContractKit RiscvPmpIrisHeapKit.
  Export Soundness.

  Lemma foreignSem `{sg : sailG Σ} : ForeignSem (Σ := Σ).
  Proof.
    intros Γ τ Δ f es δ.
    destruct f; cbn.
  Admitted.

  Lemma lemSem `{sg : sailG Σ} : LemmaSem (Σ := Σ).
  Proof.
    intros Δ [].
  Qed.
End RiscvPmpModel.
