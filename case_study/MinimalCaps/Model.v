(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel                                          *)
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

From MinimalCaps Require Import
     Machine.

From Coq Require Import
     Init.Nat
     ZArith.Znat
     Program.Tactics
     Strings.String
     ZArith.ZArith
     micromega.Lia.

From Equations Require Import
     Equations.

From MicroSail Require Import
     SemiConcrete.Outcome
     Sep.Spec
     Symbolic.Mutator
     Syntax.

From MicroSail Require Environment.
From MicroSail Require Iris.Model.
From MicroSail Require Sep.Logic.
From iris.base_logic Require lib.gen_heap lib.iprop.
From iris.base_logic Require Export invariants.
From iris.bi Require interface big_op.
From iris.proofmode Require tactics.
From stdpp Require namespaces fin_maps.

Set Implicit Arguments.

Module gh := iris.base_logic.lib.gen_heap.

Module MinCapsModel.
  From MinimalCaps Require Import Contracts.
  Import MicroSail.Iris.Model.

  Module MinCapsIrisHeapKit <: IrisHeapKit MinCapsTermKit MinCapsProgramKit MinCapsAssertionKit MinCapsSymbolicContractKit.

    Variable maxAddr : nat.

    Module IrisRegs := IrisRegisters MinCapsTermKit MinCapsProgramKit MinCapsAssertionKit MinCapsSymbolicContractKit.
    Import IrisRegs.

    Section WithIrisNotations.

    Import iris.bi.interface.
    Import iris.bi.big_op.
    Import iris.base_logic.lib.iprop.
    Import iris.base_logic.lib.gen_heap.
    Import iris.proofmode.tactics.

    Class mcMemG Σ := McMemG {
                          (* ghost variable for tracking state of registers *)
                          mc_ghG :> gh.gen_heapG Z Z Σ;
                          mc_invNs : namespace
                        }.

    Definition memPreG : gFunctors -> Set := fun Σ => gh.gen_heapPreG Z Z Σ.
    Definition memG : gFunctors -> Set := mcMemG.
    Definition memΣ : gFunctors := gh.gen_heapΣ Z Z.

    Definition memΣ_PreG : forall {Σ}, subG memΣ Σ -> memPreG Σ := fun {Σ} => gh.subG_gen_heapPreG (Σ := Σ) (L := Z) (V := Z).

    Definition mem_inv : forall {Σ}, memG Σ -> Memory -> iProp Σ :=
      fun {Σ} hG μ =>
        (∃ memmap, gen_heap_ctx (hG := mc_ghG (mcMemG := hG)) memmap ∗
                                ⌜ map_Forall (fun a v => μ a = v) memmap ⌝
        )%I.

    Fixpoint natsTo (n : nat) : list nat :=
      match n with
      | 0 => []
      | S n => n :: natsTo n
      end.

    Definition liveAddrs : list Addr := map Z.of_nat (natsTo maxAddr).
    Definition initMemMap μ := (list_to_map (map (fun a => (a , μ a)) liveAddrs) : gmap Addr Z ).

    Lemma initMemMap_works μ : map_Forall (λ (a : Addr) (v : Z), μ a = v) (initMemMap μ).
    Proof.
      unfold initMemMap.
      rewrite map_Forall_to_list.
      rewrite Forall_forall.
      intros (a , v).
      rewrite elem_of_map_to_list.
      intros el.
      apply elem_of_list_to_map_2 in el.
      apply elem_of_list_In in el.
      apply in_map_iff in el.
      by destruct el as (a' & <- & _).
    Qed.

    Definition mem_res : forall {Σ}, memG Σ -> Memory -> iProp Σ :=
      fun {Σ} hG μ =>
        ([∗ map] l↦v ∈ initMemMap μ, mapsto (hG := mc_ghG (mcMemG := hG)) l 1 v) %I.

    Lemma mem_inv_init : forall Σ (μ : Memory), memPreG Σ ->
        ⊢ |==> ∃ memG : memG Σ, (mem_inv memG μ ∗ mem_res memG μ)%I.
    Proof.
      iIntros (Σ μ gHP).

      iMod (gen_heap_init (gen_heapPreG0 := gHP) (L := Addr) (V := Z) empty) as (gH) "inv".
      pose (memmap := initMemMap μ).
      iMod (gen_heap_alloc_gen empty memmap (map_disjoint_empty_r memmap) with "inv") as "(inv & res & _)".
      iModIntro.

      rewrite (right_id empty union memmap).

      iExists (McMemG gH (nroot .@ "addr_inv")).
      iFrame.
      iExists memmap.
      iFrame.
      iPureIntro.
      apply initMemMap_works.
    Qed.

    Definition MinCaps_ptsreg `{sailRegG Σ} (reg : RegName) (v : Z + Capability) : iProp Σ :=
      match reg with
      | R0 => reg_pointsTo reg0 v
      | R1 => reg_pointsTo reg1 v
      | R2 => reg_pointsTo reg2 v
      | R3 => reg_pointsTo reg3 v
      end.

    Definition region_addrs (b : Addr) (e : Addr + unit): list Addr :=
      match e with
      | inl e => filter (fun a => and (b ≤ a)%Z (a ≤ e)%Z) liveAddrs
      | inr _ => filter (fun a => (b ≤ a)%Z) liveAddrs
      end.

    Definition MinCaps_csafe `{sailRegG Σ} `{invG Σ} {mG : memG Σ} (v : Capability) : iProp Σ :=
      match v with
      | MkCap O b e a => True%I
      | MkCap R b e a =>
                ([∗ list] a ∈ (region_addrs b e), inv (mc_invNs (mcMemG := mG) .@ a) (∃ v, mapsto (hG := mc_ghG (mcMemG := mG)) a 1 v))%I
      | MkCap RW b e a =>
                [∗ list] a ∈ (region_addrs b e), inv (mc_invNs (mcMemG := mG) .@ a) (∃ v, mapsto (hG := mc_ghG (mcMemG := mG)) a 1 v)
      end.


    Definition MinCaps_safe `{sailRegG Σ} `{invG Σ} {mG : memG Σ} (v : Z + Capability) : iProp Σ :=
      match v with
      | inl z => True%I
      | inr c => MinCaps_csafe (mG := mG) c
      end.

    Definition luser_inst `{sailRegG Σ} `{invG Σ} (p : Predicate) (ts : Env Lit (MinCapsAssertionKit.𝑷_Ty p)) (mG : memG Σ) : iProp Σ :=
      (match p return Env Lit (MinCapsAssertionKit.𝑷_Ty p) -> iProp Σ with
      | ptsreg => fun ts => MinCaps_ptsreg (env_head (env_tail ts)) (env_head ts)
      | ptsto => fun ts => mapsto (hG := mc_ghG (mcMemG := mG)) (env_head ts) 1 (env_head (env_tail ts))%Z
      | safe => fun ts => MinCaps_safe (mG := mG) (env_head ts)
      | csafe => fun ts => MinCaps_csafe (mG := mG) (env_head ts)
      end) ts.

    End WithIrisNotations.
  End MinCapsIrisHeapKit.

End MinCapsModel.
