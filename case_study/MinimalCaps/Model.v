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
From stdpp Require namespaces.

Set Implicit Arguments.

Module gh := iris.base_logic.lib.gen_heap.

Module MinCapsModel.
  From MinimalCaps Require Import Contracts.
  Import MicroSail.Iris.Model.

  Module MinCapsIrisHeapKit <: IrisHeapKit MinCapsTermKit MinCapsProgramKit MinCapsAssertionKit MinCapsSymbolicContractKit.

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

    Definition liveAddrs : list Addr := [ 0; 1; 2; 3; 4; 5; 6; 7; 8; 9]%Z.

    Definition mem_res : forall {Σ}, memG Σ -> Memory -> iProp Σ :=
      fun {Σ} hG μ =>
        ([∗ list] a ∈ liveAddrs, mapsto (hG := mc_ghG (mcMemG := hG)) a 1 (μ a)) %I.

    Lemma mem_inv_init : forall Σ (μ : Memory), memPreG Σ ->
        ⊢ |==> ∃ memG : memG Σ, (mem_inv memG μ ∗ mem_res memG μ)%I.
    Proof.
      iIntros (Σ μ gHP).

      iMod (gen_heap_init (gen_heapPreG0 := gHP) (L := Addr) (V := Z) empty) as (gH) "inv".
      iMod (gen_heap_alloc _ 9%Z (μ 9) _ with "inv") as "(inv & res9 & _)".
      iMod (gen_heap_alloc _ 8%Z (μ 8) _ with "inv") as "(inv & res8 & _)".
      iMod (gen_heap_alloc _ 7%Z (μ 7) _ with "inv") as "(inv & res7 & _)".
      iMod (gen_heap_alloc _ 6%Z (μ 6) _ with "inv") as "(inv & res6 & _)".
      iMod (gen_heap_alloc _ 5%Z (μ 5) _ with "inv") as "(inv & res5 & _)".
      iMod (gen_heap_alloc _ 4%Z (μ 4) _ with "inv") as "(inv & res4 & _)".
      iMod (gen_heap_alloc _ 3%Z (μ 3) _ with "inv") as "(inv & res3 & _)".
      iMod (gen_heap_alloc _ 2%Z (μ 2) _ with "inv") as "(inv & res2 & _)".
      iMod (gen_heap_alloc _ 1%Z (μ 1) _ with "inv") as "(inv & res1 & _)".
      iMod (gen_heap_alloc _ 0%Z (μ 0) _ with "inv") as "(inv & res0 & _)".
      iModIntro.

      pose (refmap := list_to_map (map (fun a => (a, μ a)) liveAddrs) : gmap Z Z).
      iExists (McMemG gH (nroot .@ "addr_inv")).
      cbn.
      iFrame.
      iExists refmap.
      iFrame.
      iPureIntro.
      repeat rewrite map_Forall_insert; trivial.
      repeat split; trivial.
      by apply map_Forall_empty.

      Unshelve.
      all: try rewrite !lookup_insert_ne; try apply lookup_empty; lia.
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

    Definition MinCaps_safe `{sailRegG Σ} `{invG Σ} {mG : memG Σ} (v : Z + Capability) : iProp Σ :=
      match v with
      | inl z => True%I
      | inr (MkCap O b e a) => True%I
      | inr (MkCap R b e a) =>
                ([∗ list] a ∈ (region_addrs b e), inv (mc_invNs (mcMemG := mG) .@ a) (∃ v, mapsto (hG := mc_ghG (mcMemG := mG)) a 1 v))%I
      | inr (MkCap RW b e a) =>
                [∗ list] a ∈ (region_addrs b e), inv (mc_invNs (mcMemG := mG) .@ a) (∃ v, mapsto (hG := mc_ghG (mcMemG := mG)) a 1 v)
      end.

    Definition lpred_inst `{sailRegG Σ} `{invG Σ} (p : Predicate) (ts : Env Lit (MinCapsAssertionKit.𝑷_Ty p)) (mG : memG Σ) : iProp Σ :=
      (match p return Env Lit (MinCapsAssertionKit.𝑷_Ty p) -> iProp Σ with
      | ptsreg => fun ts => MinCaps_ptsreg (env_head (env_tail ts)) (env_head ts)
      | ptsto => fun ts => mapsto (hG := mc_ghG (mcMemG := mG)) (env_head ts) 1 (env_head (env_tail ts))%Z
      | safe => fun ts => MinCaps_safe (mG := mG) (env_head ts)
      end) ts.

    End WithIrisNotations.
  End MinCapsIrisHeapKit.

End MinCapsModel.
