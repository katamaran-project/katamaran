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

From Katamaran Require Import
     Bitvector
     Environment
     Iris.Model
     RiscvPmpBoundedInts.Machine.
From iris Require Import
     base_logic.lib.gen_heap
     proofmode.tactics.

Set Implicit Arguments.

Import RiscvPmpProgram.

(* Instantiate the Iris framework solely using the operational semantics. At
   this point we do not commit to a set of contracts nor to a set of
   user-defined predicates. *)
Module RiscvPmpIrisBase <: IrisBase RiscvPmpBase RiscvPmpProgram RiscvPmpSemantics.
  (* Pull in the definition of the LanguageMixin and register ghost state. *)
  Include IrisPrelims RiscvPmpBase RiscvPmpProgram RiscvPmpSemantics.

  (* Defines the memory ghost state. *)
  Section RiscvPmpIrisParams.
    Import bv.
    Definition Byte : Set := bv 8.
    Definition MemVal : Set := Byte.

    Class mcMemGS Σ :=
      McMemGS {
          (* ghost variable for tracking state of registers *)
          mc_ghGS : gen_heapGS Addr MemVal Σ
        }.
    #[export] Existing Instance mc_ghGS.

    Definition memGpreS : gFunctors -> Set := fun Σ => gen_heapGpreS Addr MemVal Σ.
    Definition memGS : gFunctors -> Set := mcMemGS.
    Definition memΣ : gFunctors := gen_heapΣ Addr MemVal.

    Definition seqBv {n} (min : bv n) (len : nat) := List.map (@bv.of_Z n) (seqZ (bv.unsigned min) (Z.of_nat len)).
    Definition liveAddrs := seqBv minAddr lenAddr.
    Lemma NoDup_liveAddrs : NoDup liveAddrs.
    Proof. now eapply Prelude.nodup_fixed. Qed.
    
    #[global] Arguments liveAddrs : simpl never.

    Definition initMemMap μ := (list_to_map (map (fun a => (a , μ a)) liveAddrs) : gmap Addr MemVal).

    Definition memΣ_GpreS : forall {Σ}, subG memΣ Σ -> memGpreS Σ :=
      fun {Σ} => subG_gen_heapGpreS (Σ := Σ) (L := Addr) (V := MemVal).

    Definition mem_inv : forall {Σ}, mcMemGS Σ -> Memory -> iProp Σ :=
      fun {Σ} hG μ =>
        (∃ memmap, gen_heap_interp memmap ∗
           ⌜ map_Forall (fun a v => μ a = v) memmap ⌝
        )%I.

    Definition mem_res `{hG : mcMemGS Σ} : Memory -> iProp Σ :=
      fun μ => ([∗ list] a' ∈ liveAddrs, mapsto a' (DfracOwn 1) (μ a'))%I.

    Lemma initMemMap_works μ : map_Forall (λ (a : Addr) (v : MemVal), μ a = v) (initMemMap μ).
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

    Lemma big_sepM_list_to_map {Σ} {A B : Type} `{Countable A} {l : list A} {f : A -> B} (F : A -> B -> iProp Σ) :
      NoDup l ->
      ([∗ map] l↦v ∈ (list_to_map (map (λ a : A, (a, f a)) l)), F l v)
        ⊢
        [∗ list] v ∈ l, F v (f v).
    Proof.
      intros ndl.
      induction ndl.
      - now iIntros "_".
      - cbn.
        rewrite big_sepM_insert.
        + iIntros "[$ Hrest]".
          now iApply IHndl.
        + apply not_elem_of_list_to_map_1.
          change (fmap fst ?l) with (map fst l).
          now rewrite map_map map_id.
    Qed.

    Lemma mem_inv_init `{gHP : memGpreS Σ} (μ : Memory) :
      ⊢ |==> ∃ mG : mcMemGS Σ, (mem_inv mG μ ∗ mem_res μ)%I.
    Proof.
      iMod (gen_heap_init (gen_heapGpreS0 := gHP) (L := Addr) (V := MemVal) empty) as (gH) "[inv _]".

      pose (memmap := initMemMap μ).
      iMod (gen_heap_alloc_big empty memmap (map_disjoint_empty_r memmap) with "inv") as "(inv & res & _)".
      iModIntro.

      rewrite (right_id empty union memmap).

      iExists (McMemGS gH).
      iSplitL "inv".
      - iExists memmap.
        iFrame.
        iPureIntro.
        apply initMemMap_works.
      - unfold mem_res, initMemMap in *.
        iApply (big_sepM_list_to_map (f := μ) (fun a v => mapsto a (DfracOwn 1) v) with "[$]").
        eapply NoDup_liveAddrs.
    Qed.
  End RiscvPmpIrisParams.

  Include IrisResources RiscvPmpBase RiscvPmpProgram RiscvPmpSemantics.

  Import iris.program_logic.weakestpre.

  Definition WP_loop `{sg : sailGS Σ} : iProp Σ :=
    semWP (FunDef loop) (fun _ _ => True%I) env.nil.

End RiscvPmpIrisBase.
