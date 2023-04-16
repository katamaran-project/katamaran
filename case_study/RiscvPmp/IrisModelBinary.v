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
     Iris.BinaryWp
     Iris.BinaryInstance
     RiscvPmp.Machine
     RiscvPmp.IrisModel.
From iris Require Import
     base_logic.lib.gen_heap
     proofmode.tactics.

Set Implicit Arguments.

Import RiscvPmpProgram.

(* Instantiate the Iris framework solely using the operational semantics. At
   this point we do not commit to a set of contracts nor to a set of
   user-defined predicates. *)
Module RiscvPmpIrisBase2 <: IrisBase2 RiscvPmpBase RiscvPmpProgram RiscvPmpSemantics.
  (* Pull in the definition of the LanguageMixin and register ghost state. *)
  Include IrisPrelims RiscvPmpBase RiscvPmpProgram RiscvPmpSemantics.

  (* Defines the memory ghost state. *)
  Section RiscvPmpIrisParams2.
    Import bv.
    Definition Byte : Set := bv 8.
    Definition MemVal : Set := Byte.

    Class mcMemGS2 Σ :=
      McMemGS2 {
          (* ghost variable for tracking state of registers *)
          mc_ghGS2 : gen_heapGS Addr (MemVal * MemVal) Σ
        }.
    #[export] Existing Instance mc_ghGS2.

    Definition memGpreS2 : gFunctors -> Set := fun Σ => gen_heapGpreS Addr (MemVal * MemVal) Σ.
    Definition memGS2 : gFunctors -> Set := mcMemGS2.
    Definition memΣ2 : gFunctors := gen_heapΣ Addr (MemVal * MemVal).

    Definition liveAddrs := bv.seqBv (@bv.of_nat xlenbits minAddr) lenAddr.
    Lemma NoDup_liveAddrs : NoDup liveAddrs.
    Proof. now eapply Prelude.nodup_fixed. Qed.

    #[global] Arguments liveAddrs : simpl never.

    Definition initMemMap2 μ1 μ2 := (list_to_map (map (fun a => (a , (μ1 a , μ2 a))) liveAddrs) : gmap Addr (MemVal * MemVal)).

    Definition memΣ_GpreS2 : forall {Σ}, subG memΣ2 Σ -> memGpreS2 Σ :=
      fun {Σ} => subG_gen_heapGpreS (Σ := Σ) (L := Addr) (V := MemVal * MemVal).

    Definition mem_inv2 : forall {Σ}, mcMemGS2 Σ -> Memory -> Memory -> iProp Σ :=
      fun {Σ} hG μ1 μ2 =>
        (∃ memmap, gen_heap_interp memmap ∗
           ⌜ map_Forall (fun a v => (μ1 a , μ2 a) = v) memmap ⌝
        )%I.

    Definition mem_res2 `{hG : mcMemGS2 Σ} : Memory -> Memory -> iProp Σ :=
      fun μ1 μ2 => ([∗ list] a' ∈ liveAddrs, mapsto a' (DfracOwn 1) (μ1 a' , μ2 a'))%I.

    Lemma initMemMap2_works μ1 μ2 : map_Forall (λ (a : Addr) (v : MemVal * MemVal), (μ1 a , μ2 a) = v) (initMemMap2 μ1 μ2).
    Proof.
      unfold initMemMap2.
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

    Lemma mem_inv_init2 `{gHP : memGpreS2 Σ} (μ1 μ2 : Memory) :
      ⊢ |==> ∃ mG : mcMemGS2 Σ, (mem_inv2 mG μ1 μ2 ∗ mem_res2 μ1 μ2)%I.
    Proof.
      iMod (gen_heap_init (gen_heapGpreS0 := gHP) (L := Addr) (V := MemVal * MemVal) empty) as (gH) "[inv _]".

      pose (memmap := initMemMap2 μ1 μ2).
      iMod (gen_heap_alloc_big empty memmap (map_disjoint_empty_r memmap) with "inv") as "(inv & res & _)".
      iModIntro.

      rewrite (right_id empty union memmap).

      iExists (McMemGS2 gH).
      iSplitL "inv".
      - iExists memmap.
        iFrame.
        iPureIntro.
        apply initMemMap2_works.
      - unfold mem_res2, initMemMap2 in *.
        iApply (RiscvPmpIrisBase.big_sepM_list_to_map (f := fun a => (μ1 a , μ2 a)) (fun a v => mapsto a (DfracOwn 1) v) with "[$]").
        eapply NoDup_liveAddrs.
    Qed.

    (* Note: this defaultRegStore is only needed for technical reason, it is not used. *)
    Definition defaultRegStore : RegStore :=
      fun τ r =>
        match r with
          pc => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | nextpc => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | mstatus => (MkMstatus Machine : TypeDecl.ty.Val ty_mstatus)
        | mtvec => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | mcause => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | mepc => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | cur_privilege => Machine
        | x1 => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x2 => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x3 => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x4 => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x5 => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x6 => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x7 => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | pmp0cfg => (MkPmpcfg_ent false OFF true true true : TypeDecl.ty.Val ty_pmpcfg_ent)
        | pmp1cfg => (MkPmpcfg_ent false OFF true true true : TypeDecl.ty.Val ty_pmpcfg_ent)
        | pmpaddr0 => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | pmpaddr1 => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        end.

    (* Note: this defaultMemory is only needed for technical reason, it is not used. *)
    Definition defaultMemory : Memory := fun a => bv.zero.
  End RiscvPmpIrisParams2.

  Include IrisResources2 RiscvPmpBase RiscvPmpProgram RiscvPmpSemantics.

End RiscvPmpIrisBase2.
