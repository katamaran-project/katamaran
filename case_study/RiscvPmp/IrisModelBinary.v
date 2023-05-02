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
  Include RiscvPmpIrisBase.

  (* Defines the memory ghost state. *)
  Section RiscvPmpIrisParams2.
    Import bv.

    Class mcMemGS2 Σ :=
      McMemGS2 {
          (* two copies of the unary ghost variables *)
          mc_ghGS2_left : RiscvPmpIrisBase.mcMemGS Σ
        ; mc_ghGS2_right : RiscvPmpIrisBase.mcMemGS Σ
        }.

    Definition memGpreS2 : gFunctors -> Set := fun Σ => prod (RiscvPmpIrisBase.memGpreS Σ) (RiscvPmpIrisBase.memGpreS Σ).
    Definition memGS2 : gFunctors -> Set := mcMemGS2.
    Definition memΣ2 : gFunctors := gFunctors.app (RiscvPmpIrisBase.memΣ) (RiscvPmpIrisBase.memΣ).

    Definition memΣ_GpreS2 : forall {Σ}, subG memΣ2 Σ -> memGpreS2 Σ :=
      fun {Σ} HsG => (subG_gen_heapGpreS (Σ := Σ) (L := Addr) (V := MemVal) (fst (subG_inv _ _ _ HsG)),
                    subG_gen_heapGpreS (Σ := Σ) (L := Addr) (V := MemVal) (snd (subG_inv _ _ _ HsG))).

    Definition mem_inv2 : forall {Σ}, mcMemGS2 Σ -> Memory -> Memory -> iProp Σ :=
      fun {Σ} hG μ1 μ2 =>
        (RiscvPmpIrisBase.mem_inv mc_ghGS2_left μ1 ∗ RiscvPmpIrisBase.mem_inv mc_ghGS2_right μ2)%I.

    Definition mem_res2 `{hG : mcMemGS2 Σ} : Memory -> Memory -> iProp Σ :=
      fun μ1 μ2 => (RiscvPmpIrisBase.mem_res (hG := mc_ghGS2_left) μ1 ∗
                   RiscvPmpIrisBase.mem_res (hG := mc_ghGS2_right) μ2)%I.

    Lemma mem_inv_init2 `{gHP : memGpreS2 Σ} (μ1 μ2 : Memory) :
      ⊢ |==> ∃ mG : mcMemGS2 Σ, (mem_inv2 mG μ1 μ2 ∗ mem_res2 μ1 μ2)%I.
    Proof.
      iMod (RiscvPmpIrisBase.mem_inv_init (gHP := fst gHP) μ1) as (mG1) "[inv1 res1]".
      iMod (RiscvPmpIrisBase.mem_inv_init (gHP := snd gHP) μ2) as (mG2) "[inv2 res2]".
      iModIntro.
      iExists (McMemGS2 mG1 mG2).
      iSplitL "inv1 inv2"; iFrame.
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
        | x1  => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x2  => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x3  => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x4  => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x5  => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x6  => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x7  => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x8  => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x9  => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x10 => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x11 => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x12 => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x13 => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x14 => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x15 => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x16 => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x17 => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x18 => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x19 => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x20 => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x21 => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x22 => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x23 => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x24 => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x25 => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x26 => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x27 => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x28 => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x29 => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x30 => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
        | x31 => (bv.zero : TypeDecl.ty.Val ty_xlenbits)
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
