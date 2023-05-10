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
     Base
     Bitvector
     Iris.Instance
     Iris.Model
     Syntax.Predicates
     RiscvPmp.Base
     RiscvPmp.Machine
     RiscvPmp.IrisModel
     RiscvPmp.Sig.

From iris.base_logic Require Import invariants lib.iprop lib.gen_heap.
From iris.proofmode Require Import tactics.
From stdpp Require namespaces.
Module ns := stdpp.namespaces.

Set Implicit Arguments.
Import bv.notations.

Module RiscvPmpIrisInstance <:
  IrisInstance RiscvPmpBase RiscvPmpProgram RiscvPmpSemantics
    RiscvPmpSignature RiscvPmpIrisBase.
  Import RiscvPmpIrisBase.
  Import RiscvPmpProgram.

  Section WithSailGS.
    Context `{sailRegGS Σ} `{invGS Σ} `{mG : mcMemGS Σ}.
    Variable (live_addrs : list Addr) (mmio_addrs : list Addr).

    Definition reg_file : gset (bv 5) := list_to_set (bv.finite.enum 5).

    Definition interp_ptsreg (r : RegIdx) (v : Word) : iProp Σ :=
      match reg_convert r with
      | Some x => reg_pointsTo x v
      | None => True
      end.

    Definition interp_gprs : iProp Σ :=
      [∗ set] r ∈ reg_file, (∃ v, interp_ptsreg r v)%I.

    Definition PmpEntryCfg : Set := Pmpcfg_ent * Xlenbits.

    Definition interp_pmp_entries (entries : list PmpEntryCfg) : iProp Σ :=
      match entries with
      | (cfg0, addr0) :: (cfg1, addr1) :: [] =>
          reg_pointsTo pmp0cfg cfg0 ∗
                       reg_pointsTo pmpaddr0 addr0 ∗
                       reg_pointsTo pmp1cfg cfg1 ∗
                       reg_pointsTo pmpaddr1 addr1
      | _ => False
      end.

    Definition addr_inc (x : bv 32) (n : nat) : bv 32 :=
      bv.add x (bv.of_nat n).

    Fixpoint get_byte {width : nat} (offset : nat) : bv (width * byte) -> Byte :=
      match width with
      | O   => fun _ => bv.zero
      | S w =>
          fun bytes =>
            let (byte, bytes) := bv.appView byte (w * byte) bytes in
            match offset with
            | O        => byte
            | S offset => get_byte offset bytes
            end
      end.

    (* TODO: change back to words instead of bytes... might be an easier first version
             and most likely still conventient in the future *)
    Definition interp_ptsto (addr : Addr) (b : Byte) : iProp Σ :=
      mapsto addr (DfracOwn 1) b.
    Definition ptstoSth : Addr -> iProp Σ := fun a => (∃ w, interp_ptsto a w)%I.
    Definition ptstoSthL : list Addr -> iProp Σ :=
      fun addrs => ([∗ list] k↦a ∈ addrs, ptstoSth a)%I.
    Lemma ptstoSthL_app {l1 l2} : (ptstoSthL (l1 ++ l2) ⊣⊢ ptstoSthL l1 ∗ ptstoSthL l2)%I.
    Proof. eapply big_sepL_app. Qed.

    Definition interp_ptstomem' {width : nat} (addr : Addr) (bytes : bv (width * byte)) : iProp Σ :=
      [∗ list] offset ∈ seq 0 width,
        interp_ptsto (addr + bv.of_nat offset) (get_byte offset bytes).
    Fixpoint interp_ptstomem {width : nat} (addr : Addr) : bv (width * byte) -> iProp Σ :=
      match width with
      | O   => fun _ => True
      | S w =>
          fun bytes =>
            let (byte, bytes) := bv.appView byte (w * byte) bytes in
            interp_ptsto addr byte ∗ interp_ptstomem (bv.one + addr) bytes
      end%I.

    Definition femto_inv_ns : ns.namespace := (ns.ndot ns.nroot "ptstomem_readonly").
    Definition interp_ptstomem_readonly {width : nat} (addr : Addr) (b : bv (width * byte)) : iProp Σ :=
      inv femto_inv_ns (interp_ptstomem addr b).

    (* Universal contract for single byte/`width` bytes after PMP checks *)
    Definition interp_addr_access_byte (a : Addr) : iProp Σ :=
      if decide (a ∈ mmio_addrs) then False%I (* Creates a proof obligation that the adversary cannot access MMIO. TODO: Change this to a trace filter to grant the adversary access to MMIO *)
      else if decide (a ∈ live_addrs) then ptstoSth a
      else True%I.
    Definition interp_addr_access (base : Addr) (width : nat): iProp Σ :=
      [∗ list] a ∈ bv.seqBv base width, interp_addr_access_byte a.

    Definition all_addrs_def : list Addr := bv.seqBv bv.zero (Nat.pow 2 xlenbits).
    Definition all_addrs_aux : seal (@all_addrs_def). Proof. by eexists. Qed.
    Definition all_addrs := all_addrs_aux.(unseal).
    Lemma all_addrs_eq : all_addrs = all_addrs_def. Proof. rewrite -all_addrs_aux.(seal_eq) //. Qed.
    Lemma addr_in_all_addrs (a : Addr): a ∈ all_addrs.
    Proof.
      rewrite all_addrs_eq.
      apply bv.in_seqBv'; unfold bv.ule, bv.ult.
      - cbn. Lia.lia.
      - destruct a as [bin Hwf].
        cbn [bv.bin].
        rewrite bv.is_wf_spec in Hwf.
        eapply N.lt_le_trans; [exact|].
        rewrite bv.exp2_spec Nat2N.inj_pow.
        Lia.lia.
    Qed.
    Global Opaque all_addrs.
    Definition interp_pmp_addr_access (entries : list PmpEntryCfg) (m : Privilege) : iProp Σ :=
      [∗ list] a ∈ all_addrs,
        (⌜∃ p, Pmp_access a (bv.of_nat 1) entries m p⌝ -∗ interp_addr_access_byte a)%I.

    Definition interp_pmp_addr_access_without (addr : Addr) (width : nat)  (entries : list PmpEntryCfg) (m : Privilege) : iProp Σ :=
      (@interp_addr_access addr width -∗ interp_pmp_addr_access entries m)%I.

    (* TODO: introduce constant for nr of word bytes (replace 4) *)
    Definition interp_ptsto_instr (addr : Addr) (instr : AST) : iProp Σ :=
      (∃ v, @interp_ptstomem 4 addr v ∗ ⌜ pure_decode v = inr instr ⌝)%I.

  End WithSailGS.

  Section RiscvPmpIrisPredicates.

    Import env.notations.

    Equations(noeqns) luser_inst `{sailRegGS Σ, invGS Σ, mcMemGS Σ}
      (p : Predicate) (ts : Env Val (𝑯_Ty p)) : iProp Σ :=
    | pmp_entries              | [ v ]                => interp_pmp_entries v
    | pmp_addr_access          | [ entries; m ]       => interp_pmp_addr_access liveAddrs mmioAddrs entries m
    | pmp_addr_access_without bytes | [ addr; entries; m ] => interp_pmp_addr_access_without liveAddrs mmioAddrs addr bytes entries m
    | gprs                     | _                    => interp_gprs
    | ptsto                    | [ addr; w ]          => interp_ptsto addr w
    | ptstomem_readonly _      | [ addr; w ]          => interp_ptstomem_readonly addr w
    | encodes_instr            | [ code; instr ]      => ⌜ pure_decode code = inr instr ⌝%I
    | ptstomem _               | [ addr; bs]          => interp_ptstomem addr bs
    | ptstoinstr               | [ addr; instr ]      => interp_ptsto_instr addr instr.

    Ltac destruct_pmp_entries :=
      repeat match goal with
      | x : Val ty_pmpentry |- _ =>
          destruct x; auto
      | x : Val (ty.list ty_pmpentry) |- _ =>
          destruct x; auto
      | x : list (Val ty_pmpentry) |- _ =>
          destruct x; auto
      end.

    Definition lduplicate_inst `{sailRegGS Σ, invGS Σ, mcMemGS Σ} :
      forall (p : Predicate) (ts : Env Val (𝑯_Ty p)),
        is_duplicable p = true ->
        (luser_inst p ts) ⊢ (luser_inst p ts ∗ luser_inst p ts).
    Proof.
      destruct p; intros ts Heq; try discriminate Heq;
        clear Heq; cbn in *; env.destroy ts; destruct_pmp_entries; auto.
    Qed.

  End RiscvPmpIrisPredicates.

  Include IrisSignatureRules RiscvPmpBase RiscvPmpProgram RiscvPmpSemantics
    RiscvPmpSignature RiscvPmpIrisBase.
  Include IrisAdequacy RiscvPmpBase RiscvPmpProgram RiscvPmpSemantics
    RiscvPmpSignature RiscvPmpIrisBase.

End RiscvPmpIrisInstance.
