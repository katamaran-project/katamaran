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
     Iris.BinaryInstance
     Iris.BinaryWp
     trace
     Syntax.Predicates
     RiscvPmp.Base
     RiscvPmp.Machine
     RiscvPmp.IrisModelBinary
     RiscvPmp.IrisInstance
     RiscvPmp.Sig.

From iris.base_logic Require Import invariants lib.iprop lib.gen_heap.
From iris.proofmode Require Import tactics.
From stdpp Require namespaces.
Module ns := stdpp.namespaces.

Set Implicit Arguments.
Import bv.notations.

Module RiscvPmpIrisInstance2 <:
  IrisInstance2 RiscvPmpBase RiscvPmpProgram RiscvPmpSemantics
    RiscvPmpSignature RiscvPmpIrisBase2.
  Import RiscvPmpIrisBase2.
  Import RiscvPmpProgram.

  Section WithSailGS.
    Context `{sailRegGS2 Σ} `{invGS Σ} `{mG : mcMemGS2 Σ}.
    Variable (live_addrs : list Addr) (mmio_addrs : list Addr).

    Definition reg_file : gset (bv 5) := list_to_set (bv.finite.enum 5).

    Definition reg_pointsTo21 {τ} (r : Reg τ) (v : Val τ) : iProp Σ :=
      reg_pointsTo2 r v v.
    Definition interp_ptsreg (r : RegIdx) (v : Word) : iProp Σ :=
      match reg_convert r with
      | Some x => reg_pointsTo21 x v
      | None => True
      end.

    Definition interp_gprs : iProp Σ :=
      [∗ set] r ∈ reg_file, (∃ v, interp_ptsreg r v)%I.

    Definition PmpEntryCfg : Set := Pmpcfg_ent * Xlenbits.

    Definition interp_pmp_entries (entries : list PmpEntryCfg) : iProp Σ :=
      match entries with
      | (cfg0, addr0) :: (cfg1, addr1) :: [] =>
          reg_pointsTo21 pmp0cfg cfg0 ∗
                       reg_pointsTo21 pmpaddr0 addr0 ∗
                       reg_pointsTo21 pmp1cfg cfg1 ∗
                       reg_pointsTo21 pmpaddr1 addr1
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

    Definition femto_inv_ro_ns : ns.namespace := (ns.ndot ns.nroot "inv_ro").
    Definition interp_ptsto (addr : Addr) (b : Byte) : iProp Σ :=
      RiscvPmpIrisInstance.interp_ptsto (mG := mc_ghGS2_left) addr b ∗
      RiscvPmpIrisInstance.interp_ptsto (mG := mc_ghGS2_right) addr b ∗
      ⌜¬ withinMMIO addr 1⌝.
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

    Definition interp_ptstomem_readonly {width : nat} (addr : Addr) (b : bv (width * byte)) : iProp Σ :=
      inv femto_inv_ro_ns (interp_ptstomem addr b).

    (* The address we will perform all writes to is the first legal MMIO address *)
    Definition write_addr : Addr := bv.of_nat maxAddr.
    Definition event_pred (width : nat) (e : Event) := e = mkEvent IOWrite write_addr width (bv.of_N 42).
    Definition mmio_pred (width : nat) (t : Trace): Prop := Forall (event_pred width) t.
    Definition femto_inv_mmio_ns : ns.namespace := (ns.ndot ns.nroot "inv_mmio").
    Definition interp_inv_mmio (width : nat) : iProp Σ :=
      inv femto_inv_mmio_ns (∃ t,
            (@tr_frag _ _ (@traceG_preG _ _ mc_gtGS2_left) (@trace_name _ _ mc_gtGS2_left) t)
            ∗ (@tr_frag _ _ (@traceG_preG _ _ mc_gtGS2_right) (@trace_name _ _ mc_gtGS2_right) t)
            ∗ ⌜mmio_pred width t⌝).

    (* NOTE: no read predicate yet, as we will not perform nor allow MMIO reads. *)
    (* NOTE: no local state yet, but this should be an iProp for the general case *)
    Definition interp_mmio_checked_write {width : nat} (addr : Addr) (bytes : bv (width * byte)) : iProp Σ := ⌜addr = write_addr ∧ bytes = (bv.of_N 42)⌝.

    (* Universal contract for single byte/`width` bytes after PMP checks *)
    Definition interp_addr_access_byte (a : Addr) : iProp Σ :=
      if decide (a ∈ mmio_addrs) then False%I (* Creates a proof obligation that the adversary cannot access MMIO. TODO: Change this to a trace filter to grant the adversary access to MMIO *)
      else if decide (a ∈ live_addrs) then ptstoSth a
      else True%I. (* Could be `False` as well *)
    Definition interp_addr_access (base : Addr) (width : nat): iProp Σ :=
      [∗ list] a ∈ bv.seqBv base width, interp_addr_access_byte a.

    Definition all_addrs_def := RiscvPmpIrisInstance.all_addrs_def.
    Definition all_addrs_aux := RiscvPmpIrisInstance.all_addrs_aux.
    Definition all_addrs := RiscvPmpIrisInstance.all_addrs.

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

    Equations(noeqns) luser_inst2 `{sailRegGS2 Σ, invGS Σ, mcMemGS2 Σ}
      (p : Predicate) (ts : Env Val (𝑯_Ty p)) : iProp Σ :=
    | pmp_entries              | [ v ]                => interp_pmp_entries v
    | pmp_addr_access          | [ entries; m ]       => interp_pmp_addr_access liveAddrs mmioAddrs entries m
    | pmp_addr_access_without bytes | [ addr; entries; m ] => interp_pmp_addr_access_without liveAddrs mmioAddrs addr bytes entries m
    | gprs                     | _                    => interp_gprs
    | ptsto                    | [ addr; w ]          => interp_ptsto addr w
    | ptstomem_readonly _      | [ addr; w ]          => interp_ptstomem_readonly addr w
    | inv_mmio bytes           | _                    => interp_inv_mmio bytes
    | mmio_checked_write _     | [ addr; w ]          => interp_mmio_checked_write addr w
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

    Definition lduplicate_inst2 `{sailRegGS2 Σ, invGS Σ, mcMemGS2 Σ} :
      forall (p : Predicate) (ts : Env Val (𝑯_Ty p)),
        is_duplicable p = true ->
        (luser_inst2 p ts) ⊢ (luser_inst2 p ts ∗ luser_inst2 p ts).
    Proof.
      destruct p; intros ts Heq; try discriminate Heq;
        clear Heq; cbn in *; env.destroy ts; destruct_pmp_entries; auto.
    Qed.

  End RiscvPmpIrisPredicates.

  Section RiscVPmpIrisInstanceProofs.
    Context `{sr : sailRegGS2 Σ} `{igs : invGS Σ} `{mG : mcMemGS2 Σ}.

    (* Induction does not work here due to shape of `interp_pmp_addr_access_without`*)
    Lemma interp_pmp_addr_inj_extr {entries m p} base width :
      (bv.bin base + N.of_nat width < bv.exp2 xlenbits)%N →
      Pmp_access base (bv.of_nat width) entries m p →
      (interp_pmp_addr_access liveAddrs mmioAddrs entries m ⊣⊢
         (interp_addr_access liveAddrs mmioAddrs base width ∗ interp_pmp_addr_access_without liveAddrs mmioAddrs base width entries m))%I.
    Proof.
      intros Hrep Hpmp.
      (* Discharge easy direction *)
      iSplit ; last (iIntros "[H Hcont]"; by iApply "Hcont").
      unfold interp_pmp_addr_access_without, interp_pmp_addr_access, all_addrs.
      (* Hard direction: create `interp_addr_access` from scratch *)
      pose proof (RiscvPmpIrisInstance.in_allAddrs_split base width Hrep) as [l1 [l2 Hall]]. rewrite Hall.
      rewrite !big_sepL_app.
      iIntros "(Hlow & Hia & Hhigh)".
      iSplitL "Hia".
      - iApply (big_sepL_mono with "Hia"). iIntros (? ? ?) "Hyp".
        iApply "Hyp". iPureIntro.
        eexists; eapply RiscvPmpIrisInstance.pmp_seqBv_restrict; eauto.
      - iIntros "Hia". iFrame.
        iDestruct (big_sepL_mono with "Hia") as "Hia"; last iFrame.
        now iIntros.
    Qed.

    Lemma ptstomem_bv_app :
      forall {n} (a : Addr) (b : bv byte) (bs : bv (n * byte)),
        @interp_ptstomem _ _ (S n)%nat a (bv.app b bs)
        ⊣⊢
        (interp_ptsto a b ∗ interp_ptstomem (bv.one + a) bs).
    Proof. intros; cbn [interp_ptstomem]; now rewrite bv.appView_app. Qed.

    Lemma interp_ptstomem_big_sepS (bytes : nat) (paddr : Addr):
      (∃ (w : bv (bytes * byte)), interp_ptstomem paddr w) ⊣⊢
        ptstoSthL (bv.seqBv paddr bytes).
    Proof.
      generalize dependent paddr.
      iInduction bytes as [|bytes] "IHbytes"; iIntros (paddr).
      - unfold ptstoSthL. unshelve auto. exact bv.zero.
      - rewrite bv.seqBv_succ (app_comm_cons []) ptstoSthL_app.
        iDestruct ("IHbytes" $! (bv.one + paddr)) as "[IHL IHR]".
        iSplit.
        *  iIntros "[%w H]".
           destruct (bv.appView byte (bytes * byte) w) as [b bs].
           rewrite ptstomem_bv_app.
           iDestruct "H" as "[Hb Hbs]".
           iSplitL "Hb".
           + cbn. iSplit; [by iExists _ | auto].
           + iApply "IHL"; by iExists _.
        * iIntros "[[[%b Hhd] _] Htl]".
          iDestruct ("IHR" with "Htl") as "[%btl Htl]".
          iExists (bv.app b btl).
          rewrite ptstomem_bv_app. iFrame.
    Qed.

    (* Use knowledge of RAM to extract byte *)
    Lemma interp_addr_access_byte_extr  base :
      base ∈ liveAddrs ->
      (interp_addr_access_byte liveAddrs mmioAddrs base ⊢
      ptstoSth base).
    Proof.
      intros (* Hpmp *) Hlive.
      unfold interp_addr_access_byte, ptstoSth, interp_ptsto.
      repeat case_decide; auto; iIntros; by exfalso.
    Qed.

    (* Use knowledge of RAM to extract range *)
    Lemma interp_addr_access_extr base width :
      (minAddr ≤ N.to_nat (bv.bin base)) →
      (N.to_nat (bv.bin base) + width ≤ maxAddr) →
      (bv.bin base + N.of_nat width < bv.exp2 xlenbits)%N →
      interp_addr_access liveAddrs mmioAddrs base width ⊢
      (∃ (w : bv (width * byte)), interp_ptstomem base w).
    Proof.
      intros HminOK HmaxOK Hrep.
      rewrite interp_ptstomem_big_sepS.
      unfold interp_addr_access, ptstoSthL.
      iApply big_sepL_mono.
      iIntros (? y Hseq) "//".
      iApply interp_addr_access_byte_extr.
      apply bv.seqBv_spec in Hseq as Hspec.
      apply list.lookup_lt_Some in Hseq. rewrite bv.seqBv_len in Hseq.
      unfold liveAddrs, bv.seqBv.
      rewrite -(bv.of_Z_unsigned y).
      apply elem_of_list_fmap_1.
      rewrite elem_of_seqZ.
      subst y.
      unfold maxAddr in HmaxOK.
      rewrite /bv.unsigned bv.bin_add_small !bv.bin_of_nat_small; lia. (* TODO: use representability of min/maxAddr here, once they are made properly opaque *)
    Qed.

    (* Inserting a byte is always possible *)
    Lemma interp_addr_access_byte_inj base :
       ptstoSth base -∗ interp_addr_access_byte liveAddrs mmioAddrs base.
    Proof.
      unfold interp_addr_access_byte, ptstoSth, interp_ptsto.
      iIntros "HFalse". iDestruct "HFalse" as (?) "(? & ? & %HFalse)".
      repeat case_decide; auto.
      iExists _; now iFrame.
    Qed.

    (* Inserting a range is always possible *)
    Lemma interp_addr_access_inj base width:
      (∃ (w : bv (width * byte)), interp_ptstomem base w) ⊢
      interp_addr_access liveAddrs mmioAddrs base width.
    Proof.
      iIntros "Hint".
      rewrite interp_ptstomem_big_sepS.
      unfold interp_addr_access, ptstoSthL.
      iApply big_sepL_mono; last auto.
      iIntros (? y Hseq) "/=".
      iApply interp_addr_access_byte_inj.
    Qed.
  End RiscVPmpIrisInstanceProofs.

  Include IrisSignatureRules2 RiscvPmpBase RiscvPmpProgram RiscvPmpSemantics
    RiscvPmpSignature RiscvPmpIrisBase2.
  Include IrisAdequacy2 RiscvPmpBase RiscvPmpProgram RiscvPmpSemantics
    RiscvPmpSignature RiscvPmpIrisBase2.

End RiscvPmpIrisInstance2.
