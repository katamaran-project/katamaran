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
     Hoare
     Bitvector
     Iris.BinaryWeakestPre
     Iris.BinaryAdequacy
     Iris.BinaryInstance
     trace
     Syntax.Predicates
     RiscvPmp.Base
     RiscvPmp.Machine
     RiscvPmp.IrisModel
     RiscvPmp.IrisModelBinary
     RiscvPmp.IrisInstance
     RiscvPmp.PmpCheck
     RiscvPmp.Sig.

From iris.base_logic Require Import invariants lib.iprop lib.gen_heap.
From iris.proofmode Require Import tactics.
From stdpp Require namespaces.
Module ns := stdpp.namespaces.

Set Implicit Arguments.
Import bv.notations.

Module Type RiscvPmpIrisAdeqParams2
  (Import RVPCOM : RiscvPmpIrisBaseCommon)
  (RVPBASEl : RiscvPmpIrisBase LeftOrRightLeft RVPCOM)
  (RVPBASEr : RiscvPmpIrisBase LeftOrRightRight RVPCOM)
  (Import RVPBASE2 : RiscvPmpIrisBase2 RVPCOM RVPBASEl RVPBASEr)
<: IrisAdeqParameters2 RiscvPmpBase RiscvPmpProgram RiscvPmpSemantics RVPCOM RVPBASEl RVPBASEr RVPBASE2.


  Definition memGpreS2 : gFunctors -> Set := memGpreS.

  Definition memΣ2 : gFunctors := memΣ.

  Definition memΣ_GpreS2 : forall {Σ}, subG memΣ2 Σ -> memGpreS2 Σ := @memΣ_GpreS.

  Definition mem_res `{hG : mcMemGS Σ} : Memory -> iProp Σ :=
    fun μ => (([∗ list] a' ∈ liveAddrs, pointsto a' (DfracOwn 1) (memory_ram μ a')) ∗
             tr_frag (memory_trace μ) ∗
             nothingPending
          )%I.

  Definition mem_res2 `{hG : memGS2 Σ} : Memory -> Memory -> iProp Σ :=
    fun μ1 μ2 => (mem_res (hG := @mc_ghGS2_left _ hG) μ1 ∗
                 mem_res (hG := @mc_ghGS2_right _ hG) μ2)%I.

  (* Lemma mem_inv_init `{gHP : !mcMemPreGS Σ} (μ : Memory) : *)
  (*   ⊢ |==> ∃ mG : mcMemGS2 Σ, (mem_inv mG μ ∗ mem_res μ)%I. *)
  (* Proof. *)
  (*   iMod (gen_heap_init (L := Addr) (V := MemVal) memmap) as (gH) "[Hinv [Hmapsto _]]". *)
  (*   iMod (trace_alloc (memory_trace μ)) as (gT) "[Hauth Hfrag]". *)
  (*   iMod writePending_alloc as (gP) "[HauthPend HfragPend]". *)
  (*   iModIntro. *)
  (*   iExists (McMemGS gH gT gP). *)
  (*   iSplitL "Hinv Hauth HauthPend". *)
  (*   - iExists memmap. *)
  (*     iFrame. *)
  (*     iPureIntro. *)
  (*     apply initMemMap_works. *)
  (*   - unfold mem_res, initMemMap in *. iFrame. *)
  (*     iApply (big_sepM_list_to_map (f := memory_ram μ) (fun a v => pointsto a (DfracOwn 1) v) with "[$]"). *)
  (*     eapply NoDup_liveAddrs. *)
  (* Qed. *)

  Lemma initMemMap_works μ : map_Forall (λ (a : Addr) (v : MemVal), memory_ram μ a = v) (initMemMap μ).
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

  Lemma mem_inv_init2 `{gHP : memGpreS Σ} (μ1 μ2 : Memory) :
    ⊢ |==> ∃ mG : memGS2 Σ, (mem_inv2 mG μ1 μ2 ∗ mem_res2 μ1 μ2)%I.
  Proof.
    unfold memGpreS in gHP.
    pose (memmap1 := initMemMap μ1).
    iMod (gen_heap_init (L := Addr) (V := MemVal) memmap1) as (gH1) "[Hinv1 [Hmapsto1 _]]".
    iMod (trace_alloc (memory_trace μ1)) as (gT1) "[Hauth1 Hfrag1]".
    iMod writePending_alloc as (gP1) "[HauthPend1 HfragPend1]".
    pose (memmap2 := initMemMap μ2).
    iMod (gen_heap_init (L := Addr) (V := MemVal) memmap2) as (gH2) "[Hinv2 [Hmapsto2 _]]".
    iMod (trace_alloc (memory_trace μ2)) as (gT2) "[Hauth2 Hfrag2]".
    iMod writePending_alloc as (gP2) "[HauthPend2 HfragPend2]".
    iModIntro.
    iExists (McMemGS2 (McMemGS gH1 gT1 gP1) (McMemGS gH2 gT2 gP2)).
    iSplitL "Hinv1 Hinv2 Hauth1 Hauth2 HauthPend1 HauthPend2".
    - iFrame "Hinv1 Hinv2 Hauth1 Hauth2".
      iPureIntro; split; apply initMemMap_works.
      (* HauthPend*? *)
    - unfold mem_res2, mem_res, initMemMap in *.
      iFrame "Hfrag1 Hfrag2 HfragPend1 HfragPend2".
      iSplitL "Hmapsto1".
      + iPoseProof (big_sepM_list_to_map with "Hmapsto1") as "Hm".
        { eapply NoDup_liveAddrs. }
        change (map ?f liveAddrs) with (fmap f liveAddrs).
        now rewrite big_sepL_fmap.
      + iPoseProof (big_sepM_list_to_map with "Hmapsto2") as "Hm".
        { eapply NoDup_liveAddrs. }
        change (map ?f liveAddrs) with (fmap f liveAddrs).
        now rewrite big_sepL_fmap.
  Qed.

End RiscvPmpIrisAdeqParams2.

Module Type RiscvPmpIrisInstancePredicates2
  (Import RVPCOM : RiscvPmpIrisBaseCommon)
  (RVPBASEl : RiscvPmpIrisBase LeftOrRightLeft RVPCOM)
  (RVPPREDl : RiscvPmpIrisInstancePredicates LeftOrRightLeft RVPCOM RVPBASEl)
  (RVPBASEr : RiscvPmpIrisBase LeftOrRightRight RVPCOM)
  (RVPPREDr : RiscvPmpIrisInstancePredicates LeftOrRightRight RVPCOM RVPBASEr)
  (Import RVPBASE2 : RiscvPmpIrisBase2 RVPCOM RVPBASEl RVPBASEr).

  Import RiscvPmpProgram.

  Section WithMemory.
    Context {Σ : gFunctors} {mG : memGS2 Σ}.

    Definition mG' := mG : mcMemGS2 Σ.
    Existing Instance mG'.

    Definition interp_ptsto_one (k : Exec) (addr : Addr) (b : Byte) : iProp Σ :=
      match k with
      | Left  => RVPPREDl.interp_ptsto (mG := mc_ghGS2_left) addr b
      | Right => RVPPREDr.interp_ptsto (mG := mc_ghGS2_right) addr b
      end.

    Definition femto_inv_ro_ns : ns.namespace := (ns.ndot ns.nroot "inv_ro").
    Definition interp_ptsto (addr : Addr) (b : Byte) : iProp Σ :=
      interp_ptsto_one Left addr b ∗ interp_ptsto_one Right addr b.
    Definition ptstoSth : Addr -> iProp Σ := fun a => (∃ w, interp_ptsto a w)%I.
    Definition ptstoSthL : list Addr -> iProp Σ :=
      fun addrs => ([∗ list] k↦a ∈ addrs, ptstoSth a)%I.
    Lemma ptstoSthL_app {l1 l2} : (ptstoSthL (l1 ++ l2) ⊣⊢ ptstoSthL l1 ∗ ptstoSthL l2)%I.
    Proof. eapply big_sepL_app. Qed.

    Definition interp_ptstomem {width : nat} (addr : Addr) (v : bv (width * byte)) : iProp Σ :=
      RVPPREDl.interp_ptstomem (mG := mc_ghGS2_left) addr v ∗
        RVPPREDr.interp_ptstomem (mG := mc_ghGS2_right) addr v.

    Definition interp_ptstomem_readonly `{invGS Σ} {width : nat} (addr : Addr) (b : bv (width * byte)) : iProp Σ :=
      RVPPREDl.interp_ptstomem_readonly (mG := mc_ghGS2_left) addr b ∗
        RVPPREDr.interp_ptstomem_readonly (mG := mc_ghGS2_right) addr b.

    (* NOTE: no read predicate yet, as we will not perform nor allow MMIO reads. *)
    (* NOTE: no local state yet, but this should be an iProp for the general case *)
    Definition interp_mmio_checked_write {width : nat} (addr : Addr) (bytes : bv (width * byte)) : iProp Σ := ⌜addr = write_addr ∧ bytes = (bv.of_N 42)⌝.

    Section WithAddrs.
      Variable (live_addrs mmio_addrs : list Addr).

      (* Universal contract for single byte/`width` bytes after PMP checks *)
      Definition interp_addr_access_byte (a : Addr) : iProp Σ :=
        if decide (a ∈ mmio_addrs) then False%I (* Creates a proof obligation that the adversary cannot access MMIO. TODO: Change this to a trace filter to grant the adversary access to MMIO *)
        else if decide (a ∈ live_addrs) then ptstoSth a
             else True%I. (* Could be `False` as well *)
      Definition interp_addr_access (base : Addr) (width : nat): iProp Σ :=
        [∗ list] a ∈ bv.seqBv base (N.of_nat width), interp_addr_access_byte a.

      Definition interp_pmp_addr_access (entries : list PmpEntryCfg) (m : Privilege) : iProp Σ :=
        [∗ list] a ∈ all_addrs,
          (⌜∃ p, Pmp_access a (bv.of_nat 1) entries m p⌝ -∗ interp_addr_access_byte a)%I.

      Definition interp_pmp_addr_access_without (addr : Addr) (width : nat)  (entries : list PmpEntryCfg) (m : Privilege) : iProp Σ :=
        (@interp_addr_access addr width -∗ interp_pmp_addr_access entries m)%I.

    End WithAddrs.

    (* TODO: introduce constant for nr of word bytes (replace 4) *)
    Definition interp_ptsto_instr (addr : Addr) (instr : AST) : iProp Σ :=
      (∃ v, @interp_ptstomem 4 addr v ∗ ⌜ pure_decode v = inr instr ⌝)%I.
  End WithMemory.
  Section WithSailGS.
    Context `{sailRegGS2 Σ}.

    Definition reg_pointsTo21 {τ} (r : Reg τ) (v : Val τ) : iProp Σ :=
      reg_pointsTo2 r v v.

    Definition interp_gprs (exclude : gset (Reg ty_xlenbits)) : iProp Σ :=
      [∗ set] r ∈ GPRS ∖ exclude, (∃ v, reg_pointsTo21 r v)%I.

    Lemma interp_gprs_with_excluded_gen `{sailGS2 Σ} (exclude1 exclude2 : gset (Reg ty_xlenbits)) :
      exclude2 ⊆ GPRS ∖ exclude1 ->
      ([∗ set] r ∈ exclude2, ∃ v, reg_pointsTo21 r v) ∗ interp_gprs (exclude1 ∪ exclude2) ⊣⊢ interp_gprs exclude1.
    Proof.
      intros Hsub1.
      unfold interp_gprs.
      iApply bi.wand_iff_sym.
      rewrite <- difference_difference_l_L.
      now iApply RVPPREDl.big_sepS_delete_multi.
    Qed.

    Lemma interp_gprs_with_excluded `{sailGS2 Σ} (exclude : gset (Reg ty_xlenbits)) :
      exclude ⊆ GPRS ->
      ([∗ set] r ∈ exclude, ∃ v, reg_pointsTo21 r v) ∗ interp_gprs exclude ⊣⊢ interp_gprs ∅.
    Proof.
      intros Hsub.
      rewrite <- union_empty_l_L at 2.
      now iApply interp_gprs_with_excluded_gen.
    Qed.

    Definition interp_pmp_entries (entries : list PmpEntryCfg) : iProp Σ :=
      match entries with
      | (cfg0, addr0) :: (cfg1, addr1) :: [] =>
          reg_pointsTo21 pmp0cfg cfg0 ∗
          reg_pointsTo21 pmpaddr0 addr0 ∗
          reg_pointsTo21 pmp1cfg cfg1 ∗
          reg_pointsTo21 pmpaddr1 addr1
      | _ => False
      end.

  End WithSailGS.
End RiscvPmpIrisInstancePredicates2.

Module Type RiscvPmpIrisInstance2 (FL : FailLogic)
  (Import RVPCOM : RiscvPmpIrisBaseCommon)
  (RVPBASEl : RiscvPmpIrisBase LeftOrRightLeft RVPCOM)
  (RVPPREDl : RiscvPmpIrisInstancePredicates LeftOrRightLeft RVPCOM RVPBASEl)
  (RVPBASEr : RiscvPmpIrisBase LeftOrRightRight RVPCOM)
  (RVPPREDr : RiscvPmpIrisInstancePredicates LeftOrRightRight RVPCOM RVPBASEr)
  (Import RVPBASE2 : RiscvPmpIrisBase2 RVPCOM RVPBASEl RVPBASEr)
  (Import RVPPRED2 : RiscvPmpIrisInstancePredicates2 RVPCOM RVPBASEl RVPPREDl RVPBASEr RVPPREDr RVPBASE2)
  (Import RVPADEQ2 : RiscvPmpIrisAdeqParams2 RVPCOM RVPBASEl RVPBASEr RVPBASE2)
<: IrisInstance2 RiscvPmpBase RiscvPmpSignature RiscvPmpProgram FL RiscvPmpSemantics
     RVPCOM RVPBASEl RVPBASEr RVPBASE2 RVPADEQ2.

  (* Module Right := RiscvPmpIrisInstanceRight FL. *)
  Import RiscvPmpProgram.

  Section RiscvPmpIrisPredicates.

    Import env.notations.

    Equations(noeqns) luser_inst2 `{sailRegGS2 Σ, invGS Σ, mG : memGS2 Σ}
      (p : Predicate) (ts : Env Val (𝑯_Ty p)) : iProp Σ :=
    | pmp_entries              | [ v ]                => interp_pmp_entries v
    | pmp_addr_access          | [ entries; m ]       => interp_pmp_addr_access liveAddrs mmioAddrs entries m
    | pmp_addr_access_without bytes | [ addr; entries; m ] => interp_pmp_addr_access_without liveAddrs mmioAddrs addr bytes entries m
    | gprs                     | _                    => interp_gprs ∅
    | ptsto                    | [ addr; w ]          => interp_ptsto addr w
    | ptsto_one k              | [ addr; w ]          => interp_ptsto_one k addr w
    | ptstomem_readonly _      | [ addr; w ]          => interp_ptstomem_readonly addr w
    | inv_mmio bytes           | _                    => interp_inv_mmio (mG := mG) bytes
    | mmio_checked_write _     | [ addr; w ]          => interp_mmio_checked_write addr w
    | encodes_instr            | [ code; instr ]      => ⌜ pure_decode code = inr instr ⌝%I
    | ptstomem _               | [ addr; bs]          => interp_ptstomem addr bs
    | ptstoinstr               | [ addr; instr ]      => interp_ptsto_instr addr instr
    (* notWritten and Written are only used for the unary verification, we will not
       reason using Katamaran with them in the binary verification. *)
    | Sig.nothingPending       | _                    => False
    | Sig.written width        | [ addr; val ]        => False.

    Ltac destruct_pmp_entries :=
      repeat match goal with
      | x : Val ty_pmpentry |- _ =>
          destruct x; auto
      | x : Val (ty.list ty_pmpentry) |- _ =>
          destruct x; auto
      | x : list (Val ty_pmpentry) |- _ =>
          destruct x; auto
      end.

    Definition lduplicate_inst2 `{sailRegGS2 Σ, invGS Σ, memGS2 Σ} :
      forall (p : Predicate) (ts : Env Val (𝑯_Ty p)),
        is_duplicable p = true ->
        (luser_inst2 p ts) ⊢ (luser_inst2 p ts ∗ luser_inst2 p ts).
    Proof.
      destruct p; intros ts Heq; try discriminate Heq;
        clear Heq; cbn in *; env.destroy ts; cbn; destruct_pmp_entries; auto.
    Qed.

  End RiscvPmpIrisPredicates.

  Section RiscVPmpIrisInstanceProofs.
    Context `{sr : sailRegGS2 Σ} `{igs : invGS Σ} `{mG : memGS2 Σ}.

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
      pose proof (in_allAddrs_split base width Hrep) as [l1 [l2 Hall]].
      unfold all_addrs in Hall. rewrite Hall.
      rewrite !big_sepL_app.
      iIntros "(Hlow & Hia & Hhigh)".
      iSplitL "Hia".
      - iApply (big_sepL_mono with "Hia"). iIntros (? ? ?) "Hyp".
        iApply "Hyp". iPureIntro.
        eexists; eapply pmp_seqBv_restrict; eauto.
      - iIntros "Hia". iFrame.
        iDestruct (big_sepL_mono with "Hia") as "Hia"; last iFrame.
        now iIntros.
    Qed.

    Lemma ptstomem_bv_app :
      forall {n} (a : Addr) (b : bv byte) (bs : bv (n * byte)),
        @interp_ptstomem _ _ (S n)%nat a (bv.app b bs)
        ⊣⊢
        (interp_ptsto a b ∗ interp_ptstomem (bv.one + a) bs).
    Proof.
      intros.
      unfold interp_ptstomem, interp_ptsto, interp_ptsto_one.
      rewrite ?ptstomem_bv_app.
      (* rewrite ?Right.ptstomem_bv_app. *)
      rewrite <- ?bi.sep_assoc.
    (*   iSplit; iIntros "($ & $ & $ & $)". *)
    (* Qed. *)
    Admitted.

    Lemma interp_ptstomem_big_sepS (bytes : nat) (paddr : Addr):
      (∃ (w : bv (bytes * byte)), interp_ptstomem paddr w) ⊣⊢
        ptstoSthL (bv.seqBv paddr (N.of_nat bytes)).
    Proof.
      generalize dependent paddr.
      iInduction bytes as [|bytes] "IHbytes"; iIntros (paddr).
      - unfold ptstoSthL. unshelve auto. exact bv.zero.
      - rewrite Nat2N.inj_succ bv.seqBv_succ (app_comm_cons []) ptstoSthL_app.
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
      (minAddr ≤ bv.bin base)%N →
      (bv.bin base + N.of_nat width ≤ maxAddr)%N →
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
      rewrite /bv.unsigned bv.bin_add_small !bv.bin_of_N_small; lia. (* TODO: use representability of min/maxAddr here, once they are made properly opaque *)
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

  Include IrisBinaryWP RiscvPmpBase RiscvPmpSignature RiscvPmpProgram
    RiscvPmpSemantics
    RVPCOM RVPBASEl RVPBASEr RVPBASE2.

  Include IrisSignatureRules2 RiscvPmpBase RiscvPmpSignature RiscvPmpProgram
    FL RiscvPmpSemantics
    RVPCOM RVPBASEl RVPBASEr RVPBASE2.

  Include IrisAdequacy2 RiscvPmpBase RiscvPmpSignature RiscvPmpProgram
    FL RiscvPmpSemantics
    RVPCOM RVPBASEl RVPBASEr RVPBASE2 RVPADEQ2.

  Lemma gprs_equiv `{sailGS2 Σ} : ∀ {Σ} (ι : Valuation Σ) (exclude : gset (Reg ty_xlenbits)),
      interp_gprs exclude ⊣⊢
        asn.interpret (asn_regs_ptsto exclude) ι.
  Proof.
    iIntros (? ι exclude).
    unfold interp_gprs, asn_regs_ptsto, asn_and_regs.
    remember (elements (GPRS ∖ exclude)) as l eqn:El.
    assert (Hdup: NoDup l) by (subst; apply NoDup_elements).
    assert (Hl: list_to_set l = GPRS ∖ exclude) by (subst; apply list_to_set_elements_L).
    rewrite <- Hl.
    rewrite big_sepS_list_to_set; last auto.
    clear El Hdup Hl.
    iInduction l as [|gpr gprs] "IH";
      iSplit; iIntros "H"; simpl; auto.
    - iDestruct "H" as "($ & H)".
      now iApply ("IH" with "H").
    - iDestruct "H" as "($ & H)".
      now iApply ("IH" with "H").
  Qed.

  Definition WP2_loop `{sailGS2 Σ} : iProp Σ :=
    semWP2 env.nil env.nil (FunDef loop) (FunDef loop) (λ v1 δ1 v2 δ2, ⌜v1 = v2⌝ ∗ ⌜δ1 = δ2⌝)%I.
End RiscvPmpIrisInstance2.
