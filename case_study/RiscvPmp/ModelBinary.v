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
     Program.Tactics
     Lists.List.
From Katamaran Require Import
     Bitvector
     Environment
     Iris.BinaryInstance
     Program
     Semantics
     Sep.Hoare
     Specification
     RiscvPmp.PmpCheck
     RiscvPmp.Machine
     RiscvPmp.Contracts
     RiscvPmp.Model
     RiscvPmp.IrisModelBinary
     RiscvPmp.IrisInstance
     RiscvPmp.IrisInstanceBinary
     RiscvPmp.Sig.
From Equations Require Import
     Equations.

From iris.base_logic Require lib.gen_heap lib.iprop.
From iris.base_logic Require Export invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac.
From iris.program_logic Require Import weakestpre adequacy.
From iris.proofmode Require Import string_ident tactics.

Set Implicit Arguments.
Import ListNotations.
Import bv.notations.

Import RiscvPmpProgram.
Import RiscvPmpSignature.
Import RiscvPmpIrisInstancePredicates2.

Ltac destruct_syminstance ι :=
  repeat
    match type of ι with
    | Env _ (ctx.snoc _ (MkB ?s _)) =>
        string_to_ident_cps s
          ltac:(fun id =>
                  let fr := fresh id in
                  destruct (env.view ι) as [ι fr];
                  destruct_syminstance ι)
    | Env _ ctx.nil => destruct (env.view ι)
    | _ => idtac
    end.

Import RiscvPmpIrisBase2.

Module RiscvPmpModel2.
  Module Import RiscvPmpIrisInstance2 := RiscvPmpIrisInstance2 DefaultFailLogic.
  Import RiscvPmpSignature.
  Import RiscvPmpSpecification.
  Import RiscvPmpProgram.

  Module RiscvPmpProgramLogic <: ProgramLogicOn RiscvPmpBase RiscvPmpSignature RiscvPmpProgram DefaultFailLogic RiscvPmpSpecification.
    Include ProgramLogicOn RiscvPmpBase RiscvPmpSignature RiscvPmpProgram DefaultFailLogic RiscvPmpSpecification.
  End RiscvPmpProgramLogic.
  Include RiscvPmpProgramLogic.

  Include IrisInstanceWithContracts2 RiscvPmpBase RiscvPmpSignature RiscvPmpProgram DefaultFailLogic
    RiscvPmpSemantics RiscvPmpSpecification RiscvPmpIrisBase2  RiscvPmpIrisAdeqParams2 RiscvPmpIrisInstance2.

  Section ForeignProofs.
    Context `{sg : sailGS2 Σ}.

    Ltac eliminate_prim_step Heq :=
      let f := fresh "f" in
      match goal with
      | H: RiscvPmpSemantics.Step _ _ _ _ _ _ _ _ |- _ =>
          dependent elimination H as [RiscvPmpSemantics.st_foreign _ _ f];
          rewrite Heq in f;
          cbn in f;
          dependent elimination f;
          cbn
      end.

    Lemma bv_bin_one : bv.bin (@bv.one xlenbits) = 1%N.
    Proof. apply bv.bin_one, xlenbits_pos. Qed.

    Lemma interp_ptstomem_exists_intro (bytes : nat) :
      ⊢ ∀ (paddr : Addr) (w : bv (bytes * byte)),
          interp_ptstomem paddr w -∗
          ∃ (w : bv (bytes * byte)), interp_ptstomem paddr w.
    Proof. auto. Qed.

    Definition sailGS2_sailGS_left `{sailGS2 Σ} : sailGS Σ :=
      SailGS sailGS2_invGS sailRegGS2_sailRegGS_left memGS2_memGS_left.

    Definition sailGS2_sailGS_right `{sailGS2 Σ} : sailGS Σ :=
      SailGS sailGS2_invGS sailRegGS2_sailRegGS_right memGS2_memGS_right.

    Lemma pmp_entries_ptsto : ∀ (entries : list PmpEntryCfg),
        ⊢ interp_pmp_entries entries -∗
          ∃ (cfg0 : Pmpcfg_ent) (addr0 : Addr) (cfg1 : Pmpcfg_ent) (addr1 : Addr),
            ⌜entries = [(cfg0, addr0); (cfg1, addr1)]⌝ ∗
            reg_pointsTo21 pmp0cfg cfg0 ∗ reg_pointsTo21 pmpaddr0 addr0 ∗
            reg_pointsTo21 pmp1cfg cfg1 ∗ reg_pointsTo21 pmpaddr1 addr1.
    Proof.
      iIntros (entries) "H".
      destruct entries as [|[cfg0 addr0] [|[cfg1 addr1] [|]]] eqn:?; try done.
      repeat iExists _.
      now iFrame.
    Qed.

    Lemma interp_pmpentries_dedup : ∀ (entries : list PmpEntryCfg),
        interp_pmp_entries entries ⊣⊢
          RiscvPmpIrisInstancePredicates.interp_pmp_entries (H := sailRegGS2_sailRegGS_left) entries ∗
          RiscvPmpIrisInstancePredicates.interp_pmp_entries (H := sailRegGS2_sailRegGS_right) entries.
    Proof.
      iIntros (entries).
      destruct entries as [|[cfg0 addr0] [|[cfg1 addr1] [|]]] eqn:?; cbn;
      try (iSplit; iIntros; now destruct H).
      iSplit.
      - iIntros "([$ $] & [$ $] & [$ $] & [$ $])".
      - iIntros "(($ & $ & $ & $) & ($ & $ & $ & $))".
    Qed.

    Lemma read_ram_sound (bytes : nat) :
      ValidContractForeign (sep_contract_read_ram bytes) (read_ram bytes).
    Proof.
      intros Γ es δ ι Heq. cbn. destruct_syminstance ι. cbn.
      iIntros "(HmemL & HmemR)". cbn in *. iApply semWP2_foreign.
      iIntros (? ?) "(Hreg & %memmapL & Hmem & %HmapL & Htr)".
      iPoseProof (@RiscvPmpModel2.fun_read_ram_works _ sailGS2_sailGS_left _ _ _ _ _ HmapL with "[$HmemL $Hmem $Htr]") as "%eq_fun_read_ram_l".
      iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
      iIntros (res1 ? ? Hf1). rewrite Heq in Hf1. cbn in Hf1.
      inversion Hf1; subst. iIntros "!> !> !>". iMod "Hclose" as "_". iModIntro.
      iFrame "Hreg Hmem Htr". iSplitR; first by iPureIntro.
      iIntros (? ?) "(Hreg & %memmapR & Hmem & %HmapR & Htr)".
      iPoseProof (@RiscvPmpModel2.fun_read_ram_works _ sailGS2_sailGS_right _ _ _ _ _ HmapR with "[$HmemR $Hmem $Htr]") as "%eq_fun_read_ram_r".
      iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
      iIntros (res2 ? ? Hf2). rewrite Heq in Hf2. cbn in Hf2.
      inversion Hf2; subst. iMod "Hclose" as "_". iModIntro.
      iFrame "Hreg Hmem Htr". iSplitR; first by iPureIntro.
      iApply semWP2_val_1. rewrite eq_fun_read_ram_r. now iFrame "HmemL HmemR".
    Qed.

    Lemma write_ram_sound (bytes : nat) :
      ValidContractForeign (sep_contract_write_ram bytes) (write_ram bytes).
    Proof.
      intros Γ es δ ι Heq. cbn. destruct_syminstance ι. cbn.
      iIntros "(%v & HmemL & HmemR)". cbn in *. iApply semWP2_foreign.
      iIntros (? ?) "(Hreg & %memmapL & Hmem & %HmapL & Htr)".
      iMod (@RiscvPmpModel2.fun_write_ram_works _ sailGS2_sailGS_left _ _ _ data _ v HmapL with "[$HmemL $Hmem $Htr]") as "(Hmem & HmemL)".
      iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
      iIntros (res1 ? ? Hf1). rewrite Heq in Hf1. cbn in Hf1.
      inversion Hf1; subst. iIntros "!> !> !>". iMod "Hclose" as "_". iModIntro.
      iFrame "Hreg Hmem".
      iIntros (? ?) "(Hreg & %memmapR & Hmem & %HmapR & Htr)".
      iMod (@RiscvPmpModel2.fun_write_ram_works _ sailGS2_sailGS_right _ _ _ data _ v HmapR with "[$HmemR $Hmem $Htr]") as "(Hmem & HmemR)".
      iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
      iIntros (res2 ? ? Hf2). rewrite Heq in Hf2. cbn in Hf2.
      inversion Hf2; subst. iMod "Hclose" as "_". iModIntro. iFrame "Hreg Hmem".
      iApply semWP2_val_1. now iFrame "HmemL HmemR".
    Qed.

    Lemma decode_sound :
      ValidContractForeign sep_contract_decode decode.
    Proof.
      intros Γ es δ ι Heq. cbn. destruct_syminstance ι. cbn.
      iIntros "_". cbn in *. iApply semWP2_foreign. iIntros (? ?) "Hres1".
      iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
      iIntros (res1 ? ? Hf1). rewrite Heq in Hf1. cbn in Hf1.
      inversion Hf1; subst. iFrame "Hres1". iIntros "!> !> !>".
      iMod "Hclose" as "_". iModIntro.
      iIntros (? ?) "Hres2". iMod (fupd_mask_subseteq empty) as "Hclose"; auto.
      iModIntro. iIntros (res2 ? ? Hf2). rewrite Heq in Hf2. cbn in Hf2.
      inversion Hf2; subst. iFrame "Hres2". iMod "Hclose" as "_". iModIntro.
      destruct (pure_decode _).
      - now iApply semWP2_fail.
      - now iApply semWP2_val_1.
    Qed.

    Lemma mmio_read_sound (bytes : nat) :
     ValidContractForeign (sep_contract_mmio_read bytes) (mmio_read bytes).
    Proof.
      intros Γ es δ ι Heq. destruct_syminstance ι. cbn.
      now iIntros "[%HFalse _]".
    Qed.

    Lemma mmio_write_sound `(H: restrict_bytes bytes) :
     ValidContractForeign (sep_contract_mmio_write H) (mmio_write H).
    Proof.
      intros Γ es δ ι Heq. destruct_syminstance ι. cbn.
      now iIntros "[%HFalse _]".
    Qed.

    (* NOTE: duplicate of the same lemma in the unary iris instance (IrisInstance.v). *)
    Lemma interp_addr_access_app base width width':
      interp_addr_access liveAddrs mmioAddrs base (width + width') ⊣⊢
      interp_addr_access liveAddrs mmioAddrs base width ∗ interp_addr_access liveAddrs mmioAddrs (base + bv.of_nat width) width'.
    Proof.
      unfold interp_addr_access.
      by rewrite Nat2N.inj_add bv.seqBv_app big_sepL_app.
    Qed.

    (* NOTE: duplicate of the same lemma in the unary iris instance (IrisInstance.v). *)
    Lemma interp_addr_access_cons base width:
      interp_addr_access liveAddrs mmioAddrs base (S width) ⊣⊢
      interp_addr_access_byte liveAddrs mmioAddrs base ∗ interp_addr_access liveAddrs mmioAddrs (base + bv.of_nat 1) width.
    Proof. rewrite <-Nat.add_1_l.
           rewrite interp_addr_access_app.
           unfold interp_addr_access, interp_addr_access_byte.
           by rewrite bv.seqBv_one big_sepL_singleton.
    Qed.

    (* NOTE: duplicate of the same lemma in the unary iris instance (IrisInstance.v). *)
    Lemma interp_pmp_within_mmio_spec {entries m p} (paddr : Addr) bytes :
      (bv.bin paddr + N.of_nat bytes < bv.exp2 xlenbits)%N ->
      Pmp_access paddr (bv.of_nat bytes) entries m p →
      interp_pmp_addr_access liveAddrs mmioAddrs entries m -∗
      ⌜bool_decide (withinMMIO paddr bytes) = false%nat⌝.
    Proof.
      iIntros (Hrep Hpmp) "Hint".
      destruct bytes as [|bytes]. (* No induction needed: disproving one location suffices. *)
      - cbn - [xlenbits] in *. rewrite bool_decide_eq_false. iPureIntro. by intro HFalse.
      - rewrite interp_pmp_addr_inj_extr; eauto.
        iDestruct "Hint" as "[Hint _]".
        iDestruct (interp_addr_access_cons with "Hint") as "[Hfirst _]".
        unfold interp_addr_access_byte.
        case_decide; auto.
        iPureIntro.
        rewrite bool_decide_eq_false /withinMMIO.
        destruct bytes; first congruence.
        rewrite !not_and_l. left; congruence.
    Qed.

    (* NOTE: duplicate of the same lemma in the unary model (Model.v). *)
    Lemma interp_pmp_fun_within_mmio_spec {entries m p} (paddr : Addr) bytes:
      Pmp_access paddr (bv.of_nat bytes) entries m p →
      interp_pmp_addr_access liveAddrs mmioAddrs entries m -∗
      ⌜fun_within_mmio bytes paddr = false%nat⌝.
    Proof.
      iIntros (Hpmp) "Hint". rewrite /fun_within_mmio.
      rewrite bool_decide_and andb_false_iff.
      destruct (decide (bv.bin paddr + N.of_nat bytes < bv.exp2 xlenbits)%N) as [Hlt | Hnlt].
      - iDestruct (interp_pmp_within_mmio_spec with "Hint") as "->"; eauto.
      - iPureIntro. right.
        by rewrite bool_decide_false.
    Qed.

    Lemma within_mmio_sound `(H: restrict_bytes bytes) :
     ValidContractForeign (@sep_contract_within_mmio bytes H) (within_mmio H).
    Proof.
      intros Γ es δ ι Heq. destruct_syminstance ι. cbn in *.
      iIntros "(Hcurp & Hpmp & Hpmpa & [%acc [%Hpmp _]])".
      iApply semWP2_foreign. iIntros (? ?) "(Hregs & % & Hmem & %HmapL & Htr)".
      iPoseProof (interp_pmp_fun_within_mmio_spec with "Hpmpa") as "%HnotmmioL"; first eauto.
      iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
      iIntros (res1 ? ? Hf1). rewrite Heq in Hf1. cbn in Hf1.
      inversion Hf1; subst. iFrame "Hregs Hmem Htr". iIntros "!> !> !>".
      iMod "Hclose" as "_". iModIntro.
      iSplitR; first auto. iIntros (? ?) "(Hregs & % & Hmem & %HmapR & Htr)".
      iPoseProof (interp_pmp_fun_within_mmio_spec with "Hpmpa") as "%HnotmmioR"; first eauto.
      iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
      iIntros (res2 ? ? Hf2). rewrite Heq in Hf2. cbn in Hf2.
      inversion Hf2; subst. iFrame "Hregs Hmem Htr". iMod "Hclose" as "_".
      iModIntro. iSplitR; auto. iApply semWP2_val_1.
      iFrame "Hpmp Hpmpa Hcurp". now iPureIntro.
    Qed.

    Lemma foreignSem : ForeignSem.
    Proof.
      intros Δ τ f; destruct f;
        eauto using read_ram_sound, write_ram_sound, decode_sound,
                    mmio_read_sound, mmio_write_sound, within_mmio_sound.
    Qed.
  End ForeignProofs.

  Section LemProofs.
    Context `{sg : sailGS2 Σ}.

    Import IrisInstance.

    Lemma interp_gprs_split :
      interp_gprs ⊢
        @RiscvPmpIrisInstancePredicates.interp_gprs _ sailRegGS2_sailRegGS_left
        ∗ @RiscvPmpIrisInstancePredicates.interp_gprs _ sailRegGS2_sailRegGS_right.
    Proof.
      unfold interp_gprs, RiscvPmpIrisInstancePredicates.interp_gprs.
      rewrite ?big_sepS_elements.
      remember (elements RiscvPmpIrisInstancePredicates.reg_file) as l.
      replace (elements RiscvPmpIrisInstancePredicates.reg_file) with l.
      clear Heql.
      iIntros "H".
      iInduction l as [|]; simpl; try done.
      iDestruct "H" as "((%v & Hptsto) & H)".
      iDestruct ("IHl" with "H") as "($ & $)". iClear "IHl".
      unfold interp_ptsreg, RiscvPmpIrisInstancePredicates.interp_ptsreg.
      destruct (reg_convert a); try done.
      iDestruct "Hptsto" as "($ & $)".
    Qed.

    Lemma open_gprs_sound :
      ValidLemma RiscvPmpSpecification.lemma_open_gprs.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      rewrite (gprs_equiv env.nil). cbn. iIntros. iFrame.
    Qed.

    Lemma close_gprs_sound :
      ValidLemma RiscvPmpSpecification.lemma_close_gprs.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      rewrite (gprs_equiv env.nil). cbn. iIntros. iFrame.
    Qed.

    Lemma open_ptsto_instr_sound :
      ValidLemma RiscvPmpSpecification.lemma_open_ptsto_instr.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      now iIntros.
    Qed.

    Lemma close_ptsto_instr_sound :
      ValidLemma RiscvPmpSpecification.lemma_close_ptsto_instr.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      now iIntros.
    Qed.

    Lemma open_pmp_entries_sound :
      ValidLemma RiscvPmpSpecification.lemma_open_pmp_entries.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      iIntros "H".
      iPoseProof (pmp_entries_ptsto with "H") as "(% & % & % & % & -> & Hpmp0cfg & Hpmpaddr0 & Hpmp1cfg & Hpmpaddr1)".
      repeat iExists _.
      now iFrame "Hpmp0cfg Hpmp1cfg Hpmpaddr0 Hpmpaddr1".
    Qed.

    Lemma close_pmp_entries_sound :
      ValidLemma RiscvPmpSpecification.lemma_close_pmp_entries.
    Proof. intros ι; destruct_syminstance ι; cbn; auto. Qed.

    Lemma minAddr_le_ule : forall (addr : Addr),
      (minAddr <= bv.bin addr)%N <-> bv.of_N minAddr <=ᵘ addr.
    Proof.
      unfold bv.ule, bv.unsigned.
      intros.
      split.
      - intros H.
        now rewrite bv.bin_of_N_small.
      - intros H.
        now rewrite bv.bin_of_N_small in H.
    Qed.

    Lemma maxAddr_le_ule : forall (addr : Addr) (bytes : nat),
        (bv.bin addr + N.of_nat bytes < bv.exp2 xlenbits)%N ->
         (bv.bin addr + N.of_nat bytes <= maxAddr)%N -> addr + bv.of_nat bytes <=ᵘ bv.of_N maxAddr.
    Proof.
      unfold bv.ule, bv.unsigned.
      intros addr bytes Hrep H.
      rewrite bv.bin_of_N_small; last apply maxAddr_rep.
      rewrite bv.bin_add_small.
      rewrite bv.bin_of_nat_small.
      pose maxAddr_rep.
      lia.
      lia.
      rewrite bv.bin_of_nat_small; lia.
    Qed.

    Lemma in_liveAddrs : forall (addr : Addr),
        (bv.of_N minAddr <=ᵘ addr) ->
        (addr <ᵘ bv.of_N maxAddr) ->
        addr ∈ liveAddrs.
    Proof.
      unfold liveAddrs, maxAddr.
      intros.
      apply bv.in_seqBv;
        eauto using maxAddr_rep.
    Qed.

    Opaque minAddr.
    Opaque lenAddr.
    Opaque xlenbits.

    Lemma in_liveAddrs_split : forall (addr : Addr) (bytes : nat),
        (N.of_nat bytes < bv.exp2 xlenbits)%N ->
        (bv.bin addr + N.of_nat bytes < bv.exp2 xlenbits)%N ->
        (bv.bin addr - @bv.bin xlenbits (bv.of_N minAddr) < bv.exp2 xlenbits)%N ->
        (bv.of_N minAddr <=ᵘ addr) ->
        (addr + (bv.of_nat bytes) <=ᵘ bv.of_N maxAddr) ->
        exists l1 l2, liveAddrs = l1 ++ (bv.seqBv addr (N.of_nat bytes)  ++ l2).
    Proof.
    (* TODO: more efficient proof? *)
      unfold maxAddr.
      intros addr bytes bytesfit addrbytesFits addrDiffFits Hmin Hmax.
      unfold bv.ule, bv.ule in *.
      unfold liveAddrs.
      exists (bv.seqBv (bv.of_N minAddr) (bv.bin addr - @bv.bin xlenbits (bv.of_N minAddr))%N).
      exists (bv.seqBv (bv.add addr (bv.of_nat bytes)) (@bv.bin xlenbits (bv.of_N minAddr + bv.of_N lenAddr) - bv.bin (addr + bv.of_nat bytes))).
      rewrite <-(bv.seqBv_app addr).
      replace addr with (@bv.of_N xlenbits minAddr + bv.of_N (bv.bin addr - @bv.bin xlenbits (bv.of_N minAddr))) at 2.
      rewrite <-bv.seqBv_app; try lia.
      f_equal.
      - unfold bv.ule, bv.ult in *.
        apply N2Z.inj.
        rewrite ?bv.bin_add_small ?Nat2N.inj_add ?N2Nat.id ?N2Z.inj_add ?N2Z.inj_sub ?bv.bin_of_nat_small ?bv.bin_of_N_small;
        auto using lenAddr_rep.
        + rewrite (N2Z.inj_add (bv.bin addr)).
          now Lia.lia.
        + now rewrite ?bv.bin_add_small bv.bin_of_nat_small in Hmax.
      - unfold bv.of_nat.
        apply bv.unsigned_inj.
        unfold bv.unsigned.
        rewrite bv.bin_add_small.
        + rewrite N2Z.inj_add.
          rewrite bv.bin_of_N_small; try assumption.
          rewrite bv.bin_of_N_small.
          rewrite N2Z.inj_sub.
          lia.
          now rewrite bv.bin_of_N_small in Hmin.
          now rewrite bv.bin_of_N_small in addrDiffFits.
          now simpl.
        + replace (@bv.bin xlenbits (bv.of_N minAddr) + _)%N with (bv.bin addr); try Lia.lia.
          apply N2Z.inj.
          rewrite N2Z.inj_add.
          rewrite bv.bin_of_N_small; last done.
          rewrite bv.bin_of_N_small; last done.
          rewrite N2Z.inj_sub; last done.
          lia.
    Qed.

    Lemma N_of_nat_lt_S : forall w n,
        (N.of_nat (S n) < bv.exp2 w)%N ->
        (N.of_nat n < bv.exp2 w)%N.
    Proof. lia. Qed.

    (* TODO: better name! *)
    Lemma bv_ule_base : forall {n} (base a b max : bv n),
        (bv.bin base + bv.bin a < bv.exp2 n)%N ->
        b <=ᵘ a ->
        base + a <=ᵘ max ->
        base + b <=ᵘ max.
    Proof.
      intros n base a b max Hn Hba.
      apply bv.ule_trans with (y := base + a).
      unfold bv.ule in *.
      rewrite ?bv.bin_add_small; lia.
    Qed.

    Lemma big_sepL_pure_impl (bytes : nat) :
        ∀ (paddr : Addr)
            (entries : list PmpEntryCfg) (p : Privilege) p0,
            (Pmp_access paddr (bv.of_nat bytes) entries p p0) ->
            (bv.bin paddr + N.of_nat bytes < bv.exp2 xlenbits)%N ->
            (N.of_nat bytes < bv.exp2 xlenbits)%N ->
            ⊢ (([∗ list] offset ∈ bv.seqBv paddr (N.of_nat bytes),
               ⌜∃ p0, Pmp_access offset%bv
                        (bv.of_nat 1) entries p p0⌝ -∗
                        ∃ w : Byte, interp_ptsto offset w)
              ∗-∗
              (⌜∃ p0, Pmp_access paddr (bv.of_nat bytes) entries p p0⌝ -∗
                        [∗ list] offset ∈ bv.seqBv paddr (N.of_nat bytes),
                          ∃ w : Byte, interp_ptsto offset w))%I.
    Proof.
      pose proof xlenbits_pos.
      iInduction bytes as [|bytes] "IHbytes"; iIntros (paddr pmp p p0 Hpmp Hrep Hbytes) "".
      { now iSimpl; iSplit; iIntros. }
      iSplit; iIntros "H".
      - iIntros "[%acc %Haccess]".
        simpl.
        rewrite Nat2N.inj_succ bv.seqBv_succ; try lia.
        rewrite big_sepL_cons.
        iDestruct "H" as "[Hb Hbs]".
        iSplitL "Hb".
        iApply ("Hb" with "[%]").
        exists acc.
        assert (Htmp: (N.of_nat 1 < bv.exp2 xlenbits)%N) by lia.
        rewrite <- (@bv.bin_of_nat_small _ _ Hbytes) in Hrep.
        refine (RiscvPmpIrisInstance.pmp_access_reduced_width Hrep (bv.ult_nat_S_zero Htmp) (bv.ule_nat_one_S Htmp Hbytes) Haccess).
        destruct bytes; first by simpl. (* we need to know a bit more about bytes to finish this case *)
        iSimpl in "Hbs".
        apply RiscvPmpIrisInstance.pmp_access_addr_S_width_pred in Haccess; try lia.
        rewrite bv.add_comm in Haccess.
        iApply ("IHbytes" $! (bv.one + paddr) pmp p acc Haccess with "[%] [%] Hbs"); try lia.
        rewrite bv.bin_add_small ?bv_bin_one; lia.
        now iExists acc.
        rewrite bv.bin_of_nat_small; lia.
      - iSpecialize ("H" $! (ex_intro _ _ Hpmp)).
        rewrite Nat2N.inj_succ bv.seqBv_succ; try lia.
        iDestruct "H" as "[Hw H]"; fold seq.
        simpl.
        iSplitL "Hw"; auto.
        destruct bytes; first now simpl.
        apply RiscvPmpIrisInstance.pmp_access_addr_S_width_pred in Hpmp; auto.
        rewrite bv.add_comm in Hpmp.
        iApply ("IHbytes" $! (bv.one + paddr) pmp p p0 Hpmp with "[%] [%]"); auto; try lia.
        rewrite bv.bin_add_small bv_bin_one; lia.
        rewrite bv.bin_of_nat_small; try lia.
    Qed.

    Lemma extract_pmp_ptsto_sound (bytes : nat) :
      ValidLemma (RiscvPmpSpecification.lemma_extract_pmp_ptsto bytes).
    Proof.
      intros ι; destruct_syminstance ι; cbn - [liveAddrs].
      iIntros "[Hmem [[%Hlemin _] [[%Hlemax _] [%Hpmp _]]]]".
      unfold interp_pmp_addr_access_without,
        interp_pmp_addr_access,
        interp_ptsto,
        MemVal, Word.
      assert (bv.bin paddr + N.of_nat bytes < bv.exp2 xlenbits)%N.
      { eapply N.le_lt_trans; last apply lenAddr_rep.
        unfold bv.unsigned in *. zify; auto. (* TODO: why does lia not solve this? *) }
      iDestruct (interp_pmp_addr_inj_extr with "Hmem") as "[Hmemwo Hia]"; eauto.
      iFrame.
      iApply interp_addr_access_extr; last iFrame; eauto.
      - unfold bv.unsigned in *. zify; auto. (* TODO idem *)
      - unfold bv.unsigned in *. zify; auto. (* TODO idem *)
    Qed.

    Lemma return_pmp_ptsto_sound (bytes : nat) :
      ValidLemma (RiscvPmpSpecification.lemma_return_pmp_ptsto bytes).
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      iIntros "[Hwithout Hptsto]".
      iDestruct (interp_addr_access_inj with "Hptsto") as "Hacc".
      unfold interp_pmp_addr_access_without.
      iApply ("Hwithout" with "Hacc").
    Qed.

    Lemma lemSem : LemmaSem.
    Proof.
      intros Δ [];
        eauto using open_gprs_sound, close_gprs_sound, open_ptsto_instr_sound, close_ptsto_instr_sound, open_pmp_entries_sound,
        close_pmp_entries_sound, extract_pmp_ptsto_sound, return_pmp_ptsto_sound.
    Qed.
  End LemProofs.

End RiscvPmpModel2.
