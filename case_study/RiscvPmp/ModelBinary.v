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
     Iris.BinaryWp
     Program
     Semantics
     Sep.Hoare
     Sep.Logic
     Specification
     RiscvPmp.PmpCheck
     RiscvPmp.Machine
     RiscvPmp.Contracts
     RiscvPmp.Model
     RiscvPmp.IrisModelBinary
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
Import RiscvPmpIrisInstance2.

Module RiscvPmpModel2.
  Import RiscvPmpSignature.
  Import RiscvPmpSpecification.
  Import RiscvPmpProgram.

  Module RiscvPmpProgramLogic <: ProgramLogicOn RiscvPmpBase RiscvPmpProgram RiscvPmpSignature RiscvPmpSpecification.
    Include ProgramLogicOn RiscvPmpBase RiscvPmpProgram RiscvPmpSignature RiscvPmpSpecification.
  End RiscvPmpProgramLogic.
  Include RiscvPmpProgramLogic.

  Include IrisInstanceWithContracts2 RiscvPmpBase RiscvPmpProgram RiscvPmpSemantics
      RiscvPmpSignature RiscvPmpSpecification RiscvPmpIrisBase2 RiscvPmpIrisInstance2.

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

    Lemma ptstomem_bv_app :
      forall {n} (a : Addr) (b : bv byte) (bs : bv (n * byte)),
        @interp_ptstomem _ _ (S n)%nat a (bv.app b bs)
        ⊣⊢
        (interp_ptsto a b ∗ interp_ptstomem (bv.one + a) bs).
    Proof. intros; cbn [interp_ptstomem]; now rewrite bv.appView_app. Qed.

    Lemma interp_ptstomem_exists_intro (bytes : nat) :
      ⊢ ∀ (paddr : Addr) (w : bv (bytes * byte)),
          interp_ptstomem paddr w -∗
          ∃ (w : bv (bytes * byte)), interp_ptstomem paddr w.
    Proof. auto. Qed.

    Lemma interp_ptstomem_big_sepS (bytes : nat) :
      ⊢ ∀ (paddr : Addr),
          ⌜(bv.bin paddr + N.of_nat bytes < bv.exp2 xlenbits)%N⌝ -∗
      (∃ (w : bv (bytes * byte)), interp_ptstomem paddr w) ∗-∗
        [∗ list] offset ∈ bv.seqBv paddr bytes,
            ∃ w, interp_ptsto offset w.
    Proof.
      iInduction bytes as [|bytes] "IHbytes";
        iIntros (paddr) "%Hrep"; iSplit.
      - auto.
      - iIntros "H". now iExists bv.zero.
      - iIntros "[%w H]".
        rewrite bv.seqBv_succ.
        rewrite big_sepL_cons.
        destruct (bv.appView byte (bytes * byte) w) as [b bs].
        rewrite ptstomem_bv_app.
        iDestruct "H" as "[Hb Hbs]".
        iSplitL "Hb".
        + by iExists b.
        + iApply ("IHbytes" with "[%]").
          rewrite bv.bin_add_small;
            rewrite bv_bin_one; lia.
          now iExists bs.
      - iIntros "H".
        rewrite bv.seqBv_succ; try apply xlenbits_pos.
        rewrite big_sepL_cons.
        iDestruct "H" as "([%b Hb] & Hbs)".
        iAssert (∃ (w : bv (bytes * byte)), interp_ptstomem (bv.one + paddr) w)%I with "[Hbs]" as "[%w H]".
        iApply ("IHbytes" $! (bv.one + paddr) with "[%]").
        rewrite bv.bin_add_small bv_bin_one; lia.
        iApply "Hbs".
        iExists (bv.app b w).
        rewrite ptstomem_bv_app; iFrame.
    Qed.

    Lemma interp_ptstomem_dedup {paddr width} {w : bv (width * byte)}:
      IrisInstance.RiscvPmpIrisInstance.interp_ptstomem (mG := mc_ghGS2_left) paddr w ∗
        IrisInstance.RiscvPmpIrisInstance.interp_ptstomem (mG := mc_ghGS2_right) paddr w ⊣⊢
        interp_ptstomem paddr w.
    Proof.
      revert paddr w. induction width; intros paddr w.
      { now iSplit. }
      change (S width * byte)%nat with (byte + width * byte)%nat in w.
      unfold interp_ptstomem, IrisInstance.RiscvPmpIrisInstance.interp_ptstomem.
      destruct (bv.appView byte (width * byte) w).
      rewrite <-IHwidth.
      iSplit.
      now iIntros "[([$ %] & $) [$ $]]".
      iIntros "[($ & $ & _) [$ $]]".
    Qed.

    Definition sailGS2_sailGS_left `{sailGS2 Σ} : sailGS Σ :=
      SailGS sailGS2_invGS sailRegGS2_sailRegGS_left mc_ghGS2_left.

    Definition sailGS2_sailGS_right `{sailGS2 Σ} : sailGS Σ :=
      SailGS sailGS2_invGS sailRegGS2_sailRegGS_right mc_ghGS2_right.

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
          IrisInstance.RiscvPmpIrisInstance.interp_pmp_entries (H := sailRegGS2_sailRegGS_left) entries ∗
          IrisInstance.RiscvPmpIrisInstance.interp_pmp_entries (H := sailRegGS2_sailRegGS_right) entries.
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
      iIntros "H".
      rewrite <-interp_ptstomem_dedup.
      iDestruct "H" as "[Hmemres1 Hmemres2]".
      rewrite fixpoint_semWp2_eq.
      cbn in *.
      iIntros (? ? ? ?) "(Hregs & ((% & Hmem1 & %Hmap1 & Htrace1) & (% & Hmem2 & %Hmap2 & Htrace2)))".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro.
      iIntros.
      repeat iModIntro.
      eliminate_prim_step Heq.
      iMod "Hclose" as "_".
      iModIntro.
      iDestruct (RiscvPmpModel2.fun_read_ram_works (sg := sailGS2_sailGS_left) Hmap1 with "[$Hmemres1 $Hmem1]") as "%eq_fun_read_ram1".
      iDestruct (RiscvPmpModel2.fun_read_ram_works (sg := sailGS2_sailGS_right) Hmap2 with "[$Hmemres2 $Hmem2]") as "%eq_fun_read_ram2".
      iPoseProof (RiscvPmpModel2.mem_inv_not_modified (sg := sailGS2_sailGS_left) $! Hmap1 with "Hmem1") as "Hmem1".
      iPoseProof (RiscvPmpModel2.mem_inv_not_modified (sg := sailGS2_sailGS_right) $! Hmap2 with "Hmem2") as "Hmem2".
      iExists _, _, _, _.
      iSplitR.
      { iPureIntro. constructor. rewrite Heq. now cbn.  }
      iSpecialize ("Hmem1" with "Htrace1").
      iSpecialize ("Hmem2" with "Htrace2").
      iFrame.
      rewrite semWp2_val.
      iModIntro.
      iExists _.
      rewrite <-interp_ptstomem_dedup, ?eq_fun_read_ram1, ?eq_fun_read_ram2.
      now iFrame.
    Qed.

    Lemma write_ram_sound (bytes : nat) :
      ValidContractForeign (sep_contract_write_ram bytes) (write_ram bytes).
    Proof.
      intros Γ es δ ι Heq. destruct_syminstance ι. cbn.
      iIntros "(%vold & H)".
      rewrite fixpoint_semWp2_eq.
      cbn.
      iIntros (? ? ? ?) "(Hregs & ((% & Hmem1 & %Hmap1 & Htrace1) & (% & Hmem2 & %Hmap2 & Htrace2)))".
      rewrite <-interp_ptstomem_dedup.
      iDestruct "H" as "[Hmemres1 Hmemres2]".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro.
      iIntros.
      repeat iModIntro.
      eliminate_prim_step Heq.
      iMod "Hclose" as "_".
      iMod (RiscvPmpModel2.fun_write_ram_works (sg := sailGS2_sailGS_left) μ1 paddr data Hmap1
                   with "[$Hmemres1 $Hmem1 $Htrace1]") as "[Hmem1 Hmemres1]".
      iMod (RiscvPmpModel2.fun_write_ram_works (sg := sailGS2_sailGS_right) μ2 paddr data Hmap2
                   with "[$Hmemres2 $Hmem2 $Htrace2]") as "[Hmem2 Hmemres2]".
      iModIntro.
      iExists _, _, _, _.
      iSplitR.
      { iPureIntro. constructor. now rewrite Heq. }
      cbn.
      rewrite semWp2_val.
      iFrame "Hregs".
      iSplitL "Hmem1 Hmem2"; first iFrame.
      iModIntro.
      iExists _.
      rewrite <-interp_ptstomem_dedup.
      now iFrame.
    Qed.

    Lemma decode_sound :
      ValidContractForeign sep_contract_decode decode.
    Proof.
      intros Γ es δ ι Heq.
      destruct_syminstance ι.
      iIntros "_".
      rewrite fixpoint_semWp2_eq.
      cbn in *.
      iIntros (? ? ? ?) "[Hregs (Hmem1 & Hmem2)]".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro.
      iIntros.
      repeat iModIntro.
      eliminate_prim_step Heq.
      iMod "Hclose" as "_".
      iModIntro.
      iExists _, _, _, _.
      iSplitR.
      { iPureIntro. constructor. now rewrite Heq. }
      iFrame.
      destruct (pure_decode bv0).
      - rewrite fixpoint_semWp2_eq.
        now iExists _.
      - rewrite semWp2_val.
        now iExists _.
    Qed.

    Lemma vector_subrange_sound {n} (e b : nat)
                                {p : IsTrue (0 <=? b)%nat} {q : IsTrue (b <=? e)%nat} {r : IsTrue (e <? n)%nat} :
      ValidContractForeign (@sep_contract_vector_subrange n e b p q r) (vector_subrange e b).
    Proof.
      intros Γ es δ ι Heq.
      destruct_syminstance ι.
      iIntros "_".
      rewrite fixpoint_semWp2_eq.
      cbn in *.
      iIntros (? ? ? ?) "[Hregs (Hmem1 & Hmem2)]".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro.
      iIntros.
      repeat iModIntro.
      eliminate_prim_step Heq.
      iMod "Hclose" as "_".
      iModIntro.
      iExists _, _, _, _.
      iSplitR.
      iPureIntro; constructor; now rewrite Heq.
      iFrame.
      destruct (fun_vector_subrange bv0 e b) eqn:Ev.
      rewrite semWp2_val.
      now iExists _.
    Qed.

    Lemma foreignSem : ForeignSem.
    Proof.
      intros Δ τ f; destruct f;
        eauto using read_ram_sound, write_ram_sound, decode_sound, vector_subrange_sound.
    Admitted.
  End ForeignProofs.

  Section LemProofs.
    Context `{sg : sailGS2 Σ}.

    Lemma gprs_equiv :
      interp_gprs ⊣⊢
      asn.interpret asn_regs_ptsto env.nil.
    Proof.
      unfold interp_gprs, reg_file.
      rewrite big_sepS_list_to_set; [|apply bv.finite.nodup_enum].
      cbn. iSplit.
      - iIntros "(_ & H)"; repeat iDestruct "H" as "($ & H)".
      - iIntros "H"; iSplitR; first by iExists bv.zero.
        repeat iDestruct "H" as "($ & H)"; iFrame.
    Qed.

    Lemma open_gprs_sound :
      ValidLemma RiscvPmpSpecification.lemma_open_gprs.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      rewrite gprs_equiv. cbn. iIntros. iFrame.
    Qed.

    Lemma close_gprs_sound :
      ValidLemma RiscvPmpSpecification.lemma_close_gprs.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      rewrite gprs_equiv. cbn. iIntros. iFrame.
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
      (minAddr <= bv.unsigned addr)%Z <-> bv.of_nat minAddr <=ᵘ addr.
    Proof.
      unfold bv.ule, bv.unsigned.
      intros.
      split.
      - rewrite <- nat_N_Z.
        intros H.
        rewrite bv.bin_of_nat_small.
        now apply N2Z.inj_le.
        apply minAddr_rep.
      - rewrite <- nat_N_Z.
        intros H.
        rewrite bv.bin_of_nat_small in H.
        now apply N2Z.inj_le.
        apply minAddr_rep.
    Qed.

    Lemma maxAddr_le_ule : forall (addr : Addr) (bytes : nat),
        (bv.bin addr + N.of_nat bytes < bv.exp2 xlenbits)%N ->
         (bv.unsigned addr + bytes <= maxAddr)%Z -> addr + bv.of_nat bytes <=ᵘ bv.of_nat maxAddr.
    Proof.
      unfold bv.ule, bv.unsigned.
      rewrite <- nat_N_Z.
      intros addr bytes Hrep H.
      rewrite bv.bin_of_nat_small; last apply maxAddr_rep.
      rewrite bv.bin_add_small.
      rewrite bv.bin_of_nat_small.
      pose maxAddr_rep.
      lia.
      lia.
      rewrite bv.bin_of_nat_small; lia.
    Qed.

    Lemma in_liveAddrs : forall (addr : Addr),
        (bv.of_nat minAddr <=ᵘ addr) ->
        (addr <ᵘ bv.of_nat maxAddr) ->
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
        (bv.bin addr - @bv.bin xlenbits (bv.of_nat minAddr) < bv.exp2 xlenbits)%N ->
        (bv.of_nat minAddr <=ᵘ addr) ->
        (addr + (bv.of_nat bytes) <=ᵘ bv.of_nat maxAddr) ->
        exists l1 l2, liveAddrs = l1 ++ (bv.seqBv addr bytes  ++ l2).
    Proof.
    (* TODO: more efficient proof? *)
      unfold maxAddr.
      intros addr bytes bytesfit addrbytesFits addrDiffFits Hmin Hmax.
      unfold bv.ule, bv.ule in *.
      unfold liveAddrs.
      exists (bv.seqBv (bv.of_nat minAddr) (N.to_nat (bv.bin addr - @bv.bin xlenbits (bv.of_nat minAddr)))%N).
      exists (bv.seqBv (bv.add addr (bv.of_nat bytes)) (N.to_nat (@bv.bin xlenbits (bv.of_nat minAddr + bv.of_nat lenAddr) - bv.bin (addr + bv.of_nat bytes)))).
      rewrite <-(bv.seqBv_app addr).
      replace addr with (@bv.of_nat xlenbits minAddr + bv.of_nat (N.to_nat (bv.bin addr - @bv.bin xlenbits (bv.of_nat minAddr)))) at 2.
      rewrite <-bv.seqBv_app; try lia.
      f_equal.
      - unfold bv.ule, bv.ult in *.
        apply N_of_nat_inj.
        apply N2Z.inj.
        rewrite ?bv.bin_add_small ?Nat2N.inj_add ?N2Nat.id ?N2Z.inj_add ?N2Z.inj_sub ?bv.bin_of_nat_small;
        auto using lenAddr_rep.
        + rewrite (N2Z.inj_add (bv.bin addr)).
          now Lia.lia.
        + now rewrite ?bv.bin_add_small bv.bin_of_nat_small in Hmax.
      - unfold bv.of_nat.
        rewrite N2Nat.id.
        apply bv.unsigned_inj.
        unfold bv.unsigned.
        rewrite bv.bin_add_small.
        + rewrite N2Z.inj_add.
          rewrite bv.bin_of_N_small; try assumption.
          rewrite bv.bin_of_N_small.
          rewrite N2Z.inj_sub.
          lia.
          now rewrite bv.bin_of_nat_small in Hmin.
          now rewrite bv.bin_of_nat_small in addrDiffFits.
          now simpl.
        + replace (@bv.bin xlenbits (bv.of_nat minAddr) + _)%N with (bv.bin addr); try Lia.lia.
          apply N2Z.inj.
          rewrite N2Z.inj_add.
          rewrite bv.bin_of_N_small; try assumption.
          rewrite bv.bin_of_N_small.
          rewrite N2Z.inj_sub.
          lia.
          now rewrite bv.bin_of_nat_small in Hmin.
          now rewrite bv.bin_of_nat_small in addrDiffFits.
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
            ⊢ (([∗ list] offset ∈ bv.seqBv paddr bytes,
               ⌜∃ p0, Pmp_access offset%bv
                        (bv.of_nat 1) entries p p0⌝ -∗
                        ∃ w : Byte, interp_ptsto offset w)
              ∗-∗
              (⌜∃ p0, Pmp_access paddr (bv.of_nat bytes) entries p p0⌝ -∗
                        [∗ list] offset ∈ bv.seqBv paddr bytes,
                          ∃ w : Byte, interp_ptsto offset w))%I.
    Proof.
      pose proof xlenbits_pos.
      iInduction bytes as [|bytes] "IHbytes"; iIntros (paddr pmp p p0 Hpmp Hrep Hbytes) "".
      now iSimpl.
      iSplit; iIntros "H".
      - iIntros "[%acc %Haccess]".
        simpl.
        rewrite bv.seqBv_succ; try lia.
        rewrite big_sepL_cons.
        iDestruct "H" as "[Hb Hbs]".
        iSplitL "Hb".
        iApply ("Hb" with "[%]").
        exists acc.
        assert (Htmp: (N.of_nat 1 < bv.exp2 xlenbits)%N) by lia.
        rewrite <- (@bv.bin_of_nat_small _ _ Hbytes) in Hrep.
        refine (IrisInstance.RiscvPmpIrisInstance.pmp_access_reduced_width Hrep (bv.ult_nat_S_zero Htmp) (bv.ule_nat_one_S Htmp Hbytes) Haccess).
        destruct bytes; first by simpl. (* we need to know a bit more about bytes to finish this case *)
        iSimpl in "Hbs".
        apply IrisInstance.RiscvPmpIrisInstance.pmp_access_addr_S_width_pred in Haccess; try lia.
        rewrite bv.add_comm in Haccess.
        iApply ("IHbytes" $! (bv.one + paddr) pmp p acc Haccess with "[%] [%] Hbs"); try lia.
        rewrite bv.bin_add_small ?bv_bin_one; lia.
        now iExists acc.
        rewrite bv.bin_of_nat_small; lia.
      - iSpecialize ("H" $! (ex_intro _ _ Hpmp)).
        rewrite bv.seqBv_succ; try lia.
        iDestruct "H" as "[Hw H]"; fold seq.
        simpl.
        iSplitL "Hw"; auto.
        destruct bytes; first now simpl.
        apply IrisInstance.RiscvPmpIrisInstance.pmp_access_addr_S_width_pred in Hpmp; auto.
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
