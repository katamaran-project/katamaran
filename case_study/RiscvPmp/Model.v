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
     Iris.Instance
     Iris.Model
     Program
     Semantics
     Sep.Hoare
     Sep.Logic
     Specification
     RiscvPmp.Machine
     RiscvPmp.Contracts
     RiscvPmp.IrisModel
     RiscvPmp.IrisInstance
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

Import RiscvPmpProgram.
Import RiscvPmpSignature.

Ltac destruct_syminstance ι :=
  repeat
    match type of ι with
    | Env _ (ctx.snoc _ (MkB ?s _)) =>
        let id := string_to_ident s in
        let fr := fresh id in
        destruct (env.snocView ι) as [ι fr];
        destruct_syminstance ι
    | Env _ ctx.nil => destruct (env.nilView ι)
    | _ => idtac
    end.

Import RiscvPmpIrisBase.
Import RiscvPmpIrisInstance.

Module RiscvPmpModel2.
  Import RiscvPmpSignature.
  Import RiscvPmpSpecification.
  Import RiscvPmpProgram.

  Module RiscvPmpProgramLogic <: ProgramLogicOn RiscvPmpBase RiscvPmpProgram RiscvPmpSignature RiscvPmpSpecification.
    Include ProgramLogicOn RiscvPmpBase RiscvPmpProgram RiscvPmpSignature RiscvPmpSpecification.
  End RiscvPmpProgramLogic.
  Include RiscvPmpProgramLogic.

  Include IrisInstanceWithContracts RiscvPmpBase RiscvPmpProgram RiscvPmpSemantics
      RiscvPmpSignature RiscvPmpSpecification RiscvPmpIrisBase RiscvPmpIrisInstance.

  Section ForeignProofs.
    Lemma read_ram_sound `{sg : sailGS Σ, invGS} :
      ValidContractForeign sep_contract_read_ram read_ram.
    Proof.
      intros Γ es δ ι Heq.
      destruct (env.snocView ι) as [ι t].
      destruct (env.snocView ι) as [ι p].
      destruct (env.snocView ι) as [ι entries].
      destruct (env.snocView ι) as [ι w].
      destruct (env.snocView ι) as [ι paddr].
      destruct (env.nilView ι). cbn in Heq |- *.
      iIntros "((%Hperm & _) & Hcp & Hes & (%Hpmp & _) & H)".
      unfold semWP. rewrite wp_unfold.
      cbn.
      iIntros (? ? ? ? ?) "[Hregs [% (Hmem & %Hmap)]]".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro.
      iSplitR; first auto.
      iIntros.
      iModIntro.
      iModIntro.
      iModIntro.
      dependent elimination H0.
      dependent elimination s.
      rewrite Heq in f1.
      cbn in f1.
      dependent elimination f1.
      cbn.
      iMod "Hclose" as "_".
      iModIntro.
      cbn.
      iAssert (⌜ memmap !! paddr = Some w ⌝)%I with "[H Hmem]" as "%".
      { iApply (gen_heap.gen_heap_valid with "Hmem H"). }
      iSplitL "Hregs Hmem".
      iSplitL "Hregs"; first iFrame.
      iExists memmap; iFrame.
      iPureIntro; assumption.
      iSplitL; [|auto].
      iApply wp_value; cbn.
      iSplitL; [|auto].
      iSplitR.
      apply map_Forall_lookup_1 with (i := paddr) (x := w) in Hmap; auto.
      iFrame.
    Qed.

    Lemma write_ram_sound `{sg : sailGS Σ, HGS: invGS} :
      ValidContractForeign sep_contract_write_ram write_ram.
    Proof.
      intros Γ es δ ι Heq.
      destruct (env.snocView ι) as [ι t].
      destruct (env.snocView ι) as [ι p].
      destruct (env.snocView ι) as [ι entries].
      destruct (env.snocView ι) as [ι data].
      destruct (env.snocView ι) as [ι paddr].
      destruct (env.nilView ι). cbn in Heq |- *.
      iIntros "((%Hperm & _) & Hcp & Hes & (%Hpmp & _) & H)".
      unfold semWP. rewrite wp_unfold.
      cbn.
      iIntros (? ? ? ? ?) "[Hregs [% (Hmem & %Hmap)]]".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro.
      iSplitR; first auto.
      iIntros.
      iModIntro.
      iModIntro.
      iModIntro.
      dependent elimination H.
      dependent elimination s.
      rewrite Heq in f1.
      cbn in f1.
      dependent elimination f1.
      cbn.
      iDestruct "H" as "(%w & H)".
      iMod (gen_heap.gen_heap_update _ _ _ data with "Hmem H") as "[Hmem H]".
      iMod "Hclose" as "_".
      iModIntro.
      cbn.
      iSplitL "Hregs Hmem".
      - iSplitL "Hregs"; first iFrame.
        iExists (<[paddr:=data]> memmap); iFrame.
        unfold fun_write_ram; iPureIntro.
        apply map_Forall_lookup.
        intros i x H.
        destruct (Z.eqb paddr i) eqn:Heqb.
        + rewrite -> Z.eqb_eq in Heqb.
          subst.
          apply (lookup_insert_rev memmap i); assumption.
        + rewrite -> map_Forall_lookup in Hmap.
          rewrite -> Z.eqb_neq in Heqb.
          rewrite -> (lookup_insert_ne _ _ _ _ Heqb) in H.
          apply Hmap; assumption.
      - iSplitL; trivial; iApply wp_value; cbn.
        iSplitL; now iFrame.
    Qed.

    Lemma decode_sound `{sg : sailGS Σ, HGS: invGS} :
      ValidContractForeign sep_contract_decode decode.
    Proof.
      intros Γ es δ ι Heq.
      destruct (env.snocView ι) as [ι bv].
      destruct (env.nilView ι). cbn in Heq |- *.
      iIntros "_".
      iApply wp_unfold.
      cbn.
      iIntros (? ? ? ? ?) "[Hregs [% (Hmem & %Hmap)]]".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro.
      iSplitR; first auto.
      iIntros.
      iModIntro.
      iModIntro.
      iModIntro.
      dependent elimination H.
      fold_semWP.
      dependent elimination s.
      rewrite Heq in f1.
      cbn in f1.
      dependent elimination f1.
      cbn.
      iMod "Hclose" as "_".
      iModIntro.
      cbn.
      iSplitL "Hregs Hmem".
      iSplitL "Hregs"; first iFrame.
      iExists memmap; iFrame.
      iPureIntro; assumption.
      iSplitL; trivial.
      destruct (pure_decode bv) eqn:Ed.
      by rewrite semWP_fail.
      iApply wp_value.
      iSplitL; first iPureIntro; auto.
    Qed.

    Lemma foreignSem `{sailGS Σ} : ForeignSem.
    Proof.
      intros Δ τ f; destruct f;
        eauto using read_ram_sound, write_ram_sound, decode_sound.
    Qed.
  End ForeignProofs.

  Section LemProofs.
    Context `{sg : sailGS Σ}.

    Lemma gprs_equiv :
      interp_gprs ⊣⊢
      asn.interpret asn_regs_ptsto env.nil.
    Proof.
      unfold interp_gprs, reg_file.
      rewrite big_sepS_list_to_set; [|apply finite.NoDup_enum].
      cbn. iSplit.
      - iIntros "[_ [Hx1 [Hx2 [Hx3 [Hx4 [Hx5 [Hx6 [Hx7 _]]]]]]]]". iFrame.
      - iIntros "[Hx1 [Hx2 [Hx3 [Hx4 [Hx5 [Hx6 Hx7]]]]]]". iFrame.
        by iExists 0.
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
      unfold interp_pmp_entries.
      iIntros "H".
      destruct entries; try done.
      destruct v as [cfg0 addr0].
      destruct entries; try done.
      destruct v as [cfg1 addr1].
      destruct entries; try done.
      iExists cfg0.
      iExists addr0.
      iExists cfg1.
      iExists addr1.
      iDestruct "H" as "[Hcfg0 [Haddr0 [Hcfg1 Haddr1]]]".
      iSplitL "Hcfg0"; eauto.
      iSplitL "Haddr0"; eauto.
      iSplitL "Hcfg1"; eauto.
    Qed.

    Lemma close_pmp_entries_sound :
      ValidLemma RiscvPmpSpecification.lemma_close_pmp_entries.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      unfold interp_pmp_entries.
      iIntros "[Hcfg0 [Haddr0 [Hcfg1 Haddr1]]]".
      iAccu.
    Qed.

    Lemma in_liveAddrs : forall (addr : Addr),
        (minAddr <= addr)%Z ->
        (addr <= maxAddr)%Z ->
        addr ∈ liveAddrs.
    Proof.
      intros addr Hmin Hmax.
      apply elem_of_seqZ.
      lia.
    Qed.

    Lemma in_liveAddrs_split : forall (addr : Addr),
        (minAddr <= addr)%Z ->
        (addr <= maxAddr)%Z ->
        exists l1 l2, liveAddrs = l1 ++ ([addr] ++ l2).
    Proof.
      intros addr Hmin Hmax.
      unfold liveAddrs.
      exists (seqZ minAddr (addr - minAddr)).
      exists (seqZ (addr + 1) (maxAddr - addr)).
      change [addr] with (seqZ addr 1).
      rewrite <-seqZ_app; try lia.
      replace addr with (minAddr + (addr - minAddr))%Z at 2 by lia.
      rewrite <-seqZ_app; try lia.
      now f_equal; lia.
    Qed.

    Lemma extract_pmp_ptsto_sound :
      ValidLemma RiscvPmpSpecification.lemma_extract_pmp_ptsto.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      rewrite ?Z.leb_le.
      iIntros "[Hmem [[%Hlemin _] [[%Hlemax _] [%Hpmp _]]]]".
      unfold interp_pmp_addr_access_without,
        interp_pmp_addr_access,
        interp_ptsto,
        MemVal, Word.

      destruct (in_liveAddrs_split Hlemin Hlemax) as (l1 & l2 & eq).
      rewrite eq.
      rewrite big_opL_app big_opL_cons.
      iDestruct "Hmem" as "[Hmem1 [Hpaddr Hmem2]]".
      iSplitR "Hpaddr".
      - iIntros "Hpaddr".
        iFrame.
        now iIntros "_".
      - iApply "Hpaddr".
        iPureIntro.
        now exists acc.
    Qed.

    Lemma return_pmp_ptsto_sound :
      ValidLemma RiscvPmpSpecification.lemma_return_pmp_ptsto.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      iIntros "[Hwithout Hptsto]".
      unfold interp_pmp_addr_access_without.
      iApply ("Hwithout" with "Hptsto").
    Qed.

    Lemma unlocked_bool : ∀ (cfg : Pmpcfg_ent),
        unlocked cfg ->
        match cfg with
        | {| L := L |} =>
            L = false
        end.
    Proof. intros []; unfold unlocked; auto. Qed.

    (* TODO: we will never have a partial match because we are using integers instead of bitvectors, eventually this lemma will make no sense *)
    Lemma pmp_match_addr_never_partial : ∀ (a : Xlenbits) (rng : PmpAddrRange),
        pmp_match_addr a rng = PMP_Match ∨ pmp_match_addr a rng = PMP_NoMatch.
    Proof.
    intros a [[lo hi]|]; cbn;
      repeat
        match goal with
        | |- context[Z.leb ?x ?y] => destruct (Z.leb_spec x y); cbn
        | |- context[Z.ltb ?x ?y] => destruct (Z.ltb_spec x y); cbn
        end; auto; Lia.lia.
    Qed.

    Lemma machine_unlocked_pmp_get_perms : ∀ (cfg : Pmpcfg_ent),
        unlocked cfg ->
        pmp_get_perms cfg Machine = PmpRWX.
    Proof.
      intros [] H.
      unfold pmp_get_perms.
      now rewrite (unlocked_bool H).
    Qed.

    Lemma machine_unlocked_check_pmp_access : ∀ (cfg0 cfg1 : Pmpcfg_ent) (a0 a1 addr : Xlenbits),
        unlocked cfg0 ∧ unlocked cfg1 ->
        check_pmp_access addr [(cfg0, a0); (cfg1, a1)] Machine = (true, None) ∨ check_pmp_access addr [(cfg0, a0); (cfg1, a1)] Machine = (true, Some PmpRWX).
    Proof.
     intros cfg0 cfg1 a0 a1 addr [Hcfg0 Hcfg1].
     unfold check_pmp_access, pmp_check.
     unfold pmp_match_entry.
     destruct (pmp_match_addr_never_partial addr (pmp_addr_range cfg1 a1 a0)) as [-> | ->];
       destruct (pmp_match_addr_never_partial addr (pmp_addr_range cfg0 a0 0%Z)) as [-> | ->];
       destruct cfg0, cfg1;
       try rewrite (unlocked_bool Hcfg0);
       try rewrite (unlocked_bool Hcfg1);
       cbn; auto.
    Qed.

    Lemma machine_unlocked_open_pmp_entries_sound :
      ValidLemma RiscvPmpSpecification.lemma_machine_unlocked_open_pmp_entries.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      iIntros "(Hentries & Hunlocked)".
      destruct entries; try done.
      destruct v as [cfg0 addr0].
      destruct entries; try done.
      destruct v as [cfg1 addr1].
      destruct entries; try done.
      unfold interp_pmp_all_entries_unlocked.
      iDestruct "Hunlocked" as "[Hcfg0 Hcfg1]".
      unfold interp_pmp_entries.
      iDestruct "Hentries" as "(? & ? & ? & ?)".
      iExists cfg0.
      iExists addr0.
      iExists cfg1.
      iExists addr1.
      now iFrame.
    Qed.

    Lemma machine_unlocked_close_pmp_entries_sound :
      ValidLemma RiscvPmpSpecification.lemma_machine_unlocked_close_pmp_entries.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      iIntros "(? & ? & ? & ? & %Hunlocked0 & %Hunlocked1 & _ & _)".
      iFrame.
      now iPureIntro.
    Qed.

    Lemma lemSem : LemmaSem.
    Proof.
      intros Δ [];
        eauto using open_gprs_sound, close_gprs_sound, open_ptsto_instr_sound, close_ptsto_instr_sound, open_pmp_entries_sound,
        close_pmp_entries_sound, extract_pmp_ptsto_sound, return_pmp_ptsto_sound,
        machine_unlocked_open_pmp_entries_sound, machine_unlocked_close_pmp_entries_sound.
    Qed.
  End LemProofs.

End RiscvPmpModel2.
