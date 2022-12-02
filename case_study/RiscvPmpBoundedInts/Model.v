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
     RiscvPmpBoundedInts.Machine
     RiscvPmpBoundedInts.Contracts
     RiscvPmpBoundedInts.IrisModel
     RiscvPmpBoundedInts.IrisInstance
     RiscvPmpBoundedInts.Sig.
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
        let id := string_to_ident s in
        let fr := fresh id in
        destruct (env.view ι) as [ι fr];
        destruct_syminstance ι
    | Env _ ctx.nil => destruct (env.view ι)
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
    Context `{sg : sailGS Σ, invGS}.

    Ltac eliminate_prim_step Heq :=
      let s := fresh "s" in
      let f := fresh "f" in
      match goal with
      | H: prim_step _ _ _ _ _ _ |- _ =>
          dependent elimination H as [mk_prim_step _ s];
          dependent elimination s as [RiscvPmpSemantics.st_foreign _ _ f];
          rewrite Heq in f;
          cbn in f;
          dependent elimination f;
          cbn
      end.

    Lemma mem_inv_not_modified : ∀ (γ : RegStore) (μ : Memory) (memmap : gmap Addr MemVal),
        ⊢ ⌜map_Forall (λ (a : Addr) (v : Byte), (γ, μ).2 a = v) memmap⌝ -∗
        gen_heap.gen_heap_interp memmap -∗
        mem_inv sailGS_memGS μ.
    Proof. iIntros (γ μ memmap) "Hmap Hmem"; iExists memmap; now iFrame. Qed.

    Lemma map_Forall_update : ∀ (γ : RegStore) (μ : Memory) (memmap : gmap Addr MemVal)
                                (paddr : Addr) (data : Byte),
        map_Forall (λ (a : Addr) (v : Byte), (γ, μ).2 a = v) memmap ->
        map_Forall (λ (a : Addr) (v : Byte), fun_write_ram μ 1 paddr data a = v)
                   (<[paddr:=data]> memmap).
    Proof.
      intros γ μ memmap paddr data Hmap.
      unfold fun_write_ram.
      apply map_Forall_lookup.
      intros i x H0.
      destruct bv.appView as [byte bytes]. cbn in bytes.
      unfold write_byte.
      destruct eq_dec.
      - subst paddr.
        apply (lookup_insert_rev memmap i).
        destruct (bv.view bytes).
        now rewrite bv.app_nil_r in H0.
      - rewrite -> map_Forall_lookup in Hmap.
        rewrite (lookup_insert_ne _ _ _ _ n) in H0.
        apply Hmap; assumption.
    Qed.

    (* Lemma mem_inv_update : ∀ (γ : RegStore) (μ : Memory) (memmap : gmap Addr MemVal) *)
    (*                          (paddr : Addr) (data : MemVal), *)
    (*     ⊢ ⌜map_Forall (λ (a : Addr) (v : Word), (γ, μ).2 a = v) memmap⌝ -∗ *)
    (*       gen_heap.gen_heap_interp (<[paddr := data]> memmap) -∗ *)
    (*       mem_inv sailGS_memGS (fun_write_ram μ paddr data). *)
    (* Proof. *)
    (*   iIntros (γ μ memmap paddr data) "%Hmap Hmem". *)
    (*   iExists (<[paddr := data]> memmap); iFrame. *)
    (*   iPureIntro; apply (map_Forall_update _ _ _ _ Hmap). *)
    (* Qed. *)

    Lemma read_ram_sound (bytes : nat) :
      ValidContractForeign (sep_contract_read_ram bytes) (read_ram bytes).
    Proof.
      intros Γ es δ ι Heq. cbn. destruct_syminstance ι. cbn.
      iIntros "((%Hperm & _) & Hcp & Hes & (%Hpmp & _) & H)".
      unfold semWP. rewrite wp_unfold.
      cbn in *.
      iIntros (? ? ? ? ?) "(Hregs & % & Hmem & %Hmap)".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro.
      iSplitR; first auto.
      iIntros.
      repeat iModIntro.
      eliminate_prim_step Heq.
      iMod "Hclose" as "_".
      iModIntro.
      (* iPoseProof (gen_heap.gen_heap_valid with "Hmem H") as "%". *)
      (* iPoseProof (mem_inv_not_modified $! Hmap with "Hmem") as "?". *)
      (* iFrame. *)
      (* iApply wp_value; cbn. *)
      (* iSplitL; [|auto]. *)
      (* iSplitR; auto. *)
      (* apply map_Forall_lookup_1 with (i := paddr) (x := w) in Hmap; auto. *)
    Admitted.

    Lemma write_ram_sound (bytes : nat) :
      ValidContractForeign (sep_contract_write_ram bytes) (write_ram bytes).
    Proof.
      intros Γ es δ ι Heq. destruct_syminstance ι. cbn.
      iIntros "((%Hperm & _) & Hcp & Hes & (%Hpmp & _) & H)".
      unfold semWP. rewrite wp_unfold.
      cbn.
      iIntros (? ? ? ? ?) "[Hregs [% (Hmem & %Hmap)]]".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro.
      iSplitR; first auto.
      iIntros.
      repeat iModIntro.
      eliminate_prim_step Heq.
      iDestruct "H" as "(%w & H)".
      (* iMod (gen_heap.gen_heap_update _ _ _ data with "Hmem H") as "[Hmem H]". *)
      (* iMod "Hclose" as "_". *)
      (* iModIntro. *)
      (* iPoseProof (mem_inv_update $! Hmap with "Hmem") as "?". *)
      (* iFrame. *)
      (* iApply wp_value; now iFrame. *)
    Admitted.

    Lemma decode_sound :
      ValidContractForeign sep_contract_decode decode.
    Proof.
      intros Γ es δ ι Heq.
      destruct_syminstance ι.
      iIntros "_".
      iApply wp_unfold.
      cbn in *.
      iIntros (? ? ? ? ?) "[Hregs [% (Hmem & %Hmap)]]".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro.
      iSplitR; first auto.
      iIntros.
      repeat iModIntro.
      eliminate_prim_step Heq.
      fold_semWP.
      iMod "Hclose" as "_".
      iModIntro.
      iPoseProof (mem_inv_not_modified $! Hmap with "Hmem") as "?".
      iFrame.
      iSplitL; trivial.
      destruct (pure_decode bv0) eqn:Ed.
      by rewrite semWP_fail.
      iApply wp_value.
      iSplitL; first iPureIntro; auto.
    Qed.

    Lemma foreignSem : ForeignSem.
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
      rewrite big_sepS_list_to_set; [|apply bv.finite.nodup_enum].
      cbn. iSplit.
      - iIntros "[_ [Hx1 [Hx2 [Hx3 [Hx4 [Hx5 [Hx6 [Hx7 _]]]]]]]]". iFrame.
      - iIntros "[Hx1 [Hx2 [Hx3 [Hx4 [Hx5 [Hx6 Hx7]]]]]]". iFrame.
        by iExists (bv.zero _).
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

    Lemma pmp_entries_ptsto : ∀ (entries : list PmpEntryCfg),
        ⊢ interp_pmp_entries entries -∗
          ∃ (cfg0 : Pmpcfg_ent) (addr0 : Addr) (cfg1 : Pmpcfg_ent) (addr1 : Addr),
            ⌜entries = [(cfg0, addr0); (cfg1, addr1)]⌝ ∗
            reg_pointsTo pmp0cfg cfg0 ∗ reg_pointsTo pmpaddr0 addr0 ∗
            reg_pointsTo pmp1cfg cfg1 ∗ reg_pointsTo pmpaddr1 addr1.
    Proof.
      iIntros (entries) "H".
      unfold interp_pmp_entries.
      destruct entries as [|[cfg0 addr0] [|[cfg1 addr1] [|]]] eqn:?; try done.
      repeat iExists _.
      now iFrame.
    Qed.

    Lemma open_pmp_entries_sound :
      ValidLemma RiscvPmpSpecification.lemma_open_pmp_entries.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      iIntros "H".
      iPoseProof (pmp_entries_ptsto with "H") as "(% & % & % & % & -> & ? & ? & ? & ?)".
      repeat iExists _.
      now iFrame.
    Qed.

    Lemma close_pmp_entries_sound :
      ValidLemma RiscvPmpSpecification.lemma_close_pmp_entries.
    Proof. intros ι; destruct_syminstance ι; cbn; auto. Qed.

    Lemma in_seqBv n v min len :
      (bv.bin min + N.of_nat len < bv.exp2 n)%N ->
      (min <=ᵘ v) -> (v <ᵘ bv.add min (bv.of_nat len)) ->
        v ∈ @seqBv n min len.
    Proof.
      unfold bv.ule, bv.ult, seqBv.
      intros Hbits mla alm.
      apply (elem_of_list_fmap_1_alt bv.of_Z _ (bv.unsigned v)).
      - apply elem_of_seqZ.
        unfold bv.unsigned.
        enough ((bv.bin (min + bv.of_nat len)) = (N.add (bv.bin min) (N.of_nat len))) by Lia.lia.
        apply (@bv.eq2n_to_eq_lt n); try assumption.
        + apply bv.is_wf_spec.
          now destruct (min + bv.of_nat len).
        + cbn.
          rewrite bv.truncn_eq2n.
          apply bv.eq2R.
          f_equal.
          rewrite bv.truncn_spec.
          rewrite N.mod_small; Lia.lia.
      - now rewrite bv.of_Z_unsigned.
    Qed.


    Lemma in_liveAddrs : forall (addr : Addr),
        (minAddr <=ᵘ addr) ->
        (addr <ᵘ maxAddr) ->
        addr ∈ liveAddrs.
    Proof.
      unfold liveAddrs, maxAddr.
      intros.
      apply in_seqBv;
        eauto using enough_addr_bits.
    Qed.

    Lemma in_liveAddrs_split : forall (addr : Addr) (bytes : nat),
        (minAddr <=ᵘ addr) ->
        (addr + (bv.of_nat bytes) <=ᵘ maxAddr) ->
        exists l1 l2, liveAddrs = l1 ++ ((map (fun offset => addr + (bv.of_nat offset)) (seq 0 bytes))  ++ l2).
    Proof.
      intros addr Hmin Hmax.
      unfold liveAddrs.
      (* exists (seqZ minAddr (addr - minAddr)). *)
      (* exists (seqZ (addr + 1) (maxAddr - addr)). *)
      (* change [addr] with (seqZ addr 1). *)
      (* rewrite <-seqZ_app; try lia. *)
      (* replace addr with (minAddr + (addr - minAddr))%Z at 2 by lia. *)
      (* rewrite <-seqZ_app; try lia. *)
      (* now f_equal; lia. *)
    Admitted.

    Lemma extract_pmp_ptsto_sound (bytes : nat) :
      ValidLemma (RiscvPmpSpecification.lemma_extract_pmp_ptsto bytes).
    Proof.
      intros ι; destruct_syminstance ι; cbn - [liveAddrs].
      iIntros "[Hmem [[%Hlemin _] [[%Hlemax _] [%Hpmp _]]]]".
      unfold interp_pmp_addr_access_without,
        interp_pmp_addr_access,
        interp_ptsto,
        MemVal, Word.
      destruct (@in_liveAddrs_split paddr bytes Hlemin Hlemax) as (l1 & l2 & eq).
      rewrite eq. (* TODO: we need to get ptsto chuncks for the range [paddr,paddr+bytes] *)
      rewrite ?big_opL_app.
      iDestruct "Hmem" as "(Hmem1 & Haddrs & Hmem2)".
      iSplitR "Haddrs".
      - iIntros "Hpaddr".
        iFrame.
        (* unfold interp_ptstomem.
        now iIntros "_".
      - iApply "Hpaddr".
        iPureIntro.
        now exists acc. *)
    Admitted.

    Lemma return_pmp_ptsto_sound (bytes : nat) :
      ValidLemma (RiscvPmpSpecification.lemma_return_pmp_ptsto bytes).
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      iIntros "[Hwithout Hptsto]".
      unfold interp_pmp_addr_access_without.
      iApply ("Hwithout" with "Hptsto").
    Qed.

    (* TODO: we will never have a partial match because we are using integers instead of bitvectors, eventually this lemma will make no sense *)
    (* Lemma pmp_match_addr_never_partial : ∀ (a : Xlenbits) (rng : PmpAddrRange), *)
    (*     pmp_match_addr a rng = PMP_Match ∨ pmp_match_addr a rng = PMP_NoMatch. *)
    (* Proof. *)
    (* intros a [[lo hi]|]; cbn; *)
    (*   repeat *)
    (*     match goal with *)
    (*     | |- context[@bv.uleb ?n ?x ?y] => destruct (@bv.ule_spec n x y); cbn *)
    (*     | |- context[@bv.ultb ?n ?x ?y] => destruct (@bv.ult_spec n x y); cbn *)
    (*     end; auto; cbv [bv.ule bv.ult] in *; Lia.lia. *)
    (* Qed. *)

    (* Lemma machine_unlocked_pmp_get_perms : ∀ (cfg : Pmpcfg_ent), *)
    (*     Pmp_cfg_unlocked cfg -> *)
    (*     pmp_get_perms cfg Machine = PmpRWX. *)
    (* Proof. *)
    (*   intros cfg H. *)
    (*   unfold pmp_get_perms. *)
    (*   now apply Pmp_cfg_unlocked_bool in H as ->. *)
    (* Qed. *)

    (* Lemma machine_unlocked_check_pmp_access : ∀ (cfg0 cfg1 : Pmpcfg_ent) (a0 a1 addr : Xlenbits), *)
    (*     Pmp_cfg_unlocked cfg0 ∧ Pmp_cfg_unlocked cfg1 -> *)
    (*     check_pmp_access addr [(cfg0, a0); (cfg1, a1)] Machine = (true, None) ∨ check_pmp_access addr [(cfg0, a0); (cfg1, a1)] Machine = (true, Some PmpRWX). *)
    (* Proof. *)
    (* intros cfg0 cfg1 a0 a1 addr [Hcfg0 Hcfg1]. *)
    (* unfold check_pmp_access, pmp_check, pmp_match_entry. *)
    (* apply Pmp_cfg_unlocked_bool in Hcfg0. *)
    (* apply Pmp_cfg_unlocked_bool in Hcfg1. *)
    (* destruct (pmp_match_addr_never_partial addr (pmp_addr_range cfg1 a1 a0)) as [-> | ->]; *)
    (*   destruct (pmp_match_addr_never_partial addr (pmp_addr_range cfg0 a0 [bv 0])) as [-> | ->]; *)
    (*   unfold pmp_get_perms; *)
    (*   rewrite ?Hcfg0; rewrite ?Hcfg1; *)
    (*   auto. *)
    (* Qed. *)

    Lemma machine_unlocked_open_pmp_entries_sound :
      ValidLemma RiscvPmpSpecification.lemma_machine_unlocked_open_pmp_entries.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      iIntros "(Hentries & Hunlocked)".
      iPoseProof (pmp_entries_ptsto with "Hentries") as "(% & % & % & % & -> & ? & ? & ? & ?)".
      iDestruct "Hunlocked" as "[[%Hcfg0 %Hcfg1] _]".
      apply Pmp_cfg_unlocked_bool in Hcfg0.
      apply Pmp_cfg_unlocked_bool in Hcfg1.
      iExists cfg0. iExists addr0. iExists cfg1. iExists addr1.
      now iFrame.
    Qed.

    Lemma machine_unlocked_close_pmp_entries_sound :
      ValidLemma RiscvPmpSpecification.lemma_machine_unlocked_close_pmp_entries.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      iIntros "(? & ? & ? & ? & [%Hunlocked0 _] & [%Hunlocked1 _] & _ & _)".
      apply Pmp_cfg_unlocked_bool in Hunlocked0.
      apply Pmp_cfg_unlocked_bool in Hunlocked1.
      now iFrame.
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
