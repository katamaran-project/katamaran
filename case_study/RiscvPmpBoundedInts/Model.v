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

    Lemma in_liveAddrs : forall (addr : Addr),
        (minAddr <=ᵘ addr) ->
        (addr <ᵘ maxAddr) ->
        addr ∈ liveAddrs.
    Proof.
      unfold liveAddrs, maxAddr.
      intros.
      apply bv.in_seqBv;
        eauto using enough_addr_bits.
    Qed.

    Opaque minAddr.
    Opaque lenAddr.
    Opaque xlenbits.

    Lemma in_liveAddrs_split : forall (addr : Addr) (bytes : nat),
        (N.of_nat bytes < bv.exp2 xlenbits)%N ->
        (N.of_nat lenAddr < bv.exp2 xlenbits)%N ->
        (bv.bin maxAddr < bv.exp2 xlenbits)%N ->
        (bv.bin addr + N.of_nat bytes < bv.exp2 xlenbits)%N ->
        (bv.bin addr - bv.bin minAddr < bv.exp2 xlenbits)%N ->
        (minAddr <=ᵘ addr) ->
        (addr + (bv.of_nat bytes) <=ᵘ maxAddr) ->
        exists l1 l2, liveAddrs = l1 ++ (bv.seqBv addr bytes  ++ l2).
    Proof.
    Admitted.
    (* more efficient proof? *)
    (*   unfold maxAddr. *)
    (*   intros addr bytes bytesfit lenAddrFits maxAddrFits addrbytesFits addrDiffFits Hmin Hmax. *)
    (*   unfold liveAddrs. *)
    (*   exists (bv.seqBv minAddr (N.to_nat (bv.bin addr - bv.bin minAddr))%N). *)
    (*   exists (bv.seqBv (bv.add addr (bv.of_nat bytes)) (N.to_nat (bv.bin (minAddr + bv.of_nat lenAddr) - bv.bin (addr + bv.of_nat bytes)))). *)
    (*   rewrite <-(bv.seqBv_app addr). *)
    (*   replace addr with (minAddr + bv.of_nat (N.to_nat (bv.bin addr - bv.bin minAddr))) at 2. *)
    (*   rewrite <-bv.seqBv_app; try lia. *)
    (*   f_equal. *)
    (*   unfold bv.ule, bv.ult in *. *)
    (*   apply N_of_nat_inj. *)
    (*   apply Z_of_N_inj. *)
    (*   rewrite ?bv.bin_add_small ?Nat2N.inj_add ?N2Nat.id ?N2Z.inj_add ?N2Z.inj_sub ?bv.bin_of_nat_small; *)
    (*     try assumption. *)
    (*   rewrite (N2Z.inj_add (bv.bin addr)). *)
    (*   now Lia.lia. *)
    (*   now rewrite ?bv.bin_add_small bv.bin_of_nat_small in Hmax. *)

    (*   enough (bv.bin minAddr + N.of_nat (N.to_nat (bv.bin addr - bv.bin minAddr)) + *)
    (*             N.of_nat (bytes + N.to_nat (bv.bin (minAddr + bv.of_nat lenAddr) - bv.bin (addr + bv.of_nat bytes))) = bv.bin minAddr + N.of_nat lenAddr)%N as -> by assumption. *)
    (*   apply Z_of_N_inj. *)
    (*   rewrite ?bv.bin_add_small ?Nat2N.inj_add ?N2Nat.id ?N2Z.inj_add ?N2Z.inj_sub ?bv.bin_of_nat_small; *)
    (*     try assumption. *)
    (*   rewrite (N2Z.inj_add (bv.bin addr)). *)
    (*   now Lia.lia. *)

    (*   unfold bv.ule in Hmax. *)
    (*   rewrite ?bv.bin_add_small ?bv.bin_of_nat_small in Hmax; try assumption. *)

    (*   unfold bv.ule in Hmin. *)
    (*   unfold bv.of_nat. *)
    (*   rewrite N2Nat.id. *)
    (*   apply bv.unsigned_inj. *)
    (*   unfold bv.unsigned. *)
    (*   rewrite bv.bin_add_small. *)
    (*   rewrite N2Z.inj_add. *)
    (*   rewrite bv.bin_of_N_small; try assumption. *)
    (*   now Lia.lia. *)

    (*   replace (bv.bin minAddr + _)%N with (bv.bin addr). *)
    (*   Lia.lia. *)
    (*   apply Z_of_N_inj. *)
    (*   rewrite N2Z.inj_add. *)
    (*   rewrite bv.bin_of_N_small; try assumption. *)
    (*   now Lia.lia. *)

    (*   rewrite N2Nat.id. *)
    (*   rewrite ?bv.bin_add_small; try assumption. *)
    (*   rewrite ?bv.bin_of_nat_small; try assumption. *)
    (*   rewrite bv.bin_add_small bv.bin_of_nat_small in maxAddrFits; try assumption. *)
    (*   now Lia.lia. *)

    (*   now rewrite bv.bin_of_nat_small. *)
    (* Qed. *)

    (* TODO: might be beneficial to introduce "seqBV" *)
    Lemma in_liveAddrs_split_old : forall (addr : Addr) (bytes : nat),
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

    (* TODO: better name! *)
    Lemma bv_uleb_leb : forall {n} (base a b max : bv n),
        (bv.bin base + bv.bin a < bv.exp2 n)%N ->
        base + a <=ᵘ max ->
        b <=ᵘ a ->
        base + b <=ᵘ max.
    Proof.
      intros n base a b max Hn H Hba.
      unfold bv.ule.
      unfold bv.ule in H.
      rewrite (bv.bin_add_small _).
      rewrite (bv.bin_add_small _) in H.
      eapply N.le_trans.
      2: exact H.
      apply N.add_le_mono_l.
      now unfold bv.ule in Hba.
      auto.
      unfold bv.ule in Hba.
      apply N.lt_eq_cases in Hba.
      destruct Hba as [Hba|Hba].
      - eapply N.lt_trans.
        2: exact Hn.
        now apply N.add_lt_mono_l.
      - apply bv.bin_inj in Hba.
        now subst.
    Qed.

    (* TODO: better name! *)
    Lemma bv_uleb_false : forall {n} (base a b max : bv n),
        (bv.bin base + bv.bin a < bv.exp2 n)%N ->
        base + a <=ᵘ? max = false ->
        b <=ᵘ a ->
        base + b <=ᵘ? max = false.
    Admitted.

    Lemma bv_uleb_ule : forall {n} (x y : bv n),
        x <=ᵘ y <-> x <=ᵘ? y = true.
    Admitted.

    (* TODO: move all these w <=ᵘ bytes stuff as an early assumption to get rid of all the "exact H..." tactics *)
    Lemma pmp_match_addr_reduced_width (bytes w : Xlenbits) :
      forall paddr rng,
      pmp_match_addr paddr bytes rng = PMP_Match ->
      w <=ᵘ bytes ->
      pmp_match_addr paddr w rng = PMP_Match.
    Proof.
      intros paddr [[lo hi]|];
        assert (Hass: (bv.bin paddr + bv.bin bytes < bv.exp2 xlenbits)%N) by admit.
      unfold pmp_match_addr.
      destruct (hi <ᵘ? lo); auto.
      destruct (paddr + bytes <=ᵘ? lo) eqn:?.
      rewrite orb_true_l.
      now intros.
      rewrite orb_false_l.
      destruct (hi <=ᵘ? paddr).
      now intros.
      intros H Hw.
      apply (@bv_uleb_false _ _ _ w _ Hass) in Heqb.
      2: exact Hw.
      rewrite Heqb.
      simpl.
      destruct (lo <=ᵘ? paddr).
      destruct (paddr + bytes <=ᵘ? hi) eqn:?.
      apply bv_uleb_ule in Heqb0.
      apply (@bv_uleb_leb _ _ _ w _ Hass) in Heqb0.
      2: exact Hw.
      apply bv_uleb_ule in Heqb0.
      rewrite Heqb0.
      now simpl.
      now rewrite andb_false_r in H.
      now rewrite andb_false_l in H.
      auto.
    Admitted.

    Lemma pmp_match_addr_reduced_width_no_match (bytes w : Xlenbits) :
      forall paddr rng,
      w <=ᵘ bytes ->
      pmp_match_addr paddr bytes rng = PMP_NoMatch ->
      pmp_match_addr paddr w rng = PMP_NoMatch.
    Proof.
      intros paddr [[lo hi]|] Hle;
        assert (Hass: (bv.bin paddr + bv.bin bytes < bv.exp2 xlenbits)%N) by admit.
      unfold pmp_match_addr.
      destruct (hi <ᵘ? lo); auto.
      destruct (paddr + bytes <=ᵘ? lo) eqn:?.
      rewrite orb_true_l.
      intros _.
      apply bv_uleb_ule in Heqb.
      apply (@bv_uleb_leb _ _ _ w _ Hass) in Heqb.
      2: exact Hle.
      apply bv_uleb_ule in Heqb.
      rewrite Heqb.
      now rewrite orb_true_l.
      rewrite orb_false_l.
      destruct (hi <=ᵘ? paddr).
      now rewrite orb_true_r.
      destruct (lo <=ᵘ? paddr).
      destruct (paddr + bytes <=ᵘ? hi) eqn:?.
      apply bv_uleb_ule in Heqb0.
      apply (@bv_uleb_leb _ _ _ w _ Hass) in Heqb0.
      2: exact Hle.
      apply bv_uleb_ule in Heqb0.
      rewrite Heqb0.
      now simpl.
      intros; now rewrite andb_false_r in H.
      intros; now rewrite andb_false_l in H.
      auto.
    Admitted.

    Lemma pmp_match_entry_reduced_width (bytes w : Xlenbits) :
      forall paddr cfg p hi lo,
      w <=ᵘ bytes ->
      pmp_match_entry paddr bytes p cfg hi lo = PMP_Success ->
      pmp_match_entry paddr w p cfg hi lo = PMP_Success.
    Proof.
      unfold pmp_match_entry.
      intros.
      destruct (pmp_match_addr paddr bytes _) eqn:E; try discriminate.
      apply (@pmp_match_addr_reduced_width _ w _ _) in E.
      2: exact H.
      now rewrite E.
    Qed.

    Lemma pmp_match_entry_reduced_width_continue (bytes w : Xlenbits) :
      forall paddr cfg p hi lo,
      w <=ᵘ bytes ->
      pmp_match_entry paddr bytes p cfg hi lo = PMP_Continue ->
      pmp_match_entry paddr w p cfg hi lo = PMP_Continue.
    Proof.
      unfold pmp_match_entry.
      intros.
      destruct (pmp_match_addr paddr bytes _) eqn:E; try discriminate.
      apply (pmp_match_addr_reduced_width_no_match _ _ H) in E.
      now rewrite E.
    Qed.

    Lemma check_pmp_access_reduced_width (bytes w : Xlenbits) :
      forall paddr pmp p acc,
        w <=ᵘ bytes ->
        check_pmp_access paddr bytes pmp p = (true, acc) ->
        check_pmp_access paddr w pmp p = (true, acc).
    Proof.
      intros paddr [|[cfg0 addr0] [|[cfg1 addr1] []]] p acc Hle H;
        try now cbn in *.
      unfold check_pmp_access, pmp_check in *.
      destruct (pmp_match_entry paddr bytes _ _ _ _) eqn:E0.
      - apply (pmp_match_entry_reduced_width _ _ _ _ _ Hle) in E0.
        now rewrite E0.
      - apply (pmp_match_entry_reduced_width_continue _ _ _ _ _ Hle) in E0.
        rewrite E0.
        destruct (pmp_match_entry paddr bytes _ _ _ _) eqn:E1.
        + apply (pmp_match_entry_reduced_width _ _ _ _ _ Hle) in E1.
          now rewrite E1.
        + apply (pmp_match_entry_reduced_width_continue _ _ _ _ _ Hle) in E1.
          now rewrite E1.
        + discriminate.
      - discriminate.
    Qed.

    Lemma pmp_access_reduced_width (bytes w : Xlenbits) :
      forall paddr pmp p acc,
      Pmp_access paddr bytes pmp p acc ->
      w <=ᵘ bytes ->
      Pmp_access paddr w pmp p acc.
    Proof.
      intros paddr [|[cfg0 addr0] [|[cfg1 addr1] []]] p acc H Hw;
        unfold Pmp_access, decide_pmp_access in *;
        try (destruct p; now cbn).
      destruct (check_pmp_access paddr _ _) eqn:E.
      destruct b; try discriminate.
      apply (check_pmp_access_reduced_width _ _ _ Hw) in E.
      now rewrite E.
    Qed.

    Lemma big_sepL_pure_impl (bytes : nat) :
        ⊢ ∀ (base : nat) (paddr : Addr)
            (entries : list PmpEntryCfg) (p : Privilege),
            (([∗ list] offset ∈ seq base bytes,
               ⌜∃ p0, Pmp_access (paddr + bv.of_nat offset)%bv 
                        (bv.of_nat 1) entries p p0⌝ -∗
                        ∃ w : Byte, interp_ptsto (paddr + bv.of_nat offset) w)
              ∗-∗ 
              (⌜∃ p0, Pmp_access (paddr + bv.of_nat base)%bv (bv.of_nat bytes) entries p p0⌝ -∗
                        [∗ list] offset ∈ seq base bytes,
                          ∃ w : Byte, interp_ptsto (paddr + bv.of_nat offset) w))%I.
    Proof.
      iInduction bytes as [|bytes] "IHbytes"; iIntros (base paddr pmp p).
      now iSimpl.
      iSplit; iIntros "H".
      - iIntros "%Haccess".
        rewrite big_sepL_cons.
        iDestruct "H" as "[Hb Hbs]".
        iSimpl.
        iSplitL "Hb".
        iApply "Hb".
        iPureIntro.
        destruct Haccess as [acc Haccess].
        exists acc.
        apply (pmp_access_reduced_width Haccess).
        admit. (* TODO: this is provable! *)
        fold seq.
        iSpecialize ("IHbytes" $! (S base) paddr pmp p with "Hbs").
        iApply "IHbytes".
        iPureIntro.
        admit. (* TODO: provable, if we have access to pₓ₊₁ then we also have access to (p+1)ₓ (format: addr\_bytes), or more visually p:|----| -> p+1:|---| *)
    Admitted.

    Lemma big_op_addrs_sum (paddr : Addr) : forall bytes (ϕ : Addr -> iProp Σ),
      (([∗ list] x ∈ map (λ offset : nat, paddr + bv.of_nat offset) (seq 0 bytes), ϕ x)
      ⊣⊢
      [∗ list] offset ∈ seq 0 bytes, (ϕ (paddr + bv.of_nat offset)))%I.
    Proof.
      intros; induction (seq 0 bytes) as [|? ? IHl]; first (simpl; done).
      iSplit; simpl; iIntros "[$ H]"; iApply (IHl with "H").
    Qed.

    Lemma big_sepL_exists_bytes : forall paddr bytes,
       ((∃ w : bv (bytes * byte),
         [∗ list] offset ∈ seq 0 bytes, interp_ptsto (paddr + bv.of_nat offset)
                                          (get_byte offset w))
       ⊣⊢
       ([∗ list] offset ∈ seq 0 bytes,
               ∃ w : Byte, interp_ptsto (paddr + bv.of_nat offset) w))%I.
    Proof.
      iIntros;
        iSplit;
        iIntros "H";
        iInduction (seq 0 bytes) as [|b] "IH"; try (simpl; done).
      - iDestruct "H" as "(%w & Hptsto & H)".
        iSplitL "Hptsto".
        now iExists (get_byte b w).
        iApply "IH".
        now iExists w.
      - now iExists _.
      - simpl.
        iDestruct "H" as "([%w Hptsto] & H)".
        (* TODO: add lemma in the form of:
           ∃ b₀ : bv m, ∃ bs : bv n, P (bv.app b₀ bs) -> ∃ w : bv (m + n), P w
         *)
    Admitted.

    Lemma ptstomem_bv_app :
      forall {n} (a : Addr) (b : bv byte) (bs : bv (n * byte)),
        @interp_ptstomem _ _ (S n)%nat a (bv.app b bs)
        ⊣⊢
        (interp_ptsto a b ∗ interp_ptstomem (bv.one xlenbits + a) bs).
    Proof. intros; cbn [interp_ptstomem]; now rewrite bv.appView_app. Qed.

    Lemma interp_ptstomem_big_sepS (bytes : nat) :
      ⊢ ∀ (base : nat) (paddr : Addr),
      (∃ (w : bv (bytes * byte)), interp_ptstomem (bv.of_nat base + paddr) w) ∗-∗
        [∗ list] offset ∈ seq base bytes,
            ∃ w, interp_ptsto (paddr + bv.of_nat offset) w.
    Proof.
      iInduction bytes as [|bytes] "IHbytes";
        iIntros (base paddr); iSplit.
      - auto.
      - iIntros "H". now iExists (bv.zero (0 * byte)).
      - iIntros "[%w H]". cbn [seq].
        rewrite big_sepL_cons.
        rewrite (@bv.add_comm _ paddr (bv.of_nat base)).
        destruct (bv.appView byte (bytes * byte) w) as [b bs].
        rewrite ptstomem_bv_app.
        iDestruct "H" as "[Hb Hbs]".
        iSplitL "Hb".
        + by iExists b.
        + iApply "IHbytes".
          iExists bs.
          now rewrite bv.of_nat_S bv.add_assoc.
      - iIntros "H".
        rewrite big_sepL_cons.
        rewrite (@bv.add_comm _ paddr (bv.of_nat base)).
        iDestruct "H" as "([%b Hb] & Hbs)".
        iAssert (∃ (w : bv (bytes * byte)), interp_ptstomem (bv.of_nat (S base) + paddr) w)%I with "[Hbs]" as "H".
        iApply ("IHbytes" $! (S base) paddr).
        iApply "Hbs".
        iDestruct "H" as "[%w H]".
        iExists (bv.app b w).
        rewrite ptstomem_bv_app.
        iSplitL "Hb"; first iExact "Hb".
        rewrite bv.add_assoc.
        now rewrite <- bv.of_nat_S.
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
      destruct (@in_liveAddrs_split_old paddr bytes Hlemin Hlemax) as (l1 & l2 & eq).
      rewrite eq. 
      rewrite ?big_opL_app.
      iDestruct "Hmem" as "(Hmem1 & Haddrs & Hmem2)".
      iSplitR "Haddrs".
      - iIntros "Hpaddr".
        iFrame "Hmem1 Hmem2".
        unfold ptstoSth.
        rewrite big_op_addrs_sum.
        iApply big_sepL_pure_impl.
        iIntros "_".
        rewrite (bv.add_of_nat_0_l paddr).
        iPoseProof (interp_ptstomem_big_sepS bytes $! 0%nat paddr with "Hpaddr") as "H".
        now rewrite <- bv.add_of_nat_0_l.
      - unfold ptstoSth.
        rewrite big_op_addrs_sum.
        iPoseProof (big_sepL_pure_impl with "Haddrs") as "Haddrs".
        rewrite (bv.add_of_nat_0_l paddr).
        iApply (interp_ptstomem_big_sepS bytes $! 0%nat paddr).
        rewrite <- bv.add_of_nat_0_l.
        iApply "Haddrs".
        iPureIntro.
        rewrite <- bv.add_of_nat_0_r.
        now exists acc.
    Qed.

    Print Assumptions extract_pmp_ptsto_sound.

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
