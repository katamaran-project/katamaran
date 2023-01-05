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
      iInduction bytes as [|bytes] "IHbytes".
      - iSplitL "Hregs Hmem".
        now iPoseProof (mem_inv_not_modified $! Hmap with "Hmem") as "$".
        iFrame.
        iApply wp_value.
        simpl; iSplit; auto.
        iPureIntro.
        now destruct (bv.view w).
      - admit.
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
        by iExists bv.zero.
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
    (* TODO: more efficient proof? *)
      unfold maxAddr.
      intros addr bytes bytesfit lenAddrFits maxAddrFits addrbytesFits addrDiffFits Hmin Hmax.
      unfold bv.ule, bv.ule in *.
      unfold liveAddrs.
      exists (bv.seqBv minAddr (N.to_nat (bv.bin addr - bv.bin minAddr))%N).
      exists (bv.seqBv (bv.add addr (bv.of_nat bytes)) (N.to_nat (bv.bin (minAddr + bv.of_nat lenAddr) - bv.bin (addr + bv.of_nat bytes)))).
      rewrite <-(bv.seqBv_app addr).
      replace addr with (minAddr + bv.of_nat (N.to_nat (bv.bin addr - bv.bin minAddr))) at 2.
      rewrite <-bv.seqBv_app; try lia.
      f_equal.
      - unfold bv.ule, bv.ult in *.
        apply N_of_nat_inj.
        apply Z_of_N_inj.
        rewrite ?bv.bin_add_small ?Nat2N.inj_add ?N2Nat.id ?N2Z.inj_add ?N2Z.inj_sub ?bv.bin_of_nat_small;
        try assumption.
        + rewrite (N2Z.inj_add (bv.bin addr)).
          now Lia.lia.
        + now rewrite ?bv.bin_add_small bv.bin_of_nat_small in Hmax.
      - enough (bv.bin minAddr + N.of_nat (N.to_nat (bv.bin addr - bv.bin minAddr)) +
                N.of_nat (bytes + N.to_nat (bv.bin (minAddr + bv.of_nat lenAddr) - bv.bin (addr + bv.of_nat bytes))) = bv.bin minAddr + N.of_nat lenAddr)%N as -> by assumption.
        apply Z_of_N_inj.
        rewrite ?bv.bin_add_small ?Nat2N.inj_add ?N2Nat.id ?N2Z.inj_add ?N2Z.inj_sub ?bv.bin_of_nat_small;
        try assumption.
        + rewrite (N2Z.inj_add (bv.bin addr)).
          now Lia.lia.
        + rewrite ?bv.bin_add_small ?bv.bin_of_nat_small in Hmax; try assumption.
      - unfold bv.of_nat.
        rewrite N2Nat.id.
        apply bv.unsigned_inj.
        unfold bv.unsigned.
        rewrite bv.bin_add_small.
        + rewrite N2Z.inj_add.
          rewrite bv.bin_of_N_small; try assumption.
          now Lia.lia.
        + replace (bv.bin minAddr + _)%N with (bv.bin addr); try Lia.lia.
          apply Z_of_N_inj.
          rewrite N2Z.inj_add.
          rewrite bv.bin_of_N_small; try assumption.
          now Lia.lia.

      - rewrite N2Nat.id.
        rewrite ?bv.bin_add_small; try assumption.
        rewrite ?bv.bin_of_nat_small; try assumption.
        + rewrite bv.bin_add_small bv.bin_of_nat_small in maxAddrFits; try assumption.
          now Lia.lia.
        + now rewrite bv.bin_of_nat_small.
    Qed.

    (* TODO: first use Dominique's impl/lemma above, then in cleanup/refactor phase shift to a seqBV as in stddp/unstable! *)
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

    Lemma N_of_nat_lt_S : forall w n,
        (N.of_nat (S n) < bv.exp2 w)%N ->
        (N.of_nat n < bv.exp2 w)%N.
    Proof. lia. Qed.

    Lemma bv_ule_nat_one_S : forall {w} (n : nat),
        (N.of_nat 1 < bv.exp2 w)%N ->
        (N.of_nat (S n) < bv.exp2 w)%N ->
        @bv.of_nat w 1 <=ᵘ bv.of_nat (S n).
    Proof. intros; unfold bv.ule; rewrite ?bv.bin_of_nat_small; lia. Qed.

    Lemma bv_ult_nat_S_zero : forall {w} (n : nat),
        (N.of_nat (S n) < bv.exp2 w)%N ->
        @bv.zero w <ᵘ bv.of_nat (S n).
    Proof. intros; unfold bv.ult; rewrite bv.bin_of_nat_small; auto; now simpl. Qed.

    Lemma bv_ule_trans : forall {n} (x y z : bv n),
        x <=ᵘ y ->
        y <=ᵘ z ->
        x <=ᵘ z.
    Proof. intros n x y z; unfold bv.ule; apply N.le_trans. Qed.

    Lemma bv_ult_trans : forall {n} (x y z : bv n),
        x <ᵘ y ->
        y <ᵘ z ->
        x <ᵘ z.
    Proof. intros n x y z; unfold bv.ult; apply N.lt_trans. Qed.

    Lemma bv_add_ule_mono : forall {x} (n m p : bv x),
        (bv.bin p + bv.bin n < bv.exp2 x)%N ->
        (bv.bin p + bv.bin m < bv.exp2 x)%N ->
        n <=ᵘ m <-> p + n <=ᵘ p + m.
    Proof.
      intros; unfold bv.ule; rewrite ?bv.bin_add_small; lia.
    Qed.

    Lemma bv_ule_add_r : forall {x} (n m p : bv x),
        (bv.bin m + bv.bin p < bv.exp2 x)%N ->
        n <=ᵘ m -> n <=ᵘ m + p.
    Proof.
      intros.
      unfold bv.ule in *.
      rewrite bv.bin_add_small; auto.
      rewrite <- (N.add_0_r (bv.bin n)).
      apply N.add_le_mono; auto.
      apply N.le_0_l.
    Qed.

    Lemma bv_add_ule_r : forall {x} (n m p : bv x),
        (bv.bin n + bv.bin p < bv.exp2 x)%N ->
        n + p <=ᵘ m -> n <=ᵘ m.
    Proof.
      intros.
      unfold bv.ule in *.
      rewrite bv.bin_add_small in H0; auto.
      rewrite <- N.add_0_r in H0.
      apply (N.le_le_add_le _ _ _ _ (N.le_0_l (bv.bin p)) H0).
    Qed.

    Lemma bv_add_ule_S_ult : forall {x} (n m p : bv x),
        (bv.bin n + bv.bin p < bv.exp2 x)%N ->
        bv.zero <ᵘ p ->
        n + p <=ᵘ m -> n <ᵘ m.
    Proof.
      intros.
      unfold bv.ule, bv.ult in *.
      rewrite bv.bin_add_small in H1; auto.
      apply (N.lt_le_add_lt _ _ _ _ H0).
      now rewrite N.add_0_r.
    Qed.

    Lemma bv_ultb_antisym : forall {n} (x y : bv n),
        y <ᵘ? x = negb (x <=ᵘ? y).
    Proof. intros; unfold bv.uleb, bv.ultb; apply N.ltb_antisym. Qed.

    Lemma bv_ult_ule_incl : forall {n} (x y : bv n),
        x <ᵘ y -> x <=ᵘ y.
    Proof. intros; unfold bv.ule, bv.ult; apply N.lt_le_incl; auto. Qed.

    Lemma bv_ule_cases : forall {n} (x y : bv n),
        x <=ᵘ y <-> x <ᵘ y ∨ x = y.
    Proof.
      intros n x y.
      unfold bv.ule, bv.ult.
      now rewrite N.lt_eq_cases bv.bin_inj_equiv.
    Qed.

    (* TODO: better name! *)
    Lemma bv_ule_base : forall {n} (base a b max : bv n),
        (bv.bin base + bv.bin a < bv.exp2 n)%N ->
        b <=ᵘ a ->
        base + a <=ᵘ max ->
        base + b <=ᵘ max.
    Proof.
      intros n base a b max Hn Hba.
      apply bv_ule_trans with (y := base + a).
      unfold bv.ule in *.
      rewrite ?bv.bin_add_small; lia.
    Qed.

    Lemma bv_ule_refl : forall {n} (x : bv n),
        x <=ᵘ x.
    Proof. intros; unfold bv.ule; auto. Qed.

    Lemma bv_uleb_ugt : forall {n} (x y : bv n),
        x <=ᵘ? y = false <-> y <ᵘ x.
    Proof. intros; unfold bv.uleb, bv.ule; now apply N.leb_gt. Qed.

    Lemma bv_uleb_ule : forall {n} (x y : bv n),
        x <=ᵘ? y = true <-> x <=ᵘ y.
    Proof. intros; unfold bv.uleb; now apply N.leb_le. Qed.

    Lemma bv_ultb_uge : forall {n} (x y : bv n),
        x <ᵘ? y = false <-> y <=ᵘ x.
    Proof. intros; unfold bv.ultb; now apply N.ltb_ge. Qed.

    Lemma bv_ultb_ult : forall {n} (x y : bv n),
        x <ᵘ? y = true <-> x <ᵘ y.
    Proof. intros; unfold bv.ultb; now apply N.ltb_lt. Qed.

    Lemma bv_ultb_uleb : forall {n} (x y : bv n),
        x <ᵘ? y = true -> x <=ᵘ? y = true.
    Proof.
      intros n x y.
      rewrite bv_ultb_ult bv_uleb_ule.
      unfold bv.ule, bv.ult.
      lia.
    Qed.

    Lemma bv_ult_antirefl : forall {n} (x : bv n), not (x <ᵘ x).
    Proof. unfold bv.ult. lia. Qed.

    Lemma bv_add_nonzero_neq : forall {n} (x y : bv n),
        bv.zero <ᵘ y ->
        x + y ≠ x.
    Proof.
      intros n x y ynz eq.
      replace x with (x + bv.zero) in eq  at 2 by apply bv.add_zero_r.
      apply bv.add_cancel_l in eq.
      subst. revert ynz.
      now apply bv_ult_antirefl.
    Qed.

    Lemma bv_ule_antisymm {n} {x y : bv n} : x <=ᵘ y -> y <=ᵘ x -> x = y.
    Proof.
      unfold bv.ule.
      intros ineq1 ineq2.
      apply bv.bin_inj.
      now Lia.lia.
    Qed.

    (* TODO: move all these w <=ᵘ bytes stuff as an early assumption to get rid of all the "exact H..." tactics *)
    (* TODO: heavy cleanup needed! *)
    Lemma pmp_match_addr_reduced_width (bytes w : Xlenbits) :
      forall paddr rng,
        (bv.bin paddr + bv.bin bytes < bv.exp2 xlenbits)%N ->
        bv.zero <ᵘ w ->
        w <=ᵘ bytes ->
        pmp_match_addr paddr bytes rng = PMP_Match ->
        pmp_match_addr paddr w rng = PMP_Match.
    Proof.
      unfold bv.ule, bv.ult.
      intros paddr rng Hass H0w Hw Hpmp.
      assert (Hrep_paddr_w: (bv.bin paddr + bv.bin w < bv.exp2 xlenbits)%N) by lia.
      apply bv_ule_cases in Hw as [Hw|Hw]; last by subst.
      destruct rng as [[lo hi]|]; last by simpl.
      revert Hpmp.
      unfold pmp_match_addr.
      destruct (hi <ᵘ? lo) eqn:?; auto.
      destruct (paddr + bytes <=ᵘ? lo) eqn:?; first by cbn.
      rewrite orb_false_l.
      destruct (hi <=ᵘ? paddr) eqn:?; first by intros.
      destruct (paddr + bytes <=ᵘ? hi) eqn:?;
        last by (rewrite andb_false_r; inversion 1).
      intros H.
      destruct (lo <ᵘ? paddr) eqn:?.
      - rewrite ?bv_uleb_ugt ?bv_uleb_ule ?bv_ultb_ult ?bv_ultb_uge in Heqb0 Heqb1 Heqb3 Heqb.
        assert (Hlt: lo <ᵘ paddr + w).
        { unfold bv.ult in *.
          rewrite ?bv.bin_add_small; auto.
          Lia.lia.
        }
        rewrite <- bv_uleb_ugt in Hlt.
        rewrite Hlt.
        simpl.
        rewrite <- bv_ultb_ult in Heqb3.
        apply bv_ultb_uleb in Heqb3.
        rewrite Heqb3.
        enough (paddr + w <=ᵘ? hi = true) by now rewrite H0.
        rewrite bv_uleb_ule.
        apply bv_ule_trans with (y := paddr + bytes); auto.
        apply bv_add_ule_mono; auto.
        apply bv_ult_ule_incl; auto.
        now rewrite bv_uleb_ule in Heqb2.
      - rewrite ?bv_uleb_ugt ?bv_uleb_ule ?bv_ultb_ult ?bv_ultb_uge in Heqb0 Heqb1 Heqb2 Heqb3 Heqb.
        rewrite andb_true_r in H.
        destruct (lo <=ᵘ? paddr) eqn:Heqlp; inversion H.
        rewrite bv_uleb_ule in Heqlp.
        replace paddr with lo in * by now apply bv_ule_antisymm.
        clear Heqb3 Heqb H Heqlp.
        assert (lo <ᵘ lo + w).
        { unfold bv.ugt, bv.ult.
          rewrite bv.bin_add_small; lia.
        }
        rewrite <-bv_uleb_ugt in H.
        rewrite H.
        enough ((lo + w <=ᵘ? hi) = true) by now rewrite H0.
        rewrite bv_uleb_ule.
        unfold bv.ule, bv.ult in *.
        rewrite bv.bin_add_small in Heqb2; try lia.
        rewrite bv.bin_add_small; lia.
    Qed.

    Lemma pmp_match_addr_reduced_width_no_match (bytes w : Xlenbits) :
      forall paddr rng,
      (bv.bin paddr + bv.bin bytes < bv.exp2 xlenbits)%N ->
      w <=ᵘ bytes ->
      pmp_match_addr paddr bytes rng = PMP_NoMatch ->
      pmp_match_addr paddr w rng = PMP_NoMatch.
    Proof.
      intros paddr [[lo hi]|] Hass Hle; last by simpl.
      unfold pmp_match_addr.
      destruct (hi <ᵘ? lo); auto.
      destruct (paddr + bytes <=ᵘ? lo) eqn:?.
      rewrite orb_true_l.
      apply bv_uleb_ule in Heqb.
      apply (@bv_ule_base _ _ _ w _ Hass Hle) in Heqb.
      apply bv_uleb_ule in Heqb.
      rewrite Heqb.
      now rewrite orb_true_l.
      rewrite orb_false_l.
      destruct (hi <=ᵘ? paddr).
      now rewrite orb_true_r.
      destruct (lo <=ᵘ? paddr).
      destruct (paddr + bytes <=ᵘ? hi) eqn:?.
      apply bv_uleb_ule in Heqb0.
      apply (@bv_ule_base _ _ _ w _ Hass Hle) in Heqb0.
      apply bv_uleb_ule in Heqb0.
      now rewrite Heqb0.
      now rewrite andb_false_r.
      now rewrite andb_false_l.
    Qed.

    Lemma pmp_match_entry_reduced_width (bytes w : Xlenbits) :
      forall paddr cfg p hi lo,
        (bv.bin paddr + bv.bin bytes < bv.exp2 xlenbits)%N ->
        bv.zero <ᵘ w ->
        w <=ᵘ bytes ->
        pmp_match_entry paddr bytes p cfg hi lo = PMP_Success ->
        pmp_match_entry paddr w p cfg hi lo = PMP_Success.
    Proof.
      unfold pmp_match_entry.
      intros.
      destruct (pmp_match_addr paddr bytes _) eqn:E; try discriminate.
      apply pmp_match_addr_reduced_width with (w := w) in E; auto.
      now rewrite E.
    Qed.

    Lemma pmp_match_entry_reduced_width_continue (bytes w : Xlenbits) :
      forall paddr cfg p hi lo,
        (bv.bin paddr + bv.bin bytes < bv.exp2 xlenbits)%N ->
        w <=ᵘ bytes ->
        pmp_match_entry paddr bytes p cfg hi lo = PMP_Continue ->
        pmp_match_entry paddr w p cfg hi lo = PMP_Continue.
    Proof.
      unfold pmp_match_entry.
      intros.
      destruct (pmp_match_addr paddr bytes _) eqn:E; try discriminate.
      apply pmp_match_addr_reduced_width_no_match with (w := w) in E; auto.
      now rewrite E.
    Qed.

    Lemma check_pmp_access_reduced_width (bytes w : Xlenbits) :
      forall paddr pmp p acc,
        (bv.bin paddr + bv.bin bytes < bv.exp2 xlenbits)%N ->
        bv.zero <ᵘ w ->
        w <=ᵘ bytes ->
        check_pmp_access paddr bytes pmp p = (true, acc) ->
        check_pmp_access paddr w pmp p = (true, acc).
    Proof.
      intros paddr [|[cfg0 addr0] [|[cfg1 addr1] []]] p acc Hrep H0w Hle H;
        try now cbn in *.
      unfold check_pmp_access, pmp_check in *.
      destruct (pmp_match_entry paddr bytes _ _ _ _) eqn:E0.
      - apply pmp_match_entry_reduced_width with (w := w) in E0; auto.
        now rewrite E0.
      - apply pmp_match_entry_reduced_width_continue with (w := w) in E0; auto.
        rewrite E0.
        destruct (pmp_match_entry paddr bytes _ _ _ _) eqn:E1.
        + apply pmp_match_entry_reduced_width with (w := w) in E1; auto.
          now rewrite E1.
        + apply pmp_match_entry_reduced_width_continue with (w := w) in E1; auto.
          now rewrite E1.
        + discriminate.
      - discriminate.
    Qed.

    Lemma pmp_access_reduced_width (bytes w : Xlenbits) :
      forall paddr pmp p acc,
        (bv.bin paddr + bv.bin bytes < bv.exp2 xlenbits)%N ->
        bv.zero <ᵘ w ->
        w <=ᵘ bytes ->
        Pmp_access paddr bytes pmp p acc ->
        Pmp_access paddr w pmp p acc.
    Proof.
      intros paddr [|[cfg0 addr0] [|[cfg1 addr1] []]] p acc Hrep H0w Hw H;
        unfold Pmp_access, decide_pmp_access in *;
        try (destruct p; now cbn).
      destruct (check_pmp_access paddr _ _) eqn:E.
      destruct b; try discriminate.
      apply check_pmp_access_reduced_width with (w := w) in E; auto.
      now rewrite E.
    Qed.

    Lemma pmp_match_addr_match_conditions_1 : forall paddr w lo hi,
        bv.zero <ᵘ w ->
        pmp_match_addr paddr w (Some (lo , hi)) = PMP_Match ->
        lo <=ᵘ hi ∧ lo <=ᵘ paddr ∧ paddr + w <=ᵘ hi.
    Proof.
      unfold pmp_match_addr.
      intros paddr w lo hi Hw H.
      destruct (hi <ᵘ? lo) eqn:Ehilo; try discriminate H.
      destruct (paddr + w <=ᵘ? lo) eqn:Epwlo.
      now rewrite orb_true_l in H.
      destruct (hi <=ᵘ? paddr) eqn:Ehip.
      now rewrite orb_true_r in H.
      simpl in H.
      destruct (lo <=ᵘ? paddr) eqn:Elop; [|now rewrite andb_false_l in H].
      destruct (paddr + w <=ᵘ? hi) eqn:Epwhi; [|now simpl].
      rewrite bv_ultb_antisym in Ehilo.
      apply negb_false_iff in Ehilo.
      apply bv_uleb_ule in Ehilo.
      apply bv_uleb_ule in Elop.
      apply bv_uleb_ule in Epwhi.
      auto.
    Qed.

    Lemma pmp_match_addr_match_conditions_2 : forall paddr w lo hi,
        bv.zero <ᵘ w ->
        (bv.bin paddr + bv.bin w < bv.exp2 xlenbits)%N ->
        lo <=ᵘ hi ->
        lo <=ᵘ paddr ->
        paddr + w <=ᵘ hi ->
        pmp_match_addr paddr w (Some (lo , hi)) = PMP_Match.
    Proof.
      intros paddr w lo hi Hw Hrep Hlohi Hlop Hpwhi.
      unfold pmp_match_addr.
      remember Hlohi as Hlohi2.
      clear HeqHlohi2.
      apply bv_uleb_ule in Hlohi.
      apply negb_false_iff in Hlohi.
      rewrite <- bv_ultb_antisym in Hlohi.
      rewrite Hlohi.
      assert (lo <ᵘ paddr + w).
      unfold bv.ule, bv.ult in *.
      rewrite bv.bin_add_small; auto.
      lia.
      apply bv_uleb_ugt in H.
      rewrite H.
      simpl.
      apply bv_uleb_ugt in H.
      assert (paddr <ᵘ hi).
      unfold bv.ule, bv.ult in *.
      rewrite bv.bin_add_small in Hpwhi; auto.
      lia.
      apply bv_uleb_ugt in H0.
      rewrite H0.
      apply bv_uleb_ule in Hlop.
      apply bv_uleb_ule in Hpwhi.
      rewrite Hlop.
      rewrite Hpwhi.
      auto.
    Qed.

    Lemma bv_lt_S_add_one : forall {n} x,
        (N.of_nat (S x) < bv.exp2 n)%N ->
        (bv.bin (bv.one n) + (@bv.bin n (bv.of_nat x)) < bv.exp2 n)%N.
    Proof.
      destruct n.
      simpl; lia.
      assert (bv.bin (bv.one (S n)) = 1%N) by auto.
      rewrite H.
      intros.
      rewrite bv.bin_of_nat_small; lia.
    Qed.

    Lemma pmp_match_addr_addr_S_width_pred (bytes : nat) : forall paddr rng res,
        (0 < @bv.bin xlenbits (bv.of_nat bytes))%N ->
        (bv.bin paddr + N.of_nat (S bytes) < bv.exp2 xlenbits)%N ->
        (N.of_nat (S bytes) < bv.exp2 xlenbits)%N ->
        res = PMP_NoMatch ∨ res = PMP_Match ->
        pmp_match_addr paddr (bv.of_nat (S bytes)) rng = res ->
        pmp_match_addr (paddr + bv.one xlenbits) (bv.of_nat bytes) rng = res.
    Proof.
      intros paddr rng res Hb Hrep Hrepb.
      assert (HrepS: (bv.bin paddr + bv.bin (bv.one xlenbits) < bv.exp2 xlenbits)%N).
      { eapply N.lt_trans.
        2: exact Hrep.
        apply N.add_lt_mono_l.
        rewrite <- (@bv.bin_of_nat_small _ _ Hrepb).
        rewrite (bv.add_of_nat_0_r (bv.one xlenbits)).
        rewrite <- bv.of_nat_S.
        rewrite ?bv.bin_of_nat_small; auto.
        rewrite ?Nat2N.inj_succ.
        rewrite <- N.succ_lt_mono.
        rewrite <- (@bv.bin_of_nat_small xlenbits bytes); auto.
        eapply N.lt_trans.
        2: exact Hrepb.
        lia.
        lia.
      }
      destruct rng as [[lo hi]|]; subst; auto.
      intros [Hres|Hres]; subst; auto; intros H.
      - unfold pmp_match_addr in *.
        destruct (hi <ᵘ? lo) eqn:?; auto.
        destruct (hi <=ᵘ? paddr) eqn:Ehipaddr.
        + apply bv_uleb_ule in Ehipaddr.
          apply bv_ule_add_r with (p := bv.one xlenbits) in Ehipaddr; auto.
          apply bv_uleb_ule in Ehipaddr.
          rewrite Ehipaddr.
          now rewrite orb_true_r.
        + destruct (paddr + bv.of_nat (S bytes) <=ᵘ? lo) eqn:Epblo;
            rewrite bv.of_nat_S in Epblo;
            rewrite bv.add_assoc in Epblo;
            rewrite Epblo.
          * rewrite orb_true_l in H.
            now rewrite orb_true_l.
          * simpl in *.
            destruct (lo <=ᵘ? paddr);
              destruct (paddr + bv.of_nat (S bytes) <=ᵘ? hi); now auto.
      - apply pmp_match_addr_match_conditions_1 in H as (Hlohi & Hlop & Hpwhi).
        apply pmp_match_addr_match_conditions_2; auto.

        rewrite (bv.bin_add_small HrepS).
        rewrite <- N.add_assoc.
        rewrite <- bv.bin_add_small.
        rewrite <- bv.of_nat_S.
        rewrite <- (bv.bin_of_nat_small Hrepb) in Hrep.
        apply Hrep.
        apply bv_lt_S_add_one; auto.
        apply bv_ule_add_r; auto.
        rewrite bv.of_nat_S in Hpwhi.
        now rewrite bv.add_assoc in Hpwhi.
        apply bv_ult_nat_S_zero; auto.
    Qed.

    Lemma pmp_match_entry_addr_S_width_pred_success (bytes : nat) : forall paddr p cfg lo hi,
        (0 < @bv.bin xlenbits (bv.of_nat bytes))%N ->
        (bv.bin paddr + N.of_nat (S bytes) < bv.exp2 xlenbits)%N ->
        (N.of_nat (S bytes) < bv.exp2 xlenbits)%N ->
        pmp_match_entry paddr (bv.of_nat (S bytes)) p cfg lo hi = PMP_Success ->
        pmp_match_entry (paddr + bv.one xlenbits) (bv.of_nat bytes) p cfg lo hi = PMP_Success.
    Proof.
      intros paddr p cfg lo hi Hb Hrep Hrepb.
      unfold pmp_match_entry.
      intros H.
      destruct (pmp_match_addr paddr _ _) eqn:E;
        apply pmp_match_addr_addr_S_width_pred in E;
        auto;
        try now rewrite E.
      discriminate H.
    Qed.

    Lemma pmp_match_entry_addr_S_width_pred_continue (bytes : nat) : forall paddr p cfg lo hi,
        (0 < @bv.bin xlenbits (bv.of_nat bytes))%N ->
        (bv.bin paddr + N.of_nat (S bytes) < bv.exp2 xlenbits)%N ->
        (N.of_nat (S bytes) < bv.exp2 xlenbits)%N ->
        pmp_match_entry paddr (bv.of_nat (S bytes)) p cfg lo hi = PMP_Continue ->
        pmp_match_entry (paddr + bv.one xlenbits) (bv.of_nat bytes) p cfg lo hi = PMP_Continue.
    Proof.
      intros paddr p cfg lo hi Hb Hrep Hrepb.
      unfold pmp_match_entry.
      intros H.
      destruct (pmp_match_addr paddr _ _) eqn:E;
        apply pmp_match_addr_addr_S_width_pred in E;
        auto;
        try now rewrite E.
      discriminate H.
    Qed.

    Lemma pmp_access_addr_S_width_pred (bytes : nat) : forall paddr pmp p acc,
        (0 < @bv.bin xlenbits (bv.of_nat bytes))%N ->
        (bv.bin paddr + N.of_nat (S bytes) < bv.exp2 xlenbits)%N ->
        (N.of_nat (S bytes) < bv.exp2 xlenbits)%N ->
        Pmp_access paddr (bv.of_nat (S bytes)) pmp p acc ->
        Pmp_access (paddr + bv.one xlenbits) (bv.of_nat bytes) pmp p acc.
    Proof.
      intros paddr [|[cfg0 addr0] [|[cfg1 addr1] []]] p acc Hb Hrep Hrepb;
        unfold Pmp_access, decide_pmp_access;
        try (destruct p; now cbn).
      unfold check_pmp_access, pmp_check.
      destruct (pmp_match_entry paddr _ _ cfg0 _ _) eqn:Ecfg0; auto.
      apply pmp_match_entry_addr_S_width_pred_success in Ecfg0; auto.
      now rewrite Ecfg0.
      apply pmp_match_entry_addr_S_width_pred_continue in Ecfg0; auto.
      rewrite Ecfg0.
      destruct (pmp_match_entry paddr _ _ cfg1 _ _) eqn:Ecfg1; auto.
      apply pmp_match_entry_addr_S_width_pred_success in Ecfg1; auto.
      now rewrite Ecfg1.
      apply pmp_match_entry_addr_S_width_pred_continue in Ecfg1; auto.
      now rewrite Ecfg1.
    Qed.

    Lemma big_sepL_pure_impl (bytes : nat) :
        ⊢ ∀ (base : nat) (paddr : Addr)
            (entries : list PmpEntryCfg) (p : Privilege),
            (⌜bv.bin paddr + N.of_nat base + N.of_nat bytes < bv.exp2 xlenbits⌝)%N -∗
            (⌜N.of_nat bytes < bv.exp2 xlenbits⌝)%N -∗
            (⌜N.of_nat base < bv.exp2 xlenbits⌝)%N -∗
            (([∗ list] offset ∈ seq base bytes,
               ⌜∃ p0, Pmp_access (paddr + bv.of_nat offset)%bv 
                        (bv.of_nat 1) entries p p0⌝ -∗
                        ∃ w : Byte, interp_ptsto (paddr + bv.of_nat offset) w)
              ∗-∗ 
              (⌜∃ p0, Pmp_access (paddr + bv.of_nat base)%bv (bv.of_nat bytes) entries p p0⌝ -∗
                        [∗ list] offset ∈ seq base bytes,
                          ∃ w : Byte, interp_ptsto (paddr + bv.of_nat offset) w))%I.
    Proof.
      iInduction bytes as [|bytes] "IHbytes"; iIntros (base paddr pmp p) "%Hrep %Hbytes %Hbase".
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
        assert (Htmp: (N.of_nat 1 < bv.exp2 xlenbits)%N) by lia.
        rewrite <- (@bv.bin_of_nat_small _ _ Hbase) in Hrep.
        rewrite <- (@bv.bin_of_nat_small _ _ Hbytes) in Hrep.
        rewrite <- bv.bin_add_small in Hrep.
        apply (pmp_access_reduced_width Hrep (bv_ult_nat_S_zero Htmp) (bv_ule_nat_one_S Htmp Hbytes) Haccess).
        eapply N.lt_trans.
        2: exact Hrep.
        apply N.lt_add_pos_r.
        apply bv_ult_nat_S_zero; auto.
        fold seq.
        destruct bytes. (* we need to know a bit more about bytes to finish this case *)
        now iSimpl.
        iSimpl in "Hbs".
        destruct Haccess as [acc Haccess].
        apply pmp_access_addr_S_width_pred in Haccess.
        rewrite <- bv.add_assoc in Haccess.
        rewrite (@bv.add_comm _ (bv.of_nat base) (bv.one xlenbits)) in Haccess.
        rewrite <- bv.of_nat_S in Haccess.
        iApply ("IHbytes" $! (S base) paddr pmp p _ _ _ with "Hbs").
        now iExists acc.
        rewrite bv.bin_of_nat_small; first lia.
        eapply N.lt_trans.
        2: exact Hbytes.
        lia.
        rewrite <- (@bv.bin_of_nat_small _ _ Hbase) in Hrep.
        rewrite <- bv.bin_add_small in Hrep.
        apply Hrep.
        eapply N.lt_trans.
        2: exact Hrep.
        apply N.lt_add_pos_r; auto.
        rewrite <- (@bv.bin_of_nat_small _ _ Hbytes); auto.
        apply bv_ult_nat_S_zero; auto.
        lia.
        Unshelve.
        all: lia.
     - admit.
    Admitted.

    Lemma big_op_addrs_sum (paddr : Addr) : forall bytes (ϕ : Addr -> iProp Σ),
      (([∗ list] x ∈ map (λ offset : nat, paddr + bv.of_nat offset) (seq 0 bytes), ϕ x)
      ⊣⊢
      [∗ list] offset ∈ seq 0 bytes, (ϕ (paddr + bv.of_nat offset)))%I.
    Proof.
      intros; induction (seq 0 bytes) as [|? ? IHl]; first (simpl; done).
      iSplit; simpl; iIntros "[$ H]"; iApply (IHl with "H").
    Qed.

    (* TODO: not used, remove? *)
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
      - iIntros "H". now iExists bv.zero.
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
        1-3: iPureIntro.
        admit. (* TODO: if x <= maxAddr, then x < exp2 xlenbits (maxAddr should never exceed arch size) *)
        admit. (* TODO: same as above *)
        now simpl.
        iIntros "_".
        rewrite (bv.add_of_nat_0_l paddr).
        iPoseProof (interp_ptstomem_big_sepS bytes $! 0%nat paddr with "Hpaddr") as "H".
        now rewrite <- bv.add_of_nat_0_l.
      - unfold ptstoSth.
        rewrite big_op_addrs_sum.
        iPoseProof (big_sepL_pure_impl $! _ _ _ _ _ _ _ with "Haddrs") as "Haddrs".
        Unshelve. (* TODO: just derive these beforehand and pass them as args to big_sepL_pure_impl *)
        rewrite (bv.add_of_nat_0_l paddr).
        iApply (interp_ptstomem_big_sepS bytes $! 0%nat paddr).
        rewrite <- bv.add_of_nat_0_l.
        iApply "Haddrs".
        iPureIntro.
        rewrite <- bv.add_of_nat_0_r.
        now exists acc.
    Admitted.

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
