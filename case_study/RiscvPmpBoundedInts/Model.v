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
    Context `{sg : sailGS Σ}.

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

    Lemma bv_bin_one : bv.bin (bv.one xlenbits) = 1%N.
    Proof. apply bv.bin_one, xlenbits_pos. Qed.

    Lemma mem_inv_not_modified : ∀ (μ : Memory) (memmap : gmap Addr MemVal),
        ⊢ ⌜map_Forall (λ (a : Addr) (v : Byte), μ a = v) memmap⌝ -∗
        gen_heap.gen_heap_interp memmap -∗
        mem_inv sailGS_memGS μ.
    Proof. iIntros (μ memmap) "Hmap Hmem"; iExists memmap; now iFrame. Qed.

    Lemma map_Forall_update : ∀ (μ : Memory) (memmap : gmap Addr MemVal)
                                (paddr : Addr) (data : Byte),
        map_Forall (λ (a : Addr) (v : Byte), μ a = v) memmap ->
        map_Forall (λ (a : Addr) (v : Byte), write_byte μ paddr data a = v) (<[paddr:=data]> memmap).
    Proof.
      intros μ memmap paddr data Hmap.
      apply map_Forall_lookup.
      intros i x H0.
      unfold write_byte.
      destruct eq_dec.
      - subst paddr.
        apply (lookup_insert_rev memmap i).
        assumption.
      - rewrite -> map_Forall_lookup in Hmap.
        rewrite (lookup_insert_ne _ _ _ _ n) in H0.
        apply Hmap; assumption.
    Qed.

    Lemma ptstomem_bv_app :
      forall {n} (a : Addr) (b : bv byte) (bs : bv (n * byte)),
        @interp_ptstomem _ _ (S n)%nat a (bv.app b bs)
        ⊣⊢
        (interp_ptsto a b ∗ interp_ptstomem (bv.one xlenbits + a) bs).
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
        + iApply "IHbytes".
          iPureIntro.
          rewrite bv.bin_add_small;
            rewrite bv_bin_one; lia.
          iExists bs.
          iFrame.
        + apply xlenbits_pos.
        + rewrite <- N.add_1_l; lia.
      - iIntros "H".
        rewrite bv.seqBv_succ.
        rewrite big_sepL_cons.
        iDestruct "H" as "([%b Hb] & Hbs)".
        iAssert (∃ (w : bv (bytes * byte)), interp_ptstomem (bv.one xlenbits + paddr) w)%I with "[Hbs]" as "H".
        iPoseProof ("IHbytes" $! (bv.one xlenbits + paddr)) as "H".
        iApply "H".
        iPureIntro.
        rewrite bv.bin_add_small bv_bin_one; lia.
        iApply "Hbs".
        iDestruct "H" as "[%w H]".
        iExists (bv.app b w).
        rewrite ptstomem_bv_app; iFrame.
        apply xlenbits_pos.
        rewrite <- N.add_1_l; lia.
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

    Lemma fun_read_ram_works {bytes memmap μ paddr} {w : bv (bytes * byte)} :
      map_Forall (λ (a : Addr) (v : Base.Byte), μ a = v) memmap ->
           interp_ptstomem paddr w ∗ gen_heap.gen_heap_interp memmap ⊢
              ⌜ fun_read_ram μ bytes paddr = w ⌝.
    Proof.
      revert paddr.
      iInduction bytes as [|bytes] "IHbytes";
      iIntros (paddr Hmap) "[Haddr Hmem]".
      - now destruct (bv.view w).
      - change (S bytes * byte)%nat with (byte + bytes * byte)%nat in w.
        destruct (bv.appView byte (bytes * byte) w) as (w0 & w).
        rewrite ptstomem_bv_app.
        iDestruct "Haddr" as "(Haddr0 & Haddr)".
        iPoseProof (gen_heap.gen_heap_valid with "Hmem Haddr0") as "%".
        iPoseProof ("IHbytes" $! w (bv.one xlenbits + paddr) Hmap with "[$Haddr $Hmem]") as "%eq".
        iPureIntro.
        simpl.
        f_equal; auto.
    Qed.

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
      iPoseProof (fun_read_ram_works Hmap with "[$H $Hmem]") as "%eq_fun_read_ram".
      iPoseProof (mem_inv_not_modified $! Hmap with "Hmem") as "Hmem".
      iFrame.
      now iApply wp_value.
    Qed.

    Lemma fun_write_ram_works μ bytes paddr data memmap {w : bv (bytes * byte)} :
      map_Forall (λ (a : Addr) (v : Base.Byte), μ a = v) memmap ->
      interp_ptstomem paddr w ∗ gen_heap.gen_heap_interp memmap ∗ (|={∅,⊤}=> emp) ={∅,⊤}=∗
      mem_inv sailGS_memGS (fun_write_ram μ bytes paddr data) ∗ (|={⊤}=> interp_ptstomem paddr data).
    Proof.
      iRevert (data w paddr μ memmap).
      iInduction bytes as [|bytes] "IHbytes"; cbn [fun_write_ram interp_ptstomem];
        iIntros (data w paddr μ memmap Hmap) "[Haddr [Hmem Hclose]]".
      - iMod "Hclose" as "_". iModIntro.
        iPoseProof (mem_inv_not_modified $! Hmap with "Hmem") as "Hmem".
        by iFrame.
     -  change (bv.appView _ _ data) with (bv.appView byte (bytes * byte) data).
        destruct (bv.appView byte (bytes * byte) data) as [bd data].
        destruct (bv.appView byte (bytes * byte) w) as [bw w].
        iDestruct "Haddr" as "[H Haddr]".
        iMod (gen_heap.gen_heap_update _ _ _ bd with "Hmem H") as "[Hmem H]".
        iFrame "H".
        iApply ("IHbytes" $! data w
                       (bv.add (bv.one xlenbits) paddr) (write_byte μ paddr bd)
                    (insert paddr bd memmap)).
        + iPureIntro.
          by apply map_Forall_update.
        + by iFrame.
    Qed.

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
      eliminate_prim_step Heq. clear es1 Heq.
      iDestruct "H" as "(%w & H)".
      fold_semWP. rewrite semWP_val.
      iFrame "Hcp Hes Hregs".
      iPoseProof (@fun_write_ram_works μ1 bytes paddr data memmap w Hmap
                   with "[$H $Hmem $Hclose]") as "H".
      iMod "H" as "[$ H]". by iSplitL.
    Qed.

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
        apply Z_of_N_inj.
        rewrite ?bv.bin_add_small ?Nat2N.inj_add ?N2Nat.id ?N2Z.inj_add ?N2Z.inj_sub ?bv.bin_of_nat_small;
        auto using lenAddr_rep.
        + rewrite (N2Z.inj_add (bv.bin addr)).
          now Lia.lia.
        + now rewrite ?bv.bin_add_small bv.bin_of_nat_small in Hmax.
      - enough (bv.bin (bv.of_nat minAddr) + N.of_nat (N.to_nat (bv.bin addr - bv.bin (bv.of_nat minAddr))) +
                N.of_nat (bytes + N.to_nat (bv.bin ((bv.of_nat minAddr) + bv.of_nat lenAddr) - bv.bin (addr + bv.of_nat bytes))) = @bv.bin xlenbits (bv.of_nat minAddr) + N.of_nat lenAddr)%N as -> by apply maxAddr_rep.
        apply Z_of_N_inj.
        rewrite ?bv.bin_add_small ?Nat2N.inj_add ?N2Nat.id ?N2Z.inj_add ?N2Z.inj_sub ?bv.bin_of_nat_small;
        auto using lenAddr_rep.
        + rewrite (N2Z.inj_add (bv.bin addr)).
          now Lia.lia.
        + rewrite ?bv.bin_add_small ?bv.bin_of_nat_small in Hmax; auto using lenAddr_rep.
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
          apply Z_of_N_inj.
          rewrite N2Z.inj_add.
          rewrite bv.bin_of_N_small; try assumption.
          rewrite bv.bin_of_N_small.
          rewrite N2Z.inj_sub.
          lia.
          now rewrite bv.bin_of_nat_small in Hmin.
          now rewrite bv.bin_of_nat_small in addrDiffFits.
      - rewrite N2Nat.id.
        rewrite ?bv.bin_add_small ?bv.bin_of_nat_small; auto using lenAddr_rep.
        assert (maxAddrFits := maxAddr_rep).
        remember (bv.bin addr + N.of_nat bytes)%N as p.
        remember (N.of_nat minAddr + N.of_nat lenAddr)%N as q.
        rewrite N.add_sub_assoc.
        rewrite N.add_comm.
        rewrite N.add_sub.
        rewrite Heqq.
        auto.
        rewrite Heqp.
        rewrite Heqq.
        rewrite <- (@bv.bin_of_nat_small xlenbits).
        rewrite <- bv.bin_add_small.
        auto.
        rewrite bv.bin_of_nat_small.
        rewrite Heqp in addrbytesFits.
        auto.
        auto.
        auto.
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
      apply bv.ule_cases in Hw as [Hw|Hw]; last by subst.
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
      - rewrite ?bv.uleb_ugt ?bv.uleb_ule ?bv.ultb_ult ?bv.ultb_uge in Heqb0 Heqb1 Heqb3 Heqb.
        assert (Hlt: lo <ᵘ paddr + w).
        { unfold bv.ult in *.
          rewrite ?bv.bin_add_small; auto.
          Lia.lia.
        }
        rewrite <- bv.uleb_ugt in Hlt.
        rewrite Hlt.
        simpl.
        rewrite <- bv.ultb_ult in Heqb3.
        apply bv.ultb_uleb in Heqb3.
        rewrite Heqb3.
        enough (paddr + w <=ᵘ? hi = true) by now rewrite H0.
        rewrite bv.uleb_ule.
        apply bv.ule_trans with (y := paddr + bytes); auto.
        apply bv.add_ule_mono; auto.
        apply bv.ult_ule_incl; auto.
        now rewrite bv.uleb_ule in Heqb2.
      - rewrite ?bv.uleb_ugt ?bv.uleb_ule ?bv.ultb_ult ?bv.ultb_uge in Heqb0 Heqb1 Heqb2 Heqb3 Heqb.
        rewrite andb_true_r in H.
        destruct (lo <=ᵘ? paddr) eqn:Heqlp; inversion H.
        rewrite bv.uleb_ule in Heqlp.
        replace paddr with lo in * by now apply bv.ule_antisymm.
        clear Heqb3 Heqb H Heqlp.
        assert (lo <ᵘ lo + w).
        { unfold bv.ugt, bv.ult.
          rewrite bv.bin_add_small; lia.
        }
        rewrite <-bv.uleb_ugt in H.
        rewrite H.
        enough ((lo + w <=ᵘ? hi) = true) by now rewrite H0.
        rewrite bv.uleb_ule.
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
      apply bv.uleb_ule in Heqb.
      apply (@bv_ule_base _ _ _ w _ Hass Hle) in Heqb.
      apply bv.uleb_ule in Heqb.
      rewrite Heqb.
      now rewrite orb_true_l.
      rewrite orb_false_l.
      destruct (hi <=ᵘ? paddr).
      now rewrite orb_true_r.
      destruct (lo <=ᵘ? paddr).
      destruct (paddr + bytes <=ᵘ? hi) eqn:?.
      apply bv.uleb_ule in Heqb0.
      apply (@bv_ule_base _ _ _ w _ Hass Hle) in Heqb0.
      apply bv.uleb_ule in Heqb0.
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
      destruct (pmp_match_entry paddr bytes _ _ _ _) eqn:E0; last done.
      - apply pmp_match_entry_reduced_width with (w := w) in E0; auto.
        now rewrite E0.
      - apply pmp_match_entry_reduced_width_continue with (w := w) in E0; auto.
        rewrite E0.
        destruct (pmp_match_entry paddr bytes _ _ _ _) eqn:E1; last done.
        + apply pmp_match_entry_reduced_width with (w := w) in E1; auto.
          now rewrite E1.
        + apply pmp_match_entry_reduced_width_continue with (w := w) in E1; auto.
          now rewrite E1.
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

    (* TODO: move some pmp predicate specific lemmas into sig.v? *)
    Lemma pmp_match_addr_match_conditions_1 : forall paddr w lo hi,
        bv.zero <ᵘ w ->
        pmp_match_addr paddr w (Some (lo , hi)) = PMP_Match ->
        lo <=ᵘ hi ∧ lo <ᵘ paddr + w ∧ lo <=ᵘ paddr ∧ paddr <ᵘ hi ∧ paddr + w <=ᵘ hi.
    Proof.
      unfold pmp_match_addr.
      intros paddr w lo hi Hw H.
      destruct (hi <ᵘ? lo) eqn:Ehilo; try discriminate H.
      destruct (paddr + w <=ᵘ? lo) eqn:Epwlo; first done.
      destruct (hi <=ᵘ? paddr) eqn:Ehip; first done.
      simpl in H.
      destruct (lo <=ᵘ? paddr) eqn:Elop; last done.
      destruct (paddr + w <=ᵘ? hi) eqn:Epwhi; last done.
      rewrite bv.ultb_antisym in Ehilo.
      apply negb_false_iff in Ehilo.
      apply bv.uleb_ule in Ehilo.
      apply bv.uleb_ule in Elop.
      apply bv.uleb_ugt in Ehip.
      apply bv.uleb_ugt in Epwlo.
      now apply bv.uleb_ule in Epwhi.
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
      assert (HrepS: (bv.bin paddr + 1 < bv.exp2 xlenbits)%N).
      { enough (bv.bin paddr + 1 < bv.bin paddr + N.of_nat (S bytes))%N by lia.
        apply N.add_lt_mono_l.
        rewrite ?Nat2N.inj_succ.
        rewrite bv.bin_of_nat_small in Hb; lia.
      }
      destruct rng as [[lo hi]|]; subst; auto.
      intros [Hres|Hres]; subst; auto; intros H.
      - unfold pmp_match_addr in *.
        destruct (hi <ᵘ? lo) eqn:?; auto.
        destruct (hi <=ᵘ? paddr) eqn:Ehipaddr.
        + apply bv.uleb_ule in Ehipaddr.
          apply bv.ule_add_r with (p := bv.one xlenbits) in Ehipaddr; auto.
          apply bv.uleb_ule in Ehipaddr.
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
      - apply pmp_match_addr_match_conditions_1 in H as (Hlohi & Hlopw & Hlop & Hphi & Hpwhi).
        apply pmp_match_addr_match_conditions_2; auto.

        now rewrite bv.of_nat_S bv.add_assoc in Hlopw.
        eauto using bv.ule_add_r, bv_bin_one.
        rewrite bv.of_nat_S in Hpwhi.
        rewrite bv.add_assoc in Hpwhi.
        apply bv.add_ule_S_ult in Hpwhi; auto.
        rewrite bv.bin_add_small bv_bin_one; last by lia.
        rewrite Nat2N.inj_succ in Hrep.
        rewrite bv.bin_of_nat_small; lia.
        rewrite bv.of_nat_S in Hpwhi.
        now rewrite bv.add_assoc in Hpwhi.
        apply bv.ult_nat_S_zero; auto.
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
        ⊢ ∀ (paddr : Addr)
            (entries : list PmpEntryCfg) (p : Privilege),
            (⌜bv.bin paddr + N.of_nat bytes < bv.exp2 xlenbits⌝)%N -∗
            (⌜N.of_nat bytes < bv.exp2 xlenbits⌝)%N -∗
            (⌜∃ p0, Pmp_access paddr (bv.of_nat bytes) entries p p0⌝) -∗
            (([∗ list] offset ∈ bv.seqBv paddr bytes,
               ⌜∃ p0, Pmp_access offset%bv 
                        (bv.of_nat 1) entries p p0⌝ -∗
                        ∃ w : Byte, interp_ptsto offset w)
              ∗-∗ 
              (⌜∃ p0, Pmp_access paddr (bv.of_nat bytes) entries p p0⌝ -∗
                        [∗ list] offset ∈ bv.seqBv paddr bytes,
                          ∃ w : Byte, interp_ptsto offset w))%I.
    Proof.
      iInduction bytes as [|bytes] "IHbytes"; iIntros (paddr pmp p) "%Hrep %Hbytes %Hpmp".
      now iSimpl.
      iSplit; iIntros "H".
      - iIntros "%Haccess".
        simpl.
        rewrite bv.seqBv_succ.
        rewrite big_sepL_cons.
        iDestruct "H" as "[Hb Hbs]".
        iSimpl.
        iSplitL "Hb".
        iApply "Hb".
        iPureIntro.
        destruct Haccess as [acc Haccess].
        exists acc.
        assert (Htmp: (N.of_nat 1 < bv.exp2 xlenbits)%N) by lia.
        rewrite <- (@bv.bin_of_nat_small _ _ Hbytes) in Hrep.
        apply (pmp_access_reduced_width Hrep (bv.ult_nat_S_zero Htmp) (bv.ule_nat_one_S Htmp Hbytes) Haccess).
        destruct bytes. (* we need to know a bit more about bytes to finish this case *)
        now iSimpl.
        iSimpl in "Hbs".
        destruct Haccess as [acc Haccess].
        apply pmp_access_addr_S_width_pred in Haccess.
        iApply ("IHbytes" $! (bv.one xlenbits + paddr) pmp p _ _ _ with "Hbs").
        iExists acc.
        iPureIntro.
        now rewrite (@bv.add_comm _ (bv.one xlenbits) paddr).
        rewrite bv.bin_of_nat_small; lia.
        auto.
        auto.
        Unshelve.
        all: try lia.
        apply xlenbits_pos.
        eapply N.le_lt_trans.
        2: exact Hrep.
        rewrite bv.bin_add_small.
        rewrite bv_bin_one; lia.
        rewrite bv_bin_one; lia.
        exists acc.
        now rewrite (@bv.add_comm _ (bv.one xlenbits) paddr).
      - iSpecialize ("H" $! Hpmp).
        rewrite bv.seqBv_succ.
        iDestruct "H" as "[Hw H]"; fold seq.
        simpl.
        iSplitL "Hw"; auto.
        destruct bytes; first now simpl.
        iApply "IHbytes"; auto.
        1-3: iPureIntro; try lia.
        rewrite bv.bin_add_small bv_bin_one; lia.
        destruct Hpmp as [acc Hpmp].
        exists acc.
        rewrite bv.add_comm.
        apply pmp_access_addr_S_width_pred; auto.
        rewrite bv.bin_of_nat_small; try lia.
        apply xlenbits_pos; lia.
        lia.
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
      { apply Z.lt_eq_cases in Hlemax as [Hlemax|Hlemax].
        unfold bv.unsigned in Hlemax.
        apply N2Z.inj_lt.
        rewrite N2Z.inj_add.
        rewrite nat_N_Z.
        eapply Z.lt_trans.
        2: apply N2Z.inj_lt; apply maxAddr_rep.
        now rewrite nat_N_Z.
        apply N2Z.inj_lt.
        unfold bv.unsigned in Hlemax.
        rewrite N2Z.inj_add.
        rewrite nat_N_Z.
        rewrite Hlemax.
        rewrite <- nat_N_Z.
        apply N2Z.inj_lt.
        apply maxAddr_rep. }
      assert (Hbytes: (N.of_nat bytes < bv.exp2 xlenbits)%N).
      { destruct (bv.bin paddr).
        now rewrite N.add_0_l in H.
        eapply N.lt_trans.
        2: exact H.
        apply N.lt_add_pos_l.
        lia. }

      destruct (@in_liveAddrs_split paddr bytes Hbytes H) as (l1 & l2 & eq).
      lia.
      apply minAddr_le_ule; auto.
      apply maxAddr_le_ule; auto.
      rewrite eq. 
      rewrite ?big_opL_app.
      iDestruct "Hmem" as "(Hmem1 & Haddrs & Hmem2)".
      iSplitR "Haddrs".
      - iIntros "Hpaddr".
        iFrame "Hmem1 Hmem2".
        unfold ptstoSth.
        iPoseProof (big_sepL_pure_impl bytes $! _ _ _ _ _ _ with "[Hpaddr]") as "Haddrs".
        iIntros "%".
        now iApply (interp_ptstomem_big_sepS bytes $! paddr H).
        iFrame.
      - unfold ptstoSth.
        iApply (interp_ptstomem_big_sepS bytes $! paddr H).
        iApply (big_sepL_pure_impl bytes $! _ _ _ _ _ _ with "Haddrs").
        iPureIntro.
        now exists acc.
        Unshelve.
        all: try lia.
        all: now exists acc.
    Qed.

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

    Lemma lemSem : LemmaSem.
    Proof.
      intros Δ [];
        eauto using open_gprs_sound, close_gprs_sound, open_ptsto_instr_sound, close_ptsto_instr_sound, open_pmp_entries_sound,
        close_pmp_entries_sound, extract_pmp_ptsto_sound, return_pmp_ptsto_sound.
    Qed.
  End LemProofs.

End RiscvPmpModel2.
