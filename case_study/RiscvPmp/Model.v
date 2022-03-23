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
     Lists.List.
From RiscvPmp Require Import
     Machine
     Contracts.
From Katamaran Require Import
     Bitvector
     Environment
     Program
     Specification
     Sep.Hoare
     Sep.Logic
     Semantics
     Iris.Model.

From iris.base_logic Require lib.gen_heap lib.iprop.
From iris.base_logic Require Export invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac.
From iris.program_logic Require Import weakestpre adequacy.
From iris.proofmode Require Import string_ident tactics.

Set Implicit Arguments.
Import ListNotations.

Module gh := iris.base_logic.lib.gen_heap.

Module RiscvPmpSemantics <: Semantics RiscvPmpBase RiscvPmpProgram :=
  MakeSemantics RiscvPmpBase RiscvPmpProgram.

Module RiscvPmpModel.
  Import RiscvPmpProgram.
  Import RiscvPmpSpecification.

  Include ProgramLogicOn RiscvPmpBase RiscvPmpSpecification.
  Include Iris RiscvPmpBase RiscvPmpSpecification RiscvPmpSemantics.

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

  Module RiscvPmpIrisHeapKit <: IrisHeapKit.
    Section WithIrisNotations.
      Import iris.bi.interface.
      Import iris.bi.big_op.
      Import iris.base_logic.lib.iprop.
      Import iris.base_logic.lib.gen_heap.

      Definition MemVal : Set := Word.

      Class mcMemGS Σ :=
        McMemGS {
            (* ghost variable for tracking state of registers *)
            mc_ghGS :> gh.gen_heapGS Addr MemVal Σ;
            mc_invNs : namespace
          }.

      Definition memGpreS : gFunctors -> Set := fun Σ => gh.gen_heapGpreS Z MemVal Σ.
      Definition memGS : gFunctors -> Set := mcMemGS.
      Definition memΣ : gFunctors := gh.gen_heapΣ Addr MemVal.

      Definition memΣ_GpreS : forall {Σ}, subG memΣ Σ -> memGpreS Σ :=
        fun {Σ} => gh.subG_gen_heapGpreS (Σ := Σ) (L := Addr) (V := MemVal).

      Definition mem_inv : forall {Σ}, memGS Σ -> Memory -> iProp Σ :=
        fun {Σ} mG μ => (True)%I.

      Definition mem_res : forall {Σ}, memGS Σ -> Memory -> iProp Σ :=
        fun {Σ} mG μ => (True)%I.

      Definition liveAddrs := seqZ minAddr (maxAddr - minAddr + 1).
      Definition initMemMap μ := (list_to_map (map (fun a => (a , μ a)) liveAddrs) : gmap Addr MemVal).

      Lemma initMemMap_works μ : map_Forall (λ (a : Addr) (v : MemVal), μ a = v) (initMemMap μ).
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

      Lemma mem_inv_init : forall Σ (μ : Memory), memGpreS Σ ->
        ⊢ |==> ∃ mG : memGS Σ, (mem_inv mG μ ∗ mem_res mG μ)%I.
      Proof.
        iIntros (Σ μ gHP).
        iMod (gen_heap_init (gen_heapGpreS0 := gHP) (L := Addr) (V := MemVal)) as (gH) "[inv _]".
        Unshelve.
        iModIntro.
        iExists (McMemGS gH (nroot .@ "addr_inv")).
        unfold mem_inv, mem_res.
        done.
        apply initMemMap; auto.
      Qed.

      Import Contracts.

      Definition reg_file : gset (bv 3) :=
        list_to_set (finite.enum (bv 3)).

      Definition interp_ptsreg `{sailRegGS Σ} (r : RegIdx) (v : Z) : iProp Σ :=
        match reg_convert r with
        | Some x => reg_pointsTo x v
        | None => True
        end.

      Section WithResources.
        Context `{sailRegGS Σ} `{invGS Σ} `{mG : memGS Σ}.

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

        (* TODO: add perm_access predicate *)
        (* pmp_addr_access(?entries, ?mode) 
         ∀ a ∈ Mem, p : Perm . check_access(a, entries, mode) = Some p -> 
                               ∃ w . a ↦ w ∗ perm_access(a, p) *)
        Definition interp_pmp_addr_access (addrs : list Addr) (entries : list PmpEntryCfg) (m : Privilege) : iProp Σ :=
          [∗ list] a ∈ addrs,
            (⌜∃ p, Pmp_access a entries m p⌝ -∗ (* TODO: if interp_ptsto is updated to include pmp_access, then use interp_ptsto here as well *)
              (∃ w, mapsto (hG := mc_ghGS (mcMemGS := mG)) a (DfracOwn 1) w))%I.

        (* TODO: change to ⌜∃ acc, Pmp_access a entries pacc⌝ -∗ mapsto ...? *)
        Definition interp_ptsto (addr : Addr) (w : Word) : iProp Σ :=
          mapsto (hG := mc_ghGS (mcMemGS := mG)) addr (DfracOwn 1) w. 

        Definition interp_pmp_addr_access_without (addr : Addr) (addrs : list Addr) (entries : list PmpEntryCfg) (m : Privilege) : iProp Σ :=
          (((* ⌜∃ p, Pmp_access addr entries m p⌝ -∗ *) (* TODO: instead of uncommenting this, just use interp_ptsto *)
              (∃ w, mapsto (hG := mc_ghGS (mcMemGS := mG)) addr (DfracOwn 1) w)) -∗
                 interp_pmp_addr_access addrs entries m)%I.
      End WithResources.

      Definition luser_inst `{sailRegGS Σ} `{invGS Σ} (mG : memGS Σ) (p : Predicate) : Env Val (𝑯_Ty p) -> iProp Σ :=
        match p return Env Val (𝑯_Ty p) -> iProp Σ with
        | pmp_entries             => fun ts => interp_pmp_entries (env.head ts)
        | pmp_addr_access         => fun ts => interp_pmp_addr_access (mG := mG) liveAddrs (env.head (env.tail ts)) (env.head ts)
        | pmp_addr_access_without => fun ts => interp_pmp_addr_access_without (mG := mG) (env.head (env.tail (env.tail ts))) liveAddrs (env.head (env.tail ts)) (env.head ts)
        | gprs                    => fun _  => interp_gprs
        | ptsto                   => fun ts => interp_ptsto (mG := mG) (env.head (env.tail ts)) (env.head ts)
        end.

    Definition lduplicate_inst `{sailRegGS Σ} `{invGS Σ} (mG : memGS Σ) :
      forall (p : Predicate) (ts : Env Val (𝑯_Ty p)),
        is_duplicable p = true ->
        (luser_inst mG p ts) ⊢ (luser_inst mG p ts ∗ luser_inst mG p ts).
    Proof.
      iIntros (p ts hdup) "H".
      destruct p; inversion hdup;
      iDestruct "H" as "#H";
      auto.
    Qed.

    End WithIrisNotations.
  End RiscvPmpIrisHeapKit.

  Module Import RiscvPmpIrisInstance := IrisInstance RiscvPmpIrisHeapKit.

  Lemma foreignSem `{sg : sailGS Σ} : ForeignSem (Σ := Σ).
  Proof.
    intros Γ τ Δ f es δ.
    destruct f; cbn.
  Admitted.

  Section Lemmas.
    Context `{sg : sailGS Σ}.

    Lemma open_gprs_sound :
      ValidLemma RiscvPmpSpecification.lemma_open_gprs.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      unfold RiscvPmpIrisHeapKit.interp_gprs, RiscvPmpIrisHeapKit.reg_file.
      rewrite big_sepS_list_to_set; [|apply finite.NoDup_enum]; cbn.
      iIntros "[_ [Hx1 [Hx2 [Hx3 [Hx4 [Hx5 [Hx6 [Hx7 _]]]]]]]]". iFrame.
    Qed.

    Lemma close_gprs_sound :
      ValidLemma RiscvPmpSpecification.lemma_close_gprs.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      unfold RiscvPmpIrisHeapKit.interp_gprs, RiscvPmpIrisHeapKit.reg_file.
      iIntros "[Hx1 [Hx2 [Hx3 [Hx4 [Hx5 [Hx6 Hx7]]]]]]".
      iApply big_sepS_list_to_set; [apply finite.NoDup_enum|].
      cbn; iFrame. eauto using 0%Z.
    Qed.

    Lemma open_pmp_entries_sound :
      ValidLemma RiscvPmpSpecification.lemma_open_pmp_entries.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      unfold RiscvPmpIrisHeapKit.interp_pmp_entries.
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
      unfold RiscvPmpIrisHeapKit.interp_pmp_entries.
      iIntros "[%cfg0 [%addr0 [%cfg1 [%addr1 [Hcfg0 [Haddr0 [Hcfg1 [Haddr1 [%H _]]]]]]]]]".
      destruct entries as [|[cfg0' addr0']]; try discriminate.
      destruct entries as [|[cfg1' addr1']]; try discriminate.
      destruct entries; try discriminate.
      inversion H; subst.
      iAccu.
    Qed.

    Lemma in_liveAddrs : forall (addr : Addr),
        (minAddr <= addr)%Z ->
        (addr <= maxAddr)%Z ->
        addr ∈ RiscvPmpIrisHeapKit.liveAddrs.
    Proof.
      intros addr Hmin Hmax.
      unfold RiscvPmpIrisHeapKit.liveAddrs.
      apply elem_of_seqZ.
      split; auto.
      rewrite Z.add_assoc.
      rewrite Zplus_minus.
      apply Zle_lt_succ; auto.
    Qed.

    Lemma extract_pmp_ptsto_sound :
      ValidLemma RiscvPmpSpecification.lemma_extract_pmp_ptsto.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      iIntros "[Hentries [Hmem [[%Hlemin _] [[%Hlemax _] [%Hpmp _]]]]]";
        unfold Abstract_le in *.
      iSplitL "Hentries"; try done.
      unfold RiscvPmpIrisHeapKit.interp_pmp_addr_access_without,
        RiscvPmpIrisHeapKit.interp_pmp_addr_access,
        RiscvPmpIrisHeapKit.interp_ptsto,
        RiscvPmpIrisHeapKit.MemVal, Word.

      (* TODO: the following  (until the next comment) should be plenty 
               to prove this lemma, the induction on liveAddrs should exactly
               not be needed in any case... *)
      (* Search (?P ∗ (?P -∗ ?Q))%I. *)
      (* Q 
         --- 
         P ∗ R (R = P -∗ Q) *)
      (* TODO: pmp_addr_access, move ∃ p0 into universal one (acc : Val ty_access_type) *)
      (* Search bi_wand.

      rewrite bi.sep_comm.
      iApply (big_sepL_lookup_acc with "H1"). *)

      (* unfold RiscvPmpIrisHeapKit.interp_pmp_addr_access.
      assert (Hin: paddr ∈ RiscvPmpIrisHeapKit.liveAddrs) by (apply (in_liveAddrs Hlemin Hlemax)).
      iInduction RiscvPmpIrisHeapKit.liveAddrs as [|x xs] "IH".
      - apply elem_of_nil in Hin; contradiction.
      - apply elem_of_cons in Hin as [Heq|Hin].
        + rewrite big_opL_cons.
          iDestruct "Hmem" as "[Hmem _]".
          unfold RiscvPmpIrisHeapKit.interp_ptsto; subst.
          iSplitL "Hentries"; try done.
          iSplitL.
          unfold RiscvPmpIrisHeapKit.interp_pmp_addr_access_without.
          iIntros "Hx".
          unfold RiscvPmpIrisHeapKit.interp_pmp_addr_access.
          iApply "Hmem".
          iPureIntro.
          exists acc; auto.
        + rewrite big_opL_cons.
          iDestruct "Hmem" as "[_ Hmem]".
          iApply ("IH" $! Hin with "Hentries Hmem").
    Qed. *)
    Admitted.

  End Lemmas.

  Lemma lemSem `{sg : sailGS Σ} : LemmaSem (Σ := Σ).
  Proof.
    intros Δ [];
      eauto using open_gprs_sound, close_gprs_sound, open_pmp_entries_sound,
      close_pmp_entries_sound, extract_pmp_ptsto_sound.
  Admitted. (* TODO: back to Qed once the gen_addr_matching_cfg stuff is thrown away *)
End RiscvPmpModel.
