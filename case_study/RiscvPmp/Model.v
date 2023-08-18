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
     RiscvPmp.PmpCheck
     RiscvPmp.Machine
     RiscvPmp.Contracts
     RiscvPmp.IrisModel
     RiscvPmp.IrisInstance
     RiscvPmp.Sig
     trace.
From Equations Require Import
     Equations.

From iris.base_logic Require lib.gen_heap lib.iprop.
From iris.base_logic Require Export invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac.
From iris.program_logic Require Import weakestpre adequacy.
From iris.program_logic Require lifting.
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

  Ltac eliminate_prim_step Heq :=
    let s := fresh "s" in
    let f := fresh "f" in
    match goal with
    | H: language.prim_step _ _ _ _ _ _ |- _ =>
        rewrite /language.prim_step in H; cbn in H; (* unfold the Iris `prim_step`*)
        dependent elimination H as [RiscvPmpIrisBase.mk_prim_step _ s];
        destruct (RiscvPmpSemantics.smallinvstep s) as [? ? ? f];
        rewrite Heq in f;
        cbn in f;
        dependent elimination f;
        cbn
    end.

  Section ForeignProofs.
    Context `{sg : sailGS Σ}.


    Lemma mem_inv_not_modified : ∀ (μ : Memory) (memmap : gmap Addr MemVal),
        ⊢ ⌜map_Forall (λ (a : Addr) (v : Byte), memory_ram μ a = v) memmap⌝ -∗
        gen_heap.gen_heap_interp memmap -∗ trace.tr_auth trace.trace_name (memory_trace μ) -∗
        mem_inv sailGS_memGS μ.
    Proof. iIntros (μ memmap) "Hmap Hmem Htr"; iExists memmap; now iFrame. Qed.

    Lemma map_Forall_update : ∀ (μ : Memory) (memmap : gmap Addr MemVal)
                                (paddr : Addr) (data : Byte),
        map_Forall (λ (a : Addr) (v : Byte), memory_ram μ a = v) memmap ->
        map_Forall (λ (a : Addr) (v : Byte), write_byte (memory_ram μ) paddr data a = v) (<[paddr:=data]> memmap).
    Proof.
      intros μ memmap paddr data Hmap.
      apply map_Forall_lookup.
      intros i x H0.
      unfold write_byte.
      destruct eq_dec.
      - subst paddr.
        now apply (lookup_insert_rev memmap i).
      - rewrite -> map_Forall_lookup in Hmap.
        rewrite (lookup_insert_ne _ _ _ _ n) in H0.
        now apply Hmap.
    Qed.

    Lemma fun_read_ram_works {bytes memmap μ paddr} {w : bv (bytes * byte)} :
      map_Forall (λ (a : Addr) (v : Base.Byte), memory_ram μ a = v) memmap ->
           interp_ptstomem paddr w ∗ gen_heap.gen_heap_interp memmap ⊢
              ⌜ fun_read_ram μ bytes paddr = w ⌝.
    Proof.
      revert paddr.
      iInduction bytes as [|bytes] "IHbytes";
      iIntros (paddr Hmap) "[Haddr Hmem]".
      - now destruct (bv.view w).
      - destruct (bv.appView byte (bytes * byte) w) as (w0 & w).
        rewrite ptstomem_bv_app.
        iDestruct "Haddr" as "([Haddr0 HnotM] & Haddr)".
        iPoseProof (gen_heap.gen_heap_valid with "Hmem Haddr0") as "%".
        iPoseProof ("IHbytes" $! w (bv.one + paddr) Hmap with "[$Haddr $Hmem]") as "%eq".
        iPureIntro.
        simpl.
        f_equal; auto.
    Qed.

    (* Iris does not seem to have a no-fork variant for `language`s, so we prove it here, analogously to `wp_lift_atomic_head_step_no_fork` *)
    Lemma wp_lift_atomic_step_no_fork:
      ∀ {Λ : language} {Σ : gFunctors} {irisGS0 : irisGS Λ Σ}
        {s : stuckness} {E : coPset} {Φ : val Λ → iProp Σ}
        (e1 : language.expr Λ),
        language.to_val e1 = None
        → (∀ (σ1 : state Λ) (ns : nat) (κ κs : list (language.observation Λ)) (nt : nat),
            state_interp σ1 ns (κ ++ κs) nt ={E}=∗
            ⌜match s with
              | NotStuck => reducible e1 σ1
              | MaybeStuck => True
              end⌝ ∗
            ▷ (∀ (e2 : language.expr Λ) (σ2 : language.state Λ) (efs : list (language.expr Λ)),
                  ⌜language.prim_step e1 σ1 κ e2 σ2 efs⌝ ={E}=∗
                  ⌜efs = []⌝ ∗ state_interp σ2 (S ns) κs (length efs + nt) ∗
                  from_option Φ False (language.to_val e2) )) -∗
          WP e1 @ s; E {{ v, Φ v }}.
    Proof. intros * Hval. iIntros "H".
      iApply lifting.wp_lift_atomic_step; [auto | ].
      iIntros (σ1 ns κ κs nt) "Hσ1".
      iMod ("H" $! σ1 with "Hσ1") as "[$ H]"; iModIntro.
      iNext; iIntros (v2 σ2 efs Hstep) "_".
      iMod ("H" $! v2 σ2 efs with "[//]") as "(-> & ? & ?) /=". by iFrame.
    Qed.

    Lemma read_ram_sound (bytes : nat) :
      ValidContractForeign (sep_contract_read_ram bytes) (read_ram bytes).
    Proof.
      intros Γ es δ ι Heq. cbn. destruct_syminstance ι. cbn.
      iIntros "H". cbn in *.
      iApply (wp_lift_atomic_step_no_fork); [auto | ].
      iIntros (? ? ? ? ?) "(Hregs & % & Hmem & %Hmap & Htr)".
      iSplitR; first auto.
      repeat iModIntro.
      iIntros. iModIntro.
      eliminate_prim_step Heq.
      iPoseProof (fun_read_ram_works Hmap with "[$H $Hmem]") as "%eq_fun_read_ram".
      iPoseProof (mem_inv_not_modified $! Hmap with "Hmem Htr") as "Hmem".
      now iFrame.
    Qed.

    Lemma fun_write_ram_works μ bytes paddr data memmap {w : bv (bytes * byte)} :
      map_Forall (λ (a : Addr) (v : Base.Byte), (memory_ram μ) a = v) memmap ->
      interp_ptstomem paddr w ∗ gen_heap.gen_heap_interp memmap ∗ tr_auth1 (memory_trace μ) ={⊤}=∗
      mem_inv sailGS_memGS (fun_write_ram μ bytes paddr data) ∗ interp_ptstomem paddr data.
    Proof.
      iRevert (data w paddr μ memmap).
      iInduction bytes as [|bytes] "IHbytes"; cbn [fun_write_ram interp_ptstomem];
        iIntros (data w paddr μ memmap Hmap) "[Haddr [Hmem Htr]]".
      - iModIntro. iSplitL; last done.
        now iApply (mem_inv_not_modified $! Hmap with "Hmem Htr").
     -  change (bv.appView _ _ data) with (bv.appView byte (bytes * byte) data).
        destruct (bv.appView byte (bytes * byte) data) as [bd data].
        destruct (bv.appView byte (bytes * byte) w) as [bw w].
        iDestruct "Haddr" as "[[H $] Haddr]".
        iMod (gen_heap.gen_heap_update _ _ _ bd with "Hmem H") as "[Hmem $]".
        iApply ("IHbytes" $! data w
                       (bv.add bv.one paddr) (memory_update_ram μ (write_byte (memory_ram μ) paddr bd))
                    (insert paddr bd memmap) with "[%] [$Haddr $Hmem $Htr]").
        by apply map_Forall_update.
    Qed.

    Lemma write_ram_sound (bytes : nat) :
      ValidContractForeign (sep_contract_write_ram bytes) (write_ram bytes).
    Proof.
      intros Γ es δ ι Heq. destruct_syminstance ι. cbn in *.
      iIntros "[%w H]".
      iApply (wp_lift_atomic_step_no_fork); [auto | ].
      iIntros (? ? ? ? ?) "[Hregs [% (Hmem & %Hmap & Htr)]]".
      iSplitR; first auto.
      repeat iModIntro.
      iIntros.
      eliminate_prim_step Heq.
      iMod (fun_write_ram_works with "[$H $Hmem $Htr]") as "[$ H]"; [auto | now iFrame].
    Qed.

    Lemma mmio_read_sound (bytes : nat) :
     ValidContractForeign (sep_contract_mmio_read bytes) (mmio_read bytes).
    Proof.
      intros Γ es δ ι Heq. destruct_syminstance ι. cbn.
      now iIntros "[%HFalse _]".
    Qed.

    Lemma mmio_write_sound (bytes : nat) :
     ValidContractForeign (sep_contract_mmio_write bytes) (mmio_write bytes).
    Proof.
      intros Γ es δ ι Heq. destruct_syminstance ι. cbn.
      now iIntros "[%HFalse _]".
    Qed.

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

    Lemma within_mmio_sound (bytes : nat):
     ValidContractForeign (sep_contract_within_mmio bytes) (within_mmio bytes).
    Proof.
      intros Γ es δ ι Heq. destruct_syminstance ι. cbn in *.
      iIntros "(Hcurp & Hpmp & Hpmpa & [%acc [%Hpmp _]])".
      iApply (wp_lift_atomic_step_no_fork); [auto | ].
      iIntros (? ? ? ? ?) "[Hregs [% (Hmem & %Hmap & Htr)]]".
      iPoseProof (interp_pmp_fun_within_mmio_spec with "Hpmpa") as "%Hnotmmio"; first eauto.
      iSplitR; first auto.
      repeat iModIntro.
      iIntros. iModIntro.
      eliminate_prim_step Heq.
      iSplit; first auto. iFrame.
      iSplit; [iExists _; auto | ].
      repeat iSplit; auto.
    Qed.

    Lemma decode_sound :
      ValidContractForeign sep_contract_decode decode.
    Proof.
      intros Γ es δ ι Heq. destruct_syminstance ι. cbn.
      iIntros "_". cbn in *.
      iApply (lifting.wp_lift_pure_step_no_fork _ _ ⊤).
      - cbn; auto.
      - intros. eliminate_prim_step Heq; auto.
      - repeat iModIntro. iIntros. eliminate_prim_step Heq; auto.
        destruct (pure_decode _).
        * fold_semWP. now rewrite semWP_fail.
        * iApply wp_value; auto.
    Qed.

    Lemma vector_subrange_sound {n} (e b : nat)
                                {p : IsTrue (0 <=? b)%nat} {q : IsTrue (b <=? e)%nat} {r : IsTrue (e <? n)%nat} :
      ValidContractForeign (@sep_contract_vector_subrange n e b p q r) (vector_subrange e b).
    Proof.
      intros Γ es δ ι Heq.
      destruct_syminstance ι.
      iIntros "_".
      iApply (lifting.wp_lift_pure_step_no_fork _ _ ⊤).
      - cbn; auto.
      - intros. eliminate_prim_step Heq; auto.
      - repeat iModIntro. iIntros. eliminate_prim_step Heq; auto.
      destruct (fun_vector_subrange bv0 e b) eqn:Ev.
      iApply wp_value.
      iSplitL; first iPureIntro; auto.
    Qed.

    Lemma foreignSem : ForeignSem.
    Proof.
      intros Δ τ f; destruct f;
        eauto using read_ram_sound, write_ram_sound, mmio_read_sound, mmio_write_sound, within_mmio_sound, decode_sound, vector_subrange_sound.
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
      rewrite pmp_entries_ptsto.
      iIntros "(% & % & % & % & -> & e1 & e2 & e3 & e4)".
      repeat iExists _.
      now iFrame "e1 e2 e3 e4".
    Qed.

    Lemma close_pmp_entries_sound :
      ValidLemma RiscvPmpSpecification.lemma_close_pmp_entries.
    Proof. intros ι; destruct_syminstance ι; cbn; auto. Qed.

    Lemma extract_pmp_ptsto_sound (bytes : nat) :
      ValidLemma (RiscvPmpSpecification.lemma_extract_pmp_ptsto bytes).
    Proof.
      intros ι; destruct_syminstance ι; cbn - [liveAddrs].
      iIntros "[Hmem [[%Hlemin _] [[%Hlemax _] [%Hpmp _]]]]".
      assert (bv.bin paddr + N.of_nat bytes < bv.exp2 xlenbits)%N.
      {
        eapply N.le_lt_trans; last apply lenAddr_rep.
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

    Lemma close_mmio_write_sound (imm : bv 12) (r1 r2 : Reg ty_xlenbits) (width : WordWidth):
      ValidLemma (RiscvPmpSpecification.lemma_close_mmio_write imm r1 r2 width).
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      now iIntros.
    Qed.

    Lemma lemSem : LemmaSem.
    Proof.
      intros Δ [];
        eauto using open_gprs_sound, close_gprs_sound, open_ptsto_instr_sound, close_ptsto_instr_sound, open_pmp_entries_sound, close_pmp_entries_sound, extract_pmp_ptsto_sound, return_pmp_ptsto_sound, close_mmio_write_sound.
    Qed.
  End LemProofs.

End RiscvPmpModel2.
