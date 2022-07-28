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

  Include ProgramLogicOn RiscvPmpBase RiscvPmpProgram RiscvPmpSignature RiscvPmpSpecification.
  Include IrisInstanceWithContracts RiscvPmpBase RiscvPmpProgram RiscvPmpSemantics
      RiscvPmpSignature RiscvPmpSpecification RiscvPmpIrisBase RiscvPmpIrisInstance.

  Lemma read_ram_sound `{sg : sailGS Σ} `{invGS} {Γ es δ} :
    forall paddr w t entries p,
  evals es δ = env.snoc env.nil ("paddr"∷ty_exc_code) paddr
  → ⊢ semTriple δ
        ((⌜Sub_perm Read t⌝ ∧ emp) ∗ reg_pointsTo cur_privilege p ∗
         interp_pmp_entries entries ∗
         (⌜Pmp_access paddr entries p t⌝ ∧ emp) ∗ interp_ptsto paddr w)
        (stm_foreign read_ram es)
        (λ (v : Z) (δ' : CStore Γ),
           ((⌜v = w⌝ ∧ emp) ∗ reg_pointsTo cur_privilege p ∗
            interp_ptsto paddr w ∗
            interp_pmp_entries entries) ∗ ⌜δ' = δ⌝).
  Proof.
    iIntros (paddr w t entries p Heq) "((%Hperm & _) & Hcp & Hes & (%Hpmp & _) & H)".
    rewrite wp_unfold.
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


  Lemma write_ram_sound `{sg : sailGS Σ} `{HGS: invGS} {Γ es δ} :
    forall paddr data t entries p,
      evals es δ =
        env.snoc (env.snoc env.nil ("paddr"∷ty_exc_code) paddr) ("data"∷ty_exc_code) data
      → ⊢ semTriple δ
          ((⌜Sub_perm Write t⌝ ∧ emp) ∗ reg_pointsTo cur_privilege p ∗
                                      interp_pmp_entries entries ∗
                                      (⌜Pmp_access paddr entries p t⌝ ∧ emp) ∗
                                      (∃ v : Z, interp_ptsto paddr v)) (stm_foreign write_ram es)
          (λ (_ : Z) (δ' : CStore Γ),
            (reg_pointsTo cur_privilege p ∗ interp_ptsto paddr data ∗
                          interp_pmp_entries entries) ∗ ⌜δ' = δ⌝).
  Proof.
    iIntros (paddr data t entries p Heq) "((%Hperm & _) & Hcp & Hes & (%Hpmp & _) & H)".
    rewrite wp_unfold.
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

  Lemma decode_sound `{sg : sailGS Σ} `{HGS: invGS} {Γ es δ} :
    forall bv,
      evals es δ = env.snoc env.nil ("bv"∷ty_exc_code) bv
      → ⊢ semTriple δ (⌜true = true⌝ ∧ emp) (stm_foreign decode es)
          (λ (_ : AST) (δ' : CStore Γ), (⌜true = true⌝ ∧ emp) ∗ ⌜δ' = δ⌝).
  Proof.
    iIntros (bv Heq) "%_".
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
    iApply wp_compat_fail.
    iApply wp_value.
    iSplitL; first iPureIntro; auto.
  Qed.

  Lemma foreignSem `{sailGS Σ} : ForeignSem.
  Proof.
    intros Γ τ Δ f es δ.
    destruct f; cbn;
      intros ι; destruct_syminstance ι; cbn in *;
      eauto using read_ram_sound, write_ram_sound, decode_sound.
  Qed.

  Section Lemmas.
    Context `{sg : sailGS Σ}.

    Lemma open_gprs_sound :
      ValidLemma RiscvPmpSpecification.lemma_open_gprs.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      unfold interp_gprs, reg_file.
      rewrite big_sepS_list_to_set; [|apply finite.NoDup_enum]; cbn.
      iIntros "[_ [Hx1 [Hx2 [Hx3 [Hx4 [Hx5 [Hx6 [Hx7 _]]]]]]]]". iFrame.
    Qed.

    Lemma close_gprs_sound :
      ValidLemma RiscvPmpSpecification.lemma_close_gprs.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      unfold interp_gprs, reg_file.
      iIntros "[Hx1 [Hx2 [Hx3 [Hx4 [Hx5 [Hx6 Hx7]]]]]]".
      iApply big_sepS_list_to_set; [apply finite.NoDup_enum|].
      cbn; iFrame. eauto using 0%Z.
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
      iIntros "[Hcfg0 [Haddr0 [Hcfg1 [Haddr1 _]]]]".
      iAccu.
    Qed.

    Lemma update_pmp_entries_sound :
      ValidLemma RiscvPmpSpecification.lemma_update_pmp_entries.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      iIntros "[Hcfg0 [Haddr0 [Hcfg1 [Haddr1 Hpriv]]]]".
      iFrame.
    Qed.

    Lemma in_liveAddrs : forall (addr : Addr),
        (minAddr <= addr)%Z ->
        (addr <= maxAddr)%Z ->
        addr ∈ liveAddrs.
    Proof.
      intros addr Hmin Hmax.
      unfold liveAddrs.
      apply elem_of_seqZ.
      split; auto.
      rewrite Z.add_assoc.
      rewrite Zplus_minus.
      apply Zle_lt_succ; auto.
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
      transitivity (seqZ minAddr (addr - minAddr) ++ seqZ (addr) (maxAddr - addr + 1)).
      refine (eq_trans _ (eq_trans (seqZ_app minAddr (addr - minAddr) (maxAddr - addr + 1) _ _) _));
        do 2 (f_equal; try lia).
      f_equal; cbn.
      refine (eq_trans (seqZ_cons _ _ _) _); try lia.
      do 2 f_equal; lia.
    Qed.

    Lemma extract_pmp_ptsto_sound :
      ValidLemma RiscvPmpSpecification.lemma_extract_pmp_ptsto.
    Proof.
      intros ι; destruct_syminstance ι; cbn.
      rewrite ?Z.leb_le.
      iIntros "[Hentries [Hmem [[%Hlemin _] [[%Hlemax _] [%Hpmp _]]]]]".
      iSplitL "Hentries"; try done.
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
      iIntros "[Hentries [Hwithout Hptsto]]".
      iSplitL "Hentries"; first iFrame.
      unfold interp_pmp_addr_access_without.
      iApply ("Hwithout" with "Hptsto").
    Qed.

  End Lemmas.

  Lemma lemSem `{sailGS Σ} : LemmaSem.
  Proof.
    intros Δ [];
      eauto using open_gprs_sound, close_gprs_sound, open_pmp_entries_sound,
      close_pmp_entries_sound, update_pmp_entries_sound, extract_pmp_ptsto_sound, return_pmp_ptsto_sound.
  Qed.

End RiscvPmpModel2.
