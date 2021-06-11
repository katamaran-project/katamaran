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

From MinimalCaps Require Import
     Machine Contracts.

From Coq Require Import
     Init.Nat
     ZArith.Znat
     Program.Tactics
     Strings.String
     ZArith.ZArith
     micromega.Lia.

From Equations Require Import
     Equations.

From MicroSail Require Import
     Sep.Spec
     Symbolic.Mutator
     Syntax.

From MicroSail Require Environment.
From MicroSail Require Iris.Model.
From MicroSail Require Sep.Logic.
From iris.base_logic Require lib.gen_heap lib.iprop.
From iris.base_logic Require Export invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac.
From iris.program_logic Require Import weakestpre adequacy.
From iris.proofmode Require Import tactics.
From stdpp Require namespaces fin_maps.

Require Import Coq.Program.Equality.

Set Implicit Arguments.

Module gh := iris.base_logic.lib.gen_heap.

Module MinCapsModel.
  Import MicroSail.Iris.Model.

  Module MinCapsIrisHeapKit <: IrisHeapKit MinCapsTermKit MinCapsProgramKit MinCapsAssertionKit MinCapsSymbolicContractKit.

    Variable maxAddr : nat.

    Module IrisRegs := IrisRegisters MinCapsTermKit MinCapsProgramKit MinCapsAssertionKit MinCapsSymbolicContractKit.
    Export IrisRegs.

    Section WithIrisNotations.

    Import iris.bi.interface.
    Import iris.bi.big_op.
    Import iris.base_logic.lib.iprop.
    Import iris.base_logic.lib.gen_heap.

    Definition MemVal : Set := Z + Capability.

    Class mcMemG Σ := McMemG {
                          (* ghost variable for tracking state of registers *)
                          mc_ghG :> gh.gen_heapG Z MemVal Σ;
                          mc_invNs : namespace
                        }.

    Definition memPreG : gFunctors -> Set := fun Σ => gh.gen_heapPreG Z MemVal Σ.
    Definition memG : gFunctors -> Set := mcMemG.
    Definition memΣ : gFunctors := gh.gen_heapΣ Z MemVal.

    Definition memΣ_PreG : forall {Σ}, subG memΣ Σ -> memPreG Σ := fun {Σ} => gh.subG_gen_heapPreG (Σ := Σ) (L := Z) (V := MemVal).

    Definition mem_inv : forall {Σ}, memG Σ -> Memory -> iProp Σ :=
      fun {Σ} hG μ =>
        (∃ memmap, gen_heap_interp (hG := mc_ghG (mcMemG := hG)) memmap ∗
                                ⌜ map_Forall (fun a v => μ a = v) memmap ⌝
        )%I.

    Definition liveAddrs : list Addr := seqZ 0 maxAddr.
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

    Definition mem_res : forall {Σ}, memG Σ -> Memory -> iProp Σ :=
      fun {Σ} hG μ =>
        ([∗ map] l↦v ∈ initMemMap μ, mapsto (hG := mc_ghG (mcMemG := hG)) l (DfracOwn 1) v) %I.

    Lemma mem_inv_init : forall Σ (μ : Memory), memPreG Σ ->
        ⊢ |==> ∃ memG : memG Σ, (mem_inv memG μ ∗ mem_res memG μ)%I.
    Proof.
      iIntros (Σ μ gHP).

      iMod (gen_heap_init (gen_heapPreG0 := gHP) (L := Addr) (V := MemVal) empty) as (gH) "[inv _]".
      pose (memmap := initMemMap μ).
      iMod (gen_heap_alloc_big empty memmap (map_disjoint_empty_r memmap) with "inv") as "(inv & res & _)".
      iModIntro.

      rewrite (right_id empty union memmap).

      iExists (McMemG gH (nroot .@ "addr_inv")).
      iFrame.
      iExists memmap.
      iFrame.
      iPureIntro.
      apply initMemMap_works.
    Qed.

    Definition MinCaps_ptsreg `{sailRegG Σ} (reg : RegName) (v : Z + Capability) : iProp Σ :=
      match reg with
      | R0 => reg_pointsTo reg0 v
      | R1 => reg_pointsTo reg1 v
      | R2 => reg_pointsTo reg2 v
      | R3 => reg_pointsTo reg3 v
      end.

    Lemma MinCaps_ptsreg_regtag_to_reg `{sailRegG Σ} (reg : RegName) (v : Z + Capability) :
      MinCaps_ptsreg reg v = reg_pointsTo (MinCapsSymbolicContractKit.regtag_to_reg reg) v.
    Proof.
      by destruct reg.
    Qed.

    Definition region_addrs (b e : Addr) : list Addr :=
      filter (fun a => and (b ≤ a)%Z (a ≤ e)%Z) liveAddrs.

    Lemma element_of_region_addrs (a b e : Addr) :
      b ∈ liveAddrs → e ∈ liveAddrs →
      (b <= a)%Z /\ (a <= e)%Z ->
      a ∈ region_addrs b e.
    Proof.
      intros Hb He [Hba Hae].
      apply elem_of_list_filter.
      repeat (split; try assumption).
      apply elem_of_seqZ in Hb.
      apply elem_of_seqZ in He.
      apply elem_of_seqZ.
      split.
      - destruct Hb as [Hb _].
        eapply Z.le_trans; first apply Hb.
        assumption.
      - destruct He as [_ He].
        eapply Z.le_lt_trans; first apply Hae.
        assumption.
    Qed.

    Context {Σ : gFunctors}.
    Notation D := ((leibnizO MemVal) -n> iPropO Σ). (* TODO: try -d>, drop leibnizO, might not need λne *)
    Implicit Type w : (leibnizO MemVal).

    (* Copied from github.com/logsem/cerise *)
    (* TODO: include copyright notice =) *)
    Ltac auto_equiv :=
      (* Deal with "pointwise_relation" *)
      repeat lazymatch goal with
             | |- pointwise_relation _ _ _ _ => intros ?
             end;
      (* Normalize away equalities. *)
      repeat match goal with
             | H : _ ≡{_}≡ _ |-  _ => apply (discrete_iff _ _) in H
             | H : _ ≡ _ |-  _ => apply leibniz_equiv in H
             | _ => progress simplify_eq
             end;
      (* repeatedly apply congruence lemmas and use the equalities in the hypotheses. *)
      try (f_equiv; fast_done || auto_equiv).

    Ltac solve_proper ::= (repeat intros ?; simpl; auto_equiv).

    Program Definition MinCaps_ref_inv `{sailRegG Σ} `{invG Σ} {mG : memG Σ} (a : Addr) : D -n> iPropO Σ :=
      λne P, (∃ w, mapsto (hG := mc_ghG (mcMemG := mG)) a (DfracOwn 1) w ∗ P w)%I.
    Solve All Obligations with solve_proper.

    Program Definition MinCaps_csafe `{sailRegG Σ} `{invG Σ} {mG : memG Σ} (safe : D) : D :=
      λne w,
        (match w with
        | inr (MkCap O b e a) => True%I
        | inr (MkCap R b e a) =>
          (* TODO: easiest: (b ≤ e -> safe ...) ∨ (e < b -> True), check what CHERI does *)
          ⌜ b ∈ liveAddrs /\ e ∈ liveAddrs ⌝ ∗
                               [∗ list] a ∈ (region_addrs b e), inv (mc_invNs (mcMemG := mG) .@ a) (MinCaps_ref_inv (mG := mG) a safe)
        | inr (MkCap RW b e a) =>
          ⌜ b ∈ liveAddrs /\ e ∈ liveAddrs ⌝ ∗
                               [∗ list] a ∈ (region_addrs b e), inv (mc_invNs (mcMemG := mG) .@ a) (MinCaps_ref_inv (mG := mG) a safe)
        | inl _ => False
        end)%I.

    Program Definition MinCaps_safe1 `{sailRegG Σ} `{invG Σ} {mG : memG Σ} (safe : D) : D :=
      λne w,
        (match w with
        | inl z => True
        | inr c => MinCaps_csafe (mG := mG) safe w
        end)%I.

    Global Instance MinCaps_csafe_contractive `{sailRegG Σ} `{invG Σ} {mG : memG Σ} :
      Contractive (MinCaps_csafe (mG := mG)).
    Proof.
      intros n x y Hdist w.
      unfold MinCaps_csafe.
      destruct w; first by intuition.
      destruct c.
      destruct cap_permission; first auto; solve_proper_prepare; solve_contractive.
    Qed.

    Global Instance MinCaps_safe1_contractive `{sailRegG Σ} `{invG Σ} {mG : memG Σ} :
      Contractive (MinCaps_safe1 (mG := mG)).
    Proof.
      intros n x y Hdist w.
      unfold MinCaps_safe1.
      destruct w; first by intuition.
      by apply MinCaps_csafe_contractive.
    Qed.

    Lemma fixpoint_MinCaps_safe1_eq `{sailRegG Σ} `{invG Σ} {mG : memG Σ} (w : leibnizO MemVal) :
      fixpoint (MinCaps_safe1 (mG := mG)) w ≡ MinCaps_safe1 (mG := mG) (fixpoint (MinCaps_safe1 (mG := mG))) w.
    Proof. exact: (fixpoint_unfold (MinCaps_safe1 (mG := mG)) w). Qed.

    Definition MinCaps_safe `{sailRegG Σ} `{invG Σ} {mG : memG Σ} : D :=
      λne w, (fixpoint (MinCaps_safe1 (mG := mG))) w.

    Lemma le_liveAddrs1 (a a' : Addr) :
      (0 <= a')%Z /\ (a' <= a)%Z /\ a ∈ liveAddrs ->
      a' ∈ liveAddrs.
    Proof.
      intros [H0a' [Hle Hin]].
      apply elem_of_seqZ in Hin.
      destruct Hin as [H0 Hm].
      rewrite elem_of_seqZ.
      split.
      - assumption.
      - eapply Z.le_lt_trans; eassumption.
    Qed.

    Lemma le_liveAddrs2 (a a' : Addr) :
      (a' < maxAddr)%Z /\ (a <= a')%Z /\ a ∈ liveAddrs ->
      a' ∈ liveAddrs.
    Proof.
      intros [Ha'm [Hle Hin]].
      apply elem_of_seqZ in Hin.
      destruct Hin as [H0 Hm].
      rewrite elem_of_seqZ.
      split.
      - eapply Z.le_trans; eassumption.
      - rewrite Z.add_comm.
        rewrite Z.add_0_r.
        assumption.
    Qed.

    Lemma region_addrs_submseteq `{sailRegG Σ} `{invG Σ} {mG : memG Σ} (b' e' b e : Addr) :
      ⊢ ⌜ (b <= b')%Z /\ (e' <= e)%Z ⌝ -∗
                               ([∗ list] a ∈ (region_addrs b e), inv (mc_invNs (mcMemG := mG) .@ a) (∃ w, mapsto (hG := mc_ghG (mcMemG := mG)) a (DfracOwn 1) w ∗ fixpoint (MinCaps_safe1 (mG := mG)) w))%I -∗
                               ([∗ list] a ∈ (region_addrs b' e'), inv (mc_invNs (mcMemG := mG) .@ a) (∃ w, mapsto (hG := mc_ghG (mcMemG := mG)) a (DfracOwn 1) w ∗ fixpoint (MinCaps_safe1 (mG := mG)) w))%I.
    Proof.
      iIntros "[% %] Hregion".
      iApply (big_sepL_submseteq _ _ (region_addrs b e)).
      unfold region_addrs.
      induction liveAddrs.
      - cbn; trivial.
      - cbn.
        destruct (decide ((b' ≤ a)%Z ∧ (a ≤ e')%Z));
          destruct (decide ((b ≤ a)%Z ∧ (a ≤ e)%Z));
          trivial.
        + apply submseteq_skip; trivial.
        + destruct a0 as [Hb' He'].
          apply (Z.le_trans b _ _) in Hb'; try assumption.
          apply (Z.le_trans _ _ e) in He'; try assumption.
          exfalso; apply n; split; assumption.
        + apply submseteq_cons; trivial.
      - iAssumption.
    Qed.

    Lemma safe_sub_range `{sailRegG Σ} `{invG Σ} {mG : memG Σ} (b' e' b e : Addr) :
      forall p a,
      ⊢ ⌜ (b <= b')%Z /\ (e' <= e)%Z ⌝ -∗
                               MinCaps_safe (mG := mG)
                               (inr {| cap_permission := p; cap_begin := b; cap_end := e; cap_cursor := a |}) -∗
                               MinCaps_safe (mG := mG)
                               (inr {| cap_permission := p; cap_begin := b'; cap_end := e'; cap_cursor := a |}).
    Proof.
      simpl.
      iIntros (p a) "[% %] Hsafe".
      do 2 rewrite fixpoint_MinCaps_safe1_eq.
      (* the following two asserts are temporary, this information needs to become generally available (A positive, finite addr type would solve this) *)
      assert (Hb'm: (b' < maxAddr)%Z). admit. (* TODO: "by lia" all the things *)
      assert (H0e': (0 <= e')%Z). admit.
      destruct p; try by iFrame.
      - iDestruct "Hsafe" as "[[% %] H]".
        iSplitR.
        + iPureIntro; split.
          eapply le_liveAddrs2; (repeat split); eassumption.
          eapply le_liveAddrs1; (repeat split); eassumption.
        + iApply (region_addrs_submseteq $! (conj H1 H2) with "H").
      - iDestruct "Hsafe" as "[[% %] H]".
        iSplitR.
        + iPureIntro; split.
          eapply le_liveAddrs2; (repeat split); eassumption.
          eapply le_liveAddrs1; (repeat split); eassumption.
        + iApply (region_addrs_submseteq $! (conj H1 H2) with "H").
    Admitted.

    Lemma specialize_range `{sailRegG Σ} `{invG Σ} {mG : memG Σ} (b e addr : Addr) :
      ⊢ ⌜ (b <= addr)%Z /\ (addr <= e)%Z ⌝ -∗
        (⌜ b ∈ liveAddrs /\ e ∈ liveAddrs ⌝ ∗
          [∗ list] a ∈ (region_addrs b e), inv (mc_invNs (mcMemG := mG) .@ a) (∃ w, mapsto (hG := mc_ghG (mcMemG := mG)) a (DfracOwn 1) w ∗ fixpoint (MinCaps_safe1 (mG := mG)) w))%I -∗
        (inv (mc_invNs (mcMemG := mG) .@ addr) (∃ w, mapsto (hG := mc_ghG (mcMemG := mG)) addr (DfracOwn 1) w ∗ fixpoint (MinCaps_safe1 (mG := mG)) w))%I.
    Proof.
      iIntros "[% %] [[% %] Hrange]".
      iApply (big_sepL_elem_of with "Hrange").
      apply element_of_region_addrs; try assumption.
      split; assumption.
    Qed.

    Import EnvNotations.

    Definition MinCaps_subperm {Σ} (p p' : Permission) : iProp Σ :=
      match p with
      | O => True
      | R => match p' with
            | O => False
            | _ => True
            end
      | RW => match p' with
             | RW => True
             | _ => False
             end
      end.

    Definition luser_inst `{sailRegG Σ} `{invG Σ} (p : Predicate) (ts : Env Lit (MinCapsAssertionKit.𝑷_Ty p)) (mG : memG Σ) : iProp Σ :=
      (match p return Env Lit (MinCapsAssertionKit.𝑷_Ty p) -> iProp Σ with
      | ptsreg => fun ts => MinCaps_ptsreg (env_head (env_tail ts)) (env_head ts)
      | ptsto => fun ts => mapsto (hG := mc_ghG (mcMemG := mG)) (env_head (env_tail ts)) (DfracOwn 1) (env_head ts)
      | safe => fun ts => MinCaps_safe (mG := mG) (env_head ts)
      | csafe => fun ts => MinCaps_safe (mG := mG) (inr (env_head ts))
      | subperm => fun ts => MinCaps_subperm (env_head (env_tail ts)) (env_head ts) 
      | dummy => fun ts => True%I
      end) ts.

    Global Instance MinCaps_safe_Persistent `{sailRegG Σ} `{invG Σ} {mG : memG Σ} (w : leibnizO MemVal) : Persistent (MinCaps_safe (mG := mG) w).
    Proof. destruct w; simpl; rewrite fixpoint_MinCaps_safe1_eq; simpl; first apply _.
           destruct c; destruct cap_permission; apply _. Qed.

    End WithIrisNotations.
  End MinCapsIrisHeapKit.

  Module Soundness := IrisSoundness MinCapsTermKit MinCapsProgramKit MinCapsAssertionKit MinCapsSymbolicContractKit MinCapsIrisHeapKit.
  Export Soundness.

  Import EnvNotations.

  Lemma gen_dummy_sound `{sg : sailG Σ} `{invG} {Γ es δ} :
    forall c : Lit ty_cap,
    evals es δ = env_snoc env_nil (_ , ty_cap) c
    → ⊢ semTriple δ (⌜is_true true⌝ ∧ emp)
        (use lemma gen_dummy es)
          (λ (_ : ()) (δ' : CStore Γ),
             True ∗ ⌜δ' = δ⌝).
  Proof.
    iIntros (c Heq) "_".
    rewrite wp_unfold.
    iIntros (σ' ks1 ks n) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; first by intuition.
    iIntros (e2 σ'' efs) "%".
    cbn in H0.
    dependent elimination H0.
    dependent elimination s.
    rewrite Heq in f1.
    cbn in f1. 
    dependent elimination f1.
    do 2 iModIntro.
    iMod "Hclose" as "_".
    iModIntro.
    iFrame.
    iSplitL; trivial.
    iApply wp_value.
    iSimpl; iSplitL; trivial.
  Qed.

  Lemma dI_sound `{sg : sailG Σ} `{invG} {Γ es δ} :
    forall code : Lit ty_int,
    evals es δ = env_snoc env_nil (_ , ty_int) code
    → ⊢ semTriple δ (⌜is_true true⌝ ∧ emp) (stm_call_external dI es)
          (λ (v : Lit ty_instr) (δ' : CStore Γ),
             (⌜is_true true⌝ ∧ emp) ∗ ⌜δ' = δ⌝).
  Proof.
    iIntros (code Heq) "_".
    rewrite wp_unfold.
    iIntros (σ' ks1 ks n) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; first by intuition.
    iIntros (e2 σ'' efs) "%".
    cbn in H.
    dependent elimination H0.
    dependent elimination s.
    rewrite Heq in f1.
    cbn in f1. destruct f1 as [res' e].
    dependent elimination e.
    do 2 iModIntro.
    iMod "Hclose" as "_".
    iModIntro.
    iFrame.
    iSplitL; trivial.
    destruct res.
    - iApply wp_compat_fail.
    - iApply wp_value.
      cbn.
      iSplit; trivial.
  Qed.

  Lemma open_ptsreg_sound `{sg : sailG Σ} {Γ es δ} :
    forall reg w,
      let ι := env_snoc (env_snoc env_nil (_ , ty_lv) reg)
                        ("w" , ty_word) w in
      evals es δ = env_tail ι
      → ⊢ semTriple δ
          (MinCapsIrisHeapKit.MinCaps_ptsreg reg w)
          (stm_call_external (ghost open_ptsreg) es)
          (λ (v : ()) (δ' : CStore Γ),
             (MinCapsSymbolicContractKit.ASS.interpret_assertion
                  match (ι ‼ "reg")%exp with
                  | R0 =>
                      MinCapsSymbolicContractKit.ASS.asn_chunk
                        (MinCapsSymbolicContractKit.ASS.chunk_ptsreg reg0 (term_var "w"))
                  | R1 =>
                      MinCapsSymbolicContractKit.ASS.asn_chunk
                        (MinCapsSymbolicContractKit.ASS.chunk_ptsreg reg1 (term_var "w"))
                  | R2 =>
                      MinCapsSymbolicContractKit.ASS.asn_chunk
                        (MinCapsSymbolicContractKit.ASS.chunk_ptsreg reg2 (term_var "w"))
                  | R3 =>
                      MinCapsSymbolicContractKit.ASS.asn_chunk
                        (MinCapsSymbolicContractKit.ASS.chunk_ptsreg reg3 (term_var "w"))
                  end (ι ► (("result", ty_unit) ↦ v))) ∗ ⌜δ' = δ⌝).
  Proof.
    iIntros (reg w ι  Heq) "Hpre".
    rewrite wp_unfold.
    iIntros (σ' ks1 ks n) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; first by intuition.
    iIntros (e2 σ'' efs) "%".
    cbn in H.
    dependent elimination H.
    dependent elimination s.
    rewrite Heq in f1.
    cbn in f1.
    dependent elimination f1.
    do 2 iModIntro.
    iMod "Hclose" as "_".
    iModIntro.
    iFrame.
    iSplitL; trivial.
    iApply wp_value.
    cbn.
    destruct reg; iSplit; trivial.
  Qed.

  Lemma close_ptsreg_sound `{sg : sailG Σ} {Γ R es δ} :
    forall w : Lit ty_word,
      evals es δ = env_nil
      → ⊢ semTriple δ
          (MinCapsIrisHeapKit.IrisRegs.reg_pointsTo (MinCapsSymbolicContractKit.regtag_to_reg R)
                                                    w)
          (stm_call_external (ghost (close_ptsreg R)) es)
          (λ (_ : ()) (δ' : CStore Γ),
           MinCapsIrisHeapKit.MinCaps_ptsreg R w
                                             ∗ ⌜δ' = δ⌝).
  Proof.
    iIntros (w eq) "ptsto".
    destruct (nilView es). clear eq.
    cbn [env_lookup inctx_case_snoc].
    rewrite wp_unfold.
    iIntros (σ' ks1 ks n) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; first by intuition.
    iIntros (e2 σ'' efs) "%".
    cbn in H.
    dependent elimination H.
    dependent elimination s.
    cbn in f1.
    dependent elimination f1.
    iModIntro. iModIntro.
    iMod "Hclose" as "_".
    iModIntro.
    iFrame.
    iSplitL; trivial.
    iApply wp_value.
    cbn.
    rewrite MinCapsIrisHeapKit.MinCaps_ptsreg_regtag_to_reg.
    by iFrame.
  Qed.

  Lemma int_safe_sound `{sg : sailG Σ} {Γ es δ} :
    forall i,
      evals es δ = env_snoc env_nil (_ , ty_addr) i
      → ⊢ semTriple δ
          (⌜is_true true⌝ ∧ emp)
          (stm_call_external (ghost int_safe) es)
          (λ (v : ()) (δ' : CStore Γ),
           ((⌜v = tt⌝ ∧ emp)
              ∗ MinCapsIrisHeapKit.MinCaps_safe (mG := sailG_memG) (inl i))
             ∗ ⌜δ' = δ⌝).
  Proof.
    iIntros (i Heq) "_".
    rewrite wp_unfold.
    iIntros (σ' ks1 ks n) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; first by intuition.
    iIntros (e2 σ'' efs) "%".
    cbn in H.
    dependent elimination H.
    dependent elimination s.
    rewrite Heq in f1.
    cbn in f1.
    dependent elimination f1.
    do 2 iModIntro.
    iMod "Hclose" as "_".
    iModIntro.
    iFrame.
    iSplitL; [|cbn; trivial].
    iApply wp_value.
    iSimpl.
    iSplitL; [|cbn; trivial].
    iSplitL; first (cbn; trivial).
    rewrite MinCapsIrisHeapKit.fixpoint_MinCaps_safe1_eq; auto.
  Qed.

  Lemma lift_csafe_sound `{sg : sailG Σ} {Γ es δ} :
    forall c,
      evals es δ = env_snoc env_nil (_ , ty_cap) c
      → ⊢ semTriple δ
          (MinCapsIrisHeapKit.MinCaps_safe (mG := sailG_memG) (inr c))
          (stm_call_external (ghost lift_csafe) es)
          (λ (v : ()) (δ' : CStore Γ),
           ((⌜v = tt⌝ ∧ emp)
             ∗ MinCapsIrisHeapKit.MinCaps_safe (mG := sailG_memG) (inr c))
             ∗ ⌜δ' = δ⌝).
  Proof.
    iIntros (c Heq) "Hpre".
    rewrite wp_unfold.
    iIntros (σ' ks1 ks n) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; first by intuition.
    iIntros (e2 σ'' efs) "%".
    cbn in H.
    dependent elimination H.
    dependent elimination s.
    rewrite Heq in f1.
    cbn in f1.
    dependent elimination f1.
    do 2 iModIntro.
    iMod "Hclose" as "_".
    iModIntro.
    iFrame.
    iSplitL; [|cbn;trivial].
    iApply wp_value.
    cbn.
    by iFrame.
  Qed.

  Lemma duplicate_safe_sound `{sg : sailG Σ} {Γ es δ} :
    forall w,
      evals es δ = env_snoc env_nil (_ , ty_word) w
      → ⊢ semTriple δ
          (MinCapsIrisHeapKit.MinCaps_safe (mG := sailG_memG) w)
          (stm_call_external (ghost duplicate_safe) es)
          (λ (v : ()) (δ' : CStore Γ),
           (((⌜v = tt⌝ ∧ emp)
               ∗ MinCapsIrisHeapKit.MinCaps_safe (mG := sailG_memG) w)
              ∗ MinCapsIrisHeapKit.MinCaps_safe (mG := sailG_memG) w)
             ∗ ⌜δ' = δ⌝).
  Proof.
    iIntros (w Heq) "#Hsafe".
    rewrite wp_unfold.
    iIntros (σ' ks1 ks n) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; first by intuition.
    iIntros (e2 σ'' efs) "%".
    cbn in H.
    dependent elimination H.
    dependent elimination s.
    rewrite Heq in f1.
    cbn in f1.
    dependent elimination f1.
    do 2 iModIntro.
    iMod "Hclose" as "_".
    iModIntro.
    iFrame.
    iSplitL; [|cbn;trivial].
    iApply wp_value.
    cbn.
    iSplitL; trivial.
    iSplitL; try iAssumption.
    iSplitL; trivial; try iAssumption.
  Qed.
  
  Lemma specialize_safe_to_cap_sound `{sg : sailG Σ} {Γ es δ} :
    ∀ c : Lit ty_cap,
      evals es δ = (env_snoc env_nil (_ , ty_cap) c)
      → ⊢ semTriple δ
          (MinCapsIrisHeapKit.MinCaps_safe (mG := sailG_memG) (inr c))
          (stm_call_external (ghost specialize_safe_to_cap) es)
          (λ (v : ()) (δ' : CStore Γ),
           ((⌜v = tt⌝ ∧ emp)
              ∗ MinCapsIrisHeapKit.MinCaps_safe (mG := sailG_memG) (inr c))
             ∗ ⌜δ' = δ⌝).
  Proof.
    iIntros (c Heq) "Hsafe".
    rewrite wp_unfold.
    iIntros (σ' ks1 ks n) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; first by intuition.
    iIntros (e2 σ'' efs) "%".
    cbn in H.
    dependent elimination H.
    dependent elimination s.
    rewrite Heq in f1.
    cbn in f1.
    dependent elimination f1.
    do 2 iModIntro.
    iMod "Hclose" as "_".
    iModIntro.
    iFrame.
    iSplitL; [|cbn;trivial].
    iApply wp_value.
    cbn.
      by iFrame.
  Qed.

  Lemma csafe_move_cursor_sound `{sg : sailG Σ} {Γ es δ} :
    forall p b e a a',
      evals es δ = env_snoc
                     (env_snoc env_nil (_ , ty_cap)
                               {| cap_permission := p;
                                  cap_begin := b;
                                  cap_end := e;
                                  cap_cursor := a' |})
                     (_ , ty_cap)
                     {| cap_permission := p;
                        cap_begin := b;
                        cap_end := e;
                        cap_cursor := a |}
      → ⊢ semTriple δ
          (MinCapsIrisHeapKit.MinCaps_safe (mG := sailG_memG)
                                            (inr {|
                                              cap_permission := p;
                                              cap_begin := b;
                                              cap_end := e;
                                              cap_cursor := a |}))
          (stm_call_external (ghost csafe_move_cursor) es)
          (λ (v0 : ()) (δ' : CStore Γ),
           (((⌜v0 = tt⌝ ∧ emp)
               ∗ MinCapsIrisHeapKit.MinCaps_safe (mG := sailG_memG)
               (inr {| cap_permission := p;
                  cap_begin := b;
                  cap_end := e;
                  cap_cursor := a |}))
              ∗ MinCapsIrisHeapKit.MinCaps_safe (mG := sailG_memG)
              (inr {| cap_permission := p;
                      cap_begin := b;
                      cap_end := e;
                      cap_cursor := a' |})) ∗ ⌜δ' = δ⌝).
  Proof.
    iIntros (p b e a a' Heq) "#Hcsafe".
    rewrite wp_unfold.
    iIntros (σ' ks1 ks n) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; first by intuition.
    iIntros (e2 σ'' efs) "%".
    cbn in H.
    dependent elimination H.
    dependent elimination s.
    rewrite Heq in f1.
    cbn in f1.
    dependent elimination f1.
    do 2 iModIntro.
    iMod "Hclose" as "_".
    iModIntro.
    iFrame.
    iSplitL; trivial.
    iApply wp_value.
    cbn.
    repeat (iSplitL; trivial).
    do 2 rewrite MinCapsIrisHeapKit.fixpoint_MinCaps_safe1_eq.
    unfold MinCapsIrisHeapKit.MinCaps_safe1.
    destruct p; auto.
  Qed.

  Lemma csafe_sub_perm_sound `{sg : sailG Σ} {Γ es δ} :
    forall p p' b e a,
      evals es δ = env_snoc
                     (env_snoc env_nil (_ , ty_cap)
                               {| cap_permission := p';
                                  cap_begin := b;
                                  cap_end := e;
                                  cap_cursor := a |})
                     (_ , ty_cap)
                     {| cap_permission := p;
                        cap_begin := b;
                        cap_end := e;
                        cap_cursor := a |}
      → ⊢ semTriple δ
          (MinCapsIrisHeapKit.MinCaps_safe (mG := sailG_memG)
                                            (inr {|
                                              cap_permission := p;
                                              cap_begin := b;
                                              cap_end := e;
                                              cap_cursor := a |})
          ∗ MinCapsIrisHeapKit.MinCaps_subperm p' p)
          (stm_call_external (ghost csafe_sub_perm) es)
          (λ (v0 : ()) (δ' : CStore Γ),
           (((⌜v0 = tt⌝ ∧ emp)
               ∗ MinCapsIrisHeapKit.MinCaps_safe (mG := sailG_memG)
               (inr {| cap_permission := p;
                  cap_begin := b;
                  cap_end := e;
                  cap_cursor := a |}))
              ∗ MinCapsIrisHeapKit.MinCaps_safe (mG := sailG_memG)
              (inr {| cap_permission := p';
                      cap_begin := b;
                      cap_end := e;
                      cap_cursor := a |})) ∗ ⌜δ' = δ⌝).
  Proof.
    iIntros (p p' b e a Heq) "[#Hcsafe Hp]".
    rewrite wp_unfold.
    iIntros (σ' ks1 ks n) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; first by intuition.
    iIntros (e2 σ'' efs) "%".
    cbn in H.
    dependent elimination H.
    dependent elimination s.
    rewrite Heq in f1.
    cbn in f1.
    dependent elimination f1.
    do 2 iModIntro.
    iMod "Hclose" as "_".
    iModIntro.
    iFrame.
    iSplitL; trivial.
    iApply wp_value.
    cbn.
    iSplitL; trivial.
    iSplitR "Hp"; trivial.
    iSplitL; trivial.
    do 2 rewrite MinCapsIrisHeapKit.fixpoint_MinCaps_safe1_eq.
    destruct p; destruct p'; trivial.
  Qed.

  Lemma csafe_within_range_sound `{sg : sailG Σ} {Γ es δ} :
    forall p b b' e e' a,
      evals es δ = env_snoc
                     (env_snoc env_nil (_ , ty_cap)
                               {| cap_permission := p;
                                  cap_begin := b';
                                  cap_end := e';
                                  cap_cursor := a |})
                     (_ , ty_cap)
                     {| cap_permission := p;
                        cap_begin := b;
                        cap_end := e;
                        cap_cursor := a |}
      → ⊢ semTriple δ
          ((MinCapsIrisHeapKit.MinCaps_safe (mG := sailG_memG)
                                            (inr {|
                                              cap_permission := p;
                                              cap_begin := b;
                                              cap_end := e;
                                              cap_cursor := a |})
                                            ∗ True)
        ∗ ⌜is_true ((b <=? b')%Z && (e' <=? e)%Z)⌝ ∧ emp)
          (use lemma csafe_within_range es)
          (λ (v0 : ()) (δ' : CStore Γ),
           (((⌜v0 = tt⌝ ∧ emp)
               ∗ MinCapsIrisHeapKit.MinCaps_safe (mG := sailG_memG)
               (inr {| cap_permission := p;
                  cap_begin := b;
                  cap_end := e;
                  cap_cursor := a |}))
              ∗ MinCapsIrisHeapKit.MinCaps_safe (mG := sailG_memG)
              (inr {| cap_permission := p;
                      cap_begin := b';
                      cap_end := e';
                      cap_cursor := a |})) ∗ ⌜δ' = δ⌝).
  Proof.
    iIntros (p b b' e e' a Heq) "[#[Hcsafe _] [% %]]".
    clear H0.
    rewrite wp_unfold.
    iIntros (σ' ks1 ks n) "Hregs".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; first by intuition.
    iIntros (e2 σ'' efs) "%".
    cbn in H.
    dependent elimination H0.
    dependent elimination s.
    rewrite Heq in f1.
    cbn in f1.
    dependent elimination f1.
    do 2 iModIntro.
    iMod "Hclose" as "_".
    iModIntro.
    iFrame.
    iSplitL; trivial.
    iApply wp_value.
    cbn.
    iSplitL; trivial.
    iSplitL; trivial.
    iSplitL; trivial.
    unfold is_true in H;
      apply andb_prop in H;
      destruct H as [Hb He];
      apply Zle_is_le_bool in Hb;
      apply Zle_is_le_bool in He.
    iApply (MinCapsIrisHeapKit.safe_sub_range $! (conj Hb He) with "Hcsafe").
  Qed.

  Lemma rM_sound `{sg : sailG Σ} `{invG} {Γ es δ} :
    forall a(p : Lit ty_perm) (b e : Lit ty_addr),
      evals es δ = env_snoc env_nil (_ , ty_addr) a
    → ⊢ semTriple δ
        ((MinCapsIrisHeapKit.MinCaps_safe (mG := sailG_memG)
                                          (inr {|
                                               cap_permission := p;
                                               cap_begin := b;
                                               cap_end := e;
                                               cap_cursor := a |})
           ∗ MinCapsIrisHeapKit.MinCaps_subperm R p)
           ∗ ⌜is_true ((b <=? a)%Z && (a <=? e)%Z)⌝ ∧ emp)
        (stm_call_external rM es)
        (λ (v3 : Z + Capability) (δ' : CStore Γ),
         (MinCapsIrisHeapKit.MinCaps_safe (mG := sailG_memG)
                                          (inr {| cap_permission := p;
                                                  cap_begin := b;
                                                  cap_end := e;
                                                  cap_cursor := a |})
           ∗ MinCapsIrisHeapKit.MinCaps_safe (mG := sailG_memG) v3)
           ∗ ⌜δ' = δ⌝).
  Proof.
    intros a p b e.
    destruct p;
      iIntros (Heq) "[[#Hcsafe %] [% %]]";
      try contradiction.
    (* TODO: clean this up! *)
    - rewrite wp_unfold;
        unfold is_true in H1;
        apply andb_prop in H1;
        destruct H1 as [Hb He];
        apply Zle_is_le_bool in Hb;
        apply Zle_is_le_bool in He;
        iAssert (inv (MinCapsIrisHeapKit.mc_invNs.@a) (∃ w, gen_heap.mapsto a (dfrac.DfracOwn 1) w ∗ fixpoint (MinCapsIrisHeapKit.MinCaps_safe1) w))%I as "Hown".
      { rewrite MinCapsIrisHeapKit.fixpoint_MinCaps_safe1_eq; simpl.
        iApply (MinCapsIrisHeapKit.specialize_range $! (conj Hb He) with "Hcsafe"). }
      iIntros (σ' ks1 ks n) "[Hregs Hmem]".
      iDestruct "Hmem" as (memmap) "[Hmem' %]".
      iInv "Hown" as "Hinv" "Hclose".
      iMod (fupd_mask_subseteq empty) as "Hclose2"; first set_solver.
      iModIntro.
      iSplitR; first by intuition.
      iIntros (e2 σ'' efs) "%".
      cbn in H3.
      dependent elimination H3.
      dependent elimination s.
      rewrite Heq in f1.
      cbn in f1.
      dependent elimination f1.
      do 2 iModIntro.
      iDestruct "Hinv" as (v) "Hav".
      iDestruct "Hav" as "[Hav #Hrec]".
      iAssert (⌜ memmap !! a = Some v ⌝)%I with "[Hav Hmem']" as "%".
      { iApply (gen_heap.gen_heap_valid with "Hmem' Hav"). }
      iMod "Hclose2" as "_".
      iAssert (▷ (∃ v0 : Z + Capability, gen_heap.mapsto a (dfrac.DfracOwn 1) v0 ∗ fixpoint MinCapsIrisHeapKit.MinCaps_safe1 v0))%I with "[Hav Hrec]" as "Hinv".
      { iModIntro. iExists v. iSplitL "Hav"; iAssumption. }
      iMod ("Hclose" with "Hinv") as "_".
      iModIntro.
      cbn.
      iSplitL "Hmem' Hregs".
      iSplitL "Hregs"; first iFrame.
      iExists memmap.
      iSplitL "Hmem'"; first iFrame.
      iPureIntro; assumption.
      iSplitL; trivial.
      iApply wp_value; cbn.
      iSplitL; trivial.
      iSplitL; try iAssumption.
      unfold fun_rM.
      apply map_Forall_lookup_1 with (i := a) (x := v) in H1.
      simpl in H1; rewrite H1; iAssumption.
      assumption.
    - rewrite wp_unfold;
        unfold is_true in H1;
        apply andb_prop in H1;
        destruct H1 as [Hb He];
        apply Zle_is_le_bool in Hb;
        apply Zle_is_le_bool in He;
        iAssert (inv (MinCapsIrisHeapKit.mc_invNs.@a) (∃ w, gen_heap.mapsto a (dfrac.DfracOwn 1) w ∗ fixpoint (MinCapsIrisHeapKit.MinCaps_safe1) w))%I as "Hown".
      { rewrite MinCapsIrisHeapKit.fixpoint_MinCaps_safe1_eq; simpl.
        iApply (MinCapsIrisHeapKit.specialize_range $! (conj Hb He) with "Hcsafe"). }
      iIntros (σ' ks1 ks n) "[Hregs Hmem]".
      iDestruct "Hmem" as (memmap) "[Hmem' %]".
      iInv "Hown" as "Hinv" "Hclose".
      iMod (fupd_mask_subseteq empty) as "Hclose2"; first set_solver.
      iModIntro.
      iSplitR; first by intuition.
      iIntros (e2 σ'' efs) "%".
      cbn in H3.
      dependent elimination H3.
      dependent elimination s.
      rewrite Heq in f1.
      cbn in f1.
      dependent elimination f1.
      do 2 iModIntro.
      iDestruct "Hinv" as (v) "Hav".
      iDestruct "Hav" as "[Hav #Hrec]".
      iAssert (⌜ memmap !! a = Some v ⌝)%I with "[Hav Hmem']" as "%".
      { iApply (gen_heap.gen_heap_valid with "Hmem' Hav"). }
      iMod "Hclose2" as "_".
      iAssert (▷ (∃ v0 : Z + Capability, gen_heap.mapsto a (dfrac.DfracOwn 1) v0 ∗ fixpoint MinCapsIrisHeapKit.MinCaps_safe1 v0))%I with "[Hav Hrec]" as "Hinv".
      { iModIntro. iExists v. iSplitL "Hav"; iAssumption. }
      iMod ("Hclose" with "Hinv") as "_".
      iModIntro.
      cbn.
      iSplitL "Hmem' Hregs".
      iSplitL "Hregs"; first iFrame.
      iExists memmap.
      iSplitL "Hmem'"; first iFrame.
      iPureIntro; assumption.
      iSplitL; trivial.
      iApply wp_value; cbn.
      iSplitL; trivial.
      iSplitL; try iAssumption.
      unfold fun_rM.
      apply map_Forall_lookup_1 with (i := a) (x := v) in H1.
      simpl in H1; rewrite H1; iAssumption.
      assumption.
  Qed.

  Lemma wM_sound `{sg : sailG Σ} `{invG} {Γ es δ} :
    forall a w (p : Lit ty_perm) (b e : Lit ty_addr),
      evals es δ = env_snoc (env_snoc env_nil (_ , ty_addr) a)
                            (_ , ty_memval) w
    → ⊢ semTriple δ
        (((MinCapsIrisHeapKit.MinCaps_safe (mG := sailG_memG) w
           ∗ MinCapsIrisHeapKit.MinCaps_safe (mG := sailG_memG)
                                          (inr {|
                                               cap_permission := p;
                                               cap_begin := b;
                                               cap_end := e;
                                               cap_cursor := a |}))
           ∗ MinCapsIrisHeapKit.MinCaps_subperm RW p)
           ∗ ⌜is_true ((b <=? a)%Z && (a <=? e)%Z)⌝ ∧ emp)
        (stm_call_external wM es)
        (λ (v3 : ()) (δ' : CStore Γ),
         (MinCapsIrisHeapKit.MinCaps_safe (mG := sailG_memG)
                                          (inr {| cap_permission := p;
                                                  cap_begin := b;
                                                  cap_end := e;
                                                  cap_cursor := a |})
           ∗ ⌜v3 = tt⌝ ∧ emp)
           ∗ ⌜δ' = δ⌝).
    Proof.
      intros a w p b e.
      destruct p;
        iIntros (Heq) "[[[#Hwsafe #Hcsafe] %] [% %]]";
        try contradiction.
      clear H0 H2.
      rewrite wp_unfold.
      iIntros (σ' ks1 ks n) "[Hregs Hmem]".
      iDestruct "Hmem" as (memmap) "[Hmem' %]".
      unfold is_true in H1.
      apply andb_prop in H1.
      destruct H1 as [Hb He].
      apply Zle_is_le_bool in Hb.
      apply Zle_is_le_bool in He.
      iAssert (inv (MinCapsIrisHeapKit.mc_invNs.@a) (∃ w, gen_heap.mapsto a (dfrac.DfracOwn 1) w ∗ fixpoint (MinCapsIrisHeapKit.MinCaps_safe1) w))%I as "Hown".
      { do 2 rewrite MinCapsIrisHeapKit.fixpoint_MinCaps_safe1_eq; simpl.
        iApply (MinCapsIrisHeapKit.specialize_range $! (conj Hb He) with "Hcsafe"). }
      iInv "Hown" as "Hinv" "Hclose".
      iMod (fupd_mask_subseteq empty) as "Hclose2"; first set_solver.
      iModIntro.
      iSplitR; first by intuition.
      iIntros (e2 σ'' efs) "%".
      cbn in H1.
      dependent elimination H1.
      dependent elimination s.
      rewrite Heq in f1.
      cbn in f1.
      dependent elimination f1.
      do 2 iModIntro.
      iDestruct "Hinv" as (v) "Hav".
      iDestruct "Hav" as "[Hav Hrec]".
      iMod (gen_heap.gen_heap_update _ _ _ w with "Hmem' Hav") as "[Hmem' Hav]".
      iMod "Hclose2" as "_".
      iAssert (▷ (∃ v0 : Z + Capability, gen_heap.mapsto a (dfrac.DfracOwn 1) v0 ∗ fixpoint MinCapsIrisHeapKit.MinCaps_safe1 v0))%I with "[Hav Hrec]" as "Hinv".
      { iModIntro. iExists w. iSplitL "Hav"; iAssumption. }
      iMod ("Hclose" with "Hinv") as "_".
      iModIntro.
      iSplitL; trivial.
      cbn.
      iSplitL "Hregs"; first by iFrame.
      - iExists (<[a:=w]> memmap).
        iSplitL; first by iFrame.
        iPureIntro.
          apply map_Forall_lookup.
          intros i x Hl.
          unfold fun_wM.
          cbn in *.
          destruct (Z.eqb a i) eqn:Heqb.
          + rewrite -> Z.eqb_eq in Heqb.
            subst.
            apply (lookup_insert_rev memmap i); assumption.
          + rewrite -> map_Forall_lookup in H0.
            rewrite -> Z.eqb_neq in Heqb.
            rewrite -> (lookup_insert_ne _ _ _ _ Heqb) in Hl.
            apply H0; assumption.
      - iSplitL; trivial.
        iApply wp_value; cbn; trivial;
          repeat (iSplitL; trivial).
    Qed.

  Lemma sub_perm_sound `{sg : sailG Σ} `{invG} {Γ es δ} :
    forall p p',
      let ι := env_snoc (env_snoc env_nil (_ , ty_perm) p)
                            (_ , ty_perm) p' in
      evals es δ = ι
      → ⊢ semTriple δ
          (⌜is_true true⌝ ∧ emp)
          (use lemma sub_perm es)
        (λ (v1 : ()) (δ' : CStore Γ),
         ((⌜v1 = tt⌝ ∧ emp)
            ∗ MinCapsSymbolicContractKit.ASS.interpret_assertion
            match p with
            | O =>
              MinCapsSymbolicContractKit.ASS.asn_chunk
                (MinCapsSymbolicContractKit.ASS.chunk_user subperm
                                                           (env_nil ► (ty_perm ↦ (term_lit ty_perm p)) ► (ty_perm ↦ (term_lit ty_perm p'))))
            | R =>
              MinCapsSymbolicContractKit.ASS.asn_match_enum permission 
                                                            (term_lit ty_perm p')
                                                            (λ p' : Permission,
                                                                    match p' with
                                                                    | O => MinCapsSymbolicContractKit.ASS.asn_true
                                                                    | _ =>
                                                                      MinCapsSymbolicContractKit.ASS.asn_chunk
                                                                        (MinCapsSymbolicContractKit.ASS.chunk_user subperm
                                                           (env_nil ► (ty_perm ↦ (term_lit ty_perm p)) ► (ty_perm ↦ (term_lit ty_perm p'))))
                                                                    end)
            | RW =>
              MinCapsSymbolicContractKit.ASS.asn_match_enum permission 
                                                            (term_lit ty_perm p')
                                                            (λ p' : Permission,
                                                                    match p' with
                                                                    | RW =>
                                                                      MinCapsSymbolicContractKit.ASS.asn_chunk
                                                                        (MinCapsSymbolicContractKit.ASS.chunk_user subperm
                                                           (env_nil ► (ty_perm ↦ (term_lit ty_perm p)) ► (ty_perm ↦ (term_lit ty_perm p'))))
                                                                    | _ => MinCapsSymbolicContractKit.ASS.asn_true
                                                                    end)
            end (env_snoc ι ("" , ty_unit) v1)) ∗ ⌜δ' = δ⌝).
  Admitted.

  Ltac destruct_SymInstance :=
    repeat (match goal with
    | H : Env _ (ctx_snoc _ _) |- _ => destruct (snocView H)
    | H : Env _ ctx_nil |- _ => destruct (nilView H)
    end).

  Lemma foreignSem `{sg : sailG Σ} : ForeignSem (Σ := Σ).
    intros Γ τ Δ f es δ.
    destruct f as [ | | |Γ' [ | reg | | | | | | | | | ]];
      cbn - [MinCapsIrisHeapKit.MinCaps_safe MinCapsIrisHeapKit.MinCaps_csafe];
      intros ι;
      destruct_SymInstance;
      eauto using dI_sound, open_ptsreg_sound, close_ptsreg_sound, int_safe_sound, lift_csafe_sound, specialize_safe_to_cap_sound, duplicate_safe_sound, csafe_move_cursor_sound, csafe_sub_perm_sound, csafe_within_range_sound, gen_dummy_sound, rM_sound, wM_sound.
    - (* sub_perm *)
      rename v into p.
      rename v0 into p'.
      iIntros (Heq) "_".
      rewrite wp_unfold.
      iIntros (σ' ks1 ks n) "Hregs".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro.
      iSplitR; first by intuition.
      iIntros (e2 σ'' efs) "%".
      cbn in H.
      dependent elimination H.
      dependent elimination s.
      rewrite Heq in f1.
      cbn in f1.
      dependent elimination f1.
      do 2 iModIntro.
      iMod "Hclose" as "_".
      iModIntro.
      iFrame.
      iSplitL; trivial.
      iApply wp_value.
      cbn.
      iSplitL; trivial.
      iSplitL; trivial.
      destruct p'; destruct p; trivial.
  Qed.

End MinCapsModel.
