(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel                                          *)
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
     Machine.

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
     SemiConcrete.Outcome
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
  From MinimalCaps Require Import Contracts.
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

    Class mcMemG Σ := McMemG {
                          (* ghost variable for tracking state of registers *)
                          mc_ghG :> gh.gen_heapG Z Z Σ;
                          mc_invNs : namespace
                        }.

    Definition memPreG : gFunctors -> Set := fun Σ => gh.gen_heapPreG Z Z Σ.
    Definition memG : gFunctors -> Set := mcMemG.
    Definition memΣ : gFunctors := gh.gen_heapΣ Z Z.

    Definition memΣ_PreG : forall {Σ}, subG memΣ Σ -> memPreG Σ := fun {Σ} => gh.subG_gen_heapPreG (Σ := Σ) (L := Z) (V := Z).

    Definition mem_inv : forall {Σ}, memG Σ -> Memory -> iProp Σ :=
      fun {Σ} hG μ =>
        (∃ memmap, gen_heap_interp (hG := mc_ghG (mcMemG := hG)) memmap ∗
                                ⌜ map_Forall (fun a v => μ a = v) memmap ⌝
        )%I.

    Fixpoint natsTo (n : nat) : list nat :=
      match n with
      | 0 => []
      | S n => n :: natsTo n
      end.

    Definition liveAddrs : list Addr := map Z.of_nat (natsTo maxAddr).
    Definition initMemMap μ := (list_to_map (map (fun a => (a , μ a)) liveAddrs) : gmap Addr Z ).

    Lemma initMemMap_works μ : map_Forall (λ (a : Addr) (v : Z), μ a = v) (initMemMap μ).
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

      iMod (gen_heap_init (gen_heapPreG0 := gHP) (L := Addr) (V := Z) empty) as (gH) "[inv _]".
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

    Definition MinCaps_csafe `{sailRegG Σ} `{invG Σ} {mG : memG Σ} (v : Capability) : iProp Σ :=
      match v with
      | MkCap O b e a => True%I
      | MkCap R b e a =>
                ([∗ list] a ∈ (region_addrs b e), inv (mc_invNs (mcMemG := mG) .@ a) (∃ v, mapsto (hG := mc_ghG (mcMemG := mG)) a (DfracOwn 1) v))%I
      | MkCap RW b e a =>
                [∗ list] a ∈ (region_addrs b e), inv (mc_invNs (mcMemG := mG) .@ a) (∃ v, mapsto (hG := mc_ghG (mcMemG := mG)) a (DfracOwn 1) v)
      end.


    Definition MinCaps_safe `{sailRegG Σ} `{invG Σ} {mG : memG Σ} (v : Z + Capability) : iProp Σ :=
      match v with
      | inl z => True%I
      | inr c => MinCaps_csafe (mG := mG) c
      end.

    Import EnvNotations.

    Definition luser_inst `{sailRegG Σ} `{invG Σ} (p : Predicate) (ts : Env Lit (MinCapsAssertionKit.𝑷_Ty p)) (mG : memG Σ) : iProp Σ :=
      (match p return Env Lit (MinCapsAssertionKit.𝑷_Ty p) -> iProp Σ with
      | ptsreg => fun ts => MinCaps_ptsreg (env_head (env_tail ts)) (env_head ts)
      | ptsto => fun ts => mapsto (hG := mc_ghG (mcMemG := mG)) (env_head (env_tail ts)) (DfracOwn 1) (env_head ts)
      | safe => fun ts => MinCaps_safe (mG := mG) (env_head ts)
      | csafe => fun ts => MinCaps_csafe (mG := mG) (env_head ts)
      end) ts.

    Global Instance MinCaps_csafe_Persistent `{sailRegG Σ} `{invG Σ} {mG : memG Σ} (c : Capability) : Persistent (MinCaps_csafe (mG := mG) c).
    Proof. destruct c; destruct cap_permission; apply _. Qed.

    Global Instance MinCaps_safe_Persistent `{sailRegG Σ} `{invG Σ} {mG : memG Σ} (v : Z + Capability) : Persistent (MinCaps_safe (mG := mG) v).
    Proof. destruct v; apply _. Qed.

    End WithIrisNotations.
  End MinCapsIrisHeapKit.

  Module Soundness := IrisSoundness MinCapsTermKit MinCapsProgramKit MinCapsAssertionKit MinCapsSymbolicContractKit MinCapsIrisHeapKit.
  Export Soundness.

  Import EnvNotations.

  Lemma rM_sound `{sg : sailG Σ} `{invG} {Γ es δ} :
    forall address w,
    evals es δ = env_snoc env_nil (_ , ty_addr) address 
    → ⊢ semTriple δ (gen_heap.mapsto (hG := MinCapsIrisHeapKit.mc_ghG (mcMemG := sailG_memG)) address (dfrac.DfracOwn 1) w) (stm_call_external rM es)
          (λ (v : Z) (δ' : LocalStore Γ),
             (gen_heap.mapsto (hG := MinCapsIrisHeapKit.mc_ghG (mcMemG := sailG_memG)) address (dfrac.DfracOwn 1) w ∗ ⌜v = w⌝ ∧ emp) ∗ ⌜δ' = δ⌝).
  Proof.
    iIntros (address w eq) "pre".
    destruct (snocView es) as [es e_addr]. destruct (nilView es).
    cbn [env_lookup inctx_case_snoc].
    rewrite wp_unfold.
    iIntros (σ' ks1 ks n) "[Hregs Hmem]".
    iDestruct "Hmem" as (memmap) "[Hmem' %]".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; first by intuition.
    iIntros (e2 σ'' efs) "%".
    cbn in H1.
    dependent elimination H1.
    dependent elimination s.
    cbn in e0. destruct_conjs. subst.
    iModIntro. iModIntro.
    cbn.
    iDestruct (gen_heap.gen_heap_valid with "Hmem' pre") as "%".
    iMod "Hclose" as "_".
    iModIntro.
    iFrame.
    iSplitL "Hmem'".
    - iExists memmap.
      by iFrame.
    - iSplitL; trivial.
      iApply wp_value.
      cbn.
      iFrame.
      specialize (H0 address w H1).
      cbn in eq; dependent elimination eq.
      cbn in H0.
      iPureIntro.
      unfold fun_rM.
      split; split; trivial.
  Qed.

  Lemma wM_sound `{sg : sailG Σ} `{invG} {Γ es δ} :
    forall address new_value old_value,
    evals es δ = env_snoc (env_snoc env_nil (_ , ty_addr) address) (_ , ty_int) new_value
    → ⊢ semTriple δ (gen_heap.mapsto (hG := MinCapsIrisHeapKit.mc_ghG (mcMemG := sailG_memG)) address (dfrac.DfracOwn 1) old_value) (stm_call_external wM es)
        (λ (v : Lit ty_unit) (δ' : LocalStore Γ),
             (gen_heap.mapsto (hG := MinCapsIrisHeapKit.mc_ghG (mcMemG := sailG_memG)) address (dfrac.DfracOwn 1) new_value) ∗ ⌜δ' = δ⌝).
  Proof.
    iIntros (address new_value old_value eq) "pre".
    destruct (snocView es) as [es e_new_value].
    destruct (snocView es) as [es e_addr].
    destruct (nilView es).
    cbn in eq.
    cbn [env_lookup inctx_case_snoc].
    rewrite wp_unfold.
    iIntros (σ' ks1 ks n) "[Hregs Hmem]".
    iDestruct "Hmem" as (memmap) "[Hmem' %]".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro.
    iSplitR; first by intuition.
    iIntros (e2 σ'' efs) "%".
    cbn in H1.
    dependent elimination H1.
    dependent elimination s.
    cbn in e0. destruct_conjs. subst.
    iModIntro. iModIntro.
    cbn.
    iMod (gen_heap.gen_heap_update _ _ _ new_value with "Hmem' pre") as "[Hmem' ptsto]".
  Admitted.

  Lemma dI_sound `{sg : sailG Σ} `{invG} {Γ es δ} :
    forall code : Lit ty_int,
    evals es δ = env_snoc env_nil (_ , ty_int) code
    → ⊢ semTriple δ (⌜is_true true⌝ ∧ emp) (stm_call_external dI es)
          (λ (v : Lit ty_instr) (δ' : LocalStore Γ),
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
    rewrite Heq in e0.
    cbn in e0.
    destruct e0 as (Hμ & Hγ & Hres).
    subst.
    do 2 iModIntro.
    iMod "Hclose" as "_".
    iModIntro.
    iFrame.
    iSplitL; trivial.
    unfold fun_dI.
    iApply wp_value.
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
          (λ (v : ()) (δ' : LocalStore Γ),
             (MinCapsSymbolicContractKit.ASS.interpret_assertion (ι ► (("result", ty_unit) ↦ v))
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
                  end) ∗ ⌜δ' = δ⌝).
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
    rewrite Heq in e0.
    cbn in e0.
    destruct e0 as (Hμ & Hγ & Hres).
    subst.
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
          (λ (_ : ()) (δ' : LocalStore Γ),
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
    cbn in e0. destruct_conjs. subst.
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
          (λ (v : ()) (δ' : LocalStore Γ),
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
    rewrite Heq in e0.
    cbn in e0.
    destruct e0 as (Hμ & Hγ & Hres).
    subst.
    do 2 iModIntro.
    iMod "Hclose" as "_".
    iModIntro.
    iFrame.
    iSplitL; [|cbn; trivial].
    by iApply wp_value.
  Qed.

  Lemma lift_csafe_sound `{sg : sailG Σ} {Γ es δ} :
    forall c,
      evals es δ = env_snoc env_nil (_ , ty_cap) c
      → ⊢ semTriple δ
          (MinCapsIrisHeapKit.MinCaps_csafe (mG := sailG_memG) c)
          (stm_call_external (ghost lift_csafe) es)
          (λ (v : ()) (δ' : LocalStore Γ),
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
    rewrite Heq in e0.
    cbn in e0.
    destruct e0 as (Hμ & Hγ & Hres).
    subst.
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
          (λ (v : ()) (δ' : LocalStore Γ),
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
    rewrite Heq in e0.
    cbn in e0.
    destruct e0 as (Hμ & Hγ & Hres).
    subst.
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
          (λ (v : ()) (δ' : LocalStore Γ),
           ((⌜v = tt⌝ ∧ emp)
              ∗ MinCapsIrisHeapKit.MinCaps_csafe (mG := sailG_memG) c)
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
    rewrite Heq in e0.
    cbn in e0.
    destruct e0 as (Hμ & Hγ & Hres).
    subst.
    do 2 iModIntro.
    iMod "Hclose" as "_".
    iModIntro.
    iFrame.
    iSplitL; [|cbn;trivial].
    iApply wp_value.
    cbn.
      by iFrame.
  Qed.

  Lemma csafe_move_cursor_safe_sound `{sg : sailG Σ} {Γ es δ} :
    forall p b e a a',
      evals es δ = env_snoc
                     (env_snoc env_nil (_ , ty_cap)
                               {| cap_permission := p;
                                  cap_begin := b;
                                  cap_end := e;
                                  cap_cursor := a |})
                     (_ , ty_cap)
                     {| cap_permission := p;
                        cap_begin := b;
                        cap_end := e;
                        cap_cursor := a' |}
      → ⊢ semTriple δ
          (MinCapsIrisHeapKit.MinCaps_csafe (mG := sailG_memG)
                                            {|
                                              cap_permission := p;
                                              cap_begin := b;
                                              cap_end := e;
                                              cap_cursor := a |})
          (stm_call_external (ghost csafe_move_cursor) es)
          (λ (v0 : ()) (δ' : LocalStore Γ),
           (((⌜v0 = tt⌝ ∧ emp)
               ∗ MinCapsIrisHeapKit.MinCaps_csafe (mG := sailG_memG)
               {| cap_permission := p;
                  cap_begin := b;
                  cap_end := e;
                  cap_cursor := a |})
              ∗ MinCapsIrisHeapKit.MinCaps_csafe (mG := sailG_memG)
              {| cap_permission := p;
                 cap_begin := b;
                 cap_end := e;
                 cap_cursor := a' |}) ∗ ⌜
                                      δ' = δ⌝).
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
    rewrite Heq in e1.
    cbn in e1.
    destruct e1 as (Hμ & Hγ & Hres).
    subst.
    do 2 iModIntro.
    iMod "Hclose" as "_".
    iModIntro.
    iFrame.
    iSplitL; trivial.
    iApply wp_value.
    cbn.
    repeat (iSplitL; trivial).
  Qed.

  Ltac destruct_SymInstance :=
    repeat (match goal with
    | H : SymInstance _ |- _ => unfold SymInstance in H; unfold NamedEnv in H
    | H : Env _ (ctx_snoc _ _) |- _ => destruct (snocView H)
    | H : Env _ ctx_nil |- _ => destruct (nilView H)
    end).

  Lemma extSem `{sg : sailG Σ} : ExtSem (Σ := Σ).
    intros Γ τ Δ f es δ.
    destruct f as [_|_|_|Γ' [ | reg | | | | | ] es δ'];
      cbn - [MinCapsIrisHeapKit.MinCaps_safe MinCapsIrisHeapKit.MinCaps_csafe];
      intros ι;
      destruct_SymInstance;
      eauto using rM_sound, wM_sound, dI_sound, open_ptsreg_sound, close_ptsreg_sound, int_safe_sound, lift_csafe_sound, specialize_safe_to_cap_sound, duplicate_safe_sound, csafe_move_cursor_safe_sound, rM_sound.
    - (* rM *)
      iIntros (Heq) "[#Hcsafe Hp]".
      rewrite wp_unfold.
      iIntros (σ' ks1 ks n) "Hregs".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro.
      iSplitR; first by intuition.
      iIntros (e2 σ'' efs) "%".
      cbn in H.
      dependent elimination H.
      dependent elimination s.
      rewrite Heq in e0.
      cbn in e0.
      destruct e0 as (Hμ & Hγ & Hres).
      subst.
      do 2 iModIntro.
      iMod "Hclose" as "_".
      iModIntro.
      iSplitL; trivial.
      cbn.
      iSplitL; trivial.
      iApply wp_value.
      cbn.
      destruct v1; trivial; iSplit; trivial; iSplit; trivial.
    - (* wM *)
      rename v into e.
      rename v0 into b.
      rename v1 into p.
      rename v2 into w.
      rename v3 into address.
      iIntros (Heq) "[#Hcsafe Hp]".
      rewrite wp_unfold.
      iIntros (σ' ks1 ks n) "[Hregs Hmem]".
      iDestruct "Hmem" as (memmap) "[Hmem' %]".
      iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
      iModIntro.
      iSplitR; first by intuition.
      iIntros (e2 σ'' efs) "%".
      cbn in H0.
      dependent elimination H0.
      dependent elimination s.
      rewrite Heq in e1.
      cbn in e1.
      destruct e1 as (Hμ & Hγ & Hres).
      subst.
      do 2 iModIntro.
      cbn.
      destruct p;
        cbn;
        iDestruct "Hp" as "[% _]";
        try (unfold is_true in *; discriminate H0).
      iAssert (gen_heap.mapsto address (dfrac.DfracOwn 1) _)%I as "Hown".
      + admit.
      + iMod (gen_heap.gen_heap_update _ _ _ w with "Hmem' Hown") as "[Hmem' ptsto]".
        iMod "Hclose" as "_".
        iModIntro.
        iSplitL; trivial.
        cbn.
        iSplitL "Hregs"; first by iFrame.
        * iExists (<[address:=w]> memmap).
          iSplitL.
          { iFrame. }
          { iPureIntro.
            apply map_Forall_lookup.
            intros i x Hl.
            unfold fun_wM.
            cbn in *.
            destruct (address =? i) eqn:Heqb.
            - rewrite -> Z.eqb_eq in Heqb.
              subst.
              apply (lookup_insert_rev memmap i); assumption.
            - rewrite -> map_Forall_lookup in H.
              rewrite -> Z.eqb_neq in Heqb.
              rewrite -> (lookup_insert_ne _ _ _ _ Heqb) in Hl.
              apply H; assumption.
          }
        * iSplitL; trivial.
          iApply wp_value; cbn; trivial;
            repeat (iSplitL; trivial).
  Admitted.

  (* TODO: fix 
  Lemma rM_sound2 `{sg : sailG Σ} `{invG} {Γ es δ} :
    forall address (p : Lit ty_perm) (b e : Lit ty_addr),
      let ι := env_snoc (env_snoc (env_snoc (env_snoc env_nil (_ , ty_addr) address)
                                           ("p" , ty_perm) p)
                                 (_ , ty_addr) b)
                       (_ , ty_addr) e in
      evals es δ = env_snoc env_nil (_ , ty_addr) address
    → ⊢ semTriple δ
        (MinCapsIrisHeapKit.MinCaps_csafe (mG := sailG_memG)
           (MkCap p b e address)
           ∗ MinCapsSymbolicContractKit.ASS.interpret_assertion ι
           match p with
           | RW =>
             MinCapsSymbolicContractKit.ASS.asn_bool
               (term_binop binop_and
                           (term_binop binop_le (term_lit ty_addr b) (term_lit ty_addr address))
                           (term_binop binop_le (term_lit ty_addr address) (term_lit ty_addr e)))
           | _  => MinCapsSymbolicContractKit.ASS.asn_false
           end) (stm_call_external rM es)
        (λ (v3 : Z) (δ' : LocalStore Γ),
         (MinCapsIrisHeapKit.MinCaps_csafe (mG := sailG_memG)
           {|
             cap_permission := p;
             cap_begin := b;
             cap_end := e;
             cap_cursor := address |}
            ∗ MinCapsIrisHeapKit.MinCaps_safe (inl v3)) ∗ ⌜δ' = δ⌝).
   *)

End MinCapsModel.

