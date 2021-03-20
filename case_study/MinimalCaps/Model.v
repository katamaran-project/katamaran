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

    Definition region_addrs (b : Addr) (e : Addr + unit): list Addr :=
      match e with
      | inl e => filter (fun a => and (b ≤ a)%Z (a ≤ e)%Z) liveAddrs
      | inr _ => filter (fun a => (b ≤ a)%Z) liveAddrs
      end.

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

    End WithIrisNotations.
  End MinCapsIrisHeapKit.

  Module Soundness := IrisSoundness MinCapsTermKit MinCapsProgramKit MinCapsAssertionKit MinCapsSymbolicContractKit MinCapsIrisHeapKit.
  Export Soundness.

  Import EnvNotations.

  Lemma rM_sound `{sg : sailG Σ} `{invG} {Γ es δ} :
  ∀ (ι : SymInstance (ctx_snoc (ctx_snoc ctx_nil ("address", ty_addr)) ("w", ty_int))),
    evals es δ = [(ι ‼ "address")%exp]
    → ⊢ semTriple δ (gen_heap.mapsto (hG := MinCapsIrisHeapKit.mc_ghG (mcMemG := sailG_memG)) (ι ‼ "address")%exp (dfrac.DfracOwn 1) (ι ‼ "w")%exp) (stm_call_external rM es)
          (λ (v : Z) (δ' : LocalStore Γ),
             (gen_heap.mapsto (hG := MinCapsIrisHeapKit.mc_ghG (mcMemG := sailG_memG)) (ι ‼ "address")%exp (dfrac.DfracOwn 1) (ι ‼ "w")%exp ∗ ⌜v = (ι ‼ "w")%exp⌝ ∧ emp) ∗ ⌜δ' = δ⌝).
  Proof.
    iIntros (ι eq) "pre".
    destruct (snocView es) as [es e_addr]. destruct (nilView es).
    destruct (snocView ι) as [ι w].
    destruct (snocView ι) as [ι addr].
    destruct (nilView ι). cbn in eq.
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
      specialize (H0 addr w H1).
      dependent elimination eq.
      cbn in H0.
      iPureIntro.
      unfold fun_rM.
      split; split; trivial.
  Qed.

  Lemma wM_sound `{sg : sailG Σ} `{invG} {Γ es δ} :
  ∀ (ι : SymInstance (ctx_snoc (ctx_snoc (ctx_snoc ctx_nil ("address", ty_addr)) ("new_value", ty_int)) ("old_value", ty_int))),
    evals es δ = [(ι ‼ "address")%exp, (ι ‼ "new_value")%exp]
    → ⊢ semTriple δ (gen_heap.mapsto (hG := MinCapsIrisHeapKit.mc_ghG (mcMemG := sailG_memG)) (ι ‼ "address")%exp (dfrac.DfracOwn 1) (ι ‼ "old_value")%exp) (stm_call_external wM es)
        (λ (v : Lit ty_unit) (δ' : LocalStore Γ),
             (gen_heap.mapsto (hG := MinCapsIrisHeapKit.mc_ghG (mcMemG := sailG_memG)) (ι ‼ "address")%exp (dfrac.DfracOwn 1) (ι ‼ "new_value")%exp) ∗ ⌜δ' = δ⌝).
  Proof.
    iIntros (ι eq) "pre".
    destruct (snocView es) as [es e_new_value].
    destruct (snocView es) as [es e_addr].
    destruct (nilView es).
    destruct (snocView ι) as [ι old_value].
    destruct (snocView ι) as [ι new_value].
    destruct (snocView ι) as [ι addr].
    destruct (nilView ι). cbn in eq.
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
  ∀ (ι : SymInstance (ctx_snoc ctx_nil ("code", ty_int))),
    evals es δ = [(ι ‼ "code")%exp]
    → ⊢ semTriple δ (⌜is_true true⌝ ∧ emp) (stm_call_external dI es)
          (λ (v : Lit ty_instr) (δ' : LocalStore Γ),
             (⌜is_true true⌝ ∧ emp) ∗ ⌜δ' = δ⌝).
  Proof.
  Admitted.

  Lemma open_ptsreg_sound `{sg : sailG Σ} {Γ es δ} :
    ∀ ι : SymInstance (ctx_snoc (ctx_snoc ctx_nil ("reg", ty_lv)) ("w", ty_word)),
      evals es δ = [(ι ‼ "reg")%exp]
      → ⊢ semTriple δ
          (MinCapsIrisHeapKit.MinCaps_ptsreg (ι ‼ "reg")%exp (ι ‼ "w")%exp)
          (stm_call_external (ghost open_ptsreg) es)
          (λ (v : ()) (δ' : LocalStore Γ),
             (MinCapsSymbolicContractKit.ASS.inst_assertion (ι ► (("result", ty_unit) ↦ v))
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
  Admitted.

  Lemma close_ptsreg_sound `{sg : sailG Σ} {Γ R es δ} :
    ∀ ι : SymInstance (ctx_snoc ctx_nil ("w", ty_word)),
      evals es δ = env_nil
      → ⊢ semTriple δ
          (MinCapsIrisHeapKit.IrisRegs.reg_pointsTo (MinCapsSymbolicContractKit.regtag_to_reg R)
                                                    (ι ‼ "w")%exp)
          (stm_call_external (ghost (close_ptsreg R)) es)
          (λ (_ : ()) (δ' : LocalStore Γ),
           MinCapsIrisHeapKit.MinCaps_ptsreg R (ι ‼ "w")%exp
                                             ∗ ⌜δ' = δ⌝).
  Proof.
    iIntros (ι eq) "ptsto".
    destruct (nilView es). clear eq.
    destruct (snocView ι) as [ι w].
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

  Lemma extSem `{sg : sailG Σ} : ExtSem (Σ := Σ).
    intros Γ τ Δ f es δ.
    destruct f as [_|_|_|Γ' [ | reg | | ] es δ'];
      cbn;
      eauto using rM_sound, wM_sound, dI_sound, open_ptsreg_sound, close_ptsreg_sound.
    (* TODO: case for duplicate_safe & is_csafe, add lemma duplicate_safe_sound, add to eauto using ... *)
  Admitted.

End MinCapsModel.

