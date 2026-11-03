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

(* ========================================================================= *)
(* CFGVer/SpecIris.v — the Iris wiring for CFGVer's Specification instance.  *)
(*                                                                           *)
(* Split out of Spec.v (2026-07-27). Holds everything in the CFGVer spec     *)
(* layer that needs the binary Iris model or the shallow/refine/soundness    *)
(* executors: the shallow executor instantiation and                         *)
(* RiscvPmpIrisInstanceWithContracts (ProgramLogicOn +                       *)
(* IrisInstanceWithContracts2 + ShallowSoundness + RefineExecOn).            *)
(*                                                                           *)
(* Kept OUT of Spec.v so that Contracts.v, GenContract.v and the examples —  *)
(* which only vm_compute the symbolic executor — do not pay ~1.3 GB of peak  *)
(* RSS for machinery they never reduce. Required by the soundness chain      *)
(* (VerifierRel.v, Adequacy.v, EndToEnd.v).                                  *)
(* ========================================================================= *)

From Katamaran Require Import
     Iris.Instance
     Iris.BinaryInstance
     Iris.BinaryWeakestPre
     Iris.Base
     Notations
     Bitvector
     Sep.Hoare
     Specification
     MicroSail.ShallowExecutor
     MicroSail.ShallowSoundness
     MicroSail.SymbolicExecutor.
From Katamaran Require Import
     MicroSail.RefineExecutor.
From Katamaran Require Import
     MicroSail.Soundness
     RiscvPmp.PmpCheck
     RiscvPmp.IrisModel
     RiscvPmp.IrisModelBinary
     RiscvPmp.IrisInstance
     RiscvPmp.IrisInstanceBinary
     RiscvPmp.Machine
     RiscvPmp.Sig
     RiscvPmp.Contracts.
From Katamaran Require RiscvPmp.ModelBinary.
From Katamaran Require Import RiscvPmp.CFGVer.Spec.
(* For the CFGVer-local ghost-lemma catalogue (Verifier.clem_lemma), whose
   soundness is proved below next to lemSemCFGVerif. *)
From Katamaran Require Import RiscvPmp.CFGVer.Verifier.
From Coq Require Import micromega.Lia.

From iris.program_logic Require Import total_lifting.

Import RiscvPmpProgram.
Import ListNotations.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import env.notations.

Module RiscvPmpCFGVerifShalExecutor :=
  MakeShallowExecutor RiscvPmpBase RiscvPmpSignature RiscvPmpProgram RiscvPmpCFGVerifSpec.

Module RiscvPmpIrisInstanceWithContracts.
  Include ProgramLogicOn RiscvPmpBase RiscvPmpSignature RiscvPmpProgram
    RiscvPmpCFGVerifSpec.
  Include IrisInstanceWithContracts2 RiscvPmpBase RiscvPmpSignature
    RiscvPmpProgram RiscvPmpSemantics RiscvPmpCFGVerifSpec RiscvPmpIrisBase2
    (* RiscvPmpIrisAdeqParameters *) RiscvPmpIrisAdeqParams2
    RiscvPmpIrisInstance2.
  Include MicroSail.ShallowSoundness.Soundness RiscvPmpBase RiscvPmpSignature
    RiscvPmpProgram RiscvPmpCFGVerifSpec RiscvPmpCFGVerifShalExecutor.
  Include MicroSail.RefineExecutor.RefineExecOn RiscvPmpBase RiscvPmpSignature
    RiscvPmpProgram RiscvPmpCFGVerifSpec RiscvPmpCFGVerifShalExecutor
    RiscvPmpCFGVerifExecutor.

  Import RiscvPmpIrisBase2.
  Import RiscvPmpIrisInstance2.
  Import RiscvPmp.Model.

  Import iris.bi.interface.
  Import iris.bi.big_op.
  Import iris.base_logic.lib.iprop.
  Import iris.program_logic.weakestpre.
  Import iris.program_logic.total_weakestpre.
  Import iris.base_logic.lib.gen_heap.
  Import iris.proofmode.string_ident.
  Import iris.proofmode.tactics.

  Lemma read_ram_sound `{sailGS2 Σ} {bytes} :
    ValidContractForeign RiscvPmpCFGVerifSpec.sep_contract_read_ram (read_ram bytes).
  Proof.
      intros Γ es δ ι Heq. cbn. destruct_syminstance ι.
      iIntros "H". cbn in *. iApply semWP2_foreign. unfold mem_inv2.
      iIntros (? ? ? ?) "((Hregs1 & Hregs2) & ((%memmapL & HmemL & %HmapL & HtrL & HltrL) & (%memmapR & HmemR & %HmapR & HtrR & HltrR)))".
      iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
      iIntros (resL ? ? resR ? ? Hf).
      rewrite evalValsProjLeftIsProjLeftEvals in Hf. rewrite evalValsProjRightIsProjRightEvals in Hf.
      rewrite Heq in Hf. cbn in Hf. inversion Hf; subst.
      inversion H0; inversion H1; subst. clear H0 H1 Hf. do 3 iModIntro.
      iMod "Hclose" as "_".
      (* The precondition interprets [asn.match_bool inv ...] via the raw
         [pattern_match_relval pat_bool inv]. Under method-Y this succeeds on a
         [NonSyncVal v v0] scrutinee exactly when [v = v0] (both worlds take the
         same branch), and fails otherwise. Destructing the match result rather
         than [inv] itself reduces both [H] and the postcondition uniformly:
         the [Some] branch collapses to a plain boolean [b] (the [SyncVal] and
         coinciding-[NonSyncVal] cases are then literally identical), and the
         [None] branch gives a [False] precondition. *)
      destruct (pattern_match_relval (N := string) pat_bool inv) as [[b δpc]|] eqn:Hpm; cbn;
        cbn in Hpm; rewrite Hpm.
      2: { iDestruct "H" as "%HF". contradiction. }
      destruct (env.view δpc).
      destruct b.
        - (* readonly case *)
        iDestruct "H" as "#H".
         iInv "H" as "Hptsto" "Hclose_ptsto".
        iDestruct "Hptsto" as "(HptstoL & HptstoR)".
        iDestruct (bi.later_mono _ _ (RiscvPmpModel2.fun_read_ram_works (sg := sailGS2_sailGS_left) HmapL) with "[$HptstoL $HmemL]") as "#>%eq_fun_read_ramL".
        iDestruct (bi.later_mono _ _ (RiscvPmpModel2.fun_read_ram_works (sg := sailGS2_sailGS_right) HmapR) with "[$HptstoR $HmemR]") as "#>%eq_fun_read_ramR".
        iMod ("Hclose_ptsto" with "[$HptstoL $HptstoR]") as "_".
        iFrame "Hregs1 Hregs2 HmemL HmemR HtrL HltrL HtrR HltrR".
        iSplitR; first auto.
        iApply semWP2_val. do 2 iModIntro.
        iExists δ. iSplitR; first auto.
        destruct ram_val.
        + iExists (NonSyncVal (fun_read_ram μ1 bytes (ty.projLeft paddr)) (fun_read_ram μ2 bytes (ty.projRight paddr))). iSplitR; first auto.
          iFrame "H".
          iSplitR; try auto.
          iSplitR; cbn; first auto.
          rewrite eq_fun_read_ramL. by rewrite eq_fun_read_ramR.
          auto. (* TODO: How to dispatch emp goal, also several admits for this below *)
      - (* old case *)
        iModIntro.
        iDestruct "H" as "(HL & HR)".
        iPoseProof (RiscvPmpModel2.fun_read_ram_works (sg := sailGS2_sailGS_left) HmapL with "[$HL $HmemL]") as "%eq_fun_read_ramL".
        iPoseProof (RiscvPmpModel2.fun_read_ram_works (sg := sailGS2_sailGS_right) HmapR with "[$HR $HmemR]") as "%eq_fun_read_ramR".
        iPoseProof (RiscvPmpModel2.mem_inv_not_modified (sg := sailGS2_sailGS_left) $! HmapL with "HmemL HtrL HltrL") as "HmemL".
        iPoseProof (RiscvPmpModel2.mem_inv_not_modified (sg := sailGS2_sailGS_right) $! HmapR with "HmemR HtrR HltrR") as "HmemR".
        iFrame "Hregs1 Hregs2 HmemL HmemR". iApply semWP2_val.
        iFrame "HL". iFrame "HR".
        iExists δ. iModIntro. iSplitR; first auto.
        destruct ram_val.
        + iExists (NonSyncVal (fun_read_ram μ1 bytes (ty.projLeft paddr)) (fun_read_ram μ2 bytes (ty.projRight paddr))).
          iSplitR; first auto.
          iSplitR; first (rewrite eq_fun_read_ramR; by rewrite eq_fun_read_ramL).
          auto.
  Qed.

  Lemma write_ram_sound `{sailGS2 Σ} {bytes} :
    ValidContractForeign RiscvPmpCFGVerifSpec.sep_contract_write_ram (write_ram bytes).
  Proof.
    intros Γ es δ ι Heq. destruct_syminstance ι. cbn in *.
    iIntros "[%w (HL & HR)]". iApply semWP2_foreign.
    iIntros (? ? ? ?) "((Hregs1 & Hregs2) & ((%memmapL & HmemL & %HmapL & HtrL) & (%memmapR & HmemR & %HmapR & HtrR)))".
    iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
    iIntros (res1 ? ? res2 ? ? Hf).
    rewrite evalValsProjLeftIsProjLeftEvals in Hf. rewrite evalValsProjRightIsProjRightEvals in Hf.
    rewrite Heq in Hf. cbn in Hf. inversion Hf; subst.
    inversion H0; inversion H1; subst. clear H0 H1 Hf. do 3 iModIntro.
    iMod "Hclose" as "_".
    iMod (RiscvPmpModel2.fun_write_ram_works (sg := sailGS2_sailGS_left) with "[$HL $HmemL $HtrL]") as "[$ HL]"; auto.
    iMod (RiscvPmpModel2.fun_write_ram_works (sg := sailGS2_sailGS_right) with "[$HR $HmemR $HtrR]") as "[$ HR]"; auto.
    rewrite semWP2_val. iFrame "Hregs1 Hregs2".
    iExists δ. iSplitR; first auto.
    iExists (SyncVal true). iSplitR; first auto. by iFrame "HL HR".
 Qed.

  (* Important sanity condition on mmio predicates - NOTE: could be in typeclass, together with the condition that reads are either all accepted, or none of them are *)
  Lemma mmio_pred_cons {bytes : nat} t e: event_pred bytes e → mmio_pred bytes t → mmio_pred bytes (cons e t).
  Proof. now apply List.Forall_cons. Qed.

  (* Lemma mmio_write_sound `{!sailGS Σ} `(H: restrict_bytes bytes) : *)
  (*   TValidContractForeign (@RiscvPmpCFGVerifSpec.sep_contract_mmio_write _ H) (mmio_write H). *)
  (* Proof. *)
  (*   intros Γ es δ ι Heq. destruct_syminstance ι. cbn in *. *)
  (*   iIntros "([%Hmmio _] & #Hinv & [-> ->])". iApply semTWP_foreign. *)
  (*   iIntros (? ?) "[Hregs [% (Hmem & %Hmap & Htr)]]". *)
  (*   iInv "Hinv" as (t) " [>Htrf >%Hpred]" "Hclose". *)
  (*   iDestruct (trace.trace_full_frag_eq with "Htr Htrf") as "%Heqt". subst t. *)
  (*   iMod (trace.trace_update _ _ (cons _ _) with "[$Htr $Htrf]") as "[Htr Htrf]". *)
  (*   iMod ("Hclose" with "[Htrf]") as "_". *)
  (*   {(* Instantiate evars *) *)
  (*     iExists _; iFrame. iPureIntro. *)
  (*     apply mmio_pred_cons; [|eauto]. *)
  (*     constructor. } *)
  (*   iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro. *)
  (*   iIntros (res ? ? Hf). rewrite Heq in Hf. cbn in Hf. inversion Hf; subst. *)
  (*   iMod "Hclose" as "_". rewrite semTWP_val. *)
  (*   destruct bytes; first contradiction. *)
  (*   unfold mem_inv, fun_write_mmio; cbn. *)
  (*   now iFrame "Hregs Hmem Htr". *)
  (* Qed. *)

  Lemma decode_sound `{sailGS2 Σ} :
    ValidContractForeign RiscvPmpCFGVerifSpec.sep_contract_decode RiscvPmpProgram.decode.
  Proof.
    intros Γ es δ ι Heq. destruct_syminstance ι. cbn in *.
    iIntros "%Hdecode". iApply semWP2_foreign.
    iIntros (? ? ? ?) "((Hregs1 & Hregs2) & ((%memmapL & HmemL & %HmapL & HtrL & HltrL) & (%memmapR & HmemR & %HmapR & HtrR & HltrR)))".
    iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
    iIntros (res1 ? ? res2 ? ? Hf).
    rewrite evalValsProjLeftIsProjLeftEvals in Hf. rewrite evalValsProjRightIsProjRightEvals in Hf.
    rewrite Heq in Hf. cbn in Hf. inversion Hf; subst.
    inversion H0; inversion H1; subst. clear H0 H1 Hf. do 3 iModIntro.
    iMod "Hclose" as "_".
    iPoseProof (RiscvPmpModel2.mem_inv_not_modified (sg := sailGS2_sailGS_left) $! HmapL with "HmemL HtrL HltrL") as "HmemL".
    iPoseProof (RiscvPmpModel2.mem_inv_not_modified (sg := sailGS2_sailGS_right) $! HmapR with "HmemR HtrR HltrR") as "HmemR".
    iFrame "Hregs1 Hregs2 HmemL HmemR".
    destruct code; destruct instr; cbn in *;
    destruct (pure_decode _); inversion Hdecode.
    + destruct (pure_decode); inversion Hdecode.
      rewrite semWP2_val.
      iExists δ. iSplitR; first auto. iExists (NonSyncVal a a0).
      iSplitR; first auto.
      iSplitR; first (by subst). auto.
  Qed.

  (* Lemma within_mmio_sound `{!sailGS Σ} `(H: restrict_bytes bytes): *)
  (*   TValidContractForeign (RiscvPmpCFGVerifSpec.sep_contract_within_mmio H) (RiscvPmpProgram.within_mmio H). *)
  (* Proof. *)
  (*   intros Γ es δ ι Heq. destruct_syminstance ι. cbn in *. *)
  (*   iIntros "Hpre". iApply semTWP_foreign. *)
  (*   iIntros (? ?) "(Hregs & Hmem)". *)
  (*   iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro. *)
  (*   iIntros (? ? ? Hf). rewrite Heq in Hf. cbn in Hf. inversion Hf; subst. *)
  (*   rewrite semTWP_val. iMod "Hclose" as "_". iFrame "Hregs Hmem". *)
  (*   repeat iModIntro. *)
  (*   rewrite /fun_within_mmio bool_decide_and. *)
  (*   destruct inv; cbn; iDestruct "Hpre" as "([%Hlft _] & [%Hrght _])". *)
  (*   - iPureIntro; repeat split; auto. *)
  (*     rewrite -bool_decide_and bool_decide_true //. *)
  (*     split; [auto| solve_bv]. *)
  (*   - iPureIntro; repeat split; auto. *)
  (*     assert (bool_decide (withinMMIO paddr bytes) = false) as ->. *)
  (*     { rewrite bool_decide_eq_false. *)
  (*       destruct bytes; first easy. *)
  (*       assert (paddr ∈ liveAddrs)%stdpp. *)
  (*       { apply bv.in_seqBv. *)
  (*         - change (bv.of_N minAddr) with (@bv.zero xlenbits); cbn. (* TODO: add simplifying `xlenbits` to solve_bv *) solve_bv. *)
  (*         - rewrite N2Z.inj_add in Hrght. *)
  (*           change minAddr with 0%N in *; cbn in *. *)
  (*           assert (bv.unsigned paddr < Z.of_N lenAddr)%Z by Lia.lia. cbn. *)
  (*           cbv [bv.ult]. now zify. (* `solve_bv` fails because knowledge of concrete `minAddr`, `lenAddr` needed *)} *)
  (*       intros HFalse; cbn in HFalse. *)
  (*       assert (paddr ∈ mmioAddrs)%stdpp by (destruct bytes; intuition). *)
  (*       eapply mmio_ram_False; eauto. *)
  (*     } *)
  (*     auto. *)
  (* Qed. *)

    Lemma leak_sound `{sailGS2 Σ} :
    ValidContractForeign RiscvPmpCFGVerifSpec.sep_contract_leak RiscvPmpProgram.leak.
  Proof.
    intros Γ es δ ι Heq. destruct_syminstance ι. cbn in *.
    iIntros "(Hinv & %HsL & _)". iApply semWP2_foreign.
    iIntros (? ? ? ?) "((Hregs1 & Hregs2) & ((%memmapL & HmemL & %HmapL & HtrL & HltrL) & (%memmapR & HmemR & %HmapR & HtrR & HltrR)))".
    iMod (fupd_mask_subseteq empty) as "Hclose"; auto. iModIntro.
    iIntros (res1 ? ? res2 ? ? Hf).
    rewrite evalValsProjLeftIsProjLeftEvals in Hf. rewrite evalValsProjRightIsProjRightEvals in Hf.
    rewrite Heq in Hf. cbn in Hf. inversion Hf; subst.
    inversion H0; inversion H1; subst. clear H0 H1 Hf. do 3 iModIntro.
    iMod "Hclose" as "_".
    iInv "Hinv" as (t) " [>HltrfL >HltrfR]" "Hclose".
    iPoseProof (trace.trace_full_frag_eq with "HltrL HltrfL") as "%eqL".
    iPoseProof (trace.trace_full_frag_eq with "HltrR HltrfR") as "%eqR".
    cbn. subst t.
    rewrite eqR.
    iMod (trace.trace_update _ _ (cons _ _) with "[$HltrL $HltrfL]") as "[HltrL HltrfL]".
    iMod (trace.trace_update _ _ (cons _ _) with "[$HltrR $HltrfR]") as "[HltrR HltrfR]".
    iMod ("Hclose" with "[$HltrfL $HltrfR]") as "_".
    iPoseProof (RiscvPmpModel2.mem_inv_not_modified (sg := sailGS2_sailGS_left) (fun_leak μ1 (ty.projLeft leak0)) $! HmapL with "HmemL HtrL HltrL") as "HmemL".
    rewrite <- eqR.
    iPoseProof (RiscvPmpModel2.mem_inv_not_modified (sg := sailGS2_sailGS_right) (fun_leak μ2 (ty.projLeft leak0)) $! HmapR with "HmemR HtrR HltrR") as "HmemR".
    apply secLeakOtherDef in HsL. rewrite HsL. cbn.
    iFrame "Hregs1 Hregs2 HmemL HmemR".
    rewrite semWP2_val.
    iExists δ. iSplitR; first auto. iExists (SyncVal tt). auto.
  Qed.

  Lemma foreignSemCFGVerif `{sailGS2 Σ} : ForeignSem.
    intros Δ τ f; destruct f;
        eauto using read_ram_sound, write_ram_sound, (* RiscvPmpModel2.mmio_read_sound, mmio_write_sound, within_mmio_sound, *) decode_sound, leak_sound.
  Qed.

  (* Lemma foreignSemCFGVerif `{sailGS Σ} : ForeignSem. *)
  (* Proof. apply (TForeignSem_ForeignSem TforeignSemCFGVerif). Qed. *)

  Ltac destruct_syminstance ι :=
    repeat
      match type of ι with
      | Env _ (ctx.snoc _ (MkB ?s _)) =>
          string_to_ident_cps s
            ltac:(fun id =>
                    let fr := fresh id in
                    destruct (env.view ι) as [ι fr];
                    destruct_syminstance ι)
      | Env _ ctx.nil => destruct (env.view ι)
      | _ => idtac
      end.

  (* Both directions are now essentially the identity: interp_ptsto_instr NAMES
     the word (Sig.v's ptstoinstr gained a ty_word argument), so there is no `∃ v`
     left to introduce or eliminate.  The old scripts opened it with
     `iIntros "[%op ...]"` / closed it with `iExists cl`; both are gone. *)
  Lemma open_ptsto_instr_sound `{sailGS2 Σ} :
    ValidLemma RiscvPmpCFGVerifSpec.lemma_open_ptsto_instr.
  Proof.
    intros ι; destruct_syminstance ι; cbn.
    iIntros "(Hptsto & Henc & HsL)".
    now iFrame.
  Qed.

  Lemma close_ptsto_instr_sound `{sailGS2 Σ} :
    ValidLemma RiscvPmpCFGVerifSpec.lemma_close_ptsto_instr.
  Proof.
    intros ι; destruct_syminstance ι; cbn.
    iIntros "(Hptsto & Henc & HsL & _)".
    now iFrame.
  Qed.

  (* Lemma close_mmio_write_sound `{sailGS Σ} (imm : bv 12) (width : WordWidth): *)
  (*   ValidLemma (RiscvPmpCFGVerifSpec.lemma_close_mmio_write imm width). *)
  (* Proof. *)
  (*   intros ι; destruct_syminstance ι; cbn. *)
  (*   iIntros "([<- _] & [-> _])". *)
  (*   unfold interp_mmio_checked_write. *)
  (*   iPureIntro. *)
  (*   split; auto. *)
  (*   destruct width; now compute. *)
  (* Qed. *)

  (* Phase 4's abstraction lemma.  Its precondition and postcondition are the
     SAME assertion — `∃v, r ↦ v` for each register — so the semantic
     obligation is the IDENTITY, with no side condition and nothing to prove
     about the values.  All the work happens in the symbolic consume/produce:
     consuming the existential removes the chunk carrying the accumulated
     term, producing it mints a fresh variable.  That asymmetry is the whole
     mechanism (`diagnostics/havoc-abstraction-payoff.md`), and it is sound
     for exactly the reason this proof is one line. *)
  Lemma havoc_regs_sound `{sailGS2 Σ} (regs : list RegIdx) :
    ValidLemma (RiscvPmpCFGVerifSpec.lemma_havoc_regs regs).
  Proof. intros ι; iIntros "$". Qed.

  Lemma lemSemCFGVerif `{sailGS2 Σ} : LemmaSem.
  Proof.
    intros Δ []; intros ι; destruct_syminstance ι; try now iIntros "_".
    (* - apply Model.RiscvPmpModel2.open_pmp_entries_sound. *)
    (* - apply Model.RiscvPmpModel2.close_pmp_entries_sound. *)
    - apply open_ptsto_instr_sound.
    - apply close_ptsto_instr_sound.
    - apply havoc_regs_sound.
    (* - apply close_mmio_write_sound. *)
  Qed.

  (* ======================================================================= *)
  (* SOUNDNESS OF THE CFGVer-LOCAL GHOST LEMMAS (Verifier.CLem;              *)
  (* PLAN-array-invariants).  The counterpart of lemSemCFGVerif for the      *)
  (* catalogue that is NOT in Machine.v's `Lem`.  Two layers:                *)
  (*  - a STEP lemma per catalogue entry, over plain bv's, stating the       *)
  (*    big_sepL move on IrisInstanceBinary.interp_arrv (the shape of        *)
  (*    GenCompose.loop_reservoir_peel / loop_completed_push);               *)
  (*  - ValidLemma, which unpacks the assertion interpretation to the step   *)
  (*    lemma (a NonSyncVal start/count/end makes interp_arrv False).        *)
  (* The pointer/count multiplication e = a + s·n lives only here, as ring   *)
  (* identities -- never in a VC.                                            *)
  (* ======================================================================= *)
  Section CLemSound.
    Add Ring bvring_xlen : (bv.ring_theory xlenbits).
    Local Notation SV := TypeDecl.ty.SyncVal.
    (* RelVal is a pair: owning an arrv makes its arguments agree; substitute
       that, then collapse the duplicated (one per projection) pure facts. *)
    Local Ltac arr_eq1 E :=
      match type of E with
      | ?x = ?y => first [ is_var y; subst y | is_var x; subst x | clear E ]
      end.
    Local Ltac arr_eqs H :=
      let E1 := fresh "E" in let E2 := fresh "E" in let E3 := fresh "E" in
      destruct H as (E1 & E2 & E3); arr_eq1 E1; arr_eq1 E2; arr_eq1 E3.
    Local Ltac pdup := repeat match goal with H : ?P /\ ?P |- _ => destruct H as [H _] end.
    Local Ltac arrv_sync H :=
      iDestruct (interp_arrv_agree with H) as "[%Hag Harr_sync_tmp]";
      iRename "Harr_sync_tmp" into H;
      match goal with Hx : _ = _ /\ _ = _ /\ _ = _ |- _ => arr_eqs Hx end.

    (* bv ring/bit helpers the arrv proofs below share (named after the `arr`
       catalogue they were written for, deleted in PLAN-arrv Phase E) *)
    Lemma arr_neg1 : bv.of_Z (n := xlenbits) (-1) = bv.negate bv.one.
    Proof. rewrite <- bv.of_Z_one, bv.of_Z_negate. reflexivity. Qed.
    Lemma arr_neg_s (s : Z) : bv.of_Z (n := xlenbits) (- s) = bv.negate (bv.of_Z s).
    Proof. now rewrite bv.of_Z_negate. Qed.

    Lemma arr_of_nat_bin (n : bv xlenbits) : bv.of_nat (N.to_nat (bv.bin n)) = n.
    Proof. unfold bv.of_nat. rewrite N2Nat.id. apply bv.of_N_bin. Qed.

    Lemma arr_ring_flip_end (a S n : bv xlenbits) :
      bv.add a (bv.negate S)
      = bv.add (bv.add (bv.add a (bv.mul S n)) (bv.negate S)) (bv.mul (bv.negate S) n).
    Proof. ring. Qed.

    Lemma arr_of_nat_add (p q : nat) : @bv.of_nat xlenbits (p + q) = bv.add (bv.of_nat p) (bv.of_nat q).
    Proof. unfold bv.of_nat. rewrite Nat2N.inj_add. now rewrite bv.of_N_add. Qed.

    Lemma arr_ring_join_idx (a0 S n0 X : bv xlenbits) :
      bv.add (bv.add a0 (bv.mul S n0)) (bv.mul S X) = bv.add a0 (bv.mul S (bv.add n0 X)).
    Proof. ring. Qed.
    Lemma arr_ring_split_idx (a0 S K0 X : bv xlenbits) :
      bv.add a0 (bv.mul S (bv.add K0 X)) = bv.add (bv.add a0 (bv.mul S K0)) (bv.mul S X).
    Proof. ring. Qed.
    Lemma rg_of_nat_S (x : bv xlenbits) (j : nat) : bv.add (bv.add bv.one x) (bv.of_nat j) = bv.add x (bv.of_nat (S j)).
    Proof. rewrite bv.of_nat_S. ring. Qed.
    Lemma rg_of_nat_0 (x : bv xlenbits) : bv.add x (bv.of_nat 0) = x.
    Proof. change (bv.of_nat (n := xlenbits) 0) with (@bv.zero xlenbits). ring. Qed.

    (* ---- arrv: the array with its contents NAMED (Sig.v, PLAN-rsa.md
       Spike S2-arrv).  interp_arrv reads only the two runs' lists, cell i
       holding their i-th elements, so every shape move is a big_sepL
       cons/snoc over `zip`; the only RelVal reasoning is splitting a list
       value into a cons (arrv_cons_split) -- choosing SyncVal parts for a
       SyncVal list, because lifted cons is not injective. *)
    Lemma arrv_cons_split {σ} (vs : RelVal (ty.list σ)) hL tL hR tR :
      ty.projLeft vs = hL :: tL -> ty.projRight vs = hR :: tR ->
      exists x r, vs = bop.evalRel bop.cons x r /\ ty.projLeft x = hL /\ ty.projRight x = hR
                  /\ ty.projLeft r = tL /\ ty.projRight r = tR.
    Proof.
      destruct vs as [l r]; cbn; intros HL HR.
      exists (ty.NonSyncVal hL hR), (ty.NonSyncVal tL tR). subst. auto.
    Qed.

    Lemma arrv_proj_cons {σ} (x : RelVal σ) (r : RelVal (ty.list σ)) :
      ty.projLeft (bop.evalRel bop.cons x r) = ty.projLeft x :: ty.projLeft r /\
      ty.projRight (bop.evalRel bop.cons x r) = ty.projRight x :: ty.projRight r.
    Proof. destruct x, r; split; reflexivity. Qed.
    Lemma arrv_proj_snoc {σ} (vs : RelVal (ty.list σ)) (x : RelVal σ) :
      ty.projLeft (bop.evalRel bop.append vs (bop.evalRel bop.cons x (ty.SyncVal []))) =
        ty.projLeft vs ++ [ty.projLeft x] /\
      ty.projRight (bop.evalRel bop.append vs (bop.evalRel bop.cons x (ty.SyncVal []))) =
        ty.projRight vs ++ [ty.projRight x].
    Proof. destruct vs, x; split; reflexivity. Qed.

    Lemma arrv_zip_snoc {A B} (L : list A) (R : list B) l r :
      length L = length R -> zip (L ++ [l]) (R ++ [r]) = zip L R ++ [(l, r)].
    Proof.
      revert R. induction L as [|a L IH]; intros [|b R] H; cbn in *; try discriminate; [done|].
      f_equal. apply IH. lia.
    Qed.
    Lemma arrv_zip_length {A B} (L : list A) (R : list B) :
      length L = length R -> length (zip L R) = length L.
    Proof.
      revert R. induction L as [|a L IH]; intros [|b R] H; cbn in *; try discriminate; [done|].
      f_equal. apply IH. lia.
    Qed.

    Lemma arrv_ptstomem_proj `{sailGS2 Σ} {w} (addr : RVAddr) (x y : RelVal (ty.bvec (w * byte))) :
      ty.projLeft x = ty.projLeft y -> ty.projRight x = ty.projRight y ->
      interp_ptstomem addr x ⊣⊢@{iPropI Σ} interp_ptstomem addr y.
    Proof. intros HL HR. unfold interp_ptstomem. now rewrite HL HR. Qed.

    Lemma arrv_ring_zero (a s : bv xlenbits) : bv.add a (bv.mul s bv.zero) = a.
    Proof. ring. Qed.
    Lemma arrv_ring_pred (k : bv xlenbits) : k = bv.add (bv.add bv.one k) (bv.negate bv.one).
    Proof. ring. Qed.
    Lemma arrv_ring_end (a s k : bv xlenbits) :
      bv.add a (bv.mul s (bv.add bv.one k)) = bv.add (bv.add a s) (bv.mul s k).
    Proof. ring. Qed.
    Lemma arrv_ring_first (a s k : bv xlenbits) :
      bv.add (bv.add a (bv.negate s)) (bv.mul s (bv.add bv.one k)) = bv.add a (bv.mul s k).
    Proof. ring. Qed.
    Lemma arrv_ring_first0 (a s : bv xlenbits) :
      bv.add (bv.add a (bv.negate s)) (bv.mul s bv.zero) = bv.add a (bv.negate s).
    Proof. ring. Qed.
    Lemma arrv_ring_first_end (a s k : bv xlenbits) :
      bv.add a (bv.mul s k) = bv.add (bv.add a (bv.negate s)) (bv.mul s (bv.add k bv.one)).
    Proof. ring. Qed.
    Lemma arrv_ring_succ (k : bv xlenbits) : bv.add bv.one k = bv.add k bv.one.
    Proof. ring. Qed.
    Lemma arrv_ring_last (a s k : bv xlenbits) :
      bv.add (bv.add a (bv.mul s k)) s = bv.add a (bv.mul s (bv.add k bv.one)).
    Proof. ring. Qed.

    Lemma interp_arrv_take_first `{sailGS2 Σ} (w : nat) (s : Z) (a n e : bv xlenbits) vs :
      n <> bv.zero ->
      interp_arrv w s (SV a) (SV n) (SV e) vs ⊢@{iPropI Σ}
      ∃ x r, ⌜vs = bop.evalRel bop.cons x r⌝ ∗
        ⌜(bv.unsigned a + Z.of_nat w <= Z.of_N maxAddr)%Z⌝ ∗
        interp_ptstomem (SV a) x ∗
        interp_arrv w s (SV (bv.add a (bv.of_Z s))) (SV (bv.add n (bv.of_Z (-1)))) (SV e) r.
    Proof.
      intros Hn. rewrite !interp_arrv_SV; unfold interp_arrv_body. iIntros "(%He & %Hlen & %Hn' & Hcells)".
      destruct (ty.projLeft vs) as [|hL tL] eqn:EL.
      { exfalso. apply Hn. rewrite <- Hn'. reflexivity. }
      destruct (ty.projRight vs) as [|hR tR] eqn:ER; [discriminate|].
      destruct (@arrv_cons_split _ vs hL tL hR tR EL ER) as (x & r & -> & HxL & HxR & HrL & HrR).
      iExists x, r. iSplit; [done|]. rewrite !interp_arrv_SV; unfold interp_arrv_body.
      cbn [zip big_opL]. iDestruct "Hcells" as "[[%Hr0 Hc0] Hrest]".
      rewrite HrL HrR. cbn [length] in Hlen, Hn'. rewrite bv.of_nat_S in Hn'. subst n e.
      change (bv.of_nat 0) with (@bv.zero xlenbits) in Hr0. rewrite arrv_ring_zero in Hr0.
      iSplit; [done|]. iSplitL "Hc0".
      { change (bv.of_nat 0) with (@bv.zero xlenbits). rewrite arrv_ring_zero.
        iApply (arrv_ptstomem_proj with "Hc0"); cbn; congruence. }
      rewrite arr_neg1 -arrv_ring_pred.
      iSplit; [iPureIntro; apply arrv_ring_end|].
      iSplit; [iPureIntro; lia|]. iSplit; [done|].
      iApply (big_sepL_mono with "Hrest"). intros i lr _. cbn.
      rewrite bv.of_nat_S arrv_ring_end. auto.
    Qed.

    Lemma interp_arrv_add_first `{sailGS2 Σ} (w : nat) (s : Z) (a n e : bv xlenbits) vs x :
      interp_arrv w s (SV a) (SV n) (SV e) vs ∗
      ⌜(bv.unsigned (bv.add a (bv.of_Z (- s))) + Z.of_nat w <= Z.of_N maxAddr)%Z⌝ ∗
      interp_ptstomem (SV (bv.add a (bv.of_Z (- s)))) x ⊢@{iPropI Σ}
      interp_arrv w s (SV (bv.add a (bv.of_Z (- s)))) (SV (bv.add n (bv.of_Z 1))) (SV e)
        (bop.evalRel bop.cons x vs).
    Proof.
      rewrite !interp_arrv_SV; unfold interp_arrv_body. destruct (arrv_proj_cons x vs) as [-> ->].
      iIntros "[(%He & %Hlen & %Hn' & Hcells) [%Hr Hc]]".
      subst n e. rewrite arr_neg_s in Hr. rewrite !arr_neg_s bv.of_Z_one.
      iSplit; [iPureIntro; apply arrv_ring_first_end|].
      iSplit; [iPureIntro; cbn; lia|].
      iSplit; [iPureIntro; cbn [length]; rewrite bv.of_nat_S; apply arrv_ring_succ|].
      cbn [zip big_opL]. iSplitL "Hc".
      { change (bv.of_nat 0) with (@bv.zero xlenbits). rewrite arrv_ring_first0.
        iSplit; [done|]. iApply (arrv_ptstomem_proj with "Hc"); cbn; reflexivity. }
      iApply (big_sepL_mono with "Hcells"). intros i lr _. cbn.
      rewrite bv.of_nat_S arrv_ring_first. auto.
    Qed.

    Lemma interp_arrv_add_last `{sailGS2 Σ} (w : nat) (s : Z) (a n e : bv xlenbits) vs x :
      interp_arrv w s (SV a) (SV n) (SV e) vs ∗
      ⌜(bv.unsigned e + Z.of_nat w <= Z.of_N maxAddr)%Z⌝ ∗
      interp_ptstomem (SV e) x ⊢@{iPropI Σ}
      interp_arrv w s (SV a) (SV (bv.add n (bv.of_Z 1))) (SV (bv.add e (bv.of_Z s)))
        (bop.evalRel bop.append vs (bop.evalRel bop.cons x (ty.SyncVal []))).
    Proof.
      rewrite !interp_arrv_SV; unfold interp_arrv_body. destruct (arrv_proj_snoc vs x) as [-> ->].
      iIntros "[(%He & %Hlen & %Hn' & Hcells) [%Hr Hc]]".
      subst n e. rewrite bv.of_Z_one.
      iSplit; [iPureIntro; apply arrv_ring_last|].
      iSplit; [iPureIntro; rewrite !length_app; cbn; lia|].
      iSplit; [iPureIntro; rewrite length_app Nat.add_comm; cbn [Nat.add];
               rewrite bv.of_nat_S; apply arrv_ring_succ|].
      rewrite arrv_zip_snoc; [|exact Hlen]. rewrite big_sepL_app. iFrame "Hcells".
      cbn [big_opL]. rewrite Nat.add_0_r (@arrv_zip_length _ _ _ _ Hlen). iSplitL; [|done].
      iSplit; [done|]. iApply (arrv_ptstomem_proj with "Hc"); cbn; reflexivity.
    Qed.

    Lemma clem_arrv_take_first_sound `{sailGS2 Σ} (w : nat) (s : Z) (t : string) :
      ValidLemma (clem_lemma (clem_arrv_take_first w s t)).
    Proof.
      intros ι. cbv [clemv_ctx] in ι. destruct_syminstance ι.
      destruct a as [a a']; destruct n as [n n']; destruct e as [e e'];
        cbn -[interp_arrv interp_ptstomem].
      iIntros "[Harr [%Hne _]]". arrv_sync "Harr". pdup.
      iDestruct (interp_arrv_take_first with "Harr") as (x r) "(%Hvs & %Hr & Hc & Harr)";
        [exact Hne|].
      iExists x, r. iFrame "Hc Harr". auto.
    Qed.

    Lemma clem_arrv_add_first_sound `{sailGS2 Σ} (w : nat) (s : Z) (t : string) :
      ValidLemma (clem_lemma (clem_arrv_add_first w s t)).
    Proof.
      intros ι. cbv [clemv_ctx] in ι. destruct_syminstance ι.
      destruct a as [a a']; destruct n as [n n']; destruct e as [e e'];
        cbn -[interp_arrv interp_ptstomem].
      iIntros "[Harr [Hc [%Hr _]]]". arrv_sync "Harr". pdup.
      iApply interp_arrv_add_first. iFrame "Harr Hc". auto.
    Qed.

    Lemma clem_arrv_add_last_sound `{sailGS2 Σ} (w : nat) (s : Z) (t : string) :
      ValidLemma (clem_lemma (clem_arrv_add_last w s t)).
    Proof.
      intros ι. cbv [clemv_ctx] in ι. destruct_syminstance ι.
      destruct a as [a a']; destruct n as [n n']; destruct e as [e e'];
        cbn -[interp_arrv interp_ptstomem].
      iIntros "[Harr [Hc [%Hr _]]]". arrv_sync "Harr". pdup.
      iApply interp_arrv_add_last. iFrame "Harr Hc". auto.
    Qed.

    (* ---- arrv, PLAN-arrv Phase A: the rest of the catalogue.  Each shape
       move is again a big_sepL move over `zip`; the new RelVal splits are
       arrv_snoc_split (take_last) and arrv_app_split (split).  `pad` is the
       one lemma that needs the LENGTH of a value from its count: the count
       is the length mod 2^32, so interp_arrv_length bounds the length by
       pigeonhole -- for w >= 1 the cells are disjoint in-range memory
       (arrv_excl_nodup, arrv_pigeon) -- and interp_arrv_count0 follows. *)
    (* ---- generic: exclusive resources at pairwise-distinct keys ---- *)
    Lemma arrv_excl_nodup {PROP : bi} {A} `{!BiAffine PROP} (Q : nat -> PROP) (M : nat)
        (f : nat -> nat) (Φ : nat -> A -> PROP) (l : list A) :
      (forall k, Q k ∗ Q k ⊢ False) ->
      (forall k, Q k ⊢ ⌜k < M⌝) ->
      (forall i x, Φ i x ⊢ Q (f i)) ->
      ([∗ list] i ↦ x ∈ l, Φ i x) ⊢
        ⌜NoDup (map f (seq 0 (length l))) /\ Forall (fun k => k < M) (map f (seq 0 (length l)))⌝.
    Proof.
      intros Hex HM. revert f Φ. induction l as [|x l IH]; intros f Φ HΦ.
      { iIntros "_". iPureIntro. split; constructor. }
      rewrite big_sepL_cons. cbn [length seq List.map]. rewrite -seq_shift map_map.
      iIntros "[H0 Hl]". iDestruct (HΦ with "H0") as "H0".
      destruct (in_dec Nat.eq_dec (f 0) (map (fun i => f (S i)) (seq 0 (length l)))) as [Hin|Hni].
      { apply in_map_iff in Hin as (j & Hj & Hjin%in_seq).
        destruct (lookup_lt_is_Some_2 l j) as [y Hy]; [lia|].
        iDestruct (big_sepL_lookup with "Hl") as "Hy"; [exact Hy|].
        iDestruct (HΦ with "Hy") as "Hy". rewrite Hj.
        iDestruct (Hex with "[$H0 $Hy]") as "[]". }
      iDestruct (HM with "H0") as %H0.
      iDestruct (IH (fun i => f (S i)) (fun i => Φ (S i)) with "Hl") as %[Hnd Hf];
        [intros; apply HΦ|].
      iPureIntro.
      split; [apply NoDup_cons; split; [rewrite elem_of_list_In; exact Hni|exact Hnd]|constructor; done].
    Qed.

    Lemma arrv_pigeon (L : list nat) (M : nat) :
      NoDup L -> Forall (fun k => k < M) L -> length L <= M.
    Proof.
      intros Hnd Hf. rewrite -(length_seq M 0).
      apply submseteq_length, NoDup_submseteq; [exact Hnd|].
      intros x Hx. apply elem_of_seq. rewrite Forall_forall in Hf.
      specialize (Hf x Hx). lia.
    Qed.

    Lemma arrv_zip_rev {A B} (L : list A) (R : list B) :
      length L = length R -> zip (rev L) (rev R) = rev (zip L R).
    Proof.
      revert R. induction L as [|a L IH]; intros [|b R] H; cbn in *; try discriminate; [done|].
      rewrite arrv_zip_snoc; [|rewrite !length_rev; lia]. rewrite IH; [done|lia].
    Qed.
    Lemma arrv_big_sepL_rev {PROP : bi} {A} (Φ : nat -> A -> PROP) (l : list A) :
      ([∗ list] k ↦ x ∈ rev l, Φ k x) ⊣⊢ [∗ list] k ↦ x ∈ l, Φ (length l - S k) x.
    Proof.
      induction l as [|y l IH]; [done|]. cbn [rev].
      rewrite big_sepL_app big_sepL_singleton big_sepL_cons IH length_rev Nat.add_0_r.
      cbn [length]. rewrite bi.sep_comm. replace (S (length l) - 1) with (length l) by lia. f_equiv.
      apply big_sepL_proper. intros k x Hk. apply lookup_lt_Some in Hk.
      replace (S (length l) - S (S k)) with (length l - S k) by lia. done.
    Qed.

    Lemma arrv_proj_app {σ} (v1 v2 : RelVal (ty.list σ)) :
      ty.projLeft (bop.evalRel bop.append v1 v2) = ty.projLeft v1 ++ ty.projLeft v2 /\
      ty.projRight (bop.evalRel bop.append v1 v2) = ty.projRight v1 ++ ty.projRight v2.
    Proof. destruct v1, v2; split; reflexivity. Qed.
    Lemma arrv_proj_rev {σ} (vs : RelVal (ty.list σ)) :
      ty.projLeft (uop.evalRel uop.rev vs) = rev (ty.projLeft vs) /\
      ty.projRight (uop.evalRel uop.rev vs) = rev (ty.projRight vs).
    Proof. destruct vs; split; reflexivity. Qed.

    Lemma interp_arrv_proj `{sailGS2 Σ} w s (a n e : RelVal ty_xlenbits) x y :
      ty.projLeft x = ty.projLeft y -> ty.projRight x = ty.projRight y ->
      interp_arrv w s a n e x ⊣⊢@{iPropI Σ} interp_arrv w s a n e y.
    Proof. intros HL HR. unfold interp_arrv, interp_arrv_body. by rewrite HL HR. Qed.

    (* a cell of a w ≥ 1 array owns (the left copy of) its first byte *)
    Definition arrv_byteQ `{sailGS2 Σ} (k : nat) : iProp Σ :=
      ∃ (x : bv xlenbits) b, ⌜Z.to_nat (bv.unsigned x) = k /\ (bv.unsigned x < Z.of_N maxAddr)%Z⌝ ∗
        @RiscvPmpIrisInstance.interp_ptsto _ memGS2_memGS_left x b.

    Lemma interp_arrv_length `{sailGS2 Σ} (w : nat) (s : Z) (a n e : bv xlenbits) vs :
      interp_arrv (S w) s (SV a) (SV n) (SV e) vs ⊢@{iPropI Σ}
      ⌜length (ty.projLeft vs) <= N.to_nat maxAddr⌝.
    Proof.
      rewrite !interp_arrv_SV; unfold interp_arrv_body. iIntros "(%He & %Hlen & %Hn & Hcells)".
      iDestruct (arrv_excl_nodup arrv_byteQ (N.to_nat maxAddr)
         (fun i => Z.to_nat (bv.unsigned (bv.add a (bv.mul (bv.of_Z s) (bv.of_nat i)))))
         with "Hcells") as %[Hnd Hf].
      - intros k. iIntros "[(%x1 & %b1 & [%E1 _] & H1) (%x2 & %b2 & [%E2 _] & H2)]".
        unfold RiscvPmpIrisInstance.interp_ptsto.
        iDestruct (pointsto_ne with "H1 H2") as %Hne. iPureIntro. apply Hne.
        apply bv.unsigned_inj. pose proof (bv.unsigned_bounds x1). pose proof (bv.unsigned_bounds x2). lia.
      - intros k. iIntros "(%x & %b & [%E %Hr] & _)". iPureIntro.
        subst k. pose proof (bv.unsigned_bounds x). lia.
      - intros i lr. cbv beta zeta. unfold interp_ptstomem. iIntros "[%Hr [Hl _]]".
        cbn [RiscvPmpIrisInstance.interp_ptstomem ty.projLeft]. destruct (bv.appView _ _ _) as [b0 bs].
        iDestruct "Hl" as "[Hb _]". iExists (bv.add a (bv.mul (bv.of_Z s) (bv.of_nat i))), b0.
        iSplit; [iPureIntro; split; [done|lia]|iExact "Hb"].
      - iPureIntro. pose proof (@arrv_pigeon _ _ Hnd Hf) as Hp.
        rewrite length_map length_seq arrv_zip_length in Hp; done.
    Qed.

    (* a w ≥ 1 array with count 0 holds the empty list in both runs *)
    Lemma interp_arrv_count0 `{sailGS2 Σ} (w : nat) (s : Z) (a e : bv xlenbits) vs :
      interp_arrv (S w) s (SV a) (SV bv.zero) (SV e) vs ⊢@{iPropI Σ}
      ⌜ty.projLeft vs = [] /\ ty.projRight vs = []⌝.
    Proof.
      iIntros "H". iDestruct (interp_arrv_length with "H") as %Hb.
      rewrite !interp_arrv_SV; unfold interp_arrv_body. iDestruct "H" as "(_ & %Hlen & %Hn & _)". iPureIntro.
      pose proof maxAddr_rep as Hm.
      assert (Hs : (N.of_nat (length (ty.projLeft vs)) < bv.exp2 xlenbits)%N) by lia.
      apply (f_equal (@bv.bin xlenbits)) in Hn. rewrite (bv.bin_of_nat_small Hs) in Hn. cbn in Hn.
      apply (f_equal N.to_nat) in Hn. rewrite Nat2N.id in Hn.
      pose proof Hn as Hn'. rewrite Hlen in Hn'.
      apply length_zero_iff_nil in Hn, Hn'. split; assumption.
    Qed.

    Lemma arrv_snoc_split {σ} (vs : RelVal (ty.list σ)) tL hL tR hR :
      ty.projLeft vs = tL ++ [hL] -> ty.projRight vs = tR ++ [hR] ->
      exists x r, vs = bop.evalRel bop.append r (bop.evalRel bop.cons x (ty.SyncVal []))
        /\ ty.projLeft x = hL /\ ty.projRight x = hR /\ ty.projLeft r = tL /\ ty.projRight r = tR.
    Proof.
      destruct vs as [l r]; cbn; intros HL HR.
      exists (ty.NonSyncVal hL hR), (ty.NonSyncVal tL tR). subst. auto.
    Qed.

    Lemma interp_arrv_take_last `{sailGS2 Σ} (w : nat) (s : Z) (a n e : bv xlenbits) vs :
      n <> bv.zero ->
      interp_arrv w s (SV a) (SV n) (SV e) vs ⊢@{iPropI Σ}
      ∃ x r, ⌜vs = bop.evalRel bop.append r (bop.evalRel bop.cons x (ty.SyncVal []))⌝ ∗
        ⌜(bv.unsigned (bv.add e (bv.of_Z (- s))) + Z.of_nat w <= Z.of_N maxAddr)%Z⌝ ∗
        interp_ptstomem (SV (bv.add e (bv.of_Z (- s)))) x ∗
        interp_arrv w s (SV a) (SV (bv.add n (bv.of_Z (-1)))) (SV (bv.add e (bv.of_Z (- s)))) r.
    Proof.
      intros Hn. rewrite !interp_arrv_SV; unfold interp_arrv_body. iIntros "(%He & %Hlen & %Hn' & Hcells)".
      destruct (ty.projLeft vs) as [|y0 l0] eqn:EL0.
      { exfalso. apply Hn. rewrite <- Hn'. reflexivity. }
      destruct (exists_last (l := y0 :: l0) ltac:(discriminate)) as (tL & hL & EL).
      destruct (ty.projRight vs) as [|z0 m0] eqn:ER0; [cbn in Hlen; discriminate|].
      destruct (exists_last (l := z0 :: m0) ltac:(discriminate)) as (tR & hR & ER).
      rewrite <- EL0 in EL. rewrite <- ER0 in ER.
      destruct (@arrv_snoc_split _ vs tL hL tR hR EL ER) as (x & r & -> & HxL & HxR & HrL & HrR).
      iExists x, r. iSplit; [done|]. rewrite !interp_arrv_SV; unfold interp_arrv_body.
      rewrite EL0 in EL. rewrite ER0 in ER. rewrite EL ER in Hlen Hn' |- *. rewrite HrL HrR.
      rewrite !length_app in Hlen. cbn [length] in Hlen.
      (* not lia: the two lengths' hidden type indices differ *)
      assert (HlT : length tL = length tR) by (apply Nat.add_cancel_r in Hlen; exact Hlen).
      rewrite length_app Nat.add_comm in Hn'. cbn [Nat.add] in Hn'. rewrite bv.of_nat_S in Hn'.
      subst n e.
      rewrite arrv_zip_snoc; [|exact HlT]. rewrite big_sepL_app. cbn [big_opL].
      iDestruct "Hcells" as "[Hrest [[%Hr0 Hc0] _]]".
      rewrite Nat.add_0_r (@arrv_zip_length _ _ _ _ HlT) in Hr0 |- *.
      assert (Elast : bv.add (bv.add a (bv.mul (bv.of_Z s) (bv.add bv.one (bv.of_nat (length tL)))))
                         (bv.of_Z (- s)) = bv.add a (bv.mul (bv.of_Z s) (bv.of_nat (length tL)))).
      { rewrite arr_neg_s. ring. }
      rewrite Elast. iSplit; [done|]. iSplitL "Hc0".
      { iApply (arrv_ptstomem_proj with "Hc0"); cbn; congruence. }
      assert (arrv_ring_pred : forall k : bv xlenbits, k = bv.add (bv.add bv.one k) (bv.negate bv.one)) by (intros; ring).
      rewrite arr_neg1 -arrv_ring_pred.
      iSplit; [done|]. iSplit; [done|]. iSplit; [done|]. iExact "Hrest".
    Qed.

    Lemma interp_arrv_nonempty `{sailGS2 Σ} (w : nat) (s : Z) (a n e : bv xlenbits) vs :
      a <> e ->
      interp_arrv w s (SV a) (SV n) (SV e) vs ⊢@{iPropI Σ} ⌜n <> bv.zero⌝.
    Proof.
      intros Hae. rewrite !interp_arrv_SV; unfold interp_arrv_body. iIntros "(%He & _)". iPureIntro. intros ->.
      apply Hae. subst e. symmetry. apply arrv_ring_zero.
    Qed.

    Lemma interp_arrv_empty `{sailGS2 Σ} (w : nat) (s : Z) (a : bv xlenbits) :
      ⊢@{iPropI Σ} interp_arrv w s (SV a) (SV bv.zero) (SV a) (ty.SyncVal []).
    Proof.
      rewrite !interp_arrv_SV; unfold interp_arrv_body. iSplit; [iPureIntro; symmetry; apply arrv_ring_zero|]. cbn. auto.
    Qed.

    Lemma interp_arrv_empty_elim `{sailGS2 Σ} (w : nat) (s : Z) (a e : bv xlenbits) vs :
      interp_arrv w s (SV a) (SV bv.zero) (SV e) vs ⊢@{iPropI Σ} ⌜a = e⌝.
    Proof. rewrite !interp_arrv_SV; unfold interp_arrv_body. iIntros "(%He & _)". iPureIntro. subst e. symmetry. apply arrv_ring_zero. Qed.

    Lemma interp_arrv_flip `{sailGS2 Σ} (w : nat) (s : Z) (a n e : bv xlenbits) vs :
      interp_arrv w s (SV a) (SV n) (SV e) vs ⊢@{iPropI Σ}
      interp_arrv w (- s) (SV (bv.add e (bv.of_Z (- s)))) (SV n) (SV (bv.add a (bv.of_Z (- s))))
        (uop.evalRel uop.rev vs).
    Proof.
      rewrite !interp_arrv_SV; unfold interp_arrv_body. destruct (arrv_proj_rev vs) as [-> ->].
      iIntros "(%He & %Hlen & %Hn & Hcells)". subst e n. rewrite !arr_neg_s.
      iSplit; [iPureIntro; apply arr_ring_flip_end|].
      rewrite !length_rev. iSplit; [done|]. iSplit; [done|].
      rewrite arrv_zip_rev; [|exact Hlen]. rewrite arrv_big_sepL_rev.
      iApply (big_sepL_mono with "Hcells"). intros i lr Hi. apply lookup_lt_Some in Hi.
      rewrite (@arrv_zip_length _ _ _ _ Hlen) in Hi |- *. cbv beta.
      set (L := length (ty.projLeft vs)) in *.
      assert (E : bv.add (bv.add (bv.add a (bv.mul (bv.of_Z s) (bv.of_nat L))) (bv.negate (bv.of_Z s)))
                         (bv.mul (bv.negate (bv.of_Z s)) (bv.of_nat (L - S i)))
                  = bv.add a (bv.mul (bv.of_Z s) (bv.of_nat i))).
      { replace L with ((L - S i) + S i)%nat at 1 by lia.
        rewrite arr_of_nat_add bv.of_nat_S. ring. }
      rewrite E. done.
    Qed.

    Lemma interp_arrv_join `{sailGS2 Σ} (w : nat) (s : Z) (a n e n2 e2 : bv xlenbits) v1 v2 :
      interp_arrv w s (SV a) (SV n) (SV e) v1 ∗ interp_arrv w s (SV e) (SV n2) (SV e2) v2
      ⊢@{iPropI Σ} interp_arrv w s (SV a) (SV (bv.add n n2)) (SV e2) (bop.evalRel bop.append v1 v2).
    Proof.
      rewrite !interp_arrv_SV; unfold interp_arrv_body. destruct (arrv_proj_app v1 v2) as [-> ->].
      iIntros "[(%He & %Hl1 & %Hn & H1) (%He2 & %Hl2 & %Hn2 & H2)]". subst e2 e n n2.
      iSplit; [iPureIntro; apply arr_ring_join_idx|].
      iSplit; [iPureIntro; rewrite !length_app Hl1 Hl2; reflexivity|].
      iSplit; [iPureIntro; rewrite length_app arr_of_nat_add; reflexivity|].
      rewrite zip_with_app; [|exact Hl1]. rewrite big_sepL_app. iFrame "H1".
      iApply (big_sepL_mono with "H2"). intros i lr _. cbv beta.
      rewrite (@arrv_zip_length _ _ _ _ Hl1) arr_of_nat_add arr_ring_join_idx. done.
    Qed.

    Lemma interp_arrv_lockstep `{sailGS2 Σ} (w : nat) (s : Z) (a1 n e1 a2 e2 : bv xlenbits) v1 v2 :
      a1 = e1 ->
      interp_arrv w s (SV a1) (SV n) (SV e1) v1 ∗ interp_arrv w s (SV a2) (SV n) (SV e2) v2
      ⊢@{iPropI Σ} ⌜a2 = e2⌝.
    Proof.
      intros Ha. rewrite !interp_arrv_SV; unfold interp_arrv_body. iIntros "[(%He1 & _) (%He2 & _)]". iPureIntro.
      subst e1 e2. assert (Hz : bv.mul (bv.of_Z s) n = bv.zero).
      { transitivity (bv.add (bv.add a1 (bv.mul (bv.of_Z s) n)) (bv.negate a1)); [ring|].
        rewrite -He1. ring. }
      rewrite Hz. symmetry. ring.
    Qed.

    Lemma arrv_app_split {σ} (vs : RelVal (ty.list σ)) (k : nat) :
      exists v1 v2, vs = bop.evalRel bop.append v1 v2 /\
        ty.projLeft v1 = take k (ty.projLeft vs) /\ ty.projRight v1 = take k (ty.projRight vs) /\
        ty.projLeft v2 = drop k (ty.projLeft vs) /\ ty.projRight v2 = drop k (ty.projRight vs).
    Proof.
      destruct vs as [l r].
      exists (ty.NonSyncVal (take k l) (take k r)), (ty.NonSyncVal (drop k l) (drop k r)).
      cbn. rewrite !take_drop. auto.
    Qed.

    Lemma interp_arrv_split `{sailGS2 Σ} (w : nat) (s : Z) (k : N) (a n e : bv xlenbits) vs :
      (bv.bin (@bv.of_N xlenbits k) <= bv.bin n)%N ->
      interp_arrv w s (SV a) (SV n) (SV e) vs ⊢@{iPropI Σ}
      ∃ v1 v2, ⌜vs = bop.evalRel bop.append v1 v2⌝ ∗
        interp_arrv w s (SV a) (SV (bv.of_N k)) (SV (bv.add a (bv.of_Z (s * Z.of_N k)))) v1 ∗
        interp_arrv w s (SV (bv.add a (bv.of_Z (s * Z.of_N k)))) (SV (bv.add n (bv.of_Z (- Z.of_N k))))
          (SV e) v2.
    Proof.
      intros Hk. set (K := @bv.of_N xlenbits k) in *.
      assert (EsK : @bv.of_Z xlenbits (s * Z.of_N k) = bv.mul (bv.of_Z s) K).
      { unfold K. rewrite -bv.of_Z_N bv.of_Z_mul. reflexivity. }
      assert (EnK : bv.add n (@bv.of_Z xlenbits (- Z.of_N k)) = bv.sub n K).
      { unfold K. rewrite -bv.of_Z_negate bv.of_Z_N. reflexivity. }
      rewrite EsK EnK. rewrite !interp_arrv_SV; unfold interp_arrv_body. iIntros "(%He & %Hlen & %Hn & Hc)".
      set (kn := N.to_nat (bv.bin K)).
      assert (EK : @bv.of_nat xlenbits kn = K).
      { unfold kn, bv.of_nat. rewrite N2Nat.id. apply bv.of_N_bin. }
      assert (Hkn : (kn <= length (ty.projLeft vs))%nat).
      { subst n. unfold kn. pose proof (bv.bin_of_nat_decr (n := xlenbits) (length (ty.projLeft vs))). lia. }
      destruct (@arrv_app_split _ vs kn) as (v1 & v2 & -> & H1L & H1R & H2L & H2R).
      iExists v1, v2. iSplit; [done|]. rewrite !interp_arrv_SV; unfold interp_arrv_body.
      rewrite H1L H1R H2L H2R.
      set (L := ty.projLeft (bop.evalRel bop.append v1 v2)) in *.
      set (R := ty.projRight (bop.evalRel bop.append v1 v2)) in *.
      assert (HtL : length (take kn L) = kn) by (rewrite length_take; lia).
      assert (HtR : length (take kn R) = kn) by (rewrite length_take; lia).
      assert (EZ : zip L R = zip (take kn L) (take kn R) ++ zip (drop kn L) (drop kn R)).
      { rewrite -zip_with_app; [rewrite !take_drop; reflexivity|congruence]. }
      rewrite EZ big_sepL_app. iDestruct "Hc" as "[Hc1 Hc2]".
      iSplitL "Hc1".
      { iSplit; [done|]. iSplit; [iPureIntro; congruence|]. iSplit; [iPureIntro; rewrite HtL; exact EK|].
        iExact "Hc1". }
      assert (EL : @bv.of_nat xlenbits (length L) = bv.add K (bv.of_nat (length L - kn))).
      { replace (length L) with (kn + (length L - kn))%nat at 1 by lia.
        rewrite arr_of_nat_add EK. reflexivity. }
      subst n e. rewrite EL.
      assert (R1 : forall a0 S0 K0 D : bv xlenbits,
        bv.add a0 (bv.mul S0 (bv.add K0 D)) = bv.add (bv.add a0 (bv.mul S0 K0)) (bv.mul S0 (bv.sub (bv.add K0 D) K0))).
      { intros. unfold bv.sub. ring. }
      assert (R2 : forall K0 D : bv xlenbits, D = bv.sub (bv.add K0 D) K0).
      { intros. unfold bv.sub. ring. }
      iSplit; [iPureIntro; apply R1|].
      iSplit; [iPureIntro; rewrite !length_drop Hlen; reflexivity|].
      iSplit; [iPureIntro; rewrite length_drop; apply R2|].
      iApply (big_sepL_mono with "Hc2"). intros i lr _. cbv beta.
      rewrite (@arrv_zip_length _ _ _ _ (eq_trans HtL (eq_sym HtR))) HtL arr_of_nat_add EK arr_ring_split_idx. done.
    Qed.

    Lemma clem_arrv_take_last_sound `{sailGS2 Σ} (w : nat) (s : Z) (t : string) :
      ValidLemma (clem_lemma (clem_arrv_take_last w s t)).
    Proof.
      intros ι. cbv [clemv_ctx] in ι. destruct_syminstance ι.
      destruct a as [a a']; destruct n as [n n']; destruct e as [e e'];
        cbn -[interp_arrv interp_ptstomem].
      iIntros "[Harr [%Hne _]]". arrv_sync "Harr". pdup.
      iDestruct (interp_arrv_take_last with "Harr") as (x r) "(%Hvs & %Hr & Hc & Harr)";
        [exact Hne|].
      iExists x, r. iFrame "Hc Harr". auto.
    Qed.

    Lemma clem_arrv_nonempty_sound `{sailGS2 Σ} (w : nat) (s : Z) (t : string) :
      ValidLemma (clem_lemma (clem_arrv_nonempty w s t)).
    Proof.
      intros ι. cbv [clemv_ctx] in ι. destruct_syminstance ι.
      destruct a as [a a']; destruct n as [n n']; destruct e as [e e'];
        cbn -[interp_arrv].
      iIntros "[Harr [%Hne _]]". arrv_sync "Harr". pdup.
      iDestruct (interp_arrv_nonempty with "Harr") as %Hn; [exact Hne|].
      iFrame "Harr". iSplit; [|done]. iPureIntro. split; exact Hn.
    Qed.

    Lemma clem_arrv_empty_sound `{sailGS2 Σ} (w : nat) (s : Z) (t : string) :
      ValidLemma (clem_lemma (clem_arrv_empty w s t)).
    Proof.
      intros ι. destruct_syminstance ι.
      (* a NonSyncVal address is ruled out by the secLeak precondition *)
      destruct a as [a a']; cbn -[interp_arrv].
      iIntros "[%Ha _]". hnf in Ha. cbn in Ha. subst a'. iApply interp_arrv_empty.
    Qed.

    (* count 0 gives start = end, and for w ≥ 1 the value [] (both runs hold
       the empty list, interp_arrv_count0, and that pair IS SyncVal []) *)
    Lemma clem_arrv_empty_elim_sound `{sailGS2 Σ} (w : nat) (s : Z) (t : string) :
      ValidLemma (clem_lemma (clem_arrv_empty_elim w s t)).
    Proof.
      intros ι. destruct_syminstance ι.
      destruct a as [a a']; destruct e as [e e'];
        cbn -[interp_arrv].
      iIntros "Harr". arrv_sync "Harr". pdup. iDestruct (interp_arrv_empty_elim with "Harr") as %Hae.
      destruct w as [|w]; cbn -[interp_arrv].
      - iSplit; [|done]. iSplit; iPureIntro; [split; exact Hae|done].
      - iDestruct (interp_arrv_count0 with "Harr") as %[HL HR].
        iSplit; (iSplit; [iPureIntro|done]).
        + split; exact Hae.
        + destruct vs as [vl vr]; cbn in *; subst; reflexivity.
    Qed.

    (* the same fact, the array kept; w = 0: the precondition is False *)
    Lemma clem_arrv_count0_sound `{sailGS2 Σ} (w : nat) (s : Z) (t : string) :
      ValidLemma (clem_lemma (clem_arrv_count0 w s t)).
    Proof.
      intros ι. destruct_syminstance ι. destruct w as [|w].
      { cbn -[interp_arrv]. iIntros "(_ & %Hf & _)". done. }
      destruct a as [a a']; destruct e as [e e'];
        cbn -[interp_arrv].
      iIntros "[Harr _]". arrv_sync "Harr". pdup.
      iDestruct (interp_arrv_count0 with "Harr") as %[HL HR].
      iFrame "Harr". iSplit; [|done]. iPureIntro.
      destruct vs as [vl vr]; cbn in *; subst; reflexivity.
    Qed.

    Lemma clem_arrv_lockstep_sound `{sailGS2 Σ} (w : nat) (s : Z) (t1 t2 : string) :
      ValidLemma (clem_lemma (clem_arrv_lockstep w s t1 t2)).
    Proof.
      intros ι. destruct_syminstance ι.
      destruct a1 as [a1 a1']; destruct n as [n n']; destruct e1 as [e1 e1'];
        destruct a2 as [a2 a2']; destruct e2 as [e2 e2'];
        cbn -[interp_arrv].
      iIntros "[H1 [H2 [%Heq _]]]". arrv_sync "H1". arrv_sync "H2". pdup.
      iAssert ⌜a2 = e2⌝%I as %He2.
      { iApply (interp_arrv_lockstep with "[$H1 $H2]"). exact Heq. }
      iFrame "H1 H2". iSplit; [|done]. iPureIntro. split; exact He2.
    Qed.

    Lemma clem_arrv_drop_sound `{sailGS2 Σ} (w : nat) (s : Z) (t : string) :
      ValidLemma (clem_lemma (clem_arrv_drop w s t)).
    Proof. intros ι. cbn -[interp_arrv]. iIntros "_". iSplit; done. Qed.

    Lemma clem_arrv_flip_sound `{sailGS2 Σ} (w : nat) (s : Z) (t : string) :
      ValidLemma (clem_lemma (clem_arrv_flip w s t)).
    Proof.
      intros ι. cbv [clemv_ctx] in ι. destruct_syminstance ι.
      destruct a as [a a']; destruct n as [n n']; destruct e as [e e'];
        cbn -[interp_arrv].
      iIntros "Harr". arrv_sync "Harr". pdup. by iApply interp_arrv_flip.
    Qed.

    Lemma clem_arrv_join_sound `{sailGS2 Σ} (w : nat) (s : Z) (t1 t2 t : string) :
      ValidLemma (clem_lemma (clem_arrv_join w s t1 t2 t)).
    Proof.
      intros ι. destruct_syminstance ι.
      destruct a as [a a']; destruct n as [n n']; destruct e as [e e'];
        destruct n2 as [n2 n2']; destruct e2 as [e2 e2'];
        cbn -[interp_arrv].
      iIntros "[H1 H2]". arrv_sync "H1". arrv_sync "H2". pdup. iApply (interp_arrv_join with "[$H1 $H2]").
    Qed.

    Lemma clem_arrv_split_sound `{sailGS2 Σ} (w : nat) (s : Z) (t : string) (k : N) :
      ValidLemma (clem_lemma (clem_arrv_split w s t k)).
    Proof.
      intros ι. cbv [clemv_ctx] in ι. destruct_syminstance ι.
      destruct a as [a a']; destruct n as [n n']; destruct e as [e e'];
        cbn -[interp_arrv].
      iIntros "[Harr [%Hle _]]". arrv_sync "Harr". pdup.
      iDestruct (interp_arrv_split w s k with "Harr") as (v1 v2) "(%Hvs & H1 & H2)"; [exact Hle|].
      iExists v1, v2. iFrame "H1 H2". auto.
    Qed.

    (* ---- arrv, PLAN-arrv Phase B: the word ⇄ byte view of a VALUE
       (D6-D8).  `uop.regroup` evaluates to `flat_map bv.le_bytes`, and
       le_bytes splits a cell by the same `appView 8` recursion as
       interp_ptstomem, so a k-byte cell IS the byte cells of its bytes
       (arrv_cell_bytes), and a word array IS the byte array of
       `regroup` (arrv_words_bytes, both directions).  of_bytes also needs
       k <u 2^30: ·4 is not injective mod 2^32. *)
    Lemma arrv_app_nil8 (b : bv byte) : @bv.app 8 0 b bv.nil = b.
    Proof.
      rewrite bv.app_nil_r. symmetry. apply (Eqdep_dec.eq_rect_eq_dec Nat.eq_dec).
    Qed.

    (* a one-byte cell is a points-to of its byte *)
    Lemma arrv_byte_cell `{sailGS2 Σ} (x : bv xlenbits) (bl br : bv byte) :
      interp_ptstomem (width := 1) (SV x) (NonSyncVal bl br) ⊣⊢@{iPropI Σ}
      interp_ptsto (SV x) (NonSyncVal bl br).
    Proof.
      assert (EV : (NonSyncVal bl br : RelVal (ty.bvec (1 * byte))) =
                   ty.liftBinOp (σ1 := ty.bvec byte) (σ2 := ty.bvec (0 * byte)) (σ3 := ty.bvec (1 * byte))
                     bv.app (NonSyncVal bl br) (SV bv.nil)).
      { cbn. rewrite !arrv_app_nil8. reflexivity. }
      rewrite EV ptstomem_bv_app. unfold interp_ptstomem. cbn.
      rewrite !arrv_app_nil8. iSplit; [iIntros "[$ _]"|iIntros "$"; auto].
    Qed.

    (* le_bytes' one step, by conversion (cbn/simpl will not stop there) *)
    Lemma arrv_le_bytes_app (k : nat) (b : bv byte) (bs : bv (k * byte)) :
      @bv.le_bytes (S k * byte) (bv.app b bs) = b :: bv.le_bytes bs.
    Proof.
      change (@bv.le_bytes (S k * byte) (bv.app b bs)) with
        (let (b0, r) := bv.appView 8 (k * byte) (bv.app b bs) in b0 :: bv.le_bytes r).
      rewrite bv.appView_app. reflexivity.
    Qed.

    (* a k-byte cell holding NonSyncVal l r IS the byte cells of le_bytes l / r *)
    Lemma arrv_cell_bytes `{sailGS2 Σ} (k : nat) (x : bv xlenbits) (l r : bv (k * byte)) :
      interp_ptstomem (width := k) (SV x) (NonSyncVal l r) ⊣⊢@{iPropI Σ}
      [∗ list] j ↦ lr ∈ zip (bv.le_bytes l) (bv.le_bytes r),
        interp_ptstomem (width := 1) (SV (bv.add x (bv.of_nat j))) (NonSyncVal lr.1 lr.2).
    Proof.
      revert x. induction k as [|k IH]; intros x.
      - unfold interp_ptstomem. cbn. iSplit; auto.
      - destruct (bv.appView byte (k * byte) l) as [bl ls].
        destruct (bv.appView byte (k * byte) r) as [br rs].
        change (NonSyncVal (bv.app bl ls) (bv.app br rs) : RelVal (ty.bvec (S k * byte))) with
          (ty.liftBinOp (σ1 := ty.bvec byte) (σ2 := ty.bvec (k * byte)) (σ3 := ty.bvec (S k * byte))
             bv.app (NonSyncVal bl br) (NonSyncVal ls rs)).
        rewrite ptstomem_bv_app !arrv_le_bytes_app. cbn [zip zip_with big_opL fst snd].
        rewrite rg_of_nat_0 arrv_byte_cell. f_equiv.
        cbn [ty.liftUnOp]. rewrite IH. apply big_sepL_proper. intros j lr _. cbv beta.
        rewrite rg_of_nat_S. done.
    Qed.
    Lemma arrv_unsigned_add_nat (x : bv xlenbits) (t : nat) :
      (bv.unsigned x + Z.of_nat t < 2 ^ Z.of_nat xlenbits)%Z ->
      bv.unsigned (bv.add x (bv.of_nat t)) = (bv.unsigned x + Z.of_nat t)%Z.
    Proof.
      intros Ht. pose proof (bv.unsigned_bounds x) as Bx.
      assert (Et : bv.unsigned (@bv.of_nat xlenbits t) = Z.of_nat t).
      { unfold bv.of_nat. rewrite <- bv.of_Z_N, bv.unsigned_of_Z. unfold bv.truncz.
        rewrite nat_N_Z. apply Z.mod_small. lia. }
      rewrite bv.unsigned_add Et. unfold bv.truncz. apply Z.mod_small. lia.
    Qed.

    (* a word's range fact is its four bytes' (literal constants: lia cannot see
       through `2 ^ xlenbits` / `maxAddr` atoms that differ in hidden indices) *)
    Lemma arrv_range4 (x : bv xlenbits) :
      (bv.unsigned x + Z.of_nat 4 <= Z.of_N maxAddr)%Z <->
      (forall t : nat, (t < 4)%nat -> bv.unsigned (bv.add x (bv.of_nat t)) + Z.of_nat 1 <= Z.of_N maxAddr)%Z.
    Proof.
      pose proof (bv.unsigned_bounds x) as Bx.
      change (2 ^ Z.of_nat xlenbits)%Z with 4294967296%Z in Bx.
      change (Z.of_N maxAddr) with 4096%Z.
      assert (U : forall t : nat, (t < 4)%nat -> (bv.unsigned x + 4 <= 4096)%Z ->
                  bv.unsigned (bv.add x (bv.of_nat t)) = (bv.unsigned x + Z.of_nat t)%Z).
      { intros t Ht Hx. apply arrv_unsigned_add_nat. change (2 ^ Z.of_nat xlenbits)%Z with 4294967296%Z. lia. }
      split.
      - intros Hx t Ht. rewrite U; [lia|lia|lia].
      - intros H. pose proof (H 0%nat ltac:(lia)) as H0. pose proof (H 3%nat ltac:(lia)) as H3.
        rewrite arrv_unsigned_add_nat in H0; [|change (2 ^ Z.of_nat xlenbits)%Z with 4294967296%Z; lia].
        rewrite arrv_unsigned_add_nat in H3; [lia|change (2 ^ Z.of_nat xlenbits)%Z with 4294967296%Z; lia].
    Qed.

    Lemma arrv_le_bytes_length (k : nat) (x : bv (k * byte)) : length (bv.le_bytes x) = k.
    Proof.
      induction k as [|k IH]; [reflexivity|].
      destruct (bv.appView byte (k * byte) x) as [b bs]. rewrite arrv_le_bytes_app. cbn. f_equal. apply IH.
    Qed.

    (* a word cell with its range IS its four byte cells with theirs *)
    Lemma arrv_word_cell `{sailGS2 Σ} (x : bv xlenbits) (l r : bv (4 * byte)) :
      ⌜(bv.unsigned x + Z.of_nat 4 <= Z.of_N maxAddr)%Z⌝ ∗ interp_ptstomem (width := 4) (SV x) (NonSyncVal l r)
      ⊣⊢@{iPropI Σ}
      [∗ list] t ↦ lr ∈ zip (bv.le_bytes l) (bv.le_bytes r),
        ⌜(bv.unsigned (bv.add x (bv.of_nat t)) + Z.of_nat 1 <= Z.of_N maxAddr)%Z⌝ ∗
        interp_ptstomem (width := 1) (SV (bv.add x (bv.of_nat t))) (NonSyncVal lr.1 lr.2).
    Proof.
      rewrite arrv_cell_bytes big_sepL_sep arrv_range4 big_sepL_pure.
      assert (HL : length (zip (bv.le_bytes l) (bv.le_bytes r)) = 4).
      { first [rewrite length_zip_with | rewrite zip_with_length]; rewrite !arrv_le_bytes_length; reflexivity. }
      f_equiv. f_equiv. split.
      - intros Hp k y Hk. apply lookup_lt_Some in Hk. apply Hp.
        exact (eq_ind _ (fun m => k < m) Hk 4 HL).
      - intros Hp t Ht. destruct (lookup_lt_is_Some_2 (zip (bv.le_bytes l) (bv.le_bytes r)) t) as [y Hy];
          [exact (eq_ind_r (fun m => t < m) Ht HL)|].
        exact (Hp t y Hy).
    Qed.


    (* the words of an arrv 4 4 ARE the bytes of an arrv 1 1, cells and ranges *)
    Lemma arrv_words_bytes `{sailGS2 Σ} (a : bv xlenbits) (L R : list (bv (4 * byte))) :
      length L = length R ->
      ([∗ list] i ↦ lr ∈ zip L R,
         ⌜(bv.unsigned (bv.add a (bv.mul (bv.of_Z 4) (bv.of_nat i))) + Z.of_nat 4 <= Z.of_N maxAddr)%Z⌝ ∗
         interp_ptstomem (width := 4) (SV (bv.add a (bv.mul (bv.of_Z 4) (bv.of_nat i)))) (NonSyncVal lr.1 lr.2))
      ⊣⊢@{iPropI Σ}
      [∗ list] j ↦ lr ∈ zip (flat_map bv.le_bytes L) (flat_map bv.le_bytes R),
         ⌜(bv.unsigned (bv.add a (bv.mul (bv.of_Z 1) (bv.of_nat j))) + Z.of_nat 1 <= Z.of_N maxAddr)%Z⌝ ∗
         interp_ptstomem (width := 1) (SV (bv.add a (bv.mul (bv.of_Z 1) (bv.of_nat j)))) (NonSyncVal lr.1 lr.2).
    Proof.
      revert a R. induction L as [|l L IH]; intros a [|r R] HLR; cbn in HLR; try discriminate; [done|].
      cbn [zip zip_with flat_map big_opL].
      rewrite zip_with_app; [|rewrite !arrv_le_bytes_length; reflexivity].
      rewrite big_sepL_app.
      assert (E0 : bv.add a (bv.mul (bv.of_Z 4) (bv.of_nat 0)) = a).
      { change (bv.of_nat (n := xlenbits) 0) with (@bv.zero xlenbits). ring. }
      rewrite E0 arrv_word_cell. f_equiv.
      - apply big_sepL_proper. intros t lr _. cbv beta. rewrite bv.of_Z_one.
        assert (E1 : forall X : bv xlenbits, bv.mul bv.one X = X) by (intros; ring). rewrite E1. done.
      - assert (HL : length (zip (bv.le_bytes l) (bv.le_bytes r)) = 4).
        { first [rewrite length_zip_with | rewrite zip_with_length]; rewrite !arrv_le_bytes_length; reflexivity. }
        assert (E4 : @bv.of_nat xlenbits 4 = bv.of_Z 4) by reflexivity.
        injection HLR as HLR.
        etransitivity; [|etransitivity; [apply (IH (bv.add a (bv.of_Z 4)) R); exact HLR|]].
        + apply big_sepL_proper. intros i lr _. cbv beta.
          assert (EA : bv.add a (bv.mul (bv.of_Z 4) (bv.of_nat (S i)))
                       = bv.add (bv.add a (bv.of_Z 4)) (bv.mul (bv.of_Z 4) (bv.of_nat i))).
          { rewrite bv.of_nat_S. ring. }
          rewrite EA. done.
        + apply big_sepL_proper. intros k y _. cbv beta.
          assert (EA : bv.add a (bv.mul (bv.of_Z 1) (bv.of_nat (length (zip (bv.le_bytes l) (bv.le_bytes r)) + k)))
                       = bv.add (bv.add a (bv.of_Z 4)) (bv.mul (bv.of_Z 1) (bv.of_nat k))).
          { rewrite (eq_ind_r (fun m => @bv.of_nat xlenbits (m + k) = bv.add (bv.of_Z 4) (bv.of_nat k))
                       (eq_trans (arr_of_nat_add 4 k) (f_equal (fun z => bv.add z _) E4)) HL).
            rewrite bv.of_Z_one. ring. }
          rewrite EA. done.
    Qed.

    Lemma arrv_proj_regroup (vs : RelVal (ty.list (ty.bvec (4 * byte)))) :
      ty.projLeft (uop.evalRel (uop.regroup (σ := ty.bvec (4 * byte)) (τ := ty.bvec (1 * byte))) vs)
        = flat_map bv.le_bytes (ty.projLeft vs) /\
      ty.projRight (uop.evalRel (uop.regroup (σ := ty.bvec (4 * byte)) (τ := ty.bvec (1 * byte))) vs)
        = flat_map bv.le_bytes (ty.projRight vs).
    Proof. destruct vs; split; reflexivity. Qed.
    Lemma arrv_flat_length (L : list (bv (4 * byte))) : length (flat_map bv.le_bytes L) = 4 * length L.
    Proof.
      induction L as [|l L IH]; [reflexivity|]. cbn [flat_map length].
      rewrite length_app arrv_le_bytes_length IH. lia.
    Qed.
    Lemma arrv_of_nat_x4 (m : nat) : @bv.of_nat xlenbits (4 * m) = bv.mul (bv.of_N 4) (bv.of_nat m).
    Proof. unfold bv.of_nat. rewrite Nat2N.inj_mul. rewrite -!bv.of_Z_N bv.of_Z_mul. f_equal. lia. Qed.

    Lemma interp_arrv_to_bytes `{sailGS2 Σ} (a n e : bv xlenbits) vs :
      interp_arrv 4 4 (SV a) (SV n) (SV e) vs ⊢@{iPropI Σ}
      interp_arrv 1 1 (SV a) (SV (bv.mul (bv.of_N 4) n)) (SV e) (uop.evalRel uop.regroup vs).
    Proof.
      rewrite !interp_arrv_SV; unfold interp_arrv_body. destruct (arrv_proj_regroup vs) as [-> ->].
      iIntros "(%He & %Hlen & %Hn & Hc)". subst e n.
      iSplit.
      { iPureIntro. change (@bv.of_N xlenbits 4) with (@bv.of_Z xlenbits 4). rewrite bv.of_Z_one.
        assert (Er : forall a0 X : bv xlenbits, bv.add a0 X = bv.add a0 (bv.mul bv.one X)) by (intros; ring).
        apply Er. }
      iSplit; [iPureIntro; rewrite !arrv_flat_length Hlen; reflexivity|].
      iSplit; [iPureIntro; rewrite arrv_flat_length arrv_of_nat_x4; reflexivity|].
      iApply (bi.equiv_entails_1_1 _ _ (arrv_words_bytes a _ _ Hlen) with "Hc").
    Qed.

    (* the bound is needed: ·4 is not injective mod 2^32 *)
    Lemma interp_arrv_of_bytes `{sailGS2 Σ} (a k e : bv xlenbits) v :
      (bv.bin k < 1073741824)%N ->
      interp_arrv 1 1 (SV a) (SV (bv.mul (bv.of_N 4) k)) (SV e) (uop.evalRel uop.regroup v) ⊢@{iPropI Σ}
      interp_arrv 4 4 (SV a) (SV k) (SV e) v.
    Proof.
      intros Hk. iIntros "H". iDestruct (interp_arrv_length with "H") as %Hb.
      rewrite !interp_arrv_SV; unfold interp_arrv_body. destruct (arrv_proj_regroup v) as [EL ER].
      rewrite EL ER in Hb |- *. iDestruct "H" as "(%He & %Hlen & %Hn & Hc)".
      rewrite !arrv_flat_length in Hb Hlen Hn.
      assert (HlT : length (ty.projLeft v) = length (ty.projRight v)).
      { apply Nat.mul_cancel_l in Hlen; [exact Hlen|lia]. }
      set (m := length (ty.projLeft v)) in *.
      change (N.to_nat maxAddr) with 4096 in Hb.
      (* the count: 4·m = 4·bin k below 2^32 on both sides (pigeonhole bound,
         and the premise) *)
      apply (f_equal (@bv.bin xlenbits)) in Hn.
      rewrite bv.bin_of_nat_small in Hn; [|change (bv.exp2 xlenbits) with 4294967296%N; lia].
      unfold bv.mul in Hn. change (bv.bin (@bv.of_N xlenbits 4)) with 4%N in Hn.
      rewrite bv.bin_of_N_small in Hn; [|change (bv.exp2 xlenbits) with 4294967296%N; lia].
      assert (Hm : m = N.to_nat (bv.bin k)) by lia.
      iSplit.
      { iPureIntro. subst e. change (@bv.of_N xlenbits 4) with (@bv.of_Z xlenbits 4). rewrite bv.of_Z_one.
        assert (Er : forall a0 X : bv xlenbits, bv.add a0 (bv.mul bv.one X) = bv.add a0 X) by (intros; ring).
        apply Er. }
      iSplit; [iPureIntro; exact HlT|].
      iSplit; [iPureIntro; rewrite Hm; unfold bv.of_nat; rewrite N2Nat.id; apply bv.of_N_bin|].
      iApply (bi.equiv_entails_1_2 _ _ (arrv_words_bytes a _ _ HlT) with "Hc").
    Qed.

    Lemma clem_arrv_to_bytes_sound `{sailGS2 Σ} (t : string) :
      ValidLemma (clem_lemma (clem_arrv_to_bytes t)).
    Proof.
      intros ι. cbv [clemv_ctx] in ι. destruct_syminstance ι.
      destruct a as [a a']; destruct n as [n n']; destruct e as [e e'];
        cbn -[interp_arrv].
      iIntros "Harr". arrv_sync "Harr". pdup. by iApply interp_arrv_to_bytes.
    Qed.

    (* the count is 4·k, not a variable, so publicness of the count gives
       4·k = 4·k' and the k <u 2^30 bound on both sides gives k = k' *)
    Lemma arrv_mul4_inj (k k' : bv xlenbits) :
      (bv.bin k < 1073741824)%N -> (bv.bin k' < 1073741824)%N ->
      bv.mul (bv.of_N 4) k = bv.mul (bv.of_N 4) k' -> k = k'.
    Proof.
      intros Hk Hk' E. apply bv.bin_inj. apply (f_equal (@bv.bin xlenbits)) in E.
      unfold bv.mul in E. change (bv.bin (@bv.of_N xlenbits 4)) with 4%N in E.
      rewrite !bv.bin_of_N_small in E; [lia | change (bv.exp2 xlenbits) with 4294967296%N; lia ..].
    Qed.

    Lemma clem_arrv_of_bytes_sound `{sailGS2 Σ} (t : string) :
      ValidLemma (clem_lemma (clem_arrv_of_bytes t)).
    Proof.
      intros ι. destruct_syminstance ι.
      destruct a as [a a']; destruct k as [k k']; destruct e as [e e'];
        cbn -[interp_arrv].
      iIntros "[Harr [%Hk _]]".
      iDestruct (interp_arrv_agree with "Harr") as "[%Hag Harr]".
      destruct Hag as (Ea & Ek & Ee). subst a' e'.
      unfold bv.ult in Hk. change (bv.bin (@bv.of_N xlenbits 1073741824)) with 1073741824%N in Hk.
      destruct Hk as [Hk Hk'].
      apply arrv_mul4_inj in Ek; [|exact Hk|exact Hk']. subst k'.
      iApply (interp_arrv_of_bytes with "Harr"). exact Hk.
    Qed.

    (* the array is handed back; an EMPTY one at its (public) start costs
       nothing -- interp_arrv is False at a NonSyncVal address *)
    Lemma clem_arrv_empty_at_sound `{sailGS2 Σ} (w : nat) (s : Z) (t t' : string) :
      ValidLemma (clem_lemma (clem_arrv_empty_at w s t t')).
    Proof.
      intros ι. cbv [clemv_ctx] in ι. destruct_syminstance ι.
      destruct a as [a a']; destruct n as [n n']; destruct e as [e e'];
        cbn -[interp_arrv].
      iIntros "Harr". arrv_sync "Harr". pdup. iFrame "Harr". iApply interp_arrv_empty.
    Qed.

    (* ---- PLAN-rsa GATE 2: a word's bytes in the open ---- *)
    (* the bytes of a word are its four take/drop slices (clem_word_bytes) *)
    Lemma le_bytes_32 (x : bv 32) :
      bv.le_bytes x = [bv.take 8 (n := 24) x; bv.take 8 (n := 16) (bv.drop 8 (n := 24) x);
                       bv.take 8 (n := 8) (bv.drop 8 (n := 16) (bv.drop 8 (n := 24) x));
                       bv.take 8 (n := 0) (bv.drop 8 (n := 8) (bv.drop 8 (n := 16) (bv.drop 8 (n := 24) x)))].
    Proof.
      destruct (bv.appView 8 24 x) as [b0 r0].
      destruct (bv.appView 8 16 r0) as [b1 r1].
      destruct (bv.appView 8 8 r1) as [b2 r2].
      destruct (bv.appView 8 0 r2) as [b3 r3].
      rewrite ?bv.drop_app ?bv.take_app.
      rewrite (arrv_le_bytes_app 3 b0) (arrv_le_bytes_app 2 b1) (arrv_le_bytes_app 1 b2) (arrv_le_bytes_app 0 b3).
      destruct (bv.view r3). reflexivity.
    Qed.

    Lemma clem_arrv_regroup_cons_sound `{sailGS2 Σ} (t : string) :
      ValidLemma (clem_lemma (clem_arrv_regroup_cons t)).
    Proof.
      intros ι. destruct_syminstance ι.
      cbn -[interp_arrv]. iIntros "Harr". iApply (interp_arrv_proj with "Harr").
      all: destruct x as [xl xr], r as [rl rr];
        cbn -[bv.le_bytes bv.take bv.drop]; rewrite ?le_bytes_32; reflexivity.
    Qed.

    Lemma clem_arrv_word_of_bytes1_sound `{sailGS2 Σ} (t : string) :
      ValidLemma (clem_lemma (clem_arrv_word_of_bytes1 t)).
    Proof.
      intros ι. destruct_syminstance ι.
      destruct a as [a a']; destruct e as [e e']; cbn -[interp_arrv].
      iIntros "Harr". arrv_sync "Harr". pdup.
      iApply (interp_arrv_of_bytes a (bv.of_N 1) e); [cbn; lia|].
      change (bv.mul (@bv.of_N xlenbits 4) (bv.of_N 1)) with (@bv.of_N xlenbits 4).
      iApply (interp_arrv_proj with "Harr").
      all: destruct x as [xl xr]; cbn -[bv.le_bytes bv.take bv.drop]; rewrite ?le_bytes_32; reflexivity.
    Qed.

    (* bytes back to words, four at a time *)
    Fixpoint arrv_bytes_to_words (l : list (bv byte)) : list (bv (4 * byte)) :=
      match l with
      | b0 :: b1 :: b2 :: b3 :: r =>
          (bv.app b0 (bv.app b1 (bv.app b2 (bv.app b3 bv.nil))) : bv (4 * byte))
            :: arrv_bytes_to_words r
      | _ => []
      end.

    Lemma arrv_flat_b2w (m : nat) : forall (l : list (bv byte)), length l = 4 * m ->
      flat_map (@bv.le_bytes (4 * byte)) (arrv_bytes_to_words l) = l.
    Proof.
      induction m as [|m IH]; intros l Hl.
      - destruct l; [reflexivity|cbn in Hl; lia].
      - destruct l as [|b0 [|b1 [|b2 [|b3 r]]]]; cbn in Hl; try lia.
        cbn [arrv_bytes_to_words flat_map].
        rewrite (arrv_le_bytes_app 3 b0) (arrv_le_bytes_app 2 b1) (arrv_le_bytes_app 1 b2) (arrv_le_bytes_app 0 b3).
        cbn [app]. rewrite IH; [reflexivity|lia].
    Qed.

    Lemma interp_arrv_facts `{sailGS2 Σ} (w : nat) (s : Z) (a n e : bv xlenbits) vs :
      interp_arrv w s (SV a) (SV n) (SV e) vs ⊢@{iPropI Σ}
      ⌜length (ty.projLeft vs) = length (ty.projRight vs) /\ bv.of_nat (length (ty.projLeft vs)) = n⌝.
    Proof. rewrite !interp_arrv_SV; unfold interp_arrv_body. iIntros "(_ & %Hlen & %Hn & _)". auto. Qed.

    Lemma clem_arrv_of_bytes_any_sound `{sailGS2 Σ} (t : string) :
      ValidLemma (clem_lemma (clem_arrv_of_bytes_any t)).
    Proof.
      intros ι. destruct_syminstance ι.
      destruct a as [a a']; destruct k as [k k']; destruct e as [e e'];
        cbn -[interp_arrv].
      iIntros "[Harr [%Hk _]]".
      iDestruct (interp_arrv_agree with "Harr") as "[%Hag Harr]".
      destruct Hag as (Ea & Ek & Ee). subst a' e'.
      (* by conversion: the literal's spelling defeats `change` *)
      destruct Hk as [HkL HkR].
      assert (Hk : (bv.bin k < 1073741824)%N) by exact HkL.
      assert (Hk' : (bv.bin k' < 1073741824)%N) by exact HkR. clear HkL HkR.
      apply arrv_mul4_inj in Ek; [|exact Hk|exact Hk']. subst k'. clear Hk'.
      iDestruct (interp_arrv_length with "Harr") as %Hb.
      iDestruct (interp_arrv_facts with "Harr") as %[HlT Hn].
      change (N.to_nat maxAddr) with 4096 in Hb.
      apply (f_equal (@bv.bin xlenbits)) in Hn.
      rewrite bv.bin_of_nat_small in Hn; [|change (bv.exp2 xlenbits) with 4294967296%N; lia].
      unfold bv.mul in Hn. change (bv.bin (@bv.of_N xlenbits 4)) with 4%N in Hn.
      rewrite bv.bin_of_N_small in Hn; [|change (bv.exp2 xlenbits) with 4294967296%N; lia].
      assert (E4 : bv.bin (@bv.of_N xlenbits (4 * bv.bin k)) = (4 * bv.bin k)%N).
      { apply bv.bin_of_N_small. change (bv.exp2 xlenbits) with 4294967296%N. lia. }
      rewrite E4 in Hn.
      set (m := N.to_nat (bv.bin k)).
      assert (HL : length (ty.projLeft vs) = 4 * m).
      { subst m. apply (f_equal N.to_nat) in Hn. rewrite Nat2N.id N2Nat.inj_mul in Hn. exact Hn. }
      (* not lia: the two lengths' type indices are spelled differently *)
      assert (HR : length (ty.projRight vs) = 4 * m) by exact (eq_trans (eq_sym HlT) HL).
      set (v := ty.NonSyncVal (arrv_bytes_to_words (ty.projLeft vs)) (arrv_bytes_to_words (ty.projRight vs))
                : RelVal (ty.list (ty.bvec (4 * byte)))).
      assert (Hv : vs = uop.evalRel (uop.regroup (σ := ty.bvec (4 * byte)) (τ := ty.bvec (1 * byte))) v).
      { subst v. destruct vs as [l r]; cbn in HL, HR |- *; f_equal; symmetry;
          [apply (arrv_flat_b2w m); exact HL | apply (arrv_flat_b2w m); exact HR]. }
      iExists v. iSplitL "Harr".
      - iRevert "Harr". rewrite {1}Hv. iIntros "Harr".
        iApply (interp_arrv_of_bytes with "Harr"). exact Hk.
      - auto.
    Qed.

    Lemma clemSem `{sailGS2 Σ} (k : CLem) :
      ValidLemma (clem_lemma k).
    Proof.
      destruct k; [apply clem_arrv_take_first_sound
                  |apply clem_arrv_add_first_sound|apply clem_arrv_add_last_sound
                  |apply clem_arrv_take_last_sound|apply clem_arrv_nonempty_sound
                  |apply clem_arrv_empty_sound|apply clem_arrv_empty_elim_sound
                  |apply clem_arrv_count0_sound
                  |apply clem_arrv_lockstep_sound|apply clem_arrv_drop_sound
                  |apply clem_arrv_flip_sound|apply clem_arrv_join_sound
                  |apply clem_arrv_split_sound
                  |apply clem_arrv_to_bytes_sound|apply clem_arrv_of_bytes_sound
                  |apply clem_arrv_empty_at_sound|apply clem_arrv_regroup_cons_sound
                  |apply clem_arrv_word_of_bytes1_sound|apply clem_arrv_of_bytes_any_sound].
    Qed.
  End CLemSound.

  Import RiscvPmpCFGVerifSpec.
  Import RiscvPmpCFGVerifExecutor.Symbolic.

  (* Lemma TcontractsSound `{sailGS Σ} : ⊢ TValidContractEnvSem RiscvPmpCFGVerifSpec.CEnv. *)
  (* Proof. *)
  (*   apply (tsound TforeignSemCFGVerif lemSemCFGVerif). *)
  (*   intros Γ τ f c Heq. *)
  (*   pose proof (RiscvPmpSpecVerif.ValidContracts f Heq) as [fuel Hvc]. *)
  (*   eapply shallow_vcgen_fuel_soundness, symbolic_vcgen_fuel_soundness. *)
  (*   eauto. *)
  (* Qed. *)

  (* TODO: prove this lemma as: apply (TValidContractEnvSem_ValidContractEnvSem TcontractsSound). *)
  Lemma contractsSound `{sailGS2 Σ} : ⊢ ValidContractEnvSem RiscvPmpCFGVerifSpec.CEnv.
  Proof.
    apply (sound foreignSemCFGVerif lemSemCFGVerif).
    intros Γ τ f c Heq.
    pose proof (RiscvPmpSpecVerif.ValidContracts f Heq) as [fuel Hvc].
    eapply shallow_vcgen_fuel_soundness, symbolic_vcgen_fuel_soundness.
    eauto.
  Qed.

End RiscvPmpIrisInstanceWithContracts.
