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
      destruct (pattern_match_relval pat_bool inv) as [[b δpc]|] eqn:Hpm; cbn.
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
        + iExists (SyncVal (fun_read_ram μ1 bytes (ty.projLeft paddr))). iSplitR; first by rewrite eq_fun_read_ramR.
          iFrame "H".
          iSplitR; try auto.
          iSplitR; first auto.
          by rewrite eq_fun_read_ramL.
          auto. (* TODO: How to dispatch emp goal, also several admits for this below *)
        + iExists (NonSyncVal (fun_read_ram μ1 bytes (ty.projLeft paddr)) (fun_read_ram μ2 bytes (ty.projRight paddr))). iSplitR; first by rewrite eq_fun_read_ramR.
          iFrame "H".
          iSplitR; try auto.
          iSplitR; first auto.
          by rewrite eq_fun_read_ramL eq_fun_read_ramR.
          auto.
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
        + iExists (SyncVal (fun_read_ram μ1 bytes (ty.projLeft paddr))).
          iSplitR; first by rewrite eq_fun_read_ramR.
          iSplitR; try auto.
          iSplitR; first by rewrite eq_fun_read_ramL.
          auto.
        + iExists (NonSyncVal (fun_read_ram μ1 bytes (ty.projLeft paddr)) (fun_read_ram μ2 bytes (ty.projRight paddr))). iSplitR; first by rewrite eq_fun_read_ramR.
          iSplitR; try auto.
          iSplitR; first auto.
          by rewrite eq_fun_read_ramL eq_fun_read_ramR.
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
    + rewrite semWP2_val.
      iExists δ. iSplitR; first auto. iExists (SyncVal v0). auto.
    + destruct (pure_decode); inversion Hdecode.
      rewrite semWP2_val.
      iExists δ. iSplitR; first auto. iExists (NonSyncVal v1 v2). auto.
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
  (*    big_sepL move on IrisInstanceBinary.interp_arr (the shape of         *)
  (*    GenCompose.loop_reservoir_peel / loop_completed_push);               *)
  (*  - ValidLemma, which unpacks the assertion interpretation to the step   *)
  (*    lemma (a NonSyncVal start/count/end makes interp_arr False).         *)
  (* The pointer/count multiplication e = a + s·n lives only here, as ring   *)
  (* identities -- never in a VC.                                            *)
  (* ======================================================================= *)
  Section CLemSound.
    Add Ring bvring_xlen : (bv.ring_theory xlenbits).
    Local Notation SV := TypeDecl.ty.SyncVal.

    Lemma arr_pred_bin (n : bv xlenbits) : n <> bv.zero ->
      bv.bin (bv.add n (bv.of_Z (-1))) = (bv.bin n - 1)%N.
    Proof.
      intros Hn.
      replace (bv.of_Z (n := xlenbits) (-1)) with (bv.negate (bv.of_Z (n := xlenbits) 1))
        by (rewrite bv.of_Z_negate; reflexivity).
      rewrite bv.of_Z_one. fold (bv.sub n bv.one).
      rewrite bv.bin_sub_small.
      - rewrite bv.bin_one; [reflexivity|cbv; lia].
      - unfold bv.ule. rewrite bv.bin_one; [|cbv; lia].
        destruct (bv.bin n) eqn:E; [|lia].
        exfalso. apply Hn. apply bv.bin_inj. now rewrite E.
    Qed.

    (* bin (n+1) = bin n + 1, or the count wrapped to 0 *)
    Lemma arr_succ_bin (n : bv xlenbits) :
      (bv.bin (bv.add n (bv.of_Z 1)) = bv.bin n + 1)%N \/ bv.bin (bv.add n (bv.of_Z 1)) = 0%N.
    Proof.
      rewrite bv.of_Z_one bv.bin_add bv.bin_one; [|cbv; lia].
      pose proof (bv.bv_is_wf n) as Hw.
      set (E := bv.exp2 xlenbits) in *. clearbody E.
      destruct (N.lt_ge_cases (bv.bin n + 1) E) as [Hl|Hg].
      - left. now apply N.mod_small.
      - right. replace (bv.bin n + 1)%N with E by lia. apply N.mod_same. lia.
    Qed.

    Lemma arr_neg1 : bv.of_Z (n := xlenbits) (-1) = bv.negate bv.one.
    Proof. rewrite <- bv.of_Z_one, bv.of_Z_negate. reflexivity. Qed.
    Lemma arr_neg_s (s : Z) : bv.of_Z (n := xlenbits) (- s) = bv.negate (bv.of_Z s).
    Proof. now rewrite bv.of_Z_negate. Qed.
    Lemma arr_of_nat0 : bv.of_nat (n := xlenbits) 0 = bv.zero.
    Proof. reflexivity. Qed.

    (* Stated separately and APPLIED: `ring` refuses a goal whose carrier
       spells the width index unfolded, while `apply` works up to conversion
       (bv-pitfalls, "Blanket cbn unfolds the width index"). *)
    Lemma arr_ring_zero (a s : bv xlenbits) : a = bv.add a (bv.mul s bv.zero).
    Proof. ring. Qed.
    Lemma arr_ring_end_take (a s n : bv xlenbits) :
      bv.add a (bv.mul s n) = bv.add (bv.add a s) (bv.mul s (bv.add n (bv.negate bv.one))).
    Proof. ring. Qed.
    Lemma arr_ring_idx_take (a s x : bv xlenbits) :
      bv.add a (bv.mul s (bv.add bv.one x)) = bv.add (bv.add a s) (bv.mul s x).
    Proof. ring. Qed.
    Lemma arr_ring_end_add (a s n : bv xlenbits) :
      bv.add a (bv.mul s n) = bv.add (bv.add a (bv.negate s)) (bv.mul s (bv.add n bv.one)).
    Proof. ring. Qed.
    Lemma arr_ring_idx_add (a s x : bv xlenbits) :
      bv.add (bv.add a (bv.negate s)) (bv.mul s (bv.add bv.one x)) = bv.add a (bv.mul s x).
    Proof. ring. Qed.

    Lemma interp_arr_take_first `{sailGS2 Σ} (pub : bool) (w : nat) (s : Z) (a n e : bv xlenbits) :
      n <> bv.zero ->
      interp_arr pub w s (SV a) (SV n) (SV e) ⊢@{iPropI Σ}
      interp_arr_cell pub w a ∗
      interp_arr pub w s (SV (bv.add a (bv.of_Z s))) (SV (bv.add n (bv.of_Z (-1)))) (SV e).
    Proof.
      intros Hn. cbn [interp_arr]. iIntros "[%He Hcells]".
      rewrite arr_pred_bin; [|exact Hn].
      destruct (N.to_nat (bv.bin n)) as [|k] eqn:Ek.
      { exfalso. apply Hn. apply bv.bin_inj.
        pose proof (f_equal N.of_nat Ek) as E0. rewrite N2Nat.id in E0. exact E0. }
      cbn [seq]. iDestruct "Hcells" as "[Hc0 Hrest]".
      rewrite arr_of_nat0 -arr_ring_zero.
      iFrame "Hc0". iSplit.
      { iPureIntro. subst e. rewrite arr_neg1. apply arr_ring_end_take. }
      replace (N.to_nat (bv.bin n - 1)) with k by lia.
      iRevert "Hrest". rewrite -fmap_S_seq big_sepL_fmap. iIntros "Hrest".
      iApply (big_sepL_mono with "Hrest"). intros i x _. cbn.
      rewrite bv.of_nat_S arr_ring_idx_take. auto.
    Qed.

    (* A count that wraps to 0 leaves an empty right-hand side: the cells are
       dropped (affine) and the end fact still holds, since then n = -1. *)
    Lemma interp_arr_add_first `{sailGS2 Σ} (pub : bool) (w : nat) (s : Z) (a n e : bv xlenbits) :
      interp_arr pub w s (SV a) (SV n) (SV e) ∗ interp_arr_cell pub w (bv.add a (bv.of_Z (- s)))
      ⊢@{iPropI Σ}
      interp_arr pub w s (SV (bv.add a (bv.of_Z (- s)))) (SV (bv.add n (bv.of_Z 1))) (SV e).
    Proof.
      cbn [interp_arr]. iIntros "[[%He Hcells] Hc]".
      iSplit.
      { iPureIntro. subst e. rewrite arr_neg_s bv.of_Z_one. apply arr_ring_end_add. }
      destruct (arr_succ_bin n) as [Hs|Hz].
      - rewrite Hs. replace (N.to_nat (bv.bin n + 1)) with (S (N.to_nat (bv.bin n))) by lia.
        cbn [seq]. rewrite big_sepL_cons arr_of_nat0 -arr_ring_zero. iFrame "Hc".
        rewrite -fmap_S_seq big_sepL_fmap.
        iApply (big_sepL_mono with "Hcells"). intros i x _. cbn.
        rewrite bv.of_nat_S arr_neg_s arr_ring_idx_add. auto.
      - rewrite Hz. cbn. done.
    Qed.

    Lemma clem_take_first_sound `{sailGS2 Σ} (pub : bool) (w : nat) (s : Z) :
      ValidLemma (clem_lemma
                    (clem_arr_take_first pub w s)).
    Proof.
      intros ι. cbv [clem_ctx] in ι. destruct_syminstance ι.
      destruct a as [a|]; destruct n as [n|]; destruct e as [e|];
        cbn -[interp_arr]; try (iIntros "[[] _]").
      iIntros "[Harr [%Hne _]]".
      iDestruct (interp_arr_take_first with "Harr") as "[Hc $]"; [exact Hne|].
      iDestruct "Hc" as "[%Hr [%v [Hw %Hs]]]".
      iSplitL "Hw".
      { iExists v. iFrame "Hw". destruct pub; cbn.
        - iSplit; [iPureIntro; now apply Hs|done].
        - iSplit; done. }
      iSplit; [iPureIntro; exact Hr|done].
    Qed.

    Lemma clem_add_first_sound `{sailGS2 Σ} (pub : bool) (w : nat) (s : Z) :
      ValidLemma (clem_lemma
                    (clem_arr_add_first pub w s)).
    Proof.
      intros ι. cbv [clem_ctx] in ι. destruct_syminstance ι.
      destruct a as [a|]; destruct n as [n|]; destruct e as [e|];
        cbn -[interp_arr]; try (iIntros "[[] _]").
      iIntros "[Harr [[%v [Hw Hs]] [%Hr _]]]".
      iApply interp_arr_add_first. iFrame "Harr".
      unfold interp_arr_cell. iSplit; [iPureIntro; exact Hr|].
      iExists v. iFrame "Hw". destruct pub; cbn.
      - iDestruct "Hs" as "[%Hs _]". iPureIntro. intros _. exact Hs.
      - iPureIntro. discriminate.
    Qed.

    (* ENTRY CHECK (PLAN-array-invariants Phase 1): an arr chunk is
       SATISFIABLE -- k concrete in-range cells at a, a+s, … ARE an array of
       count k ending at a + s·k, as long as k fits the count's width.  So an
       invariant stated over arr is not vacuous for want of a model (§R11's
       lesson for loop_reservoir), and this is the Iris half of the
       caller-side conversion Phase 3 needs. *)
    Lemma interp_arr_intro `{sailGS2 Σ} (pub : bool) (w : nat) (s : Z) (a : bv xlenbits) (k : nat) :
      (N.of_nat k < bv.exp2 xlenbits)%N ->
      ([∗ list] i ∈ seq 0 k, interp_arr_cell pub w (bv.add a (bv.mul (bv.of_Z s) (bv.of_nat i))))
      ⊢@{iPropI Σ}
      interp_arr pub w s (SV a) (SV (bv.of_nat k)) (SV (bv.add a (bv.mul (bv.of_Z s) (bv.of_nat k)))).
    Proof.
      intros Hk. cbn [interp_arr]. iIntros "H". iSplit; [done|].
      rewrite bv.bin_of_nat_small; [|exact Hk]. rewrite Nat2N.id. iExact "H".
    Qed.

    (* An array whose start is not its end is non-empty: with n = 0 the end
       fact gives e = a. *)
    Lemma clem_nonempty_sound `{sailGS2 Σ} (pub : bool) (w : nat) (s : Z) :
      ValidLemma (clem_lemma
                    (clem_arr_nonempty pub w s)).
    Proof.
      intros ι. cbv [clem_ctx] in ι. destruct_syminstance ι.
      destruct a as [a|]; destruct n as [n|]; destruct e as [e|];
        cbn -[interp_arr]; try (iIntros "[[] _]").
      iIntros "[Harr [%Hne _]]".
      iAssert (⌜e = bv.add a (bv.mul (bv.of_Z s) n)⌝ ∗
               interp_arr pub w s (SV a) (SV n) (SV e))%I with "[Harr]" as "[%He Harr]".
      { cbn [interp_arr]. iDestruct "Harr" as "[%He Hc]". iFrame "Hc". done. }
      iFrame "Harr". iSplit; [|done]. iPureIntro. intros ->.
      apply Hne. rewrite He. apply arr_ring_zero.
    Qed.

    Lemma arr_of_nat_bin (n : bv xlenbits) : bv.of_nat (N.to_nat (bv.bin n)) = n.
    Proof. unfold bv.of_nat. rewrite N2Nat.id. apply bv.of_N_bin. Qed.
    Lemma arr_ring_end_last (a s n : bv xlenbits) :
      bv.add (bv.add a (bv.mul s n)) s = bv.add a (bv.mul s (bv.add n bv.one)).
    Proof. ring. Qed.

    (* The mirror of interp_arr_add_first at the OTHER end: the new cell is
       the one AT the end e = a + s·n.  A wrapping count drops the cells. *)
    Lemma interp_arr_add_last `{sailGS2 Σ} (pub : bool) (w : nat) (s : Z) (a n e : bv xlenbits) :
      interp_arr pub w s (SV a) (SV n) (SV e) ∗ interp_arr_cell pub w e
      ⊢@{iPropI Σ}
      interp_arr pub w s (SV a) (SV (bv.add n (bv.of_Z 1))) (SV (bv.add e (bv.of_Z s))).
    Proof.
      cbn [interp_arr]. iIntros "[[%He Hcells] Hc]".
      iSplit.
      { iPureIntro. subst e. rewrite bv.of_Z_one. apply arr_ring_end_last. }
      destruct (arr_succ_bin n) as [Hs|Hz].
      - rewrite Hs. replace (N.to_nat (bv.bin n + 1)) with (S (N.to_nat (bv.bin n))) by lia.
        rewrite seq_S big_sepL_app. iFrame "Hcells". cbn [big_opL].
        rewrite arr_of_nat_bin -He. iFrame "Hc".
      - rewrite Hz. cbn. done.
    Qed.

    Lemma clem_empty_sound `{sailGS2 Σ} (pub : bool) (w : nat) (s : Z) :
      ValidLemma (clem_lemma
                    (clem_arr_empty pub w s)).
    Proof.
      intros ι. destruct_syminstance ι.
      (* a NonSyncVal address is ruled out by the secLeak precondition *)
      destruct a as [a|]; cbn -[interp_arr]; [|iIntros "[[] _]"].
      iIntros "_". cbn [interp_arr]. iSplit; [|done].
      iPureIntro. apply arr_ring_zero.
    Qed.

    Lemma clem_add_last_sound `{sailGS2 Σ} (pub : bool) (w : nat) (s : Z) :
      ValidLemma (clem_lemma
                    (clem_arr_add_last pub w s)).
    Proof.
      intros ι. cbv [clem_ctx] in ι. destruct_syminstance ι.
      destruct a as [a|]; destruct n as [n|]; destruct e as [e|];
        cbn -[interp_arr]; try (iIntros "[[] _]").
      iIntros "[Harr [[%v [Hw Hs]] [%Hr _]]]".
      iApply interp_arr_add_last. iFrame "Harr".
      unfold interp_arr_cell. iSplit; [iPureIntro; exact Hr|].
      iExists v. iFrame "Hw". destruct pub; cbn.
      - iDestruct "Hs" as "[%Hs _]". iPureIntro. intros _. exact Hs.
      - iPureIntro. discriminate.
    Qed.

    (* An EMPTY array's start is its end: the end fact at n = 0. *)
    Lemma clem_empty_elim_sound `{sailGS2 Σ} (pub : bool) (w : nat) (s : Z) :
      ValidLemma (clem_lemma
                    (clem_arr_empty_elim pub w s)).
    Proof.
      intros ι. destruct_syminstance ι.
      destruct a as [a|]; destruct e as [e|];
        cbn -[interp_arr]; try (iIntros "[]").
      iIntros "Harr". cbn [interp_arr]. iDestruct "Harr" as "[%He _]".
      iSplit; [|done]. iPureIntro. subst e. apply arr_ring_zero.
    Qed.

    Lemma arr_lockstep_eq (a1 a2 s n : bv xlenbits) :
      a1 = bv.add a1 (bv.mul s n) -> a2 = bv.add a2 (bv.mul s n).
    Proof.
      intros H. rewrite <- (bv.add_zero_r (x := a1)) in H at 1.
      apply bv.add_cancel_l in H. rewrite <- H. symmetry. apply bv.add_zero_r.
    Qed.

    (* Same stride, same count: if one array's start is its end, s·n = 0,
       so the other's is too. *)
    Lemma clem_lockstep_sound `{sailGS2 Σ} (pub1 pub2 : bool) (w : nat) (s : Z) :
      ValidLemma (clem_lemma
                    (clem_arr_lockstep pub1 pub2 w s)).
    Proof.
      intros ι. destruct_syminstance ι.
      destruct a1 as [a1|]; destruct n as [n|]; destruct e1 as [e1|];
        destruct a2 as [a2|]; destruct e2 as [e2|];
        cbn -[interp_arr]; try (iIntros "[[] _]"); try (iIntros "[_ [[] _]]").
      iIntros "[H1 [H2 [%Heq _]]]".
      iAssert (⌜e2 = bv.add a2 (bv.mul (bv.of_Z s) n)⌝ ∗
               interp_arr pub2 w s (SV a2) (SV n) (SV e2))%I with "[H2]" as "[%He2 H2]".
      { cbn [interp_arr]. iDestruct "H2" as "[%He Hc]". iFrame "Hc". done. }
      iAssert (⌜e1 = bv.add a1 (bv.mul (bv.of_Z s) n)⌝ ∗
               interp_arr pub1 w s (SV a1) (SV n) (SV e1))%I with "[H1]" as "[%He1 H1]".
      { cbn [interp_arr]. iDestruct "H1" as "[%He Hc]". iFrame "Hc". done. }
      iFrame "H1 H2". iSplit; [|done]. iPureIntro.
      subst e1 e2. eapply arr_lockstep_eq; eassumption.
    Qed.

    (* Dropping resources is sound in an affine logic. *)
    Lemma clem_drop_sound `{sailGS2 Σ} (pub : bool) (w : nat) (s : Z) :
      ValidLemma (clem_lemma
                    (clem_arr_drop pub w s)).
    Proof. intros ι. cbn -[interp_arr]. iIntros "_". iSplit; done. Qed.

    Lemma arr_ring_end_take_last (a s n : bv xlenbits) :
      bv.add (bv.add a (bv.mul s n)) (bv.negate s)
      = bv.add a (bv.mul s (bv.add n (bv.negate bv.one))).
    Proof. ring. Qed.

    (* The mirror of interp_arr_take_first at the OTHER end: the last cell
       sits at e - s, i.e. at index n - 1. *)
    Lemma interp_arr_take_last `{sailGS2 Σ} (pub : bool) (w : nat) (s : Z) (a n e : bv xlenbits) :
      n <> bv.zero ->
      interp_arr pub w s (SV a) (SV n) (SV e) ⊢@{iPropI Σ}
      interp_arr_cell pub w (bv.add e (bv.of_Z (- s))) ∗
      interp_arr pub w s (SV a) (SV (bv.add n (bv.of_Z (-1)))) (SV (bv.add e (bv.of_Z (- s)))).
    Proof.
      intros Hn. cbn [interp_arr]. iIntros "[%He Hcells]".
      assert (Hk : bv.of_nat (N.to_nat (bv.bin n - 1)) = bv.add n (bv.of_Z (-1))).
      { rewrite <- (arr_pred_bin Hn). apply arr_of_nat_bin. }
      rewrite (arr_pred_bin Hn).
      destruct (N.to_nat (bv.bin n)) as [|k] eqn:Ek.
      { exfalso. apply Hn. apply bv.bin_inj.
        pose proof (f_equal N.of_nat Ek) as E0. rewrite N2Nat.id in E0. exact E0. }
      replace (N.to_nat (bv.bin n - 1)) with k in * by lia.
      rewrite seq_S big_sepL_app. cbn [big_opL].
      iDestruct "Hcells" as "[Hrest [Hc _]]". iFrame "Hrest".
      rewrite ?Nat.add_0_l Hk.
      assert (Hend : bv.add e (bv.of_Z (- s))
                     = bv.add a (bv.mul (bv.of_Z s) (bv.add n (bv.of_Z (-1))))).
      { subst e. rewrite arr_neg_s arr_neg1. apply arr_ring_end_take_last. }
      rewrite Hend. by iFrame "Hc".
    Qed.

    Lemma clem_take_last_sound `{sailGS2 Σ} (pub : bool) (w : nat) (s : Z) :
      ValidLemma (clem_lemma
                    (clem_arr_take_last pub w s)).
    Proof.
      intros ι. cbv [clem_ctx] in ι. destruct_syminstance ι.
      destruct a as [a|]; destruct n as [n|]; destruct e as [e|];
        cbn -[interp_arr]; try (iIntros "[[] _]").
      iIntros "[Harr [%Hne _]]".
      iDestruct (interp_arr_take_last with "Harr") as "[Hc $]"; [exact Hne|].
      iDestruct "Hc" as "[%Hr [%v [Hw %Hs]]]".
      iSplitL "Hw".
      { iExists v. iFrame "Hw". destruct pub; cbn.
        - iSplit; [iPureIntro; now apply Hs|done].
        - iSplit; done. }
      iSplit; [iPureIntro; exact Hr|done].
    Qed.

    (* The cells a + s·i (i < N), walked from the other end: start at the
       last cell a + s·N - s, stride -s.  By induction on N, peeling the
       FIRST cell on the left and the LAST on the right. *)
    Lemma big_sepL_flip {PROP : bi} (Φ : bv xlenbits -> PROP) (N : nat) (S a : bv xlenbits) :
      ([∗ list] i ∈ seq 0 N, Φ (bv.add a (bv.mul S (bv.of_nat i)))) ⊢
      [∗ list] i ∈ seq 0 N,
        Φ (bv.add (bv.add (bv.add a (bv.mul S (bv.of_nat N))) (bv.negate S))
                  (bv.mul (bv.negate S) (bv.of_nat i))).
    Proof.
      revert a. induction N as [|N IH]; intros a; [done|].
      rewrite {1}/seq -/seq big_sepL_cons -fmap_S_seq big_sepL_fmap.
      rewrite seq_S big_sepL_app big_sepL_singleton.
      iIntros "[H0 Hr]". iSplitL "Hr".
      - iPoseProof (IH (bv.add a S) with "[Hr]") as "Hr".
        { iApply (big_sepL_mono with "Hr"). intros k x _. cbv beta.
          rewrite bv.of_nat_S.
          match goal with |- Φ ?x ⊢ Φ ?y => replace x with y by ring; done end. }
        iApply (big_sepL_mono with "Hr"). intros k x _. cbv beta.
        rewrite bv.of_nat_S.
        match goal with |- Φ ?x ⊢ Φ ?y => replace x with y by ring; done end.
      - cbn [Nat.add]. rewrite bv.of_nat_S.
        iStopProof. match goal with |- Φ ?x ⊢ Φ ?y => replace x with y; [done|] end.
        change (bv.of_nat 0) with (bv.zero (n := xlenbits)). ring.
    Qed.

    Lemma arr_ring_flip_end (a S n : bv xlenbits) :
      bv.add a (bv.negate S)
      = bv.add (bv.add (bv.add a (bv.mul S n)) (bv.negate S)) (bv.mul (bv.negate S) n).
    Proof. ring. Qed.

    Lemma interp_arr_flip `{sailGS2 Σ} (pub : bool) (w : nat) (s : Z) (a n e : bv xlenbits) :
      interp_arr pub w s (SV a) (SV n) (SV e) ⊢@{iPropI Σ}
      interp_arr pub w (- s) (SV (bv.add e (bv.of_Z (- s)))) (SV n) (SV (bv.add a (bv.of_Z (- s)))).
    Proof.
      cbn [interp_arr]. iIntros "[%He Hcells]". subst e. rewrite !arr_neg_s.
      iSplit; [iPureIntro; apply arr_ring_flip_end|].
      iPoseProof (big_sepL_flip (interp_arr_cell pub w) with "Hcells") as "H".
      rewrite arr_of_nat_bin. iExact "H".
    Qed.

    Lemma clem_flip_sound `{sailGS2 Σ} (pub : bool) (w : nat) (s : Z) :
      ValidLemma (clem_lemma
                    (clem_arr_flip pub w s)).
    Proof.
      intros ι. cbv [clem_ctx] in ι. destruct_syminstance ι.
      destruct a as [a|]; destruct n as [n|]; destruct e as [e|];
        cbn -[interp_arr]; try (iIntros "[]").
      iIntros "Harr". by iApply interp_arr_flip.
    Qed.

    Lemma arr_add_nowrap (n n2 : bv xlenbits) : (bv.bin n <= bv.bin (bv.add n n2))%N ->
      bv.bin (bv.add n n2) = (bv.bin n + bv.bin n2)%N.
    Proof.
      intros H. rewrite bv.bin_add in H |- *. pose proof (bv.bv_is_wf n). pose proof (bv.bv_is_wf n2).
      set (E := bv.exp2 xlenbits) in *. clearbody E.
      destruct (N.lt_ge_cases (bv.bin n + bv.bin n2) E) as [Hl|Hg].
      - now apply N.mod_small.
      - exfalso.
        replace (bv.bin n + bv.bin n2)%N with ((bv.bin n + bv.bin n2 - E) + 1 * E)%N in H by lia.
        rewrite N.Div0.mod_add N.mod_small in H; lia.
    Qed.

    Lemma arr_of_nat_add (p q : nat) : @bv.of_nat xlenbits (p + q) = bv.add (bv.of_nat p) (bv.of_nat q).
    Proof. unfold bv.of_nat. rewrite Nat2N.inj_add. now rewrite bv.of_N_add. Qed.

    Lemma arr_ring_join_idx (a0 S n0 X : bv xlenbits) :
      bv.add (bv.add a0 (bv.mul S n0)) (bv.mul S X) = bv.add a0 (bv.mul S (bv.add n0 X)).
    Proof. ring. Qed.
    Lemma arr_ring_split_end (a0 S n0 K0 : bv xlenbits) :
      bv.add a0 (bv.mul S n0) = bv.add (bv.add a0 (bv.mul S K0)) (bv.mul S (bv.add n0 (bv.negate K0))).
    Proof. ring. Qed.
    Lemma arr_ring_split_idx (a0 S K0 X : bv xlenbits) :
      bv.add a0 (bv.mul S (bv.add K0 X)) = bv.add (bv.add a0 (bv.mul S K0)) (bv.mul S X).
    Proof. ring. Qed.

    (* two adjacent arrays (the second starts at the first's end) are one *)
    Lemma interp_arr_join `{sailGS2 Σ} (pub : bool) (w : nat) (s : Z) (a n e n2 e2 : bv xlenbits) :
      (bv.bin n <= bv.bin (bv.add n n2))%N ->
      interp_arr pub w s (SV a) (SV n) (SV e) ∗ interp_arr pub w s (SV e) (SV n2) (SV e2)
      ⊢@{iPropI Σ} interp_arr pub w s (SV a) (SV (bv.add n n2)) (SV e2).
    Proof.
      intros Hnw. cbn [interp_arr]. iIntros "[[%He H1] [%He2 H2]]".
      iSplit.
      { iPureIntro. subst e2 e. match goal with |- ?x = ?y => change (@eq (bv xlenbits) x y) end. ring. }
      rewrite (arr_add_nowrap n n2 Hnw) N2Nat.inj_add seq_app big_sepL_app. iFrame "H1".
      rewrite -fmap_add_seq big_sepL_fmap.
      rewrite -{1}(Nat.add_0_r (N.to_nat (bv.bin n))).
      rewrite <- (fmap_add_seq (N.to_nat (bv.bin n)) 0 (N.to_nat (bv.bin n2))). rewrite big_sepL_fmap.
      iApply (big_sepL_mono with "H2"). intros i x _. cbv beta.
      rewrite Nat.add_0_l arr_of_nat_add arr_of_nat_bin. subst e.
      rewrite arr_ring_join_idx. done.
    Qed.

    (* split at a constant index k ≤ n *)
    Lemma interp_arr_split `{sailGS2 Σ} (pub : bool) (w : nat) (s : Z) (k : N) (a n e : bv xlenbits) :
      (bv.bin (@bv.of_N xlenbits k) <= bv.bin n)%N ->
      interp_arr pub w s (SV a) (SV n) (SV e) ⊢@{iPropI Σ}
      interp_arr pub w s (SV a) (SV (bv.of_N k)) (SV (bv.add a (bv.of_Z (s * Z.of_N k))))
      ∗ interp_arr pub w s (SV (bv.add a (bv.of_Z (s * Z.of_N k)))) (SV (bv.add n (bv.of_Z (- Z.of_N k)))) (SV e).
    Proof.
      intros Hk. set (K := @bv.of_N xlenbits k) in *.
      assert (EsK : @bv.of_Z xlenbits (s * Z.of_N k) = bv.mul (bv.of_Z s) K).
      { unfold K. rewrite -bv.of_Z_N bv.of_Z_mul. reflexivity. }
      assert (EnK : bv.add n (@bv.of_Z xlenbits (- Z.of_N k)) = bv.sub n K).
      { unfold K. rewrite -bv.of_Z_negate bv.of_Z_N. reflexivity. }
      assert (Hb : bv.bin (bv.sub n K) = (bv.bin n - bv.bin K)%N).
      { apply bv.bin_sub_small. unfold bv.ule. exact Hk. }
      rewrite EsK EnK. cbn [interp_arr]. iIntros "[%He Hc]".
      replace (N.to_nat (bv.bin n)) with (N.to_nat (bv.bin K) + N.to_nat (bv.bin (bv.sub n K)))%nat
        by (rewrite Hb; lia).
      rewrite seq_app big_sepL_app. iDestruct "Hc" as "[H1 H2]".
      iSplitL "H1".
      { iSplit; [done|]. iExact "H1". }
      iSplit.
      { iPureIntro. subst e. unfold bv.sub. apply arr_ring_split_end. }
      rewrite -{1}(Nat.add_0_r (N.to_nat (bv.bin K))).
      rewrite <- (fmap_add_seq (N.to_nat (bv.bin K)) 0). rewrite big_sepL_fmap.
      iApply (big_sepL_mono with "H2"). intros i x _. cbv beta.
      rewrite arr_of_nat_add arr_of_nat_bin arr_ring_split_idx. done.
    Qed.

    Lemma clem_split_sound `{sailGS2 Σ} (pub : bool) (w : nat) (s : Z) (k : N) :
      ValidLemma (clem_lemma
                    (clem_arr_split pub w s k)).
    Proof.
      intros ι. cbv [clem_ctx] in ι. destruct_syminstance ι.
      destruct a as [a|]; destruct n as [n|]; destruct e as [e|];
        cbn -[interp_arr]; try (iIntros "[[] _]").
      iIntros "[Harr [%Hle _]]".
      iDestruct (interp_arr_split pub w s k with "Harr") as "[H1 H2]"; [exact Hle|].
      iFrame "H1 H2".
    Qed.

    Lemma clem_join_sound `{sailGS2 Σ} (pub : bool) (w : nat) (s : Z) :
      ValidLemma (clem_lemma
                    (clem_arr_join pub w s)).
    Proof.
      intros ι. destruct_syminstance ι.
      destruct a as [a|]; destruct n as [n|]; destruct e as [e|];
        destruct n2 as [n2|]; destruct e2 as [e2|];
        cbn -[interp_arr]; try (iIntros "[[] _]"); try (iIntros "[_ [[] _]]").
      iIntros "[H1 [H2 [%Hle _]]]".
      iApply (interp_arr_join with "[$H1 $H2]"). exact Hle.
    Qed.

    (* ---- a word array read byte by byte (clem_arr_bytes_of_words) ------- *)
    Lemma arr_word_decomp (w : RelVal (ty.bvec (4 * byte))) :
      exists (b0 b1 b2 b3 : RelVal (ty.bvec byte)) (r : RelVal (ty.bvec (0 * byte))),
        w = ty.liftBinOp (σ1 := ty.bvec byte) (σ2 := ty.bvec (3*byte)) (σ3 := ty.bvec (4*byte)) bv.app b0
              (ty.liftBinOp (σ1 := ty.bvec byte) (σ2 := ty.bvec (2*byte)) (σ3 := ty.bvec (3*byte)) bv.app b1
                (ty.liftBinOp (σ1 := ty.bvec byte) (σ2 := ty.bvec (1*byte)) (σ3 := ty.bvec (2*byte)) bv.app b2
                  (ty.liftBinOp (σ1 := ty.bvec byte) (σ2 := ty.bvec (0*byte)) (σ3 := ty.bvec (1*byte)) bv.app b3 r)))
        /\ (RiscvPmpSignature.secLeak w -> RiscvPmpSignature.secLeak b0 /\ RiscvPmpSignature.secLeak b1
              /\ RiscvPmpSignature.secLeak b2 /\ RiscvPmpSignature.secLeak b3).
    Proof.
      destruct w as [v|v1 v2].
      - destruct (bv.appView byte (3*byte) v) as [b0 r0].
        destruct (bv.appView byte (2*byte) r0) as [b1 r1].
        destruct (bv.appView byte (1*byte) r1) as [b2 r2].
        destruct (bv.appView byte (0*byte) r2) as [b3 r3].
        exists (SyncVal b0), (SyncVal b1), (SyncVal b2), (SyncVal b3), (SyncVal r3).
        split; [reflexivity|]. intros _. cbn. tauto.
      - destruct (bv.appView byte (3*byte) v1) as [b0 r0].
        destruct (bv.appView byte (2*byte) r0) as [b1 r1].
        destruct (bv.appView byte (1*byte) r1) as [b2 r2].
        destruct (bv.appView byte (0*byte) r2) as [b3 r3].
        destruct (bv.appView byte (3*byte) v2) as [c0 s0].
        destruct (bv.appView byte (2*byte) s0) as [c1 s1].
        destruct (bv.appView byte (1*byte) s1) as [c2 s2].
        destruct (bv.appView byte (0*byte) s2) as [c3 s3].
        exists (NonSyncVal b0 c0), (NonSyncVal b1 c1), (NonSyncVal b2 c2), (NonSyncVal b3 c3), (NonSyncVal r3 s3).
        split; [reflexivity|]. intros [].
    Qed.

    Lemma arr_ptsto_ptstomem1 `{sailGS2 Σ} (addr : RVAddr) (b : RelVal (ty.bvec byte)) :
      interp_ptsto addr b ⊢@{iPropI Σ} ∃ v : RelVal (ty.bvec (1*byte)), interp_ptstomem (width := 1) addr v ∗ ⌜secLeak b -> secLeak v⌝.
    Proof.
      iIntros "H". iExists (ty.liftBinOp (σ1 := ty.bvec byte) (σ2 := ty.bvec (0*byte)) (σ3 := ty.bvec (1*byte)) bv.app b (SyncVal bv.nil)).
      rewrite ptstomem_bv_app. iFrame "H". iSplit.
      - destruct addr, b; cbn; done.
      - iPureIntro. destruct b; cbn; tauto.
    Qed.

    Lemma arr_word_cell_bytes `{sailGS2 Σ} (pub : bool) (x : bv xlenbits) :
      interp_arr_cell pub 4 x ⊢@{iPropI Σ}
      [∗ list] j ∈ seq 0 4, interp_arr_cell pub 1 (bv.add x (bv.mul (bv.of_Z 1) (bv.of_nat j))).
    Proof.
      unfold interp_arr_cell. iIntros "[%Hr [%w [Hw %Hs]]]".
      destruct (arr_word_decomp w) as (b0&b1&b2&b3&r&->&Hsl).
      rewrite !ptstomem_bv_app. iDestruct "Hw" as "(H0 & H1 & H2 & H3 & _)".
      iPoseProof (arr_ptsto_ptstomem1 with "H0") as (v0) "[H0 %S0]".
      iPoseProof (arr_ptsto_ptstomem1 with "H1") as (v1) "[H1 %S1]".
      iPoseProof (arr_ptsto_ptstomem1 with "H2") as (v2) "[H2 %S2]".
      iPoseProof (arr_ptsto_ptstomem1 with "H3") as (v3) "[H3 %S3]".
      cbn [ty.liftUnOp seq big_opL].
      assert (E0 : bv.add x (bv.mul (bv.of_Z 1) (bv.of_nat 0)) = x).
      { change (bv.of_nat (n := xlenbits) 0) with (@bv.zero xlenbits). rewrite bv.of_Z_one.
        assert (Er : forall y : bv xlenbits, bv.add y (bv.mul bv.one bv.zero) = y) by (intros; ring). apply Er. }
      assert (E1 : bv.add x (bv.mul (bv.of_Z 1) (bv.of_nat 1)) = bv.add bv.one x).
      { change (bv.of_nat (n := xlenbits) 1) with (@bv.one xlenbits). rewrite bv.of_Z_one.
        assert (Er : forall y : bv xlenbits, bv.add y (bv.mul bv.one bv.one) = bv.add bv.one y) by (intros; ring). apply Er. }
      assert (E2 : bv.add x (bv.mul (bv.of_Z 1) (bv.of_nat 2)) = bv.add bv.one (bv.add bv.one x)).
      { change (bv.of_nat (n := xlenbits) 2) with (bv.add (@bv.one xlenbits) bv.one). rewrite bv.of_Z_one.
        assert (Er : forall y : bv xlenbits, bv.add y (bv.mul bv.one (bv.add bv.one bv.one)) = bv.add bv.one (bv.add bv.one y)) by (intros; ring). apply Er. }
      assert (E3 : bv.add x (bv.mul (bv.of_Z 1) (bv.of_nat 3)) = bv.add bv.one (bv.add bv.one (bv.add bv.one x))).
      { change (bv.of_nat (n := xlenbits) 3) with (bv.add (@bv.one xlenbits) (bv.add bv.one bv.one)). rewrite bv.of_Z_one.
        assert (Er : forall y : bv xlenbits, bv.add y (bv.mul bv.one (bv.add bv.one (bv.add bv.one bv.one))) = bv.add bv.one (bv.add bv.one (bv.add bv.one y))) by (intros; ring). apply Er. }
      rewrite E0 E1 E2 E3.
      assert (Hm : (Z.of_N maxAddr < 2 ^ Z.of_nat xlenbits)%Z) by (vm_compute; reflexivity).
      assert (U : forall y : bv xlenbits, (bv.unsigned y + 1 < 2 ^ Z.of_nat xlenbits)%Z -> bv.unsigned (bv.add bv.one y) = (bv.unsigned y + 1)%Z).
      { intros y Hy. rewrite bv.unsigned_add. change (bv.unsigned (@bv.one xlenbits)) with 1%Z.
        unfold bv.truncz. pose proof (bv.unsigned_bounds y). rewrite Z.mod_small; lia. }
      pose proof (bv.unsigned_bounds x) as Bx.
      assert (U1 : bv.unsigned (bv.add bv.one x) = (bv.unsigned x + 1)%Z) by (apply U; lia).
      assert (U2 : bv.unsigned (bv.add bv.one (bv.add bv.one x)) = (bv.unsigned x + 2)%Z) by (rewrite U; [rewrite U1; lia|rewrite U1; lia]).
      assert (U3 : bv.unsigned (bv.add bv.one (bv.add bv.one (bv.add bv.one x))) = (bv.unsigned x + 3)%Z) by (rewrite U; [rewrite U2; lia|rewrite U2; lia]).
      cbn [ty.liftUnOp] in *. rewrite U1 U2 U3.
      iSplitL "H0"; [iSplit; [iPureIntro; lia|iExists v0; iFrame "H0"; iPureIntro; intros Hp; apply S0, Hsl, Hs, Hp]|].
      iSplitL "H1"; [iSplit; [iPureIntro; lia|iExists v1; iFrame "H1"; iPureIntro; intros Hp; apply S1, Hsl, Hs, Hp]|].
      iSplitL "H2"; [iSplit; [iPureIntro; lia|iExists v2; iFrame "H2"; iPureIntro; intros Hp; apply S2, Hsl, Hs, Hp]|].
      iSplitL "H3"; [iSplit; [iPureIntro; lia|iExists v3; iFrame "H3"; iPureIntro; intros Hp; apply S3, Hsl, Hs, Hp]|].
      done.
    Qed.

    Lemma arr_words_cells_bytes `{sailGS2 Σ} (pub : bool) (a : bv xlenbits) (m : nat) :
      ([∗ list] i ∈ seq 0 m, interp_arr_cell pub 4 (bv.add a (bv.mul (bv.of_Z 4) (bv.of_nat i))))
      ⊢@{iPropI Σ} [∗ list] j ∈ seq 0 (4 * m), interp_arr_cell pub 1 (bv.add a (bv.mul (bv.of_Z 1) (bv.of_nat j))).
    Proof.
      induction m as [|m IH]; [iIntros "_"; done|].
      rewrite seq_S big_sepL_app. replace (4 * S m)%nat with (4 * m + 4)%nat by lia.
      rewrite seq_app big_sepL_app. iIntros "[Hm Hl]". iSplitL "Hm"; [iApply (IH with "Hm")|].
      cbn [big_opL]. iDestruct "Hl" as "[Hl _]".
      iPoseProof (arr_word_cell_bytes with "Hl") as "Hb".
      rewrite Nat.add_0_l.
      rewrite -{1}(Nat.add_0_r (4 * m)%nat).
      replace (0 + (4 * m + 0))%nat with (4 * m + 0)%nat by lia.
      rewrite <- (fmap_add_seq (4 * m)%nat 0 4). rewrite big_sepL_fmap.
      iApply (big_sepL_mono with "Hb"). intros k j _. cbv beta.
      assert (H4 : @bv.of_nat xlenbits (4 * m) = bv.mul (bv.of_Z 4) (bv.of_nat m)).
      { unfold bv.of_nat. rewrite Nat2N.inj_mul. rewrite -!bv.of_Z_N bv.of_Z_mul. f_equal. lia. }
      rewrite arr_of_nat_add H4 bv.of_Z_one.
      assert (Er : forall a0 X M : bv xlenbits, bv.add (bv.add a0 (bv.mul (bv.of_Z 4) M)) (bv.mul bv.one X)
                    = bv.add a0 (bv.mul bv.one (bv.add (bv.mul (bv.of_Z 4) M) X))) by (intros; ring).
      rewrite Er. done.
    Qed.

    Lemma interp_arr_bytes_of_words `{sailGS2 Σ} (pub : bool) (a n e : bv xlenbits) :
      (bv.bin n < 1073741824)%N ->
      interp_arr pub 4 4 (SV a) (SV n) (SV e) ⊢@{iPropI Σ}
      interp_arr pub 1 1 (SV a) (SV (bv.mul (bv.of_N 4) n)) (SV e).
    Proof.
      intros Hn. cbn [interp_arr]. iIntros "[%He Hc]".
      assert (Hb : bv.bin (bv.mul (@bv.of_N xlenbits 4) n) = (4 * bv.bin n)%N).
      { unfold bv.mul. change (bv.bin (@bv.of_N xlenbits 4)) with 4%N.
        apply bv.bin_of_N_small. change (bv.exp2 xlenbits) with 4294967296%N. lia. }
      iSplit.
      { iPureIntro. subst e. rewrite bv.of_Z_one.
        change (@bv.of_N xlenbits 4) with (@bv.of_Z xlenbits 4).
        assert (Er : forall a0 X : bv xlenbits, bv.add a0 (bv.mul (bv.of_Z 4) X) = bv.add a0 (bv.mul bv.one (bv.mul (bv.of_Z 4) X))) by (intros; ring).
        apply Er. }
      rewrite Hb. replace (N.to_nat (4 * bv.bin n)) with (4 * N.to_nat (bv.bin n))%nat by lia.
      iApply (arr_words_cells_bytes with "Hc").
    Qed.

    Lemma clem_bytes_of_words_sound `{sailGS2 Σ} (pub : bool) :
      ValidLemma (clem_lemma
                    (clem_arr_bytes_of_words pub)).
    Proof.
      intros ι. cbv [clem_ctx] in ι. destruct_syminstance ι.
      destruct a as [a|]; destruct n as [n|]; destruct e as [e|];
        cbn -[interp_arr]; try (iIntros "[[] _]").
      iIntros "[Harr [%Hlt _]]".
      iApply (interp_arr_bytes_of_words with "Harr").
      unfold bv.ult in Hlt. change (bv.bin (@bv.of_N xlenbits 1073741824)) with 1073741824%N in Hlt. exact Hlt.
    Qed.

    (* ---- regrouping cells of any width k through bytes ----------------- *)
    (* (clem_arr_to_bytes / clem_arr_of_bytes, PLAN-general-endtoend.md B4).
       A k-byte cell IS k byte cells, for any RelVal value: the value splits
       by bv.appView (S k · byte reduces to byte + k · byte), ownership by
       ptstomem_bv_app, publicness carried per byte; and back. *)
    Lemma rg_decomp (k : nat) (v : RelVal (ty.bvec (S k * byte))) :
      exists (B : RelVal (ty.bvec byte)) (Bs : RelVal (ty.bvec (k * byte))),
        v = ty.liftBinOp (σ1 := ty.bvec byte) (σ2 := ty.bvec (k*byte)) (σ3 := ty.bvec (S k*byte)) bv.app B Bs
        /\ (secLeak v <-> secLeak B /\ secLeak Bs).
    Proof.
      destruct v as [x|x1 x2].
      - destruct (bv.appView byte (k*byte) x) as [b bs]. exists (SV b), (SV bs). split; [reflexivity|cbn; tauto].
      - destruct (bv.appView byte (k*byte) x1) as [b1 bs1]. destruct (bv.appView byte (k*byte) x2) as [b2 bs2].
        exists (NonSyncVal b1 b2), (NonSyncVal bs1 bs2). split; [reflexivity|cbn; tauto].
    Qed.
    Lemma rg_app_leak (k : nat) (B : RelVal (ty.bvec byte)) (Bs : RelVal (ty.bvec (k * byte))) :
      secLeak B -> secLeak Bs ->
      secLeak (ty.liftBinOp (σ1 := ty.bvec byte) (σ2 := ty.bvec (k*byte)) (σ3 := ty.bvec (S k*byte)) bv.app B Bs).
    Proof. destruct B, Bs; cbn; tauto. Qed.
    Lemma rg_of_nat_S (x : bv xlenbits) (j : nat) : bv.add (bv.add bv.one x) (bv.of_nat j) = bv.add x (bv.of_nat (S j)).
    Proof. rewrite bv.of_nat_S. ring. Qed.
    Lemma rg_of_nat_0 (x : bv xlenbits) : bv.add x (bv.of_nat 0) = x.
    Proof. change (bv.of_nat (n := xlenbits) 0) with (@bv.zero xlenbits). ring. Qed.

    Definition rg_own `{sailGS2 Σ} (pub : bool) (k : nat) (x : bv xlenbits) : iProp Σ :=
      ∃ w : RelVal (ty.bvec (k * byte)), interp_ptstomem (SV x) w ∗ ⌜pub = true -> secLeak w⌝.

    Lemma rg_own_split `{sailGS2 Σ} (pub : bool) (k : nat) (x : bv xlenbits) :
      rg_own pub k x ⊢ [∗ list] j ∈ seq 0 k, rg_own pub 1 (bv.add x (bv.of_nat j)).
    Proof.
      revert x. induction k as [|k IH]; intros x; [iIntros "_"; done|].
      iIntros "[%w [Hw %Hs]]". destruct (rg_decomp w) as (B & Bs & -> & HL).
      rewrite ptstomem_bv_app. iDestruct "Hw" as "[HB HBs]".
      cbn [seq big_opL]. iSplitL "HB".
      - iPoseProof (arr_ptsto_ptstomem1 with "HB") as (u) "[Hu %Su]".
        rewrite rg_of_nat_0. iExists u. iFrame "Hu". iPureIntro. intros Hp. apply Su, HL, Hs, Hp.
      - rewrite -fmap_S_seq big_sepL_fmap.
        iPoseProof (IH (bv.add bv.one x) with "[HBs]") as "H".
        { iExists Bs. cbn [ty.liftUnOp]. iFrame "HBs". iPureIntro. intros Hp. apply HL, Hs, Hp. }
        iApply (big_sepL_mono with "H"). intros i j _. cbv beta. rewrite rg_of_nat_S. done.
    Qed.

    Lemma rg_own1_ptsto `{sailGS2 Σ} (pub : bool) (x : bv xlenbits) :
      rg_own pub 1 x ⊢ ∃ B : RelVal (ty.bvec byte), interp_ptsto (SV x) B ∗ ⌜pub = true -> secLeak B⌝.
    Proof.
      iIntros "[%u [Hu %Su]]". destruct (@rg_decomp 0 u) as (B & r & -> & HL).
      rewrite ptstomem_bv_app. iDestruct "Hu" as "[HB _]".
      iExists B. iFrame "HB". iPureIntro. intros Hp. apply HL, Su, Hp.
    Qed.

    Lemma rg_own0 `{sailGS2 Σ} (pub : bool) (x : bv xlenbits) : ⊢@{iPropI Σ} rg_own pub 0 x.
    Proof.
      iExists (SV bv.nil). iSplit; [|iPureIntro; intros; exact I].
      unfold interp_ptstomem. cbn. done.
    Qed.

    Lemma rg_own_join `{sailGS2 Σ} (pub : bool) (k : nat) (x : bv xlenbits) :
      ([∗ list] j ∈ seq 0 k, rg_own pub 1 (bv.add x (bv.of_nat j))) ⊢ rg_own pub k x.
    Proof.
      revert x. induction k as [|k IH]; intros x; [iIntros "_"; iApply rg_own0|].
      cbn [seq big_opL]. iIntros "[H0 Hr]".
      rewrite rg_of_nat_0. iPoseProof (rg_own1_ptsto with "H0") as (B) "[HB %SB]".
      rewrite -fmap_S_seq big_sepL_fmap.
      iPoseProof (IH (bv.add bv.one x) with "[Hr]") as (Bs) "[HBs %SBs]".
      { iApply (big_sepL_mono with "Hr"). intros i j _. cbv beta. rewrite rg_of_nat_S. done. }
      iExists (ty.liftBinOp (σ1 := ty.bvec byte) (σ2 := ty.bvec (k*byte)) (σ3 := ty.bvec (S k*byte)) bv.app B Bs).
      rewrite ptstomem_bv_app. iFrame "HB". cbn [ty.liftUnOp]. iFrame "HBs".
      iPureIntro. intros Hp. apply rg_app_leak; [apply SB, Hp|apply SBs, Hp].
    Qed.

    Lemma rg_maxAddr : (Z.of_N maxAddr < 2 ^ Z.of_nat xlenbits)%Z.
    Proof. vm_compute. reflexivity. Qed.
    Lemma rg_unsigned_add (x : bv xlenbits) (j : nat) :
      (bv.unsigned x + Z.of_nat j < 2 ^ Z.of_nat xlenbits)%Z ->
      bv.unsigned (bv.add x (bv.of_nat j)) = (bv.unsigned x + Z.of_nat j)%Z.
    Proof.
      intros H. rewrite bv.unsigned_add. unfold bv.of_nat.
      rewrite -(bv.of_Z_N) bv.unsigned_of_Z. pose proof (bv.unsigned_bounds x).
      unfold bv.truncz. rewrite nat_N_Z. rewrite (Z.mod_small (Z.of_nat j)); [|lia]. apply Z.mod_small. lia.
    Qed.

    Lemma rg_cell_split `{sailGS2 Σ} (pub : bool) (k : nat) (x : bv xlenbits) :
      interp_arr_cell pub k x ⊢@{iPropI Σ} [∗ list] j ∈ seq 0 k, interp_arr_cell pub 1 (bv.add x (bv.of_nat j)).
    Proof.
      unfold interp_arr_cell. iIntros "[%Hr H]".
      iPoseProof (rg_own_split pub k x with "H") as "H".
      iApply (big_sepL_impl with "H"). iIntros "!>" (i j Hj) "H".
      apply lookup_seq in Hj as [-> Hlt]. pose proof rg_maxAddr. pose proof (bv.unsigned_bounds x).
      iSplit; [iPureIntro|unfold rg_own; iExact "H"].
      rewrite rg_unsigned_add; lia.
    Qed.

    Lemma rg_cell_join `{sailGS2 Σ} (pub : bool) (k : nat) (x : bv xlenbits) :
      (1 <= k)%nat -> (Z.of_nat k <= 2 ^ 20)%Z ->
      ([∗ list] j ∈ seq 0 k, interp_arr_cell pub 1 (bv.add x (bv.of_nat j))) ⊢@{iPropI Σ} interp_arr_cell pub k x.
    Proof.
      intros Hk1 Hk2. unfold interp_arr_cell. rewrite big_sepL_sep. iIntros "[Hp Ho]".
      iPoseProof (big_sepL_pure_1 with "Hp") as "%Hp".
      pose proof rg_maxAddr. pose proof (bv.unsigned_bounds x).
      assert (Hz : (bv.unsigned x + 1 <= Z.of_N maxAddr)%Z).
      { pose proof (Hp 0%nat 0%nat ltac:(apply lookup_seq; lia)) as Hq. cbv beta in Hq. rewrite rg_of_nat_0 in Hq. exact Hq. }
      assert (HL : (bv.unsigned (bv.add x (bv.of_nat (k - 1))) + 1 <= Z.of_N maxAddr)%Z).
      { exact (Hp (k - 1)%nat (k - 1)%nat ltac:(apply lookup_seq; lia)). }
      assert (Hmx : (Z.of_N maxAddr <= 2 ^ 20)%Z) by (vm_compute; discriminate).
      rewrite rg_unsigned_add in HL; [|change (Z.of_nat xlenbits) with 32%Z in *; lia].
      iSplit; [iPureIntro; lia|].
      iPoseProof (rg_own_join pub k x with "[Ho]") as "H"; [unfold rg_own; iExact "Ho"|]. unfold rg_own. iExact "H".
    Qed.

    Lemma rg_of_nat_mul (k n : nat) : @bv.of_nat xlenbits (k * n) = bv.mul (bv.of_Z (Z.of_nat k)) (bv.of_nat n).
    Proof. unfold bv.of_nat. rewrite Nat2N.inj_mul -!bv.of_Z_N bv.of_Z_mul. f_equal. lia. Qed.

    Lemma rg_cells_split `{sailGS2 Σ} (pub : bool) (k : nat) (a : bv xlenbits) (n : nat) :
      ([∗ list] i ∈ seq 0 n, interp_arr_cell pub k (bv.add a (bv.mul (bv.of_Z (Z.of_nat k)) (bv.of_nat i))))
      ⊢@{iPropI Σ} [∗ list] j ∈ seq 0 (k * n), interp_arr_cell pub 1 (bv.add a (bv.mul (bv.of_Z 1) (bv.of_nat j))).
    Proof.
      induction n as [|n IH]; [rewrite Nat.mul_0_r; iIntros "_"; done|].
      rewrite seq_S big_sepL_app. replace (k * S n)%nat with (k * n + k)%nat by lia.
      rewrite seq_app big_sepL_app. iIntros "[Hm Hl]". iSplitL "Hm"; [iApply (IH with "Hm")|].
      cbn [big_opL]. iDestruct "Hl" as "[Hl _]".
      iPoseProof (rg_cell_split with "Hl") as "Hb".
      rewrite Nat.add_0_l -{1}(Nat.add_0_r (k * n)%nat).
      replace (0 + (k * n + 0))%nat with (k * n + 0)%nat by lia.
      rewrite <- (fmap_add_seq (k * n)%nat 0 k). rewrite big_sepL_fmap.
      iApply (big_sepL_mono with "Hb"). intros i j _. cbv beta.
      rewrite arr_of_nat_add rg_of_nat_mul bv.of_Z_one.
      assert (Er : forall a0 X M K : bv xlenbits, bv.add (bv.add a0 (bv.mul K M)) X
                    = bv.add a0 (bv.mul bv.one (bv.add (bv.mul K M) X))) by (intros; ring).
      rewrite Er. done.
    Qed.

    Lemma rg_cells_join `{sailGS2 Σ} (pub : bool) (k : nat) (a : bv xlenbits) (q : nat) :
      (1 <= k)%nat -> (Z.of_nat k <= 2 ^ 20)%Z ->
      ([∗ list] j ∈ seq 0 (k * q), interp_arr_cell pub 1 (bv.add a (bv.mul (bv.of_Z 1) (bv.of_nat j))))
      ⊢@{iPropI Σ} [∗ list] i ∈ seq 0 q, interp_arr_cell pub k (bv.add a (bv.mul (bv.of_Z (Z.of_nat k)) (bv.of_nat i))).
    Proof.
      intros Hk1 Hk2.
      induction q as [|q IH]; [rewrite Nat.mul_0_r; iIntros "_"; done|].
      replace (k * S q)%nat with (k * q + k)%nat by lia.
      rewrite seq_app big_sepL_app seq_S big_sepL_app. iIntros "[Hm Hl]". iSplitL "Hm"; [iApply (IH with "Hm")|].
      cbn [big_opL]. iSplit; [|done].
      iApply rg_cell_join; [exact Hk1|exact Hk2|].
      replace (0 + k * q)%nat with (k * q + 0)%nat by lia.
      rewrite <- (fmap_add_seq (k * q)%nat 0 k). rewrite big_sepL_fmap.
      iApply (big_sepL_mono with "Hl"). intros i j _. cbv beta.
      rewrite arr_of_nat_add rg_of_nat_mul bv.of_Z_one.
      assert (Er : forall a0 X M K : bv xlenbits, bv.add (bv.add a0 (bv.mul K M)) X
                    = bv.add a0 (bv.mul bv.one (bv.add (bv.mul K M) X))) by (intros; ring).
      rewrite Er. done.
    Qed.

    Lemma rg_bin_mulk (k : nat) (n : bv xlenbits) : (Z.of_nat k <= 2 ^ 20)%Z -> (N.of_nat k * bv.bin n < 4294967296)%N ->
      bv.bin (bv.mul (@bv.of_N xlenbits (N.of_nat k)) n) = (N.of_nat k * bv.bin n)%N.
    Proof.
      intros Hk H. unfold bv.mul.
      rewrite (bv.bin_of_N_small (n := xlenbits) (x := N.of_nat k)); [|change (bv.exp2 xlenbits) with 4294967296%N; lia].
      apply bv.bin_of_N_small. change (bv.exp2 xlenbits) with 4294967296%N. lia.
    Qed.

    Lemma rg_mv (k : nat) (m q r : bv xlenbits) : (Z.of_nat k <= 2 ^ 20)%Z ->
      bv.bin m = (N.of_nat k * bv.bin q + bv.bin r)%N ->
      m = bv.add (bv.mul (bv.of_Z (Z.of_nat k)) q) r.
    Proof.
      intros Hk Hm. pose proof (bv.bv_is_wf m) as Wm. change (bv.exp2 xlenbits) with 4294967296%N in Wm.
      rewrite -(nat_N_Z k) bv.of_Z_N.
      apply bv.bin_inj. unfold bv.add, bv.mul.
      rewrite (bv.bin_of_N_small (n := xlenbits) (x := N.of_nat k)); [|change (bv.exp2 xlenbits) with 4294967296%N; lia].
      rewrite (bv.bin_of_N_small (n := xlenbits) (x := (N.of_nat k * bv.bin q)%N)); [|change (bv.exp2 xlenbits) with 4294967296%N; lia].
      rewrite bv.bin_of_N_small; [lia|change (bv.exp2 xlenbits) with 4294967296%N; lia].
    Qed.

    Lemma rg_arr_to_bytes `{sailGS2 Σ} (pub : bool) (k : nat) (a n e : bv xlenbits) :
      (Z.of_nat k <= 2 ^ 20)%Z -> (N.of_nat k * bv.bin n < 4294967296)%N ->
      interp_arr pub k (Z.of_nat k) (SV a) (SV n) (SV e) ⊢@{iPropI Σ}
      interp_arr pub 1 1 (SV a) (SV (bv.mul (bv.of_N (N.of_nat k)) n)) (SV e).
    Proof.
      intros Hk Hn. cbn [interp_arr]. iIntros "[%He Hc]".
      iSplit.
      { iPureIntro. subst e. rewrite bv.of_Z_one -bv.of_Z_N nat_N_Z.
        assert (Er : forall a0 K X : bv xlenbits, bv.add a0 (bv.mul K X) = bv.add a0 (bv.mul bv.one (bv.mul K X))) by (intros; ring).
        apply Er. }
      rewrite rg_bin_mulk; [|exact Hk|exact Hn].
      replace (N.to_nat (N.of_nat k * bv.bin n)) with (k * N.to_nat (bv.bin n))%nat by lia.
      iApply (rg_cells_split with "Hc").
    Qed.

    Lemma rg_arr_of_bytes `{sailGS2 Σ} (pub : bool) (k : nat) (a m e q r : bv xlenbits) :
      (1 <= k)%nat -> (Z.of_nat k <= 2 ^ 20)%Z ->
      bv.bin m = (N.of_nat k * bv.bin q + bv.bin r)%N ->
      interp_arr pub 1 1 (SV a) (SV m) (SV e) ⊢@{iPropI Σ}
      interp_arr pub k (Z.of_nat k) (SV a) (SV q) (SV (bv.add a (bv.mul (bv.of_Z (Z.of_nat k)) q)))
      ∗ interp_arr pub 1 1 (SV (bv.add a (bv.mul (bv.of_Z (Z.of_nat k)) q))) (SV r) (SV e).
    Proof.
      intros Hk1 Hk2 Hm. pose proof (@rg_mv k m q r Hk2 Hm) as Hmv.
      cbn [interp_arr]. iIntros "[%He Hc]".
      rewrite Hm. replace (N.to_nat (N.of_nat k * bv.bin q + bv.bin r)) with (k * N.to_nat (bv.bin q) + N.to_nat (bv.bin r))%nat by lia.
      rewrite seq_app big_sepL_app. iDestruct "Hc" as "[H1 H2]".
      iSplitL "H1".
      { iSplit; [done|]. iApply (rg_cells_join with "H1"); assumption. }
      iSplit.
      { iPureIntro. subst e. rewrite bv.of_Z_one {1}Hmv.
        assert (Er : forall a0 K Q R : bv xlenbits, bv.add a0 (bv.mul bv.one (bv.add (bv.mul K Q) R)) = bv.add (bv.add a0 (bv.mul K Q)) (bv.mul bv.one R)) by (intros; ring).
        apply Er. }
      replace (0 + k * N.to_nat (bv.bin q))%nat with (k * N.to_nat (bv.bin q) + 0)%nat by lia.
      rewrite <- (fmap_add_seq (k * N.to_nat (bv.bin q))%nat 0). rewrite big_sepL_fmap.
      iApply (big_sepL_mono with "H2"). intros i j _. cbv beta.
      rewrite arr_of_nat_add rg_of_nat_mul arr_of_nat_bin bv.of_Z_one.
      assert (Er : forall a0 K Q X : bv xlenbits, bv.add a0 (bv.mul bv.one (bv.add (bv.mul K Q) X)) = bv.add (bv.add a0 (bv.mul K Q)) (bv.mul bv.one X)) by (intros; ring).
      rewrite Er. done.
    Qed.

    Lemma rg_shiftr_bin (m : bv xlenbits) (sh : nat) : (sh < 5)%nat ->
      bv.bin (bv.shiftr m (@bv.of_N 5 (N.of_nat sh))) = (bv.bin m / 2 ^ N.of_nat sh)%N.
    Proof.
      intros Hs. unfold bv.shiftr.
      assert (E5 : bv.unsigned (@bv.of_N 5 (N.of_nat sh)) = Z.of_nat sh).
      { unfold bv.unsigned. rewrite bv.bin_of_N_small; [lia|cbn; lia]. }
      rewrite E5 Z.shiftr_div_pow2; [|lia].
      pose proof (bv.bv_is_wf m) as Wm. change (bv.exp2 xlenbits) with 4294967296%N in Wm.
      unfold bv.of_Z. rewrite bv.bin_of_N_small.
      - unfold bv.unsigned. unfold bv.truncz. change (Z.of_nat xlenbits) with 32%Z.
        assert (Hd : (0 <= Z.of_N (bv.bin m) / 2 ^ Z.of_nat sh < 2 ^ 32)%Z).
        { split; [apply Z.div_pos; lia|].
          apply (Z.le_lt_trans _ (Z.of_N (bv.bin m))); [apply Z.div_le_upper_bound; [lia|]; nia|].
          cbn. change (2 ^ 32)%Z with 4294967296%Z. change (@bv.bin xlenbits) with (@bv.bin 32) in *. lia. }
        rewrite Z.mod_small; [|exact Hd].
        rewrite Z2N.inj_div; [|lia|lia]. rewrite N2Z.id Z2N.inj_pow; [|lia|lia]. f_equal. f_equal. lia.
      - unfold bv.truncz. pose proof (Z.mod_pos_bound (bv.unsigned m / 2 ^ Z.of_nat sh) (2 ^ Z.of_nat xlenbits) ltac:(lia)) as B.
        change (bv.exp2 xlenbits) with 4294967296%N. change (Z.of_nat xlenbits) with 32%Z in B.
        change (2 ^ 32)%Z with 4294967296%Z in B. change (2 ^ Z.of_nat xlenbits)%Z with 4294967296%Z. lia.
    Qed.

    Lemma rg_land_bin (m : bv xlenbits) (sh : nat) : (sh < 5)%nat ->
      bv.bin (bv.land m (@bv.of_N xlenbits (2 ^ N.of_nat sh - 1))) = (bv.bin m mod 2 ^ N.of_nat sh)%N.
    Proof.
      intros Hs. unfold bv.land.
      assert (Hc : bv.bin (@bv.of_N xlenbits (2 ^ N.of_nat sh - 1)) = N.ones (N.of_nat sh)).
      { rewrite N.ones_equiv. rewrite bv.bin_of_N_small; [lia|].
        change (bv.exp2 xlenbits) with 4294967296%N.
        assert (2 ^ N.of_nat sh <= 2 ^ 4)%N by (apply N.pow_le_mono_r; lia). cbn in *. lia. }
      rewrite Hc N.land_ones. apply bv.bin_of_N_small.
      pose proof (bv.bv_is_wf m). eapply N.le_lt_trans; [apply N.Div0.mod_le|exact H].
    Qed.

    Lemma rg_divmod (m : bv xlenbits) (sh : nat) : (sh < 5)%nat ->
      bv.bin m = (N.of_nat (2 ^ sh) * bv.bin (bv.shiftr m (@bv.of_N 5 (N.of_nat sh)))
                  + bv.bin (bv.land m (@bv.of_N xlenbits (2 ^ N.of_nat sh - 1))))%N.
    Proof.
      intros Hs. rewrite rg_shiftr_bin; [|exact Hs]. rewrite rg_land_bin; [|exact Hs].
      rewrite Nat2N.inj_pow. change (N.of_nat 2) with 2%N. apply N.Div0.div_mod.
    Qed.

    Lemma clem_to_bytes_sound `{sailGS2 Σ} (pub : bool) (u : RgWidth) :
      ValidLemma (clem_lemma
                    (clem_arr_to_bytes pub u)).
    Proof.
      intros ι. cbv [clem_ctx] in ι. destruct_syminstance ι.
      destruct a as [a|]; destruct n as [n|]; destruct e as [e|];
        cbn -[interp_arr rg_k rg_bound];
        try (iIntros "[[] _]").
      iIntros "[Harr [%Hlt _]]".
      iApply (rg_arr_to_bytes with "Harr").
      - destruct u; cbn; lia.
      - unfold bv.ult in Hlt.
        assert (Eb : (bv.bin (@bv.of_N xlenbits (rg_bound u)) * N.of_nat (rg_k u) = 4294967296)%N).
        { destruct u; vm_compute; reflexivity. }
        assert (Hk : (1 <= N.of_nat (rg_k u))%N) by (destruct u; vm_compute; discriminate).
        (* restate at the plain xlenbits width index, or lia sees two atoms *)
        assert (Hlt' : (@bv.bin xlenbits n < bv.bin (@bv.of_N xlenbits (rg_bound u)))%N) by exact Hlt.
        clear Hlt. revert Hlt' Eb Hk.
        generalize (@bv.bin xlenbits n) (bv.bin (@bv.of_N xlenbits (rg_bound u))) (N.of_nat (rg_k u)).
        intros x b k Hx Hb Hk. nia.
    Qed.

    Lemma clem_of_bytes_sound `{sailGS2 Σ} (pub : bool) (u : RgWidth) :
      ValidLemma (clem_lemma
                    (clem_arr_of_bytes pub u)).
    Proof.
      intros ι. cbv [clem_ctx] in ι. destruct_syminstance ι.
      destruct a as [a|]; destruct n as [n|]; destruct e as [e|];
        cbn -[interp_arr rg_k rg_sh];
        try (iIntros "[]").
      iIntros "Harr".
      iApply (rg_arr_of_bytes with "Harr").
      - destruct u; cbn; lia.
      - destruct u; cbn; lia.
      - unfold rg_k. apply (@rg_divmod n (rg_sh u)). destruct u; cbn; lia.
    Qed.

    (* The catalogue's lemSemCFGVerif. *)
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
      destruct vs as [l|l r]; cbn; intros HL HR.
      - subst l. injection HR as <- <-. exists (ty.SyncVal hL), (ty.SyncVal tL). auto.
      - exists (ty.NonSyncVal hL hR), (ty.NonSyncVal tL tR). subst. auto.
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
      intros Hn. cbn [interp_arrv]. iIntros "(%He & %Hlen & %Hn' & Hcells)".
      destruct (ty.projLeft vs) as [|hL tL] eqn:EL.
      { exfalso. apply Hn. rewrite <- Hn'. reflexivity. }
      destruct (ty.projRight vs) as [|hR tR] eqn:ER; [discriminate|].
      destruct (@arrv_cons_split _ vs hL tL hR tR EL ER) as (x & r & -> & HxL & HxR & HrL & HrR).
      iExists x, r. iSplit; [done|].
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

    (* No n≠0 premise: a cons value is non-empty, and a count that wrapped
       to 0 still gives a consistent n-1 and end fact modulo 2^32. *)
    Lemma interp_arrv_take_cons `{sailGS2 Σ} (w : nat) (s : Z) (a n e : bv xlenbits) x r :
      interp_arrv w s (SV a) (SV n) (SV e) (bop.evalRel bop.cons x r) ⊢@{iPropI Σ}
        ⌜(bv.unsigned a + Z.of_nat w <= Z.of_N maxAddr)%Z⌝ ∗
        interp_ptstomem (SV a) x ∗
        interp_arrv w s (SV (bv.add a (bv.of_Z s))) (SV (bv.add n (bv.of_Z (-1)))) (SV e) r.
    Proof.
      cbn [interp_arrv]. destruct (arrv_proj_cons x r) as [-> ->].
      iIntros "(%He & %Hlen & %Hn' & Hcells)".
      cbn [zip big_opL]. iDestruct "Hcells" as "[[%Hr0 Hc0] Hrest]".
      cbn [length] in Hlen, Hn'. rewrite bv.of_nat_S in Hn'. subst n e.
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
      cbn [interp_arrv]. destruct (arrv_proj_cons x vs) as [-> ->].
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
      cbn [interp_arrv]. destruct (arrv_proj_snoc vs x) as [-> ->].
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

    Lemma clem_arrv_take_first_sound `{sailGS2 Σ} (w : nat) (s : Z) :
      ValidLemma (clem_lemma (clem_arrv_take_first w s)).
    Proof.
      intros ι. cbv [clemv_ctx] in ι. destruct_syminstance ι.
      destruct a as [a|]; destruct n as [n|]; destruct e as [e|];
        cbn -[interp_arrv interp_ptstomem]; try (iIntros "[[] _]").
      iIntros "[Harr [%Hne _]]".
      iDestruct (interp_arrv_take_first with "Harr") as (x r) "(%Hvs & %Hr & Hc & Harr)";
        [exact Hne|].
      iExists x, r. iFrame "Hc Harr". auto.
    Qed.

    Lemma clem_arrv_take_cons_sound `{sailGS2 Σ} (w : nat) (s : Z) :
      ValidLemma (clem_lemma (clem_arrv_take_cons w s)).
    Proof.
      intros ι. destruct_syminstance ι.
      destruct a as [a|]; destruct n as [n|]; destruct e as [e|];
        cbn -[interp_arrv interp_ptstomem]; try (iIntros "[]").
      iIntros "Harr".
      iDestruct (interp_arrv_take_cons with "Harr") as "(%Hr & Hc & Harr)".
      iFrame "Hc Harr". auto.
    Qed.

    Lemma clem_arrv_add_first_sound `{sailGS2 Σ} (w : nat) (s : Z) :
      ValidLemma (clem_lemma (clem_arrv_add_first w s)).
    Proof.
      intros ι. cbv [clemv_ctx] in ι. destruct_syminstance ι.
      destruct a as [a|]; destruct n as [n|]; destruct e as [e|];
        cbn -[interp_arrv interp_ptstomem]; try (iIntros "[[] _]").
      iIntros "[Harr [Hc [%Hr _]]]".
      iApply interp_arrv_add_first. iFrame "Harr Hc". auto.
    Qed.

    Lemma clem_arrv_add_last_sound `{sailGS2 Σ} (w : nat) (s : Z) :
      ValidLemma (clem_lemma (clem_arrv_add_last w s)).
    Proof.
      intros ι. cbv [clemv_ctx] in ι. destruct_syminstance ι.
      destruct a as [a|]; destruct n as [n|]; destruct e as [e|];
        cbn -[interp_arrv interp_ptstomem]; try (iIntros "[[] _]").
      iIntros "[Harr [Hc [%Hr _]]]".
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
    Proof. intros HL HR. destruct a, n, e; cbn [interp_arrv]; try done. by rewrite HL HR. Qed.

    (* a cell of a w ≥ 1 array owns (the left copy of) its first byte *)
    Definition arrv_byteQ `{sailGS2 Σ} (k : nat) : iProp Σ :=
      ∃ (x : bv xlenbits) b, ⌜Z.to_nat (bv.unsigned x) = k /\ (bv.unsigned x < Z.of_N maxAddr)%Z⌝ ∗
        @RiscvPmpIrisInstance.interp_ptsto _ memGS2_memGS_left x b.

    Lemma interp_arrv_length `{sailGS2 Σ} (w : nat) (s : Z) (a n e : bv xlenbits) vs :
      interp_arrv (S w) s (SV a) (SV n) (SV e) vs ⊢@{iPropI Σ}
      ⌜length (ty.projLeft vs) <= N.to_nat maxAddr⌝.
    Proof.
      cbn [interp_arrv]. iIntros "(%He & %Hlen & %Hn & Hcells)".
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
      cbn [interp_arrv]. iDestruct "H" as "(_ & %Hlen & %Hn & _)". iPureIntro.
      pose proof maxAddr_rep as Hm.
      assert (Hs : (N.of_nat (length (ty.projLeft vs)) < bv.exp2 xlenbits)%N) by lia.
      apply (f_equal (@bv.bin xlenbits)) in Hn. rewrite (bv.bin_of_nat_small Hs) in Hn. cbn in Hn.
      apply (f_equal N.to_nat) in Hn. rewrite Nat2N.id in Hn.
      pose proof Hn as Hn'. rewrite Hlen in Hn'.
      apply length_zero_iff_nil in Hn, Hn'. split; assumption.
    Qed.

    Lemma interp_arrv_pad `{sailGS2 Σ} (w : nat) (s : Z) (a n e b c : bv xlenbits) vs ws :
      interp_arrv (S w) s (SV a) (SV n) (SV e) vs ∗ interp_arrv (S w) s (SV b) (SV bv.zero) (SV c) ws
      ⊢@{iPropI Σ}
      interp_arrv (S w) s (SV a) (SV n) (SV e) (bop.evalRel bop.append vs ws)
      ∗ interp_arrv (S w) s (SV b) (SV bv.zero) (SV c) ws.
    Proof.
      iIntros "[Ha Hb]". iDestruct (interp_arrv_count0 with "Hb") as %[HL HR].
      iFrame "Hb". destruct (arrv_proj_app vs ws) as [E1 E2].
      iApply (interp_arrv_proj with "Ha"); rewrite ?E1 ?E2 ?HL ?HR app_nil_r; done.
    Qed.

    Lemma arrv_snoc_split {σ} (vs : RelVal (ty.list σ)) tL hL tR hR :
      ty.projLeft vs = tL ++ [hL] -> ty.projRight vs = tR ++ [hR] ->
      exists x r, vs = bop.evalRel bop.append r (bop.evalRel bop.cons x (ty.SyncVal []))
        /\ ty.projLeft x = hL /\ ty.projRight x = hR /\ ty.projLeft r = tL /\ ty.projRight r = tR.
    Proof.
      destruct vs as [l|l r]; cbn; intros HL HR.
      - subst l. apply app_inj_tail in HR as [<- <-].
        exists (ty.SyncVal hL), (ty.SyncVal tL). auto.
      - exists (ty.NonSyncVal hL hR), (ty.NonSyncVal tL tR). subst. auto.
    Qed.

    Lemma interp_arrv_take_last `{sailGS2 Σ} (w : nat) (s : Z) (a n e : bv xlenbits) vs :
      n <> bv.zero ->
      interp_arrv w s (SV a) (SV n) (SV e) vs ⊢@{iPropI Σ}
      ∃ x r, ⌜vs = bop.evalRel bop.append r (bop.evalRel bop.cons x (ty.SyncVal []))⌝ ∗
        ⌜(bv.unsigned (bv.add e (bv.of_Z (- s))) + Z.of_nat w <= Z.of_N maxAddr)%Z⌝ ∗
        interp_ptstomem (SV (bv.add e (bv.of_Z (- s)))) x ∗
        interp_arrv w s (SV a) (SV (bv.add n (bv.of_Z (-1)))) (SV (bv.add e (bv.of_Z (- s)))) r.
    Proof.
      intros Hn. cbn [interp_arrv]. iIntros "(%He & %Hlen & %Hn' & Hcells)".
      destruct (ty.projLeft vs) as [|y0 l0] eqn:EL0.
      { exfalso. apply Hn. rewrite <- Hn'. reflexivity. }
      destruct (exists_last (l := y0 :: l0) ltac:(discriminate)) as (tL & hL & EL).
      destruct (ty.projRight vs) as [|z0 m0] eqn:ER0; [cbn in Hlen; discriminate|].
      destruct (exists_last (l := z0 :: m0) ltac:(discriminate)) as (tR & hR & ER).
      rewrite <- EL0 in EL. rewrite <- ER0 in ER.
      destruct (@arrv_snoc_split _ vs tL hL tR hR EL ER) as (x & r & -> & HxL & HxR & HrL & HrR).
      iExists x, r. iSplit; [done|].
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
      intros Hae. cbn [interp_arrv]. iIntros "(%He & _)". iPureIntro. intros ->.
      apply Hae. subst e. symmetry. apply arrv_ring_zero.
    Qed.

    Lemma interp_arrv_empty `{sailGS2 Σ} (w : nat) (s : Z) (a : bv xlenbits) :
      ⊢@{iPropI Σ} interp_arrv w s (SV a) (SV bv.zero) (SV a) (ty.SyncVal []).
    Proof.
      cbn [interp_arrv]. iSplit; [iPureIntro; symmetry; apply arrv_ring_zero|]. cbn. auto.
    Qed.

    Lemma interp_arrv_empty_elim `{sailGS2 Σ} (w : nat) (s : Z) (a e : bv xlenbits) vs :
      interp_arrv w s (SV a) (SV bv.zero) (SV e) vs ⊢@{iPropI Σ} ⌜a = e⌝.
    Proof. cbn [interp_arrv]. iIntros "(%He & _)". iPureIntro. subst e. symmetry. apply arrv_ring_zero. Qed.

    Lemma interp_arrv_flip `{sailGS2 Σ} (w : nat) (s : Z) (a n e : bv xlenbits) vs :
      interp_arrv w s (SV a) (SV n) (SV e) vs ⊢@{iPropI Σ}
      interp_arrv w (- s) (SV (bv.add e (bv.of_Z (- s)))) (SV n) (SV (bv.add a (bv.of_Z (- s))))
        (uop.evalRel uop.rev vs).
    Proof.
      cbn [interp_arrv]. destruct (arrv_proj_rev vs) as [-> ->].
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
      cbn [interp_arrv]. destruct (arrv_proj_app v1 v2) as [-> ->].
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
      intros Ha. cbn [interp_arrv]. iIntros "[(%He1 & _) (%He2 & _)]". iPureIntro.
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
      destruct vs as [l|l r].
      - exists (ty.SyncVal (take k l)), (ty.SyncVal (drop k l)). cbn. rewrite take_drop. auto.
      - exists (ty.NonSyncVal (take k l) (take k r)), (ty.NonSyncVal (drop k l) (drop k r)).
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
      rewrite EsK EnK. cbn [interp_arrv]. iIntros "(%He & %Hlen & %Hn & Hc)".
      set (kn := N.to_nat (bv.bin K)).
      assert (EK : @bv.of_nat xlenbits kn = K).
      { unfold kn, bv.of_nat. rewrite N2Nat.id. apply bv.of_N_bin. }
      assert (Hkn : (kn <= length (ty.projLeft vs))%nat).
      { subst n. unfold kn. pose proof (bv.bin_of_nat_decr (n := xlenbits) (length (ty.projLeft vs))). lia. }
      destruct (@arrv_app_split _ vs kn) as (v1 & v2 & -> & H1L & H1R & H2L & H2R).
      iExists v1, v2. iSplit; [done|].
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

    Lemma clem_arrv_take_last_sound `{sailGS2 Σ} (w : nat) (s : Z) :
      ValidLemma (clem_lemma (clem_arrv_take_last w s)).
    Proof.
      intros ι. cbv [clemv_ctx] in ι. destruct_syminstance ι.
      destruct a as [a|]; destruct n as [n|]; destruct e as [e|];
        cbn -[interp_arrv interp_ptstomem]; try (iIntros "[[] _]").
      iIntros "[Harr [%Hne _]]".
      iDestruct (interp_arrv_take_last with "Harr") as (x r) "(%Hvs & %Hr & Hc & Harr)";
        [exact Hne|].
      iExists x, r. iFrame "Hc Harr". auto.
    Qed.

    Lemma clem_arrv_nonempty_sound `{sailGS2 Σ} (w : nat) (s : Z) :
      ValidLemma (clem_lemma (clem_arrv_nonempty w s)).
    Proof.
      intros ι. cbv [clemv_ctx] in ι. destruct_syminstance ι.
      destruct a as [a|]; destruct n as [n|]; destruct e as [e|];
        cbn -[interp_arrv]; try (iIntros "[[] _]").
      iIntros "[Harr [%Hne _]]".
      iDestruct (interp_arrv_nonempty with "Harr") as %Hn; [exact Hne|].
      iFrame "Harr". iSplit; [|done]. iPureIntro. exact Hn.
    Qed.

    Lemma clem_arrv_empty_sound `{sailGS2 Σ} (w : nat) (s : Z) :
      ValidLemma (clem_lemma (clem_arrv_empty w s)).
    Proof.
      intros ι. destruct_syminstance ι.
      (* a NonSyncVal address is ruled out by the secLeak precondition *)
      destruct a as [a|]; cbn -[interp_arrv]; [|iIntros "[[] _]"].
      iIntros "_". iApply interp_arrv_empty.
    Qed.

    (* count 0 gives start = end, and NOTHING about the value *)
    Lemma clem_arrv_empty_elim_sound `{sailGS2 Σ} (w : nat) (s : Z) :
      ValidLemma (clem_lemma (clem_arrv_empty_elim w s)).
    Proof.
      intros ι. destruct_syminstance ι.
      destruct a as [a|]; destruct e as [e|];
        cbn -[interp_arrv]; try (iIntros "[]").
      iIntros "Harr". iDestruct (interp_arrv_empty_elim with "Harr") as %Hae.
      iSplit; [|done]. iPureIntro. exact Hae.
    Qed.

    Lemma clem_arrv_lockstep_sound `{sailGS2 Σ} (w : nat) (s : Z) :
      ValidLemma (clem_lemma (clem_arrv_lockstep w s)).
    Proof.
      intros ι. destruct_syminstance ι.
      destruct a1 as [a1|]; destruct n as [n|]; destruct e1 as [e1|];
        destruct a2 as [a2|]; destruct e2 as [e2|];
        cbn -[interp_arrv]; try (iIntros "[[] _]"); try (iIntros "[_ [[] _]]").
      iIntros "[H1 [H2 [%Heq _]]]".
      iAssert ⌜a2 = e2⌝%I as %He2.
      { iApply (interp_arrv_lockstep with "[$H1 $H2]"). exact Heq. }
      iFrame "H1 H2". iSplit; [|done]. iPureIntro. exact He2.
    Qed.

    Lemma clem_arrv_drop_sound `{sailGS2 Σ} (w : nat) (s : Z) :
      ValidLemma (clem_lemma (clem_arrv_drop w s)).
    Proof. intros ι. cbn -[interp_arrv]. iIntros "_". iSplit; done. Qed.

    Lemma clem_arrv_flip_sound `{sailGS2 Σ} (w : nat) (s : Z) :
      ValidLemma (clem_lemma (clem_arrv_flip w s)).
    Proof.
      intros ι. cbv [clemv_ctx] in ι. destruct_syminstance ι.
      destruct a as [a|]; destruct n as [n|]; destruct e as [e|];
        cbn -[interp_arrv]; try (iIntros "[]").
      iIntros "Harr". by iApply interp_arrv_flip.
    Qed.

    Lemma clem_arrv_join_sound `{sailGS2 Σ} (w : nat) (s : Z) :
      ValidLemma (clem_lemma (clem_arrv_join w s)).
    Proof.
      intros ι. destruct_syminstance ι.
      destruct a as [a|]; destruct n as [n|]; destruct e as [e|];
        destruct n2 as [n2|]; destruct e2 as [e2|];
        cbn -[interp_arrv]; try (iIntros "[[] _]"); try (iIntros "[_ []]").
      iIntros "[H1 H2]". iApply (interp_arrv_join with "[$H1 $H2]").
    Qed.

    (* w = 0: the precondition is False (cells own no bytes, so a count of
       0 mod 2^32 says nothing about the length) *)
    Lemma clem_arrv_pad_sound `{sailGS2 Σ} (w : nat) (s : Z) :
      ValidLemma (clem_lemma (clem_arrv_pad w s)).
    Proof.
      intros ι. destruct_syminstance ι. destruct w as [|w].
      { cbn -[interp_arrv]. iIntros "(_ & _ & %Hf & _)". done. }
      destruct a as [a|]; destruct n as [n|]; destruct e as [e|];
        destruct b as [b|]; destruct c as [c|];
        cbn -[interp_arrv]; try (iIntros "[[] _]"); try (iIntros "[_ [[] _]]").
      iIntros "[Ha [Hb _]]". iApply (interp_arrv_pad with "[$Ha $Hb]").
    Qed.

    Lemma clem_arrv_split_sound `{sailGS2 Σ} (w : nat) (s : Z) (k : N) :
      ValidLemma (clem_lemma (clem_arrv_split w s k)).
    Proof.
      intros ι. cbv [clemv_ctx] in ι. destruct_syminstance ι.
      destruct a as [a|]; destruct n as [n|]; destruct e as [e|];
        cbn -[interp_arrv]; try (iIntros "[[] _]").
      iIntros "[Harr [%Hle _]]".
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
      cbn [interp_arrv]. destruct (arrv_proj_regroup vs) as [-> ->].
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
      cbn [interp_arrv]. destruct (arrv_proj_regroup v) as [EL ER].
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

    Lemma clem_arrv_to_bytes_sound `{sailGS2 Σ} :
      ValidLemma (clem_lemma clem_arrv_to_bytes).
    Proof.
      intros ι. cbv [clemv_ctx] in ι. destruct_syminstance ι.
      destruct a as [a|]; destruct n as [n|]; destruct e as [e|];
        cbn -[interp_arrv]; try (iIntros "[]").
      iIntros "Harr". by iApply interp_arrv_to_bytes.
    Qed.

    Lemma clem_arrv_of_bytes_sound `{sailGS2 Σ} :
      ValidLemma (clem_lemma clem_arrv_of_bytes).
    Proof.
      intros ι. destruct_syminstance ι.
      destruct a as [a|]; destruct k as [k|]; destruct e as [e|];
        cbn -[interp_arrv]; try (iIntros "[[] _]").
      iIntros "[Harr [%Hk _]]".
      iApply (interp_arrv_of_bytes with "Harr").
      unfold bv.ult in Hk. change (bv.bin (@bv.of_N xlenbits 1073741824)) with 1073741824%N in Hk.
      exact Hk.
    Qed.

    Lemma clemSem `{sailGS2 Σ} (k : CLem) :
      ValidLemma (clem_lemma k).
    Proof.
      destruct k; [apply clem_take_first_sound|apply clem_add_first_sound
                  |apply clem_nonempty_sound|apply clem_empty_sound
                  |apply clem_add_last_sound|apply clem_empty_elim_sound
                  |apply clem_lockstep_sound|apply clem_drop_sound
                  |apply clem_take_last_sound|apply clem_flip_sound
                  |apply clem_split_sound|apply clem_join_sound
                  |apply clem_bytes_of_words_sound
                  |apply clem_to_bytes_sound|apply clem_of_bytes_sound
                  |apply clem_arrv_take_first_sound|apply clem_arrv_take_cons_sound
                  |apply clem_arrv_add_first_sound|apply clem_arrv_add_last_sound
                  |apply clem_arrv_take_last_sound|apply clem_arrv_nonempty_sound
                  |apply clem_arrv_empty_sound|apply clem_arrv_empty_elim_sound
                  |apply clem_arrv_lockstep_sound|apply clem_arrv_drop_sound
                  |apply clem_arrv_flip_sound|apply clem_arrv_join_sound
                  |apply clem_arrv_pad_sound|apply clem_arrv_split_sound
                  |apply clem_arrv_to_bytes_sound|apply clem_arrv_of_bytes_sound].
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
