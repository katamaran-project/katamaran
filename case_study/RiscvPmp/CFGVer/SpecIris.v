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
   soundness is proved below next to lemSemCFGVerif.  Light file; a bare
   Require, names qualified (see CFGVer/CLAUDE.md on Require Import Verifier). *)
From Katamaran Require RiscvPmp.CFGVer.Verifier.
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

    Lemma interp_arr_take_first `{sailGS2 Σ} (pub : bool) (s : Z) (a n e : bv xlenbits) :
      n <> bv.zero ->
      interp_arr pub s (SV a) (SV n) (SV e) ⊢@{iPropI Σ}
      interp_arr_cell pub a ∗
      interp_arr pub s (SV (bv.add a (bv.of_Z s))) (SV (bv.add n (bv.of_Z (-1)))) (SV e).
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
    Lemma interp_arr_add_first `{sailGS2 Σ} (pub : bool) (s : Z) (a n e : bv xlenbits) :
      interp_arr pub s (SV a) (SV n) (SV e) ∗ interp_arr_cell pub (bv.add a (bv.of_Z (- s)))
      ⊢@{iPropI Σ}
      interp_arr pub s (SV (bv.add a (bv.of_Z (- s)))) (SV (bv.add n (bv.of_Z 1))) (SV e).
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

    Lemma clem_take_first_sound `{sailGS2 Σ} (pub : bool) (s : Z) :
      ValidLemma (Katamaran.RiscvPmp.CFGVer.Verifier.clem_lemma
                    (Katamaran.RiscvPmp.CFGVer.Verifier.clem_arr_take_first pub s)).
    Proof.
      intros ι. cbv [Katamaran.RiscvPmp.CFGVer.Verifier.clem_ctx] in ι. destruct_syminstance ι.
      destruct a as [a|]; destruct n as [n|]; destruct e as [e|];
        cbn -[interp_arr]; try (iIntros "[[] _]").
      iIntros "[Harr [%Hne _]]".
      iDestruct (interp_arr_take_first with "Harr") as "[Hc $]"; [exact Hne|].
      iDestruct "Hc" as "[%Hr [%w [Hw %Hs]]]".
      iSplitL "Hw".
      { iExists w. iFrame "Hw". destruct pub; cbn.
        - iSplit; [iPureIntro; now apply Hs|done].
        - iSplit; done. }
      iSplit; [iPureIntro; exact Hr|done].
    Qed.

    Lemma clem_add_first_sound `{sailGS2 Σ} (pub : bool) (s : Z) :
      ValidLemma (Katamaran.RiscvPmp.CFGVer.Verifier.clem_lemma
                    (Katamaran.RiscvPmp.CFGVer.Verifier.clem_arr_add_first pub s)).
    Proof.
      intros ι. cbv [Katamaran.RiscvPmp.CFGVer.Verifier.clem_ctx] in ι. destruct_syminstance ι.
      destruct a as [a|]; destruct n as [n|]; destruct e as [e|];
        cbn -[interp_arr]; try (iIntros "[[] _]").
      iIntros "[Harr [[%w [Hw Hs]] [%Hr _]]]".
      iApply interp_arr_add_first. iFrame "Harr".
      unfold interp_arr_cell. iSplit; [iPureIntro; exact Hr|].
      iExists w. iFrame "Hw". destruct pub; cbn.
      - iDestruct "Hs" as "[%Hs _]". iPureIntro. intros _. exact Hs.
      - iPureIntro. discriminate.
    Qed.

    (* ENTRY CHECK (PLAN-array-invariants Phase 1): an arr chunk is
       SATISFIABLE -- k concrete in-range cells at a, a+s, … ARE an array of
       count k ending at a + s·k, as long as k fits the count's width.  So an
       invariant stated over arr is not vacuous for want of a model (§R11's
       lesson for loop_reservoir), and this is the Iris half of the
       caller-side conversion Phase 3 needs. *)
    Lemma interp_arr_intro `{sailGS2 Σ} (pub : bool) (s : Z) (a : bv xlenbits) (k : nat) :
      (N.of_nat k < bv.exp2 xlenbits)%N ->
      ([∗ list] i ∈ seq 0 k, interp_arr_cell pub (bv.add a (bv.mul (bv.of_Z s) (bv.of_nat i))))
      ⊢@{iPropI Σ}
      interp_arr pub s (SV a) (SV (bv.of_nat k)) (SV (bv.add a (bv.mul (bv.of_Z s) (bv.of_nat k)))).
    Proof.
      intros Hk. cbn [interp_arr]. iIntros "H". iSplit; [done|].
      rewrite bv.bin_of_nat_small; [|exact Hk]. rewrite Nat2N.id. iExact "H".
    Qed.

    (* An array whose start is not its end is non-empty: with n = 0 the end
       fact gives e = a. *)
    Lemma clem_nonempty_sound `{sailGS2 Σ} (pub : bool) (s : Z) :
      ValidLemma (Katamaran.RiscvPmp.CFGVer.Verifier.clem_lemma
                    (Katamaran.RiscvPmp.CFGVer.Verifier.clem_arr_nonempty pub s)).
    Proof.
      intros ι. cbv [Katamaran.RiscvPmp.CFGVer.Verifier.clem_ctx] in ι. destruct_syminstance ι.
      destruct a as [a|]; destruct n as [n|]; destruct e as [e|];
        cbn -[interp_arr]; try (iIntros "[[] _]").
      iIntros "[Harr [%Hne _]]".
      iAssert (⌜e = bv.add a (bv.mul (bv.of_Z s) n)⌝ ∗
               interp_arr pub s (SV a) (SV n) (SV e))%I with "[Harr]" as "[%He Harr]".
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
    Lemma interp_arr_add_last `{sailGS2 Σ} (pub : bool) (s : Z) (a n e : bv xlenbits) :
      interp_arr pub s (SV a) (SV n) (SV e) ∗ interp_arr_cell pub e
      ⊢@{iPropI Σ}
      interp_arr pub s (SV a) (SV (bv.add n (bv.of_Z 1))) (SV (bv.add e (bv.of_Z s))).
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

    Lemma clem_empty_sound `{sailGS2 Σ} (pub : bool) (s : Z) :
      ValidLemma (Katamaran.RiscvPmp.CFGVer.Verifier.clem_lemma
                    (Katamaran.RiscvPmp.CFGVer.Verifier.clem_arr_empty pub s)).
    Proof.
      intros ι. destruct_syminstance ι.
      (* a NonSyncVal address is ruled out by the secLeak precondition *)
      destruct a as [a|]; cbn -[interp_arr]; [|iIntros "[[] _]"].
      iIntros "_". cbn [interp_arr]. iSplit; [|done].
      iPureIntro. apply arr_ring_zero.
    Qed.

    Lemma clem_add_last_sound `{sailGS2 Σ} (pub : bool) (s : Z) :
      ValidLemma (Katamaran.RiscvPmp.CFGVer.Verifier.clem_lemma
                    (Katamaran.RiscvPmp.CFGVer.Verifier.clem_arr_add_last pub s)).
    Proof.
      intros ι. cbv [Katamaran.RiscvPmp.CFGVer.Verifier.clem_ctx] in ι. destruct_syminstance ι.
      destruct a as [a|]; destruct n as [n|]; destruct e as [e|];
        cbn -[interp_arr]; try (iIntros "[[] _]").
      iIntros "[Harr [[%w [Hw Hs]] [%Hr _]]]".
      iApply interp_arr_add_last. iFrame "Harr".
      unfold interp_arr_cell. iSplit; [iPureIntro; exact Hr|].
      iExists w. iFrame "Hw". destruct pub; cbn.
      - iDestruct "Hs" as "[%Hs _]". iPureIntro. intros _. exact Hs.
      - iPureIntro. discriminate.
    Qed.

    (* An EMPTY array's start is its end: the end fact at n = 0. *)
    Lemma clem_empty_elim_sound `{sailGS2 Σ} (pub : bool) (s : Z) :
      ValidLemma (Katamaran.RiscvPmp.CFGVer.Verifier.clem_lemma
                    (Katamaran.RiscvPmp.CFGVer.Verifier.clem_arr_empty_elim pub s)).
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
    Lemma clem_lockstep_sound `{sailGS2 Σ} (pub1 pub2 : bool) (s : Z) :
      ValidLemma (Katamaran.RiscvPmp.CFGVer.Verifier.clem_lemma
                    (Katamaran.RiscvPmp.CFGVer.Verifier.clem_arr_lockstep pub1 pub2 s)).
    Proof.
      intros ι. destruct_syminstance ι.
      destruct a1 as [a1|]; destruct n as [n|]; destruct e1 as [e1|];
        destruct a2 as [a2|]; destruct e2 as [e2|];
        cbn -[interp_arr]; try (iIntros "[[] _]"); try (iIntros "[_ [[] _]]").
      iIntros "[H1 [H2 [%Heq _]]]".
      iAssert (⌜e2 = bv.add a2 (bv.mul (bv.of_Z s) n)⌝ ∗
               interp_arr pub2 s (SV a2) (SV n) (SV e2))%I with "[H2]" as "[%He2 H2]".
      { cbn [interp_arr]. iDestruct "H2" as "[%He Hc]". iFrame "Hc". done. }
      iAssert (⌜e1 = bv.add a1 (bv.mul (bv.of_Z s) n)⌝ ∗
               interp_arr pub1 s (SV a1) (SV n) (SV e1))%I with "[H1]" as "[%He1 H1]".
      { cbn [interp_arr]. iDestruct "H1" as "[%He Hc]". iFrame "Hc". done. }
      iFrame "H1 H2". iSplit; [|done]. iPureIntro.
      subst e1 e2. eapply arr_lockstep_eq; eassumption.
    Qed.

    (* Dropping resources is sound in an affine logic. *)
    Lemma clem_drop_sound `{sailGS2 Σ} (pub : bool) (s : Z) :
      ValidLemma (Katamaran.RiscvPmp.CFGVer.Verifier.clem_lemma
                    (Katamaran.RiscvPmp.CFGVer.Verifier.clem_arr_drop pub s)).
    Proof. intros ι. cbn -[interp_arr]. iIntros "_". iSplit; done. Qed.

    (* The catalogue's lemSemCFGVerif. *)
    Lemma clemSem `{sailGS2 Σ} (k : Katamaran.RiscvPmp.CFGVer.Verifier.CLem) :
      ValidLemma (Katamaran.RiscvPmp.CFGVer.Verifier.clem_lemma k).
    Proof.
      destruct k; [apply clem_take_first_sound|apply clem_add_first_sound
                  |apply clem_nonempty_sound|apply clem_empty_sound
                  |apply clem_add_last_sound|apply clem_empty_elim_sound
                  |apply clem_lockstep_sound|apply clem_drop_sound].
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
