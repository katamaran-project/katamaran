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
