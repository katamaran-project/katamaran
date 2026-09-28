(* ========================================================================= *)
(* Example/ZZPaddedLoopResult.v -- SUB-TABLE loop cut (heavy half).           *)
(*                                                                           *)
(* Mirrors Example/CountdownComposedResult.v, with ONE difference that is    *)
(* the whole point: the Iris side owns `ptsto_instrs` of the WHOLE            *)
(* 66-instruction program, while each segment contract's table holds only    *)
(* the two instructions it executes.  The gap is closed by the AST          *)
(* containment `pl_contain` (Tables.v's `instrs_of_list_segment`), which      *)
(* GenCompose.contract_run turns into table faithfulness itself -- sound      *)
(* precisely because `itable_rel` is indexed by the TABLE and only asks that  *)
(* the map CONTAIN each entry.                                                *)
(*                                                                           *)
(* Reuses bvdec / bvdec_one / bvdec_bin / ik / cdInvAsn from                  *)
(* CountdownComposedResult.v -- none of them mention the instruction list.    *)
(* ========================================================================= *)

From Coq Require Import
     ZArith.ZArith Lists.List micromega.Lia Strings.String.
From Katamaran Require Import
     Notations Bitvector Semantics
     RiscvPmp.CFGVer.Spec RiscvPmp.Machine RiscvPmp.Sig.
From stdpp Require Import gmap.
From Katamaran Require Import
     RiscvPmp.CFGVer.Verifier
     RiscvPmp.CFGVer.VerifierRel
     RiscvPmp.CFGVer.SpecIris
     RiscvPmp.CFGVer.TablesRel
     RiscvPmp.CFGVer.Noninterference
     RiscvPmp.CFGVer.Tables
     RiscvPmp.CFGVer.Contracts
     RiscvPmp.CFGVer.GenContract
     RiscvPmp.CFGVer.Adequacy
     RiscvPmp.CFGVer.EndToEnd
     RiscvPmp.CFGVer.GenSegment
     RiscvPmp.CFGVer.GenCompose
     RiscvPmp.CFGVer.Example.CountdownComposed
     RiscvPmp.CFGVer.Example.CountdownComposedResult
     RiscvPmp.CFGVer.Example.PaddedLoop.
From iris.base_logic Require Import lib.gen_heap lib.iprop invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac big_op.
From iris.program_logic Require weakestpre adequacy.
From iris.proofmode Require string_ident tactics.
From stdpp Require namespaces.
From Equations Require Import Equations.

Import RiscvPmpProgram.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import bv.notations.
Import env.notations.
Import ListNotations.

Import RiscvPmpCFGVerifExecutor.
Import Assembly.
Import RiscvPmp.Sig.
Import iris.proofmode.tactics.
Import IrisInstanceBinary.
Import RiscvPmpIrisInstance2.
Import RiscvPmpSemantics.
Import RiscvPmpIrisAdeqParams2.
Import SmallStepNotations.
Import IrisModelBinary.RiscvPmpIrisBase2.
Import iris.algebra.excl.
Import iris.algebra.gmap.
Import IrisModel.RiscvPmpIrisBase.

Section ComposePaddedLoop.
  Context {Σ} {GS : sailGS2 Σ}.

  (* The real exit: pc past the END OF THE WHOLE 66-instruction program. *)
  Definition plExit : iProp Σ :=
    (∃ v, pc ↦ᵣ SyncVal v ∗ ⌜atPc 264 v⌝)%I.

  (* The loop invariant.  Note the instruction resource is the WHOLE program,
     not the segment -- that is the change this file exists to demonstrate. *)
  Definition plInv (k : bv xlenbits) : iProp Σ :=
    (asn.interpret cdInvAsn (ik k)
     ∗ pc ↦ᵣ SyncVal (bv.of_N pl_head) ∗ (∃ v, nextpc ↦ᵣ v)
     ∗ Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs
         (ai_instr <$> instrs_of_list (bv.of_N 0) padded_annot))%I.

  Definition plInvN (n : nat) : iProp Σ :=
    (∃ k : bv xlenbits, ⌜bv.bin k = (N.of_nat n + 1)%N⌝ ∗ plInv k)%I.

  (* THE SEGMENT CONTRACTS ARE VALID -- sealed, from their own VCs.  The only
     place the annotated segment `pl_seg` appears (PLAN-valid-blk-annot.md
     Phase 4). *)
  Lemma plBody_valid : ValidCFGVerifierContract plBody.
  Proof. solve_valid valid_plBody. Qed.
  Lemma plFinal_valid : ValidCFGVerifierContract plFinal.
  Proof. solve_valid valid_plFinal. Qed.

  (* The segment's code sits inside the WHOLE program at pl_head -- an
     AST-level containment.  It replaced the annotated sub-table
     faithfulness fact pl_itable: contract_run derives faithfulness itself. *)
  Lemma pl_contain :
    instrs_of_list (bv.of_N pl_head) cd_instrs
      ⊆ ai_instr <$> instrs_of_list (bv.of_N 0) padded_annot.
  Proof.
    unfold padded_annot.
    pose proof (instrs_of_list_segment pl_pre pl_seg pl_post (@bv.of_N xlenbits 0)) as H.
    apply (map_fmap_mono ai_instr) in H.
    - rewrite fmap_instrs_of_list in H. exact H.
    - unfold pl_pre, pl_seg, pl_post, pl_filler, cd_instrs.
      cbn [List.length List.app List.repeat].
      change (bv.exp2 xlenbits) with 4294967296%N. cbn. lia.
  Qed.

  Lemma pl_fit :
    (bv.bin (@bv.of_N xlenbits pl_head) + 4 * N.of_nat (length cd_instrs)
       < bv.exp2 xlenbits)%N.
  Proof. change (bv.exp2 xlenbits) with 4294967296%N. cbn. lia. Qed.

  (* ===== BODY: one trip, n+1 -> n, at the loop head (offset 256). ===== *)
  Lemma pl_step (n : nat) : plInvN (S n) -∗ myWP2_loop (plInvN n).
  Proof.
    iIntros "(%k & %Hk & Hres0)".
    iDestruct "Hres0" as "(Hres & Hpc & Hnpc & Hinstrs)".
    assert (Hef : Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx cdCtx)
                    (SyncVal (bv.of_N pl_head)) (cfg_exit plBody) (ik k)).
    { eexists. split; reflexivity. }
    assert (Hk2 : bv.bin k = (N.of_nat n + 2)%N) by lia.
    assert (Hdec : bv.bin (bvdec k) = (N.of_nat n + 1)%N) by (apply bvdec_bin; exact Hk2).
    assert (Hne : bvdec k <> bv.zero).
    { intros HH. rewrite HH in Hdec. cbn in Hdec. lia. }
    iApply (contract_run plBody plBody_valid (ik k) (bv.of_N pl_head)
              (ai_instr <$> instrs_of_list (bv.of_N 0) padded_annot) _ (plInvN n)
              eq_refl pl_fit pl_contain Hef
              $! (SyncVal (bv.of_N pl_head)) with "[Hres Hpc Hnpc Hinstrs]").
    - unfold cdInvAsn. iEval (cbn) in "Hres". cbn. iFrame.
      iDestruct "Hres" as "(H1 & Hpriv & Hinv)".
      iSplitR "Hpriv Hinv"; [| iFrame].
      iSplitR; [iSplit; [iPureIntro; reflexivity | done]|].
      iSplitL "H1"; [iExact "H1"|].
      iSplitR; [iSplit; [done|done]|].
      iSplit; [|done]. iPureIntro.
      change ((k + minus1)%bv) with (bvdec k). exact Hne.
    - iIntros (an) "(%Hex & Hpc & Hnpc & Hinstrs & Hpost)".
      destruct an as [av|a1 a2]; [|contradiction].
      apply Katamaran.RiscvPmp.CFGVer.VerifierRel.exit_hit_spec in Hex.
      injection Hex as <-.
      iExists (bvdec k). iSplitR; [iPureIntro; exact Hdec|].
      unfold plInv, cdInvAsn. iEval (cbn) in "Hpost". cbn.
      iDestruct "Hpost" as "(H1 & _ & Hpriv & Hinv)".
      iFrame "Hpc Hnpc Hinstrs Hpriv Hinv". iExact "H1".
  Qed.

  (* ===== EXIT: the guard fails, leave the loop at 264. ===== *)
  Lemma pl_exit : plInvN 0 -∗ myWP2_loop plExit.
  Proof.
    iIntros "(%k & %Hk & Hres0)".
    iDestruct "Hres0" as "(Hres & Hpc & Hnpc & Hinstrs)".
    assert (Hef : Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx cdCtx)
                    (SyncVal (bv.of_N 264)) (cfg_exit plFinal) (ik k)).
    { eexists. split; reflexivity. }
    iApply (contract_run plFinal plFinal_valid (ik k) (bv.of_N pl_head)
              (ai_instr <$> instrs_of_list (bv.of_N 0) padded_annot) _ plExit
              eq_refl pl_fit pl_contain Hef
              $! (SyncVal (bv.of_N pl_head)) with "[Hres Hpc Hnpc Hinstrs]").
    - unfold cdInvAsn. iEval (cbn) in "Hres". cbn. iFrame.
      iDestruct "Hres" as "(H1 & Hpriv & Hinv)".
      iSplitR "Hpriv Hinv"; [| iFrame].
      iSplitR; [iSplit; [iPureIntro; reflexivity | done]|].
      iSplitL "H1"; [iExact "H1"|].
      iSplitR; [iSplit; [done|done]|].
      iSplit; [|done]. iPureIntro.
      change ((k + minus1)%bv) with (bvdec k). apply bvdec_one. cbn in Hk. exact Hk.
    - iIntros (an) "(%Hex & Hpc & Hnpc & Hinstrs & _)".
      destruct an as [av|a1 a2]; [|contradiction].
      unfold plExit. iExists av. iFrame "Hpc". iPureIntro.
      cbn in Hex. unfold atPc. rewrite Hex. exact I.
  Qed.

  (* ===== THE LOOP, for free from the two above. ===== *)
  Lemma pl_loop (n : nat) : plInvN n -∗ myWP2_loop plExit.
  Proof. apply (myWP2_loop_induction plInvN plExit pl_step pl_exit). Qed.

  Corollary pl_loop_from_2 : plInv (bv.of_N 2) -∗ myWP2_loop plExit.
  Proof.
    iIntros "H". iApply (pl_loop 1). iExists (bv.of_N 2).
    iSplitR; [iPureIntro; reflexivity|]. iExact "H".
  Qed.

End ComposePaddedLoop.
