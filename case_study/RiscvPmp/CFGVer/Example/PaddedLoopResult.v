(* ========================================================================= *)
(* Example/ZZPaddedLoopResult.v -- SUB-TABLE loop cut (heavy half).           *)
(*                                                                           *)
(* Mirrors Example/CountdownComposedResult.v, with ONE difference that is    *)
(* the whole point: the Iris side owns `ptsto_instrs` of the WHOLE            *)
(* 66-instruction program, while each segment contract's table holds only    *)
(* the two instructions it executes.  The gap is closed by                    *)
(* TablesRel.v's `itable_faith_of_segment` (itself Tables.v's                 *)
(* `instrs_of_list_segment` + the pre-existing `itable_faith_weaken`),        *)
(* which is sound precisely because `itable_rel` is indexed by the TABLE and  *)
(* only asks that the map CONTAIN each entry.                                 *)
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
    (∃ v, pc ↦ᵣ SyncVal v ∗ ⌜pcOutOfInstrs_exitCond 0 padded_instrs v⌝)%I.

  (* The loop invariant.  Note the instruction resource is the WHOLE program,
     not the segment -- that is the change this file exists to demonstrate. *)
  Definition plInv (k : bv xlenbits) : iProp Σ :=
    (asn.interpret cdInvAsn (ik k)
     ∗ pc ↦ᵣ SyncVal (bv.of_N pl_head) ∗ (∃ v, nextpc ↦ᵣ v)
     ∗ Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs
         (ai_instr <$> instrs_of_list (bv.of_N 0) padded_annot))%I.

  Definition plInvN (n : nat) : iProp Σ :=
    (∃ k : bv xlenbits, ⌜bv.bin k = (N.of_nat n + 1)%N⌝ ∗ plInv k)%I.

  (* The sub-table faithfulness fact, shared by both segment contracts:
     the SEGMENT's table is faithful to the WHOLE program's store. *)
  Lemma pl_itable (k : bv xlenbits) :
    Katamaran.RiscvPmp.CFGVer.VerifierRel.itable_rel (w := wlctx cdCtx)
      (instrs_of_list (bv.of_N 0) padded_annot)
      (table_of_list (term_val ty_xlenbits (bv.of_N pl_head)) 0 pl_seg) (ik k).
  Proof.
    unfold padded_annot.
    (* pre/seg/post are EXPLICIT (Set Implicit Arguments marks only strict
       implicits, and `length pre` is not a rigid position); only Σ, cbase and
       off are implicit.  All of p, ι, cbase, pre, seg and post are determined
       by unification against the goal, because padded_annot was DEFINED as
       `pl_pre ++ pl_seg ++ pl_post`.  But `off` occurs in no explicit
       argument's type, so it cannot be inferred, and the `(off := _)` form
       needs every preceding EXPLICIT argument supplied first ("Not enough
       non implicit arguments").  Hence the fully-@ form: Σ p ι cbase off
       pre seg post. *)
    apply (@itable_faith_of_segment cdCtx
             (term_val ty_xlenbits (bv.of_N pl_head)) (ik k)
             (@bv.of_N xlenbits 0) pl_head pl_pre pl_seg pl_post).
    - reflexivity.
    - reflexivity.
    - unfold pl_pre, pl_seg, pl_post, pl_filler, cd_instrs, pl_head.
      cbn [List.length List.app List.repeat].
      change (bv.exp2 xlenbits) with 4294967296%N. cbn. lia.
  Qed.

  (* ===== BODY: one trip, n+1 -> n, at the loop head (offset 256). ===== *)
  Lemma pl_step (n : nat) : plInvN (S n) -∗ myWP2_loop (plInvN n).
  Proof.
    iIntros "(%k & %Hk & Hres0)".
    iDestruct "Hres0" as "(Hres & Hpc & Hnpc & Hinstrs)".
    pose proof valid_plBody as Hv.
    unfold ValidCFGVerifierContract, Valid_CFG_VC, CFG_VC_triple in Hv.
    cbn [cfg_map plBody] in Hv.
    pose proof (pl_itable k) as Hif.
    assert (Hef : Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx cdCtx)
                    pl_headExitCond (cfg_exits plBody) (ik k)).
    { constructor; [|constructor]. eexists. split; reflexivity. }
    assert (Hk2 : bv.bin k = (N.of_nat n + 2)%N) by lia.
    assert (Hdec : bv.bin (bvdec k) = (N.of_nat n + 1)%N) by (apply bvdec_bin; exact Hk2).
    assert (Hne : bvdec k <> bv.zero).
    { intros HH. rewrite HH in Hdec. cbn in Hdec. lia. }
    iApply (sound_scfg_verification_condition_myWP2 Hv (plInvN n) Hif Hef
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
      cbn in Hex. unfold pl_headExitCond in Hex.
      assert (Hav : av = bv.of_N pl_head)
        by (destruct (bv.eqb_spec av (bv.of_N pl_head)); congruence).
      subst av.
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
    pose proof valid_plFinal as Hv.
    unfold ValidCFGVerifierContract, Valid_CFG_VC, CFG_VC_triple in Hv.
    cbn [cfg_map plFinal] in Hv.
    pose proof (pl_itable k) as Hif.
    assert (Hef : Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx cdCtx)
                    (pcOutOfInstrs_exitCond 0 padded_instrs) (cfg_exits plFinal) (ik k)).
    { constructor; [|constructor]. eexists. split; reflexivity. }
    iApply (sound_scfg_verification_condition_myWP2 Hv plExit Hif Hef
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
      unfold plExit. iExists av. iFrame "Hpc". iPureIntro. rewrite Hex. exact I.
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
