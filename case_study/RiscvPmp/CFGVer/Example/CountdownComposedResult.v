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
(* Example/CountdownComposedResult.v — LOOP CUT demonstrator (heavy half).   *)
(*                                                                           *)
(* `cd_loop` closes the loop by INDUCTION on the trip count, chaining the    *)
(* single body contract to itself:                                           *)
(*                                                                           *)
(*   base   counter = 1        -> cdFinal  -> the real exit                  *)
(*   step   counter = m+2      -> cdBody   -> back at the head with m+1,     *)
(*                                            then the induction hypothesis  *)
(*                                                                           *)
(* Each step discharges the loop body with ExitCond := myWP2_loop <real      *)
(* exit>, i.e. "one trip, then keep looping", and myWP2_loop_join collapses  *)
(* the nested loop.  That is exactly the Lob-guarded recursion myWP2_loop    *)
(* already provides, used at per-ITERATION granularity instead of per-run.   *)
(*                                                                           *)
(* See plans/PLAN-loop-invariant.md U9.                                       *)
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
     RiscvPmp.CFGVer.GenCompose
     RiscvPmp.CFGVer.Example.CountdownComposed.
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

Section ComposeLoop.
  Context {Σ} {GS : sailGS2 Σ}.

  (* Coq-level mirror of the term-level `dec`. *)
  Definition bvdec (k : bv xlenbits) : bv xlenbits := bv.add k minus1.

  Lemma bin_minus1 : bv.bin minus1 = 4294967295%N.
  Proof. reflexivity. Qed.

  Lemma bvdec_one (k : bv xlenbits) : bv.bin k = 1%N -> bvdec k = bv.zero.
  Proof.
    intros Hk. unfold bvdec. apply bv.bin_inj.
    rewrite bv.bin_add. rewrite Hk. rewrite bin_minus1. reflexivity.
  Qed.

  Lemma bvdec_bin (k : bv xlenbits) (m : nat) :
    bv.bin k = (N.of_nat m + 2)%N -> bv.bin (bvdec k) = (N.of_nat m + 1)%N.
  Proof.
    intros Hk. unfold bvdec. rewrite bv.bin_add. rewrite Hk. rewrite bin_minus1.
    pose proof (bv.bv_is_wf k) as Hb. rewrite Hk in Hb.
    change (bv.exp2 xlenbits) with 4294967296%N in Hb |- *.
    replace (N.of_nat m + 2 + 4294967295)%N
       with ((N.of_nat m + 1) + 1 * 4294967296)%N by lia.
    rewrite N.Div0.mod_add. apply N.mod_small. lia.
  Qed.

  Definition ik (k : bv xlenbits) : Valuation cdCtx :=
    [env].["k"∷ty_xlenbits ↦ SyncVal k].

  Definition cdExit : iProp Σ :=
    (∃ v, pc ↦ᵣ SyncVal v ∗ ⌜atPc 8 v⌝)%I.

  (* The LOOP INVARIANT, as an iProp: at the loop head, counter = k. *)
  Definition cdInv (k : bv xlenbits) : iProp Σ :=
    (asn.interpret cdInvAsn (ik k)
     ∗ pc ↦ᵣ SyncVal (bv.of_N 0) ∗ (∃ v, nextpc ↦ᵣ v)
     ∗ Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs
         (ai_instr <$> instrs_of_list (bv.of_N 0) (list_AST_AnnotInstr (cfg_instrs cdBody))))%I.

  (* THE SEGMENT CONTRACTS ARE VALID -- sealed, from their own VCs
     (PLAN-valid-blk-annot.md Phase 4). *)
  Lemma cdBody_valid : ValidCFGVerifierContract cdBody.
  Proof. solve_valid valid_cdBody. Qed.
  Lemma cdFinal_valid : ValidCFGVerifierContract cdFinal.
  Proof. solve_valid valid_cdFinal. Qed.

  (* The program IS the contracts' code at 0: containment is reflexivity
     once the projection is taken (fmap_instrs_of_list + strip_of_AST). *)
  Lemma cd_contain :
    instrs_of_list (bv.of_N 0) (cfg_instrs cdBody)
      ⊆ ai_instr <$> instrs_of_list (bv.of_N 0) (list_AST_AnnotInstr (cfg_instrs cdBody)).
  Proof.
    rewrite fmap_instrs_of_list.
    change (List.map ai_instr (list_AST_AnnotInstr (cfg_instrs cdBody)))
      with (strip (list_AST_AnnotInstr (cfg_instrs cdBody))).
    rewrite strip_of_AST. reflexivity.
  Qed.

  Lemma cd_fit :
    (bv.bin (@bv.of_N xlenbits 0) + 4 * N.of_nat (length (cfg_instrs cdBody))
       < bv.exp2 xlenbits)%N.
  Proof. change (bv.exp2 xlenbits) with 4294967296%N. cbn. lia. Qed.

  (* The invariant as a FAMILY indexed by trips-remaining -- the shape
     myWP2_loop_induction wants.  The counter value is existential; only its
     relation to n is fixed. *)
  Definition cdInvN (n : nat) : iProp Σ :=
    (∃ k : bv xlenbits, ⌜bv.bin k = (N.of_nat n + 1)%N⌝ ∗ cdInv k)%I.

  (* ===== THE BODY CONTRACT: one trip, n+1 -> n. =====
     Note there is no myWP2_loop_join here: the body is discharged with
     ExitCond := cdInvN n, so its conclusion IS myWP2_loop (cdInvN n). *)
  Lemma cd_step (n : nat) : cdInvN (S n) -∗ myWP2_loop (cdInvN n).
  Proof.
    iIntros "(%k & %Hk & Hres0)".
    iDestruct "Hres0" as "(Hres & Hpc & Hnpc & Hinstrs)".
    assert (Hef : Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx cdCtx)
                    (SyncVal (bv.of_N 0)) (cfg_exit cdBody) (ik k)).
    { eexists. split; reflexivity. }
    assert (Hk2 : bv.bin k = (N.of_nat n + 2)%N) by lia.
    assert (Hdec : bv.bin (bvdec k) = (N.of_nat n + 1)%N) by (apply bvdec_bin; exact Hk2).
    assert (Hne : bvdec k <> bv.zero).
    { intros HH. rewrite HH in Hdec. cbn in Hdec. lia. }
    iApply (contract_run cdBody cdBody_valid (ik k) (bv.of_N 0)
              (ai_instr <$> instrs_of_list (bv.of_N 0) (list_AST_AnnotInstr (cfg_instrs cdBody))) _ (cdInvN n) eq_refl cd_fit cd_contain Hef
              $! (SyncVal (bv.of_N 0)) with "[Hres Hpc Hnpc Hinstrs]").
    - unfold cdInvAsn. iEval (cbn) in "Hres". cbn. iFrame.
      iDestruct "Hres" as "(H1 & Hpriv & Hinv)".
      iSplitL; [| done].  (* trailing ⌜secLeak (SyncVal _)⌝, no longer framed away *)
      iSplitR "Hpriv Hinv"; [| iFrame].
      iSplitR; [iSplit; [iPureIntro; repeat split; reflexivity | done]|].
      iSplitL "H1"; [iExact "H1"|].
      iSplitR; [iSplit; [done|done]|].
      iSplit; [|done]. iPureIntro.
      change ((k + minus1)%bv) with (bvdec k). split; exact Hne.
    - iIntros (an) "(%Hex & Hpc & Hnpc & Hinstrs & Hpost)".
      destruct Hex as (av & -> & Hex).
      apply Katamaran.RiscvPmp.CFGVer.VerifierRel.exit_hit_spec in Hex.
      injection Hex as <- _.
      iExists (bvdec k). iSplitR; [iPureIntro; exact Hdec|].
      unfold cdInv, cdInvAsn. iEval (cbn) in "Hpost". cbn.
      iDestruct "Hpost" as "(H1 & _ & Hpriv & Hinv)".
      iFrame "Hpc Hnpc Hinstrs Hpriv Hinv". iExact "H1".
  Qed.

  (* ===== THE EXIT CONTRACT: the guard fails, leave the loop. ===== *)
  Lemma cd_exit : cdInvN 0 -∗ myWP2_loop cdExit.
  Proof.
    iIntros "(%k & %Hk & Hres0)".
    iDestruct "Hres0" as "(Hres & Hpc & Hnpc & Hinstrs)".
    assert (Hef : Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx cdCtx)
                    (SyncVal (bv.of_N 8)) (cfg_exit cdFinal) (ik k)).
    { eexists. split; reflexivity. }
    iApply (contract_run cdFinal cdFinal_valid (ik k) (bv.of_N 0)
              (ai_instr <$> instrs_of_list (bv.of_N 0) (list_AST_AnnotInstr (cfg_instrs cdBody))) _ cdExit eq_refl cd_fit cd_contain Hef
              $! (SyncVal (bv.of_N 0)) with "[Hres Hpc Hnpc Hinstrs]").
    - unfold cdInvAsn. iEval (cbn) in "Hres". cbn. iFrame.
      iDestruct "Hres" as "(H1 & Hpriv & Hinv)".
      iSplitL; [| done].  (* trailing ⌜secLeak (SyncVal _)⌝, no longer framed away *)
      iSplitR "Hpriv Hinv"; [| iFrame].
      iSplitR; [iSplit; [iPureIntro; repeat split; reflexivity | done]|].
      iSplitL "H1"; [iExact "H1"|].
      iSplitR; [iSplit; [done|done]|].
      iSplit; [|done]. iPureIntro.
      change ((k + minus1)%bv) with (bvdec k). cbn in Hk. split; apply bvdec_one; exact Hk.
    - iIntros (an) "(%Hex & Hpc & Hnpc & Hinstrs & _)".
      destruct Hex as (av & -> & Hex).
      unfold cdExit. iExists av. iFrame "Hpc". iPureIntro.
      cbn in Hex. apply andb_prop in Hex as [Hex _].
      unfold atPc. rewrite Hex. exact I.
  Qed.

  (* ===== THE LOOP CONTRACT, for free from the two above. ===== *)
  Lemma cd_loop (n : nat) : cdInvN n -∗ myWP2_loop cdExit.
  Proof. apply (myWP2_loop_induction cdInvN cdExit cd_step cd_exit). Qed.

  (* Concrete anchor: the original countdown program starts X1 at 2. *)
  Corollary cd_loop_from_2 : cdInv (bv.of_N 2) -∗ myWP2_loop cdExit.
  Proof.
    iIntros "H". iApply (cd_loop 1). iExists (bv.of_N 2).
    iSplitR; [iPureIntro; repeat split; reflexivity|]. iExact "H".
  Qed.

End ComposeLoop.
