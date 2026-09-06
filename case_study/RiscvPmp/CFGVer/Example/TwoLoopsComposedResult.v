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
(* Example/TwoLoopsComposedResult.v — TWO-LOOP composition (heavy half).    *)
(*                                                                           *)
(* Two nested inductions, joined:                                            *)
(*   loopB n : bin m = n+1 -> invB m -* myWP2_loop tExit                     *)
(*   loopA n : bin k = n+1 -> bin m = nB+1                                   *)
(*             -> invA k * <X2 framed> -* myWP2_loop tExit                   *)
(*                                                                           *)
(* loopA's BASE case is the hand-off: A's exit contract lands at pc 8, and   *)
(* loopB takes over there, receiving X2 from the frame and minimal_pre from  *)
(* A's postcondition.  A's final X1 value is simply dropped (iProp is        *)
(* affine).                                                                  *)
(*                                                                           *)
(* Neither loop's trip count ever reaches the symbolic executor.             *)
(*                                                                           *)
(* See plans/PLAN-loop-invariant.md U11.                                     *)
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
     RiscvPmp.CFGVer.Example.TwoLoopsComposed.
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

Section TwoLoops.
  Context {Σ} {GS : sailGS2 Σ}.

  Definition tminus1 : Val ty_xlenbits := bv.of_N 4294967295.
  Definition tdecv (k : bv xlenbits) : bv xlenbits := bv.add k tminus1.

  Lemma tbin_minus1 : bv.bin tminus1 = 4294967295%N.
  Proof. reflexivity. Qed.

  Lemma tdec_one (k : bv xlenbits) : bv.bin k = 1%N -> tdecv k = bv.zero.
  Proof.
    intros Hk. unfold tdecv. apply bv.bin_inj.
    rewrite bv.bin_add. rewrite Hk. rewrite tbin_minus1. reflexivity.
  Qed.

  Lemma tdec_bin (k : bv xlenbits) (m : nat) :
    bv.bin k = (N.of_nat m + 2)%N -> bv.bin (tdecv k) = (N.of_nat m + 1)%N.
  Proof.
    intros Hk. unfold tdecv. rewrite bv.bin_add. rewrite Hk. rewrite tbin_minus1.
    pose proof (bv.bv_is_wf k) as Hb. rewrite Hk in Hb.
    change (bv.exp2 xlenbits) with 4294967296%N in Hb |- *.
    replace (N.of_nat m + 2 + 4294967295)%N
       with ((N.of_nat m + 1) + 1 * 4294967296)%N by lia.
    rewrite N.Div0.mod_add. apply N.mod_small. lia.
  Qed.

  Definition iA (k : bv xlenbits) : Valuation tCtxA :=
    [env].["k"∷ty_xlenbits ↦ SyncVal k].
  Definition iB (m : bv xlenbits) : Valuation tCtxB :=
    [env].["m"∷ty_xlenbits ↦ SyncVal m].

  Definition tExit : iProp Σ :=
    (∃ v, pc ↦ᵣ SyncVal v ∗ ⌜pcOutOfInstrs_exitCond 0 t_instrs v⌝)%I.

  Definition tOwn : iProp Σ :=
    Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs
      (ai_instr <$> instrs_of_list (bv.of_N 0) (cfg_instrs tAbody)).

  (* loop A's invariant: at head 0, counter k.  Does NOT mention X2. *)
  Definition invA (k : bv xlenbits) : iProp Σ :=
    (asn.interpret tInvA (iA k) ∗ pc ↦ᵣ SyncVal (bv.of_N 0)
     ∗ (∃ v, nextpc ↦ᵣ v) ∗ tOwn)%I.

  (* loop B's invariant: at head 8, counter m. *)
  Definition invB (m : bv xlenbits) : iProp Σ :=
    (asn.interpret tInvB (iB m) ∗ pc ↦ᵣ SyncVal (bv.of_N 8)
     ∗ (∃ v, nextpc ↦ᵣ v) ∗ tOwn)%I.

  Lemma loopB (n : nat) : forall (m : bv xlenbits),
    bv.bin m = (N.of_nat n + 1)%N -> invB m -∗ myWP2_loop tExit.
  Proof.
    induction n as [|q IH]; intros m Hm.
    - (* B's last trip -> the program exit *)
      pose proof valid_tBfinal as Hv.
      unfold ValidCFGVerifierContract, Valid_CFG_VC, CFG_VC_triple in Hv.
      cbn [cfg_map tBfinal] in Hv.
      assert (Hif : Katamaran.RiscvPmp.CFGVer.VerifierRel.itable_rel (w := wlctx tCtxB)
                      (instrs_of_list (bv.of_N 0) (cfg_instrs tAbody))
                      (table_of_list (term_val ty_xlenbits (bv.of_N 0)) 0 t_instrs) (iB m)).
      { apply itable_faith_of_list; [reflexivity|].
        apply table_bound_of_lenAddr. unfold lenAddr. cbn. lia. }
      assert (Hef : Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx tCtxB)
                      (pcOutOfInstrs_exitCond 0 t_instrs)
                      (exits_of_offs (term_val ty_xlenbits (bv.of_N 0)) [16%N]) (iB m)).
      { constructor; [|constructor]. eexists. split; reflexivity. }
      iIntros "(Hres & Hpc & Hnpc & Hinstrs)".
      iApply (sound_scfg_verification_condition_myWP2 Hv tExit Hif Hef
                $! (SyncVal (bv.of_N 8)) with "[Hres Hpc Hnpc Hinstrs]").
      + unfold tInvB. iEval (cbn) in "Hres". cbn. iFrame.
        iDestruct "Hres" as "(H1 & Hpriv & Hinv)".
        iSplitR "Hpriv Hinv"; [| iFrame].
        iSplitR; [iSplit; [iPureIntro; reflexivity | done]|].
        iSplitL "H1"; [iExact "H1"|].
        iSplitR; [iSplit; [done|done]|].
        iSplit; [|done]. iPureIntro.
        change ((m + bv.of_N 4294967295)%bv) with (tdecv m).
        apply tdec_one. cbn in Hm. exact Hm.
      + iIntros (an) "(%Hex & Hpc & Hnpc & Hinstrs & _)".
        destruct an as [av|a1 a2]; [|contradiction].
        unfold tExit. iExists av. iFrame "Hpc". iPureIntro. rewrite Hex. exact I.
    - (* one trip of B *)
      pose proof valid_tBbody as Hv.
      unfold ValidCFGVerifierContract, Valid_CFG_VC, CFG_VC_triple in Hv.
      cbn [cfg_map tBbody] in Hv.
      assert (Hif : Katamaran.RiscvPmp.CFGVer.VerifierRel.itable_rel (w := wlctx tCtxB)
                      (instrs_of_list (bv.of_N 0) (cfg_instrs tAbody))
                      (table_of_list (term_val ty_xlenbits (bv.of_N 0)) 0 t_instrs) (iB m)).
      { apply itable_faith_of_list; [reflexivity|].
        apply table_bound_of_lenAddr. unfold lenAddr. cbn. lia. }
      assert (Hef : Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx tCtxB)
                      at8 (exits_of_offs (term_val ty_xlenbits (bv.of_N 0)) [8%N]) (iB m)).
      { constructor; [|constructor]. eexists. split; reflexivity. }
      assert (Hm2 : bv.bin m = (N.of_nat q + 2)%N) by lia.
      assert (Hd : bv.bin (tdecv m) = (N.of_nat q + 1)%N) by (apply tdec_bin; exact Hm2).
      assert (Hne : tdecv m <> bv.zero).
      { intros HH. rewrite HH in Hd. cbn in Hd. lia. }
      iIntros "(Hres & Hpc & Hnpc & Hinstrs)".
      iApply myWP2_loop_join.
      iApply (sound_scfg_verification_condition_myWP2 Hv (myWP2_loop tExit) Hif Hef
                $! (SyncVal (bv.of_N 8)) with "[Hres Hpc Hnpc Hinstrs]").
      + unfold tInvB. iEval (cbn) in "Hres". cbn. iFrame.
        iDestruct "Hres" as "(H1 & Hpriv & Hinv)".
        iSplitR "Hpriv Hinv"; [| iFrame].
        iSplitR; [iSplit; [iPureIntro; reflexivity | done]|].
        iSplitL "H1"; [iExact "H1"|].
        iSplitR; [iSplit; [done|done]|].
        iSplit; [|done]. iPureIntro.
        change ((m + bv.of_N 4294967295)%bv) with (tdecv m). exact Hne.
      + iIntros (an) "(%Hex & Hpc & Hnpc & Hinstrs & Hpost)".
        destruct an as [av|a1 a2]; [|contradiction].
        cbn in Hex. unfold at8 in Hex.
        assert (Hav : av = bv.of_N 8) by (destruct (bv.eqb_spec av (bv.of_N 8)); congruence).
        subst av.
        iApply (IH (tdecv m) Hd).
        unfold invB, tInvB. iEval (cbn) in "Hpost". cbn.
        iDestruct "Hpost" as "(H1 & _ & Hpriv & Hinv)".
        iFrame "Hpc Hnpc Hinstrs Hpriv Hinv". iExact "H1".
  Qed.


  (* X2 is carried through the WHOLE of loop A as a frame -- it is never fed
     to loop A's VCs, so no step of loop A pays for it. *)
  Lemma loopA (nA : nat) : forall (k : bv xlenbits) (nB : nat) (m : bv xlenbits),
    bv.bin k = (N.of_nat nA + 1)%N -> bv.bin m = (N.of_nat nB + 1)%N ->
    invA k ∗ asn.interpret tX2 (iB m) -∗ myWP2_loop tExit.
  Proof.
    induction nA as [|p IH]; intros k nB m Hk Hm.
    - (* A's LAST trip: falls through to 8, which is loop B's head.  This is
         the HAND-OFF between the two loops. *)
      pose proof valid_tAfinal as Hv.
      unfold ValidCFGVerifierContract, Valid_CFG_VC, CFG_VC_triple in Hv.
      cbn [cfg_map tAfinal] in Hv.
      assert (Hif : Katamaran.RiscvPmp.CFGVer.VerifierRel.itable_rel (w := wlctx tCtxA)
                      (instrs_of_list (bv.of_N 0) (cfg_instrs tAbody))
                      (table_of_list (term_val ty_xlenbits (bv.of_N 0)) 0 t_instrs) (iA k)).
      { apply itable_faith_of_list; [reflexivity|].
        apply table_bound_of_lenAddr. unfold lenAddr. cbn. lia. }
      assert (Hef : Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx tCtxA)
                      at8 (exits_of_offs (term_val ty_xlenbits (bv.of_N 0)) [8%N]) (iA k)).
      { constructor; [|constructor]. eexists. split; reflexivity. }
      iIntros "((Hres & Hpc & Hnpc & Hinstrs) & HX2)".
      iApply myWP2_loop_join.
      iApply (sound_scfg_verification_condition_myWP2 Hv (myWP2_loop tExit) Hif Hef
                $! (SyncVal (bv.of_N 0)) with "[Hres Hpc Hnpc Hinstrs]").
      + unfold tInvA. iEval (cbn) in "Hres". cbn. iFrame.
        iDestruct "Hres" as "(H1 & Hpriv & Hinv)".
        iSplitR "Hpriv Hinv"; [| iFrame].
        iSplitR; [iSplit; [iPureIntro; reflexivity | done]|].
        iSplitL "H1"; [iExact "H1"|].
        iSplitR; [iSplit; [done|done]|].
        iSplit; [|done]. iPureIntro.
        change ((k + bv.of_N 4294967295)%bv) with (tdecv k).
        apply tdec_one. cbn in Hk. exact Hk.
      + iIntros (an) "(%Hex & Hpc & Hnpc & Hinstrs & Hpost)".
        destruct an as [av|a1 a2]; [|contradiction].
        cbn in Hex. unfold at8 in Hex.
        assert (Hav : av = bv.of_N 8) by (destruct (bv.eqb_spec av (bv.of_N 8)); congruence).
        subst av.
        (* loop B takes over.  X2 arrives from the FRAME -- it was never fed to
           any of loop A's VCs.  X1's final value is simply dropped (affine). *)
        iApply (loopB nB m Hm).
        unfold invB, tInvB. iEval (cbn) in "Hpost". cbn.
        iDestruct "Hpost" as "(_ & Hpriv & Hinv)".
        unfold tX2 in *. iEval (cbn) in "HX2".
        iFrame "Hpc Hnpc Hinstrs Hpriv Hinv". iExact "HX2".
    - (* one trip of A; X2 is carried along untouched *)
      pose proof valid_tAbody as Hv.
      unfold ValidCFGVerifierContract, Valid_CFG_VC, CFG_VC_triple in Hv.
      cbn [cfg_map tAbody] in Hv.
      assert (Hif : Katamaran.RiscvPmp.CFGVer.VerifierRel.itable_rel (w := wlctx tCtxA)
                      (instrs_of_list (bv.of_N 0) (cfg_instrs tAbody))
                      (table_of_list (term_val ty_xlenbits (bv.of_N 0)) 0 t_instrs) (iA k)).
      { apply itable_faith_of_list; [reflexivity|].
        apply table_bound_of_lenAddr. unfold lenAddr. cbn. lia. }
      assert (Hef : Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx tCtxA)
                      at0 (exits_of_offs (term_val ty_xlenbits (bv.of_N 0)) [0%N]) (iA k)).
      { constructor; [|constructor]. eexists. split; reflexivity. }
      assert (Hk2 : bv.bin k = (N.of_nat p + 2)%N) by lia.
      assert (Hd : bv.bin (tdecv k) = (N.of_nat p + 1)%N) by (apply tdec_bin; exact Hk2).
      assert (Hne : tdecv k <> bv.zero).
      { intros HH. rewrite HH in Hd. cbn in Hd. lia. }
      iIntros "((Hres & Hpc & Hnpc & Hinstrs) & HX2)".
      iApply myWP2_loop_join.
      iApply (sound_scfg_verification_condition_myWP2 Hv (myWP2_loop tExit) Hif Hef
                $! (SyncVal (bv.of_N 0)) with "[Hres Hpc Hnpc Hinstrs]").
      + unfold tInvA. iEval (cbn) in "Hres". cbn. iFrame.
        iDestruct "Hres" as "(H1 & Hpriv & Hinv)".
        iSplitR "Hpriv Hinv"; [| iFrame].
        iSplitR; [iSplit; [iPureIntro; reflexivity | done]|].
        iSplitL "H1"; [iExact "H1"|].
        iSplitR; [iSplit; [done|done]|].
        iSplit; [|done]. iPureIntro.
        change ((k + bv.of_N 4294967295)%bv) with (tdecv k). exact Hne.
      + iIntros (an) "(%Hex & Hpc & Hnpc & Hinstrs & Hpost)".
        destruct an as [av|a1 a2]; [|contradiction].
        cbn in Hex. unfold at0 in Hex.
        assert (Hav : av = bv.of_N 0) by (destruct (bv.eqb_spec av (bv.of_N 0)); congruence).
        subst av.
        iApply (IH (tdecv k) nB m Hd Hm).
        unfold invA, tInvA. iEval (cbn) in "Hpost". cbn.
        iDestruct "Hpost" as "(H1 & _ & Hpriv & Hinv)".
        iFrame "Hpc Hnpc Hinstrs Hpriv Hinv HX2". iExact "H1".
  Qed.

  (* Concrete anchor: 2 trips of loop A, then 3 trips of loop B. *)
  Corollary two_loops_2_3 :
    invA (bv.of_N 2) ∗ asn.interpret tX2 (iB (bv.of_N 3)) -∗ myWP2_loop tExit.
  Proof. apply (loopA 1 (bv.of_N 2) 2 (bv.of_N 3)); reflexivity. Qed.


End TwoLoops.
