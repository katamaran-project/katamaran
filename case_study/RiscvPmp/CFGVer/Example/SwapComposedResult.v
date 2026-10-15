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
(* Example/SwapComposedResult.v — CONTRACT COMPOSITION demonstrator          *)
(* (heavy half).                                                             *)
(*                                                                           *)
(* `swap_composed` proves ONE myWP2_loop fact about the whole three-         *)
(* instruction program, using nothing about the program except the two       *)
(* separately-discharged segment contracts valid_swapA / valid_swapB.        *)
(* Neither segment's VC ever sees the other's steps.                          *)
(*                                                                           *)
(* Shape of the argument:                                                     *)
(*   myWP2_loop_join  collapses the nested loop that arises from discharging  *)
(*                    segment A with ExitCond := myWP2_loop <real exit>;      *)
(*   bridge(A)        runs 0 -> 4 and RETURNS A's exit assertion;             *)
(*   bridge(B)        runs 4 -> 12 from that assertion.                        *)
(*                                                                            *)
(* See plans/PLAN-loop-invariant.md U1-U8.                                     *)
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
     RiscvPmp.CFGVer.Example.SwapComposed.
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

Section Compose.
  Context {Σ} {GS : sailGS2 Σ}.

  Definition swapExit : iProp Σ :=
    (∃ v, pc ↦ᵣ SyncVal v ∗ ⌜atPc 12 v⌝)%I.

  Lemma swap_composed (ι : Valuation swapCtx) :
    ⊢ asn.interpret (extend_to_minimal_pre (cfg_precondition swapA))
          ι.["a"∷ty_xlenbits ↦ SyncVal (bv.of_N 0)]
      ∗ pc ↦ᵣ SyncVal (bv.of_N 0) ∗ (∃ v, nextpc ↦ᵣ v)
      ∗ ptsto_instrs
          (ai_instr <$> instrs_of_list (bv.of_N 0) (list_AST_AnnotInstr (cfg_instrs swapA)))
      -∗ myWP2_loop swapExit.
  Proof.
    (* Both segments run over the whole program at 0: containment is
       reflexivity after the projection (PLAN-valid-blk-annot.md Phase 4). *)
    assert (Hin : instrs_of_list (bv.of_N 0) (cfg_instrs swapA)
                    ⊆ ai_instr <$> instrs_of_list (bv.of_N 0) (list_AST_AnnotInstr (cfg_instrs swapA))).
    { rewrite fmap_instrs_of_list.
      change (List.map ai_instr (list_AST_AnnotInstr (cfg_instrs swapA)))
        with (strip (list_AST_AnnotInstr (cfg_instrs swapA))).
      rewrite strip_of_AST. reflexivity. }
    assert (Hfit : (bv.bin (@bv.of_N xlenbits 0) + 4 * N.of_nat (length (cfg_instrs swapA))
                      < bv.exp2 xlenbits)%N).
    { change (bv.exp2 xlenbits) with 4294967296%N. cbn. lia. }
    assert (HcA : ValidCFGVerifierContract swapA) by solve_valid valid_swapA.
    assert (HcB : ValidCFGVerifierContract swapB) by solve_valid valid_swapB.
    assert (HefA : etable_rel (w := wlctx swapCtx)
                     (SyncVal (bv.of_N 4)) (cfg_exit swapA) ι).
    { eexists. split; reflexivity. }
    assert (HefB : etable_rel (w := wlctx swapCtx)
                     (SyncVal (bv.of_N 12)) (cfg_exit swapB) ι).
    { eexists. split; reflexivity. }
    iIntros "(Hpre & Hpc & Hnpc & Hinstrs)".
    (* ONE nested loop, collapsed by the bind lemma's corollary. *)
    iApply myWP2_loop_join.
    (* --- SEGMENT A, discharged with ExitCond := "keep running until the
           real exit".  This is what produces the nested loop. --- *)
    iApply (contract_run swapA HcA ι (bv.of_N 0) (ai_instr <$> instrs_of_list (bv.of_N 0) (list_AST_AnnotInstr (cfg_instrs swapA))) _ (myWP2_loop swapExit)
              eq_refl Hfit Hin HefA
              $! (SyncVal (bv.of_N 0)) with "[Hpre Hpc Hnpc Hinstrs]").
    - cbn [cfg_precondition cfg_instrs swapA] in *. iFrame.
    - (* --- THE CUT.  `Hpost` is segment A's exit assertion, delivered by the
             re-threaded bridge conjunct; it is the whole reason this works. --- *)
      iIntros (an) "(%HexitA & Hpc & Hnpc & Hinstrs & Hpost)".
      destruct an as [av|a1 a2]; [|contradiction].
      apply exit_hit_spec in HexitA.
      injection HexitA as <-.
      (* --- SEGMENT B, entered at the cut address with A's exit assertion. --- *)
      iApply (contract_run swapB HcB ι (bv.of_N 0) (ai_instr <$> instrs_of_list (bv.of_N 0) (list_AST_AnnotInstr (cfg_instrs swapA))) _ swapExit
                eq_refl Hfit Hin HefB
                $! (SyncVal (bv.of_N 4)) with "[Hpc Hnpc Hinstrs Hpost]").
      + iEval (cbn) in "Hpost". cbn. iFrame.
        iDestruct "Hpost" as "(H1 & H2 & H3 & Hpriv & Hinv)".
        iSplitR "Hpriv Hinv"; [| iFrame].
        (* A's post is interpreted at ι.["a"↦0].["an"↦4] and B's pre at
           ι.["a"↦4].  Those are CONVERTIBLE but not syntactically equal, so
           iFrame (syntactic) cannot place them and iExact (conversion) can. *)
        iSplitR; [iSplit; [iPureIntro; reflexivity | done]|].
        iSplitL "H1"; [iExact "H1"|].
        iSplitL "H2"; [iExact "H2"| iExact "H3"].
      + iIntros (an2) "(%HexitB & Hpc & Hnpc & Hinstrs & _)".
        destruct an2 as [bv2|b1 b2]; [|contradiction].
        unfold swapExit. iExists bv2. iFrame "Hpc". iPureIntro.
        cbn in HexitB. unfold atPc. rewrite HexitB. exact I.
  Qed.

End Compose.
