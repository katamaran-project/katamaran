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
(* Example/PaddedLoopResult.v -- a loop block inside a longer program (HEAVY) *)
(*                                                                           *)
(* padded_loop_noninterferent_param: the 66-instruction program of           *)
(* PaddedLoop.v -- 64 executed filler no-ops, then the countdown loop as ONE  *)
(* block (cdRecBlk, valid at every address: CountdownRecResult) -- end to    *)
(* end, via cfg_instrs_endToEnd, for every load address it fits at.  As in    *)
(* CountdownRecResult, X1 is PINNED to 2 (the loop needs k <> 0).            *)
(*                                                                           *)
(* Replaced 2026-10-01 the hand-written Iris composition (pl_step / pl_exit / *)
(* myWP2_loop_induction over two segment contracts), whose framing of the     *)
(* whole instruction map peaked at ~9.4 GB.                                    *)
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
     RiscvPmp.CFGVer.GenSegment
     RiscvPmp.CFGVer.Adequacy
     RiscvPmp.CFGVer.GenCompose
     RiscvPmp.CFGVer.EndToEnd
     RiscvPmp.CFGVer.Example.CountdownComposed
     RiscvPmp.CFGVer.Example.CountdownRec
     RiscvPmp.CFGVer.Example.CountdownRecResult
     RiscvPmp.CFGVer.Example.PaddedLoop.
From iris.base_logic Require Import lib.gen_heap lib.iprop invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac big_op.
From iris.program_logic Require weakestpre adequacy.
From iris.proofmode Require string_ident tactics.
From stdpp Require namespaces.
From Equations Require Import Equations.

Import RiscvPmpProgram.

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


(* THE ANNOTATIONS, TYPED: the filler plain, the loop head carrying cdRecBlk
   with its validity.  Its erasure is padded_annot by conversion. *)
Definition padded_annotV : list (AnnotInstrV blkValid) :=
  List.map AST_AnnotInstrV pl_filler
  ++ (MkAnnotInstrV [] (ADDI X1 X1 neg1_12) [] (Some (MkBlkAnnotV cdRecBlk cdRecBlk_valid)) false
      :: List.map AST_AnnotInstrV [BNE X1 X0 back4]).

Lemma plLink_valid : ValidCFGVerifierContract plLink.
Proof.
  apply (@ValidCFGVerifierContract_intro _ plLink padded_annotV);
    [exact valid_plLink | reflexivity | repeat constructor].
Qed.

Lemma padded_loop_noninterferent_param (init_addr : N) :
  fits (init_addr + 4 * N.of_nat (length padded_instrs)) [] ->
  noninterferent_strong init_addr padded_instrs (init_addr + 4 * N.of_nat (length padded_instrs))
    [(X1, Known (bv.of_N 2)); (X4, Secret)] (compile (init_addr + 4 * N.of_nat (length padded_instrs)) []).
Proof.
  intros Hfit0.
  assert (Hl : length padded_instrs = 66%nat) by reflexivity.
  assert (Hfit : (init_addr + 264 < lenAddr)%N)
    by (apply fits_nil in Hfit0; rewrite Hl in Hfit0; exact Hfit0).
  apply (ni_of_cells (regs' := [(X1, Known (bv.of_N 2)); (X4, Secret)]) (cs := []));
    [apply compile_clear; lia | apply compile_in_range; [lia | assumption] | reflexivity | reflexivity |].
  rewrite Hl. change (4 * N.of_nat 66)%N with 264%N.
  intros γ1 γ2 μ1 μ2 ws Hmem1 Hmem2 HpubReg HpubMem
    HInitReg1 HInitReg2 HInitMem1 HInitMem2
    γ1curpriv γ2curpriv γ1pc γ2pc Htrace n γ1' μ1' steps1.
  pose proof (seg_fits_bin init_addr 264 ltac:(unfold seg_fits_memory; lia)) as Hbin.
  pose proof (seg_fits_bin (init_addr + pl_head) 8 ltac:(unfold seg_fits_memory, pl_head; lia)) as Hbin2.
  eapply (@cfg_instrs_endToEnd γ1 γ2 γ1' μ1 μ2 μ1' padded_instrs
    (init_addr + 264)%N n ws cdRecCtx
    ([env].["q"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)]
          .["k"∷ty_xlenbits ↦ SyncVal (bv.of_N 2)])
    _ HpubReg plLink plLink_valid eq_refl init_addr).
  - reflexivity.
  - apply (seg_exit_table_ok _ _ init_addr 264). reflexivity.
  - intros Σ' GS'.
    iIntros "(Hregs & Hpriv & #Hinv)".
    iPoseProof (gen_implpre [(X1, Known (bv.of_N 2)); (X4, Secret)]
                  _ HpubReg ltac:(apply Prelude.nodup_fixed; reflexivity)
                  HInitReg1 HInitReg2 with "Hregs") as "Hpre".
    cbn -[bv.of_N].
    iDestruct "Hpre" as "(HX1 & HX4 & _)".
    iFrame "Hpriv Hinv HX1 HX4".
    repeat iSplit; try done; iPureIntro.
    all: first [ reflexivity
               | (try unfold bv.unsigned; rewrite Hbin; lia)
               | (rewrite bv.of_N_add; unfold bv.unsigned; rewrite Hbin2; unfold pl_head; lia)
               | (intros H; apply (f_equal (@bv.bin _)) in H; discriminate) ].
  - unfold padded_instrs, pl_filler, cd_instrs. cbn [length List.app List.repeat]. lia.
  - exact Hmem1.
  - exact Hmem2.
  - exact γ1curpriv.
  - exact γ2curpriv.
  - exact γ1pc.
  - exact γ2pc.
  - exact steps1.
  - exact Htrace.
Qed.
