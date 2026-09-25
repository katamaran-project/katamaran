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
(* Example/CountdownRecResult.v -- a LOOP and a SEGMENT, combined.  HEAVY.   *)
(*                                                                           *)
(* cdRec_blockSound: the countdown loop earns blockSound from ONE VC         *)
(* (valid_cd_rec) and the block door blockSound_of_contract, whose Löb       *)
(* induction lets the loop's own head be annotated with it.                  *)
(*                                                                           *)
(* countdown_rec_noninterferent_param: the whole program -- loop block, then the   *)
(* executed tail -- end to end, via cfg_instrs_endToEnd.                     *)
(*                                                                           *)
(* For EVERY load address init_addr with init_addr + 12 < lenAddr: the     *)
(* contracts, the block and the annotated code are all functions of it      *)
(* (CountdownRec.v), so the block is justified wherever the code sits.      *)
(*                                                                           *)
(* One choice in the statement, forced:                                      *)
(*  - X1 PINNED to 2: the loop needs k <> 0, and noninterferent_strong's     *)
(*    reg_specs can pin a register or leave it free but cannot constrain     *)
(*    it.  2 is the original countdown's start value (CountdownResult.v).    *)
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
     RiscvPmp.CFGVer.Example.CountdownRec.
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

Section Link.
  Context {Σ} {GS : sailGS2 Σ}.

  (* THE LOOP, AS A BLOCK.  One VC, one generic Löb lemma. *)
  Lemma cdRec_blockSound (ia : N) (Hfit : (ia + 8 < lenAddr)%N)
      (words : bv xlenbits -> bv word) :
    ⊢ blockSound words (@bv.of_N xlenbits ia) (cdRecBlk ia).
  Proof.
    (* where the code sits: base ia, two instructions, inside memory *)
    iPoseProof (blockFaithful_of_seg (term_var "q") (term_var "q") ia
                  cd_instrs 8 4 [] cd_rec_inv cd_rec_post
                  (@bv.of_N xlenbits ia) (cd_rec_annot ia)) as "Hf".
    { intros iota. reflexivity. }
    { pose proof lenAddr_rep.
      rewrite (seg_fits_bin ia 8 ltac:(unfold seg_fits_memory; lia)).
      cbn [length cd_rec_annot list_AST_AnnotInstr List.map]. lia. }
    iApply (blockSound_of_contract words (@bv.of_N xlenbits ia) (cdRecBlk ia)
              (cd_rec_annot ia) (valid_cd_rec ia) with "Hf").
    (* No "the block resumes where its contract exits" bullet any more: a
       block resumes AT its contract's exit by construction
       (PLAN-exit-targets.md). *)
    - (* the annotated code IS the contract's code *)
      reflexivity.
    - (* no ai_block in the loop's own code: nothing may fire at its entry *)
      apply blocksSoundAt_of_none. repeat constructor.
    - (* the loop's own program: its head re-enters the block, nothing else *)
      iIntros "#Hb". unfold cd_rec_annot.
      iApply (blocksSound_of_head with "Hb").
      + reflexivity.
      + repeat constructor.
  Qed.

  (* THE LINK: the only block cdLink's VC trusted is sound. *)
  Lemma cd_link_blocksSound (ia : N) (Hfit : (ia + 8 < lenAddr)%N)
      (words : bv xlenbits -> bv word) :
    ⊢ blocksSound words (instrs_of_list (@bv.of_N xlenbits ia) (cd_link_annot ia)).
  Proof.
    iPoseProof (cdRec_blockSound ia Hfit words) as "#Hb".
    unfold cd_link_annot.
    iApply (blocksSound_of_head with "Hb").
    - reflexivity.
    - repeat constructor.
  Qed.
End Link.

(* THE END THEOREM, for every load address the program fits at.  The block
   obligation is cd_link_blocksSound above; the rest is cfg_instrs_endToEnd's
   ordinary wiring. *)
Lemma countdown_rec_noninterferent_param (init_addr : N) :
  (init_addr + 12 < lenAddr)%N ->
  noninterferent_strong init_addr cd_link_instrs (init_addr + 12)%N
    [(X1, true, Some (bv.of_N 2)); (X2, false, None)] [].
Proof.
  intros Hfit γ1 γ2 μ1 μ2 ws Hmem1 Hmem2 HpubReg HpubMem
    HInitReg1 HInitReg2 HInitMem1 HInitMem2
    γ1curpriv γ2curpriv γ1pc γ2pc Htrace n γ1' μ1' steps1.
  assert (Hfit8 : (init_addr + 8 < lenAddr)%N) by lia.
  pose proof (seg_fits_bin init_addr 8 ltac:(unfold seg_fits_memory; lia)) as Hbin.
  (* ι: code at init_addr, counter at its pinned 2. *)
  eapply (@cfg_instrs_endToEnd γ1 γ2 γ1' μ1 μ2 μ1' (cd_link_annot init_addr)
    (init_addr + 12)%N n ws cdRecCtx
    ([env].["q"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)]
          .["k"∷ty_xlenbits ↦ SyncVal (bv.of_N 2)])
    _ HpubReg (cdLink init_addr) (valid_cd_link init_addr) init_addr
    eq_refl).
  - (* placement: the bare code base *)
    reflexivity.
  - (* the one exit, +12: the generic segment exit table *)
    apply (seg_exit_table_ok _ _ init_addr 12). reflexivity.
  - (* ImplPre: the pinned X1 and the free X2 from gen_implpre, the rest pure *)
    intros Σ' GS'.
    iIntros "(Hregs & Hpriv & #Hinv)".
    iPoseProof (gen_implpre [(X1, true, Some (bv.of_N 2)); (X2, false, None)]
                  _ HpubReg ltac:(apply Prelude.nodup_fixed; reflexivity)
                  HInitReg1 HInitReg2 with "Hregs") as "Hpre".
    cbn -[bv.of_N].
    iDestruct "Hpre" as "(HX1 & HX2 & _)".
    iFrame "Hpriv Hinv HX1 HX2".
    repeat iSplit; try done; iPureIntro.
    all: first [ reflexivity
               | (try unfold bv.unsigned; rewrite Hbin; lia)
               | (intros H; apply (f_equal (@bv.bin _)) in H; discriminate) ].
  - cbn [length cd_link_annot list_AST_AnnotInstr List.map]. lia.
  - intros Σ' GS' wds. apply (cd_link_blocksSound init_addr Hfit8).
  - exact Hmem1.
  - exact Hmem2.
  - exact γ1curpriv.
  - exact γ2curpriv.
  - exact γ1pc.
  - exact γ2pc.
  - exact steps1.
  - exact Htrace.
Qed.
