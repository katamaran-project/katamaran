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
(* countdown_rec_noninterferent: the whole program -- loop block, then the   *)
(* executed tail -- end to end, via cfg_instrs_endToEnd.                     *)
(*                                                                           *)
(* Two choices in the statement, both forced:                                *)
(*  - BASE 0, not a universal base: the loop block is justified at base 0    *)
(*    (cdRec_blockSound), so that is where the program is loaded.            *)
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
  Lemma cdRec_blockSound (words : bv xlenbits -> bv word) :
    ⊢ blockSound words (@bv.of_N xlenbits 0) cdRecBlk.
  Proof.
    (* where the code sits: base 0, two instructions, well inside memory *)
    iPoseProof (blockFaithful_of_seg (term_var "q") (term_var "q") 0 0
                  cd_instrs 0 2 [8%N] 8 4 [] cd_rec_inv cd_rec_post
                  8 (@bv.of_N xlenbits 0) cd_rec_annot) as "Hf".
    { intros iota. reflexivity. }
    { vm_compute. reflexivity. }
    { repeat constructor. lia. }
    { vm_compute. reflexivity. }
    iApply (blockSound_of_contract words (@bv.of_N xlenbits 0) cdRecBlk cd_rec_annot
              valid_cd_rec with "Hf").
    - (* the block resumes where its contract exits: +8 *)
      intros x Hx. apply seg_exitCond_inv1 in Hx. rewrite Hx.
      vm_compute. reflexivity.
    - (* the annotated code IS the contract's code *)
      reflexivity.
    - (* no ai_block in the loop's own code: nothing may fire at its entry *)
      apply blocksSoundAt_of_none. repeat constructor.
    - (* the loop's own program: its head re-enters the block, nothing else *)
      iIntros "#Hb". unfold cd_rec_annot.
      iApply (blocksSound_of_head with "Hb").
      + reflexivity.
      + repeat constructor.
      + apply (blk_span_sub (@bv.of_N xlenbits 0) cdRecBlk _ []). reflexivity.
  Qed.

  (* THE LINK: the only block cdLink's VC trusted is sound. *)
  Lemma cd_link_blocksSound (words : bv xlenbits -> bv word) :
    ⊢ blocksSound words (instrs_of_list (@bv.of_N xlenbits 0) cd_link_annot).
  Proof.
    iPoseProof (cdRec_blockSound words) as "#Hb".
    unfold cd_link_annot.
    iApply (blocksSound_of_head with "Hb").
    - reflexivity.
    - repeat constructor.
    - apply (blk_span_sub (@bv.of_N xlenbits 0) cdRecBlk _ [ADDI X2 X0 (bv.of_N 42)]).
      reflexivity.
  Qed.
End Link.

(* THE END THEOREM.  The block obligation is cd_link_blocksSound above; the
   rest is cfg_instrs_endToEnd's ordinary wiring. *)
Lemma countdown_rec_noninterferent :
  noninterferent_strong 0 cd_link_instrs (seg_exitCond 0 [12%N])
    [(X1, true, Some (bv.of_N 2)); (X2, false, None)] [].
Proof.
  intros γ1 γ2 μ1 μ2 ws Hmem1 Hmem2 HpubReg HpubMem
    HInitReg1 HInitReg2 HInitMem1 HInitMem2
    γ1curpriv γ2curpriv γ1pc γ2pc Htrace n γ1' μ1' steps1.
  (* ι: code at 0, counter at its pinned 2 *)
  eapply (@cfg_instrs_endToEnd γ1 γ2 γ1' μ1 μ2 μ1' cd_link_annot
    (seg_exitCond 0 [12%N]) n ws cdRecCtx
    ([env].["q"∷ty_xlenbits ↦ SyncVal (bv.of_N 0)]
          .["k"∷ty_xlenbits ↦ SyncVal (bv.of_N 2)])
    _ HpubReg cdLink valid_cd_link 0 eq_refl eq_refl).
  - (* placement *)
    reflexivity.
  - (* the one exit, +12 *)
    unfold cdLink, gen_seg_contract. cbn [cfg_exits].
    apply etable_faith_exits_of_offs with (cbase := bv.of_N 0);
      [reflexivity | constructor; [reflexivity | constructor]].
  - (* ImplPre: the pinned X1 and the free X2 from gen_implpre, the rest pure *)
    intros Σ' GS'.
    iIntros "(Hregs & Hpriv & #Hinv)".
    iPoseProof (gen_implpre [(X1, true, Some (bv.of_N 2)); (X2, false, None)]
                  _ HpubReg ltac:(apply Prelude.nodup_fixed; reflexivity)
                  HInitReg1 HInitReg2 with "Hregs") as "Hpre".
    cbn.
    iDestruct "Hpre" as "(HX1 & HX2 & _)".
    iFrame "Hpriv Hinv HX1 HX2".
    repeat iSplit; try done; iPureIntro.
    all: first [ reflexivity
               | (unfold lenAddr; lia)
               | (intros H; apply (f_equal (@bv.bin _)) in H; discriminate) ].
  - vm_compute. reflexivity.
  - intros Σ' GS' wds. apply cd_link_blocksSound.
  - exact Hmem1.
  - exact Hmem2.
  - exact γ1curpriv.
  - exact γ2curpriv.
  - exact γ1pc.
  - exact γ2pc.
  - exact steps1.
  - exact Htrace.
Qed.
