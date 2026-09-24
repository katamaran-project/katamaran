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

(* ------------------------------------------------------------------------ *)
(* Where the code sits: base arithmetic, for every ia that fits.            *)
(* ------------------------------------------------------------------------ *)

(* the placement is `q + 0` *)
Lemma cd_add0 (ia : N) : @bv.of_N xlenbits ia = bv.add (bv.of_N ia) (bv.of_N 0).
Proof. change (@bv.of_N xlenbits 0) with (@bv.zero xlenbits). now rewrite bv.add_zero_r. Qed.

(* ia is representable, so bv.of_N does not truncate it *)
Lemma cd_bin (ia : N) (Hfit : (ia + 8 < lenAddr)%N) :
  bv.bin (@bv.of_N xlenbits ia) = ia.
Proof.
  assert (Hf : seg_fits_memory ia 8) by (unfold seg_fits_memory; lia).
  exact (seg_fits_bin ia 8 Hf).
Qed.

(* the one exit of cdLink, at ia + 12 *)
Lemma cd_exit12 (ia : N) :
  seg_exitCond ia [12%N] (bv.add (bv.add (bv.of_N ia) (bv.of_N 0)) (bv.of_N (12 - 0))) = true.
Proof.
  rewrite !bv.of_N_add. cbn. rewrite N.add_0_r.
  match goal with |- context [bv.eqb ?a ?b] => destruct (bv.eqb_spec a b) as [_|Hn] end;
    [reflexivity | now contradiction Hn].
Qed.

Section Link.
  Context {Σ} {GS : sailGS2 Σ}.

  (* THE LOOP, AS A BLOCK.  One VC, one generic Löb lemma. *)
  Lemma cdRec_blockSound (ia : N) (Hfit : (ia + 8 < lenAddr)%N)
      (words : bv xlenbits -> bv word) :
    ⊢ blockSound words (@bv.of_N xlenbits ia) (cdRecBlk ia).
  Proof.
    (* where the code sits: base ia, two instructions, inside memory *)
    iPoseProof (blockFaithful_of_seg (term_var "q") (term_var "q") ia 0
                  cd_instrs 0 2 [8%N] 8 4 [] cd_rec_inv cd_rec_post
                  8 (@bv.of_N xlenbits ia) (cd_rec_annot ia)) as "Hf".
    { intros iota. reflexivity. }
    { apply cd_add0. }
    { repeat constructor. lia. }
    { pose proof lenAddr_rep. rewrite (cd_bin ia Hfit).
      cbn [length cd_rec_annot list_AST_AnnotInstr List.map]. lia. }
    iApply (blockSound_of_contract words (@bv.of_N xlenbits ia) (cdRecBlk ia)
              (cd_rec_annot ia) (valid_cd_rec ia) with "Hf").
    - (* the block resumes where its contract exits: ia + 8 *)
      intros x Hx. apply seg_exitCond_inv1 in Hx. rewrite Hx.
      apply seg_addr_add.
    - (* the annotated code IS the contract's code *)
      reflexivity.
    - (* no ai_block in the loop's own code: nothing may fire at its entry *)
      apply blocksSoundAt_of_none. repeat constructor.
    - (* the loop's own program: its head re-enters the block, nothing else *)
      iIntros "#Hb". unfold cd_rec_annot.
      iApply (blocksSound_of_head with "Hb").
      + reflexivity.
      + repeat constructor.
      + apply (blk_span_sub (@bv.of_N xlenbits ia) (cdRecBlk ia) _ []). reflexivity.
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
    - apply (blk_span_sub (@bv.of_N xlenbits ia) (cdRecBlk ia) _
               [ADDI X2 X0 (bv.of_N 42)]).
      reflexivity.
  Qed.
End Link.

(* THE END THEOREM, for every load address the program fits at.  The block
   obligation is cd_link_blocksSound above; the rest is cfg_instrs_endToEnd's
   ordinary wiring. *)
Lemma countdown_rec_noninterferent_param (init_addr : N) :
  (init_addr + 12 < lenAddr)%N ->
  noninterferent_strong init_addr cd_link_instrs (seg_exitCond init_addr [12%N])
    [(X1, true, Some (bv.of_N 2)); (X2, false, None)] [].
Proof.
  intros Hfit γ1 γ2 μ1 μ2 ws Hmem1 Hmem2 HpubReg HpubMem
    HInitReg1 HInitReg2 HInitMem1 HInitMem2
    γ1curpriv γ2curpriv γ1pc γ2pc Htrace n γ1' μ1' steps1.
  assert (Hfit8 : (init_addr + 8 < lenAddr)%N) by lia.
  pose proof (cd_bin init_addr Hfit8) as Hbin.
  (* ι: code at init_addr, counter at its pinned 2.  cfg_init_addr is
     `init_addr + 0`, which is not convertible to init_addr, hence N.add_0_r. *)
  eapply (@cfg_instrs_endToEnd γ1 γ2 γ1' μ1 μ2 μ1' (cd_link_annot init_addr)
    (seg_exitCond init_addr [12%N]) n ws cdRecCtx
    ([env].["q"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)]
          .["k"∷ty_xlenbits ↦ SyncVal (bv.of_N 2)])
    _ HpubReg (cdLink init_addr) (valid_cd_link init_addr) init_addr
    (N.add_0_r init_addr) eq_refl).
  - (* placement *)
    cbn. f_equal. symmetry. apply cd_add0.
  - (* the one exit, +12 *)
    unfold cdLink, gen_seg_contract. cbn [cfg_exits].
    apply etable_faith_exits_of_offs
      with (cbase := bv.add (bv.of_N init_addr) (bv.of_N 0));
      [reflexivity | constructor; [apply cd_exit12 | constructor]].
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
               | (f_equal; apply cd_add0)
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
