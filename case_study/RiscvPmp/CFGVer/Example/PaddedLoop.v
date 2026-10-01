(* ========================================================================= *)
(* Example/PaddedLoop.v -- a LOOP BLOCK inside a longer program (light half). *)
(*                                                                           *)
(* THE REGRESSION TEST FOR A BLOCK WHOSE TABLE IS A PROPER SUBSET OF THE      *)
(* PROGRAM.  The countdown loop of Example/CountdownRec.v (cdRecBlk: one     *)
(* self-referential block, its own table = its two instructions) sits at    *)
(* byte offset 256 of a 66-instruction program: 64 filler no-ops, then the   *)
(* loop.  The program runs the filler, meets the loop head, fires cdRecBlk   *)
(* there (an ordinary ai_block), and exits at +264.  The block's code is     *)
(* checked against the program's table at q + 256 (blk_code_in, PLAN-valid- *)
(* blk-annot.md), and the block is valid at every address                     *)
(* (CountdownRecResult.cdRecBlk_valid).                                       *)
(*                                                                           *)
(* Migrated 2026-10-01 from the earlier hand-composed version (two segment    *)
(* contracts plBody/plFinal glued in Iris by contract_run and                 *)
(* myWP2_loop_induction, PLAN-subtable / diagnostics/prefix-length-cost.md):  *)
(* that Iris glue framed the whole 66-instruction memory map by hand and      *)
(* peaked at ~9.4 GB; the loop is now one block and the solver frames.        *)
(* ========================================================================= *)

From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.CountdownComposed.
From Katamaran Require Export RiscvPmp.CFGVer.Example.CountdownRec.

(* 64 filler instructions in front of the loop, all executed. *)
Definition pl_filler : list AST := List.repeat (MV X4 X4) 64.

(* The whole program: 66 instructions, loop head at byte offset 256. *)
Definition padded_instrs : list AST := pl_filler ++ cd_instrs.

Definition pl_head : N := 256.

(* The filler plain; the loop head carries cdRecBlk as an ORDINARY ai_block,
   which fires when the head is reached. *)
Definition padded_annot : list AnnotInstr :=
  list_AST_AnnotInstr pl_filler
  ++ ({| ai_ghost_before := []
       ; ai_instr        := ADDI X1 X1 neg1_12
       ; ai_ghost_after  := []
       ; ai_block        := Some cdRecBlk
       ; ai_loop         := None |}
      :: list_AST_AnnotInstr [BNE X1 X0 back4]).

(* The block's own conjuncts, VERBATIM at its firing address q + 256 (consume
   is syntactic against the path condition, cf. CountdownRec.cd_link_extra):
   its 8-byte code bound and its invariant.  The outer 264-byte bound is
   gen_seg_contract's own.  X4 is the filler's register. *)
Definition pl_extra : Assertion (cdRecCtx ▻ "a"∷ty_xlenbits) :=
  ( gen_base_bound (term_binop bop.bvadd (term_var "q")
                      (term_val ty_xlenbits (bv.of_N pl_head))) 8
    ∗ cd_rec_inv
    ∗ asn.exist "v" ty_xlenbits (X4 ↦ᵣ term_var "v") )%asn.

Definition pl_post
    : Assertion (cdRecCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( X1 ↦ᵣ term_val ty_xlenbits bv.zero )%asn.

(* 64 filler steps, the block, the exit check, with slack. *)
Definition plLink : @CFGVerifierContract cdRecCtx :=
  gen_seg_contract (term_var "q") (term_var "q")
    padded_instrs 264 70 [] pl_extra pl_post.

Lemma valid_plLink : cfg_vc plLink padded_annot.
Proof. solve_param_vc. Qed.
