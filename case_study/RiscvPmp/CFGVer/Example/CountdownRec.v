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
(* Example/CountdownRec.v -- a LOOP and a SEGMENT, combined.  LIGHT half.   *)
(*                                                                           *)
(*   addr 0: ADDI X1 X1 -1    \  the loop: ONE loop contract, cdRec          *)
(*   addr 4: BNE  X1 X0 -4    /                                              *)
(*   addr 8: ADDI X2 X0 42       the segment after it, executed              *)
(*   addr 12: exit                                                           *)
(*                                                                           *)
(* Two VCs:                                                                  *)
(*  - valid_cd_rec: the loop on its own, as a LOOP VC (cfg_vc_loop,          *)
(*    PLAN-loop-rule.md).  The body runs ONCE from the invariant; the run    *)
(*    stops back at the head (owing the invariant again) or at the exit      *)
(*    (owing the post).  No annotation, no trip count.                       *)
(*  - valid_cd_link: the whole program.  Its head carries the loop as an     *)
(*    ORDINARY ai_block, which fires at step 0, so the loop is one step and  *)
(*    only the tail is executed.                                             *)
(*                                                                           *)
(* The induction over the trips, and the end-to-end theorem, are in          *)
(* CountdownRecResult.v.                                                     *)
(* ========================================================================= *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.CountdownComposed.

(* ------------------------------------------------------------------------ *)
(* 1. THE LOOP, AS ONE LOOP CONTRACT                                        *)
(* ------------------------------------------------------------------------ *)

(* The PARAMETERS: what does not change across trips -- here only the code
   base "q".  The counter changes, so it is existential inside the invariant
   (PLAN-loop-rule.md, decision L2). *)
Definition cdRecCtx : LCtx := ["q"∷ty_xlenbits].

(* THE INVARIANT: a public, non-zero counter.  The pure conjuncts come after
   the chunk that pins "k" (cfgver-contracts: `∗` order matters on consume). *)
Definition cd_rec_inv : Assertion (cdRecCtx ▻ "a"∷ty_xlenbits) :=
  asn.exist "k" ty_xlenbits
    ( X1 ↦ᵣ term_var "k" ∗ secLeakvar "k"
      ∗ asn.formula (formula_relop bop.neq (term_var "k")
                       (term_val ty_xlenbits bv.zero)) )%asn.

(* What the loop leaves: the counter at 0.  gen_seg_contract appends
   minimal_pre itself. *)
Definition cd_rec_post
    : Assertion (cdRecCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( X1 ↦ᵣ term_val ty_xlenbits bv.zero )%asn.

(* base q, the loop's own two instructions, one exit at +8 (relative to the
   loop), fuel 4.  The code bound (8 bytes) is derived by gen_seg_contract.
   The code base is the variable q, so the VCs hold at every load address at
   once, with no vm_compute on it. *)
Definition cdRec : @CFGVerifierContract cdRecCtx :=
  gen_seg_contract (term_var "q") (term_var "q")
    cd_instrs 8 4 [] cd_rec_inv cd_rec_post.

Definition cdRecBlk : BlkAnnot :=
  {| blk_ctx := cdRecCtx ; blk_contract := cdRec |}.

Lemma valid_cd_rec : cfg_vc_loop cdRec (list_AST_AnnotInstr cd_instrs).
Proof. solve_param_vc. Qed.

(* NEGATIVE CONTROLS: the VC is not vacuous. *)

(* As an ORDINARY VC the run does not stop at the head, so the executor must
   unroll a loop whose trip count is symbolic, and cannot. *)
Goal cfg_vc cdRec (list_AST_AnnotInstr cd_instrs).
Proof. Fail solve_param_vc. Abort.

(* An invariant that is NOT PRESERVED by the body must be rejected: with
   `k <> 1`, at k = 2 the branch is taken and the head would owe
   `k-1 <> 1`, i.e. `1 <> 1`. *)
Goal let bad := asn.exist "k" ty_xlenbits
                  (X1 ↦ᵣ term_var "k" ∗ secLeakvar "k"
                   ∗ asn.formula (formula_relop bop.neq (term_var "k")
                                    (term_val ty_xlenbits (bv.of_N 1))))%asn in
     cfg_vc_loop (gen_seg_contract (term_var "q") (term_var "q")
                    cd_instrs 8 4 [] bad cd_rec_post)
       (list_AST_AnnotInstr cd_instrs).
Proof. intros bad. Fail solve_param_vc. Abort.

(* Recorded rather than tested here: DROPPING `k <> 0` STILL VERIFIES, and
   correctly: the VC is PARTIAL correctness, and from k = 0 the counter
   wraps and the loop does exit, after 2^32 trips, with X1 = 0.  An invariant
   must be preserved, not ensure termination. *)

(* ------------------------------------------------------------------------ *)
(* 2. THE LOOP, THEN A SEGMENT                                              *)
(* ------------------------------------------------------------------------ *)

Definition cd_link_instrs : list AST := cd_instrs ++ [ADDI X2 X0 (bv.of_N 42)].

Definition cd_link_annot : list AnnotInstr :=
  {| ai_ghost_before := []
   ; ai_instr        := ADDI X1 X1 neg1_12
   ; ai_ghost_after  := []
     (* the enclosing program STARTS at the loop: an ordinary ai_block, which
        fires at step 0 *)
   ; ai_block        := Some cdRecBlk |}
  :: list_AST_AnnotInstr [BNE X1 X0 back4; ADDI X2 X0 (bv.of_N 42)].

(* The loop block's own conjuncts, VERBATIM (consume is syntactic against the
   path condition): its 8-byte code bound and its invariant.  The outer
   12-byte bound is gen_seg_contract's own, for the tail's fetch. *)
Definition cd_link_extra : Assertion (cdRecCtx ▻ "a"∷ty_xlenbits) :=
  ( gen_base_bound (term_var "q") 8
    ∗ cd_rec_inv
    ∗ asn.exist "v" ty_xlenbits (X2 ↦ᵣ term_var "v") )%asn.

Definition cd_link_post
    : Assertion (cdRecCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( X1 ↦ᵣ term_val ty_xlenbits bv.zero
    ∗ X2 ↦ᵣ term_val ty_xlenbits (bv.of_N 42) )%asn.

Definition cdLink : @CFGVerifierContract cdRecCtx :=
  gen_seg_contract (term_var "q") (term_var "q")
    cd_link_instrs 12 4 [] cd_link_extra cd_link_post.

Lemma valid_cd_link : cfg_vc cdLink cd_link_annot.
Proof. solve_param_vc. Qed.
