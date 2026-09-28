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
(*   addr 0: ADDI X1 X1 -1    \  the loop: ONE self-referential block        *)
(*   addr 4: BNE  X1 X0 -4    /  contract, cdRecBlk                          *)
(*   addr 8: ADDI X2 X0 42       the segment after it, executed              *)
(*   addr 12: exit                                                           *)
(*                                                                           *)
(* Two VCs:                                                                  *)
(*  - valid_cd_rec: the loop on its own.  Its head carries cdRecBlk as a     *)
(*    RE-ENTRY block (ai_loop): the entry executes the head, the back edge   *)
(*    meets the block and CONSUMES the invariant (the contract's own         *)
(*    precondition) at k-1.  No trip count, no LoopSpec.                     *)
(*  - valid_cd_link: the whole program.  Its head carries the same block as  *)
(*    an ORDINARY ai_block, which fires at step 0, so the loop is one step   *)
(*    and only the tail is executed.                                         *)
(*                                                                           *)
(* The Löb argument that makes the self-reference sound, and the end-to-end  *)
(* theorem, are in CountdownRecResult.v.  See plans/PLAN-rec-loop-block.md.  *)
(* ========================================================================= *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.CountdownComposed.

(* ------------------------------------------------------------------------ *)
(* 1. THE LOOP, AS ONE BLOCK                                                *)
(* ------------------------------------------------------------------------ *)

(* "q" is the code base, "k" the counter. *)
Definition cdRecCtx : LCtx := ["q"∷ty_xlenbits; "k"∷ty_xlenbits].

(* THE INVARIANT: a public, non-zero counter.  The pure conjuncts come after
   the chunk that pins "k" (cfgver-contracts: `∗` order matters on consume). *)
Definition cd_rec_inv : Assertion (cdRecCtx ▻ "a"∷ty_xlenbits) :=
  ( X1 ↦ᵣ term_var "k" ∗ secLeakvar "k"
    ∗ asn.formula (formula_relop bop.neq (term_var "k")
                     (term_val ty_xlenbits bv.zero)) )%asn.

(* What the loop leaves: the counter at 0.  gen_seg_contract appends
   minimal_pre itself. *)
Definition cd_rec_post
    : Assertion (cdRecCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( X1 ↦ᵣ term_val ty_xlenbits bv.zero )%asn.

(* base q, the loop's own two instructions, one exit at +8 (relative to the
   loop), fuel 4 (head, BNE, block, exit check).  The code bound (8 bytes) is
   derived by gen_seg_contract.

   No concrete load address appears anywhere here: the contract used to take
   one (`ia`) only to fill cfg_init_addr, a field dropped by
   PLAN-valid-blk-annot §8.2, and before that the concrete exit condition
   `seg_exitCond ia` (gone since PLAN-exit-targets.md -- the exit is the term
   q + 8, and a block resumes there).  The code base is the variable q, so the
   VCs hold at every load address at once, with no vm_compute on it. *)
Definition cdRec : @CFGVerifierContract cdRecCtx :=
  gen_seg_contract (term_var "q") (term_var "q")
    cd_instrs 8 4 [] cd_rec_inv cd_rec_post.

Definition cdRecBlk : BlkAnnot :=
  {| blk_ctx := cdRecCtx ; blk_contract := cdRec |}.

(* The loop's code with its head annotated by ITS OWN block, as a RE-ENTRY
   block (ai_loop): the entry executes the head, the back edge fires it. *)
Definition cd_rec_annot : list AnnotInstr :=
  {| ai_ghost_before := []
   ; ai_instr        := ADDI X1 X1 neg1_12
   ; ai_ghost_after  := []
   ; ai_block        := None
   ; ai_loop         := Some cdRecBlk |}
  :: list_AST_AnnotInstr [BNE X1 X0 back4].

Lemma valid_cd_rec : cfg_vc cdRec cd_rec_annot.
Proof. solve_param_vc. Qed.

(* NEGATIVE CONTROLS: the VC is not vacuous. *)

(* Without the head annotation the executor must unroll a loop whose trip
   count is symbolic, and cannot. *)
Goal cfg_vc cdRec (list_AST_AnnotInstr cd_instrs).
Proof. Fail solve_param_vc. Abort.

(* An invariant that is NOT PRESERVED by the body must be rejected: with
   `k <> 1`, at k = 2 the branch is taken and the back edge would owe
   `k-1 <> 1`, i.e. `1 <> 1`. *)
Goal let bad := (X1 ↦ᵣ term_var "k" ∗ secLeakvar "k"
                 ∗ asn.formula (formula_relop bop.neq (term_var "k")
                                  (term_val ty_xlenbits (bv.of_N 1))))%asn in
     let c := gen_seg_contract (term_var "q") (term_var "q")
                cd_instrs 8 4 [] bad cd_rec_post in
     cfg_vc c ({| ai_ghost_before := []; ai_instr := ADDI X1 X1 neg1_12;
                      ai_ghost_after := []; ai_block := None;
                      ai_loop := Some {| blk_ctx := cdRecCtx ;
                                         blk_contract := c |} |}
                   :: list_AST_AnnotInstr [BNE X1 X0 back4]).
Proof. intros bad c. Fail solve_param_vc. Abort.

(* Recorded rather than tested here: DROPPING `k <> 0` STILL VERIFIES, and
   correctly: the VC is PARTIAL correctness (Löb), and from k = 0 the counter
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
   ; ai_block        := Some cdRecBlk
   ; ai_loop         := None |}
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
