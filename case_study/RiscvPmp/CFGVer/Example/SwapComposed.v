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
(* Example/SwapComposed.v — CONTRACT COMPOSITION demonstrator (light half).  *)
(*                                                                           *)
(* The three-instruction register swap, verified NOT as one contract but as  *)
(* TWO contracts joined at a cut point.  This is the smallest end-to-end      *)
(* exercise of the composability machinery:                                  *)
(*                                                                           *)
(*   - `cfg_postcondition` carrying a REAL exit assertion (not asn_no_post),  *)
(*   - the soundness bridge handing that assertion back to the caller,        *)
(*   - `myWP2_loop_join` collapsing the resulting nested loop.                *)
(*                                                                           *)
(* Both segments range over the SAME instruction table; only the             *)
(* precondition, postcondition, exit set and fuel differ.  That is the        *)
(* intended shape of a cut: instruction ownership threads straight through,   *)
(* and each segment's VC unrolls only its own steps.                          *)
(*                                                                           *)
(* The composition itself is in Example/SwapComposedResult.v (it needs the    *)
(* Iris/Adequacy stack, which must not be dragged in here).                   *)
(*                                                                           *)
(* See plans/PLAN-loop-invariant.md U1-U8.                                    *)
(* ========================================================================= *)

From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.

Definition swap_instrs : list AST := [MV X3 X2; MV X2 X1; MV X1 X3].

Definition swapCtx : LCtx :=
  ["x" :: ty_xlenbits; "y" :: ty_xlenbits; "z" :: ty_xlenbits].

(* The CUT's exit condition: pc is exactly the cut address (offset 4).
   Unlike a whole-program exit condition this is an equality, not a
   past-the-end test -- the cut is in the MIDDLE of the program. *)
Definition cut_exitCond : bv xlenbits -> bool :=
  fun v => bv.eqb v (bv.of_N 4).

(* ---- Segment A: 0 -> 4.  Executes `MV X3 X2` only. ----
   Its postcondition is the state at the cut.  `minimal_pre` appears there
   because segment B's precondition is wrapped in extend_to_minimal_pre, so
   cur_privilege and the leakage-invariant chunk have to be handed ACROSS the
   cut -- exactly the "ownership the next segment needs" a cut assertion is
   for.  The registers are private, so no secLeakvar is required here; a cut
   carrying public values would need those too. *)
Definition swapA : @CFGVerifierContract swapCtx :=
  @MkCFGVerifierContract swapCtx 0%N
    (term_val ty_xlenbits (bv.of_N 0))
    (exits_of_offs (term_val ty_xlenbits (bv.of_N 0)) [4%N])
    (asn_init_pc (bv.of_N 0)
       ∗ X1 ↦ᵣ term_var "x" ∗ X2 ↦ᵣ term_var "y" ∗ X3 ↦ᵣ term_var "z")
    swap_instrs
    cut_exitCond
    3
    (X1 ↦ᵣ term_var "x" ∗ X2 ↦ᵣ term_var "y" ∗ X3 ↦ᵣ term_var "y"
       ∗ minimal_pre).

Lemma valid_swapA : ValidCFGVerifierContract swapA.
Proof. vm_compute. solve_vc. Qed.

(* ---- Segment B: 4 -> 12.  Executes `MV X2 X1; MV X1 X3`. ----
   Entry pc pinned to the cut address by asn_pc_eq; precondition is exactly
   segment A's postcondition.  Ordinary trivial post: nothing follows it. *)
Definition swapB : @CFGVerifierContract swapCtx :=
  @MkCFGVerifierContract swapCtx 0%N
    (term_val ty_xlenbits (bv.of_N 0))
    (exits_of_offs (term_val ty_xlenbits (bv.of_N 0)) [12%N])
    (asn_pc_eq (term_val ty_xlenbits (bv.of_N 4))
       ∗ X1 ↦ᵣ term_var "x" ∗ X2 ↦ᵣ term_var "y" ∗ X3 ↦ᵣ term_var "y")
    swap_instrs
    (pcOutOfInstrs_exitCond 0 swap_instrs)
    4
    asn_no_post.

Lemma valid_swapB : ValidCFGVerifierContract swapB.
Proof. vm_compute. solve_vc. Qed.
