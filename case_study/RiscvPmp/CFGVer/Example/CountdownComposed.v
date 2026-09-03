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
(* Example/CountdownComposed.v — LOOP CUT demonstrator (light half).         *)
(*                                                                           *)
(* The countdown loop                                                        *)
(*     addr 0: ADDI X1 X1 (-1)                                               *)
(*     addr 4: BNE  X1 X0 (-4)      <- backward branch to the head           *)
(*     addr 8: exit                                                          *)
(* verified NOT by unrolling it, but as TWO contracts over the loop head:    *)
(*                                                                           *)
(*   cdBody   head -> head, ONE trip, guarded by  k-1 <> 0  (BNE taken)      *)
(*   cdFinal  head -> 8,    the last trip, guarded by  k-1 = 0 (falls out)   *)
(*                                                                           *)
(* Each is discharged ONCE, at a symbolic counter `k`.  The trip count lives *)
(* entirely in the Coq-level induction in CountdownComposedResult.v, so the  *)
(* symbolic executor never sees more than one loop body -- which is the      *)
(* whole point of a loop invariant.                                          *)
(*                                                                           *)
(* Each contract's guard makes the OTHER branch of the BNE infeasible, which *)
(* is what lets a single-exit contract describe a two-way branch.            *)
(*                                                                           *)
(* See plans/PLAN-loop-invariant.md U9.                                       *)
(* ========================================================================= *)

From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.

Definition neg1_12 : bv 12 := bv.of_N 4095.
Definition back4 : bv 13 := bv.of_N 8188.

(* addr 0: ADDI X1 X1 -1 ; addr 4: BNE X1 X0 -4 ; addr 8: exit *)
Definition cd_instrs : list AST := [ADDI X1 X1 neg1_12; BNE X1 X0 back4].

Definition cdCtx : LCtx := ["k" :: ty_xlenbits].

(* -1 sign-extended to 32 bits *)
Definition minus1 : Val ty_xlenbits := bv.of_N 4294967295.

(* the decremented counter, as a TERM *)
Definition dec {Σ} (t : Term Σ ty_xlenbits) : Term Σ ty_xlenbits :=
  term_binop bop.bvadd t (term_val ty_xlenbits minus1).

(* exit condition of the CUT: back at the loop head (offset 0). *)
Definition head_exitCond : bv xlenbits -> bool :=
  fun v => bv.eqb v (bv.of_N 0).

(* ---- LOOP BODY: head -> head, one trip.  Requires k-1 <> 0 so the BNE
       is taken and the fall-through path is infeasible. ---- *)
Definition cdBody : @CFGVerifierContract cdCtx :=
  @MkCFGVerifierContract cdCtx 0%N
    (term_val ty_xlenbits (bv.of_N 0))
    (exits_of_offs (term_val ty_xlenbits (bv.of_N 0)) [0%N])
    (asn_init_pc (bv.of_N 0)
       ∗ X1 ↦ᵣ term_var "k" ∗ secLeakvar "k"
       ∗ asn.formula (formula_relop bop.neq (dec (term_var "k"))
                        (term_val ty_xlenbits bv.zero)))
    cd_instrs
    head_exitCond
    3
    (X1 ↦ᵣ dec (term_var "k") ∗ secLeakvar "k" ∗ minimal_pre).

Lemma valid_cdBody : ValidCFGVerifierContract cdBody.
Proof.
  vm_compute. solve_vc.
  destruct v as [v'|a b]; [|contradiction]. cbn in *.
  right. intros Heq. apply H0. unfold ty.valToRelVal in Heq. congruence.
Qed.

(* The LOOP INVARIANT's resource part, as an assertion at cdCtx.  Defined
   HERE (light half) because the `∗` of the assertion language is shadowed by
   Iris's separating conjunction in any file that imports the Iris stack. *)
Definition cdInvAsn : Assertion cdCtx :=
  X1 ↦ᵣ term_var "k" ∗ minimal_pre.

(* ---- LOOP EXIT: head -> 8, the final trip.  Requires k-1 = 0 so the BNE
       falls through. ---- *)
Definition cdFinal : @CFGVerifierContract cdCtx :=
  @MkCFGVerifierContract cdCtx 0%N
    (term_val ty_xlenbits (bv.of_N 0))
    (exits_of_offs (term_val ty_xlenbits (bv.of_N 0)) [8%N])
    (asn_init_pc (bv.of_N 0)
       ∗ X1 ↦ᵣ term_var "k" ∗ secLeakvar "k"
       ∗ asn.formula (formula_relop bop.eq (dec (term_var "k"))
                        (term_val ty_xlenbits bv.zero)))
    cd_instrs
    (pcOutOfInstrs_exitCond 0 cd_instrs)
    3
    asn_no_post.

Lemma valid_cdFinal : ValidCFGVerifierContract cdFinal.
Proof.
  vm_compute. solve_vc.
  destruct v as [v'|a b]; [|contradiction]. cbn in *.
  unfold ty.valToRelVal in H0. congruence.
Qed.
