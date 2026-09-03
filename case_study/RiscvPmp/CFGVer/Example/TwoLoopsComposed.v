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
(* Example/TwoLoopsComposed.v — TWO-LOOP composition (light half).          *)
(*                                                                           *)
(*   addr  0: ADDI X1 X1 -1     loop A head                                  *)
(*   addr  4: BNE  X1 X0 -4     back to 0                                    *)
(*   addr  8: ADDI X2 X2 -1     loop B head                                  *)
(*   addr 12: BNE  X2 X0 -4     back to 8                                    *)
(*   addr 16: exit                                                           *)
(*                                                                           *)
(* FOUR contracts, each discharged ONCE at a symbolic counter: a body and an *)
(* exit contract for each loop.  Loop A's exit contract lands on loop B's    *)
(* HEAD, which is what joins the two loops.                                  *)
(*                                                                           *)
(* Note what loop A's contracts do NOT mention: X2.  Loop B's counter is     *)
(* FRAMED past the whole of loop A -- never fed to any of A's VCs, so no     *)
(* step of loop A pays for it.  That is the O(1)-per-segment footprint       *)
(* property, exercised for the first time here.                              *)
(*                                                                           *)
(* See plans/PLAN-loop-invariant.md U11.                                     *)
(* ========================================================================= *)

From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.

Definition t_neg1 : bv 12 := bv.of_N 4095.
Definition t_back4 : bv 13 := bv.of_N 8188.
Definition t_instrs : list AST :=
  [ADDI X1 X1 t_neg1; BNE X1 X0 t_back4; ADDI X2 X2 t_neg1; BNE X2 X0 t_back4].

Definition tCtxA : LCtx := ["k" :: ty_xlenbits].
Definition tCtxB : LCtx := ["m" :: ty_xlenbits].

Definition tdec {Σ} (t : Term Σ ty_xlenbits) : Term Σ ty_xlenbits :=
  term_binop bop.bvadd t (term_val ty_xlenbits (bv.of_N 4294967295)).

Definition at0 : bv xlenbits -> bool := fun v => bv.eqb v (bv.of_N 0).
Definition at8 : bv xlenbits -> bool := fun v => bv.eqb v (bv.of_N 8).

(* ---- LOOP A: head 0.  Owns ONLY X1 -- X2 is framed OUTSIDE, never fed to
       these VCs, which is what keeps each segment's footprint O(1). ---- *)
Definition tAbody : @CFGVerifierContract tCtxA :=
  @MkCFGVerifierContract tCtxA 0%N
    (term_val ty_xlenbits (bv.of_N 0))
    (exits_of_offs (term_val ty_xlenbits (bv.of_N 0)) [0%N])
    (asn_init_pc (bv.of_N 0) ∗ X1 ↦ᵣ term_var "k" ∗ secLeakvar "k"
       ∗ asn.formula (formula_relop bop.neq (tdec (term_var "k"))
                        (term_val ty_xlenbits bv.zero)))
    t_instrs at0 3
    (X1 ↦ᵣ tdec (term_var "k") ∗ secLeakvar "k" ∗ minimal_pre).

Lemma valid_tAbody : ValidCFGVerifierContract tAbody.
Proof.
  vm_compute. solve_vc.
  destruct v as [v'|a b]; [|contradiction]. cbn in *.
  right. intros Heq. apply H0. unfold ty.valToRelVal in Heq. congruence.
Qed.

(* A's last trip: falls through to 8, which is LOOP B's HEAD. *)
Definition tAfinal : @CFGVerifierContract tCtxA :=
  @MkCFGVerifierContract tCtxA 0%N
    (term_val ty_xlenbits (bv.of_N 0))
    (exits_of_offs (term_val ty_xlenbits (bv.of_N 0)) [8%N])
    (asn_init_pc (bv.of_N 0) ∗ X1 ↦ᵣ term_var "k" ∗ secLeakvar "k"
       ∗ asn.formula (formula_relop bop.eq (tdec (term_var "k"))
                        (term_val ty_xlenbits bv.zero)))
    t_instrs at8 3
    (X1 ↦ᵣ tdec (term_var "k") ∗ minimal_pre).

Lemma valid_tAfinal : ValidCFGVerifierContract tAfinal.
Proof.
  vm_compute. solve_vc.
  destruct v as [v'|a b]; [|contradiction]. cbn in *.
  unfold ty.valToRelVal in H0. congruence.
Qed.

(* ---- LOOP B: head 8.  Owns ONLY X2.  Entered from A's fall-through. ---- *)
Definition tBbody : @CFGVerifierContract tCtxB :=
  @MkCFGVerifierContract tCtxB 0%N
    (term_val ty_xlenbits (bv.of_N 0))
    (exits_of_offs (term_val ty_xlenbits (bv.of_N 0)) [8%N])
    (asn_pc_eq (term_val ty_xlenbits (bv.of_N 8))
       ∗ X2 ↦ᵣ term_var "m" ∗ secLeakvar "m"
       ∗ asn.formula (formula_relop bop.neq (tdec (term_var "m"))
                        (term_val ty_xlenbits bv.zero)))
    t_instrs at8 3
    (X2 ↦ᵣ tdec (term_var "m") ∗ secLeakvar "m" ∗ minimal_pre).

Lemma valid_tBbody : ValidCFGVerifierContract tBbody.
Proof.
  vm_compute. solve_vc.
  destruct v as [v'|a b]; [|contradiction]. cbn in *.
  right. intros Heq. apply H0. unfold ty.valToRelVal in Heq. congruence.
Qed.

Definition tBfinal : @CFGVerifierContract tCtxB :=
  @MkCFGVerifierContract tCtxB 0%N
    (term_val ty_xlenbits (bv.of_N 0))
    (exits_of_offs (term_val ty_xlenbits (bv.of_N 0)) [16%N])
    (asn_pc_eq (term_val ty_xlenbits (bv.of_N 8))
       ∗ X2 ↦ᵣ term_var "m" ∗ secLeakvar "m"
       ∗ asn.formula (formula_relop bop.eq (tdec (term_var "m"))
                        (term_val ty_xlenbits bv.zero)))
    t_instrs (pcOutOfInstrs_exitCond 0 t_instrs) 3
    asn_no_post.

Lemma valid_tBfinal : ValidCFGVerifierContract tBfinal.
Proof.
  vm_compute. solve_vc.
  destruct v as [v'|a b]; [|contradiction]. cbn in *.
  unfold ty.valToRelVal in H0. congruence.
Qed.

(* invariant resource parts, defined here where `∗` is the assertion-level one *)
Definition tInvA : Assertion tCtxA := X1 ↦ᵣ term_var "k" ∗ minimal_pre.
Definition tInvB : Assertion tCtxB := X2 ↦ᵣ term_var "m" ∗ minimal_pre.

(* X2 alone: the resource FRAMED past the whole of loop A. *)
Definition tX2 : Assertion tCtxB := X2 ↦ᵣ term_var "m".
