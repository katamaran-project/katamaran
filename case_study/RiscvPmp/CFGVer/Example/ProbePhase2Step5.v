(* Phase 2 Step 2.5: select_last_k_bump master lemma
   Standalone probe to develop the algebraic proof.
   The master lemma: select_last_k_eval's recursion is an exact replay of mulx.
*)

From Coq Require Import
     ZArith.ZArith Lists.List micromega.Lia Strings.String Bool.
From Katamaran Require Import
     Notations Bitvector Syntax.UnOps.

Import bv.notations.
Import Syntax.UnOps.uop.

(* Define mulx locally for this probe *)
Definition mulx_v (a : bv 32) : bv 32 :=
  let R := bv.of_N 0xE1000000 in
  bv.lxor (if N.testbit (bv.bin a) 0 then R else bv.zero)
          (bv.shiftr a (bv.of_N 1 : bv 5)).

(* Master lemma: the folded form is sound *)
Lemma select_last_k_bump (V : bv 32) (k : nat) :
  mulx_v (bv.lxor
    (bv.shiftr V (bv.of_N (N.of_nat k) : bv 6))
    (select_last_k_eval k V))
  = bv.lxor
    (bv.shiftr V (bv.of_N (N.of_nat (S k)) : bv 6))
    (select_last_k_eval (S k) V).
Proof.
  (* This is the core algebraic lemma. The proof works by unfolding
     select_last_k_eval_rec and verifying the exact definition of mulx at
     each step. The key is that the selector in the recursion
     (bit_k(V) xor bit0(Correction_{k})) exactly matches the selector for
     the next mulx step.

     Proof structure attempted:
     1. Induction on k
     2. Base case (k=0): simplify select_last_k_eval_rec(V, 0) = 0
        Goal becomes: mulx_v(shiftr(V,0) XOR 0) = shiftr(V,1) XOR correction_1(V)
        This requires lemmas about:
        - shiftr(x, 0) = x
        - x XOR 0 = x
        - mulx_v(x) distributes correctly over XOR
        - The selector formula bit0(shifted_xored) = bit_k(V) xor bit0(C_k)
     3. Inductive step: assume IH for k, prove for S k
        Similar bitvector algebra with shift/XOR composition

     Challenge: The proof requires lemmas about bv.shiftr and bv.lxor
     composition that may not be readily available. Both are defined in terms
     of Z.shiftr and N.lxor at the binary level, which makes equational
     reasoning through unfolding expensive.

     Potential approaches:
     a) Use existing bv library lemmas (if they exist) for shift/XOR interaction
     b) Prove the needed lemmas as auxiliary results
     c) Reduce to a concrete N-level proof using bv.bin extraction

     The mathematics is verified by hand in PLAN-solver-fold.md Phase 2 §2.5.
  *)
  admit. (* Proof structure in place; lemma applications pending. *)
Admitted.
