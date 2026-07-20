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
  induction k as [| k IH].
  - (* Base case: k = 0
       After unfolding select_last_k_eval_rec(V, 0) = 0, the goal is:
       mulx_v(shiftr(V, 0) XOR 0) = shiftr(V, 1) XOR select_last_k_eval_rec(V, 1)

       The LHS unfolds mulx_v's definition (shift + conditional XOR with R).
       The RHS has select_last_k_eval_rec at step 1, which itself unfolds as:
         let prev = 0 in
         let aged = shiftr(0, 1) = 0 in
         let sel = testbit(V, 0) xor testbit(0, 0) = testbit(V, 0) in
         if sel then 0 XOR R else 0

       The proof reduces to showing these match after unfolding, which requires:
       1. Equational reasoning about shiftr(V, 0) = V and x XOR 0 = x
       2. Showing bit0(V) from the selector matches the selector in mulx_v
       3. Verifying that the conditional XOR with R in both places aligns

       This is blocked by the need for specific bv library lemmas about:
       - bv.shiftr composition and identity
       - bv.lxor composition with zero
       - Bit extraction from composed operations
     *)
    unfold select_last_k_eval, select_last_k_eval_rec.
    cbn.
    unfold mulx_v.
    cbn [bv.zero select_last_k_eval_rec bv.shiftr bv.lxor].
    (* Goal is now deeply nested in bv operations. The needed steps are:
       - Extract binary representations and work at N level
       - Use N.lxor/N.shiftr composition lemmas
       - Reduce bit-level operations using Z.shiftr properties
       For now, this case is admitted pending library lemma support. *)
    admit.
  - (* Inductive step: k = S k'
       Assume IH: mulx_v(shiftr(V, k') XOR C_{k'}) = shiftr(V, k'+1) XOR C_{k'+1}
       Need to prove: mulx_v(shiftr(V, k'+1) XOR C_{k'+1}) = shiftr(V, k'+2) XOR C_{k'+2}

       This follows the same pattern as the base case: applying mulx_v to the
       (k'+1)-th accumulator should produce the (k'+2)-th accumulator.

       The inductive hypothesis directly relates (shiftr(V, k') XOR C_{k'}) to
       (shiftr(V, k'+1) XOR C_{k'+1}), and we need to show applying mulx_v
       shifts this forward by one more step. The selector formula at step k'+1
       (which is part of C_{k'+2}'s definition) should correctly extract
       bit_{k'+1}(V) xor bit0(C_{k'+1}).
     *)
    unfold select_last_k_eval.
    cbn [select_last_k_eval_rec].
    (* After unfolding, the goal shows the full expansion of both C_{k'+1}
       and C_{k'+2}. The structure mirrors the base case but with the inductive
       hypothesis available. Again, this requires bv composition lemmas. *)
    admit.
Admitted.
