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
       After unfolding, the goal is:
       mulx_v(lxor(shiftr(V, 0), 0)) = lxor(shiftr(V, 1), select_last_k_eval_rec(V, 1))

       The key is that both sides are lxor of two parts: a shifted value and
       a correction/selector. The f_equal tactic splits this into:
       1. Selector part: (if testbit(...) then R else 0) must match shiftr(V, 1)
       2. Aged part: shiftr(lxor(...), 1) must match the correction's shifted form
     *)
    unfold select_last_k_eval, select_last_k_eval_rec, mulx_v, select_last_k_R.
    cbn [select_last_k_eval_rec bv.zero].
    (* Split the lxor equality into its two operands *)
    f_equal.
    * (* Selector part: (if ... then R else 0) = shiftr(V, 1) *)
      cbn [bv.shiftr bv.lxor bv.of_N bv.zero N.lxor bv.bin].
      (* After computational normalization, this should reduce further. *)
      admit.
    * (* Aged part: shiftr(lxor(shiftr(V, 0), 0), 1) = (if ... then ... else ...) *)
      cbn [bv.shiftr bv.lxor bv.of_N bv.zero N.lxor bv.bin xorb].
      (* After unfolding and normalization at the N/Z level *)
      admit.
  - (* Inductive step: k = S k' *)
    (* Assume: IH : ∀ V, mulx_v(lxor(shiftr(V, k'), C_{k'})) = lxor(shiftr(V, S k'), C_{S k'}) *)
    (* Goal: ∀ V, mulx_v(lxor(shiftr(V, S k'), C_{S k'})) = lxor(shiftr(V, S(S k')), C_{S(S k')}) *)
    unfold select_last_k_eval.
    cbn [select_last_k_eval_rec].
    (* The recursion unfolds to show C_{S(S k')} in full *)
    f_equal.
    * (* Selector for step S k' *)
      cbn [bv.shiftr bv.lxor bv.of_N N.lxor bv.bin].
      (* Should reduce with the same strategy as base case *)
      admit.
    * (* Aged part at step S k' *)
      cbn [bv.shiftr bv.lxor bv.of_N N.lxor bv.bin xorb].
      (* With IH available, should follow the same pattern *)
      admit.
Admitted.
