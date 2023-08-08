(******************************************************************************)
(* Copyright (c) 2022 Steven Keuchel                                          *)
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

From Coq Require Import
     Arith.PeanoNat
     Bool.Bool
     NArith.BinNat
     PArith.BinPos
     ZArith.BinInt
     RelationClasses
     Morphisms.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Notations
     Prelude
     BitvectorSolve.
From Katamaran Require Export
     BitvectorBase.

Local Set Implicit Arguments.

Module bv.
  Include BitvectorBase.bv.

  Section Sequences.
    Import bv.notations.
    Import Lists.List.
    Import ListNotations.

    (* why do we have both bv_seq and seqBv? *)
    Definition seqBv {n} (min : bv n) (len : nat) := List.map (@bv.of_Z n) (list_numbers.seqZ (bv.unsigned min) (Z.of_nat len)).

    Lemma seqBv_zero {n} m : @seqBv n m 0 = nil.
    Proof. unfold seqBv. now cbv. Qed.
    Lemma seqBv_one {n} m : @seqBv n m 1 = cons m nil.
    Proof.
      unfold seqBv.
      rewrite list_numbers.seqZ_cons; [|Lia.lia]. cbn.
      f_equal. now rewrite of_Z_unsigned. Qed.

    Lemma seqBv_len n base width : length (@seqBv n base width) = width.
    Proof. unfold seqBv. rewrite map_length, list_numbers.seqZ_length. Lia.lia. Qed.

    Lemma seqBv_width_at_least {n width} base k y :
      base.lookup k (@seqBv n base width) = Some y -> exists p , width = (k + S p)%nat.
    Proof.
      intros Hlkup.
      apply list.lookup_lt_Some in Hlkup as Hw.
      apply Nat.le_exists_sub in Hw as (p & [Hweq _]).
      rewrite seqBv_len, <-Nat.add_succ_comm, Nat.add_comm in Hweq.
      eauto.
    Qed.

    Lemma seqBv_app {n} m n1 n2 :
      @seqBv n m (n1 + n2) = seqBv m n1 ++ seqBv (bv.add m (bv.of_nat n1)) n2.
    Proof.
      unfold seqBv.
      rewrite Znat.Nat2Z.inj_add.
      rewrite list_numbers.seqZ_app; try Lia.lia.
      rewrite map_app.
      f_equal.
      apply list.list_eq; intro i.
      rewrite !list.list_lookup_fmap.
      destruct (base.decide (Z.of_nat n2 <= Z.of_nat i)%Z).
      - rewrite !list_numbers.lookup_seqZ_ge ; auto.
      - rewrite !list_numbers.lookup_seqZ_lt; [cbn|Lia.lia..].
        f_equal.
        now rewrite <-!of_Z_add, !of_Z_unsigned, !of_Z_nat.
    Qed.

    Lemma seqBv_succ {n} m n1 :
      (@seqBv n m (S n1)) = cons m (seqBv (one + m) n1).
    Proof.
      rewrite <-Nat.add_1_l, seqBv_app.
      rewrite seqBv_one, add_comm. cbn.
      repeat f_equal.
      now destruct n.
    Qed.

    Lemma seqBv_succ_end {n} m n1 :
      (@seqBv n m (S n1)) = (seqBv m n1)%bv ++ (cons (m + of_nat n1) nil) .
    Proof.
      now rewrite <-Nat.add_1_r, seqBv_app, seqBv_one.
    Qed.

    Lemma seqBv_spec {n width} base k y:
      base.lookup k (@seqBv n base width) = Some y ->
      (base + bv.of_nat k) = y.
    Proof.
      intros Hlkup.
      pose proof (seqBv_width_at_least _ _ Hlkup) as [p ->].
      rewrite seqBv_app, list.lookup_app_r in Hlkup; [| now rewrite seqBv_len].
      rewrite seqBv_len, seqBv_succ, list.lookup_cons, Nat.sub_diag in Hlkup.
      now inversion Hlkup.
    Qed.

    (* More powerful version of `in_seqBv` where `len` and `min + len` need not be representable in `n` bits *)
    Lemma in_seqBv' n v min len :
      (min <=ᵘ v) -> (bv.bin v < bv.bin min + N.of_nat len)%N ->
        base.elem_of v (@seqBv n min len).
    Proof.
      unfold bv.ule, seqBv.
      intros mla alm.
      apply (list.elem_of_list_fmap_1_alt bv.of_Z _ (bv.unsigned v)).
      - apply list_numbers.elem_of_seqZ.
        unfold unsigned, Z.of_nat.
        destruct len; Lia.lia.
      - now rewrite bv.of_Z_unsigned.
    Qed.

    (* NOTE: this lemma does not work for the case where `min == 0` and `len == bv.exp2 n`, which is a valid case. We have hence proven the more general lemma above. *)
    Lemma in_seqBv n v min len :
      (min <=ᵘ v) -> (v <ᵘ bv.add min (bv.of_nat len)) ->
        base.elem_of v (@seqBv n min len).
    Proof.
      unfold bv.ule, bv.ult, seqBv.
      intros mla alm.
      enough (bv.bin v < bv.bin min + N.of_nat len)%N by (apply in_seqBv'; auto).
      eapply N.lt_le_trans; [exact alm |].
      unfold add.
      rewrite bin_of_N_decr. apply N.add_le_mono; auto.
      now rewrite bin_of_nat_decr.
    Qed.

    (* Only prove one direction *)
    Lemma seqBv_no_overlap {n} a a1 a2 b1 b2:
      (N.of_nat (b1 + b2) < (exp2 n))%N ->
      a1 + a2 <= b1 ->
      base.elem_of a (@seqBv n (bv.of_nat a1) a2) ->
      base.elem_of a (seqBv (bv.of_nat b1) b2) ->
      False.
    Proof.
      intros Hrep Hlt Hain Hbin.
      rewrite !list.elem_of_list_lookup in Hain, Hbin.
      destruct Hain as (ai & Hain).
      destruct Hbin as (bi & Hbin).
      apply list.lookup_lt_Some in Hain as Halen.
      apply list.lookup_lt_Some in Hbin as Hblen.
      rewrite !seqBv_len in Halen, Hblen.

      apply seqBv_spec, (f_equal (@bv.bin n)) in Hain, Hbin.
      rewrite !@bin_add_small, !@bin_of_nat_small in Hain, Hbin; try Lia.lia;
      rewrite ?@bin_of_nat_small ; try Lia.lia.
    Qed.

  Lemma seqBv_sub_list {n s s' e e'}:
    (bv.ule s s') ->
    (N.to_nat (bv.bin s') + e' <= N.to_nat (bv.bin s) + e) ->
    exists l1 l2, @seqBv n s e = l1 ++ (seqBv s' e' ++ l2).
  Proof. intros Hs He.
      unfold bv.ule in Hs.
      assert (e = (N.to_nat (bv.bin s') - N.to_nat (bv.bin s)) + (((N.to_nat (bv.bin s') + e') - N.to_nat (bv.bin s')) + ((N.to_nat (bv.bin s) + e) - (N.to_nat (bv.bin s') + e'))))%nat as -> by Lia.lia.
      rewrite 2!seqBv_app.
      do 2 eexists.
      repeat f_equal.
      - unfold bv.add.
        rewrite <-(bv.of_N_bin s') at -1. f_equal.
        rewrite bv.bin_of_nat_small; last solve_bv.
        rewrite <-Nnat.N2Nat.inj_sub, Nnat.N2Nat.id. Lia.lia.
      - Lia.lia.
  Qed.

  Lemma seqBv_sub_elem_of {n s s' e e'} a:
    (s <=ᵘ s') ->
    (N.to_nat (bv.bin s') + e' <= N.to_nat (bv.bin s) + e) ->
    (base.elem_of a (seqBv s' e')) -> (base.elem_of a (@seqBv n s e)).
  Proof.
    intros Hs He Hel.
    destruct (seqBv_sub_list Hs He) as (l1 & l2 & ->).
    rewrite !list.elem_of_app. auto.
  Qed.

  Lemma seqBv_in' {n v min len} :
    (bv.bin min + N.of_nat len <= bv.exp2 n)%N -> (* Required in this direction *)
    (base.elem_of v (@seqBv n min len)) ->
    and (min <=ᵘ v) (bv.bin v < bv.bin min + N.of_nat len)%N.
  Proof.
     unfold bv.ule, bv.ult, seqBv.
     intros Hflow [y [-> Hel%list_numbers.elem_of_seqZ]]%list.elem_of_list_fmap_2.
     unfold bv.of_Z.
     rewrite <-(Znat.Z2N.id y); last solve_bv.
     rewrite bv.to_N_truncz.
     rewrite bv.truncn_small; last solve_bv.
     rewrite bv.bin_of_N_small; last solve_bv.
     solve_bv.
  Qed.

  Lemma NoDup_seqbv {n min len}:
    (bv.bin min + N.of_nat len <= bv.exp2 n)%N ->
    base.NoDup (@seqBv n min len).
  Proof.
    intros Hof.
    apply list.NoDup_fmap_2_strong; last apply list_numbers.NoDup_seqZ.
    intros x y Hxin Hyin Heq.
    rewrite !list_numbers.elem_of_seqZ in Hxin, Hyin.
    rewrite <-(Znat.Z2N.id y) in Heq; last solve_bv.
    rewrite <-(Znat.Z2N.id x) in Heq; last solve_bv.
    unfold bv.unsigned, bv.of_Z in *.
    rewrite !bv.to_N_truncz, !bv.truncn_small in Heq; [|solve_bv..].
    apply (f_equal (@bv.bin _)) in Heq.
    rewrite !bv.bin_of_N_small in Heq; solve_bv.
  Qed.

  End Sequences.

End bv.

Export (hints) bv.
Export (hints) bv.countable.
Export bv (bv).
