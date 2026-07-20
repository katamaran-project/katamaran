(* ProbeFoldAlgebra.v — PLAN-solver-fold.md Phase 0: the fold algebra,
   proven standalone against Katamaran's bv library, ZERO executor
   machinery. Establishes:
   1. mulx_spec — the 8-op constant-time mask chain (exact ALU ops of
      key_schedule_loop2's masking round) equals the clean spec form
      (A >> 1) ^ (bit0(A) ? R : 0).
   2. mulx_mulx_fold — the k=2 base identity:
      mulx (mulx A) = (A >> 2) ^ T2[A & 3].
   Doubling instances (k=2→4, k=4→8) come next in this same file once
   the base lands. Only imports Bitvector — compiles in seconds. *)
From Coq Require Import
     NArith.NArith
     ZArith.ZArith
     micromega.Lia.
From Katamaran Require Import
     Bitvector.

Local Open Scope N_scope.

(* ---------------------------------------------------------------- *)
(* Constants                                                         *)
(* ---------------------------------------------------------------- *)

(* GHASH reduction constant: LUI 921600 = 0xE1000 << 12 = 0xE1000000. *)
Definition R32 : bv 32 := bv.of_N 0xE1000000.
(* sext(-1) at width 32 (the ADDI/XORI -1 immediate). *)
Definition ones32 : bv 32 := bv.ones 32.
(* shift amounts as the machine sees them (vector_subrange 0 5 : bv 5) *)
Definition sh1  : bv 5 := bv.of_N 1.
Definition sh2  : bv 5 := bv.of_N 2.
Definition sh31 : bv 5 := bv.of_N 31.

Definition bit {n} (x : bv n) (i : N) : bool := N.testbit (bv.bin x) i.

(* ---------------------------------------------------------------- *)
(* Bit-level helper library (bv.lxor/shiftr have no lemmas upstream)  *)
(* ---------------------------------------------------------------- *)

Lemma exp2_32 : bv.exp2 32 = 2 ^ 32.
Proof. reflexivity. Qed.

Lemma bin_of_N32 (z : N) : bv.bin (@bv.of_N 32 z) = bv.truncn 32 z.
Proof. reflexivity. Qed.

Lemma bin_of_N32_mod (z : N) : bv.bin (@bv.of_N 32 z) = z mod 2 ^ 32.
Proof. rewrite bin_of_N32, bv.truncn_spec. reflexivity. Qed.

Lemma bit_high (x : bv 32) (i : N) : 32 <= i -> bit x i = false.
Proof.
  intros Hi. unfold bit. apply N.bits_above_log2.
  pose proof (bv.bv_is_wf x) as Hwf. rewrite exp2_32 in Hwf.
  destruct (N.eq_dec (bv.bin x) 0) as [->|Hnz]; [cbn; lia|].
  apply N.log2_lt_pow2 in Hwf; lia.
Qed.

Lemma bv_bits_inj (x y : bv 32) :
  (forall i, i < 32 -> bit x i = bit y i) -> x = y.
Proof.
  intros H. apply bv.bin_inj_equiv, N.bits_inj. intros i.
  destruct (N.lt_ge_cases i 32) as [Hi|Hi].
  - exact (H i Hi).
  - change (bit x i = bit y i). now rewrite !bit_high.
Qed.

Lemma bit_land (x y : bv 32) (i : N) :
  bit (bv.land x y) i = andb (bit x i) (bit y i).
Proof.
  unfold bit, bv.land. rewrite bin_of_N32_mod.
  destruct (N.lt_ge_cases i 32) as [Hi|Hi].
  - rewrite N.mod_pow2_bits_low by exact Hi. apply N.land_spec.
  - rewrite N.mod_pow2_bits_high by exact Hi.
    change (N.testbit (bv.bin x) i) with (bit x i).
    change (N.testbit (bv.bin y) i) with (bit y i).
    now rewrite !bit_high.
Qed.

Lemma bit_lxor (x y : bv 32) (i : N) :
  bit (bv.lxor x y) i = xorb (bit x i) (bit y i).
Proof.
  unfold bit, bv.lxor. rewrite bin_of_N32_mod.
  destruct (N.lt_ge_cases i 32) as [Hi|Hi].
  - rewrite N.mod_pow2_bits_low by exact Hi. apply N.lxor_spec.
  - rewrite N.mod_pow2_bits_high by exact Hi.
    change (N.testbit (bv.bin x) i) with (bit x i).
    change (N.testbit (bv.bin y) i) with (bit y i).
    now rewrite !bit_high.
Qed.

Lemma shiftr_ZN (a b : N) :
  Z.shiftr (Z.of_N a) (Z.of_N b) = Z.of_N (N.shiftr a b).
Proof.
  rewrite Z.shiftr_div_pow2 by apply N2Z.is_nonneg.
  rewrite N.shiftr_div_pow2, N2Z.inj_div, N2Z.inj_pow.
  reflexivity.
Qed.

Lemma bin_shiftr32 (x : bv 32) (y : bv 5) :
  bv.bin (bv.shiftr x y) = N.shiftr (bv.bin x) (bv.bin y) mod 2 ^ 32.
Proof.
  unfold bv.shiftr, bv.of_Z, bv.unsigned, bv.truncz.
  rewrite bin_of_N32_mod, shiftr_ZN.
  change (2 ^ Z.of_nat 32)%Z with (Z.of_N (2 ^ 32)).
  rewrite <- N2Z.inj_mod, N2Z.id.
  now rewrite N.Div0.mod_mod.
Qed.

Lemma bit_shiftr (x : bv 32) (y : bv 5) (i : N) :
  bit (bv.shiftr x y) i = bit x (i + bv.bin y).
Proof.
  unfold bit. rewrite bin_shiftr32.
  destruct (N.lt_ge_cases i 32) as [Hi|Hi].
  - rewrite N.mod_pow2_bits_low by exact Hi. apply N.shiftr_spec'.
  - rewrite N.mod_pow2_bits_high by exact Hi.
    change (N.testbit (bv.bin x) (i + bv.bin y)) with (bit x (i + bv.bin y)).
    rewrite bit_high; [reflexivity|lia].
Qed.

Lemma bit_zero (i : N) : bit (@bv.zero 32) i = false.
Proof.
  unfold bit. change (bv.bin (@bv.zero 32)) with 0. apply N.bits_0.
Qed.

Lemma testbit_1 (i : N) : N.testbit 1 i = (0 =? i).
Proof. change 1 with (2 ^ 0) at 1. apply N.pow2_bits_eqb. Qed.

Lemma lxor_zero_l (x : bv 32) : bv.lxor bv.zero x = x.
Proof.
  apply bv_bits_inj. intros i Hi.
  rewrite bit_lxor, bit_zero. apply Bool.xorb_false_l.
Qed.

Lemma lxor_assoc (x y z : bv 32) :
  bv.lxor (bv.lxor x y) z = bv.lxor x (bv.lxor y z).
Proof.
  apply bv_bits_inj. intros i Hi. rewrite !bit_lxor.
  now destruct (bit x i), (bit y i), (bit z i).
Qed.

Lemma shiftr_lxor (x y : bv 32) (k : bv 5) :
  bv.shiftr (bv.lxor x y) k = bv.lxor (bv.shiftr x k) (bv.shiftr y k).
Proof.
  apply bv_bits_inj. intros i Hi.
  rewrite bit_shiftr, !bit_lxor, !bit_shiftr. reflexivity.
Qed.

Lemma shiftr_shiftr_1_1 (x : bv 32) :
  bv.shiftr (bv.shiftr x sh1) sh1 = bv.shiftr x sh2.
Proof.
  apply bv_bits_inj. intros i Hi.
  rewrite !bit_shiftr. f_equal.
  change (bv.bin sh1) with 1. change (bv.bin sh2) with 2. lia.
Qed.

(* ---------------------------------------------------------------- *)
(* The masking round, instruction-faithful                           *)
(* ---------------------------------------------------------------- *)

(* Instructions 2-8 of the round: from b = A0 & 1 build (b?~0:0) & R.
     xori a2, a1, -1  ; addi a1, a1, -1 ; and a1, a1, a2 ;
     srli a1, a1, 31  ; addi a1, a1, -1 ; lui a2, 921600 ; and a1, a1, a2 *)
Definition mask_of (b : bv 32) : bv 32 :=
  bv.land
    (bv.add
       (bv.shiftr (bv.land (bv.add b ones32) (bv.lxor b ones32)) sh31)
       ones32)
    R32.

(* The whole round: andi a1,a0,1 ; <mask_of> ; srli a0,a0,1 ; xor a0,a1,a0 *)
Definition mulx (a : bv 32) : bv 32 :=
  bv.lxor (mask_of (bv.land a (bv.of_N 1))) (bv.shiftr a sh1).

(* ---------------------------------------------------------------- *)
(* Spec form                                                         *)
(* ---------------------------------------------------------------- *)

Lemma bit_one (i : N) : i < 32 -> bit (@bv.of_N 32 1) i = (0 =? i).
Proof.
  intros Hi. unfold bit. rewrite bin_of_N32_mod.
  rewrite N.mod_pow2_bits_low by exact Hi. apply testbit_1.
Qed.

Lemma land1_bit0 (a : bv 32) :
  bv.land a (bv.of_N 1) = if bit a 0 then bv.of_N 1 else bv.zero.
Proof.
  apply bv_bits_inj. intros i Hi. rewrite bit_land.
  rewrite bit_one by exact Hi.
  destruct (bit a 0) eqn:B0.
  - rewrite bit_one by exact Hi.
    destruct (N.eqb_spec 0 i) as [<-|Hne].
    + now rewrite B0.
    + now rewrite Bool.andb_false_r.
  - rewrite bit_zero.
    destruct (N.eqb_spec 0 i) as [<-|Hne].
    + now rewrite B0.
    + now rewrite Bool.andb_false_r.
Qed.

Lemma mulx_spec (a : bv 32) :
  mulx a = bv.lxor (if bit a 0 then R32 else bv.zero) (bv.shiftr a sh1).
Proof.
  unfold mulx. rewrite land1_bit0. destruct (bit a 0).
  - replace (mask_of (bv.of_N 1)) with R32 by (vm_compute; reflexivity).
    reflexivity.
  - replace (mask_of bv.zero) with (@bv.zero 32) by (vm_compute; reflexivity).
    reflexivity.
Qed.

(* ---------------------------------------------------------------- *)
(* mulx is GF(2)-linear — the load-bearing fact for the per-bit       *)
(* incremental form (PLAN-solver-fold.md 2026-07-20 LOCKED block).    *)
(* Everything about the incremental representation V_n and its        *)
(* one-round recurrence follows from this + shiftr_lxor.              *)
(* ---------------------------------------------------------------- *)

Lemma lxor_zero_r (x : bv 32) : bv.lxor x bv.zero = x.
Proof.
  apply bv_bits_inj. intros i Hi.
  rewrite bit_lxor, bit_zero. apply Bool.xorb_false_r.
Qed.

Lemma lxor_comm (x y : bv 32) : bv.lxor x y = bv.lxor y x.
Proof.
  apply bv_bits_inj. intros i Hi. rewrite !bit_lxor. apply Bool.xorb_comm.
Qed.

Lemma lxor_nilpotent (x : bv 32) : bv.lxor x x = bv.zero.
Proof.
  apply bv_bits_inj. intros i Hi.
  rewrite bit_lxor, bit_zero. apply Bool.xorb_nilpotent.
Qed.

(* The bit-select distributes over XOR: this is exactly the algebraic
   identity that makes the round GF(2)-linear despite the branch. *)
Lemma sel_xor (bx cy : bool) :
  (if xorb bx cy then R32 else bv.zero)
  = bv.lxor (if bx then R32 else bv.zero) (if cy then R32 else bv.zero).
Proof.
  destruct bx, cy; cbn.
  - now rewrite lxor_nilpotent.
  - now rewrite lxor_zero_r.
  - now rewrite lxor_zero_l.
  - now rewrite lxor_zero_l.
Qed.

(* A pure four-way XOR rearrangement (associativity + commutativity). *)
Lemma lxor_middle_swap (a b c d : bv 32) :
  bv.lxor (bv.lxor a b) (bv.lxor c d)
  = bv.lxor (bv.lxor a c) (bv.lxor b d).
Proof.
  apply bv_bits_inj. intros i Hi. rewrite !bit_lxor.
  now destruct (bit a i), (bit b i), (bit c i), (bit d i).
Qed.

Theorem mulx_linear (x y : bv 32) :
  mulx (bv.lxor x y) = bv.lxor (mulx x) (mulx y).
Proof.
  rewrite !mulx_spec.
  rewrite bit_lxor, shiftr_lxor, sel_xor.
  apply lxor_middle_swap.
Qed.

(* The one-round incremental recurrence.  A per-bit value is carried as
     V = (A >> k) ^ S      -- S an XOR of masked constants (the accumulator)
   and applying one masking round yields
     mulx V = (bit_k(A) ? R : 0) ^ ( (A >> k >> 1) ^ mulx S ).
   Reading the RHS as the next value: the A-part shifts once more
   (A>>k>>1, folded to A>>(k+1) by a generic shiftr-composition rule),
   a fresh summand (bit_k(A)?R:0) is appended, and every old constant in S
   advances by one mulx (mulx S, pushed through the XOR-list by
   mulx_linear + the concrete constant folds).  No copy of A is
   duplicated: A occurs exactly in the shift and in the one new bit-test.
   This is the identity the peval fold rule realizes; only mulx_linear
   and mulx_spec are load-bearing here. *)
Theorem mulx_incremental (A S : bv 32) (k : bv 5) :
  mulx (bv.lxor (bv.shiftr A k) S)
  = bv.lxor (if bit A (bv.bin k) then R32 else bv.zero)
            (bv.lxor (bv.shiftr (bv.shiftr A k) sh1) (mulx S)).
Proof.
  rewrite mulx_linear, (mulx_spec (bv.shiftr A k)).
  rewrite bit_shiftr, N.add_0_l.
  apply lxor_assoc.
Qed.

(* ---------------------------------------------------------------- *)
(* The k=2 fold                                                      *)
(* ---------------------------------------------------------------- *)

(* Correction table, indexed by the low 2 bits of A (hand-derived in
   PLAN-solver-fold.md; this file re-derives it mechanically):
     T2[b1b0] = (T1[b0] >> 1) ^ T1[b1],  T1 = [0; R]. *)
Definition T2 (x : N) : bv 32 :=
  match x with
  | 0 => bv.zero
  | 1 => bv.of_N 0x70800000
  | 2 => R32
  | _ => bv.of_N 0x91800000
  end.

Definition g2 (a : bv 32) : bv 32 :=
  bv.lxor (T2 (bv.bin (bv.land a (bv.of_N 3)))) (bv.shiftr a sh2).

Lemma bin_land3_mod (a : bv 32) :
  bv.bin (bv.land a (bv.of_N 3)) = bv.bin a mod 4.
Proof.
  unfold bv.land. rewrite bin_of_N32_mod.
  rewrite bin_of_N32_mod.
  change (3 mod 2 ^ 32) with 3.
  change 3 with (N.ones 2). rewrite N.land_ones.
  change (2 ^ 2) with 4.
  apply N.mod_small.
  pose proof (N.mod_upper_bound (bv.bin a) 4 ltac:(lia)).
  lia.
Qed.

Theorem mulx_mulx_fold (a : bv 32) : mulx (mulx a) = g2 a.
Proof.
  rewrite mulx_spec.
  rewrite mulx_spec.
  unfold g2. rewrite bin_land3_mod.
  (* bit 0 of the first round's output is bit 1 of a
     (bit 0 of both R32 and zero is 0) *)
  assert (B0 : bit (bv.lxor (if bit a 0 then R32 else bv.zero)
                            (bv.shiftr a sh1)) 0 = bit a 1).
  { rewrite bit_lxor, bit_shiftr.
    change (bv.bin sh1) with 1. change (0 + 1) with 1.
    destruct (bit a 0).
    - replace (bit R32 0) with false by reflexivity.
      apply Bool.xorb_false_l.
    - rewrite bit_zero. apply Bool.xorb_false_l. }
  rewrite B0.
  (* case on the low two bits of a *)
  assert (Hm4 : bv.bin a mod 4 < 4) by (apply N.mod_upper_bound; lia).
  assert (Hb0 : bit a 0 = N.testbit (bv.bin a mod 4) 0)
    by (unfold bit; change 4 with (2 ^ 2);
        now rewrite N.mod_pow2_bits_low by lia).
  assert (Hb1 : bit a 1 = N.testbit (bv.bin a mod 4) 1)
    by (unfold bit; change 4 with (2 ^ 2);
        now rewrite N.mod_pow2_bits_low by lia).
  (* abstract the mod term first: lia's zify chokes on N-mod atoms
     (same family as the gmap-pitfalls Zify-vs-lia gotcha) *)
  remember (bv.bin a mod 4) as m eqn:Hm in *. clear Hm.
  assert (Hcases : m = 0 \/ m = 1 \/ m = 2 \/ m = 3) by lia.
  destruct Hcases as [H4|[H4|[H4|H4]]];
    rewrite H4 in Hb0, Hb1 |- *; cbn in Hb0, Hb1;
    rewrite Hb0, Hb1;
    rewrite shiftr_lxor, shiftr_shiftr_1_1, <- lxor_assoc;
    f_equal; vm_compute; reflexivity.
Qed.

(* T2 sanity check against the hand-derived values in the plan. *)
Goal T2 1 = bv.of_N 0x70800000. Proof. reflexivity. Qed.
Goal T2 2 = bv.of_N 0xE1000000. Proof. reflexivity. Qed.
Goal T2 3 = bv.of_N 0x91800000. Proof. reflexivity. Qed.
