(******************************************************************************)
(* Copyright (c) 2023 Steven Keuchel                                          *)
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
  NArith.BinNat
  ZArith.BinInt.
From Equations Require Import
  Equations.
From Katamaran Require Import
  Bitvector
  Context
  Prelude
  Syntax.TypeDecl.

Import ctx.notations.

Local Set Implicit Arguments.
Local Set Transparent Obligations.

Module uop.

  Import ty.

  Section WithTypeDecl.
    Context {TDC : TypeDeclKit}.

    Variant UnOp : Ty -> Ty -> Set :=
    | inl {σ1 σ2 : Ty}  : UnOp σ1 (sum σ1 σ2)
    | inr {σ1 σ2 : Ty}  : UnOp σ2 (sum σ1 σ2)
    | neg               : UnOp int int
    | not               : UnOp bool bool
    | rev {σ}           : UnOp (ty.list σ) (ty.list σ)
    | sext {m n} {p : IsTrue (m <=? n)} : UnOp (bvec m) (bvec n)
    | zext {m n} {p : IsTrue (m <=? n)} : UnOp (bvec m) (bvec n)
    | get_slice_int {n} : UnOp int (bvec n)
    | signed {n}        : UnOp (bvec n) int
    | unsigned {n}      : UnOp (bvec n) int
    | truncate {n} (m : nat) {p : IsTrue (m <=? n)} : UnOp (bvec n) (bvec m)
    | vector_subrange {n} (s l : nat) {p : IsTrue (s + l <=? n)} : UnOp (bvec n) (bvec l)
    | bvnot {n}         : UnOp (bvec n) (bvec n)
    | bvdrop m {n}      : UnOp (bvec (m + n)) (bvec n)
    | bvtake m {n}      : UnOp (bvec (m + n)) (bvec m)
    | negate {n}        : UnOp (bvec n) (bvec n)
    (* select_last_k x = XOR over i=0..k-1 of (bit_i(x) ? (R >> i) : 0),
       specialized to the fixed constant R = 0xE1000000 (RiscvPmp's
       "mulx"/key-schedule masking constant). NOT a generic multi-bit
       select: R's 24 trailing zero bits are exactly what make this
       collapse to a clean per-bit selection with no carry/wraparound; a
       different constant would need a genuine GF(2) reduction instead.
       See PLAN-solver-fold.md and skill project_key_schedule_loop_scaling. *)
    | select_last_k (k : nat) : UnOp (bvec 32) (bvec 32).
    Set Transparent Obligations.
    Derive Signature for UnOp.
    Derive NoConfusion for UnOp.

  End WithTypeDecl.

  Section WithTypeDef.
    Context {TDC : TypeDeclKit}.
    Context {TDN : TypeDenoteKit TDC}.
    Context {TDF : TypeDefKit TDN}.

    #[local] Set Equations With UIP.

    Definition Tel (τ : Ty) : Set :=
      sigma (fun σ : Ty => UnOp σ τ).

    Lemma eq_tel_bvdrop_inv {m1 m2 n} (H : m1 <> m2) :
      sigmaI (fun σ => UnOp σ (bvec n)) (bvec (m1 + n)) (bvdrop m1) <>
      sigmaI (fun σ => UnOp σ (bvec n)) (bvec (m2 + n)) (bvdrop m2).
    Proof. intros e%(f_equal pr1). cbn in e. depelim e. Lia.lia. Qed.

    Lemma eq_tel_bvtake_inv {m n1 n2} (H : n1 <> n2) :
      sigmaI (fun σ => UnOp σ (bvec m)) (bvec (m + n1)) (bvtake m) <>
      sigmaI (fun σ => UnOp σ (bvec m)) (bvec (m + n2)) (bvtake m).
    Proof. intros e%(f_equal pr1). cbn in e. depelim e. Lia.lia. Qed.

    Obligation Tactic := cbn; intros;
      try solve
        [eauto using eq_tel_bvdrop_inv, eq_tel_bvtake_inv
        |let e := fresh in intro e; depelim e; try easy;
         try progress cbn in * |-; congruence
        |subst; repeat f_equal; apply IsTrue.proof_irrelevance
        ].

    #[derive(equations=no)] Equations tel_eq_dec {σ1 σ2 τ : Ty}
      (op1 : UnOp σ1 τ) (op2 : UnOp σ2 τ) :
      dec_eq (A := Tel τ) (sigmaI _ σ1 op1) (sigmaI _ σ2 op2) :=
    | inl                              | inl => left eq_refl
    | inr                              | inr => left eq_refl
    | neg                              | neg => left eq_refl
    | not                              | not => left eq_refl
    | rev                              | rev => left eq_refl
    | @sext _ m1 ?(n) p1               | @sext _ m2 n p2 with eq_dec m1 m2 => {
      | left _ => left _
      | right _ => right _
      }
    | @zext _ m1 ?(n) p1               | @zext _ m2 n p2 with eq_dec m1 m2 => {
      | left _ => left _
      | right _ => right _
      }
    | get_slice_int                    | get_slice_int => left eq_refl
    | @unsigned _ m                    | @unsigned _ n with eq_dec m n => {
      | left _ => left _
      | right _ => right _
      }
    | @signed _ m                      | @signed _ n with eq_dec m n => {
      | left _ => left _
      | right _ => right _
      }
    | @truncate _ m1 ?(n) p1           | @truncate _ m2 n p2 with eq_dec m1 m2 => {
      | left _ => left _
      | right _ => right _
      }
    | @vector_subrange _ n1 s1 ?(l) p1 | @vector_subrange _ n2 s2 l p2 with eq_dec n1 n2, eq_dec s1 s2 => {
      | left _  | left _  => left _
      | left _  | right _ => right _
      | right _ | _       => right _
      }
    | bvnot                            | bvnot => left eq_refl
    | bvdrop m1                        | bvdrop m2 with eq_dec m1 m2 => {
      | left _ => left _
      | right _ => right _
      }
    | @bvtake _ ?(m) n1                | @bvtake _ m n2 with eq_dec n1 n2 => {
      | left _ => left _
      | right _ => right _
      }
    | negate                           | negate => left eq_refl
    | select_last_k k1                 | select_last_k k2 with eq_dec k1 k2 => {
      | left _ => left _
      | right _ => right _
      }
    | _                                | _ => right _.

    #[local] Instance eq_dec_unop [σ1 σ2] : EqDec (UnOp σ1 σ2) :=
      fun x y =>
        match tel_eq_dec x y with
        | left e => left
                      (* Uses decidable equality of Ty. *)
                      (inj_right_sigma _ _ _ e)
        | right b => right (fun e => b (f_equal _ e))
        end.

    (* select_last_k x = the correction term that k applications of "mulx"
       (mulx a = shiftr(a,1) xor (bit0(a) ? R : 0)) accumulate from x's low
       k bits, i.e. select_last_k k x = Correction_k(x) where the
       accumulator A_k := shiftr(x,k) xor Correction_k(x) must satisfy
       mulx(A_k) = A_(k+1). Unfolding mulx(A_k), its selector bit is
       bit0(A_k) = bit_k(x) xor bit0(Correction_k(x)) -- NOT bit_k(x)
       alone: the freshly-exposed bit and the low bit of whatever
       correction has already accumulated both flip mulx's conditional.
       So the recursion has to fold that xor back in each step:
         Correction_0(x)     = 0
         Correction_(k+1)(x) = shiftr(Correction_k(x), 1)
                                 xor ((bit_k(x) xor bit0(Correction_k(x)))
                                      ? R : 0).
       Dropping the "xor bit0(Correction_k(x))" term (i.e. just gating on
       bit_k(x)) LOOKS right and even compiles/verifies fine up to k=24 --
       it silently diverges from the true mulx^k(x) starting at k=25,
       exactly where R's own bit 24 (0xE1000000's lowest set bit) first
       surfaces into bit0 of the accumulated correction and starts
       affecting the selector. (An earlier version of this function had
       exactly that bug -- caught only by hand-deriving the k+1 step
       proof for PLAN-solver-fold.md's Phase 2, never by any test run so
       far, since every N validated to date is well under 25.) With the
       xor folded back in, this is an exact, unconditional replay of
       mulx's own per-round update, valid for any k. Only ever invoked
       concretely (runs once, in Gallina, when a concrete x is finally
       plugged in -- never unfolded into a Term), so its cost doesn't
       reintroduce the term-size blowup this primitive exists to avoid.
       See PLAN-solver-fold.md and project_key_schedule_loop_scaling. *)
    Definition select_last_k_R : bv 32 := bv.of_N 0xE1000000.

    Fixpoint select_last_k_eval_rec (bits : N) (k : nat) : bv 32 :=
      match k with
      | 0%nat => bv.zero
      | S k' =>
          let prev := select_last_k_eval_rec bits k' in
          let aged := bv.shiftr prev (@bv.of_N 5 1) in
          let sel  := xorb (N.testbit bits (N.of_nat k')) (N.testbit (bv.bin prev) 0) in
          if sel then bv.lxor aged select_last_k_R else aged
      end.

    Definition select_last_k_eval (k : nat) (x : bv 32) : bv 32 :=
      select_last_k_eval_rec (bv.bin x) k.

    Definition eval {σ1 σ2 : Ty} (op : UnOp σ1 σ2) : Val σ1 -> Val σ2 :=
      match op in UnOp σ1 σ2 return Val σ1 -> Val σ2 with
      | inl                 => Datatypes.inl
      | inr                 => Datatypes.inr
      | rev                 => @List.rev (Val _)
      | neg                 => Z.opp
      | not                 => negb
      | sext                => fun v => bv.sext v
      | zext                => fun v => bv.zext v
      | get_slice_int       => bv.of_Z
      | signed              => fun v => bv.signed v
      | unsigned            => fun v => bv.unsigned v
      | truncate m          => fun v => bv.truncate m v
      | vector_subrange s l => bv.vector_subrange s l
      | bvnot               => bv.not
      | bvdrop m            => bv.drop m
      | bvtake m            => bv.take m
      | negate              => bv.negate
      | select_last_k k     => select_last_k_eval k
      end.
    Global Arguments eval {σ1} {σ2} !op v.    

    Definition evalRel {σ1 σ2 : Ty} (op : UnOp σ1 σ2) : RelVal σ1 -> RelVal σ2 :=
      liftUnOp (eval op).
    Global Arguments evalRel {σ1} {σ2} !op !rv.

    Lemma comProjLeftRVEvalRel {σ1 σ2 : Ty} (op : UnOp σ1 σ2) (rv : RelVal σ1) :
      projLeftRV (evalRel op rv) = eval op (projLeftRV rv).
    Proof.
      unfold evalRel.
      apply comProjLeftRVLiftUnOpRV.
    Qed.

    Lemma comProjRightRVEvalRel {σ1 σ2 : Ty} (op : UnOp σ1 σ2) (rv : RelVal σ1) :
      projRightRV (evalRel op rv) = eval op (projRightRV rv).
    Proof.
      unfold evalRel.
      apply comProjRightRVLiftUnOpRV.
    Qed.

    Lemma comProjLeftEvalRel {σ1 σ2 : Ty} (op : UnOp σ1 σ2) (rv : RelVal σ1) :
      projLeft (evalRel op rv) = eval op (projLeft rv).
    Proof.
      unfold evalRel.
      apply comProjLeftLiftUnOp.
    Qed.

    Lemma comProjRightEvalRel {σ1 σ2 : Ty} (op : UnOp σ1 σ2) (rv : RelVal σ1) :
      projRight (evalRel op rv) = eval op (projRight rv).
    Proof.
      unfold evalRel.
      apply comProjRightLiftUnOp.
    Qed.

  End WithTypeDef.
  #[export] Existing Instance eq_dec_unop.

End uop.
#[export] Existing Instance uop.eq_dec_unop.
Export uop (UnOp).
