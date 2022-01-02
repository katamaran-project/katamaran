(******************************************************************************)
(* Copyright (c) 2019 Steven Keuchel                                          *)
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
     Bool.Bool
     ZArith.ZArith.
From Equations Require Import
     Equations.
From Katamaran Require Export
     Syntax.Types.

Import ctx.notations.

Local Set Implicit Arguments.

(******************************************************************************)

Module Type ValueKit.

  Declare Module typekit : TypeKit.
  Module Export TY := Types typekit.

  (* Union data constructor field type *)
  Parameter Inline 𝑼𝑲_Ty : forall (U : 𝑼), 𝑼𝑲 U -> Ty.
  Parameter Inline 𝑼_fold   : forall (U : 𝑼), { K : 𝑼𝑲 U & Val (𝑼𝑲_Ty K) } -> 𝑼𝑻 U.
  Parameter Inline 𝑼_unfold : forall (U : 𝑼), 𝑼𝑻 U -> { K : 𝑼𝑲 U & Val (𝑼𝑲_Ty K) }.
  Parameter Inline 𝑼_fold_unfold :
    forall (U : 𝑼) (Kv: 𝑼𝑻 U),
      𝑼_fold (𝑼_unfold Kv) = Kv.
  Parameter Inline 𝑼_unfold_fold :
    forall (U : 𝑼) (Kv: { K : 𝑼𝑲 U & Val (𝑼𝑲_Ty K) }),
      𝑼_unfold (𝑼_fold Kv) = Kv.

  (* Record field names. *)
  Parameter Inline 𝑹𝑭  : Set.
  (* Record field types. *)
  Parameter Inline 𝑹𝑭_Ty : 𝑹 -> NCtx 𝑹𝑭 Ty.
  Parameter Inline 𝑹_fold   : forall (R : 𝑹), NamedEnv Val (𝑹𝑭_Ty R) -> 𝑹𝑻 R.
  Parameter Inline 𝑹_unfold : forall (R : 𝑹), 𝑹𝑻 R -> NamedEnv Val (𝑹𝑭_Ty R).
  Parameter Inline 𝑹_fold_unfold :
    forall (R : 𝑹) (Kv: 𝑹𝑻 R),
      𝑹_fold (𝑹_unfold Kv) = Kv.
  Parameter Inline 𝑹_unfold_fold :
    forall (R : 𝑹) (Kv: NamedEnv Val (𝑹𝑭_Ty R)),
      𝑹_unfold (𝑹_fold Kv) = Kv.

End ValueKit.

Module Values (Export valuekit : ValueKit).

  Fixpoint Val_eqb (σ : Ty) : forall (l1 l2 : Val σ), bool :=
    match σ with
    | ty_int      => Z.eqb
    | ty_bool     => Bool.eqb
    | ty_bit      => Bit_eqb
    | ty_string   => String.eqb
    | ty_list σ   => list_beq (Val_eqb σ)
    | ty_prod σ τ => prod_beq (Val_eqb σ) (Val_eqb τ)
    | ty_sum σ τ  => sum_beq (Val_eqb σ) (Val_eqb τ)
    | ty_unit     => fun _ _ => true
    | ty_enum E   => fun l1 l2 => if 𝑬𝑲_eq_dec l1 l2 then true else false
    | ty_bvec n   => @Word.weqb n
    | ty_tuple σs => envrec.eqb Val_eqb
    | ty_union U  => fun l1 l2 => if 𝑼𝑻_eq_dec l1 l2 then true else false
    | ty_record R => fun l1 l2 => if 𝑹𝑻_eq_dec l1 l2 then true else false
    end.

  Lemma Val_eqb_spec (σ : Ty) (x y : Val σ) : reflect (x = y) (Val_eqb σ x y).
  Proof with solve_eqb_spec.
    induction σ; cbn.
    - apply Z.eqb_spec.
    - apply Bool.eqb_spec.
    - apply Bit_eqb_spec.
    - apply String.eqb_spec.
    - apply list_beq_spec; auto.
    - destruct x as [x1 x2]; destruct y as [y1 y2]...
    - destruct x as [x1|x2]; destruct y as [y1|y2]...
    - destruct x. destruct y...
    - destruct (𝑬𝑲_eq_dec x y)...
    - apply iff_reflect. symmetry.
      apply (Word.weqb_true_iff x y).
    - induction σs; intros.
      + destruct x; destruct y...
      + cbn in *.
        destruct x as [xs x]; destruct y as [ys y]; destruct X as [pσs pb]; cbn in *.
        specialize (IHσs pσs).
        destruct (IHσs xs ys); destruct (pb x y)...
    - destruct (𝑼𝑻_eq_dec x y)...
    - destruct (𝑹𝑻_eq_dec x y)...
  Qed.

  Lemma 𝑼_fold_inj {U} (v1 v2 : {K : 𝑼𝑲 U & Val (𝑼𝑲_Ty K)}) :
    𝑼_fold v1 = 𝑼_fold v2 <-> v1 = v2.
  Proof.
    split; try congruence. intros H.
    apply (f_equal (@𝑼_unfold U)) in H.
    now rewrite ?𝑼_unfold_fold in H.
  Qed.

  Lemma 𝑼_unfold_inj {U} (v1 v2 : Val (ty_union U)) :
    𝑼_unfold v1 = 𝑼_unfold v2 <-> v1 = v2.
  Proof.
    split; try congruence. intros H.
    apply (f_equal (@𝑼_fold U)) in H.
    now rewrite ?𝑼_fold_unfold in H.
  Qed.

  Fixpoint tuple_proj (σs : Ctx Ty) (n : nat) (σ : Ty) :
    Val (ty_tuple σs) -> ctx.nth_is σs n σ -> Val σ :=
    match σs with
    | ε      => fun l (p : ctx.nth_is ε _ _) =>
                  match p with end
    | τs ▻ τ => match n with
                | 0   => fun (l : Val (ty_tuple (_ ▻ _)))
                             (p : ctx.nth_is _ 0 _) =>
                           @eq_rect Ty τ Val (snd l) σ p
                | S m => fun l p => tuple_proj τs m σ (fst l) p
                end
    end.

  Section BinaryOperations.

    Inductive BinOp : Ty -> Ty -> Ty -> Set :=
    | binop_plus              : BinOp ty_int ty_int ty_int
    | binop_times             : BinOp ty_int ty_int ty_int
    | binop_minus             : BinOp ty_int ty_int ty_int
    | binop_eq                : BinOp ty_int ty_int ty_bool
    | binop_le                : BinOp ty_int ty_int ty_bool
    | binop_lt                : BinOp ty_int ty_int ty_bool
    | binop_ge                : BinOp ty_int ty_int ty_bool
    | binop_gt                : BinOp ty_int ty_int ty_bool
    | binop_and               : BinOp ty_bool ty_bool ty_bool
    | binop_or                : BinOp ty_bool ty_bool ty_bool
    | binop_pair {σ1 σ2 : Ty} : BinOp σ1 σ2 (ty_prod σ1 σ2)
    | binop_cons {σ : Ty}     : BinOp σ (ty_list σ) (ty_list σ)
    | binop_append {σ : Ty}   : BinOp (ty_list σ) (ty_list σ) (ty_list σ)
    | binop_tuple_snoc {σs σ} : BinOp (ty_tuple σs) σ (ty_tuple (σs ▻ σ))
    | binop_bvplus {n}        : BinOp (ty_bvec n) (ty_bvec n) (ty_bvec n)
    | binop_bvmult {n}        : BinOp (ty_bvec n) (ty_bvec n) (ty_bvec n)
    | binop_bvcombine {m n}   : BinOp (ty_bvec m) (ty_bvec n) (ty_bvec (m + n))
    | binop_bvcons {m}        : BinOp (ty_bit) (ty_bvec m) (ty_bvec (S m))
    .

    Local Set Transparent Obligations.
    Derive Signature NoConfusion for BinOp.
    Local Unset Transparent Obligations.

    Import Sigma_Notations.

    Definition BinOpTel : Set :=
      Σ i : (Σ σ1 σ2 : Ty, Ty), BinOp i.1 (i.2).1 (i.2).2.

    Definition binoptel_pair (σ1 σ2 : Ty) : BinOpTel :=
      ((σ1, σ2, ty_prod σ1 σ2), binop_pair).
    Definition binoptel_cons (σ : Ty) : BinOpTel :=
      ((σ, ty_list σ, ty_list σ), binop_cons).
    Definition binoptel_append (σ : Ty) : BinOpTel :=
      ((ty_list σ, ty_list σ, ty_list σ), binop_append).
    Definition binoptel_tuple_snoc (σs : Ctx Ty) (σ : Ty) : BinOpTel :=
      ((ty_tuple σs, σ, ty_tuple (σs ▻ σ)), binop_tuple_snoc).

    Definition binoptel_eq_dec {σ1 σ2 σ3 τ1 τ2 τ3}
      (op1 : BinOp σ1 σ2 σ3) (op2 : BinOp τ1 τ2 τ3) :
      dec_eq (A := BinOpTel) ((σ1,σ2,σ3),op1) ((τ1,τ2,τ3),op2) :=
      match op1 , op2 with
      | binop_plus  , binop_plus   => left eq_refl
      | binop_times , binop_times  => left eq_refl
      | binop_minus , binop_minus  => left eq_refl
      | binop_eq    , binop_eq     => left eq_refl
      | binop_le    , binop_le     => left eq_refl
      | binop_lt    , binop_lt     => left eq_refl
      | binop_ge    , binop_ge     => left eq_refl
      | binop_gt    , binop_gt     => left eq_refl
      | binop_and   , binop_and    => left eq_refl
      | binop_or    , binop_or     => left eq_refl
      | @binop_pair σ1 σ2 , @binop_pair τ1 τ2   =>
        f_equal2_dec binoptel_pair noConfusion_inv (eq_dec σ1 τ1) (eq_dec σ2 τ2)
      | @binop_cons σ  , @binop_cons τ   =>
        f_equal_dec binoptel_cons noConfusion_inv (eq_dec σ τ)
      | @binop_append σ , @binop_append τ   =>
        f_equal_dec binoptel_append noConfusion_inv (eq_dec σ τ)
      | @binop_tuple_snoc σs σ , @binop_tuple_snoc τs τ =>
        f_equal2_dec binoptel_tuple_snoc noConfusion_inv (eq_dec σs τs) (eq_dec σ τ)
      | @binop_bvplus m , @binop_bvplus n =>
        f_equal_dec
          (fun n => ((ty_bvec n, ty_bvec n, ty_bvec n), binop_bvplus))
          noConfusion_inv (eq_dec m n)
      | @binop_bvmult m , @binop_bvmult n =>
        f_equal_dec
          (fun n => ((ty_bvec n, ty_bvec n, ty_bvec n), binop_bvmult))
          noConfusion_inv (eq_dec m n)
      | @binop_bvcombine m1 m2 , @binop_bvcombine n1 n2 =>
        f_equal2_dec
          (fun m n => ((ty_bvec m, ty_bvec n, ty_bvec (m+n)), binop_bvcombine))
          noConfusion_inv (eq_dec m1 n1) (eq_dec m2 n2)
      | @binop_bvcons m , @binop_bvcons n =>
        f_equal_dec
          (fun n => ((ty_bit, ty_bvec n, ty_bvec (S n)), binop_bvcons))
          noConfusion_inv (eq_dec m n)
      | _           , _            => right noConfusion_inv
      end.

    Inductive OpEq {σ1 σ2 σ3} (op1 : BinOp σ1 σ2 σ3) : forall τ1 τ2 τ3, BinOp τ1 τ2 τ3 -> Prop :=
    | opeq_refl : OpEq op1 op1.
    Derive Signature for OpEq.
    Global Arguments opeq_refl {_ _ _ _}.

    Lemma binop_eqdep_dec {σ1 σ2 σ3 τ1 τ2 τ3} (op1 : BinOp σ1 σ2 σ3) (op2 : BinOp τ1 τ2 τ3) :
      {OpEq op1 op2} + {~ OpEq op1 op2}.
    Proof.
      destruct (binoptel_eq_dec op1 op2).
      - left. dependent elimination e. constructor.
      - right. intro e. apply n. dependent elimination e. reflexivity.
    Defined.

    Local Set Equations With UIP.
    Global Instance binop_eq_dec {σ1 σ2 σ3} : EqDec (BinOp σ1 σ2 σ3).
    Proof.
      intros x y.
      destruct (binoptel_eq_dec x y) as [p|p].
      - left. dependent elimination p. reflexivity.
      - right. congruence.
    Defined.

    Definition eval_binop {σ1 σ2 σ3 : Ty} (op : BinOp σ1 σ2 σ3) : Val σ1 -> Val σ2 -> Val σ3 :=
      match op with
      | binop_plus      => Z.add
      | binop_times     => Z.mul
      | binop_minus     => Z.sub
      | binop_eq        => Z.eqb
      | binop_le        => Z.leb
      | binop_lt        => Z.ltb
      | binop_ge        => Z.geb
      | binop_gt        => Z.gtb
      | binop_and       => andb
      | binop_or        => fun v1 v2 => orb v1 v2
      | binop_pair      => pair
      | binop_cons      => cons
      | binop_append    => app
      | binop_tuple_snoc => pair
      | binop_bvplus    => fun v1 v2 => Word.wplus v1 v2
      | binop_bvmult    => fun v1 v2 => Word.wmult v1 v2
      | binop_bvcombine => fun v1 v2 => Word.combine v1 v2
      | binop_bvcons    => fun b bs => Word.WS (Bit_eqb b bitone) bs
      end.

  End BinaryOperations.

End Values.
