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
     Strings.String
     ZArith.ZArith.
From bbv Require
     Word.
From Equations Require Import
     Equations.
From Katamaran Require Export
     Environment
     Prelude
     Tactics
     Syntax.TypeKit
     Syntax.Variables.

Import ctx.notations.

Local Set Implicit Arguments.
Local Set Transparent Obligations.
Local Unset Elimination Schemes.

Inductive Bit : Set := bitzero | bitone.

Definition Bit_eqb (b1 : Bit) (b2 : Bit) : bool :=
  match b1, b2 with
  | bitzero, bitzero => true
  | bitone , bitone  => true
  | _      , _       => false
  end.

Lemma Bit_eqb_spec (b1 b2 : Bit) : reflect (b1 = b2) (Bit_eqb b1 b2).
Proof. destruct b1, b2; cbn; constructor; congruence. Qed.

Module Type TypeCodeOn (Import typekit : TypeKit).

  Inductive Ty : Set :=
  | ty_int
  | ty_bool
  | ty_bit
  | ty_string
  | ty_list (σ : Ty)
  | ty_prod (σ τ : Ty)
  | ty_sum  (σ τ : Ty)
  | ty_unit
  | ty_enum (E : 𝑬)
  | ty_bvec (n : nat)
  | ty_tuple (σs : Ctx Ty)
  | ty_union (U : 𝑼)
  | ty_record (R : 𝑹)
  .

  (* convenience definition. *)
  Definition ty_option : Ty -> Ty := fun T => ty_sum T ty_unit.

  Derive NoConfusion for Ty.

  Section Ty_rect.
    Variable P  : Ty -> Type.

    Hypothesis (P_int    : P ty_int).
    Hypothesis (P_bool   : P ty_bool).
    Hypothesis (P_bit    : P ty_bit).
    Hypothesis (P_string : P ty_string).
    Hypothesis (P_list   : forall σ, P σ -> P (ty_list σ)).
    Hypothesis (P_prod   : forall σ τ, P σ -> P τ -> P (ty_prod σ τ)).
    Hypothesis (P_sum    : forall σ τ, P σ -> P τ -> P (ty_sum σ τ)).
    Hypothesis (P_unit   : P ty_unit).
    Hypothesis (P_enum   : forall E, P (ty_enum E)).
    Hypothesis (P_bvec   : forall n, P (ty_bvec n)).
    Hypothesis (P_tuple  : forall σs, EnvRec P σs -> P (ty_tuple σs)).
    Hypothesis (P_union  : forall U, P (ty_union U)).
    Hypothesis (P_record : forall R, P (ty_record R)).

    Fixpoint Ty_rect (σ : Ty) : P σ :=
      match σ with
      | ty_int      => ltac:(apply P_int)
      | ty_bool     => ltac:(apply P_bool)
      | ty_bit      => ltac:(apply P_bit)
      | ty_string   => ltac:(apply P_string)
      | ty_list σ   => ltac:(apply P_list; auto)
      | ty_prod σ τ => ltac:(apply P_prod; auto)
      | ty_sum σ τ  => ltac:(apply P_sum; auto)
      | ty_unit     => ltac:(apply P_unit; auto)
      | ty_enum E   => ltac:(apply P_enum; auto)
      | ty_bvec n   => ltac:(apply P_bvec; auto)
      | ty_tuple σs => ltac:(apply P_tuple; induction σs; cbn; auto using unit)
      | ty_union U  => ltac:(apply P_union; auto)
      | ty_record R => ltac:(apply P_record; auto)
      end.

  End Ty_rect.

  Definition Ty_rec (P : Ty -> Set) := Ty_rect P.
  Definition Ty_ind (P : Ty -> Prop) := Ty_rect P.

  Instance Ty_eq_dec : EqDec Ty :=
    fix ty_eqdec (σ τ : Ty) {struct σ} : dec_eq σ τ :=
      match σ , τ with
      | ty_int        , ty_int        => left eq_refl
      | ty_bool       , ty_bool       => left eq_refl
      | ty_bit        , ty_bit        => left eq_refl
      | ty_string     , ty_string     => left eq_refl
      | ty_list σ     , ty_list τ     => f_equal_dec ty_list noConfusion_inv (ty_eqdec σ τ)
      | ty_prod σ1 σ2 , ty_prod τ1 τ2 => f_equal2_dec ty_prod noConfusion_inv (ty_eqdec σ1 τ1) (ty_eqdec σ2 τ2)
      | ty_sum σ1 σ2  , ty_sum τ1 τ2  => f_equal2_dec ty_sum noConfusion_inv (ty_eqdec σ1 τ1) (ty_eqdec σ2 τ2)
      | ty_unit       , ty_unit       => left eq_refl
      | ty_enum E1    , ty_enum E2    => f_equal_dec ty_enum noConfusion_inv (eq_dec E1 E2)
      | ty_bvec n1    , ty_bvec n2    => f_equal_dec ty_bvec noConfusion_inv (eq_dec n1 n2)
      | ty_tuple σs   , ty_tuple τs   => f_equal_dec
                                           ty_tuple noConfusion_inv
                                           (eq_dec (EqDec := ctx.eq_dec_ctx ty_eqdec) σs τs)
      | ty_union U1   , ty_union U2   => f_equal_dec ty_union noConfusion_inv (eq_dec U1 U2)
      | ty_record R1  , ty_record R2  => f_equal_dec ty_record noConfusion_inv (eq_dec R1 R2)
      | _             , _             => right noConfusion_inv
      end.

  (* Lemma Ty_K (σ : Ty) (p : σ = σ) : p = eq_refl. *)
  (* Proof. apply uip. Qed. *)

End TypeCodeOn.

Module Type TypeExtOn (Import TK : TypeKit) (Import TY : TypeCodeOn TK).

  Fixpoint Val (σ : Ty) : Set :=
    match σ with
    | ty_int => Z
    | ty_bool => bool
    | ty_bit => Bit
    | ty_string => string
    | ty_list σ' => list (Val σ')
    | ty_prod σ1 σ2 => Val σ1 * Val σ2
    | ty_sum σ1 σ2 => Val σ1 + Val σ2
    | ty_unit => unit
    | ty_enum E => 𝑬𝑲 E
    | ty_bvec n => Word.word n
    | ty_tuple σs => EnvRec Val σs
    | ty_union U => 𝑼𝑻 U
    | ty_record R => 𝑹𝑻 R
    end%type.
  Bind Scope exp_scope with Val.

  Fixpoint Val_eqb (σ : Ty) : forall (l1 l2 : Val σ), bool :=
    match σ return Val σ -> Val σ -> bool with
    | ty_int      => Z.eqb
    | ty_bool     => Bool.eqb
    | ty_bit      => Bit_eqb
    | ty_string   => String.eqb
    | ty_list σ   => list_beq (Val_eqb σ)
    | ty_prod σ τ => prod_beq (Val_eqb σ) (Val_eqb τ)
    | ty_sum σ τ  => sum_beq (Val_eqb σ) (Val_eqb τ)
    | ty_unit     => fun _ _ => true
    | ty_enum E   => fun l1 l2 => if eq_dec l1 l2 then true else false
    | ty_bvec n   => @Word.weqb n
    | ty_tuple σs => envrec.eqb Val_eqb
    | ty_union U  => fun l1 l2 => if eq_dec l1 l2 then true else false
    | ty_record R => fun l1 l2 => if eq_dec l1 l2 then true else false
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
    - destruct (eq_dec x y)...
    - apply iff_reflect. symmetry.
      apply (Word.weqb_true_iff x y).
    - induction σs; intros.
      + destruct x; destruct y...
      + cbn in *.
        destruct x as [xs x]; destruct y as [ys y]; destruct X as [pσs pb]; cbn in *.
        specialize (IHσs pσs).
        destruct (IHσs xs ys); destruct (pb x y)...
    - destruct (eq_dec x y)...
    - destruct (eq_dec x y)...
  Qed.

  (* TODO: deprecate tuple projections *)
  Fixpoint tuple_proj (σs : Ctx Ty) (n : nat) (σ : Ty) :
    Val (ty_tuple σs) -> ctx.nth_is σs n σ -> Val σ :=
    match σs with
    | ctx.nil =>
        fun l (p : ctx.nth_is ctx.nil _ _) =>
          match p with end
    | ctx.snoc τs τ =>
        match n with
        | 0   => fun (l : Val (ty_tuple (ctx.snoc _ _)))
                     (p : ctx.nth_is _ 0 _) =>
                   @eq_rect Ty τ Val (snd l) σ p
        | S m => fun l p => tuple_proj τs m σ (fst l) p
        end
    end.

End TypeExtOn.

Module Type BinopsOn (Import TK : TypeKit) (Import TY : TypeCodeOn TK).

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

  Derive Signature NoConfusion for BinOp.

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
  Instance binop_eq_dec {σ1 σ2 σ3} : EqDec (BinOp σ1 σ2 σ3).
  Proof.
    intros x y.
    destruct (binoptel_eq_dec x y) as [p|p].
    - left. dependent elimination p. reflexivity.
    - right. congruence.
  Defined.

End BinopsOn.

Module Type BinopEvalOn (Import TK  : TypeKit) (Import TY  : TypeCodeOn TK)
       (Import LIT : TypeExtOn TK TY) (Import BOP : BinopsOn TK TY).

  Definition eval_binop {σ1 σ2 σ3 : Ty} (op : BinOp σ1 σ2 σ3) : Val σ1 -> Val σ2 -> Val σ3 :=
    match op with
    | binop_plus       => Z.add
    | binop_times      => Z.mul
    | binop_minus      => Z.sub
    | binop_eq         => Z.eqb
    | binop_le         => Z.leb
    | binop_lt         => Z.ltb
    | binop_ge         => Z.geb
    | binop_gt         => Z.gtb
    | binop_and        => andb
    | binop_or         => fun v1 v2 => orb v1 v2
    | binop_pair       => pair
    | binop_cons       => cons
    | binop_append     => app
    | binop_tuple_snoc => pair
    | binop_bvplus     => fun v1 v2 => Word.wplus v1 v2
    | binop_bvmult     => fun v1 v2 => Word.wmult v1 v2
    | binop_bvcombine  => fun v1 v2 => Word.combine v1 v2
    | binop_bvcons     => fun b bs => Word.WS (Bit_eqb b bitone) bs
    end.

End BinopEvalOn.

Module Type TypesOn (TK : TypeKit) :=
  TypeCodeOn TK <+ TypeExtOn TK <+ BinopsOn TK <+ BinopEvalOn TK.

Module Type Types.
  Declare Module Export VAR : VarKit.
  Declare Module Export TK : TypeKit.TypeKit.
  Include TypeCodeOn TK <+ TypeExtOn TK <+ BinopsOn TK <+ BinopEvalOn TK.

  Notation PCtx := (NCtx 𝑿 Ty).
  Notation LCtx := (NCtx 𝑺 Ty).
End Types.

Module MakeTypes (Export VAR' : VarKit) (Export TK' : TypeKit) <: Types. (* with Module TK := TK'. *)
  Module VAR := VAR'.
  Module TK := TK'.
  Include TypeCodeOn TK <+ TypeExtOn TK <+ BinopsOn TK <+ BinopEvalOn TK.

  Notation PCtx := (NCtx 𝑿 Ty).
  Notation LCtx := (NCtx 𝑺 Ty).
End MakeTypes.
