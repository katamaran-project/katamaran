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
     ZArith.BinInt.
From Equations Require Import
     Equations.
From stdpp Require
     finite.
From Katamaran Require Export
     Bitvector.
From Katamaran Require Import
     Prelude
     Context
     Environment
     Tactics.

Local Set Implicit Arguments.
Local Set Transparent Obligations.

Import ctx.notations.

Module Type EnumTypeDeclKit.
  (* Names of enum type constructors. *)
  Parameter Inline 𝑬 : Set. (* input: \MIE *)
  Declare Instance 𝑬_eq_dec : EqDec 𝑬.
  (* Names of enum data constructors. *)
  Parameter Inline 𝑬𝑲 : 𝑬 -> Set.
  Declare Instance 𝑬𝑲_eq_dec : forall (e : 𝑬), EqDec (𝑬𝑲 e).
  Declare Instance 𝑬𝑲_finite : forall E, finite.Finite (𝑬𝑲 E).
End EnumTypeDeclKit.

Module Type UnionTypeDeclKit.
  (* Names of union type constructors. *)
  Parameter Inline 𝑼   : Set. (* input: \MIU *)
  Declare Instance 𝑼_eq_dec : EqDec 𝑼.
  (* Union types. *)
  Parameter Inline 𝑼𝑻  : 𝑼 -> Set.
  Declare Instance 𝑼𝑻_eq_dec : forall (u : 𝑼), EqDec (𝑼𝑻 u).
  (* Names of union data constructors. *)
  Parameter Inline 𝑼𝑲  : 𝑼 -> Set.
  Declare Instance 𝑼𝑲_eq_dec : forall (u : 𝑼), EqDec (𝑼𝑲 u).
  Declare Instance 𝑼𝑲_finite : forall U, finite.Finite (𝑼𝑲 U).
End UnionTypeDeclKit.

Module Type RecordTypeDeclKit.
  (* Names of record type constructors. *)
  Parameter Inline 𝑹  : Set. (* input: \MIR *)
  Declare Instance 𝑹_eq_dec : EqDec 𝑹.
  (* Record types. *)
  Parameter Inline 𝑹𝑻  : 𝑹 -> Set.
  Declare Instance 𝑹𝑻_eq_dec : forall (r : 𝑹), EqDec (𝑹𝑻 r).
End RecordTypeDeclKit.

Module Type TypeDeclKit :=
  EnumTypeDeclKit <+ UnionTypeDeclKit <+ RecordTypeDeclKit.

Module NoEnums <: EnumTypeDeclKit.
  Definition 𝑬          := Empty_set.
  Definition 𝑬𝑲 (E : 𝑬) := Empty_set.

  Instance 𝑬_eq_dec : EqDec 𝑬 := Empty_set_EqDec.
  Instance 𝑬𝑲_eq_dec (E : 𝑬) : EqDec (𝑬𝑲 E)  := Empty_set_EqDec.
  Instance 𝑬𝑲_finite (E : 𝑬) : finite.Finite (𝑬𝑲 E) := finite.Empty_set_finite.
End NoEnums.

Module NoUnions <: UnionTypeDeclKit.
  Definition 𝑼          := Empty_set.
  Definition 𝑼𝑻 (U : 𝑼) := Empty_set.
  Definition 𝑼𝑲 (U : 𝑼) := Empty_set.

  Instance 𝑼_eq_dec : EqDec 𝑼 := Empty_set_EqDec.
  Instance 𝑼𝑻_eq_dec (U : 𝑼) : EqDec (𝑼𝑻 U)  := Empty_set_EqDec.
  Instance 𝑼𝑲_eq_dec (U : 𝑼) : EqDec (𝑼𝑲 U)  := Empty_set_EqDec.
  Instance 𝑼𝑲_finite (U : 𝑼) : finite.Finite (𝑼𝑲 U) := finite.Empty_set_finite.
End NoUnions.

Module NoRecords <: RecordTypeDeclKit.
  Definition 𝑹          := Empty_set.
  Definition 𝑹𝑻 (R : 𝑹) := Empty_set.
  Instance 𝑹_eq_dec : EqDec 𝑹 := Empty_set_EqDec.
  Instance 𝑹𝑻_eq_dec (R : 𝑹) : EqDec (𝑹𝑻 R) := Empty_set_EqDec.
End NoRecords.

Module DefaultTypeDeclKit <: TypeDeclKit :=
  NoEnums <+ NoUnions <+ NoRecords.

Module Type TypeCodeMixin (Import TK : TypeDeclKit).

  Local Unset Elimination Schemes.

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
    Local Unset Implicit Arguments.
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
    Hypothesis (P_tuple  : forall σs (IH : ctx.All P σs), P (ty_tuple σs)).
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
      | ty_tuple σs => ltac:(apply P_tuple, ctx.all_intro, Ty_rect)
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

End TypeCodeMixin.

(* TODO: Move me *)
Inductive Bit : Set := bitone | bitzero.

Definition Bit_eqb (b1 : Bit) (b2 : Bit) : bool :=
  match b1, b2 with
  | bitone , bitone  => true
  | bitzero, bitzero => true
  | _      , _       => false
  end.

Lemma Bit_eqb_spec (b1 b2 : Bit) : reflect (b1 = b2) (Bit_eqb b1 b2).
Proof. destruct b1, b2; cbn; constructor; congruence. Qed.

Module Type TypeDenoteMixin (Import TK : TypeDeclKit) (Import TC : TypeCodeMixin TK).

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
    | ty_bvec n => bv n
    | ty_tuple σs => EnvRec Val σs
    | ty_union U => 𝑼𝑻 U
    | ty_record R => 𝑹𝑻 R
    end%type.
  Bind Scope exp_scope with Val.

  Fixpoint Val_eqb (σ : Ty) : forall (v1 v2 : Val σ), bool :=
    match σ return Val σ -> Val σ -> bool with
    | ty_int      => Z.eqb
    | ty_bool     => Bool.eqb
    | ty_bit      => Bit_eqb
    | ty_string   => String.eqb
    | ty_list σ   => list_beq (Val_eqb σ)
    | ty_prod σ τ => prod_beq (Val_eqb σ) (Val_eqb τ)
    | ty_sum σ τ  => sum_beq (Val_eqb σ) (Val_eqb τ)
    | ty_unit     => fun _ _ => true
    | ty_enum E   => fun v1 v2 => if eq_dec v1 v2 then true else false
    | ty_bvec n   => @bv.eqb n
    | ty_tuple σs => envrec.eqb Val_eqb
    | ty_union U  => fun v1 v2 => if eq_dec v1 v2 then true else false
    | ty_record R => fun v1 v2 => if eq_dec v1 v2 then true else false
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
    - apply bv.eqb_spec.
    - induction IH...
      + now destruct x, y.
      + destruct x as [xs x], y as [ys y]; destruct (p x y)...
    - destruct (eq_dec x y)...
    - destruct (eq_dec x y)...
  Qed.

End TypeDenoteMixin.

Module Type TypeDeclMixin (TK : TypeDeclKit) :=
  TypeCodeMixin TK <+ TypeDenoteMixin TK.
Module Type TypeDecl :=
  TypeDeclKit <+ TypeDeclMixin.
Module DefaultTypeDecl <: TypeDecl :=
  DefaultTypeDeclKit <+ TypeDeclMixin.

(* Record EnumTypeDeclKit : Type := *)
(*   { enum               : Set; *)
(*     enum_eq_dec        : EqDec enum; *)
(*     unmake              : enum -> Set; *)
(*     enumk_eq_dec E     : EqDec (enumk E); *)
(*     enumk_finite E     : finite.Finite (enumk E); *)
(*   }. *)

(* Record UnionTypeDeclKit : Type := *)
(*   { union              : Set; *)
(*     union_eq_dec       : EqDec union; *)
(*     uniont             : union -> Set; *)
(*     uniont_eq_dec U    : EqDec (uniont U); *)
(*     unionk             : union -> Set; *)
(*     unionk_eq_dec U    : EqDec (unionk U); *)
(*     unionk_finite U    : finite.Finite (unionk U); *)
(*   }. *)

(* Record RecordTypeDeclKit : Type := *)
(*   { record             : Set; *)
(*     record_eq_dec      : EqDec record; *)
(*     recordt            : record -> Set; *)
(*     recordt_eq_dec R   : EqDec (recordt R); *)
(*   }. *)

(* Record TypeDeclKit : Type := *)
(*   { enumtypekit   :> EnumTypeDeclKit; *)
(*     uniontypekit  :> UnionTypeDeclKit; *)
(*     recordtypekit :> RecordTypeDeclKit; *)
(*   }. *)

(* Existing Instance enum_eq_dec. *)
(* Existing Instance enumk_eq_dec. *)
(* Existing Instance union_eq_dec. *)
(* Existing Instance uniont_eq_dec. *)
(* Existing Instance unionk_eq_dec. *)
(* Existing Instance record_eq_dec. *)
(* Existing Instance recordt_eq_dec. *)

(* Inductive Bit : Set := bitzero | bitone. *)

(* Definition Bit_eqb (b1 : Bit) (b2 : Bit) : bool := *)
(*   match b1, b2 with *)
(*   | bitzero, bitzero => true *)
(*   | bitone , bitone  => true *)
(*   | _      , _       => false *)
(*   end. *)

(* Lemma Bit_eqb_spec (b1 b2 : Bit) : reflect (b1 = b2) (Bit_eqb b1 b2). *)
(* Proof. destruct b1, b2; cbn; constructor; congruence. Qed. *)

(* Section Types. *)
(*   Context {TK : TypeDeclKit}. *)

(*   Local Set Transparent Obligations. *)
(*   Local Unset Elimination Schemes. *)

(*   Inductive Ty : Set := *)
(*   | ty_int *)
(*   | ty_bool *)
(*   | ty_bit *)
(*   | ty_string *)
(*   | ty_list (σ : Ty) *)
(*   | ty_prod (σ τ : Ty) *)
(*   | ty_sum  (σ τ : Ty) *)
(*   | ty_unit *)
(*   | ty_enum (E : enum TK) *)
(*   | ty_bvec (n : nat) *)
(*   | ty_tuple (σs : Ctx Ty) *)
(*   | ty_union (U : union TK) *)
(*   | ty_record (R : record TK) *)
(*   . *)

(*   (* convenience definition. *) *)
(*   Definition ty_option : Ty -> Ty := fun T => ty_sum T ty_unit. *)

(*   Derive NoConfusion for Ty. *)

(*   Section Ty_rect. *)
(*     Variable P  : Ty -> Type. *)

(*     Hypothesis (P_int    : P ty_int). *)
(*     Hypothesis (P_bool   : P ty_bool). *)
(*     Hypothesis (P_bit    : P ty_bit). *)
(*     Hypothesis (P_string : P ty_string). *)
(*     Hypothesis (P_list   : forall σ, P σ -> P (ty_list σ)). *)
(*     Hypothesis (P_prod   : forall σ τ, P σ -> P τ -> P (ty_prod σ τ)). *)
(*     Hypothesis (P_sum    : forall σ τ, P σ -> P τ -> P (ty_sum σ τ)). *)
(*     Hypothesis (P_unit   : P ty_unit). *)
(*     Hypothesis (P_enum   : forall E, P (ty_enum E)). *)
(*     Hypothesis (P_bvec   : forall n, P (ty_bvec n)). *)
(*     Hypothesis (P_tuple  : forall σs (IH : forall σ, ctx.In σ σs -> P σ), P (ty_tuple σs)). *)
(*     Hypothesis (P_union  : forall U, P (ty_union U)). *)
(*     Hypothesis (P_record : forall R, P (ty_record R)). *)

(*     Fixpoint Ty_rect (σ : Ty) : P σ := *)
(*       match σ with *)
(*       | ty_int      => ltac:(apply P_int) *)
(*       | ty_bool     => ltac:(apply P_bool) *)
(*       | ty_bit      => ltac:(apply P_bit) *)
(*       | ty_string   => ltac:(apply P_string) *)
(*       | ty_list σ   => ltac:(apply P_list; auto) *)
(*       | ty_prod σ τ => ltac:(apply P_prod; auto) *)
(*       | ty_sum σ τ  => ltac:(apply P_sum; auto) *)
(*       | ty_unit     => ltac:(apply P_unit; auto) *)
(*       | ty_enum E   => ltac:(apply P_enum; auto) *)
(*       | ty_bvec n   => ltac:(apply P_bvec; auto) *)
(*       | ty_tuple σs => ltac:(apply P_tuple; *)
(*                              induction σs; cbn; intros ? xIn; *)
(*                              [ destruct (ctx.nilView xIn) | destruct (ctx.snocView xIn) ]; *)
(*                              [ apply Ty_rect | apply IHσs; auto ]) *)
(*       | ty_union U  => ltac:(apply P_union; auto) *)
(*       | ty_record R => ltac:(apply P_record; auto) *)
(*       end. *)

(*   End Ty_rect. *)

(*   Definition Ty_rec (P : Ty -> Set) := Ty_rect P. *)
(*   Definition Ty_ind (P : Ty -> Prop) := Ty_rect P. *)

(*   Instance Ty_eq_dec : EqDec Ty := *)
(*     fix ty_eqdec (σ τ : Ty) {struct σ} : dec_eq σ τ := *)
(*       match σ , τ with *)
(*       | ty_int        , ty_int        => left eq_refl *)
(*       | ty_bool       , ty_bool       => left eq_refl *)
(*       | ty_bit        , ty_bit        => left eq_refl *)
(*       | ty_string     , ty_string     => left eq_refl *)
(*       | ty_list σ     , ty_list τ     => f_equal_dec ty_list noConfusion_inv (ty_eqdec σ τ) *)
(*       | ty_prod σ1 σ2 , ty_prod τ1 τ2 => f_equal2_dec ty_prod noConfusion_inv (ty_eqdec σ1 τ1) (ty_eqdec σ2 τ2) *)
(*       | ty_sum σ1 σ2  , ty_sum τ1 τ2  => f_equal2_dec ty_sum noConfusion_inv (ty_eqdec σ1 τ1) (ty_eqdec σ2 τ2) *)
(*       | ty_unit       , ty_unit       => left eq_refl *)
(*       | ty_enum E1    , ty_enum E2    => f_equal_dec ty_enum noConfusion_inv (eq_dec E1 E2) *)
(*       | ty_bvec n1    , ty_bvec n2    => f_equal_dec ty_bvec noConfusion_inv (eq_dec n1 n2) *)
(*       | ty_tuple σs   , ty_tuple τs   => f_equal_dec *)
(*                                            ty_tuple noConfusion_inv *)
(*                                            (eq_dec (EqDec := ctx.eq_dec_ctx ty_eqdec) σs τs) *)
(*       | ty_union U1   , ty_union U2   => f_equal_dec ty_union noConfusion_inv (eq_dec U1 U2) *)
(*       | ty_record R1  , ty_record R2  => f_equal_dec ty_record noConfusion_inv (eq_dec R1 R2) *)
(*       | _             , _             => right noConfusion_inv *)
(*       end. *)

(*   (* Lemma Ty_K (σ : Ty) (p : σ = σ) : p = eq_refl. *) *)
(*   (* Proof. apply uip. Qed. *) *)

(*   Fixpoint Val (σ : Ty) : Set := *)
(*     match σ with *)
(*     | ty_int => Z *)
(*     | ty_bool => bool *)
(*     | ty_bit => Bit *)
(*     | ty_string => string *)
(*     | ty_list σ' => list (Val σ') *)
(*     | ty_prod σ1 σ2 => Val σ1 * Val σ2 *)
(*     | ty_sum σ1 σ2 => Val σ1 + Val σ2 *)
(*     | ty_unit => unit *)
(*     | ty_enum E => enumk _ E *)
(*     | ty_bvec n => Word.word n *)
(*     | ty_tuple σs => EnvRec Val σs *)
(*     | ty_union U => uniont _ U *)
(*     | ty_record R => recordt _ R *)
(*     end%type. *)
(*   Bind Scope exp_scope with Val. *)

(*   Fixpoint Val_eqb (σ : Ty) : forall (v1 v2 : Val σ), bool := *)
(*     match σ return Val σ -> Val σ -> bool with *)
(*     | ty_int      => Z.eqb *)
(*     | ty_bool     => Bool.eqb *)
(*     | ty_bit      => Bit_eqb *)
(*     | ty_string   => String.eqb *)
(*     | ty_list σ   => list_beq (Val_eqb σ) *)
(*     | ty_prod σ τ => prod_beq (Val_eqb σ) (Val_eqb τ) *)
(*     | ty_sum σ τ  => sum_beq (Val_eqb σ) (Val_eqb τ) *)
(*     | ty_unit     => fun _ _ => true *)
(*     | ty_enum E   => fun v1 v2 => if eq_dec v1 v2 then true else false *)
(*     | ty_bvec n   => @Word.weqb n *)
(*     | ty_tuple σs => envrec.eqb Val_eqb *)
(*     | ty_union U  => fun v1 v2 => if eq_dec v1 v2 then true else false *)
(*     | ty_record R => fun v1 v2 => if eq_dec v1 v2 then true else false *)
(*     end. *)

(*   Import ctx.notations. *)

(*   Lemma Val_eqb_spec (σ : Ty) (x y : Val σ) : reflect (x = y) (Val_eqb σ x y). *)
(*   Proof with solve_eqb_spec. *)
(*     induction σ; cbn. *)
(*     - apply Z.eqb_spec. *)
(*     - apply Bool.eqb_spec. *)
(*     - apply Bit_eqb_spec. *)
(*     - apply String.eqb_spec. *)
(*     - apply list_beq_spec; auto. *)
(*     - destruct x as [x1 x2]; destruct y as [y1 y2]... *)
(*     - destruct x as [x1|x2]; destruct y as [y1|y2]... *)
(*     - destruct x. destruct y... *)
(*     - destruct (eq_dec x y)... *)
(*     - apply iff_reflect. symmetry. *)
(*       apply (Word.weqb_true_iff x y). *)
(*     - induction σs; cbn in *. *)
(*       + constructor. now destruct x, y. *)
(*       + destruct x as [xs x]; destruct y as [ys y]. *)
(*         assert (forall σ : Ty, σ ∈ σs -> forall x y : Val σ, reflect (x = y) (Val_eqb σ x y)) as IH' *)
(*             by (intros ? ?; now apply IH, ctx.in_succ). *)
(*         specialize (IH _ ctx.in_zero x y). *)
(*         specialize (IHσs IH' xs ys)... *)
(*     - destruct (eq_dec x y)... *)
(*     - destruct (eq_dec x y)... *)
(*   Qed. *)

(* End Types. *)
