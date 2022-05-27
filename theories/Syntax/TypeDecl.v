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
     Tactics
     Syntax.Variables.

From Coq Require Import
     Bool.Bool
     Strings.String
     ZArith.BinInt.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Bitvector
     Context
     Prelude.
From Coq Require Import
     Strings.String
     ZArith.BinInt.
From Katamaran Require Import
     Context
     Environment
     Notations
     Prelude
     Syntax.Variables
     Tactics.

(* Local Set Transparent Obligations. *)
(* Local Unset Elimination Schemes. *)

Import ctx.notations.
Import env.notations.

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

Module ty.

  Class TypeDeclKit : Type :=
    { (* Type constructor names. *)
      enumi    : Set;           (* Names of enum type constructors. *)
      unioni   : Set;           (* Names of union type constructors. *)
      recordi  : Set;           (* Names of record type constructors. *)
    }.

  Section WithTypeDecl.

    Context {TK : TypeDeclKit}.

    Local Unset Elimination Schemes.
    Local Set Transparent Obligations.

    Inductive Ty : Set :=
    | int
    | bool
    | bit
    | string
    | list (σ : Ty)
    | prod (σ τ : Ty)
    | sum  (σ τ : Ty)
    | unit
    | enum (E : enumi)
    | bvec (n : nat)
    | tuple (σs : Ctx Ty)
    | union (U : unioni)
    | record (R : recordi)
    .
    Derive NoConfusion for Ty.

    (* convenience definition. *)
    Definition option : Ty -> Ty := fun T => sum T unit.

    Section Ty_rect.
      Variable P : Ty -> Type.

      Hypothesis (P_int    : P int).
      Hypothesis (P_bool   : P bool).
      Hypothesis (P_bit    : P bit).
      Hypothesis (P_string : P string).
      Hypothesis (P_list   : forall σ, P σ -> P (list σ)).
      Hypothesis (P_prod   : forall σ τ, P σ -> P τ -> P (prod σ τ)).
      Hypothesis (P_sum    : forall σ τ, P σ -> P τ -> P (sum σ τ)).
      Hypothesis (P_unit   : P unit).
      Hypothesis (P_enum   : forall E, P (enum E)).
      Hypothesis (P_bvec   : forall n, P (bvec n)).
      Hypothesis (P_tuple  : forall σs (IH : ctx.All P σs), P (tuple σs)).
      Hypothesis (P_union  : forall U, P (union U)).
      Hypothesis (P_record : forall R, P (record R)).

      Fixpoint Ty_rect (σ : Ty) : P σ :=
        match σ with
        | int      => ltac:(apply P_int)
        | bool     => ltac:(apply P_bool)
        | bit      => ltac:(apply P_bit)
        | string   => ltac:(apply P_string)
        | list σ   => ltac:(apply P_list; auto)
        | prod σ τ => ltac:(apply P_prod; auto)
        | sum σ τ  => ltac:(apply P_sum; auto)
        | unit     => ltac:(apply P_unit; auto)
        | enum E   => ltac:(apply P_enum; auto)
        | bvec n   => ltac:(apply P_bvec; auto)
        | tuple σs => ltac:(apply P_tuple, ctx.all_intro, Ty_rect)
        | union U  => ltac:(apply P_union; auto)
        | record R => ltac:(apply P_record; auto)
        end.

    End Ty_rect.

    Definition Ty_rec (P : Ty -> Set) := Ty_rect P.
    Definition Ty_ind (P : Ty -> Prop) := Ty_rect P.

  End WithTypeDecl.
  (* #[export] Existing Instance Ty_eq_dec. *)

  Class TypeDenoteKit (TDC : TypeDeclKit) : Type :=
    { (* Mapping enum type constructor names to enum types *)
      enumt   : enumi -> Set;
      (* Mapping union type constructor names to union types *)
      uniont  : unioni -> Set;
      (* Mapping record type constructor names to record types *)
      recordt : recordi -> Set;
    }.

  Section WithTypeDenote.

    Context {TDC : TypeDeclKit}.
    Context {TDN : TypeDenoteKit TDC}.

    Fixpoint Val (σ : Ty) : Set :=
      match σ with
      | int => Z
      | bool => Datatypes.bool
      | bit => Bit
      | string => String.string
      | list σ' => Datatypes.list (Val σ')
      | prod σ1 σ2 => Val σ1 * Val σ2
      | sum σ1 σ2 => Val σ1 + Val σ2
      | unit => Datatypes.unit
      | enum E => enumt E
      | bvec n => bv n
      | tuple σs => EnvRec Val σs
      | union U => uniont U
      | record R => recordt R
      end%type.

  End WithTypeDenote.

  Class TypeDefKit {TDC : TypeDeclKit} (TDN : TypeDenoteKit TDC) : Type :=
    { enum_eqdec   :> EqDec enumi;
      union_eqdec  :> EqDec unioni;
      record_eqdec :> EqDec recordi;

      enumt_eqdec E  :> EqDec (enumt E);
      enumt_finite E :> finite.Finite (enumt E);

      uniont_eqdec U  :> EqDec (uniont U);
      (* Names of union data constructors. *)
      unionk          : unioni -> Set;
      unionk_eqdec U  :> EqDec (unionk U);
      unionk_finite U :> finite.Finite (unionk U);
      unionk_ty U     : unionk U -> Ty;

      recordt_eqdec R  :> EqDec (recordt R);
      (* Record field names. *)
      recordf          : Set;
      (* Record field types. *)
      recordf_ty       : recordi -> NCtx recordf Ty;

      (* Union types. *)
      (* Union data constructor field type *)
      unionv_fold U   : { K : unionk U & Val (unionk_ty U K) } -> uniont U;
      unionv_unfold U : uniont U -> { K : unionk U & Val (unionk_ty U K) };

      (* Record types. *)
      recordv_fold R   : NamedEnv Val (recordf_ty R) -> recordt R;
      recordv_unfold R : recordt R -> NamedEnv Val (recordf_ty R);

      unionv_fold_unfold U K : unionv_fold U (unionv_unfold U K) = K;
      unionv_unfold_fold U K : unionv_unfold U (unionv_fold U K) = K;

      recordv_fold_unfold R v : recordv_fold R (recordv_unfold R v) = v;
      recordv_unfold_fold R v : recordv_unfold R (recordv_fold R v) = v;
    }.

  Section WithTypeDef.

    Context {TDC : TypeDeclKit}.
    Context {TDN : TypeDenoteKit TDC}.
    Context {TDF : TypeDefKit TDN}.

    Instance Ty_eq_dec : EqDec Ty :=
      fix ty_eqdec (σ τ : Ty) {struct σ} : dec_eq σ τ :=
        match σ , τ with
        | int        , int        => left eq_refl
        | bool       , bool       => left eq_refl
        | bit        , bit        => left eq_refl
        | string     , string     => left eq_refl
        | list σ     , list τ     => f_equal_dec list noConfusion_inv (ty_eqdec σ τ)
        | prod σ1 σ2 , prod τ1 τ2 => f_equal2_dec prod noConfusion_inv (ty_eqdec σ1 τ1) (ty_eqdec σ2 τ2)
        | sum σ1 σ2  , sum τ1 τ2  => f_equal2_dec sum noConfusion_inv (ty_eqdec σ1 τ1) (ty_eqdec σ2 τ2)
        | unit       , unit       => left eq_refl
        | enum E1    , enum E2    => f_equal_dec enum noConfusion_inv (eq_dec E1 E2)
        | bvec n1    , bvec n2    => f_equal_dec bvec noConfusion_inv (eq_dec n1 n2)
        | tuple σs   , tuple τs   => f_equal_dec
                                       tuple noConfusion_inv
                                       (eq_dec (EqDec := ctx.eq_dec_ctx ty_eqdec) σs τs)
        | union U1   , union U2   => f_equal_dec union noConfusion_inv (eq_dec U1 U2)
        | record R1  , record R2  => f_equal_dec record noConfusion_inv (eq_dec R1 R2)
        | _          , _          => right noConfusion_inv
        end.

    Fixpoint Val_eqb (σ : Ty) : forall (v1 v2 : Val σ), Datatypes.bool :=
      match σ return Val σ -> Val σ -> Datatypes.bool with
      | int      => Z.eqb
      | bool     => Bool.eqb
      | bit      => Bit_eqb
      | string   => String.eqb
      | list σ   => list_beq (Val_eqb σ)
      | prod σ τ => prod_beq (Val_eqb σ) (Val_eqb τ)
      | sum σ τ  => sum_beq (Val_eqb σ) (Val_eqb τ)
      | unit     => fun _ _ => true
      | enum E   => fun v1 v2 => if eq_dec v1 v2 then true else false
      | bvec n   => @bv.eqb n
      | tuple σs => envrec.eqb Val_eqb
      | union U  => fun v1 v2 => if eq_dec v1 v2 then true else false
      | record R => fun v1 v2 => if eq_dec v1 v2 then true else false
      end.

    Lemma Val_eqb_spec (σ : Ty) (x y : Val σ) : reflect (x = y) (Val_eqb σ x y).
    Proof with solve_eqb_spec.
      induction σ; cbn.
      - apply Z.eqb_spec.
      - apply Bool.eqb_spec.
      - apply Bit_eqb_spec.
      - apply String.eqb_spec.
      - apply list_beq_spec; auto.
      - destruct x as [x1 x2], y as [y1 y2]...
      - destruct x as [x1|x2], y as [y1|y2]...
      - destruct x, y...
      - destruct (eq_dec x y)...
      - apply bv.eqb_spec.
      - induction IH...
        destruct x as [? x], y as [? y]; destruct (p x y)...
      - destruct (eq_dec x y)...
      - destruct (eq_dec x y)...
    Qed.

    Lemma unionv_fold_inj {U} (v1 v2 : {K : unionk U & Val (unionk_ty U K)}) :
      unionv_fold U v1 = unionv_fold U v2 <-> v1 = v2.
    Proof.
      split; try congruence. intros H.
      apply (f_equal (unionv_unfold U)) in H.
      now rewrite ?unionv_unfold_fold in H.
    Qed.

    Lemma unionv_unfold_inj {U} (v1 v2 : Val (union U)) :
      unionv_unfold U v1 = unionv_unfold U v2 <-> v1 = v2.
    Proof.
      split; try congruence. intros H.
      apply (f_equal (unionv_fold U)) in H.
      now rewrite ?unionv_fold_unfold in H.
    Qed.

    Lemma K (σ : Ty) (p : σ = σ) : p = eq_refl.
    Proof. apply uip. Qed.

  End WithTypeDef.
  #[global] Arguments int {TK}.
  #[global] Arguments bool {TK}.
  #[global] Arguments bit {TK}.
  #[global] Arguments string {TK}.
  #[global] Arguments list {TK} σ.
  #[global] Arguments prod {TK} σ τ.
  #[global] Arguments sum {TK} σ τ.
  #[global] Arguments unit {TK}.
  #[global] Arguments enum {TK} E.
  #[global] Arguments bvec {TK} n%nat_scope.
  #[global] Arguments tuple {TK} σs%ctx_scope.
  #[global] Arguments union {TK} U.
  #[global] Arguments record {TK} R.
  (* #[global] Arguments MkTypeDefKit {TK} &. *)

  (* Record Types : Type := *)
  (*   { typedecls   : TypeDeclKit; *)
  (*     typedefs    :> TypeDefKit typedecls; *)
  (*     typedeflaws :> TypeDefKitLaws typedecls; *)
  (*   }. *)


  (* Module DefaultVarKit <: VarKit. *)
  (*   (** Variables **) *)
  (*   Definition 𝑿        := string. *)
  (*   Definition 𝑿_eq_dec := string_dec. *)
  (*   Definition 𝑺        := string. *)
  (*   Definition 𝑺_eq_dec := string_dec. *)

  (*   Definition 𝑿to𝑺 (x : 𝑿) : 𝑺 := x. *)
  (*   Definition fresh := ctx.fresh. *)
  (* End DefaultVarKit. *)

End ty.
Export ty
  ( TypeDeclKit, enumt, uniont, recordt,

    TypeDenoteKit,

    Ty, Ty_eq_dec, Val, Val_eqb, Val_eqb_spec,

    TypeDefKit, (* MkTypeDefKit, *) enum_eqdec, enumt_eqdec, enumt_finite,
    enumi,
    unioni,
    recordi,
    union_eqdec, uniont_eqdec, unionk, unionk_eqdec, unionk_finite, unionk_ty,
    unionv_fold, unionv_unfold, record_eqdec, recordt_eqdec, recordf,
    recordf_ty, recordv_fold, recordv_unfold,

    (* TypeDefKitLaws, *) unionv_fold_unfold, unionv_unfold_fold,
    unionv_fold_inj, unionv_unfold_inj,
    recordv_fold_unfold, recordv_unfold_fold

    (* Types, *) (* typedecls, *) (* typedefs *)
  ).
#[export] Existing Instance ty.Ty_eq_dec.

Module Type Types.

  Declare Instance typedeclkit   : TypeDeclKit.
  Declare Instance typedenotekit : TypeDenoteKit typedeclkit.
  Declare Instance typedefkit    : TypeDefKit typedenotekit.
  Declare Instance varkit        : VarKit.

End Types.

Local Instance DefaultTypeDeclKit : TypeDeclKit :=
  {| enumi := Empty_set;
     unioni := Empty_set;
     recordi := Empty_set;
  |}.

Local Instance DefaultTypeDenoteKit : TypeDenoteKit DefaultTypeDeclKit :=
  {| enumt _ := Empty_set;
     uniont _ := Empty_set;
     recordt _ := Empty_set;
  |}.

Local Instance DefaultTypeDefKit : TypeDefKit DefaultTypeDenoteKit.
  refine
    {| unionk _            := Empty_set;
       unionk_ty _ _       := ty.unit;
       unionv_fold         := Empty_set_rec _;
       unionv_unfold       := Empty_set_rec _;
       recordf             := Empty_set;
       recordf_ty          := Empty_set_rec _;
       recordv_fold        := Empty_set_rec _;
       recordv_unfold      := Empty_set_rec _;
       (* unionv_fold_unfold  := Empty_set_rec _; *)
    |}; abstract (intros []).
Defined.
