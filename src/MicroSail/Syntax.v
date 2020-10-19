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
     Classes.Equivalence
     Classes.Morphisms
     Classes.RelationClasses
     Logic.EqdepFacts
     Logic.FinFun
     Logic.FunctionalExtensionality
     Program.Equality
     Program.Tactics
     Relations
     Strings.String
     ZArith.ZArith.
From Coq Require
     Vector
     ssr.ssrbool.

From bbv Require
     Word.

From stdpp Require
     finite.
From Equations Require Import
     Equations Signature.

From MicroSail Require Export
     Context
     Environment
     Notation
     Prelude
     Tactics.

Import CtxNotations.
Import EnvNotations.

Local Set Implicit Arguments.
Local Unset Transparent Obligations.
Obligation Tactic := idtac.

Inductive Bit : Set := bitzero | bitone.

(* Simple telescopic equality for a family with one index. *)
Inductive teq {I} {F : I -> Type} {i j} (fi : F i) (fj : F j) : Prop :=
| teq_refl (eqi : i = j) (eqf : eq_rect _ _ fi _ eqi = fj) : teq fi fj.
Infix "≡" := teq (at level 70, no associativity).

Definition Bit_eqb (b1 : Bit) (b2 : Bit) : bool :=
  match b1, b2 with
  | bitzero, bitzero => true
  | bitone , bitone  => true
  | _      , _       => false
  end.

Lemma Bit_eqb_spec (b1 b2 : Bit) : reflect (b1 = b2) (Bit_eqb b1 b2).
Proof.
  destruct b1; destruct b2; cbn; constructor; congruence.
Qed.

Section TraverseList.

  Import stdpp.base.

  Context `{MRet M, MBind M} {A B : Type} (f : A -> M B).

  Fixpoint traverse_list (xs : list A) : M (list B) :=
    match xs with
    | nil       => mret nil
    | cons x xs => b ← f x ; bs ← traverse_list xs ; mret (cons b bs)
  end.

  Fixpoint traverse_vector {n} (xs : Vector.t A n) : M (Vector.t B n) :=
    match xs with
    | Vector.nil => mret Vector.nil
    | Vector.cons x xs =>
      b ← f x ; bs ← traverse_vector xs ; mret (Vector.cons b bs)
  end.

End TraverseList.

Section TraverseEnv.

  Import stdpp.base.

  Context `{MRet M, MBind M} {I : Set} {A B : I -> Type} (f : forall i : I, A i -> M (B i)).

  Fixpoint traverse_env {Γ : Ctx I} (xs : Env A Γ) : M (Env B Γ) :=
    match xs with
    | env_nil => mret (env_nil)
    | env_snoc Ea i a => Eb ← traverse_env Ea ; b ← f a ; mret (env_snoc Eb i b)
  end.

End TraverseEnv.

(******************************************************************************)

Class Blastable (A : Type) : Type :=
  { blast : A -> (A -> Prop) -> Prop;
    blast_sound:
      forall (a : A) (k : A -> Prop),
        blast a k <-> k a
  } .

Program Instance blastable_bool : Blastable bool :=
  {| blast b k := (b = true -> k true) /\ (b = false -> k false) |}.
Solve All Obligations with intros []; intuition; congruence.

Program Instance blastable_int : Blastable Z :=
  {| blast z k := k z |}.
Solve All Obligations with intuition.

Program Instance blastable_string : Blastable string :=
  {| blast s k := k s |}.
Solve All Obligations with intuition.

Program Instance blastable_unit : Blastable unit :=
  {| blast u k := k tt |}.
Solve All Obligations with intros []; intuition; congruence.

Program Instance blastable_list {A : Type} : Blastable (list A) :=
  {| blast xs k :=
       (forall (y : A) (ys : list A), xs = cons y ys -> k (cons y ys)) /\
       (xs = nil -> k nil)
  |}.
Solve All Obligations with intros ? []; intuition; congruence.

Program Instance blastable_prod {A B : Type} : Blastable (A * B) :=
  { blast ab k := k (fst ab , snd ab) }.
Solve All Obligations with intuition.

Program Instance blastable_sigt {A} {B : A -> Type} : Blastable (sigT B) :=
  {| blast ab k := k (existT (projT1 ab) (projT2 ab)) |}.
Solve All Obligations with intros ? ? []; intuition; congruence.

Program Instance blastable_sum {A B : Type} : Blastable (A + B) :=
  {| blast ab k :=
       (forall (a : A), ab = inl a -> k (inl a)) /\
       (forall (b : B), ab = inr b -> k (inr b))
  |}.
Solve All Obligations with intros ? ? []; intuition; congruence.

Program Instance blastable_bit : Blastable Bit :=
  {| blast b k := (b = bitzero -> k bitzero) /\ (b = bitone -> k bitone) |}.
Solve All Obligations with intros []; intuition; congruence.

Program Instance blastable_word {n} : Blastable (Word.word n) :=
  {| blast w k := k w |}.
Solve All Obligations with intuition.

Program Instance blastable_env {B D} {Γ : Ctx B} : Blastable (Env D Γ) :=
  {| blast :=
       (fix blast {Δ : Ctx B} (E : Env D Δ) {struct E} : (Env D Δ -> Prop) -> Prop :=
       match E in Env _ Δ return (Env D Δ -> Prop) -> Prop with
       | env_nil => fun k => k env_nil
       | env_snoc E b db => fun k => blast E (fun E' => k (env_snoc E' b db))
       end) Γ
  |}.
Next Obligation.
  intros ? ? ? E; induction E; cbn.
  - reflexivity.
  - intro k; exact (IHE (fun E' : Env D Γ => k (env_snoc E' b db))).
Defined.
Instance blastable_env' {X T : Set} {D} {Δ : Ctx (X * T)} : Blastable (NamedEnv D Δ) :=
  blastable_env.

Program Instance Blastable_Finite `{finite.Finite A} : Blastable A :=
  {| blast a POST :=
       match finite.enum A with
       | nil       => True
       | cons x xs => List.fold_left (fun P y => P /\ (a = y -> POST y)) xs (a = x -> POST x)
       end
  |}.
Admit Obligations.

Module Type TypeKit.

  Import stdpp.finite.

  (* Names of enum type constructors. *)
  Parameter Inline 𝑬 : Set. (* input: \MIE *)
  Declare Instance 𝑬_eq_dec : EqDec 𝑬.
  (* Names of enum data constructors. *)
  Parameter Inline 𝑬𝑲 : 𝑬 -> Set.
  Declare Instance 𝑬𝑲_eq_dec : forall (e : 𝑬), EqDec (𝑬𝑲 e).
  Declare Instance 𝑬𝑲_finite : forall E, Finite (𝑬𝑲 E).

  (* Names of union type constructors. *)
  Parameter Inline 𝑼   : Set. (* input: \MIT *)
  Declare Instance 𝑼_eq_dec : EqDec 𝑼.
  (* Union types. *)
  Parameter Inline 𝑼𝑻  : 𝑼 -> Set.
  Parameter Inline 𝑼𝑻_eq_dec : forall (u : 𝑼) (x y : 𝑼𝑻 u), {x=y}+{~x=y}.
  (* Names of union data constructors. *)
  Parameter Inline 𝑼𝑲  : 𝑼 -> Set.
  Declare Instance 𝑼𝑲_eq_dec : forall (u : 𝑼), EqDec (𝑼𝑲 u).
  Declare Instance 𝑼𝑲_finite : forall U, Finite (𝑼𝑲 U).

  (* Names of record type constructors. *)
  Parameter Inline 𝑹  : Set. (* input: \MIR *)
  Declare Instance 𝑹_eq_dec : EqDec 𝑹.
  (* Record types. *)
  Parameter Inline 𝑹𝑻  : 𝑹 -> Set.
  Declare Instance 𝑹𝑻_eq_dec : forall (r : 𝑹), EqDec (𝑹𝑻 r).

  (* Names of expression variables. These represent mutable variables appearing
     in programs. *)
  Parameter Inline 𝑿 : Set. (* input: \MIX *)
  (* For name resolution we rely on decidable equality of expression
     variables. The functions in this module resolve to the closest binding
     of an equal name and fill in the de Bruijn index automatically from
     a successful resolution.
  *)
  Declare Instance 𝑿_eq_dec : EqDec 𝑿.

  (* Names of logical variables. These represent immutable variables
     standing for concrete literals in assertions. *)
  Parameter Inline 𝑺 : Set. (* input: \MIS *)
  Declare Instance 𝑺_eq_dec : EqDec 𝑺.
  (* Punning of program variables with logical variables. *)
  Parameter Inline 𝑿to𝑺 : 𝑿 -> 𝑺.

End TypeKit.

Module Types (Export typekit : TypeKit).

  Local Set Transparent Obligations.
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
  (* Experimental features. These are still in flux. *)
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

  Global Instance Ty_eq_dec : EqDec Ty :=
    fix ty_eqdec (σ τ : Ty) {struct σ} : ssrbool.decidable (σ = τ) :=
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
      | ty_tuple σs   , ty_tuple τs   => f_equal_dec ty_tuple noConfusion_inv (@ctx_eqdec Ty ty_eqdec σs τs)
      | ty_union U1   , ty_union U2   => f_equal_dec ty_union noConfusion_inv (eq_dec U1 U2)
      | ty_record R1  , ty_record R2  => f_equal_dec ty_record noConfusion_inv (eq_dec R1 R2)
      | _             , _             => right noConfusion_inv
      end.

  Lemma Ty_K (σ : Ty) (p : σ = σ) : p = eq_refl.
  Proof. apply uip. Qed.

  Fixpoint Lit (σ : Ty) : Set :=
    match σ with
    | ty_int => Z
    | ty_bool => bool
    | ty_bit => Bit
    | ty_string => string
    | ty_list σ' => list (Lit σ')
    | ty_prod σ1 σ2 => Lit σ1 * Lit σ2
    | ty_sum σ1 σ2 => Lit σ1 + Lit σ2
    | ty_unit => unit
    | ty_enum E => 𝑬𝑲 E
    | ty_bvec n => Word.word n
    (* Experimental features *)
    | ty_tuple σs => EnvRec Lit σs
    | ty_union U => 𝑼𝑻 U
    | ty_record R => 𝑹𝑻 R
    end%type.

End Types.

(******************************************************************************)

Module Type TermKit (typekit : TypeKit).
  Module TY := Types typekit.
  Export TY.

  (* Union data constructor field type *)
  Parameter Inline 𝑼𝑲_Ty : forall (U : 𝑼), 𝑼𝑲 U -> Ty.
  Parameter Inline 𝑼_fold   : forall (U : 𝑼), { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty K) } -> 𝑼𝑻 U.
  Parameter Inline 𝑼_unfold : forall (U : 𝑼), 𝑼𝑻 U -> { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty K) }.
  Parameter Inline 𝑼_fold_unfold :
    forall (U : 𝑼) (Kv: 𝑼𝑻 U),
      𝑼_fold (𝑼_unfold Kv) = Kv.
  Parameter Inline 𝑼_unfold_fold :
    forall (U : 𝑼) (Kv: { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty K) }),
      𝑼_unfold (𝑼_fold Kv) = Kv.

  (* Record field names. *)
  Parameter Inline 𝑹𝑭  : Set.
  (* Record field types. *)
  Parameter Inline 𝑹𝑭_Ty : 𝑹 -> Ctx (𝑹𝑭 * Ty).
  Parameter Inline 𝑹_fold   : forall (R : 𝑹), NamedEnv Lit (𝑹𝑭_Ty R) -> 𝑹𝑻 R.
  Parameter Inline 𝑹_unfold : forall (R : 𝑹), 𝑹𝑻 R -> NamedEnv Lit (𝑹𝑭_Ty R).
  Parameter Inline 𝑹_fold_unfold :
    forall (R : 𝑹) (Kv: 𝑹𝑻 R),
      𝑹_fold (𝑹_unfold Kv) = Kv.
  Parameter Inline 𝑹_unfold_fold :
    forall (R : 𝑹) (Kv: NamedEnv Lit (𝑹𝑭_Ty R)),
      𝑹_unfold (𝑹_fold Kv) = Kv.

  (* Names of functions. *)
  Parameter Inline 𝑭 : Ctx (𝑿 * Ty) -> Ty -> Set.
  Parameter Inline 𝑭𝑿 : Ctx (𝑿 * Ty) -> Ty -> Set.

  (* Names of registers. *)
  Parameter Inline 𝑹𝑬𝑮 : Ty -> Set.
  Parameter Inline 𝑹𝑬𝑮_eq_dec :
    forall {σ τ} (x : 𝑹𝑬𝑮 σ) (y : 𝑹𝑬𝑮 τ), {x ≡ y}+{~ x ≡ y}.

End TermKit.

Module Terms (typekit : TypeKit) (termkit : TermKit typekit).
  Export termkit.

  Program Instance blastable_union (U : 𝑼) : Blastable (𝑼𝑻 U) :=
    {| blast v k :=
         forall (K : 𝑼𝑲 U),
           blast K (fun K =>
                      forall p,
                        v = 𝑼_fold (existT K p) ->
                        k (𝑼_fold (existT K p)))
    |}.
  Admit Obligations.
  (* Next Obligation. *)
  (*   intros; cbn; constructor; intro hyp. *)
  (*   - rewrite <- (@𝑼_fold_unfold U a) in *. *)
  (*     destruct (𝑼_unfold a) as [K v] eqn:eq_a. *)
  (*     specialize (hyp K). *)
  (*     rewrite blast_sound in hyp. *)
  (*     now apply hyp. *)
  (*   - intros K. *)
  (*     rewrite blast_sound. *)
  (*     now intros; subst. *)
  (* Qed. *)

  Program Instance blastable_record (R : 𝑹) : Blastable (𝑹𝑻 R) :=
    {| blast v k := k (𝑹_fold (𝑹_unfold v)) |}.
  Next Obligation.
    cbn; intros; now rewrite 𝑹_fold_unfold.
  Qed.

  Section Literals.

    Global Instance blastable_lit {σ} : Blastable (Lit σ) :=
      match σ with
      | ty_int => blastable_int
      | ty_bool => blastable_bool
      | ty_bit => blastable_bit
      | ty_string => blastable_string
      | ty_list σ0 => @blastable_list (Lit σ0)
      | ty_prod σ1 σ2 => @blastable_prod (Lit σ1) (Lit σ2)
      | ty_sum σ1 σ2 => @blastable_sum (Lit σ1) (Lit σ2)
      | ty_unit => blastable_unit
      | ty_enum E => Blastable_Finite
      | ty_bvec n => blastable_word
      | ty_tuple σs => Ctx_rect
                         (fun σs => Blastable (Lit (ty_tuple σs)))
                         blastable_unit
                         (fun σs blast_σs σ => @blastable_prod (EnvRec Lit σs) (Lit σ))
                         σs
      | ty_union U => blastable_union U
      | ty_record R => blastable_record R
      end%type.

    Fixpoint Lit_eqb (σ : Ty) : forall (l1 l2 : Lit σ), bool :=
      match σ with
      | ty_int      => Z.eqb
      | ty_bool     => Bool.eqb
      | ty_bit      => Bit_eqb
      | ty_string   => String.eqb
      | ty_list σ   => list_beq (Lit_eqb σ)
      | ty_prod σ τ => prod_beq (Lit_eqb σ) (Lit_eqb τ)
      | ty_sum σ τ  => sum_beq (Lit_eqb σ) (Lit_eqb τ)
      | ty_unit     => fun _ _ => true
      | ty_enum E   => fun l1 l2 => if 𝑬𝑲_eq_dec l1 l2 then true else false
      | ty_bvec n   => @Word.weqb n
      | ty_tuple σs => envrec_beq Lit_eqb
      | ty_union U  => fun l1 l2 => if 𝑼𝑻_eq_dec l1 l2 then true else false
      | ty_record R => fun l1 l2 => if 𝑹𝑻_eq_dec l1 l2 then true else false
      end.

    Lemma Lit_eqb_spec (σ : Ty) (x y : Lit σ) : reflect (x = y) (Lit_eqb σ x y).
    Proof with microsail_solve_eqb_spec.
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

  End Literals.
  Bind Scope lit_scope with Lit.

  Definition LocalStore (Γ : Ctx (𝑿 * Ty)) : Type := NamedEnv Lit Γ.
  Bind Scope env_scope with LocalStore.

  Section BinaryOperations.

    Inductive BinOp : Ty -> Ty -> Ty -> Set :=
    | binop_plus              : BinOp ty_int ty_int ty_int
    | binop_times             : BinOp ty_int ty_int ty_int
    | binop_minus             : BinOp ty_int ty_int ty_int
    | binop_eq                : BinOp ty_int ty_int ty_bool
    | binop_le                : BinOp ty_int ty_int ty_bool
    | binop_lt                : BinOp ty_int ty_int ty_bool
    | binop_gt                : BinOp ty_int ty_int ty_bool
    | binop_and               : BinOp ty_bool ty_bool ty_bool
    | binop_or                : BinOp ty_bool ty_bool ty_bool
    | binop_pair {σ1 σ2 : Ty} : BinOp σ1 σ2 (ty_prod σ1 σ2)
    | binop_cons {σ : Ty}     : BinOp σ (ty_list σ) (ty_list σ)
    | binop_bvplus {n}        : BinOp (ty_bvec n) (ty_bvec n) (ty_bvec n)
    | binop_bvmult {n}        : BinOp (ty_bvec n) (ty_bvec n) (ty_bvec n)
    | binop_bvcombine {m n}   : BinOp (ty_bvec m) (ty_bvec n) (ty_bvec (m + n))
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

    Definition binoptel_eq_dec {σ1 σ2 σ3 τ1 τ2 τ3}
      (op1 : BinOp σ1 σ2 σ3) (op2 : BinOp τ1 τ2 τ3) :
      ssrbool.decidable (((σ1,σ2,σ3), op1) = ((τ1,τ2,τ3),op2) :> BinOpTel) :=
      match op1 , op2 with
      | binop_plus  , binop_plus   => left eq_refl
      | binop_times , binop_times  => left eq_refl
      | binop_minus , binop_minus  => left eq_refl
      | binop_eq    , binop_eq     => left eq_refl
      | binop_le    , binop_le     => left eq_refl
      | binop_lt    , binop_lt     => left eq_refl
      | binop_gt    , binop_gt     => left eq_refl
      | binop_and   , binop_and    => left eq_refl
      | binop_or    , binop_or     => left eq_refl
      | @binop_pair σ1 σ2 , @binop_pair τ1 τ2   =>
        f_equal2_dec binoptel_pair noConfusion_inv (eq_dec σ1 τ1) (eq_dec σ2 τ2)
      | @binop_cons σ  , @binop_cons τ   =>
        f_equal_dec binoptel_cons noConfusion_inv (eq_dec σ τ)
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

  End BinaryOperations.

  Section Expressions.

    Local Unset Elimination Schemes.

    (* Intrinsically well-typed expressions. The context Γ of mutable variables
       contains names 𝑿 and types Ty, but the names are not computationally
       relevant. The underlying representation is still a de Bruijn index based
       one. The names are meant for human consumption and we also provide name
       resolution infrastructure in the NameResolution module to fill in de
       Bruijn indices automatically.

       The de Bruijn indices are wrapped together with a resolution proof in the
       InCtx type class, which currently does not have any global instances. We
       do have local implicit instances like for example in the exp_var
       constructor below and use the type class mechanism to copy these
       locally. *)
    Inductive Exp (Γ : Ctx (𝑿 * Ty)) : Ty -> Type :=
    | exp_var     (x : 𝑿) (σ : Ty) {xInΓ : InCtx (x , σ) Γ} : Exp Γ σ
    | exp_lit     (σ : Ty) : Lit σ -> Exp Γ σ
    | exp_binop   {σ1 σ2 σ3 : Ty} (op : BinOp σ1 σ2 σ3) (e1 : Exp Γ σ1) (e2 : Exp Γ σ2) : Exp Γ σ3
    | exp_neg     (e : Exp Γ ty_int) : Exp Γ ty_int
    | exp_not     (e : Exp Γ ty_bool) : Exp Γ ty_bool
    | exp_inl     {σ1 σ2 : Ty} : Exp Γ σ1 -> Exp Γ (ty_sum σ1 σ2)
    | exp_inr     {σ1 σ2 : Ty} : Exp Γ σ2 -> Exp Γ (ty_sum σ1 σ2)
    | exp_list    {σ : Ty} (es : list (Exp Γ σ)) : Exp Γ (ty_list σ)
    (* Experimental features *)
    | exp_bvec    {n} (es : Vector.t (Exp Γ ty_bit) n) : Exp Γ (ty_bvec n)
    | exp_tuple   {σs : Ctx Ty} (es : Env (Exp Γ) σs) : Exp Γ (ty_tuple σs)
    | exp_projtup {σs : Ctx Ty} (e : Exp Γ (ty_tuple σs)) (n : nat) {σ : Ty}
                  {p : ctx_nth_is σs n σ} : Exp Γ σ
    | exp_union   {U : 𝑼} (K : 𝑼𝑲 U) (e : Exp Γ (𝑼𝑲_Ty K)) : Exp Γ (ty_union U)
    | exp_record  (R : 𝑹) (es : NamedEnv (Exp Γ) (𝑹𝑭_Ty R)) : Exp Γ (ty_record R)
    | exp_projrec {R : 𝑹} (e : Exp Γ (ty_record R)) (rf : 𝑹𝑭) {σ : Ty}
                  {rfInR : InCtx (rf , σ) (𝑹𝑭_Ty R)} : Exp Γ σ.
    Bind Scope exp_scope with Exp.

    Global Arguments exp_var {_} _ {_ _}.
    Global Arguments exp_tuple {_ _} _%exp.
    Global Arguments exp_union {_} _ _.
    Global Arguments exp_record {_} _ _.
    Global Arguments exp_projrec {_ _} _ _ {_ _}.

    Section ExpElimination.

      Variable (Γ : Ctx (𝑿 * Ty)).
      Variable (P : forall t, Exp Γ t -> Type).
      Arguments P _ _ : clear implicits.

      Let PL (σ : Ty) : list (Exp Γ σ) -> Type :=
        List.fold_right (fun e es => P _ e * es)%type unit.
      Let PV (n : nat) (es : Vector.t (Exp Γ ty_bit) n) : Type :=
        Vector.fold_right (fun e ps => P _ e * ps)%type es unit.
      Let PE : forall σs, Env (Exp Γ) σs -> Type :=
        Env_rect (fun _ _ => Type) unit (fun _ es IHes _ e => IHes * P _ e)%type.
      Let PNE : forall (σs : Ctx (𝑹𝑭 * Ty)), NamedEnv (Exp Γ) σs -> Type :=
        Env_rect (fun _ _ => Type) unit (fun _ es IHes _ e => IHes * P _ e)%type.

      Hypothesis (P_var     : forall (x : 𝑿) (σ : Ty) (xInΓ : (x ∶ σ)%ctx ∈ Γ), P σ (exp_var x)).
      Hypothesis (P_lit     : forall (σ : Ty) (l : Lit σ), P σ (exp_lit Γ σ l)).
      Hypothesis (P_binop   : forall (σ1 σ2 σ3 : Ty) (op : BinOp σ1 σ2 σ3) (e1 : Exp Γ σ1), P σ1 e1 -> forall e2 : Exp Γ σ2, P σ2 e2 -> P σ3 (exp_binop op e1 e2)).
      Hypothesis (P_neg     : forall e : Exp Γ ty_int, P ty_int e -> P ty_int (exp_neg e)).
      Hypothesis (P_not     : forall e : Exp Γ ty_bool, P ty_bool e -> P ty_bool (exp_not e)).
      Hypothesis (P_inl     : forall (σ1 σ2 : Ty) (e : Exp Γ σ1), P σ1 e -> P (ty_sum σ1 σ2) (exp_inl e)).
      Hypothesis (P_inr     : forall (σ1 σ2 : Ty) (e : Exp Γ σ2), P σ2 e -> P (ty_sum σ1 σ2) (exp_inr e)).
      Hypothesis (P_list    : forall (σ : Ty) (es : list (Exp Γ σ)), PL es -> P (ty_list σ) (exp_list es)).
      Hypothesis (P_bvec    : forall (n : nat) (es : Vector.t (Exp Γ ty_bit) n), PV es -> P (ty_bvec n) (exp_bvec es)).
      Hypothesis (P_tuple   : forall (σs : Ctx Ty) (es : Env (Exp Γ) σs), PE es -> P (ty_tuple σs) (exp_tuple es)).
      Hypothesis (P_projtup : forall (σs : Ctx Ty) (e : Exp Γ (ty_tuple σs)), P (ty_tuple σs) e -> forall (n : nat) (σ : Ty) (p : ctx_nth_is σs n σ), P σ (@exp_projtup _ _ e n _ p)).
      Hypothesis (P_union   : forall (U : 𝑼) (K : 𝑼𝑲 U) (e : Exp Γ (𝑼𝑲_Ty K)), P (𝑼𝑲_Ty K) e -> P (ty_union U) (exp_union U K e)).
      Hypothesis (P_record  : forall (R : 𝑹) (es : NamedEnv (Exp Γ) (𝑹𝑭_Ty R)), PNE es -> P (ty_record R) (exp_record R es)).
      Hypothesis (P_projrec : forall (R : 𝑹) (e : Exp Γ (ty_record R)), P (ty_record R) e -> forall (rf : 𝑹𝑭) (σ : Ty) (rfInR : (rf ∶ σ)%ctx ∈ 𝑹𝑭_Ty R), P σ (exp_projrec e rf)).

      Fixpoint Exp_rect {τ : Ty} (e : Exp Γ τ) {struct e} : P τ e :=
        match e with
        | exp_var x                 => ltac:(apply P_var; auto)
        | exp_lit _ _ l             => ltac:(apply P_lit; auto)
        | exp_binop op e1 e2        => ltac:(apply P_binop; auto)
        | exp_neg e                 => ltac:(apply P_neg; auto)
        | exp_not e                 => ltac:(apply P_not; auto)
        | exp_inl e                 => ltac:(apply P_inl; auto)
        | exp_inr e                 => ltac:(apply P_inr; auto)
        | exp_list es               => ltac:(apply P_list; induction es; cbn; auto using unit)
        | exp_bvec es               => ltac:(apply P_bvec; induction es; cbn; auto using unit)
        | exp_tuple es              => ltac:(apply P_tuple; induction es; cbn; auto using unit)
        | @exp_projtup _ σs e n σ p => ltac:(apply P_projtup; auto)
        | exp_union U K e           => ltac:(apply P_union; auto)
        | exp_record R es           => ltac:(apply P_record; induction es; cbn; auto using unit)
        | exp_projrec e rf          => ltac:(apply P_projrec; auto)
        end.

    End ExpElimination.

    Definition Exp_rec {Γ} (P : forall σ, Exp Γ σ -> Set) := Exp_rect P.
    Definition Exp_ind {Γ} (P : forall σ, Exp Γ σ -> Prop) := Exp_rect P.

    Import EnvNotations.

    Fixpoint tuple_proj (σs : Ctx Ty) (n : nat) (σ : Ty) :
      Lit (ty_tuple σs) -> ctx_nth_is σs n σ -> Lit σ :=
      match σs with
      | ctx_nil       => fun l (p : ctx_nth_is ctx_nil _ _) =>
                           match p with end
      | ctx_snoc τs τ => match n with
                         | 0   => fun (l : Lit (ty_tuple (ctx_snoc _ _)))
                                      (p : ctx_nth_is _ 0 _) =>
                                    @eq_rect Ty τ Lit (snd l) σ p
                         | S m => fun l p => tuple_proj τs m σ (fst l) p
                         end
      end.

    Definition eval_binop {σ1 σ2 σ3 : Ty} (op : BinOp σ1 σ2 σ3) : Lit σ1 -> Lit σ2 -> Lit σ3 :=
      match op with
      | binop_plus      => Z.add
      | binop_times     => Z.mul
      | binop_minus     => Z.sub
      | binop_eq        => Z.eqb
      | binop_le        => Z.leb
      | binop_lt        => Z.ltb
      | binop_gt        => Z.gtb
      | binop_and       => andb
      | binop_or        => fun v1 v2 => orb v1 v2
      | binop_pair      => pair
      | binop_cons      => cons
      | binop_bvplus    => fun v1 v2 => Word.wplus v1 v2
      | binop_bvmult    => fun v1 v2 => Word.wmult v1 v2
      | binop_bvcombine => fun v1 v2 => Word.combine v1 v2
      end.

    Fixpoint eval {Γ : Ctx (𝑿 * Ty)} {σ : Ty} (e : Exp Γ σ) (δ : LocalStore Γ) {struct e} : Lit σ :=
      match e in (Exp _ t) return (Lit t) with
      | exp_var x           => δ ‼ x
      | exp_lit _ _ l       => l
      | exp_binop op e1 e2  => eval_binop op (eval e1 δ) (eval e2 δ)
      | exp_neg e           => Z.opp (eval e δ)
      | exp_not e           => negb (eval e δ)
      | exp_inl e           => inl (eval e δ)
      | exp_inr e           => inr (eval e δ)
      | exp_list es         => List.map (fun e => eval e δ) es
      | exp_bvec es         => Vector.t_rect
                                 _ (fun m (_ : Vector.t (Exp Γ ty_bit) m) => Word.word m)
                                 Word.WO (fun eb m _ (vs : Word.word m) =>
                                            match eval eb δ with
                                            | bitzero => Word.WS false vs
                                            | bitone => Word.WS true vs
                                            end)
                                 _ es
      | exp_tuple es        => Env_rect
                                 (fun σs _ => Lit (ty_tuple σs))
                                 tt
                                 (fun σs _ (vs : Lit (ty_tuple σs)) σ e => (vs, eval e δ))
                                 es
      | @exp_projtup _ σs e n σ p => tuple_proj σs n σ (eval e δ) p
      | exp_union U K e     => 𝑼_fold (existT K (eval e δ))
      | exp_record R es     => 𝑹_fold (Env_rect
                                         (fun σs _ => NamedEnv Lit σs)
                                         env_nil
                                         (fun σs _ vs _ e => env_snoc vs _ (eval e δ)) es)
      | exp_projrec e rf    => 𝑹_unfold (eval e δ) ‼ rf
      end.

    Definition evals {Γ Δ} (es : NamedEnv (Exp Γ) Δ) (δ : LocalStore Γ) : LocalStore Δ :=
      env_map (fun xτ e => eval e δ) es.

  End Expressions.
  Bind Scope exp_scope with Exp.

  Section Statements.

    Inductive TuplePat : Ctx Ty -> Ctx (𝑿 * Ty) -> Set :=
    | tuplepat_nil  : TuplePat ctx_nil ctx_nil
    | tuplepat_snoc
        {σs : Ctx Ty} {Δ : Ctx (𝑿 * Ty)}
        (pat : TuplePat σs Δ) {σ : Ty} (x : 𝑿) :
        TuplePat (ctx_snoc σs σ) (ctx_snoc Δ (x , σ)).
    Bind Scope pat_scope with TuplePat.

    Inductive RecordPat : Ctx (𝑹𝑭 * Ty) -> Ctx (𝑿 * Ty) -> Set :=
    | recordpat_nil  : RecordPat ctx_nil ctx_nil
    | recordpat_snoc
        {rfs : Ctx (𝑹𝑭 * Ty)} {Δ : Ctx (𝑿 * Ty)}
        (pat : RecordPat rfs Δ) (rf : 𝑹𝑭) {τ : Ty} (x : 𝑿) :
        RecordPat (ctx_snoc rfs (rf , τ)) (ctx_snoc Δ (x , τ)).
    Bind Scope pat_scope with RecordPat.

    Inductive Pattern : Ctx (𝑿 * Ty) -> Ty -> Set :=
    | pat_var (x : 𝑿) {σ : Ty} : Pattern [ x ∶ σ ]%ctx σ
    | pat_unit : Pattern ctx_nil ty_unit
    | pat_pair (x y : 𝑿) {σ τ : Ty} : Pattern [ x ∶ σ , y ∶ τ ]%ctx (ty_prod σ τ)
    | pat_tuple {σs Δ} (p : TuplePat σs Δ) : Pattern Δ (ty_tuple σs).

    Local Unset Elimination Schemes.

    Inductive Stm (Γ : Ctx (𝑿 * Ty)) : Ty -> Type :=
    | stm_lit        {τ : Ty} (l : Lit τ) : Stm Γ τ
    | stm_exp        {τ : Ty} (e : Exp Γ τ) : Stm Γ τ
    | stm_let        (x : 𝑿) (τ : Ty) (s : Stm Γ τ) {σ : Ty} (k : Stm (ctx_snoc Γ (x , τ)) σ) : Stm Γ σ
    | stm_block      (Δ : Ctx (𝑿 * Ty)) (δ : LocalStore Δ) {σ : Ty} (k : Stm (ctx_cat Γ Δ) σ) : Stm Γ σ
    | stm_assign     (x : 𝑿) (τ : Ty) {xInΓ : InCtx (x , τ) Γ} (e : Stm Γ τ) : Stm Γ τ
    | stm_call       {Δ σ} (f : 𝑭 Δ σ) (es : NamedEnv (Exp Γ) Δ) : Stm Γ σ
    | stm_call_frame (Δ : Ctx (𝑿 * Ty)) (δ : LocalStore Δ) (τ : Ty) (s : Stm Δ τ) : Stm Γ τ
    | stm_call_external {Δ σ} (f : 𝑭𝑿 Δ σ) (es : NamedEnv (Exp Γ) Δ) : Stm Γ σ
    | stm_if         {τ : Ty} (e : Exp Γ ty_bool) (s1 s2 : Stm Γ τ) : Stm Γ τ
    | stm_seq        {τ : Ty} (e : Stm Γ τ) {σ : Ty} (k : Stm Γ σ) : Stm Γ σ
    | stm_assert     (e1 : Exp Γ ty_bool) (e2 : Exp Γ ty_string) : Stm Γ ty_bool
    (* | stm_while      (w : 𝑾 Γ) (e : Exp Γ ty_bool) {σ : Ty} (s : Stm Γ σ) -> Stm Γ ty_unit *)
    | stm_fail      (τ : Ty) (s : Lit ty_string) : Stm Γ τ
    | stm_match_list {σ τ : Ty} (e : Exp Γ (ty_list σ)) (alt_nil : Stm Γ τ)
      (xh xt : 𝑿) (alt_cons : Stm (ctx_snoc (ctx_snoc Γ (xh , σ)) (xt , ty_list σ)) τ) : Stm Γ τ
    | stm_match_sum  {σinl σinr τ : Ty} (e : Exp Γ (ty_sum σinl σinr))
      (xinl : 𝑿) (alt_inl : Stm (ctx_snoc Γ (xinl , σinl)) τ)
      (xinr : 𝑿) (alt_inr : Stm (ctx_snoc Γ (xinr , σinr)) τ) : Stm Γ τ
    | stm_match_pair {σ1 σ2 τ : Ty} (e : Exp Γ (ty_prod σ1 σ2))
      (xl xr : 𝑿) (rhs : Stm (ctx_snoc (ctx_snoc Γ (xl , σ1)) (xr , σ2)) τ) : Stm Γ τ
    | stm_match_enum {E : 𝑬} (e : Exp Γ (ty_enum E)) {τ : Ty}
      (alts : forall (K : 𝑬𝑲 E), Stm Γ τ) : Stm Γ τ
    | stm_match_tuple {σs : Ctx Ty} {Δ : Ctx (𝑿 * Ty)} (e : Exp Γ (ty_tuple σs))
      (p : TuplePat σs Δ) {τ : Ty} (rhs : Stm (ctx_cat Γ Δ) τ) : Stm Γ τ
    | stm_match_union {U : 𝑼} (e : Exp Γ (ty_union U)) {τ : Ty}
      (alts : forall (K : 𝑼𝑲 U), Alternative Γ (𝑼𝑲_Ty K) τ) : Stm Γ τ
    | stm_match_record {R : 𝑹} {Δ : Ctx (𝑿 * Ty)} (e : Exp Γ (ty_record R))
      (p : RecordPat (𝑹𝑭_Ty R) Δ) {τ : Ty} (rhs : Stm (ctx_cat Γ Δ) τ) : Stm Γ τ
    | stm_read_register {τ} (reg : 𝑹𝑬𝑮 τ) : Stm Γ τ
    | stm_write_register {τ} (reg : 𝑹𝑬𝑮 τ) (e : Exp Γ τ) : Stm Γ τ
    | stm_bind   {σ τ : Ty} (s : Stm Γ σ) (k : Lit σ -> Stm Γ τ) : Stm Γ τ
    with Alternative (Γ : Ctx (𝑿 * Ty)) : Ty -> Ty -> Type :=
    | alt {σ τ} {Δ : Ctx (𝑿 * Ty)} (p : Pattern Δ σ) (rhs : Stm (ctx_cat Γ Δ) τ) : Alternative Γ σ τ.

    Section TransparentObligations.

      Local Set Transparent Obligations.
      Derive Signature for Stm.
      Derive NoConfusionHom for Stm.

    End TransparentObligations.

    Definition proj_alt_ext {Γ σ τ} (a : Alternative Γ σ τ) : Ctx (𝑿 * Ty) :=
      match a with @alt _ _ _ Δ _ _ => Δ end.
    Definition proj_alt_pat {Γ σ τ} (a : Alternative Γ σ τ) : Pattern (proj_alt_ext a) σ :=
      match a with @alt _ _ _ _ p _ => p end.
    Definition proj_alt_rhs {Γ σ τ} (a : Alternative Γ σ τ) : Stm (ctx_cat Γ (proj_alt_ext a)) τ :=
      match a with @alt _ _ _ _ _ s => s end.

    Section StmElimination.

      Variable (P : forall (Γ : Ctx (𝑿 * Ty)) (t : Ty), Stm Γ t -> Type).

      Hypothesis (P_lit   : forall (Γ : Ctx (𝑿 * Ty)) (τ : Ty) (l : Lit τ), P (stm_lit Γ l)).
      Hypothesis (P_exp  : forall (Γ : Ctx (𝑿 * Ty)) (τ : Ty) (e : Exp Γ τ), P (stm_exp e)).
      Hypothesis (P_let  : forall (Γ : Ctx (𝑿 * Ty)) (x : 𝑿) (τ : Ty) (s : Stm Γ τ) (σ : Ty) (k : Stm (Γ ▻ (x ∶ τ)%ctx) σ), P s -> P k -> P (stm_let s k)).
      Hypothesis (P_block : forall (Γ Δ : Ctx (𝑿 * Ty)) (δ : LocalStore Δ) (σ : Ty) (k : Stm (Γ ▻▻ Δ) σ), P k -> P (stm_block Γ δ k)).
      Hypothesis (P_assign : forall (Γ : Ctx (𝑿 * Ty)) (x : 𝑿) (τ : Ty) (xInΓ : (x ∶ τ)%ctx ∈ Γ) (e : Stm Γ τ), P e -> P (stm_assign e)).
      Hypothesis (P_call  : forall (Γ Δ : Ctx (𝑿 * Ty)) (σ : Ty) (f : 𝑭 Δ σ) (es : NamedEnv (Exp Γ) Δ), P (stm_call f es)).
      Hypothesis (P_call_frame  : forall (Γ Δ : Ctx (𝑿 * Ty)) (δ : LocalStore Δ) (τ : Ty) (s : Stm Δ τ), P s -> P (stm_call_frame Γ δ s)).
      Hypothesis (P_call_external  : forall (Γ Δ : Ctx (𝑿 * Ty)) (σ : Ty) (f : 𝑭𝑿 Δ σ) (es : NamedEnv (Exp Γ) Δ), P (stm_call_external f es)).
      Hypothesis (P_if  : forall (Γ : Ctx (𝑿 * Ty)) (τ : Ty) (e : Exp Γ ty_bool) (s1 : Stm Γ τ) (s2 : Stm Γ τ), P s1 -> P s2 -> P (stm_if e s1 s2)).
      Hypothesis (P_seq  : forall (Γ : Ctx (𝑿 * Ty)) (τ : Ty) (e : Stm Γ τ) (σ : Ty) (k : Stm Γ σ), P e -> P k -> P (stm_seq e k)).
      Hypothesis (P_assert  : forall (Γ : Ctx (𝑿 * Ty)) (e1 : Exp Γ ty_bool) (e2 : Exp Γ ty_string), P (stm_assert e1 e2)).
      Hypothesis (P_fail  : forall (Γ : Ctx (𝑿 * Ty)) (τ : Ty) (s : Lit ty_string), P (stm_fail Γ τ s)).
      Hypothesis (P_match_list : forall (Γ : Ctx (𝑿 * Ty)) (σ τ : Ty) (e : Exp Γ (ty_list σ)) (alt_nil : Stm Γ τ) (xh xt : 𝑿) (alt_cons : Stm (Γ ▻ (xh ∶ σ)%ctx ▻ (xt ∶ ty_list σ)%ctx) τ),
            P alt_nil -> P alt_cons -> P (stm_match_list e alt_nil alt_cons)).
      Hypothesis (P_match_sum : forall (Γ : Ctx (𝑿 * Ty)) (σinl σinr τ : Ty) (e : Exp Γ (ty_sum σinl σinr)) (xinl : 𝑿) (alt_inl : Stm (Γ ▻ (xinl ∶ σinl)%ctx) τ) (xinr : 𝑿) (alt_inr : Stm (Γ ▻ (xinr ∶ σinr)%ctx) τ),
            P alt_inl -> P alt_inr -> P (stm_match_sum e alt_inl alt_inr)).
      Hypothesis (P_match_pair : forall (Γ : Ctx (𝑿 * Ty)) (σ1 σ2 τ : Ty) (e : Exp Γ (ty_prod σ1 σ2)) (xl xr : 𝑿) (rhs : Stm (Γ ▻ (xl ∶ σ1)%ctx ▻ (xr ∶ σ2)%ctx) τ),
            P rhs -> P (stm_match_pair e rhs)).
      Hypothesis (P_match_enum : forall (Γ : Ctx (𝑿 * Ty)) (E : 𝑬) (e : Exp Γ (ty_enum E)) (τ : Ty) (alts : 𝑬𝑲 E -> Stm Γ τ),
            (forall K : 𝑬𝑲 E, P (alts K)) -> P (stm_match_enum e alts)).
      Hypothesis (P_match_tuple : forall (Γ : Ctx (𝑿 * Ty)) (σs : Ctx Ty) (Δ : Ctx (𝑿 * Ty)) (e : Exp Γ (ty_tuple σs)) (p : TuplePat σs Δ) (τ : Ty) (rhs : Stm (Γ ▻▻ Δ) τ),
            P rhs -> P (stm_match_tuple e p rhs)).
      Hypothesis (P_match_union : forall (Γ : Ctx (𝑿 * Ty)) (U : 𝑼) (e : Exp Γ (ty_union U)) (τ : Ty) (alts : forall (K : 𝑼𝑲 U), Alternative Γ (𝑼𝑲_Ty K) τ),
            (forall K : 𝑼𝑲 U, P (proj_alt_rhs (alts K))) -> P (stm_match_union e alts)).
      Hypothesis (P_match_record : forall (Γ : Ctx (𝑿 * Ty)) (R : 𝑹) (Δ : Ctx (𝑿 * Ty)) (e : Exp Γ (ty_record R)) (p : RecordPat (𝑹𝑭_Ty R) Δ) (τ : Ty) (rhs : Stm (Γ ▻▻ Δ) τ),
            P rhs -> P (stm_match_record e p rhs)).
      Hypothesis (P_read_register : forall (Γ : Ctx (𝑿 * Ty)) (τ : Ty) (reg : 𝑹𝑬𝑮 τ),
            P (stm_read_register Γ reg)).
      Hypothesis (P_write_register : forall (Γ : Ctx (𝑿 * Ty)) (τ : Ty) (reg : 𝑹𝑬𝑮 τ) (e : Exp Γ τ),
            P (stm_write_register reg e)).
      Hypothesis (P_bind : forall (Γ : Ctx (𝑿 * Ty)) (σ τ : Ty) (s : Stm Γ σ) (k : Lit σ -> Stm Γ τ),
            P s -> (forall l : Lit σ, P (k l)) -> P (stm_bind s k)).

      Fixpoint Stm_rect {Γ : Ctx (𝑿 * Ty)} {τ : Ty} (s : Stm Γ τ) {struct s} : P s :=
        match s with
        | stm_lit _ _            => ltac:(apply P_lit; auto)
        | stm_exp _              => ltac:(apply P_exp; auto)
        | stm_let _ _            => ltac:(apply P_let; auto)
        | stm_block _ _ _        => ltac:(apply P_block; auto)
        | stm_assign _           => ltac:(apply P_assign; auto)
        | stm_call _ _           => ltac:(apply P_call; auto)
        | stm_call_frame _ _ _   => ltac:(apply P_call_frame; auto)
        | stm_call_external _ _  => ltac:(apply P_call_external; auto)
        | stm_if _ _ _           => ltac:(apply P_if; auto)
        | stm_seq _ _            => ltac:(apply P_seq; auto)
        | stm_assert _ _         => ltac:(apply P_assert; auto)
        | stm_fail _ _ _         => ltac:(apply P_fail; auto)
        | stm_match_list _ _ _   => ltac:(apply P_match_list; auto)
        | stm_match_sum _ _ _    => ltac:(apply P_match_sum; auto)
        | stm_match_pair _ _     => ltac:(apply P_match_pair; auto)
        | stm_match_enum _ _     => ltac:(apply P_match_enum; auto)
        | stm_match_tuple _ _ _  => ltac:(apply P_match_tuple; auto)
        | stm_match_union _ _    => ltac:(apply P_match_union; auto)
        | stm_match_record _ _ _ => ltac:(apply P_match_record; auto)
        | stm_read_register _ _  => ltac:(apply P_read_register; auto)
        | stm_write_register _ _ => ltac:(apply P_write_register; auto)
        | stm_bind _ _           => ltac:(apply P_bind; auto)
        end.

    End StmElimination.

    Definition Stm_rec (P : forall Γ σ, Stm Γ σ -> Set) := Stm_rect P.
    Definition Stm_ind (P : forall Γ σ, Stm Γ σ -> Prop) := Stm_rect P.

    Global Arguments stm_lit {_} _ _.
    Global Arguments stm_exp {_ _} _.
    Global Arguments stm_let {_} _ _ _ {_} _.
    Global Arguments stm_block {_ _} _ {_} _.
    Global Arguments stm_assign {_} _ {_ _} _.
    Global Arguments stm_call {_%ctx _%ctx _} _ _%arg.
    Global Arguments stm_call_frame {_} _ _ _ _.
    Global Arguments stm_call_external {_%ctx _%ctx _} _ _%arg.
    Global Arguments stm_if {_ _} _ _ _.
    Global Arguments stm_seq {_ _} _ {_} _.
    Global Arguments stm_assert {_} _ _.
    Global Arguments stm_fail {_} _ _.
    Global Arguments stm_match_list {_ _ _} _ _ _ _ _.
    Global Arguments stm_match_sum {_ _ _ _} _ _ _ _ _.
    Global Arguments stm_match_pair {_ _ _ _} _ _ _ _.
    Global Arguments stm_match_enum {_%ctx} _ _%exp {_} _%stm.
    Global Arguments stm_match_tuple {_ _ _} _ _%pat {_} _.
    Global Arguments stm_match_union {_} _ _ {_} _.
    Global Arguments stm_match_record {_} _ {_} _ _ {_} _.
    Global Arguments stm_read_register {_ _} _.
    Global Arguments stm_write_register {_ _} _ _.

  End Statements.

  Bind Scope stm_scope with Stm.
  Bind Scope pat_scope with Pattern.
  Bind Scope pat_scope with TuplePat.
  Bind Scope pat_scope with RecordPat.

  Section PatternMatching.

    Fixpoint tuple_pattern_match {σs : Ctx Ty} {Δ : Ctx (𝑿 * Ty)}
             (p : TuplePat σs Δ) {struct p} : Lit (ty_tuple σs) -> LocalStore Δ :=
      match p with
      | tuplepat_nil => fun _ => env_nil
      | tuplepat_snoc p x =>
        fun lit =>
          env_snoc
            (tuple_pattern_match p (fst lit)) (x, _)
            (snd lit)
      end.

    Fixpoint record_pattern_match {rfs : Ctx (𝑹𝑭 * Ty)}  {Δ : Ctx (𝑿 * Ty)}
             (p : RecordPat rfs Δ) {struct p} : NamedEnv Lit rfs -> LocalStore Δ :=
      match p with
      | recordpat_nil => fun _ => env_nil
      | recordpat_snoc p rf x =>
        fun E =>
          env_snoc
            (record_pattern_match p (env_tail E)) (x, _)
            (env_lookup E inctx_zero)
      end.

    Definition pattern_match {σ : Ty} {Δ : Ctx (𝑿 * Ty)} (p : Pattern Δ σ) :
      Lit σ -> LocalStore Δ :=
      match p with
      | pat_var x => env_snoc env_nil (x,_)
      | pat_unit => fun _ => env_nil
      | pat_pair x y => fun '(u , v) => (env_nil ► (x ∶ _)%ctx ↦ u ► (y ∶ _)%ctx ↦ v)%env
      | pat_tuple p => tuple_pattern_match p
      end.

  End PatternMatching.

  (* Record FunDef (Δ : Ctx (𝑿 * Ty)) (τ : Ty) : Set := *)
  (*   { fun_body : Stm Δ τ }. *)

  Section NameResolution.

    (* Ideally the following smart constructors would perform name resolution
       and fill in the de Bruijn index and the type of a variable. Unfortunately,
       they critically rely on the order that type-checking is performed. For
       instance in context Γ := (ε ▻ ("x", ty_int)) the expression
       (@exp_smart_var Γ "x" tt) type-checks while the (@exp_smart_var _ "x" tt)
       fails to type-check with error message

         The term "tt" has type "unit" while it is expected
         to have type "IsSome (ctx_resolve ?Γ0 "x")".

       So the variable ?Γ0 has not been unified and blocks the evaluation of
       ctx_resolve. Unfortunately, Coq decides to fail immediately.
     *)
    Definition exp_smart_var {Γ : Ctx (𝑿 * Ty)} (x : 𝑿) {p : IsSome (ctx_resolve Γ x)} :
      Exp Γ (fromSome (ctx_resolve Γ x) p) :=
      @exp_var Γ x (fromSome (ctx_resolve Γ x) p) (mk_inctx Γ x p).

    Definition stm_smart_assign {Γ : Ctx (𝑿 * Ty)} (x : 𝑿) {p : IsSome (ctx_resolve Γ x)} :
      Stm Γ (fromSome (ctx_resolve Γ x) p) -> Stm Γ (fromSome (ctx_resolve Γ x) p) :=
      @stm_assign Γ x (fromSome _ p) (mk_inctx Γ x p).

    (* Instead we hook mk_inctx directly into the typeclass resolution mechanism.
       Apparently, the unification of Γ is performed before the resolution so
       evaluation of ctx_resolve and mk_inctx is not blocked. This hook is more
       generally defined in MicroSail.Context.
     *)

  End NameResolution.

  Definition SymInstance (Σ : Ctx (𝑺 * Ty)) : Type := NamedEnv Lit Σ.
  Bind Scope env_scope with SymInstance.

  Section SymbolicTerms.

    Local Unset Elimination Schemes.

    Inductive Term (Σ : Ctx (𝑺 * Ty)) : Ty -> Type :=
    | term_var     (ς : 𝑺) (σ : Ty) {ςInΣ : InCtx (ς , σ) Σ} : Term Σ σ
    | term_lit     (σ : Ty) : Lit σ -> Term Σ σ
    | term_binop   {σ1 σ2 σ3 : Ty} (op : BinOp σ1 σ2 σ3) (e1 : Term Σ σ1) (e2 : Term Σ σ2) : Term Σ σ3
    | term_neg     (e : Term Σ ty_int) : Term Σ ty_int
    | term_not     (e : Term Σ ty_bool) : Term Σ ty_bool
    | term_inl     {σ1 σ2 : Ty} : Term Σ σ1 -> Term Σ (ty_sum σ1 σ2)
    | term_inr     {σ1 σ2 : Ty} : Term Σ σ2 -> Term Σ (ty_sum σ1 σ2)
    | term_list    {σ : Ty} (es : list (Term Σ σ)) : Term Σ (ty_list σ)
    (* Experimental features *)
    | term_bvec    {n} (es : Vector.t (Term Σ ty_bit) n) : Term Σ (ty_bvec n)
    | term_tuple   {σs : Ctx Ty} (es : Env (Term Σ) σs) : Term Σ (ty_tuple σs)
    | term_projtup {σs : Ctx Ty} (e : Term Σ (ty_tuple σs)) (n : nat) {σ : Ty}
                   {p : ctx_nth_is σs n σ} : Term Σ σ
    | term_union   {U : 𝑼} (K : 𝑼𝑲 U) (e : Term Σ (𝑼𝑲_Ty K)) : Term Σ (ty_union U)
    | term_record  (R : 𝑹) (es : NamedEnv (Term Σ) (𝑹𝑭_Ty R)) : Term Σ (ty_record R)
    | term_projrec {R : 𝑹} (e : Term Σ (ty_record R)) (rf : 𝑹𝑭) {σ : Ty}
                   {rfInR : InCtx (rf , σ) (𝑹𝑭_Ty R)} : Term Σ σ.
    Local Set Transparent Obligations.
    Derive NoConfusion Signature for Term.

    Global Arguments term_var {_} _ {_ _}.
    Global Arguments term_lit {_} _ _.
    Global Arguments term_neg {_} _.
    Global Arguments term_not {_} _.
    Global Arguments term_inl {_ _ _} _.
    Global Arguments term_inr {_ _ _} _.
    Global Arguments term_list {_ _} _.
    Global Arguments term_bvec {_ _} _%exp.
    Global Arguments term_tuple {_ _} _%exp.
    Global Arguments term_projtup {_ _} _%exp _ {_ _}.
    Global Arguments term_union {_} _ _.
    Global Arguments term_record {_} _ _.
    Global Arguments term_projrec {_ _} _ _ {_ _}.

    Definition term_enum {Σ} (E : 𝑬) (k : 𝑬𝑲 E) : Term Σ (ty_enum E) :=
      term_lit (ty_enum E) k.
    Global Arguments term_enum {_} _ _.

    Section Term_rect.

      Variable (Σ : Ctx (𝑺 * Ty)).
      Variable (P  : forall t : Ty, Term Σ t -> Type).
      Arguments P _ _ : clear implicits.

      Let PL (σ : Ty) : list (Term Σ σ) -> Type :=
        List.fold_right (fun t ts => P _ t * ts)%type unit.
      Let PV (n : nat) (es : Vector.t (Term Σ ty_bit) n) : Type :=
        Vector.fold_right (fun e ps => P _ e * ps)%type es unit.
      Let PE : forall σs, Env (Term Σ) σs -> Type :=
        Env_rect (fun _ _ => Type) unit (fun _ ts IHts _ t => IHts * P _ t)%type.
      Let PNE : forall (σs : Ctx (𝑹𝑭 * Ty)), NamedEnv (Term Σ) σs -> Type :=
        Env_rect (fun _ _ => Type) unit (fun _ ts IHts _ t => IHts * P _ t)%type.

      Hypothesis (P_var        : forall (ς : 𝑺) (σ : Ty) (ςInΣ : (ς , σ) ∈ Σ), P σ (term_var ς)).
      Hypothesis (P_lit        : forall (σ : Ty) (l : Lit σ), P σ (term_lit σ l)).
      Hypothesis (P_binop      : forall (σ1 σ2 σ3 : Ty) (op : BinOp σ1 σ2 σ3) (e1 : Term Σ σ1) (e2 : Term Σ σ2), P σ1 e1 -> P σ2 e2 -> P σ3 (term_binop op e1 e2)).
      Hypothesis (P_neg        : forall e : Term Σ ty_int, P ty_int e -> P ty_int (term_neg e)).
      Hypothesis (P_not        : forall e : Term Σ ty_bool, P ty_bool e -> P ty_bool (term_not e)).
      Hypothesis (P_inl        : forall (σ1 σ2 : Ty) (t : Term Σ σ1), P σ1 t -> P (ty_sum σ1 σ2) (term_inl t)).
      Hypothesis (P_inr        : forall (σ1 σ2 : Ty) (t : Term Σ σ2), P σ2 t -> P (ty_sum σ1 σ2) (term_inr t)).
      Hypothesis (P_list       : forall (σ : Ty) (es : list (Term Σ σ)), PL es -> P (ty_list σ) (term_list es)).
      Hypothesis (P_bvec       : forall (n : nat) (es : Vector.t (Term Σ ty_bit) n), PV es -> P (ty_bvec n) (term_bvec es)).
      Hypothesis (P_tuple      : forall (σs : Ctx Ty) (es : Env (Term Σ) σs), PE es -> P (ty_tuple σs) (term_tuple es)).
      Hypothesis (P_projtup    : forall (σs : Ctx Ty) (e : Term Σ (ty_tuple σs)), P (ty_tuple σs) e -> forall (n : nat) (σ : Ty) (p : ctx_nth_is σs n σ), P σ (@term_projtup _ _ e n _ p)).
      Hypothesis (P_union      : forall (U : 𝑼) (K : 𝑼𝑲 U) (e : Term Σ (𝑼𝑲_Ty K)), P (𝑼𝑲_Ty K) e -> P (ty_union U) (term_union U K e)).
      Hypothesis (P_record     : forall (R : 𝑹) (es : NamedEnv (Term Σ) (𝑹𝑭_Ty R)), PNE es -> P (ty_record R) (term_record R es)).
      Hypothesis (P_projrec    : forall (R : 𝑹) (e : Term Σ (ty_record R)), P (ty_record R) e -> forall (rf : 𝑹𝑭) (σ : Ty) (rfInR : (rf ∶ σ)%ctx ∈ 𝑹𝑭_Ty R), P σ (term_projrec e rf)).

      Fixpoint Term_rect (σ : Ty) (t : Term Σ σ) : P σ t :=
        match t with
        | @term_var _ ς σ ςInΣ           => ltac:(eapply P_var; eauto)
        | @term_lit _ σ x                => ltac:(eapply P_lit; eauto)
        | term_binop op e1 e2            => ltac:(eapply P_binop; eauto)
        | @term_neg _ e                  => ltac:(eapply P_neg; eauto)
        | @term_not _ e                  => ltac:(eapply P_not; eauto)
        | @term_inl _ σ1 σ2 x            => ltac:(eapply P_inl; eauto)
        | @term_inr _ σ1 σ2 x            => ltac:(eapply P_inr; eauto)
        | @term_bvec _ _ es              => ltac:(apply P_bvec; induction es; cbn; auto using unit)
        | @term_list _ σ es              => ltac:(eapply P_list; induction es; cbn; eauto using unit)
        | @term_tuple _ σs es            => ltac:(eapply P_tuple; induction es; cbn; eauto using unit)
        | @term_projtup _ σs e n σ p     => ltac:(eapply P_projtup; eauto)
        | @term_union _ U K e            => ltac:(eapply P_union; eauto)
        | @term_record _ R es            => ltac:(eapply P_record; induction es; cbn; eauto using unit)
        | @term_projrec _ R e rf σ rfInR => ltac:(eapply P_projrec; eauto)
        end.

    End Term_rect.

    Definition Term_ind Σ (P : forall σ, Term Σ σ -> Prop) := Term_rect P.

    Fixpoint inst_term {Σ : Ctx (𝑺 * Ty)} (ι : SymInstance Σ) {σ : Ty} (t : Term Σ σ) {struct t} : Lit σ :=
      match t in Term _ σ return Lit σ with
      | @term_var _ x _      => (ι ‼ x)%lit
      | term_lit _ l         => l
      | term_binop op e1 e2  => eval_binop op (inst_term ι e1) (inst_term ι e2)
      | term_neg e           => Z.opp (inst_term ι e)
      | term_not e           => negb (inst_term ι e)
      | term_inl e           => inl (inst_term ι e)
      | term_inr e           => inr (inst_term ι e)
      | term_list es         => List.map (fun e => inst_term ι e) es
      | term_bvec es         => Vector.t_rect
                                 _ (fun m (_ : Vector.t (Term Σ ty_bit) m) => Word.word m)
                                 Word.WO (fun eb m _ (vs : Word.word m) =>
                                            match inst_term ι eb with
                                            | bitzero => Word.WS false vs
                                            | bitone => Word.WS true vs
                                            end)
                                 _ es
      | term_tuple es        => Env_rect
                                  (fun σs _ => Lit (ty_tuple σs))
                                  tt
                                  (fun σs _ (vs : Lit (ty_tuple σs)) σ e => (vs, inst_term ι e))
                                  es
      | @term_projtup _ σs e n σ p => tuple_proj σs n σ (inst_term ι e) p
      | @term_union _ U K e     => 𝑼_fold (existT K (inst_term ι e))
      | @term_record _ R es     => 𝑹_fold (Env_rect
                                             (fun σs _ => NamedEnv Lit σs)
                                             env_nil
                                             (fun σs _ vs _ e => env_snoc vs _ (inst_term ι e)) es)
      | @term_projrec _ _ e rf    => 𝑹_unfold (inst_term ι e) ‼ rf
      end.

    Section TermEquivalence.

      Context {Σ : Ctx (𝑺 * Ty)} {σ : Ty}.

      Definition TermEqv : relation (Term Σ σ) :=
        fun t1 t2 => forall (ι : SymInstance Σ),
          inst_term ι t1 = inst_term ι t2.

      Global Instance TermEqv_Equiv : Equivalence TermEqv.
      Proof. split; congruence. Qed.

    End TermEquivalence.

    Section TermEqvB.

      Context {Σ : Ctx (𝑺 * Ty)}.

      Fixpoint Term_eqvb {σ τ} (t1 : Term Σ σ) (t2 : Term Σ τ) {struct t1} : option bool :=
        match t1 , t2 with
        | @term_var _ _ _ ς1inΣ , @term_var _ _ _ ς2inΣ =>
          if InCtx_eqb ς1inΣ ς2inΣ
          then Some true
          else None
        | term_lit σ l1 , term_lit τ l2 =>
          match Ty_eq_dec σ τ with
          | left  p => Some (Lit_eqb τ (eq_rect σ Lit l1 τ p) l2)
          | right _ => Some false
          end
        | term_neg x   , term_neg y   => Term_eqvb x y
        | term_not x   , term_not y   => Term_eqvb x y
        | term_inl x   , term_inl y   => Term_eqvb x y
        | term_inl _   , term_inr _   => Some false
        | term_inr _   , term_inl _   => Some false
        | term_inr x   , term_inr y   => Term_eqvb x y
        | _            , _            => None
        end.

    End TermEqvB.

    Equations(noind) Term_eqb {Σ} {σ : Ty} (t1 t2 : Term Σ σ) : bool :=
      Term_eqb (@term_var _ _ ς1inΣ) (@term_var _ _ ς2inΣ) :=
        InCtx_eqb ς1inΣ ς2inΣ;
      Term_eqb (term_lit _ l1) (term_lit _ l2) := Lit_eqb _ l1 l2;
      Term_eqb (term_binop op1 x1 y1) (term_binop op2 x2 y2)
        with binop_eqdep_dec op1 op2 => {
        Term_eqb (term_binop op1 x1 y1) (term_binop op2 x2 y2) (left opeq_refl) :=
          Term_eqb x1 x2 && Term_eqb y1 y2;
        Term_eqb (term_binop op1 x1 y1) (term_binop op2 x2 y2) (right _) := false
      };
      Term_eqb (term_neg x) (term_neg y) := Term_eqb x y;
      Term_eqb (term_not x) (term_not y) := Term_eqb x y;
      Term_eqb (term_inl x) (term_inl y) := Term_eqb x y;
      Term_eqb (term_inr x) (term_inr y) := Term_eqb x y;
      Term_eqb (term_list xs) (term_list ys) := list_beq Term_eqb xs ys;
      Term_eqb (term_bvec xs) (term_bvec ys) := Vector.eqb _ Term_eqb xs ys;
      Term_eqb (term_tuple x) (term_tuple y) :=
         @env_beq _ (Term Σ) (@Term_eqb _) _ x y;
      Term_eqb (@term_projtup σs x n _ p) (@term_projtup τs y m _ q)
        with eq_dec σs τs => {
        Term_eqb (@term_projtup σs x n _ p) (@term_projtup ?(σs) y m _ q) (left eq_refl) :=
          (n =? m) && Term_eqb x y;
        Term_eqb (@term_projtup _ x n _ p) (@term_projtup _ y m _ q) (right _) := false
        };
      Term_eqb (@term_union ?(u) _ k1 e1) (@term_union u _ k2 e2)
        with 𝑼𝑲_eq_dec k1 k2 => {
        Term_eqb (term_union k1 e1) (term_union k2 e2) (left eq_refl) :=
          Term_eqb e1 e2;
        Term_eqb _ _ (right _) := false
      };
      Term_eqb (@term_record ?(r) xs) (@term_record r ys) :=
         @env_beq _ (fun b => Term Σ (snd b)) (fun b => @Term_eqb _ (snd b)) _ xs ys;
      Term_eqb (@term_projrec r1 e1 _ _ prf1) (@term_projrec r2 e2 _ _ prf2)
               with (𝑹_eq_dec r1 r2) => {
      Term_eqb (@term_projrec r e1 _ _ prf1) (@term_projrec ?(r) e2 _ _ prf2)
        (left eq_refl) := (@inctx_at _ _ _ prf1 =? @inctx_at _ _ _ prf2) && Term_eqb e1 e2;
      Term_eqb (@term_projrec r1 e1 _ _ prf1) (@term_projrec r2 e2 _ _ prf2)
        (right _) := false };

      Term_eqb _ _ := false.

    Local Transparent Term_eqb.
    Set Equations With UIP.
    Lemma Term_eqb_spec Σ (σ : Ty) (t1 t2 : Term Σ σ) :
      reflect (t1 = t2) (Term_eqb t1 t2).
    Proof.
      induction t1 using Term_rect; cbn [Term_eqb]; dependent elimination t2;
        microsail_solve_eqb_spec.
      - unfold InCtx_eqb.
        repeat match goal with
               | |- context[?m =? ?n] => destruct (Nat.eqb_spec m n)
               | H: InCtx _ _ |- _ =>
                 let n := fresh "n" in
                 let p := fresh "p" in
                 destruct H as [n p]
               end; cbn in *; constructor.
        + subst n0.
          match goal with
          | H1: ctx_nth_is ?Σ ?n ?b1, H2: ctx_nth_is ?Σ ?n ?b2 |- _ =>
            let H := fresh in
            pose proof (ctx_nth_is_right_exact _ _ _ H1 H2) as H; inversion H; clear H
          end.
          subst ς0.
          f_equal.
          f_equal.
          apply ctx_nth_is_proof_irrelevance.
        + inversion 1. congruence.
      - match goal with
        | |- context[Lit_eqb _ ?l1 ?l2] => destruct (Lit_eqb_spec _ l1 l2); cbn
        end; microsail_solve_eqb_spec.
      - destruct (binop_eqdep_dec op op0) as [e|ne]; cbn.
        + dependent elimination e; cbn.
          microsail_solve_eqb_spec.
        + constructor; intro e.
          dependent elimination e.
          apply ne; constructor.
      - revert es0.
        induction es as [|x xs]; intros [|y ys]; cbn in *; try (constructor; congruence).
        + constructor. intros ?. dependent elimination H.
        + constructor. intros ?. dependent elimination H.
        + destruct X as [x1 x2].
          specialize (IHxs x2 ys).
          specialize (x1 y).
          microsail_solve_eqb_spec.
          intro H. apply n. inversion H.
          dependent elimination H1.
          constructor.
      - admit.
      - admit.
      - admit.
      - destruct (𝑼𝑲_eq_dec K K0); cbn.
        + destruct e. specialize (IHt1 e4). microsail_solve_eqb_spec.
        + microsail_solve_eqb_spec.
      - admit.
      - admit.
    Admitted.

  End SymbolicTerms.
  Bind Scope exp_scope with Term.

  Section OccursCheck.

    Import stdpp.base.

    (* Most explicit type-signatures given below are only necessary for Coq 8.9
       and can be cleaned up for later versions. *)
    Fixpoint occurs_check_index {Σ} {x y : 𝑺 * Ty} {struct Σ} :
      forall (m n : nat) (p : ctx_nth_is Σ m x) (q : ctx_nth_is Σ n y),
        option (y ∈ ctx_remove {| inctx_at := m; inctx_valid := p |}) :=
      match Σ with
      | ctx_nil => fun m n _ (q : ctx_nth_is ctx_nil n y) => match q with end
      | ctx_snoc Σ b =>
        fun (m n : nat) =>
          match m , n with
          | 0   , 0   => fun _ _ => None
          | 0   , S n => fun p (q : ctx_nth_is (ctx_snoc Σ b) (S n) y) =>
                          Some (@MkInCtx _ _ (ctx_remove (@MkInCtx _ _ (ctx_snoc Σ b) 0 p)) n q)
          | S m , 0   => fun _ (q : ctx_nth_is (ctx_snoc Σ b) 0 y) =>
                          Some (@MkInCtx _ _ (ctx_snoc (Σ - x) b) 0 q)
          | S m , S n => fun p q => option_map inctx_succ (occurs_check_index m n p q)
          end
      end.

    Definition occurs_check_var {Σ} {x y : 𝑺 * Ty} (xIn : x ∈ Σ) (yIn : y ∈ Σ) : option (y ∈ Σ - x) :=
      occurs_check_index (inctx_at xIn) (inctx_at yIn) inctx_valid inctx_valid.

    Fixpoint occurs_check {Σ x} (xIn : x ∈ Σ) {σ} (t : Term Σ σ) : option (Term (Σ - x) σ) :=
      match t with
      | @term_var _ ς σ0 ςInΣ =>
        ςInΣ' ← occurs_check_var xIn ςInΣ; mret (@term_var _ _ _ ςInΣ')
      | term_lit σ0 l => mret (term_lit σ0 l)
      | term_binop op t1 t2 =>
        t1' ← occurs_check xIn t1; t2' ← occurs_check xIn t2; mret (term_binop op t1' t2')
      | term_neg t => t' ← occurs_check xIn t ; mret (term_neg t')
      | term_not t => t' ← occurs_check xIn t ; mret (term_not t')
      | term_inl t => t' ← occurs_check xIn t ; mret (term_inl t')
      | term_inr t => t' ← occurs_check xIn t ; mret (term_inr t')
      | term_list es => option_map term_list (traverse_list (occurs_check xIn) es)
      | term_bvec es => option_map term_bvec (traverse_vector (occurs_check xIn) es)
      | term_tuple es => option_map term_tuple (traverse_env (@occurs_check _ _ xIn) es)
      | @term_projtup _ σs t n σ p =>
        t' ← occurs_check xIn t ; mret (@term_projtup _ _ t' n _ p)
      | term_union U K t => t' ← occurs_check xIn t ; mret (term_union U K t')
      | term_record R es => option_map (term_record R) (traverse_env (fun _ => occurs_check xIn) es)
      | term_projrec t rf => t' ← occurs_check xIn t ; mret (term_projrec t' rf)
      end.

    Fixpoint occurs_check_index_sum {Σ} {x y : 𝑺 * Ty} {struct Σ} :
      forall (m n : nat) (p : ctx_nth_is Σ m x) (q : ctx_nth_is Σ n y),
        (x = y) + (y ∈ ctx_remove {| inctx_at := m; inctx_valid := p |}) :=
      match Σ with
      | ctx_nil => fun m n _ (q : ctx_nth_is ctx_nil n y) => match q with end
      | ctx_snoc Σ b =>
        fun m n =>
          match m , n with
          | 0   , 0   => fun (p : ctx_nth_is (Σ ▻ b) 0 x) q =>
                          inl (eq_trans (eq_sym p) q)
          | 0   , S n => fun p (q : ctx_nth_is (ctx_snoc Σ b) (S n) y) =>
                          inr (@MkInCtx _ _ (ctx_remove (@MkInCtx _ _ (ctx_snoc Σ b) 0 p)) n q)
          | S m , 0   => fun _ (q : ctx_nth_is (ctx_snoc Σ b) 0 y) =>
                          inr (@MkInCtx _ _ (ctx_snoc (Σ - x) b) 0 q)
          | S m , S n => fun p q => sum_map id inctx_succ (occurs_check_index_sum m n p q)
          end
      end.

    Definition occurs_check_var_sum {Σ} {x y : 𝑺 * Ty} (xIn : x ∈ Σ) (yIn : y ∈ Σ) : (x = y) + (y ∈ Σ - x) :=
      occurs_check_index_sum (inctx_at xIn) (inctx_at yIn) inctx_valid inctx_valid.

  End OccursCheck.

  Section SymbolicSubstitutions.

    Definition Sub (Σ1 Σ2 : Ctx (𝑺 * Ty)) : Type :=
      Env (fun b => Term Σ2 (snd b)) Σ1.
    (* Hint Unfold Sub. *)

    Fixpoint sub_term {σ} {Σ1 Σ2 : Ctx (𝑺 * Ty)} (ζ : Sub Σ1 Σ2) (t : Term Σ1 σ) {struct t} : Term Σ2 σ :=
      match t with
      | term_var ς                => (ζ ‼ ς)%lit
      | term_lit σ l              => term_lit σ l
      | term_binop op t1 t2       => term_binop op (sub_term ζ t1) (sub_term ζ t2)
      | term_neg t0               => term_neg (sub_term ζ t0)
      | term_not t0               => term_not (sub_term ζ t0)
      | @term_inl _ σ1 σ2 t0      => term_inl (sub_term ζ t0)
      | @term_inr _ σ1 σ2 t0      => term_inr (sub_term ζ t0)
      | @term_list _ σ es         => term_list (List.map (sub_term ζ) es)
      | term_bvec es              => term_bvec (Vector.map (sub_term ζ) es)
      | term_tuple es             => term_tuple (env_map (fun σ => @sub_term σ _ _ ζ) es)
      | @term_projtup _ _ t n σ p => term_projtup (sub_term ζ t) n (p := p)
      | term_union U K t0         => term_union U K (sub_term ζ t0)
      | term_record R es          => term_record R (env_map (fun _ => sub_term ζ) es)
      | term_projrec t rf         => term_projrec (sub_term ζ t) rf
      end.

    Class Subst (T : Ctx (𝑺 * Ty) -> Type) : Type :=
      subst : forall {Σ1 Σ2 : Ctx (𝑺 * Ty)}, Sub Σ1 Σ2 -> T Σ1 -> T Σ2.
    Global Arguments subst {T _ _ _} _ _.

    Global Instance SubstTerm {σ} : Subst (fun Σ => Term Σ σ) :=
      fun Σ1 Σ2 ζ => sub_term ζ.
    Global Instance SubstPair {A B} `{Subst A, Subst B} : Subst (fun Σ => A Σ * B Σ)%type :=
      fun Σ1 Σ2 ζ '(a,b) => (subst ζ a, subst ζ b).
    Global Instance SubstList {A} `{Subst A} : Subst (fun Σ => list (A Σ))%type :=
      fun Σ1 Σ2 ζ => List.map (subst ζ).

    Definition sub_id Σ : Sub Σ Σ :=
      @env_tabulate _ (fun b => Term _ (snd b)) _
                    (fun '(ς , σ) ςIn => @term_var Σ ς σ ςIn).
    Global Arguments sub_id : clear implicits.

    Definition sub_snoc {Σ1 Σ2 : Ctx (𝑺 * Ty)} (ζ : Sub Σ1 Σ2)
      (b : 𝑺 * Ty) (t : Term Σ2 (snd b)) : Sub (Σ1 ▻ b) Σ2 :=
      env_snoc ζ b t.
    Global Arguments sub_snoc {_ _} _ _ _.

    Definition sub_wk1 {Σ b} : Sub Σ (Σ ▻ b) :=
      @env_tabulate _ (fun b => Term _ (snd b)) _
                    (fun '(ς , σ) ςIn => @term_var _ ς σ (inctx_succ ςIn)).

    Definition sub_comp {Σ1 Σ2 Σ3} (ζ1 : Sub Σ1 Σ2) (ζ2 : Sub Σ2 Σ3) : Sub Σ1 Σ3 :=
      env_map (fun _ => sub_term ζ2) ζ1.

    Definition wk1_term {Σ σ b} (t : Term Σ σ) : Term (Σ ▻ b) σ :=
      sub_term sub_wk1 t.

    Definition sub_up1 {Σ1 Σ2} (ζ : Sub Σ1 Σ2) {b : 𝑺 * Ty} : Sub (Σ1 ▻ b) (Σ2 ▻ b) :=
      let '(ς , σ) := b in
      env_snoc (env_map (fun _ => wk1_term) ζ) (ς , σ) (@term_var _ ς σ inctx_zero).

  End SymbolicSubstitutions.

  Section SymbolicLocalStore.

    Definition SymbolicLocalStore (Γ : Ctx (𝑿 * Ty)) (Σ : Ctx (𝑺 * Ty)) : Type :=
      NamedEnv (Term Σ) Γ.

    Definition lift_localstore {Γ Σ} : LocalStore Γ -> SymbolicLocalStore Γ Σ :=
      env_map (fun _ => term_lit _).
    Definition inst_localstore {Γ Σ}
      (ι : SymInstance Σ) (δ : SymbolicLocalStore Γ Σ) : LocalStore Γ :=
      env_map (fun _ => inst_term ι) δ.

    Lemma inst_lift_localstore {Γ Σ} (ι : SymInstance Σ) (δ : LocalStore Γ) :
      inst_localstore ι (lift_localstore δ) = δ.
    Proof.
      induction δ; cbn.
      - reflexivity.
      - f_equal. apply IHδ.
    Qed.

  End SymbolicLocalStore.
  Bind Scope env_scope with SymbolicLocalStore.

  Section Contracts.

    Definition Pred (A : Type) : Type := A -> Prop.

    Definition Final {Γ σ} (s : Stm Γ σ) : Prop :=
      match s with
      | stm_lit _ _   => True
      | stm_fail _ _ => True
      | _ => False
      end.

    Definition ResultOrFail {Γ σ} (s : Stm Γ σ) :
      forall (POST : Lit σ -> Prop), Prop :=
      match s with
      | stm_lit _ v => fun POST => POST v
      | stm_fail _ _ => fun _ => True
      | _ => fun _ => False
      end.

    Lemma result_or_fail_inversion {Γ σ} (s : Stm Γ σ) (POST : Lit σ -> Prop) :
      ResultOrFail s POST -> (exists msg, s = stm_fail _ msg)
                          \/ (exists v, s = stm_lit _ v /\ POST v).
    Proof. destruct s; cbn in *; try contradiction; eauto. Qed.

    (* This predicate encodes that the statement s is a finished computation and
       that the result is not a failure. This is a computational version that is
       better suited for the goal and the inversion below is better suited for
       a hypothesis. *)
    Definition ResultNoFail {Γ σ} (s : Stm Γ σ) :
      forall (POST : Lit σ -> Prop), Prop :=
      match s with
      | stm_lit _ v => fun POST => POST v
      | _ => fun _ => False
      end.

    Lemma result_no_fail_inversion {Γ σ} (s : Stm Γ σ) (POST : Lit σ -> Prop) :
      ResultNoFail s POST -> exists v, s = stm_lit _ v /\ POST v.
    Proof. destruct s; cbn in *; try contradiction; eauto. Qed.

  End Contracts.

  Section GenericRegStore.

    Lemma 𝑹𝑬𝑮_eq_dec_refl {σ} : forall (r : 𝑹𝑬𝑮 σ),
      𝑹𝑬𝑮_eq_dec r r = left (@teq_refl Ty _ σ σ r r eq_refl eq_refl).
    Proof.
      intros r.
      destruct (𝑹𝑬𝑮_eq_dec r r).
      + dependent destruction t.
        dependent destruction eqi.
        now dependent destruction eqf.
      + destruct (n (@teq_refl Ty 𝑹𝑬𝑮 σ σ r r eq_refl ltac:(auto))).
    Qed.

    Lemma 𝑹𝑬𝑮_eq_dec_distinct {σ τ} : forall (r : 𝑹𝑬𝑮 σ) (k : 𝑹𝑬𝑮 τ),
        ~ r ≡ k -> exists (prf : ~ r ≡ k), 𝑹𝑬𝑮_eq_dec r k = right prf.
    Proof.
      intros.
      destruct (𝑹𝑬𝑮_eq_dec r k).
      + destruct (H t).
      + f_equal.
        now exists n.
    Qed.

    Definition GenericRegStore : Type := forall σ, 𝑹𝑬𝑮 σ -> Lit σ.

    Definition generic_write_register (γ : GenericRegStore) {σ} (r : 𝑹𝑬𝑮 σ)
      (v : Lit σ) : GenericRegStore :=
      fun τ r' =>
        match 𝑹𝑬𝑮_eq_dec r r' with
        | left (teq_refl _ eqt _) => eq_rect σ Lit v τ eqt
        | right _ => γ τ r'
        end.

    Definition generic_read_register (γ : GenericRegStore) {σ} (r : 𝑹𝑬𝑮 σ) :
      Lit σ := γ _ r.

    Lemma generic_read_write γ {σ} (r : 𝑹𝑬𝑮 σ) (v : Lit σ) :
      generic_read_register (generic_write_register γ r v) r = v.
    Proof.
      unfold generic_read_register, generic_write_register.
      destruct (𝑹𝑬𝑮_eq_dec r r) as [[eqσ eqr]|].
      - symmetry. apply Eqdep_dec.eq_rect_eq_dec, Ty_eq_dec.
      - contradict n. now apply teq_refl with eq_refl.
    Qed.

    Lemma generic_read_write_distinct γ {σ τ} (r : 𝑹𝑬𝑮 σ) (k : 𝑹𝑬𝑮 τ)
          (prf : ~ r ≡ k) (v : Lit σ) :
      generic_read_register (generic_write_register γ r v) k = generic_read_register γ k.
    Proof.
      unfold generic_read_register, generic_write_register.
      destruct (𝑹𝑬𝑮_eq_dec_distinct prf) as [prf' H].
      now rewrite H.
    Qed.

    Lemma generic_write_read γ {σ} (r : 𝑹𝑬𝑮 σ) :
      generic_write_register γ r (generic_read_register γ r) = γ.
    Proof.
      extensionality τ. extensionality r'.
      unfold generic_write_register, generic_read_register.
      destruct (𝑹𝑬𝑮_eq_dec r r') as [[eqt eqr]|]; now subst.
    Qed.

    Lemma generic_write_write γ {σ} (r : 𝑹𝑬𝑮 σ) (v1 v2 : Lit σ) :
      generic_write_register (generic_write_register γ r v1) r v2 =
      generic_write_register γ r v2.
    Proof.
      extensionality τ. extensionality r'.
      unfold generic_write_register, generic_read_register.
      destruct (𝑹𝑬𝑮_eq_dec r r') as [[eqσ eqr]|]; now cbn.
    Qed.

  End GenericRegStore.

  Notation "'lit_int' l" := (exp_lit _ ty_int l) (at level 1, no associativity) : exp_scope.
  Notation "'lit_bool' l" := (exp_lit _ ty_bool l) (at level 1, no associativity) : exp_scope.
  Notation "'lit_string' s" := (exp_lit _ ty_string s%string) (at level 1, no associativity) : exp_scope.
  Notation "e1 && e2" := (exp_binop binop_and e1 e2) : exp_scope.
  Notation "e1 || e2" := (exp_binop binop_or e1 e2) : exp_scope.
  Notation "e1 + e2" := (exp_binop binop_plus e1 e2) : exp_scope.
  Notation "e1 * e2" := (exp_binop binop_times e1 e2) : exp_scope.
  Notation "e1 - e2" := (exp_binop binop_minus e1 e2) : exp_scope.
  Notation "e1 < e2" := (exp_binop binop_lt e1 e2) : exp_scope.
  Notation "e1 > e2" := (exp_binop binop_gt e1 e2) : exp_scope.
  Notation "e1 <= e2" := (exp_binop binop_le e1 e2) : exp_scope.
  Notation "e1 = e2" := (exp_binop binop_eq e1 e2) : exp_scope.
  Notation "- e" := (exp_neg e) : exp_scope.
  Notation "e ․ f" := (* Using Unicode Character “․” (U+2024) *)
      (@exp_projrec _ _ e f%string _ _)
        (at level 9, no associativity, format
         "e ․ f") : exp_scope.

  Notation "[ x , .. , z ]" :=
    (tuplepat_snoc .. (tuplepat_snoc tuplepat_nil x) .. z) (at level 0) : pat_scope.
  Notation "[ x , .. , z ]" :=
    (env_snoc .. (env_snoc env_nil (_,_) x) .. (_,_) z) (at level 0) : arg_scope.

  Notation "'if:' e 'then' s1 'else' s2" := (stm_if e%exp s1%stm s2%stm)
    (at level 99, right associativity, format
     "'[hv' 'if:'  e  '/' '[' 'then'  s1  ']' '/' '[' 'else'  s2 ']' ']'"
    ) : stm_scope.

  Notation "'let:' x := s1 'in' s2" := (stm_let x _ s1%stm s2%stm)
    (at level 100, right associativity, x at level 75, s1 at next level, format
     "'let:'  x  :=  s1  'in'  '/' s2"
    ) : stm_scope.
  Notation "'let:' x ∶ τ := s1 'in' s2" := (stm_let x%string τ s1%stm s2%stm)
    (at level 100, right associativity, x at level 75, τ at next level, s1 at next level, format
     "'let:'  x  ∶  τ  :=  s1  'in'  '/' s2"
    ) : stm_scope.
  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1%exp => rhs1%stm
                                  | alt2%exp => rhs2%stm
                                  end))
    (at level 100, alt1 pattern, alt2 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' 'end' ']'"
    ) : stm_scope.
  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1 => rhs1%stm
                                  | alt2 => rhs2%stm
                                  | alt3 => rhs3%stm
                                  end))
    (at level 100, alt1 pattern, alt2 pattern, alt3 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' 'end' ']'"
    ) : stm_scope.
  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1 => rhs1%stm
                                  | alt2 => rhs2%stm
                                  | alt3 => rhs3%stm
                                  | alt4 => rhs4%stm
                                  end))
    (at level 100, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' |  alt4  =>  rhs4  '/' 'end' ']'"
    ) : stm_scope.
  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 | alt5 => rhs5 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1 => rhs1%stm
                                  | alt2 => rhs2%stm
                                  | alt3 => rhs3%stm
                                  | alt4 => rhs4%stm
                                  | alt5 => rhs5%stm
                                  end))
    (at level 100, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, alt5 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' |  alt4  =>  rhs4  '/' |  alt5  =>  rhs5  '/' 'end' ']'"
    ) : stm_scope.
  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 | alt5 => rhs5 | alt6 => rhs6 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1 => rhs1%stm
                                  | alt2 => rhs2%stm
                                  | alt3 => rhs3%stm
                                  | alt4 => rhs4%stm
                                  | alt5 => rhs5%stm
                                  | alt6 => rhs6%stm
                                  end))
    (at level 100, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, alt5 pattern, alt6 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' |  alt4  =>  rhs4  '/' |  alt5  =>  rhs5  '/' |  alt6  =>  rhs6  '/' 'end' ']'"
    ) : stm_scope.

  (* Notation "'match:' e 'in' U 'with' | alt1 x1 => rhs1 | alt2 x2 => rhs2 'end'" := *)
  (*   (@stm_match_union _ U e _ *)
  (*     (fun K => match K with *)
  (*               | alt1%exp => x1 *)
  (*               | alt2%exp => x2 *)
  (*               end) *)
  (*     (fun K => match K return Stm _ _ with *)
  (*               | alt1%exp => rhs1%stm *)
  (*               | alt2%exp => rhs2%stm *)
  (*               end) *)
  (*   ) *)
  (*   (at level 100, alt1 pattern, alt2 pattern, format *)
  (*    "'[hv' 'match:'  e  'in'  U  'with'  '/' |  alt1  x1  =>  rhs1  '/' |  alt2  x2  =>  rhs2  '/' 'end' ']'" *)
  (*     ) : stm_scope. *)

  Notation "'match:' e 'with' | 'inl' p1 => rhs1 | 'inr' p2 => rhs2 'end'" :=
    (stm_match_sum e p1 rhs1 p2 rhs2) (at level 100, only parsing) : stm_scope.

  Notation "'match:' e 'in' '(' σ1 ',' σ2 ')' 'with' | '(' fst ',' snd ')' => rhs 'end'" :=
    (@stm_match_pair _ σ1 σ2 _ e fst snd rhs)
    (at level 100, fst pattern, snd pattern, format
     "'[hv' 'match:' e 'in' '(' σ1 ',' σ2 ')' 'with' '/' | '(' fst ',' snd ')' => rhs '/' 'end' ']'"
    ) : stm_scope.

  Notation "'call' f a1 .. an" :=
    (stm_call f (env_snoc .. (env_snoc env_nil (_,_) a1%exp) .. (_,_) an%exp))
    (at level 10, f global, a1, an at level 9) : stm_scope.
  Notation "'callex' f a1 .. an" :=
    (stm_call_external f (env_snoc .. (env_snoc env_nil (_,_) a1%exp) .. (_,_) an%exp))
    (at level 10, f global, a1, an at level 9) : stm_scope.

  Notation "'call' f" :=
    (stm_call f env_nil)
    (at level 10, f global) : stm_scope.
  Notation "'callex' f" :=
    (stm_call_external f env_nil)
    (at level 10, f global) : stm_scope.

  Notation "s1 ;; s2" := (stm_seq s1 s2) : stm_scope.
  Notation "x <- s" := (stm_assign x s)
    (at level 80, s at next level) : stm_scope.
  Notation "'fail' s" := (stm_fail _ s)
    (at level 10, no associativity) : stm_scope.

End Terms.

(******************************************************************************)

Module Type ProgramKit
       (Import typekit : TypeKit)
       (Import termkit : TermKit typekit).
  Module TM := Terms typekit termkit.
  Export TM.

  (* We choose to make [RegStore] a parameter so the users of the module would be able to
     instantiate it with their own data structure and [read_regsiter]/[write_register]
     functions *)
  Parameter RegStore : Type.
  (* Definition RegStore : Type := forall σ, 𝑹𝑬𝑮 σ -> Lit σ. *)
  Bind Scope env_scope with RegStore.
  Parameter read_register : forall (γ : RegStore) {σ} (r : 𝑹𝑬𝑮 σ), Lit σ.
  Parameter write_register : forall (γ : RegStore) {σ} (r : 𝑹𝑬𝑮 σ) (v : Lit σ), RegStore.

  Parameter read_write : forall (γ : RegStore) σ (r : 𝑹𝑬𝑮 σ) (v : Lit σ),
            read_register (write_register γ r v) r = v.

  Parameter read_write_distinct : forall (γ : RegStore) σ τ (r : 𝑹𝑬𝑮 σ) (k : 𝑹𝑬𝑮 τ)
                                    (prf : ~ r ≡ k) (v : Lit σ),
            read_register (write_register γ r v) k = read_register γ k.

  Parameter write_read : forall (γ : RegStore) σ (r : 𝑹𝑬𝑮 σ),
            (write_register γ r (read_register γ r)) = γ.

  Parameter write_write : forall (γ : RegStore) σ (r : 𝑹𝑬𝑮 σ) (v1 v2 : Lit σ),
            write_register (write_register γ r v1) r v2 = write_register γ r v2.

  (* Memory model *)
  Parameter Memory : Type.
  (* Step relation for calling an external function. The complete function call
     is done in one step. The result of an external call is either a failure
     with an error message msg (res = inl msg) or a successful computation with
     a result value v (res = inr v).
   *)
  Parameter ExternalCall :
    forall
      {Δ σ} (f : 𝑭𝑿 Δ σ)
      (args : LocalStore Δ)
      (res  : string + Lit σ)
      (γ γ' : RegStore)
      (μ μ' : Memory), Prop.
  Parameter ExternalProgress :
    forall {Δ σ} (f : 𝑭𝑿 Δ σ) (args : LocalStore Δ) γ μ,
    exists γ' μ' res, ExternalCall f args res γ γ' μ μ'.

  (* Bind Scope env_scope with Memory. *)
  (* Parameter read_memory : forall (μ : Memory) (addr : 𝑨𝑫𝑫𝑹), Lit ty_int. *)
  (* Parameter write_memory : forall (μ : Memory) (addr : 𝑨𝑫𝑫𝑹) (v : Lit ty_int), Memory. *)

  (* Parameter Inline Pi : forall {Δ τ} (f : 𝑭 Δ τ), FunDef Δ τ. *)
  Parameter Inline Pi : forall {Δ τ} (f : 𝑭 Δ τ), Stm Δ τ.

End ProgramKit.

Module Programs
       (typekit : TypeKit)
       (termkit : TermKit typekit)
       (progkit : ProgramKit typekit termkit).
  Export progkit.

  Inductive Contract (Δ : Ctx (𝑿 * Ty)) (τ : Ty) : Type :=
  | ContractNoFail
      (pre : abstract_named Lit Δ (RegStore -> Prop))
      (post: abstract_named Lit Δ (Lit τ -> RegStore -> Prop))
  | ContractTerminateNoFail
      (pre : abstract_named Lit Δ (RegStore -> Prop))
      (post: abstract_named Lit Δ (Lit τ -> RegStore -> Prop))
  | ContractTerminate
      (pre : abstract_named Lit Δ (RegStore -> Prop))
      (post: abstract_named Lit Δ (Lit τ -> RegStore -> Prop))
  | ContractNone.

  Definition ContractEnv : Type :=
    forall Δ τ (f : 𝑭 Δ τ), Contract Δ τ.
  Definition ContractEnvEx : Type :=
    forall Δ τ (f : 𝑭𝑿 Δ τ), Contract Δ τ.

End Programs.

Module Type ContractKit
       (Import typekit : TypeKit)
       (Import termkit : TermKit typekit)
       (Import progkit : ProgramKit typekit termkit).

  Module PM := Programs typekit termkit progkit.
  Export PM.

  Parameter Inline CEnv   : ContractEnv.
  Parameter Inline CEnvEx : ContractEnvEx.

End ContractKit.
