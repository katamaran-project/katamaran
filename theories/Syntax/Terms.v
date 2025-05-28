(******************************************************************************)
(* Copyright (c) 2019 Dominique Devriese, Georgy Lukyanov,                    *)
(*   Sander Huyghebaert, Steven Keuchel                                       *)
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
     ssr.ssrbool.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Context
     Environment
     Notations
     Prelude
     Bitvector
     Syntax.BinOps
     Syntax.TypeDecl
     Syntax.UnOps
     Syntax.Variables
     Tactics.

Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.
Local Set Transparent Obligations.
Local Unset Elimination Schemes.

Module Type TermsOn (Import TY : Types).

  Local Notation PCtx := (NCtx PVar Ty).
  Local Notation LCtx := (NCtx LVar Ty).

  Inductive Term (Σ : LCtx) : Ty -> Set :=
  | term_var     (ς : LVar) (σ : Ty) {ςInΣ : ς∷σ ∈ Σ} : Term Σ σ
  | term_val     (σ : Ty) : Val σ -> Term Σ σ
  | term_binop   {σ1 σ2 σ3 : Ty} (op : BinOp σ1 σ2 σ3) (e1 : Term Σ σ1) (e2 : Term Σ σ2) : Term Σ σ3
  | term_unop    {σ1 σ2 : Ty} (op : UnOp σ1 σ2) (t : Term Σ σ1) : Term Σ σ2
  | term_tuple   {σs} (ts : Env (Term Σ) σs) : Term Σ (ty.tuple σs)
  | term_union   {U : unioni} (K : unionk U) (t : Term Σ (unionk_ty U K)) : Term Σ (ty.union U)
  | term_record  (R : recordi) (ts : NamedEnv (Term Σ) (recordf_ty R)) : Term Σ (ty.record R).
  #[global] Arguments term_var {_} _ {_ _}.
  #[global] Arguments term_val {_} _ _.
  #[global] Arguments term_tuple {_ _} ts.
  #[global] Arguments term_union {_} U K t.
  #[global] Arguments term_record {_} R ts.
  Bind Scope term_scope with Term.
  Derive NoConfusion Signature for Term.

  Definition term_enum {Σ} (E : enumi) (k : enumt E) : Term Σ (ty.enum E) :=
    term_val (ty.enum E) k.
  #[global] Arguments term_enum {_} _ _.

  Fixpoint term_list {Σ σ} (ts : list (Term Σ σ)) : Term Σ (ty.list σ) :=
    match ts with
    | nil       => term_val (ty.list σ) nil
    | cons t ts => term_binop bop.cons t (term_list ts)
    end.

  Fixpoint term_bvec {Σ n} (es : Vector.t (Term Σ ty.bool) n) : Term Σ (ty.bvec n) :=
    match es with
    | Vector.nil       => term_val (ty.bvec 0) bv.nil
    | Vector.cons e es => term_binop bop.bvcons e (term_bvec es)
    end.

  Definition term_relop_neg [Σ σ] (op : RelOp σ) :
    forall (t1 t2 : Term Σ σ), Term Σ ty.bool :=
    match op with
    | bop.eq     => term_binop (bop.relop bop.neq)
    | bop.neq    => term_binop (bop.relop bop.eq)
    | bop.le     => Basics.flip (term_binop (bop.relop bop.lt))
    | bop.lt     => Basics.flip (term_binop (bop.relop bop.le))
    | bop.bvsle  => Basics.flip (term_binop (bop.relop bop.bvslt))
    | bop.bvslt  => Basics.flip (term_binop (bop.relop bop.bvsle))
    | bop.bvule  => Basics.flip (term_binop (bop.relop bop.bvult))
    | bop.bvult  => Basics.flip (term_binop (bop.relop bop.bvule))
    end.

  Section Term_rect.

    Variable (Σ : LCtx).
    Variable (P  : forall t : Ty, Term Σ t -> Type).
    Arguments P _ _ : clear implicits.

    Let PE : forall (σs : Ctx Ty), Env (Term Σ) σs -> Type :=
      fun σs es => env.All P es.
    Let PNE : forall (σs : NCtx recordf Ty), NamedEnv (Term Σ) σs -> Type :=
      fun σs es => env.All (fun b t => P (type b) t) es.

    Hypothesis (P_var        : forall (ς : LVar) (σ : Ty) (ςInΣ : ς∷σ ∈ Σ), P σ (term_var ς)).
    Hypothesis (P_val        : forall (σ : Ty) (v : Val σ), P σ (term_val σ v)).
    Hypothesis (P_binop      : forall (σ1 σ2 σ3 : Ty) (op : BinOp σ1 σ2 σ3) (e1 : Term Σ σ1) (e2 : Term Σ σ2), P σ1 e1 -> P σ2 e2 -> P σ3 (term_binop op e1 e2)).
    Hypothesis (P_unop       : forall (σ1 σ2 : Ty) (op : UnOp σ1 σ2) (t : Term Σ σ1), P σ1 t -> P σ2 (term_unop op t)).
    Hypothesis (P_tuple      : forall (σs : Ctx Ty) (es : Env (Term Σ) σs) (IH : PE es), P (ty.tuple σs) (term_tuple es)).
    Hypothesis (P_union      : forall (U : unioni) (K : unionk U) (e : Term Σ (unionk_ty U K)), P (unionk_ty U K) e -> P (ty.union U) (term_union U K e)).
    Hypothesis (P_record     : forall (R : recordi) (es : NamedEnv (Term Σ) (recordf_ty R)) (IH : PNE es), P (ty.record R) (term_record R es)).

    Fixpoint Term_rect (σ : Ty) (t : Term Σ σ) {struct t} : P σ t :=
      match t with
      | term_var ς                  => ltac:(eapply P_var; eauto)
      | term_val σ v                => ltac:(eapply P_val; eauto)
      | term_binop op t1 t2         => ltac:(eapply P_binop; eauto)
      | term_unop op t              => ltac:(eapply P_unop; eauto)
      | term_tuple ts               => ltac:(eapply P_tuple, env.all_intro; eauto)
      | term_union U K t            => ltac:(eapply P_union; eauto)
      | term_record R ts            => ltac:(eapply P_record, env.all_intro; eauto)
      end.

  End Term_rect.

  Definition Term_rec Σ (P : forall σ, Term Σ σ -> Set) := @Term_rect _ P.
  Definition Term_ind Σ (P : forall σ, Term Σ σ -> Prop) := @Term_rect _ P.

  Section Term_bool_case.

    Context {Σ : LCtx} [P : Term Σ ty.bool -> Type].

    Variable (pvar : forall (ς : LVar) (ςInΣ : ς∷ty.bool ∈ Σ), P (term_var ς)).
    Variable (pval : forall (v : Val ty.bool), P (term_val ty.bool v)).
    Variable (pand : forall (e1 : Term Σ ty.bool) (e2 : Term Σ ty.bool), P (term_binop bop.and e1 e2)).
    Variable (por : forall (e1 : Term Σ ty.bool) (e2 : Term Σ ty.bool), P (term_binop bop.or e1 e2)).
    Variable (prel : forall σ (op : RelOp σ) (e1 e2 : Term Σ σ), P (term_binop (bop.relop op) e1 e2)).
    Variable (pnot : forall t : Term Σ ty.bool, P (term_unop uop.not t)).

    Equations(noeqns) Term_bool_case (t : Term Σ ty.bool) : P t :=
    | term_var ς                    => @pvar ς _
    | term_val _ b                  => @pval b
    | term_binop bop.and s t        => pand s t
    | term_binop (bop.relop op) s t => prel op s t
    | term_binop bop.or s t         => por s t
    | term_unop uop.not t           => pnot t.

  End Term_bool_case.

  Section Term_int_case.

    Context {Σ : LCtx} [P : Term Σ ty.int -> Type].

    Variable (pvar : forall (ς : LVar) (ςInΣ : ς∷ty.int ∈ Σ), P (term_var ς)).
    Variable (pval : forall (v : Val ty.int), P (term_val ty.int v)).
    Variable (pplus : forall (e1 : Term Σ ty.int) (e2 : Term Σ ty.int), P e1 -> P e2 -> P (term_binop bop.plus e1 e2)).
    Variable (pminus : forall (e1 : Term Σ ty.int) (e2 : Term Σ ty.int), P e1 -> P e2 -> P (term_binop bop.minus e1 e2)).
    Variable (ptimes : forall (e1 : Term Σ ty.int) (e2 : Term Σ ty.int), P e1 -> P e2 -> P (term_binop bop.times e1 e2)).
    Variable (pland : forall (e1 : Term Σ ty.int) (e2 : Term Σ ty.int), P e1 -> P e2 -> P (term_binop bop.land e1 e2)).
    Variable (pneg : forall t : Term Σ ty.int, P t -> P (term_unop uop.neg t)).
    Variable (psigned : forall {n} (e : Term Σ (ty.bvec n)), P (term_unop uop.signed e)).
    Variable (punsigned : forall {n} (e : Term Σ (ty.bvec n)), P (term_unop uop.unsigned e)).

    Equations(noeqns) Term_int_ind (t : Term Σ ty.int) : P t :=
    | term_var ς               => @pvar ς _
    | term_val _ b             => @pval b
    | term_binop bop.plus s t  => pplus (Term_int_ind s) (Term_int_ind t)
    | term_binop bop.minus s t => pminus (Term_int_ind s) (Term_int_ind t)
    | term_binop bop.times s t => ptimes (Term_int_ind s) (Term_int_ind t)
    | term_binop bop.land s t  => pland (Term_int_ind s) (Term_int_ind t)
    | term_unop uop.neg t      => pneg (Term_int_ind t)
    | term_unop uop.signed t   => psigned t
    | term_unop uop.unsigned t => punsigned t.

  End Term_int_case.

  Section Term_bv_case.

    Context {Σ : LCtx} [P : forall n, Term Σ (ty.bvec n) -> Type].

    Variable (pvar : forall n (ς : LVar) (ςInΣ : ς∷ty.bvec n ∈ Σ), P (term_var ς)).
    Variable (pval : forall n (v : Val (ty.bvec n)), P (term_val (ty.bvec n) v)).
    Variable (pbvadd : forall n (e1 : Term Σ (ty.bvec n)) (e2 : Term Σ (ty.bvec n)), P (term_binop bop.bvadd e1 e2)).
    Variable (pbvsub : forall n (e1 : Term Σ (ty.bvec n)) (e2 : Term Σ (ty.bvec n)), P (term_binop bop.bvsub e1 e2)).
    Variable (pbvmul : forall n (e1 : Term Σ (ty.bvec n)) (e2 : Term Σ (ty.bvec n)), P (term_binop bop.bvmul e1 e2)).
    Variable (pbvand : forall n (e1 : Term Σ (ty.bvec n)) (e2 : Term Σ (ty.bvec n)), P (term_binop bop.bvand e1 e2)).
    Variable (pbvor : forall n (e1 : Term Σ (ty.bvec n)) (e2 : Term Σ (ty.bvec n)), P (term_binop bop.bvor e1 e2)).
    Variable (pbvxor : forall n (e1 : Term Σ (ty.bvec n)) (e2 : Term Σ (ty.bvec n)), P (term_binop bop.bvxor e1 e2)).
    Variable (pshiftr : forall n m (e1 : Term Σ (ty.bvec n)) (e2 : Term Σ (ty.bvec m)), P (term_binop bop.shiftr e1 e2)).
    Variable (pshiftl : forall n m (e1 : Term Σ (ty.bvec n)) (e2 : Term Σ (ty.bvec m)), P (term_binop bop.shiftl e1 e2)).
    Variable (pbvapp : forall n1 n2 (e1 : Term Σ (ty.bvec n1)) (e2 : Term Σ (ty.bvec n2)), P (term_binop bop.bvapp e1 e2)).
    Variable (pbvcons : forall n (e1 : Term Σ ty.bool) (e2 : Term Σ (ty.bvec n)), P (term_binop bop.bvcons e1 e2)).
    Variable (pupdate_subrange : forall {n s l : nat} (pf : IsTrue (s + l <=? n)) (e1 : Term Σ (ty.bvec n)) (e2 : Term Σ (ty.bvec l)), P (term_binop (@bop.update_vector_subrange _ _ s l pf) e1 e2)).
    Variable (pbvnot : forall n (e : Term Σ (ty.bvec n)), P (term_unop uop.bvnot e)).
    Variable (pnegate : forall n (e : Term Σ (ty.bvec n)), P (term_unop uop.negate e)).
    Variable (psext : forall n m (pf : IsTrue (m <=? n)) (e : Term Σ (ty.bvec m)), P (term_unop (uop.sext (p := pf)) e)).
    Variable (pzext : forall n m (pf : IsTrue (m <=? n)) (e : Term Σ (ty.bvec m)), P (term_unop (uop.zext (p := pf)) e)).
    Variable (pgetslice : forall n (e : Term Σ ty.int), P (term_unop (uop.get_slice_int (n := n)) e)).
    Variable (ptruncate : forall n m (pf : IsTrue (n <=? m)) (e : Term Σ (ty.bvec m)), P (term_unop (@uop.truncate _ m n pf) e)).
    Variable (psubrange : forall n m s (pf : IsTrue (s + n <=? m)) (e : Term Σ (ty.bvec m)), P (term_unop (@uop.vector_subrange _ _ s n pf) e)).

    Equations(noeqns) Term_bv_case [n : nat] (t : Term Σ (ty.bvec n)) : P t :=
    | term_var ς                            => @pvar _ ς _
    | term_val _ b                          => @pval _ b
    | term_binop bop.bvadd s t              => pbvadd s t
    | term_binop bop.bvsub s t              => pbvsub s t
    | term_binop bop.bvmul s t              => pbvmul s t
    | term_binop bop.bvand s t              => pbvand s t
    | term_binop bop.bvor s t               => pbvor s t
    | term_binop bop.bvxor s t              => pbvxor s t
    | term_binop bop.shiftr s t             => pshiftr s t
    | term_binop bop.shiftl s t             => pshiftl s t
    | term_binop bop.bvapp s t              => pbvapp s t
    | term_binop bop.bvcons s t             => pbvcons s t
    | term_binop (bop.update_vector_subrange _ _) e t => pupdate_subrange _ e t
    | term_unop uop.bvnot t                 => pbvnot t
    | term_unop uop.negate t                => pnegate t
    | term_unop uop.sext t                  => psext _ _ t
    | term_unop uop.zext t                  => pzext _ _ t
    | term_unop uop.get_slice_int t         => pgetslice _ _
    | term_unop (uop.truncate _) t          => ptruncate _ _ t
    | term_unop (uop.vector_subrange _ _) t => psubrange _ _ _ t
    .

  End Term_bv_case.

  Section Term_bv_rect.

    Context {Σ : LCtx} [P : forall n, Term Σ (ty.bvec n) -> Type].

    Variable (pvar : forall n (ς : LVar) (ςInΣ : ς∷ty.bvec n ∈ Σ), P (term_var ς)).
    Variable (pval : forall n (v : Val (ty.bvec n)), P (term_val (ty.bvec n) v)).
    Variable (pbvadd : forall n (e1 : Term Σ (ty.bvec n)) (e2 : Term Σ (ty.bvec n)), P e1 -> P e2 -> P (term_binop bop.bvadd e1 e2)).
    Variable (pbvsub : forall n (e1 : Term Σ (ty.bvec n)) (e2 : Term Σ (ty.bvec n)), P e1 -> P e2 -> P (term_binop bop.bvsub e1 e2)).
    Variable (pbvmul : forall n (e1 : Term Σ (ty.bvec n)) (e2 : Term Σ (ty.bvec n)), P e1 -> P e2 -> P (term_binop bop.bvmul e1 e2)).
    Variable (pbvand : forall n (e1 : Term Σ (ty.bvec n)) (e2 : Term Σ (ty.bvec n)), P e1 -> P e2 -> P (term_binop bop.bvand e1 e2)).
    Variable (pbvor : forall n (e1 : Term Σ (ty.bvec n)) (e2 : Term Σ (ty.bvec n)), P e1 -> P e2 -> P (term_binop bop.bvor e1 e2)).
    Variable (pbvxor : forall n (e1 : Term Σ (ty.bvec n)) (e2 : Term Σ (ty.bvec n)), P e1 -> P e2 -> P (term_binop bop.bvxor e1 e2)).
    Variable (pshiftr : forall n m (e1 : Term Σ (ty.bvec n)) (e2 : Term Σ (ty.bvec m)), P e1 -> P e2 -> P (term_binop bop.shiftr e1 e2)).
    Variable (pshiftl : forall n m (e1 : Term Σ (ty.bvec n)) (e2 : Term Σ (ty.bvec m)), P e1 -> P e2 -> P (term_binop bop.shiftl e1 e2)).
    Variable (pbvapp : forall n1 n2 (e1 : Term Σ (ty.bvec n1)) (e2 : Term Σ (ty.bvec n2)), P e1 -> P e2 -> P (term_binop bop.bvapp e1 e2)).
    Variable (pbvcons : forall n (e1 : Term Σ ty.bool) (e2 : Term Σ (ty.bvec n)), P e2 -> P (term_binop bop.bvcons e1 e2)).
    Variable (pupdate_subrange : forall {n s l : nat} (pf : IsTrue (s + l <=? n)) (e1 : Term Σ (ty.bvec n)) (e2 : Term Σ (ty.bvec l)), P e1 -> P e2 -> P (term_binop (@bop.update_vector_subrange _ _ s l pf) e1 e2)).
    Variable (pbvnot : forall n (e : Term Σ (ty.bvec n)), P e -> P (term_unop uop.bvnot e)).
    Variable (pnegate : forall n (e : Term Σ (ty.bvec n)), P e -> P (term_unop uop.negate e)).
    Variable (psext : forall n m (pf : IsTrue (m <=? n)) (e : Term Σ (ty.bvec m)), P e -> P (term_unop (uop.sext (p := pf)) e)).
    Variable (pzext : forall n m (pf : IsTrue (m <=? n)) (e : Term Σ (ty.bvec m)), P e -> P (term_unop (uop.zext (p := pf)) e)).
    Variable (pgetslice : forall n (e : Term Σ ty.int), P (term_unop (uop.get_slice_int (n := n)) e)).
    Variable (ptruncate : forall n m (pf : IsTrue (n <=? m)) (e : Term Σ (ty.bvec m)), P e -> P (term_unop (@uop.truncate _ m n pf) e)).
    Variable (psubrange : forall n m s (pf : IsTrue (s + n <=? m)) (e : Term Σ (ty.bvec m)), P e -> P (term_unop (@uop.vector_subrange _ _ s n pf) e)).

    Fixpoint Term_bv_rect [n : nat] (t : Term Σ (ty.bvec n)) {struct t} : P t :=
      Term_bv_case (P := P)
        ltac:(intros; apply pvar)
        ltac:(intros; apply pval)
        ltac:(intros; apply pbvadd; auto)
        ltac:(intros; apply pbvsub; auto)
        ltac:(intros; apply pbvmul; auto)
        ltac:(intros; apply pbvand; auto)
        ltac:(intros; apply pbvor; auto)
        ltac:(intros; apply pbvxor; auto)
        ltac:(intros; apply pshiftr; auto)
        ltac:(intros; apply pshiftl; auto)
        ltac:(intros; apply pbvapp; auto)
        ltac:(intros; apply pbvcons; auto)
        ltac:(intros; apply pupdate_subrange; auto)
        ltac:(intros; apply pbvnot; auto)
        ltac:(intros; apply pnegate; auto)
        ltac:(intros; apply psext; auto)
        ltac:(intros; apply pzext; auto)
        ltac:(intros; apply pgetslice; auto)
        ltac:(intros; apply ptruncate; auto)
        ltac:(intros; apply psubrange; auto)
        t.

  End Term_bv_rect.

  Section Term_bool_ind.

    Context {Σ : LCtx} [P : Term Σ ty.bool -> Type].

    Variable (pvar : forall (ς : LVar) (ςInΣ : ς∷ty.bool ∈ Σ), P (term_var ς)).
    Variable (pval : forall (v : Val ty.bool), P (term_val ty.bool v)).
    Variable (pand : forall e1 e2, P e1 -> P e2 -> P (term_binop bop.and e1 e2)).
    Variable (por : forall e1 e2, P e1 -> P e2 -> P (term_binop bop.or e1 e2)).
    Variable (prel : forall σ (op : RelOp σ) e1 e2, P (term_binop (bop.relop op) e1 e2)).
    Variable (pnot : forall e, P e -> P (term_unop uop.not e)).

    Fixpoint Term_bool_ind (t : Term Σ ty.bool) : P t :=
      Term_bool_case
        pvar
        pval
        (fun t1 t2 => pand (Term_bool_ind t1) (Term_bool_ind t2))
        (fun t1 t2 => por (Term_bool_ind t1) (Term_bool_ind t2))
        prel
        (fun t1 => pnot (Term_bool_ind t1))
        t.

  End Term_bool_ind.

  Section Term_tuple_case.

    Context {Σ : LCtx} {σs : Ctx Ty} [P : Term Σ (ty.tuple σs) -> Type].

    Variable (pvar : forall (ς : LVar) (ςInΣ : ς∷ty.tuple σs ∈ Σ), P (term_var ς)).
    Variable (pval : forall (v : Val (ty.tuple σs)), P (term_val (ty.tuple σs) v)).
    Variable (ptuple : forall (ts : Env (Term Σ) σs), P (term_tuple ts)).

    Equations(noeqns) Term_tuple_case (t : Term Σ (ty.tuple σs)) : P t :=
    | term_var ς    => @pvar ς _
    | term_val _ v  => @pval v
    | term_tuple ts => ptuple ts.

  End Term_tuple_case.

  Section Term_union_case.

    Context {Σ : LCtx} {U : unioni} [P : Term Σ (ty.union U) -> Type].

    Variable (pvar : forall (ς : LVar) (ςInΣ : ς∷ty.union U ∈ Σ), P (term_var ς)).
    Variable (pval : forall (v : Val (ty.union U)), P (term_val (ty.union U) v)).
    Variable (punion : forall K (t : Term Σ (unionk_ty U K)), P (term_union U K t)).

    Equations(noeqns) Term_union_case (t : Term Σ (ty.union U)) : P t :=
    | term_var ς       => @pvar ς _
    | term_val _ v     => @pval v
    | term_union U K t => punion K t.

  End Term_union_case.

  Section Term_record_case.

    Context {Σ : LCtx} {R : recordi} [P : Term Σ (ty.record R) -> Type].

    Variable (pvar : forall (ς : LVar) (ςInΣ : ς∷ty.record R ∈ Σ), P (term_var ς)).
    Variable (pval : forall (v : Val (ty.record R)), P (term_val (ty.record R) v)).
    Variable (precord : forall (ts : NamedEnv (Term Σ) (recordf_ty R)), P (term_record R ts)).

    Equations(noeqns) Term_record_case (t : Term Σ (ty.record R)) : P t :=
    | term_var ς    => @pvar ς _
    | term_val _ v  => @pval v
    | term_record ts => precord ts.

  End Term_record_case.

  (* We define some specialized view for certain types to make
     recusion over terms easier. *)
  Section TermView.
    Local Set Elimination Schemes.

    (* A view on list terms. *)
    Inductive ListView {Σ σ} : Term Σ (ty.list σ) -> Type :=
    | term_list_var {ς} {ςInΣ : (ς∷ty.list σ) ∈ Σ} :
      ListView (term_var ς)
    | term_list_val v :
      ListView (term_val _ v)
    | term_list_cons h {t} (lv : ListView t) :
      ListView (term_binop bop.cons h t)
    | term_list_append {t1 t2} (lv1 : ListView t1) (lv2 : ListView t2) :
      ListView (term_binop bop.append t1 t2).
    #[global] Arguments term_list_var {Σ σ} ς {ςInΣ}.
    #[global] Arguments term_list_append {Σ σ} [t1 t2] lv1 lv2.

    (* We map each type to a specialized view for that type. *)
    Definition View {Σ} (σ : Ty) : Term Σ σ -> Type :=
      match σ with
      | ty.list τ => ListView
      | _         => fun _ => unit
      end.

    Definition view_var {Σ ς σ} : forall ςInΣ, View (@term_var Σ ς σ ςInΣ) :=
      match σ with
       | ty.list σ => @term_list_var _ _ ς
       | _         => fun _ => tt
       end.

    Definition view_val {Σ σ} : forall v, View (@term_val Σ σ v) :=
      match σ with
      | ty.list σ0 => term_list_val
      | _          => fun _ => tt
      end.

    Definition view_binop {Σ σ1 σ2 σ3} (op : BinOp σ1 σ2 σ3) :
      forall {t1 : Term Σ σ1} {t2 : Term Σ σ2},
        View t1 -> View t2 -> View (term_binop op t1 t2) :=
       match op with
       | bop.cons   => fun t1 t2 _  v2 => term_list_cons t1 v2
       | bop.append => term_list_append
       | _ => fun _ _ _ _ => tt
       end.

    Definition view_unop {Σ σ1 σ2} (op : UnOp σ1 σ2) :
      forall {t : Term Σ σ1},
        View t -> View (term_unop op t) :=
      match op with
      | uop.inl | _ => fun _ _ => tt
      end.

    (* Construct a view for each term. *)
    Fixpoint view {Σ σ} (t : Term Σ σ) {struct t} : View t :=
      match t as t1 in (Term _ t0) return (View t1) with
      | term_var ς          => view_var _
      | term_val _ v        => view_val v
      | term_binop op t1 t2 => view_binop op (view t1) (view t2)
      | term_unop op t      => view_unop op (view t)
      | _                   => tt
      end.

  End TermView.

  Open Scope lazy_bool_scope.

  Equations(noeqns) Term_eqb {Σ} [σ : Ty] (t1 t2 : Term Σ σ) : bool :=
    Term_eqb (@term_var _ _ ς1inΣ) (@term_var _ _ ς2inΣ) :=
      ctx.In_eqb ς1inΣ ς2inΣ;
    Term_eqb (term_val _ v1) (term_val _ v2) :=
      if eq_dec v1 v2 then true else false;
    Term_eqb (term_binop op1 x1 y1) (term_binop op2 x2 y2)
      with bop.eqdep_dec op1 op2 => {
      Term_eqb (term_binop op1 x1 y1) (term_binop ?(op1) x2 y2) (left bop.opeq_refl) :=
        Term_eqb x1 x2 &&& Term_eqb y1 y2;
      Term_eqb (term_binop op1 x1 y1) (term_binop op2 x2 y2) (right _) := false
    };
    Term_eqb (term_unop op1 t1) (term_unop op2 t2) with uop.tel_eq_dec op1 op2 => {
      Term_eqb (term_unop op1 t1) (term_unop ?(op1) t2) (left eq_refl) :=
        Term_eqb t1 t2;
      Term_eqb (term_unop op1 t1) (term_unop op2 t2) (right _) := false;
    };
    Term_eqb (@term_tuple ?(σs) xs) (@term_tuple σs ys) :=
      @env.eqb_hom _ (Term Σ) (@Term_eqb _) _ xs ys;
    Term_eqb (@term_union ?(u) _ k1 e1) (@term_union u _ k2 e2)
      with eq_dec k1 k2 => {
      Term_eqb (term_union k1 e1) (term_union ?(k1) e2) (left eq_refl) :=
        Term_eqb e1 e2;
      Term_eqb _ _ (right _) := false
    };
    Term_eqb (@term_record ?(r) xs) (@term_record r ys) :=
      @env.eqb_hom _ (fun b => Term Σ (type b)) (fun b => @Term_eqb _ (type b)) _ xs ys;
    Term_eqb _ _ := false.

  Local Set Equations With UIP.
  Lemma Term_eqb_spec Σ (σ : Ty) (t1 t2 : Term Σ σ) :
    reflect (t1 = t2) (Term_eqb t1 t2).
  Proof.
    induction t1 using Term_rect; cbn [Term_eqb]; dependent elimination t2;
      solve_eqb_spec with
      repeat match goal with
          | |- context[eq_dec ?l1 ?l2] => destruct (eq_dec l1 l2)
          | |- context[bop.eqdep_dec ?x ?y] =>
              let e := fresh in
              destruct (bop.eqdep_dec x y) as [e|];
              [dependent elimination e|]
          | |- context[uop.tel_eq_dec ?x ?y] =>
              let e := fresh in
              destruct (uop.tel_eq_dec x y) as [e|];
              [dependent elimination e|]
          | H: ~ bop.OpEq ?o ?o |- False => apply H; constructor
          end.
    - apply (@ssrbool.iffP (es = ts)); solve_eqb_spec.
      apply env.eqb_hom_spec_point, IH.
    - apply (@ssrbool.iffP (es = ts0)); solve_eqb_spec.
      apply env.eqb_hom_spec_point, IH.
  Qed.

  Section Symbolic.

    Polymorphic Definition List (A : LCtx -> Type) (Σ : LCtx) : Type :=
      list (A Σ).
    Definition Const (A : Type) (Σ : LCtx) : Type :=
      A.

  End Symbolic.

  Section SymbolicSubstitutions.

    Definition Sub (Σ1 Σ2 : LCtx) : Set :=
      Env (fun b => Term Σ2 (type b)) Σ1.
    (* Hint Unfold Sub. *)

    Class Subst (T : LCtx -> Type) : Type :=
      subst : forall {Σ1 : LCtx}, T Σ1 -> forall {Σ2 : LCtx}, Sub Σ1 Σ2 -> T Σ2.
    #[global] Arguments subst {T _ Σ1} t {Σ2} ζ.

    Fixpoint sub_term {σ Σ1} (t : Term Σ1 σ) {Σ2} (ζ : Sub Σ1 Σ2) {struct t} : Term Σ2 σ :=
      match t with
      | term_var ς                 => ζ.[??ς]
      | term_val σ v               => term_val σ v
      | term_binop op t1 t2        => term_binop op (sub_term t1 ζ) (sub_term t2 ζ)
      | term_unop op t             => term_unop op (sub_term t ζ)
      | term_tuple ts              => term_tuple (env.map (fun _ t => sub_term t ζ) ts)
      | term_union U K t           => term_union U K (sub_term t ζ)
      | term_record R ts           => term_record R (env.map (fun _ t => sub_term t ζ) ts)
      end.

    #[export] Instance SubstTerm {σ} : Subst (fun Σ => Term Σ σ) :=
      @sub_term σ.
    #[export,universes(polymorphic=yes)] Instance SubstList {A} `{Subst A} : Subst (List A) :=
      fix substlist {Σ1} xs {Σ2} ζ :=
        match xs with
        | nil => nil
        | cons x xs => cons (subst x ζ) (substlist xs ζ)
        end.

    Lemma substlist_is_map_subst {A} `{Subst A} {Σ1 Σ2} (xs : List A Σ1) (ζ : Sub Σ1 Σ2) :
      subst xs ζ = List.map (fun x => subst x ζ) xs.
    Proof. induction xs; cbn; f_equal; auto. Qed.

    #[export] Instance SubstConst {A} : Subst (Const A) | 10 :=
       fun _ x _ _ => x.
    #[export] Instance SubstEnv {B : Set} {A : Ctx _ -> B -> Set} `{forall b, Subst (fun Σ => A Σ b)} {Δ : Ctx B} :
      Subst (fun Σ => Env (A Σ) Δ) :=
      fun Σ1 xs Σ2 ζ => env.map (fun b a => subst (T := fun Σ => A Σ b) a ζ) xs.

    Definition sub_id Σ : Sub Σ Σ :=
      @env.tabulate _ (fun b => Term _ (type b)) _
                    (fun '(ς∷σ) ςIn => @term_var Σ ς σ ςIn).
    #[global] Arguments sub_id : clear implicits.

    Definition sub_snoc {Σ1 Σ2 : LCtx} (ζ : Sub Σ1 Σ2) b (t : Term Σ2 (type b)) :
      Sub (Σ1 ▻ b) Σ2 := env.snoc ζ b t.
    #[global] Arguments sub_snoc {_ _} _ _ _.

    Definition sub_shift {Σ b} (bIn : b ∈ Σ) : Sub (Σ - b) Σ :=
      env.tabulate
        (D := fun b => Term Σ (type b))
        (fun '(x∷τ) xIn => @term_var Σ x τ (ctx.shift_var bIn xIn)).

    Definition sub_wk1 {Σ b} : Sub Σ (Σ ▻ b) :=
      env.tabulate
        (D := fun b => Term _ (type b))
        (fun '(ς∷σ) ςIn => @term_var _ ς σ (ctx.in_succ ςIn)).

    Definition sub_cat_left {Σ} Δ : Sub Σ (Σ ▻▻ Δ) :=
      env.tabulate
        (D := fun b => Term _ (type b))
        (fun '(ς∷σ) ςIn => @term_var _ ς σ (ctx.in_cat_left Δ ςIn)).

    Definition sub_cat_right {Σ} Δ : Sub Δ (Σ ▻▻ Δ) :=
      env.tabulate
        (D := fun b => Term _ (type b))
        (fun '(ς∷σ) ςIn => @term_var _ ς σ (ctx.in_cat_right ςIn)).

    Definition sub_up1 {Σ1 Σ2} (ζ : Sub Σ1 Σ2) {b} : Sub (Σ1 ▻ b) (Σ2 ▻ b) :=
      sub_snoc (subst ζ sub_wk1) b (let '(ς∷σ) := b in @term_var _ ς σ ctx.in_zero).

    Definition sub_up {Σ1 Σ2} (ζ : Sub Σ1 Σ2) Δ : Sub (Σ1 ▻▻ Δ) (Σ2 ▻▻ Δ) :=
      subst ζ (sub_cat_left Δ) ►► sub_cat_right Δ.

    Definition sub_single {Σ x} (xIn : x ∈ Σ) (t : Term (Σ - x) (type x)) : Sub Σ (Σ - x) :=
       @env.tabulate _
         (fun b => Term (Σ - x) (@type _ _ b)) Σ
         (fun y (yIn : y ∈ Σ) =>
            match ctx.occurs_check_view xIn yIn
            in @ctx.OccursCheckView _ _ _ _ y i
            return Term (Σ - x) (@type _ _ y)
            with
            | ctx.Same _     => t
            | ctx.Diff _ yIn => @term_var _ _ _ yIn
            end).

    Class SubstLaws (T : LCtx -> Type) `{Subst T} : Type :=
      { subst_sub_id Σ (t : T Σ) :
          subst t (sub_id _) = t;
        subst_sub_comp Σ0 Σ1 Σ2 (ζ1 : Sub Σ0 Σ1) (ζ2 : Sub Σ1 Σ2) t :
          subst t (subst ζ1 ζ2) = subst (subst t ζ1) ζ2;
      }.

    #[global] Arguments SubstLaws T {_}.

    #[export] Instance SubstLawsTerm {σ} : SubstLaws (fun Σ => Term Σ σ).
    Proof.
      constructor.
      { intros ? t.
        induction t; cbn; f_equal; try assumption.
        - unfold sub_id. now rewrite env.lookup_tabulate.
        - induction IH; cbn; f_equal; auto.
        - induction IH; cbn; f_equal; auto.
      }
      { intros ? ? ? ? ? t.
        induction t; cbn; f_equal; try assumption.
        - unfold subst at 1, SubstEnv. now rewrite env.lookup_map.
        - induction IH; cbn; f_equal; auto.
        - induction IH; cbn; f_equal; auto.
      }
    Qed.

    #[export,universes(polymorphic=yes)] Instance SubstLawsList {A} `{SubstLaws A} : SubstLaws (List A).
    Proof.
      constructor.
      { intros ? t.
        induction t; cbn; f_equal; auto using subst_sub_id.
      }
      { intros ? ? ? ? ? t.
        induction t; cbn; f_equal; auto using subst_sub_comp.
      }
    Qed.

    #[export] Instance SubstLawsConst {A} : SubstLaws (Const A).
    Proof. constructor; reflexivity. Qed.

    #[export] Instance SubstLawsEnv {B : Set} {A : Ctx _ -> B -> Set}
      `{forall b, Subst (fun Σ => A Σ b), forall b, SubstLaws (fun Σ => A Σ b)}
      {Δ : Ctx B} :
      SubstLaws (fun Σ => Env (A Σ) Δ).
    Proof.
      constructor.
      { intros ? t.
        induction t; cbn.
        - reflexivity.
        - f_equal.
          + apply IHt.
          + apply subst_sub_id.
      }
      { intros ? ? ? ? ? t.
        induction t; cbn.
        - reflexivity.
        - f_equal.
          + apply IHt.
          + apply subst_sub_comp.
      }
    Qed.

    #[export] Instance subst_ctx `{Subst A} : Subst (fun Σ => Ctx (A Σ)) :=
      fix subst_ctx {Σ} xs {Σ'} ζ {struct xs} :=
        match xs with
        | ctx.nil       => ctx.nil
        | ctx.snoc xs x => ctx.snoc (subst_ctx xs ζ) (subst x ζ)
        end.

    #[export] Instance substlaws_ctx `{SubstLaws A} : SubstLaws (fun Σ => Ctx (A Σ)).
    Proof.
      constructor.
      - intros ? xs. induction xs; cbn; f_equal; auto; apply subst_sub_id.
      - intros ? ? ? ? ? xs; induction xs; cbn; f_equal; auto; apply subst_sub_comp.
    Qed.

  End SymbolicSubstitutions.

  Module SubNotations.

    Notation "a ⟨ ζ ⟩" := (subst a ζ).
    Notation "ζ1 ∘ ζ2" := (@subst (Sub _) _ _ ζ1 _ ζ2).

  End SubNotations.

  Section InfrastructureLemmas.

    Lemma lookup_sub_id {Σ x σ} (xIn : x∷σ ∈ Σ) :
      env.lookup (sub_id _) xIn = term_var x.
    Proof. unfold sub_id; now rewrite env.lookup_tabulate. Qed.

    Lemma lookup_sub_comp {Σ0 Σ1 Σ2 x} (xIn : x ∈ Σ0) (ζ1 : Sub Σ0 Σ1) (ζ2 : Sub Σ1 Σ2) :
      env.lookup (subst ζ1 ζ2) xIn = subst (env.lookup ζ1 xIn) ζ2.
    Proof.
      unfold subst at 1, SubstEnv.
      now rewrite env.lookup_map.
    Qed.

    Lemma lookup_sub_wk1 {Σ x σ b} (xIn : x∷σ ∈ Σ) :
      env.lookup (@sub_wk1 Σ b) xIn = @term_var _ _ _ (ctx.in_succ xIn).
    Proof. unfold sub_wk1; now rewrite env.lookup_tabulate. Qed.

    Lemma lookup_sub_shift {Σ x σ b} (bIn : b ∈ Σ) (xIn : x∷σ ∈ (Σ - b)) :
      env.lookup (@sub_shift Σ b bIn) xIn = @term_var Σ x σ (ctx.shift_var bIn xIn).
    Proof. unfold sub_shift; now rewrite env.lookup_tabulate. Qed.

    Lemma lookup_sub_single_eq {Σ x σ} (xIn : x∷σ ∈ Σ) (t : Term (Σ - x∷σ) σ) :
      env.lookup (sub_single xIn t) xIn = t.
    Proof. unfold sub_single. now rewrite env.lookup_tabulate, ctx.occurs_check_view_refl. Qed.

    Lemma lookup_sub_single_neq {Σ x σ y τ} (xIn : x ∷ σ ∈ Σ) (t : Term (Σ - x∷σ) σ) (yIn : y∷τ ∈ Σ - x∷σ) :
      env.lookup (sub_single xIn t) (ctx.shift_var xIn yIn) = term_var y.
    Proof. unfold sub_single. now rewrite env.lookup_tabulate, ctx.occurs_check_view_shift. Qed.

    Lemma sub_comp_id_left {Σ0 Σ1} (ζ : Sub Σ0 Σ1) :
      subst (sub_id Σ0) ζ = ζ.
    Proof.
      apply env.lookup_extensional; intros [x σ] *.
      now rewrite lookup_sub_comp, lookup_sub_id.
    Qed.

    Lemma sub_comp_id_right {Σ0 Σ1} (ζ : Sub Σ0 Σ1) :
      subst ζ (sub_id Σ1) = ζ.
    Proof.
      apply subst_sub_id.
    Qed.

    Lemma sub_comp_assoc {Σ0 Σ1 Σ2 Σ3} (ζ1 : Sub Σ0 Σ1) (ζ2 : Sub Σ1 Σ2) (ζ3 : Sub Σ2 Σ3) :
      subst (subst ζ1 ζ2) ζ3 = subst ζ1 (subst ζ2 ζ3).
    Proof. now rewrite subst_sub_comp. Qed.

    Lemma sub_comp_wk1_tail {Σ0 Σ1 b} (ζ : Sub (Σ0 ▻ b) Σ1) :
      subst sub_wk1 ζ = env.tail ζ.
    Proof.
      apply env.lookup_extensional. intros [x σ] *.
      rewrite lookup_sub_comp, lookup_sub_wk1.
      now destruct (env.view ζ) as [ζ t].
    Qed.

    Lemma sub_comp_shift {Σ0 Σ1 b} (bIn : b ∈ Σ0) (ζ : Sub Σ0 Σ1) :
      subst (sub_shift bIn) ζ = env.remove b ζ bIn.
    Proof.
      rewrite env.remove_remove'. unfold env.remove'.
      apply env.lookup_extensional. intros [x σ] xIn.
      now rewrite lookup_sub_comp, lookup_sub_shift, env.lookup_tabulate.
    Qed.

    Lemma sub_comp_wk1_comm {Σ0 Σ1 b} (ζ : Sub Σ0 Σ1) :
      subst sub_wk1 (sub_up1 ζ) = subst ζ (sub_wk1 (b:=b)).
    Proof. now rewrite sub_comp_wk1_tail. Qed.

    Lemma sub_snoc_comp {Σ1 Σ2 Σ3 x τ v} (ζ1 : Sub Σ1 Σ2) (ζ2 : Sub Σ2 Σ3) :
      subst ζ1 ζ2 ► (x∷τ ↦ v) =
      subst (sub_up1 ζ1) (ζ2 ► (x∷τ ↦ v)).
    Proof.
      unfold sub_up1, subst, SubstEnv; cbn.
      rewrite env.map_map. f_equal.
      apply env.map_ext. intros.
      now rewrite <- subst_sub_comp, sub_comp_wk1_tail.
    Qed.

    Lemma sub_up1_comp {Σ0 Σ1 Σ2} (ζ1 : Sub Σ0 Σ1) (ζ2 : Sub Σ1 Σ2) b :
      sub_up1 (b:=b) (subst ζ1 ζ2) = subst (sub_up1 ζ1) (sub_up1 ζ2).
    Proof.
      destruct b as [x σ]. DepElim.hnf_eq. f_equal.
      change (subst (subst ζ1 ζ2) (sub_wk1 (b:=x∷σ)) = subst (subst ζ1 sub_wk1) (sub_up1 ζ2)).
      now rewrite ?sub_comp_assoc, ?sub_comp_wk1_comm.
    Qed.

    Lemma sub_comp_shift_single {Σ x σ} (xIn : x∷σ ∈ Σ) (t : Term (Σ - x∷σ) σ) :
      subst (sub_shift xIn) (sub_single xIn t) = sub_id _.
    Proof.
      apply env.lookup_extensional. intros [y τ] yIn.
      rewrite lookup_sub_id.
      rewrite lookup_sub_comp.
      rewrite lookup_sub_shift.
      cbn.
      rewrite lookup_sub_single_neq.
      reflexivity.
    Qed.

    Lemma sub_up1_id {Σ x} : sub_up1 (sub_id Σ) = sub_id (Σ ▻ x).
    Proof.
      destruct x as [x σ].
      unfold sub_up1.
      rewrite sub_comp_id_left.
      apply env.lookup_extensional. intros y yIn.
      destruct (ctx.view yIn) as [|[y τ] yIn].
      - reflexivity.
      - rewrite lookup_sub_id. cbn.
        now rewrite lookup_sub_wk1.
    Qed.

    Lemma sub_comp_cat_right {Σ1 Σ2 Σ} (ζ1 : Sub Σ1 Σ) (ζ2 : Sub Σ2 Σ) :
      subst (sub_cat_right Σ2) (ζ1 ►► ζ2) = ζ2.
    Proof.
      apply env.lookup_extensional. intros [x σ] xIn.
      unfold sub_cat_right. unfold subst, SubstEnv.
      rewrite env.lookup_map, env.lookup_tabulate. cbn.
      now rewrite env.lookup_cat_right.
    Qed.

    Lemma sub_comp_cat_left {Σ1 Σ2 Σ} (ζ1 : Sub Σ1 Σ) (ζ2 : Sub Σ2 Σ) :
      subst (sub_cat_left Σ2) (ζ1 ►► ζ2) = ζ1.
    Proof.
      apply env.lookup_extensional. intros [x σ] xIn.
      unfold sub_cat_left. unfold subst, SubstEnv.
      rewrite env.lookup_map, env.lookup_tabulate. cbn.
      now rewrite env.lookup_cat_left.
    Qed.

    Lemma subst_shift_single {AT} `{SubstLaws AT} {Σ x σ} (xIn : x∷σ ∈ Σ) (a : AT (Σ - x∷σ)) (t : Term (Σ - x∷σ) σ) :
      subst (subst a (sub_shift xIn)) (sub_single xIn t) = a.
    Proof. now rewrite <- subst_sub_comp, sub_comp_shift_single, subst_sub_id. Qed.

    Lemma subst_wk1_snoc {AT} `{SubstLaws AT} {Σ1 Σ2 b} (a : AT _) (t : Term Σ2 (type b)) (ζ : Sub Σ1 Σ2) :
      subst (subst a sub_wk1) (sub_snoc ζ b t) = subst a ζ.
    Proof. now rewrite <- subst_sub_comp, sub_comp_wk1_tail. Qed.

  End InfrastructureLemmas.

  Section SymbolicPair.

    Definition Pair (A B : LCtx -> Type) (Σ : LCtx) : Type :=
      A Σ * B Σ.
    #[export] Instance SubstPair {A B} `{Subst A, Subst B} : Subst (Pair A B) :=
      fun _ '(a,b) _ ζ => (subst a ζ, subst b ζ).

    #[export] Instance SubstLawsPair {A B} `{SubstLaws A, SubstLaws B} : SubstLaws (Pair A B).
    Proof.
      constructor.
      { intros ? [t1 t2]; cbn.
        f_equal; apply subst_sub_id.
      }
      { intros ? ? ? ? ? [t1 t2]; cbn.
        f_equal; apply subst_sub_comp.
      }
    Qed.

  End SymbolicPair.

  Section SymbolicOption.

    Definition Option (A : LCtx -> Type) (Σ : LCtx) : Type :=
      option (A Σ).
    #[export] Instance SubstOption {A} `{Subst A} : Subst (Option A) :=
      fun _ ma _ ζ => option_map (fun a => subst a ζ) ma.

    #[export] Instance SubstLawsOption {A} `{SubstLaws A} : SubstLaws (Option A).
    Proof.
      constructor.
      { intros ? [t|]; cbn.
        - f_equal; apply subst_sub_id.
        - reflexivity.
      }
      { intros ? ? ? ? ? [t|]; cbn.
        - f_equal; apply subst_sub_comp.
        - reflexivity.
      }
    Qed.


  End SymbolicOption.

  Section SymbolicUnit.

    Definition Unit : LCtx -> Type := fun _ => unit.
    #[export] Instance SubstUnit : Subst Unit :=
      fun _ t _ _ => t.
    #[export] Instance SubstLawsUnit : SubstLaws Unit.
    Proof. constructor; reflexivity. Qed.

  End SymbolicUnit.

  Section SymbolicStore.

    Definition SStore (Γ : PCtx) (Σ : LCtx) : Type :=
      NamedEnv (Term Σ) Γ.

    #[export] Instance subst_localstore {Γ} : Subst (SStore Γ) :=
      SubstEnv.
    #[export] Instance substlaws_localstore {Γ} : SubstLaws (SStore Γ) :=
      SubstLawsEnv.

    Lemma subst_lookup {Γ Σ Σ' x σ} (xInΓ : x∷σ ∈ Γ) (ζ : Sub Σ Σ') (δ : SStore Γ Σ) :
      subst δ.[?? x] ζ = (subst δ ζ).[?? x].
    Proof.
      unfold subst at 2, subst_localstore, SubstEnv.
      now rewrite env.lookup_map.
    Qed.

  End SymbolicStore.
  Bind Scope env_scope with SStore.

  Module TermNotations.
    Open Scope term_scope.
    Notation "e1 && e2" := (term_binop bop.and e1 e2) : term_scope.
    Notation "e1 || e2" := (term_binop bop.or e1 e2) : term_scope.
    Notation "e1 + e2" := (term_binop bop.plus e1 e2) : term_scope.
    Notation "e1 * e2" := (term_binop bop.times e1 e2) : term_scope.
    Notation "e1 - e2" := (term_binop bop.minus e1 e2) : term_scope.
    Notation "e1 +ᵇ e2" := (term_binop bop.bvadd e1 e2) : term_scope.
    Notation "e1 -ᵇ e2" := (term_binop bop.bvsub e1 e2) : term_scope.
    Notation "e1 *ᵇ e2" := (term_binop bop.bvmul e1 e2) : term_scope.

    Notation "e1 >= e2" := (term_binop (bop.relop bop.le) e2 e1) : term_scope.
    Notation "e1 > e2" := (term_binop (bop.relop bop.lt) e2 e1) : term_scope.
    Notation "e1 <= e2" := (term_binop (bop.relop bop.le) e1 e2) : term_scope.
    Notation "e1 < e2" := (term_binop (bop.relop bop.lt) e1 e2) : term_scope.

    Notation "e1 >=ˢ e2" := (term_binop (bop.relop bop.bvule) e2 e1) : term_scope.
    Notation "e1 >ˢ e2" := (term_binop (bop.relop bop.bvult) e2 e1) : term_scope.
    Notation "e1 <ˢ e2" := (term_binop (bop.relop bop.bvult) e1 e2) : term_scope.
    Notation "e1 <=ˢ e2" := (term_binop (bop.relop bop.bvule) e1 e2) : term_scope.

    Notation "e1 >=ᵘ e2" := (term_binop (bop.relop bop.bvule) e2 e1) : term_scope.
    Notation "e1 >ᵘ e2" := (term_binop (bop.relop bop.bvult) e2 e1) : term_scope.
    Notation "e1 <=ᵘ e2" := (term_binop (bop.relop bop.bvule) e1 e2) : term_scope.
    Notation "e1 <ᵘ e2" := (term_binop (bop.relop bop.bvult) e1 e2) : term_scope.

    (* Note: this uses ?= rather than = to avoid overlap with the notation for an equality assertion... *)
    Notation "e1 ?= e2" := (term_binop (bop.relop bop.eq) e1 e2) : term_scope.
    Notation "e1 != e2" := (term_binop (bop.relop bop.neq) e1 e2) : term_scope.
    Notation "- e" := (term_unop uop.neg e) : term_scope.

  End TermNotations.

  Notation term_var_in ςIn := (term_var _ (ςInΣ := ςIn)) (only parsing).
  Notation term_inl t := (term_unop uop.inl t%term).
  Notation term_inr t := (term_unop uop.inr t%term).
  Notation term_neg t := (term_unop uop.neg t%term).
  Notation term_not t := (term_unop uop.not t%term).
  Notation term_sext t := (term_unop uop.sext t%term).
  Notation term_zext t := (term_unop uop.zext t%term).
  Notation term_get_slice_int t := (term_unop uop.get_slice_int t%term).
  Notation term_unsigned t := (term_unop uop.unsigned t%term).
  Notation term_signed t := (term_unop uop.signed t%term).
  Notation term_truncate m t := (term_unop (uop.truncate m) t%term).
  Notation term_vector_subrange s l t := (term_unop (uop.vector_subrange s l) t%term).
  Notation term_bvnot t := (term_unop uop.bvnot t%term).
  Notation term_negate t := (term_unop uop.negate t%term).

End TermsOn.
