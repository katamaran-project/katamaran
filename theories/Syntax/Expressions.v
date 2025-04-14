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
     Strings.String
     ZArith.BinInt.
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
Local Unset Elimination Schemes.

Module Type ExpressionsOn (Import TY : Types).

  Local Notation PCtx := (NCtx PVar Ty).
  Local Notation CStore := (@NamedEnv PVar Ty Val).
  Local Notation CStoreRel := (@NamedEnv PVar Ty RelVal).

  (* Intrinsically well-typed expressions. The context Γ of mutable variables
     contains names PVar and types Ty, but the names are not computationally
     relevant. The underlying representation is still a de Bruijn index based
     one. The names are meant for human consumption and we also provide name
     resolution infrastructure in the NameResolution module to fill in de
     Bruijn indices automatically.

     The de Bruijn indices are wrapped together with a resolution proof in the
     InCtx type class, which currently does not have any global instances. We
     do have local implicit instances like for example in the exp_var
     constructor below and use the type class mechanism to copy these
     locally. *)
  Inductive Exp (Γ : PCtx) : Ty -> Set :=
  | exp_var     (x : PVar) (σ : Ty) (xInΓ : x∷σ ∈ Γ) : Exp Γ σ
  | exp_val     (σ : Ty) : Val σ -> Exp Γ σ
  | exp_binop   {σ1 σ2 σ3} (op : BinOp σ1 σ2 σ3) (e1 : Exp Γ σ1) (e2 : Exp Γ σ2) : Exp Γ σ3
  | exp_unop    {σ1 σ2} (op : UnOp σ1 σ2) (e : Exp Γ σ1) : Exp Γ σ2
  | exp_list    {σ : Ty} (es : list (Exp Γ σ)) : Exp Γ (ty.list σ)
  | exp_bvec    {n} (es : Vector.t (Exp Γ ty.bool) n) : Exp Γ (ty.bvec n)
  (* | exp_tuple   {σs : Ctx Ty} (es : Env (Exp Γ) σs) : Exp Γ (ty.tuple σs) *)
  (* | exp_union   {U : unioni} (K : unionk U) (e : Exp Γ (unionk_ty U K)) : Exp Γ (ty.union U) *)
  (* | exp_record  (R : recordi) (es : NamedEnv (Exp Γ) (recordf_ty R)) : Exp Γ (ty.record R) *)
  .
  Arguments exp_var {_} _ {_ _}.
  Arguments exp_val {_} _ _.
  (* Arguments exp_tuple {_ σs} & es. *)
  (* Arguments exp_union {_} U K & e. *)
  (* Arguments exp_record {_} R & es. *)
  Bind Scope exp_scope with Exp.

  Section ExpElimination.

    Variable (Γ : PCtx).
    Variable (P : forall t, Exp Γ t -> Type).
    Arguments P _ _ : clear implicits.

    Let PL (σ : Ty) : list (Exp Γ σ) -> Type :=
      List.fold_right (fun e es => P _ e * es)%type unit.
    Let PV (n : nat) (es : Vector.t (Exp Γ ty.bool) n) : Type :=
      Vector.fold_right (fun e ps => P _ e * ps)%type es unit.
    Let PE : forall σs, Env (Exp Γ) σs -> Type :=
      env.Env_rect (fun _ _ => Type) unit (fun _ es IHes _ e => IHes * P _ e)%type.
    (* Let PNE : forall (σs : NCtx recordf Ty), NamedEnv (Exp Γ) σs -> Type := *)
    (*   env.Env_rect (fun _ _ => Type) unit (fun _ es IHes _ e => IHes * P _ e)%type. *)

    Hypothesis (P_var     : forall (x : PVar) (σ : Ty) (xInΓ : x∷σ ∈ Γ), P σ (exp_var x)).
    Hypothesis (P_val     : forall (σ : Ty) (l : Val σ), P σ (exp_val σ l)).
    Hypothesis (P_binop   : forall (σ1 σ2 σ3 : Ty) (op : BinOp σ1 σ2 σ3) (e1 : Exp Γ σ1), P σ1 e1 -> forall e2 : Exp Γ σ2, P σ2 e2 -> P σ3 (exp_binop op e1 e2)).
    Hypothesis (P_unop    : forall (σ1 σ2 : Ty) (op : UnOp σ1 σ2) (e : Exp Γ σ1), P σ1 e -> P σ2 (exp_unop op e)).
    Hypothesis (P_list    : forall (σ : Ty) (es : list (Exp Γ σ)), PL es -> P (ty.list σ) (exp_list es)).
    Hypothesis (P_bvec    : forall (n : nat) (es : Vector.t (Exp Γ ty.bool) n), PV es -> P (ty.bvec n) (exp_bvec es)).
    (* Hypothesis (P_tuple   : forall (σs : Ctx Ty) (es : Env (Exp Γ) σs), PE es -> P (ty.tuple σs) (exp_tuple es)). *)
    (* Hypothesis (P_union   : forall (U : unioni) (K : unionk U) (e : Exp Γ (unionk_ty U K)), P (unionk_ty U K) e -> P (ty.union U) (exp_union U K e)). *)
    (* Hypothesis (P_record  : forall (R : recordi) (es : NamedEnv (Exp Γ) (recordf_ty R)), PNE es -> P (ty.record R) (exp_record R es)). *)

    Fixpoint Exp_rect {τ : Ty} (e : Exp Γ τ) {struct e} : P τ e :=
      match e with
      | exp_var x                 => ltac:(apply P_var; auto)
      | exp_val _ l               => ltac:(apply P_val; auto)
      | exp_binop op e1 e2        => ltac:(apply P_binop; auto)
      | exp_unop op e             => ltac:(apply P_unop; auto)
      | exp_list es               => ltac:(apply P_list; induction es; cbn; auto using unit)
      | exp_bvec es               => ltac:(apply P_bvec; induction es; cbn; auto using unit)
      (* | exp_tuple es              => ltac:(apply P_tuple; induction es; cbn; auto using unit) *)
      (* | exp_union U K e           => ltac:(apply P_union; auto) *)
      (* | exp_record R es           => ltac:(apply P_record; induction es; cbn; auto using unit) *)
      end.

  End ExpElimination.

  Definition Exp_rec {Γ} (P : forall σ, Exp Γ σ -> Set) := Exp_rect P.
  Definition Exp_ind {Γ} (P : forall σ, Exp Γ σ -> Prop) := Exp_rect P.

  Fixpoint eval {Γ σ} (e : Exp Γ σ) (δ : CStore Γ) {struct e} : Val σ :=
    match e in (Exp _ t) return (Val t) with
    | exp_var x           => δ.[??x]
    | exp_val _ l         => l
    | exp_binop op e1 e2  => bop.eval op (eval e1 δ) (eval e2 δ)
    | exp_unop op e       => uop.eval op (eval e δ)
    | exp_list es         => List.map (fun e => eval e δ) es
    | exp_bvec es         => Vector.t_rect
                               _ (fun m (_ : Vector.t (Exp Γ ty.bool) m) => bv m)
                               bv.nil (fun eb m _ => bv.cons (eval eb δ))
                               _ es
    (* | exp_tuple es        => env.Env_rect *)
    (*                            (fun σs _ => Val (ty.tuple σs)) *)
    (*                            tt *)
    (*                            (fun σs _ (vs : Val (ty.tuple σs)) σ e => (vs, eval e δ)) *)
    (*                            es *)
    (* | exp_union U K e     => unionv_fold U (existT K (eval e δ)) *)
    (* | exp_record R es     => recordv_fold R (env.map (fun xτ e => eval e δ) es) *)
    end.

  Fixpoint evalRel {Γ σ} (e : Exp Γ σ) (δ : CStoreRel Γ) {struct e} : RelVal σ :=
    match e in (Exp _ t) return (RelVal t) with
    | exp_var x           => δ.[??x]
    | exp_val _ l         => ty.SyncVal _ l
    | exp_binop op e1 e2  => ty.liftBinOp (bop.eval op) (evalRel e1 δ) (evalRel e2 δ)
    | exp_unop op e       => ty.liftUnOp (uop.eval op) (evalRel e δ)
    | exp_list es         => ty.listRelValIsRelValList (List.map (fun e => evalRel e δ) es)
    | @exp_bvec _ n es         => ty.vecRelValIsRelValVec (VectorDef.map (fun e => evalRel e δ) es)
    (* | exp_tuple es        => env.Env_rect *)
    (*                            (fun σs _ => Val (ty.tuple σs)) *)
    (*                            tt *)
    (*                            (fun σs _ (vs : Val (ty.tuple σs)) σ e => (vs, evalRel e δ)) *)
    (*                            es *)
    (* | exp_union U K e     => unionv_fold U (existT K (evalRel e δ)) *)
    (* | exp_record R es     => recordv_fold R (env.map (fun xτ e => evalRel e δ) es) *)
    end.

  Definition evals {Γ Δ} (es : NamedEnv (Exp Γ) Δ) (δ : CStore Γ) : CStore Δ :=
    env.map (fun xτ e => eval e δ) es.

  Definition evalsRel {Γ Δ} (es : NamedEnv (Exp Γ) Δ) (δ : CStoreRel Γ) : CStoreRel Δ :=
    env.map (fun xτ e => evalRel e δ) es.

  Notation exp_int l := (@exp_val _ ty.int l%Z).
  Notation exp_bool l := (@exp_val _ ty.bool l).
  Notation exp_true   := (@exp_val _ ty.bool true).
  Notation exp_false  := (@exp_val _ ty.bool false).
  Notation exp_string s := (@exp_val _ ty.string s%string).
  Notation exp_inl e := (exp_unop uop.inl e%exp).
  Notation exp_inr e := (exp_unop uop.inr e%exp).
  Notation exp_neg e := (exp_unop uop.neg e%exp).
  Notation exp_not e := (exp_unop uop.not e%exp).
  Notation exp_sext e := (exp_unop uop.sext e%exp).
  Notation exp_zext e := (exp_unop uop.zext e%exp).
  Notation exp_get_slice_int e := (exp_unop uop.get_slice_int e%exp).
  Notation exp_signed e := (exp_unop uop.signed e%exp).
  Notation exp_unsigned e := (exp_unop uop.unsigned e%exp).
  Notation exp_truncate m e := (exp_unop (uop.truncate m) e%exp).
  Notation exp_vector_subrange s l e := (exp_unop (uop.vector_subrange s l) e%exp).
  Notation exp_negate e := (exp_unop uop.negate e%exp).

  Notation "e1 && e2" := (exp_binop bop.and e1 e2) : exp_scope.
  Notation "e1 || e2" := (exp_binop bop.or e1 e2) : exp_scope.
  Notation "e1 + e2" := (exp_binop bop.plus e1 e2) : exp_scope.
  Notation "e1 * e2" := (exp_binop bop.times e1 e2) : exp_scope.
  Notation "e1 - e2" := (exp_binop bop.minus e1 e2) : exp_scope.
  Notation "e1 +ᵇ e2" := (exp_binop bop.bvadd e1 e2) : exp_scope.
  Notation "e1 -ᵇ e2" := (exp_binop bop.bvsub e1 e2) : exp_scope.
  Notation "e1 *ᵇ e2" := (exp_binop bop.bvmul e1 e2) : exp_scope.

  Notation "e1 >= e2" := (exp_binop (bop.relop bop.le) e2 e1) : exp_scope.
  Notation "e1 > e2" := (exp_binop (bop.relop bop.lt) e2 e1) : exp_scope.
  Notation "e1 <= e2" := (exp_binop (bop.relop bop.le) e1 e2) : exp_scope.
  Notation "e1 < e2" := (exp_binop (bop.relop bop.lt) e1 e2) : exp_scope.

  Notation "e1 >=ˢ e2" := (exp_binop (bop.relop bop.bvule) e2 e1) : exp_scope.
  Notation "e1 >ˢ e2" := (exp_binop (bop.relop bop.bvult) e2 e1) : exp_scope.
  Notation "e1 <ˢ e2" := (exp_binop (bop.relop bop.bvult) e1 e2) : exp_scope.
  Notation "e1 <=ˢ e2" := (exp_binop (bop.relop bop.bvule) e1 e2) : exp_scope.

  Notation "e1 >=ᵘ e2" := (exp_binop (bop.relop bop.bvule) e2 e1) : exp_scope.
  Notation "e1 >ᵘ e2" := (exp_binop (bop.relop bop.bvult) e2 e1) : exp_scope.
  Notation "e1 <=ᵘ e2" := (exp_binop (bop.relop bop.bvule) e1 e2) : exp_scope.
  Notation "e1 <ᵘ e2" := (exp_binop (bop.relop bop.bvult) e1 e2) : exp_scope.

  Notation "e1 = e2" := (exp_binop (bop.relop bop.eq) e1 e2) : exp_scope.
  Notation "e1 != e2" := (exp_binop (bop.relop bop.neq) e1 e2) : exp_scope.
  Notation "- e" := (exp_unop uop.neg e) : exp_scope.

End ExpressionsOn.
