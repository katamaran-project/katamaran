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
     Strings.String
     ZArith.BinInt.
From Katamaran Require Import
     Context
     Environment
     Notation
     Prelude
     Syntax.BinOps
     Syntax.TypeDecl
     Syntax.TypeDef
     Syntax.Variables
     Tactics.

Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.
Local Unset Elimination Schemes.

Module Type ExpressionsOn (Import TY : Types) (Import BOP : BinOpsOn TY).

  Local Notation PCtx := (NCtx 𝑿 Ty).
  Local Notation CStore := (@NamedEnv 𝑿 Ty Val).

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
  Inductive Exp (Γ : PCtx) : Ty -> Set :=
  | exp_var     (x : 𝑿) (σ : Ty) (xInΓ : x∷σ ∈ Γ) : Exp Γ σ
  | exp_val     (σ : Ty) : Val σ -> Exp Γ σ
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
                {p : ctx.nth_is σs n σ} : Exp Γ σ
  | exp_union   {U : 𝑼} (K : 𝑼𝑲 U) (e : Exp Γ (𝑼𝑲_Ty K)) : Exp Γ (ty_union U)
  | exp_record  (R : 𝑹) (es : NamedEnv (Exp Γ) (𝑹𝑭_Ty R)) : Exp Γ (ty_record R).
  (* | exp_projrec {R : 𝑹} (e : Exp Γ (ty_record R)) (rf : 𝑹𝑭) {σ : Ty} *)
  (*               {rfInR : rf∶σ ∈ 𝑹𝑭_Ty R} : Exp Γ σ. *)
  Arguments exp_var {_} _ {_ _}.
  Arguments exp_val {_} _ _.
  Arguments exp_tuple {_ _} _.
  Arguments exp_union {_} _ _.
  Arguments exp_record {_} _ _.
  (* Arguments exp_projrec {_ _} _ _ {_ _}. *)
  Bind Scope exp_scope with Exp.

  Section ExpElimination.

    Variable (Γ : PCtx).
    Variable (P : forall t, Exp Γ t -> Type).
    Arguments P _ _ : clear implicits.

    Let PL (σ : Ty) : list (Exp Γ σ) -> Type :=
      List.fold_right (fun e es => P _ e * es)%type unit.
    Let PV (n : nat) (es : Vector.t (Exp Γ ty_bit) n) : Type :=
      Vector.fold_right (fun e ps => P _ e * ps)%type es unit.
    Let PE : forall σs, Env (Exp Γ) σs -> Type :=
      env.Env_rect (fun _ _ => Type) unit (fun _ es IHes _ e => IHes * P _ e)%type.
    Let PNE : forall (σs : NCtx 𝑹𝑭 Ty), NamedEnv (Exp Γ) σs -> Type :=
      env.Env_rect (fun _ _ => Type) unit (fun _ es IHes _ e => IHes * P _ e)%type.

    Hypothesis (P_var     : forall (x : 𝑿) (σ : Ty) (xInΓ : x∷σ ∈ Γ), P σ (exp_var x)).
    Hypothesis (P_val     : forall (σ : Ty) (l : Val σ), P σ (exp_val σ l)).
    Hypothesis (P_binop   : forall (σ1 σ2 σ3 : Ty) (op : BinOp σ1 σ2 σ3) (e1 : Exp Γ σ1), P σ1 e1 -> forall e2 : Exp Γ σ2, P σ2 e2 -> P σ3 (exp_binop op e1 e2)).
    Hypothesis (P_neg     : forall e : Exp Γ ty_int, P ty_int e -> P ty_int (exp_neg e)).
    Hypothesis (P_not     : forall e : Exp Γ ty_bool, P ty_bool e -> P ty_bool (exp_not e)).
    Hypothesis (P_inl     : forall (σ1 σ2 : Ty) (e : Exp Γ σ1), P σ1 e -> P (ty_sum σ1 σ2) (exp_inl e)).
    Hypothesis (P_inr     : forall (σ1 σ2 : Ty) (e : Exp Γ σ2), P σ2 e -> P (ty_sum σ1 σ2) (exp_inr e)).
    Hypothesis (P_list    : forall (σ : Ty) (es : list (Exp Γ σ)), PL es -> P (ty_list σ) (exp_list es)).
    Hypothesis (P_bvec    : forall (n : nat) (es : Vector.t (Exp Γ ty_bit) n), PV es -> P (ty_bvec n) (exp_bvec es)).
    Hypothesis (P_tuple   : forall (σs : Ctx Ty) (es : Env (Exp Γ) σs), PE es -> P (ty_tuple σs) (exp_tuple es)).
    Hypothesis (P_projtup : forall (σs : Ctx Ty) (e : Exp Γ (ty_tuple σs)), P (ty_tuple σs) e -> forall (n : nat) (σ : Ty) (p : ctx.nth_is σs n σ), P σ (@exp_projtup _ _ e n _ p)).
    Hypothesis (P_union   : forall (U : 𝑼) (K : 𝑼𝑲 U) (e : Exp Γ (𝑼𝑲_Ty K)), P (𝑼𝑲_Ty K) e -> P (ty_union U) (exp_union U K e)).
    Hypothesis (P_record  : forall (R : 𝑹) (es : NamedEnv (Exp Γ) (𝑹𝑭_Ty R)), PNE es -> P (ty_record R) (exp_record R es)).
    (* Hypothesis (P_projrec : forall (R : 𝑹) (e : Exp Γ (ty_record R)), P (ty_record R) e -> forall (rf : 𝑹𝑭) (σ : Ty) (rfInR : (rf ∶ σ)%ctx ∈ 𝑹𝑭_Ty R), P σ (exp_projrec e rf)). *)

    Fixpoint Exp_rect {τ : Ty} (e : Exp Γ τ) {struct e} : P τ e :=
      match e with
      | exp_var x                 => ltac:(apply P_var; auto)
      | exp_val _ l               => ltac:(apply P_val; auto)
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
      (* | exp_projrec e rf          => ltac:(apply P_projrec; auto) *)
      end.

  End ExpElimination.

  Definition Exp_rec {Γ} (P : forall σ, Exp Γ σ -> Set) := Exp_rect P.
  Definition Exp_ind {Γ} (P : forall σ, Exp Γ σ -> Prop) := Exp_rect P.

  Fixpoint eval {Γ σ} (e : Exp Γ σ) (δ : CStore Γ) {struct e} : Val σ :=
    match e in (Exp _ t) return (Val t) with
    | exp_var x           => δ ‼ x
    | exp_val _ l         => l
    | exp_binop op e1 e2  => eval_binop op (eval e1 δ) (eval e2 δ)
    | exp_neg e           => Z.opp (eval e δ)
    | exp_not e           => negb (eval e δ)
    | exp_inl e           => inl (eval e δ)
    | exp_inr e           => inr (eval e δ)
    | exp_list es         => List.map (fun e => eval e δ) es
    | exp_bvec es         => Vector.t_rect
                               _ (fun m (_ : Vector.t (Exp Γ ty_bit) m) => bv m)
                               bv.nil (fun eb m _ (vs : bv m) =>
                                          match eval eb δ with
                                          | bitzero => bv.cons false vs
                                          | bitone => bv.cons true vs
                                          end)
                               _ es
    | exp_tuple es        => env.Env_rect
                               (fun σs _ => Val (ty_tuple σs))
                               tt
                               (fun σs _ (vs : Val (ty_tuple σs)) σ e => (vs, eval e δ))
                               es
    | @exp_projtup _ σs e n σ p => tuple_proj σs n σ (eval e δ) p
    | exp_union U K e     => 𝑼_fold (existT K (eval e δ))
    | exp_record R es     => 𝑹_fold (env.map (fun xτ e => eval e δ) es)
    (* | exp_projrec e rf    => 𝑹_unfold (eval e δ) ‼ rf *)
    end.

  Definition evals {Γ Δ} (es : NamedEnv (Exp Γ) Δ) (δ : CStore Γ) : CStore Δ :=
    env.map (fun xτ e => eval e δ) es.

  Notation exp_int l := (@exp_val _ ty_int l%Z).
  Notation exp_bool l := (@exp_val _ ty_bool l).
  Notation exp_true   := (@exp_val _ ty_bool true).
  Notation exp_false  := (@exp_val _ ty_bool false).
  Notation exp_string s := (@exp_val _ ty_string s%string).
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
  (* Notation "e ․ f" := (* Using Unicode Character “․” (U+2024) *) *)
  (*     (@exp_projrec _ _ e f%string _ _) *)
  (*       (at level 9, no associativity, format *)
  (*        "e ․ f") : exp_scope. *)

End ExpressionsOn.
