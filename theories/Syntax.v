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
     Bool.Bool
     Classes.Equivalence
     Program.Tactics
     Relations
     Strings.String
     ZArith.ZArith
     micromega.Lia.
From Coq Require
     Vector.

From bbv Require
     Word.

From stdpp Require
     finite.
From Equations Require Import
     Equations Signature.
Require Equations.Prop.DepElim.
Require Import Equations.Prop.EqDec.

From Katamaran Require Export
     Context
     Notation
     Syntax.Types
     Syntax.Values.

Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.
Local Unset Transparent Obligations.
Obligation Tactic := idtac.

Module Type TermKit.

  Declare Module valuekit : ValueKit.
  Module Export VAL := Values valuekit.

  (* Names of functions. *)
  Parameter Inline 𝑭 : PCtx -> Ty -> Set.
  Parameter Inline 𝑭𝑿 : PCtx -> Ty -> Set.
  (* Names of lemmas. *)
  Parameter Inline 𝑳 : PCtx -> Set.

  (* Names of registers. *)
  Parameter Inline 𝑹𝑬𝑮 : Ty -> Set.
  Declare Instance 𝑹𝑬𝑮_eq_dec : EqDec (sigT 𝑹𝑬𝑮).
  Declare Instance 𝑹𝑬𝑮_finite : finite.Finite (sigT 𝑹𝑬𝑮).

End TermKit.

Module Terms (Export termkit : TermKit).

  Definition CStore (Γ : PCtx) : Set := NamedEnv Val Γ.
  Bind Scope env_scope with CStore.

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
    Inductive Exp (Γ : PCtx) : Ty -> Set :=
    | exp_var     (x : 𝑿) (σ : Ty) {xInΓ : x∷σ ∈ Γ} : Exp Γ σ
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
    Bind Scope exp_scope with Exp.

    Global Arguments exp_var {_} _ {_ _}.
    Global Arguments exp_val {_} _ _.
    Global Arguments exp_tuple {_ _} _.
    Global Arguments exp_union {_} _ _.
    Global Arguments exp_record {_} _ _.
    (* Global Arguments exp_projrec {_ _} _ _ {_ _}. *)

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

    Fixpoint eval {Γ : PCtx} {σ : Ty} (e : Exp Γ σ) (δ : CStore Γ) {struct e} : Val σ :=
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
                                 _ (fun m (_ : Vector.t (Exp Γ ty_bit) m) => Word.word m)
                                 Word.WO (fun eb m _ (vs : Word.word m) =>
                                            match eval eb δ with
                                            | bitzero => Word.WS false vs
                                            | bitone => Word.WS true vs
                                            end)
                                 _ es
      | exp_tuple es        => env.Env_rect
                                 (fun σs _ => Val (ty_tuple σs))
                                 tt
                                 (fun σs _ (vs : Val (ty_tuple σs)) σ e => (vs, eval e δ))
                                 es
      | @exp_projtup _ σs e n σ p => tuple_proj σs n σ (eval e δ) p
      | exp_union U K e     => 𝑼_fold (existT K (eval e δ))
      | exp_record R es     => 𝑹_fold (env.Env_rect
                                         (fun σs _ => NamedEnv Val σs)
                                         env.nil
                                         (fun σs _ vs _ e => env.snoc vs _ (eval e δ)) es)
      (* | exp_projrec e rf    => 𝑹_unfold (eval e δ) ‼ rf *)
      end.

    Definition evals {Γ Δ} (es : NamedEnv (Exp Γ) Δ) (δ : CStore Γ) : CStore Δ :=
      env.map (fun xτ e => eval e δ) es.

  End Expressions.
  Bind Scope exp_scope with Exp.

  Section Statements.

    Inductive TuplePat {N : Set} : Ctx Ty -> (NCtx N Ty) -> Set :=
    | tuplepat_nil  : TuplePat ε ε
    | tuplepat_snoc
        {σs : Ctx Ty} {Δ : NCtx N Ty}
        (pat : TuplePat σs Δ) {σ : Ty} (x : N) :
        TuplePat (σs ▻ σ) (Δ ▻ x∷σ).
    Bind Scope pat_scope with TuplePat.

    Inductive RecordPat {N : Set} : NCtx 𝑹𝑭 Ty -> NCtx N Ty -> Set :=
    | recordpat_nil  : RecordPat ε ε
    | recordpat_snoc
        {rfs : NCtx 𝑹𝑭 Ty} {Δ : NCtx N Ty}
        (pat : RecordPat rfs Δ) (rf : 𝑹𝑭) {τ : Ty} (x : N) :
        RecordPat (rfs ▻ rf∷τ) (Δ ▻ x∷τ).
    Bind Scope pat_scope with RecordPat.

    Inductive Pattern {N : Set} : NCtx N Ty -> Ty -> Set :=
    | pat_var (x : N) {σ : Ty} : Pattern [ x∷σ ] σ
    | pat_unit : Pattern ε ty_unit
    | pat_pair (x y : N) {σ τ : Ty} : Pattern [ x∷σ , y∷τ ] (ty_prod σ τ)
    | pat_tuple {σs Δ} (p : TuplePat σs Δ) : Pattern Δ (ty_tuple σs)
    | pat_record {R Δ} (p : RecordPat (𝑹𝑭_Ty R) Δ) : Pattern Δ (ty_record R).

    (* Local Unset Elimination Schemes. *)

    (* Inductive Effect (Γ : PCtx) : Type := *)
    (* | eff_assign (x : 𝑿) {τ} {xInΓ : x::τ ∈ Γ} (e : Stm Γ τ) *)
    (* | eff_write_register (reg : 𝑹𝑬𝑮 τ) (e : Exp Γ τ) *)
    (* | eff_lemma  {Δ : PCtx} (l : 𝑳 Δ) (es : NamedEnv (Exp Γ) Δ) *)
    (* | eff_assert (e1 : Exp Γ ty_bool) (e2 : Exp Γ ty_string) *)
    (* | eff_debug *)
    (* | eff_while (e : Exp Γ ty_bool) {σ : Ty} (s : Stm Γ σ). *)

    Inductive Stm (Γ : PCtx) (τ : Ty) : Type :=
    (* We avoid defining effects and statements mutually recursively. Instead, *)
    (* we inline seqe and put up with the boilerplate. *)
    (* | stm_seqe          (eff : Effect Γ) (k : Stm Γ τ) *)
    | stm_val           (v : Val τ)
    | stm_exp           (e : Exp Γ τ)
    | stm_let           (x : 𝑿) (σ : Ty) (s__σ : Stm Γ σ) (s__τ : Stm (Γ ▻ x∷σ) τ)
    | stm_block         (Δ : PCtx) (δ : CStore Δ) (s : Stm (Γ ▻▻ Δ) τ)
    | stm_assign        (x : 𝑿) {xInΓ : x∷τ ∈ Γ} (s : Stm Γ τ)
    | stm_call          {Δ : PCtx} (f : 𝑭 Δ τ) (es : NamedEnv (Exp Γ) Δ)
    | stm_call_frame    (Δ : PCtx) (δ : CStore Δ) (s : Stm Δ τ)
    | stm_foreign       {Δ : PCtx} (f : 𝑭𝑿 Δ τ) (es : NamedEnv (Exp Γ) Δ)
    | stm_lemmak        {Δ : PCtx} (l : 𝑳 Δ) (es : NamedEnv (Exp Γ) Δ) (k : Stm Γ τ)
    | stm_if            (e : Exp Γ ty_bool) (s1 s2 : Stm Γ τ)
    | stm_seq           {σ : Ty} (s : Stm Γ σ) (k : Stm Γ τ)
    | stm_assertk       (e1 : Exp Γ ty_bool) (e2 : Exp Γ ty_string) (k : Stm Γ τ)
    | stm_fail          (s : Val ty_string)
    | stm_match_list
        {σ : Ty} (e : Exp Γ (ty_list σ)) (alt_nil : Stm Γ τ) (xh xt : 𝑿)
        (alt_cons : Stm (Γ ▻ xh∷σ ▻ xt∷ty_list σ) τ)
    | stm_match_sum
        {σinl σinr : Ty} (e : Exp Γ (ty_sum σinl σinr))
        (xinl : 𝑿) (alt_inl : Stm (Γ ▻ xinl∷σinl) τ)
        (xinr : 𝑿) (alt_inr : Stm (Γ ▻ xinr∷σinr) τ)
    | stm_match_prod
        {σ1 σ2 : Ty} (e : Exp Γ (ty_prod σ1 σ2))
        (xl xr : 𝑿) (rhs : Stm (Γ ▻ xl∷σ1 ▻ xr∷σ2) τ)
    | stm_match_enum
        {E : 𝑬} (e : Exp Γ (ty_enum E))
        (alts : forall (K : 𝑬𝑲 E), Stm Γ τ)
    | stm_match_tuple
        {σs : Ctx Ty} {Δ : PCtx} (e : Exp Γ (ty_tuple σs))
        (p : TuplePat σs Δ) (rhs : Stm (Γ ▻▻ Δ) τ)
    | stm_match_union
        {U : 𝑼} (e : Exp Γ (ty_union U))
        (alt__ctx : forall (K : 𝑼𝑲 U), PCtx)
        (alt__pat : forall (K : 𝑼𝑲 U), Pattern (alt__ctx K) (𝑼𝑲_Ty K))
        (alt__rhs : forall (K : 𝑼𝑲 U), Stm (Γ ▻▻ alt__ctx K) τ)
    | stm_match_record
        {R : 𝑹} {Δ : PCtx} (e : Exp Γ (ty_record R))
        (p : RecordPat (𝑹𝑭_Ty R) Δ) (rhs : Stm (Γ ▻▻ Δ) τ)
    | stm_read_register (reg : 𝑹𝑬𝑮 τ)
    | stm_write_register (reg : 𝑹𝑬𝑮 τ) (e : Exp Γ τ)
    (* EXPERIMENTAL *)
    (* | stm_while  (e : Exp Γ ty_bool) {σ : Ty} (s : Stm Γ σ) : Stm Γ ty_unit *)
    | stm_bind   {σ : Ty} (s : Stm Γ σ) (k : Val σ -> Stm Γ τ)
    | stm_debugk (k : Stm Γ τ).

    Section TransparentObligations.

      Local Set Transparent Obligations.
      Derive Signature for Stm.
      Derive NoConfusionHom for Stm.

    End TransparentObligations.

    (* Section StmElimination. *)

    (*   Variable (P : forall (Γ : PCtx) (t : Ty), Stm Γ t -> Type). *)

    (*   Hypothesis (P_val   : forall (Γ : PCtx) (τ : Ty) (v : Val τ), P (stm_val Γ v)). *)
    (*   Hypothesis (P_exp  : forall (Γ : PCtx) (τ : Ty) (e : Exp Γ τ), P (stm_exp e)). *)
    (*   Hypothesis (P_let  : forall (Γ : PCtx) (x : 𝑿) (τ : Ty) (s : Stm Γ τ) (σ : Ty) (k : Stm (Γ ▻ (x ∶ τ)%ctx) σ), P s -> P k -> P (stm_let s k)). *)
    (*   Hypothesis (P_block : forall (Γ Δ : PCtx) (δ : CStore Δ) (σ : Ty) (k : Stm (Γ ▻▻ Δ) σ), P k -> P (stm_block Γ δ k)). *)
    (*   Hypothesis (P_assign : forall (Γ : PCtx) (x : 𝑿) (τ : Ty) (xInΓ : (x ∶ τ)%ctx ∈ Γ) (e : Stm Γ τ), P e -> P (stm_assign e)). *)
    (*   Hypothesis (P_call  : forall (Γ Δ : PCtx) (σ : Ty) (f : 𝑭 Δ σ) (es : NamedEnv (Exp Γ) Δ), P (stm_call f es)). *)
    (*   Hypothesis (P_call_frame  : forall (Γ Δ : PCtx) (δ : CStore Δ) (τ : Ty) (s : Stm Δ τ), P s -> P (stm_call_frame Γ δ s)). *)
    (*   Hypothesis (P_foreign  : forall (Γ Δ : PCtx) (σ : Ty) (f : 𝑭𝑿 Δ σ) (es : NamedEnv (Exp Γ) Δ), P (stm_foreign f es)). *)
    (*   Hypothesis (P_if  : forall (Γ : PCtx) (τ : Ty) (e : Exp Γ ty_bool) (s1 : Stm Γ τ) (s2 : Stm Γ τ), P s1 -> P s2 -> P (stm_if e s1 s2)). *)
    (*   Hypothesis (P_seq  : forall (Γ : PCtx) (τ : Ty) (e : Stm Γ τ) (σ : Ty) (k : Stm Γ σ), P e -> P k -> P (stm_seq e k)). *)
    (*   Hypothesis (P_assert  : forall (Γ : PCtx) (e1 : Exp Γ ty_bool) (e2 : Exp Γ ty_string), P (stm_assert e1 e2)). *)
    (*   Hypothesis (P_fail  : forall (Γ : PCtx) (τ : Ty) (s : Val ty_string), P (stm_fail Γ τ s)). *)
    (*   Hypothesis (P_match_list : forall (Γ : PCtx) (σ τ : Ty) (e : Exp Γ (ty_list σ)) (alt_nil : Stm Γ τ) (xh xt : 𝑿) (alt_cons : Stm (Γ ▻ (xh ∶ σ)%ctx ▻ (xt ∶ ty_list σ)%ctx) τ), *)
    (*         P alt_nil -> P alt_cons -> P (stm_match_list e alt_nil alt_cons)). *)
    (*   Hypothesis (P_match_sum : forall (Γ : PCtx) (σinl σinr τ : Ty) (e : Exp Γ (ty_sum σinl σinr)) (xinl : 𝑿) (alt_inl : Stm (Γ ▻ (xinl ∶ σinl)%ctx) τ) (xinr : 𝑿) (alt_inr : Stm (Γ ▻ (xinr ∶ σinr)%ctx) τ), *)
    (*         P alt_inl -> P alt_inr -> P (stm_match_sum e alt_inl alt_inr)). *)
    (*   Hypothesis (P_match_prod : forall (Γ : PCtx) (σ1 σ2 τ : Ty) (e : Exp Γ (ty_prod σ1 σ2)) (xl xr : 𝑿) (rhs : Stm (Γ ▻ (xl ∶ σ1)%ctx ▻ (xr ∶ σ2)%ctx) τ), *)
    (*         P rhs -> P (stm_match_prod e rhs)). *)
    (*   Hypothesis (P_match_enum : forall (Γ : PCtx) (E : 𝑬) (e : Exp Γ (ty_enum E)) (τ : Ty) (alts : 𝑬𝑲 E -> Stm Γ τ), *)
    (*         (forall K : 𝑬𝑲 E, P (alts K)) -> P (stm_match_enum e alts)). *)
    (*   Hypothesis (P_match_tuple : forall (Γ : PCtx) (σs : Ctx Ty) (Δ : PCtx) (e : Exp Γ (ty_tuple σs)) (p : TuplePat σs Δ) (τ : Ty) (rhs : Stm (Γ ▻▻ Δ) τ), *)
    (*         P rhs -> P (stm_match_tuple e p rhs)). *)
    (*   Hypothesis (P_match_union : forall (Γ : PCtx) (U : 𝑼) (e : Exp Γ (ty_union U)) (τ : Ty) (alt__ctx : 𝑼𝑲 U -> PCtx) *)
    (*         (alt__pat : forall K : 𝑼𝑲 U, Pattern (alt__ctx K) (𝑼𝑲_Ty K)) (alt__rhs : forall K : 𝑼𝑲 U, Stm (Γ ▻▻ alt__ctx K) τ), *)
    (*         (forall K : 𝑼𝑲 U, P (alt__rhs K)) -> P (stm_match_union e alt__ctx alt__pat alt__rhs)). *)
    (*   Hypothesis (P_match_record : forall (Γ : PCtx) (R : 𝑹) (Δ : PCtx) (e : Exp Γ (ty_record R)) (p : RecordPat (𝑹𝑭_Ty R) Δ) (τ : Ty) (rhs : Stm (Γ ▻▻ Δ) τ), *)
    (*         P rhs -> P (stm_match_record e p rhs)). *)
    (*   Hypothesis (P_read_register : forall (Γ : PCtx) (τ : Ty) (reg : 𝑹𝑬𝑮 τ), *)
    (*         P (stm_read_register Γ reg)). *)
    (*   Hypothesis (P_write_register : forall (Γ : PCtx) (τ : Ty) (reg : 𝑹𝑬𝑮 τ) (e : Exp Γ τ), *)
    (*         P (stm_write_register reg e)). *)
    (*   Hypothesis (P_bind : forall (Γ : PCtx) (σ τ : Ty) (s : Stm Γ σ) (k : Val σ -> Stm Γ τ), *)
    (*         P s -> (forall l : Val σ, P (k l)) -> P (stm_bind s k)). *)

    (*   Fixpoint Stm_rect {Γ : PCtx} {τ : Ty} (s : Stm Γ τ) {struct s} : P s := *)
    (*     match s with *)
    (*     | stm_val _ _             => ltac:(apply P_val; auto) *)
    (*     | stm_exp _               => ltac:(apply P_exp; auto) *)
    (*     | stm_let _ _             => ltac:(apply P_let; auto) *)
    (*     | stm_block _ _ _         => ltac:(apply P_block; auto) *)
    (*     | stm_assign _            => ltac:(apply P_assign; auto) *)
    (*     | stm_call _ _            => ltac:(apply P_call; auto) *)
    (*     | stm_call_frame _ _ _    => ltac:(apply P_call_frame; auto) *)
    (*     | stm_foreign _ _         => ltac:(apply P_foreign; auto) *)
    (*     | stm_if _ _ _            => ltac:(apply P_if; auto) *)
    (*     | stm_seq _ _             => ltac:(apply P_seq; auto) *)
    (*     | stm_assert _ _          => ltac:(apply P_assert; auto) *)
    (*     | stm_fail _ _ _          => ltac:(apply P_fail; auto) *)
    (*     | stm_match_list _ _ _    => ltac:(apply P_match_list; auto) *)
    (*     | stm_match_sum _ _ _     => ltac:(apply P_match_sum; auto) *)
    (*     | stm_match_prod _ _      => ltac:(apply P_match_prod; auto) *)
    (*     | stm_match_enum _ _      => ltac:(apply P_match_enum; auto) *)
    (*     | stm_match_tuple _ _ _   => ltac:(apply P_match_tuple; auto) *)
    (*     | stm_match_union _ _ _ _ => ltac:(apply P_match_union; auto) *)
    (*     | stm_match_record _ _ _  => ltac:(apply P_match_record; auto) *)
    (*     | stm_read_register _ _   => ltac:(apply P_read_register; auto) *)
    (*     | stm_write_register _ _  => ltac:(apply P_write_register; auto) *)
    (*     | stm_bind _ _            => ltac:(apply P_bind; auto) *)
    (*     end. *)

    (* End StmElimination. *)

    (* Definition Stm_rec (P : forall Γ σ, Stm Γ σ -> Set) := Stm_rect P. *)
    (* Definition Stm_ind (P : forall Γ σ, Stm Γ σ -> Prop) := Stm_rect P. *)

    Global Arguments stm_val {Γ} τ v.
    Global Arguments stm_exp {Γ τ} e%exp.
    Global Arguments stm_let {Γ τ} x σ s__σ%exp s__τ%exp.
    Global Arguments stm_block {Γ τ Δ} δ s%exp.
    Global Arguments stm_assign {Γ τ} x {xInΓ} s%exp.
    Global Arguments stm_call {Γ τ Δ} f _%arg.
    Global Arguments stm_call_frame {Γ τ Δ} δ s%exp.
    Global Arguments stm_foreign {Γ τ Δ} f _%arg.
    Global Arguments stm_lemmak {Γ τ Δ} l _%arg k.
    Global Arguments stm_if {Γ τ} e%exp s1%exp s2%exp.
    Global Arguments stm_seq {Γ τ σ} s%exp k%exp.
    Global Arguments stm_assertk {Γ τ} e1%exp e2%exp k%exp.
    Global Arguments stm_fail {Γ} τ s%string.
    Global Arguments stm_match_list {Γ τ _} _ _ _ _ _.
    Global Arguments stm_match_sum {Γ τ _ _} _ _ _ _ _.
    Global Arguments stm_match_prod {Γ τ _ _} _ _ _ _.
    Global Arguments stm_match_enum {Γ τ} E e%exp alts%exp.
    Global Arguments stm_match_tuple {Γ τ σs Δ} e%exp p%pat rhs%exp.
    Global Arguments stm_match_union {Γ τ} U e {alt__ctx} alt__pat alt__rhs.
    Global Arguments stm_match_record {Γ τ} R {Δ} e%exp p%pat rhs%exp.
    Global Arguments stm_read_register {Γ τ} reg.
    Global Arguments stm_write_register {Γ τ} reg e%exp.

    Record Alternative (Γ : PCtx) (σ τ : Ty) : Set :=
      MkAlt
        { alt_ctx : PCtx;
          alt_pat : Pattern alt_ctx σ;
          alt_rhs : Stm (Γ ▻▻ alt_ctx) τ;
        }.

    Definition stm_match_union_alt {Γ τ} U (e : Exp Γ (ty_union U))
      (alts : forall (K : 𝑼𝑲 U), Alternative Γ (𝑼𝑲_Ty K) τ) : Stm Γ τ :=
      stm_match_union U e
        (fun K => alt_pat (alts K))
        (fun K => alt_rhs (alts K)).

    Definition stm_assert {Γ} (e1 : Exp Γ ty_bool) (e2 : Exp Γ ty_string) : Stm Γ ty_unit :=
      stm_assertk e1 e2 (stm_val ty_unit tt).
    Definition stm_lemma {Γ Δ} (l : 𝑳 Δ) (es : NamedEnv (Exp Γ) Δ) : Stm Γ ty_unit :=
      stm_lemmak l es (stm_val ty_unit tt).

    Global Arguments MkAlt {_ _ _ _} _ _.
    Global Arguments stm_match_union_alt {_ _} _ _ _.
    Global Arguments stm_assert {Γ} e1%exp e2%exp.
    Global Arguments stm_lemma {Γ Δ} l es%arg.

  End Statements.

  Bind Scope exp_scope with Stm.
  Bind Scope pat_scope with Pattern.
  Bind Scope pat_scope with TuplePat.
  Bind Scope pat_scope with RecordPat.

  Section NameResolution.

    (* Ideally the following smart constructors would perform name resolution
       and fill in the de Bruijn index and the type of a variable. Unfortunately,
       they critically rely on the order that type-checking is performed. For
       instance in context Γ := (ε ▻ "x"∷ty_int) the expression
       (@exp_smart_var Γ "x" tt) type-checks while the (@exp_smart_var _ "x" tt)
       fails to type-check with error message

         The term "tt" has type "unit" while it is expected
         to have type "IsSome (ctx.resolve ?Γ0 "x")".

       So the variable ?Γ0 has not been unified and blocks the evaluation of
       ctx.resolve. Unfortunately, Coq decides to fail immediately. This can be
       can be solved using bidirectionality hints, but is brittle.
     *)
    Definition exp_smart_var {Γ : PCtx} (x : 𝑿) {p : IsSome (ctx.resolve Γ x)} :
      Exp Γ (fromSome (ctx.resolve Γ x) p) :=
      @exp_var Γ x (fromSome (ctx.resolve Γ x) p) (ctx.resolve_mk_in Γ x p).

    Definition stm_smart_assign {Γ : PCtx} (x : 𝑿) {p : IsSome (ctx.resolve Γ x)} :
      Stm Γ (fromSome (ctx.resolve Γ x) p) -> Stm Γ (fromSome (ctx.resolve Γ x) p) :=
      @stm_assign Γ (fromSome _ p) x (ctx.resolve_mk_in Γ x p).

    (* Instead we hook mk_inctx directly into the typeclass resolution mechanism.
       Apparently, the unification of Γ is performed before the resolution so
       evaluation of ctx_resolve and mk_inctx is not blocked. This hook is more
       generally defined in Context.
     *)

  End NameResolution.

  Notation Valuation Σ := (@Env (Binding 𝑺 Ty) (fun xt : Binding 𝑺 Ty => Val (@type 𝑺 Ty xt)) Σ).

  Section Symbolic.

    Definition List (A : LCtx -> Type) (Σ : LCtx) : Type :=
      list (A Σ).
    Definition Const (A : Type) (Σ : LCtx) : Type :=
      A.

  End Symbolic.

  Section SymbolicTerms.

    Local Unset Elimination Schemes.

    Inductive Term (Σ : LCtx) : Ty -> Set :=
    | term_var     (ς : 𝑺) (σ : Ty) {ςInΣ : ς∷σ ∈ Σ} : Term Σ σ
    | term_val     (σ : Ty) : Val σ -> Term Σ σ
    | term_binop   {σ1 σ2 σ3 : Ty} (op : BinOp σ1 σ2 σ3) (e1 : Term Σ σ1) (e2 : Term Σ σ2) : Term Σ σ3
    | term_neg     (e : Term Σ ty_int) : Term Σ ty_int
    | term_not     (e : Term Σ ty_bool) : Term Σ ty_bool
    | term_inl     {σ1 σ2 : Ty} : Term Σ σ1 -> Term Σ (ty_sum σ1 σ2)
    | term_inr     {σ1 σ2 : Ty} : Term Σ σ2 -> Term Σ (ty_sum σ1 σ2)
    (* Experimental features *)
    | term_projtup {σs : Ctx Ty} (e : Term Σ (ty_tuple σs)) (n : nat) {σ : Ty}
                   {p : ctx.nth_is σs n σ} : Term Σ σ
    | term_union   {U : 𝑼} (K : 𝑼𝑲 U) (e : Term Σ (𝑼𝑲_Ty K)) : Term Σ (ty_union U)
    | term_record  (R : 𝑹) (es : NamedEnv (Term Σ) (𝑹𝑭_Ty R)) : Term Σ (ty_record R).
    (* | term_projrec {R : 𝑹} (e : Term Σ (ty_record R)) (rf : 𝑹𝑭) {σ : Ty} *)
    (*                {rfInR : InCtx (rf ∶ σ) (𝑹𝑭_Ty R)} : Term Σ σ. *)
    Local Set Transparent Obligations.
    Derive NoConfusion Signature for Term.

    Global Arguments term_var {_} _ {_ _}.
    Global Arguments term_val {_} _ _.
    Global Arguments term_neg {_} _.
    Global Arguments term_not {_} _.
    Global Arguments term_inl {_ _ _} _.
    Global Arguments term_inr {_ _ _} _.
    Global Arguments term_projtup {_ _} _%exp _ {_ _}.
    Global Arguments term_union {_} _ _.
    Global Arguments term_record {_} _ _.
    (* Global Arguments term_projrec {_ _} _ _ {_ _}. *)

    Definition term_enum {Σ} (E : 𝑬) (k : 𝑬𝑲 E) : Term Σ (ty_enum E) :=
      term_val (ty_enum E) k.
    Global Arguments term_enum {_} _ _.

    Fixpoint term_list {Σ σ} (ts : list (Term Σ σ)) : Term Σ (ty_list σ) :=
      match ts with
      | nil       => term_val (ty_list σ) nil
      | cons t ts => term_binop binop_cons t (term_list ts)
      end.

    Fixpoint term_tuple {Σ σs} (es : Env (Term Σ) σs) : Term Σ (ty_tuple σs) :=
      match es with
      | env.nil         => term_val (ty_tuple ε) tt
      | env.snoc es _ e => term_binop binop_tuple_snoc (term_tuple es) e
      end.

    Fixpoint term_bvec {Σ n} (es : Vector.t (Term Σ ty_bit) n) : Term Σ (ty_bvec n) :=
      match es with
      | Vector.nil       => term_val (ty_bvec 0) Word.WO
      | Vector.cons e es => term_binop binop_bvcons e (term_bvec es)
      end.

    Section Term_rect.

      Variable (Σ : LCtx).
      Variable (P  : forall t : Ty, Term Σ t -> Type).
      Arguments P _ _ : clear implicits.

      Let PL (σ : Ty) : list (Term Σ σ) -> Type :=
        List.fold_right (fun t ts => P _ t * ts)%type unit.
      Let PV (n : nat) (es : Vector.t (Term Σ ty_bit) n) : Type :=
        Vector.fold_right (fun e ps => P _ e * ps)%type es unit.
      Let PE : forall σs, Env (Term Σ) σs -> Type :=
        env.Env_rect (fun _ _ => Type) unit (fun _ ts IHts _ t => IHts * P _ t)%type.
      Let PNE : forall (σs : NCtx 𝑹𝑭 Ty), NamedEnv (Term Σ) σs -> Type :=
        env.Env_rect (fun _ _ => Type) unit (fun _ ts IHts _ t => IHts * P _ t)%type.

      Hypothesis (P_var        : forall (ς : 𝑺) (σ : Ty) (ςInΣ : ς∷σ ∈ Σ), P σ (term_var ς)).
      Hypothesis (P_val        : forall (σ : Ty) (v : Val σ), P σ (term_val σ v)).
      Hypothesis (P_binop      : forall (σ1 σ2 σ3 : Ty) (op : BinOp σ1 σ2 σ3) (e1 : Term Σ σ1) (e2 : Term Σ σ2), P σ1 e1 -> P σ2 e2 -> P σ3 (term_binop op e1 e2)).
      Hypothesis (P_neg        : forall e : Term Σ ty_int, P ty_int e -> P ty_int (term_neg e)).
      Hypothesis (P_not        : forall e : Term Σ ty_bool, P ty_bool e -> P ty_bool (term_not e)).
      Hypothesis (P_inl        : forall (σ1 σ2 : Ty) (t : Term Σ σ1), P σ1 t -> P (ty_sum σ1 σ2) (term_inl t)).
      Hypothesis (P_inr        : forall (σ1 σ2 : Ty) (t : Term Σ σ2), P σ2 t -> P (ty_sum σ1 σ2) (term_inr t)).
      Hypothesis (P_list       : forall (σ : Ty) (es : list (Term Σ σ)), PL es -> P (ty_list σ) (term_list es)).
      Hypothesis (P_bvec       : forall (n : nat) (es : Vector.t (Term Σ ty_bit) n), PV es -> P (ty_bvec n) (term_bvec es)).
      Hypothesis (P_tuple      : forall (σs : Ctx Ty) (es : Env (Term Σ) σs), PE es -> P (ty_tuple σs) (term_tuple es)).
      Hypothesis (P_projtup    : forall (σs : Ctx Ty) (e : Term Σ (ty_tuple σs)), P (ty_tuple σs) e -> forall (n : nat) (σ : Ty) (p : ctx.nth_is σs n σ), P σ (@term_projtup _ _ e n _ p)).
      Hypothesis (P_union      : forall (U : 𝑼) (K : 𝑼𝑲 U) (e : Term Σ (𝑼𝑲_Ty K)), P (𝑼𝑲_Ty K) e -> P (ty_union U) (term_union U K e)).
      Hypothesis (P_record     : forall (R : 𝑹) (es : NamedEnv (Term Σ) (𝑹𝑭_Ty R)), PNE es -> P (ty_record R) (term_record R es)).
      (* Hypothesis (P_projrec    : forall (R : 𝑹) (e : Term Σ (ty_record R)), P (ty_record R) e -> forall (rf : 𝑹𝑭) (σ : Ty) (rfInR : (rf ∶ σ)%ctx ∈ 𝑹𝑭_Ty R), P σ (term_projrec e rf)). *)

      Fixpoint Term_rect (σ : Ty) (t : Term Σ σ) : P σ t :=
        match t with
        | @term_var _ ς σ ςInΣ           => ltac:(eapply P_var; eauto)
        | @term_val _ σ x                => ltac:(eapply P_val; eauto)
        | term_binop op e1 e2            => ltac:(eapply P_binop; eauto)
        | @term_neg _ e                  => ltac:(eapply P_neg; eauto)
        | @term_not _ e                  => ltac:(eapply P_not; eauto)
        | @term_inl _ σ1 σ2 x            => ltac:(eapply P_inl; eauto)
        | @term_inr _ σ1 σ2 x            => ltac:(eapply P_inr; eauto)
        | @term_projtup _ σs e n σ p     => ltac:(eapply P_projtup; eauto)
        | @term_union _ U K e            => ltac:(eapply P_union; eauto)
        | @term_record _ R es            => ltac:(eapply P_record; induction es; cbn; eauto using unit)
        (* | @term_projrec _ R e rf σ rfInR => ltac:(eapply P_projrec; eauto) *)
        end.

    End Term_rect.

    Definition Term_rec Σ (P : forall σ, Term Σ σ -> Set) := Term_rect P.
    Definition Term_ind Σ (P : forall σ, Term Σ σ -> Prop) := Term_rect P.

    Equations(noind) Term_eqb {Σ} {σ : Ty} (t1 t2 : Term Σ σ) : bool :=
      Term_eqb (@term_var _ _ ς1inΣ) (@term_var _ _ ς2inΣ) :=
        ctx.In_eqb ς1inΣ ς2inΣ;
      Term_eqb (term_val _ v1) (term_val _ v2) := Val_eqb _ v1 v2;
      Term_eqb (term_binop op1 x1 y1) (term_binop op2 x2 y2)
        with binop_eqdep_dec op1 op2 => {
        Term_eqb (term_binop op1 x1 y1) (term_binop ?(op1) x2 y2) (left opeq_refl) :=
          Term_eqb x1 x2 && Term_eqb y1 y2;
        Term_eqb (term_binop op1 x1 y1) (term_binop op2 x2 y2) (right _) := false
      };
      Term_eqb (term_neg x) (term_neg y) := Term_eqb x y;
      Term_eqb (term_not x) (term_not y) := Term_eqb x y;
      Term_eqb (term_inl x) (term_inl y) := Term_eqb x y;
      Term_eqb (term_inr x) (term_inr y) := Term_eqb x y;
      Term_eqb (@term_projtup σs x n _ p) (@term_projtup τs y m _ q)
        with eq_dec σs τs => {
        Term_eqb (@term_projtup σs x n _ p) (@term_projtup ?(σs) y m _ q) (left eq_refl) :=
          (n =? m) && Term_eqb x y;
        Term_eqb (@term_projtup _ x n _ p) (@term_projtup _ y m _ q) (right _) := false
        };
      Term_eqb (@term_union ?(u) _ k1 e1) (@term_union u _ k2 e2)
        with eq_dec k1 k2 => {
        Term_eqb (term_union k1 e1) (term_union ?(k1) e2) (left eq_refl) :=
          Term_eqb e1 e2;
        Term_eqb _ _ (right _) := false
      };
      Term_eqb (@term_record ?(r) xs) (@term_record r ys) :=
         @env.eqb_hom _ (fun b => Term Σ (type b)) (fun b => @Term_eqb _ (type b)) _ xs ys;
      (* Term_eqb (@term_projrec r1 e1 _ _ prf1) (@term_projrec r2 e2 _ _ prf2) *)
      (*          with (𝑹_eq_dec r1 r2) => { *)
      (* Term_eqb (@term_projrec r e1 _ _ prf1) (@term_projrec ?(r) e2 _ _ prf2) *)
      (*   (left eq_refl) := InCtx_eqb prf1 prf2 && Term_eqb e1 e2; *)
      (* Term_eqb (@term_projrec r1 e1 _ _ prf1) (@term_projrec r2 e2 _ _ prf2) *)
      (*   (right _) := false }; *)

      Term_eqb _ _ := false.

    Local Transparent Term_eqb.
    Local Set Equations With UIP.
    Lemma Term_eqb_spec Σ (σ : Ty) (t1 t2 : Term Σ σ) :
      reflect (t1 = t2) (Term_eqb t1 t2).
    Proof.
      induction t1 using Term_rect; cbn [Term_eqb]; dependent elimination t2;
        solve_eqb_spec with
        try match goal with
            | |- context[Val_eqb _ ?l1 ?l2] => destruct (Val_eqb_spec _ l1 l2)
            | |- context[binop_eqdep_dec ?x ?y] =>
                let e := fresh in
                destruct (binop_eqdep_dec x y) as [e|];
                [dependent elimination e|]
            | H: ~ OpEq ?o ?o |- False => apply H; constructor
            end.
      - apply (@ssrbool.iffP (es = es0)).
        + revert es0.
          induction es; intros es0; dependent elimination es0; solve_eqb_spec.
          destruct X as [x1 x2].
          specialize (IHes x1 E).
          specialize (x2 db0).
          solve_eqb_spec.
        + solve_eqb_spec.
        + solve_eqb_spec.
    Qed.

  End SymbolicTerms.
  Bind Scope exp_scope with Term.

  Section PatternMatching.

    Definition tuple_pattern_match_env {N : Set} {T : Ty -> Set} :
      forall {σs : Ctx Ty} {Δ : NCtx N Ty},
        TuplePat σs Δ -> Env T σs -> NamedEnv T Δ :=
      fix pattern_match {σs} {Δ} p {struct p} :=
        match p with
        | tuplepat_nil => fun _ => env.nil
        | tuplepat_snoc p x =>
          fun EΔ =>
            match env.snocView EΔ with
            | env.isSnoc E v => pattern_match p E ► (_∷_ ↦ v)
            end
        end.

    Definition tuple_pattern_match_env_reverse {N : Set} {T : Ty -> Set} :
      forall {σs : Ctx Ty} {Δ : NCtx N Ty},
        TuplePat σs Δ -> NamedEnv T Δ -> Env T σs :=
      fix pattern_match {σs} {Δ} p {struct p} :=
        match p with
        | tuplepat_nil => fun _ => env.nil
        | tuplepat_snoc p x =>
          fun EΔ =>
            match env.snocView EΔ with
            | env.isSnoc E v => pattern_match p E ► (_ ↦ v)
            end
        end.

    Definition tuple_pattern_match_val {N : Set} {σs : Ctx Ty} {Δ : NCtx N Ty}
             (p : TuplePat σs Δ) : Val (ty_tuple σs) -> NamedEnv Val Δ :=
      fun lit => tuple_pattern_match_env p (@envrec.to_env Ty Val σs lit).

    Fixpoint record_pattern_match_env {N : Set} {V : Ty -> Set} {rfs : NCtx 𝑹𝑭 Ty} {Δ : NCtx N Ty}
             (p : RecordPat rfs Δ) {struct p} : NamedEnv V rfs -> NamedEnv V Δ :=
      match p with
      | recordpat_nil => fun _ => env.nil
      | recordpat_snoc p rf x =>
        fun E =>
          env.snoc
            (record_pattern_match_env p (env.tail E)) (x∷_)
            (env.lookup E ctx.in_zero)
      end.

    Fixpoint record_pattern_match_env_reverse {N : Set} {V : Ty -> Set} {rfs : NCtx 𝑹𝑭 Ty} {Δ : NCtx N Ty}
             (p : RecordPat rfs Δ) {struct p} :  NamedEnv V Δ -> NamedEnv V rfs :=
      match p with
      | recordpat_nil => fun _ => env.nil
      | recordpat_snoc p rf x =>
        fun E =>
          env.snoc
            (record_pattern_match_env_reverse p (env.tail E)) (rf∷_)
            (env.lookup E ctx.in_zero)
      end.

    Lemma record_pattern_match_env_inverse_right {N : Set} {V : Ty -> Set} {rfs : NCtx 𝑹𝑭 Ty} {Δ : NCtx N Ty}
          (p : RecordPat rfs Δ) (vs : NamedEnv V Δ) :
      record_pattern_match_env p (record_pattern_match_env_reverse p vs) = vs.
    Proof.
      induction p.
      - now destruct (env.nilView vs).
      - destruct (env.snocView vs) as [vs v].
        cbn. f_equal. now apply IHp.
    Qed.

    Lemma record_pattern_match_env_inverse_left {N : Set} {V : Ty -> Set} {rfs : NCtx 𝑹𝑭 Ty} {Δ : NCtx N Ty}
          (p : RecordPat rfs Δ) (vs : NamedEnv V rfs) :
      record_pattern_match_env_reverse p (record_pattern_match_env p vs) = vs.
    Proof.
      induction p.
      - now destruct (env.nilView vs).
      - destruct (env.snocView vs) as [vs v].
        cbn. f_equal. now apply IHp.
    Qed.

    Lemma tuple_pattern_match_env_inverse_right {N : Set} {T : Ty -> Set}
      {σs : Ctx Ty} {Δ : NCtx N Ty} (p : TuplePat σs Δ) (ts : NamedEnv T Δ) :
      tuple_pattern_match_env p (tuple_pattern_match_env_reverse p ts) = ts.
    Proof.
      induction p; cbn.
      - now destruct (env.nilView ts).
      - destruct (env.snocView ts); cbn.
        now rewrite (IHp E).
    Qed.

    Lemma tuple_pattern_match_env_inverse_left {N : Set} {T : Ty -> Set}
          {σs : Ctx Ty} {Δ : NCtx N Ty} (p : TuplePat σs Δ) (ts : Env T σs) :
      tuple_pattern_match_env_reverse p (tuple_pattern_match_env p ts) = ts.
    Proof.
      induction p.
      - now destruct (env.nilView ts).
      - destruct (env.snocView ts); cbn.
        now rewrite (IHp E).
    Qed.

    Definition record_pattern_match_val {N : Set} {R} {Δ : NCtx N Ty}
      (p : RecordPat (𝑹𝑭_Ty R) Δ) : Val (ty_record R) -> NamedEnv Val Δ :=
      fun v => record_pattern_match_env p (𝑹_unfold v).

    Definition pattern_match_val {N : Set} {σ : Ty} {Δ : NCtx N Ty} (p : Pattern Δ σ) :
      Val σ -> NamedEnv Val Δ :=
      match p with
      | pat_var x => fun v => env.snoc env.nil (x∷_) v
      | pat_unit => fun _ => env.nil
      | pat_pair x y => fun '(u , v) => env.snoc (env.snoc env.nil (x∷_) u) (y∷_) v
      | pat_tuple p => tuple_pattern_match_val p
      | pat_record p => record_pattern_match_val p
      end.

    Definition pattern_match_env_reverse {N : Set} {Σ : LCtx} {σ : Ty} {Δ : NCtx N Ty} (p : Pattern Δ σ) :
      NamedEnv (Term Σ) Δ -> Term Σ σ :=
      match p with
      | pat_var x    => fun Ex => match env.snocView Ex with env.isSnoc _ t => t end
      | pat_unit     => fun _ => term_val ty_unit tt
      | pat_pair x y => fun Exy => match env.snocView Exy with
                                     env.isSnoc Ex ty =>
                                     match env.snocView Ex with
                                       env.isSnoc _ tx => term_binop binop_pair tx ty
                                     end
                                   end
      | pat_tuple p  => fun EΔ => term_tuple (tuple_pattern_match_env_reverse p EΔ)
      | pat_record p => fun EΔ => term_record _ (record_pattern_match_env_reverse p EΔ)
      end.

    Definition pattern_match_env_val_reverse {N : Set} {σ : Ty} {Δ : NCtx N Ty} (p : Pattern Δ σ) :
      NamedEnv Val Δ -> Val σ :=
      match p with
      | pat_var x    => fun Ex => match env.snocView Ex with env.isSnoc _ t => t end
      | pat_unit     => fun _ => (tt : Val ty_unit)
      | pat_pair x y => fun Exy => match env.snocView Exy with
                                     env.isSnoc Ex ty =>
                                     match env.snocView Ex with
                                       env.isSnoc _ tx => (pair tx ty : Val (ty_prod _ _))
                                     end
                                   end
      | pat_tuple p  => fun EΔ => (envrec.of_env (tuple_pattern_match_env_reverse p EΔ) : Val (ty_tuple _))
      | pat_record p => fun EΔ => (𝑹_fold (record_pattern_match_env_reverse p EΔ) : Val (ty_record _))
      end.


    Lemma pattern_match_val_inverse_left {N : Set} {σ : Ty} {Δ : NCtx N Ty} {p : Pattern Δ σ}
          (v : Val σ) :
      pattern_match_env_val_reverse p (pattern_match_val p v) = v.
    Proof.
      induction p; cbn; eauto.
      - now destruct v.
      - now destruct v.
      - unfold tuple_pattern_match_val.
        now rewrite tuple_pattern_match_env_inverse_left, envrec.of_to_env.
      - unfold record_pattern_match_val.
        now rewrite record_pattern_match_env_inverse_left, 𝑹_fold_unfold.
    Qed.

    Lemma pattern_match_val_inverse_right {N : Set} {σ : Ty} {Δ : NCtx N Ty} (p : Pattern Δ σ)
      (vs : NamedEnv Val Δ) :
      pattern_match_val p (pattern_match_env_val_reverse p vs) = vs.
    Proof.
      induction p; cbn; eauto.
      - destruct (env.snocView vs).
        now destruct (env.nilView E).
      - now destruct (env.nilView vs).
      - destruct (env.snocView vs).
        destruct (env.snocView E).
        now destruct (env.nilView E).
      - unfold tuple_pattern_match_val.
        now rewrite envrec.to_of_env, tuple_pattern_match_env_inverse_right.
      - unfold record_pattern_match_val.
        now rewrite 𝑹_unfold_fold, record_pattern_match_env_inverse_right.
    Qed.

  End PatternMatching.

  Section SymbolicSubstitutions.

    Definition Sub (Σ1 Σ2 : LCtx) : Set :=
      Env (fun b => Term Σ2 (type b)) Σ1.
    (* Hint Unfold Sub. *)

    Class Subst (T : LCtx -> Type) : Type :=
      subst : forall {Σ1 : LCtx}, T Σ1 -> forall {Σ2 : LCtx}, Sub Σ1 Σ2 -> T Σ2.
    Global Arguments subst {T _ Σ1} t {Σ2} ζ.

    Fixpoint sub_term {σ Σ1} (t : Term Σ1 σ) {Σ2} (ζ : Sub Σ1 Σ2) {struct t} : Term Σ2 σ :=
      match t with
      | term_var ς                => ζ ‼ ς
      | term_val σ v              => term_val σ v
      | term_binop op t1 t2       => term_binop op (sub_term t1 ζ) (sub_term t2 ζ)
      | term_neg t0               => term_neg (sub_term t0 ζ)
      | term_not t0               => term_not (sub_term t0 ζ)
      | @term_inl _ σ1 σ2 t0      => term_inl (sub_term t0 ζ)
      | @term_inr _ σ1 σ2 t0      => term_inr (sub_term t0 ζ)
      | @term_projtup _ _ t n σ p => term_projtup (sub_term t ζ) n (p := p)
      | term_union U K t          => term_union U K (sub_term t ζ)
      | term_record R ts          => term_record R (env.map (fun _ t => sub_term t ζ) ts)
      end.

    Global Instance SubstTerm {σ} : Subst (fun Σ => Term Σ σ) :=
      @sub_term σ.
    Global Instance SubstList {A} `{Subst A} : Subst (List A) :=
      fix substlist {Σ1} xs {Σ2} ζ :=
        match xs with
        | nil => nil
        | cons x xs => cons (subst x ζ) (substlist xs ζ)
        end.

    Lemma substlist_is_map_subst {A} `{Subst A} {Σ1 Σ2} (xs : List A Σ1) (ζ : Sub Σ1 Σ2) :
      subst xs ζ = List.map (fun x => subst x ζ) xs.
    Proof. induction xs; cbn; f_equal; auto. Qed.

    Global Instance SubstConst {A} `{finite.Finite A} : Subst (Const A) :=
      fun _ x _ _ => x.
    Global Instance SubstEnv {B : Set} {A : Ctx _ -> B -> Set} `{forall b, Subst (fun Σ => A Σ b)} {Δ : Ctx B} :
      Subst (fun Σ => Env (A Σ) Δ) :=
      fun Σ1 xs Σ2 ζ => env.map (fun b a => subst (T := fun Σ => A Σ b) a ζ) xs.

    Definition sub_id Σ : Sub Σ Σ :=
      @env.tabulate _ (fun b => Term _ (type b)) _
                    (fun '(ς∷σ) ςIn => @term_var Σ ς σ ςIn).
    Global Arguments sub_id : clear implicits.

    Definition sub_snoc {Σ1 Σ2 : LCtx} (ζ : Sub Σ1 Σ2) b (t : Term Σ2 (type b)) :
      Sub (Σ1 ▻ b) Σ2 := env.snoc ζ b t.
    Global Arguments sub_snoc {_ _} _ _ _.

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

    Definition sub_single {Σ x σ} (xIn : x∷σ ∈ Σ) (t : Term (Σ - x∷σ) σ) : Sub Σ (Σ - x∷σ) :=
      @env.tabulate
        _ (fun b => Term _ (type b)) _
        (fun '(y∷τ) =>
           fun yIn =>
             match ctx.occurs_check_var xIn yIn with
             | inl e => eq_rect σ (Term (Σ - x∷σ)) t τ (f_equal type e)
             | inr i => term_var y
             end).

    Class SubstLaws (T : LCtx -> Type) `{Subst T} : Type :=
      { subst_sub_id Σ (t : T Σ) :
          subst t (sub_id _) = t;
        subst_sub_comp Σ0 Σ1 Σ2 (ζ1 : Sub Σ0 Σ1) (ζ2 : Sub Σ1 Σ2) t :
          subst t (subst ζ1 ζ2) = subst (subst t ζ1) ζ2;
      }.

    Global Arguments SubstLaws T {_}.

    Global Instance SubstLawsTerm {σ} : SubstLaws (fun Σ => Term Σ σ).
    Proof.
      constructor.
      { intros ? t.
        induction t; cbn; f_equal; try assumption.
        - unfold sub_id.
          now rewrite env.lookup_tabulate.
        - induction es; cbn in *.
          + reflexivity.
          + f_equal.
            * apply IHes, X.
            * apply X.
      }
      { intros ? ? ? ? ? t.
        induction t; cbn; f_equal; try assumption.
        - unfold subst at 1, SubstEnv.
          now rewrite env.lookup_map.
        - induction es; cbn in *.
          + reflexivity.
          + f_equal.
            * apply IHes, X.
            * apply X.
      }
    Qed.

    Global Instance SubstLawsList {A} `{SubstLaws A} : SubstLaws (List A).
    Proof.
      constructor.
      { intros ? t.
        induction t; cbn; f_equal; auto using subst_sub_id.
      }
      { intros ? ? ? ? ? t.
        induction t; cbn; f_equal; auto using subst_sub_comp.
      }
    Qed.

    Global Instance SubstLawsConst {A} `{finite.Finite A} : SubstLaws (Const A).
    Proof. constructor; reflexivity. Qed.

    Global Instance SubstLawsEnv {B : Set} {A : Ctx _ -> B -> Set}
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

  End SymbolicSubstitutions.

  Module SubNotations.

    Notation "a ⟨ ζ ⟩" := (subst a ζ)
      (at level 8, left associativity,
        format "a ⟨ ζ ⟩").
    Notation "ζ1 ∘ ζ2" := (@subst (Sub _) _ _ ζ1 _ ζ2) (at level 60, right associativity).

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
    Proof. unfold sub_single. now rewrite env.lookup_tabulate, ctx.occurs_check_var_refl. Qed.

    Lemma lookup_sub_single_neq {Σ x σ y τ} (xIn : x ∷ σ ∈ Σ) (t : Term (Σ - x∷σ) σ) (yIn : y∷τ ∈ Σ - x∷σ) :
      env.lookup (sub_single xIn t) (ctx.shift_var xIn yIn) = term_var y.
    Proof. unfold sub_single. now rewrite env.lookup_tabulate, ctx.occurs_check_shift_var. Qed.

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
      now destruct (env.snocView ζ) as [ζ t].
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
      destruct (ctx.snocView yIn) as [|[y τ] yIn].
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

  Section OccursCheck.

    Class OccursCheck (T : LCtx -> Type) : Type :=
      occurs_check : forall {Σ x} (xIn : x ∈ Σ) (t : T Σ), option (T (Σ - x)%ctx).

    Import stdpp.base.

    Fixpoint occurs_check_term {Σ x} (xIn : x ∈ Σ) {σ} (t : Term Σ σ) : option (Term (Σ - x) σ) :=
      match t with
      | @term_var _ ς σ0 ςInΣ =>
        match ctx.occurs_check_var xIn ςInΣ with
        | inl e     => None
        | inr ςInΣ' => Some (@term_var _ _ _ ςInΣ')
        end
      | term_val σ0 v => Some (term_val σ0 v)
      | term_binop op t1 t2 =>
        t1' ← occurs_check_term xIn t1; t2' ← occurs_check_term xIn t2; Some (term_binop op t1' t2')
      | term_neg t => option_map term_neg (occurs_check_term xIn t)
      | term_not t => option_map term_not (occurs_check_term xIn t)
      | term_inl t => option_map term_inl (occurs_check_term xIn t)
      | term_inr t => option_map term_inr (occurs_check_term xIn t)
      | @term_projtup _ σs t n σ p =>
        option_map (fun t' => @term_projtup _ _ t' n _ p) (occurs_check_term xIn t)
      | term_union U K t => option_map (term_union U K) (occurs_check_term xIn t)
      | term_record R es => option_map (term_record R) (env.traverse (fun _ => occurs_check_term xIn) es)
      (* | term_projrec t rf => option_map (fun t' => term_projrec t' rf) (occurs_check_term xIn t) *)
      end.

    Global Instance OccursCheckTerm {σ} : OccursCheck (fun Σ => Term Σ σ) :=
      fun _ _ xIn => occurs_check_term xIn.

    Global Instance OccursCheckList {T : LCtx -> Type} `{OccursCheck T} :
      OccursCheck (List T) :=
      fun _ _ xIn => traverse_list (occurs_check xIn).

    Global Instance OccursCheckEnv {I : Set} {T : LCtx -> I -> Set}
           {_ : forall i : I, OccursCheck (fun Σ => T Σ i)}
           {Γ : Ctx I} :
      OccursCheck (fun Σ => Env (T Σ) Γ) :=
      fun _ _ xIn => env.traverse (fun i => occurs_check (T := fun Σ => T Σ i) xIn).

    Global Instance OccursCheckSub {Σ} : OccursCheck (Sub Σ) :=
      OccursCheckEnv.

  End OccursCheck.

  Section OccursCheckLaws.

    Class OccursCheckLaws (T : LCtx -> Type) `{Subst T, OccursCheck T} : Prop :=
      { occurs_check_shift {Σ x σ} (xIn : x∷σ ∈ Σ) (t : T (Σ - x∷σ)) :
          occurs_check xIn (subst t (sub_shift xIn)) = Some t;
        occurs_check_sound {Σ x} (xIn : x ∈ Σ) (t : T Σ) (t' : T (Σ - x)) :
          occurs_check xIn t = Some t' -> t = subst t' (sub_shift xIn);
      }.

    Global Arguments OccursCheckLaws T {_ _}.

    Lemma option_map_eq_some {A B} (f : A -> B) (o : option A) (a : A) :
      o = Some a ->
      option_map f o = Some (f a).
    Proof. now intros ->. Qed.

    Lemma option_map_eq_some' {A B} (f : A -> B) (o : option A) (b : B) :
      option_map f o = Some b <->
      exists a, o = Some a /\ f a = b.
    Proof.
      split.
      - destruct o as [a|].
        + intros H. apply noConfusion_inv in H. cbn in H.
          exists a. split; congruence.
        + discriminate.
      - now intros (a & -> & <-).
    Qed.

    Lemma option_bind_eq_some {A B} (f : A -> option B) (o : option A) (b : B) :
      (exists a, o = Some a /\ f a = Some b) <->
      option.option_bind A B f o = Some b.
    Proof.
      split.
      - now intros (a & -> & <-).
      - destruct o as [a|]; [ now exists a | discriminate ].
    Qed.

    Local Ltac solve :=
      repeat
        match goal with
        | H: Some _ = Some _ |- _ =>
          apply noConfusion_inv in H; cbn in H; subst
        | H: base.mbind _ _ = Some _ |- _ =>
          apply option_bind_eq_some in H; cbn in H; destruct_conjs; subst
        | H: option_map _ _ = Some _ |- _ =>
          apply option_map_eq_some' in H; cbn in H; destruct_conjs; subst

        | |- match occurs_check_term ?xIn ?t with _ => _ end = _ =>
          destruct (occurs_check_term xIn t); try discriminate
        | |- match occurs_check ?xIn ?t with _ => _ end = _ =>
          destruct (occurs_check xIn t); try discriminate
        | |- base.mbind _ _ = Some _ =>
          apply option_bind_eq_some; eexists; split; [ eassumption; fail | idtac ]
        | |- option_map ?f _ = Some (?f _) =>
          apply option_map_eq_some
        | |- option_map _ _ = Some _ =>
          apply option_map_eq_some'; eexists; split; [ eassumption; fail | idtac ]
        | |- _ =>
          unfold base.mret, option.option_ret in *; cbn in *; try congruence
        end.

    Global Instance OccursCheckLawsTerm {τ} : OccursCheckLaws (fun Σ => Term Σ τ).
    Proof.
      constructor.
      - intros; unfold occurs_check, OccursCheckTerm, subst, SubstTerm.
        induction t; cbn.
        + unfold sub_shift. rewrite env.lookup_tabulate.
          cbv [occurs_check_term base.mbind option.option_bind].
          now rewrite ctx.occurs_check_shift_var.
        + solve.
        + solve.
        + solve.
        + solve.
        + solve.
        + solve.
        + solve.
        + solve.
        + solve.
          induction es; destruct X; cbn.
          * reflexivity.
          * now rewrite IHes, e0.
        (* + solve. *)
      - unfold occurs_check, OccursCheckTerm, subst, SubstTerm.
        intros ? ? ? t t' H1.
        induction t; cbn in H1.
        + pose proof (ctx.occurs_check_var_spec xIn ςInΣ) as H2.
          destruct (ctx.occurs_check_var xIn ςInΣ); apply noConfusion_inv in H1;
            cbn in H1; try contradiction; subst; cbn.
          destruct H2 as [H2 H3]. subst. unfold sub_shift.
          now rewrite env.lookup_tabulate.
        + solve.
        + solve. f_equal; auto.
        + solve. f_equal; auto.
        + solve. f_equal; auto.
        + solve. f_equal; auto.
        + solve. f_equal; auto.
        + solve. f_equal. auto.
        + solve. f_equal. auto.
        + solve. f_equal.
          change (es = subst H1 (sub_shift xIn)).
          induction es; destruct X; cbn.
          * destruct (env.nilView H1). reflexivity.
          * destruct (env.snocView H1).
            change (es ► (b ↦ db) = subst E (sub_shift xIn) ► (b ↦ subst v (sub_shift xIn))).
            cbn in H.
            apply option.bind_Some in H.
            destruct H as [E' [HE H]].
            apply option.bind_Some in H.
            destruct H as [t' [? Heq]].
            unfold base.mret in Heq.
            apply noConfusion_inv in Heq.
            cbn in Heq.
            apply env.inversion_eq_snoc in Heq.
            destruct Heq; subst.
            f_equal.
            apply IHes; auto.
            apply e0; auto.
    Qed.

    Global Instance OccursCheckLawsList {T : LCtx -> Type} `{OccursCheckLaws T} :
      OccursCheckLaws (fun Σ => list (T Σ)).
    Proof.
      constructor.
      - intros. induction t; cbn.
        + reflexivity.
        + cbv [base.mbind option.option_bind].
          now rewrite occurs_check_shift, IHt.
      - intros ? ? ? t. induction t; cbn; intros t' Heq.
        + solve.
        + solve. apply occurs_check_sound in H2.
          f_equal; auto.
    Qed.

    Global Instance OccursCheckLawsEnv {I : Set} {T : LCtx -> I -> Set}
           {_ : forall i : I, Subst (fun Σ => T Σ i)}
           {_ : forall i : I, OccursCheck (fun Σ => T Σ i)}
           {_ : forall i : I, OccursCheckLaws (fun Σ => T Σ i)}
           {Γ : Ctx I} :
      OccursCheckLaws (fun Σ => Env (T Σ) Γ).
    Proof.
      constructor.
      - intros. induction t.
        + reflexivity.
        + unfold occurs_check, OccursCheckEnv, subst, SubstEnv in IHt.
          cbn. cbv [base.mbind option.option_ret option.option_bind] in *.
          now rewrite IHt, occurs_check_shift.
      - intros ? ? ? E. induction E; cbn; intros E' Heq.
        + solve. reflexivity.
        + solve. apply (occurs_check_sound (T := fun Σ => T Σ _)) in H2.
          f_equal.
          * now apply IHE.
          * auto.
    Qed.

    Global Instance OccursCheckLawsSub {Σ} : OccursCheckLaws (Sub Σ) :=
      OccursCheckLawsEnv.

  End OccursCheckLaws.

  Section Instantiation.

    (* This type class connects a symbolic representation of a type with its
       concrete / semi-concrete counterpart. The method 'inst' will instantiate
       all logic variables in a symbolic value to obtain the concrete value and
       'lift' injects the concrete type into the symbolic one. *)
    Class Inst (T : LCtx -> Type) (A : Type) : Type :=
      { inst {Σ} (t : T Σ) (ι : Valuation Σ) : A;
        lift {Σ} (a : A) : T Σ;
      }.

    Global Instance instantiate_list {T : LCtx -> Type} {A : Type} `{Inst T A} :
      Inst (List T) (list A) :=
      {| inst Σ xs ι := List.map (fun x => inst x ι) xs;
         lift Σ      := List.map lift;
      |}.

    Global Instance instantiate_const {A} `{finite.Finite A} :
      Inst (Const A) A :=
      {| inst Σ x ι := x;
         lift Σ x   := x;
      |}.

    Global Instance instantiate_env {T : Set} {S : LCtx -> T -> Set}
           {A : T -> Set} {InstSA : forall τ : T, Inst (fun Σ => S Σ τ) (A τ)}
           {Γ : Ctx T} :
      Inst (fun Σ => Env (S Σ) Γ) (Env A Γ) :=
      {| inst Σ xs ι := env.map (fun (b : T) (s : S Σ b) => inst s ι) xs;
         lift Σ      := env.map (fun (b : T) (a : A b) => lift a)
      |}.

    Fixpoint inst_term {σ : Ty} {Σ : LCtx} (t : Term Σ σ) (ι : Valuation Σ) {struct t} : Val σ :=
      match t in Term _ σ return Val σ with
      | @term_var _ _ _ bIn  => env.lookup ι bIn
      | term_val _ v         => v
      | term_binop op e1 e2  => eval_binop op (inst_term e1 ι) (inst_term e2 ι)
      | term_neg e           => Z.opp (inst_term e ι)
      | term_not e           => negb (inst_term e ι)
      | term_inl e           => @inl (Val _) (Val _) (inst_term e ι)
      | term_inr e           => @inr (Val _) (Val _) (inst_term e ι)
      | @term_projtup _ σs e n σ p => tuple_proj σs n σ (inst_term e ι) p
      | @term_union _ U K e     => 𝑼_fold (existT K (inst_term e ι))
      | @term_record _ R ts     =>
          let InstTerm :=
            fun xt : Binding 𝑹𝑭 Ty => {| inst := @inst_term (@type 𝑹𝑭 Ty xt);
                                   lift Σ := @term_val Σ (@type 𝑹𝑭 Ty xt) |} in
          𝑹_fold (inst (Inst := instantiate_env (InstSA := InstTerm)) ts ι)
      end.

    Global Instance instantiate_term {σ} : Inst (fun Σ => Term Σ σ) (Val σ) :=
      {| inst Σ t ι := inst_term t ι;
         lift Σ v   := term_val σ v;
      |}.

    Global Instance instantiate_sub {Σ} : Inst (Sub Σ) (Valuation Σ) :=
      instantiate_env.

    Class InstLaws (T : LCtx -> Type) (A : Type) `{SubstLaws T, Inst T A} : Prop :=
      { inst_lift {Σ} (ι : Valuation Σ) (a : A) :
          inst (lift a) ι = a;
        inst_subst {Σ Σ'} (ζ : Sub Σ Σ') (ι : Valuation Σ') (t : T Σ) :
          inst (subst t ζ) ι = inst t (inst ζ ι)
      }.

    Global Arguments InstLaws T A {_ _ _}.

    Global Instance instantiatelaws_term {σ} : InstLaws (fun Σ => Term Σ σ) (Val σ).
    Proof.
      constructor.
      { reflexivity. }
      { induction t; cbn; try (f_equal; auto; fail).
        - now rewrite env.lookup_map.
        - f_equal.
          f_equal.
          apply IHt.
        - f_equal.
          induction es; cbn in *.
          + reflexivity.
          + f_equal.
            * apply IHes, X.
            * apply X.
        (* - f_equal. *)
        (*   f_equal. *)
        (*   apply IHt. *)
      }
    Qed.

    Global Instance instantiatelaws_list {T : LCtx -> Set} {A : Set} `{InstLaws T A} :
      InstLaws (List T) (list A).
    Proof.
      constructor.
      { intros; cbn.
        rewrite List.map_map, <- List.map_id.
        apply List.map_ext, inst_lift.
      }
      { intros ? ? ζ ι xs; cbn.
        rewrite substlist_is_map_subst.
        rewrite List.map_map.
        apply List.map_ext, inst_subst.
      }
    Qed.

    Global Instance instantiatelaws_const {A} `{finite.Finite A} :
      InstLaws (Const A) A.
    Proof. constructor; reflexivity. Qed.

    Global Instance instantiatelaws_env {T : Set} {S : LCtx -> T -> Set} {A : T -> Set}
           {_ : forall τ : T, Subst (fun Σ => S Σ τ)}
           {_ : forall τ : T, SubstLaws (fun Σ => S Σ τ)}
           {_ : forall τ : T, Inst (fun Σ => S Σ τ) (A τ)}
           {_ : forall τ : T, InstLaws (fun Σ => S Σ τ) (A τ)}
           {Γ : Ctx T} :
      InstLaws (fun Σ => Env (S Σ) Γ) (Env A Γ).
    Proof.
      constructor.
      { intros; cbn.
        rewrite env.map_map.
        apply env.map_id_eq.
        intros; apply inst_lift.
      }
      { intros ? ? ζ ι E; cbn.
        unfold subst, SubstEnv.
        rewrite env.map_map.
        apply env.map_ext.
        intros b s.
        now rewrite inst_subst.
      }
    Qed.

    Global Instance instantiatelaws_sub {Σ} : InstLaws (Sub Σ) (Valuation Σ).
    Proof. apply instantiatelaws_env. Qed.

    Lemma inst_env_snoc {B : Set} {AT : LCtx -> B -> Set}
           {A : B -> Set} {_ : forall b : B, Inst (fun Σ => AT Σ b) (A b)}
           {Γ : Ctx B} {Σ} (ι : Valuation Σ) (E : Env (AT Σ) Γ) (b : B) (a : AT Σ b) :
      inst (env.snoc E b a) ι = env.snoc (inst E ι) b (inst a ι).
    Proof. reflexivity. Qed.

    Lemma inst_sub_wk1 {Σ b v} (ι : Valuation Σ) :
      inst sub_wk1 (ι ► (b ↦ v)) = ι.
    Proof.
      apply env.lookup_extensional.
      intros [x σ] ?; unfold sub_wk1; cbn.
      now rewrite env.map_tabulate, env.lookup_tabulate.
    Qed.

    Lemma inst_sub_id {Σ} (ι : Valuation Σ) :
      inst (sub_id Σ) ι = ι.
    Proof.
      apply env.lookup_extensional.
      intros [x τ] ?; unfold sub_id; cbn.
      now rewrite env.map_tabulate, env.lookup_tabulate.
    Qed.

    Lemma inst_sub_snoc {Σ0 Σ1} (ι : Valuation Σ1) (ζ : Sub Σ0 Σ1) b (t : Term Σ1 (type b)) :
      inst (sub_snoc ζ b t) ι = env.snoc (inst ζ ι) b (inst t ι).
    Proof. reflexivity. Qed.

    Lemma inst_sub_up1 {Σ1 Σ2 b} (ζ12 : Sub Σ1 Σ2) (ι2 : Valuation Σ2) (v : Val (type b)) :
      inst (sub_up1 ζ12) (ι2 ► (b ↦ v)) = inst ζ12 ι2 ► (b ↦ v).
    Proof.
      destruct b; unfold sub_up1.
      now rewrite inst_sub_snoc, inst_subst, inst_sub_wk1.
    Qed.

    Lemma inst_sub_shift {Σ} (ι : Valuation Σ) {b} (bIn : b ∈ Σ) :
      inst (sub_shift bIn) ι = env.remove b ι bIn.
    Proof.
      rewrite env.remove_remove'.
      unfold env.remove', sub_shift, inst; cbn.
      apply env.lookup_extensional. intros [y τ] yIn.
      now rewrite env.lookup_map, ?env.lookup_tabulate.
    Qed.

    Lemma inst_sub_single_shift {Σ} (ι : Valuation Σ) {x σ} (xIn : x∷σ ∈ Σ) (t : Term (Σ - x∷σ) σ) :
      inst t (inst (sub_shift xIn) ι) = env.lookup ι xIn ->
      inst (sub_single xIn t) (inst (sub_shift xIn) ι) = ι.
    Proof.
      rewrite inst_sub_shift.
      rewrite env.remove_remove'.
      intros HYP. apply env.lookup_extensional. intros [y τ] yIn.
      unfold inst, sub_single; cbn.
      rewrite env.lookup_map, env.lookup_tabulate.
      pose proof (ctx.occurs_check_var_spec xIn yIn).
      destruct (ctx.occurs_check_var xIn yIn).
      * dependent elimination e. subst yIn. exact HYP.
      * destruct H; subst yIn. cbn. unfold env.remove'.
        now rewrite env.lookup_tabulate.
    Qed.

    Lemma sub_single_zero {Σ : LCtx} {x : 𝑺} {σ : Ty} (t : Term Σ σ) :
      (sub_single ctx.in_zero t) = env.snoc (sub_id Σ) (x∷σ) t.
    Proof.
      eapply env.lookup_extensional.
      intros [x' σ'] ([|n] & eq).
      - cbn in *.
        now subst.
      - cbn in *.
        rewrite env.lookup_tabulate; cbn.
        now rewrite lookup_sub_id.
    Qed.

    Lemma inst_sub_single2 {Σ : LCtx} {x σ} (xIn : x∷σ ∈ Σ)
          (t : Term (Σ - x∷σ) σ) (ι : Valuation (Σ - x∷σ)) :
      inst (sub_single xIn t) ι = env.insert xIn ι (inst t ι).
    Proof.
      rewrite env.insert_insert'.
      unfold env.insert', sub_single, inst; cbn.
      apply env.lookup_extensional.
      intros [y τ] yIn.
      rewrite env.lookup_map, ?env.lookup_tabulate.
      assert (ovs := ctx.occurs_check_var_spec xIn yIn).
      destruct (ctx.occurs_check_var xIn yIn).
      - now dependent elimination e.
      - now reflexivity.
    Qed.

    Lemma inst_lookup {Σ0 Σ1} (ι : Valuation Σ1) (ζ : Sub Σ0 Σ1) x τ (xIn : x∷τ ∈ Σ0) :
      inst (env.lookup ζ xIn) ι = env.lookup (inst (A := Valuation Σ0) ζ ι) xIn.
    Proof. cbn. now rewrite env.lookup_map. Qed.

    Lemma inst_tuple_pattern_match {N : Set} {Σ : LCtx} {σs : Ctx Ty} {Δ : NCtx N Ty}
      (ι : Valuation Σ) (p : TuplePat σs Δ) (ts : Env (Term Σ) σs) :
      inst (tuple_pattern_match_env p ts) ι =
      tuple_pattern_match_env p (inst (T := fun Σ => Env (Term Σ) σs) ts ι).
    Proof.
      unfold inst at 1; cbn.
      induction p; cbn.
      - reflexivity.
      - destruct (env.snocView ts); cbn.
        f_equal. apply IHp.
    Qed.

    Lemma inst_tuple_pattern_match_reverse {N : Set} {Σ : LCtx} {σs : Ctx Ty} {Δ : NCtx N Ty}
      (ι : Valuation Σ) (p : TuplePat σs Δ) (ts : NamedEnv (Term Σ) Δ) :
      inst (tuple_pattern_match_env_reverse p ts) ι =
      tuple_pattern_match_env_reverse p (inst (T := fun Σ => NamedEnv (Term Σ) Δ) ts ι).
    Proof.
      unfold inst at 1; cbn.
      induction p; cbn.
      - reflexivity.
      - destruct (env.snocView ts); cbn.
        f_equal. apply IHp.
    Qed.

    Lemma inst_record_pattern_match {N : Set} {Δ__R : NCtx 𝑹𝑭 Ty} {Σ : LCtx} {Δ : NCtx N Ty}
      (ι : Valuation Σ) (p : RecordPat Δ__R Δ) (ts : NamedEnv (Term Σ) Δ__R) :
      inst (T := fun Σ => NamedEnv (Term Σ) Δ) (record_pattern_match_env p ts) ι =
      record_pattern_match_env p (inst ts ι).
    Proof.
      unfold inst at 1; cbn.
      induction p; cbn.
      - reflexivity.
      - destruct (env.snocView ts); cbn.
        f_equal. apply IHp.
    Qed.

    Lemma inst_record_pattern_match_reverse {N : Set} {Δ__R : NCtx 𝑹𝑭 Ty} {Σ : LCtx} {Δ : NCtx N Ty}
      (ι : Valuation Σ) (p : RecordPat Δ__R Δ) (ts : NamedEnv (Term Σ) Δ) :
      inst (record_pattern_match_env_reverse p ts) ι =
      record_pattern_match_env_reverse p (inst (T := fun Σ => NamedEnv (Term Σ) Δ) ts ι).
    Proof.
      unfold inst at 1; cbn.
      induction p; cbn.
      - reflexivity.
      - destruct (env.snocView ts); cbn.
        f_equal. apply IHp.
    Qed.

    Lemma inst_term_tuple {Σ σs} {ι : Valuation Σ} (es : Env (Term Σ) σs) :
      @eq (EnvRec Val σs) (inst (Inst := instantiate_term)(term_tuple es) ι)
          (envrec.of_env (inst es ι)).
    Proof.
      induction σs; cbn.
      - destruct (env.nilView es); now cbn.
      - destruct (env.snocView es); cbn.
        f_equal. now eapply IHσs.
    Qed.

    Lemma inst_pattern_match_env_reverse {N : Set} {Σ : LCtx} {σ : Ty} {Δ : NCtx N Ty}
          (ι : Valuation Σ) (p : Pattern Δ σ) (ts : NamedEnv (Term Σ) Δ) :
      inst (Inst := instantiate_term) (pattern_match_env_reverse p ts) ι =
      pattern_match_env_val_reverse p (inst (T := fun Σ => NamedEnv (Term Σ) Δ) ts ι).
    Proof.
      induction p.
      - now destruct (env.snocView ts).
      - reflexivity.
      - destruct (env.snocView ts).
        now destruct (env.snocView E); cbn.
      - cbn.
        change (inst_term (term_tuple (tuple_pattern_match_env_reverse p ts)) ι) with (inst (term_tuple (tuple_pattern_match_env_reverse p ts)) ι).
        now rewrite inst_term_tuple, inst_tuple_pattern_match_reverse.
      - cbn.
        f_equal.
        eapply inst_record_pattern_match_reverse.
    Qed.

    Global Arguments inst {T A _ Σ} !_ ι.
    Global Arguments lift {T A _ Σ} !_.

  End Instantiation.

  (* Section TermEquivalence. *)

  (*   Context {Σ : LCtx} {σ : Ty}. *)

  (*   Definition TermEqv (ι : Valuation Σ) : relation (Term Σ σ) := *)
  (*     fun t1 t2 => inst_term t1 ι = inst_term t2 ι. *)

  (*   Global Instance TermEqv_Equiv {ι} : Equivalence (TermEqv ι). *)
  (*   Proof. split; congruence. Qed. *)

  (* End TermEquivalence. *)

  (* Section TermEqvB. *)

  (*   Context {Σ : LCtx}. *)

  (*   Fixpoint Term_eqvb {σ τ} (t1 : Term Σ σ) (t2 : Term Σ τ) {struct t1} : option bool := *)
  (*     match t1 , t2 with *)
  (*     | @term_var _ _ _ ς1inΣ , @term_var _ _ _ ς2inΣ => *)
  (*       if InCtx_eqb ς1inΣ ς2inΣ *)
  (*       then Some true *)
  (*       else None *)
  (*     | term_val σ v1 , term_val τ v2 => *)
  (*       match eq_dec σ τ with *)
  (*       | left  p => Some (Val_eqb τ (eq_rect σ Val v1 τ p) v2) *)
  (*       | right _ => Some false *)
  (*       end *)
  (*     | term_neg x   , term_neg y   => Term_eqvb x y *)
  (*     | term_not x   , term_not y   => Term_eqvb x y *)
  (*     | term_inl x   , term_inl y   => Term_eqvb x y *)
  (*     | term_inl _   , term_inr _   => Some false *)
  (*     | term_inr _   , term_inl _   => Some false *)
  (*     | term_inr x   , term_inr y   => Term_eqvb x y *)
  (*     | _            , _            => None *)
  (*     end. *)

  (*   Local Set Equations With UIP. *)
  (*   Lemma Term_eqvb_spec {σ} (t1 t2 : Term Σ σ) : *)
  (*     OptionSpec *)
  (*       (fun b : bool => forall ι : Valuation Σ, TermEqv ι t1 t2 <-> is_true b) *)
  (*       True *)
  (*       (Term_eqvb t1 t2). *)
  (*   Proof. *)
  (*     induction t1; dependent elimination t2; cbn; intros; try (solve [ constructor; auto ]). *)
  (*     - destruct (InCtx_eqb_spec ςInΣ ςInΣ0); constructor; auto. *)
  (*       dependent elimination e. *)
  (*       intros ι. apply reflect_iff. constructor. reflexivity. *)
  (*     - rewrite eq_dec_refl. cbn. constructor. *)
  (*       intros ι. apply reflect_iff, Val_eqb_spec. *)
  (*     - specialize (IHt1 e). revert IHt1. *)
  (*       apply optionspec_monotonic; auto. *)
  (*       intros ? H ι. specialize (H ι). rewrite <- H. *)
  (*       unfold TermEqv; cbn; lia. *)
  (*     - specialize (IHt1 e0). revert IHt1. *)
  (*       apply optionspec_monotonic; auto. *)
  (*       intros ? H ι. specialize (H ι). rewrite <- H. *)
  (*       unfold TermEqv; cbn. split. *)
  (*       + now intros ?%ssrbool.negb_inj. *)
  (*       + congruence. *)
  (*     - specialize (IHt1 t). revert IHt1. *)
  (*       apply optionspec_monotonic; auto. *)
  (*       intros ? H ι. specialize (H ι). rewrite <- H. *)
  (*       unfold TermEqv; cbn. split; congruence. *)
  (*     - constructor. intros ?. apply reflect_iff. constructor. discriminate. *)
  (*     - constructor. intros ?. apply reflect_iff. constructor. discriminate. *)
  (*     - specialize (IHt1 t0). revert IHt1. *)
  (*       apply optionspec_monotonic; auto. *)
  (*       intros ? H ι. specialize (H ι). rewrite <- H. *)
  (*       unfold TermEqv; cbn. split; congruence. *)
  (*   Qed. *)

  (* End TermEqvB. *)

  Section Utils.

    Definition term_get_val {Σ σ} (t : Term Σ σ) : option (Val σ) :=
      match t with
      | term_val _ v => Some v
      | _            => None
      end.

    Lemma term_get_val_spec {Σ σ} (s : Term Σ σ) :
      OptionSpec
        (fun v => forall ι : Valuation Σ, inst s ι = v)
        True
        (term_get_val s).
    Proof.
      dependent elimination s; cbn; try constructor; auto.
    Qed
.
    Equations(noeqns) term_get_pair {Σ σ1 σ2} (t : Term Σ (ty_prod σ1 σ2)) :
      option (Term Σ σ1 * Term Σ σ2) :=
      term_get_pair (term_val _ (v1,v2))          := Some (term_val _ v1, term_val _ v2);
      term_get_pair (term_binop binop_pair t1 t2) := Some (t1, t2);
      term_get_pair _ := None.

    Lemma term_get_pair_spec {Σ σ1 σ2} (s : Term Σ (ty_prod σ1 σ2)) :
      OptionSpec
        (fun '(t1,t2) =>
           forall ι : Valuation Σ,
             inst (T := fun Σ => Term Σ (ty_prod σ1 σ2)) (A := Val σ1 * Val σ2) s ι =
             (inst (A := Val σ1) t1 ι, inst (A := Val σ2) t2 ι))
        True
        (term_get_pair s).
    Proof.
      dependent elimination s; cbn; try constructor; auto.
      - destruct v; constructor; auto.
      - dependent elimination op. constructor. reflexivity.
    Qed.

    Equations(noeqns) term_get_sum {Σ σ1 σ2} (t : Term Σ (ty_sum σ1 σ2)) :
      option (Term Σ σ1 + Term Σ σ2) :=
      term_get_sum (term_val _ (inl v)) := Some (inl (term_val _ v));
      term_get_sum (term_val _ (inr v)) := Some (inr (term_val _ v));
      term_get_sum (term_inl t)         := Some (inl t);
      term_get_sum (term_inr t)         := Some (inr t);
      term_get_sum _ := None.

    Lemma term_get_sum_spec {Σ σ1 σ2} (s : Term Σ (ty_sum σ1 σ2)) :
      OptionSpec
        (fun s' => match s' with
                   | inl t => forall ι : Valuation Σ,
                       inst (T := fun Σ => Term Σ (ty_sum σ1 σ2)) (A := Val σ1 + Val σ2) s ι =
                       @inl (Val σ1) (Val σ2) (inst t ι)
                   | inr t => forall ι : Valuation Σ,
                       inst (T := fun Σ => Term Σ (ty_sum σ1 σ2)) (A := Val σ1 + Val σ2) s ι =
                       @inr (Val σ1) (Val σ2) (inst t ι)
                   end)
        True
        (term_get_sum s).
    Proof.
      dependent elimination s; cbn; try constructor; auto.
      destruct v; constructor; auto.
    Qed.

    Equations(noeqns) term_get_union {Σ U} (t : Term Σ (ty_union U)) :
      option { K : 𝑼𝑲 U & Term Σ (𝑼𝑲_Ty K) } :=
      term_get_union (term_val _ v)   :=
        Some (let (K, p) := 𝑼_unfold v in existT K (term_val _ p));
      term_get_union (term_union K t) := Some (existT K t);
      term_get_union _ := None.

    Lemma term_get_union_spec {Σ U} (s : Term Σ (ty_union U)) :
      OptionSpec
        (fun x : {K : 𝑼𝑲 U & Term Σ (𝑼𝑲_Ty K)} =>
           match x with
           | existT K t =>
             forall ι : Valuation Σ,
               inst (T := fun Σ => Term Σ (ty_union U)) (A := 𝑼𝑻 U) s ι =
               𝑼_fold (@existT (𝑼𝑲 U) (fun K => Val (𝑼𝑲_Ty K)) K (inst t ι)) :> Val (ty_union U)
           end)
        True
        (term_get_union s).
    Proof.
      dependent elimination s; cbn; try constructor; auto.
      destruct (𝑼_unfold v) eqn:?. intros. cbn.
      now rewrite <- Heqs, 𝑼_fold_unfold.
    Qed.

    Equations(noeqns) term_get_record {R Σ} (t : Term Σ (ty_record R)) :
      option (NamedEnv (Term Σ) (𝑹𝑭_Ty R)) :=
      term_get_record (term_val _ v)        := Some (lift (𝑹_unfold v));
      term_get_record (@term_record _ R ts) := Some ts;
      term_get_record _ := None.

    Lemma term_get_record_spec {Σ R} (s : Term Σ (ty_record R)) :
      OptionSpec
        (fun ts =>
           forall ι : Valuation Σ,
             inst (T := fun Σ => Term Σ (ty_record R)) (A := 𝑹𝑻 R) s ι =
             𝑹_fold (inst (T := fun Σ => NamedEnv (fun τ => Term Σ τ) (𝑹𝑭_Ty R)) (A := NamedEnv Val (𝑹𝑭_Ty R)) ts ι))
        True
        (term_get_record s).
    Proof.
      dependent elimination s; try constructor; auto.
      intros ι. now rewrite inst_lift, 𝑹_fold_unfold.
    Qed.

    Equations(noeqns) term_get_tuple {σs Σ} (t : Term Σ (ty_tuple σs)) :
      option (Env (Term Σ) σs) :=
      (* term_get_tuple (term_val _ v)       := Some _; *)
      (* term_get_tuple (@term_tuple _ _ ts) := Some ts; *)
      term_get_tuple _ := None.

    Lemma term_get_tuple_spec {Σ σs} (s : Term Σ (ty_tuple σs)) :
      OptionSpec
        (fun ts =>
           forall ι : Valuation Σ,
             inst (T := fun Σ => Term Σ (ty_tuple σs)) (A := Val (ty_tuple σs)) s ι =
             inst (term_tuple ts) ι)
        True
        (term_get_tuple s).
    Proof.
      now constructor.
    Qed.

  End Utils.

  Section SymbolicPair.

    Definition Pair (A B : LCtx -> Type) (Σ : LCtx) : Type :=
      A Σ * B Σ.
    Global Instance SubstPair {A B} `{Subst A, Subst B} : Subst (Pair A B) :=
      fun _ '(a,b) _ ζ => (subst a ζ, subst b ζ).

    Global Instance SubstLawsPair {A B} `{SubstLaws A, SubstLaws B} : SubstLaws (Pair A B).
    Proof.
      constructor.
      { intros ? [t1 t2]; cbn.
        f_equal; apply subst_sub_id.
      }
      { intros ? ? ? ? ? [t1 t2]; cbn.
        f_equal; apply subst_sub_comp.
      }
    Qed.

    Global Instance InstPair {AT BT A B} `{Inst AT A, Inst BT B} :
      Inst (Pair AT BT) (A * B) :=
      {| inst Σ '(a , b) ι := (inst a ι, inst b ι);
         lift Σ '(a, b)    := (lift a , lift b);
      |}.

    Global Instance InstLawsPair {AT BT A B} `{InstLaws AT A, InstLaws BT B} :
      InstLaws (Pair AT BT) (A * B).
    Proof.
      constructor.
      { intros ? ? []; cbn; f_equal; apply inst_lift. }
      { intros ? ? ? ? []; cbn; f_equal; apply inst_subst. }
    Qed.

    Global Instance OccursCheckPair {AT BT} `{OccursCheck AT, OccursCheck BT} :
      OccursCheck (Pair AT BT) :=
      fun _ _ xIn '(a,b) =>
        match occurs_check xIn a, occurs_check xIn b with
        | Some a' , Some b' => Some (a', b')
        | _       , _       => None
        end.

    Global Instance OccursCheckLawsPair {AT BT} `{OccursCheckLaws AT, OccursCheckLaws BT} :
      OccursCheckLaws (Pair AT BT).
    Proof.
      constructor.
      - intros. destruct t as [a b]; cbn.
        now rewrite ?occurs_check_shift.
      - intros ? ? ? [a b] [a' b']; cbn.
        destruct (occurs_check xIn a) eqn:Heq1; intros; try discriminate.
        destruct (occurs_check xIn b) eqn:Heq2; intros; try discriminate.
        apply occurs_check_sound in Heq1.
        apply occurs_check_sound in Heq2.
        congruence.
    Qed.

  End SymbolicPair.

  Section SymbolicOption.

    Definition Option (A : LCtx -> Type) (Σ : LCtx) : Type :=
      option (A Σ).
    Global Instance SubstOption {A} `{Subst A} : Subst (Option A) :=
      fun _ ma _ ζ => option_map (fun a => subst a ζ) ma.

    Global Instance SubstLawsOption {A} `{SubstLaws A} : SubstLaws (Option A).
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

    Global Instance InstOption {AT A} `{Inst AT A} :
      Inst (Option AT) (option A) :=
      {| inst Σ ma ι := option_map (fun a => inst a ι) ma;
         lift Σ ma   := option_map lift ma;
      |}.

    Global Instance InstLawsOption {AT A} `{InstLaws AT A} :
      InstLaws (Option AT) (option A).
    Proof.
      constructor.
      { intros ? ? []; cbn; f_equal; apply inst_lift. }
      { intros ? ? ? ? []; cbn; f_equal; apply inst_subst. }
    Qed.

    Global Instance OccursCheckOption {AT} `{OccursCheck AT} :
      OccursCheck (Option AT) :=
      fun _ _ xIn ma =>
        match ma with
        | Some a => option_map Some (occurs_check xIn a)
        | None   => Some None
        end.

    Global Instance OccursCheckLawsOption {AT} `{OccursCheckLaws AT} :
      OccursCheckLaws (Option AT).
    Proof.
      constructor.
      { intros. destruct t as [a|]; cbn.
        - now rewrite ?occurs_check_shift.
        - reflexivity.
      }
      { intros ? ? ? [a|] mt' Heq; cbn.
        - apply option_map_eq_some' in Heq. destruct Heq as [t' [Heq <-]].
          apply occurs_check_sound in Heq. subst. reflexivity.
        - apply noConfusion_inv in Heq. cbn in Heq. subst. reflexivity.
      }
    Qed.

  End SymbolicOption.

  Section SymbolicUnit.

    Definition Unit : LCtx -> Type := fun _ => unit.
    Global Instance SubstUnit : Subst Unit :=
      fun _ t _ _ => t.
    Global Instance SubstLawsUnit : SubstLaws Unit.
    Proof. constructor; reflexivity. Qed.
    Global Instance InstUnit : Inst Unit unit :=
      @Build_Inst Unit unit (fun _ x ι => x) (fun _ x => x).
    Global Instance InstLawsUnit : InstLaws Unit unit.
    Proof. constructor; reflexivity. Qed.
    Global Instance OccursCheckUnit : OccursCheck Unit :=
      fun _ _ _ _ => Some tt.
    Global Instance OccursCheckLawsUnit : OccursCheckLaws Unit.
    Proof.
      constructor; cbn.
      - destruct t; reflexivity.
      - destruct t, t'; reflexivity.
    Qed.

  End SymbolicUnit.

  Section SymbolicStore.

    Definition SStore (Γ : PCtx) (Σ : LCtx) : Type :=
      NamedEnv (Term Σ) Γ.

    Global Instance subst_localstore {Γ} : Subst (SStore Γ) :=
      SubstEnv.
    Global Instance substlaws_localstore {Γ} : SubstLaws (SStore Γ) :=
      SubstLawsEnv.
    Global Program Instance inst_localstore {Γ} : Inst (SStore Γ) (CStore Γ) :=
      instantiate_env.

    Global Instance instlaws_localstore {Γ} : InstLaws (SStore Γ) (CStore Γ).
    Proof. apply instantiatelaws_env. Qed.

    Lemma subst_lookup {Γ Σ Σ' x σ} (xInΓ : x∷σ ∈ Γ) (ζ : Sub Σ Σ') (δ : SStore Γ Σ) :
      (subst (δ ‼ x)%exp ζ = (subst δ ζ ‼ x)%exp).
    Proof.
      unfold subst at 2, subst_localstore, SubstEnv.
      now rewrite env.lookup_map.
    Qed.

  End SymbolicStore.
  Bind Scope env_scope with SStore.

  Section PartialEvaluation.

    Equations(noeqns) peval_append {Σ σ} (t1 t2 : Term Σ (ty_list σ)) : Term Σ (ty_list σ) :=
    | term_val _ v1                 | term_val _ v2 := term_val (ty_list σ) (app v1 v2);
    (* TODO: recurse over the value instead *)
    | term_val _ nil                | t2 := t2;
    | term_val _ (cons v vs)        | t2 := term_binop binop_cons (term_val σ v) (term_binop binop_append (term_val (ty_list σ) vs) t2);
    | term_binop binop_cons t11 t12 | t2 := term_binop binop_cons t11 (term_binop binop_append t12 t2);
    | t1                            | t2 := term_binop binop_append t1 t2.

    Equations(noeqns) peval_binop' {Σ σ1 σ2 σ} (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) : Term Σ σ :=
    | op | term_val _ v1 | term_val _ v2 := term_val σ (eval_binop op v1 v2);
    | op | t1            | t2            := term_binop op t1 t2.

    Equations(noeqns) peval_binop {Σ σ1 σ2 σ} (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) : Term Σ σ :=
    | binop_append | t1 | t2 := peval_append t1 t2;
    | op           | t1 | t2 := peval_binop' op t1 t2.

    Lemma peval_append_sound {Σ σ} (t1 t2 : Term Σ (ty_list σ)) :
      forall (ι : Valuation Σ),
        inst  (peval_append t1 t2) ι =
          eval_binop binop_append (inst t1 ι) (inst t2 ι).
    Proof.
      intros ι.
      dependent elimination t1; cbn; auto.
      - dependent elimination t2; cbn; auto;
        destruct v; cbn; auto.
      - dependent elimination op; cbn; auto.
    Qed.

    Lemma peval_binop'_sound {Σ σ1 σ2 σ} (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) :
      forall (ι : Valuation Σ),
        inst (peval_binop' op t1 t2) ι = eval_binop op (inst t1 ι) (inst t2 ι).
    Proof. intros ι. destruct t1, t2; cbn; auto. Qed.

    Lemma peval_binop_sound {Σ σ1 σ2 σ} (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) :
      forall (ι : Valuation Σ),
        inst (peval_binop op t1 t2) ι = eval_binop op (inst t1 ι) (inst t2 ι).
    Proof.
      intros ι.
      destruct op; cbn [peval_binop];
        auto using peval_binop'_sound, peval_append_sound.
    Qed.

    Equations(noeqns) peval_neg {Σ} (t : Term Σ ty_int) : Term Σ ty_int :=
    | term_val _ v := term_val ty_int (Z.opp v);
    | t            := term_neg t.

    Equations(noeqns) peval_not {Σ} (t : Term Σ ty_bool) : Term Σ ty_bool :=
    | term_val _ v := term_val ty_bool (negb v);
    | t            := term_not t.

    Equations(noeqns) peval_inl {Σ σ1 σ2} (t : Term Σ σ1) : Term Σ (ty_sum σ1 σ2) :=
    | term_val _ v := term_val (ty_sum _ _) (@inl (Val _) (Val _) v);
    | t            := term_inl t.

    Equations(noeqns) peval_inr {Σ σ1 σ2} (t : Term Σ σ2) : Term Σ (ty_sum σ1 σ2) :=
    | term_val _ v := term_val (ty_sum _ _) (@inr (Val _) (Val _) v);
    | t            := term_inr t.

    Equations(noeqns) peval {Σ σ} (t : Term Σ σ) : Term Σ σ :=
    | term_var ς                 := term_var ς;
    | term_val _ v               := term_val _ v;
    | term_binop op t1 t2        := peval_binop op (peval t1) (peval t2);
    | term_neg t                 := peval_neg (peval t);
    | term_not t                 := peval_not (peval t);
    | term_inl t                 := peval_inl (peval t);
    | term_inr t                 := peval_inr (peval t);
    (* TODO: Finish the cases below. *)
    | @term_projtup _ _ t n _ p  := @term_projtup _ _ (peval t) n _ p;
    | @term_union _ U K t        := @term_union _ U K (peval t);
    | @term_record _ R ts        := @term_record _ R ts.

    Lemma peval_neg_sound {Σ} (t : Term Σ ty_int) :
      forall (ι : Valuation Σ),
        inst (peval_neg t) ι = inst (term_neg t) ι.
    Proof. dependent elimination t; cbn; auto. Qed.

    Lemma peval_not_sound {Σ} (t : Term Σ ty_bool) :
      forall (ι : Valuation Σ),
        inst (peval_not t) ι = inst (term_not t) ι.
    Proof. dependent elimination t; cbn; auto. Qed.

    Lemma peval_inl_sound {Σ σ1 σ2} (t : Term Σ σ1) :
      forall (ι : Valuation Σ),
        inst (peval_inl (σ2 := σ2) t) ι = inst (term_inl t) ι.
    Proof. destruct t; cbn; auto. Qed.

    Lemma peval_inr_sound {Σ σ1 σ2} (t : Term Σ σ2) :
      forall (ι : Valuation Σ),
        inst (peval_inr (σ1 := σ1) t) ι = inst (term_inr t) ι.
    Proof. destruct t; cbn; auto. Qed.

    Lemma peval_sound {Σ σ} (t : Term Σ σ) :
      forall (ι : Valuation Σ),
        inst (peval t) ι = inst t ι.
    Proof.
      intros ι. symmetry.
      induction t; cbn;
        change (inst_term ?t ?ι) with (inst t ι).
      - reflexivity.
      - reflexivity.
      - now rewrite peval_binop_sound, IHt1, IHt2.
      - now rewrite peval_neg_sound, IHt.
      - now rewrite peval_not_sound, IHt.
      - change (Val σ1 + Val σ2)%type with (Val (ty_sum σ1 σ2)).
        now rewrite peval_inl_sound, IHt.
      - change (Val σ1 + Val σ2)%type with (Val (ty_sum σ1 σ2)).
        now rewrite peval_inr_sound, IHt.
      - now rewrite IHt.
      - now rewrite IHt.
      - reflexivity.
    Qed.

  End PartialEvaluation.

  Definition seval_exp {Γ Σ} (δ : SStore Γ Σ) :
    forall {σ} (e : Exp Γ σ), Term Σ σ :=
    fix seval_exp {σ} (e : Exp Γ σ) : Term Σ σ :=
      match e with
      | exp_var ς                => δ ‼ ς
      | exp_val σ v              => term_val σ v
      | exp_binop op e1 e2       => term_binop op (seval_exp e1) (seval_exp e2)
      | exp_neg e                => term_neg (seval_exp e)
      | exp_not e                => term_not (seval_exp e)
      | exp_inl e                => term_inl (seval_exp e)
      | exp_inr e                => term_inr (seval_exp e)
      | exp_list es              => term_list (List.map seval_exp es)
      | exp_bvec es              => term_bvec (Vector.map seval_exp es)
      | exp_tuple es             => term_tuple (env.map (@seval_exp) es)
      | @exp_projtup _ _ e n _ p => term_projtup (seval_exp e) n (p := p)
      | exp_union E K e          => term_union E K (seval_exp e)
      | exp_record R es          => term_record R (env.map (fun _ => seval_exp) es)
      (* | exp_projrec e rf         => term_projrec (seval_exp e) rf *)
      end%exp.

  Lemma eval_exp_inst {Γ Σ τ} (ι : Valuation Σ) (δΓΣ : SStore Γ Σ) (e : Exp Γ τ) :
    eval e (inst δΓΣ ι) = inst (seval_exp δΓΣ e) ι.
  Proof.
    induction e; cbn; repeat f_equal; auto.
    { unfold inst; cbn. now rewrite env.lookup_map. }
    2: {
      induction es as [|eb n es IHes]; cbn in *.
      { reflexivity. }
      { destruct X as [-> Heqs].
        change (inst_term ?ι ?t) with (inst ι t).
        destruct (inst (seval_exp δΓΣ eb) ι);
          cbn; f_equal; auto.
      }
    }
    all: induction es; cbn in *; destruct_conjs; f_equal; auto.
  Qed.

  Lemma subst_seval {Γ τ Σ Σ'} (e : Exp Γ τ) (ζ : Sub Σ Σ') (δ : SStore Γ Σ) :
    subst (T := fun Σ => Term Σ _) (seval_exp δ e) ζ = seval_exp (subst δ ζ) e.
  Proof.
    induction e; cbn; f_equal; auto.
    { now rewrite (subst_lookup xInΓ). }
    all: induction es; cbn in *; destruct_conjs; f_equal; auto.
  Qed.

  Section Contracts.

    Definition Pred (A : Type) : Type := A -> Prop.

    Definition Final {Γ σ} (s : Stm Γ σ) : Prop :=
      match s with
      | stm_val _ _   => True
      | stm_fail _ _ => True
      | _ => False
      end.

    Definition ResultOrFail {Γ σ} (s : Stm Γ σ) :
      forall (POST : Val σ -> Prop), Prop :=
      match s with
      | stm_val _ v => fun POST => POST v
      | stm_fail _ _ => fun _ => True
      | _ => fun _ => False
      end.

    Lemma result_or_fail_inversion {Γ σ} (s : Stm Γ σ) (POST : Val σ -> Prop) :
      ResultOrFail s POST -> (exists msg, s = stm_fail _ msg)
                          \/ (exists v, s = stm_val _ v /\ POST v).
    Proof. destruct s; cbn in *; try contradiction; eauto. Qed.

    (* This predicate encodes that the statement s is a finished computation and
       that the result is not a failure. This is a computational version that is
       better suited for the goal and the inversion below is better suited for
       a hypothesis. *)
    Definition ResultNoFail {Γ σ} (s : Stm Γ σ) :
      forall (POST : Val σ -> Prop), Prop :=
      match s with
      | stm_val _ v => fun POST => POST v
      | _ => fun _ => False
      end.

    Lemma result_no_fail_inversion {Γ σ} (s : Stm Γ σ) (POST : Val σ -> Prop) :
      ResultNoFail s POST -> exists v, s = stm_val _ v /\ POST v.
    Proof. destruct s; cbn in *; try contradiction; eauto. Qed.

  End Contracts.

  Section GenericRegStore.

    Definition GenericRegStore : Type := forall σ, 𝑹𝑬𝑮 σ -> Val σ.

    Definition generic_write_register (γ : GenericRegStore) {σ} (r : 𝑹𝑬𝑮 σ)
      (v : Val σ) : GenericRegStore :=
      fun τ r' =>
        match eq_dec_het r r' with
        | left eqt => eq_rect σ Val v τ (f_equal projT1 eqt)
        | right _ => γ τ r'
        end.

    Definition generic_read_register (γ : GenericRegStore) {σ} (r : 𝑹𝑬𝑮 σ) :
      Val σ := γ _ r.

    Lemma generic_read_write γ {σ} (r : 𝑹𝑬𝑮 σ) (v : Val σ) :
      generic_read_register (generic_write_register γ r v) r = v.
    Proof.
      unfold generic_read_register, generic_write_register.
      unfold eq_dec_het. now rewrite eq_dec_refl.
    Qed.

    Lemma generic_read_write_distinct γ {σ τ} (r : 𝑹𝑬𝑮 σ) (k : 𝑹𝑬𝑮 τ) (v : Val σ):
      existT _ r <> existT _ k ->
      generic_read_register (generic_write_register γ r v) k = generic_read_register γ k.
    Proof.
      intros ?; unfold generic_read_register, generic_write_register.
      destruct (eq_dec_het r k).
      - congruence.
      - reflexivity.
    Qed.

    Lemma generic_write_read γ {σ} (r : 𝑹𝑬𝑮 σ) :
      forall τ (r' : 𝑹𝑬𝑮 τ),
        generic_write_register γ r (generic_read_register γ r) r' = γ τ r'.
    Proof.
      intros ? ?.
      unfold generic_write_register, generic_read_register.
      destruct (eq_dec_het r r') as [e|].
      - now dependent elimination e.
      - reflexivity.
    Qed.

    Lemma generic_write_write γ {σ} (r : 𝑹𝑬𝑮 σ) (v1 v2 : Val σ) :
      forall τ (r' : 𝑹𝑬𝑮 τ),
        generic_write_register (generic_write_register γ r v1) r v2 r' =
        generic_write_register γ r v2 r'.
    Proof.
      intros ? ?.
      unfold generic_write_register, generic_read_register.
      destruct (eq_dec_het r r'); reflexivity.
    Qed.

  End GenericRegStore.

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

  Notation "[ x , .. , z ]" :=
    (tuplepat_snoc .. (tuplepat_snoc tuplepat_nil x) .. z) (at level 0) : pat_scope.
  Notation "[ x , .. , z ]" :=
    (env.snoc .. (env.snoc env.nil (_∷_) x) .. (_∷_) z) (at level 0, only parsing) : arg_scope.

  Notation "'if:' e 'then' s1 'else' s2" := (stm_if e%exp s1%exp s2%exp)
    (at level 99, right associativity, format
     "'[hv' 'if:'  e  '/' '[' 'then'  s1  ']' '/' '[' 'else'  s2 ']' ']'"
    ) : exp_scope.

  Notation "'let:' x := s1 'in' s2" := (stm_let x%string _ s1%exp s2%exp)
    (at level 100, right associativity, x at level 30, s1 at next level, format
     "'let:'  x  :=  s1  'in'  '/' s2"
    ) : exp_scope.
  Notation "'let:' x ∷ τ := s1 'in' s2" := (stm_let x%string τ s1%exp s2%exp)
    (at level 100, right associativity, x at level 30, τ at next level, s1 at next level,
     format "'let:'  x  ∷  τ  :=  s1  'in'  '/' s2"
    ) : exp_scope.
  Notation "'let:' x :: τ := s1 'in' s2" := (stm_let x%string τ s1%exp s2%exp)
    (at level 100, right associativity, x at level 30, τ at next level, s1 at next level,
    (* format "'let:'  x  ::  τ  :=  s1  'in'  '/' s2", *) only parsing
    ) : exp_scope.
  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1%exp => rhs1%exp
                                  end))
    (at level 100, alt1 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' 'end' ']'"
    ) : exp_scope.
  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1%exp => rhs1%exp
                                  | alt2%exp => rhs2%exp
                                  end))
    (at level 100, alt1 pattern, alt2 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' 'end' ']'"
    ) : exp_scope.
  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1 => rhs1%exp
                                  | alt2 => rhs2%exp
                                  | alt3 => rhs3%exp
                                  end))
    (at level 100, alt1 pattern, alt2 pattern, alt3 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' 'end' ']'"
    ) : exp_scope.
  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1 => rhs1%exp
                                  | alt2 => rhs2%exp
                                  | alt3 => rhs3%exp
                                  | alt4 => rhs4%exp
                                  end))
    (at level 100, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' |  alt4  =>  rhs4  '/' 'end' ']'"
    ) : exp_scope.
  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 | alt5 => rhs5 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1 => rhs1%exp
                                  | alt2 => rhs2%exp
                                  | alt3 => rhs3%exp
                                  | alt4 => rhs4%exp
                                  | alt5 => rhs5%exp
                                  end))
    (at level 100, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, alt5 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' |  alt4  =>  rhs4  '/' |  alt5  =>  rhs5  '/' 'end' ']'"
    ) : exp_scope.
  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 | alt5 => rhs5 | alt6 => rhs6 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1 => rhs1%exp
                                  | alt2 => rhs2%exp
                                  | alt3 => rhs3%exp
                                  | alt4 => rhs4%exp
                                  | alt5 => rhs5%exp
                                  | alt6 => rhs6%exp
                                  end))
    (at level 100, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, alt5 pattern, alt6 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' |  alt4  =>  rhs4  '/' |  alt5  =>  rhs5  '/' |  alt6  =>  rhs6  '/' 'end' ']'"
    ) : exp_scope.

  (* Notation "'match:' e 'in' U 'with' | alt1 x1 => rhs1 | alt2 x2 => rhs2 'end'" := *)
  (*   (@stm_match_union _ U e _ *)
  (*     (fun K => match K with *)
  (*               | alt1%exp => x1 *)
  (*               | alt2%exp => x2 *)
  (*               end) *)
  (*     (fun K => match K return Stm _ _ with *)
  (*               | alt1%exp => rhs1%exp *)
  (*               | alt2%exp => rhs2%exp *)
  (*               end) *)
  (*   ) *)
  (*   (at level 100, alt1 pattern, alt2 pattern, format *)
  (*    "'[hv' 'match:'  e  'in'  U  'with'  '/' |  alt1  x1  =>  rhs1  '/' |  alt2  x2  =>  rhs2  '/' 'end' ']'" *)
  (*     ) : exp_scope. *)

  Notation "'match:' e 'with' | 'inl' p1 => rhs1 | 'inr' p2 => rhs2 'end'" :=
    (stm_match_sum e p1%string rhs1 p2%string rhs2) (at level 100, only parsing) : exp_scope.

  Notation "'match:' e 'in' '(' σ1 ',' σ2 ')' 'with' | '(' fst ',' snd ')' => rhs 'end'" :=
    (@stm_match_prod _ _ σ1 σ2 e fst%string snd%string rhs)
    (at level 100, fst pattern, snd pattern, format
     "'[hv' 'match:' e 'in' '(' σ1 ',' σ2 ')' 'with' '/' | '(' fst ',' snd ')' => rhs '/' 'end' ']'"
    ) : exp_scope.

  Notation "'call' f a1 .. an" :=
    (stm_call f (env.snoc .. (env.snoc env.nil (_∷_) a1%exp) .. (_∷_) an%exp))
    (at level 10, f global, a1, an at level 9) : exp_scope.
  Notation "'foreign' f a1 .. an" :=
    (stm_foreign f (env.snoc .. (env.snoc env.nil (_∷_) a1%exp) .. (_∷_) an%exp))
    (at level 10, f global, a1, an at level 9) : exp_scope.

  Notation "'call' f" :=
    (stm_call f env.nil)
    (at level 10, f global) : exp_scope.
  Notation "'foreign' f" :=
    (stm_foreign f env.nil)
    (at level 10, f global) : exp_scope.

  Notation "s1 ;; s2" := (stm_seq s1 s2) : exp_scope.
  Notation "x <- s" := (stm_assign x s)
    (at level 80, s at next level) : exp_scope.
  Notation "'fail' s" := (stm_fail _ s)
    (at level 10, no associativity) : exp_scope.

  Section Commands.

    Inductive Command (A : Type) : Type :=
    | cmd_return (a : A)
    | cmd_fail
    | cmd_read_register {τ} (reg : 𝑹𝑬𝑮 τ) (c : Val τ -> Command A)
    | cmd_write_register {τ} (reg : 𝑹𝑬𝑮 τ) (v : Val τ) (c : Command A)
    | cmd_call          {Δ τ} (f : 𝑭 Δ τ) (vs : CStore Δ) (c : Val τ -> Command A)
    | cmd_foreign       {Δ τ} (f : 𝑭𝑿 Δ τ) (vs : CStore Δ) (c : Val τ -> Command A).
    Global Arguments cmd_fail {A}.

    Fixpoint cmd_bind {A B} (m : Command A) (g : A -> Command B) {struct m} : Command B :=
      match m with
      | cmd_return a => g a
      | cmd_fail     => cmd_fail
      | cmd_read_register reg k => cmd_read_register reg (fun v => cmd_bind (k v) g)
      | cmd_write_register reg v c => cmd_write_register reg v (cmd_bind c g)
      | cmd_call f vs k => cmd_call f vs (fun v => cmd_bind (k v) g)
      | cmd_foreign f vs k => cmd_foreign f vs (fun v => cmd_bind (k v) g)
      end.

    Definition cmd_map {A B} (f : A -> B) (ma : Command A) : Command B :=
      cmd_bind ma (fun v => cmd_return (f v)).

  End Commands.

End Terms.

(******************************************************************************)

Module Type ProgramKit (termkit : TermKit).

  Module Export TM := Terms termkit.

  (* We choose to make [RegStore] a parameter so the users of the module would be able to
     instantiate it with their own data structure and [read_regsiter]/[write_register]
     functions *)
  Parameter RegStore : Type.
  (* Definition RegStore : Type := forall σ, 𝑹𝑬𝑮 σ -> Val σ. *)
  Parameter read_register : forall (γ : RegStore) {σ} (r : 𝑹𝑬𝑮 σ), Val σ.
  Parameter write_register : forall (γ : RegStore) {σ} (r : 𝑹𝑬𝑮 σ) (v : Val σ), RegStore.

  Parameter read_write : forall (γ : RegStore) σ (r : 𝑹𝑬𝑮 σ) (v : Val σ),
            read_register (write_register γ r v) r = v.

  Parameter read_write_distinct :
    forall (γ : RegStore) {σ τ} (r__σ : 𝑹𝑬𝑮 σ) (r__τ : 𝑹𝑬𝑮 τ) (v__σ : Val σ),
      existT _ r__σ <> existT _ r__τ ->
      read_register (write_register γ r__σ v__σ) r__τ = read_register γ r__τ.

  (* Parameter write_read : *)
  (*   forall (γ : RegStore) {σ τ} (r__σ : 𝑹𝑬𝑮 σ) (r__τ : 𝑹𝑬𝑮 τ), *)
  (*     read_register (write_register γ r (read_register γ r)) r__τ = *)
  (*     read_register γ r__τ. *)

  (* Parameter write_write : forall (γ : RegStore) σ (r : 𝑹𝑬𝑮 σ) (v1 v2 : Val σ), *)
  (*     write_register (write_register γ r v1) r v2 = write_register γ r v2. *)

  (* Memory model *)
  Parameter Memory : Type.
  (* Step relation for calling an external function. The complete function call
     is done in one step. The result of an external call is either a failure
     with an error message msg (res = inl msg) or a successful computation with
     a result value v (res = inr v).
   *)
  Parameter ForeignCall :
    forall
      {Δ σ} (f : 𝑭𝑿 Δ σ)
      (args : CStore Δ)
      (res  : string + Val σ)
      (γ γ' : RegStore)
      (μ μ' : Memory), Prop.
  Parameter ForeignProgress :
    forall {Δ σ} (f : 𝑭𝑿 Δ σ) (args : CStore Δ) γ μ,
    exists γ' μ' res, ForeignCall f args res γ γ' μ μ'.

  (* Bind Scope env_scope with Memory. *)
  (* Parameter read_memory : forall (μ : Memory) (addr : 𝑨𝑫𝑫𝑹), Val ty_int. *)
  (* Parameter write_memory : forall (μ : Memory) (addr : 𝑨𝑫𝑫𝑹) (v : Val ty_int), Memory. *)

  (* Parameter Inline Pi : forall {Δ τ} (f : 𝑭 Δ τ), FunDef Δ τ. *)
  Parameter Inline Pi : forall {Δ τ} (f : 𝑭 Δ τ), Stm Δ τ.

End ProgramKit.
