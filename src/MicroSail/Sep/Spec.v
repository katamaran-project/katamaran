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
     Logic.EqdepFacts
     Program.Equality
     Program.Tactics
     Strings.String
     ZArith.ZArith.

From MicroSail Require Import
     Syntax.

Set Implicit Arguments.

Module Symbolic
  (Import typekit : TypeKit)
  (Import termkit : TermKit typekit)
  (Import progKit : ProgramKit typekit termkit).

  Parameter Inline 𝑺 : Set. (* input: \MIS *)

  (* Predicate names. *)
  Parameter Inline 𝑷  : Set.
  (* Predicate field types. *)
  Parameter Inline 𝑷_Ty : 𝑷 -> Ctx Ty.

  Import CtxNotations.
  Import EnvNotations.

  Inductive Term (Σ : Ctx (𝑺 * Ty)) : Ty -> Type :=
  | term_var     (ς : 𝑺) (σ : Ty) {ςInΣ : InCtx (ς , σ) Σ} : Term Σ σ
  | term_lit     (σ : Ty) : Lit σ -> Term Σ σ
  | term_plus    (e1 e2 : Term Σ ty_int) : Term Σ ty_int
  | term_times   (e1 e2 : Term Σ ty_int) : Term Σ ty_int
  | term_minus   (e1 e2 : Term Σ ty_int) : Term Σ ty_int
  | term_neg     (e : Term Σ ty_int) : Term Σ ty_int
  | term_eq      (e1 e2 : Term Σ ty_int) : Term Σ ty_bool
  | term_le      (e1 e2 : Term Σ ty_int) : Term Σ ty_bool
  | term_lt      (e1 e2 : Term Σ ty_int) : Term Σ ty_bool
  | term_gt      (e1 e2 : Term Σ ty_int) : Term Σ ty_bool
  | term_and     (e1 e2 : Term Σ ty_bool) : Term Σ ty_bool
  | term_or      (e1 e2 : Term Σ ty_bool) : Term Σ ty_bool
  | term_not     (e : Term Σ ty_bool) : Term Σ ty_bool
  | term_pair    {σ1 σ2 : Ty} (e1 : Term Σ σ1) (e2 : Term Σ σ2) : Term Σ (ty_prod σ1 σ2)
  | term_inl     {σ1 σ2 : Ty} : Term Σ σ1 -> Term Σ (ty_sum σ1 σ2)
  | term_inr     {σ1 σ2 : Ty} : Term Σ σ2 -> Term Σ (ty_sum σ1 σ2)
  | term_list    {σ : Ty} (es : list (Term Σ σ)) : Term Σ (ty_list σ)
  | term_cons    {σ : Ty} (h : Term Σ σ) (t : Term Σ (ty_list σ)) : Term Σ (ty_list σ)
  | term_nil     {σ : Ty} : Term Σ (ty_list σ)
  (* Experimental features *)
  | term_tuple   {σs : Ctx Ty} (es : Env (Term Σ) σs) : Term Σ (ty_tuple σs)
  | term_projtup {σs : Ctx Ty} (e : Term Σ (ty_tuple σs)) (n : nat) {σ : Ty}
                {p : ctx_nth_is σs n σ} : Term Σ σ
  | term_union   {U : 𝑼} (K : 𝑼𝑲 U) (e : Term Σ (𝑼𝑲_Ty K)) : Term Σ (ty_union U)
  | term_record  (R : 𝑹) (es : Env' (Term Σ) (𝑹𝑭_Ty R)) : Term Σ (ty_record R)
  | term_projrec {R : 𝑹} (e : Term Σ (ty_record R)) (rf : 𝑹𝑭) {σ : Ty}
                {rfInR : InCtx (rf , σ) (𝑹𝑭_Ty R)} : Term Σ σ
  | term_builtin {σ τ : Ty} (f : Lit σ -> Lit τ) (e : Term Σ σ) : Term Σ τ.
  Bind Scope exp_scope with Term.

  Global Arguments term_var {_} _ {_ _}.
  Global Arguments term_tuple {_ _} _%exp.
  Global Arguments term_union {_} _ _.
  Global Arguments term_record {_} _ _.
  Global Arguments term_projrec {_ _} _ _ {_ _}.

  Definition SymbolicStore (Σ : Ctx (𝑺 * Ty)) (Γ : Ctx (𝑿 * Ty)) : Type := Env' (Term Σ) Γ.
  Bind Scope env_scope with SymbolicStore.

  Fixpoint seval {Σ : Ctx (𝑺 * Ty)} {Γ : Ctx (𝑿 * Ty)} {σ : Ty} (e : Exp Γ σ) (δ : SymbolicStore Σ Γ) : Term Σ σ :=
    match e in (Exp _ t) return (Term Σ t) with
    | exp_var ς                       => (δ ! ς)%lit
    | exp_lit _ σ0 l                  => term_lit _ σ0 l
    | exp_plus e1 e2                  => term_plus (seval e1 δ) (seval e2 δ)
    | exp_times e1 e2                 => term_times (seval e1 δ) (seval e2 δ)
    | exp_minus e1 e2                 => term_minus (seval e1 δ) (seval e2 δ)
    | exp_neg e0                      => term_neg (seval e0 δ)
    | exp_eq e1 e2                    => term_eq (seval e1 δ) (seval e2 δ)
    | exp_le e1 e2                    => term_le (seval e1 δ) (seval e2 δ)
    | exp_lt e1 e2                    => term_lt (seval e1 δ) (seval e2 δ)
    | exp_gt e1 e2                    => term_gt (seval e1 δ) (seval e2 δ)
    | exp_and e1 e2                   => term_and (seval e1 δ) (seval e2 δ)
    | exp_or e1 e2                    => term_or (seval e1 δ) (seval e2 δ)
    | exp_not e0                      => term_not (seval e0 δ)
    | exp_pair e1 e2                  => term_pair (seval e1 δ) (seval e2 δ)
    | @exp_inl _ σ1 σ2 e0             => @term_inl _ σ1 σ2 (seval e0 δ)
    | @exp_inr _ σ1 σ2 e0             => @term_inr _ σ1 σ2 (seval e0 δ)
    | @exp_list _ σ0 es               => term_list (List.map (fun e : Exp Γ σ0 => seval e δ) es)
    | exp_cons e1 e2                  => term_cons (seval e1 δ) (seval e2 δ)
    | @exp_nil _ σ0                   => term_nil _
    | @exp_tuple _ σs es              =>
      let sevals := fix sevals {σs : Ctx Ty} (es : Env (Exp Γ) σs) : Env (Term Σ) σs :=
                      match es with
                      | env_nil => env_nil
                      | env_snoc es σ e => env_snoc (sevals es) σ (seval e δ)
                      end
      in @term_tuple _ σs (sevals es)
    | @exp_projtup _ σs e0 n σ0 p     => @term_projtup _ σs (seval e0 δ) n σ0 p
    | @exp_union _ T K e0             => @term_union _ T K (seval e0 δ)
    | exp_record R es                 =>
      let sevals := fix sevals {rfs : Ctx (𝑹𝑭 * Ty)} (es : Env' (Exp Γ) rfs) : Env' (Term Σ) rfs :=
                      match es with
                      | env_nil => env_nil
                      | env_snoc es σ e => env_snoc (sevals es) σ (seval e δ)
                      end
      in term_record R (sevals es)
    | @exp_projrec _ R e0 rf σ0 rfInR => @term_projrec _ R (seval e0 δ) rf σ0 rfInR
    | @exp_builtin _ σ0 τ f e0        => @term_builtin _ σ0 τ f (seval e0 δ)
    end.

  Definition PathCondition (Σ : Ctx (𝑺 * Ty)) : Type :=
    Ctx (Term Σ ty_bool).
  Definition SymbolicHeap (Σ : Ctx (𝑺 * Ty)) : Type :=
    Ctx { p : 𝑷 & Env (Term Σ) (𝑷_Ty p) }.
  Bind Scope ctx_scope with SymbolicHeap.

  Definition SymbolicState (Σ : Ctx (𝑺 * Ty)) (Γ : Ctx (𝑿 * Ty)) : Type :=
    PathCondition Σ * SymbolicStore Σ Γ * SymbolicHeap Σ.

  Inductive outcome (S A: Type) :=
  | single (s: S)(a: A)
  | demonic {I : Set} (os: I -> outcome S A)
  | angelic {I : Set} (os: I -> outcome S A).

  Section SymbolicExecution.

    Context {Σ : Ctx (𝑺 * Ty)}.
    Context {Γ : Ctx (𝑿 * Ty)}.
    (* Path condition *)

    Inductive sexec (pc : Ctx (Term Σ ty_bool)) (δ : SymbolicStore Σ Γ) (ĥ : SymbolicHeap Σ) :
      forall (σ : Ty), Stm Γ σ -> outcome (SymbolicState Σ Γ) (Term Σ σ) -> Prop :=
    (* Bake in: path condition should imply post-condition. *)
    | sexc_lit {σ : Ty} (v : Lit σ)   : sexec pc δ ĥ (stm_lit σ v) (single (pc , δ , ĥ) (term_lit _ σ v))
    | sexc_exp {τ : Ty} (e : Exp Γ τ) : sexec pc δ ĥ (stm_exp e) (single (pc , δ , ĥ) (seval e δ))
    | sexc_if  {τ : Ty} (e : Exp Γ ty_bool) (s1 s2 : Stm Γ τ) o1 o2 :
        sexec (pc ▻ seval e δ)            δ ĥ s1 o1 ->
        sexec (pc ▻ term_not (seval e δ)) δ ĥ s1 o2 ->
        sexec pc                          δ ĥ (stm_if e s1 s2) (demonic (fun b : bool => if b then o1 else o2)).
  (*   | sexc_seq {ĥ : SymbolicHeap Σ} {τ σ : Ty} (s1 : Stm Γ τ) (s2 : Stm Γ σ) o1 o2 : *)
  (*       sexec pc ĥ s1 o1 -> *)

  (*       sexec pc ĥ (stm_seq s1 s2). *)
  (*   (* | stm_let        (x : 𝑿) (τ : Ty) (s : Stm Γ τ) {σ : Ty} (k : Stm (ctx_snoc Γ (x , τ)) σ) : Stm Γ σ *) *)
  (*   (* | stm_let'       (Δ : Ctx (𝑿 * Ty)) (δ : LocalStore Δ) {σ : Ty} (k : Stm (ctx_cat Γ Δ) σ) : Stm Γ σ *) *)
  (*   (* | stm_assign     (x : 𝑿) (τ : Ty) {xInΓ : InCtx (x , τ) Γ} (e : Stm Γ τ) : Stm Γ τ *) *)
  (*   (* | stm_call       {Δ σ} (f : 𝑭 Δ σ) (es : Env' (Exp Γ) Δ) : Stm Γ σ *) *)
  (*   (* | stm_call'      (Δ : Ctx (𝑿 * Ty)) (δ : LocalStore Δ) (τ : Ty) (s : Stm Δ τ) : Stm Γ τ *) *)
  (*   | stm_assert     (e1 : Exp Γ ty_bool) (e2 : Exp Γ ty_string) : Stm Γ ty_bool *)
  (*   (* | stm_while      (w : 𝑾 Γ) (e : Exp Γ ty_bool) {σ : Ty} (s : Stm Γ σ) -> Stm Γ ty_unit *) *)
  (*   | stm_fail      (τ : Ty) (s : Lit ty_string) : Stm Γ τ *)
  (*   | stm_match_list {σ τ : Ty} (e : Exp Γ (ty_list σ)) (alt_nil : Stm Γ τ) *)
  (*     (xh xt : 𝑿) (alt_cons : Stm (ctx_snoc (ctx_snoc Γ (xh , σ)) (xt , ty_list σ)) τ) : Stm Γ τ *)
  (*   | stm_match_sum  {σinl σinr τ : Ty} (e : Exp Γ (ty_sum σinl σinr)) *)
  (*     (xinl : 𝑿) (alt_inl : Stm (ctx_snoc Γ (xinl , σinl)) τ) *)
  (*     (xinr : 𝑿) (alt_inr : Stm (ctx_snoc Γ (xinr , σinr)) τ) : Stm Γ τ *)
  (*   | stm_match_pair {σ1 σ2 τ : Ty} (e : Exp Γ (ty_prod σ1 σ2)) *)
  (*     (xl xr : 𝑿) (rhs : Stm (ctx_snoc (ctx_snoc Γ (xl , σ1)) (xr , σ2)) τ) : Stm Γ τ *)
  (*   | stm_match_enum {E : 𝑬} (e : Exp Γ (ty_enum E)) {τ : Ty} *)
  (*     (alts : forall (K : 𝑬𝑲 E), Stm Γ τ) : Stm Γ τ *)
  (*   | stm_match_tuple {σs : Ctx Ty} {Δ : Ctx (𝑿 * Ty)} (e : Exp Γ (ty_tuple σs)) *)
  (*     (p : TuplePat σs Δ) {τ : Ty} (rhs : Stm (ctx_cat Γ Δ) τ) : Stm Γ τ *)
  (*   | stm_match_union {U : 𝑼} (e : Exp Γ (ty_union U)) {τ : Ty} *)
  (*     (* An earlier definition of stm_match_union used a "list of pairs" *)
  (*         (alts : forall (K : 𝑲 T), { x : 𝑿 & Stm (ctx_snoc Γ (x , 𝑲_Ty K)) τ}) *)
  (*        to define alternatives, which packs the variable name x for the field *)
  (*        of the union neatly together with the right hand side. Unfortunately, *)
  (*        due toe the sigma type constructor the derived induction principle is *)
  (*        not strong enough. It's possible to write a better induction principle *)
  (*        by hand, but since the AST is still in flux this is too much of a *)
  (*        burden to keep updated. Instead we use two "lists", one for the *)
  (*        variable names and one for the RHSs, which separates them lexically, *)
  (*        but gives a better induction principle. *) *)
  (*     (altx : forall (K : 𝑼𝑲 U), 𝑿) *)
  (*     (alts : forall (K : 𝑼𝑲 U), Stm (ctx_snoc Γ (altx K , 𝑼𝑲_Ty K)) τ) : Stm Γ τ *)
  (*   | stm_match_record {R : 𝑹} {Δ : Ctx (𝑿 * Ty)} (e : Exp Γ (ty_record R)) *)
  (*     (p : RecordPat (𝑹𝑭_Ty R) Δ) {τ : Ty} (rhs : Stm (ctx_cat Γ Δ) τ) : Stm Γ τ *)
  (*   | stm_read_register {τ} (reg : 𝑹𝑬𝑮 τ) : Stm Γ τ *)
  (*   | stm_write_register {τ} (reg : 𝑹𝑬𝑮 τ) (e : Exp Γ τ) : Stm Γ τ *)
  (*   | stm_bind   {σ τ : Ty} (s : Stm Γ σ) (k : Lit σ -> Stm Γ τ) : Stm Γ τ. *)
  (*   Bind Scope stm_scope with Stm. *)
  (* | *)

End Symbolic.
