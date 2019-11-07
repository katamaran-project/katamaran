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
     Context
     Environment
     Notation.

Set Implicit Arguments.

Module Type TypeKit.

  (* Names of union type constructors. *)
  Parameter 𝑻   : Set. (* input: \MIT *)
  (* Names of record type constructors. *)
  Parameter 𝑹  : Set.
  (* Names of expression variables. *)
  Parameter 𝑿 : Set. (* input: \MIX *)

  Inductive Ty : Set :=
  | ty_int
  | ty_bool
  | ty_bit
  | ty_string
  | ty_list (σ : Ty)
  | ty_prod (σ τ : Ty)
  | ty_sum  (σ τ : Ty)
  | ty_unit
  (* Experimental features. These are still in flux. *)
  | ty_tuple (σs : Ctx Ty)
  | ty_union (T : 𝑻)
  | ty_record (R : 𝑹)
  .

End TypeKit.

Module Type TermKit (typeKit : TypeKit).
  Import typeKit.

  (* Names of union data constructors. *)
  Parameter 𝑲  : 𝑻 -> Set.
  (* Union data constructor field type *)
  Parameter 𝑲_Ty : forall (T : 𝑻), 𝑲 T -> Ty.
  (* Record field names. *)
  Parameter 𝑹𝑭  : Set.
  (* Record field types. *)
  Parameter 𝑹𝑭_Ty : 𝑹 -> Ctx (𝑹𝑭 * Ty).

  (* Names of functions. *)
  Parameter 𝑭  : Ctx (𝑿 * Ty) -> Ty -> Set.

  Section Literals.

    Inductive Bit : Set := bitzero | bitone.

    (* Ideally we want object language literals to coincide with meta-language
       values to get sexy looking predicates. See the definition of Lit below.
       Unfortunately our setup of union and record types essentially is a giant
       mutually recursive family of types and hence Lit below would not
       terminate if it were directly extended to unions/records. TaggedLit is an
       inductive and therefore terminating definition of the recursive family of
       types and our current solution to the problem.

       Because Sail does not allow recursive types the records and unions in the
       generated output will form a strict DAG. Enforcing a topological sorting
       is more work than simply allowing recursive definitions. Another option
       is to encode the DAG as a well-founded relation between type constructor
       names an defining Lit by well-founded recursion. This would need some
       investigation.

       The ideal way to add recursive types would be to only introduce tags at
       recursive positions. For instance writing Lit as a recursive definition
       of a functor and using that in the definition of tagged:

         Fixpoint Lit (tl : Ty -> Set) (σ : Ty) {struct σ} : Set := match σ with
           ... end.

         Inductive TaggedLit (σ : Ty) : Set := | tagged : Lit TaggedLit σ ->
         TaggedLit σ.

       But currently Coq's strict-positivity checker is not smart enough to deem
       it safe. (Agda excepts this definition). So TaggedLit adds tags
       everywhere.
     *)
    Inductive TaggedLit : Ty -> Set :=
    | taglit_int           : Z -> TaggedLit (ty_int)
    | taglit_bool          : bool -> TaggedLit (ty_bool)
    | taglit_bit           : Bit -> TaggedLit (ty_bit)
    | taglit_string        : string -> TaggedLit (ty_string)
    | taglit_list   σ'     : list (TaggedLit σ') -> TaggedLit (ty_list σ')
    | taglit_prod   σ₁ σ₂  : TaggedLit σ₁ * TaggedLit σ₂ -> TaggedLit (ty_prod σ₁ σ₂)
    | taglit_sum    σ₁ σ₂  : TaggedLit σ₁ + TaggedLit σ₂ -> TaggedLit (ty_sum σ₁ σ₂)
    | taglit_unit          : TaggedLit (ty_unit)
    (* Experimental features *)
    | taglit_tuple σs      : Env TaggedLit σs -> TaggedLit (ty_tuple σs)
    | taglit_union (T : 𝑻) (K : 𝑲 T) : TaggedLit (𝑲_Ty K) -> TaggedLit (ty_union T)
    | taglit_record (R : 𝑹) : Env' TaggedLit (𝑹𝑭_Ty R) -> TaggedLit (ty_record R).

    Global Arguments taglit_tuple {_} _.
    Global Arguments taglit_union {_} _ _.
    Global Arguments taglit_record : clear implicits.

    Fixpoint Lit (σ : Ty) : Set :=
      match σ with
      | ty_int => Z
      | ty_bool => bool
      | ty_bit => Bit
      | ty_string => string
      | ty_list σ' => list (Lit σ')
      | ty_prod σ₁ σ₂ => Lit σ₁ * Lit σ₂
      | ty_sum σ₁ σ₂ => Lit σ₁ + Lit σ₂
      | ty_unit => unit
      (* Experimental features *)
      | ty_tuple σs => Env TaggedLit σs
      | ty_union T => { K : 𝑲 T & TaggedLit (𝑲_Ty K) }
      | ty_record R => Env' TaggedLit (𝑹𝑭_Ty R)
      end%type.

    Fixpoint untag {σ : Ty} (v : TaggedLit σ) : Lit σ :=
      match v with
      | taglit_int z        => z
      | taglit_bool b       => b
      | taglit_bit b        => b
      | taglit_string s     => s
      | taglit_list ls      => List.map untag ls
      | taglit_prod (l , r) => (untag l , untag r)
      | taglit_sum (inl v)  => inl (untag v)
      | taglit_sum (inr v)  => inr (untag v)
      | taglit_unit         => tt
      (* Experimental features *)
      | taglit_tuple ls     => ls
      | taglit_union K l    => existT _ K l
      | taglit_record R t   => t
      end.

    Fixpoint tag (σ : Ty) {struct σ} : Lit σ -> TaggedLit σ :=
      match σ with
      | ty_int => fun (l : Lit ty_int) => taglit_int l
      | ty_bool => taglit_bool
      | ty_bit => taglit_bit
      | ty_string => taglit_string
      | ty_list σ =>
        fun l => taglit_list (List.map (tag σ) l)
      | ty_prod σ1 σ2 =>
        fun l => let (l1, l2) := l in
                 taglit_prod (tag σ1 l1, tag σ2 l2)
      | ty_sum σ1 σ2 =>
        fun l : Lit (ty_sum σ1 σ2) =>
          match l with
          | inl l => taglit_sum (inl (tag σ1 l))
          | inr l => taglit_sum (inr (tag σ2 l))
          end
      | ty_unit => fun _ => taglit_unit
      | ty_tuple σs => taglit_tuple
      | ty_union T => fun Ktl => let (K, tl) := Ktl in taglit_union K tl
      | ty_record R => taglit_record R
      end.

  End Literals.

  Section Expressions.

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
    Inductive Exp (Γ : Ctx (𝑿 * Ty)) : Ty -> Set :=
    | exp_var     (x : 𝑿) (σ : Ty) {xInΓ : InCtx (x , σ) Γ} : Exp Γ σ
    | exp_lit     (σ : Ty) : Lit σ -> Exp Γ σ
    | exp_plus    (e₁ e₂ : Exp Γ ty_int) : Exp Γ ty_int
    | exp_times   (e₁ e₂ : Exp Γ ty_int) : Exp Γ ty_int
    | exp_minus   (e₁ e₂ : Exp Γ ty_int) : Exp Γ ty_int
    | exp_neg     (e : Exp Γ ty_int) : Exp Γ ty_int
    | exp_eq      (e₁ e₂ : Exp Γ ty_int) : Exp Γ ty_bool
    | exp_le      (e₁ e₂ : Exp Γ ty_int) : Exp Γ ty_bool
    | exp_lt      (e₁ e₂ : Exp Γ ty_int) : Exp Γ ty_bool
    | exp_and     (e₁ e₂ : Exp Γ ty_bool) : Exp Γ ty_bool
    | exp_not     (e : Exp Γ ty_bool) : Exp Γ ty_bool
    | exp_pair    {σ₁ σ₂ : Ty} (e₁ : Exp Γ σ₁) (e₂ : Exp Γ σ₂) : Exp Γ (ty_prod σ₁ σ₂)
    | exp_inl     {σ₁ σ₂ : Ty} : Exp Γ σ₁ -> Exp Γ (ty_sum σ₁ σ₂)
    | exp_inr     {σ₁ σ₂ : Ty} : Exp Γ σ₂ -> Exp Γ (ty_sum σ₁ σ₂)
    | exp_list    {σ : Ty} (es : list (Exp Γ σ)) : Exp Γ (ty_list σ)
    | exp_cons    {σ : Ty} (h : Exp Γ σ) (t : Exp Γ (ty_list σ)) : Exp Γ (ty_list σ)
    | exp_nil     {σ : Ty} : Exp Γ (ty_list σ)
    (* Experimental features *)
    | exp_tuple   {σs : Ctx Ty} (es : Env (Exp Γ) σs) : Exp Γ (ty_tuple σs)
    | exp_projtup {σs : Ctx Ty} (e : Exp Γ (ty_tuple σs)) (n : nat) {σ : Ty}
                  {p : ctx_nth_is σs n σ} : Exp Γ σ
    | exp_union   {T : 𝑻} (K : 𝑲 T) (e : Exp Γ (𝑲_Ty K)) : Exp Γ (ty_union T)
    | exp_record  (R : 𝑹) (es : Env' (Exp Γ) (𝑹𝑭_Ty R)) : Exp Γ (ty_record R)
    | exp_projrec {R : 𝑹} (e : Exp Γ (ty_record R)) (rf : 𝑹𝑭) {σ : Ty}
                  {rfInR : InCtx (rf , σ) (𝑹𝑭_Ty R)} : Exp Γ σ
    | exp_builtin {σ τ : Ty} (f : Lit σ -> Lit τ) (e : Exp Γ σ) : Exp Γ τ.

    Global Arguments exp_var {_} _ {_ _}.
    Global Arguments exp_union {_ _} _ _.
    Global Arguments exp_record {_} _ _.
    Global Arguments exp_projrec {_ _} _ _ {_ _}.

    Import EnvNotations.

    Definition LocalStore (Γ : Ctx (𝑿 * Ty)) : Set := Env' Lit Γ.

    Fixpoint evalTagged {Γ : Ctx (𝑿 * Ty)} {σ : Ty} (e : Exp Γ σ) (δ : LocalStore Γ) {struct e} : TaggedLit σ :=
      match e in (Exp _ t) return (TaggedLit t) with
      | exp_var x => tag _ (δ ! x)
      | exp_lit _ σ0 l => tag σ0 l
      | exp_plus e1 e2 => taglit_int (untag (evalTagged e1 δ) + untag (evalTagged e2 δ))
      | exp_times e1 e2 => taglit_int (untag (evalTagged e1 δ) * untag (evalTagged e2 δ))
      | exp_minus e1 e2 => taglit_int (untag (evalTagged e1 δ) - untag (evalTagged e2 δ))
      | exp_neg e0 => taglit_int (- untag (evalTagged e0 δ))
      | exp_eq e1 e2 => taglit_bool (Zeq_bool (untag (evalTagged e1 δ)) (untag (evalTagged e2 δ)))
      | exp_le e1 e2 => taglit_bool (untag (evalTagged e1 δ) <=? untag (evalTagged e2 δ))%Z
      | exp_lt e1 e2 => taglit_bool (untag (evalTagged e1 δ) <? untag (evalTagged e2 δ))%Z
      | exp_and e1 e2 => taglit_bool (untag (evalTagged e1 δ) && untag (evalTagged e2 δ))
      | exp_not e0 => taglit_bool (negb (untag (evalTagged e0 δ)))
      | @exp_pair _ σ₁ σ₂ e1 e2 => taglit_prod (evalTagged e1 δ, evalTagged e2 δ)
      | @exp_inl _ σ₁ σ₂ e0 => taglit_sum (inl (evalTagged e0 δ))
      | @exp_inr _ σ₁ σ₂ e0 => taglit_sum (inr (evalTagged e0 δ))
      | @exp_list _ σ0 es => taglit_list (List.map (fun e0 : Exp Γ σ0 => evalTagged e0 δ) es)
      | @exp_cons _ σ0 e1 e2 =>
        (* This is less efficient than it could be. It's untagging the head and
           the whole list while it would only need to destruct (evalTagged e2
           δ). *)
        tag (ty_list σ0) (cons (untag (evalTagged e1 δ)) (untag (evalTagged e2 δ)))
      | @exp_nil _ σ0 => taglit_list nil
      | @exp_tuple _ σs es =>
        let evalsTagged := fix evalsTagged {σs : Ctx Ty} (es : Env (Exp Γ) σs) : Env TaggedLit σs :=
                             match es with
                             | env_nil => env_nil
                             | env_snoc es σ e => env_snoc (evalsTagged es) σ (evalTagged e δ)
                             end
        in taglit_tuple (evalsTagged es)
      | @exp_projtup _ σs e0 n σ0 p => env_lookup (untag (evalTagged e0 δ)) (Build_InCtx _ _ n p)
      | @exp_union _ T K e0 => taglit_union K (evalTagged e0 δ)
      | exp_record R es =>
        let evalsTagged := fix evalsTagged {rfs : Ctx (𝑹𝑭 * Ty)} (es : Env' (Exp Γ) rfs) : Env' TaggedLit rfs :=
                             match es with
                             | env_nil => env_nil
                             | env_snoc es σ e => env_snoc (evalsTagged es) σ (evalTagged e δ)
                             end
        in taglit_record R (evalsTagged es)
      | @exp_projrec _ R e0 rf σ0 rfInR => env_lookup (untag (evalTagged e0 δ)) rfInR
      | @exp_builtin _ σ0 τ f e0 => tag τ (f (untag (evalTagged e0 δ)))
      end.

    Fixpoint eval {Γ : Ctx (𝑿 * Ty)} {σ : Ty} (e : Exp Γ σ) (δ : LocalStore Γ) {struct e} : Lit σ :=
      match e in (Exp _ t) return (Lit t) with
      | exp_var x           => δ ! x
      | exp_lit _ _ l       => l
      | exp_plus e₁ e2      => Z.add (eval e₁ δ) (eval e2 δ)
      | exp_times e₁ e2     => Z.mul (eval e₁ δ) (eval e2 δ)
      | exp_minus e₁ e2     => Z.sub (eval e₁ δ) (eval e2 δ)
      | exp_neg e           => Z.opp (eval e δ)
      | exp_eq e₁ e2        => Zeq_bool (eval e₁ δ) (eval e2 δ)
      | exp_le e₁ e2        => Z.leb (eval e₁ δ) (eval e2 δ)
      | exp_lt e₁ e2        => Z.ltb (eval e₁ δ) (eval e2 δ)
      | exp_and e₁ e2       => andb (eval e₁ δ) (eval e2 δ)
      | exp_not e           => negb (eval e δ)
      | exp_pair e₁ e2      => pair (eval e₁ δ) (eval e2 δ)
      | exp_inl e           => inl (eval e δ)
      | exp_inr e           => inr (eval e δ)
      | exp_list es         => List.map (fun e => eval e δ) es
      | exp_cons e₁ e2      => cons (eval e₁ δ) (eval e2 δ)
      | exp_nil _           => nil
      | exp_tuple es        => env_map (fun τ e => evalTagged e δ) es
      | @exp_projtup _ σs e n σ p => untag (env_lookup (eval e δ) (Build_InCtx _ _ n p))
      | exp_union K e       => existT _ K (evalTagged e δ)
      | exp_record R es     => env_map (fun τ e => evalTagged e δ) es
      | exp_projrec e rf    => untag (eval e δ ! rf)
      | exp_builtin f e     => f (eval e δ)
      end.

    Definition evals {Γ Δ} (es : Env' (Exp Γ) Δ) (δ : LocalStore Γ) : LocalStore Δ :=
      env_map (fun xτ e => eval e δ) es.

  End Expressions.

  Section Statements.

    Inductive TuplePat : Ctx Ty -> Ctx (𝑿 * Ty) -> Set :=
    | tuplepat_nil  : TuplePat ctx_nil ctx_nil
    | tuplepat_snoc
        {σs : Ctx Ty} {Δ : Ctx (𝑿 * Ty)}
        (pat : TuplePat σs Δ) {σ : Ty} (x : 𝑿) :
        TuplePat (ctx_snoc σs σ) (ctx_snoc Δ (x , σ)).

    Inductive RecordPat : Ctx (𝑹𝑭 * Ty) -> Ctx (𝑿 * Ty) -> Set :=
    | recordpat_nil  : RecordPat ctx_nil ctx_nil
    | recordpat_snoc
        {rfs : Ctx (𝑹𝑭 * Ty)} {Δ : Ctx (𝑿 * Ty)}
        (pat : RecordPat rfs Δ) (rf : 𝑹𝑭) {τ : Ty} (x : 𝑿) :
        RecordPat (ctx_snoc rfs (rf , τ)) (ctx_snoc Δ (x , τ)).

    Inductive Stm (Γ : Ctx (𝑿 * Ty)) : Ty -> Set :=
    | stm_lit        {τ : Ty} (l : Lit τ) : Stm Γ τ
    | stm_exp        {τ : Ty} (e : Exp Γ τ) : Stm Γ τ
    | stm_let        (x : 𝑿) (τ : Ty) (s : Stm Γ τ) {σ : Ty} (k : Stm (ctx_snoc Γ (x , τ)) σ) : Stm Γ σ
    | stm_let'       (Δ : Ctx (𝑿 * Ty)) (δ : LocalStore Δ) {σ : Ty} (k : Stm (ctx_cat Γ Δ) σ) : Stm Γ σ
    | stm_assign     (x : 𝑿) (τ : Ty) {xInΓ : InCtx (x , τ) Γ} (e : Exp Γ τ) : Stm Γ τ
    | stm_app        {σs σ} (f : 𝑭 σs σ) (es : Env' (Exp Γ) σs) : Stm Γ σ
    | stm_app'       (Δ : Ctx (𝑿 * Ty)) (δ : LocalStore Δ) (τ : Ty) (s : Stm Δ τ) : Stm Γ τ
    | stm_if         {τ : Ty} (e : Exp Γ ty_bool) (s₁ s₂ : Stm Γ τ) : Stm Γ τ
    | stm_seq        {τ : Ty} (e : Stm Γ τ) {σ : Ty} (k : Stm Γ σ) : Stm Γ σ
    | stm_assert     (e₁ : Exp Γ ty_bool) (e₂ : Exp Γ ty_string) : Stm Γ ty_bool
    (* | stm_while      (w : 𝑾 Γ) (e : Exp Γ ty_bool) {σ : Ty} (s : Stm Γ σ) -> Stm Γ ty_unit *)
    | stm_exit       (τ : Ty) (s : Lit ty_string) : Stm Γ τ
    | stm_match_list {σ τ : Ty} (e : Exp Γ (ty_list σ)) (alt_nil : Stm Γ τ)
      (xh xt : 𝑿) (alt_cons : Stm (ctx_snoc (ctx_snoc Γ (xh , σ)) (xt , ty_list σ)) τ) : Stm Γ τ
    | stm_match_sum  {σinl σinr τ : Ty} (e : Exp Γ (ty_sum σinl σinr))
      (xinl : 𝑿) (alt_inl : Stm (ctx_snoc Γ (xinl , σinl)) τ)
      (xinr : 𝑿) (alt_inr : Stm (ctx_snoc Γ (xinr , σinr)) τ) : Stm Γ τ
    | stm_match_pair {σ₁ σ₂ τ : Ty} (e : Exp Γ (ty_prod σ₁ σ₂))
      (xl xr : 𝑿) (rhs : Stm (ctx_snoc (ctx_snoc Γ (xl , σ₁)) (xr , σ₂)) τ) : Stm Γ τ
    | stm_match_tuple {σs : Ctx Ty} {Δ : Ctx (𝑿 * Ty)} (e : Exp Γ (ty_tuple σs))
      (p : TuplePat σs Δ) {τ : Ty} (rhs : Stm (ctx_cat Γ Δ) τ) : Stm Γ τ
    | stm_match_union {T : 𝑻} (e : Exp Γ (ty_union T)) {τ : Ty}
      (* An earlier definition of stm_match_union used a "list of pairs"
          (alts : forall (K : 𝑲 T), { x : 𝑿 & Stm (ctx_snoc Γ (x , 𝑲_Ty K)) τ})
         to define alternatives, which packs the variable name x for the field
         of the union neatly together with the right hand side. Unfortunately,
         due toe the sigma type constructor the derived induction principle is
         not strong enough. It's possible to write a better induction principle
         by hand, but since the AST is still in flux this is too much of a
         burden to keep updated. Instead we use two "lists", one for the
         variable names and one for the RHSs, which separates them lexically,
         but gives a better induction principle. *)
      (altx : forall (K : 𝑲 T), 𝑿)
      (alts : forall (K : 𝑲 T), Stm (ctx_snoc Γ (altx K , 𝑲_Ty K)) τ) : Stm Γ τ
    | stm_match_record {R : 𝑹} {Δ : Ctx (𝑿 * Ty)} (e : Exp Γ (ty_record R))
      (p : RecordPat (𝑹𝑭_Ty R) Δ) {τ : Ty} (rhs : Stm (ctx_cat Γ Δ) τ) : Stm Γ τ.

    Global Arguments stm_lit {_} _ _.
    Global Arguments stm_exp {_ _} _.
    Global Arguments stm_let {_} _ _ _ {_} _.
    Global Arguments stm_let' {_ _} _ {_} _.
    Global Arguments stm_assign {_} _ {_ _} _.
    Global Arguments stm_app {_ _ _} _ _.
    Global Arguments stm_app' {_} _ _ _ _.
    Global Arguments stm_if {_ _} _ _ _.
    Global Arguments stm_seq {_ _} _ {_} _.
    Global Arguments stm_assert {_} _ _.
    Global Arguments stm_exit {_} _ _.
    Global Arguments stm_match_list {_ _ _} _ _ _ _ _.
    Global Arguments stm_match_sum {_ _ _ _} _ _ _ _ _.
    Global Arguments stm_match_pair {_ _ _ _} _ _ _ _.
    Global Arguments stm_match_tuple {_ _ _} _ _ {_} _.
    Global Arguments stm_match_union {_ _} _ {_} _ _.
    Global Arguments stm_match_record {_} _ {_} _ _ {_} _.

  End Statements.

  Record FunDef (Δ : Ctx (𝑿 * Ty)) (τ : Ty) : Set :=
    { fun_body : Stm Δ τ }.

  Module NameResolution.

    (* For name resolution we rely on decidable equality of expression
       variables. The functions in this module resolve to the closest binding
       of an equal name and fill in the de Bruijn index automatically from
       a successful resolution.
    *)
    Parameter 𝑿_eq_dec : forall x y : 𝑿, {x=y}+{~x=y}.

    Fixpoint ctx_resolve {D : Set} (Γ : Ctx (𝑿 * D)) (x : 𝑿) {struct Γ} : option D :=
      match Γ with
      | ctx_nil           => None
      | ctx_snoc Γ (y, d) => if 𝑿_eq_dec x y then Some d else ctx_resolve Γ x
      end.

    Definition IsSome {D : Set} (m : option D) : Set :=
      match m with
        | Some _ => unit
        | None => Empty_set
      end.

    Definition fromSome {D : Set} (m : option D) : IsSome m -> D :=
      match m return IsSome m -> D with
      | Some d => fun _ => d
      | None   => fun p => match p with end
      end.

    Fixpoint mk_inctx {D : Set} (Γ : Ctx (prod 𝑿 D)) (x : 𝑿) {struct Γ} :
      let m := ctx_resolve Γ x in forall (p : IsSome m), InCtx (x , fromSome m p) Γ :=
      match Γ with
      | ctx_nil => fun p => match p with end
      | ctx_snoc Γ (y, d) =>
        match 𝑿_eq_dec x y as s
        return (forall p, InCtx (x, fromSome (if s then Some d else ctx_resolve Γ x) p) (ctx_snoc Γ (y, d)))
        with
        | left e => fun _ => match e with | eq_refl => inctx_zero end
        | right _ => fun p => inctx_succ (mk_inctx Γ x p)
        end
      end.

    Definition exp_smart_var {Γ : Ctx (𝑿 * Ty)} (x : 𝑿) {p : IsSome (ctx_resolve Γ x)} :
      Exp Γ (fromSome (ctx_resolve Γ x) p) := @exp_var Γ x (fromSome _ p) (mk_inctx Γ x p).

    Definition stm_smart_assign {Γ : Ctx (𝑿 * Ty)} (x : 𝑿) {p : IsSome (ctx_resolve Γ x)} :
      Exp Γ (fromSome (ctx_resolve Γ x) p) -> Stm Γ (fromSome (ctx_resolve Γ x) p) :=
      @stm_assign Γ x (fromSome _ p) (mk_inctx Γ x p).

  End NameResolution.

  Definition Pred (A : Set) : Type := A -> Prop.

  Record Contract (Δ : Ctx (𝑿 * Ty)) (τ : Ty) : Type :=
    { contract_pre_condition  : Pred (Env' Lit Δ);
      contract_post_condition : Lit τ -> Pred (Env' Lit Δ)
    }.

  Definition ContractEnv : Type :=
    forall Δ τ (f : 𝑭 Δ τ), option (Contract Δ τ).

End TermKit.

Module Type ProgramKit (typeKit : TypeKit) (termKit : TermKit typeKit).
  Import typeKit.
  Import termKit.

  Parameter Pi : forall {Δ τ} (f : 𝑭 Δ τ), FunDef Δ τ.

  Import CtxNotations.
  Import EnvNotations.

  Section SmallStep.

    Fixpoint tuple_pattern_match {σs : Ctx Ty} {Δ : Ctx (𝑿 * Ty)}
             (p : TuplePat σs Δ) {struct p} : Env TaggedLit σs -> LocalStore Δ :=
      match p with
      | tuplepat_nil => fun _ => env_nil
      | tuplepat_snoc p x =>
        fun E =>
          env_snoc
            (tuple_pattern_match p (env_tail E)) (x, _)
            (untag (env_lookup E inctx_zero))
      end.

    Fixpoint record_pattern_match {rfs : Ctx (𝑹𝑭 * Ty)}  {Δ : Ctx (𝑿 * Ty)}
             (p : RecordPat rfs Δ) {struct p} : Env' TaggedLit rfs -> LocalStore Δ :=
      match p with
      | recordpat_nil => fun _ => env_nil
      | recordpat_snoc p rf x =>
        fun E =>
          env_snoc
            (record_pattern_match p (env_tail E)) (x, _)
            (untag (env_lookup E inctx_zero))
      end.

    Inductive Step {Γ : Ctx (𝑿 * Ty)} : forall {σ : Ty} (δ₁ δ₂ : LocalStore Γ) (s₁ s₂ : Stm Γ σ), Prop :=

    | step_stm_exp
        (δ : LocalStore Γ) (σ : Ty) (e : Exp Γ σ) :
        ⟨ δ , stm_exp e ⟩ ---> ⟨ δ , stm_lit σ (eval e δ) ⟩

    | step_stm_let_value
        (δ : LocalStore Γ) (x : 𝑿) (τ σ : Ty) (v : Lit τ) (k : Stm (Γ ▻ (x , τ)) σ) :
        ⟨ δ , stm_let x τ (stm_lit τ v) k ⟩ ---> ⟨ δ , stm_let' (env_snoc env_nil (x,τ) v) k ⟩
    | step_stm_let_exit
        (δ : LocalStore Γ) (x : 𝑿) (τ σ : Ty) (s : string) (k : Stm (Γ ▻ (x , τ)) σ) :
        ⟨ δ , stm_let x τ (stm_exit τ s) k ⟩ ---> ⟨ δ , stm_exit σ s ⟩
    | step_stm_let_step
        (δ : LocalStore Γ) (δ' : LocalStore Γ) (x : 𝑿) (τ σ : Ty)
        (s : Stm Γ τ) (s' : Stm Γ τ) (k : Stm (Γ ▻ (x , τ)) σ) :
        ⟨ δ , s ⟩ ---> ⟨ δ' , s' ⟩ ->
        ⟨ δ , stm_let x τ s k ⟩ ---> ⟨ δ' , stm_let x τ s' k ⟩
    | step_stm_let'_value
        (δ : LocalStore Γ) (Δ : Ctx (𝑿 * Ty)) (δΔ : LocalStore Δ) (σ : Ty) (v : Lit σ) :
        ⟨ δ , stm_let' δΔ (stm_lit σ v) ⟩ ---> ⟨ δ , stm_lit σ v ⟩
    | step_stm_let'_exit
        (δ : LocalStore Γ) (Δ : Ctx (𝑿 * Ty)) (δΔ : LocalStore Δ) (σ : Ty) (s : string) :
        ⟨ δ , stm_let' δΔ (stm_exit σ s) ⟩ ---> ⟨ δ , stm_exit σ s ⟩
    | step_stm_let'_step
        (δ δ' : LocalStore Γ) (Δ : Ctx (𝑿 * Ty)) (δΔ δΔ' : LocalStore Δ) (σ : Ty) (k k' : Stm (Γ ▻▻ Δ) σ) :
        ⟨ δ ►► δΔ , k ⟩ ---> ⟨ δ' ►► δΔ' , k' ⟩ ->
        ⟨ δ , stm_let' δΔ k ⟩ ---> ⟨ δ' , stm_let' δΔ' k' ⟩

    | step_stm_seq_step
        (δ δ' : LocalStore Γ) (τ σ : Ty) (s s' : Stm Γ τ) (k : Stm Γ σ) :
        ⟨ δ , s ⟩ ---> ⟨ δ' , s' ⟩ ->
        ⟨ δ , stm_seq s k ⟩ ---> ⟨ δ' , stm_seq s' k ⟩
    | step_stm_seq_value
        (δ : LocalStore Γ) (τ σ : Ty) (v : Lit τ) (k : Stm Γ σ) :
        ⟨ δ , stm_seq (stm_lit τ v) k ⟩ ---> ⟨ δ , k ⟩
    | step_stm_seq_exit
        (δ : LocalStore Γ) (τ σ : Ty) (s : string) (k : Stm Γ σ) :
        ⟨ δ , stm_seq (stm_exit τ s) k ⟩ ---> ⟨ δ , stm_exit σ s ⟩

    | step_stm_app
        {δ : LocalStore Γ} {σs σ} {f : 𝑭 σs σ} (es : Env' (Exp Γ) σs) :
        ⟨ δ , stm_app f es ⟩ --->
        ⟨ δ , stm_app' σs (evals es δ) σ (fun_body (Pi f)) ⟩
    | step_stm_app'_step
        {δ : LocalStore Γ} (Δ : Ctx (𝑿 * Ty)) {δΔ δΔ' : LocalStore Δ} (τ : Ty)
        (s s' : Stm Δ τ) :
        ⟨ δΔ , s ⟩ ---> ⟨ δΔ' , s' ⟩ ->
        ⟨ δ , stm_app' Δ δΔ τ s ⟩ ---> ⟨ δ , stm_app' Δ δΔ' τ s' ⟩
    | step_stm_app'_value
        {δ : LocalStore Γ} (Δ : Ctx (𝑿 * Ty)) {δΔ : LocalStore Δ} (τ : Ty) (v : Lit τ) :
        ⟨ δ , stm_app' Δ δΔ τ (stm_lit τ v) ⟩ ---> ⟨ δ , stm_lit τ v ⟩
    | step_stm_app'_exit
        {δ : LocalStore Γ} (Δ : Ctx (𝑿 * Ty)) {δΔ : LocalStore Δ} (τ : Ty) (s : string) :
        ⟨ δ , stm_app' Δ δΔ τ (stm_exit τ s) ⟩ ---> ⟨ δ , stm_exit τ s ⟩
    | step_stm_assign
        (δ : LocalStore Γ) (x : 𝑿) (σ : Ty) {xInΓ : InCtx (x , σ) Γ} (e : Exp Γ σ) :
        let v := eval e δ in
        ⟨ δ , stm_assign x e ⟩ ---> ⟨ δ [ x ↦ v ] , stm_lit σ v ⟩
    | step_stm_if
        (δ : LocalStore Γ) (e : Exp Γ ty_bool) (σ : Ty) (s₁ s₂ : Stm Γ σ) :
        ⟨ δ , stm_if e s₁ s₂ ⟩ ---> ⟨ δ , if eval e δ then s₁ else s₂ ⟩
    | step_stm_assert
        (δ : LocalStore Γ) (e₁ : Exp Γ ty_bool) (e₂ : Exp Γ ty_string) :
        ⟨ δ , stm_assert e₁ e₂ ⟩ --->
        ⟨ δ , if eval e₁ δ then stm_lit ty_bool true else stm_exit ty_bool (eval e₂ δ) ⟩
    (* | step_stm_while : *)
    (*   (δ : LocalStore Γ) (w : 𝑾 δ) (e : Exp Γ ty_bool) {σ : Ty} (s : Stm Γ σ) -> *)
    (*   ⟨ δ , stm_while w e s ⟩ ---> *)
    (*   ⟨ δ , stm_if e (stm_seq s (stm_while w e s)) (stm_lit tt) ⟩ *)
    | step_stm_match_list
        (δ : LocalStore Γ) {σ τ : Ty} (e : Exp Γ (ty_list σ)) (alt_nil : Stm Γ τ)
        (xh xt : 𝑿) (alt_cons : Stm (Γ ▻ (xh , σ) ▻ (xt , ty_list σ)) τ) :
        ⟨ δ , stm_match_list e alt_nil xh xt alt_cons ⟩ --->
        ⟨ δ , match eval e δ with
              | nil => alt_nil
              | cons vh vt => stm_let' (env_snoc (env_snoc env_nil (xh,σ) vh) (xt,ty_list σ) vt) alt_cons
              end
        ⟩
    | step_stm_match_sum
        (δ : LocalStore Γ) {σinl σinr τ : Ty} (e : Exp Γ (ty_sum σinl σinr))
        (xinl : 𝑿) (alt_inl : Stm (Γ ▻ (xinl , σinl)) τ)
        (xinr : 𝑿) (alt_inr : Stm (Γ ▻ (xinr , σinr)) τ) :
        ⟨ δ , stm_match_sum e xinl alt_inl xinr alt_inr ⟩ --->
        ⟨ δ , match eval e δ with
              | inl v => stm_let' (env_snoc env_nil (xinl,σinl) v) alt_inl
              | inr v => stm_let' (env_snoc env_nil (xinr,σinr) v) alt_inr
              end
        ⟩
    | step_stm_match_pair
        (δ : LocalStore Γ) {σ₁ σ₂ τ : Ty} (e : Exp Γ (ty_prod σ₁ σ₂)) (xl xr : 𝑿)
        (rhs : Stm (Γ ▻ (xl , σ₁) ▻ (xr , σ₂)) τ) :
        ⟨ δ , stm_match_pair e xl xr rhs ⟩ --->
        ⟨ δ , let (vl , vr) := eval e δ in
              stm_let' (env_snoc (env_snoc env_nil (xl,σ₁) vl) (xr,σ₂) vr) rhs
        ⟩

    | step_stm_match_tuple
        (δ : LocalStore Γ) {σs : Ctx Ty} {Δ : Ctx (𝑿 * Ty)}
        (e : Exp Γ (ty_tuple σs)) (p : TuplePat σs Δ)
        {τ : Ty} (rhs : Stm (ctx_cat Γ Δ) τ) :
        ⟨ δ , stm_match_tuple e p rhs ⟩ --->
        ⟨ δ , stm_let' (tuple_pattern_match p (eval e δ)) rhs ⟩

    | step_stm_match_union
        (δ : LocalStore Γ) {T : 𝑻} (e : Exp Γ (ty_union T)) {τ : Ty}
        (altx : forall (K : 𝑲 T), 𝑿)
        (alts : forall (K : 𝑲 T), Stm (ctx_snoc Γ (altx K , 𝑲_Ty K)) τ) :
        ⟨ δ , stm_match_union e altx alts ⟩ --->
        ⟨ δ , let (K , v) := eval e δ in
              stm_let' (env_snoc env_nil (altx K,𝑲_Ty K) (untag v)) (alts K)
        ⟩
    | step_stm_match_record
        (δ : LocalStore Γ) {R : 𝑹} {Δ : Ctx (𝑿 * Ty)}
        (e : Exp Γ (ty_record R)) (p : RecordPat (𝑹𝑭_Ty R) Δ)
        {τ : Ty} (rhs : Stm (ctx_cat Γ Δ) τ) :
        ⟨ δ , stm_match_record R e p rhs ⟩ --->
        ⟨ δ , stm_let' (record_pattern_match p (eval e δ)) rhs ⟩

    where "'⟨' δ1 ',' s1 '⟩' '--->' '⟨' δ2 ',' s2 '⟩'" := (@Step _ _ δ1 δ2 s1 s2).

    Inductive Steps {Γ : Ctx (𝑿 * Ty)} {σ : Ty} (δ1 : LocalStore Γ) (s1 : Stm Γ σ) : LocalStore Γ -> Stm Γ σ -> Prop :=
    | step_refl : Steps δ1 s1 δ1 s1
    | step_trans {δ2 δ3 : LocalStore Γ} {s2 s3 : Stm Γ σ} :
        Step δ1 δ2 s1 s2 -> Steps δ2 s2 δ3 s3 -> Steps δ1 s1 δ3 s3.

    Definition Final {Γ σ} (s : Stm Γ σ) : Prop :=
      match s with
      | stm_lit _ _  => True
      | stm_exit _ _ => True
      | _ => False
      end.

    Lemma can_form_store_cat (Γ Δ : Ctx (𝑿 * Ty)) (δ : LocalStore (Γ ▻▻ Δ)) :
      exists (δ₁ : LocalStore Γ) (δ₂ : LocalStore Δ), δ = env_cat δ₁ δ₂.
    Proof. pose (env_cat_split δ); eauto. Qed.

    (* Lemma can_form_store_snoc (Γ : Ctx (𝑿 * Ty)) (x : 𝑿) (σ : Ty) (δ : LocalStore (Γ ▻ (x , σ))) : *)
    (*   exists (δ' : LocalStore Γ) (v : Lit σ), δ = env_snoc δ' x σ v. *)
    (* Admitted. *)

    (* Lemma can_form_store_nil (δ : LocalStore ε) : *)
    (*   δ = env_nil. *)
    (* Admitted. *)

    Local Ltac progress_can_form :=
      match goal with
      (* | [ H: LocalStore (ctx_snoc _ _) |- _ ] => pose proof (can_form_store_snoc H) *)
      (* | [ H: LocalStore ctx_nil |- _ ] => pose proof (can_form_store_nil H) *)
      | [ H: LocalStore (ctx_cat _ _) |- _ ] => pose proof (can_form_store_cat _ _ H)
      | [ H: Final ?s |- _ ] => destruct s; cbn in H
      end; destruct_conjs; subst; try contradiction.

    Local Ltac progress_simpl :=
      repeat
        (cbn in *; destruct_conjs; subst;
         try progress_can_form;
         try match goal with
             | [ |- True \/ _] => left; constructor
             | [ |- False \/ _] => right
             | [ |- forall _, _ ] => intro
             | [ H : True |- _ ] => clear H
             | [ H : _ \/ _ |- _ ] => destruct H
             end).

    Local Ltac progress_inst T :=
      match goal with
      | [ IH: (forall (δ : LocalStore (ctx_cat ?Γ ?Δ)), _),
          δ1: LocalStore ?Γ, δ2: LocalStore ?Δ |- _
        ] => specialize (IH (env_cat δ1 δ2)); T
      (* | [ IH: (forall (δ : LocalStore (ctx_snoc ctx_nil (?x , ?σ))), _), *)
      (*     v: Lit ?σ |- _ *)
      (*   ] => specialize (IH (env_snoc env_nil x σ v)); T *)
      | [ IH: (forall (δ : LocalStore ?Γ), _), δ: LocalStore ?Γ |- _
        ] => solve [ specialize (IH δ); T | clear IH; T ]
      end.

    Local Ltac progress_tac :=
      progress_simpl;
      solve
        [ repeat eexists; constructor; eauto
        | progress_inst progress_tac
        ].

    Lemma progress {Γ σ} (s : Stm Γ σ) :
      Final s \/ forall δ, exists δ' s', ⟨ δ , s ⟩ ---> ⟨ δ' , s' ⟩.
    Proof. induction s; intros; try progress_tac. Qed.

  End SmallStep.

  Section Predicates.

    Variable CEnv : ContractEnv.

    Definition Cont (R A : Type) : Type := (A -> R) -> R.

    Definition DST (Γ₁ Γ₂ : Ctx (𝑿 * Ty)) (A : Type) : Type :=
      (A -> Pred (LocalStore Γ₂)) -> Pred (LocalStore Γ₁).

    Definition evalDST {Γ₁ Γ₂ A} (m : DST Γ₁ Γ₂ A) :
      LocalStore Γ₁ -> Cont Prop A :=
      fun δ₁ k => m (fun a δ₂ => k a) δ₁.

    Definition lift {Γ A} (m : Cont Prop A) : DST Γ Γ A :=
      fun k δ => m (fun a => k a δ).

    Definition pure {Γ A} (a : A) : DST Γ Γ A :=
      fun k => k a.
    Definition ap {Γ₁ Γ₂ Γ₃ A B} (mf : DST Γ₁ Γ₂ (A -> B))
               (ma : DST Γ₂ Γ₃ A) : DST Γ₁ Γ₃ B :=
      fun k => mf (fun f => ma (fun a => k (f a))).
    Definition abort {Γ₁ Γ₂ A} : DST Γ₁ Γ₂ A :=
      fun k δ => False.
    Definition assert {Γ} (b : bool) : DST Γ Γ bool :=
      fun k δ => Bool.Is_true b /\ k b δ.
    Definition bind {Γ₁ Γ₂ Γ₃ A B} (ma : DST Γ₁ Γ₂ A) (f : A -> DST Γ₂ Γ₃ B) : DST Γ₁ Γ₃ B :=
      fun k => ma (fun a => f a k).
    Definition bindright {Γ₁ Γ₂ Γ₃ A B} (ma : DST Γ₁ Γ₂ A) (mb : DST Γ₂ Γ₃ B) : DST Γ₁ Γ₃ B :=
      bind ma (fun _ => mb).
    Definition bindleft {Γ₁ Γ₂ Γ₃ A B} (ma : DST Γ₁ Γ₂ A) (mb : DST Γ₂ Γ₃ B) : DST Γ₁ Γ₃ A :=
      bind ma (fun a => bind mb (fun _ => pure a)).
    Definition get {Γ} : DST Γ Γ (LocalStore Γ) :=
      fun k δ => k δ δ.
    Definition put {Γ Γ'} (δ' : LocalStore Γ') : DST Γ Γ' unit :=
      fun k _ => k tt δ'.
    Definition modify {Γ Γ'} (f : LocalStore Γ -> LocalStore Γ') : DST Γ Γ' unit :=
      bind get (fun δ => put (f δ)).
    Definition meval {Γ σ} (e : Exp Γ σ) : DST Γ Γ (Lit σ) :=
      bind get (fun δ => pure (eval e δ)).
    Definition mevals {Γ Δ} (es : Env' (Exp Γ) Δ) : DST Γ Γ (Env' Lit Δ) :=
      bind get (fun δ => pure (evals es δ)).
    Definition push {Γ x σ} (v : Lit σ) : DST Γ (ctx_snoc Γ (x , σ)) unit :=
      modify (fun δ => env_snoc δ (x,σ) v).
    Definition pop {Γ x σ} : DST (ctx_snoc Γ (x , σ)) Γ unit :=
      modify (fun δ => env_tail δ).
    Definition pushs {Γ Δ} (δΔ : LocalStore Δ) : DST Γ (ctx_cat Γ Δ) unit :=
      modify (fun δΓ => env_cat δΓ δΔ).
    Definition pops {Γ} Δ : DST (ctx_cat Γ Δ) Γ unit :=
      modify (fun δΓΔ => env_drop Δ δΓΔ).

    Notation "ma >>= f" := (bind ma f) (at level 90, left associativity).
    Notation "ma *> mb" := (bindright ma mb) (at level 90, left associativity).
    Notation "ma <* mb" := (bindleft ma mb) (at level 90, left associativity).

    (* Version that computes *)
    Definition IsLit {Γ σ} (δ : LocalStore Γ) (s : Stm Γ σ) :
      forall (POST : Lit σ -> Pred (LocalStore Γ)), Prop :=
      match s with
      | stm_lit _ v => fun POST => POST v δ
      | _ => fun _ => False
      end.

    Lemma IsLit_inversion {Γ σ} (δ : LocalStore Γ) (s : Stm Γ σ)
          (POST : Lit σ -> Pred (LocalStore Γ)) :
      IsLit δ s POST -> exists v, s = stm_lit _ v /\ POST v δ.
    Proof. destruct s; cbn in *; try contradiction; eauto. Qed.

    Fixpoint WLP {Γ τ} (s : Stm Γ τ) : DST Γ Γ (Lit τ) :=
      match s in (Stm _ τ) return (DST Γ Γ (Lit τ)) with
      | stm_lit _ l => pure l
      | stm_assign x e => meval e >>= fun v => modify (fun δ => δ [ x ↦ v ]) *> pure v
      | stm_let x σ s k => WLP s >>= push *> WLP k <* pop
      | stm_exp e => meval e
      | stm_assert e1 e2  => meval e1 >>= assert
      | stm_if e s1 s2 => meval e >>= fun b => if b then WLP s1 else WLP s2
      | stm_exit _ _  => abort
      | stm_seq s1 s2 => WLP s1 *> WLP s2
      | stm_app' Δ δ τ s => lift (evalDST (WLP s) δ)

      | stm_app f es =>
        mevals es >>= fun δf_in =>
        match CEnv f with
        | None => abort (* NOT IMPLEMENTED *)
        | Some c => fun POST δ =>
                      contract_pre_condition c δf_in
                      /\ (forall v, contract_post_condition c v δf_in -> POST v δ)
        end
      | stm_let' δ k => pushs δ *> WLP k <* pops _
      | stm_match_list e alt_nil xh xt alt_cons =>
        meval e >>= fun v =>
        match v with
        | nil => WLP alt_nil
        | cons vh vt => push vh *> @push _ _ (ty_list _) vt *> WLP alt_cons <* pop <* pop
        end
      | stm_match_sum e xinl altinl xinr altinr =>
        meval e >>= fun v =>
        match v with
        | inl v => push v *> WLP altinl <* pop
        | inr v => push v *> WLP altinr <* pop
        end
      | stm_match_pair e xl xr rhs =>
        meval e >>= fun v =>
        let (vl , vr) := v in
        push vl *> push vr *> WLP rhs <* pop <* pop
      | stm_match_tuple e p rhs =>
        meval e >>= fun v =>
        pushs (tuple_pattern_match p v) *> WLP rhs <* pops _
      | stm_match_union e xs rhs =>
        meval e >>= fun v =>
        let (K , tv) := v in
        push (untag tv) *> WLP (rhs K) <* pop
      | stm_match_record R e p rhs =>
        meval e >>= fun v =>
        pushs (record_pattern_match p v) *> WLP rhs <* pops _
      end.

    Notation "'⟨' δ1 ',' s1 '⟩' '--->' '⟨' δ2 ',' s2 '⟩'" := (@Step _ _ δ1 δ2 s1 s2).
    Notation "'⟨' δ1 ',' s1 '⟩' --->* '⟨' δ2 ',' s2 '⟩'" := (@Steps _ _ δ1 s1 δ2 s2).

    Section Soundness.

      Local Ltac steps_inversion_simpl :=
        repeat
          (try match goal with
               | [ H: exists t, _ |- _ ] => destruct H
               | [ H: _ /\ _ |- _ ] => destruct H
               | [ H: existT _ _ _ = existT _ _ _ |- _ ] => dependent destruction H
               | [ H : False |- _ ] => destruct H
               end;
           cbn in *).

      Local Ltac extend p :=
        let P := type of p in
        match goal with
        | [ _ : P |- _ ] => fail 1
        | _ => pose proof p
        end.

      Local Ltac steps_inversion_inster :=
        repeat
          (try match goal with
               | [ H : forall _, _ = _ -> _ |- _ ]
                 => specialize (H _ eq_refl)
               | [ H : forall _ _, _ = _ -> _ |- _ ]
                 => specialize (H _ _ eq_refl)
               | [ H : forall _ _ _, _ = _ -> _ |- _ ]
                 => specialize (H _ _ _ eq_refl)
               | [ H : Final ?s -> _, H' : Final ?s |- _ ]
                 => specialize (H H')
               | [ H1 : ⟨ ?δ1, ?s1 ⟩ ---> ⟨ ?δ2, ?s2 ⟩,
                   H2 : ⟨ ?δ2, ?s2 ⟩ --->* ⟨ ?δ3, ?s3 ⟩ |- _ ]
                 => extend (step_trans H1 H2)
               end;
           steps_inversion_simpl).

      Local Ltac steps_inversion_solve :=
        repeat
          (match goal with
           | [ |- exists t, _ ] => eexists
           | [ |- _ /\ _ ] => constructor
           | [ |- True ] => constructor
           | [ |- ⟨ _ , stm_lit _ _ ⟩ --->* ⟨ _, _ ⟩ ] => constructor 1
           | [ |- ⟨ _ , stm_exit _ _ ⟩ --->* ⟨ _, _ ⟩ ] => constructor 1
           | [ |- ⟨ _ , stm_let _ _ (stm_lit _ _) _ ⟩ ---> ⟨ _ , _ ⟩ ] => apply step_stm_let_value
           | [ |- ⟨ _ , stm_let _ _ (stm_exit _ _) _ ⟩ ---> ⟨ _ , _ ⟩ ] => apply step_stm_let_exit
           end; cbn); eauto.

      Local Ltac steps_inversion_induction :=
        let step := fresh in
        induction 1 as [|? ? ? ? ? ? step]; intros; subst;
          [ steps_inversion_simpl
          | inversion step; steps_inversion_inster; steps_inversion_solve
          ].

      Lemma steps_inversion_let {Γ x τ σ} {δ1 δ3 : LocalStore Γ}
        {s1 : Stm Γ τ} {s2 : Stm (ctx_snoc Γ (x, τ)) σ} {t : Stm Γ σ} (final : Final t)
        (steps : ⟨ δ1, stm_let x τ s1 s2 ⟩ --->* ⟨ δ3, t ⟩) :
        exists (δ2 : LocalStore Γ) (s1' : Stm Γ τ),
        (⟨ δ1, s1 ⟩ --->* ⟨ δ2, s1' ⟩) /\ Final s1' /\
        (exists (s0 : Stm Γ σ),
            (⟨ δ2, stm_let x τ s1' s2 ⟩ ---> ⟨ δ2, s0 ⟩) /\ ⟨ δ2, s0 ⟩ --->* ⟨ δ3, t ⟩).
      Proof.
        remember (stm_let x τ s1 s2) as s. revert steps s1 s2 Heqs.
        steps_inversion_induction.
      Qed.

      Lemma steps_inversion_let' {Γ Δ σ} (δ1 δ3 : LocalStore Γ)
        (δΔ : LocalStore Δ) (k : Stm (ctx_cat Γ Δ) σ) (t : Stm Γ σ) (final : Final t)
        (steps : ⟨ δ1, stm_let' δΔ k ⟩ --->* ⟨ δ3, t ⟩) :
        exists δ2 δΔ' k',
          ⟨ env_cat δ1 δΔ , k ⟩ --->* ⟨ env_cat δ2 δΔ' , k' ⟩ /\ Final k' /\
          exists (s0 : Stm Γ σ),
            (⟨ δ2, stm_let' δΔ' k' ⟩ ---> ⟨ δ2, s0 ⟩) /\ (⟨ δ2, s0 ⟩ --->* ⟨ δ3, t ⟩).
      Proof.
        remember (stm_let' δΔ k) as s. revert steps δΔ k Heqs.
        steps_inversion_induction.
      Qed.

      Lemma steps_inversion_seq {Γ τ σ} (δ1 δ3 : LocalStore Γ)
        (s1 : Stm Γ τ) (s2 : Stm Γ σ) (t : Stm Γ σ) (final : Final t)
        (steps : ⟨ δ1, stm_seq s1 s2 ⟩ --->* ⟨ δ3, t ⟩) :
        exists δ2 s1',
          ⟨ δ1, s1 ⟩ --->* ⟨ δ2, s1' ⟩ /\ Final s1' /\
          exists (s0 : Stm Γ σ),
            (⟨ δ2, stm_seq s1' s2 ⟩ ---> ⟨ δ2 , s0 ⟩) /\ (⟨ δ2 , s0 ⟩ --->* ⟨ δ3, t ⟩).
      Proof.
        remember (stm_seq s1 s2) as s. revert steps s1 s2 Heqs.
        steps_inversion_induction.
      Qed.

      Lemma steps_inversion_app' {Γ Δ σ} (δ1 δ3 : LocalStore Γ)
        (δΔ : LocalStore Δ) (k : Stm Δ σ) (t : Stm Γ σ) (final : Final t)
        (steps : ⟨ δ1, stm_app' Δ δΔ σ k ⟩ --->* ⟨ δ3, t ⟩) :
        exists δΔ' k',
          ⟨ δΔ , k ⟩ --->* ⟨ δΔ' , k' ⟩ /\ Final k' /\
          exists s0,
          (⟨ δ1, stm_app' Δ δΔ' σ k' ⟩ ---> ⟨ δ1, s0 ⟩) /\ (⟨ δ1, s0⟩ --->* ⟨ δ3, t ⟩).
      Proof.
        remember (stm_app' Δ δΔ σ k) as s. revert steps δΔ k Heqs.
        steps_inversion_induction.
      Qed.

      Definition Triple {Γ τ}
        (PRE : Pred (LocalStore Γ)) (s : Stm Γ τ)
        (POST : Lit τ -> Pred (LocalStore Γ)) : Prop :=
        forall (δ δ' : LocalStore Γ) (v : Lit τ),
          ⟨ δ , s ⟩ --->* ⟨ δ' , stm_lit τ v ⟩ ->
          PRE δ ->
          POST v δ'.

      Ltac wlp_sound_steps_inversion :=
        repeat
          match goal with
          | [ H: ⟨ _, stm_app _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>               dependent destruction H
          | [ H: ⟨ _, stm_app _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>              dependent destruction H
          | [ H: ⟨ _, stm_assert _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>            dependent destruction H
          | [ H: ⟨ _, stm_assert _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>           dependent destruction H
          | [ H: ⟨ _, stm_assign _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>            dependent destruction H
          | [ H: ⟨ _, stm_assign _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>           dependent destruction H
          | [ H: ⟨ _, stm_exit _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>              dependent destruction H
          | [ H: ⟨ _, stm_exit _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>             dependent destruction H
          | [ H: ⟨ _, stm_exp _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>                 dependent destruction H
          | [ H: ⟨ _, stm_exp _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>                dependent destruction H
          | [ H: ⟨ _, stm_if _ _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>              dependent destruction H
          | [ H: ⟨ _, stm_if _ _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>             dependent destruction H
          | [ H: ⟨ _, stm_lit _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>               dependent destruction H
          | [ H: ⟨ _, stm_lit _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>              dependent destruction H
          | [ H: ⟨ _, stm_match_sum _ _ _ _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>   dependent destruction H
          | [ H: ⟨ _, stm_match_sum _ _ _ _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>  dependent destruction H
          | [ H: ⟨ _, stm_match_list _ _ _ _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>  dependent destruction H
          | [ H: ⟨ _, stm_match_list _ _ _ _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] => dependent destruction H
          | [ H: ⟨ _, stm_match_pair _ _ _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>    dependent destruction H
          | [ H: ⟨ _, stm_match_pair _ _ _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>   dependent destruction H
          | [ H: ⟨ _, stm_match_tuple _ _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>     dependent destruction H
          | [ H: ⟨ _, stm_match_tuple _ _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>    dependent destruction H
          | [ H: ⟨ _, stm_match_union _ _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>       dependent destruction H
          | [ H: ⟨ _, stm_match_union _ _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] =>      dependent destruction H
          | [ H: ⟨ _, stm_match_record _ _ _ _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>  dependent destruction H
          | [ H: ⟨ _, stm_match_record _ _ _ _ ⟩ --->* ⟨ _, _ ⟩ |- _ ] => dependent destruction H

          | [ H: ⟨ _, stm_app' _ _ _ (stm_lit _ _) ⟩ ---> ⟨ _, _ ⟩ |- _ ] => dependent destruction H
          | [ H: ⟨ _, stm_let _ _ (stm_lit _ _) _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>  dependent destruction H
          | [ H: ⟨ _, stm_let' _ (stm_lit _ _) ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>     dependent destruction H
          | [ H: ⟨ _, stm_seq (stm_lit _ _) _ ⟩ ---> ⟨ _, _ ⟩ |- _ ] =>      dependent destruction H

          | [ H: ⟨ _, stm_app' _ _ _ _ ⟩ --->* ⟨ _, ?s1 ⟩, HF: Final ?s1 |- _ ] => apply (steps_inversion_app' HF) in H
          | [ H: ⟨ _, stm_let _ _ _ _ ⟩ --->* ⟨ _, ?s1 ⟩, HF: Final ?s1 |- _ ] =>  apply (steps_inversion_let HF) in H
          | [ H: ⟨ _, stm_let' _ _ ⟩ --->* ⟨ _, ?s1 ⟩, HF: Final ?s1 |- _ ] =>     apply (steps_inversion_let' HF) in H
          | [ H: ⟨ _, stm_seq _ _ ⟩ --->* ⟨ _, ?s1 ⟩, HF: Final ?s1 |- _ ] =>      apply (steps_inversion_seq HF) in H
          | [ H: IsLit _ _ _ |- _ ] => apply IsLit_inversion in H
          end.

      Ltac wlp_sound_inst :=
        match goal with
        | [ IH: forall _ _ _, ⟨ _ , ?s ⟩ --->* ⟨ _ , _ ⟩ -> _,
            HS: ⟨ _ , ?s ⟩ --->* ⟨ _ , ?t ⟩, HF: Final ?t |- _ ] =>
          specialize (IH _ _ _ HS HF); clear HS HF
        | [ IH: forall _ _ _ _, ⟨ _ , _ ⟩ --->* ⟨ _ , _ ⟩ -> _,
            HS: ⟨ _ , _ ⟩ --->* ⟨ _ , ?t ⟩, HF: Final ?t |- _ ] =>
          specialize (IH _ _ _ _ HS HF); clear HS HF
        | [ IH: forall POST, WLP ?s POST ?δ -> _, WP: WLP ?s _ ?δ |- _ ] =>
          specialize (IH _ WP); clear WP
        end.

      Ltac wlp_sound_simpl :=
        repeat
          (cbn in *; destruct_conjs; subst;
           try match goal with
               | [ H: True |- _ ] => clear H
               | [ H: False |- _ ] => destruct H
               | [ H: Env _ (ctx_snoc _ _) |- _ ] =>
                 dependent destruction H
               | [ H: Env _ ctx_nil |- _ ] =>
                 dependent destruction H
               | [ H: context[env_drop _ (_ ►► _)]|- _] =>
                 rewrite env_drop_cat in H
               | [ _: context[match eval ?e ?δ with _ => _ end] |- _ ] =>
                 destruct (eval e δ)
               end).

      Ltac wlp_sound_solve :=
        repeat
          (wlp_sound_steps_inversion;
           wlp_sound_simpl;
           try wlp_sound_inst); auto.

      Definition ValidContractEnv (cenv : ContractEnv) : Prop :=
        forall σs σ (f : 𝑭 σs σ),
          match cenv σs σ f with
          | Some c=>
            forall (δ δ' : LocalStore σs) (s' : Stm σs σ),
              ⟨ δ, fun_body (Pi f) ⟩ --->* ⟨ δ', s' ⟩ ->
              Final s' ->
              contract_pre_condition c δ ->
              IsLit δ s' (contract_post_condition c)
          | None => True
          end.

      Variable validCEnv : ValidContractEnv CEnv.

      Lemma WLP_sound {Γ σ} (s : Stm Γ σ) :
        forall (δ δ' : LocalStore Γ) (s' : Stm Γ σ), ⟨ δ, s ⟩ --->* ⟨ δ', s' ⟩ -> Final s' ->
          forall (POST : Lit σ -> Pred (LocalStore Γ)), WLP s POST δ -> IsLit δ' s' POST.
      Proof.
        induction s; cbn; repeat unfold
          Triple, abort, assert, bind, bindleft, bindright, evalDST, get,
          lift, meval, mevals, modify, pop, pops, pure, push, pushs, put;
        intros.
        - wlp_sound_solve.
        - wlp_sound_solve.
        - wlp_sound_solve.
        - wlp_sound_solve.
        - wlp_sound_solve.
        - pose proof (validCEnv f).
          destruct (CEnv f); wlp_sound_solve.
          intuition.
          wlp_sound_solve.
        - wlp_sound_solve.
        - wlp_sound_solve.
        - wlp_sound_solve.
        - wlp_sound_solve.
        - wlp_sound_solve.
        - wlp_sound_solve.
        - wlp_sound_solve.
        - wlp_sound_solve.
        - wlp_sound_solve.
        - wlp_sound_solve.
        - wlp_sound_solve.
      Qed.

    End Soundness.

  End Predicates.

End ProgramKit.
