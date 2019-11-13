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

From MicroSail Require Export
     Context
     Environment
     Notation.

Set Implicit Arguments.

Module Type TypeKit.

  (* Names of enum type constructors. *)
  Parameter Inline 𝑬 : Set. (* input: \MIE *)
  (* Names of union type constructors. *)
  Parameter Inline 𝑻   : Set. (* input: \MIT *)
  (* Names of record type constructors. *)
  Parameter Inline 𝑹  : Set. (* input: \MIR *)
  (* Names of expression variables. *)
  Parameter Inline 𝑿 : Set. (* input: \MIX *)
  (* For name resolution we rely on decidable equality of expression
     variables. The functions in this module resolve to the closest binding
     of an equal name and fill in the de Bruijn index automatically from
     a successful resolution.
  *)
  Parameter Inline 𝑿_eq_dec : forall x y : 𝑿, {x=y}+{~x=y}.

End TypeKit.

Module Types (Export typekit : TypeKit).

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
  (* Experimental features. These are still in flux. *)
  | ty_tuple (σs : Ctx Ty)
  | ty_union (T : 𝑻)
  | ty_record (R : 𝑹)
  .

End Types.

(******************************************************************************)

Module Type TermKit (typekit : TypeKit).
  Module TY := Types typekit.
  Export TY.

  (* Names of enum data constructors. *)
  Parameter Inline 𝑬𝑲 : 𝑬 -> Set.
  (* Names of union data constructors. *)
  Parameter Inline 𝑲  : 𝑻 -> Set.
  (* Union data constructor field type *)
  Parameter Inline 𝑲_Ty : forall (T : 𝑻), 𝑲 T -> Ty.
  (* Record field names. *)
  Parameter Inline 𝑹𝑭  : Set.
  (* Record field types. *)
  Parameter Inline 𝑹𝑭_Ty : 𝑹 -> Ctx (𝑹𝑭 * Ty).

  (* Names of functions. *)
  Parameter Inline 𝑭  : Ctx (𝑿 * Ty) -> Ty -> Set.

End TermKit.

Module Terms (typekit : TypeKit) (termkit : TermKit typekit).
  Export termkit.

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
    | taglit_prod   σ1 σ2  : TaggedLit σ1 * TaggedLit σ2 -> TaggedLit (ty_prod σ1 σ2)
    | taglit_sum    σ1 σ2  : TaggedLit σ1 + TaggedLit σ2 -> TaggedLit (ty_sum σ1 σ2)
    | taglit_unit          : TaggedLit (ty_unit)
    | taglit_enum (E : 𝑬) (K : 𝑬𝑲 E) : TaggedLit (ty_enum E)
    (* Experimental features *)
    | taglit_tuple σs      : Env TaggedLit σs -> TaggedLit (ty_tuple σs)
    | taglit_union (T : 𝑻) (K : 𝑲 T) : TaggedLit (𝑲_Ty K) -> TaggedLit (ty_union T)
    | taglit_record (R : 𝑹) : Env' TaggedLit (𝑹𝑭_Ty R) -> TaggedLit (ty_record R).

    Global Arguments taglit_enum : clear implicits.
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
      | ty_prod σ1 σ2 => Lit σ1 * Lit σ2
      | ty_sum σ1 σ2 => Lit σ1 + Lit σ2
      | ty_unit => unit
      | ty_enum E => 𝑬𝑲 E
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
      | taglit_enum E K     => K
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
      | ty_enum E => taglit_enum E
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
    | exp_plus    (e1 e2 : Exp Γ ty_int) : Exp Γ ty_int
    | exp_times   (e1 e2 : Exp Γ ty_int) : Exp Γ ty_int
    | exp_minus   (e1 e2 : Exp Γ ty_int) : Exp Γ ty_int
    | exp_neg     (e : Exp Γ ty_int) : Exp Γ ty_int
    | exp_eq      (e1 e2 : Exp Γ ty_int) : Exp Γ ty_bool
    | exp_le      (e1 e2 : Exp Γ ty_int) : Exp Γ ty_bool
    | exp_lt      (e1 e2 : Exp Γ ty_int) : Exp Γ ty_bool
    | exp_gt      (e1 e2 : Exp Γ ty_int) : Exp Γ ty_bool
    | exp_and     (e1 e2 : Exp Γ ty_bool) : Exp Γ ty_bool
    | exp_not     (e : Exp Γ ty_bool) : Exp Γ ty_bool
    | exp_pair    {σ1 σ2 : Ty} (e1 : Exp Γ σ1) (e2 : Exp Γ σ2) : Exp Γ (ty_prod σ1 σ2)
    | exp_inl     {σ1 σ2 : Ty} : Exp Γ σ1 -> Exp Γ (ty_sum σ1 σ2)
    | exp_inr     {σ1 σ2 : Ty} : Exp Γ σ2 -> Exp Γ (ty_sum σ1 σ2)
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
    Bind Scope exp_scope with Exp.

    Global Arguments exp_var {_} _ {_ _}.
    Global Arguments exp_tuple {_ _} _%exp.
    Global Arguments exp_union {_} _ _.
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
      | exp_eq e1 e2 => taglit_bool (untag (evalTagged e1 δ) =? untag (evalTagged e2 δ))%Z
      | exp_le e1 e2 => taglit_bool (untag (evalTagged e1 δ) <=? untag (evalTagged e2 δ))%Z
      | exp_lt e1 e2 => taglit_bool (untag (evalTagged e1 δ) <? untag (evalTagged e2 δ))%Z
      | exp_gt e1 e2 => taglit_bool (untag (evalTagged e1 δ) >? untag (evalTagged e2 δ))%Z
      | exp_and e1 e2 => taglit_bool (untag (evalTagged e1 δ) && untag (evalTagged e2 δ))
      | exp_not e0 => taglit_bool (negb (untag (evalTagged e0 δ)))
      | @exp_pair _ σ1 σ2 e1 e2 => taglit_prod (evalTagged e1 δ, evalTagged e2 δ)
      | @exp_inl _ σ1 σ2 e0 => taglit_sum (inl (evalTagged e0 δ))
      | @exp_inr _ σ1 σ2 e0 => taglit_sum (inr (evalTagged e0 δ))
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
      | exp_plus e1 e2      => Z.add (eval e1 δ) (eval e2 δ)
      | exp_times e1 e2     => Z.mul (eval e1 δ) (eval e2 δ)
      | exp_minus e1 e2     => Z.sub (eval e1 δ) (eval e2 δ)
      | exp_neg e           => Z.opp (eval e δ)
      | exp_eq e1 e2        => Z.eqb (eval e1 δ) (eval e2 δ)
      | exp_le e1 e2        => Z.leb (eval e1 δ) (eval e2 δ)
      | exp_lt e1 e2        => Z.ltb (eval e1 δ) (eval e2 δ)
      | exp_gt e1 e2        => Z.gtb (eval e1 δ) (eval e2 δ)
      | exp_and e1 e2       => andb (eval e1 δ) (eval e2 δ)
      | exp_not e           => negb (eval e δ)
      | exp_pair e1 e2      => pair (eval e1 δ) (eval e2 δ)
      | exp_inl e           => inl (eval e δ)
      | exp_inr e           => inr (eval e δ)
      | exp_list es         => List.map (fun e => eval e δ) es
      | exp_cons e1 e2      => cons (eval e1 δ) (eval e2 δ)
      | exp_nil _           => nil
      | exp_tuple es        => env_map (fun τ e => evalTagged e δ) es
      | @exp_projtup _ σs e n σ p => untag (env_lookup (eval e δ) (Build_InCtx _ _ n p))
      | exp_union T K e     => existT _ K (evalTagged e δ)
      | exp_record R es     => env_map (fun τ e => evalTagged e δ) es
      | exp_projrec e rf    => untag (eval e δ ! rf)
      | exp_builtin f e     => f (eval e δ)
      end.

    Definition evals {Γ Δ} (es : Env' (Exp Γ) Δ) (δ : LocalStore Γ) : LocalStore Δ :=
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

    Inductive Stm (Γ : Ctx (𝑿 * Ty)) : Ty -> Set :=
    | stm_lit        {τ : Ty} (l : Lit τ) : Stm Γ τ
    | stm_exp        {τ : Ty} (e : Exp Γ τ) : Stm Γ τ
    | stm_let        (x : 𝑿) (τ : Ty) (s : Stm Γ τ) {σ : Ty} (k : Stm (ctx_snoc Γ (x , τ)) σ) : Stm Γ σ
    | stm_let'       (Δ : Ctx (𝑿 * Ty)) (δ : LocalStore Δ) {σ : Ty} (k : Stm (ctx_cat Γ Δ) σ) : Stm Γ σ
    | stm_assign     (x : 𝑿) (τ : Ty) {xInΓ : InCtx (x , τ) Γ} (e : Exp Γ τ) : Stm Γ τ
    | stm_app        {Δ σ} (f : 𝑭 Δ σ) (es : Env' (Exp Γ) Δ) : Stm Γ σ
    | stm_app'       (Δ : Ctx (𝑿 * Ty)) (δ : LocalStore Δ) (τ : Ty) (s : Stm Δ τ) : Stm Γ τ
    | stm_if         {τ : Ty} (e : Exp Γ ty_bool) (s1 s2 : Stm Γ τ) : Stm Γ τ
    | stm_seq        {τ : Ty} (e : Stm Γ τ) {σ : Ty} (k : Stm Γ σ) : Stm Γ σ
    | stm_assert     (e1 : Exp Γ ty_bool) (e2 : Exp Γ ty_string) : Stm Γ ty_bool
    (* | stm_while      (w : 𝑾 Γ) (e : Exp Γ ty_bool) {σ : Ty} (s : Stm Γ σ) -> Stm Γ ty_unit *)
    | stm_exit       (τ : Ty) (s : Lit ty_string) : Stm Γ τ
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
      (p : RecordPat (𝑹𝑭_Ty R) Δ) {τ : Ty} (rhs : Stm (ctx_cat Γ Δ) τ) : Stm Γ τ
    | stm_bind   {σ τ : Ty} (s : Stm Γ σ) (k : Lit σ -> Stm Γ τ) : Stm Γ τ.

    Global Arguments stm_lit {_} _ _.
    Global Arguments stm_exp {_ _} _.
    Global Arguments stm_let {_} _ _ _ {_} _.
    Global Arguments stm_let' {_ _} _ {_} _.
    Global Arguments stm_assign {_} _ {_ _} _.
    Global Arguments stm_app {_%ctx _%ctx _} _ _%exp.
    Global Arguments stm_app' {_} _ _ _ _.
    Global Arguments stm_if {_ _} _ _ _.
    Global Arguments stm_seq {_ _} _ {_} _.
    Global Arguments stm_assert {_} _ _.
    Global Arguments stm_exit {_} _ _.
    Global Arguments stm_match_list {_ _ _} _ _ _ _ _.
    Global Arguments stm_match_sum {_ _ _ _} _ _ _ _ _.
    Global Arguments stm_match_pair {_ _ _ _} _ _ _ _.
    Global Arguments stm_match_enum {_} _ _ {_} _.
    Global Arguments stm_match_tuple {_ _ _} _ _%pat {_} _.
    Global Arguments stm_match_union {_} _ _ {_} _ _.
    Global Arguments stm_match_record {_} _ {_} _ _ {_} _.

  End Statements.

  Section PatternMatching.

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

  End PatternMatching.

  (* Record FunDef (Δ : Ctx (𝑿 * Ty)) (τ : Ty) : Set := *)
  (*   { fun_body : Stm Δ τ }. *)

  Module NameResolution.

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
        return (forall p, InCtx (x, fromSome (if s then Some d else ctx_resolve Γ x) p)
                                (ctx_snoc Γ (y, d)))
        with
        | left e => fun _ => match e with | eq_refl => inctx_zero end
        | right _ => fun p => inctx_succ (mk_inctx Γ x p)
        end
      end.

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
      Exp Γ (fromSome (ctx_resolve Γ x) p) -> Stm Γ (fromSome (ctx_resolve Γ x) p) :=
      @stm_assign Γ x (fromSome _ p) (mk_inctx Γ x p).

    (* Instead we hook mk_inctx directly into the typeclass resolution mechanism.
       Apparently, the unification of Γ is performed before the resolution so
       evaluation of ctx_resolve and mk_inctx is not blocked.
     *)
    Hint Extern 10 (InCtx (?x , _) ?Γ) => exact (mk_inctx Γ x tt) : typeclass_instances.

  End NameResolution.

  Section Contracts.

    Definition Pred (A : Set) : Type := A -> Prop.

    Definition Final {Γ σ} (s : Stm Γ σ) : Prop :=
      match s with
      | stm_lit _ _  => True
      | stm_exit _ _ => True
      | _ => False
      end.

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

    Record Contract (Δ : Ctx (𝑿 * Ty)) (τ : Ty) : Type :=
      { contract_pre_condition  : Pred (Env' Lit Δ);
        contract_post_condition : Lit τ -> Pred (Env' Lit Δ)
      }.

    Definition ContractEnv : Type :=
      forall Δ τ (f : 𝑭 Δ τ), option (Contract Δ τ).

  End Contracts.

End Terms.

(******************************************************************************)

Module Type ProgramKit
       (Import typekit : TypeKit)
       (Import termkit : TermKit typekit).
  Module TM := Terms typekit termkit.
  Export TM.

  (* Parameter Inline Pi : forall {Δ τ} (f : 𝑭 Δ τ), FunDef Δ τ. *)
  Parameter Inline Pi : forall {Δ τ} (f : 𝑭 Δ τ), Stm Δ τ.

End ProgramKit.

Module Type ContractKit
       (Import typekit : TypeKit)
       (Import termkit : TermKit typekit)
       (Import progkit : ProgramKit typekit termkit).

  Parameter Inline CEnv : ContractEnv.

End ContractKit.
