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

Local Set Implicit Arguments.
Local Unset Transparent Obligations.
Obligation Tactic := idtac.

Inductive Bit : Set := bitzero | bitone.

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
  {| blast ab k := k (existT B (projT1 ab) (projT2 ab)) |}.
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
Instance blastable_env' {X T : Set} {D} {Δ : Ctx (X * T)} : Blastable (Env' D Δ) :=
  blastable_env.

Module Type TypeKit.

  (* Names of enum type constructors. *)
  Parameter Inline 𝑬 : Set. (* input: \MIE *)
  Parameter Inline 𝑬_eq_dec : forall x y : 𝑬, {x=y}+{~x=y}.
  (* Names of union type constructors. *)
  Parameter Inline 𝑼   : Set. (* input: \MIT *)
  Parameter Inline 𝑼_eq_dec : forall x y : 𝑼, {x=y}+{~x=y}.
  (* Names of record type constructors. *)
  Parameter Inline 𝑹  : Set. (* input: \MIR *)
  Parameter Inline 𝑹_eq_dec : forall x y : 𝑹, {x=y}+{~x=y}.
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
  (* Experimental features. These are still in flux. *)
  | ty_tuple (σs : Ctx Ty)
  | ty_union (U : 𝑼)
  | ty_record (R : 𝑹)
  .

  Section ty_rect.
    Variable P  : Ty -> Type.
    Variable PS : Ctx Ty -> Type.

    Hypothesis (P_int    : P ty_int).
    Hypothesis (P_bool   : P ty_bool).
    Hypothesis (P_bit    : P ty_bit).
    Hypothesis (P_string : P ty_string).
    Hypothesis (P_list   : forall σ, P σ -> P (ty_list σ)).
    Hypothesis (P_prod   : forall σ τ, P σ -> P τ -> P (ty_prod σ τ)).
    Hypothesis (P_sum    : forall σ τ, P σ -> P τ -> P (ty_sum σ τ)).
    Hypothesis (P_unit   : P ty_unit).
    Hypothesis (P_enum   : forall E, P (ty_enum E)).
    Hypothesis (P_tuple  : forall σs, PS σs -> P (ty_tuple σs)).
    Hypothesis (P_union  : forall U, P (ty_union U)).
    Hypothesis (P_record : forall R, P (ty_record R)).
    Hypothesis (PS_nil   : PS ctx_nil).
    Hypothesis (PS_snoc  : forall σs σ, PS σs -> P σ -> PS (ctx_snoc σs σ)).

    Fixpoint ty_rect (σ : Ty) : P σ :=
      match σ as t return (P t) with
      | ty_int => P_int
      | ty_bool => P_bool
      | ty_bit => P_bit
      | ty_string => P_string
      | ty_list σ0 => P_list (ty_rect σ0)
      | ty_prod σ1 σ2 => P_prod (ty_rect σ1) (ty_rect σ2)
      | ty_sum σ1 σ2 => P_sum (ty_rect σ1) (ty_rect σ2)
      | ty_unit => P_unit
      | ty_enum E => P_enum E
      | ty_tuple σs => P_tuple (Ctx_rect PS PS_nil (fun σs PS_σs σ => PS_snoc PS_σs (ty_rect σ)) σs)
      | ty_union U => P_union U
      | ty_record R => P_record R
      end.

  End ty_rect.

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
    Hypothesis (P_tuple  : forall σs, (forall σ, InCtx σ σs -> P σ) -> P (ty_tuple σs)).
    Hypothesis (P_union  : forall U, P (ty_union U)).
    Hypothesis (P_record : forall R, P (ty_record R)).

    Lemma Ty_rect : forall σ, P σ.
      apply (ty_rect P (fun σs => forall σ, InCtx σ σs -> P σ)); try assumption.
      - intros. apply (inctx_case_nil H).
      - intros. now apply (inctx_case_snoc P) in H.
    Defined.

  End Ty_rect.

  Definition Ty_rec (P : Ty -> Set) := Ty_rect P.
  Definition Ty_ind (P : Ty -> Prop) := Ty_rect P.

  Lemma Ty_eq_dec : forall x y : Ty, {x=y}+{~x=y}.
  Proof.
    decide equality; auto using 𝑬_eq_dec, 𝑼_eq_dec, 𝑹_eq_dec.
    revert σs H. rename σs0 into τs.
    induction τs; intros; destruct σs.
    - left. reflexivity.
    - right. discriminate.
    - right. discriminate.
    - specialize (IHτs σs (fun σ σInσs => H σ (inctx_succ σInσs))).
      specialize (H b0 inctx_zero b).
      intuition congruence.
  Qed.

End Types.

(******************************************************************************)

Module Type TermKit (typekit : TypeKit).
  Module TY := Types typekit.
  Export TY.

  (* Names of enum data constructors. *)
  Parameter Inline 𝑬𝑲 : 𝑬 -> Set.
  Declare Instance Blastable_𝑬𝑲 : forall E, Blastable (𝑬𝑲 E).

  (* Names of union data constructors. *)
  Parameter Inline 𝑼𝑲  : 𝑼 -> Set.
  (* Union data constructor field type *)
  Parameter Inline 𝑼𝑲_Ty : forall (U : 𝑼), 𝑼𝑲 U -> Ty.
  Declare Instance Blastable_𝑼𝑲 : forall U, Blastable (𝑼𝑲 U).

  (* Record field names. *)
  Parameter Inline 𝑹𝑭  : Set.
  (* Record field types. *)
  Parameter Inline 𝑹𝑭_Ty : 𝑹 -> Ctx (𝑹𝑭 * Ty).

  (* Names of functions. *)
  Parameter Inline 𝑭  : Ctx (𝑿 * Ty) -> Ty -> Set.

  (* Names of registers. *)
  Parameter Inline 𝑹𝑬𝑮 : Ty -> Set.

  (* Memory addresses. *)
  Parameter Inline 𝑨𝑫𝑫𝑹 : Set.

End TermKit.

Module Terms (typekit : TypeKit) (termkit : TermKit typekit).
  Export termkit.

  Section Literals.

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
    Inductive TaggedLit : Ty -> Type :=
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
    | taglit_union (U : 𝑼) (K : 𝑼𝑲 U) : TaggedLit (𝑼𝑲_Ty K) -> TaggedLit (ty_union U)
    | taglit_record (R : 𝑹) : Env' TaggedLit (𝑹𝑭_Ty R) -> TaggedLit (ty_record R).

    Global Arguments taglit_enum : clear implicits.
    Global Arguments taglit_tuple {_} _.
    Global Arguments taglit_union {_} _ _.
    Global Arguments taglit_record : clear implicits.

    Fixpoint Lit (σ : Ty) : Type :=
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
      | ty_union U => { K : 𝑼𝑲 U & TaggedLit (𝑼𝑲_Ty K) }
      | ty_record R => Env' TaggedLit (𝑹𝑭_Ty R)
      end%type.

    Global Instance blastable_lit {σ} : Blastable (Lit σ) :=
      match σ with
      | ty_int => blastable_int
      | ty_bool => blastable_bool
      | ty_bit => blastable_bit
      | ty_string => blastable_string
      | ty_list σ0 => blastable_list
      | ty_prod σ1 σ2 => blastable_prod
      | ty_sum σ1 σ2 => blastable_sum
      | ty_unit => blastable_unit
      | ty_enum E => Blastable_𝑬𝑲 E
      | ty_tuple σs => blastable_env
      | ty_union T => blastable_sigt
      | ty_record R => blastable_env'
      end.

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
  Bind Scope lit_scope with TaggedLit.
  Bind Scope lit_scope with Lit.

  Definition LocalStore (Γ : Ctx (𝑿 * Ty)) : Type := Env' Lit Γ.
  Bind Scope env_scope with LocalStore.

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
    Inductive Exp (Γ : Ctx (𝑿 * Ty)) : Ty -> Type :=
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
    | exp_or      (e1 e2 : Exp Γ ty_bool) : Exp Γ ty_bool
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
    | exp_union   {U : 𝑼} (K : 𝑼𝑲 U) (e : Exp Γ (𝑼𝑲_Ty K)) : Exp Γ (ty_union U)
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
      | exp_or e1 e2 => taglit_bool (untag (evalTagged e1 δ) || untag (evalTagged e2 δ))
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
      | exp_or e1 e2        => orb (eval e1 δ) (eval e2 δ)
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

    Inductive Stm (Γ : Ctx (𝑿 * Ty)) : Ty -> Type :=
    | stm_lit        {τ : Ty} (l : Lit τ) : Stm Γ τ
    | stm_exp        {τ : Ty} (e : Exp Γ τ) : Stm Γ τ
    | stm_let        (x : 𝑿) (τ : Ty) (s : Stm Γ τ) {σ : Ty} (k : Stm (ctx_snoc Γ (x , τ)) σ) : Stm Γ σ
    | stm_let'       (Δ : Ctx (𝑿 * Ty)) (δ : LocalStore Δ) {σ : Ty} (k : Stm (ctx_cat Γ Δ) σ) : Stm Γ σ
    | stm_assign     (x : 𝑿) (τ : Ty) {xInΓ : InCtx (x , τ) Γ} (e : Stm Γ τ) : Stm Γ τ
    | stm_call       {Δ σ} (f : 𝑭 Δ σ) (es : Env' (Exp Γ) Δ) : Stm Γ σ
    | stm_call'      (Δ : Ctx (𝑿 * Ty)) (δ : LocalStore Δ) (τ : Ty) (s : Stm Δ τ) : Stm Γ τ
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
      (altx : forall (K : 𝑼𝑲 U), 𝑿)
      (alts : forall (K : 𝑼𝑲 U), Stm (ctx_snoc Γ (altx K , 𝑼𝑲_Ty K)) τ) : Stm Γ τ
    | stm_match_record {R : 𝑹} {Δ : Ctx (𝑿 * Ty)} (e : Exp Γ (ty_record R))
      (p : RecordPat (𝑹𝑭_Ty R) Δ) {τ : Ty} (rhs : Stm (ctx_cat Γ Δ) τ) : Stm Γ τ
    | stm_read_register {τ} (reg : 𝑹𝑬𝑮 τ) : Stm Γ τ
    | stm_write_register {τ} (reg : 𝑹𝑬𝑮 τ) (e : Exp Γ τ) : Stm Γ τ
    | stm_read_memory (addr : 𝑨𝑫𝑫𝑹) : Stm Γ ty_int
    | stm_write_memory (addr : 𝑨𝑫𝑫𝑹) (e : Exp Γ ty_int) : Stm Γ ty_int
    | stm_bind   {σ τ : Ty} (s : Stm Γ σ) (k : Lit σ -> Stm Γ τ) : Stm Γ τ.
    Bind Scope stm_scope with Stm.

    Global Arguments stm_lit {_} _ _.
    Global Arguments stm_exp {_ _} _.
    Global Arguments stm_let {_} _ _ _ {_} _.
    Global Arguments stm_let' {_ _} _ {_} _.
    Global Arguments stm_assign {_} _ {_ _} _.
    Global Arguments stm_call {_%ctx _%ctx _} _ _%arg.
    Global Arguments stm_call' {_} _ _ _ _.
    Global Arguments stm_if {_ _} _ _ _.
    Global Arguments stm_seq {_ _} _ {_} _.
    Global Arguments stm_assert {_} _ _.
    Global Arguments stm_fail {_} _ _.
    Global Arguments stm_match_list {_ _ _} _ _ _ _ _.
    Global Arguments stm_match_sum {_ _ _ _} _ _ _ _ _.
    Global Arguments stm_match_pair {_ _ _ _} _ _ _ _.
    Global Arguments stm_match_enum {_} _ _ {_} _.
    Global Arguments stm_match_tuple {_ _ _} _ _%pat {_} _.
    Global Arguments stm_match_union {_} _ _ {_} _ _.
    Global Arguments stm_match_record {_} _ {_} _ _ {_} _.
    Global Arguments stm_read_register {_ _} _.
    Global Arguments stm_write_register {_ _} _ _.
    Global Arguments stm_read_memory {_} _.
    Global Arguments stm_write_memory {_} _ _.

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
      Stm Γ (fromSome (ctx_resolve Γ x) p) -> Stm Γ (fromSome (ctx_resolve Γ x) p) :=
      @stm_assign Γ x (fromSome _ p) (mk_inctx Γ x p).

    (* Instead we hook mk_inctx directly into the typeclass resolution mechanism.
       Apparently, the unification of Γ is performed before the resolution so
       evaluation of ctx_resolve and mk_inctx is not blocked.
     *)
    Hint Extern 10 (InCtx (?x , _) ?Γ) =>
      let xInΓ := eval vm_compute in (mk_inctx Γ x tt) in
        exact xInΓ : typeclass_instances.

  End NameResolution.

  Section Contracts.

    Definition Pred (A : Type) : Type := A -> Prop.

    Definition Final {Γ σ} (s : Stm Γ σ) : Prop :=
      match s with
      | stm_lit _ _   => True
      | stm_fail _ _ => True
      | _ => False
      end.

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

  Notation "e1 && e2" := (exp_and e1 e2) : exp_scope.
  Notation "e1 * e2" := (exp_times e1 e2) : exp_scope.
  Notation "e1 - e2" := (exp_minus e1 e2) : exp_scope.
  Notation "e1 < e2" := (exp_lt e1 e2) : exp_scope.
  Notation "e1 > e2" := (exp_gt e1 e2) : exp_scope.
  Notation "e1 <= e2" := (exp_le e1 e2) : exp_scope.
  Notation "e1 = e2" := (exp_eq e1 e2) : exp_scope.
  Notation "- e" := (exp_neg e) : exp_scope.
  Notation "'lit_int' l" := (exp_lit _ ty_int l) (at level 1, no associativity) : exp_scope.

  Notation "[ x , .. , z ]" :=
    (tuplepat_snoc .. (tuplepat_snoc tuplepat_nil x) .. z) (at level 0) : pat_scope.
  Notation "[ x , .. , z ]" :=
    (env_snoc .. (env_snoc env_nil (_,_) x) .. (_,_) z) (at level 0) : arg_scope.

  Notation "'if:' e 'then' s1 'else' s2" := (stm_if e%exp s1%stm s2%stm)
    (at level 99, right associativity, format
     "'[hv' 'if:'  e  '/' '[' 'then'  s1  ']' '/' '[' 'else'  s2 ']' ']'").

  Notation "'let:' x := s1 'in' s2" := (stm_let x _ s1%stm s2%stm)
    (at level 100, right associativity, s1 at next level, format
     "'let:'  x  :=  s1  'in'  '/' s2"
    ).
  Notation "'let:' x ∶ τ := s1 'in' s2" := (stm_let x τ s1%stm s2%stm)
    (at level 100, right associativity, s1 at next level, format
     "'let:'  x  ∶  τ  :=  s1  'in'  '/' s2"
    ).
  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1%exp => rhs1%stm
                                  | alt2%exp => rhs2%stm
                                  end))
    (at level 100, alt1 pattern, alt2 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' 'end' ']'"
    ).
  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1%exp => rhs1%stm
                                  | alt2%exp => rhs2%stm
                                  | alt3%exp => rhs3%stm
                                  end))
    (at level 100, alt1 pattern, alt2 pattern, alt3 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' 'end' ']'"
    ).

  Notation "'match:' e 'in' U 'with' | alt1 x1 => rhs1 | alt2 x2 => rhs2 'end'" :=
    (@stm_match_union _ U e _
      (fun K => match K with
                | alt1%exp => x1
                | alt2%exp => x2
                end)
      (fun K => match K return Stm _ _ with
                | alt1%exp => rhs1%stm
                | alt2%exp => rhs2%stm
                end)
    )
    (at level 100, alt1 pattern, alt2 pattern, format
     "'[hv' 'match:'  e  'in'  U  'with'  '/' |  alt1  x1  =>  rhs1  '/' |  alt2  x2  =>  rhs2  '/' 'end' ']'"
      ).

  Notation "'match:' e 'in' '(' σ1 ',' σ2 ')' 'with' | '(' fst ',' snd ')' => rhs 'end'" :=
    (@stm_match_pair _ σ1 σ2 _ e fst snd rhs)
    (at level 100, fst pattern, snd pattern, format
     "'[hv' 'match:' e 'in' '(' σ1 ',' σ2 ')' 'with' '/' | '(' fst ',' snd ')' => rhs '/' 'end' ']'"
    ).

  Notation "'call' f a1 .. an" :=
    (stm_call f (env_snoc .. (env_snoc env_nil (_,_) a1) .. (_,_) an))
    (at level 10, f global, a1, an at level 9).

  Notation "s1 ;; s2" := (stm_seq s1 s2) : stm_scope.
  Notation "x <- s" := (stm_assign x s)
    (at level 80, s at next level) : stm_scope.
  Notation "'fail' s" := (stm_fail _ s)
    (at level 1, no associativity) : stm_scope.

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

  Parameter write_read : forall (γ : RegStore) σ (r : 𝑹𝑬𝑮 σ),
            (write_register γ r (read_register γ r)) = γ.

  Parameter write_write : forall (γ : RegStore) σ (r : 𝑹𝑬𝑮 σ) (v1 v2 : Lit σ),
            write_register (write_register γ r v1) r v2 = write_register γ r v2.

  (* Memory model *)
  Parameter Memory : Type.
  Bind Scope env_scope with Memory.
  Parameter read_memory : forall (μ : Memory) (addr : 𝑨𝑫𝑫𝑹), Lit ty_int.
  Parameter write_memory : forall (μ : Memory) (addr : 𝑨𝑫𝑫𝑹) (v : Lit ty_int), Memory.

  (* Parameter Inline Pi : forall {Δ τ} (f : 𝑭 Δ τ), FunDef Δ τ. *)
  Parameter Inline Pi : forall {Δ τ} (f : 𝑭 Δ τ), Stm Δ τ.

End ProgramKit.

Module Programs
       (typekit : TypeKit)
       (termkit : TermKit typekit)
       (progkit : ProgramKit typekit termkit).
  Export progkit.

  Inductive Contract (Δ : Ctx (𝑿 * Ty)) (τ : Ty) : Type :=
  | ContractNoFail          (pre : abstract' Lit Δ (RegStore -> Prop)) (post: abstract' Lit Δ (Lit τ -> RegStore -> Prop))
  | ContractTerminateNoFail (pre : abstract' Lit Δ (RegStore -> Prop)) (post: abstract' Lit Δ (Lit τ -> RegStore -> Prop))
  | ContractTerminate       (pre : abstract' Lit Δ (RegStore -> Prop)) (post: abstract' Lit Δ (Lit τ -> RegStore -> Prop))
  | ContractNone.

  Definition ContractEnv : Type :=
    forall Δ τ (f : 𝑭 Δ τ), Contract Δ τ.

End Programs.

Module Type ContractKit
       (Import typekit : TypeKit)
       (Import termkit : TermKit typekit)
       (Import progkit : ProgramKit typekit termkit).

  Module PM := Programs typekit termkit progkit.
  Export PM.

  Parameter Inline CEnv : ContractEnv.

End ContractKit.
