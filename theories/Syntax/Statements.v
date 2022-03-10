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
     Logic.Decidable
     Strings.String.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Base
     Bitvector
     Context
     Environment
     Notations Prelude
     Syntax.FunDecl.

Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.
Local Set Transparent Obligations.
(* Local Unset Elimination Schemes. *)

Module Type StatementsOn (Import B : Base) (Import F : FunDeclKit B).

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
  | stm_match_bvec
      {n} (e : Exp Γ (ty_bvec n)) (rhs : bv n -> Stm Γ τ)
  | stm_read_register (reg : 𝑹𝑬𝑮 τ)
  | stm_write_register (reg : 𝑹𝑬𝑮 τ) (e : Exp Γ τ)
  (* EXPERIMENTAL *)
  (* | stm_while  (e : Exp Γ ty_bool) {σ : Ty} (s : Stm Γ σ) : Stm Γ ty_unit *)
  | stm_bind   {σ : Ty} (s : Stm Γ σ) (k : Val σ -> Stm Γ τ)
  | stm_debugk (k : Stm Γ τ).

  Derive NoConfusionHom Signature for Stm.

  (* Section StmElimination. *)

  (*   Variable (P : forall (Γ : PCtx) (t : Ty), Stm Γ t -> Type). *)

  (*   Hypothesis (P_val   : forall (Γ : PCtx) (τ : Ty) (l : Val τ), P (stm_val Γ l)). *)
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

  Arguments stm_val {Γ} τ v.
  Arguments stm_exp {Γ τ} e%exp.
  Arguments stm_let {Γ τ} x σ s__σ%exp s__τ%exp.
  Arguments stm_block {Γ τ Δ} δ s%exp.
  Arguments stm_assign {Γ τ} x {xInΓ} s%exp.
  Arguments stm_call {Γ τ Δ} f & _%env.
  Arguments stm_call_frame {Γ τ Δ} δ s%exp.
  Arguments stm_foreign {Γ τ Δ} f & _%env.
  Arguments stm_lemmak {Γ τ Δ} l & _%env k.
  Arguments stm_if {Γ τ} e%exp s1%exp s2%exp.
  Arguments stm_seq {Γ τ σ} s%exp k%exp.
  Arguments stm_assertk {Γ τ} e1%exp e2%exp k%exp.
  Arguments stm_fail {Γ} τ s%string.
  Arguments stm_match_list {Γ τ _} _ _ _ _ _.
  Arguments stm_match_sum {Γ τ _ _} _ _ _ _ _.
  Arguments stm_match_prod {Γ τ _ _} _ _ _ _.
  Arguments stm_match_enum {Γ τ} E e%exp alts%exp.
  Arguments stm_match_tuple {Γ τ σs Δ} e%exp p%pat rhs%exp.
  Arguments stm_match_union {Γ τ} U e {alt__ctx} alt__pat alt__rhs.
  Arguments stm_match_record {Γ%ctx τ} R {Δ%ctx} e%exp p%pat rhs%exp.
  Arguments stm_match_bvec {Γ τ} n%nat_scope e%exp rhs%exp.
  Arguments stm_read_register {Γ τ} reg.
  Arguments stm_write_register {Γ τ} reg e%exp.
  Bind Scope exp_scope with Stm.

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

  Arguments MkAlt {_ _ _ _} _ _.
  Arguments stm_match_union_alt {_ _} _ _ _.
  Arguments stm_assert {Γ} e1%exp e2%exp.
  Arguments stm_lemma {Γ Δ} l es%env.


  Definition UnionAlt (U : 𝑼) (Γ : PCtx) (τ : Ty) (K : 𝑼𝑲 U) : Set :=
    Alternative Γ (𝑼𝑲_Ty K) τ.
  Arguments UnionAlt : clear implicits.

  Definition UnionAlts (U : 𝑼) (Γ : PCtx) (τ : Ty) : Set :=
    list (sigT (@UnionAlt U Γ τ)).

  Definition findUnionAlt {U : 𝑼} {Γ : PCtx} {τ : Ty} (K : 𝑼𝑲 U) :
    UnionAlts U Γ τ -> option (@UnionAlt U Γ τ K) := findAD K.

  (* The well-formedness property for lists of alternatives captures the
     exhaustiveness of pattern-matching. We currently don't rule out redundancy.
     The find function will always return the first alternative matching a given
     union constructor. *)
  Definition UnionAltsWf {U Γ τ} (alts : UnionAlts U Γ τ) : SProp :=
    IsTrue (List.forallb (fun K => option.isSome (findUnionAlt K alts)) (finite.enum (𝑼𝑲 U))).

  Lemma union_alts_wf' {U Γ τ} (alts : UnionAlts U Γ τ) (alts_wf : UnionAltsWf alts) :
    forall (K : 𝑼𝑲 U), findUnionAlt K alts <> None.
  Proof.
    intros K. unfold UnionAltsWf in alts_wf.
    destruct List.forallb eqn:Hwf; [|easy].
    rewrite List.forallb_forall in Hwf.
    specialize (Hwf K).
    rewrite <- base.elem_of_list_In in Hwf.
    inster Hwf by apply finite.elem_of_enum.
    now destruct (findUnionAlt K alts).
  Qed.

  Definition stm_match_union_alt_list {Γ τ} U (e : Exp Γ (ty_union U))
    (alts : UnionAlts U Γ τ) (alts_wf : UnionAltsWf alts) : Stm Γ τ :=
    stm_match_union_alt U e
      (fun K =>
         match findUnionAlt K alts as o return findUnionAlt K alts = o -> _ with
         | Some alt => fun _   => alt
         | None     => fun Heq => False_rec _ (union_alts_wf' alts alts_wf Heq)
         end eq_refl).
  Arguments stm_match_union_alt_list {_ _} U e alts _.

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

  #[deprecated(since="20220204", note="Use the tuple compatible ( x , .. , z ) notation instead.")]
  Notation "[ x , y , .. , z ]" :=
    (tuplepat_snoc .. (tuplepat_snoc (tuplepat_snoc tuplepat_nil x) y) .. z)
    (at level 0, only parsing) : pat_scope.
  Notation "( x , y , .. , z )" :=
    (tuplepat_snoc .. (tuplepat_snoc (tuplepat_snoc tuplepat_nil x) y) .. z) (at level 0) : pat_scope.

  Notation "'if:' e 'then' s1 'else' s2" := (stm_if e%exp s1%exp s2%exp)
    (at level 200, format
     "'[hv' 'if:'  e  '/' '[' 'then'  s1  ']' '/' '[' 'else'  s2 ']' ']'"
    ) : exp_scope.

  (* The infix operators ∷ is at level 49, so all of the notations have to bind tighter. *)
  Notation "'let:' x := s1 'in' s2" := (stm_let x%string _ s1%exp s2%exp)
    (at level 200, x at level 48, format
     "'[hv' 'let:'  x  :=  s1  'in'  '/' s2 ']'"
    ) : exp_scope.
  Notation "'let:' x :: τ := s1 'in' s2" := (stm_let x%string τ s1%exp s2%exp)
    (at level 200, x at level 48,
    (* format "'let:'  x  ::  τ  :=  s1  'in'  '/' s2", *) only parsing
    ) : exp_scope.
  Notation "'let:' x ∷ τ := s1 'in' s2" := (stm_let x%string τ s1%exp s2%exp)
    (at level 200, x at level 48,
     format "'[hv' 'let:'  x  ∷  τ  :=  s1  'in'  '/' s2 ']'"
    ) : exp_scope.
  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1%exp => rhs1%exp
                                  end))
    (at level 0, alt1 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' 'end' ']'"
    ) : exp_scope.
  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1%exp => rhs1%exp
                                  | alt2%exp => rhs2%exp
                                  end))
    (at level 0, alt1 pattern, alt2 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' 'end' ']'"
    ) : exp_scope.
  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1 => rhs1%exp
                                  | alt2 => rhs2%exp
                                  | alt3 => rhs3%exp
                                  end))
    (at level 0, alt1 pattern, alt2 pattern, alt3 pattern, format
     "'[hv' 'match:'  e  'in'  τ  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' 'end' ']'"
    ) : exp_scope.
  Notation "'match:' e 'in' τ 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 'end'" :=
    (stm_match_enum τ e (fun K => match K with
                                  | alt1 => rhs1%exp
                                  | alt2 => rhs2%exp
                                  | alt3 => rhs3%exp
                                  | alt4 => rhs4%exp
                                  end))
    (at level 0, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, format
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
    (at level 0, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, alt5 pattern, format
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
    (at level 0, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, alt5 pattern, alt6 pattern, format
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
  (*   (at level 0, alt1 pattern, alt2 pattern, format *)
  (*    "'[hv' 'match:'  e  'in'  U  'with'  '/' |  alt1  x1  =>  rhs1  '/' |  alt2  x2  =>  rhs2  '/' 'end' ']'" *)
  (*     ) : exp_scope. *)

  Notation "'match:' e 'with' | 'inl' p1 => rhs1 | 'inr' p2 => rhs2 'end'" :=
    (stm_match_sum e p1%string rhs1 p2%string rhs2) (at level 0, only parsing) : exp_scope.

  Notation "'match:' e 'in' '(' σ1 ',' σ2 ')' 'with' | '(' fst ',' snd ')' => rhs 'end'" :=
    (@stm_match_prod _ _ σ1 σ2 e fst%string snd%string rhs)
    (at level 0, fst pattern, snd pattern, format
     "'[hv' 'match:' e 'in' '(' σ1 ',' σ2 ')' 'with' '/' | '(' fst ',' snd ')' => rhs '/' 'end' ']'"
    ) : exp_scope.

  Notation "'match:' e 'in' 'bvec' 1 'with' | alt1 => rhs1 | alt2 => rhs2 'end'" :=
    (@stm_match_bvec _ _ 1 e
       (fun (x : bv 1) =>
          match bv.to_bitstring x with
          | alt1 => rhs1%exp
          | alt2 => rhs2%exp
          end))
    (at level 0, alt1 pattern, alt2 pattern, format
     "'[hv' 'match:'  e  'in'  'bvec'  1  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' 'end' ']'"
    ) : exp_scope.
  Notation "'match:' e 'in' 'bvec' 2 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 'end'" :=
    (@stm_match_bvec _ _ 2 e
       (fun (x : bv 2) =>
          match bv.to_bitstring x with
          | alt1 => rhs1%exp
          | alt2 => rhs2%exp
          | alt3 => rhs3%exp
          | alt4 => rhs4%exp
          end))
    (at level 0, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, format
     "'[hv' 'match:'  e  'in'  'bvec'  2  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' |  alt4  =>  rhs4  '/' 'end' ']'"
    ) : exp_scope.
  Notation "'match:' e 'in' 'bvec' 3 'with' | alt1 => rhs1 | alt2 => rhs2 | alt3 => rhs3 | alt4 => rhs4 | alt5 => rhs5 | alt6 => rhs6 | alt7 => rhs7 | alt8 => rhs8 'end'" :=
    (@stm_match_bvec _ _ 3 e
       (fun (x : bv 3) =>
          match bv.to_bitstring x with
          | alt1 => rhs1%exp
          | alt2 => rhs2%exp
          | alt3 => rhs3%exp
          | alt4 => rhs4%exp
          | alt5 => rhs5%exp
          | alt6 => rhs6%exp
          | alt7 => rhs7%exp
          | alt8 => rhs8%exp
          end))
    (at level 0, alt1 pattern, alt2 pattern, alt3 pattern, alt4 pattern, alt5 pattern, alt6 pattern, alt7 pattern, alt8 pattern, format
     "'[hv' 'match:'  e  'in'  'bvec'  3  'with'  '/' |  alt1  =>  rhs1  '/' |  alt2  =>  rhs2  '/' |  alt3  =>  rhs3  '/' |  alt4  =>  rhs4  '/' |  alt5  =>  rhs5  '/' |  alt6  =>  rhs6  '/' |  alt7  =>  rhs7  '/' |  alt8  =>  rhs8  '/' 'end' ']'"
    ) : exp_scope.

  Notation "'match:' e 'in' R 'with' [ x ] => rhs 'end'" :=
    (stm_match_record R e%exp
      (recordpat_snoc recordpat_nil _ x)
      rhs%exp)
    (format "'[hv' 'match:'  e  'in'  R  'with'  '/  ' [ x ]  =>  '/    ' rhs  '/' 'end' ']'") : exp_scope.

  Notation "'match:' e 'in' R 'with' [ x ; y ; .. ; z ] => rhs 'end'" :=
    (stm_match_record R e%exp
      (recordpat_snoc .. (recordpat_snoc (recordpat_snoc recordpat_nil _ x) _ y) .. _ z)
      rhs%exp)
    (format "'[hv' 'match:'  e  'in'  R  'with'  '/  ' [ x ; y ; .. ; z ]  =>  '/    ' rhs  '/' 'end' ']'") : exp_scope.

  Notation "'match:' e 'in' 'union' U 'with' | x | y | .. | z 'end'" :=
    (stm_match_union_alt_list U e (cons x%alt (cons y%alt .. (cons z%alt nil) ..)) StrictProp.stt)
    (format "'[hv' 'match:'  e  'in'  'union'  U  'with'  '/' | x  '/' | y  '/' | ..  '/' | z  '/' 'end' ']'") : exp_scope.

  Notation "'>' K pat => rhs" := (existT K (MkAlt pat rhs))
    (K global, at level 200, pat at level 9, format ">  K  pat  =>  rhs") : alt_scope.

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

End StatementsOn.

Module Type FunDecl (B : Base) := FunDeclKit B <+ StatementsOn B.
