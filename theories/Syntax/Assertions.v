(******************************************************************************)
(* Copyright (c) 2020 Dominique Devriese, Georgy Lukyanov,                    *)
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
     Bool.Bool.
From Katamaran Require Import
     Base
     Notations
     Prelude
     Sep.Logic
     Syntax.Chunks
     Syntax.Formulas
     Syntax.Predicates.

Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.

Module Type AssertionsOn
  (Import B : Base)
  (Import P : PredicateKit B)
  (Import F : FormulasOn B P)
  (Import C : ChunksOn B P).
Module Import asn.

  Local Obligation Tactic := idtac.

  Inductive Assertion (Σ : LCtx) : Type :=
  | formula (fml : Formula Σ)
  | chunk (c : Chunk Σ)
  | chunk_angelic (c : Chunk Σ)
  | newpattern_match {σ} (s : Term Σ σ) (pat : PatternShape σ)
      (rhs : forall (pc : PatternCase pat), Assertion (Σ ▻▻ PatternCaseCtx pc))
  | match_enum (E : enumi) (k : Term Σ (ty.enum E)) (alts : forall (K : enumt E), Assertion Σ)
  | match_sum (σ τ : Ty) (s : Term Σ (ty.sum σ τ)) (xl : LVar)
      (alt_inl : Assertion (Σ ▻ xl∷σ)) (xr : LVar) (alt_inr : Assertion (Σ ▻ xr∷τ))
  | match_list
      {σ : Ty} (s : Term Σ (ty.list σ)) (alt_nil : Assertion Σ) (xh xt : LVar)
      (alt_cons : Assertion (Σ ▻ xh∷σ ▻ xt∷ty.list σ))
  | match_prod
      {σ1 σ2 : Ty} (s : Term Σ (ty.prod σ1 σ2))
      (xl xr : LVar) (rhs : Assertion (Σ ▻ xl∷σ1 ▻ xr∷σ2))
  | match_tuple
      {σs : Ctx Ty} {Δ : LCtx} (s : Term Σ (ty.tuple σs))
      (p : TuplePat σs Δ) (rhs : Assertion (Σ ▻▻ Δ))
  | match_record
      {R : recordi} {Δ : LCtx} (s : Term Σ (ty.record R))
      (p : RecordPat (recordf_ty R) Δ) (rhs : Assertion (Σ ▻▻ Δ))
  | match_union
      {U : unioni} (s : Term Σ (ty.union U))
      (alt__ctx : forall (K : unionk U), LCtx)
      (alt__pat : forall (K : unionk U), Pattern (alt__ctx K) (unionk_ty U K))
      (alt__rhs : forall (K : unionk U), Assertion (Σ ▻▻ alt__ctx K))
  | sep  (A1 A2 : Assertion Σ)
  | or   (A1 A2 : Assertion Σ)
  | exist (ς : LVar) (τ : Ty) (a : Assertion (Σ ▻ ς∷τ))
  | debug.

  #[global] Arguments match_enum [_] E _ _.
  #[global] Arguments match_sum [_] σ τ _ _ _.
  #[global] Arguments match_list [_] {σ} s alt_nil xh xt alt_cons.
  #[global] Arguments match_prod [_] {σ1 σ2} s xl xr rhs.
  #[global] Arguments match_tuple [_] {σs Δ} s p rhs.
  #[global] Arguments match_record [_] R {Δ} s p rhs.
  #[global] Arguments match_union [_] U s alt__ctx alt__pat alt__rhs.
  #[global] Arguments exist [_] _ _ _.
  #[global] Arguments debug {_}.

  Definition match_bool {Σ} (b : Term Σ ty.bool) (A1 A2 : Assertion Σ) : Assertion Σ :=
    newpattern_match b pat_shape_bool (fun v => if v then A1 else A2).

  Fixpoint exs {Σ} Δ : Assertion (Σ ▻▻ Δ) -> Assertion Σ :=
    match Δ return Assertion (Σ ▻▻ Δ) -> Assertion Σ with
    | ctx.nil => fun A => A
    | ctx.snoc Γ (x :: τ) =>
      fun A =>
        @exs Σ Γ (exist x τ A)
    end.

  #[export] Instance sub_assertion : Subst Assertion :=
    fix sub_assertion {Σ1} (A : Assertion Σ1) {Σ2} (ζ : Sub Σ1 Σ2) {struct A} : Assertion Σ2 :=
      match A with
      | formula fml => formula (subst fml ζ)
      | chunk c => chunk (subst c ζ)
      | chunk_angelic c => chunk_angelic (subst c ζ)
      | newpattern_match s pat rhs =>
        newpattern_match (subst s ζ) pat (fun pc => sub_assertion (rhs pc) (sub_up ζ _))
      | match_enum E k alts =>
        match_enum E (subst k ζ) (fun z => sub_assertion (alts z) ζ)
      | match_sum σ τ t xl al xr ar =>
        match_sum σ τ (subst t ζ) xl (sub_assertion al (sub_up1 ζ)) xr (sub_assertion ar (sub_up1 ζ))
      | match_list s anil xh xt acons =>
        match_list (subst s ζ) (sub_assertion anil ζ) xh xt (sub_assertion acons (sub_up1 (sub_up1 ζ)))
      | match_prod s xl xr A =>
        match_prod (subst s ζ) xl xr (sub_assertion A (sub_up1 (sub_up1 ζ)))
      | match_tuple s p A =>
        match_tuple (subst s ζ) p (sub_assertion A (sub_up ζ _))
      | match_record R s p A =>
        match_record R (subst s ζ) p (sub_assertion A (sub_up ζ _))
      | match_union U s ctx pat rhs =>
        match_union U (subst s ζ) ctx pat (fun K => sub_assertion (rhs K) (sub_up ζ _))
      | sep A1 A2 => sep (sub_assertion A1 ζ) (sub_assertion A2 ζ)
      | or A1 A2  => sep (sub_assertion A1 ζ) (sub_assertion A2 ζ)
      | exist ς τ A => exist ς τ (sub_assertion A (sub_up1 ζ))
      | debug => debug
      end.

  (* TODO: This instance is currently unused and incomplete. Do not use. *)
  Import option.notations.
  #[local] Instance OccursCheckAssertion :
    OccursCheck Assertion :=
    fix occurs Σ b (bIn : b ∈ Σ) (asn : Assertion Σ) : option (Assertion (Σ - b)) :=
      match asn with
      | formula fml => option.map (@formula _) (occurs_check bIn fml)
      | chunk c     => option.map (@chunk _) (occurs_check bIn c)
      | chunk_angelic c => option.map (@chunk_angelic _) (occurs_check bIn c)
      | newpattern_match s pat rhs =>
          s' <- occurs_check bIn s;;
          None (* TODO *)
      | match_enum E k alts => None (* TODO *)
      | match_sum σ τ s xl alt_inl xr alt_inr =>
          s'   <- occurs_check bIn s ;;
          inl' <- occurs (Σ ▻ xl∷σ) b (ctx.in_succ bIn) alt_inl ;;
          inr' <- occurs (Σ ▻ xr∷τ) b (ctx.in_succ bIn) alt_inr ;;
          Some (match_sum σ τ s' xl inl' xr inr')
      | @match_list _ σ s alt_nil xh xt alt_cons => None (* TODO *)
      | @match_prod _ σ1 σ2 s xl xr rhs => None (* TODO *)
      | @match_tuple _ σs Δ s p rhs => None (* TODO *)
      | @match_record _ R4 Δ s p rhs => None (* TODO *)
      | match_union U s alt__ctx alt__pat alt__rhs => None (* TODO *)
      | sep A1 A2 =>
          A1' <- occurs _ _ bIn A1 ;;
          A2' <- occurs _ _ bIn A2 ;;
          Some (sep A1' A2')
      | or A1 A2  =>
          A1' <- occurs _ _ bIn A1 ;;
          A2' <- occurs _ _ bIn A2 ;;
          Some (or A1' A2')
      | exist ς τ A => option_map (@exist _ ς τ) (occurs _ _ (ctx.in_succ bIn) A)
      | debug => Some debug
      end.

  Fixpoint is_pure {Σ} (a : Assertion Σ) : bool :=
    match a with
    | formula fml => true
    | chunk c => false
    | chunk_angelic c => false
    | newpattern_match s pat rhs =>
        List.forallb (fun pc => is_pure (rhs pc)) (finite.enum (PatternCase pat))
    | match_enum E k alts => List.forallb (fun K => is_pure (alts K)) (finite.enum _)
    | match_sum σ τ s xl alt_inl xr alt_inr => is_pure alt_inl && is_pure alt_inr
    | match_list s alt_nil xh xt alt_cons => is_pure alt_nil && is_pure alt_cons
    | match_prod s xl xr rhs => is_pure rhs
    | match_tuple s p rhs => is_pure rhs
    | match_record R s p rhs => is_pure rhs
    | match_union U s alt__ctx alt__pat alt__rhs =>
        List.forallb (fun K => is_pure (alt__rhs K)) (finite.enum _)
    | sep A1 A2 => is_pure A1 && is_pure A2
    | or A1 A2  => is_pure A1 && is_pure A2
    | exist ς τ A => is_pure A
    | debug => true
  end.

  Section Interpretation.
    Import sep.notations.

    Fixpoint interpret_pure {Σ} (a : Assertion Σ) (ι : Valuation Σ) : Prop :=
      match a with
      | formula F => inst F ι
      | chunk c => False
      | chunk_angelic c => False
      | newpattern_match s pat rhs =>
        let v := inst (T := fun Σ => Term Σ _) s ι in
        let (pc,δpc) := newpattern_match_val pat v in
        interpret_pure (rhs pc) (ι ►► δpc)
      | match_enum E k alts => interpret_pure (alts (inst (T := fun Σ => Term Σ _) k ι)) ι
      | match_sum σ τ s xl alt_inl xr alt_inr =>
        match inst (T := fun Σ => Term Σ _) s ι with
        | inl v => interpret_pure alt_inl (ι ► (xl∷σ ↦ v))
        | inr v => interpret_pure alt_inr (ι ► (xr∷τ ↦ v))
        end
      | match_list s alt_nil xh xt alt_cons =>
        match inst (T := fun Σ => Term Σ _) s ι with
        | nil        => interpret_pure alt_nil ι
        | cons vh vt => interpret_pure alt_cons (ι ► (xh∷_ ↦ vh) ► (xt∷ty.list _ ↦ vt))
        end
      | match_prod s xl xr rhs =>
        match inst (T := fun Σ => Term Σ _) s ι with
        | (vl,vr)    => interpret_pure rhs (ι ► (xl∷_ ↦ vl) ► (xr∷_ ↦ vr))
        end
      | match_tuple s p rhs =>
        let t := inst (T := fun Σ => Term Σ _) s ι in
        let ι' := tuple_pattern_match_val p t in
        interpret_pure rhs (ι ►► ι')
      | match_record R s p rhs =>
        let t := inst (T := fun Σ => Term Σ _) s ι in
        let ι' := record_pattern_match_val p t in
        interpret_pure rhs (ι ►► ι')
      | match_union U s alt__ctx alt__pat alt__rhs =>
        let t := inst (T := fun Σ => Term Σ _) s ι in
        let (K , v) := unionv_unfold U t in
        let ι' := pattern_match_val (alt__pat K) v in
        interpret_pure (alt__rhs K) (ι ►► ι')
      | sep A1 A2 => interpret_pure A1 ι /\ interpret_pure A2 ι
      | or A1 A2  => interpret_pure A1 ι \/ interpret_pure A2 ι
      | exist ς τ A => exists (v : Val τ), interpret_pure A (ι ► (ς∷τ ↦ v))
      | debug => True
    end.

    Context {HProp} `{PI : PredicateDef HProp}.

    Fixpoint interpret {Σ} (A : Assertion Σ) (ι : Valuation Σ) : HProp :=
      match A with
      | formula F => !!(inst F ι) ∧ lemp
      | chunk c => interpret_chunk c ι
      | chunk_angelic c => interpret_chunk c ι
      | newpattern_match s pat rhs =>
        let v := inst (T := fun Σ => Term Σ _) s ι in
        let (pc,δpc) := newpattern_match_val pat v in
        interpret (rhs pc) (ι ►► δpc)
      | match_enum E k alts => interpret (alts (inst (T := fun Σ => Term Σ _) k ι)) ι
      | match_sum σ τ s xl alt_inl xr alt_inr =>
        match inst (T := fun Σ => Term Σ _) s ι with
        | inl v => interpret alt_inl (ι ► (xl∷σ ↦ v))
        | inr v => interpret alt_inr (ι ► (xr∷τ ↦ v))
        end
      | match_list s alt_nil xh xt alt_cons =>
        match inst (T := fun Σ => Term Σ _) s ι with
        | nil        => interpret alt_nil ι
        | cons vh vt => interpret alt_cons (ι ► (xh∷_ ↦ vh) ► (xt∷ty.list _ ↦ vt))
        end
      | match_prod s xl xr rhs =>
        match inst (T := fun Σ => Term Σ _) s ι with
        | (vl,vr)    => interpret rhs (ι ► (xl∷_ ↦ vl) ► (xr∷_ ↦ vr))
        end
      | match_tuple s p rhs =>
        let t := inst (T := fun Σ => Term Σ _) s ι in
        let ι' := tuple_pattern_match_val p t in
        interpret rhs (ι ►► ι')
      | match_record R s p rhs =>
        let t := inst (T := fun Σ => Term Σ _) s ι in
        let ι' := record_pattern_match_val p t in
        interpret rhs (ι ►► ι')
      | match_union U s alt__ctx alt__pat alt__rhs =>
        let t := inst (T := fun Σ => Term Σ _) s ι in
        let (K , v) := unionv_unfold U t in
        let ι' := pattern_match_val (alt__pat K) v in
        interpret (alt__rhs K) (ι ►► ι')
      | sep A1 A2 => interpret A1 ι ∗ interpret A2 ι
      | or A1 A2  => interpret A1 ι ∨ interpret A2 ι
      | exist ς τ A => ∃ (v : Val τ), interpret A (ι ► (ς∷τ ↦ v))
      | debug => lemp
    end.

    Import sep.instances.

    Lemma interpret_pure_equiv {Σ} (a : Assertion Σ) (a_pure : is_pure a = true) :
      forall (ι : Valuation Σ),
        interpret a ι ⊣⊢ !!(interpret_pure a ι).
    Proof.
      induction a; cbn in *; intros ι; try discriminate a_pure.
      - now rewrite lemp_true, land_true.
      - destruct newpattern_match_val.
        apply H. rewrite List.forallb_forall in a_pure. apply a_pure.
        apply base.elem_of_list_In. apply finite.elem_of_enum.
      - apply H. rewrite List.forallb_forall in a_pure. apply a_pure.
        apply base.elem_of_list_In. apply finite.elem_of_enum.
      - apply andb_true_iff in a_pure. destruct a_pure.
        destruct (inst s ι); auto.
      - apply andb_true_iff in a_pure. destruct a_pure.
        destruct (inst s ι); auto.
      - destruct (inst s ι); auto.
      - apply IHa; auto.
      - apply IHa; auto.
      - destruct (unionv_unfold U (inst s ι)).
        apply H. rewrite List.forallb_forall in a_pure. apply a_pure.
        apply base.elem_of_list_In. apply finite.elem_of_enum.
      - apply andb_true_iff in a_pure. destruct a_pure.
        rewrite IHa1, IHa2; auto. now rewrite lprop_sep_distr.
      - apply andb_true_iff in a_pure. destruct a_pure.
        rewrite IHa1, IHa2; auto. now rewrite lprop_or_distr.
      - setoid_rewrite IHa; auto.
        now rewrite lprop_exists_comm.
      - apply lemp_true.
    Qed.

  End Interpretation.

  Module notations.
    Open Scope asn_scope.

    Notation "r ↦ val" := (chunk (chunk_ptsreg r val)) (at level 70) : asn_scope.
    Notation "P ∗ Q" := (sep P Q) : asn_scope.
    Notation "∃ w , A" := (exist w _ A) (at level 79, right associativity) : asn_scope.
    Notation "P ∨ Q" := (or P Q) : asn_scope.
    Notation "⊤" := (formula (formula_bool (term_val ty.bool true))) : asn_scope.
    Notation "⊥" := (formula (formula_bool (term_val ty.bool false))) : asn_scope.
    Notation "'if:' c 'then' A1 'else' A2" := (match_bool c A1 A2)
      (at level 200, format
       "'[hv' 'if:'  c  '/' '[' 'then'  A1  ']' '/' '[' 'else'  A2 ']' ']'"
      ) : asn_scope.
    Notation "x = y" := (formula (formula_eq x y)) : asn_scope.
    Notation "x < y" := (formula (formula_lt x y)) : asn_scope.
    Notation "x <= y" := (formula (formula_le x y)) : asn_scope.
    Notation "x > y" := (formula (formula_gt x y)) : asn_scope.
    Notation "x >= y" := (formula (formula_ge x y)) : asn_scope.

  End notations.

End asn.
Export asn ( Assertion ).
Bind Scope asn_scope with Assertion.

Section Contracts.
  #[local] Existing Instance OccursCheckAssertion.

  Record SepContract (Δ : PCtx) (τ : Ty) : Type :=
    MkSepContract
      { sep_contract_logic_variables  : LCtx;
        sep_contract_localstore       : SStore Δ sep_contract_logic_variables;
        sep_contract_precondition     : Assertion sep_contract_logic_variables;
        sep_contract_result           : LVar;
        sep_contract_postcondition    : Assertion (sep_contract_logic_variables ▻ sep_contract_result∷τ);
      }.

  #[global] Arguments MkSepContract : clear implicits.

  Record Lemma (Δ : PCtx) : Type :=
    MkLemma
      { lemma_logic_variables  : LCtx;
        lemma_patterns         : SStore Δ lemma_logic_variables;
        lemma_precondition     : Assertion lemma_logic_variables;
        lemma_postcondition    : Assertion lemma_logic_variables;
      }.

  #[global] Arguments MkLemma : clear implicits.

  Open Scope lazy_bool_scope.

  (* This function is used as part of the linter, which checks that all
     logic variables of the contract are in fact used in the pattern or
     the precondition. It essentially performs an occurs check, albeit with
     a boolean result.
   *)
  Fixpoint lint_assertion {Σ b} (bIn : b ∈ Σ) (asn : Assertion Σ) : bool :=
    match asn with
    | formula fml => option.isNone (occurs_check bIn fml)
    | chunk c     => option.isNone (option.map (@chunk _) (occurs_check bIn c))
    | chunk_angelic c => option.isNone (option.map (@chunk_angelic _) (occurs_check bIn c))
    | newpattern_match s pat rhs =>
        option.isNone (occurs_check bIn s) |||
        List.existsb
          (fun pc => lint_assertion
                       (ctx.in_cat_left (PatternCaseCtx pc) bIn)
                       (rhs pc))
          (finite.enum (PatternCase pat))
    | match_enum E k alts =>
        option.isNone (occurs_check bIn k) |||
        List.existsb
          (fun K => lint_assertion bIn (alts K))
          (finite.enum (enumt E))
    | match_sum σ τ s xl alt_inl xr alt_inr =>
        option.isNone (occurs_check bIn s) |||
        lint_assertion (ctx.in_succ bIn) alt_inl |||
        lint_assertion (ctx.in_succ bIn) alt_inr
    | @match_list _ σ s alt_nil xh xt alt_cons =>
        option.isNone (occurs_check bIn s) |||
        lint_assertion bIn alt_nil |||
        lint_assertion (ctx.in_succ (ctx.in_succ bIn)) alt_cons
    | @match_prod _ σ1 σ2 s xl xr rhs =>
        option.isNone (occurs_check bIn s) |||
        lint_assertion (ctx.in_succ (ctx.in_succ bIn)) rhs
    | @match_tuple _ σs Δ s p rhs =>
        option.isNone (occurs_check bIn s) |||
        lint_assertion (ctx.in_cat_left Δ bIn) rhs
    | @match_record _ R Δ s p rhs =>
        option.isNone (occurs_check bIn s) |||
        lint_assertion (ctx.in_cat_left Δ bIn) rhs
    | match_union U s alt__ctx alt__pat alt__rhs =>
        option.isNone (occurs_check bIn s) |||
        List.existsb
          (fun K => lint_assertion
                      (ctx.in_cat_left (alt__ctx K) bIn)
                      (alt__rhs K))
          (finite.enum (unionk U))
    | sep A1 A2 =>
        lint_assertion bIn A1 |||
        lint_assertion bIn A2
    | or A1 A2  =>
        lint_assertion bIn A1 |||
        lint_assertion bIn A2
    | exist ς τ A =>
        lint_assertion (ctx.in_succ bIn) A
    | debug => false
    end.

  Definition lint_contract {Δ σ} (c : SepContract Δ σ) : bool :=
    match c with
    | {| sep_contract_logic_variables := Σ;
         sep_contract_localstore      := δ;
         sep_contract_precondition    := pre
      |} =>
      ctx.forallb Σ
        (fun b bIn =>
           option.isNone (occurs_check bIn δ) |||
           lint_assertion bIn pre)
    end.

  Definition lint_lemma {Δ} (l : Lemma Δ) : bool :=
    match l with
    | {| lemma_logic_variables := Σ;
         lemma_patterns        := δ;
         lemma_precondition    := pre
      |} =>
      ctx.forallb Σ
        (fun b bIn =>
           option.isNone (occurs_check bIn δ) |||
           lint_assertion bIn pre)
    end.

  Definition Linted {Δ σ} (c : SepContract Δ σ) : Prop :=
    lint_contract c = true.

  (* Notation "'CONTRACT' 'VARS' Σ 'PATS' δ 'REQ' pre 'RES' res 'ENS' post" := (@MkSepContract _ _ Σ δ pre res post) *)
  (*   (at level 200, *)
  (*    format "'[v  ' 'CONTRACT' '/' '[' 'VARS'  Σ ']' '/' '[' 'PATS'  δ ']' '/' '[' 'REQ'   pre ']' '/' '[' 'RES'   res ']' '/' '[' 'ENS'   post ']' ']'"). *)

  (* Notation "'LEMMA' 'VARS' Σ 'PATS' δ 'REQ' pre 'ENS' post" := (@MkLemma _ Σ δ pre post) *)
  (*   (at level 200, *)
  (*    format "'[v  ' 'LEMMA' '/' '[' 'VARS'  Σ ']' '/' '[' 'PATS'  δ ']' '/' '[' 'REQ'   pre ']' '/' '[' 'ENS'   post ']' ']'"). *)

  Section Experimental.

    Definition sep_contract_pun_logvars (Δ : PCtx) (Σ : LCtx) : LCtx :=
      ctx.map (fun '(x∷σ) => (PVartoLVar x∷σ)) Δ ▻▻ Σ.

    Record SepContractPun (Δ : PCtx) (τ : Ty) : Type :=
      MkSepContractPun
        { sep_contract_pun_logic_variables   : LCtx;
          sep_contract_pun_precondition      : Assertion
                                                 (sep_contract_pun_logvars
                                                    Δ sep_contract_pun_logic_variables);
          sep_contract_pun_result            : LVar;
          sep_contract_pun_postcondition     : Assertion
                                                 (sep_contract_pun_logvars Δ
                                                                           sep_contract_pun_logic_variables
                                                                           ▻ sep_contract_pun_result∷τ)
        }.

    Global Arguments MkSepContractPun : clear implicits.

    Definition sep_contract_pun_to_sep_contract {Δ τ} :
      SepContractPun Δ τ -> SepContract Δ τ :=
      fun c =>
        match c with
        | MkSepContractPun _ _ Σ req result ens =>
          MkSepContract
            Δ τ
            (sep_contract_pun_logvars Δ Σ)
            (env.tabulate (fun '(x∷σ) xIn =>
                             @term_var
                               (sep_contract_pun_logvars Δ Σ)
                               (PVartoLVar x)
                               σ
                               (ctx.in_cat_left Σ (ctx.in_map (fun '(y∷τ) => (PVartoLVar y∷τ)) xIn))))
            req result ens
        end.

    Global Coercion sep_contract_pun_to_sep_contract : SepContractPun >-> SepContract.

  End Experimental.

  Section ContractInt.

    Context {HProp} `{PI : PredicateDef HProp}.

    Definition inst_contract_localstore {Δ τ} (c : SepContract Δ τ)
      (ι : Valuation (sep_contract_logic_variables c)) : CStore Δ :=
      inst (sep_contract_localstore c) ι.

    Definition interpret_contract_precondition {Δ τ} (c : SepContract Δ τ)
      (ι : Valuation (sep_contract_logic_variables c)) : HProp :=
      interpret (sep_contract_precondition c) ι.

    Definition interpret_contract_postcondition {Δ τ} (c : SepContract Δ τ)
      (ι : Valuation (sep_contract_logic_variables c)) (result : Val τ) : HProp :=
        interpret (sep_contract_postcondition c) (env.snoc ι (sep_contract_result c ∷ τ) result).

  End ContractInt.

End Contracts.
End AssertionsOn.
