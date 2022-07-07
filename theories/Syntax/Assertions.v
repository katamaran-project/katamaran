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

  Local Obligation Tactic := idtac.

  Inductive Assertion (Σ : LCtx) : Type :=
  | asn_formula (fml : Formula Σ)
  | asn_chunk (c : Chunk Σ)
  | asn_chunk_angelic (c : Chunk Σ)
  | asn_if   (b : Term Σ ty.bool) (a1 a2 : Assertion Σ)
  | asn_match_enum (E : enumi) (k : Term Σ (ty.enum E)) (alts : forall (K : enumt E), Assertion Σ)
  | asn_match_sum (σ τ : Ty) (s : Term Σ (ty.sum σ τ)) (xl : LVar) (alt_inl : Assertion (Σ ▻ xl∷σ)) (xr : LVar) (alt_inr : Assertion (Σ ▻ xr∷τ))
  | asn_match_list
      {σ : Ty} (s : Term Σ (ty.list σ)) (alt_nil : Assertion Σ) (xh xt : LVar)
      (alt_cons : Assertion (Σ ▻ xh∷σ ▻ xt∷ty.list σ))
  | asn_match_prod
      {σ1 σ2 : Ty} (s : Term Σ (ty.prod σ1 σ2))
      (xl xr : LVar) (rhs : Assertion (Σ ▻ xl∷σ1 ▻ xr∷σ2))
  | asn_match_tuple
      {σs : Ctx Ty} {Δ : LCtx} (s : Term Σ (ty.tuple σs))
      (p : TuplePat σs Δ) (rhs : Assertion (Σ ▻▻ Δ))
  | asn_match_record
      {R : recordi} {Δ : LCtx} (s : Term Σ (ty.record R))
      (p : RecordPat (recordf_ty R) Δ) (rhs : Assertion (Σ ▻▻ Δ))
  | asn_match_union
      {U : unioni} (s : Term Σ (ty.union U))
      (alt__ctx : forall (K : unionk U), LCtx)
      (alt__pat : forall (K : unionk U), Pattern (alt__ctx K) (unionk_ty U K))
      (alt__rhs : forall (K : unionk U), Assertion (Σ ▻▻ alt__ctx K))
  | asn_sep  (a1 a2 : Assertion Σ)
  | asn_or   (a1 a2 : Assertion Σ)
  | asn_exist (ς : LVar) (τ : Ty) (a : Assertion (Σ ▻ ς∷τ))
  | asn_debug.
  Bind Scope asn_scope with Assertion.

  Arguments asn_match_enum [_] E _ _.
  Arguments asn_match_sum [_] σ τ _ _ _.
  Arguments asn_match_list [_] {σ} s alt_nil xh xt alt_cons.
  Arguments asn_match_prod [_] {σ1 σ2} s xl xr rhs.
  Arguments asn_match_tuple [_] {σs Δ} s p rhs.
  Arguments asn_match_record [_] R {Δ} s p rhs.
  Arguments asn_match_union [_] U s alt__ctx alt__pat alt__rhs.
  Arguments asn_exist [_] _ _ _.
  Arguments asn_debug {_}.

  Notation asn_bool b := (asn_formula (formula_bool b)).
  Notation asn_prop Σ P := (asn_formula (@formula_prop Σ Σ (sub_id Σ) P)).
  Notation asn_eq t1 t2 := (asn_formula (formula_eq t1 t2)).
  Notation asn_true := (asn_bool (term_val ty.bool true)).
  Notation asn_false := (asn_bool (term_val ty.bool false)).

  Global Instance sub_assertion : Subst Assertion :=
    fix sub_assertion {Σ1} (a : Assertion Σ1) {Σ2} (ζ : Sub Σ1 Σ2) {struct a} : Assertion Σ2 :=
      match a with
      | asn_formula fml => asn_formula (subst fml ζ)
      | asn_chunk c => asn_chunk (subst c ζ)
      | asn_chunk_angelic c => asn_chunk_angelic (subst c ζ)
      | asn_if b a1 a2 => asn_if (subst b ζ) (sub_assertion a1 ζ) (sub_assertion a2 ζ)
      | asn_match_enum E k alts =>
        asn_match_enum E (subst k ζ) (fun z => sub_assertion (alts z) ζ)
      | asn_match_sum σ τ t xl al xr ar =>
        asn_match_sum σ τ (subst t ζ) xl (sub_assertion al (sub_up1 ζ)) xr (sub_assertion ar (sub_up1 ζ))
      | asn_match_list s anil xh xt acons =>
        asn_match_list (subst s ζ) (sub_assertion anil ζ) xh xt (sub_assertion acons (sub_up1 (sub_up1 ζ)))
      | asn_match_prod s xl xr asn =>
        asn_match_prod (subst s ζ) xl xr (sub_assertion asn (sub_up1 (sub_up1 ζ)))
      | asn_match_tuple s p rhs =>
        asn_match_tuple (subst s ζ) p (sub_assertion rhs (sub_up ζ _))
      | asn_match_record R s p rhs =>
        asn_match_record R (subst s ζ) p (sub_assertion rhs (sub_up ζ _))
      | asn_match_union U s ctx pat rhs =>
        asn_match_union U (subst s ζ) ctx pat (fun K => sub_assertion (rhs K) (sub_up ζ _))
      | asn_sep a1 a2 => asn_sep (sub_assertion a1 ζ) (sub_assertion a2 ζ)
      | asn_or a1 a2  => asn_sep (sub_assertion a1 ζ) (sub_assertion a2 ζ)
      | asn_exist ς τ a => asn_exist ς τ (sub_assertion a (sub_up1 ζ))
      | asn_debug => asn_debug
      end.

  (* This instance is only used for linting contracts. *)
  Import option.notations.
  #[export] Instance OccursCheckAssertion :
    OccursCheck Assertion :=
    fix occurs Σ b (bIn : b ∈ Σ) (asn : Assertion Σ) : option (Assertion (Σ - b)) :=
      match asn with
      | asn_formula fml => option.map (@asn_formula _) (occurs_check bIn fml)
      | asn_chunk c     => option.map (@asn_chunk _) (occurs_check bIn c)
      | asn_chunk_angelic c => option.map (@asn_chunk_angelic _) (occurs_check bIn c)
      | asn_if b a1 a2  =>
          b'  <- occurs_check bIn b;;
          a1' <- occurs _ _ bIn a1 ;;
          a2' <- occurs _ _ bIn a2 ;;
          Some (asn_if b' a1' a2')
      | asn_match_enum E k alts => None (* TODO *)
      | asn_match_sum σ τ s xl alt_inl xr alt_inr =>
          s'   <- occurs_check bIn s ;;
          inl' <- occurs (Σ ▻ xl∷σ) b (ctx.in_succ bIn) alt_inl ;;
          inr' <- occurs (Σ ▻ xr∷τ) b (ctx.in_succ bIn) alt_inr ;;
          Some (asn_match_sum σ τ s' xl inl' xr inr')
      | @asn_match_list _ σ s alt_nil xh xt alt_cons => None (* TODO *)
      | @asn_match_prod _ σ1 σ2 s xl xr rhs => None (* TODO *)
      | @asn_match_tuple _ σs Δ s p rhs => None (* TODO *)
      | @asn_match_record _ R4 Δ s p rhs => None (* TODO *)
      | asn_match_union U s alt__ctx alt__pat alt__rhs => None (* TODO *)
      | asn_sep a1 a2 =>
          a1' <- occurs _ _ bIn a1 ;;
          a2' <- occurs _ _ bIn a2 ;;
          Some (asn_sep a1' a2')
      | asn_or a1 a2  =>
          a1' <- occurs _ _ bIn a1 ;;
          a2' <- occurs _ _ bIn a2 ;;
          Some (asn_or a1' a2')
      | asn_exist ς τ a => option_map (@asn_exist _ ς τ) (occurs _ _ (ctx.in_succ bIn) a)
      | asn_debug => Some asn_debug
      end.

  Record SepContract (Δ : PCtx) (τ : Ty) : Type :=
    MkSepContract
      { sep_contract_logic_variables  : LCtx;
        sep_contract_localstore       : SStore Δ sep_contract_logic_variables;
        sep_contract_precondition     : Assertion sep_contract_logic_variables;
        sep_contract_result           : LVar;
        sep_contract_postcondition    : Assertion (sep_contract_logic_variables ▻ sep_contract_result∷τ);
      }.

  Arguments MkSepContract : clear implicits.

  Record Lemma (Δ : PCtx) : Type :=
    MkLemma
      { lemma_logic_variables  : LCtx;
        lemma_patterns         : SStore Δ lemma_logic_variables;
        lemma_precondition     : Assertion lemma_logic_variables;
        lemma_postcondition    : Assertion lemma_logic_variables;
      }.

  Arguments MkLemma : clear implicits.

  Definition lint_contract {Δ σ} (c : SepContract Δ σ) : bool :=
    match c with
    | {| sep_contract_logic_variables := Σ;
         sep_contract_localstore      := δ;
         sep_contract_precondition    := pre
      |} =>
      ctx.forallb Σ
        (fun b bIn =>
           match occurs_check bIn (δ , pre) with
           | Some _ => false
           | None   => true
           end)
    end.

  Definition lint_lemma {Δ} (l : Lemma Δ) : bool :=
    match l with
    | {| lemma_logic_variables := Σ;
         lemma_patterns        := δ;
         lemma_precondition    := pre
      |} =>
      ctx.forallb Σ
        (fun b bIn =>
           match occurs_check bIn (δ , pre) with
           | Some _ => false
           | None   => true
           end)
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

  Import sep.notations.

  Class PredicateDef (HProp : SepLogic) : Type :=
    { lptsreg    : forall {σ : Ty}, 𝑹𝑬𝑮 σ -> Val σ -> HProp;
      luser      : forall (p : 𝑯), Env Val (𝑯_Ty p) -> HProp;
      lduplicate : forall (p : 𝑯) (ts : Env Val (𝑯_Ty p)),
        is_duplicable p = true ->
        @luser p ts ⊢ @luser p ts ∗ @luser p ts;
    }.
  Arguments luser {_ _} p _.

  Section ContractInt.

    Context {HProp} `{PI : PredicateDef HProp}.

    Fixpoint interpret_chunk {Σ} (c : Chunk Σ) (ι : Valuation Σ) {struct c} : HProp :=
      match c with
      | chunk_user p ts => luser p (inst ts ι)
      | chunk_ptsreg r t => lptsreg r (inst t ι)
      | chunk_conj c1 c2 => interpret_chunk c1 ι ∗ interpret_chunk c2 ι
      | chunk_wand c1 c2 => interpret_chunk c1 ι -∗ interpret_chunk c2 ι
      end.

    Fixpoint interpret_scchunk (c : SCChunk) : HProp :=
      match c with
      | scchunk_user p vs => luser p vs
      | scchunk_ptsreg r v => lptsreg r v
      | scchunk_conj c1 c2 => interpret_scchunk c1 ∗ interpret_scchunk c2
      | scchunk_wand c1 c2 => interpret_scchunk c1 -∗ interpret_scchunk c2
      end.

    Definition interpret_scheap : SCHeap -> HProp :=
      List.fold_right (fun c h => interpret_scchunk c ∗ h) lemp.
    Arguments interpret_scheap !h.

    Fixpoint interpret_assertion {Σ} (a : Assertion Σ) (ι : Valuation Σ) : HProp :=
      match a with
      | asn_formula fml => !!(inst fml ι) ∧ lemp
      | asn_chunk c => interpret_chunk c ι
      | asn_chunk_angelic c => interpret_chunk c ι
      | asn_if b a1 a2 => if inst (A := Val ty.bool) b ι then interpret_assertion a1 ι else interpret_assertion a2 ι
      | asn_match_enum E k alts => interpret_assertion (alts (inst (T := fun Σ => Term Σ _) k ι)) ι
      | asn_match_sum σ τ s xl alt_inl xr alt_inr =>
        match inst (T := fun Σ => Term Σ _) s ι with
        | inl v => interpret_assertion alt_inl (ι ► (xl∷σ ↦ v))
        | inr v => interpret_assertion alt_inr (ι ► (xr∷τ ↦ v))
        end
      | asn_match_list s alt_nil xh xt alt_cons =>
        match inst (T := fun Σ => Term Σ _) s ι with
        | nil        => interpret_assertion alt_nil ι
        | cons vh vt => interpret_assertion alt_cons (ι ► (xh∷_ ↦ vh) ► (xt∷ty.list _ ↦ vt))
        end
      | asn_match_prod s xl xr rhs =>
        match inst (T := fun Σ => Term Σ _) s ι with
        | (vl,vr)    => interpret_assertion rhs (ι ► (xl∷_ ↦ vl) ► (xr∷_ ↦ vr))
        end
      | asn_match_tuple s p rhs =>
        let t := inst (T := fun Σ => Term Σ _) s ι in
        let ι' := tuple_pattern_match_val p t in
        interpret_assertion rhs (ι ►► ι')
      | asn_match_record R s p rhs =>
        let t := inst (T := fun Σ => Term Σ _) s ι in
        let ι' := record_pattern_match_val p t in
        interpret_assertion rhs (ι ►► ι')
      | asn_match_union U s alt__ctx alt__pat alt__rhs =>
        let t := inst (T := fun Σ => Term Σ _) s ι in
        let (K , v) := unionv_unfold U t in
        let ι' := pattern_match_val (alt__pat K) v in
        interpret_assertion (alt__rhs K) (ι ►► ι')
      | asn_sep a1 a2 => interpret_assertion a1 ι ∗ interpret_assertion a2 ι
      | asn_or a1 a2  => interpret_assertion a1 ι ∨ interpret_assertion a2 ι
      | asn_exist ς τ a => ∃ (v : Val τ), interpret_assertion a (ι ► (ς∷τ ↦ v))
      | asn_debug => lemp
    end.

    Definition inst_contract_localstore {Δ τ} (c : SepContract Δ τ)
      (ι : Valuation (sep_contract_logic_variables c)) : CStore Δ :=
      inst (sep_contract_localstore c) ι.

    Definition interpret_contract_precondition {Δ τ} (c : SepContract Δ τ)
      (ι : Valuation (sep_contract_logic_variables c)) : HProp :=
      interpret_assertion (sep_contract_precondition c) ι.

    Definition interpret_contract_postcondition {Δ τ} (c : SepContract Δ τ)
      (ι : Valuation (sep_contract_logic_variables c)) (result : Val τ) : HProp :=
        interpret_assertion (sep_contract_postcondition c) (env.snoc ι (sep_contract_result c ∷ τ) result).

    Fixpoint is_pure {Σ} (a : Assertion Σ) : bool :=
      match a with
      | asn_formula fml => true
      | asn_chunk c => false
      | asn_chunk_angelic c => false
      | asn_if b a1 a2 => is_pure a1 && is_pure a2
      | asn_match_enum E k alts => List.forallb (fun K => is_pure (alts K)) (finite.enum _)
      | asn_match_sum σ τ s xl alt_inl xr alt_inr => is_pure alt_inl && is_pure alt_inr
      | asn_match_list s alt_nil xh xt alt_cons => is_pure alt_nil && is_pure alt_cons
      | asn_match_prod s xl xr rhs => is_pure rhs
      | asn_match_tuple s p rhs => is_pure rhs
      | asn_match_record R s p rhs => is_pure rhs
      | asn_match_union U s alt__ctx alt__pat alt__rhs => List.forallb (fun K => is_pure (alt__rhs K)) (finite.enum _)
      | asn_sep a1 a2 => is_pure a1 && is_pure a2
      | asn_or a1 a2  => is_pure a1 && is_pure a2
      | asn_exist ς τ a => is_pure a
      | asn_debug => true
    end.

    Fixpoint interpret_assertion_pure {Σ} (a : Assertion Σ) (ι : Valuation Σ) : Prop :=
      match a with
      | asn_formula fml => inst fml ι
      | asn_chunk c => False
      | asn_chunk_angelic c => False
      | asn_if b a1 a2 => if inst (A := Val ty.bool) b ι then interpret_assertion_pure a1 ι else interpret_assertion_pure a2 ι
      | asn_match_enum E k alts => interpret_assertion_pure (alts (inst (T := fun Σ => Term Σ _) k ι)) ι
      | asn_match_sum σ τ s xl alt_inl xr alt_inr =>
        match inst (T := fun Σ => Term Σ _) s ι with
        | inl v => interpret_assertion_pure alt_inl (ι ► (xl∷σ ↦ v))
        | inr v => interpret_assertion_pure alt_inr (ι ► (xr∷τ ↦ v))
        end
      | asn_match_list s alt_nil xh xt alt_cons =>
        match inst (T := fun Σ => Term Σ _) s ι with
        | nil        => interpret_assertion_pure alt_nil ι
        | cons vh vt => interpret_assertion_pure alt_cons (ι ► (xh∷_ ↦ vh) ► (xt∷ty.list _ ↦ vt))
        end
      | asn_match_prod s xl xr rhs =>
        match inst (T := fun Σ => Term Σ _) s ι with
        | (vl,vr)    => interpret_assertion_pure rhs (ι ► (xl∷_ ↦ vl) ► (xr∷_ ↦ vr))
        end
      | asn_match_tuple s p rhs =>
        let t := inst (T := fun Σ => Term Σ _) s ι in
        let ι' := tuple_pattern_match_val p t in
        interpret_assertion_pure rhs (ι ►► ι')
      | asn_match_record R s p rhs =>
        let t := inst (T := fun Σ => Term Σ _) s ι in
        let ι' := record_pattern_match_val p t in
        interpret_assertion_pure rhs (ι ►► ι')
      | asn_match_union U s alt__ctx alt__pat alt__rhs =>
        let t := inst (T := fun Σ => Term Σ _) s ι in
        let (K , v) := unionv_unfold U t in
        let ι' := pattern_match_val (alt__pat K) v in
        interpret_assertion_pure (alt__rhs K) (ι ►► ι')
      | asn_sep a1 a2 => interpret_assertion_pure a1 ι /\ interpret_assertion_pure a2 ι
      | asn_or a1 a2  => interpret_assertion_pure a1 ι \/ interpret_assertion_pure a2 ι
      | asn_exist ς τ a => exists (v : Val τ), interpret_assertion_pure a (ι ► (ς∷τ ↦ v))
      | asn_debug => True
    end.

    Lemma interpret_assertion_pure_equiv {Σ} (a : Assertion Σ) (a_pure : is_pure a = true) :
      forall (ι : Valuation Σ),
        interpret_assertion a ι ⊣⊢ !!(interpret_assertion_pure a ι).
    Proof.
      induction a; cbn in *; intros ι; try discriminate a_pure.
      - now rewrite lemp_true, land_true.
      - apply andb_true_iff in a_pure. destruct a_pure.
        destruct (inst b ι); auto.
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

  End ContractInt.

End AssertionsOn.
