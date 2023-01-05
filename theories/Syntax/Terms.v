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
     ssr.ssrbool.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Context
     Environment
     Notations
     Prelude
     Syntax.BinOps
     Syntax.TypeDecl
     Syntax.Variables
     Tactics.

Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.
Local Set Transparent Obligations.
Local Unset Elimination Schemes.

Module Type TermsOn (Import TY : Types).

  Local Notation PCtx := (NCtx PVar Ty).
  Local Notation LCtx := (NCtx LVar Ty).

  Inductive Term (Σ : LCtx) : Ty -> Set :=
  | term_var     (ς : LVar) (σ : Ty) {ςInΣ : ς∷σ ∈ Σ} : Term Σ σ
  | term_val     (σ : Ty) : Val σ -> Term Σ σ
  | term_binop   {σ1 σ2 σ3 : Ty} (op : BinOp σ1 σ2 σ3) (e1 : Term Σ σ1) (e2 : Term Σ σ2) : Term Σ σ3
  | term_neg     (e : Term Σ ty.int) : Term Σ ty.int
  | term_not     (e : Term Σ ty.bool) : Term Σ ty.bool
  | term_inl     {σ1 σ2 : Ty} : Term Σ σ1 -> Term Σ (ty.sum σ1 σ2)
  | term_inr     {σ1 σ2 : Ty} : Term Σ σ2 -> Term Σ (ty.sum σ1 σ2)
  | term_sext    {m n} {p : IsTrue (m <=? n)} (t : Term Σ (ty.bvec m)) : Term Σ (ty.bvec n)
  | term_zext    {m n} {p : IsTrue (m <=? n)} (t : Term Σ (ty.bvec m)) : Term Σ (ty.bvec n)
  | term_get_slice_int {n} (t : Term Σ ty.int) : Term Σ (ty.bvec n)
  | term_tuple   {σs} (ts : Env (Term Σ) σs) : Term Σ (ty.tuple σs)
  | term_union   {U : unioni} (K : unionk U) (t : Term Σ (unionk_ty U K)) : Term Σ (ty.union U)
  | term_record  (R : recordi) (ts : NamedEnv (Term Σ) (recordf_ty R)) : Term Σ (ty.record R).
  #[global] Arguments term_var {_} _ {_ _}.
  #[global] Arguments term_val {_} _ _.
  #[global] Arguments term_neg {_} _.
  #[global] Arguments term_not {_} _.
  #[global] Arguments term_inl {_ _ _} _.
  #[global] Arguments term_inr {_ _ _} _.
  #[global] Arguments term_sext {_ _ _ p} t.
  #[global] Arguments term_zext {_ _ _ p} t.
  #[global] Arguments term_get_slice_int {_ _} t.
  #[global] Arguments term_tuple {_ _} ts.
  #[global] Arguments term_union {_} U K t.
  #[global] Arguments term_record {_} R ts.
  Bind Scope exp_scope with Term.
  Derive NoConfusion Signature for Term.

  Definition term_enum {Σ} (E : enumi) (k : enumt E) : Term Σ (ty.enum E) :=
    term_val (ty.enum E) k.
  #[global] Arguments term_enum {_} _ _.

  Fixpoint term_list {Σ σ} (ts : list (Term Σ σ)) : Term Σ (ty.list σ) :=
    match ts with
    | nil       => term_val (ty.list σ) nil
    | cons t ts => term_binop bop.cons t (term_list ts)
    end.

  Fixpoint term_bvec {Σ n} (es : Vector.t (Term Σ ty.bool) n) : Term Σ (ty.bvec n) :=
    match es with
    | Vector.nil       => term_val (ty.bvec 0) bv.nil
    | Vector.cons e es => term_binop bop.bvcons e (term_bvec es)
    end.

  Definition term_relop_neg [Σ σ] (op : RelOp σ) :
    forall (t1 t2 : Term Σ σ), Term Σ ty.bool :=
    match op with
    | bop.eq     => term_binop (bop.relop bop.neq)
    | bop.neq    => term_binop (bop.relop bop.eq)
    | bop.le     => Basics.flip (term_binop (bop.relop bop.lt))
    | bop.lt     => Basics.flip (term_binop (bop.relop bop.le))
    | bop.bvsle  => Basics.flip (term_binop (bop.relop bop.bvslt))
    | bop.bvslt  => Basics.flip (term_binop (bop.relop bop.bvsle))
    | bop.bvule  => Basics.flip (term_binop (bop.relop bop.bvult))
    | bop.bvult  => Basics.flip (term_binop (bop.relop bop.bvule))
    end.

  Section Term_rect.

    Variable (Σ : LCtx).
    Variable (P  : forall t : Ty, Term Σ t -> Type).
    Arguments P _ _ : clear implicits.

    Let PE : forall (σs : Ctx Ty), Env (Term Σ) σs -> Type :=
      fun σs es => env.All P es.
    Let PNE : forall (σs : NCtx recordf Ty), NamedEnv (Term Σ) σs -> Type :=
      fun σs es => env.All (fun b t => P (type b) t) es.

    Hypothesis (P_var        : forall (ς : LVar) (σ : Ty) (ςInΣ : ς∷σ ∈ Σ), P σ (term_var ς)).
    Hypothesis (P_val        : forall (σ : Ty) (v : Val σ), P σ (term_val σ v)).
    Hypothesis (P_binop      : forall (σ1 σ2 σ3 : Ty) (op : BinOp σ1 σ2 σ3) (e1 : Term Σ σ1) (e2 : Term Σ σ2), P σ1 e1 -> P σ2 e2 -> P σ3 (term_binop op e1 e2)).
    Hypothesis (P_neg        : forall e : Term Σ ty.int, P ty.int e -> P ty.int (term_neg e)).
    Hypothesis (P_not        : forall e : Term Σ ty.bool, P ty.bool e -> P ty.bool (term_not e)).
    Hypothesis (P_inl        : forall (σ1 σ2 : Ty) (t : Term Σ σ1), P σ1 t -> P (ty.sum σ1 σ2) (term_inl t)).
    Hypothesis (P_inr        : forall (σ1 σ2 : Ty) (t : Term Σ σ2), P σ2 t -> P (ty.sum σ1 σ2) (term_inr t)).
    Hypothesis (P_sext       : forall {m n} {p : IsTrue (Nat.leb m n)} (t : Term Σ (ty.bvec m)), P (ty.bvec m) t -> P (ty.bvec n) (term_sext t)).
    Hypothesis (P_zext       : forall {m n} {p : IsTrue (Nat.leb m n)} (t : Term Σ (ty.bvec m)), P (ty.bvec m) t -> P (ty.bvec n) (term_zext t)).
    Hypothesis (P_get_slice_int : forall {n} (t : Term Σ ty.int), P ty.int t -> P (ty.bvec n) (term_get_slice_int t)).
    Hypothesis (P_tuple      : forall (σs : Ctx Ty) (es : Env (Term Σ) σs) (IH : PE es), P (ty.tuple σs) (term_tuple es)).
    Hypothesis (P_union      : forall (U : unioni) (K : unionk U) (e : Term Σ (unionk_ty U K)), P (unionk_ty U K) e -> P (ty.union U) (term_union U K e)).
    Hypothesis (P_record     : forall (R : recordi) (es : NamedEnv (Term Σ) (recordf_ty R)) (IH : PNE es), P (ty.record R) (term_record R es)).

    Fixpoint Term_rect (σ : Ty) (t : Term Σ σ) {struct t} : P σ t :=
      match t with
      | term_var ς          => ltac:(eapply P_var; eauto)
      | term_val σ v        => ltac:(eapply P_val; eauto)
      | term_binop op t1 t2 => ltac:(eapply P_binop; eauto)
      | term_neg t          => ltac:(eapply P_neg; eauto)
      | term_not t          => ltac:(eapply P_not; eauto)
      | term_inl t          => ltac:(eapply P_inl; eauto)
      | term_inr t          => ltac:(eapply P_inr; eauto)
      | term_sext t         => ltac:(eapply P_sext; eauto)
      | term_zext t         => ltac:(eapply P_zext; eauto)
      | term_get_slice_int t => ltac:(eapply P_get_slice_int; eauto)
      | term_tuple ts       => ltac:(eapply P_tuple, env.all_intro; eauto)
      | term_union U K t    => ltac:(eapply P_union; eauto)
      | term_record R ts    => ltac:(eapply P_record, env.all_intro; eauto)
      end.

  End Term_rect.

  Definition Term_rec Σ (P : forall σ, Term Σ σ -> Set) := @Term_rect _ P.
  Definition Term_ind Σ (P : forall σ, Term Σ σ -> Prop) := @Term_rect _ P.

  Open Scope lazy_bool_scope.

  Equations(noeqns) Term_eqb {Σ} [σ : Ty] (t1 t2 : Term Σ σ) : bool :=
    Term_eqb (@term_var _ _ ς1inΣ) (@term_var _ _ ς2inΣ) :=
      ctx.In_eqb ς1inΣ ς2inΣ;
    Term_eqb (term_val _ v1) (term_val _ v2) :=
      if eq_dec v1 v2 then true else false;
    Term_eqb (term_binop op1 x1 y1) (term_binop op2 x2 y2)
      with bop.eqdep_dec op1 op2 => {
      Term_eqb (term_binop op1 x1 y1) (term_binop ?(op1) x2 y2) (left bop.opeq_refl) :=
        Term_eqb x1 x2 &&& Term_eqb y1 y2;
      Term_eqb (term_binop op1 x1 y1) (term_binop op2 x2 y2) (right _) := false
    };
    Term_eqb (term_neg x) (term_neg y) := Term_eqb x y;
    Term_eqb (term_not x) (term_not y) := Term_eqb x y;
    Term_eqb (term_inl x) (term_inl y) := Term_eqb x y;
    Term_eqb (term_inr x) (term_inr y) := Term_eqb x y;
    Term_eqb (@term_sext _ m ?(k) p x) (@term_sext _ n k q y) with eq_dec m n => {
      Term_eqb (@term_sext _ m ?(k) p x) (@term_sext _ ?(m) k q y) (left eq_refl) :=
          Term_eqb x y;
      Term_eqb _ _ (right _) := false
    };
    Term_eqb (@term_zext _ m ?(k) p x) (@term_zext _ n k q y) with eq_dec m n => {
      Term_eqb (@term_zext _ m ?(k) p x) (@term_zext _ ?(m) k q y) (left eq_refl) :=
          Term_eqb x y;
      Term_eqb _ _ (right _) := false
    };
    Term_eqb (term_get_slice_int x) (term_get_slice_int y) := Term_eqb x y;
    Term_eqb (@term_tuple ?(σs) xs) (@term_tuple σs ys) :=
       @env.eqb_hom _ (Term Σ) (@Term_eqb _ ) _ xs ys;
    Term_eqb (@term_union ?(u) _ k1 e1) (@term_union u _ k2 e2)
      with eq_dec k1 k2 => {
      Term_eqb (term_union k1 e1) (term_union ?(k1) e2) (left eq_refl) :=
        Term_eqb e1 e2;
      Term_eqb _ _ (right _) := false
    };
    Term_eqb (@term_record ?(r) xs) (@term_record r ys) :=
       @env.eqb_hom _ (fun b => Term Σ (type b)) (fun b => @Term_eqb _ (type b)) _ xs ys;
    Term_eqb _ _ := false.

  Local Set Equations With UIP.
  Lemma Term_eqb_spec Σ (σ : Ty) (t1 t2 : Term Σ σ) :
    reflect (t1 = t2) (Term_eqb t1 t2).
  Proof.
    induction t1 using Term_rect; cbn [Term_eqb]; dependent elimination t2;
      solve_eqb_spec with
      try match goal with
          | |- context[eq_dec ?l1 ?l2] => destruct (eq_dec l1 l2)
          | |- context[bop.eqdep_dec ?x ?y] =>
              let e := fresh in
              destruct (bop.eqdep_dec x y) as [e|];
              [dependent elimination e|]
          | H: ~ bop.OpEq ?o ?o |- False => apply H; constructor
          | p : IsTrue (?m <=? ?n), q : IsTrue (?m <=? ?n) |- _ =>
            destruct (IsTrue.proof_irrelevance p q)
          end.
    - apply (@ssrbool.iffP (es = ts)); solve_eqb_spec.
      apply env.eqb_hom_spec_point, IH.
    - apply (@ssrbool.iffP (es = ts0)); solve_eqb_spec.
      apply env.eqb_hom_spec_point, IH.
  Qed.

  Section Symbolic.

    Polymorphic Definition List (A : LCtx -> Type) (Σ : LCtx) : Type :=
      list (A Σ).
    Definition Const (A : Type) (Σ : LCtx) : Type :=
      A.

  End Symbolic.

  Section SymbolicSubstitutions.

    Definition Sub (Σ1 Σ2 : LCtx) : Set :=
      Env (fun b => Term Σ2 (type b)) Σ1.
    (* Hint Unfold Sub. *)

    Class Subst (T : LCtx -> Type) : Type :=
      subst : forall {Σ1 : LCtx}, T Σ1 -> forall {Σ2 : LCtx}, Sub Σ1 Σ2 -> T Σ2.
    #[global] Arguments subst {T _ Σ1} t {Σ2} ζ.

    Fixpoint sub_term {σ Σ1} (t : Term Σ1 σ) {Σ2} (ζ : Sub Σ1 Σ2) {struct t} : Term Σ2 σ :=
      match t with
      | term_var ς                => ζ.[??ς]
      | term_val σ v              => term_val σ v
      | term_binop op t1 t2       => term_binop op (sub_term t1 ζ) (sub_term t2 ζ)
      | term_neg t0               => term_neg (sub_term t0 ζ)
      | term_not t0               => term_not (sub_term t0 ζ)
      | @term_inl _ σ1 σ2 t0      => term_inl (sub_term t0 ζ)
      | @term_inr _ σ1 σ2 t0      => term_inr (sub_term t0 ζ)
      | term_sext t               => term_sext (sub_term t ζ)
      | term_zext t               => term_zext (sub_term t ζ)
      | term_get_slice_int t      => term_get_slice_int (sub_term t ζ)
      | term_tuple ts             => term_tuple (env.map (fun _ t => sub_term t ζ) ts)
      | term_union U K t          => term_union U K (sub_term t ζ)
      | term_record R ts          => term_record R (env.map (fun _ t => sub_term t ζ) ts)
      end.

    #[export] Instance SubstTerm {σ} : Subst (fun Σ => Term Σ σ) :=
      @sub_term σ.
    #[export,universes(polymorphic=yes)] Instance SubstList {A} `{Subst A} : Subst (List A) :=
      fix substlist {Σ1} xs {Σ2} ζ :=
        match xs with
        | nil => nil
        | cons x xs => cons (subst x ζ) (substlist xs ζ)
        end.

    Lemma substlist_is_map_subst {A} `{Subst A} {Σ1 Σ2} (xs : List A Σ1) (ζ : Sub Σ1 Σ2) :
      subst xs ζ = List.map (fun x => subst x ζ) xs.
    Proof. induction xs; cbn; f_equal; auto. Qed.

    #[export] Instance SubstConst {A} : Subst (Const A) | 10 :=
       fun _ x _ _ => x.
    #[export] Instance SubstEnv {B : Set} {A : Ctx _ -> B -> Set} `{forall b, Subst (fun Σ => A Σ b)} {Δ : Ctx B} :
      Subst (fun Σ => Env (A Σ) Δ) :=
      fun Σ1 xs Σ2 ζ => env.map (fun b a => subst (T := fun Σ => A Σ b) a ζ) xs.

    Definition sub_id Σ : Sub Σ Σ :=
      @env.tabulate _ (fun b => Term _ (type b)) _
                    (fun '(ς∷σ) ςIn => @term_var Σ ς σ ςIn).
    #[global] Arguments sub_id : clear implicits.

    Definition sub_snoc {Σ1 Σ2 : LCtx} (ζ : Sub Σ1 Σ2) b (t : Term Σ2 (type b)) :
      Sub (Σ1 ▻ b) Σ2 := env.snoc ζ b t.
    #[global] Arguments sub_snoc {_ _} _ _ _.

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

    Definition sub_single {Σ x} (xIn : x ∈ Σ) (t : Term (Σ - x) (type x)) : Sub Σ (Σ - x) :=
       @env.tabulate _
         (fun b => Term (Σ - x) (@type _ _ b)) Σ
         (fun y (yIn : y ∈ Σ) =>
            match ctx.occurs_check_view xIn yIn
            in @ctx.OccursCheckView _ _ _ _ y i
            return Term (Σ - x) (@type _ _ y)
            with
            | ctx.Same _     => t
            | ctx.Diff _ yIn => @term_var _ _ _ yIn
            end).

    Class SubstLaws (T : LCtx -> Type) `{Subst T} : Type :=
      { subst_sub_id Σ (t : T Σ) :
          subst t (sub_id _) = t;
        subst_sub_comp Σ0 Σ1 Σ2 (ζ1 : Sub Σ0 Σ1) (ζ2 : Sub Σ1 Σ2) t :
          subst t (subst ζ1 ζ2) = subst (subst t ζ1) ζ2;
      }.

    #[global] Arguments SubstLaws T {_}.

    #[export] Instance SubstLawsTerm {σ} : SubstLaws (fun Σ => Term Σ σ).
    Proof.
      constructor.
      { intros ? t.
        induction t; cbn; f_equal; try assumption.
        - unfold sub_id. now rewrite env.lookup_tabulate.
        - induction IH; cbn; f_equal; auto.
        - induction IH; cbn; f_equal; auto.
      }
      { intros ? ? ? ? ? t.
        induction t; cbn; f_equal; try assumption.
        - unfold subst at 1, SubstEnv. now rewrite env.lookup_map.
        - induction IH; cbn; f_equal; auto.
        - induction IH; cbn; f_equal; auto.
      }
    Qed.

    #[export,universes(polymorphic=yes)] Instance SubstLawsList {A} `{SubstLaws A} : SubstLaws (List A).
    Proof.
      constructor.
      { intros ? t.
        induction t; cbn; f_equal; auto using subst_sub_id.
      }
      { intros ? ? ? ? ? t.
        induction t; cbn; f_equal; auto using subst_sub_comp.
      }
    Qed.

    #[export] Instance SubstLawsConst {A} : SubstLaws (Const A).
    Proof. constructor; reflexivity. Qed.

    #[export] Instance SubstLawsEnv {B : Set} {A : Ctx _ -> B -> Set}
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

    #[export] Instance subst_ctx `{Subst A} : Subst (fun Σ => Ctx (A Σ)) :=
      fix subst_ctx {Σ} xs {Σ'} ζ {struct xs} :=
        match xs with
        | ctx.nil       => ctx.nil
        | ctx.snoc xs x => ctx.snoc (subst_ctx xs ζ) (subst x ζ)
        end.

    #[export] Instance substlaws_ctx `{SubstLaws A} : SubstLaws (fun Σ => Ctx (A Σ)).
    Proof.
      constructor.
      - intros ? xs. induction xs; cbn; f_equal; auto; apply subst_sub_id.
      - intros ? ? ? ? ? xs; induction xs; cbn; f_equal; auto; apply subst_sub_comp.
    Qed.

  End SymbolicSubstitutions.

  Module SubNotations.

    Notation "a ⟨ ζ ⟩" := (subst a ζ).
    Notation "ζ1 ∘ ζ2" := (@subst (Sub _) _ _ ζ1 _ ζ2).

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
    Proof. unfold sub_single. now rewrite env.lookup_tabulate, ctx.occurs_check_view_refl. Qed.

    Lemma lookup_sub_single_neq {Σ x σ y τ} (xIn : x ∷ σ ∈ Σ) (t : Term (Σ - x∷σ) σ) (yIn : y∷τ ∈ Σ - x∷σ) :
      env.lookup (sub_single xIn t) (ctx.shift_var xIn yIn) = term_var y.
    Proof. unfold sub_single. now rewrite env.lookup_tabulate, ctx.occurs_check_view_shift. Qed.

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
      now destruct (env.view ζ) as [ζ t].
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
      destruct (ctx.view yIn) as [|[y τ] yIn].
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

  Section SymbolicPair.

    Definition Pair (A B : LCtx -> Type) (Σ : LCtx) : Type :=
      A Σ * B Σ.
    #[export] Instance SubstPair {A B} `{Subst A, Subst B} : Subst (Pair A B) :=
      fun _ '(a,b) _ ζ => (subst a ζ, subst b ζ).

    #[export] Instance SubstLawsPair {A B} `{SubstLaws A, SubstLaws B} : SubstLaws (Pair A B).
    Proof.
      constructor.
      { intros ? [t1 t2]; cbn.
        f_equal; apply subst_sub_id.
      }
      { intros ? ? ? ? ? [t1 t2]; cbn.
        f_equal; apply subst_sub_comp.
      }
    Qed.

  End SymbolicPair.

  Section SymbolicOption.

    Definition Option (A : LCtx -> Type) (Σ : LCtx) : Type :=
      option (A Σ).
    #[export] Instance SubstOption {A} `{Subst A} : Subst (Option A) :=
      fun _ ma _ ζ => option_map (fun a => subst a ζ) ma.

    #[export] Instance SubstLawsOption {A} `{SubstLaws A} : SubstLaws (Option A).
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


  End SymbolicOption.

  Section SymbolicUnit.

    Definition Unit : LCtx -> Type := fun _ => unit.
    #[export] Instance SubstUnit : Subst Unit :=
      fun _ t _ _ => t.
    #[export] Instance SubstLawsUnit : SubstLaws Unit.
    Proof. constructor; reflexivity. Qed.

  End SymbolicUnit.

  Section SymbolicStore.

    Definition SStore (Γ : PCtx) (Σ : LCtx) : Type :=
      NamedEnv (Term Σ) Γ.

    #[export] Instance subst_localstore {Γ} : Subst (SStore Γ) :=
      SubstEnv.
    #[export] Instance substlaws_localstore {Γ} : SubstLaws (SStore Γ) :=
      SubstLawsEnv.

    Lemma subst_lookup {Γ Σ Σ' x σ} (xInΓ : x∷σ ∈ Γ) (ζ : Sub Σ Σ') (δ : SStore Γ Σ) :
      subst δ.[?? x] ζ = (subst δ ζ).[?? x].
    Proof.
      unfold subst at 2, subst_localstore, SubstEnv.
      now rewrite env.lookup_map.
    Qed.

  End SymbolicStore.
  Bind Scope env_scope with SStore.

End TermsOn.
