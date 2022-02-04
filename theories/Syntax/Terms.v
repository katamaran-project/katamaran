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
     Bool.Bool.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Context
     Environment
     Notations
     Prelude
     Syntax.BinOps
     Syntax.TypeDecl
     Syntax.TypeDef
     Syntax.Variables
     Tactics.

Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.
Local Set Transparent Obligations.
Local Unset Elimination Schemes.

Module Type TermsOn (Import TY : Types) (Import BO : BinOpsOn TY).

  Local Notation PCtx := (NCtx 𝑿 Ty).
  Local Notation LCtx := (NCtx 𝑺 Ty).

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
  Bind Scope exp_scope with Term.
  Derive NoConfusion Signature for Term.

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
    | env.nil         => term_val (ty_tuple []) tt
    | env.snoc es _ e => term_binop binop_tuple_snoc (term_tuple es) e
    end.

  Fixpoint term_bvec {Σ n} (es : Vector.t (Term Σ ty_bit) n) : Term Σ (ty_bvec n) :=
    match es with
    | Vector.nil       => term_val (ty_bvec 0) bv.nil
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
    (* Hypothesis (P_bv         : forall (n : nat) (es : Vector.t (Term Σ ty_bit) n), PV es -> P (ty_bv n) (term_bv es)). *)
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

  Equations(noeqns) Term_eqb {Σ} [σ : Ty] (t1 t2 : Term Σ σ) : bool :=
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
        (Nat.eqb n m) && Term_eqb x y;
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

  Section Symbolic.

    Definition List (A : LCtx -> Type) (Σ : LCtx) : Type :=
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
    Global Arguments subst {T _ Σ1} t {Σ2} ζ.

    Fixpoint sub_term {σ Σ1} (t : Term Σ1 σ) {Σ2} (ζ : Sub Σ1 Σ2) {struct t} : Term Σ2 σ :=
      match t with
      | term_var ς                => ζ.[??ς]
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


  End SymbolicOption.

  Section SymbolicUnit.

    Definition Unit : LCtx -> Type := fun _ => unit.
    Global Instance SubstUnit : Subst Unit :=
      fun _ t _ _ => t.
    Global Instance SubstLawsUnit : SubstLaws Unit.
    Proof. constructor; reflexivity. Qed.

  End SymbolicUnit.

  Section SymbolicStore.

    Definition SStore (Γ : PCtx) (Σ : LCtx) : Type :=
      NamedEnv (Term Σ) Γ.

    Global Instance subst_localstore {Γ} : Subst (SStore Γ) :=
      SubstEnv.
    Global Instance substlaws_localstore {Γ} : SubstLaws (SStore Γ) :=
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
