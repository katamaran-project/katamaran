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
     Classes.Morphisms
     Classes.Morphisms_Prop
     Classes.RelationClasses
     NArith.BinNat
     Program.Basics
     Relations.Relation_Definitions
     Strings.String
     ZArith.BinInt.

From Equations Require Import
     Equations.
From Katamaran Require Import
     Environment
     Notations
     Prelude
     Syntax.BinOps
     Syntax.Terms
     Syntax.TypeDecl
     Syntax.Variables
     Tactics.

Import base (Equiv, equiv).
Import (notations) base.
Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.

Module Type InstantiationOn
  (Import TY : Types)
  (Import TM : TermsOn TY).

  Local Notation LCtx := (NCtx LVar Ty).
  Local Notation Valuation Σ := (Env (fun xt : Binding LVar Ty => Val (type xt)) Σ).
  Local Notation CStore := (@NamedEnv PVar Ty Val).

  (* This type class connects a symbolic representation of a type with its
     concrete / semi-concrete counterpart. The method 'inst' will instantiate
     all logic variables in a symbolic value to obtain the concrete value and
     'lift' injects the concrete type into the symbolic one. *)
  Class Inst (T : LCtx -> Type) (A : Type) : Type :=
    inst : forall {Σ}, T Σ -> Valuation Σ -> A.
  Class Lift (T : LCtx -> Type) (A : Type) : Type :=
    lift : forall {Σ}, A -> T Σ.
  #[global] Arguments inst {T A _ Σ} !_ ι.
  #[global] Arguments lift {T A _ Σ} !_.

  #[export] Instance inst_list {T : LCtx -> Type} {A : Type} `{Inst T A} :
    Inst (List T) (list A) := fun Σ xs ι => List.map (fun x => inst x ι) xs.
  #[export] Instance lift_list {T : LCtx -> Type} {A : Type} `{Lift T A} :
    Lift (List T) (list A) := fun Σ => List.map lift.

  #[export] Instance inst_const {A} : Inst (Const A) A | 10 := fun Σ x ι => x.
  #[export] Instance lift_const {A} : Lift (Const A) A | 10 := fun Σ x => x.

  #[export] Instance inst_env {T : Set} {S : LCtx -> T -> Set} {A : T -> Set}
    {InstSA : forall τ : T, Inst (fun Σ => S Σ τ) (A τ)} {Γ : Ctx T} :
    Inst (fun Σ => Env (S Σ) Γ) (Env A Γ) :=
    fun Σ xs ι => env.map (fun (b : T) (s : S Σ b) => inst s ι) xs.
  #[export] Instance lift_env {T : Set} {S : LCtx -> T -> Set} {A : T -> Set}
    {InstSA : forall τ : T, Lift (fun Σ => S Σ τ) (A τ)} {Γ : Ctx T} :
    Lift (fun Σ => Env (S Σ) Γ) (Env A Γ) :=
    fun Σ => env.map (fun (b : T) (a : A b) => lift a).

  Lemma inst_env_snoc {B : Set} {AT : LCtx -> B -> Set}
    {A : B -> Set} {_ : forall b : B, Inst (fun Σ => AT Σ b) (A b)}
    {Γ : Ctx B} {Σ} (ι : Valuation Σ) (E : Env (AT Σ) Γ) (b : B) (a : AT Σ b) :
    inst (env.snoc E b a) ι = env.snoc (inst E ι) b (inst a ι).
  Proof. reflexivity. Qed.

  #[export] Instance inst_term : forall {σ}, Inst (fun Σ => Term Σ σ) (Val σ) :=
    fix inst_term {σ : Ty} [Σ : LCtx] (t : Term Σ σ) (ι : Valuation Σ) {struct t} : Val σ :=
    match t in Term _ σ return Val σ with
    | @term_var _ _ _ bIn  => env.lookup ι bIn
    | term_val _ v         => v
    | term_binop op t1 t2  => bop.eval op
                                (inst (Inst := @inst_term _) t1 ι)
                                (inst (Inst := @inst_term _) t2 ι)
    | term_neg t           => Z.opp (inst_term t ι)
    | term_not t           => negb (inst_term t ι)
    | term_inl t           => @inl (Val _) (Val _) (inst (Inst := inst_term) t ι)
    | term_inr t           => @inr (Val _) (Val _) (inst (Inst := inst_term) t ι)
    | term_sext t          => bv.sext (inst (Inst := inst_term) t ι)
    | term_zext t          => bv.zext (inst (Inst := inst_term) t ι)
    | @term_tuple _ σs ts  =>
        envrec.of_env (inst (Inst := inst_env (InstSA := @inst_term)) ts ι)
    | @term_union _ U K t     => unionv_fold U (existT K (inst (Inst := inst_term) t ι))
    | @term_record _ R ts     =>
        let InstTerm xt := @inst_term (@type recordf Ty xt) in
        recordv_fold R (inst (Inst := inst_env (InstSA := InstTerm)) ts ι)
    end.
  #[export] Instance lift_term {σ} : Lift (fun Σ => Term Σ σ) (Val σ) :=
    fun Σ v => term_val σ v.

  #[export] Instance inst_sub {Σ} : Inst (Sub Σ) (Valuation Σ) :=
    inst_env.

  Class InstSubst (T : LCtx -> Type) (A : Type) `{Inst T A, Subst T} : Prop :=
    inst_subst : forall {Σ Σ'} (ζ : Sub Σ Σ') (ι : Valuation Σ') (t : T Σ),
        inst (subst t ζ) ι = inst t (inst ζ ι).
  Class InstLift (T : LCtx -> Type) (A : Type) `{Inst T A, Lift T A} : Prop :=
    inst_lift : forall {Σ} (ι : Valuation Σ) (a : A),
        inst (lift a) ι = a.

  Arguments InstSubst T A {_ _}.
  Arguments InstLift T A {_ _}.

  #[export] Instance inst_subst_list {T : LCtx -> Set} {A : Set} `{InstSubst T A} :
    InstSubst (List T) (list A).
  Proof.
    intros ? ? ζ ι xs.
    rewrite substlist_is_map_subst.
    unfold inst, inst_list at 1.
    rewrite List.map_map.
    apply List.map_ext, inst_subst.
  Qed.

  #[export] Instance inst_lift_list {T : LCtx -> Set} {A : Set} `{InstLift T A} :
    InstLift (List T) (list A).
  Proof.
    intros Σ ι a. unfold inst, inst_list, lift, lift_list.
    rewrite List.map_map, <- List.map_id.
    apply List.map_ext, inst_lift.
  Qed.

  #[export] Instance inst_subst_const {A} `{finite.Finite A} :
    InstSubst (Const A) A.
  Proof. intros ? ? ζ ι t. reflexivity. Qed.

  #[export] Instance inst_lift_const {A} `{finite.Finite A} :
    InstLift (Const A) A.
  Proof. intros ? ι a. reflexivity. Qed.

  #[export] Instance inst_subst_env {T : Set} {S : LCtx -> T -> Set} {A : T -> Set}
         {_ : forall τ : T, Inst (fun Σ => S Σ τ) (A τ)}
         {_ : forall τ : T, Subst (fun Σ => S Σ τ)}
         {_ : forall τ : T, InstSubst (fun Σ => S Σ τ) (A τ)}
         {Γ : Ctx T} :
    InstSubst (fun Σ => Env (S Σ) Γ) (Env A Γ).
  Proof.
    intros ? ? ζ ι E.
    unfold inst, inst_env, subst, SubstEnv at 1.
    rewrite env.map_map. apply env.map_ext.
    intros b s; apply inst_subst.
  Qed.

  #[export] Instance inst_lift_env {T : Set} {S : LCtx -> T -> Set} {A : T -> Set}
         {_ : forall τ : T, Inst (fun Σ => S Σ τ) (A τ)}
         {_ : forall τ : T, Lift (fun Σ => S Σ τ) (A τ)}
         {_ : forall τ : T, InstLift (fun Σ => S Σ τ) (A τ)}
         {Γ : Ctx T} :
    InstLift (fun Σ => Env (S Σ) Γ) (Env A Γ).
  Proof.
    intros ? ι E.
    unfold inst, inst_env, lift, lift_env.
    rewrite env.map_map. apply env.map_id_eq.
    intros; apply inst_lift.
  Qed.

  #[export] Instance inst_subst_term {σ} : InstSubst (fun Σ => Term Σ σ) (Val σ).
  Proof.
    unfold InstSubst.
    induction t; cbn; try (repeat f_equal; auto; fail).
    - unfold inst, inst_sub, inst_env.
      now rewrite env.lookup_map.
    - f_equal. induction IH; cbn; now f_equal.
    - f_equal. induction IH; cbn; now f_equal.
  Qed.

  #[export] Instance inst_lift_term {σ} : InstLift (fun Σ => Term Σ σ) (Val σ).
  Proof. red. reflexivity. Qed.

  Lemma inst_term_relop_neg [Σ σ] (op : RelOp σ) (t1 t2 : Term Σ σ) :
    forall (ι : Valuation Σ),
      inst (T := fun Σ => Term Σ ty.bool) (term_relop_neg op t1 t2) ι =
        negb (bop.eval_relop_val op (inst t1 ι) (inst t2 ι)).
  Proof.
    destruct op; cbn; intros; unfold bv.sltb, bv.sleb, bv.ultb, bv.uleb;
      rewrite ?negb_involutive, <- ?Z.leb_antisym, <- ?Z.ltb_antisym,
      <- ?N.leb_antisym, <- ?N.ltb_antisym; try easy; try now destruct eq_dec.
  Qed.

  #[export] Instance inst_subst_sub {Σ} : InstSubst (Sub Σ) (Valuation Σ).
  Proof. apply inst_subst_env. Qed.

  #[export] Instance inst_lift_sub {Σ} : InstLift (Sub Σ) (Valuation Σ).
  Proof. apply inst_lift_env. Qed.

  Lemma inst_sub_wk1 {Σ b v} (ι : Valuation Σ) :
    inst sub_wk1 (ι ► (b ↦ v)) = ι.
  Proof.
    apply env.lookup_extensional. intros [x σ] ?.
    unfold inst, inst_sub, inst_env, sub_wk1.
    now rewrite env.map_tabulate, env.lookup_tabulate.
  Qed.

  Lemma inst_sub_id {Σ} (ι : Valuation Σ) :
    inst (sub_id Σ) ι = ι.
  Proof.
    apply env.lookup_extensional. intros [x τ] ?.
    unfold inst, inst_sub, inst_env, sub_id.
    now rewrite env.map_tabulate, env.lookup_tabulate.
  Qed.

  Lemma inst_sub_snoc {Σ0 Σ1} (ι : Valuation Σ1) (ζ : Sub Σ0 Σ1) b (t : Term Σ1 (type b)) :
    inst (sub_snoc ζ b t) ι = env.snoc (inst ζ ι) b (inst t ι).
  Proof. reflexivity. Qed.

  Lemma inst_env_cat {T : Set} {AT : LCtx -> T -> Set} {A : T -> Set}
     {instAT : forall τ : T, Inst (fun Σ : LCtx => AT Σ τ) (A τ)}
     {Σ : LCtx} {Γ Δ : Ctx T} (EΓ : Env (fun τ => AT Σ τ) Γ) (EΔ : Env (fun τ => AT Σ τ) Δ)
     (ι : Valuation Σ) :
    inst (EΓ ►► EΔ) ι = inst EΓ ι ►► inst EΔ ι.
  Proof.
    unfold inst, inst_env; cbn.
    now rewrite env.map_cat.
  Qed.

  Lemma inst_sub_cat {Σ Γ Δ : LCtx} (ζΓ : Sub Γ Σ) (ζΔ : Sub Δ Σ) (ι : Valuation Σ) :
    inst (A := Valuation _) (ζΓ ►► ζΔ) ι = inst ζΓ ι ►► inst ζΔ ι.
  Proof.
    apply (@inst_env_cat (LVar ∷ Ty) (fun Σ b => Term Σ (type b))).
  Qed.

  Lemma inst_sub_cat_left {Σ Δ : LCtx} (ι : Valuation Δ) (ιΔ : Valuation Σ) :
    inst (sub_cat_left Δ) (ιΔ ►► ι) = ιΔ.
  Proof.
    eapply env.lookup_extensional.
    intros b bInΔ.
    unfold inst, inst_sub, inst_env, sub_cat_left.
    rewrite ?env.lookup_map, env.lookup_tabulate. cbn.
    now rewrite env.lookup_cat_left.
  Qed.

  Lemma inst_sub_cat_right {Σ Δ : LCtx} (ι : Valuation Δ) (ιΔ : Valuation Σ) :
    inst (sub_cat_right Δ) (ιΔ ►► ι) = ι.
  Proof.
    eapply env.lookup_extensional.
    intros b bInΔ.
    unfold inst, inst_sub, inst_env, sub_cat_right.
    rewrite ?env.lookup_map, env.lookup_tabulate. cbn.
    now rewrite env.lookup_cat_right.
  Qed.

  Lemma inst_sub_up1 {Σ1 Σ2 b} (ζ12 : Sub Σ1 Σ2) (ι2 : Valuation Σ2) (v : Val (type b)) :
    inst (sub_up1 ζ12) (ι2 ► (b ↦ v)) = inst ζ12 ι2 ► (b ↦ v).
  Proof.
    destruct b; unfold sub_up1.
    now rewrite inst_sub_snoc, inst_subst, inst_sub_wk1.
  Qed.

  Lemma inst_sub_up {Σ1 Σ2 Δ} (ζ12 : Sub Σ1 Σ2) (ι2 : Valuation Σ2) (ι : Valuation Δ) :
    inst (sub_up ζ12 Δ) (ι2 ►► ι) = inst ζ12 ι2 ►► ι.
  Proof.
    unfold sub_up.
    now rewrite inst_sub_cat, inst_subst, inst_sub_cat_left, inst_sub_cat_right.
  Qed.

  Lemma inst_sub_shift {Σ} (ι : Valuation Σ) {b} (bIn : b ∈ Σ) :
    inst (sub_shift bIn) ι = env.remove b ι bIn.
  Proof.
    rewrite env.remove_remove'.
    apply env.lookup_extensional. intros [y τ] yIn.
    unfold env.remove', sub_shift, inst, inst_sub, inst_env.
    now rewrite env.lookup_map, ?env.lookup_tabulate.
  Qed.

  Lemma inst_sub_single_shift {Σ} (ι : Valuation Σ) {x σ} (xIn : x∷σ ∈ Σ) (t : Term (Σ - x∷σ) σ) :
    inst t (inst (sub_shift xIn) ι) = env.lookup ι xIn ->
    inst (sub_single xIn t) (inst (sub_shift xIn) ι) = ι.
  Proof.
    rewrite inst_sub_shift, env.remove_remove'. intros HYP.
    apply env.lookup_extensional. intros [y τ] yIn.
    unfold inst, inst_sub, inst_env, sub_single; cbn.
    rewrite env.lookup_map, env.lookup_tabulate.
    pose proof (ctx.occurs_check_var_spec xIn yIn).
    destruct (ctx.occurs_check_var xIn yIn).
    * dependent elimination e. subst yIn. exact HYP.
    * destruct H; subst yIn. cbn. unfold env.remove'.
      now rewrite env.lookup_tabulate.
  Qed.

  Lemma sub_single_zero {Σ : LCtx} {x : LVar} {σ : Ty} (t : Term Σ σ) :
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
    apply env.lookup_extensional. intros y yIn.
    unfold env.insert', sub_single, inst, inst_sub, inst_env; cbn.
    rewrite env.lookup_map, ?env.lookup_tabulate.
    destruct (ctx.occurs_check_view xIn yIn).
    - now rewrite ctx.occurs_check_var_refl.
    - now rewrite ctx.occurs_check_shift_var.
  Qed.

  Lemma inst_lookup {Σ0 Σ1} (ι : Valuation Σ1) (ζ : Sub Σ0 Σ1) x τ (xIn : x∷τ ∈ Σ0) :
    inst (env.lookup ζ xIn) ι = env.lookup (inst (A := Valuation Σ0) ζ ι) xIn.
  Proof. unfold inst, inst_sub, inst_env. now rewrite env.lookup_map. Qed.

  #[export] Instance inst_unit : Inst Unit unit :=
    fun _ x ι => x.
  #[export] Instance lift_unit : Lift Unit unit :=
    fun _ x => x.

  #[export] Instance inst_subst_unit : InstSubst Unit unit.
  Proof. red. reflexivity. Qed.
  #[export] Instance inst_lift_unit : InstLift Unit unit.
  Proof. red. reflexivity. Qed.

  #[export] Instance inst_pair {AT BT A B} `{Inst AT A, Inst BT B} :
    Inst (Pair AT BT) (A * B) :=
    fun Σ '(a , b) ι => (inst a ι, inst b ι).
  #[export] Instance lift_pair {AT BT A B} `{Lift AT A, Lift BT B} :
    Lift (Pair AT BT) (A * B) :=
    fun Σ '(a, b) => (lift a , lift b).

  #[export] Instance inst_subst_pair {AT BT A B} `{InstSubst AT A, InstSubst BT B} :
    InstSubst (Pair AT BT) (A * B).
  Proof. intros ? ? ? ? []; cbn; f_equal; apply inst_subst. Qed.

  #[export] Instance inst_lift_pair {AT BT A B} `{InstLift AT A, InstLift BT B} :
    InstLift (Pair AT BT) (A * B).
  Proof. intros ? ? []; cbn; f_equal; apply inst_lift. Qed.

  #[export] Instance inst_option {AT A} `{Inst AT A} : Inst (Option AT) (option A) :=
    fun Σ ma ι => option_map (fun a => inst a ι) ma.
  #[export] Instance lift_option {AT A} `{Lift AT A} : Lift (Option AT) (option A) :=
    fun Σ ma => option_map lift ma.

  #[export] Instance inst_subst_option {AT A} `{InstSubst AT A} :
    InstSubst (Option AT) (option A).
  Proof. intros ? ? ? ? []; cbn; f_equal; apply inst_subst. Qed.
  #[export] Instance inst_lift_option {AT A} `{InstLift AT A} :
    InstLift (Option AT) (option A).
  Proof. intros ? ? []; cbn; f_equal; apply inst_lift. Qed.

  #[export] Instance inst_store {Γ} : Inst (SStore Γ) (CStore Γ) :=
    inst_env.
  #[export] Instance inst_subst_store {Γ} : InstSubst (SStore Γ) (CStore Γ).
  Proof. apply inst_subst_env. Qed.
  #[export] Instance inst_lift_store {Γ} : InstLift (SStore Γ) (CStore Γ).
  Proof. apply inst_lift_env. Qed.

  Section SemanticEquivalence.

    Definition SEquiv T V {instTV : Inst T V} (Σ : LCtx) : relation (T Σ) :=
      fun s t => forall (ι : Valuation Σ), inst s ι = inst t ι.
    #[global] Typeclasses Opaque SEquiv.
    #[global] Arguments SEquiv T V {_} Σ.

    Definition seequiv_equivalence {T V} {instTV : Inst T V} {Σ} :
      Equivalence (SEquiv T V Σ).
    Proof.
      constructor. easy. easy. intros x y z ? ? ι.
      now transitivity (inst y ι).
    Qed.

    #[export] Instance term_equiv {Σ σ} : base.Equiv (Term Σ σ) :=
      SEquiv (fun Σ => Term Σ σ) (Val σ) Σ.
    #[export] Instance term_equivalence {Σ σ} : Equivalence (≡@{Term Σ σ}) :=
      seequiv_equivalence.
    #[export] Typeclasses Opaque term_equiv.

    #[export] Instance env_equiv {Σ σs} : base.Equiv (Env (Term Σ) σs) :=
      SEquiv (fun Σ => Env (Term Σ) σs) (Env Val σs) Σ.
    #[export] Instance seenv_equivalence {Σ σs} : Equivalence (≡@{Env (Term Σ) σs}) :=
      seequiv_equivalence.

    #[export] Instance nenv_equiv {N Σ} {Δ : NCtx N Ty} :
      base.Equiv (NamedEnv (Term Σ) Δ) :=
      SEquiv (fun Σ => NamedEnv (Term Σ) Δ) (NamedEnv Val Δ) Σ.
    #[export] Instance senamedenv_equivalence {N Σ} {Δ : NCtx N Ty} :
      Equivalence (≡@{NamedEnv (Term Σ) Δ}) :=
      seequiv_equivalence.

    #[local] Obligation Tactic :=
      repeat intro; cbn; f_equal; constructor_congruence; solve [ eauto ].

    #[export,program] Instance proper_term_binop {σ1 σ2 σ3} (op : BinOp σ1 σ2 σ3) [Σ] :
      Proper ((≡) ==> (≡) ==> (≡)) (term_binop (Σ:=Σ) op).
    #[export,program] Instance proper_term_neg {Σ} : Proper ((≡) ==> (≡)) (term_neg (Σ:=Σ)).
    #[export,program] Instance proper_term_not {Σ} : Proper ((≡) ==> (≡)) (term_not (Σ:=Σ)).
    #[export,program] Instance proper_term_inl {Σ σ1 σ2} : Proper ((≡) ==> (≡)) (@term_inl Σ σ1 σ2).
    #[export,program] Instance proper_term_inr {Σ σ1 σ2} : Proper ((≡) ==> (≡)) (@term_inr Σ σ1 σ2).
    #[export,program] Instance proper_term_sext {Σ m n p} : Proper ((≡) ==> (≡)) (@term_sext Σ m n p).
    #[export,program] Instance proper_term_zext {Σ m n p} : Proper ((≡) ==> (≡)) (@term_zext Σ m n p).
    #[export,program] Instance proper_term_tuple {Σ σs} : Proper ((≡) ==> (≡)) (@term_tuple Σ σs).
    #[export,program] Instance proper_term_union {Σ U K} : Proper ((≡) ==> (≡)) (@term_union Σ U K).
    #[export,program] Instance proper_term_record {Σ R} : Proper ((≡) ==> (≡)) (@term_record Σ R).
    #[export,program] Instance proper_env_snoc {Σ σs} :
      Proper ((≡) ==> forall_relation (fun σ => (≡) ==> (≡)))
        (@env.snoc _ (Term Σ) σs).
    #[export,program] Instance proper_namedenv_snoc {N Σ} {Δ : NCtx N Ty} :
      Proper ((≡) ==> forall_relation (fun b : N∷Ty => (≡) ==> (≡)))
        (@env.snoc _ (fun b => Term Σ (type b)) Δ).

    Lemma term_orb_false_l [Σ] (b : Term Σ ty.bool) :
      term_binop bop.or (term_val ty.bool false) b ≡ b.
    Proof. intro ι; reflexivity. Qed.
    Lemma term_orb_false_r [Σ] (b : Term Σ ty.bool) :
      term_binop bop.or b (term_val ty.bool false) ≡ b.
    Proof. intro ι; apply orb_false_r. Qed.
    Lemma term_orb_true_l [Σ] (b : Term Σ ty.bool) :
      term_binop bop.or (term_val ty.bool true) b ≡ term_val ty.bool true.
    Proof. intro ι; reflexivity. Qed.
    Lemma term_orb_true_r [Σ] (b : Term Σ ty.bool) :
      term_binop bop.or b (term_val ty.bool true) ≡ term_val ty.bool true.
    Proof. intro ι; apply orb_true_r. Qed.
    Lemma term_negb_andb [Σ] (b1 b2 : Term Σ ty.bool) :
      term_not (term_binop bop.and b1 b2) ≡
      term_binop bop.or (term_not b1) (term_not b2).
    Proof. intro ι; apply negb_andb. Qed.
    Lemma term_negb_orb [Σ] (b1 b2 : Term Σ ty.bool) :
      term_not (term_binop bop.or b1 b2) ≡
      term_binop bop.and (term_not b1) (term_not b2).
    Proof. intro ι; apply negb_orb. Qed.
    Lemma term_negb_involutive [Σ] (t : Term Σ ty.bool) :
      term_not (term_not t) ≡ t.
    Proof. intro ι; apply negb_involutive. Qed.
    Lemma term_negb_val [Σ b] :
      term_not (Σ:=Σ) (term_val ty.bool b) ≡ term_val ty.bool (negb b).
    Proof. easy. Qed.
    Lemma term_negb_relop [σ] (op : RelOp σ) [Σ] (t1 t2 : Term Σ σ) :
      term_not (term_binop (bop.relop op) t1 t2) ≡ term_relop_neg op t1 t2.
    Proof. intro ι. symmetry. apply inst_term_relop_neg. Qed.

  End SemanticEquivalence.
  #[export] Hint Rewrite term_orb_false_l term_orb_false_r term_orb_true_l term_orb_true_r : katamaran.
  #[export] Hint Rewrite term_negb_andb term_negb_orb term_negb_relop : katamaran.
  #[export] Hint Rewrite term_negb_involutive term_negb_val : katamaran.
  #[export] Hint Extern 0 (term_binop ?op _ _ ≡ term_binop ?op _ _) =>
      simple apply (proper_term_binop op) : katamaran.

  Section InstProp.

    Class InstProp (T : LCtx -> Type) : Type :=
      instprop : forall {Σ}, T Σ -> Valuation Σ -> Prop.
    Class InstPropSubst (T : LCtx -> Type) `{InstProp T, Subst T} : Prop :=
      instprop_subst : forall {Σ Σ'} (ζ : Sub Σ Σ') (ι : Valuation Σ') (t : T Σ),
          instprop (subst t ζ) ι <-> instprop t (inst ζ ι).
    #[global] Arguments instprop {T _ Σ} !_ ι.
    #[global] Arguments InstPropSubst T {_ _}.

    #[export] Instance instprop_option `{InstProp A} : InstProp (Option A) :=
      fun Σ o =>
        match o with
        | Some C => fun ι => instprop C ι
        | None   => fun _ => False
        end.

    #[export] Instance instprop_pair `{InstProp A, InstProp B} : InstProp (Pair A B) :=
      fun Σ '(a,b) ι => instprop a ι /\ instprop b ι.

    #[export] Instance instpropsubst_pair `{InstPropSubst A, InstPropSubst B} : InstPropSubst (Pair A B).
    Proof. hnf. intros ? ? ζ ι [a b]. apply and_iff_morphism; apply instprop_subst. Qed.

    #[export] Instance instprop_ctx `{InstProp A} : InstProp (fun Σ => Ctx (A Σ)) :=
      fix instprop_ctx {Σ} (xs : Ctx (A Σ)) (ι : Valuation Σ) : Prop :=
        match xs with
        | ctx.nil       => True
        | ctx.snoc xs x => instprop_ctx xs ι /\ instprop x ι
        end.

    #[export] Instance instpropsubst_ctx `{InstPropSubst A} : InstPropSubst (fun Σ => Ctx (A Σ)).
    Proof. intros ? ? ζ ι x. now induction x; cbn; [|apply and_iff_morphism]. Qed.

    Lemma instprop_nil `{InstProp A} {Σ} (ι : Valuation Σ) :
      instprop (@ctx.nil (A Σ)) ι <-> True.
    Proof. reflexivity. Qed.

    Lemma instprop_snoc `{InstProp A} {Σ} (ι : Valuation Σ) (xs : Ctx (A Σ)) (x : A Σ) :
      instprop (xs ▻ x) ι <-> instprop xs ι /\ instprop x ι.
    Proof. reflexivity. Qed.

    Lemma instprop_cat `{InstProp A} {Σ} (x y : Ctx (A Σ)) (ι : Valuation Σ) :
      instprop (x ▻▻ y) ι <->
        instprop x ι /\ instprop y ι.
    Proof. induction y; cbn; rewrite ?IHy; intuition. Qed.

  End InstProp.

  Module Entailment.

    (* A preorder on path conditions. This encodes that either pc1 belongs to a
       longer symbolic execution path (or that it's the same path, but with
       potentially some constraints substituted away). *)
    Definition entails {A B} {IA : InstProp A} {IB : InstProp B}
      {Σ} (x : A Σ) (y : B Σ) : Prop :=
      forall (ι : Valuation Σ), instprop x ι -> instprop y ι.
    Definition bientails {A} {IA : InstProp A} {Σ} : relation (A Σ) :=
      fun x y => forall ι, instprop x ι <-> instprop y ι.

    Section WithA.
      Context `{IA : InstProp A} {Σ : LCtx}.
      Notation "(⊢)" := (@entails A A _ _ Σ).
      Notation "(⊣⊢)" := (@bientails A _ Σ).

      Definition entails_refl : Reflexive (⊢).
      Proof. now unfold Reflexive, entails. Qed.

      Definition entails_trans : Transitive (⊢).
      Proof. unfold Transitive, entails; eauto. Qed.

      #[export] Instance preorder_entails : PreOrder (⊢).
      Proof. split; auto using entails_refl, entails_trans. Qed.

      #[export] Instance equivalence_bientails : Equivalence (⊣⊢).
      Proof.
        unfold bientails. constructor; try easy.
        intros x y z xy yz ι. now transitivity (instprop y ι).
      Qed.

      #[export] Instance subrelation_bientails_entails :
        subrelation (⊣⊢) (⊢).
      Proof. intros x y xy ι. apply xy. Qed.

      #[export] Instance subrelation_bientails_flip_entails :
        subrelation (⊣⊢) (flip (⊢)).
      Proof. intros x y xy ι. apply xy. Qed.

      Definition Unsatisfiable (x : A Σ) : Prop :=
        forall ι : Valuation Σ, ~ instprop x ι.

      #[export] Instance proper_unsatisfiable_entails :
        Proper ((⊢) --> impl) Unsatisfiable.
      Proof. intros xs ys xys uxs ι H. apply (uxs ι), xys, H. Qed.

      #[export] Instance proper_unsatisfiable_bientails :
        Proper ((⊣⊢) ==> iff) Unsatisfiable.
      Proof.
        intros x y xy.
        split; apply proper_unsatisfiable_entails;
          intros ι; apply xy.
      Qed.

      Definition Valid (x : A Σ) : Prop :=
        forall ι : Valuation Σ, instprop x ι.

      #[export] Instance proper_valid_entails :
        Proper ((⊢) ==> impl) Valid.
      Proof. intros xs ys xys uxs ι. apply xys, (uxs ι). Qed.

      #[export] Instance proper_valid_bientails :
        Proper ((⊣⊢) ==> iff) Valid.
      Proof.
        intros x y xy.
        split; apply proper_valid_entails;
          intros ι; apply xy.
      Qed.

    End WithA.

    #[global] Instance: Params (@entails) 5 := {}.
    #[global] Instance: Params (@bientails) 3 := {}.
    #[global] Instance: Params (@Unsatisfiable) 3 := {}.
    #[global] Instance: Params (@Valid) 3 := {}.

    #[global] Typeclasses Opaque entails.
    #[global] Typeclasses Opaque bientails.

    Notation "(⊢)" := entails.
    Infix "⊢" := entails.
    Notation "(⊢@{ A } )" := (entails (A:=A) (B:=A)) (only parsing).

    Notation "(⊣⊢)" := bientails.
    Infix "⊣⊢" := bientails.
    Notation "(⊣⊢@{ A } )" := (bientails (A:=A)) (only parsing).

    Lemma entails_nil `{InstProp A, InstProp B} {Σ} {x : A Σ} : x ⊢ @ctx.nil (B Σ).
    Proof. constructor. Qed.

    Lemma entails_cons `{InstProp A, InstProp B} {Σ} (x : A Σ) (ys : Ctx (B Σ)) (y : B Σ) :
      (x ⊢ ys) /\ (x ⊢ y) <-> (x ⊢ ys ▻ y).
    Proof. unfold entails; cbn. intuition. Qed.

    Lemma proper_subst_entails `{InstPropSubst A, InstPropSubst B}
      {Σ1 Σ2} (ζ12 : Sub Σ1 Σ2) (x : A Σ1) (y : B Σ1) :
      (x ⊢ y) -> (subst x ζ12 ⊢ subst y ζ12).
    Proof. intros E ι. rewrite ?instprop_subst; eauto. Qed.

    #[export] Instance proper_snoc `{InstProp A} [Σ] :
      Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (@ctx.snoc (A Σ)).
    Proof. intros C1 C2 HC F1 F2 HF ι. now apply and_iff_morphism. Qed.

    #[local] Instance proper_snoc_entails `{InstProp A} [Σ] :
      Proper ((⊢) ==> (⊢) ==> (⊢)) (@ctx.snoc (A Σ)).
    Proof.
      intros C1 C2 HC F1 F2 HF ι; cbn.
      apply and_impl_morphism; red; [apply HC|apply HF].
    Qed.

    #[local] Instance proper_some `{InstProp A} [Σ] :
      Proper ((⊣⊢) ==> (⊣⊢)) (@Some (A Σ)).
    Proof. intros xs ys Hxys. apply Hxys. Qed.

    Lemma snoc_cancel `{InstProp A} [Σ] (xs : Ctx (A Σ)) (x : A Σ) :
      Valid x -> xs ⊣⊢ xs ▻ x.
    Proof. intros vx ι; specialize (vx ι). cbn in *. intuition. Qed.

    Lemma unsatisfiable_snoc_l `{InstProp A} [Σ] (xs : Ctx (A Σ)) (x : A Σ) :
      Unsatisfiable xs -> Unsatisfiable (xs ▻ x).
    Proof. unfold Unsatisfiable; intuition. Qed.

    Lemma unsatisfiable_snoc_r `{InstProp A} [Σ] (xs : Ctx (A Σ)) (x : A Σ) :
      Unsatisfiable x -> Unsatisfiable (xs ▻ x).
    Proof. unfold Unsatisfiable; intuition. Qed.

    Lemma unsatisfiable_none_some `{InstProp A} [Σ] (x : A Σ) :
      Unsatisfiable x -> None ⊣⊢ Some x.
    Proof. unfold Unsatisfiable; intros ? ι; cbn; intuition. Qed.

    Lemma unsatisfiable_some_none `{InstProp A} [Σ] (x : A Σ) :
      Unsatisfiable x -> Some x ⊣⊢ None.
    Proof. unfold Unsatisfiable; intros ? ι; cbn; intuition. Qed.

    Lemma nil_l_valid `{InstProp A} [Σ] (xs : Ctx (A Σ)) :
      Valid xs -> [ctx] ⊣⊢ xs.
    Proof. unfold Valid; intros ? ι; cbn; intuition. Qed.

    Lemma nil_r_valid `{InstProp A} [Σ] (xs : Ctx (A Σ)) :
      Valid xs -> xs ⊣⊢ [ctx].
    Proof. unfold Valid; intros ? ι; cbn; intuition. Qed.

  End Entailment.

  Section Utils.

    Definition term_get_val {Σ σ} (t : Term Σ σ) : option (Val σ) :=
      match t with
      | term_val _ v => Some v
      | _            => None
      end.

    Lemma term_get_val_spec {Σ σ} (s : Term Σ σ) :
      option.wlp
        (fun v => s = term_val _ v)
        (term_get_val s).
    Proof. destruct s; constructor; auto. Qed.

    Equations(noeqns) term_get_pair {Σ σ1 σ2} (t : Term Σ (ty.prod σ1 σ2)) :
      option (Term Σ σ1 * Term Σ σ2) :=
      term_get_pair (term_val _ (v1,v2))        := Some (term_val _ v1, term_val _ v2);
      term_get_pair (term_binop bop.pair t1 t2) := Some (t1, t2);
      term_get_pair _ := None.

    Lemma term_get_pair_spec {Σ σ1 σ2} (s : Term Σ (ty.prod σ1 σ2)) :
      option.wlp
        (fun '(t1,t2) =>
           forall ι : Valuation Σ,
             inst (T := fun Σ => Term Σ (ty.prod σ1 σ2)) (A := Val σ1 * Val σ2) s ι =
             (inst (A := Val σ1) t1 ι, inst (A := Val σ2) t2 ι))
        (term_get_pair s).
    Proof.
      dependent elimination s; cbn; try constructor; auto.
      - destruct v; constructor; auto.
      - dependent elimination op. constructor. reflexivity.
    Qed.

    Equations(noeqns) term_get_sum {Σ σ1 σ2} (t : Term Σ (ty.sum σ1 σ2)) :
      option (Term Σ σ1 + Term Σ σ2) :=
      term_get_sum (term_val _ (inl v)) := Some (inl (term_val _ v));
      term_get_sum (term_val _ (inr v)) := Some (inr (term_val _ v));
      term_get_sum (term_inl t)         := Some (inl t);
      term_get_sum (term_inr t)         := Some (inr t);
      term_get_sum _ := None.

    Lemma term_get_sum_spec {Σ σ1 σ2} (s : Term Σ (ty.sum σ1 σ2)) :
      option.wlp
        (fun s' => match s' with
                   | inl t => forall ι : Valuation Σ,
                       inst (T := fun Σ => Term Σ (ty.sum σ1 σ2)) (A := Val σ1 + Val σ2) s ι =
                       @inl (Val σ1) (Val σ2) (inst t ι)
                   | inr t => forall ι : Valuation Σ,
                       inst (T := fun Σ => Term Σ (ty.sum σ1 σ2)) (A := Val σ1 + Val σ2) s ι =
                       @inr (Val σ1) (Val σ2) (inst t ι)
                   end)
        (term_get_sum s).
    Proof.
      dependent elimination s; cbn; try constructor; auto.
      destruct v; constructor; auto.
    Qed.

    Equations(noeqns) term_get_list {Σ σ} (t : Term Σ (ty.list σ)) :
      option ((Term Σ σ * Term Σ (ty.list σ)) + unit) :=
      term_get_list (term_val _ []%list)       := Some (inr tt);
      term_get_list (term_val _ (cons x xs))   := Some (inl (term_val _ x , term_val (ty.list σ) xs));
      term_get_list (term_binop bop.cons x xs) := Some (inl (x , xs));
      term_get_list _                          := None.

    Lemma term_get_list_spec {Σ σ} (s : Term Σ (ty.list σ)) :
      option.wlp
        (fun s' => match s' with
                   | inl (x , xs) => forall ι : Valuation Σ,
                       inst (T := fun Σ => Term Σ (ty.list σ)) (A := list (Val σ)) s ι =
                         @cons (Val σ) (inst x ι) (inst (T := fun Σ => Term Σ (ty.list σ)) xs ι)
                   | inr _ => forall ι : Valuation Σ,
                       inst (T := fun Σ => Term Σ (ty.list σ)) (A := list (Val σ)) s ι = nil
                   end)
        (term_get_list s).
    Proof.
      dependent elimination s; cbn; try constructor; auto.
      - destruct v; constructor; auto.
      - dependent elimination op; cbn; try constructor; auto.
    Qed.

    Equations(noeqns) term_get_union {Σ U} (t : Term Σ (ty.union U)) :
      option { K : unionk U & Term Σ (unionk_ty U K) } :=
      term_get_union (term_val _ v)   :=
        Some (let (K, p) := unionv_unfold U v in existT K (term_val _ p));
      term_get_union (term_union K t) := Some (existT K t);
      term_get_union _ := None.

    Lemma term_get_union_spec {Σ U} (s : Term Σ (ty.union U)) :
      option.wlp
        (fun x : {K : unionk U & Term Σ (unionk_ty U K)} =>
           match x with
           | existT K t =>
             forall ι : Valuation Σ,
               inst (T := fun Σ => Term Σ (ty.union U)) (A := uniont U) s ι =
               unionv_fold U (@existT (unionk U) (fun K => Val (unionk_ty U K)) K (inst t ι)) :> Val (ty.union U)
           end)
        (term_get_union s).
    Proof.
      dependent elimination s; cbn; try constructor; auto.
      destruct (unionv_unfold U v) eqn:?. intros. cbn.
      now rewrite <- Heqs, unionv_fold_unfold.
    Qed.

    Equations(noeqns) term_get_record {R Σ} (t : Term Σ (ty.record R)) :
      option (NamedEnv (Term Σ) (recordf_ty R)) :=
    | term_val _ v     => (* We inlined lift here, so that user solvers that use
                             this operation are spared with a inst_lift rewrite
                             when pattern matching on symbolic records. *)
                          Some (env.map (fun _ v => term_val _ v) (recordv_unfold R v))
    | term_record R ts => Some ts
    | _                => None.

    Lemma term_get_record_spec {Σ R} (s : Term Σ (ty.record R)) :
      option.wlp
        (fun ts =>
           forall ι : Valuation Σ,
             inst (T := fun Σ => Term Σ (ty.record R)) (A := recordt R) s ι =
             recordv_fold R (inst (T := fun Σ => NamedEnv (fun τ => Term Σ τ) (recordf_ty R)) (A := NamedEnv Val (recordf_ty R)) ts ι))
        (term_get_record s).
    Proof.
      dependent elimination s; try constructor; auto. intros ι. cbn.
      change (v = recordv_fold R (inst (lift (recordv_unfold R v)) ι)).
      now rewrite inst_lift, recordv_fold_unfold.
    Qed.

    Equations(noeqns) term_get_tuple {σs Σ} (t : Term Σ (ty.tuple σs)) :
      option (Env (Term Σ) σs) :=
      (* term_get_tuple (term_val _ v)       := Some _; *)
      (* term_get_tuple (@term_tuple _ _ ts) := Some ts; *)
      term_get_tuple _ := None.

    Lemma term_get_tuple_spec {Σ σs} (s : Term Σ (ty.tuple σs)) :
      option.wlp
        (fun ts =>
           forall ι : Valuation Σ,
             inst (T := fun Σ => Term Σ (ty.tuple σs)) (A := Val (ty.tuple σs)) s ι =
             inst (term_tuple ts) ι)
        (term_get_tuple s).
    Proof.
      now constructor.
    Qed.

  End Utils.

End InstantiationOn.
