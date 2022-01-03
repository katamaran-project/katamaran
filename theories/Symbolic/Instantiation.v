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
     Bool.Bool
     Strings.String
     ZArith.BinInt.

From Equations Require Import
     Equations.
From Katamaran Require Import
     Environment
     Notation
     Prelude
     Syntax.BinOps
     Syntax.Terms
     Syntax.TypeDecl
     Syntax.TypeDef
     Syntax.Variables
     Tactics.

Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.

Module Type InstantiationOn
  (Import TY : Types)
  (Import BO : BinOpsOn TY)
  (Import TM : TermsOn TY BO).

  Local Notation LCtx := (NCtx 𝑺 Ty).
  Local Notation Valuation Σ := (@Env (Binding 𝑺 Ty) (fun xt : Binding 𝑺 Ty => Val (@type 𝑺 Ty xt)) Σ).
  Local Notation CStore := (@NamedEnv 𝑿 Ty Val).

  (* This type class connects a symbolic representation of a type with its
     concrete / semi-concrete counterpart. The method 'inst' will instantiate
     all logic variables in a symbolic value to obtain the concrete value and
     'lift' injects the concrete type into the symbolic one. *)
  Class Inst (T : LCtx -> Type) (A : Type) : Type :=
    { inst {Σ} (t : T Σ) (ι : Valuation Σ) : A;
      lift {Σ} (a : A) : T Σ;
    }.

  Global Instance instantiate_list {T : LCtx -> Type} {A : Type} `{Inst T A} :
    Inst (List T) (list A) :=
    {| inst Σ xs ι := List.map (fun x => inst x ι) xs;
       lift Σ      := List.map lift;
    |}.

  Global Instance instantiate_const {A} `{finite.Finite A} :
    Inst (Const A) A :=
    {| inst Σ x ι := x;
       lift Σ x   := x;
    |}.

  Global Instance instantiate_env {T : Set} {S : LCtx -> T -> Set}
         {A : T -> Set} {InstSA : forall τ : T, Inst (fun Σ => S Σ τ) (A τ)}
         {Γ : Ctx T} :
    Inst (fun Σ => Env (S Σ) Γ) (Env A Γ) :=
    {| inst Σ xs ι := env.map (fun (b : T) (s : S Σ b) => inst s ι) xs;
       lift Σ      := env.map (fun (b : T) (a : A b) => lift a)
    |}.

  Fixpoint inst_term {σ : Ty} {Σ : LCtx} (t : Term Σ σ) (ι : Valuation Σ) {struct t} : Val σ :=
    match t in Term _ σ return Val σ with
    | @term_var _ _ _ bIn  => env.lookup ι bIn
    | term_val _ v         => v
    | term_binop op e1 e2  => eval_binop op (inst_term e1 ι) (inst_term e2 ι)
    | term_neg e           => Z.opp (inst_term e ι)
    | term_not e           => negb (inst_term e ι)
    | term_inl e           => @inl (Val _) (Val _) (inst_term e ι)
    | term_inr e           => @inr (Val _) (Val _) (inst_term e ι)
    | @term_projtup _ σs e n σ p => tuple_proj σs n σ (inst_term e ι) p
    | @term_union _ U K e     => 𝑼_fold (existT K (inst_term e ι))
    | @term_record _ R ts     =>
        let InstTerm :=
          fun xt : Binding 𝑹𝑭 Ty => {| inst := @inst_term (@type 𝑹𝑭 Ty xt);
                                 lift Σ := @term_val Σ (@type 𝑹𝑭 Ty xt) |} in
        𝑹_fold (inst (Inst := instantiate_env (InstSA := InstTerm)) ts ι)
    end.

  Global Instance instantiate_term {σ} : Inst (fun Σ => Term Σ σ) (Val σ) :=
    {| inst Σ t ι := inst_term t ι;
       lift Σ v   := term_val σ v;
    |}.

  Global Instance instantiate_sub {Σ} : Inst (Sub Σ) (Valuation Σ) :=
    instantiate_env.

  Class InstLaws (T : LCtx -> Type) (A : Type) `{SubstLaws T, Inst T A} : Prop :=
    { inst_lift {Σ} (ι : Valuation Σ) (a : A) :
        inst (lift a) ι = a;
      inst_subst {Σ Σ'} (ζ : Sub Σ Σ') (ι : Valuation Σ') (t : T Σ) :
        inst (subst t ζ) ι = inst t (inst ζ ι)
    }.

  Global Arguments InstLaws T A {_ _ _}.

  Global Instance instantiatelaws_term {σ} : InstLaws (fun Σ => Term Σ σ) (Val σ).
  Proof.
    constructor.
    { reflexivity. }
    { induction t; cbn; try (f_equal; auto; fail).
      - now rewrite env.lookup_map.
      - f_equal.
        f_equal.
        apply IHt.
      - f_equal.
        induction es; cbn in *.
        + reflexivity.
        + f_equal.
          * apply IHes, X.
          * apply X.
      (* - f_equal. *)
      (*   f_equal. *)
      (*   apply IHt. *)
    }
  Qed.

  Global Instance instantiatelaws_list {T : LCtx -> Set} {A : Set} `{InstLaws T A} :
    InstLaws (List T) (list A).
  Proof.
    constructor.
    { intros; cbn.
      rewrite List.map_map, <- List.map_id.
      apply List.map_ext, inst_lift.
    }
    { intros ? ? ζ ι xs; cbn.
      rewrite substlist_is_map_subst.
      rewrite List.map_map.
      apply List.map_ext, inst_subst.
    }
  Qed.

  Global Instance instantiatelaws_const {A} `{finite.Finite A} :
    InstLaws (Const A) A.
  Proof. constructor; reflexivity. Qed.

  Global Instance instantiatelaws_env {T : Set} {S : LCtx -> T -> Set} {A : T -> Set}
         {_ : forall τ : T, Subst (fun Σ => S Σ τ)}
         {_ : forall τ : T, SubstLaws (fun Σ => S Σ τ)}
         {_ : forall τ : T, Inst (fun Σ => S Σ τ) (A τ)}
         {_ : forall τ : T, InstLaws (fun Σ => S Σ τ) (A τ)}
         {Γ : Ctx T} :
    InstLaws (fun Σ => Env (S Σ) Γ) (Env A Γ).
  Proof.
    constructor.
    { intros; cbn.
      rewrite env.map_map.
      apply env.map_id_eq.
      intros; apply inst_lift.
    }
    { intros ? ? ζ ι E; cbn.
      unfold subst, SubstEnv.
      rewrite env.map_map.
      apply env.map_ext.
      intros b s.
      now rewrite inst_subst.
    }
  Qed.

  Global Instance instantiatelaws_sub {Σ} : InstLaws (Sub Σ) (Valuation Σ).
  Proof. apply instantiatelaws_env. Qed.

  Lemma inst_env_snoc {B : Set} {AT : LCtx -> B -> Set}
         {A : B -> Set} {_ : forall b : B, Inst (fun Σ => AT Σ b) (A b)}
         {Γ : Ctx B} {Σ} (ι : Valuation Σ) (E : Env (AT Σ) Γ) (b : B) (a : AT Σ b) :
    inst (env.snoc E b a) ι = env.snoc (inst E ι) b (inst a ι).
  Proof. reflexivity. Qed.

  Lemma inst_sub_wk1 {Σ b v} (ι : Valuation Σ) :
    inst sub_wk1 (ι ► (b ↦ v)) = ι.
  Proof.
    apply env.lookup_extensional.
    intros [x σ] ?; unfold sub_wk1; cbn.
    now rewrite env.map_tabulate, env.lookup_tabulate.
  Qed.

  Lemma inst_sub_id {Σ} (ι : Valuation Σ) :
    inst (sub_id Σ) ι = ι.
  Proof.
    apply env.lookup_extensional.
    intros [x τ] ?; unfold sub_id; cbn.
    now rewrite env.map_tabulate, env.lookup_tabulate.
  Qed.

  Lemma inst_sub_snoc {Σ0 Σ1} (ι : Valuation Σ1) (ζ : Sub Σ0 Σ1) b (t : Term Σ1 (type b)) :
    inst (sub_snoc ζ b t) ι = env.snoc (inst ζ ι) b (inst t ι).
  Proof. reflexivity. Qed.

  Lemma inst_sub_up1 {Σ1 Σ2 b} (ζ12 : Sub Σ1 Σ2) (ι2 : Valuation Σ2) (v : Val (type b)) :
    inst (sub_up1 ζ12) (ι2 ► (b ↦ v)) = inst ζ12 ι2 ► (b ↦ v).
  Proof.
    destruct b; unfold sub_up1.
    now rewrite inst_sub_snoc, inst_subst, inst_sub_wk1.
  Qed.

  Lemma inst_sub_shift {Σ} (ι : Valuation Σ) {b} (bIn : b ∈ Σ) :
    inst (sub_shift bIn) ι = env.remove b ι bIn.
  Proof.
    rewrite env.remove_remove'.
    unfold env.remove', sub_shift, inst; cbn.
    apply env.lookup_extensional. intros [y τ] yIn.
    now rewrite env.lookup_map, ?env.lookup_tabulate.
  Qed.

  Lemma inst_sub_single_shift {Σ} (ι : Valuation Σ) {x σ} (xIn : x∷σ ∈ Σ) (t : Term (Σ - x∷σ) σ) :
    inst t (inst (sub_shift xIn) ι) = env.lookup ι xIn ->
    inst (sub_single xIn t) (inst (sub_shift xIn) ι) = ι.
  Proof.
    rewrite inst_sub_shift.
    rewrite env.remove_remove'.
    intros HYP. apply env.lookup_extensional. intros [y τ] yIn.
    unfold inst, sub_single; cbn.
    rewrite env.lookup_map, env.lookup_tabulate.
    pose proof (ctx.occurs_check_var_spec xIn yIn).
    destruct (ctx.occurs_check_var xIn yIn).
    * dependent elimination e. subst yIn. exact HYP.
    * destruct H; subst yIn. cbn. unfold env.remove'.
      now rewrite env.lookup_tabulate.
  Qed.

  Lemma sub_single_zero {Σ : LCtx} {x : 𝑺} {σ : Ty} (t : Term Σ σ) :
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
    unfold env.insert', sub_single, inst; cbn.
    apply env.lookup_extensional.
    intros [y τ] yIn.
    rewrite env.lookup_map, ?env.lookup_tabulate.
    assert (ovs := ctx.occurs_check_var_spec xIn yIn).
    destruct (ctx.occurs_check_var xIn yIn).
    - now dependent elimination e.
    - now reflexivity.
  Qed.

  Lemma inst_lookup {Σ0 Σ1} (ι : Valuation Σ1) (ζ : Sub Σ0 Σ1) x τ (xIn : x∷τ ∈ Σ0) :
    inst (env.lookup ζ xIn) ι = env.lookup (inst (A := Valuation Σ0) ζ ι) xIn.
  Proof. cbn. now rewrite env.lookup_map. Qed.

  Lemma inst_term_tuple {Σ σs} {ι : Valuation Σ} (es : Env (Term Σ) σs) :
    @eq (EnvRec Val σs) (inst (Inst := instantiate_term)(term_tuple es) ι)
        (envrec.of_env (inst es ι)).
  Proof.
    induction σs; cbn.
    - destruct (env.nilView es); now cbn.
    - destruct (env.snocView es); cbn.
      f_equal. now eapply IHσs.
  Qed.

  Global Arguments inst {T A _ Σ} !_ ι.
  Global Arguments lift {T A _ Σ} !_.

  Global Instance InstUnit : Inst Unit unit :=
    @Build_Inst Unit unit (fun _ x ι => x) (fun _ x => x).
  Global Instance InstLawsUnit : InstLaws Unit unit.
  Proof. constructor; reflexivity. Qed.

  Global Instance InstPair {AT BT A B} `{Inst AT A, Inst BT B} :
    Inst (Pair AT BT) (A * B) :=
    {| inst Σ '(a , b) ι := (inst a ι, inst b ι);
       lift Σ '(a, b)    := (lift a , lift b);
    |}.

  Global Instance InstLawsPair {AT BT A B} `{InstLaws AT A, InstLaws BT B} :
    InstLaws (Pair AT BT) (A * B).
  Proof.
    constructor.
    { intros ? ? []; cbn; f_equal; apply inst_lift. }
    { intros ? ? ? ? []; cbn; f_equal; apply inst_subst. }
  Qed.

  Global Instance InstOption {AT A} `{Inst AT A} :
    Inst (Option AT) (option A) :=
    {| inst Σ ma ι := option_map (fun a => inst a ι) ma;
       lift Σ ma   := option_map lift ma;
    |}.

  Global Instance InstLawsOption {AT A} `{InstLaws AT A} :
    InstLaws (Option AT) (option A).
  Proof.
    constructor.
    { intros ? ? []; cbn; f_equal; apply inst_lift. }
    { intros ? ? ? ? []; cbn; f_equal; apply inst_subst. }
  Qed.

  Global Program Instance inst_localstore {Γ} : Inst (SStore Γ) (CStore Γ) :=
    instantiate_env.

  Global Instance instlaws_localstore {Γ} : InstLaws (SStore Γ) (CStore Γ).
  Proof. apply instantiatelaws_env. Qed.

  Section Utils.

    Definition term_get_val {Σ σ} (t : Term Σ σ) : option (Val σ) :=
      match t with
      | term_val _ v => Some v
      | _            => None
      end.

    Lemma term_get_val_spec {Σ σ} (s : Term Σ σ) :
      OptionSpec
        (fun v => forall ι : Valuation Σ, inst s ι = v)
        True
        (term_get_val s).
    Proof.
      dependent elimination s; cbn; try constructor; auto.
    Qed.

    Equations(noeqns) term_get_pair {Σ σ1 σ2} (t : Term Σ (ty_prod σ1 σ2)) :
      option (Term Σ σ1 * Term Σ σ2) :=
      term_get_pair (term_val _ (v1,v2))          := Some (term_val _ v1, term_val _ v2);
      term_get_pair (term_binop binop_pair t1 t2) := Some (t1, t2);
      term_get_pair _ := None.

    Lemma term_get_pair_spec {Σ σ1 σ2} (s : Term Σ (ty_prod σ1 σ2)) :
      OptionSpec
        (fun '(t1,t2) =>
           forall ι : Valuation Σ,
             inst (T := fun Σ => Term Σ (ty_prod σ1 σ2)) (A := Val σ1 * Val σ2) s ι =
             (inst (A := Val σ1) t1 ι, inst (A := Val σ2) t2 ι))
        True
        (term_get_pair s).
    Proof.
      dependent elimination s; cbn; try constructor; auto.
      - destruct v; constructor; auto.
      - dependent elimination op. constructor. reflexivity.
    Qed.

    Equations(noeqns) term_get_sum {Σ σ1 σ2} (t : Term Σ (ty_sum σ1 σ2)) :
      option (Term Σ σ1 + Term Σ σ2) :=
      term_get_sum (term_val _ (inl v)) := Some (inl (term_val _ v));
      term_get_sum (term_val _ (inr v)) := Some (inr (term_val _ v));
      term_get_sum (term_inl t)         := Some (inl t);
      term_get_sum (term_inr t)         := Some (inr t);
      term_get_sum _ := None.

    Lemma term_get_sum_spec {Σ σ1 σ2} (s : Term Σ (ty_sum σ1 σ2)) :
      OptionSpec
        (fun s' => match s' with
                   | inl t => forall ι : Valuation Σ,
                       inst (T := fun Σ => Term Σ (ty_sum σ1 σ2)) (A := Val σ1 + Val σ2) s ι =
                       @inl (Val σ1) (Val σ2) (inst t ι)
                   | inr t => forall ι : Valuation Σ,
                       inst (T := fun Σ => Term Σ (ty_sum σ1 σ2)) (A := Val σ1 + Val σ2) s ι =
                       @inr (Val σ1) (Val σ2) (inst t ι)
                   end)
        True
        (term_get_sum s).
    Proof.
      dependent elimination s; cbn; try constructor; auto.
      destruct v; constructor; auto.
    Qed.

    Equations(noeqns) term_get_union {Σ U} (t : Term Σ (ty_union U)) :
      option { K : 𝑼𝑲 U & Term Σ (𝑼𝑲_Ty K) } :=
      term_get_union (term_val _ v)   :=
        Some (let (K, p) := 𝑼_unfold v in existT K (term_val _ p));
      term_get_union (term_union K t) := Some (existT K t);
      term_get_union _ := None.

    Lemma term_get_union_spec {Σ U} (s : Term Σ (ty_union U)) :
      OptionSpec
        (fun x : {K : 𝑼𝑲 U & Term Σ (𝑼𝑲_Ty K)} =>
           match x with
           | existT K t =>
             forall ι : Valuation Σ,
               inst (T := fun Σ => Term Σ (ty_union U)) (A := 𝑼𝑻 U) s ι =
               𝑼_fold (@existT (𝑼𝑲 U) (fun K => Val (𝑼𝑲_Ty K)) K (inst t ι)) :> Val (ty_union U)
           end)
        True
        (term_get_union s).
    Proof.
      dependent elimination s; cbn; try constructor; auto.
      destruct (𝑼_unfold v) eqn:?. intros. cbn.
      now rewrite <- Heqs, 𝑼_fold_unfold.
    Qed.

    Equations(noeqns) term_get_record {R Σ} (t : Term Σ (ty_record R)) :
      option (NamedEnv (Term Σ) (𝑹𝑭_Ty R)) :=
      term_get_record (term_val _ v)        := Some (lift (𝑹_unfold v));
      term_get_record (@term_record _ R ts) := Some ts;
      term_get_record _ := None.

    Lemma term_get_record_spec {Σ R} (s : Term Σ (ty_record R)) :
      OptionSpec
        (fun ts =>
           forall ι : Valuation Σ,
             inst (T := fun Σ => Term Σ (ty_record R)) (A := 𝑹𝑻 R) s ι =
             𝑹_fold (inst (T := fun Σ => NamedEnv (fun τ => Term Σ τ) (𝑹𝑭_Ty R)) (A := NamedEnv Val (𝑹𝑭_Ty R)) ts ι))
        True
        (term_get_record s).
    Proof.
      dependent elimination s; try constructor; auto.
      intros ι. now rewrite inst_lift, 𝑹_fold_unfold.
    Qed.

    Equations(noeqns) term_get_tuple {σs Σ} (t : Term Σ (ty_tuple σs)) :
      option (Env (Term Σ) σs) :=
      (* term_get_tuple (term_val _ v)       := Some _; *)
      (* term_get_tuple (@term_tuple _ _ ts) := Some ts; *)
      term_get_tuple _ := None.

    Lemma term_get_tuple_spec {Σ σs} (s : Term Σ (ty_tuple σs)) :
      OptionSpec
        (fun ts =>
           forall ι : Valuation Σ,
             inst (T := fun Σ => Term Σ (ty_tuple σs)) (A := Val (ty_tuple σs)) s ι =
             inst (term_tuple ts) ι)
        True
        (term_get_tuple s).
    Proof.
      now constructor.
    Qed.

  End Utils.

End InstantiationOn.
