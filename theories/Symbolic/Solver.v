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
     Bool.Bool
     Classes.Morphisms
     Classes.Morphisms_Prop
     Classes.RelationClasses
     NArith.BinNat
     Relations.Relation_Definitions
     ZArith.BinInt.

From Katamaran Require Import
     Base
     Prelude
     Syntax.Predicates
     Symbolic.Propositions
     Symbolic.Worlds.

From Equations Require Import
     Equations.

Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.
Local Set Equations Transparent.

Module Type GenericSolverOn
  (Import B : Base)
  (Import P : PredicateKit B)
  (Import W : WorldsMixin B P)
  (Import S : SolverKit B P W).

  Module Import GenericSolver.

    Import option.notations.
    Import Entailment.
    Import DList.

    #[local] Hint Rewrite @instprop_formula_relop_neg : katamaran.
    #[local] Hint Rewrite @instprop_nil @instprop_snoc @instprop_cat : katamaran.
    #[local] Hint Rewrite @recordv_fold_inj @unionv_fold_inj : katamaran.
    #[local] Hint Rewrite @bop.eval_relop_equiv : katamaran.
    #[local] Hint Rewrite formula_bool_and formula_bool_relop formula_bool_relop_neg : katamaran.

    Lemma valid_formula_bool [Σ] (t : Term Σ ty.bool) :
      base.equiv t (term_val ty.bool true) -> Valid (formula_bool t).
    Proof. easy. Qed.

    #[local] Hint Rewrite instprop_dlist_cat instprop_dlist_singleton : katamaran.
    #[local] Hint Rewrite singleton_formula_and : katamaran.

    Local Ltac arw :=
      repeat
        (try progress cbn - [cat] in *;
         repeat
           match goal with
           | |- base.equiv ?x ?x => reflexivity
           | |- ?x ⊣⊢ ?x => reflexivity
           | |- singleton _ ⊣⊢ singleton _ => apply proper_singleton
           | |- formula_bool _ ⊣⊢ formula_bool _ => apply proper_formula_bool
           | |- formula_user ?p _ ⊣⊢ formula_user ?p _ => apply proper_formula_user
           | |- empty ⊣⊢ _ => apply empty_l_valid
           | |- Valid (singleton _) => apply valid_singleton
           | |- Valid (formula_bool _) => apply valid_formula_bool
           | |- error ⊣⊢ _ => apply error_l_unsatisfiable
           | |- Unsatisfiable (singleton _) => apply unsatisfiable_singleton
           | |- Unsatisfiable (formula_bool _) => apply unsatisfiable_formula_bool
           | |- context[env.snoc _ _ _ = env.snoc _ _ _] =>
               unfold NamedEnv; rewrite env.inversion_eq_snoc
           end; try easy;
         autorewrite with katamaran in *).

    Fixpoint simplify_bool [Σ] (t : Term Σ ty.bool) : DList Σ :=
      Term_bool_case
        (fun (*var*) ς _        => singleton (formula_bool (term_var ς)))
        (fun (*val*) b          => if b then empty else error)
        (fun (*and*) t1 t2      => cat (simplify_bool t1) (simplify_bool t2))
        (fun (*or*)  t1 t2      => singleton (formula_bool (term_binop bop.or t1 t2)))
        (fun (*rel*) σ op t1 t2 => singleton (formula_relop op t1 t2))
        (fun (*not*) t1         => simplify_bool_neg t1)
        t
    with
    simplify_bool_neg [Σ] (t : Term Σ ty.bool) : DList Σ :=
      Term_bool_case
        (fun (*var*) ς _        => singleton (formula_bool (term_unop uop.not (term_var ς))))
        (fun (*val*) b          => if b then error else empty)
        (fun (*and*) t1 t2      => singleton (formula_bool (term_binop bop.or (term_unop uop.not t1) (term_unop uop.not t2))))
        (fun (*or*)  t1 t2      => cat (simplify_bool_neg t1) (simplify_bool_neg t2))
        (fun (*rel*) σ op t1 t2 => singleton (formula_relop_neg op t1 t2))
        (fun (*not*) t1         => simplify_bool t1)
        t.

    Lemma simplify_bool_spec_combined {Σ} (t : Term Σ ty.bool) :
      (simplify_bool t ⊣⊢ singleton (formula_bool t)) /\
      (simplify_bool_neg t ⊣⊢ singleton (formula_bool (term_unop uop.not t))).
    Proof.
      induction t using Term_bool_ind; cbn; arw.
      - destruct v; split; arw.
      - destruct IHt1 as [IHt11 IHt12], IHt2 as [IHt21 IHt22]; split; arw.
        now apply proper_cat.
      - destruct IHt1 as [IHt11 IHt12], IHt2 as [IHt21 IHt22]; split; arw.
        now apply proper_cat.
    Qed.

    Lemma simplify_bool_spec [Σ] (t : Term Σ ty.bool) :
      simplify_bool t ⊣⊢ singleton (formula_bool t).
    Proof. apply simplify_bool_spec_combined. Qed.

    Lemma simplify_bool_neg_spec [Σ] (t : Term Σ ty.bool) :
      simplify_bool_neg t ⊣⊢ singleton (formula_bool (term_unop uop.not t)).
    Proof. apply simplify_bool_spec_combined. Qed.
    #[local] Opaque simplify_bool simplify_bool_neg.
    #[local] Hint Rewrite simplify_bool_spec simplify_bool_neg_spec : katamaran.

    (* Simplifies equations of the form (term_binop op t1 t2 = v). *)
    Equations(noeqns) simplify_eq_binop_val [Σ σ σ1 σ2]
      (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) (v : Val σ) : DList Σ :=
    | bop.pair       | t1 | t2 | (v1 , v2)  => cat
                                                (singleton (formula_relop bop.eq t1 (term_val _ v1)))
                                                (singleton (formula_relop bop.eq t2 (term_val _ v2)))
    | bop.cons       | t1 | t2 | nil        => error
    | bop.cons       | t1 | t2 | cons v1 v2 => cat
                                                 (singleton (formula_relop bop.eq t1 (term_val _ v1)))
                                                 (singleton (formula_relop bop.eq t2 (term_val (ty.list _) v2)))
    | bop.and        | t1 | t2 | v          => if v
                                               then simplify_bool (term_binop bop.and t1 t2)
                                               else simplify_bool_neg (term_binop bop.and t1 t2)
    | bop.or         | t1 | t2 | v          => if v
                                               then simplify_bool (term_binop bop.or t1 t2)
                                               else simplify_bool_neg (term_binop bop.or t1 t2)
    | bop.relop op   | t1 | t2 | v          => if v
                                               then singleton (formula_relop op t1 t2)
                                               else singleton (formula_relop_neg op t1 t2)
    | op             | t1 | t2 | v          => singleton (formula_relop bop.eq (term_binop op t1 t2) (term_val _ v)).

    Lemma simplify_eq_binop_val_spec [Σ σ σ1 σ2]
      (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) (v : Val σ) :
      simplify_eq_binop_val op t1 t2 v ⊣⊢
      singleton (formula_relop bop.eq (term_binop op t1 t2) (term_val σ v)).
    Proof. destruct op; arw; destruct v; arw; intro ι; arw. Qed.
    #[local] Opaque simplify_eq_binop_val.
    #[local] Hint Rewrite simplify_eq_binop_val_spec : katamaran.

    Equations(noeqns) simplify_eq_unop_val [Σ σ1 σ2]
      (op : UnOp σ1 σ2) (t : Term Σ σ1) (v : Val σ2) : DList Σ :=
    | uop.neg        | t | v      => singleton (formula_relop bop.eq t (term_val ty.int (Z.opp v)))
    | uop.not        | t | v     => if v then simplify_bool_neg t else simplify_bool t
    | uop.inl        | t | inl v => singleton (formula_relop bop.eq t (term_val _ v))
    | uop.inl        | t | inr _ => error
    | uop.inr        | t | inl _ => error
    | uop.inr        | t | inr v => singleton (formula_relop bop.eq t (term_val _ v))
    | op             | t | v     => singleton (formula_relop bop.eq (term_unop op t) (term_val _ v)).

    Lemma simplify_eq_unop_val_spec [Σ σ1 σ2]
      (op : UnOp σ1 σ2) (t : Term Σ σ1) (v : Val σ2) :
      simplify_eq_unop_val op t v ⊣⊢
      singleton (formula_relop bop.eq (term_unop op t) (term_val σ2 v)).
    Proof. destruct op; arw; destruct v; arw; intro ι; arw; Lia.lia. Qed.
    #[local] Opaque simplify_eq_unop_val.
    #[local] Hint Rewrite simplify_eq_unop_val_spec : katamaran.

    Definition simplify_eqb {Σ σ} (t1 t2 : Term Σ σ) : DList Σ :=
      if Term_eqb t1 t2 then empty else singleton (formula_relop bop.eq t1 t2).

    Lemma simplify_eqb_spec [Σ σ] (t1 t2 : Term Σ σ) :
      simplify_eqb t1 t2 ⊣⊢ singleton (formula_relop bop.eq t1 t2).
    Proof. unfold simplify_eqb. destruct (Term_eqb_spec t1 t2); now subst. Qed.
    #[local] Hint Rewrite simplify_eqb_spec : katamaran.
    #[local] Opaque simplify_eqb.

    Equations(noeqns) simplify_eq_binop {Σ σ σ11 σ12 σ21 σ22}
      (op1 : BinOp σ11 σ12 σ) (t11 : Term Σ σ11) (t12 : Term Σ σ12)
      (op2 : BinOp σ21 σ22 σ) (t21 : Term Σ σ21) (t22 : Term Σ σ22)
      : DList Σ :=
    | bop.pair | t11 | t12 | bop.pair | t21 | t22 =>
      cat
        (singleton (formula_relop bop.eq t11 t21))
        (singleton (formula_relop bop.eq t12 t22))
    | bop.cons | t11 | t12 | bop.cons | t21 | t22 =>
      cat
        (singleton (formula_relop bop.eq t11 t21))
        (singleton (formula_relop bop.eq t12 t22))
    | op1      | t11 | t12 | op2      | t21 | t22 =>
      simplify_eqb (term_binop op1 t11 t12) (term_binop op2 t21 t22).

    Lemma simplify_eq_binop_spec [Σ σ σ11 σ12 σ21 σ22]
      (op1 : BinOp σ11 σ12 σ) (t11 : Term Σ σ11) (t12 : Term Σ σ12)
      (op2 : BinOp σ21 σ22 σ) (t21 : Term Σ σ21) (t22 : Term Σ σ22) :
      simplify_eq_binop op1 t11 t12 op2 t21 t22 ⊣⊢
      singleton (formula_relop bop.eq (term_binop op1 t11 t12) (term_binop op2 t21 t22)).
    Proof. destruct op1; arw; dependent elimination op2; arw; intro ι; arw. Qed.
    #[local] Hint Rewrite simplify_eq_binop_spec : katamaran.
    #[local] Opaque simplify_eq_binop.

    Equations(noeqns) simplify_eq_unop {Σ σ σ1 σ2}
      (op1 : UnOp σ1 σ) (t1 : Term Σ σ1)
      (op2 : UnOp σ2 σ) (t2 : Term Σ σ2)
      : DList Σ :=
    | uop.inl | t1 | uop.inl | t2 => singleton (formula_relop bop.eq t1 t2)
    | uop.inl | t1 | uop.inr | t2 => error
    | uop.inr | t1 | uop.inl | t2 => error
    | uop.inr | t1 | uop.inr | t2 => singleton (formula_relop bop.eq t1 t2)
    | op1     | t1 | op2     | t2 =>
      simplify_eqb (term_unop op1 t1) (term_unop op2 t2).

    Lemma simplify_eq_unop_spec [Σ σ σ1 σ2]
      (op1 : UnOp σ1 σ) (t1 : Term Σ σ1)
      (op2 : UnOp σ2 σ) (t2 : Term Σ σ2) :
      simplify_eq_unop op1 t1 op2 t2 ⊣⊢
      singleton (formula_relop bop.eq (term_unop op1 t1) (term_unop op2 t2)).
    Proof. destruct op1; arw; dependent elimination op2; arw; intro ι; arw. Qed.
    #[local] Hint Rewrite simplify_eq_unop_spec : katamaran.
    #[local] Opaque simplify_eq_unop.

    Definition simplify_eq_union_val [Σ U] [K1 : unionk U]
      (t1 : Term Σ (unionk_ty U K1)) (v2 : Val (ty.union U)) : DList Σ :=
       let (K2, v2) := unionv_unfold U v2 in
       match eq_dec K1 K2 with
       | left e  => let v2' := eq_rec_r (fun K1 => Val (unionk_ty U K1)) v2 e in
                    let t2  := term_val (unionk_ty U K1) v2' in
                    singleton (formula_relop bop.eq t1 t2)
       | right _ => error
       end.

    Set Equations With UIP.
    Lemma simplify_eq_union_val_spec [Σ U] [K1 : unionk U]
      (t1 : Term Σ (unionk_ty U K1)) (v : Val (ty.union U)) :
      simplify_eq_union_val t1 v ⊣⊢
      singleton (formula_relop bop.eq (term_union U K1 t1) (term_val (ty.union U) v)).
    Proof.
      unfold simplify_eq_union_val.
      destruct unionv_unfold as [K2 v2] eqn:?.
      apply (f_equal (unionv_fold U)) in Heqs.
      rewrite unionv_fold_unfold in Heqs. subst.
      destruct eq_dec as [e|e]; arw.
      - intros ι; arw. split; intros HYP.
        + destruct e. now f_equal.
        + depelim HYP. now dependent elimination e.
      - intros ι; arw. congruence.
    Qed.
    #[local] Opaque simplify_eq_union_val.

    Fixpoint simplify_eq_val {Σ} [σ] (t : Term Σ σ) : forall (v : Val σ), DList Σ :=
      match t with
      | term_var x          => fun v => singleton (formula_relop bop.eq (term_var x) (term_val _ v))
      | term_val σ v        => fun v' => if eq_dec v v' then empty else error
      | term_binop op t1 t2 => simplify_eq_binop_val op t1 t2
      | term_unop op t      => simplify_eq_unop_val op t
      | term_tuple ts       => env.Env_rect
                                 (fun σs _ => Val (ty.tuple σs) -> DList Σ)
                                 (fun _ => empty)
                                 (fun τs _ IHts τ t (vτsτ : Val (ty.tuple (τs ▻ τ))) =>
                                    let (vτs, vτ) := vτsτ in
                                    cat (simplify_eq_val t vτ) (IHts vτs))
                                 ts
      | term_union U K t    => simplify_eq_union_val t
      | term_record R ts    => fun vR =>
                                 env.Env_rect
                                   (fun Δ _ => NamedEnv Val Δ -> DList Σ)
                                   (fun _ => empty)
                                   (fun Δ _ IHts b t vs =>
                                      let (vsΔ,vb) := env.view vs in
                                      cat (IHts vsΔ) (simplify_eq_val t vb))
                                   ts
                                   (recordv_unfold R vR)
      end.

    Lemma simplify_eq_val_spec [Σ σ] (t : Term Σ σ) (v : Val σ) :
      simplify_eq_val t v ⊣⊢ singleton (formula_relop bop.eq t (term_val σ v)).
    Proof.
      induction t; cbn.
      - reflexivity.
      - destruct eq_dec; arw.
      - apply simplify_eq_binop_val_spec.
      - apply simplify_eq_unop_val_spec.
      - induction IH; cbn.
        + now destruct v.
        + destruct v as [vs v]. rewrite q, IHIH. clear.
          intros ι; arw.
      - apply simplify_eq_union_val_spec.
      - rewrite <- (recordv_fold_unfold R v) at 2.
        generalize (recordv_unfold R v). clear v.
        intros n ι. arw.
        induction IH; env.destroy n; arw.
        rewrite IHIH, (q v ι). arw.
    Qed.
    #[local] Opaque simplify_eq_val.
    #[local] Hint Rewrite simplify_eq_val_spec : katamaran.

    Section SimplifyEqCtx.
      Variable simplify_eq : forall {Σ σ} (t1 t2 : Term Σ σ), DList Σ.

      Equations(noeqns) formula_eqs_ctx {Σ Δ}
        (δ δ' : Env (Term Σ) Δ) : DList Σ :=
      | env.nil,        env.nil          => empty
      | env.snoc δ _ t, env.snoc δ' _ t' =>
        cat (formula_eqs_ctx δ δ') (simplify_eq t t').

      Equations(noeqns) formula_eqs_nctx {N Σ} {Δ : NCtx N Ty}
        (δ δ' : NamedEnv (Term Σ) Δ) : DList Σ :=
      | env.nil,        env.nil          => empty
      | env.snoc δ _ t, env.snoc δ' _ t' =>
        cat (formula_eqs_nctx δ δ') (simplify_eq t t').

    End SimplifyEqCtx.

    Equations(noeqns) simplify_eq {Σ σ} (t1 t2 : Term Σ σ) : DList Σ :=
    simplify_eq (term_val _ v)           t                        := simplify_eq_val t v;
    simplify_eq t                        (term_val _ v)           := simplify_eq_val t v;
    simplify_eq (term_binop op1 t11 t12) (term_binop op2 t21 t22) := simplify_eq_binop op1 t11 t12 op2 t21 t22;
    simplify_eq (term_unop op1 t1)       (term_unop op2 t2)       := simplify_eq_unop op1 t1 op2 t2;
    simplify_eq (term_tuple ts1)         (term_tuple ts2)         := formula_eqs_ctx (@simplify_eq) ts1 ts2;
    simplify_eq (term_record _ ts1)      (term_record _ ts2)      := formula_eqs_nctx (@simplify_eq) ts1 ts2;
    simplify_eq (term_union _ K1 t1)     (term_union _ K2 t2) with eq_dec K1 K2 => {
      simplify_eq (term_union _ K1 t1)   (term_union _ ?(K1) t2) (left eq_refl) := simplify_eq t1 t2;
      simplify_eq _ _ (right _) := error
    };
    simplify_eq t1              t2   := simplify_eqb t1 t2.

    Lemma simplify_eq_spec [Σ σ] (s t : Term Σ σ) :
      simplify_eq s t ⊣⊢ singleton (formula_relop bop.eq s t).
    Proof.
      induction s.
      - dependent elimination t; arw.
      - arw.
      - dependent elimination t; arw.
      - dependent elimination t; arw.
      - dependent elimination t; arw. intros ι. arw.
        induction IH; env.destroy ts; arw.
        rewrite IHIH, (q v ι). arw.
      - dependent elimination t; arw. destruct eq_dec as [Heq|Hneq]; arw.
        + destruct Heq; cbn. rewrite IHs. intros ι; arw. split; intros HYP.
          * now f_equal.
          * now depelim HYP.
        + intros ι; arw. congruence.
      - dependent elimination t; arw. intros ι. arw.
        induction IH; env.destroy ts0; arw.
        rewrite IHIH, (q v ι). arw.
    Qed.

    Definition simplify_relopb {Σ σ} (op : RelOp σ)
      (t1 t2 : STerm σ Σ) : DList Σ :=
      match term_get_val t1 , term_get_val t2 with
      | Some v1 , Some v2 => if bop.eval_relop_val op v1 v2 then empty else error
      | _       , _       => singleton (formula_relop op t1 t2)
      end.

    Definition simplify_relop {Σ σ} (op : RelOp σ) :
      forall (t1 t2 : STerm σ Σ), DList Σ :=
      match op with
      | bop.eq => fun t1 t2 => simplify_eq t1 t2
      | _      => simplify_relopb op
      end.

    Definition simplify_relopb_spec {Σ σ} (op : RelOp σ)
      (t1 t2 : STerm σ Σ) :
      simplify_relopb op t1 t2 ⊣⊢ singleton (formula_relop op t1 t2).
    Proof.
      unfold simplify_relopb.
      destruct (term_get_val_spec t1) as [v1|]; try easy. subst.
      destruct (term_get_val_spec t2) as [v2|]; try easy. subst.
      rewrite formula_relop_val. destruct bop.eval_relop_val; [easy|].
      now apply error_l_unsatisfiable, unsatisfiable_singleton.
    Qed.
    #[local] Opaque simplify_relopb.

    Definition simplify_relop_spec {Σ σ} (op : RelOp σ) (t1 t2 : STerm σ Σ) :
      simplify_relop op t1 t2 ⊣⊢ singleton (formula_relop op t1 t2).
    Proof.
      unfold simplify_relop.
      destruct op; cbn; rewrite ?simplify_relopb_spec; try easy.
      apply simplify_eq_spec.
    Qed.

    Fixpoint simplify_formula {Σ} (fml : Formula Σ) : DList Σ :=
      match fml with
      | formula_user p ts      => singleton (formula_user p (pevals ts))
      | formula_bool t         => simplify_bool (peval t)
      | formula_prop ζ P       => singleton fml
      | formula_relop op t1 t2 => simplify_relop op (peval t1) (peval t2)
      | formula_true           => empty
      | formula_false          => error
      | formula_and F1 F2      => cat (simplify_formula F1) (simplify_formula F2)
      | formula_or F1 F2       => singleton fml
      end.

    Fixpoint simplify_pathcondition {Σ} (C : PathCondition Σ) : DList Σ :=
      match C with
      | [ctx] => empty
      | C ▻ F => cat (simplify_pathcondition C) (simplify_formula F)
      end.

    Lemma simplify_formula_spec {Σ} (F : Formula Σ) :
      simplify_formula F ⊣⊢ singleton F.
    Proof.
      induction F; cbn.
      - arw. apply pevals_sound.
      - arw. apply peval_sound.
      - reflexivity.
      - rewrite simplify_relop_spec. arw.
        apply proper_formula_relop; apply peval_sound.
      - arw.
      - arw.
      - arw. now apply proper_cat.
      - arw.
    Qed.

    Lemma simplify_pathcondition_spec {Σ} (C : PathCondition Σ) (ι : Valuation Σ) :
      instprop (run (simplify_pathcondition C)) ι <-> instprop C ι.
    Proof.
      change (instprop (simplify_pathcondition C) ι <-> instprop C ι).
      induction C as [|C IHC F]; cbn.
      - reflexivity.
      - rewrite instprop_dlist_cat. apply and_iff_morphism; [easy|].
        now rewrite (simplify_formula_spec F ι), instprop_dlist_singleton.
    Qed.

    Definition occurs_check_lt {Σ x} (xIn : x ∈ Σ) {σ} (t : Term Σ σ) : option (Term (Σ - x) σ) :=
      match t with
      | term_var_in yIn =>
        if Nat.ltb (ctx.in_at xIn) (ctx.in_at yIn) then occurs_check xIn t else None
      | _ => occurs_check xIn t
      end.

    Lemma occurs_check_lt_sound {Σ x} (xIn : x ∈ Σ) {σ} (t : Term Σ σ) (t' : Term (Σ - x) σ) :
      occurs_check_lt xIn t = Some t' -> t = subst t' (sub_shift xIn).
    Proof.
      unfold occurs_check_lt. intros Hwlp.
      pose proof (occurs_check_sound xIn t) as H.
      unfold OccursCheckSoundPoint in H.
      rewrite option.wlp_forall in H. apply H. clear H.
      destruct t; auto. destruct (Nat.ltb _ _); auto.
      discriminate.
    Qed.

    Equations(noeqns) try_unify_bool {w : World} (t : Term w ty.bool) :
      option { w' & Tri w w' } :=
      try_unify_bool (@term_var _ x σ xIn) :=
        Some (existT _ (tri_cons x (term_val ty.bool true) tri_id));
      try_unify_bool (term_unop uop.not (@term_var _ x σ xIn)) :=
        Some (existT _ (tri_cons x (term_val ty.bool false) tri_id));
      try_unify_bool _ :=
        None.

    Definition try_unify_eq {w : World} {σ} (t1 t2 : Term w σ) :
      option { w' & Tri w w' } :=
      match t1 with
      | @term_var _ ς σ ςInΣ =>
        fun t2 : Term w σ =>
          match occurs_check_lt ςInΣ t2 with
          | Some t => Some (existT _ (tri_cons ς t tri_id))
          | None => None
          end
      | _ => fun _ => None
      end t2.

    Definition try_unify_formula {w : World} (fml : Formula w) :
      option { w' & Tri w w' } :=
      match fml with
      | formula_bool t => try_unify_bool t
      | formula_relop bop.eq t1 t2 =>
        match try_unify_eq t1 t2 with
        | Some r => Some r
        | None => try_unify_eq t2 t1
        end
      | _ => None
      end.

    Lemma try_unify_bool_spec {w : World} (t : Term w ty.bool) :
      option.wlp (fun '(existT w' ν) => forall ι, inst (T := STerm ty.bool) t ι = true <-> inst_triangular ν ι) (try_unify_bool t).
    Proof.
      induction t using Term_bool_ind; cbn; try constructor; auto.
      - intros ι. cbn. intuition.
      - induction t using Term_bool_ind; cbn; try constructor; auto.
        intros ι. cbn. destruct ι.[??ς]; intuition.
    Qed.

    Lemma try_unify_eq_spec {w : World} {σ} (t1 t2 : Term w σ) :
      option.wlp (fun '(existT w' ν) => forall ι, inst t1 ι = inst t2 ι <-> inst_triangular ν ι) (try_unify_eq t1 t2).
    Proof.
      unfold try_unify_eq. destruct t1; cbn; try (constructor; auto; fail).
      destruct (occurs_check_lt ςInΣ t2) eqn:Heq; constructor; auto.
      apply occurs_check_lt_sound in Heq. subst.
      intros ι. rewrite inst_subst, inst_sub_shift.
      cbn. intuition.
    Qed.

    Lemma try_unify_formula_spec {w : World} (fml : Formula w) :
      option.wlp (fun '(existT w' ν) => forall ι, instprop fml ι <-> inst_triangular ν ι) (try_unify_formula fml).
    Proof.
      unfold try_unify_formula; destruct fml; cbn; try (constructor; auto; fail).
      - apply try_unify_bool_spec.
      - destruct rop; try constructor; cbn.
        destruct (try_unify_eq_spec t1 t2) as [[w' ν] HYP|]. constructor. auto.
        destruct (try_unify_eq_spec t2 t1) as [[w' ν] HYP|]. constructor.
        intros ι. specialize (HYP ι). intuition.
        now constructor.
    Qed.

    Definition unify_formula {w0 : World} (F : Formula w0) :
      { w1 & Tri w0 w1 * PathCondition w1 }%type :=
      match try_unify_formula F with
      | Some (existT w1 ν01) => existT w1 (ν01 , ctx.nil)
      | None => existT w0 (tri_id , ctx.nil ▻ F)
      end.

    Lemma unify_formula_spec {w0 : World} (fml : Formula w0) :
      match unify_formula fml with
      | existT w1 (ν01 , fmls) =>
        (forall ι0 : Valuation w0,
            instprop fml ι0 ->
            inst_triangular ν01 ι0 /\
            instprop fmls (inst (sub_triangular_inv ν01) ι0)) /\
        (forall ι1 : Valuation w1,
            instprop fmls ι1 ->
            instprop fml (inst (sub_triangular ν01) ι1))
      end.
    Proof.
      unfold unify_formula.
      destruct (try_unify_formula_spec fml).
      - destruct a as [w1 ν01]. split.
        + intros ι0 Hfml. specialize (H ι0). intuition. constructor.
        + intros ι1 []. apply H. apply inst_triangular_valid.
      - cbn. split; intros ?; rewrite inst_sub_id; intuition.
    Qed.

    Fixpoint unify_pathcondition {w0 : World} (C : PathCondition w0) :
      { w1 & Tri w0 w1 * PathCondition w1 }%type.
    Proof.
      destruct C as [|C F].
      - exists w0. split. apply tri_id. apply ctx.nil.
      - destruct (unify_pathcondition w0 C) as (w1 & ν01 & C1).
        clear unify_pathcondition C.
        destruct (unify_formula (persist F (acc_triangular ν01))) as (w2 & ν12 & C2).
        exists w2. split. apply (tri_comp ν01 ν12).
        refine (persist C1 (acc_triangular ν12) ▻▻ C2).
    Defined.

    Lemma unify_pathcondition_spec {w0 : World} (C0 : PathCondition w0) :
      match unify_pathcondition C0 with
      | existT w1 (ν01 , C1) =>
        (forall ι0 : Valuation w0,
            instprop C0 ι0 ->
            inst_triangular ν01 ι0 /\
            instprop C1 (inst (sub_triangular_inv ν01) ι0)) /\
        (forall ι1 : Valuation w1,
            instprop C1 ι1 ->
            instprop C0 (inst (sub_triangular ν01) ι1))
      end.
    Proof.
      induction C0 as [|C0 IHC F0]; cbn.
      - intuition.
      - destruct unify_pathcondition as (w1 & ν01 & C1).
        pose proof (unify_formula_spec (persist F0 (acc_triangular ν01))) as IHF.
        destruct (unify_formula (persist F0 (acc_triangular ν01))) as (w2 & ν12 & C2).
        destruct IHC as [IHC01 IHC10].
        destruct IHF as [IHF12 IHF21].
        split.
        + intros ι0. intros [HCι0 HFι0].
          specialize (IHC01 ι0 HCι0). destruct IHC01 as [Hν01 HCι1].
          specialize (IHF12 (inst (sub_triangular_inv ν01) ι0)).
          rewrite instprop_persist, sub_acc_triangular in IHF12.
          rewrite inst_triangular_right_inverse in IHF12; auto.
          specialize (IHF12 HFι0). destruct IHF12 as [Hν12 Hfmls2].
          unfold PathCondition. rewrite instprop_cat.
          rewrite instprop_persist, inst_tri_comp, sub_acc_triangular.
          split; auto. rewrite sub_triangular_inv_comp, inst_subst. split; auto.
          revert HCι1. remember (inst (sub_triangular_inv ν01) ι0) as ι1.
          rewrite inst_triangular_right_inverse; auto.
        + intros ι2. unfold PathCondition.
          rewrite !instprop_cat, instprop_persist, sub_acc_triangular.
          intros [HCι1 HFι2].
          specialize (IHF21 ι2 HFι2). rewrite instprop_persist, sub_acc_triangular in IHF21.
          specialize (IHC10 (inst (sub_triangular ν12) ι2) HCι1).
          rewrite sub_triangular_comp, inst_subst.
          split; auto.
    Qed.

    Open Scope lazy_bool_scope.
    Equations(noind) formula_eqb {Σ} (f1 f2 : Formula Σ) : bool :=
      formula_eqb (formula_bool t1) (formula_bool t2) := Term_eqb t1 t2;
      formula_eqb (@formula_relop _ σ op1 t11 t12) (@formula_relop _ τ op2 t21 t22) with eq_dec σ τ => {
        formula_eqb (@formula_relop _ σ op1 t11 t12) (@formula_relop _ ?(σ) op2 t21 t22) (left eq_refl) :=
          (if eq_dec op1 op2 then true else false) &&& Term_eqb t11 t21 &&& Term_eqb t12 t22;
        formula_eqb (@formula_relop _ σ op1 t11 t12) (@formula_relop _ τ op2 t21 t22) (right _) := false
      };
      formula_eqb (@formula_user _ p ts1) (@formula_user _ q ts2) with 𝑷_eq_dec p q => {
        formula_eqb (@formula_user _ p ts1) (@formula_user _ ?(p) ts2) (left eq_refl) :=
          env.eqb_hom (@Term_eqb _) ts1 ts2;
        formula_eqb (@formula_user _ p ts1) (@formula_user _ q ts2) (right _) := false
      };
      formula_eqb _ _ := false.

    Lemma formula_eqb_spec {Σ} (f1 f2 : Formula Σ) :
      BoolSpec (f1 = f2) True (formula_eqb f1 f2).
    Proof.
      induction f1; dependent elimination f2; simp formula_eqb;
        repeat
          match goal with
          | |- BoolSpec _ _ false   => constructor; auto
          | |- context[eq_dec _ _ ] => destruct eq_dec; subst; cbn
          | |- context[Term_eqb ?t1 ?t2] =>
              destruct (Term_eqb_spec t1 t2); cbn;
              try (constructor; congruence; fail)
          end.
      - destruct 𝑷_eq_dec.
        + destruct e; cbn.
          destruct (env.eqb_hom_spec (@Term_eqb Σ) (@Term_eqb_spec Σ) ts ts0);
            constructor; [congruence|easy].
        + now constructor.
    Qed.

    Fixpoint assumption_formula {Σ} (C : PathCondition Σ) (F : Formula Σ) (k : PathCondition Σ) {struct C} : PathCondition Σ :=
      match C with
      | [ctx]  => k ▻ F
      | C ▻ F' => if formula_eqb F F'
                     then k
                     else assumption_formula C F k
      end.

    Fixpoint assumption_pathcondition {Σ} (C : PathCondition Σ) (FS : PathCondition Σ) (k : PathCondition Σ) {struct FS} : PathCondition Σ :=
      match FS with
      | [ctx]  => k
      | FS ▻ F => assumption_formula C F (assumption_pathcondition C FS k)
      end.

    Lemma assumption_formula_spec {Σ} (C : PathCondition Σ) (F : Formula Σ) (k : PathCondition Σ) (ι : Valuation Σ) :
      instprop C ι -> instprop k ι /\ instprop F ι <-> instprop (assumption_formula C F k) ι.
    Proof.
      induction C as [|C ? F']; cbn; auto.
      intros [HCι HFι']. specialize (IHC HCι).
      destruct (formula_eqb_spec F F');
        subst; intuition auto.
    Qed.

    Lemma assumption_pathcondition_spec {Σ} (C : PathCondition Σ) (FS : PathCondition Σ) (k : PathCondition Σ) (ι : Valuation Σ) :
      instprop C ι -> instprop k ι /\ instprop FS ι <-> instprop (assumption_pathcondition C FS k) ι.
    Proof.
      intros HCι. induction FS as [|FS ? F]; cbn.
      - intuition auto.
      - pose proof (assumption_formula_spec C F (assumption_pathcondition C FS k) ι HCι).
        intuition auto.
    Qed.

    Definition solver_generic : Solver :=
      fun w0 C0 =>
        match DList.run (simplify_pathcondition C0) with
        | Some C1 => Some (unify_pathcondition (assumption_pathcondition (wco w0) C1 ctx.nil))
        | None => None
        end.

    Lemma solver_generic_spec : SolverSpec solver_generic.
    Proof.
      unfold solver_generic. intros w0 C0.
      pose proof (simplify_pathcondition_spec C0) as Hequiv.
      destruct run as [C0'|]; constructor; cbn.
      - pose proof (unify_pathcondition_spec (assumption_pathcondition (wco w0) C0' ctx.nil)) as Hunify.
        destruct (unify_pathcondition (assumption_pathcondition (wco w0) C0' ctx.nil)) as (w1 & ν01 & C1).
        intros ι0 Hpc0. specialize (Hequiv ι0). cbn in Hequiv.
        pose proof (assumption_pathcondition_spec (wco w0) C0' ctx.nil ι0 Hpc0) as Hassumption.
        destruct Hassumption as [Hassumption01 Hassumption10].
        destruct Hunify as [Hunify01 Hunify10]. specialize (Hunify01 ι0).
        split.
        + intros HC0. apply Hunify01. apply Hassumption01.
          split. constructor. apply Hequiv. auto.
        + intros ι1 Heqι. specialize (Hunify10 ι1).
          split.
          * intros HC0. destruct Hequiv as [_ Hequiv].
            inster Hequiv by auto.
            inster Hassumption01 by split; auto; constructor.
            inster Hunify01 by auto. destruct Hunify01 as [Hν01 HC1].
            revert HC1. subst. now rewrite inst_triangular_left_inverse.
          * intros HC1. inster Hunify10 by subst; auto.
            apply Hequiv. apply Hassumption10. subst; auto.
      - intros ι. specialize (Hequiv ι). cbn in Hequiv. intuition.
    Qed.

  End GenericSolver.

  Definition combined_solver : Solver :=
    let g   := solver_generic in
    let gg  := solver_compose g g in
    let ggu := solver_compose gg solver in
    solver_compose ggu (solver_compose ggu gg).

  Lemma combined_solver_spec : SolverSpec combined_solver.
  Proof.
    unfold combined_solver.
    auto using solver_compose_spec, solver_generic_spec, solver_spec.
  Qed.

End GenericSolverOn.

(* Local Variables: *)
(* proof-omit-proofs-option: t *)
(* End: *)
