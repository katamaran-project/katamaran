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
     Program.Basics
     Program.Tactics
     Relations.Relation_Definitions
     ZArith.

From Katamaran Require Import
     Prelude
     Notations
     Syntax.Predicates
     Base.

From Equations Require Import
     Equations.

Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.

Module Type FormulasOn
  (Import B : Base)
  (Import P : PredicateKit B).

  Local Obligation Tactic := idtac.

  Inductive Formula (Σ : LCtx) : Type :=
  | formula_user (p : 𝑷) (ts : Env (Term Σ) (𝑷_Ty p))
  | formula_bool (t : Term Σ ty.bool)
  | formula_prop {Σ'} (ζ : Sub Σ' Σ) (P : abstract_named Val Σ' Prop)
  | formula_relop {σ} (rop : bop.RelOp σ) (t1 t2 : Term Σ σ)
  | formula_true
  | formula_false
  | formula_and (F1 F2 : Formula Σ)
  | formula_or (F1 F2 : Formula Σ).
  #[global] Arguments formula_user {_} p ts.
  #[global] Arguments formula_bool {_} t.
  #[global] Arguments formula_true {_}.
  #[global] Arguments formula_false {_}.

  Definition formula_relop_neg {Σ σ} (op : RelOp σ) :
    forall (t1 t2 : Term Σ σ), Formula Σ :=
    match op with
    | bop.eq     => formula_relop bop.neq
    | bop.neq    => formula_relop bop.eq
    | bop.le     => Basics.flip (formula_relop bop.lt)
    | bop.lt     => Basics.flip (formula_relop bop.le)
    | bop.bvsle  => Basics.flip (formula_relop bop.bvslt)
    | bop.bvslt  => Basics.flip (formula_relop bop.bvsle)
    | bop.bvule  => Basics.flip (formula_relop bop.bvult)
    | bop.bvult  => Basics.flip (formula_relop bop.bvule)
    end.

  #[export] Instance sub_formula : Subst Formula :=
    fix sub_formula {Σ} fml {Σ2} ζ {struct fml} :=
      match fml with
      | formula_user p ts      => formula_user p (subst ts ζ)
      | formula_bool t         => formula_bool (subst t ζ)
      | formula_prop ζ' P      => formula_prop (subst ζ' ζ) P
      | formula_relop op t1 t2 => formula_relop op (subst t1 ζ) (subst t2 ζ)
      | formula_true           => formula_true
      | formula_false          => formula_false
      | formula_and F1 F2      => formula_and (sub_formula F1 ζ) (sub_formula F2 ζ)
      | formula_or F1 F2       => formula_or (sub_formula F1 ζ) (sub_formula F2 ζ)
      end.

  #[export] Instance substlaws_formula : SubstLaws Formula.
  Proof.
      constructor.
      { intros ? F.
        induction F; cbn; f_equal; auto; apply subst_sub_id.
      }
      { intros ? ? ? ? ? F.
        induction F; cbn; f_equal; auto; apply subst_sub_comp.
      }
  Qed.

  #[export] Instance instprop_formula : InstProp Formula :=
    fix inst_formula {Σ} (fml : Formula Σ) (ι : Valuation Σ) :=
      match fml with
      | formula_user p ts      => env.uncurry (𝑷_inst p) (inst ts ι)
      | formula_bool t         => inst (A := Val ty.bool) t ι = true
      | formula_prop ζ P       => uncurry_named P (inst ζ ι)
      | formula_relop op t1 t2 => bop.eval_relop_prop op (inst t1 ι) (inst t2 ι)
      | formula_true           => True
      | formula_false          => False
      | formula_and F1 F2      => inst_formula F1 ι /\ inst_formula F2 ι
      | formula_or F1 F2       => inst_formula F1 ι \/ inst_formula F2 ι
      end.

  #[export] Instance instprop_subst_formula : InstPropSubst Formula.
  Proof.
    intros ? ? ? ? f. induction f; cbn; rewrite ?inst_subst; auto.
    now apply and_iff_morphism. now apply or_iff_morphism.
  Qed.

  Lemma instprop_formula_relop_neg {Σ σ} (ι : Valuation Σ) (op : RelOp σ) :
    forall (t1 t2 : Term Σ σ),
      instprop (formula_relop_neg op t1 t2) ι <->
      bop.eval_relop_val op (inst t1 ι) (inst t2 ι) = false.
  Proof.
    destruct op; cbn; intros t1 t2;
      unfold bv.sle, bv.sleb, bv.slt, bv.sltb;
      unfold bv.ule, bv.uleb, bv.ult, bv.ultb;
      rewrite ?N.ltb_antisym, ?negb_true_iff, ?negb_false_iff, ?N.leb_gt, ?N.leb_le;
      auto; try Lia.lia; now destruct eq_dec.
  Qed.

  Section Reasoning.
    Import Entailment.

    #[export] Instance proper_formula_user [Σ p] :
      Proper (base.equiv ==> (⊣⊢)) (@formula_user Σ p).
    Proof. intros xs ys xys ι; cbn; now rewrite xys. Qed.

    #[export] Instance proper_formula_bool [Σ] :
      Proper (base.equiv ==> (⊣⊢)) (@formula_bool Σ).
    Proof. intros s t e ι; cbn; now rewrite e. Qed.

    #[export] Instance proper_formula_relop [Σ σ] (rop : RelOp σ) :
      Proper (base.equiv ==> base.equiv ==> (⊣⊢)) (@formula_relop Σ σ rop).
    Proof. intros s1 t1 e1 s2 t2 e2 ι; cbn; now rewrite e1, e2. Qed.

    Lemma formula_bool_and [Σ] (t1 t2 : Term Σ ty.bool):
      formula_bool (term_binop bop.and t1 t2) ⊣⊢ formula_and (formula_bool t1) (formula_bool t2).
    Proof. intro ι. cbn. rewrite andb_true_iff. intuition. Qed.
    #[local] Hint Rewrite formula_bool_and : katamaran.

    Lemma formula_bool_relop [Σ σ] (op : RelOp σ) (s t : Term Σ σ) :
      formula_bool (term_binop (bop.relop op) s t) ⊣⊢ formula_relop op s t.
    Proof. intro; cbn; symmetry; apply bop.eval_relop_equiv. Qed.

    Lemma formula_bool_relop_neg [Σ σ] (op : RelOp σ) (s t : Term Σ σ) :
      formula_bool (term_relop_neg op s t) ⊣⊢ formula_relop_neg op s t.
    Proof.
      intro; cbn.
      rewrite inst_term_relop_neg, negb_true_iff.
      now rewrite instprop_formula_relop_neg.
    Qed.

    Lemma formula_relop_val [Σ σ] (op : RelOp σ) (v1 v2 : Val σ) :
      formula_relop (Σ:=Σ) op (term_val σ v1) (term_val σ v2) ⊣⊢
      if bop.eval_relop_val op v1 v2 then formula_true else formula_false.
    Proof.
      intro. cbn. rewrite bop.eval_relop_equiv.
      now destruct bop.eval_relop_val.
    Qed.

    Lemma formula_and_l [Σ] (F1 F2 : Formula Σ) : formula_and F1 F2 ⊢ F1.
    Proof. intros ι H. apply H. Qed.

    Lemma formula_and_r [Σ] (F1 F2 : Formula Σ) : formula_and F1 F2 ⊢ F2.
    Proof. intros ι H. apply H. Qed.

    Lemma unsatisfiable_formula_bool [Σ] (t : Term Σ ty.bool) :
      base.equiv t (term_val ty.bool false) -> Unsatisfiable (formula_bool t).
    Proof. intros e ι. specialize (e ι). cbn in *. congruence. Qed.

    Lemma unsatisfiable_formula_false [Σ] :
      Unsatisfiable (@formula_false Σ).
    Proof. unfold Unsatisfiable; intuition. Qed.

  End Reasoning.

  Import option.notations.
  #[export] Instance OccursCheckFormula : OccursCheck Formula :=
    fix oc {Σ x} xIn fml {struct fml} :=
      match fml with
      | formula_user p ts      => option.map (formula_user p) (occurs_check xIn ts)
      | formula_bool t         => option.map formula_bool (occurs_check xIn t)
      | formula_prop ζ P       => option.map (fun ζ' => formula_prop ζ' P) (occurs_check xIn ζ)
      | formula_relop op t1 t2 => t1' <- occurs_check xIn t1 ;;
                                  t2' <- occurs_check xIn t2 ;;
                                  Some (formula_relop op t1' t2')
      | formula_true           => Some formula_true
      | formula_false          => Some formula_false
      | formula_and F1 F2      => F1' <- oc xIn F1 ;;
                                  F2' <- oc xIn F2 ;;
                                  Some (formula_and F1' F2')
      | formula_or F1 F2       => F1' <- oc xIn F1 ;;
                                  F2' <- oc xIn F2 ;;
                                  Some (formula_or F1' F2')
      end.

  #[export] Instance occurs_check_laws_formula : OccursCheckLaws Formula.
  Proof. occurs_check_derive. Qed.

  Section PathCondition.
    Import Entailment.

    Definition PathCondition (Σ : LCtx) : Type := Ctx (Formula Σ).

    Lemma formula_cons_true [Σ] (k : PathCondition Σ) :
      k ▻ formula_true ⊣⊢ k.
    Proof. symmetry. now apply snoc_cancel. Qed.

    Lemma formula_snoc_and [Σ] (k : PathCondition Σ) (F1 F2 : Formula Σ) :
      k ▻ formula_and F1 F2 ⊣⊢ k ▻ F1 ▻ F2.
    Proof. intro ι. cbn. intuition. Qed.

    Equations(noeqns) formula_eqs_ctx {Δ : Ctx Ty} {Σ : LCtx}
      (δ δ' : Env (Term Σ) Δ) : PathCondition Σ :=
    | env.nil,        env.nil          => ctx.nil
    | env.snoc δ _ t, env.snoc δ' _ t' =>
      ctx.snoc (formula_eqs_ctx δ δ') (formula_relop bop.eq t t').

    Equations(noeqns) formula_eqs_nctx {N : Set} {Δ : NCtx N Ty} {Σ : LCtx}
      (δ δ' : NamedEnv (Term Σ) Δ) : PathCondition Σ :=
    | env.nil,        env.nil          => ctx.nil
    | env.snoc δ _ t, env.snoc δ' _ t' =>
      ctx.snoc (formula_eqs_nctx δ δ') (formula_relop bop.eq t t').

    Lemma instprop_formula_eqs_ctx {Δ Σ} (xs ys : Env (Term Σ) Δ) ι :
      instprop (formula_eqs_ctx xs ys) ι <-> inst xs ι = inst ys ι.
    Proof.
      induction xs; env.destroy ys; cbn; [easy|].
      now rewrite IHxs, env.inversion_eq_snoc.
    Qed.

    Lemma instprop_formula_eqs_nctx {N : Set} {Δ : NCtx N Ty} {Σ} (xs ys : NamedEnv (Term Σ) Δ) ι :
      instprop (formula_eqs_nctx xs ys) ι <-> inst xs ι = inst ys ι.
    Proof.
      induction xs; env.destroy ys; cbn; [easy|].
      now rewrite IHxs, env.inversion_eq_snoc.
    Qed.

  End PathCondition.
  Bind Scope ctx_scope with PathCondition.

  Module Import DList.
    Import Entailment.
    Record DList (Σ : LCtx) : Type :=
      MkDList
      { raw : PathCondition Σ -> Option PathCondition Σ;
        wf : forall k ι, instprop (raw k) ι <-> instprop (raw ctx.nil) ι /\ instprop k ι;
      }.

    #[export] Instance instprop_dlist : InstProp DList :=
      fun Σ x ι => instprop (raw x [ctx]) ι.

    Section Alternative.
      Let equiv {Σ} : relation (DList Σ) :=
        fun x y =>
          forall k1 k2 : PathCondition Σ,
            k1 ⊣⊢ k2 -> raw x k1 ⊣⊢ raw y k2.

      Goal forall {Σ} (x y : DList Σ),
        equiv x y <-> (x ⊣⊢ y).
      Proof.
        intros Σ x y.
        change (equiv x y <-> (raw x [ctx] ⊣⊢ raw y [ctx])).
        destruct x as [x mx], y as [y my]; unfold equiv; cbn.
        split; intros HYP.
        - now apply HYP.
        - intros k1 k2 Hk ι. specialize (Hk ι). specialize (HYP ι).
          rewrite mx, my. intuition.
      Qed.
    End Alternative.

    Definition singleton {Σ} (F : Formula Σ) : DList Σ.
      refine (MkDList (fun k => Some (k ▻ F)) _).
      abstract (cbn; intuition).
    Defined.
    Definition error {Σ} : DList Σ.
    Proof.
      refine (MkDList (fun k => None) _).
      abstract (cbn; intuition).
    Defined.
    Definition empty {Σ} : DList Σ.
      refine (MkDList Some _).
      abstract (cbn; intuition).
    Defined.
    Definition cat {Σ} (xs ys : DList Σ) : DList Σ.
      refine (MkDList (fun k => option.bind (raw xs k) (raw ys)) _).
      abstract
        (destruct xs as [rx wx], ys as [ry wy]; cbn; intros k ι;
         specialize (wx k ι); destruct (rx k) as [k1|], (rx ctx.nil) as [k2|];
         cbn in *; try rewrite (wy k1); try rewrite (wy k2); intuition).
    Defined.
    #[local] Arguments cat {Σ} !_ !_ /.

    Lemma instprop_dlist_singleton [Σ] (F : Formula Σ) (ι : Valuation Σ) :
      instprop (singleton F) ι <-> instprop F ι.
    Proof. now cbn. Qed.

    Lemma instprop_dlist_cat [Σ] (x y : DList Σ) (ι : Valuation Σ) :
      instprop (cat x y) ι <-> instprop x ι /\ instprop y ι.
    Proof.
      destruct x as [x wx], y as [y wy]; cbn.
      destruct (x [ctx]); cbn; [|easy].
      rewrite wy. intuition.
    Qed.

    #[global] Arguments singleton : simpl never.
    #[global] Arguments cat : simpl never.

    Definition run [Σ] (xs : DList Σ) : Option PathCondition Σ :=
      raw xs ctx.nil.

    Lemma run_singleton {Σ} (F : Formula Σ) :
      run (singleton F) ⊣⊢ Some [F]%ctx.
    Proof. easy. Qed.

    #[export] Instance proper_singleton [Σ] : Proper ((⊣⊢) ==> (⊣⊢)) (@DList.singleton Σ).
    Proof. intros F1 F2 HF ι. apply and_iff_morphism; auto. Qed.

    #[export] Instance proper_cat [Σ] : Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (@DList.cat Σ).
    Proof. repeat intro. rewrite !instprop_dlist_cat. now apply and_iff_morphism. Qed.

    Lemma empty_l_valid [Σ] (xs : DList Σ) : Valid xs -> empty ⊣⊢ xs.
    Proof. easy. Qed.

    Lemma empty_r_valid [Σ] (xs : DList Σ) : Valid xs -> xs ⊣⊢ empty.
    Proof. easy. Qed.

    Lemma valid_singleton [Σ] (F : Formula Σ) : Valid F -> Valid (singleton F).
    Proof. easy. Qed.

    Lemma error_l_unsatisfiable [Σ] (xs : DList Σ) : Unsatisfiable xs -> error ⊣⊢ xs.
    Proof. intros uxs ι. specialize (uxs ι). easy. Qed.

    Lemma error_r_unsatisfiable [Σ] (xs : DList Σ) : Unsatisfiable xs -> xs ⊣⊢ error.
    Proof. intros uxs ι. specialize (uxs ι). easy. Qed.

    Lemma unsatisfiable_singleton [Σ] (F : Formula Σ) :
      Unsatisfiable F -> Unsatisfiable (singleton F).
    Proof. apply unsatisfiable_snoc_r. Qed.

    Lemma singleton_formula_and [Σ] (F1 F2 : Formula Σ) :
      singleton (formula_and F1 F2) ⊣⊢ cat (singleton F1) (singleton F2).
    Proof. intro. now rewrite instprop_dlist_cat, !instprop_dlist_singleton. Qed.

    #[export] Instance proper_run [Σ] : Proper ((⊣⊢) ==> (⊣⊢)) (@run Σ).
    Proof. easy. Qed.

  End DList.

End FormulasOn.
