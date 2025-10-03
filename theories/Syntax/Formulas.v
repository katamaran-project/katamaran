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
     Bitvector
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
  | formula_prop {Σ'} (ζ : Sub Σ' Σ) (P : abstract_named RelVal Σ' Prop)
  | formula_relop {σ} (rop : bop.RelOp σ) (t1 t2 : Term Σ σ)
  | formula_true
  | formula_false
  | formula_and (F1 F2 : Formula Σ)
  | formula_or (F1 F2 : Formula Σ)
  | formula_propeq {σ} (t1 t2 : Term Σ σ)
  | formula_secLeak {σ} (t : Term Σ σ)
  .
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
      | formula_propeq t1 t2   => formula_propeq (subst t1 ζ) (subst t2 ζ)
      | formula_secLeak t       => formula_secLeak (subst t ζ)
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

  Definition secLeak {σ} (rv : RelVal σ) : Prop :=
    match rv with
    | SyncVal v => True
    | NonSyncVal _ _ => False
    end.

  #[export] Instance instprop_formula : InstProp Formula :=
    fix inst_formula {Σ} (fml : Formula Σ) (ι : Valuation Σ) :=
      match fml with
      | formula_user p ts      => env.uncurry (𝑷_inst p) (inst ts ι)
      | formula_bool t         => let rvb := inst (A := RelVal ty.bool) t ι in
                                  ty.projLeft rvb = true /\ ty.projRight rvb = true
      | formula_prop ζ P       => uncurry_named P (inst ζ ι)
      | formula_relop op t1 t2 => let rvp := bop.eval_relop_relprop op (inst t1 ι) (inst t2 ι) in
                                    ty.projLeftRV rvp /\ ty.projRightRV rvp
      | formula_true           => True
      | formula_false          => False
      | formula_and F1 F2      => inst_formula F1 ι /\ inst_formula F2 ι
      | formula_or F1 F2       => inst_formula F1 ι \/ inst_formula F2 ι
      | formula_propeq t1 t2   => inst t1 ι = inst t2 ι
      | formula_secLeak t      => secLeak (inst t ι)
      end.

  Lemma formula_bool_move_projs {Σ σ} op (t1 t2 : Term Σ σ ) (ι : Valuation Σ) (b1 b2 : bool) :
    let rvb := bop.eval_relop_relval op (inst t1 ι) (inst t2 ι) in
    (ty.projLeft rvb = b1 /\ ty.projRight rvb = b2) =
      (bop.eval_relop_val op (ty.projLeft (inst t1 ι)) (ty.projLeft (inst t2 ι)) = b1 /\ bop.eval_relop_val op (ty.projRight (inst t1 ι)) (ty.projRight (inst t2 ι)) = b2).
  Proof.
    intros rvp. unfold rvp.
    repeat rewrite bop.comProjLeftEval_relop_relval.
    repeat rewrite bop.comProjRightEval_relop_relval.
    reflexivity.
  Qed.

  Lemma formula_relop_op_move_projs {Σ σ} op (t1 t2 : Term Σ σ ) (ι : Valuation Σ) :
    let rvp := bop.eval_relop_relprop op (inst t1 ι) (inst t2 ι) in
    (ty.projLeftRV rvp /\ ty.projRightRV rvp) =
                           (bop.eval_relop_prop op (ty.projLeft (inst t1 ι)) (ty.projLeft (inst t2 ι)) /\ bop.eval_relop_prop op (ty.projRight (inst t1 ι)) (ty.projRight (inst t2 ι))).
  Proof.
    intros rvp. unfold rvp.
    repeat rewrite bop.comProjLeftRVEval_relop_relprop.
    repeat rewrite bop.comProjRightRVEval_relop_relprop.
    reflexivity.
  Qed.


  (* #[export] Instance instprop_subst_formula : InstPropSubst Formula. *)
  (* Proof. *)
  (*   intros ? ? ? ? f. induction f; cbn; rewrite ?inst_subst; auto. *)
  (*   now apply and_iff_morphism. now apply or_iff_morphism. *)
  (* Qed. *)

  (* Lemma instprop_formula_relop_neg {Σ σ} (ι : Valuation Σ) (op : RelOp σ) : *)
  (*   forall (t1 t2 : Term Σ σ), *)
  (*     instprop (formula_relop_neg op t1 t2) ι <-> *)
  (*     let rvb := bop.eval_relop_relval op (inst t1 ι) (inst t2 ι) in *)
  (*     ty.projLeft rvb = false /\ ty.projRight rvb = false. *)
  (* Proof. *)
  (*   intros t1 t2. rewrite formula_bool_move_projs. *)
  (*   destruct op. *)
  (*   all: *)
  (*     cbn -[bop.eval_relop_relprop bop.eval_relop_val]; *)
  (*     rewrite bop.comProjLeftRVEval_relop_relprop, bop.comProjRightRVEval_relop_relprop. *)
  (*   all: *)
  (*     cbn; *)
  (*     unfold bv.sle, bv.sleb, bv.slt, bv.sltb; *)
  (*     unfold bv.ule, bv.uleb, bv.ult, bv.ultb; *)
  (*     rewrite ?N.ltb_antisym, ?negb_true_iff, ?negb_false_iff, ?N.leb_gt, ?N.leb_le; *)
  (*     auto; try Lia.lia; try now repeat destruct eq_dec. *)
  (* Qed. *)

  Section Reasoning.
    Import Entailment.

    (* #[export] Instance proper_formula_user [Σ p] : *)
    (*   Proper (base.equiv ==> (⊣⊢)) (@formula_user Σ p). *)
    (* Proof. intros xs ys xys ι; cbn; now rewrite xys. Qed. *)

    (* #[export] Instance proper_formula_bool [Σ] : *)
    (*   Proper (base.equiv ==> (⊣⊢)) (@formula_bool Σ). *)
    (* Proof. intros s t e ι; cbn; now rewrite e. Qed. *)

    (* #[export] Instance proper_formula_relop [Σ σ] (rop : RelOp σ) : *)
    (*   Proper (base.equiv ==> base.equiv ==> (⊣⊢)) (@formula_relop Σ σ rop). *)
    (* Proof. intros s1 t1 e1 s2 t2 e2 ι; cbn; now rewrite e1, e2. Qed. *)

    (* Lemma formula_bool_and [Σ] (t1 t2 : Term Σ ty.bool): *)
    (*   formula_bool (term_binop bop.and t1 t2) ⊣⊢ formula_and (formula_bool t1) (formula_bool t2). *)
    (* Proof. intro ι. cbn -[bop.evalRel]. rewrite bop.comProjLeftEvalRel, bop.comProjRightEvalRel. *)
    (*        cbn. repeat rewrite andb_true_iff. intuition. *)
    (* Qed. *)
    (* #[local] Hint Rewrite formula_bool_and : katamaran. *)

    (* Lemma formula_bool_relop [Σ σ] (op : RelOp σ) (s t : Term Σ σ) : *)
    (*   formula_bool (term_binop (bop.relop op) s t) ⊣⊢ formula_relop op s t. *)
    (* Proof. *)
    (*   intro; cbn -[bop.evalRel bop.eval_relop_relprop]; symmetry. *)
    (*   rewrite bop.comProjLeftEvalRel, bop.comProjRightEvalRel. *)
    (*   rewrite bop.comProjLeftRVEval_relop_relprop, bop.comProjRightRVEval_relop_relprop. *)
    (*   now repeat rewrite bop.eval_relop_equiv. *)
    (* Qed. *)

    (* Lemma formula_bool_relop_neg [Σ σ] (op : RelOp σ) (s t : Term Σ σ) : *)
    (*   formula_bool (term_relop_neg op s t) ⊣⊢ formula_relop_neg op s t. *)
    (* Proof. *)
    (*   intro; cbn. *)
    (*   rewrite inst_term_relop_neg. *)
    (*   rewrite instprop_formula_relop_neg. *)
    (*   rewrite ty.comProjLeftLiftUnOp, ty.comProjRightLiftUnOp. *)
    (*   rewrite bop.comProjLeftEval_relop_relval, bop.comProjRightEval_relop_relval. *)
    (*   cbv zeta. rewrite bop.comProjLeftEval_relop_relval, bop.comProjRightEval_relop_relval. *)
    (*   now repeat rewrite negb_true_iff. *)
    (* Qed. *)

    (* Lemma formula_relop_val [Σ σ] (op : RelOp σ) (v1 v2 : Val σ) : *)
    (*   formula_relop (Σ:=Σ) op (term_val σ v1) (term_val σ v2) ⊣⊢ *)
    (*   if bop.eval_relop_val op v1 v2 then formula_true else formula_false. *)
    (* Proof. *)
    (*   intro. cbn. rewrite bop.eval_relop_equiv. *)
    (*   now destruct bop.eval_relop_val. *)
    (* Qed. *)

    (* Lemma formula_and_l [Σ] (F1 F2 : Formula Σ) : formula_and F1 F2 ⊢ F1. *)
    (* Proof. intros ι H. apply H. Qed. *)

    (* Lemma formula_and_r [Σ] (F1 F2 : Formula Σ) : formula_and F1 F2 ⊢ F2. *)
    (* Proof. intros ι H. apply H. Qed. *)

    (* Lemma unsatisfiable_formula_bool [Σ] (t : Term Σ ty.bool) : *)
    (*   base.equiv t (term_val ty.bool false) -> Unsatisfiable (formula_bool t). *)
    (* Proof. intros e ι. specialize (e ι). cbn in *. rewrite e. *)
    (*        cbn. intros [A B]. congruence. *)
    (* Qed. *)

    (* Lemma unsatisfiable_formula_false [Σ] : *)
    (*   Unsatisfiable (@formula_false Σ). *)
    (* Proof. unfold Unsatisfiable; intuition. Qed. *)

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
      | formula_propeq t1 t2   => t1' <- occurs_check xIn t1 ;;
                                  t2' <- occurs_check xIn t2 ;;
                                  Some (formula_propeq t1' t2')
      | formula_secLeak t       => t' <- occurs_check xIn t ;;
                                   Some (formula_secLeak t')
      end.

  #[export] Instance occurs_check_laws_formula : OccursCheckLaws Formula.
  Proof. occurs_check_derive. Qed.

  Section PathCondition.
    Import Entailment.

    Definition PathCondition (Σ : LCtx) : Type := Ctx (Formula Σ).

    (* Lemma formula_cons_true [Σ] (k : PathCondition Σ) : *)
    (*   k ▻ formula_true ⊣⊢ k. *)
    (* Proof. symmetry. now apply snoc_cancel. Qed. *)

    (* Lemma formula_snoc_and [Σ] (k : PathCondition Σ) (F1 F2 : Formula Σ) : *)
    (*   k ▻ formula_and F1 F2 ⊣⊢ k ▻ F1 ▻ F2. *)
    (* Proof. intro ι. cbn. intuition. Qed. *)

    Equations(noeqns) formula_eqs_ctx {Δ : Ctx Ty} {Σ : LCtx}
      (δ δ' : Env (Term Σ) Δ) : PathCondition Σ :=
    | env.nil,        env.nil          => ctx.nil
    | env.snoc δ _ t, env.snoc δ' _ t' =>
        ctx.snoc (formula_eqs_ctx δ δ') (formula_propeq t t').

    Equations(noeqns) formula_eqs_nctx {N : Set} {Δ : NCtx N Ty} {Σ : LCtx}
      (δ δ' : NamedEnv (Term Σ) Δ) : PathCondition Σ :=
    | env.nil,        env.nil          => ctx.nil
    | env.snoc δ _ t, env.snoc δ' _ t' =>
      ctx.snoc (formula_eqs_nctx δ δ') (formula_propeq t t').

    Search Inst Env.
    Locate inst_store.
    Print CStore.
    Print SStore.

    Fixpoint envRelValToRVEnv {nctx} (nenv : Env RelVal nctx) : RV (Env Val nctx) :=
      match nenv with
      | env.nil => SyncVal env.nil
      | env.snoc nenv' db b => ty.liftBinOpRV (fun nenv b => env.snoc nenv db b) (envRelValToRVEnv nenv') b
      end.
    
    (* Lemma instprop_formula_eqs_ctx {Δ Σ} (xs ys : Env (Term Σ) Δ) ι : *)
    (*   instprop (formula_eqs_ctx xs ys) ι <-> inst xs ι = inst ys ι. *)
    (* Proof. *)
    (*   induction xs; env.destroy ys; cbn; [easy|]. *)
    (*   rewrite env.inversion_eq_snoc. *)
    (*   now rewrite IHxs. *)
    (* Qed. *)

    (* Lemma instprop_formula_eqs_nctx {N : Set} {Δ : NCtx N Ty} {Σ} (xs ys : NamedEnv (Term Σ) Δ) ι : *)
    (*   instprop (formula_eqs_nctx xs ys) ι <-> inst xs ι = inst ys ι. *)
    (* Proof. *)
    (*   induction xs; env.destroy ys; cbn; [easy|]. *)
    (*   now rewrite IHxs, env.inversion_eq_snoc. *)
    (* Qed. *)

  End PathCondition.
  Bind Scope ctx_scope with PathCondition.

  Notation formula_eq := (formula_relop bop.eq).
  Notation formula_neq := (formula_relop bop.neq).
  Notation formula_le := (formula_relop bop.le).
  Notation formula_lt := (formula_relop bop.lt).
  Notation formula_bvsle := (formula_relop bop.bvsle).
  Notation formula_bvslt := (formula_relop bop.bvslt).
  Notation formula_bvule := (formula_relop bop.bvule).
  Notation formula_bvult := (formula_relop bop.bvult).

End FormulasOn.
