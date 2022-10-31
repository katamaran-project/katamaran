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
     Classes.RelationClasses
     Program.Basics
     Program.Tactics
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

  #[export] Instance inst_formula : Inst Formula Prop :=
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

  #[export] Instance inst_subst_formula : InstSubst Formula Prop.
  Proof.
    intros ? ? ? ? f.
    induction f; cbn; repeat f_equal; try easy; now apply inst_subst.
  Qed.

  Lemma inst_formula_relop_neg {Σ σ} (ι : Valuation Σ) (op : RelOp σ) :
    forall (t1 t2 : Term Σ σ),
      inst (formula_relop_neg op t1 t2) ι <->
      bop.eval_relop_val op (inst t1 ι) (inst t2 ι) = false.
  Proof.
    destruct op; cbn; intros t1 t2;
      unfold bv.sle, bv.sleb, bv.slt, bv.sltb;
      unfold bv.ule, bv.uleb, bv.ult, bv.ultb;
      rewrite ?N.ltb_antisym, ?negb_true_iff, ?negb_false_iff, ?N.leb_gt, ?N.leb_le;
      auto; try Lia.lia; try (now destruct eq_dec; intuition).
  Qed.

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

  (* The path condition expresses a set of constraints on the logic variables
     that encode the path taken during execution. *)
  Section PathConditions.

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

    #[export] Instance occurscheck_ctx `{OccursCheck A} : OccursCheck (fun Σ => Ctx (A Σ)) :=
      fix oc {Σ x} xIn ys {struct ys} :=
        match ys with
        | ctx.nil       => Some (ctx.nil)
        | ctx.snoc ys y => ys' <- oc xIn ys ;;
                           y'  <- occurs_check xIn y;;
                           Some (ctx.snoc ys' y')
        end.

    #[export] Instance occurschecklaws_ctx `{OccursCheckLaws A} : OccursCheckLaws (fun Σ => Ctx (A Σ)).
    Proof. occurs_check_derive. Qed.

    #[export] Instance instprop_ctx `{Inst A Prop} : Inst (fun Σ => Ctx (A Σ)) Prop :=
      fix instctx {Σ} (xs : Ctx (A Σ)) (ι : Valuation Σ) : Prop :=
        match xs with
        | ctx.nil       => True
        | ctx.snoc xs x => instctx xs ι /\ inst x ι
        end.

    #[export] Instance instpropsubst_ctx `{InstSubst A Prop} : InstSubst (fun Σ => Ctx (A Σ)) Prop.
    Proof. intros ? ? ζ ι xs. induction xs; cbn; f_equal; auto using inst_subst. Qed.

    Lemma inst_nil `{Inst A Prop} {Σ} (ι : Valuation Σ) :
      inst (@ctx.nil (A Σ)) ι <-> True.
    Proof. reflexivity. Qed.

    Lemma inst_snoc `{Inst A Prop} {Σ} (ι : Valuation Σ) (xs : Ctx (A Σ)) (x : A Σ) :
      inst (xs ▻ x) ι <-> inst xs ι /\ inst x ι.
    Proof. reflexivity. Qed.

    Lemma inst_cat `{Inst A Prop} {Σ} (x y : Ctx (A Σ)) (ι : Valuation Σ) :
      inst (x ▻▻ y) ι <->
      inst x ι /\ inst y ι.
    Proof. induction y; cbn; rewrite ?IHy; intuition. Qed.

    Definition PathCondition (Σ : LCtx) : Type := Ctx (Formula Σ).

    Lemma inst_pathcondition_nil {Σ} (ι : Valuation Σ) :
      inst (T := PathCondition) ctx.nil ι <-> True.
    Proof. reflexivity. Qed.

    Lemma inst_pathcondition_snoc {Σ} (ι : Valuation Σ) (C : PathCondition Σ) (F : Formula Σ) :
      inst (C ▻ F) ι <-> inst C ι /\ inst F ι.
    Proof. reflexivity. Qed.

    Lemma inst_pathcondition_cat {Σ} (C1 C2 : PathCondition Σ) (ι : Valuation Σ) :
      inst (C1 ▻▻ C2) ι <->
      inst C1 ι /\ inst C2 ι.
    Proof. induction C2; cbn; rewrite ?IHC2; intuition. Qed.

    (* Lemma inst_pathcondition_rev_append {Σ} (ι : Valuation Σ) (pc1 pc2 : PathCondition Σ) : *)
    (*   inst (List.rev_append pc1 pc2) ι <-> inst pc1 ι /\ inst pc2 ι. *)
    (* Proof. *)
    (*   revert pc2. *)
    (*   induction pc1; cbn; intros pc2. *)
    (*   - intuition. *)
    (*   - rewrite IHpc1. clear IHpc1. cbn. intuition. *)
    (* Qed. *)

    Equations(noeqns) formula_eqs_ctx {Δ : Ctx Ty} {Σ : LCtx}
      (δ δ' : Env (Term Σ) Δ) : PathCondition Σ :=
      formula_eqs_ctx env.nil          env.nil            := ctx.nil;
      formula_eqs_ctx (env.snoc δ _ t) (env.snoc δ' _ t') :=
        ctx.snoc (formula_eqs_ctx δ δ') (formula_relop bop.eq t t').

    Equations(noeqns) formula_eqs_nctx {N : Set} {Δ : NCtx N Ty} {Σ : LCtx}
      (δ δ' : NamedEnv (Term Σ) Δ) : PathCondition Σ :=
      formula_eqs_nctx env.nil          env.nil            := ctx.nil;
      formula_eqs_nctx (env.snoc δ _ t) (env.snoc δ' _ t') :=
        ctx.snoc (formula_eqs_nctx δ δ') (formula_relop bop.eq t t').

    Lemma inst_formula_eqs_ctx {Δ Σ} (xs ys : Env (Term Σ) Δ) ι :
      inst (formula_eqs_ctx xs ys) ι <-> inst xs ι = inst ys ι.
    Proof.
      induction xs; env.destroy ys; cbn; [easy|].
      now rewrite IHxs, env.inversion_eq_snoc.
    Qed.

    Lemma inst_formula_eqs_nctx {N : Set} {Δ : NCtx N Ty} {Σ} (xs ys : NamedEnv (Term Σ) Δ) ι :
      inst (formula_eqs_nctx xs ys) ι <-> inst xs ι = inst ys ι.
    Proof.
      induction xs; env.destroy ys; cbn; [easy|].
      now rewrite IHxs, env.inversion_eq_snoc.
    Qed.

  End PathConditions.

  (* Avoid some Prop <-> Type confusion. *)
  Notation instprop x ι := (@inst _ Prop _ _ x ι).

  Module Entailment.

    (* A preorder on path conditions. This encodes that either pc1 belongs to a
       longer symbolic execution path (or that it's the same path, but with
       potentially some constraints substituted away). *)
    Definition entails {Σ} (C1 C0 : PathCondition Σ) : Prop :=
      forall (ι : Valuation Σ), instprop C1 ι -> instprop C0 ι.
    Infix "⊢" := (@entails _).

    Definition entails_formula {Σ} (C : PathCondition Σ) (F : Formula Σ) : Prop :=
      forall (ι : Valuation Σ), instprop C ι -> instprop F ι.
    Infix "⊢f" := (@entails_formula _).

    Lemma entails_nil {Σ} {pc : PathCondition Σ} : pc ⊢ ctx.nil.
    Proof. constructor. Qed.

    Lemma entails_cons {Σ} (C1 C2 : PathCondition Σ) (F : Formula Σ) :
      (C1 ⊢ C2) /\ (C1 ⊢f F) <-> (C1 ⊢ C2 ▻ F).
    Proof. unfold entails, entails_formula. cbn. intuition. Qed.

    Definition entails_refl {Σ} : Reflexive (@entails Σ).
    Proof. now unfold Reflexive, entails. Qed.

    Definition entails_trans {Σ} : Transitive (@entails Σ).
    Proof. unfold Transitive, entails; eauto. Qed.

    #[export] Instance preorder_entails {Σ} : PreOrder (@entails Σ).
    Proof. split; auto using entails_refl, entails_trans. Qed.

    Lemma proper_subst_entails {Σ1 Σ2} (ζ12 : Sub Σ1 Σ2) (C1 C2 : PathCondition Σ1) :
      (C1 ⊢ C2) -> (subst C1 ζ12 ⊢ subst C2 ζ12).
    Proof. intros E ι. rewrite ?inst_subst; eauto. Qed.

    (* Definition entails_eq {AT A} `{Inst AT A} {Σ} (C : PathCondition Σ) (a0 a1 : AT Σ) : Prop := *)
    (*   forall (ι : Valuation Σ), instprop C ι -> inst a0 ι = inst a1 ι. *)
    (* Notation "C ⊢ a0 == a1" := *)
    (*   (entails_eq C a0 a1) *)
    (*   (at level 99, a1 at level 200, no associativity). *)

    (* (* (* Not sure this instance is a good idea... *) *)
    (* (*    This seems to cause rewrite to take very long... *) *) *)
    (* (* #[export] Instance proper_entails_pc_iff {Σ} (C : PathCondition Σ) : *) *)
    (* (*   Proper (entails_eq C ==> iff) (entails C). *) *)
    (* (* Proof. *) *)
    (* (*   intros C1 C2 E12. *) *)
    (* (*   split; intros HYP ι ιC; *) *)
    (* (*     specialize (E12 ι ιC); *) *)
    (* (*     specialize (HYP ι ιC); *) *)
    (* (*     congruence. *) *)
    (* (* Qed. *) *)

    (* (* #[export] Instance proper_entails_formula_iff *) *)
    (* (*        {Σ} (C : PathCondition Σ): *) *)
    (* (*      Proper (entails_eq C ==> iff) (entails_formula C). *) *)
    (* (* Proof. *) *)
    (* (*   intros C1 C2 E12. *) *)
    (* (*   split; intros HYP ι ιC; *) *)
    (* (*     specialize (E12 ι ιC); *) *)
    (* (*     specialize (HYP ι ιC); *) *)
    (* (*     congruence. *) *)
    (* (* Qed. *) *)

    (* #[export] Instance proper_entails_eq_impl {AT A} {Σ} {Γ} : *)
    (*   Proper (entails --> eq ==> eq ==> impl) (@entails_eq AT A Γ Σ). *)
    (* Proof. *)
    (*   intros C1 C2 E21 a1 _ [] a2 _ [] eq1 ι ιC2; eauto. *)
    (* Qed. *)

    (* #[export] Instance proper_entails_eq_flip_impl {AT A} `{Inst AT A} {Σ} : *)
    (*   Proper ((@entails Σ) ==> eq ==> eq ==> flip impl) entails_eq. *)
    (* Proof. *)
    (*   intros C1 C2 E21 a1 _ [] a2 _ [] eq1 ι ιC2; eauto. *)
    (* Qed. *)

    (* #[export] Instance equiv_entails_eq `{instA : Inst AT A} {Σ} {C : PathCondition Σ} : *)
    (*   Equivalence (entails_eq C). *)
    (* Proof. *)
    (*   split. *)
    (*   - intuition. *)
    (*   - intros x y xy ι ιC. *)
    (*     now symmetry; apply xy. *)
    (*   - intros x y z xy yz ι ipc. *)
    (*     now transitivity (inst y ι); [apply xy|apply yz]. *)
    (* Qed. *)

    (* (* #[export] Instance proper_entails_eq_flip_impl_pc {AT A} `{Inst AT A} {Σ} {pc : PathCondition Σ}: *) *)
    (* (*   Proper (entails_eq pc ==> entails_eq pc ==> iff) (entails_eq pc). *) *)
    (* (* Proof. *) *)
    (* (*   split; intros Heq. *) *)
    (* (*   - transitivity x; [|transitivity x0]; easy. *) *)
    (* (*   - transitivity y; [|transitivity y0]; easy. *) *)
    (* (* Qed. *) *)

    (* (* #[export] Instance proper_entails_eq_sub_comp *) *)
    (* (*        {Σ1 Σ2 Σ3} {ζ : Sub Σ1 Σ2} (pc : PathCondition Σ3): *) *)
    (* (*   Proper (entails_eq pc ==> entails_eq pc) (subst ζ). *) *)
    (* (* Proof. *) *)
    (* (*   intros ζ1 ζ2 ζ12. *) *)
    (* (*   unfold entails_eq in *. *) *)
    (* (*   intros ι Hpc. specialize (ζ12 ι Hpc). *) *)
    (* (*   now rewrite ?inst_subst, ζ12. *) *)
    (* (* Qed. *) *)

  End Entailment.

End FormulasOn.
