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
     ZArith.BinInt.

From Katamaran Require Import
     Prelude
     Symbolic.Worlds
     Specification
     Base.

From Equations Require Import
     Equations.

Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.

Module Type SolverOn
  (Import B    : Base)
  (Import PK   : PredicateKit B)
  (Import FML  : FormulasOn B PK)
  (Import WRLD : WorldsOn B PK FML).

  Module Solver.

    Equations(noeqns) simplify_formula_bool_binop {Σ σ1 σ2} (op : BinOp σ1 σ2 ty_bool) (t1 : STerm σ1 Σ) (t2 : STerm σ2 Σ) (k : List Formula Σ) : List Formula Σ :=
    | binop_eq  | t1 | t2 | k := cons (formula_eq t1 t2) k;
    | binop_le  | t1 | t2 | k := cons (formula_le t1 t2) k;
    | binop_lt  | t1 | t2 | k := cons (formula_lt t1 t2) k;
    | binop_ge  | t1 | t2 | k := cons (formula_ge t1 t2) k;
    | binop_gt  | t1 | t2 | k := cons (formula_gt t1 t2) k;
    | binop_and | t1 | t2 | k := cons (formula_bool t1) (cons (formula_bool t2) k);
    | op        | t1 | t2 | k := cons (formula_bool (term_binop op t1 t2)) k.

    Equations(noeqns) simplify_formula_bool_binop_neg {Σ σ1 σ2} (op : BinOp σ1 σ2 ty_bool) (t1 : STerm σ1 Σ) (t2 : STerm σ2 Σ) (k : List Formula Σ) : List Formula Σ :=
    | binop_eq  | t1 | t2 | k := cons (formula_neq t1 t2) k;
    | binop_le  | t1 | t2 | k := cons (formula_gt t1 t2) k;
    | binop_lt  | t1 | t2 | k := cons (formula_ge t1 t2) k;
    | binop_ge  | t1 | t2 | k := cons (formula_lt t1 t2) k;
    | binop_gt  | t1 | t2 | k := cons (formula_le t1 t2) k;
    | binop_or  | t1 | t2 | k := cons (formula_bool (term_not t1)) (cons (formula_bool (term_not t2)) k);
    | op        | t1 | t2 | k := cons (formula_bool (term_not (term_binop op t1 t2))) k.

    Lemma simplify_formula_bool_binop_spec {Σ σ1 σ2} (op : BinOp σ1 σ2 ty_bool) t1 t2 (k : List Formula Σ) :
      forall ι : Valuation Σ,
        instpc (simplify_formula_bool_binop op t1 t2 k) ι <->
          eval_binop op (inst t1 ι) (inst t2 ι) = true /\ instpc k ι.
    Proof.
      intros; dependent elimination op; cbn;
        rewrite ?inst_pathcondition_cons, ?andb_true_iff; cbn;
        rewrite ?Z.leb_le, ?Z.ltb_lt, ?Z.geb_le, ?Z.ge_le_iff,
          ?Z.gtb_lt, ?Z.gt_lt_iff, ?and_assoc;
        try reflexivity.
      now destruct (Val_eqb_spec σ (inst t1 ι) (inst t2 ι)).
    Qed.

    Lemma simplify_formula_bool_binop_neg_spec {Σ σ1 σ2} (op : BinOp σ1 σ2 ty_bool) t1 t2 k :
      forall ι : Valuation Σ,
        instpc (simplify_formula_bool_binop_neg op t1 t2 k) ι <->
          eval_binop op (inst t1 ι) (inst t2 ι) = false /\ instpc k ι.
    Proof.
      intros; dependent elimination op; cbn;
        rewrite ?inst_pathcondition_cons; cbn;
        change (inst_term ?t ?ι) with (inst t ι);
        rewrite ?Z.eqb_neq, ?Z.leb_gt, ?Z.gt_lt_iff, ?Z.ltb_ge, ?Z.ge_le_iff,
          ?Z.geb_leb, ?Z.leb_gt, ?Z.gtb_ltb, ?Z.ltb_ge,
          ?orb_false_iff, ?negb_true_iff, ?and_assoc;
        try reflexivity.
      now destruct (Val_eqb_spec σ (inst t1 ι) (inst t2 ι)).
    Qed.

    Equations(noeqns) simplify_formula_bool {Σ} (t : Term Σ ty_bool) (k : List Formula Σ) : option (List Formula Σ) :=
    | term_var ς                 | k := Some (cons (formula_bool (term_var ς)) k);
    | term_val _ b               | k := if b then Some k else None;
    | term_binop op t1 t2        | k := Some (simplify_formula_bool_binop op t1 t2 k);
    | term_not t                 | k := simplify_formula_bool_neg t k;
    with simplify_formula_bool_neg {Σ} (t : Term Σ ty_bool) (k : List Formula Σ) : option (List Formula Σ) :=
    | term_var ς                | k := Some (cons (formula_bool (term_not (term_var ς))) k);
    | term_val _ b              | k := if b then None else Some k;
    | term_binop op t1 t2        | k := Some (simplify_formula_bool_binop_neg op t1 t2 k);
    | term_not t                | k := simplify_formula_bool t k.

    Definition simplify_formula_eqb {Σ σ} (t1 t2 : Term Σ σ) (k : List Formula Σ) : option (List Formula Σ) :=
      if Term_eqb t1 t2
      then Some k
      else Some (cons (formula_eq t1 t2) k).

    Lemma simplify_formula_eqb_spec {Σ σ} (t1 t2 : Term Σ σ) (k : List Formula Σ) :
      option.spec
        (fun fmlsk => forall ι, instpc fmlsk ι <-> inst (formula_eq t1 t2) ι /\ instpc k ι)
        (forall ι, ~ inst (formula_eq t1 t2) ι)
        (simplify_formula_eqb t1 t2 k).
    Proof.
      unfold simplify_formula_eqb.
      destruct (Term_eqb_spec t1 t2); constructor; intros ι.
      - subst; intuition.
      - now rewrite inst_pathcondition_cons.
    Qed.

    Equations(noeqns) simplify_formula_eq_binop {Σ σ σ11 σ12 σ21 σ22}
      (op1 : BinOp σ11 σ12 σ) (t11 : Term Σ σ11) (t12 : Term Σ σ12)
      (op2 : BinOp σ21 σ22 σ) (t21 : Term Σ σ21) (t22 : Term Σ σ22)
      (k : List Formula Σ) : option (List Formula Σ) :=
    | binop_pair | t11 | t12 | binop_pair | t21 | t22 | k :=
      Some (cons (formula_eq t11 t21) (cons (formula_eq t12 t22) k));
    | binop_cons | t11 | t12 | binop_cons | t21 | t22 | k :=
      Some (cons (formula_eq t11 t21) (cons (formula_eq t12 t22) k));
    | op1        | t11 | t12 | op2        | t21 | t22 | k :=
      simplify_formula_eqb (term_binop op1 t11 t12) (term_binop op2 t21 t22) k.

    Lemma simplify_formula_eq_binop_spec {Σ σ σ11 σ12 σ21 σ22}
      (op1 : BinOp σ11 σ12 σ) (t11 : Term Σ σ11) (t12 : Term Σ σ12)
      (op2 : BinOp σ21 σ22 σ) (t21 : Term Σ σ21) (t22 : Term Σ σ22)
      (k : List Formula Σ) :
      option.spec
        (fun fmlsk : List Formula Σ =>
           forall ι,
             instpc fmlsk ι <->
               eval_binop op1 (inst t11 ι) (inst t12 ι) =
               eval_binop op2 (inst t21 ι) (inst t22 ι) /\ instpc k ι)
        (forall ι, eval_binop op1 (inst t11 ι) (inst t12 ι) <>
                   eval_binop op2 (inst t21 ι) (inst t22 ι))
        (simplify_formula_eq_binop op1 t11 t12 op2 t21 t22 k).
    Proof.
      destruct op1; cbn;
        try match goal with
            | |- option.spec _ _ (simplify_formula_eqb ?t1 ?t2 ?k) =>
                generalize (simplify_formula_eqb_spec t1 t2 k);
                let H := fresh in
                let ι := fresh "ι" in
                apply option.spec_monotonic;
                [ let pc := fresh "pc" in intros pc |];
                intros H ι; specialize (H ι); auto
                (* change (inst_term ?t ?ι) with (inst t ι); auto *)
            end.
      - dependent elimination op2; cbn. constructor. intros ι.
        rewrite ?inst_pathcondition_cons. cbn. intuition.
      - dependent elimination op2; cbn.
        + constructor. intros ι.
          rewrite ?inst_pathcondition_cons. cbn. intuition.
        + constructor. intros ι.
          rewrite ?inst_pathcondition_cons. cbn. intuition.
    Qed.

    Equations(noeqns) simplify_formula_eq_binop_val {Σ σ σ1 σ2}
      (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) (v : Val σ)
      (k : List Formula Σ) : option (List Formula Σ) :=
    | binop_pair       | t1 | t2 | (v1 , v2)  | k := Some (cons (formula_eq t1 (term_val _ v1)) (cons (formula_eq t2 (term_val _ v2)) k));
    | binop_cons       | t1 | t2 | nil        | k := None;
    | binop_cons       | t1 | t2 | cons v1 v2 | k := Some (cons (formula_eq t1 (term_val _ v1)) (cons (formula_eq t2 (term_val (ty_list _) v2)) k));
    | binop_tuple_snoc | t1 | t2 | (v1 , v2)  | k := Some (cons (formula_eq t1 (term_val (ty_tuple _) v1)) (cons (formula_eq t2 (term_val _ v2)) k));
    | op               | t1 | t2 | v          | k :=
      Some (cons (formula_eq (term_binop op t1 t2) (term_val _ v)) k).

    Lemma simplify_formula_eq_binop_val_spec {Σ σ σ1 σ2}
      (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) (v : Val σ) (k : List Formula Σ) :
      option.spec
        (fun fmlsk : List Formula Σ =>
           forall ι, instpc fmlsk ι <-> eval_binop op (inst t1 ι) (inst t2 ι) = v /\ instpc k ι)
        (forall ι, eval_binop op (inst t1 ι) (inst t2 ι) <> v)
        (simplify_formula_eq_binop_val op t1 t2 v k).
    Proof.
      destruct op; cbn; try (constructor; intros ι); cbn;
        rewrite ?inst_pathcondition_cons; cbn; try reflexivity.
      - destruct v. constructor. intros ι. cbn.
        rewrite ?inst_pathcondition_cons. cbn. intuition.
      - destruct v; constructor; intros ι; cbn.
        + discriminate.
        + rewrite ?inst_pathcondition_cons. cbn. intuition.
      - destruct v; constructor; intros ι; cbn.
        rewrite ?inst_pathcondition_cons. cbn. intuition.
    Qed.

    Definition simplify_formula_eq_union {Σ U} {K1 K2 : 𝑼𝑲 U}
      (t1 : Term Σ (𝑼𝑲_Ty K1)) (t2 : Term Σ (𝑼𝑲_Ty K2)) (k : List Formula Σ) :
      option (List Formula Σ) :=
      match eq_dec K1 K2 with
      | left e  => let t2' := eq_rec_r (fun K => Term Σ (𝑼𝑲_Ty K)) t2 e in
                   Some (cons (formula_eq t1 t2') k)
      | right _ => None
      end.

    Definition simplify_formula_eq_union_val {Σ U} {K1 : 𝑼𝑲 U}
      (t1 : Term Σ (𝑼𝑲_Ty K1)) (v2 : Val (ty_union U)) (k : List Formula Σ) :
      option (List Formula Σ) :=
       let (K2, v2) := 𝑼_unfold v2 in
       match eq_dec K1 K2 with
       | left e  => let v2' := eq_rec_r (fun K1 => Val (𝑼𝑲_Ty K1)) v2 e in
                    let t2  := term_val (𝑼𝑲_Ty K1) v2' in
                    Some (cons (formula_eq t1 t2) k)
       | right _ => None
       end.

    Section WithUIP.

      Local Set Equations With UIP.

      Lemma simplify_formula_eq_union_spec {Σ U} {K1 K2 : 𝑼𝑲 U}
            (t1 : Term Σ (𝑼𝑲_Ty K1)) (t2 : Term Σ (𝑼𝑲_Ty K2)) (k : List Formula Σ) :
        option.spec
          (fun fmlsk : List Formula Σ =>
             forall ι : Valuation Σ,
               instpc fmlsk ι <->
                 existT (P := fun K => Val (𝑼𝑲_Ty K)) K1 (inst t1 ι) =
                   existT (P := fun K => Val (𝑼𝑲_Ty K)) K2 (inst t2 ι)
                 /\ instpc k ι)
          (forall ι : Valuation Σ,
              existT (P := fun K => Val (𝑼𝑲_Ty K)) K1 (inst t1 ι) <>
                existT (P := fun K => Val (𝑼𝑲_Ty K)) K2 (inst t2 ι))
          (simplify_formula_eq_union t1 t2 k).
      Proof.
        unfold simplify_formula_eq_union.
        destruct eq_dec as [e|e]; constructor; intros ι.
        - rewrite inst_pathcondition_cons. cbn.
          apply and_iff_compat_r'. intros Hk.
          destruct e. cbn. split.
          + intros. now apply f_equal.
          + generalize (inst t1 ι), (inst t2 ι). clear.
            intros v1 v2 H. now dependent elimination H.
        - generalize (inst t1 ι), (inst t2 ι). clear - e.
          intros v1 v2 H. now dependent elimination H.
      Qed.

      Lemma simplify_formula_eq_union_val_spec {Σ U}
        {K1 : 𝑼𝑲 U} (t1 : Term Σ (𝑼𝑲_Ty K1))
        (l : Val (ty_union U)) (k : List Formula Σ) :
        option.spec
          (fun fmlsk : List Formula Σ =>
             forall ι : Valuation Σ,
               instpc fmlsk ι <-> 𝑼_fold (existT K1 (inst t1 ι)) = l /\ instpc k ι)
          (forall ι : Valuation Σ, 𝑼_fold (existT K1 (inst_term t1 ι)) <> l)
          (simplify_formula_eq_union_val t1 l k).
      Proof.
        unfold simplify_formula_eq_union_val.
        destruct 𝑼_unfold as [K2 v2] eqn:?.
        apply (f_equal (@𝑼_fold U)) in Heqs.
        rewrite 𝑼_fold_unfold in Heqs. subst.
        destruct eq_dec as [e|e]; constructor; intros ι.
        - rewrite inst_pathcondition_cons. cbn.
          apply and_iff_compat_r'. intros Hk.
          destruct e. cbn. split.
          + now intros <-.
          + intros.
            apply (f_equal (@𝑼_unfold U)) in H.
            rewrite ?𝑼_unfold_fold in H.
            now dependent elimination H.
        - intros ?. apply (f_equal (@𝑼_unfold U)) in H.
          rewrite ?𝑼_unfold_fold in H. apply e.
            now dependent elimination H.
      Qed.

    End WithUIP.

    Equations(noeqns) simplify_formula_eq {Σ σ} (t1 t2 : Term Σ σ) (k : List Formula Σ) : option (List Formula Σ) :=
    | term_val ?(σ) l1       | term_val σ l2            | k => if Val_eqb σ l1 l2 then Some k else None;
    | term_inr _             | term_val _ (inl _)       | k => None;
    | term_inl _             | term_val _ (inr _)       | k => None;
    | term_inl t1            | term_val _ (inl v2)      | k => simplify_formula_eq t1 (term_val _ v2) k;
    | term_inr t1            | term_val _ (inr v2)      | k => simplify_formula_eq t1 (term_val _ v2) k;
    | term_inr _             | term_inl _               | k => None;
    | term_inl _             | term_inr _               | k => None;
    | term_inl t1            | term_inl t2              | k => simplify_formula_eq t1 t2 k;
    | term_inr t1            | term_inr t2              | k => simplify_formula_eq t1 t2 k;
    | term_record ?(R) ts1   | term_record R ts2        | k => Some (app (formula_eqs_nctx ts1 ts2) k);
    | term_binop op1 t11 t12 | term_binop op2 t21 t22   | k => simplify_formula_eq_binop op1 t11 t12 op2 t21 t22 k;
    | term_binop op1 t11 t12 | term_val _ v             | k => simplify_formula_eq_binop_val op1 t11 t12 v k;
    | term_union U K t       | term_val ?(ty_union U) v | k => simplify_formula_eq_union_val t v k;
    | term_union ?(U) K1 t1  | term_union U K2 t2       | k => simplify_formula_eq_union t1 t2 k;
    | t1                     | t2                       | k => simplify_formula_eqb t1 t2 k.

    Definition simplify_formula {Σ} (fml : Formula Σ) (k : List Formula Σ) : option (List Formula Σ) :=
      match fml with
      (* TODO: partial evaluation of ts *)
      | formula_user p ts => Some (cons fml k)
      | formula_bool t    => simplify_formula_bool (peval t) k
      | formula_prop ζ P  => Some (cons fml k)
      | formula_ge t1 t2  => simplify_formula_bool (peval (term_binop binop_ge t1 t2)) k
      | formula_gt t1 t2  => simplify_formula_bool (peval (term_binop binop_gt t1 t2)) k
      | formula_le t1 t2  => simplify_formula_bool (peval (term_binop binop_le t1 t2)) k
      | formula_lt t1 t2  => simplify_formula_bool (peval (term_binop binop_lt t1 t2)) k
      | formula_eq t1 t2  => simplify_formula_eq (peval t1) (peval t2) k
      | formula_neq t1 t2 => Some (cons fml k)
      end.

    Fixpoint simplify_formulas {Σ} (fmls : List Formula Σ) (k : List Formula Σ) : option (List Formula Σ) :=
      match fmls with
      | nil           => Some k
      | cons fml fmls =>
        option.bind (simplify_formulas fmls k) (simplify_formula fml)
      end.

    Lemma simplify_formula_bool_spec {Σ} (t : Term Σ ty_bool) (k : List Formula Σ) :
      option.spec
        (fun fmlsk => forall ι, instpc fmlsk ι <-> inst (formula_bool t) ι /\ instpc k ι)
        (forall ι, ~ inst (formula_bool t) ι)
        (simplify_formula_bool t k)
    with simplify_formula_bool_neg_spec {Σ} (t : Term Σ ty_bool) (k : List Formula Σ) :
      option.spec
        (fun fmlsk => forall ι, instpc fmlsk ι <-> ~ inst (formula_bool t) ι /\ instpc k ι)
        (forall ι, inst (A := Prop) (formula_bool t) ι)
        (simplify_formula_bool_neg t k).
    Proof.
      { dependent elimination t; cbn; try constructor.
        - intros ι. rewrite inst_pathcondition_cons. reflexivity.
        - destruct v; constructor; intuition.
        - apply simplify_formula_bool_binop_spec.
        - generalize (simplify_formula_bool_neg_spec Σ e0 k).
          apply option.spec_monotonic.
          + intros fmlsk HYP ι; specialize (HYP ι); revert HYP. cbn.
            unfold is_true. now rewrite negb_true_iff, not_true_iff_false.
          + intros HYP ι; specialize (HYP ι); revert HYP. cbn.
            unfold is_true. now rewrite not_true_iff_false, negb_false_iff.
      }
      { dependent elimination t; try constructor.
        - intros ι. rewrite inst_pathcondition_cons. cbn.
          unfold is_true. now rewrite negb_true_iff, not_true_iff_false.
        - destruct v; cbn; constructor; intuition.
        - intros ι. cbn. rewrite not_true_iff_false.
          apply simplify_formula_bool_binop_neg_spec.
        - generalize (simplify_formula_bool_spec Σ e0 k).
          apply option.spec_monotonic.
          + intros fmlsk HYP ι; specialize (HYP ι); revert HYP. cbn.
            unfold is_true. now rewrite not_true_iff_false, negb_false_iff.
          + intros HYP ι; specialize (HYP ι); revert HYP. cbn.
            unfold is_true. now rewrite not_true_iff_false, negb_true_iff.
      }
    Qed.

    Lemma simplify_formula_eq_spec {Σ σ} (s t : Term Σ σ) (k : List Formula Σ) :
      option.spec
        (fun fmlsk : List Formula Σ => forall ι, instpc fmlsk ι <-> inst (formula_eq s t) ι /\ instpc k ι)
        (forall ι, ~ inst (formula_eq s t) ι)
        (simplify_formula_eq s t k).
    Proof.
      induction s; try apply simplify_formula_eqb_spec;
        dependent elimination t; try (cbn; constructor; intros;
          rewrite ?inst_pathcondition_cons; auto; fail).
      - cbn. destruct (Val_eqb_spec σ1 v v0); constructor; intuition.
      - cbn. apply simplify_formula_eq_binop_val_spec.
      - cbn. apply simplify_formula_eq_binop_spec.
      - cbn. destruct v.
        + specialize (IHs (term_val _ v)). revert IHs.
          apply option.spec_monotonic.
          * intros fmls HYP ι. specialize (HYP ι). rewrite HYP. cbn.
            apply and_iff_compat_r. cbn. split; intros Heq.
            -- now f_equal.
            -- apply noConfusion_inv in Heq. apply Heq.
          * intros HYP ι Heq. apply noConfusion_inv in Heq. apply (HYP ι Heq).
        + constructor. discriminate.
      - specialize (IHs t). revert IHs. apply option.spec_monotonic.
        + intros fmls HYP ι. specialize (HYP ι). rewrite HYP. cbn.
          apply and_iff_compat_r. cbn. split; intros Heq.
          * now f_equal.
          * apply noConfusion_inv in Heq. apply Heq.
        + intros HYP ι Heq. apply noConfusion_inv in Heq. apply (HYP ι Heq).
      - cbn. destruct v.
        + constructor. discriminate.
        + specialize (IHs (term_val _ v)). revert IHs.
          apply option.spec_monotonic.
          * intros fmls HYP ι. specialize (HYP ι). rewrite HYP. cbn.
            apply and_iff_compat_r. cbn. split; intros Heq.
            -- now f_equal.
            -- apply noConfusion_inv in Heq. apply Heq.
          * intros HYP ι Heq. apply noConfusion_inv in Heq. apply (HYP ι Heq).
      - specialize (IHs t0). revert IHs. apply option.spec_monotonic.
        + intros fmls HYP ι. rewrite (HYP ι). cbn.
          apply and_iff_compat_r'. intros Hpc.
          split; intros Heq.
          * now f_equal.
          * apply noConfusion_inv in Heq. apply Heq.
        + intros HYP ι Heq. apply noConfusion_inv in Heq. apply (HYP ι Heq).
      - cbn. apply simplify_formula_eq_union_val_spec.
      - cbn. clear. rename e3 into t2, K1 into K2, s into t1, K0 into K1, U0 into U.
        generalize (simplify_formula_eq_union_spec t1 t2 k). apply option.spec_monotonic.
        + intros k'. apply base.forall_proper. intros ι.
          now rewrite 𝑼_fold_inj.
        + apply base.forall_proper. intros ι.
          now rewrite 𝑼_fold_inj.
      - cbn. constructor. intros ι.
        rewrite inst_pathcondition_app, inst_formula_eqs_nctx.
        apply and_iff_compat_r.
        split; intros Heq.
        + f_equal. apply Heq.
        + apply (@f_equal _ _ (@𝑹_unfold R0)) in Heq.
          rewrite ?𝑹_unfold_fold in Heq. apply Heq.
    Qed.

    Lemma simplify_formula_spec {Σ} (fml : Formula Σ) (k : List Formula Σ) :
      option.spec
        (fun fmlsk : List Formula Σ => forall ι, instpc fmlsk ι <-> inst fml ι /\ instpc k ι)
        (forall ι, ~ inst fml ι)
        (simplify_formula fml k).
    Proof.
      destruct fml; cbn - [peval].
      - constructor; intros ι. now rewrite inst_pathcondition_cons.
      - generalize (simplify_formula_bool_spec (peval t) k).
        apply option.spec_monotonic; cbn; intros; specialize (H ι);
          now rewrite (peval_sound t) in H.
      - constructor. intros ι. now rewrite inst_pathcondition_cons.
      - generalize (simplify_formula_bool_spec (peval (term_binop binop_ge t1 t2)) k).
        apply option.spec_monotonic; cbn - [peval]; intros; specialize (H ι); revert H;
          rewrite (peval_sound (term_binop binop_ge t1 t2)); cbn;
          change (inst_term ?t ?ι) with (inst t ι); unfold is_true;
          now rewrite Z.geb_le, Z.ge_le_iff.
      - generalize (simplify_formula_bool_spec (peval (term_binop binop_gt t1 t2)) k).
        apply option.spec_monotonic; cbn; intros; specialize (H ι); revert H;
          rewrite (peval_sound (term_binop binop_gt t1 t2)); cbn;
          change (inst_term ?t ?ι) with (inst t ι); unfold is_true;
          now rewrite Z.gtb_lt, Z.gt_lt_iff.
      - generalize (simplify_formula_bool_spec (peval (term_binop binop_le t1 t2)) k).
        apply option.spec_monotonic; cbn; intros; specialize (H ι); revert H;
          rewrite (peval_sound (term_binop binop_le t1 t2)); cbn;
          change (inst_term ?t ?ι) with (inst t ι); unfold is_true;
          now rewrite Z.leb_le.
      - generalize (simplify_formula_bool_spec (peval (term_binop binop_lt t1 t2)) k).
        apply option.spec_monotonic; cbn; intros; specialize (H ι); revert H;
          rewrite (peval_sound (term_binop binop_lt t1 t2)); cbn;
          change (inst_term ?t ?ι) with (inst t ι); unfold is_true;
          now rewrite Z.ltb_lt.
      - generalize (simplify_formula_eq_spec (peval t1) (peval t2) k).
        apply option.spec_monotonic; cbn; intros; specialize (H ι);
          now rewrite (peval_sound t1), (peval_sound t2) in H.
      - constructor. intros ι. now rewrite inst_pathcondition_cons.
    Qed.

    Lemma simplify_formulas_spec {Σ} (fmls k : List Formula Σ) :
      option.spec
        (fun fmlsk : List Formula Σ => forall ι, instpc fmlsk ι <-> instpc fmls ι /\ instpc k ι)
        (forall ι, ~ instpc fmls ι)
        (simplify_formulas fmls k).
    Proof.
      induction fmls as [|fml fmls]; cbn.
      - constructor. intuition.
      - apply option.spec_bind. revert IHfmls.
        apply option.spec_monotonic.
        + intros fmlsk Hfmls.
          generalize (simplify_formula_spec fml fmlsk).
          apply option.spec_monotonic.
          * intros ? Hfml ι. specialize (Hfmls ι). specialize (Hfml ι).
            intuition.
          * intros Hfml ι. specialize (Hfml ι).
            intuition.
        + intros Hfmls ι. specialize (Hfmls ι).
          intuition.
    Qed.

    Definition occurs_check_lt {Σ x} (xIn : x ∈ Σ) {σ} (t : Term Σ σ) : option (Term (Σ - x) σ) :=
      match t with
      | @term_var _ y σ yIn =>
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

    Equations(noeqns) try_unify_bool {w : World} (t : Term w ty_bool) :
      option { w' & Tri w w' } :=
      try_unify_bool (@term_var _ x σ xIn) :=
        Some (existT _ (tri_cons x (term_val ty_bool true) tri_id));
      try_unify_bool (term_not (@term_var _ x σ xIn)) :=
        Some (existT _ (tri_cons x (term_val ty_bool false) tri_id));
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
      | formula_eq t1 t2 =>
        match try_unify_eq t1 t2 with
        | Some r => Some r
        | None => try_unify_eq t2 t1
        end
      | _ => None
      end.

    Lemma try_unify_bool_spec {w : World} (t : Term w ty_bool) :
      option.wlp (fun '(existT w' ν) => forall ι, inst (T := STerm ty_bool) t ι = true <-> inst_triangular ν ι) (try_unify_bool t).
    Proof.
      dependent elimination t; cbn; try constructor; auto.
      intros ι. cbn. intuition.
      dependent elimination e0; cbn; try constructor; auto.
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
      option.wlp (fun '(existT w' ν) => forall ι, (inst fml ι : Prop) <-> inst_triangular ν ι) (try_unify_formula fml).
    Proof.
      unfold try_unify_formula; destruct fml; cbn; try (constructor; auto; fail).
      - apply try_unify_bool_spec.
      - destruct (try_unify_eq_spec t1 t2) as [[w' ν] HYP|_]. constructor. auto.
        destruct (try_unify_eq_spec t2 t1) as [[w' ν] HYP|_]. constructor.
        intros ι. specialize (HYP ι). intuition.
        now constructor.
    Qed.

    Definition unify_formula {w0 : World} (fml : Formula w0) :
      { w1 & Tri w0 w1 * List Formula w1 }%type :=
      match try_unify_formula fml with
      | Some (existT w1 ν01) => existT w1 (ν01 , nil)
      | None => existT w0 (tri_id , cons fml nil)
      end.

    Lemma unify_formula_spec {w0 : World} (fml : Formula w0) :
      match unify_formula fml with
      | existT w1 (ν01 , fmls) =>
        (forall ι0 : Valuation w0,
            inst (A := Prop) fml ι0 ->
            inst_triangular ν01 ι0 /\
            instpc fmls (inst (sub_triangular_inv ν01) ι0)) /\
        (forall ι1 : Valuation w1,
            instpc fmls ι1 ->
            inst (A := Prop) fml (inst (sub_triangular ν01) ι1))
      end.
    Proof.
      unfold unify_formula.
      destruct (try_unify_formula_spec fml).
      - destruct a as [w1 ν01]. split.
        + intros ι0 Hfml. specialize (H ι0). intuition. constructor.
        + intros ι1 []. apply H. apply inst_triangular_valid.
      - split; intros ?; rewrite inst_pathcondition_cons;
          cbn; rewrite inst_sub_id; intuition.
    Qed.

    Fixpoint unify_formulas {w0 : World} (fmls : List Formula w0) :
      { w1 & Tri w0 w1 * List Formula w1 }%type.
    Proof.
      destruct fmls as [|fml fmls].
      - exists w0. split. apply tri_id. apply nil.
      - destruct (unify_formulas w0 fmls) as (w1 & ν01 & fmls1).
        clear unify_formulas fmls.
        destruct (unify_formula (persist fml (acc_triangular ν01))) as (w2 & ν12 & fmls2).
        exists w2. split. apply (tri_comp ν01 ν12).
        refine (app fmls2 (persist fmls1 (acc_triangular ν12))).
    Defined.

    Lemma unify_formulas_spec {w0 : World} (fmls0 : List Formula w0) :
      match unify_formulas fmls0 with
      | existT w1 (ν01 , fmls1) =>
        (forall ι0 : Valuation w0,
            instpc fmls0 ι0 ->
            inst_triangular ν01 ι0 /\
            instpc fmls1 (inst (sub_triangular_inv ν01) ι0)) /\
        (forall ι1 : Valuation w1,
            instpc fmls1 ι1 ->
            instpc fmls0 (inst (sub_triangular ν01) ι1))
      end.
    Proof.
      induction fmls0 as [|fml0 fmls0]; cbn.
      - intuition.
      - destruct (unify_formulas fmls0) as (w1 & ν01 & fmls1).
        pose proof (unify_formula_spec (persist fml0 (acc_triangular ν01))) as IHfml.
        destruct (unify_formula (persist fml0 (acc_triangular ν01))) as (w2 & ν12 & fmls2).
        destruct IHfmls0 as [IHfmls01 IHfmls10].
        destruct IHfml as [IHfml12 IHfml21].
        split.
        + intros ι0. intros [Hfml Hfmls].
          specialize (IHfmls01 ι0 Hfmls). destruct IHfmls01 as [Hν01 Hfmls1].
          specialize (IHfml12 (inst (sub_triangular_inv ν01) ι0)).
          rewrite inst_persist, sub_acc_triangular in IHfml12.
          rewrite inst_triangular_right_inverse in IHfml12; auto.
          specialize (IHfml12 Hfml). destruct IHfml12 as [Hν12 Hfmls2].
          rewrite inst_pathcondition_app, inst_persist, inst_tri_comp, sub_acc_triangular.
          split; auto. rewrite sub_triangular_inv_comp, inst_subst. split; auto.
          revert Hfmls1. remember (inst (sub_triangular_inv ν01) ι0) as ι1.
          rewrite inst_triangular_right_inverse; auto.
        + intros ι2. rewrite ?inst_pathcondition_app, inst_persist, sub_acc_triangular.
          intros [Hfmls2 Hfmls1].
          specialize (IHfml21 ι2 Hfmls2). rewrite inst_persist, sub_acc_triangular in IHfml21.
          specialize (IHfmls10 (inst (sub_triangular ν12) ι2) Hfmls1).
          rewrite sub_triangular_comp, inst_subst.
          split; auto.
    Qed.

    Open Scope lazy_bool_scope.
    Equations(noind) formula_eqb {Σ} (f1 f2 : Formula Σ) : bool :=
      formula_eqb (formula_bool t1) (formula_bool t2) := Term_eqb t1 t2;
      formula_eqb (formula_le t11 t12) (formula_le t21 t22) := Term_eqb t11 t21 &&& Term_eqb t12 t22;
      formula_eqb (formula_lt t11 t12) (formula_lt t21 t22) := Term_eqb t11 t21 &&& Term_eqb t12 t22;
      formula_eqb (formula_ge t11 t12) (formula_ge t21 t22) := Term_eqb t11 t21 &&& Term_eqb t12 t22;
      formula_eqb (formula_gt t11 t12) (formula_gt t21 t22) := Term_eqb t11 t21 &&& Term_eqb t12 t22;
      formula_eqb (@formula_eq _ σ t11 t12) (@formula_eq _ τ t21 t22) with eq_dec σ τ => {
        formula_eqb (@formula_eq _ σ t11 t12) (@formula_eq _ ?(σ) t21 t22) (left eq_refl) :=
          Term_eqb t11 t21 &&& Term_eqb t12 t22;
        formula_eqb (@formula_eq _ σ t11 t12) (@formula_eq _ τ t21 t22) (right _) := false
      };
      formula_eqb (@formula_neq _ σ t11 t12) (@formula_neq _ τ t21 t22) with eq_dec σ τ => {
        formula_eqb (@formula_neq _ σ t11 t12) (@formula_neq _ ?(σ) t21 t22) (left eq_refl) :=
          Term_eqb t11 t21 &&& Term_eqb t12 t22;
        formula_eqb (@formula_neq _ σ t11 t12) (@formula_neq _ τ t21 t22) (right _) := false
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
      induction f1; dependent elimination f2;
        simp formula_eqb;
        try (constructor; auto; fail).
      - destruct 𝑷_eq_dec.
        + destruct e; cbn.
          destruct (env.eqb_hom_spec (@Term_eqb Σ) (@Term_eqb_spec Σ) ts ts0);
            constructor; intuition.
        + now constructor.
      - destruct (Term_eqb_spec t t0); constructor; intuition.
      - repeat
          match goal with
          | |- context[Term_eqb ?t1 ?t2] =>
              destruct (Term_eqb_spec t1 t2); cbn;
              try (constructor; intuition; fail)
          end.
      - repeat
          match goal with
          | |- context[Term_eqb ?t1 ?t2] =>
              destruct (Term_eqb_spec t1 t2); cbn;
              try (constructor; intuition; fail)
          end.
      - repeat
          match goal with
          | |- context[Term_eqb ?t1 ?t2] =>
              destruct (Term_eqb_spec t1 t2); cbn;
              try (constructor; intuition; fail)
          end.
      - repeat
          match goal with
          | |- context[Term_eqb ?t1 ?t2] =>
              destruct (Term_eqb_spec t1 t2); cbn;
              try (constructor; intuition; fail)
          end.
      - destruct (eq_dec σ σ0); cbn.
        + destruct e.
          repeat
            match goal with
            | |- context[Term_eqb ?t1 ?t2] =>
              destruct (Term_eqb_spec t1 t2); cbn;
                try (constructor; intuition; fail)
            end.
        + constructor; auto.
      - destruct (eq_dec σ σ1); cbn.
        + destruct e.
          repeat
            match goal with
            | |- context[Term_eqb ?t1 ?t2] =>
              destruct (Term_eqb_spec t1 t2); cbn;
                try (constructor; intuition; fail)
            end.
        + constructor; auto.
    Qed.

    Fixpoint assumption_formula {Σ} (pc : PathCondition Σ) (fml : Formula Σ) (k : List Formula Σ) {struct pc} : List Formula Σ :=
      match pc with
      | nil       => cons fml k
      | cons f pc => if formula_eqb f fml
                     then k
                     else assumption_formula pc fml k
      end.

    Fixpoint assumption_formulas {Σ} (pc : PathCondition Σ) (fmls : List Formula Σ) (k : List Formula Σ) {struct fmls} : List Formula Σ :=
      match fmls with
      | nil           => k
      | cons fml fmls => assumption_formula pc fml (assumption_formulas pc fmls k)
      end.

    Lemma assumption_formula_spec {Σ} (pc : PathCondition Σ) (fml : Formula Σ) (k : List Formula Σ) (ι : Valuation Σ) :
      instpc pc ι -> inst (A := Prop) fml ι /\ instpc k ι <-> instpc (assumption_formula pc fml k) ι.
    Proof.
      induction pc as [|f pc]; cbn; auto.
      intros [Hf Hpc]. specialize (IHpc Hpc).
      destruct (formula_eqb_spec f fml);
        subst; intuition.
    Qed.

    Lemma assumption_formulas_spec {Σ} (pc : PathCondition Σ) (fmls : List Formula Σ) (k : List Formula Σ) (ι : Valuation Σ) :
      instpc pc ι -> instpc fmls ι /\ instpc k ι <-> instpc (assumption_formulas pc fmls k) ι.
    Proof.
      intros Hpc. induction fmls as [|fml fmls]; cbn.
      - intuition.
      - pose proof (assumption_formula_spec pc fml (assumption_formulas pc fmls k) ι Hpc).
        intuition.
    Qed.

    Definition solver_generic_round : Solver :=
      fun w0 fmls0 =>
        match simplify_formulas fmls0 nil with
        | Some fmls01 => Some (unify_formulas (assumption_formulas (wco w0) fmls01 nil))
        | None => None
        end.

    Lemma solver_generic_round_spec : SolverSpec solver_generic_round.
    Proof.
      unfold solver_generic_round. intros w0 fmls0.
      destruct (simplify_formulas_spec fmls0 nil) as [fmls0' Hequiv|].
      - constructor.
        pose proof (unify_formulas_spec (assumption_formulas (wco w0) fmls0' nil)) as Hunify.
        destruct (unify_formulas (assumption_formulas (wco w0) fmls0' nil)) as (w1 & ν01 & fmls1).
        intros ι0 Hpc0. specialize (Hequiv ι0).
        pose proof (assumption_formulas_spec (wco w0) fmls0' nil ι0 Hpc0) as Hassumption.
        destruct Hassumption as [Hassumption01 Hassumption10].
        destruct Hunify as [Hunify01 Hunify10]. specialize (Hunify01 ι0).
        split.
        + intros Hfmls0. apply Hunify01. apply Hassumption01.
          split. apply Hequiv. split; auto. constructor.
          constructor.
        + intros ι1 Heqι. specialize (Hunify10 ι1).
          split.
          * intros Hfmls0. destruct Hequiv as [_ Hequiv].
            inster Hequiv by split; auto; constructor.
            inster Hassumption01 by split; auto; constructor.
            inster Hunify01 by auto. destruct Hunify01 as [Hν01 Hfmls1].
            revert Hfmls1. subst. now rewrite inst_triangular_left_inverse.
          * intros Hfmls1. inster Hunify10 by subst; auto.
            apply Hequiv. apply Hassumption10. subst; auto.
      - constructor. intuition.
    Qed.

    Definition solver_compose (s1 s2 : Solver) : Solver :=
      fun w0 fmls0 =>
        option.bind
          (s1 _ fmls0)
          (fun '(existT w1 (ν01 , fmls1)) =>
             option.map
               (fun '(existT w2 (ν12 , fmls2)) =>
                  existT w2 (tri_comp ν01 ν12 , fmls2))
               (s2 _ fmls1)).

    Lemma solver_compose_spec {s1 s2} (spec1 : SolverSpec s1) (spec2 : SolverSpec s2) : SolverSpec (solver_compose s1 s2).
    Proof.
      unfold SolverSpec, solver_compose. intros w0 fmls0.
      apply option.spec_bind.
      generalize (spec1 _ fmls0); clear spec1.
      apply option.spec_monotonic; auto.
      intros (w1 & ν01 & fmls1) H1.
      apply option.spec_map.
      generalize (spec2 _ fmls1); clear spec2.
      apply option.spec_monotonic; auto.
      - intros (w2 & ν12 & fmls2) H2. intros ι0 Hpc0.
        specialize (H1 ι0 Hpc0). destruct H1 as [H01 H10].
        rewrite inst_tri_comp. split.
        + intros Hfmls0. split; auto.
          remember (inst (sub_triangular_inv ν01) ι0) as ι1.
          assert (instpc (wco w1) ι1) as Hpc1 by
              (subst; apply entails_triangular_inv; auto).
          apply H2; auto. apply H10; auto.
          subst; rewrite inst_triangular_right_inverse; auto.
        + intros ι2 Hpc2 Hι0. rewrite sub_triangular_comp, inst_subst in Hι0.
          remember (inst (sub_triangular ν12) ι2) as ι1.
          assert (instpc (wco w1) ι1) as Hpc1 by
              (revert Hpc2; subst; rewrite <- sub_acc_triangular, <- inst_persist; apply ent_acc).
          rewrite H10; eauto. apply H2; auto.
      - intros Hfmls1 ι0 Hpc0 Hfmls0. specialize (H1 ι0 Hpc0).
        destruct H1 as [H01 H10]. inster H01 by auto.
        pose (inst (sub_triangular_inv ν01) ι0) as ι1.
        assert (instpc (wco w1) ι1) as Hpc1 by
            (subst; apply entails_triangular_inv; auto).
        apply (Hfmls1 ι1 Hpc1). revert Hfmls0.
        apply H10; auto. subst ι1.
        now rewrite inst_triangular_right_inverse.
    Qed.

    Definition generic (user : Solver) : Solver :=
      let s := solver_compose solver_generic_round solver_generic_round in
      solver_compose s (solver_compose user s).

    Lemma generic_spec {user} (H : SolverSpec user) :
      SolverSpec (generic user).
    Proof.
      unfold generic.
      auto using solver_compose_spec, solver_generic_round_spec.
    Qed.

  End Solver.

End SolverOn.

Module MakeSolver
  (B : Base)
  (Import SPEC : Specification B)
  (SOLV : SolverKit B SPEC)
  <: SolverKit B SPEC.

  Include SolverOn B SPEC SPEC SPEC.

  Definition solver : Solver :=
    Solver.generic SOLV.solver.
  Definition solver_spec : SolverSpec solver :=
    Solver.generic_spec SOLV.solver_spec.

End MakeSolver.
