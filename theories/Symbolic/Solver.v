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
     NArith.BinNat
     Relations.Relation_Definitions
     ZArith.BinInt.

From Katamaran Require Import
     Base
     Prelude
     Signature
     Symbolic.Worlds.

From Equations Require Import
     Equations.

Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.
Local Set Equations Transparent.

Module Type SolverOn (Import B : Base) (Import SIG : Signature B).

  Module Solver.

    Open Scope list_scope.
    Import List.ListNotations.
    Import option.notations.

    Definition RFormula {Σ} : relation (Formula Σ) :=
      fun x y => forall ι : Valuation Σ, inst x ι <-> inst y ι.
    Definition RFormulas {Σ} : relation (List Formula Σ) :=
      fun xs ys => forall ι : Valuation Σ, instpc xs ι <-> instpc ys ι.
    Definition ROFormulas {Σ} : relation (option (List Formula Σ)) :=
      fun oxs oys =>
        forall ι : Valuation Σ,
          option.wp (fun xs => instpc xs ι) oxs <->
          option.wp (fun ys => instpc ys ι) oys.
    #[local] Notation "x ~ y" := (RFormula x y) (at level 90).
    #[local] Notation "x ≈ y" := (RFormulas x y) (at level 90).
    #[local] Notation "x ≋ y" := (ROFormulas x y) (at level 90).

    #[local] Hint Rewrite @inst_formula_relop_neg @inst_pathcondition_cons @inst_pathcondition_app @inst_pathcondition_nil : katamaran.
    #[local] Hint Rewrite @inst_formula_eqs_ctx @inst_formula_eqs_nctx @envrec.of_env_inj
      @recordv_fold_inj @unionv_fold_inj : katamaran.
    #[local] Hint Rewrite @bop.eval_relop_equiv : katamaran.
    #[local] Hint Rewrite <- and_assoc : katamaran.

    #[local] Instance rformula_equiv {Σ} : Equivalence (@RFormula Σ).
    Proof.
      constructor.
      - unfold Reflexive. easy.
      - unfold Symmetric. easy.
      - intros x y z xy yz ι. now transitivity (inst y ι).
    Qed.

    #[local] Instance rformulas_equiv {Σ} : Equivalence (@RFormulas Σ).
    Proof.
      constructor.
      - unfold Reflexive. easy.
      - unfold Symmetric. easy.
      - intros x y z xy yz ι. now transitivity (instpc y ι).
    Qed.

    #[local] Instance roformulas_equiv {Σ} : Equivalence (@ROFormulas Σ).
    Proof.
      constructor.
      - unfold Reflexive. easy.
      - unfold Symmetric. easy.
      - intros x y z xy yz ι.
        now transitivity (option.wp (fun xs => instpc xs ι) y).
    Qed.

    #[local] Instance proper_cons [Σ] :
      Proper (@RFormula Σ ==> RFormulas ==> RFormulas) cons.
    Proof.
      intros ? ? H1 ? ? H2 ι. rewrite ?inst_pathcondition_cons.
      specialize (H1 ι). specialize (H2 ι). intuition.
    Qed.

    #[local] Instance proper_some [Σ] :
      Proper (@RFormulas Σ ==> @ROFormulas Σ) Some.
    Proof. intros xs ys Hxys ι. now rewrite ?option.wp_some. Qed.

    Local Ltac arw :=
      repeat
        (try progress cbn
           [bop.eval bop.eval_relop_val bop.eval_relop_prop
            Val inst inst_formula inst_term] in *;
         autorewrite with katamaran in *;
         repeat
           match goal with
           | |- Some _ ≋ Some _   => apply proper_some
           | |- _ :: ?k ≈ _ :: ?k => apply proper_cons; [|easy]
           | |- (?B /\ ?A <-> ?C /\ ?A) =>
               apply (@and_iff_compat_r' A B C); intro
           end).

    Lemma formula_bool_relop [Σ σ] (op : RelOp σ) (s t : Term Σ σ) :
      formula_bool (term_binop (bop.relop op) s t) ~ formula_relop op s t.
    Proof. intros ι; now arw. Qed.
    #[local] Hint Rewrite formula_bool_relop : katamaran.

    (* Simplifies boolean terms to equivalent formulas. These come for instance
       from (formula_bool t) or equations of the form
       (formula_relop bop.eq t = true). *)
    Equations simplify_bool [Σ] (t : Term Σ ty.bool) (k : List Formula Σ)  :
      option (List Formula Σ)  :=
    | term_var ς                    | k => Some (formula_bool (term_var ς) :: k)
    | term_val _ b                  | k => if b then Some k else None
    | term_binop bop.and s t        | k => k' <- simplify_bool t k ;; simplify_bool s k'
    | term_binop (bop.relop op) s t | k => (* We do not recurse into the terms of a relop
                                              to avoid defining too many mutually recursive
                                              functions. We content ourselves with the fact
                                              that the boolean term has been turned into
                                              a Prop. *)
                                           Some (formula_relop op s t :: k)
    | term_binop bop.or s t         | k => Some (formula_bool (term_binop bop.or s t) :: k)
    | term_not t                    | k => simplify_bool_neg t k
    (* Simplifies formulas of the the shape (formula_bool (term_not t)) or
       (formula_relop bop.eq t = false) *)
    with simplify_bool_neg [Σ] (t : Term Σ ty.bool) (k : List Formula Σ) : option (List Formula Σ) :=
    | term_var ς                    | k => Some (formula_bool (term_not (term_var ς)) :: k)
    | term_val _ b                  | k => if b then None else Some k
    | term_binop bop.and s t        | k => Some (formula_bool (term_binop bop.or (term_not s) (term_not t)) :: k)
    | term_binop bop.or s t         | k => k' <- simplify_bool_neg t k ;; simplify_bool_neg s k'
    | term_binop (bop.relop op) s t | k => Some (formula_relop_neg op s t :: k)
    | term_not t                    | k => simplify_bool t k.

    Lemma simplify_bool_spec_combined :
      (forall Σ (t : Term Σ ty.bool) (k : List Formula Σ),
          simplify_bool t k ≋ Some (formula_bool t :: k)) *
      (forall Σ (t : Term Σ ty.bool) (k : List Formula Σ),
          simplify_bool_neg t k ≋ Some (formula_bool (term_not t) :: k)).
    Proof.
      (* This uses the fucntional elimination principle
         generated by the equations library. *)
      apply (simplify_bool_elim
               (fun Σ t k r => r ≋ Some (formula_bool t :: k))
               (fun Σ t k r => r ≋ Some (formula_bool (term_not t) :: k))).
      - intros; reflexivity.
      - intros ? [] *; arw; intros ι; arw; intuition.
      - intros ? s t k Ht Hs ι. specialize (Ht ι). arw.
        destruct simplify_bool as [kt|]; arw.
        + rewrite (Hs kt ι); arw. now rewrite Ht.
        + clear Hs. intuition.
      - intros; reflexivity.
      - intros Σ σ op s t k. now arw.
      - easy.
      - easy.
      - intros ? [] * ι; arw; intuition.
      - intros * ι; arw; easy.
      - intros ? s t k Ht Hs ι; specialize (Ht ι). arw.
        destruct simplify_bool_neg as [kt|]; arw.
        + specialize (Hs kt ι). arw. now rewrite Hs, Ht.
        + clear Hs. intuition.
      - intros Σ σ op s t k. arw. intros ι; now arw.
      - intros * HYP ι. specialize (HYP ι); now arw.
    Qed.

    Lemma simplify_bool_spec [Σ] (t : Term Σ ty.bool) (k : List Formula Σ) :
      simplify_bool t k ≋ Some (formula_bool t :: k).
    Proof. apply simplify_bool_spec_combined. Qed.

    Lemma simplify_bool_neg_spec [Σ] (t : Term Σ ty.bool) (k : List Formula Σ) :
      simplify_bool_neg t k ≋ Some (formula_bool (term_not t) :: k).
    Proof. apply simplify_bool_spec_combined. Qed.
    #[local] Opaque simplify_bool simplify_bool_neg.
    #[local] Hint Rewrite simplify_bool_spec simplify_bool_neg_spec : katamaran.

    (* Simplifies equations of the form (term_binop op t1 t2 = v). *)
    Equations(noeqns) simplify_eq_binop_val [Σ σ σ1 σ2]
      (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) (v : Val σ)
      (k : List Formula Σ) : option (List Formula Σ) :=
    | bop.pair       | t1 | t2 | (v1 , v2)  | k =>
      Some (formula_relop bop.eq t1 (term_val _ v1) ::
            formula_relop bop.eq t2 (term_val _ v2) :: k)
    | bop.cons       | t1 | t2 | nil        | k => None
    | bop.cons       | t1 | t2 | cons v1 v2 | k =>
      Some (formula_relop bop.eq t1 (term_val _ v1) ::
            formula_relop bop.eq t2 (term_val (ty.list _) v2) :: k)
    | bop.and        | t1 | t2 | v          | k =>
      if v
      then simplify_bool (term_binop bop.and t1 t2) k
      else simplify_bool_neg (term_binop bop.and t1 t2) k
    | bop.or         | t1 | t2 | v          | k =>
      if v
      then simplify_bool (term_binop bop.or t1 t2) k
      else simplify_bool_neg (term_binop bop.or t1 t2) k
    | bop.relop op   | t1 | t2 | v          | k =>
      if v
      then Some (formula_relop op t1 t2 :: k)
      else Some (formula_relop_neg op t1 t2 :: k)
    | op             | t1 | t2 | v          | k =>
      Some (formula_relop bop.eq (term_binop op t1 t2) (term_val _ v) :: k).

    Lemma simplify_eq_binop_val_spec [Σ σ σ1 σ2]
      (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) (v : Val σ) (k : List Formula Σ) :
      simplify_eq_binop_val op t1 t2 v k ≋
      Some (formula_relop bop.eq (term_binop op t1 t2) (term_val σ v) :: k).
    Proof.
      destruct op; cbn; try reflexivity;
        destruct v; arw; try easy; intros ι; now arw.
    Qed.
    #[local] Opaque simplify_eq_binop_val.
    #[local] Hint Rewrite simplify_eq_binop_val_spec : katamaran.

    Definition simplify_eqb {Σ σ} (t1 t2 : Term Σ σ) (k : List Formula Σ) :
      option (List Formula Σ) :=
      if Term_eqb t1 t2
      then Some k
      else Some (formula_relop bop.eq t1 t2 :: k).

    Lemma simplify_eqb_spec [Σ σ] (t1 t2 : Term Σ σ) (k : List Formula Σ) :
      simplify_eqb t1 t2 k ≋ Some (formula_relop bop.eq t1 t2 :: k).
    Proof.
      unfold simplify_eqb.
      destruct (Term_eqb_spec t1 t2); arw.
      - subst; intros ι; now arw.
      - reflexivity.
    Qed.
    #[local] Hint Rewrite simplify_eqb_spec : katamaran.
    #[local] Opaque simplify_eqb.

    Equations(noeqns) simplify_eq_binop {Σ σ σ11 σ12 σ21 σ22}
      (op1 : BinOp σ11 σ12 σ) (t11 : Term Σ σ11) (t12 : Term Σ σ12)
      (op2 : BinOp σ21 σ22 σ) (t21 : Term Σ σ21) (t22 : Term Σ σ22)
      (k : List Formula Σ) : option (List Formula Σ) :=
    | bop.pair | t11 | t12 | bop.pair | t21 | t22 | k =>
      Some (formula_relop bop.eq t11 t21 :: formula_relop bop.eq t12 t22 :: k)
    | bop.cons | t11 | t12 | bop.cons | t21 | t22 | k =>
      Some (formula_relop bop.eq t11 t21 :: formula_relop bop.eq t12 t22 :: k)
    | op1      | t11 | t12 | op2      | t21 | t22 | k =>
      simplify_eqb (term_binop op1 t11 t12) (term_binop op2 t21 t22) k.

    Lemma simplify_eq_binop_spec [Σ σ σ11 σ12 σ21 σ22]
      (op1 : BinOp σ11 σ12 σ) (t11 : Term Σ σ11) (t12 : Term Σ σ12)
      (op2 : BinOp σ21 σ22 σ) (t21 : Term Σ σ21) (t22 : Term Σ σ22)
      (k : List Formula Σ) :
      simplify_eq_binop op1 t11 t12 op2 t21 t22 k ≋
      Some (formula_relop bop.eq (term_binop op1 t11 t12) (term_binop op2 t21 t22) :: k).
    Proof.
      destruct op1; cbn; arw; try easy; dependent elimination op2;
        cbn; arw; intros ι; now arw.
    Qed.
    #[local] Hint Rewrite simplify_eq_binop_spec : katamaran.
    #[local] Opaque simplify_eq_binop.

    Definition simplify_eq_union [Σ U] [K1 K2 : unionk U]
      (t1 : Term Σ (unionk_ty U K1)) (t2 : Term Σ (unionk_ty U K2)) (k : List Formula Σ) :
      option (List Formula Σ) :=
      match eq_dec K1 K2 with
      | left e  => let t2' := eq_rec_r (fun K => Term Σ (unionk_ty U K)) t2 e in
                   Some (formula_relop bop.eq t1 t2' :: k)
      | right _ => None
      end.

    Set Equations With UIP.
    Lemma simplify_eq_union_spec [Σ U] [K1 K2 : unionk U]
      (t1 : Term Σ (unionk_ty U K1)) (t2 : Term Σ (unionk_ty U K2)) (k : List Formula Σ) :
      simplify_eq_union t1 t2 k ≋
      Some (formula_relop bop.eq (term_union U K1 t1) (term_union U K2 t2) :: k).
    Proof.
      unfold simplify_eq_union. destruct eq_dec; arw.
      - intros ι; arw. split; intros HYP.
        + destruct e. now f_equal.
        + depelim HYP. now dependent elimination e.
      - intros ι; arw. intuition.
    Qed.
    #[local] Opaque simplify_eq_union.

    Definition simplify_eq_union_val [Σ U] [K1 : unionk U]
      (t1 : Term Σ (unionk_ty U K1)) (v2 : Val (ty.union U)) (k : List Formula Σ) :
      option (List Formula Σ) :=
       let (K2, v2) := unionv_unfold U v2 in
       match eq_dec K1 K2 with
       | left e  => let v2' := eq_rec_r (fun K1 => Val (unionk_ty U K1)) v2 e in
                    let t2  := term_val (unionk_ty U K1) v2' in
                    Some (formula_relop bop.eq t1 t2 :: k)
       | right _ => None
       end.

    Lemma simplify_eq_union_val_spec [Σ U] [K1 : unionk U]
      (t1 : Term Σ (unionk_ty U K1)) (v : Val (ty.union U)) (k : List Formula Σ) :
      simplify_eq_union_val t1 v k ≋
      Some (formula_relop bop.eq (term_union U K1 t1) (term_val (ty.union U) v) :: k).
    Proof.
      unfold simplify_eq_union_val.
      destruct unionv_unfold as [K2 v2] eqn:?.
      apply (f_equal (unionv_fold U)) in Heqs.
      rewrite unionv_fold_unfold in Heqs. subst.
      destruct eq_dec as [e|e]; arw.
      - intros ι; arw. split; intros HYP.
        + destruct e. now f_equal.
        + depelim HYP. now dependent elimination e.
      - intros ι; arw. intuition.
    Qed.
    #[local] Opaque simplify_eq_union_val.

    Fixpoint simplify_eq_val {Σ} [σ] (t : Term Σ σ) : forall (v : Val σ) (k : List Formula Σ), option (List Formula Σ) :=
      match t with
      | term_var x          => fun v k => Some (formula_relop bop.eq (term_var x) (term_val _ v) :: k)
      | term_val σ v        => fun v' k => if Val_eqb σ v v' then Some k else None
      | term_binop op t1 t2 => simplify_eq_binop_val op t1 t2
      | term_neg t          => fun v k => Some (formula_relop bop.eq (term_neg t) (term_val ty.int v) :: k)
      | term_not t          => fun v k => if v
                                          then simplify_bool_neg t k
                                          else simplify_bool t k
      | term_inl t          => fun v k =>
                                 match v with
                                 | inl v => simplify_eq_val t v k
                                 | inr _ => None
                                 end
      | term_inr t          => fun v k =>
                                 match v with
                                 | inl _ => None
                                 | inr v => simplify_eq_val t v k
                                 end
      | term_sext t         => fun v k => Some (formula_relop bop.eq (term_sext t) (term_val _ v) :: k)
      | term_zext t         => fun v k => Some (formula_relop bop.eq (term_zext t) (term_val _ v) :: k)
      | term_tuple ts       => env.Env_rect
                                 (fun σs _ => Val (ty.tuple σs) -> List Formula Σ -> option (List Formula Σ))
                                 (fun _ => Some)
                                 (fun τs _ IHts τ t (vτsτ : Val (ty.tuple (τs ▻ τ))) k =>
                                    let (vτs, vτ) := vτsτ in
                                    k' <- simplify_eq_val t vτ k;; IHts vτs k')
                                 ts
      | term_union U K t    => simplify_eq_union_val t
      | term_record R ts    => fun v k => Some (app (formula_eqs_nctx ts (lift (recordv_unfold _ v))) k)
                                 (* env.All_rect *)
                                 (*   (fun Δ _ _ => NamedEnv Val Δ -> List Formula Σ -> OFormulas Σ) *)
                                 (*   (fun _ => Some) *)
                                 (*   (fun Δ _ b _ _ *)
                                 (*        (IHΔ : NamedEnv Val Δ -> List Formula Σ -> OFormulas Σ) *)
                                 (*        (IHb : Val (type b) -> List Formula Σ -> OFormulas Σ) *)
                                 (*        (vΔb : NamedEnv Val (Δ ▻ b)) *)
                                 (*        (k : List Formula Σ) => *)
                                 (*      let (vΔ , vb) := env.snocView vΔb in *)
                                 (*      k' <- IHb vb k;; IHΔ vΔ k') *)
                                 (*   (env.all_intro (fun b t => simplify_eq_val t) ts) *)
                                 (*   (recordv_unfold R v) *)
      end.

    Lemma simplify_eq_val_spec [Σ σ] (t : Term Σ σ) (v : Val σ) :
      forall (k : List Formula Σ),
        simplify_eq_val t v k ≋ Some (formula_relop bop.eq t (term_val σ v) :: k).
    Proof.
      induction t; cbn; intros k; arw.
      - reflexivity.
      - destruct (Val_eqb_spec σ v0 v); arw.
        + subst. intros ι; now arw.
        + intros ι; now arw.
      - reflexivity.
      - reflexivity.
      - destruct v; arw; try easy. intros ι; now arw.
      - destruct v; arw.
        + rewrite IHt; arw. intros ι; now arw.
        + intros ι; now arw.
      - destruct v; arw.
        + intros ι; now arw.
        + rewrite IHt; arw. intros ι; now arw.
      - reflexivity.
      - reflexivity.
      - revert k. induction IH; cbn; intros k; arw.
        + destruct v. intros ι; now arw.
        + destruct v as [vs v]. specialize (q v k).
          destruct (simplify_eq_val d v k) as [k'|]; cbn.
          * rewrite (IHIH vs k'); arw. intros ι. specialize (q ι); arw.
            cbn. rewrite q. now arw.
          * clear IHIH. intros ι. specialize (q ι).
            arw. cbn in *. intuition.
      - apply simplify_eq_union_val_spec.
      - intros ι; arw. rewrite inst_lift. split.
        intros ->. now rewrite recordv_fold_unfold.
        intros <-. now rewrite recordv_unfold_fold.
    Qed.
    #[local] Opaque simplify_eq_val.
    #[local] Hint Rewrite simplify_eq_val_spec : katamaran.

    Equations(noeqns) simplify_eq {Σ σ} (t1 t2 : Term Σ σ)
      (k : List Formula Σ) : option (List Formula Σ) :=
    | term_val _ v           | t                        | k => simplify_eq_val t v k
    | t                      | term_val _ v             | k => simplify_eq_val t v k
    | term_inr _             | term_inl _               | k => None
    | term_inl _             | term_inr _               | k => None
    | term_inl t1            | term_inl t2              | k => simplify_eq t1 t2 k
    | term_inr t1            | term_inr t2              | k => simplify_eq t1 t2 k
    | term_tuple ts1         | term_tuple ts2           | k => Some (app (formula_eqs_ctx ts1 ts2) k)
    | term_record _ ts1      | term_record _ ts2        | k => Some (app (formula_eqs_nctx ts1 ts2) k)
    | term_binop op1 t11 t12 | term_binop op2 t21 t22   | k => simplify_eq_binop op1 t11 t12 op2 t21 t22 k
    | term_union _ K1 t1     | term_union _ K2 t2       | k => simplify_eq_union t1 t2 k
    | t1                     | t2                       | k => simplify_eqb t1 t2 k.

    Lemma simplify_eq_spec [Σ σ] (s t : Term Σ σ) (k : List Formula Σ) :
      simplify_eq s t k ≋ Some (formula_relop bop.eq s t :: k).
    Proof.
      induction s.
      - dependent elimination t; cbn; now arw.
      - cbn. rewrite simplify_eq_val_spec. now arw.
      - dependent elimination t; cbn; now arw.
      - dependent elimination t; cbn; now arw.
      - dependent elimination t; cbn; now arw.
      - dependent elimination t; cbn; arw; try easy.
        + rewrite IHs; arw. intros ι; now arw.
        + intros ι; now arw.
      - dependent elimination t; cbn; arw; try easy.
        + intros ι; now arw.
        + rewrite IHs; arw. intros ι; now arw.
      - dependent elimination t; cbn; arw; try easy.
      - dependent elimination t; cbn; arw; try easy.
      - dependent elimination t; cbn; arw; try easy.
        intros ι; now arw.
      - dependent elimination t; cbn; arw; try easy.
        apply simplify_eq_union_spec.
      - dependent elimination t; cbn; arw; try easy.
        intros ι; now arw.
    Qed.

    Definition simplify_relopb {Σ σ} (op : RelOp σ)
      (t1 t2 : STerm σ Σ) (k : List Formula Σ) : option (List Formula Σ) :=
      match term_get_val t1 , term_get_val t2 with
      | Some v1 , Some v2 => if bop.eval_relop_val op v1 v2 then Some k else None
      | _       , _       => Some (formula_relop op t1 t2 :: k)
      end.

    Definition simplify_relop {Σ σ} (op : RelOp σ) :
      forall (t1 t2 : STerm σ Σ), List Formula Σ -> option (List Formula Σ) :=
      match op with
      | bop.eq => fun t1 t2 k => simplify_eq t1 t2 k
      | _      => simplify_relopb op
      end.

    Definition simplify_relopb_spec {Σ σ} (op : RelOp σ)
      (t1 t2 : STerm σ Σ) (k : List Formula Σ) :
      simplify_relopb op t1 t2 k ≋ Some (formula_relop op t1 t2 :: k).
    Proof.
      unfold simplify_relopb.
      destruct (term_get_val_spec t1) as [v1|]; try easy. subst.
      destruct (term_get_val_spec t2) as [v2|]; try easy. subst.
      - intros ι; arw. destruct bop.eval_relop_val; now arw.
    Qed.
    #[local] Opaque simplify_relopb.

    Definition simplify_relop_spec {Σ σ} (op : RelOp σ)
      (t1 t2 : STerm σ Σ) (k : List Formula Σ) :
      simplify_relop op t1 t2 k ≋ Some (formula_relop op t1 t2 :: k).
    Proof.
      unfold simplify_relop.
      destruct op; cbn; rewrite ?simplify_relopb_spec; try easy.
      now rewrite simplify_eq_spec.
    Qed.

    Fixpoint simplify_formula {Σ} (fml : Formula Σ) (k : List Formula Σ) : option (List Formula Σ) :=
      match fml with
      | formula_user p ts      => Some (formula_user p (pevals ts) :: k)
      | formula_bool t         => simplify_bool (peval t) k
      | formula_prop ζ P       => Some (fml :: k)
      | formula_relop op t1 t2 => simplify_relop op (peval t1) (peval t2) k
      | formula_true           => Some k
      | formula_false          => None
      | formula_and F1 F2      => k' <- simplify_formula F1 k ;;
                                  simplify_formula F2 k'
      | formula_or F1 F2       => Some (fml :: k)
      end.

    Fixpoint simplify_formulas {Σ} (fmls : List Formula Σ) (k : List Formula Σ) : option (List Formula Σ) :=
      match fmls with
      | nil           => Some k
      | cons fml fmls =>
        option.bind (simplify_formulas fmls k) (simplify_formula fml)
      end.

    Lemma simplify_formula_spec {Σ} (fml : Formula Σ) :
      forall k, simplify_formula fml k ≋ Some (fml :: k).
    Proof.
      induction fml; cbn - [peval]; intros k; arw.
      - intros ι; cbn. now rewrite pevals_sound.
      - intros ι; cbn. now rewrite peval_sound.
      - reflexivity.
      - rewrite simplify_relop_spec; arw.
        intros ι; cbn. now rewrite ?peval_sound.
      - intros ι; cbn. easy.
      - intros ι; now arw.
      - intros ι; arw. specialize (IHfml1 k ι).
        destruct (simplify_formula fml1 k) as [k'|]; arw.
        + rewrite (IHfml2 k' ι); arw; intuition.
        + intuition.
      - reflexivity.
    Qed.

    Lemma simplify_formulas_spec {Σ} (fmls k : List Formula Σ) :
      simplify_formulas fmls k ≋ Some (fmls ++ k).
    Proof.
      revert k; induction fmls as [|fml fmls]; cbn; intros k.
      - reflexivity.
      - intros ι. specialize (IHfmls k ι). arw.
        destruct simplify_formulas as [k'|]; arw.
        + rewrite (simplify_formula_spec fml k' ι); arw. now rewrite IHfmls.
        + intuition.
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

    Equations(noeqns) try_unify_bool {w : World} (t : Term w ty.bool) :
      option { w' & Tri w w' } :=
      try_unify_bool (@term_var _ x σ xIn) :=
        Some (existT _ (tri_cons x (term_val ty.bool true) tri_id));
      try_unify_bool (term_not (@term_var _ x σ xIn)) :=
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
      - destruct rop; try constructor; cbn.
        destruct (try_unify_eq_spec t1 t2) as [[w' ν] HYP|]. constructor. auto.
        destruct (try_unify_eq_spec t2 t1) as [[w' ν] HYP|]. constructor.
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
              try (constructor; intuition; fail)
          end.
      - destruct 𝑷_eq_dec.
        + destruct e; cbn.
          destruct (env.eqb_hom_spec (@Term_eqb Σ) (@Term_eqb_spec Σ) ts ts0);
            constructor; intuition.
        + now constructor.
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
      pose proof (simplify_formulas_spec fmls0 nil) as Hequiv.
      destruct simplify_formulas as [fmls0'|]; constructor; cbn.
      - pose proof (unify_formulas_spec (assumption_formulas (wco w0) fmls0' nil)) as Hunify.
        destruct (unify_formulas (assumption_formulas (wco w0) fmls0' nil)) as (w1 & ν01 & fmls1).
        intros ι0 Hpc0. specialize (Hequiv ι0). autorewrite with katamaran in Hequiv.
        pose proof (assumption_formulas_spec (wco w0) fmls0' nil ι0 Hpc0) as Hassumption.
        destruct Hassumption as [Hassumption01 Hassumption10].
        destruct Hunify as [Hunify01 Hunify10]. specialize (Hunify01 ι0).
        split.
        + intros Hfmls0. apply Hunify01. apply Hassumption01.
          split. apply Hequiv. split; auto. constructor.
        + intros ι1 Heqι. specialize (Hunify10 ι1).
          split.
          * intros Hfmls0. destruct Hequiv as [_ Hequiv].
            inster Hequiv by split; auto; constructor.
            inster Hassumption01 by split; auto; constructor.
            inster Hunify01 by auto. destruct Hunify01 as [Hν01 Hfmls1].
            revert Hfmls1. subst. now rewrite inst_triangular_left_inverse.
          * intros Hfmls1. inster Hunify10 by subst; auto.
            apply Hequiv. apply Hassumption10. subst; auto.
      - intros ι. specialize (Hequiv ι).
        autorewrite with katamaran in Hequiv.
        intuition.
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
      let g   := solver_generic_round in
      let gg  := solver_compose g g in
      let ggu := solver_compose gg user in
      solver_compose ggu (solver_compose ggu gg).

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
  (Import SIG : Signature B)
  (SOLV : SolverKit B SIG)
  <: SolverKit B SIG.

  Include SolverOn B SIG.

  Definition solver : Solver :=
    Solver.generic SOLV.solver.
  Definition solver_spec : SolverSpec solver :=
    Solver.generic_spec SOLV.solver_spec.

End MakeSolver.
