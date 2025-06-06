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
     Classes.RelationClasses
     List
     NArith.BinNat
     ZArith.BinInt
     PArith
     Ring
     Ring_polynom
     micromega.Lia.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Context
     Environment
     Bitvector
     Symbolic.Instantiation
     Syntax.BinOps
     Syntax.Terms
     Syntax.TypeDecl
     Syntax.UnOps
     Syntax.Variables.

Import (notations) stdpp.base.
Import ctx.notations.
Import env.notations.

Local Set Implicit Arguments.
Local Set Transparent Obligations.
Local Unset Elimination Schemes.
Local Set Equations Transparent.

Section Util.
  Lemma jump_of_succ_nat_length {A : Type} {def : A} {lo l : list A} :
    BinList.jump (Pos.of_succ_nat (length lo)) (def :: lo ++ l) = l.
  Proof.
    revert def.
    induction lo; intros def; cbn; [easy|].
    rewrite BinList.jump_succ; cbn.
    rewrite BinList.jump_tl; cbn.
    now apply IHlo.
  Qed.

  Lemma nth_length_prefix {o} {A} {def} {lo l : list A} : o = Pos.of_succ_nat (length lo) -> BinList.nth def o (lo ++ l) = hd def l.
  Proof.
    intros ->.
    change (lo ++ l) with (tl (def ::(lo ++ l))).
    rewrite BinList.nth_jump.
    f_equal.
    now apply jump_of_succ_nat_length.
  Qed.

  Lemma nth_succ {i} {A} {def t} {ts : list A} :
    BinList.nth def (Pos.succ i) (t :: ts) = BinList.nth def i ts.
  Proof.
    change (t :: ts)%list with (tl (def :: t :: ts)).
    rewrite BinList.nth_jump.
    replace ((Pos.succ i)) with (i + 1)%positive by lia.
    rewrite BinList.jump_add.
    cbn.
    now rewrite <-BinList.nth_jump.
  Qed.

  Lemma nth_lookup {i} {A} {def} {ts la : list A} {t} :
      ts !! i = Some t ->
      BinList.nth def (Pos.of_succ_nat i) (ts ++ la) = t.
  Proof.
    revert i.
    induction ts; intros i; first inversion 1.
    destruct i; inversion 1; first easy; cbn.
    rewrite nth_succ.
    now eapply IHts.
  Qed.

  Fixpoint plusNatPos (n : nat) (p : positive) : positive :=
    match n with
    | 0 => p
    | S n => Pos.succ (plusNatPos n p)
    end.

  Lemma plusNatPos_of_succ_nat {n m} : plusNatPos n (Pos.of_succ_nat m) = Pos.of_succ_nat (n + m).
  Proof. induction n; cbn; now f_equal. Qed.
End Util.

Module Type PartialEvaluationOn
  (Import TY : Types)
  (Import TM : TermsOn TY)
  (Import IN : InstantiationOn TY TM).

  Local Notation LCtx := (NCtx LVar Ty).
  Local Notation Valuation Σ := (Env (fun xt : Binding LVar Ty => Val (type xt)) Σ).

  Section WithLCtx.
    Context {Σ : LCtx}.

    #[local] Ltac lsolve :=
      try progress cbn;
      try (progress autorewrite with katamaran);
      try easy;
      auto with core katamaran.

    Class TermRing (σ : Ty) :=
      MkTermRing {
          tmr_zero : Val σ
        ; tmr_one : Val σ
        ; tmr_plus : BinOp σ σ σ
        ; tmr_times : BinOp σ σ σ
        ; tmr_minus : BinOp σ σ σ
        ; tmr_negate : UnOp σ σ
        ; tmr_of_Z : Z -> Val σ
        ; tmr_ring_morph : ring_morph (term_val (Σ := Σ) σ tmr_zero) (term_val σ tmr_one)
                             (term_binop tmr_plus) (term_binop tmr_times) (term_binop tmr_minus)
                             (term_unop tmr_negate) base.equiv 0%Z 1%Z
                             Z.add Z.mul Z.sub Z.opp Zbool.Zeq_bool (λ c : Z, term_val σ (tmr_of_Z c))
        ; tmr_ring_theory : ring_theory (term_val (Σ := Σ) σ tmr_zero) (term_val σ tmr_one) (term_binop tmr_plus) (term_binop tmr_times) (term_binop tmr_minus) (term_unop tmr_negate) base.equiv
        ; tmr_ring_eq_ext : ring_eq_ext (term_binop (Σ := Σ) tmr_plus) (term_binop tmr_times) (term_unop tmr_negate) base.equiv
        }.

    #[program,export] Instance TermRing_int : TermRing ty.int := {
        tmr_zero := 0%Z
      ; tmr_one := 1%Z
      ; tmr_plus := bop.plus
      ; tmr_times := bop.times
      ; tmr_minus := bop.minus
      ; tmr_negate := uop.neg
      ; tmr_of_Z := id
      ; tmr_ring_theory := Term_int_ring_theory
      ; tmr_ring_eq_ext := Term_int_ring_eq_ext
      }.
    Next Obligation.
      constructor; try reflexivity; intros;
        rewrite ?term_binop_val, ?term_unop_val; try reflexivity.
      now apply Zbool.Zeq_bool_eq in H.
    Qed.

    #[program, export] Instance TermRing_bv {n} : TermRing (ty.bvec n) := {
        tmr_zero := bv.zero
      ; tmr_one := bv.one
      ; tmr_plus := bop.bvadd
      ; tmr_times := bop.bvmul
      ; tmr_minus := bop.bvsub
      ; tmr_negate := uop.negate
      ; tmr_of_Z := bv.of_Z
      ; tmr_ring_theory := Term_bv_ring_theory Σ n
      ; tmr_ring_eq_ext := Term_bv_ring_eq_ext Σ n
      }.
    Next Obligation.
      constructor; try reflexivity; rewrite ?term_binop_val, ?term_unop_val; intros.
      - now rewrite bv.of_Z_one.
      - rewrite term_binop_val; cbn; now rewrite bv.of_Z_add.
      - rewrite term_binop_val; cbn; now rewrite bv.of_Z_sub.
      - rewrite term_binop_val; cbn; now rewrite bv.of_Z_mul.
      - rewrite term_unop_val; cbn; now rewrite bv.of_Z_negate.
      - apply Zbool.Zeq_bool_eq in H; now subst.
    Qed.

    Definition evalPolTm `{TermRing σ} : list (Term Σ σ) -> Pol Z -> Term Σ σ :=
      Pphi_dev (term_val σ tmr_zero)
        (term_val σ tmr_one)
        (term_binop tmr_plus)
        (term_binop tmr_times)
        (term_binop tmr_minus)
        (term_unop tmr_negate)
        0%Z 1%Z Zbool.Zeq_bool
        (fun c => term_val σ (tmr_of_Z c))
        get_signZ.

    Definition evalPExprTm `{TermRing σ} : list (Term Σ σ) -> PExpr Z -> Term Σ σ :=
      PEeval (term_val σ tmr_zero)
        (term_val σ tmr_one)
        (term_binop tmr_plus)
        (term_binop tmr_times)
        (term_binop tmr_minus)
        (term_unop tmr_negate)
        (fun c => term_val σ (tmr_of_Z c))
        id_phi_N (pow_N (term_val (Σ := Σ) σ tmr_one) (term_binop tmr_times)).

    Lemma evalPol_norm_aux `{tmr : TermRing σ} {p : PExpr Z} (l : list (Term Σ σ)) :
      evalPolTm l (norm_aux 0%Z 1%Z Z.add Z.mul Z.sub Z.opp Zbool.Zeq_bool p) ≡ evalPExprTm l p.
    Proof.
      unfold evalPolTm, evalPExprTm.
      rewrite Pphi_dev_ok;
        rewrite ?bv.of_N_one;
        try eauto using tmr_ring_eq_ext, Rth_ARth, tmr_ring_theory, tmr_ring_morph, get_signZ_th with typeclass_instances.
      rewrite norm_aux_spec;
        rewrite ?bv.of_N_one; try eauto using tmr_ring_eq_ext, Rth_ARth, tmr_ring_theory, tmr_ring_morph, get_signZ_th, pow_N_th with typeclass_instances.
    Qed.

    Definition RQuote (σ : Ty) : Type := list (Term Σ σ) -> positive -> PExpr Z * list (Term Σ σ).

    Definition RQuoteValid `{TermRing σ} (t : Term Σ σ) (q : RQuote σ): Prop :=
      forall lo o, match q lo o with
                     (poly , ln) => o = Pos.of_succ_nat (length lo) -> forall la, evalPExprTm (lo ++ ln ++ la) poly ≡ t
                  end.

    Definition Term_Quote_def {σ} (t : Term Σ σ) : RQuote σ :=
      fun ts o =>
        match find_index (fun t' => Term_eqb t t') ts with
        | None => (PEX Z o , [ t ]%list)
        | Some i => (PEX Z (Pos.of_succ_nat i) , []%list)
        end.

    Lemma Term_Quote_def_Valid `{TermRing σ} {t : Term Σ σ} : RQuoteValid t (Term_Quote_def t).
    Proof.
      intros ts o.
      unfold Term_Quote_def.
      destruct (find_index_spec (fun t' => Term_eqb t t') ts) as [i Hlkpi|];
        intros Ho la; cbn.
      - rewrite (nth_lookup (t := t)); first reflexivity.
        destruct Hlkpi as [a Ha].
        destruct (Term_eqb_spec t a); inversion Ha; now subst.
      - now rewrite nth_length_prefix.
    Qed.

    Definition Term_Quote_unop {n} (comb : PExpr Z -> PExpr Z) (q1 : RQuote n) : RQuote n :=
      fun ts o => let (pol1 , ts1) := q1 ts o in
                  (comb pol1 , ts1).

    Lemma Term_Quote_unop_Valid `{TermRing σ} {op : UnOp σ σ}
      {comb} {t1} {q1} :
      (forall env pol1, evalPExprTm env (comb pol1) = term_unop op (evalPExprTm env pol1)) ->
      RQuoteValid t1 q1 ->
      RQuoteValid (term_unop op t1) (Term_Quote_unop comb q1).
    Proof.
      intros Hcomb Hq1 ts o; unfold Term_Quote_unop; cbn.
      generalize (Hq1 ts o); destruct q1 as [pol1 l1].
      intros.
      now rewrite Hcomb, H0.
    Qed.

    Definition Term_Quote_bin `{TermRing σ} (comb : PExpr Z -> PExpr Z -> PExpr Z) (q1 : RQuote σ) (q2 : RQuote σ) : RQuote σ :=
      fun ts o => let (pol1 , ts1) := q1 ts o in
                  let (pol2 , ts2) := q2 (app ts ts1) (plusNatPos (length ts1) o) in
                  ((comb pol1 pol2) , app ts1 ts2).

    Lemma Term_Quote_bin_Valid `{TermRing σ} {op : BinOp σ σ σ}
      {comb} {t1 t2} {q1 q2} :
      (forall env pol1 pol2, evalPExprTm env (comb pol1 pol2) = term_binop op (evalPExprTm env pol1) (evalPExprTm env pol2)) ->
      RQuoteValid t1 q1 -> RQuoteValid t2 q2 ->
      RQuoteValid (term_binop op t1 t2) (Term_Quote_bin comb q1 q2).
    Proof.
      intros Hcomb Hq1 Hq2 ts o; unfold Term_Quote_bin; cbn.
      generalize (Hq1 ts o); destruct q1 as [pol1 l1].
      intros Hl1.
      generalize (Hq2 (ts ++ l1) (plusNatPos (length l1) o)); destruct q2 as [pol2 l2].
      intros Hl2 Ho l3.
      rewrite Hcomb.
      eapply proper_term_binop.
      - now rewrite <-List.app_assoc, (Hl1 Ho _).
      - rewrite !List.app_assoc, <-List.app_assoc.
        apply Hl2.
        subst.
        now rewrite plusNatPos_of_succ_nat, app_length, Nat.add_comm.
    Qed.

    Definition CanonTerm σ : Type :=
      match σ with
      | ty.bvec n => RQuote σ
      | ty.int => RQuote σ
      | _ => Term Σ σ
      end.

    Definition CanonTerm_to_Term {σ} : CanonTerm σ -> Term Σ σ :=
      match σ return CanonTerm σ -> Term Σ σ with
      | ty.bvec n => fun ct =>
                       match ct nil 1%positive with
                       | (pexpr , env) =>
                           evalPolTm (H := TermRing_bv) env (norm_aux 0%Z 1%Z Z.add Z.mul Z.sub Z.opp Zbool.Zeq_bool pexpr)
                       end
      | ty.int => fun ct =>
                    match ct nil 1%positive with
                    | (pexpr , env) =>
                        evalPolTm env (norm_aux 0%Z 1%Z Z.add Z.mul Z.sub Z.opp Zbool.Zeq_bool pexpr)
                    end
      | _σ => fun t => t
      end.

    #[export] Instance equiv_CanonTerm {σ} : base.Equiv (CanonTerm σ)
      := match σ with
         | ty.bvec n => (eq ==> eq ==> base.prod_relation eq base.equiv)%signature
         | ty.int => (eq ==> eq ==> base.prod_relation eq base.equiv)%signature
         | _ => base.equiv
         end.

    Definition CanonTermRep {σ : Ty} : CanonTerm σ -> Term Σ σ -> Prop :=
      match σ with
      | ty.bvec n => fun ct t => RQuoteValid t ct
      | ty.int => fun ct t => RQuoteValid t ct
      | _ => fun ct t => ct ≡ t
      end.

    #[export] Instance proper_tl_equiv `{base.Equiv A} :
      Proper (base.equiv ==> base.equiv) (@tl A).
    Proof. intros l1 l2 Hl. destruct Hl; cbn; [constructor|easy]. Qed.

    #[export] Instance proper_hd_equiv {A} {_ : base.Equiv A} :
      Proper (base.equiv ==> base.equiv ==> base.equiv) (@hd A).
    Proof. intros def1 def2 Hdef l1 l2 Hl. now destruct Hl. Qed.

    #[export] Instance proper_jump_equiv `{base.Equiv A} :
      Proper (eq ==> base.equiv ==> base.equiv) (@BinList.jump A).
    Proof.
      intros p ? <-.
      induction p; cbn;
        intros l1 l2 Hl;
        try do 2 apply IHp;
        now try apply proper_tl_equiv.
    Qed.

    Lemma proper_pow_pos `{base.Equiv A} :
      Proper ((base.equiv ==> base.equiv ==> base.equiv) ==> base.equiv ==> eq ==> base.equiv) (@pow_pos A).
    Proof.
      intros m1 m2 Hm x1 x2 Hx n ? <-.
      revert m1 m2 Hm x1 x2 Hx.
      induction n; cbn.
      - intros m1 m2 Hm x1 x2 Hx.
        apply Hm; [easy|].
        apply Hm; now apply IHn.
      - intros m1 m2 Hm x1 x2 Hx.
        apply Hm; now apply IHn.
      - now intros.
    Qed.

    Lemma proper_pow_N `{base.Equiv A} :
      Proper (base.equiv ==> (base.equiv ==> base.equiv ==> base.equiv) ==> base.equiv ==> eq ==> base.equiv) (@pow_N A).
    Proof.
      intros o1 o2 Ho m1 m2 Hm x1 x2 Hx n ? <-.
      revert o1 o2 Ho m1 m2 Hm x1 x2 Hx.
      destruct n; cbn.
      - now intros.
      - intros o1 o2 Ho m1 m2 Hm x1 x2 Hx.
        now apply proper_pow_pos.
    Qed.

    #[export] Instance proper_nth_equiv `{base.Equiv A} :
      Proper (base.equiv ==> eq ==> base.equiv ==> base.equiv) (@BinList.nth A).
    Proof.
      intros def1 def2 Hdef x ? <-.
      induction x; intros l1 l2 Hl; cbn.
      - apply IHx, proper_jump_equiv; first easy.
        now apply proper_tl_equiv.
      - now apply IHx, proper_jump_equiv.
      - now apply proper_hd_equiv.
    Qed.

    #[export] Instance proper_evalPExprTm `{TermRing σ} :
      Proper (base.equiv ==> eq ==> base.equiv) (evalPExprTm (σ := σ)).
    Proof.
      intros env1 env2 Henv expr ? <-.
      induction expr; cbn; try easy.
      - now rewrite Henv.
      - now rewrite IHexpr1, IHexpr2.
      - now rewrite IHexpr1, IHexpr2.
      - now rewrite IHexpr1, IHexpr2.
      - now rewrite IHexpr.
      - apply proper_pow_N; try easy.
        apply proper_term_binop.
    Qed.

    Instance proper_CanonTermRep `{TermRing σ} : Proper (base.equiv ==> base.equiv ==> iff) (@CanonTermRep σ).
    Proof.
      intros x1 x2 Hx y1 y2 Hy.
      destruct σ; cbn; try now rewrite Hx, Hy;
        cbn.
      - split; intros Hrqv lo o; specialize (Hrqv lo o); specialize (Hx lo _ eq_refl o _ eq_refl);
        destruct (x1 lo o), (x2 lo o), Hx; cbn in *; subst.
        + intros -> la.
          rewrite <-Hy, <-H1.
          now apply Hrqv.
        + intros -> la.
          rewrite Hy, H1.
          now apply Hrqv.
      - split; intros Hrqv lo o; specialize (Hrqv lo o); specialize (Hx lo _ eq_refl o _ eq_refl);
        destruct (x1 lo o), (x2 lo o), Hx; cbn in *; subst.
        + intros -> la.
          rewrite <-Hy, <-H1.
          now apply Hrqv.
        + intros -> la.
          rewrite Hy, H1.
          now apply Hrqv.
    Qed.

    Lemma CanonTermRep_adeq {σ : Ty} {ct : CanonTerm σ} {t} : CanonTermRep ct t -> CanonTerm_to_Term ct ≡ t.
    Proof.
      destruct σ; intros; cbn; try trivial;
        specialize (H []%list 1%positive);
        destruct (ct []%list 1%positive);
        rewrite evalPol_norm_aux;
        now rewrite <-(H eq_refl nil), app_nil_r.
    Qed.

    Lemma Term_Quote_bin_sound {n} {op : BinOp (ty.bvec n) (ty.bvec n) (ty.bvec n)}
      {comb} {ct1 t1 ct2 t2} :
      (forall env pol1 pol2, evalPExprTm env (comb pol1 pol2) = term_binop op (evalPExprTm env pol1) (evalPExprTm env pol2)) ->
      CanonTermRep (σ := ty.bvec n) ct1 t1 ->
      CanonTermRep (σ := ty.bvec n) ct2 t2 ->
      CanonTermRep (σ := ty.bvec n) (Term_Quote_bin comb ct1 ct2) (term_binop op t1 t2).
    Proof.
      intros Hcomb.
      now eapply Term_Quote_bin_Valid.
    Qed.

    Equations(noeqns) peval_append {σ} (t1 t2 : Term Σ (ty.list σ)) : Term Σ (ty.list σ) :=
    | term_val _ v1                 | term_val _ v2 := term_val (ty.list σ) (app v1 v2);
    (* TODO: recurse over the value instead *)
    | term_val _ nil                | t2 := t2;
    | term_val _ (cons v vs)        | t2 := term_binop bop.cons (term_val σ v) (term_binop bop.append (term_val (ty.list σ) vs) t2);
    | term_binop bop.cons t11 t12 | t2 := term_binop bop.cons t11 (term_binop bop.append t12 t2);
    | t1                            | t2 := term_binop bop.append t1 t2.

    Equations(noeqns) peval_or (t1 t2 : Term Σ ty.bool) : Term Σ ty.bool :=
    | term_val _ true  , t2               => term_val ty.bool true
    | term_val _ false , t2               => t2
    | t1               , term_val _ true  => term_val ty.bool true
    | t1               , term_val _ false => t1
    | t1               , t2               => term_binop bop.or t1 t2.

    Equations peval_plus (t1 t2 : Term Σ ty.int) : Term Σ ty.int :=
    | term_val _ v1  , term_val _ v2    => term_val ty.int (v1 + v2)%Z
    | term_val _ 0%Z , t2               => t2
    | t1             , term_val _ 0%Z   => t1
    | t1             , term_val _ v2    => term_binop bop.plus (term_val ty.int v2) t1
    | t1             , t2               => term_binop bop.plus t1 t2.

    Equations peval_bvadd {n} (t1 t2 : Term Σ (ty.bvec n)) : Term Σ (ty.bvec n) :=
    | term_val _ v1          , term_val _ v2          => term_val (ty.bvec n) (bv.add v1 v2)
    | term_val _ (bv.mk 0 _) , t2                     => t2
    | t1                     , term_val _ (bv.mk 0 _) => t1
    | t1                     , term_val _ v2          => term_binop bop.bvadd (term_val (ty.bvec n) v2) t1
    | t1                     , t2                     => term_binop bop.bvadd t1 t2.

    Equations(noeqns) peval_binop' {σ1 σ2 σ} (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) : Term Σ σ :=
    | op | term_val _ v1 | term_val _ v2 := term_val σ (bop.eval op v1 v2);
    | op | t1            | t2            := term_binop op t1 t2.

    Equations(noeqns) peval_binop {σ1 σ2 σ} (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) : Term Σ σ :=
    | bop.append , t1 , t2 => peval_append t1 t2
    | bop.or     , t1 , t2 => peval_or t1 t2
    | bop.plus   , t1 , t2 => peval_plus t1 t2
    | bop.bvadd  , t1 , t2 => peval_bvadd t1 t2
    | op         , t1 , t2 => peval_binop' op t1 t2.

    Lemma peval_append_sound {σ} (t1 t2 : Term Σ (ty.list σ)) :
      peval_append t1 t2 ≡ term_binop bop.append t1 t2.
    Proof.
      depelim t1.
      - reflexivity.
      - depelim t2; cbn.
        + now destruct v.
        + now constructor.
        + now destruct v.
        + depelim op.
      - now depelim op.
      - now depelim op.
    Qed.

    Lemma peval_or_sound (t1 t2 : Term Σ ty.bool) :
      peval_or t1 t2 ≡ term_binop bop.or t1 t2.
    Proof with lsolve.
      depelim t1.
      - depelim t2... destruct v...
      - now destruct v.
      - depelim t2... destruct v...
      - depelim t2... destruct v...
    Qed.

    Lemma peval_plus_sound (t1 t2 : Term Σ ty.int) :
      peval_plus t1 t2 ≡ term_binop bop.plus t1 t2.
    Proof. funelim (peval_plus t1 t2); lsolve; intros ι; cbn; lia. Qed.

    Lemma peval_bvadd_sound {n} (t1 t2 : Term Σ (ty.bvec n)) :
      peval_bvadd t1 t2 ≡ term_binop bop.bvadd t1 t2.
    Proof.
      funelim (peval_bvadd t1 t2); lsolve; intros ι; cbn; auto;
        first
          [ symmetry; apply bv.add_zero_l
          | symmetry; apply bv.add_zero_r
          | now apply bv.add_comm
          ].
    Qed.

    Lemma peval_binop'_sound {σ1 σ2 σ} (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) :
      peval_binop' op t1 t2 ≡ term_binop op t1 t2.
    Proof.
      unfold peval_binop'.
      now repeat
        match goal with
        | |- context[match ?t with _ => _ end] => destruct t
        end.
    Qed.

    Lemma peval_binop_sound {σ1 σ2 σ} (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) :
      peval_binop op t1 t2 ≡ term_binop op t1 t2.
    Proof.
      destruct op; cbn [peval_binop];
        auto using peval_binop'_sound, peval_append_sound, peval_or_sound,
                 peval_plus_sound, peval_bvadd_sound.
    Qed.


    Equations peval_not (t : Term Σ ty.bool) : Term Σ ty.bool :=
    | term_val _ v                    => term_val ty.bool (negb v)
    | term_binop bop.and t1 t2        => term_binop bop.or (peval_not t1) (peval_not t2)
    | term_binop bop.or t1 t2         => term_binop bop.and (peval_not t1) (peval_not t2)
    | term_binop (bop.relop op) t1 t2 => term_relop_neg op t1 t2
    | t                               => term_unop uop.not t.

    #[local] Open Scope lazy_bool_scope.

    Definition peval_vector_subrange_update_vector_subrange {n}
      start len {p : IsTrue (start + len <=? n)}
      start_u len_u {p_u : IsTrue (start_u + len_u <=? n)}
      (xs : Term Σ (ty.bvec n)) (ys : Term Σ (ty.bvec len_u)) :
      Term Σ (ty.bvec len) :=
      match
        match eq_dec start start_u , eq_dec len len_u with
        | left e1 , left e2 => Some (e1 , e2)
        | _       , _      => None
        end
      with
      | Some (_,e) =>
          (* SAME *)
          eq_rect_r (fun l => Term Σ (ty.bvec l)) ys e
      | None =>
          if (* BEFORE *) (start + len <=? start_u) |||
             (* AFTER *) (start_u + len_u <=? start)
          then term_vector_subrange start len xs
          else term_vector_subrange start len
                  (term_binop (bop.update_vector_subrange start_u len_u) xs ys)
      end.
    #[global] Arguments peval_vector_subrange_update_vector_subrange {n}
      start len {p} start_u len_u {p_u} xs ys.

    Equations peval_vector_subrange {n} start len {p : IsTrue (start + len <=? n)}
      (t : Term Σ (ty.bvec n)) : Term Σ (ty.bvec len) :=
    | start , len , term_val _ v                    =>
        term_val (ty.bvec len) (bv.vector_subrange start len v)
    | start , len , term_binop (bop.update_vector_subrange start_u len_u) t1 t2 =>
        peval_vector_subrange_update_vector_subrange start len start_u len_u t1 t2
    | start , len , t => term_vector_subrange start len t.

    Definition peval_unop' {σ1 σ2} (op : UnOp σ1 σ2) (t : Term Σ σ1) : Term Σ σ2 :=
      match term_get_val t with
      | Some v => term_val σ2 (uop.eval op v)
      | None   => term_unop op t
      end.

    Definition peval_unop {σ1 σ2} (op : UnOp σ1 σ2) : Term Σ σ1 -> Term Σ σ2 :=
      match op with
      | uop.not                       => peval_not
      | uop.vector_subrange start len => peval_vector_subrange start len
      | op                            => peval_unop' op
      end.

    Lemma peval_not_sound (t : Term Σ ty.bool) :
      peval_not t ≡ term_unop uop.not t.
    Proof. funelim (peval_not t); lsolve; now apply proper_term_binop. Qed.

    Lemma peval_unop'_sound {σ1 σ2} (op : UnOp σ1 σ2) (t : Term Σ σ1) :
      peval_unop' op t ≡ term_unop op t.
    Proof. unfold peval_unop'; destruct (term_get_val_spec t); subst; easy. Qed.

    Lemma peval_vector_subrange_update_vector_subrange_sound
      {n} start len len_u start_u {p : IsTrue (start + len <=? n)}
      {p_u : IsTrue (start_u + len_u <=? n)} (t1 : Term Σ (ty.bvec n))
      (t2 : Term Σ (ty.bvec len_u)) :
        peval_vector_subrange_update_vector_subrange start len start_u len_u t1 t2 ≡
        term_vector_subrange start len
          (term_binop (bop.update_vector_subrange start_u len_u) t1 t2).
    Proof.
      unfold peval_vector_subrange_update_vector_subrange.
      destruct (if eq_dec start start_u then _ else _) as [[e1 e2]|].
      { (* SAME *)
        intros ι; subst; cbn. destruct (IsTrue.proof_irrelevance p p_u).
        now rewrite bv.subrange_same_update_vector_subrange. }
      destruct (start + len <=? start_u) eqn:e.
      { (* BEFORE *)
        intros ι; cbn.
        rewrite bv.subrange_before_update_vector_subrange.
        easy. now rewrite e. }
      clear e. destruct (start_u + len_u <=? start) eqn:e.
      { (* AFTER *)
        intros ι; cbn.
        rewrite bv.subrange_after_update_vector_subrange.
        easy. now rewrite e. }
      reflexivity.
    Qed.

    Lemma peval_vector_subrange_sound {n} start len {p : IsTrue (start + len <=? n)}
      (t : Term Σ (ty.bvec n)) :
      peval_vector_subrange start len t ≡ term_vector_subrange start len t.
    Proof.
      funelim (peval_vector_subrange start len t); lsolve.
      apply peval_vector_subrange_update_vector_subrange_sound.
    Qed.

    Lemma peval_unop_sound {σ1 σ2} (op : UnOp σ1 σ2) (t : Term Σ σ1) :
      peval_unop op t ≡ term_unop op t.
    Proof.
      destruct op; cbn [peval_unop];
        auto using peval_unop'_sound, peval_not_sound,
                 peval_vector_subrange_sound.
    Qed.

    Definition peval_union {U K} (t : Term Σ (unionk_ty U K)) : Term Σ (ty.union U) :=
      match term_get_val t with
      | Some v => term_val (ty.union U) (unionv_fold U (existT K v))
      | None   => term_union U K t
      end.

    Lemma peval_union_sound {U K} (t : Term Σ (unionk_ty U K)) :
      peval_union t ≡ term_union U K t.
    Proof. unfold peval_union. destruct (term_get_val_spec t); now subst. Qed.

    Import option.notations.
    Fixpoint peval_record' {rfs : NCtx recordf Ty} (ts : NamedEnv (Term Σ) rfs) {struct ts} : option (NamedEnv Val rfs) :=
      match ts with
      | env.nil         => Some [env]
      | env.snoc ts _ t => vs <- peval_record' ts ;;
                           v  <- term_get_val t ;;
                           Some (env.snoc vs _ v)
      end.

    Definition peval_record R (ts : NamedEnv (Term Σ) (recordf_ty R)) : Term Σ (ty.record R) :=
      match peval_record' ts with
      | Some a => term_val (ty.record R) (recordv_fold R a)
      | None => term_record R ts
      end.

    Lemma peval_record'_sound {rfs : NCtx recordf Ty} (ts : NamedEnv (Term Σ) rfs) :
      option.wlp (fun vs => forall ι, inst ts ι = vs) (peval_record' ts).
    Proof.
      induction ts; cbn.
      - now constructor.
      - rewrite option.wlp_bind. revert IHts.
        apply option.wlp_monotonic. intros vs IHvs.
        rewrite option.wlp_bind. generalize (term_get_val_spec db).
        apply option.wlp_monotonic. intros v IHv. constructor.
        intros ι. specialize (IHvs ι). subst. reflexivity.
    Qed.

    Lemma peval_record_sound {R} ts :
      peval_record R ts ≡ term_record R ts.
    Proof.
      unfold peval_record. destruct (peval_record'_sound ts); [|reflexivity].
      intros ι; cbn. now f_equal.
    Qed.

    Definition CanonTerm_def {σ : Ty} : Term Σ σ -> CanonTerm σ :=
      match σ with
      | ty.bvec n => Term_Quote_def
      | ty.int => Term_Quote_def
      | _ => fun t => t
      end.

    Lemma CanonTerm_def_sound {σ : Ty} {t : Term Σ σ} :
      CanonTermRep (CanonTerm_def t) t.
    Proof.
      destruct σ; try reflexivity;
      apply Term_Quote_def_Valid.
    Qed.

    Definition peval2_val {σ : Ty} : Val σ -> CanonTerm σ :=
      match σ with
      | ty.bvec n => fun v l p => (PEc (bv.unsigned v) , nil)
      | ty.int => fun v l p => (PEc v , nil)
      | _ => term_val _
      end.

    Lemma peval2_val_sound {σ : Ty} {v : Val σ} : CanonTermRep (peval2_val v) (term_val _ v).
    Proof. destruct σ; try reflexivity;
           intros lo ? -> la; cbn; try reflexivity.
           now rewrite bv.of_Z_unsigned.
    Qed.

    Definition peval2_binop {σ1 σ2 σ3 : Ty} (op : BinOp σ1 σ2 σ3) :
      CanonTerm σ1 -> CanonTerm σ2 -> CanonTerm σ3 :=
      match op in BinOp σ1 σ2 σ3 return CanonTerm σ1 -> CanonTerm σ2 -> CanonTerm σ3 with
      | bop.plus => Term_Quote_bin (@PEadd _)
      | bop.minus => Term_Quote_bin (@PEsub _)
      | bop.times => Term_Quote_bin (@PEmul _)
      | bop.land => fun t1 t2 => CanonTerm_def (peval_binop bop.land (CanonTerm_to_Term t1) (CanonTerm_to_Term t2))
      | bop.and => peval_binop bop.and
      | bop.or => peval_binop bop.or
      | bop.pair => fun t1 t2 => peval_binop bop.pair (CanonTerm_to_Term t1) (CanonTerm_to_Term t2)
      | bop.cons => fun t1 t2 => peval_binop bop.cons (CanonTerm_to_Term t1) t2
      | bop.append => fun t1 t2 => peval_binop bop.append t1 t2
      | bop.shiftr => fun t1 t2 => CanonTerm_def (peval_binop bop.shiftr (CanonTerm_to_Term t1) (CanonTerm_to_Term t2))
      | bop.shiftl => fun t1 t2 => CanonTerm_def (peval_binop bop.shiftl (CanonTerm_to_Term t1) (CanonTerm_to_Term t2))
      | bop.bvadd => Term_Quote_bin (@PEadd _)
      | bop.bvsub => Term_Quote_bin (@PEsub _)
      | bop.bvmul => Term_Quote_bin (@PEmul _)
      | bop.bvand => fun t1 t2 => CanonTerm_def (peval_binop bop.bvand (CanonTerm_to_Term t1) (CanonTerm_to_Term t2))
      | bop.bvor => fun t1 t2 => CanonTerm_def (peval_binop bop.bvor (CanonTerm_to_Term t1) (CanonTerm_to_Term t2))
      | bop.bvxor => fun t1 t2 => CanonTerm_def (peval_binop bop.bvxor (CanonTerm_to_Term t1) (CanonTerm_to_Term t2))
      | bop.bvapp => fun t1 t2 => CanonTerm_def (peval_binop bop.bvapp (CanonTerm_to_Term t1) (CanonTerm_to_Term t2))
      | bop.bvcons => fun t1 t2 => CanonTerm_def (peval_binop bop.bvcons t1 (CanonTerm_to_Term t2))
      | (bop.update_vector_subrange s l) => fun t1 t2 => CanonTerm_def (peval_binop (bop.update_vector_subrange s l) (CanonTerm_to_Term t1) (CanonTerm_to_Term t2))
      | bop.relop rop => fun t1 t2 => peval_binop (bop.relop rop) (CanonTerm_to_Term t1) (CanonTerm_to_Term t2)
      end.

    Lemma peval2_binop_sound {σ1 σ2 σ3 : Ty} {op : BinOp σ1 σ2 σ3}
      {ct1 : CanonTerm σ1} {t1} {ct2 : CanonTerm σ2} {t2} :
      CanonTermRep ct1 t1 ->
      CanonTermRep ct2 t2 ->
      CanonTermRep (peval2_binop op ct1 ct2) (term_binop op t1 t2).
    Proof.
      destruct op; intros H1 H2; cbn [peval2_binop].
      - now eapply Term_Quote_bin_Valid.
      - now eapply Term_Quote_bin_Valid.
      - now eapply Term_Quote_bin_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2), <-peval_binop_sound.
        now eapply Term_Quote_def_Valid.
      - now rewrite peval_binop_sound, H1, H2.
      - now rewrite peval_binop_sound, <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2).
      - now rewrite peval_binop_sound, <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2).
      - now rewrite peval_binop_sound, <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2).
      - now rewrite peval_binop_sound, <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2).
      - rewrite <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2), <-peval_binop_sound.
        now eapply Term_Quote_def_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2), <-peval_binop_sound.
        now eapply Term_Quote_def_Valid.
      - now eapply Term_Quote_bin_Valid.
      - now eapply Term_Quote_bin_Valid.
      - now eapply Term_Quote_bin_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2), <-peval_binop_sound.
        now eapply Term_Quote_def_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2), <-peval_binop_sound.
        now eapply Term_Quote_def_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2), <-peval_binop_sound.
        now eapply Term_Quote_def_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2), <-peval_binop_sound.
        now eapply Term_Quote_def_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2), <-peval_binop_sound.
        now eapply Term_Quote_def_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2), <-peval_binop_sound.
        now eapply Term_Quote_def_Valid.
      - now rewrite <-(CanonTermRep_adeq H1), <-(CanonTermRep_adeq H2), peval_binop_sound.
    Qed.

    Definition peval2_unop {σ1 σ2 : Ty} (op : UnOp σ1 σ2) :
      CanonTerm σ1 -> CanonTerm σ2 :=
      match op in UnOp σ1 σ2 return CanonTerm σ1 -> CanonTerm σ2 with
      | uop.inl => fun t1 => peval_unop uop.inl (CanonTerm_to_Term t1)
      | uop.inr => fun t1 => peval_unop uop.inr (CanonTerm_to_Term t1)
      | uop.neg => Term_Quote_unop (@PEopp _)
      | uop.not => peval_unop uop.not
      | uop.sext => fun t1 => CanonTerm_def (peval_unop uop.sext (CanonTerm_to_Term t1))
      | uop.zext => fun t1 => CanonTerm_def (peval_unop uop.zext (CanonTerm_to_Term t1))
      | uop.get_slice_int => fun t1 => CanonTerm_def (peval_unop uop.get_slice_int (CanonTerm_to_Term t1))
      | uop.signed => fun t1 => CanonTerm_def (peval_unop uop.signed (CanonTerm_to_Term t1))
      | uop.unsigned => fun t1 => CanonTerm_def (peval_unop uop.unsigned (CanonTerm_to_Term t1))
      | uop.truncate m => fun t1 => CanonTerm_def (peval_unop (uop.truncate m) (CanonTerm_to_Term t1))
      | uop.vector_subrange s l => fun t1 => CanonTerm_def (peval_unop (uop.vector_subrange s l) (CanonTerm_to_Term t1))
      | uop.bvnot => fun t1 => CanonTerm_def (peval_unop uop.bvnot (CanonTerm_to_Term t1))
      | uop.bvdrop m => fun t1 => CanonTerm_def (peval_unop (uop.bvdrop m) (CanonTerm_to_Term t1))
      | uop.bvtake m => fun t1 => CanonTerm_def (peval_unop (uop.bvtake m) (CanonTerm_to_Term t1))
      | uop.negate => Term_Quote_unop (@PEopp _)
      end.

    Lemma peval2_unop_sound {σ1 σ2 : Ty} {op : UnOp σ1 σ2}
      {ct1 : CanonTerm σ1} {t1} :
      CanonTermRep ct1 t1 ->
      CanonTermRep (peval2_unop op ct1) (term_unop op t1).
    Proof.
      destruct op; intros H1; cbn [peval2_unop].
      - now rewrite peval_unop_sound, <-(CanonTermRep_adeq H1).
      - now rewrite peval_unop_sound, <-(CanonTermRep_adeq H1).
      - now eapply Term_Quote_unop_Valid.
      - now rewrite peval_unop_sound, <-(CanonTermRep_adeq H1).
      - rewrite <-(CanonTermRep_adeq H1), <-peval_unop_sound.
        eapply Term_Quote_def_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-peval_unop_sound.
        eapply Term_Quote_def_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-peval_unop_sound.
        eapply Term_Quote_def_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-peval_unop_sound.
        eapply Term_Quote_def_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-peval_unop_sound.
        eapply Term_Quote_def_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-peval_unop_sound.
        eapply Term_Quote_def_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-peval_unop_sound.
        eapply Term_Quote_def_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-peval_unop_sound.
        eapply Term_Quote_def_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-peval_unop_sound.
        eapply Term_Quote_def_Valid.
      - rewrite <-(CanonTermRep_adeq H1), <-peval_unop_sound.
        eapply Term_Quote_def_Valid.
      - now eapply Term_Quote_unop_Valid.
    Qed.

    Fixpoint peval2 [σ] (t : Term Σ σ) : CanonTerm σ :=
      match t with
      | term_var ς                 => CanonTerm_def (term_var ς)
      | term_val _ v               => peval2_val v
      | term_binop op t1 t2        => peval2_binop op (peval2 t1) (peval2 t2)
      | term_unop op t             => peval2_unop op (peval2 t)
      | term_tuple ts              => term_tuple (env.map (fun b t => CanonTerm_to_Term (peval2 t)) ts)
      | term_union U K t           => peval_union (CanonTerm_to_Term (peval2 t))
      | term_record R ts           => peval_record R (env.map (fun b t => CanonTerm_to_Term (peval2 t)) ts)
      end.

    Lemma peval2_sound [σ] (t : Term Σ σ) :
      CanonTermRep (peval2 t) t.
    Proof.
      induction t; cbn.
      - now eapply CanonTerm_def_sound.
      - eapply peval2_val_sound.
      - now eapply peval2_binop_sound.
      - now eapply peval2_unop_sound.
      - apply proper_term_tuple.
        induction IH; [reflexivity|]; cbn.
        apply proper_env_snoc; first trivial.
        now apply CanonTermRep_adeq.
      - etransitivity; [apply peval_union_sound|apply proper_term_union].
        now apply CanonTermRep_adeq.
      - rewrite peval_record_sound.
        apply proper_term_record.
        induction IH; cbn; [reflexivity|].
        apply proper_namedenv_snoc; first trivial.
        now apply CanonTermRep_adeq.
    Qed.


    Definition peval [σ] (t : Term Σ σ) : Term Σ σ := CanonTerm_to_Term (peval2 t).

    Lemma peval_sound [σ] (t : Term Σ σ) :
      peval t ≡ t.
    Proof.
      eapply CanonTermRep_adeq.
      eapply peval2_sound.
    Qed.
    #[global] Arguments peval [σ] t : simpl never.

    Definition pevals [Δ] : Env (Term Σ) Δ -> Env (Term Σ) Δ :=
      env.map (fun σ  t => peval t).

    Lemma pevals_sound [Δ] (ts : Env (Term Σ) Δ) :
      pevals ts ≡ ts.
    Proof.
      induction ts; [reflexivity|]; cbn.
      apply proper_env_snoc; auto using peval_sound.
    Qed.

  End WithLCtx.
End PartialEvaluationOn.

(* Local Variables: *)
(* proof-omit-proofs-option: t *)
(* End: *)
