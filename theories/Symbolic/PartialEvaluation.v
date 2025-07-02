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
     Logic.Eqdep_dec
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

    Definition CanonTerm σ : Type :=
      match σ with
      | ty.bvec n => Pol Z * list (Term Σ (ty.bvec n))
      (* | ty.int => PExpr Z * list (Term Σ ty.int) *)
      | _ => Term Σ σ
      end.

    Definition evalPolTmBv {n} : list (Term Σ (ty.bvec n)) -> Pol Z -> Term Σ (ty.bvec n) :=
      Pphi_dev (term_val (Σ := Σ) (ty.bvec n) bv.zero)
        (term_val (Σ := Σ) (ty.bvec n) (bv.of_N 1))
        (term_binop bop.bvadd)
        (term_binop bop.bvmul)
        (term_binop bop.bvsub)
        (term_unop uop.negate)
        0%Z 1%Z Zbool.Zeq_bool
        (fun c => term_val (ty.bvec n) (bv.of_Z c))
        get_signZ.

    Definition evalPExprTmBv {n} : list (Term Σ (ty.bvec n)) -> PExpr Z -> Term Σ (ty.bvec n) :=
      PEeval (term_val (Σ := Σ) (ty.bvec n) bv.zero)
        (term_val (Σ := Σ) (ty.bvec n) (bv.of_N 1))
        (term_binop bop.bvadd)
        (term_binop bop.bvmul)
        (term_binop bop.bvsub)
        (term_unop uop.negate)
        (fun p => term_val (ty.bvec n) (bv.of_Z p))
        id_phi_N (pow_N (term_val (Σ := Σ) (ty.bvec n) bv.one) (term_binop bop.bvmul)).

    Lemma ring_morph_val_of_Z {n} :
      ring_morph (term_val (Σ := Σ) (ty.bvec n) bv.zero) (term_val (ty.bvec n) bv.one) (term_binop bop.bvadd) (term_binop bop.bvmul) (term_binop bop.bvsub) (term_unop uop.negate) base.equiv 0%Z 1%Z 
        Z.add Z.mul Z.sub Z.opp Zbool.Zeq_bool (λ c : Z, term_val (ty.bvec n) (bv.of_Z c)).
    Proof.
      constructor; intros; try reflexivity; rewrite ?term_binop_val, ?term_unop_val; cbn.
      - now rewrite bv.of_Z_one.
      - now rewrite bv.of_Z_add.
      - now rewrite bv.of_Z_sub.
      - now rewrite bv.of_Z_mul.
      - now rewrite bv.of_Z_negate.
      - apply Zbool.Zeq_bool_eq in H.
        now subst.
    Qed.

    Lemma evalPol_norm_aux {n : nat} {p : PExpr Z} {l : list (Term Σ (ty.bvec n))} :
      evalPolTmBv l (norm_aux 0%Z 1%Z Z.add Z.mul Z.sub Z.opp Zbool.Zeq_bool p) ≡ evalPExprTmBv l p.
    Proof.
      unfold evalPolTmBv, evalPExprTmBv.
      rewrite Pphi_dev_ok; 
        rewrite ?bv.of_N_one;
        try eauto using Term_bv_ring_eq_ext, Rth_ARth, Term_bv_ring_theory, ring_morph_val_of_Z, get_signZ_th with typeclass_instances.
      rewrite norm_aux_spec; 
        rewrite ?bv.of_N_one;
        try eauto using Term_bv_ring_eq_ext, Rth_ARth, Term_bv_ring_theory, ring_morph_val_of_Z, get_signZ_th, pow_N_th with typeclass_instances.
    Qed.

    Definition CanonTerm_to_Term {σ} : CanonTerm σ -> Term Σ σ :=
      match σ return CanonTerm σ -> Term Σ σ with
      | ty.bvec n => fun ct =>
                       match ct with
                       | (pol , env) => evalPolTmBv env pol
                       end
      (* | ty.int => fun t => match t with *)
      (*                      | (None , v) => term_val _ v *)
      (*                      | (Some t , v) => term_binop bop.plus t (term_val _ v) *)
      (*                      end *)
      | _σ => fun t => t
      end.

    Definition RQuote n : Type := list (Term Σ (ty.bvec n)) -> positive -> PExpr Z * list (Term Σ (ty.bvec n)).

    Definition RQuoteValid {n} (t : Term Σ (ty.bvec n)) (q : RQuote n): Prop :=
      forall lo o, match q lo o with
                     (poly , ln) => o = Pos.of_succ_nat (length lo) -> forall la, evalPExprTmBv (lo ++ ln ++ la) poly = t
                  end.

    Definition Term_bv_Quote_def {n} (t : Term Σ (ty.bvec n)) : RQuote n :=
      fun ts o => (PEX Z o , [ t ]%list).

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

    Lemma Term_bv_Quote_def_Valid {n} {t : Term Σ (ty.bvec n)} : RQuoteValid t (Term_bv_Quote_def t).
    Proof.
      intros lo o Ho la; cbn.
      now rewrite nth_length_prefix.
    Qed.

    Fixpoint plusNatPos (n : nat) (p : positive) : positive :=
      match n with
      | 0 => p
      | S n => Pos.succ (plusNatPos n p)
      end.

    Lemma plusNatPos_of_succ_nat {n m} : plusNatPos n (Pos.of_succ_nat m) = Pos.of_succ_nat (n + m).
    Proof. induction n; cbn; now f_equal. Qed.

    Definition Term_bv_Quote_bin {n} (comb : PExpr Z -> PExpr Z -> PExpr Z) (q1 : RQuote n) (q2 : RQuote n) : RQuote n :=
      fun ts o => let (pol1 , ts1) := q1 ts o in
                  let (pol2 , ts2) := q2 (app ts ts1) (plusNatPos (length ts1) o) in
                  ((comb pol1 pol2) , app ts1 ts2).

    Lemma Term_bv_Quote_bin_Valid {n} {op : BinOp (ty.bvec n) (ty.bvec n) (ty.bvec n)}
      {comb} {t1 t2} {q1 q2} :
      (forall env pol1 pol2, evalPExprTmBv env (comb pol1 pol2) = term_binop op (evalPExprTmBv env pol1) (evalPExprTmBv env pol2)) ->
      RQuoteValid t1 q1 -> RQuoteValid t2 q2 ->
      RQuoteValid (term_binop op t1 t2) (Term_bv_Quote_bin comb q1 q2).
    Proof.
      intros Hcomb Hq1 Hq2 ts o; unfold Term_bv_Quote_bin; cbn.
      generalize (Hq1 ts o); destruct q1 as [pol1 l1].
      intros Hl1.
      generalize (Hq2 (ts ++ l1) (plusNatPos (length l1) o)); destruct q2 as [pol2 l2].
      intros Hl2 Ho l3.
      rewrite Hcomb; f_equal.
      - now rewrite <-List.app_assoc, (Hl1 Ho _).
      - rewrite !List.app_assoc, <-List.app_assoc.
        apply Hl2.
        subst.
        now rewrite plusNatPos_of_succ_nat, app_length, Nat.add_comm.
    Qed.

    Fixpoint Term_bv_Quote {n} (t : Term Σ (ty.bvec n)) {struct t} : RQuote n :=
      Term_bv_case (P := fun n _ => RQuote n)
        (fun n ζ ζin => Term_bv_Quote_def (term_var ζ))
        (fun n v => fun l p => (PEc (bv.unsigned v) , nil))
        (fun n v => Term_bv_Quote_def (term_relval _ v))
        (fun n e1 e2 => Term_bv_Quote_bin (@PEadd _) (Term_bv_Quote e1) (Term_bv_Quote e2))
        (fun n e1 e2 => Term_bv_Quote_bin (@PEsub _) (Term_bv_Quote e1) (Term_bv_Quote e2))
        (fun n e1 e2 => Term_bv_Quote_bin (@PEmul _) (Term_bv_Quote e1) (Term_bv_Quote e2))
        (fun n e1 e2 => Term_bv_Quote_def (term_binop bop.bvand e1 e2))
        (fun n e1 e2 => Term_bv_Quote_def (term_binop bop.bvor e1 e2))
        (fun n e1 e2 => Term_bv_Quote_def (term_binop bop.bvxor e1 e2))
        (fun n m e1 e2 => Term_bv_Quote_def (term_binop bop.shiftr e1 e2))
        (fun n m e1 e2 => Term_bv_Quote_def (term_binop bop.shiftl e1 e2))
        (fun n1 n2 e1 e2 => Term_bv_Quote_def (term_binop bop.bvapp e1 e2))
        (fun n e1 e2 => Term_bv_Quote_def (term_binop bop.bvcons e1 e2))
        (fun n s l pf e1 e2 => Term_bv_Quote_def (term_binop (bop.update_vector_subrange s l) e1 e2))
        (fun n e => Term_bv_Quote_def (term_unop uop.bvnot e))
        (fun n e => Term_bv_Quote_def (term_unop uop.negate e))
        (fun n m pf e => Term_bv_Quote_def (term_unop uop.sext e))
        (fun n m pf e => Term_bv_Quote_def (term_unop uop.zext e))
        (fun n e => Term_bv_Quote_def (term_unop uop.get_slice_int e))
        (fun n m pf e => Term_bv_Quote_def (term_unop (uop.truncate _) e))
        (fun n m s pf e => Term_bv_Quote_def (term_unop (uop.vector_subrange s n) e))
        t.

    Lemma Term_bv_Quote_Valid {n} (t : Term Σ (ty.bvec n)) : RQuoteValid t (Term_bv_Quote t).
    Proof.
      induction n, t using Term_bv_rect; cbn;
        eauto using Term_bv_Quote_def_Valid, Term_bv_Quote_bin_Valid.
      - intros l o Heqo la; cbn.
        now rewrite bv.of_Z_unsigned.
    Qed.

    Definition Term_to_CanonTerm {σ} : Term Σ σ -> CanonTerm σ :=
      match σ return Term Σ σ -> CanonTerm σ with
      | ty.bvec n => fun t =>
                       let (pexpr, env) := Term_bv_Quote t nil 1%positive
                       in (norm_aux 0%Z 1%Z Z.add Z.mul Z.sub Z.opp Zbool.Zeq_bool pexpr , env)
      (* | ty.int => fun t => (Some t , 0%Z) *)
      | _ => fun t => t
      end.

    Lemma Term_to_CanonTerm_to_Term {σ t} : CanonTerm_to_Term (σ := σ) (Term_to_CanonTerm t) ≡ t.
    Proof.
      destruct σ; try reflexivity.
      cbn.
      generalize (Term_bv_Quote_Valid t nil 1%positive).
      destruct (Term_bv_Quote t []%list 1%positive).
      intros H.
      specialize (H eq_refl nil).
      cbn in H.
      rewrite app_nil_r in H.
      now rewrite evalPol_norm_aux, H.
    Qed.

    (* Definition peval_plus (t1 t2 : CanonTerm Σ ty.int) : CanonTerm Σ ty.int := *)
    (*   match t1 , t2 with *)
    (*   | (t1 , v1)  , (t2 , v2)    => (match t1 , t2 with *)
    (*                                   | None , t2 => t2 *)
    (*                                   | t1 , None => t1 *)
    (*                                   | Some t1 , Some t2 => Some (term_binop bop.plus t1 t2) *)
    (*                                   end, (v1 + v2)%Z) *)
    (*   end. *)

    (* Definition peval_minus (t1 t2 : CanonTerm Σ ty.int) : CanonTerm Σ ty.int := *)
    (*   match t1 , t2 with *)
    (*   | (t1 , v1)  , (t2 , v2)    => (match t1 , t2 with *)
    (*                                   | t1 , None => t1 *)
    (*                                   | None , Some t2 => Some (term_unop uop.neg t2) *)
    (*                                   | Some t1 , Some t2 => Some (term_binop bop.minus t1 t2) *)
    (*                                   end, (v1 - v2)%Z) *)
    (*   end. *)

    (* Definition peval_bvadd {n} (t1 t2 : CanonTerm Σ (ty.bvec n)) : CanonTerm Σ (ty.bvec n):= *)
    (*   match t1 , t2 with *)
    (*   | (t1 , v1)  , (t2 , v2)    => (match t1 , t2 with *)
    (*                                   | None , t2 => t2 *)
    (*                                   | t1 , None => t1 *)
    (*                                   | Some t1 , Some t2 => Some (term_binop bop.bvadd t1 t2) *)
    (*                                   end, bv.add v1 v2) *)
    (*   end. *)

    (* Definition peval_bvsub {n} (t1 t2 : CanonTerm Σ (ty.bvec n)) : CanonTerm Σ (ty.bvec n):= *)
    (*   match t1 , t2 with *)
    (*   | (t1 , v1)  , (t2 , v2)    => (match t1 , t2 with *)
    (*                                   | t1 , None => t1 *)
    (*                                   | None , (Some t2) => Some (term_unop uop.negate t2) *)
    (*                                   | Some t1 , Some t2 => Some (term_binop bop.bvsub t1 t2) *)
    (*                                   end, bv.add v1 v2) *)
    (*   end. *)

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

    Equations(noeqns) peval_binop' {σ1 σ2 σ} (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) : Term Σ σ :=
    | op | term_val _ v1 | term_val _ v2 := term_val σ (bop.eval op v1 v2);
    | op | t1            | t2            := term_binop op t1 t2.

    Equations(noeqns) peval_binop {σ1 σ2 σ} (op : BinOp σ1 σ2 σ) (t1 : Term Σ σ1) (t2 : Term Σ σ2) : Term Σ σ :=
    | bop.append , t1 , t2 => peval_append t1 t2
    | bop.or     , t1 , t2 => peval_or t1 t2
    | bop.plus   , t1 , t2 => peval_plus t1 t2
    | op         , t1 , t2 => peval_binop' op t1 t2.

    Lemma peval_append_sound {σ} (t1 t2 : Term Σ (ty.list σ)) :
      peval_append t1 t2 ≡ term_binop bop.append t1 t2.
    Admitted.
    (* Proof. *)
    (*   depelim t1. *)
    (*   - reflexivity. *)
    (*   - depelim t2; cbn. *)
    (*     + now destruct v. *)
    (*     + now constructor. *)
    (*     + now destruct v. *)
    (*     + depelim op. *)
    (*   - now depelim op. *)
    (*   - now depelim op. *)
    (* Qed. *)

    Lemma peval_or_sound (t1 t2 : Term Σ ty.bool) :
      peval_or t1 t2 ≡ term_binop bop.or t1 t2.
    Admitted.
    (* Proof with lsolve. *)
    (*   depelim t1. *)
    (*   - depelim t2... destruct v... *)
    (*   - now destruct v. *)
    (*   - depelim t2... destruct v... *)
    (*   - depelim t2... destruct v... *)
    (* Qed. *)

    Lemma peval_plus_sound (t1 t2 : Term Σ ty.int) :
      peval_plus t1 t2 ≡ term_binop bop.plus t1 t2.
    Admitted.
    (* Proof. funelim (peval_plus t1 t2); lsolve; intros ι; cbn; lia. Qed. *)
    (* Lemma peval_minus_sound (t1 t2 : CanonTerm Σ ty.int) : *)
    (*   CanonTerm_to_Term (peval_minus t1 t2) ≡ term_binop bop.minus (CanonTerm_to_Term t1) (CanonTerm_to_Term t2). *)
    (* Proof. *)
    (*   destruct t1 as [[t1|] v1], t2 as [[t2|] v2]; cbn; *)
    (*     rewrite <-?(term_binop_val (op := bop.minus) (v1 := v1) (v2 := v2)); *)
    (*     ring. *)
    (* Qed. *)

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
        auto using peval_binop'_sound, peval_append_sound, peval_or_sound, peval_plus_sound.
    Qed.


    Equations peval_not (t : Term Σ ty.bool) : Term Σ ty.bool :=
    | term_val _ v                    => term_val ty.bool (negb v)
    | term_binop bop.and t1 t2        => term_binop bop.or (peval_not t1) (peval_not t2)
    | term_binop bop.or t1 t2         => term_binop bop.and (peval_not t1) (peval_not t2)
    | term_binop (bop.relop op) t1 t2 => term_relop_neg op t1 t2
    | t                               => term_unop uop.not t.

    Definition peval_unop' {σ1 σ2} (op : UnOp σ1 σ2) (t : Term Σ σ1) : Term Σ σ2 :=
      match term_get_relval t with
      | Some v =>
          match v with
          | ty.SyncVal _ v => match t with
                              | term_val _ _ => term_val σ2 (uop.eval op v)
                              | term_relval _ _ => term_relval σ2 (ty.SyncVal σ2  (uop.eval op v))
                              | _ => term_unop op t
                              end
          | ty.NonSyncVal _ v1 v2 => term_relval σ2 (ty.NonSyncVal _ (uop.eval op v1) (uop.eval op v2))
          end
      | None   => term_unop op t
      end.

    Definition peval_unop {σ1 σ2} (op : UnOp σ1 σ2) : Term Σ σ1 -> Term Σ σ2 :=
      match op with
      | uop.not => peval_not
      | op      => peval_unop' op
      end.

    Lemma peval_not_sound (t : Term Σ ty.bool) :
      peval_not t ≡ term_unop uop.not t.
    Proof. funelim (peval_not t); lsolve; now apply proper_term_binop. Qed.

    (* TODO: Problems arise when applying a unop to term_relval (ty.SyncVal _ v), because this becomes a term_val (uop.eval op v) at the end. *)
    Lemma peval_unop'_sound {σ1 σ2} (op : UnOp σ1 σ2) (t : Term Σ σ1) :
      peval_unop' op t ≡ term_unop op t.
    Proof. unfold peval_unop'; destruct (term_get_relval_spec t); subst; try easy.
           destruct a.
           - destruct t; cbn; inversion H; try reflexivity; try congruence.
             { rewrite H0.
             easy. }
             inversion H0.
             apply (inj_pair2_eq_dec _ ty.Ty_eq_dec) in H2.
             subst; easy.
           - subst; easy.
    Qed.

    Lemma peval_unop_sound {σ1 σ2} (op : UnOp σ1 σ2) (t : Term Σ σ1) :
      peval_unop op t ≡ term_unop op t.
    Proof.
      destruct op; cbn [peval_unop];
        auto using peval_unop'_sound, peval_not_sound.
    Qed.

    (* Definition peval_union {U K} (t : Term Σ (unionk_ty U K)) : Term Σ (ty.union U) := *)
    (*   match term_get_val t with *)
    (*   | Some v => term_val (ty.union U) (unionv_fold U (existT K v)) *)
    (*   | None   => term_union U K t *)
    (*   end. *)

    (* Import option.notations. *)
    (* Fixpoint peval_record' {rfs : NCtx recordf Ty} (ts : NamedEnv (Term Σ) rfs) {struct ts} : option (NamedEnv Val rfs) := *)
    (*   match ts with *)
    (*   | env.nil         => Some [env] *)
    (*   | env.snoc ts _ t => vs <- peval_record' ts ;; *)
    (*                        v  <- term_get_val t ;; *)
    (*                        Some (env.snoc vs _ v) *)
    (*   end. *)

    (* Definition peval_record R (ts : NamedEnv (Term Σ) (recordf_ty R)) : Term Σ (ty.record R) := *)
    (*   match peval_record' ts with *)
    (*   | Some a => term_val (ty.record R) (recordv_fold R a) *)
    (*   | None => term_record R ts *)
    (*   end. *)

    Fixpoint peval' [σ] (t : Term Σ σ) : Term Σ σ :=
      match t with
      | term_var ς                 => term_var ς
      | term_val _ v               => term_val _ v
      | term_relval _ v               => term_relval _ v
      | term_binop op t1 t2        => peval_binop op (peval' t1) (peval' t2)
      | term_unop op t             => peval_unop op (peval' t)
      (* | term_tuple ts              => term_tuple (env.map (fun b => @peval' b) ts) *)
      (* | term_union U K t           => peval_union (peval' t) *)
      (* | term_record R ts           => peval_record R (env.map (fun b => peval' (σ := type b)) ts) *)
      end.

    Definition peval [σ] : Term Σ σ -> Term Σ σ :=
      match σ return Term Σ σ -> Term Σ σ with
      | ty.bvec n => fun t => peval' (CanonTerm_to_Term (Term_to_CanonTerm t))
      | _ => @peval' _
      end.

    (* Lemma peval_union_sound {U K} (t : Term Σ (unionk_ty U K)) : *)
    (*   peval_union t ≡ term_union U K t. *)
    (* Proof. unfold peval_union. destruct (term_get_val_spec t); now subst. Qed. *)

    (* Lemma peval_record'_sound {rfs : NCtx recordf Ty} (ts : NamedEnv (Term Σ) rfs) : *)
    (*   option.wlp (fun vs => forall ι, inst ts ι = vs) (peval_record' ts). *)
    (* Proof. *)
    (*   induction ts; cbn. *)
    (*   - now constructor. *)
    (*   - rewrite option.wlp_bind. revert IHts. *)
    (*     apply option.wlp_monotonic. intros vs IHvs. *)
    (*     rewrite option.wlp_bind. generalize (term_get_val_spec db). *)
    (*     apply option.wlp_monotonic. intros v IHv. constructor. *)
    (*     intros ι. specialize (IHvs ι). subst. reflexivity. *)
    (* Qed. *)

    (* Lemma peval_record_sound {R} ts : *)
    (*   peval_record R ts ≡ term_record R ts. *)
    (* Proof. *)
    (*   unfold peval_record. destruct (peval_record'_sound ts); [|reflexivity]. *)
    (*   intros ι; cbn. now f_equal. *)
    (* Qed. *)

    Lemma peval'_sound [σ] (t : Term Σ σ) :
      peval' t ≡ t.
    Proof.
      induction t; cbn.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - etransitivity; [apply peval_binop_sound|now apply proper_term_binop].
      - etransitivity; [apply peval_unop_sound|now apply proper_term_unop].
      (* - apply proper_term_tuple. *)
      (*   induction IH; [reflexivity|]; cbn. *)
      (*   now apply proper_env_snoc. *)
      (* - etransitivity; [apply peval_union_sound|now apply proper_term_union]. *)
      (* - rewrite peval_record_sound. *)
      (*   apply proper_term_record. *)
      (*   induction IH; cbn; [reflexivity|]. *)
      (*   now apply proper_namedenv_snoc. *)
    Qed.

    Lemma peval_sound [σ] (t : Term Σ σ) :
      peval t ≡ t.
    Proof.
      destruct σ; try apply peval'_sound; cbn [peval].
      rewrite peval'_sound.
      now rewrite Term_to_CanonTerm_to_Term.
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
