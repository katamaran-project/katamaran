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
     Symbolic.UnifLogic
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
  (Import S : SolverKit B P W)
  (Import SP : SymPropOn B P W)
  (Import UL : UnifLogicOn B P W)
  (Import LSP : LogSymPropOn B P W SP UL).

  Import iris.bi.interface iris.proofmode.tactics proofmode LogicalSoundness.
  Import AutorewriteUnifLogic.

  Module Import GenericSolver.
    Import option.notations.
    Import DList.

    Fixpoint simplify_bool [Σ] (t : Term Σ ty.bool) : DList Σ :=
      Term_bool_case
        (fun (*var*) ς _        => singleton (formula_bool (term_var ς)))
        (fun (*val*) b          => if b then empty else error)
        (fun (*relval*) b          => if b then empty else error)
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
        (fun (*relval*) b          => if b then error else empty)
        (fun (*and*) t1 t2      => singleton (formula_bool (term_binop bop.or (term_unop uop.not t1) (term_unop uop.not t2))))
        (fun (*or*)  t1 t2      => cat (simplify_bool_neg t1) (simplify_bool_neg t2))
        (fun (*rel*) σ op t1 t2 => singleton (formula_relop_neg op t1 t2))
        (fun (*not*) t1         => simplify_bool t1)
        t.

    Lemma simplify_bool_spec_combined {w : World} (t : Term w ty.bool) :
      (instpred (simplify_bool t) ⊣⊢ instpred (w := w) (formula_bool t)) /\
      (instpred (simplify_bool_neg t) ⊣⊢ instpred (formula_bool (term_unop uop.not t))).
    Proof.
      induction t using Term_bool_ind; cbn; arw.
      - destruct v; arw.
      - admit. 
      - destruct IHt1 as [IHt11 IHt12], IHt2 as [IHt21 IHt22]; arw.
        rewrite IHt11 IHt21.
        (* need to find a confluent rewrite strategy... *)
        now rewrite -(term_negb_involutive (term_binop bop.and _ _)) repₚ_term_not' term_not_and; arw.
      - destruct IHt1 as [IHt11 IHt12], IHt2 as [IHt21 IHt22]; arw; arw_slow.
        now rewrite IHt12 IHt22.
      - (* now arw_slow. *) admit.
    (* Qed. *)
    Admitted.

    Lemma simplify_bool_spec [w : World] (t : Term w ty.bool) :
      instpred (simplify_bool t) ⊣⊢ instpred (formula_bool t).
    Proof. apply simplify_bool_spec_combined. Qed.

    Lemma simplify_bool_neg_spec [w : World] (t : Term w ty.bool) :
      instpred (simplify_bool_neg t) ⊣⊢ instpred (formula_bool (term_unop uop.not t)).
    Proof. apply simplify_bool_spec_combined. Qed.
    #[local] Opaque simplify_bool simplify_bool_neg.
    #[local] Hint Rewrite simplify_bool_spec simplify_bool_neg_spec : uniflogic.

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

    Lemma simplify_eq_binop_val_spec [w : World] [σ σ1 σ2]
      (op : BinOp σ1 σ2 σ) (t1 : Term w σ1) (t2 : Term w σ2) (v : Val σ) :
      instpred (simplify_eq_binop_val op t1 t2 v) ⊣⊢
      repₚ (ty.SyncVal _ v) (term_binop op t1 t2).
    Proof. destruct op; arw; destruct v; arw; arw_slow. (* Qed. *)
    Admitted.
    #[local] Opaque simplify_eq_binop_val.
    #[local] Hint Rewrite simplify_eq_binop_val_spec : uniflogic.

    Equations(noeqns) simplify_eq_unop_val [Σ σ1 σ2]
      (op : UnOp σ1 σ2) (t : Term Σ σ1) (v : Val σ2) : DList Σ :=
    | uop.neg        | t | v      => singleton (formula_relop bop.eq t (term_val ty.int (Z.opp v)))
    | uop.not        | t | v     => if v then simplify_bool_neg t else simplify_bool t
    | uop.inl        | t | inl v => singleton (formula_relop bop.eq t (term_val _ v))
    | uop.inl        | t | inr _ => error
    | uop.inr        | t | inl _ => error
    | uop.inr        | t | inr v => singleton (formula_relop bop.eq t (term_val _ v))
    | op             | t | v     => singleton (formula_relop bop.eq (term_unop op t) (term_val _ v)).

    Lemma simplify_eq_unop_val_spec [w : World] [σ1 σ2]
      (op : UnOp σ1 σ2) (t : STerm σ1 w) (v : Val σ2) :
      instpred (simplify_eq_unop_val op t v) ⊣⊢ repₚ (ty.SyncVal _ v) (term_unop op t).
    Proof. destruct op; arw; destruct v; arw; arw_slow. (* Qed. *)
    Admitted.
    #[local] Opaque simplify_eq_unop_val.
    #[local] Hint Rewrite simplify_eq_unop_val_spec : uniflogic.

    Definition simplify_eqb {Σ σ} (t1 t2 : Term Σ σ) : DList Σ :=
      if Term_eqb t1 t2 then empty else singleton (formula_relop bop.eq t1 t2).

    Lemma simplify_eqb_spec [w : World] [σ] (t1 t2 : STerm σ w) :
      instpred (simplify_eqb t1 t2) ⊣⊢ instpred (formula_relop bop.eq t1 t2).
    Proof. (* unfold simplify_eqb. destruct (Term_eqb_spec t1 t2); subst; arw. Qed. *)
    Admitted.
    #[local] Hint Rewrite simplify_eqb_spec : uniflogic.
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

    Lemma simplify_eq_binop_spec [w : World] [σ σ11 σ12 σ21 σ22]
      (op1 : BinOp σ11 σ12 σ) (t11 : STerm σ11 w) (t12 : STerm σ12 w)
      (op2 : BinOp σ21 σ22 σ) (t21 : STerm σ21 w) (t22 : STerm σ22 w) :
      instpred (simplify_eq_binop op1 t11 t12 op2 t21 t22) ⊣⊢
      instpred (formula_relop bop.eq (term_binop op1 t11 t12) (term_binop op2 t21 t22)).
    Proof.
      destruct op1; arw; dependent elimination op2; arw;
        rewrite ?formula_relop_term'; arw.
      - split; intros; split; intros.
        + unfold instpred in H0. destruct H0. cbn in *. unfold instpred_formula_relop in *. cbn in *.
          destruct (inst t11 ι); destruct (inst t21 ι); destruct (inst t12 ι); destruct (inst t22 ι); cbn in *; try contradiction.
          subst. reflexivity.
        + unfold instpred. cbn in *. unfold instpred_formula_relop in *. cbn in *.
          split;
          destruct (inst t11 ι); destruct (inst t21 ι); destruct (inst t12 ι); destruct (inst t22 ι); cbn in *; try contradiction;
          inversion H0; reflexivity.
      - split; intros; split; intros.
        + unfold instpred in H0. destruct H0. cbn in *. unfold instpred_formula_relop in *. cbn in *.
          destruct (inst t11 ι); destruct (inst t21 ι); destruct (inst t12 ι); destruct (inst t22 ι); cbn in *; try contradiction.
          subst. reflexivity.
        + unfold instpred. cbn in *. unfold instpred_formula_relop in *. cbn in *.
          split;
            destruct (inst t11 ι); destruct (inst t21 ι); destruct (inst t12 ι); destruct (inst t22 ι); cbn in *; try contradiction;
            inversion H0; reflexivity.
    Qed.
    #[local] Hint Rewrite simplify_eq_binop_spec : uniflogic.
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

    Lemma simplify_eq_unop_spec [w : World] [σ σ1 σ2]
      (op1 : UnOp σ1 σ) (t1 : STerm σ1 w)
      (op2 : UnOp σ2 σ) (t2 : STerm σ2 w) :
      instpred (simplify_eq_unop op1 t1 op2 t2) ⊣⊢
      instpred (formula_relop bop.eq (term_unop op1 t1) (term_unop op2 t2)).
    Proof.
      (* destruct op1; arw; dependent elimination op2; arw; rewrite formula_relop_term'; arw. *)
    (* Qed. *)
    Admitted.
    #[local] Hint Rewrite simplify_eq_unop_spec : uniflogic.
    #[local] Opaque simplify_eq_unop.

    (* Definition simplify_eq_union_val [Σ U] [K1 : unionk U] *)
    (*   (t1 : Term Σ (unionk_ty U K1)) (v2 : Val (ty.union U)) : DList Σ := *)
    (*    let (K2, v2) := unionv_unfold U v2 in *)
    (*    match eq_dec K1 K2 with *)
    (*    | left e  => let v2' := eq_rec_r (fun K1 => Val (unionk_ty U K1)) v2 e in *)
    (*                 let t2  := term_val (unionk_ty U K1) v2' in *)
    (*                 singleton (formula_relop bop.eq t1 t2) *)
    (*    | right _ => error *)
    (*    end. *)

    (* Lemma simplify_eq_union_val_spec [w : World] [U] [K1 : unionk U] *)
    (*   (t1 : STerm (unionk_ty U K1) w) (v : Val (ty.union U)) : *)
    (*   instpred (simplify_eq_union_val t1 v) ⊣⊢ *)
    (*   instpred (formula_relop bop.eq (term_union U K1 t1) (term_val (ty.union U) v)). *)
    (* Proof. *)
    (*   unfold simplify_eq_union_val. *)
    (*   destruct unionv_unfold as [K2 v2] eqn:?. *)
    (*   apply (f_equal (unionv_fold U)) in Heqs. *)
    (*   rewrite unionv_fold_unfold in Heqs. subst. *)
    (*   destruct eq_dec as [->|e]; arw. *)
    (*   now rewrite (repₚ_unionv_neq e). *)
    (* Qed. *)
    (* #[local] Opaque simplify_eq_union_val. *)
    (* #[export] Hint Rewrite @simplify_eq_union_val_spec : uniflogic. *)

    Fixpoint simplify_eq_val {Σ} [σ] (t : Term Σ σ) : forall (v : Val σ), DList Σ :=
      match t with
      | term_var x          => fun v => singleton (formula_relop bop.eq (term_var x) (term_val _ v))
      | term_val σ v        => fun v' => if eq_dec v v' then empty else error
      | term_relval σ v        => fun v' => if eq_dec v (ty.SyncVal _ v') then empty else error
      | term_binop op t1 t2 => simplify_eq_binop_val op t1 t2
      | term_unop op t      => simplify_eq_unop_val op t
      (* | term_tuple ts       => env.Env_rect *)
      (*                            (fun σs _ => Val (ty.tuple σs) -> DList Σ) *)
      (*                            (fun _ => empty) *)
      (*                            (fun τs _ IHts τ t (vτsτ : Val (ty.tuple (τs ▻ τ))) => *)
      (*                               let (vτs, vτ) := vτsτ in *)
      (*                               cat (simplify_eq_val t vτ) (IHts vτs)) *)
      (*                            ts *)
      (* | term_union U K t    => simplify_eq_union_val t *)
      (* | term_record R ts    => fun vR => *)
      (*                            env.Env_rect *)
      (*                              (fun Δ _ => NamedEnv Val Δ -> DList Σ) *)
      (*                              (fun _ => empty) *)
      (*                              (fun Δ _ IHts b t vs => *)
      (*                                 let (vsΔ,vb) := env.view vs in *)
      (*                                 cat (IHts vsΔ) (simplify_eq_val t vb)) *)
      (*                              ts *)
      (*                              (recordv_unfold R vR) *)
      end.

    Lemma simplify_eq_val_spec [w : World] [σ] (t : STerm σ w) (v : Val σ) :
      instpred (simplify_eq_val t v) ⊣⊢ repₚ (ty.SyncVal _ v) t.
    Proof.
      induction t; arw.
     (*  - cbn; destruct eq_dec; arw. *)
    (*   - induction IH; arw. *)
    (*     + now destruct v. *)
    (*     + destruct v as [vs v]; arw. *)
    (*       now rewrite q IHIH. *)
    (*   - cbn. *)
    (*     rewrite -(recordv_fold_unfold R v). *)
    (*     rewrite repₚ_term_record. *)
    (*     generalize (recordv_unfold R v); intros vs. *)
    (*     rewrite recordv_unfold_fold. *)
    (*     induction IH; destruct (env.view vs); arw. *)
    (*     arw_slow. *)
    (*     now rewrite IHIH q. *)
    (* Qed. *)
    Admitted.
    #[local] Opaque simplify_eq_val.
    #[local] Hint Rewrite simplify_eq_val_spec : uniflogic.

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
    (* simplify_eq (term_tuple ts1)         (term_tuple ts2)         := formula_eqs_ctx (@simplify_eq) ts1 ts2; *)
    (* simplify_eq (term_record _ ts1)      (term_record _ ts2)      := formula_eqs_nctx (@simplify_eq) ts1 ts2; *)
    (* simplify_eq (term_union _ K1 t1)     (term_union _ K2 t2) with eq_dec K1 K2 => { *)
    (*   simplify_eq (term_union _ K1 t1)   (term_union _ ?(K1) t2) (left eq_refl) := simplify_eq t1 t2; *)
    (*   simplify_eq _ _ (right _) := error *)
    (* }; *)
    simplify_eq t1              t2   := simplify_eqb t1 t2.

    Lemma simplify_eq_spec [w : World] [σ] (s t : Term w σ) :
      instpred (simplify_eq s t) ⊣⊢ instpred (formula_relop bop.eq s t).
    Proof.
      induction s.
      (* - dependent elimination t; arw. *)
    (*   - arw. *)
    (*   - dependent elimination t; arw. *)
    (*   - dependent elimination t; arw. *)
    (*   - dependent elimination t; arw. *)
    (*     induction IH; env.destroy ts; arw. *)
    (*     rewrite IHIH (q v) !formula_relop_term' bi.sep_comm. arw. *)
    (*   - dependent elimination t; arw; cbn. *)
    (*     destruct eq_dec as [Heq|Hneq]; arw. *)
    (*     + destruct Heq; cbn. rewrite IHs !formula_relop_term'. arw. *)
    (*     + rewrite formula_relop_term'; arw. *)
    (*       now rewrite (eqₚ_term_union_neq Hneq). *)
    (*   - dependent elimination t; arw; cbn.  *)
    (*     rewrite formula_relop_term'; arw. *)
    (*     arw_slow. *)
    (*     induction IH; env.destroy ts0; arw. *)
    (*     rewrite IHIH (q v) formula_relop_term'. arw. *)
    (*     arw_slow. *)
    (* Qed. *)
      Admitted.
    #[export] Hint Rewrite @simplify_eq_spec : uniflogic.

    Definition simplify_relopb {Σ σ} (op : RelOp σ)
      (t1 t2 : STerm σ Σ) : DList Σ :=
      singleton (formula_relop op t1 t2).
      (* match term_get_relval t1 , term_get_relval t2 with *)
      (* | Some v1 , Some v2 => if bop.eval_relop_val op v1 v2 then empty else error *)
      (* | _       , _       => singleton (formula_relop op t1 t2) *)
      (* end. *)

    Definition simplify_relopb_spec {w : World} {σ} (op : RelOp σ)
      (t1 t2 : STerm σ w) :
      instpred (simplify_relopb op t1 t2) ⊣⊢ instpred (formula_relop op t1 t2).
    Proof.
      unfold simplify_relopb.
      arw.
      (* destruct (term_get_relval_spec t1) as [v1|]; arw; try now rewrite formula_relop_term'. subst. *)
      (* destruct (term_get_relval_spec t2) as [v2|]; arw; try now rewrite formula_relop_term'. subst. *)
      (* destruct (bop.eval_relop_val_spec op v1 v2); arw. *)
    Qed.
    #[local] Opaque simplify_relopb.
    #[export] Hint Rewrite @simplify_relopb_spec : uniflogic.

    Equations(noeqns) simplify_le {Σ} (t1 t2 : Term Σ ty.int) : DList Σ :=
    simplify_le (term_val _ 0%Z)         (term_unop uop.unsigned t) := empty;
    simplify_le t1                       t2                         := simplify_relopb bop.le t1 t2.

    Lemma simplify_le_spec [w : World] (s t : Term w ty.int) :
      instpred (simplify_le s t) ⊣⊢ instpred (formula_relop bop.le s t).
    Proof.
      dependent elimination s; try (now apply simplify_relopb_spec).
      destruct v; try (now apply simplify_relopb_spec).
      dependent elimination t; try (now apply simplify_relopb_spec).
      dependent elimination op1; try (now apply simplify_relopb_spec).
      cbn -[empty].
      arw_slow.
      iSplit; iIntros; [|done].
      iStopProof. crushPredEntails3; cbn.
    (*   now apply N2Z.is_nonneg. *)
    (* Qed. *)
    Admitted.
    #[export] Hint Rewrite @simplify_le_spec : uniflogic.

    Definition simplify_relop {Σ σ} (op : RelOp σ) :
      forall (t1 t2 : STerm σ Σ), DList Σ :=
      match op in RelOp σ return forall (t1 t2 : STerm σ Σ), DList Σ with
      | bop.eq => simplify_eq
      | bop.le => simplify_le
      | op     => simplify_relopb op
      end.

    Lemma simplify_relop_spec {w : World} {σ} (op : RelOp σ) (t1 t2 : STerm σ w) :
      instpred (simplify_relop op t1 t2) ⊣⊢ instpred (formula_relop op t1 t2).
    Proof.
      unfold simplify_relop.
      destruct op; arw; rewrite ?formula_relop_term'; arw.
    Qed.
    #[export] Hint Rewrite @simplify_relop_spec : uniflogic.

    Definition smart_and {Σ} (F1 F2 : Formula Σ) : Formula Σ :=
      match F1 , F2 with
      | formula_true , _ => F2
      | _ , formula_true => F1
      | formula_false , _ => formula_false
      | _ , formula_false => formula_false
      | _ , _ => formula_and F1 F2
      end.

    Lemma smart_and_spec {w : World} (F1 F2 : Formula w) :
      instpred (smart_and F1 F2) ⊣⊢ instpred (formula_and F1 F2).
    Proof.
      destruct F1, F2; cbn;
        now rewrite ?bi.True_sep ?bi.sep_True ?bi.sep_False ?bi.False_sep.
    Qed.
    #[export] Hint Rewrite @smart_and_spec : uniflogic.

    Lemma smart_and_spec' {w : World} (F1 F2 : Formula w) :
      instpred_formula (smart_and F1 F2) ⊣⊢ instpred (formula_and F1 F2).
    Proof. apply smart_and_spec. Qed.
    #[export] Hint Rewrite @smart_and_spec' : uniflogic.

    Definition PathCondition_to_Formula [Σ] : PathCondition Σ -> Formula Σ :=
      ctx.Ctx_rect (fun _ => Formula Σ) formula_true (fun PC FPC F' => smart_and FPC F').

    Lemma PathCondition_to_Formula_sound [w : World] (P : PathCondition w) :
      instpred (PathCondition_to_Formula P) ⊣⊢ instpred P.
    Proof.
      induction P; first done; cbn; arw; cbn.
      unfold instpred_inst_formula, instpred in IHP; cbn in IHP.
      now rewrite IHP.
    Qed.
    #[export] Hint Rewrite @PathCondition_to_Formula_sound : uniflogic.

    Program Definition PathCondition_to_DList [Σ] (pc : PathCondition Σ) : DList Σ :=
      MkDList (fun k => Some (pc ▻▻ k)) _.
    Next Obligation. intros; cbn. now rewrite instprop_cat. Qed.

    Fixpoint simplify_formula {Σ} (fml : Formula Σ) : DList Σ :=
      match fml with
      | formula_user p ts      => singleton (formula_user p (pevals ts))
      | formula_bool t         => simplify_bool (peval t)
      | formula_prop ζ P       => singleton fml
      | formula_relop op t1 t2 => simplify_relop op (peval t1) (peval t2)
      | formula_true           => empty
      | formula_false          => error
      | formula_and F1 F2      => cat (simplify_formula F1) (simplify_formula F2)
      | formula_or F1 F2       => match DList.run (simplify_formula F1) with
                                  | Some []%ctx => empty
                                  | None => simplify_formula F2
                                  | Some F1' => match DList.run (simplify_formula F2) with
                                                | Some []%ctx => empty
                                                | None => PathCondition_to_DList F1'
                                                | Some F2' => singleton (formula_or (PathCondition_to_Formula F1') (PathCondition_to_Formula F2'))
                                         end
                                  end
      | formula_public t       => singleton (formula_public t)
      | formula_eq_nonsync t1 t2 => singleton (formula_eq_nonsync t1 t2) (* No simplifications for now, but machinery should be reusable *)
      end.

    Lemma PathCondition_to_Formula_sound' [w : World] (P : PathCondition w) :
      instpred_formula (PathCondition_to_Formula P) ⊣⊢ instpred P.
    Proof. now apply PathCondition_to_Formula_sound. Qed.
    #[export] Hint Rewrite @PathCondition_to_Formula_sound' : uniflogic.

    Lemma PathCondition_to_DList_sound [w : World] (P : PathCondition w) :
      instpred (PathCondition_to_DList P) ⊣⊢ instpred P.
    Proof. reflexivity. Qed.
    #[export] Hint Rewrite @PathCondition_to_DList_sound : uniflogic.

    Fixpoint simplify_pathcondition {Σ} (C : PathCondition Σ) : DList Σ :=
      match C with
      | [ctx] => empty
      | C ▻ F => cat (simplify_pathcondition C) (simplify_formula F)
      end.

    Lemma simplify_formula_spec {w : World} (F : Formula w) :
      instpred (simplify_formula F) ⊣⊢ instpred F.
    Proof.
      induction F; arw; cbn; rewrite ?pevals_sound ?peval_sound ?formula_relop_term'; arw.
      - now rewrite IHF1 IHF2.
      - pose proof (instpred_run (simplify_formula F1)) as HrF1.
        pose proof (instpred_run (simplify_formula F2)) as HrF2.
        destruct run as [PC|].
        + destruct PC as [|PCrest1 F11]; cbn in *.
          { iSplit; iIntros "_"; [|now cbn].
            now iLeft; iApply IHF1; iApply HrF1. }
          destruct run as [PC|].
          destruct PC as [|PCrest2 F22]; cbn in *.
          { iSplit; iIntros "_"; [|now cbn].
            now iRight; iApply IHF2; iApply HrF2. }
          rewrite instpred_dlist_singleton.
          { change (instpred_formula ?F) with (instpred F).
            rewrite -IHF2 -HrF2.
            rewrite -IHF1 -HrF1.
            now arw.
          }
          change (instpred_formula ?F) with (instpred F).
          rewrite -IHF2 -HrF2 bi.or_False.
          now rewrite -IHF1 -HrF1.
        + change (instpred_formula F1) with (instpred F1).
          rewrite -IHF1 -HrF1; cbn.
          now rewrite bi.False_or.
    Qed.
    #[export] Hint Rewrite @simplify_formula_spec : uniflogic.

    Lemma simplify_pathcondition_spec {w : World} (C : PathCondition w) :
      instpred (w := w) (run (simplify_pathcondition C)) ⊣⊢ instpred C.
    Proof.
      change (instpred (simplify_pathcondition C) ⊣⊢ instpred C).
      induction C as [|C IHC F]; arw.
      now rewrite IHC.
    Qed.
    #[export] Hint Rewrite @simplify_pathcondition_spec : uniflogic.

    Definition occurs_check_lt {Σ x} (xIn : (x ∈ Σ)%katamaran) {σ} (t : Term Σ σ) : option (Term (Σ - x) σ) :=
      match t with
      | term_var_in yIn =>
        if Nat.ltb (ctx.in_at xIn) (ctx.in_at yIn) then occurs_check xIn t else None
      | _ => occurs_check xIn t
      end.

    Lemma occurs_check_lt_sound {Σ x} (xIn : (x ∈ Σ)%katamaran) {σ} (t : Term Σ σ) (t' : Term (Σ - x) σ) :
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
      option.wlp
        (fun '(existT w' ν) => repₚ (T := STerm ty.bool) (ty.SyncVal ty.bool true) t ⊣⊢ inst_triangular ν)
        (try_unify_bool t).
    Proof.
      induction t using Term_bool_ind; cbn; try constructor; auto.
      - rewrite inst_triangular_knowing.
        rewrite (knowing_trans (w2 := wsubst _ _ _)).
        rewrite knowing_id knowing_acc_subst_right.
        now crushPredEntails3.
      - induction t using Term_bool_ind; cbn; try constructor.
        rewrite inst_triangular_knowing (knowing_trans (ω23 := acc_refl)) knowing_id knowing_acc_subst_right.
    (*     unfold assuming; crushPredEntails3; cbn; *)
    (*       now apply negb_true_iff. *)
    (* Qed. *)
    Admitted.

    Lemma try_unify_eq_spec {w : World} {σ} (t1 t2 : Term w σ) :
      option.wlp
        (fun '(existT w' ν) => eqₚ t1 t2 ⊣⊢ inst_triangular ν)
        (try_unify_eq t1 t2).
    Proof.
      unfold try_unify_eq. destruct t1; cbn; try (constructor; auto; fail).
      destruct (occurs_check_lt ςInΣ t2) eqn:Heq; constructor; auto.
      apply occurs_check_lt_sound in Heq.
      rewrite inst_triangular_knowing (knowing_trans (ω23 := acc_refl)) knowing_id knowing_acc_subst_right assuming_True bi.sep_True.
      now subst.
    Qed.

    Lemma try_unify_formula_spec {w : World} (fml : Formula w) :
      option.wlp 
        (fun '(existT w' ν) => instpred fml ⊣⊢ inst_triangular ν) (try_unify_formula fml).
    Proof.
      unfold try_unify_formula; destruct fml; cbn; try (constructor; auto; fail).
      - apply try_unify_bool_spec.
      - destruct rop; try constructor; cbn.
        destruct (try_unify_eq_spec t1 t2) as [[w' ν] HYP|]. constructor. auto.
    (*     destruct (try_unify_eq_spec t2 t1) as [[w' ν] HYP|]; constructor. *)
    (*     rewrite <-HYP. *)
    (*     now unfold eqₚ. *)
    (* Qed. *)
    Admitted.

    Definition unify_formula {w0 : World} (F : Formula w0) :
      { w1 & Tri w0 w1 * PathCondition w1 }%type :=
      match try_unify_formula F with
      | Some (existT w1 ν01) => existT w1 (ν01 , ctx.nil)
      | None => existT w0 (tri_id , ctx.nil ▻ F)
      end.

    Lemma unify_formula_spec {w0 : World} (fml : Formula w0) :
      match unify_formula fml with
      | existT w1 (ν01 , fmls) =>
         (instpred fml) ⊣⊢ knowing (acc_triangular ν01) (instpred fmls)
      end.
    Proof.
      unfold unify_formula.
      destruct (try_unify_formula_spec fml).
      - destruct a as [w1 ν01].
        now rewrite H inst_triangular_knowing.
      - now rewrite knowing_id instpred_singleton.
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

    Lemma instprop_cat_pred `{H : InstProp A} (w : World) (C1 C2 : Ctx (A w)) :
      instprop (C1 ▻▻ C2) ⊣⊢ (instprop C1 : Pred w) ∗ instprop C2.
    Proof.
      constructor. intros. now rewrite instprop_cat.
    Qed.

    Lemma knowing_tri_comp {w0 w1 w2} {ν01 : Tri w0 w1} {ν12 : Tri w1 w2} {P} :
      knowing (acc_triangular (tri_comp ν01 ν12)) P ⊣⊢ knowing (acc_trans (acc_triangular ν01) (acc_triangular ν12)) P.
    Proof.
      apply knowing_resp_sub_acc.
      now rewrite sub_acc_trans !sub_acc_triangular sub_triangular_comp.
    Qed.


    Lemma unify_pathcondition_spec {w0 : World} (C0 : PathCondition w0) :
      match unify_pathcondition C0 with
      | existT w1 (ν01 , C1) =>
          instpred C0 ⊣⊢ knowing (acc_triangular ν01) (instpred C1)
      end.
    Proof.
      induction C0 as [|C0 IHC F0]; cbn.
      - now rewrite knowing_id.
      - destruct unify_pathcondition as (w1 & ν01 & C1).
        pose proof (unify_formula_spec (persist F0 (acc_triangular ν01))) as IHF.
        destruct (unify_formula (persist F0 (acc_triangular ν01))) as (w2 & ν12 & C2).
        change (instpred_ctx C0) with (instpred C0).
        rewrite IHC.
        rewrite knowing_tri_comp.
        rewrite instpred_cat.
        rewrite knowing_trans.
        rewrite knowing_absorb_forgetting.
        rewrite instpred_persist in IHF.
        rewrite IHF.
        rewrite instpred_persist.
        apply knowing_proper_bientails.
        rewrite (bi.sep_comm _ (instpred C2)).
        rewrite <-knowing_absorb_forgetting.
        now rewrite bi.sep_comm.
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

    Definition smart_or {Σ} (F1 F2 : Formula Σ) : Formula Σ :=
      match F1 , F2 with
      | formula_false , _ => F2
      | _ , formula_false => F1
      | formula_true , _ => formula_true
      | _ , formula_true => formula_true
      | _ , _ => formula_or F1 F2
      end.

    Lemma smart_or_spec {w : World} (F1 F2 : Formula w) :
      instpred (smart_or F1 F2) ⊣⊢ instpred (formula_or F1 F2).
    Proof.
      destruct F1, F2; cbn;
        now rewrite ?bi.True_or ?bi.or_True ?bi.or_False ?bi.False_or.
    Qed.
    #[export] Hint Rewrite @smart_or_spec : uniflogic.

    Fixpoint formula_simplifies {Σ} (hyp : Formula Σ) (fact : Formula Σ) : option (Formula Σ) :=
      match hyp with
        formula_and hyp1 hyp2 => match formula_simplifies hyp1 fact , formula_simplifies hyp2 fact with
                                 | Some hyp1' , Some hyp2' => Some (smart_and hyp1' hyp2')
                                 | Some hyp1' , None => Some (smart_and hyp1' hyp2)
                                 | None , Some hyp2' => Some (smart_and hyp1 hyp2')
                                 | None , None => None
                                 end
      | formula_or hyp1 hyp2 => match formula_simplifies hyp1 fact , formula_simplifies hyp2 fact with
                                | Some hyp1' , Some hyp2' => Some (smart_or hyp1' hyp2')
                                | Some hyp1' , None => Some (smart_or hyp1' hyp2)
                                | None , Some hyp2' => Some (smart_or hyp1 hyp2')
                                | None , None => None
                                end
      | _ => if formula_eqb hyp fact then Some formula_true else None
      end.

    Lemma bi_wand_iff_true {w} {P : Pred w} : P ⊢ P ∗-∗ True.
    Proof. iIntros "HP"; iSplit; now iIntros. Qed.

    Lemma bi_wand_iff_sep {w} {P1 P2 Q1 Q2 : Pred w} : (P1 ∗-∗ Q1) ∗ (P2 ∗-∗ Q2) ⊢ P1 ∗ P2 ∗-∗ Q1 ∗ Q2.
    Proof.
      iIntros "[H1 H2]". iSplit.
      - iIntros "[HP1 HP2]". now iSplitL "H1 HP1"; [iApply "H1"|iApply "H2"].
      - iIntros "[HQ1 HQ2]". now iSplitL "H1 HQ1"; [iApply "H1"|iApply "H2"].
    Qed.

    Lemma bi_wand_iff_sep_l {w} {P Q R : Pred w} : P ∗-∗ Q ⊢ R ∗ P ∗-∗ R ∗ Q.
    Proof.
      iIntros "HPQ". iApply (bi_wand_iff_sep with "[HPQ]"). iFrame.
      now iApply bi.wand_iff_refl.
    Qed.


    Lemma bi_wand_iff_or {w} {P1 P2 Q1 Q2 : Pred w} : (P1 ∗-∗ Q1) ∗ (P2 ∗-∗ Q2) ⊢ P1 ∨ P2 ∗-∗ Q1 ∨ Q2.
    Proof.
      iIntros "[H1 H2]"; iSplit.
      - iIntros "[HP1|HP2]"; [iLeft|iRight]; [now iApply "H1"|now iApply "H2"].
      - iIntros "[HQ1|HQ2]"; [iLeft|iRight]; [now iApply "H1"|now iApply "H2"].
    Qed.

    Lemma formula_simplifies_spec {w : World} (hyp fact : Formula w) :
      option.wlp (fun hyp' => ⊢ instpred fact -∗ (instpred hyp ∗-∗ instpred hyp'))
        (formula_simplifies hyp fact).
    Proof.
      induction hyp; cbn;
        repeat match goal with
          | |- context[ formula_eqb ?F1 ?F2] => destruct (formula_eqb_spec F1 F2); subst
          | H : option.wlp _ (formula_simplifies ?hyp ?F)|- context[ formula_simplifies ?hyp ?F ] => destruct H
        end; try (now eapply option.wlp_none); try eapply option.wlp_some; cbn;
        try (now iApply bi_wand_iff_true);
        arw; cbn; iIntros "#Hfact";
        (iApply bi_wand_iff_or || iApply bi_wand_iff_sep); iSplit;
        now (iApply H || iApply H0 || iApply bi.wand_iff_refl).
    Qed.

    Fixpoint assumption_formula {Σ} (C : PathCondition Σ) (F : Formula Σ) (k : PathCondition Σ) {struct C} : PathCondition Σ :=
      match C with
      | [ctx]  => k ▻ F
      | C ▻ F' => match formula_simplifies F F' with
                  | Some F2 => assumption_formula C F2 k
                  | None => assumption_formula C F k
                  end
      end.

    Fixpoint assumption_pathcondition {Σ} (C : PathCondition Σ) (Fs : PathCondition Σ) (k : PathCondition Σ) {struct Fs} : PathCondition Σ :=
      match Fs with
      | [ctx]  => k
      | Fs ▻ F => assumption_formula C F (assumption_pathcondition C Fs k)
      end.

    Lemma assumption_formula_spec {w : World} (C : PathCondition w) (F : Formula w) (k : PathCondition w) :
      ⊢ instpred C -∗ instpred k ∗ instpred F ∗-∗ instpred (assumption_formula C F k).
    Proof.
      revert F; induction C as [|C ? F']; intros F; cbn; auto.
      iIntros "[#HC #HF']".
      destruct (formula_simplifies_spec F F');
        subst; [|now iApply IHC].
      iPoseProof (IHC a with "HC") as "HC'".
      iPoseProof (H with "HF'") as "HF".
      iApply (bi.wand_iff_trans).
      iFrame "HC'".
      now iApply (bi_wand_iff_sep_l with "HF").
    Qed.

    Lemma assumption_pathcondition_spec {w : World} (C : PathCondition w) (FS : PathCondition w) (k : PathCondition w) :
      instpred C -∗ ((instpred (w := w) k ∗ instpred FS ∗-∗ instpred (assumption_pathcondition C FS k))).
    Proof.
      induction FS as [|FS ? F]; cbn; iIntros "#HC".
      - rewrite bi.sep_emp.
        now iApply bi.wand_iff_refl.
      - iPoseProof (assumption_formula_spec C F (assumption_pathcondition C FS k) with "HC") as "HCF".
        iPoseProof (IHFS with "HC") as "HCFS".
        iApply (bi.wand_iff_trans with "[HCFS HCF]").
        iSplitR "HCF"; last iExact "HCF".
        iSplit.
        + iIntros "(Hk & HFS & HF)"; iFrame.
          iApply "HCFS".
          now iFrame.
        + iIntros "(HFS & HF)".
          iDestruct "HCFS" as "[_ HCFS2]".
          iDestruct ("HCFS2" with "HFS") as "(Hk & HFS)".
          now iFrame.
    Qed.

    Definition solver_generic : Solver :=
      fun w0 C0 =>
        match DList.run (simplify_pathcondition C0) with
        | Some C1 => Some (unify_pathcondition (assumption_pathcondition (wco w0) C1 ctx.nil))
        | None => None
        end.

    Lemma solver_generic_spec : SolverSpec solver_generic.
    Proof.
      unfold solver_generic. intros w C0.
      pose proof (simplify_pathcondition_spec C0) as Hequiv.
      destruct run as [C0'|]; constructor; cbn.
      - pose proof (unify_pathcondition_spec (assumption_pathcondition (wco w) C0' ctx.nil)) as Hunify.
        destruct (unify_pathcondition (assumption_pathcondition (wco w) C0' ctx.nil)) as (w1 & ν01 & C1).
        rewrite <-Hunify.
        rewrite <-Hequiv.
        pose proof (assumption_pathcondition_spec (wco w) C0' ctx.nil) as Hassumption.
        iPoseProof wco_valid as "Hwco".
        iDestruct (Hassumption with "Hwco") as "Hassumption".
        rewrite bi.emp_sep.
        now iApply (bi.wand_iff_sym with "Hassumption").
      - now rewrite <-Hequiv.
    Qed.

  End GenericSolver.

  Lemma solver_compose_spec {s1 s2} (spec1 : SolverSpec s1) (spec2 : SolverSpec s2) : SolverSpec (solver_compose s1 s2).
  Proof.
    unfold SolverSpec, solver_compose. intros w0 fmls0.
    apply option.spec_bind.
    generalize (spec1 w0 fmls0); clear spec1.
    apply option.spec_monotonic; auto.
    intros (w1 & ν01 & fmls1) H1.
    apply option.spec_map.
    generalize (spec2 w1 fmls1); clear spec2.
    apply option.spec_monotonic; auto.
    - intros (w2 & ν12 & fmls2) H2.
      rewrite knowing_tri_comp.
      rewrite knowing_trans.
      now rewrite H2.
    - intros Hfmls1.
      now rewrite <-H1, Hfmls1, knowing_pure.
  Qed.


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
