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

(* ========================================================================= *)
(* Solver.v -- the generic, framework-provided constraint solver used by     *)
(* every symbolic executor at each `assume`/`assert` to simplify and prune   *)
(* path conditions.  `simplify_bool`/`simplify_bool_neg` normalize boolean    *)
(* formulas into simpler equivalent formula lists; `solver_generic`          *)
(* discharges/simplifies the framework-level formulas (equalities, relops,   *)
(* `secLeak`, ...), and `solver_compose` sequences it with a case-study-     *)
(* supplied external `Solver` (from the `SolverKit` module type in          *)
(* `Symbolic/Worlds.v`) into `combined_solver`, the solver each case study   *)
(* actually installs.  See the `secret-data-walls` skill for the narrower    *)
(* `secLeak`-specific recognizer logic further down this file.               *)
(* ========================================================================= *)

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
     Bitvector
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
      Term_bool_case (fun _ => DList Σ)
        (fun (*var*) ς _        => singleton (formula_bool (term_var ς)))
        (fun (*val*) b          => if b then empty else error)
        (fun (*relval*) b       =>
           (* formula_bool holds iff it holds on BOTH sides *)
           if ty.projLeftRV b && ty.projRightRV b then empty else error)
        (fun (*and*) t1 t2      => cat (simplify_bool t1) (simplify_bool t2))
        (fun (*or*)  t1 t2      => singleton (formula_bool (term_binop bop.or t1 t2)))
        (fun (*rel*) σ op t1 t2 => singleton (formula_relop op t1 t2))
        (fun (*not*) t1         => simplify_bool_neg t1)
        t
    with
    simplify_bool_neg [Σ] (t : Term Σ ty.bool) : DList Σ :=
      Term_bool_case (fun _ => DList Σ)
        (fun (*var*) ς _        => singleton (formula_bool (term_unop uop.not (term_var ς))))
        (fun (*val*) b          => if b then error else empty)
        (fun (*relval*) b       =>
           if negb (ty.projLeftRV b) && negb (ty.projRightRV b) then empty else error)
        (fun (*and*) t1 t2      => singleton (formula_bool (term_binop bop.or (term_unop uop.not t1) (term_unop uop.not t2))))
        (fun (*or*)  t1 t2      => cat (simplify_bool_neg t1) (simplify_bool_neg t2))
        (fun (*rel*) σ op t1 t2 => singleton (formula_relop_neg op t1 t2))
        (fun (*not*) t1         => simplify_bool t1)
        t.

    Lemma simplify_bool_spec_combined {w : World} (t : Term w ty.bool) :
      (instpred (simplify_bool t) ⊣⊢ repₚ (T := fun Σ => Term Σ ty.bool) (ty.valToRelVal (σ := ty.bool) true) t) ∧
        (instpred (simplify_bool_neg t) ⊣⊢ repₚ (T := fun Σ => Term Σ ty.bool) (ty.valToRelVal (σ := ty.bool) false) t).
    Proof.
      induction t using Term_bool_ind; cbn; arw.
      - destruct b; arw.
      - destruct b as [[] []]; cbn; arw.
      - split.
        + destruct IHt1 as [-> _], IHt2 as [-> _].
          by rewrite repₚ_term_and.
        + (* need to find a confluent rewrite strategy... *)
          now rewrite -(term_negb_involutive (term_binop bop.and _ _))
                         repₚ_term_not' term_not_and.
      - rewrite instpred_dlist_cat. destruct IHt1 as [_ ->], IHt2 as [_ ->].
        rewrite repₚ_term_or_false. intuition.
        arw.
    Qed.

    Lemma simplify_bool_spec [w : World] (t : Term w ty.bool) :
      instpred (simplify_bool t) ⊣⊢ instpred (formula_bool t).
    Proof. apply simplify_bool_spec_combined. Qed.

    Lemma simplify_bool_neg_spec [w : World] (t : Term w ty.bool) :
      instpred (simplify_bool_neg t) ⊣⊢ repₚ (T := fun Σ => Term Σ ty.bool) (ty.valToRelVal (σ := ty.bool) false) t.
    Proof. apply simplify_bool_spec_combined. Qed.
    #[local] Opaque simplify_bool simplify_bool_neg.
    #[local] Hint Rewrite simplify_bool_spec simplify_bool_neg_spec : uniflogic.

    Equations(noind) formula_is_secLeakT {Σ σ} (f : Formula Σ) (t : Term Σ σ) : bool :=
      formula_is_secLeakT (@formula_secLeak _ τ t') t with eq_dec σ τ => {
          formula_is_secLeakT (@formula_secLeak _ _ t') t (left eq_refl) := Term_eqb t t';
          formula_is_secLeakT (@formula_secLeak _ _ t') t (right _) := false
        };
      formula_is_secLeakT _ _ := false.

    Lemma formula_is_secLeakT_spec {Σ σ} (f : Formula Σ) (t : Term Σ σ) :
      BoolSpec (f = formula_secLeak t) True (formula_is_secLeakT f t).
    Proof.
      induction f; simp formula_is_secLeakT;
        repeat
          match goal with
          | |- BoolSpec _ _ false   => constructor; auto
          | |- BoolSpec _ _ true   => try (constructor; congruence; fail)
          | |- context[eq_dec _ _ ] => destruct eq_dec; subst; cbn
          | |- context[Term_eqb ?t1 ?t2] =>
              destruct (Term_eqb_spec t1 t2); cbn;
              try (constructor; congruence; fail)
          | IH: forall f2 : Formula _, BoolSpec _ _ (formula_is_secLeakT ?f f2)
                                       |- context[formula_is_secLeakT ?f ?f2] =>
              specialize (IH f2); destruct IH
          end.
    Qed.

    Fixpoint pathconditions_contains_secLeakT {Σ σ} (C : PathCondition Σ) (t : Term Σ σ) : bool :=
      match C with
      | [ctx] => false
      | (C ▻ F') => formula_is_secLeakT F' t || pathconditions_contains_secLeakT C t
      end.

    Lemma weakening_constraints_helper {Σ wco} (b f : Formula Σ) :
      (⊢ @instpred _ _ {| wctx := Σ; wco := wco |} f) ->
      (⊢ @instpred _ _ {| wctx := Σ; wco := wco ▻ b |} f).
    Proof.
      intro Hf.
      constructor. intros ι Hco _.
      Search entails.
      specialize (fromEntails Hf) as H'.
      specialize (H' ι). 
      rewrite instpred_prop. rewrite instpred_prop in H'.
      apply H'.
      cbn in *.
      tauto.
      easy.
    Qed.
      
    Lemma pathconditions_contains_secLeakT_spec {w : World} {σ} (t : Term w σ) :
      ⌜pathconditions_contains_secLeakT (wco w) t⌝ -∗ instpred (formula_secLeak t) .
    Proof.
      destruct w as [Σ wco].
      Set Printing Implicit.
      Set Printing Coercions.
      Search assuming.
      induction wco.
      - iIntros "%H". contradiction.
      - iIntros "%Hwco". apply orb_prop_elim in Hwco.
        destruct Hwco.
        + cbn in *.
          destruct (formula_is_secLeakT_spec b t).
          cbn in H.
          * rewrite H0.
            iApply instpred_formula_if_formula.
          * contradiction.
        + change (Is_true _) with
            (Is_true (pathconditions_contains_secLeakT wco0 t)) in H.
          specialize (IHwco t).
          iStopProof.
          apply weakening_constraints_helper.
          cbn in *.
          iApply IHwco.
          by iPureIntro.
          Unset Printing Implicit.
          Unset Printing Coercions.
    Qed.

    (* moved up from SimplifySecLeakSpec: secLeakT's spec needs the
       compositional direction (2026-10-01) *)
    Section SecLeakCompositional.
      Context [w : World].

      (* Compositional in ONE direction only: public operands give a public
         result.  The converse fails for pairs ([x - x] is public for any [x]),
         which the old tagged RelVal made true by fiat. *)
      Lemma instpred_formula_secLeak_binop {σ1 σ2 σ3} (t1 : Term w σ1) (t2 : Term w σ2) op :
        instpred_formula_secLeak t1 ∗ instpred_formula_secLeak t2
          ⊢ instpred_formula_secLeak (σ := σ3) (term_binop op t1 t2).
      Proof.
        constructor. intros ι _ [H1 H2].
        unfold instpred_formula_secLeak, secLeak in *. cbn.
        destruct (inst t1 ι), (inst t2 ι); cbn in *. now rewrite H1 H2.
      Qed.

      Lemma instpred_formula_secLeak_unop {σ1 σ2} (t : Term w σ1) op :
        instpred_formula_secLeak t ⊢ instpred_formula_secLeak (σ := σ2) (term_unop op t).
      Proof.
        constructor. intros ι _ H0. unfold instpred_formula_secLeak, secLeak in *. cbn.
        destruct (inst t ι); cbn in *. now rewrite H0.
      Qed.

    End SecLeakCompositional.

    (* COMPOSITIONAL since 2026-10-01: a lifted binop/unop of public terms is
       public (instpred_formula_secLeak_binop/_unop), so a term is accepted if
       it is a literal, its operands are accepted, or the path condition says
       so of the exact term.  Before, only the last two: `(31 + sext b) >> 5`
       over a public `b` was NOT public to the solver, which kept every rule
       guarded by secLeakT (try_bvadd_cancel, Term_eqb_relval) from firing
       on it.  Cost: one wco scan per node that falls back. *)
    Fixpoint secLeakT_noeq {w : World} {σ} (t : Term w σ) : bool :=
      match t with
      | term_val _ v => true
      | term_binop op t1 t2 =>
          (secLeakT_noeq t1 && secLeakT_noeq t2) || pathconditions_contains_secLeakT (wco w) t
      | term_unop op t1 => secLeakT_noeq t1 || pathconditions_contains_secLeakT (wco w) t
      | _ => pathconditions_contains_secLeakT (wco w) t
      end.

    Lemma secLeakT_noeq_spec {w : World} {σ} (t : Term w σ) :
      secLeakT_noeq t -> ⊢ instpred (formula_secLeak t) .
    Proof.
      induction t; cbn [secLeakT_noeq]; intros H;
        try (iApply pathconditions_contains_secLeakT_spec; by iPureIntro).
      - iApply instpred_formula_secLeak_val.
      - apply Bool.orb_prop_elim in H as [H|H].
        + apply Bool.andb_prop_elim in H as [H1 H2].
          change (⊢ instpred_formula_secLeak (term_binop op t1 t2)).
          iApply instpred_formula_secLeak_binop.
          iSplit; [iApply (IHt1 H1)|iApply (IHt2 H2)].
        + iApply pathconditions_contains_secLeakT_spec; by iPureIntro.
      - apply Bool.orb_prop_elim in H as [H|H].
        + change (⊢ instpred_formula_secLeak (term_unop op t)).
          iApply instpred_formula_secLeak_unop.
          iApply (IHt H).
        + iApply pathconditions_contains_secLeakT_spec; by iPureIntro.
    Qed.

    Lemma secLeakT_noeq_inst {w : World} {σ} (a : Term w σ) (ι : Valuation w) :
      Is_true (secLeakT_noeq a) -> instprop (wco w) ι -> secLeak (inst a ι).
    Proof.
      intros H Hw. apply secLeakT_noeq_spec in H. destruct H as [H].
      specialize (H ι Hw I). cbn in H. exact H.
    Qed.

    (* R4 (PLAN-relval-pair): an equation `t = u` of the path condition with u
       public makes t public, `secLeak u ∧ t = u ⊢ secLeak t`.  ONE hop: u is
       judged by secLeakT_noeq, so there is no closure over equalities, and a
       call costs one more wco walk. *)
    Equations(noind) formula_propeq_other {Σ σ} (f : Formula Σ) (t : Term Σ σ) : option (Term Σ σ) :=
      formula_propeq_other (@formula_propeq _ τ a b) t with eq_dec σ τ => {
          formula_propeq_other (@formula_propeq _ _ a b) t (left eq_refl) :=
            if Term_eqb t a then Some b else if Term_eqb t b then Some a else None;
          formula_propeq_other (@formula_propeq _ _ a b) t (right _) := None
        };
      formula_propeq_other _ _ := None.

    Lemma formula_propeq_other_spec {Σ σ} (f : Formula Σ) (t u : Term Σ σ) (ι : Valuation Σ) :
      formula_propeq_other f t = Some u -> instprop f ι -> inst t ι = inst u ι.
    Proof.
      destruct f; simp formula_propeq_other; try discriminate.
      destruct eq_dec; subst; cbn; [|discriminate].
      repeat match goal with
        | |- context[Term_eqb ?x ?y] => destruct (Term_eqb_spec x y); subst
        end.
      all: intros H; try discriminate; injection H as <-; cbn;
        first [ intros E; exact E | intros E; symmetry; exact E | intros _; reflexivity ].
    Qed.

    Fixpoint pathconditions_eq_public {w : World} {σ} (C : PathCondition w) (t : Term w σ) : bool :=
      match C with
      | [ctx] => false
      | C ▻ F => match formula_propeq_other F t with
                 | Some u => secLeakT_noeq u
                 | None => false
                 end || pathconditions_eq_public C t
      end.

    Lemma pathconditions_eq_public_inst {w : World} {σ} (C : PathCondition w) (t : Term w σ)
      (ι : Valuation w) :
      Is_true (pathconditions_eq_public C t) -> instprop C ι -> instprop (wco w) ι ->
      secLeak (inst t ι).
    Proof.
      induction C as [|C IH F]; cbn [pathconditions_eq_public]; [intros []|].
      intros H HC Hw. apply instprop_snoc in HC as [HC HF].
      apply Bool.orb_prop_elim in H as [H|H]; [|exact (IH H HC Hw)].
      destruct (formula_propeq_other F t) as [u|] eqn:E; [|destruct H].
      rewrite (@formula_propeq_other_spec _ _ F t u ι E HF). exact (@secLeakT_noeq_inst _ _ u ι H Hw).
    Qed.

    (* the base case of secLeakT: the exact term, or one equation away *)
    Definition secLeak_base {w : World} {σ} (t : Term w σ) : bool :=
      pathconditions_contains_secLeakT (wco w) t || pathconditions_eq_public (wco w) t.

    Lemma secLeak_base_spec {w : World} {σ} (t : Term w σ) :
      secLeak_base t -> ⊢ instpred (formula_secLeak t).
    Proof.
      unfold secLeak_base. intros H. apply Bool.orb_prop_elim in H as [H|H].
      - iApply pathconditions_contains_secLeakT_spec; by iPureIntro.
      - constructor. intros ι Hw _. exact (@pathconditions_eq_public_inst _ _ (wco w) t ι H Hw Hw).
    Qed.

    Fixpoint secLeakT {w : World} {σ} (t : Term w σ) : bool :=
      match t with
      | term_val _ v => true
      | term_binop op t1 t2 => (secLeakT t1 && secLeakT t2) || secLeak_base t
      | term_unop op t1 => secLeakT t1 || secLeak_base t
      | _ => secLeak_base t
      end.

    Lemma secLeakT_spec {w : World} {σ} (t : Term w σ) :
      secLeakT t -> ⊢ instpred (formula_secLeak t) .
    Proof.
      induction t; cbn [secLeakT]; intros H; try (apply secLeak_base_spec; exact H).
      - iApply instpred_formula_secLeak_val.
      - apply Bool.orb_prop_elim in H as [H|H].
        + apply Bool.andb_prop_elim in H as [H1 H2].
          change (⊢ instpred_formula_secLeak (term_binop op t1 t2)).
          iApply instpred_formula_secLeak_binop.
          iSplit; [iApply (IHt1 H1)|iApply (IHt2 H2)].
        + apply secLeak_base_spec; exact H.
      - apply Bool.orb_prop_elim in H as [H|H].
        + change (⊢ instpred_formula_secLeak (term_unop op t)).
          iApply instpred_formula_secLeak_unop.
          iApply (IHt H).
        + apply secLeak_base_spec; exact H.
    Qed.

    Definition Term_eqb_relval {w : World} [σ] (t1 t2 : Term w σ) : bool :=
      match secLeakT t1, secLeakT t2 with
      | true , true => Term_eqb t1 t2
      | _ , _ => false
      end.

    #[local] Set Equations With UIP.

    Lemma Term_eqb_relval_spec {w : World} {σ} (t1 t2 : Term w σ) :
      reflect (secLeakT t1 /\ secLeakT t2 /\ t1 = t2) (Term_eqb_relval t1 t2).
    Proof.
      unfold Term_eqb_relval.
      destruct (secLeakT t1) as [|] eqn:H1; destruct (secLeakT t2) as [|] eqn:H2;
      try (destruct (Term_eqb_spec t1 t2); subst);
        solve_eqb_spec; tauto.
    Qed.

    #[local] Unset Equations With UIP.

    Notation dlist_propeq t1 t2 := (singleton (formula_propeq t1 t2)).

    Definition simplify_eqb {w : World} (Term_eqb : forall {σ} (t1 t2 : Term w σ), Datatypes.bool) (dlist_eq : ∀ {σ : Ty}, Term w σ → Term w σ → DList w) {σ} (t1 t2 : Term w σ) : DList w :=
      let num t :=
        match t with
        | term_var _       => 1
        | term_val _ _     => 2
        | term_relval _ _  => 3
        | term_binop _ _ _ => 4
        | term_unop _ _    => 5
        | term_tuple _     => 6
        | term_union _ _ _ => 7
        | term_record _ _  => 8
        end%positive in
      if Term_eqb t1 t2
      then empty
      else
        if (num t1 <=? num t2)%positive
        then dlist_eq t1 t2
        else dlist_eq t2 t1.

    Lemma instpred_formula_relop_secLeak_eq' [w : World] [σ] (t1 t2 : STerm σ w) :
      instpred (formula_secLeak t1) -∗
       instpred (formula_secLeak t2) -∗
        instpred_formula_relop bop.eq t1 t2 ∗-∗ eqₚ t1 t2.
    Proof.
      crushPredEntails3; cbn in *.
      + by apply instpred_formula_relop_eqₚ' in H3.
      + unfold instpred_formula_relop. rewrite H3. destruct (inst t2 ι); cbn; auto.
    Qed.

    Lemma instpred_formula_relop_secLeak_eq [w : World] [σ] (t1 t2 : STerm σ w)
      (H1 : secLeakT t1) (H2 : secLeakT t2) :
      instpred (formula_eq t1 t2) ⊣⊢ eqₚ t1 t2.
    Proof.
      cbn.
      apply secLeakT_spec in H1. apply secLeakT_spec in H2.
      by iPoseProof (instpred_formula_relop_secLeak_eq' $! H1 H2) as "H".
    Qed.

    Lemma simplify_eqb_spec [w : World] [σ] (t1 t2 : STerm σ w) :
      instpred (simplify_eqb Term_eqb_relval (fun {σ} t1 t2 => dlist_eq t1 t2) t1 t2) ⊣⊢ instpred (formula_eq t1 t2).
    Proof.
      unfold simplify_eqb.
      destruct (Term_eqb_relval_spec t1 t2); subst; arw.
      {
        destruct a as (H1 & H2 & eq). subst.
        rewrite instpred_formula_relop_secLeak_eq; auto.
        rewrite eqₚ_refl. auto.
      }
      destruct Pos.leb.
      - rewrite <- instpred_dlist_singleton. auto.
      - rewrite instpred_formula_eq_com.
        rewrite <- instpred_dlist_singleton. auto.
    Qed.
    #[local] Hint Rewrite simplify_eqb_spec : uniflogic.

    Lemma simplify_propeqb_spec [w : World] [σ] (t1 t2 : STerm σ w) :
      instpred (simplify_eqb Term_eqb (fun {σ} t1 t2 => dlist_propeq t1 t2) t1 t2) ⊣⊢ instpred (formula_propeq t1 t2).
    Proof.
      unfold simplify_eqb.
      destruct (Term_eqb_spec t1 t2); subst; arw.
      destruct Pos.leb; arw.
    Qed.
    #[local] Hint Rewrite simplify_propeqb_spec : uniflogic.
    #[local] Opaque simplify_eqb.
    
    Section SimplifyEq.

      Context {Σ : World}.
      Variable Term_eqb : forall σ (t1 t2 : Term Σ σ), Datatypes.bool.
      Variable dlist_eq : ∀ {σ : Ty}, Term Σ σ → Term Σ σ → DList Σ.

      Definition simplify_eq_binop_default_val {σ1 σ2 σ} (op : BinOp σ1 σ2 σ)
        (t1 : Term Σ σ1) (t2 : Term Σ σ2) (v : Val σ) : DList Σ :=
        dlist_eq (term_val σ v) (term_binop op t1 t2).

      Definition simplify_eq_unop_default_val {σ1 σ2} (op : UnOp σ1 σ2)
        (t : Term Σ σ1) (v : Val σ2) : DList Σ :=
        dlist_eq (term_val _ v) (term_unop op t).

      Definition simplify_eq_binop_and_val (t1 t2 : Term Σ ty.bool)
        (v : Val ty.bool) : DList Σ :=
        if v
        then simplify_bool (term_binop bop.and t1 t2)
        else simplify_bool_neg (term_binop bop.and t1 t2). 

      Definition simplify_eq_binop_or_val (t1 t2 : Term Σ ty.bool)
        (v : Val ty.bool) : DList Σ :=
        if v
        then simplify_bool (term_binop bop.or t1 t2)
        else simplify_bool_neg (term_binop bop.or t1 t2).

      Definition simplify_eq_unop_not_val (t : Term Σ ty.bool) (v : Val ty.bool) :
        DList Σ :=
        if v then simplify_bool_neg t else simplify_bool t.

      Definition simplify_eq_binop_relop_val {σ} (op : RelOp σ)
        (t1 t2 : Term Σ σ) (v : Val ty.bool) : DList Σ :=
        if v
        then singleton (formula_relop op t1 t2)
        else singleton (formula_relop_neg op t1 t2).

      Section WithSimplifyEqVal.

        Variable simplify_eq_val : ∀ [σ] (t : Term Σ σ) (v : Val σ), DList Σ.

        Definition simplify_eq_binop_pair_val {σ1 σ2} (t1 : Term Σ σ1)
          (t2 : Term Σ σ2) (v : Val (ty.prod σ1 σ2)) : DList Σ :=
          let (v1, v2) := v in
          cat (simplify_eq_val t1 v1) (simplify_eq_val t2 v2).

        Definition simplify_eq_binop_cons_val {σ} (t1 : Term Σ σ)
          (t2 : Term Σ (ty.list σ)) (v : Val (ty.list σ)) : DList Σ :=
          match v with
          | nil        => error
          | cons vh vl => cat (simplify_eq_val t1 vh) (simplify_eq_val t2 vl)
          end.

        Definition simplify_eq_binop_bvapp_val {m n} (t1 : Term Σ (ty.bvec m))
          (t2 : Term Σ (ty.bvec n)) (v : Val (ty.bvec (m + n))) : DList Σ :=
          let (v1,v2) := bv.appView _ _ v in
          cat (simplify_eq_val t1 v1) (simplify_eq_val t2 v2).

        Definition simplify_eq_binop_bvcons_val {m} (t1 : Term Σ ty.bool)
          (t2 : Term Σ (ty.bvec m)) (v : Val (ty.bvec (S m))) : DList Σ :=
          let (v1,v2) := bv.view v in
          cat (simplify_eq_val t1 v1) (simplify_eq_val t2 v2).

        (* Simplifies equations of the form (term_binop op t1 t2 = v). *)
        Definition simplify_eq_binop_val [σ σ1 σ2] (op : BinOp σ1 σ2 σ) :
          Term Σ σ1 → Term Σ σ2 → Val σ → DList Σ :=
          match op with
          | bop.plus => simplify_eq_binop_default_val bop.plus
          | bop.minus => simplify_eq_binop_default_val bop.minus
          | bop.times => simplify_eq_binop_default_val bop.times
          | bop.land => simplify_eq_binop_default_val bop.land
          | bop.and => simplify_eq_binop_and_val
          | bop.or => simplify_eq_binop_or_val
          | bop.pair => simplify_eq_binop_pair_val
          | bop.cons => simplify_eq_binop_cons_val
          | bop.append => simplify_eq_binop_default_val bop.append
          | bop.shiftr => simplify_eq_binop_default_val bop.shiftr
          | bop.shiftl => simplify_eq_binop_default_val bop.shiftl
          | bop.bvadd => simplify_eq_binop_default_val bop.bvadd
          | bop.bvsub => simplify_eq_binop_default_val bop.bvsub
          | bop.bvmul => simplify_eq_binop_default_val bop.bvmul
          | bop.bvand => simplify_eq_binop_default_val bop.bvand
          | bop.bvor => simplify_eq_binop_default_val bop.bvor
          | bop.bvxor => simplify_eq_binop_default_val bop.bvxor
          | bop.coalesce => simplify_eq_binop_default_val bop.coalesce
          | bop.mulx => simplify_eq_binop_default_val bop.mulx
          | bop.bvapp => simplify_eq_binop_bvapp_val
          | bop.bvcons => simplify_eq_binop_bvcons_val
          | bop.update_vector_subrange s l =>
              simplify_eq_binop_default_val (bop.update_vector_subrange s l)
          | bop.relop op => simplify_eq_binop_relop_val op
          end.

        Definition simplify_eq_unop_inl_val {σ1 σ2} (t : Term Σ σ1)
          (v : Val (ty.sum σ1 σ2)) : DList Σ :=
          match v with
          | inl vl => simplify_eq_val t vl
          | inr _  => error
          end.

        Definition simplify_eq_unop_inr_val {σ1 σ2} (t : Term Σ σ2)
          (v : Val (ty.sum σ1 σ2)) : DList Σ :=
          match v with
          | inl _  => error
          | inr vr => simplify_eq_val t vr
          end.

        Definition simplify_eq_unop_neg_val (t : Term Σ ty.int) (v : Val ty.int) :
          DList Σ := simplify_eq_val t (Z.opp v).

        Definition simplify_eq_unop_signed_val {n} (t : Term Σ (ty.bvec n))
          (v : Val ty.int) : DList Σ :=
          if ((- 2 ^ (Z.of_nat n) <=? 2 * v) &&& (2 * v <? 2 ^ Z.of_nat n))%Z
          then simplify_eq_val t (bv.of_Z v)
          else error.

        Definition simplify_eq_unop_unsigned_val {n} (t : Term Σ (ty.bvec n))
          (v : Val ty.int) : DList Σ :=
          if ((0 <=? v) &&& (v <? 2 ^ Z.of_nat n))%Z
          then simplify_eq_val t (bv.of_Z v)
          else error.

        Definition simplify_eq_unop_val {σ1 σ2} (op : UnOp σ1 σ2) :
          Term Σ σ1 → Val σ2 → DList Σ :=
          match op with
          | uop.inl => simplify_eq_unop_inl_val
          | uop.inr => simplify_eq_unop_inr_val
          | uop.neg => simplify_eq_unop_neg_val
          | uop.not => simplify_eq_unop_not_val
          | uop.rev => simplify_eq_unop_default_val uop.rev
          | uop.sext => simplify_eq_unop_default_val uop.sext
          | uop.zext => simplify_eq_unop_default_val uop.zext
          | uop.get_slice_int => simplify_eq_unop_default_val uop.get_slice_int
          | uop.signed => simplify_eq_unop_signed_val
          | uop.unsigned => simplify_eq_unop_unsigned_val
          | uop.truncate m => simplify_eq_unop_default_val (uop.truncate m)
          | uop.vector_subrange s l => simplify_eq_unop_default_val (uop.vector_subrange s l)
          | uop.bvnot => simplify_eq_unop_default_val uop.bvnot
          | uop.bvdrop m => simplify_eq_unop_default_val (uop.bvdrop m)
          | uop.bvtake m => simplify_eq_unop_default_val (uop.bvtake m)
          | uop.negate => simplify_eq_unop_default_val uop.negate
          | uop.expand => simplify_eq_unop_default_val uop.expand
          | uop.regroup => simplify_eq_unop_default_val uop.regroup
          end.

        Definition simplify_eq_tuple_val {σs} (ts : Env (Term Σ) σs)
          (vs : Val (ty.tuple σs)) : DList Σ :=
          env.Env_rect
            (fun σs _ => Val (ty.tuple σs) → DList Σ)
            (fun _ => empty)
            (fun τs _ IHts τ t (vτsτ : Val (ty.tuple (τs ▻ τ))) =>
               let (vτs, vτ) := vτsτ in
               cat (IHts vτs) (simplify_eq_val t vτ))
            ts vs.

        Definition simplify_eq_union_val [U] [K1 : unionk U]
          (t1 : Term Σ (unionk_ty U K1)) (v2 : Val (ty.union U)) : DList Σ :=
          let (K2, v2) := unionv_unfold U v2 in
          match eq_dec K1 K2 with
          | left e  => let v2' := eq_rect_r (fun K1 => Val (unionk_ty U K1)) v2 e in
                       simplify_eq_val t1 v2'
          | right _ => error
          end.

        Definition simplify_eq_record_val (R : recordi)
          (ts : NamedEnv (Term Σ) (recordf_ty R)) (v : Val (ty.record R)) :
          DList Σ :=
          env.Env_rect
            (fun Δ _ => NamedEnv Val Δ → DList Σ)
            (fun _ => empty)
            (fun Δ _ IHts b t vs =>
               let (vsΔ,vb) := env.view vs in
               cat (IHts vsΔ) (simplify_eq_val t vb))
            ts
            (recordv_unfold R v).

      End WithSimplifyEqVal.

      Fixpoint simplify_eq_val [σ] (t : Term Σ σ) (v : Val σ) : DList Σ :=
        match t with
        | term_var x          => fun _ => dlist_eq t (term_val _ v)
        | term_val σ v        => fun v' => if eq_dec v v' then empty else error
        | term_relval σ rv    => fun v' => if eq_dec rv (SyncVal v') then empty else error
        | term_binop op t1 t2 => simplify_eq_binop_val simplify_eq_val op t1 t2
        | term_unop op t      => simplify_eq_unop_val simplify_eq_val op t
        | term_tuple ts       => simplify_eq_tuple_val simplify_eq_val ts
        | term_union U K t    => simplify_eq_union_val simplify_eq_val t
        | term_record R ts    => simplify_eq_record_val simplify_eq_val R ts
        end v.

      Definition simplify_eq_relval [σ] (t : Term Σ σ) (rv : RelVal σ) : DList Σ :=
        let default := dlist_eq t (term_relval _ rv) in
        match t with
        | term_var x          => fun _ => default
        | term_val σ v        => fun rv' => if eq_dec (SyncVal v) rv' then empty else error
        | term_relval σ rv    => fun rv' => if eq_dec rv rv' then empty else error
        | term_binop op t1 t2 => (* simplify_eq_binop_val simplify_eq_val op t1 t2 *) fun rv' => default
        | term_unop op t      => (* simplify_eq_unop_val simplify_eq_val op t *) fun rv' => default
        | term_tuple ts       => (* simplify_eq_tuple_val simplify_eq_val ts *) fun rv' => default
        | term_union U K t    => (* simplify_eq_union_val simplify_eq_val t *) fun rv' => default
        | term_record R ts    => (* simplify_eq_record_val simplify_eq_val R ts *) fun rv' => default
        end rv.

      Definition simplify_eq_binop_default {σ1 σ2 σ} (op : BinOp σ1 σ2 σ)
        (t1 : Term Σ σ1) (t2 : Term Σ σ2) (t : Term Σ σ) : DList Σ :=
        dlist_eq (term_binop op t1 t2) t.

      Definition simplify_eq_binop_minus_default
        (t1 : Term Σ ty.int) (t2 : Term Σ ty.int) (t : Term Σ ty.int) : DList Σ :=
        dlist_eq (term_val ty.int 0) (term_minus t (term_minus t1 t2)).

      Definition simplify_eq_binop_minus (tl1 : Term Σ ty.int)
        (tl2 : Term Σ ty.int) (tr : Term Σ ty.int) : DList Σ :=
          Term_int_case (fun _ => DList Σ)
            (fun (*var*) _ _ => simplify_eq_binop_minus_default tl1 tl2 tr)
            (fun (*val*) v =>
               match v with
               | 0%Z => dlist_eq tl1 tr
               | _ => simplify_eq_binop_minus_default tl1 tl2 tr
               end
            )
            (fun (*relval*) rv => simplify_eq_binop_minus_default tl1 tl2 tr) (* TODO: A simplify_eq_relval might be warranted in the future *)
            (fun (*plus*) tr1 tr2 =>
               simplify_eq_binop_minus_default tl1 tl2 tr)
            (fun (*minus*) tr1 tr2 =>
               simplify_eq_binop_minus_default tl1 tl2 tr)
            (fun (*times*) tr1 tr2 => simplify_eq_binop_minus_default tl1 tl2 tr)
            (fun (*land*) tr1 tr2 => simplify_eq_binop_minus_default tl1 tl2 tr)
            (fun (*neg*) tr' => simplify_eq_binop_minus_default tl1 tl2 tr)
            (fun (*signed*) n _ => simplify_eq_binop_minus_default tl1 tl2 tr)
            (fun (*unsigned*) n _ => simplify_eq_binop_minus_default tl1 tl2 tr)
            tl2.

      Definition simplify_eq_binop_times (tl1 : Term Σ ty.int)
        (tl2 : Term Σ ty.int) (tr : Term Σ ty.int) : DList Σ :=
        dlist_eq (term_val ty.int 0) (term_minus tr (term_times tl1 tl2)).


      Definition simplify_eq_unop_default {σ1 σ2} (op : UnOp σ1 σ2)
        (t1 : Term Σ σ1) (t : Term Σ σ2) : DList Σ :=
        dlist_eq (term_unop op t1) t.

      Section WithSimplifyEq.

        Variable simplify_eq : forall [σ] (t1 t2 : Term Σ σ), DList Σ.

        Definition simplify_eq_binop_plus (tl1 : Term Σ ty.int)
          (tl2 : Term Σ ty.int) (tr : Term Σ ty.int) : DList Σ :=
          let default := dlist_eq tr (term_plus tl1 tl2) in
          Term_int_case (fun _ => DList Σ)
            (fun (*var*) _ _ => default)
            (fun (*val*) v => simplify_eq_val (term_plus tl1 tl2) v)
            (fun (*relval*) rv => default) (* TODO: A simplify_eq_relval might be warranted in the future *)
            (fun (*plus*) tr1 tr2 =>
               if Term_eqb_relval tl1 tr1 then simplify_eq tl2 tr2 else
                 if Term_eqb_relval tl2 tr2 then simplify_eq tl1 tr1 else
                   if Term_eqb_relval tl1 tr2 then simplify_eq tl2 tr1 else
                     if Term_eqb_relval tl2 tr1 then simplify_eq tl1 tr2 else
                       default)
            (fun (*minus*) tr1 tr2 =>
               if Term_eqb_relval tl1 tr1 then simplify_eq tl2 (term_neg tr2) else
                 if Term_eqb_relval tl2 tr1 then simplify_eq tl1 (term_neg tr2) else
                   default)
            (fun (*times*) tr1 tr2 => default)
            (fun (*land*) tr1 tr2 => default)
            (fun (*neg*) tr' => default)
            (fun (*signed*) n _ => default)
            (fun (*unsigned*) n _ => default)
            tr.

        Definition simplify_eq_binop_and (tl1 : Term Σ ty.bool)
          (tl2 : Term Σ ty.bool) (tr : Term Σ ty.bool) : DList Σ :=
          let tl := term_and tl1 tl2 in
          let default := dlist_eq tl tr in
          Term_bool_case (fun _ => DList Σ)
            (fun (*var*) _ _ => dlist_eq tr tl)
            (fun (*val*) v => simplify_eq_val tl v)
            (fun (*val*) v => default)
            (fun (*and*) tr1 tr2 =>
               if Term_eqb tl1 tr1 && Term_eqb tl2 tr2
               then empty else default)
            (fun (*or*) _ _ => default)
            (fun (*relop*) _ _ _ _ => default)
            (fun (*not*) _ => default)
            tr.

        Definition simplify_eq_binop_or (tl1 : Term Σ ty.bool)
          (tl2 : Term Σ ty.bool) (tr : Term Σ ty.bool) : DList Σ :=
          let tl := term_or tl1 tl2 in
          let default := dlist_eq tl tr in
          Term_bool_case (fun _ => DList Σ)
            (fun (*var*) _ _ => dlist_eq tr tl)
            (fun (*val*) v => simplify_eq_val tl v)
            (fun (*relval*) v => default)
            (fun (*and*) _ _ => default)
            (fun (*or*) tr1 tr2 =>
               if Term_eqb tl1 tr1 && Term_eqb tl2 tr2
               then empty else default)
            (fun (*relop*) _ _ _ _ => default)
            (fun (*not*) _ => default)
            tr.

        Definition simplify_eq_binop_pair {σ1 σ2} (t1 : Term Σ σ1)
          (t2 : Term Σ σ2) (t : Term Σ (ty.prod σ1 σ2)) : DList Σ :=
          let tl := term_pair t1 t2 in
          let default := dlist_eq tl t in
          Term_prod_case (fun _ => DList Σ)
            (fun (*var*) _ _      => dlist_eq t (term_pair t1 t2))
            (fun (*val*) v        => simplify_eq_val (term_pair t1 t2) v)
            (fun (*relval*) v     => default)
            (fun (*pair*) t1' t2' => cat (simplify_eq t1 t1') (simplify_eq t2 t2'))
            t.

        Definition simplify_eq_binop_cons {σ} (t1 : Term Σ σ)
          (t2 : Term Σ (ty.list σ)) (t : Term Σ (ty.list σ)) : DList Σ :=
          let default := dlist_eq t (term_cons t1 t2) in
          Term_list_case (fun _ => DList Σ)
            (fun (*var*) _ _ => default)
            (fun (*val*) v => simplify_eq_val (term_cons t1 t2) v)
            (fun (*relval*) rv => default)
            (fun (*cons*) t1' t2' => cat (simplify_eq t1 t1') (simplify_eq t2 t2'))
            (fun (*append*) _ _ => dlist_eq (term_cons t1 t2) t)
            (fun (*rev*) _ => dlist_eq (term_cons t1 t2) t)
            (fun (*regroup*) _ _ => dlist_eq (term_cons t1 t2) t)
            t.

        Definition simplify_eq_binop_append {σ} (tl1 : Term Σ (ty.list σ))
          (tl2 : Term Σ (ty.list σ)) (tr : Term Σ (ty.list σ)) : DList Σ :=
          let default := dlist_eq tr (term_append tl1 tl2) in
          Term_list_case (fun _ => DList Σ)
            (fun (*var*) _ _ => default)
            (fun (*val*) v => simplify_eq_val (term_append tl1 tl2) v)
            (fun (*relval*) v => default)
            (fun (*cons*) t1' t2' => dlist_eq tr (term_append tl1 tl2))
            (fun (*append*) tr1 tr2 =>
               if Term_eqb tl1 tr1 then simplify_eq tl2 tr2 else
                 if Term_eqb tl2 tr2 then simplify_eq tl1 tr1 else
                   dlist_eq (term_append tl1 tl2) tr)
            (fun (*rev*) _ => dlist_eq (term_append tl1 tl2) tr)
            (fun (*regroup*) _ _ => dlist_eq (term_append tl1 tl2) tr)
            tr.

        Definition simplify_eq_binop_bvapp' {m n} (t1 : Term Σ (ty.bvec m))
          (t2 : Term Σ (ty.bvec n)) mn (t : Term Σ (ty.bvec mn))
          (e : m + n = mn) : DList Σ :=
          let default {mn} (_ : m + n = mn) : DList Σ :=
            dlist_eq (term_bvapp t1 t2)
              (eq_rect_r (fun l => Term Σ (ty.bvec l)) t e) in
          Term_bvec_case (fun mn t => m + n = mn -> DList Σ)
            (fun (*var*) _ _ _ _ =>
               dlist_eq
                 (eq_rect_r (fun l => Term Σ (ty.bvec l)) t e)
                 (term_bvapp t1 t2))
            (fun (*val*) n v e =>
               simplify_eq_val (term_bvapp t1 t2)
                 (eq_rect_r (fun l => Val (ty.bvec l)) v e))
            (fun (*relval*) n v e => default e)
            (fun (*bvadd*) _ _ _ => default)
            (fun (*bvsub*) _ _ _ => default)
            (fun (*bvmul*) _ _ _ => default)
            (fun (*bvand*) _ _ _ => default)
            (fun (*bvor*) _ _ _ => default)
            (fun (*bvxor*) _ _ _ => default)
            (fun (*shiftr*) _ _ _ _ => default)
            (fun (*shiftl*) _ _ _ _ => default)
            (fun (*bvapp*) m' n' =>
               match eq_dec m m' with
               | left em =>
                   match em with
                   | eq_refl =>
                       fun t1' t2' e' =>
                         let en  : n = n' :=
                           transparent.nat_add_cancel_l n n' m e' in
                         let t2' : Term Σ (ty.bvec n) :=
                           eq_rect_r (fun l => Term Σ (ty.bvec l)) t2' en in
                         cat
                           (simplify_eq t1 t1')
                           (simplify_eq t2 t2')
                   end
               | right _ => fun _ _ => default
               end)
            (fun (*bvcons*) _ _ _ => default)
            (fun (*update_vector_subrange*) _ _ _ _ _ _ => default)
            (fun (*bvnote*) _ _ => default)
            (fun (*negate*) _ _ => default)
            (fun (*sext*) _ _ _ _ => default)
            (fun (*zext*) _ _ _ _ => default)
            (fun (*get_slice_int*) _ _ => default)
            (fun (*truncate*) _ _ _ _ => default)
            (fun (*vector_subrange*) _ _ _ _ _ => default)
            (fun (*bvdrop*) _ _ _ => default)
            (fun (*bvtake*) _ _ _ => default)
            (fun (*expand*) _ _ => default)
            (fun (*coalesce*) _ _ _ => default)
            (fun (*mulx*) _ _ _ => default)
            t e.

        Definition simplify_eq_binop_bvapp {m n} (t1 : Term Σ (ty.bvec m))
          (t2 : Term Σ (ty.bvec n)) (t : Term Σ (ty.bvec (m + n))) : DList Σ :=
          simplify_eq_binop_bvapp' t1 t2 t eq_refl.

        Definition simplify_eq_binop_bvcons' {m} (t1 : Term Σ ty.bool)
          (t2 : Term Σ (ty.bvec m)) sm (t : Term Σ (ty.bvec sm))
          (e : S m = sm) : DList Σ :=
          let default {sm} (_ : S m = sm) : DList Σ :=
            dlist_eq (term_bvcons t1 t2)
              (eq_rect_r (fun l => Term Σ (ty.bvec l)) t e) in
          Term_bvec_case (fun sm t => S m = sm -> DList Σ)
            (fun (*var*) _ _ _ _ =>
               dlist_eq
                 (eq_rect_r (fun l => Term Σ (ty.bvec l)) t e)
                 (term_bvcons t1 t2))
            (fun (*val*) n v e =>
               simplify_eq_val (term_bvcons t1 t2)
                 (eq_rect_r (fun l => Val (ty.bvec l)) v e))
            (fun (*relval*) n v e => default e)
            (fun (*bvadd*) _ _ _ => default)
            (fun (*bvsub*) _ _ _ => default)
            (fun (*bvmul*) _ _ _ => default)
            (fun (*bvand*) _ _ _ => default)
            (fun (*bvor*) _ _ _ => default)
            (fun (*bvxor*) _ _ _ => default)
            (fun (*shiftr*) _ _ _ _ => default)
            (fun (*shiftl*) _ _ _ _ => default)
            (fun (*bvapp*) _ _ _ _ => default)
            (fun (*bvcons*) m' t1' t2' e2 =>
               let e' : m = m' := eq_add_S m m' e2 in
               let t2' := eq_rect_r (fun l => Term Σ (ty.bvec l)) t2' e' in
               cat (simplify_eq t1 t1') (simplify_eq t2 t2'))
            (fun (*update_vector_subrange*) _ _ _ _ _ _ => default)
            (fun (*bvnote*) _ _ => default)
            (fun (*negate*) _ _ => default)
            (fun (*sext*) _ _ _ _ => default)
            (fun (*zext*) _ _ _ _ => default)
            (fun (*get_slice_int*) _ _ => default)
            (fun (*truncate*) _ _ _ _ => default)
            (fun (*vector_subrange*) _ _ _ _ _ => default)
            (fun (*bvdrop*) _ _ _ => default)
            (fun (*bvtake*) _ _ _ => default)
            (fun (*expand*) _ _ => default)
            (fun (*coalesce*) _ _ _ => default)
            (fun (*mulx*) _ _ _ => default)
            t e.

        Definition simplify_eq_binop_bvcons {m} (t1 : Term Σ ty.bool)
          (t2 : Term Σ (ty.bvec m)) (t : Term Σ (ty.bvec (S m))) : DList Σ :=
          simplify_eq_binop_bvcons' t1 t2 t eq_refl.

        Fixpoint simplify_eq_relop {σ} (op : RelOp σ) (tl1 tl2 : Term Σ σ)
          (tr : Term Σ ty.bool) {struct tr} : DList Σ :=
          let tl := term_binop (bop.relop op) tl1 tl2 in
          let default : DList Σ := dlist_eq tr tl in
          Term_bool_case (fun _ => DList Σ)
            (fun (*var*) _ _ => default)
            (fun (*val*) v => simplify_eq_val tl v)
            (fun (*relval*) rv => simplify_eq_relval tl rv)
            (fun (*and*) tr1 tr2 => default)
            (fun (*or*) tr1 tr2 => default)
            (fun (*relop*) _ op tr1 tr2 => default)
            (fun (*not*) tr' =>
               match op with
               | bop.eq     => fun tl1 tl2 => simplify_eq_relop bop.neq tl1 tl2 tr'
               | bop.neq    => fun tl1 tl2 => simplify_eq_relop bop.eq tl1 tl2 tr'
               | bop.le     => fun tl1 tl2 => simplify_eq_relop bop.lt tl2 tl1 tr'
               | bop.lt     => fun tl1 tl2 => simplify_eq_relop bop.le tl2 tl1 tr'
               | bop.bvsle  => fun tl1 tl2 => simplify_eq_relop bop.bvslt tl2 tl1 tr'
               | bop.bvslt  => fun tl1 tl2 => simplify_eq_relop bop.bvsle tl2 tl1 tr'
               | bop.bvule  => fun tl1 tl2 => simplify_eq_relop bop.bvult tl2 tl1 tr'
               | bop.bvult  => fun tl1 tl2 => simplify_eq_relop bop.bvule tl2 tl1 tr'
               end tl1 tl2)
            tr.

        Definition simplify_eq_binop {σ1 σ2 σ} (op : BinOp σ1 σ2 σ) :
          Term Σ σ1 -> Term Σ σ2 -> Term Σ σ -> DList Σ :=
          match op in BinOp σ1 σ2 σ
                return Term Σ σ1 -> Term Σ σ2 -> Term Σ σ -> DList Σ
          with
          | bop.plus => simplify_eq_binop_plus
          | bop.minus => simplify_eq_binop_minus
          | bop.times => simplify_eq_binop_times
          | bop.land => simplify_eq_binop_default bop.land
          | bop.and => simplify_eq_binop_and
          | bop.or => simplify_eq_binop_or
          | bop.pair => simplify_eq_binop_pair
          | bop.cons => simplify_eq_binop_cons
          | bop.append => simplify_eq_binop_append
          | bop.shiftr => simplify_eq_binop_default bop.shiftr
          | bop.shiftl => simplify_eq_binop_default bop.shiftl
          | bop.bvadd => simplify_eq_binop_default bop.bvadd
          | bop.bvsub => simplify_eq_binop_default bop.bvsub
          | bop.bvmul => simplify_eq_binop_default bop.bvmul
          | bop.bvand => simplify_eq_binop_default bop.bvand
          | bop.bvor => simplify_eq_binop_default bop.bvor
          | bop.bvxor => simplify_eq_binop_default bop.bvxor
          | bop.coalesce => simplify_eq_binop_default bop.coalesce
          | bop.mulx => simplify_eq_binop_default bop.mulx
          | bop.bvapp => simplify_eq_binop_bvapp
          | bop.bvcons => simplify_eq_binop_bvcons
          | bop.update_vector_subrange s l =>
              simplify_eq_binop_default (bop.update_vector_subrange s l)
          | bop.relop rop => simplify_eq_relop rop
          end.

        (* propeq through the injective constructors.  On the RelVal pair,
           `c a b = c a' b'` holds iff `a = a'` and `b = b'` (both projections),
           so decomposing is exact, as simplify_eq_binop does for relop eq.
           Without it `h :: hs = x :: xs` stays one opaque equation and
           unification never substitutes the head.  Every other operator
           stays opaque. *)
        Definition simplify_propeq_binop {σ1 σ2 σ} (op : BinOp σ1 σ2 σ) :
          Term Σ σ1 -> Term Σ σ2 -> Term Σ σ -> DList Σ :=
          match op in BinOp σ1 σ2 σ
                return Term Σ σ1 -> Term Σ σ2 -> Term Σ σ -> DList Σ
          with
          | bop.pair => simplify_eq_binop_pair
          | bop.cons => simplify_eq_binop_cons
          | bop.bvapp => simplify_eq_binop_bvapp
          | bop.bvcons => simplify_eq_binop_bvcons
          | op => fun t1 t2 tr =>
                    simplify_eqb Term_eqb (fun {σ} t1 t2 => dlist_eq t1 t2)
                      (term_binop op t1 t2) tr
          end.

        Definition simplify_eq_unop_inl {σ1 σ2} (t1 : Term Σ σ1)
          (t : Term Σ (ty.sum σ1 σ2)) : DList Σ :=
          let default := simplify_eq_unop_default uop.inl t1 t in
          Term_sum_case (fun _ => DList Σ)
            (fun (*var*) x _ => default)
            (fun (*val*) v   => simplify_eq_val (term_inl t1) v)
            (fun (*relval*) v   => default)
            (fun (*inl*) t1' => simplify_eq t1 t1')
            (fun (*inr*) t2  => error)
            t.

        Definition simplify_eq_unop_inr {σ1 σ2} (t2 : Term Σ σ2)
          (t : Term Σ (ty.sum σ1 σ2)) : DList Σ :=
          let default := simplify_eq_unop_default uop.inr t2 t in
          Term_sum_case (fun _ => DList Σ)
            (fun (*var*) x _ => default)
            (fun (*val*) v   => simplify_eq_val (term_inr t2) v)
            (fun (*val*) v   => default)
            (fun (*inl*) t1  => error)
            (fun (*inr*) t2' => simplify_eq t2 t2')
            t.

        Definition simplify_eq_unop_get_slice_int {m} (tl : Term Σ ty.int)
          (tr : Term Σ (ty.bvec m)) : DList Σ :=
          let tl := term_get_slice_int tl in
          if Term_eqb tl tr then empty else dlist_eq tl tr.

        Definition simplify_eq_unop_signed {m} (tl : Term Σ (ty.bvec m))
          (tr : Term Σ ty.int) : DList Σ :=
          let default := dlist_eq (term_val ty.int 0)
                           (term_minus tr (term_signed tl)) in
          Term_int_case (fun _ => DList Σ)
            (fun (*var*) _ _ => default)
            (fun (*val*) v => simplify_eq_val (term_signed tl) v)
            (fun (*relval*) v => default)
            (fun (*plus*) tr1 tr2 => default)
            (fun (*minus*) tr1 tr2 => default)
            (fun (*times*) tr1 tr2 => default)
            (fun (*land*) tr1 tr2 => default)
            (fun (*neg*) tr' => default)
            (fun (*signed*) n =>
               match eq_dec m n with
               | left e => match e with eq_refl => simplify_eq tl end
               | right _ => fun _ => default
               end)
            (fun (*unsigned*) n tr' => default)
            tr.

        Definition simplify_propeq_unop_signed {m} (tl : Term Σ (ty.bvec m))
          (tr : Term Σ ty.int) : DList Σ :=
          let default := dlist_eq (term_signed tl) tr in
          Term_int_case (fun _ => DList Σ)
            (fun (*var*) _ _ => default)
            (fun (*val*) v => default (* simplify_eq_val (term_signed tl) v *))
            (fun (*relval*) v => default)
            (fun (*plus*) tr1 tr2 => default)
            (fun (*minus*) tr1 tr2 => default)
            (fun (*times*) tr1 tr2 => default)
            (fun (*land*) tr1 tr2 => default)
            (fun (*neg*) tr' => default)
            (fun (*signed*) n =>
               match eq_dec m n with
               | left e => match e with eq_refl => simplify_eq tl end
               | right _ => fun _ => default
               end)
            (fun (*unsigned*) n tr' => default)
            tr.

        Definition simplify_eq_unop {σ1 σ2} (op : UnOp σ1 σ2) :
          Term Σ σ1 -> Term Σ σ2 -> DList Σ :=
          match op with
          | uop.inl => simplify_eq_unop_inl
          | uop.inr => simplify_eq_unop_inr
          | uop.neg => simplify_eq_unop_default uop.neg
          | uop.not => simplify_eq_unop_default uop.not
          | uop.rev => simplify_eq_unop_default uop.rev
          | uop.sext => simplify_eq_unop_default uop.sext
          | uop.zext => simplify_eq_unop_default uop.zext
          | uop.get_slice_int => simplify_eq_unop_get_slice_int
          | uop.signed => simplify_eq_unop_signed
          | uop.unsigned => simplify_eq_unop_default uop.unsigned
          | uop.truncate n => simplify_eq_unop_default (uop.truncate n)
          | uop.vector_subrange s l => simplify_eq_unop_default (uop.vector_subrange s l)
          | uop.bvnot => simplify_eq_unop_default uop.bvnot
          | uop.bvdrop m => simplify_eq_unop_default (uop.bvdrop m)
          | uop.bvtake m => simplify_eq_unop_default (uop.bvtake m)
          | uop.negate => simplify_eq_unop_default uop.negate
          | uop.expand => simplify_eq_unop_default uop.expand
          | uop.regroup => simplify_eq_unop_default uop.regroup
          end.

        (* rev is injective, per projection: `rev a = rev b` iff `a = b`, and
           `rev a = v` iff `a = rev v` -- exact on the pair.  A flipped arrv
           (clem_arrv_flip) carries `rev vs`, so an emptied one says
           `rev vs = []`, which has to reach `vs`. *)
        Definition simplify_propeq_unop_rev {σ} (t1 : Term Σ (ty.list σ))
          (tr : Term Σ (ty.list σ)) : DList Σ :=
          let default := simplify_eq_unop_default uop.rev t1 tr in
          Term_list_case (fun _ => DList Σ)
            (fun (*var*) _ _ => default)
            (fun (*val*) v => simplify_eq_val t1 (List.rev v))
            (fun (*relval*) _ => default)
            (fun (*cons*) _ _ => default)
            (fun (*append*) _ _ => default)
            (fun (*rev*) t2 => simplify_eq t1 t2)
            (fun (*regroup*) _ _ => default)
            tr.

        Definition simplify_propeq_unop {σ1 σ2} (op : UnOp σ1 σ2) :
          Term Σ σ1 -> Term Σ σ2 -> DList Σ :=
          match op with
          | uop.inl => simplify_eq_unop_inl
          | uop.inr => simplify_eq_unop_inr
          | uop.neg => simplify_eq_unop_default uop.neg
          | uop.not => simplify_eq_unop_default uop.not
          | uop.rev => simplify_propeq_unop_rev
          | uop.sext => simplify_eq_unop_default uop.sext
          | uop.zext => simplify_eq_unop_default uop.zext
          | uop.get_slice_int => simplify_eq_unop_get_slice_int
          | uop.signed => simplify_propeq_unop_signed
          | uop.unsigned => simplify_eq_unop_default uop.unsigned
          | uop.truncate n => simplify_eq_unop_default (uop.truncate n)
          | uop.vector_subrange s l => simplify_eq_unop_default (uop.vector_subrange s l)
          | uop.bvnot => simplify_eq_unop_default uop.bvnot
          | uop.bvdrop m => simplify_eq_unop_default (uop.bvdrop m)
          | uop.bvtake m => simplify_eq_unop_default (uop.bvtake m)
          | uop.negate => simplify_eq_unop_default uop.negate
          | uop.expand => simplify_eq_unop_default uop.expand
          | uop.regroup => simplify_eq_unop_default uop.regroup
          end.

        Equations(noeqns) formula_eqs_ctx {Δ}
          (δ δ' : Env (Term Σ) Δ) : DList Σ :=
        | env.nil,        env.nil          => empty
        | env.snoc δ _ t, env.snoc δ' _ t' =>
            cat (formula_eqs_ctx δ δ') (simplify_eq t t').

        Equations(noeqns) formula_eqs_nctx {N} {Δ : NCtx N Ty}
          (δ δ' : NamedEnv (Term Σ) Δ) : DList Σ :=
        | env.nil,        env.nil          => empty
        | env.snoc δ _ t, env.snoc δ' _ t' =>
            cat (formula_eqs_nctx δ δ') (simplify_eq t t').

        Definition simplify_eq_tuple {σs} (tls : Env (Term Σ) σs)
          (tr : Term Σ (ty.tuple σs)) : DList Σ :=
          let default := dlist_eq (term_tuple tls) tr in
          Term_tuple_case (fun _ => DList Σ)
            ((*var*)  fun x xIn => default)
            ((*val*)  fun v     => simplify_eq_val (term_tuple tls) v)
            ((*relval*) fun rv  => default)
            ((*tuple*)fun trs   => formula_eqs_ctx tls trs)
            tr.

        Definition simplify_eq_record {R}
          (tls : NamedEnv (Term Σ) (recordf_ty R)) (tr : Term Σ (ty.record R)) :
          DList Σ :=
          let default := dlist_eq tr (term_record R tls) in
          Term_record_case (fun _ => DList Σ)
            (fun (*var*) _ _    => default)
            (fun (*val*) v      => simplify_eq_record_val simplify_eq_val R tls v)
            (fun (*relval*) v      => default)
            (fun (*record*) trs => formula_eqs_nctx tls trs)
            tr.

        Definition simplify_propeq_record {R}
          (tls : NamedEnv (Term Σ) (recordf_ty R)) (tr : Term Σ (ty.record R)) :
          DList Σ :=
          let default := dlist_eq tr (term_record R tls) in
          Term_record_case (fun _ => DList Σ)
            (fun (*var*) _ _    => default)
            (fun (*val*) v      => simplify_eq_record_val simplify_eq_val R tls v)
            (fun (*relval*) v      => default)
            (fun (*record*) trs =>
               match tls with
               | [env] => empty
               | env.snoc [env] b db => formula_eqs_nctx tls trs
               | _ => default
               end
            )
            tr.
        

        Definition simplify_eq_union [U] [K1 : unionk U]
          (t1 : Term Σ (unionk_ty U K1)) (t2 : Term Σ (ty.union U)) : DList Σ :=
          let default := dlist_eq t2 (term_union U K1 t1) in
          Term_union_case (fun _ => DList Σ)
            ((*var*) fun x In    => default)
            ((*val*) fun v       => simplify_eq_val (term_union U K1 t1) v)
            ((*relval*) fun v    => default)
            ((*union*)
              fun K2 t3 =>
                match eq_dec K1 K2 with
                | left e  => simplify_eq t1
                               (eq_rect_r (fun K => Term Σ (unionk_ty U K)) t3 e)
                | right _ => error
                end)
            t2.

      End WithSimplifyEq.

      (* TODO: The solver simplifies way less now *)
      Fixpoint simplify_eq [σ] (tl : Term Σ σ) (tr : Term Σ σ) : DList Σ :=
        match tl in Term _ σ return Term Σ σ → DList Σ with
        | term_var _          => fun _ => simplify_eqb Term_eqb (fun {σ} t1 t2 => dlist_eq t1 t2) tl tr
        | term_val _ v        => fun tr => simplify_eq_val tr v
        | term_relval r rv     => fun tr => simplify_eq_relval tr rv
        | term_binop op t1 t2 => simplify_eq_binop simplify_eq op t1 t2
        | term_unop op t1     => simplify_eq_unop simplify_eq op t1
        | term_tuple tls      => simplify_eq_tuple simplify_eq tls
        | term_union U K tl   => simplify_eq_union simplify_eq tl
        | term_record R tls   => simplify_eq_record simplify_eq tls
        end tr.

      Fixpoint simplify_propeq [σ] (tl : Term Σ σ) (tr : Term Σ σ) : DList Σ :=
        match tl in Term _ σ return Term Σ σ → DList Σ with
        | term_var _          => fun _ => simplify_eqb Term_eqb (fun {σ} t1 t2 => dlist_propeq t1 t2) tl tr
        | term_val _ v        => fun tr => simplify_eq_val tr v
        | term_relval r v     => fun tr => simplify_eqb Term_eqb (fun {σ} t1 t2 => dlist_propeq t1 t2) (term_relval r v) tr
        | term_binop op t1 t2 => simplify_propeq_binop simplify_propeq op t1 t2
        | term_unop op t1     => simplify_propeq_unop simplify_propeq op t1
        | term_tuple tls      => (* simplify_eq_tuple simplify_propeq tls *)
            fun tr => simplify_eqb Term_eqb (fun {σ} t1 t2 => dlist_propeq t1 t2) (term_tuple tls) tr
        | term_union U K tl   => simplify_eq_union simplify_propeq tl
        | term_record R tls   => simplify_propeq_record simplify_propeq tls
        end tr.

    End SimplifyEq.

    Section SimplifyEqSpec.

      Context [w : World].

      Lemma rep_val_eq_true {σ} (t : Term w σ) v :
        repₚ (T := STerm ty.bool) (SyncVal true) (term_binop (bop.relop bop.eq) (term_val σ v)t) ⊣⊢
          repₚ (T := STerm σ) (w := w) (SyncVal v) t.
      Proof. unfold repₚ; crushPredEntails2; cbn in *; destruct (inst t ι); cbn in *; ty.rv_split;
        repeat destruct Classes.eq_dec; subst; try congruence; reflexivity.
      Qed.

      Lemma simplify_eq_binop_default_val_spec [σ σ1 σ2] (op : BinOp σ1 σ2 σ)
        (t1 : Term w σ1) (t2 : Term w σ2) (v : Val σ) :
          instpred (simplify_eq_binop_default_val (fun {σ} t1 t2 => dlist_eq t1 t2) op t1 t2 v) ⊣⊢
          repₚ (ty.valToRelVal v) (term_binop op t1 t2).
      Proof.
        unfold simplify_eq_binop_default_val; arw.
        by rewrite rep_val_eq_true.
      Qed.

      Lemma simplify_eq_unop_default_val_spec [σ1 σ2] (op : UnOp σ1 σ2)
        (t : Term w σ1) (v : Val σ2) :
        instpred (simplify_eq_unop_default_val (fun {σ} t1 t2 => dlist_eq t1 t2) op t v) ⊣⊢
        repₚ (ty.valToRelVal v) (term_unop op t).
      Proof.
        unfold simplify_eq_unop_default_val; arw.
        by rewrite rep_val_eq_true.
      Qed.

      #[local] Hint Resolve simplify_eq_binop_default_val_spec
        simplify_eq_unop_default_val_spec : core.

      Lemma eq_term_val_eq {w1 : World} {σ : Ty} {v1 v2 : Val σ} :
        eqₚ (w := w1) (term_val σ v1) (term_val σ v2) ⊣⊢ ⌜ v1 = v2 ⌝.
      Proof.
        unfold eqₚ. crushPredEntails3.
        + by inversion H0.
        + by subst.
      Qed.

      Lemma eq_term_relval_eq {w1 : World} {σ : Ty} {v : Val σ} {rv : RelVal σ} :
        eqₚ (w := w1) (term_val σ v) (term_relval σ rv) ⊣⊢ ⌜ ty.valToRelVal v = rv ⌝.
      Proof.
        unfold eqₚ. crushPredEntails3.
      Qed.

      Lemma repₚ_term_prod_valToRelVal {σ1 σ2} {v1 : Val σ1} {v2 : Val σ2} {w1 : World} {sv1 : STerm σ1 w1} {sv2 : STerm σ2 w1} :
        repₚ (ty.valToRelVal v1) sv1 ∗ repₚ (ty.valToRelVal v2) sv2 ⊣⊢
          repₚ (T := STerm (ty.prod σ1 σ2)) (ty.valToRelVal (σ := ty.prod _ _) (v1, v2)) (term_binop bop.pair sv1 sv2).
      Proof.
        unfold repₚ.
        crushPredEntails3.
        by rewrite H0 H1.
        all: revert H0; cbn; destruct (inst sv1 ι), (inst sv2 ι); cbn; intros H0; ty.rv_split;
          repeat match goal with H : (_ , _) = (_ , _) |- _ => injection H as ? ? end; subst; reflexivity.
      Qed.

      Lemma repₚ_term_bvapp_valToRelVal {w1 : World} {m n : nat} {t1 : STerm (ty.bvec m) w1} {t2 : STerm (ty.bvec n) w1}
        {v1 : Val (ty.bvec m)} {v2 : Val (ty.bvec n)} :
        repₚ (T := STerm (ty.bvec m)) (ty.valToRelVal v1) t1 ∗ repₚ (T := STerm (ty.bvec n)) (ty.valToRelVal v2) t2 ⊣⊢
          repₚ (T := STerm (ty.bvec (m + n))) (ty.valToRelVal (σ := ty.bvec _) (bv.app v1 v2)) (term_binop bop.bvapp t1 t2)
      .
      Proof.
        unfold repₚ, bi_pred, bi_sep, sepₚ; crushPredEntails2.
        { rewrite H0 H1. auto. }
        all: revert H0; cbn; destruct (inst t1 ι), (inst t2 ι); cbn; intros H0; ty.rv_split;
          apply bv.app_inj in HL as [? ?]; apply bv.app_inj in HR as [? ?]; subst; reflexivity.
      Qed.

      Lemma repₚ_term_bvcons_valToRelVal {w1 : World} {m : nat} {t1 : STerm ty.bool w1} {t2 : STerm (ty.bvec m) w1}
        {v1 : Val ty.bool} {v2 : Val (ty.bvec m)} :
        repₚ (T := STerm ty.bool) (ty.valToRelVal v1) t1 ∗ repₚ (T := STerm (ty.bvec m)) (ty.valToRelVal v2) t2 ⊣⊢
          repₚ (T := STerm (ty.bvec (S m))) (ty.valToRelVal (σ := ty.bvec _) ((@bv.cons m) v1 v2)) (term_binop bop.bvcons t1 t2)
      .
      Proof.
        unfold repₚ, bi_pred, bi_sep, sepₚ; crushPredEntails2.
        { rewrite H0 H1. auto. }
        all: revert H0; cbn; destruct (inst t1 ι), (inst t2 ι); cbn; intros H0; ty.rv_split;
          apply bv.cons_inj in HL as [? ?]; apply bv.cons_inj in HR as [? ?]; subst; reflexivity.
      Qed.

      Lemma simplify_eq_val_spec [σ] (t : STerm σ w) (v : Val σ) :
        instpred (simplify_eq_val (fun {σ} t1 t2 => dlist_eq t1 t2) t v) ⊣⊢ repₚ (ty.valToRelVal v) t.
      Proof.
        induction t; cbn [simplify_eq_val]; auto.
        - arw.
        - destruct eq_dec; arw; unfold ty.valToRelVal; rewrite <- eq_val_rep_l.
          + by subst.
          + constructor. intros.
            split; intros.
            * contradiction.
            * pose proof (@eq_term_val_eq w σ v v0) as H'.
              crushPredEntails3.
              congruence.
        - destruct eq_dec as [->|n]; arw.
        - destruct op; cbn; auto.
          + (*and*) destruct v; cbn; arw. rewrite simplify_bool_spec. reflexivity.
          + (*or*) destruct v; cbn; arw. rewrite simplify_bool_neg_spec. reflexivity.
          + (*pair*) destruct v; cbn; arw. rewrite IHt1 IHt2.
            apply repₚ_term_prod_valToRelVal.
          + (*cons*) destruct v; cbn; arw; try (by rewrite rep_neq_nil_cons).
            rewrite IHt1 IHt2; arw.
            change (ty.valToRelVal (σ := ty.list _) (v :: v0)) with (ty.liftBinOpRV cons (ty.valToRelVal v) (ty.valToRelVal (σ := ty.list _) v0)).
            by rewrite <- rep_term_cons_sync.
          + (*bvapp*) unfold simplify_eq_binop_bvapp_val.
            destruct bv.appView; arw. rewrite IHt1 IHt2.
            apply repₚ_term_bvapp_valToRelVal.
          + (*bvcons*) unfold simplify_eq_binop_bvcons_val.
            destruct bv.view; arw. rewrite IHt1 IHt2.
            apply repₚ_term_bvcons_valToRelVal.
          + (*relop*) destruct v; cbn; arw.
        - destruct op; cbn; auto.
          + (*inl*) destruct v; cbn; arw; arw_slow.
            all: try rewrite IHt; constructor; intros ι _; unfold repₚ;
              change (inst (term_inl t) ι) with (uop.evalRel (@uop.inl _ σ1 σ2) (inst t ι));
              destruct inst; cbn; split; intro H; now inversion H.
          + (*inr*) destruct v; cbn; arw; arw_slow.
            all: try rewrite IHt; constructor; intros ι _; unfold repₚ;
              change (inst (term_inr t) ι) with (uop.evalRel (@uop.inr _ σ1 σ2) (inst t ι));
              destruct inst; cbn; split; intro H; now inversion H.
          + (*neg*) unfold simplify_eq_unop_neg_val; arw.
          + (*not*) destruct v; cbn; arw.
          + (*signed*)
            rewrite /simplify_eq_unop_signed_val -andb_lazy_alt.
            destruct andb eqn:H; arw.
            * rewrite IHt. constructor. intros ι Hpc. cbn.
              destruct (inst t ι) as [a b]; cbn; split; intro H'; ty.rv_split.
              1-2: subst; rewrite bv.signed_eq_z; intuition; lia.
              1: rewrite <- HL; by rewrite bv.of_Z_signed.
              1: rewrite <- HR; by rewrite bv.of_Z_signed.
            * rewrite instpred_dlist_error.
              iSplit; [iIntros ([])|].
              iIntros "Hsimpl".
              iDestruct (repₚ_inversion_term_signed with "Hsimpl")
                as "(%bv & %Heq & Hrep)".
              destruct bv as [a b]; cbn in *.
              pose proof (bv.signed_bounds a). inversion Heq. lia.
          + (*unsigned*)
            rewrite /simplify_eq_unop_unsigned_val -andb_lazy_alt.
            destruct andb eqn:H; arw.
            * rewrite IHt. constructor. intros ι Hpc. cbn.
              destruct (inst t ι) as [a b]; cbn; split; intro H'; ty.rv_split.
              1-2: subst; rewrite bv.unsigned_eq_z; intuition; lia.
              1: rewrite <- HL; by rewrite bv.of_Z_unsigned.
              1: rewrite <- HR; by rewrite bv.of_Z_unsigned.
            * rewrite instpred_dlist_error.
              iSplit; [iIntros ([])|].
              iIntros "Hsimpl".
              iDestruct (repₚ_inversion_term_unsigned with "Hsimpl")
                as "(%bv & %Heq & Hrep)".
              destruct bv as [a b]; cbn in *.
              pose proof (bv.unsigned_bounds a). inversion Heq. subst. lia.
        - induction IH.
          + now destruct v.
          + destruct v as [vs v]; arw. cbn.
            rewrite instpred_dlist_cat.
            rewrite q.
            rewrite repₚ_term_tuple_snoc.
            apply bi.sep_proper; eauto.
        - unfold simplify_eq_union_val.
          destruct unionv_unfold as [K2 v2] eqn:?.
          apply (f_equal (unionv_fold U)) in Heqs.
          rewrite unionv_fold_unfold in Heqs. subst.
          destruct eq_dec as [->|e]; arw.
          now rewrite (repₚ_unionv_neq e).
        - rewrite -(recordv_fold_unfold R v).
          rewrite repₚ_term_record.
          generalize (recordv_unfold R v); intros vs.
          unfold simplify_eq_record_val.
          rewrite recordv_unfold_fold.
          induction IH; destruct (env.view vs); arw.
          rewrite IHIH.
          rewrite q.
          apply repₚ_namedenv_snoc.
      Qed.
      #[local] Opaque simplify_eq_val.
      #[local] Hint Resolve simplify_eq_val_spec : core.

      Lemma simplify_eq_relval_spec [σ] (t : STerm σ w) (rv : RelVal σ) :
        instpred (simplify_eq_relval (fun {σ} t1 t2 => dlist_eq t1 t2) t rv) ⊣⊢
          instpred (formula_eq t (term_relval σ rv)).
      Proof.
        induction t; cbn [simplify_eq_relval]; auto.
        all: try by rewrite instpred_dlist_singleton.
        all: destruct eq_dec as [Heq|Hneq]; rewrite ?instpred_dlist_empty ?instpred_dlist_error.
        all: constructor; intros ι _; cbn; unfold instpred_formula_relop; cbn.
        all: try subst rv; try subst v; cbn.
        all: try (destruct rv as [l r]; cbn).
        all: try (destruct v as [vl vr]); cbn in *.
        all: split; [intros H; try contradiction H; try done | intros [H1 H2]; subst; try done].
        all: try (now apply Hneq).
      Qed.
      #[local] Opaque simplify_eq_relval.
      #[local] Hint Resolve simplify_eq_relval_spec : core.

      Lemma simplify_eq_binop_default_spec [σ1 σ2 σ] (op : BinOp σ1 σ2 σ)
        (t1 : Term w σ1) (t2 : Term w σ2) (t : Term w σ) :
        instpred (simplify_eq_binop_default (fun {σ} t1 t2 => dlist_eq t1 t2) op t1 t2 t) ⊣⊢
          repₚ (ty.valToRelVal (σ := ty.bool) true) (term_eq (term_binop op t1 t2) t).
      Proof.
        rewrite instpred_dlist_singleton.
        apply instpred_formula_relop_eq.
      Qed.

      Lemma simplify_eq_binop_minus_default_spec (tl1 : Term w ty.int) (tl2 : Term w ty.int) (tr : Term w ty.int) :
  instpred
    (simplify_eq_binop_minus_default (λ (σ : Ty) (t1 t2 : Term w σ), dlist_eq t1 t2) tl1 tl2
       tr)
    ⊣⊢ repₚ (ty.valToRelVal (σ := ty.bool) true) (term_eq (term_minus tl1 tl2) tr).
      Proof.
        unfold simplify_eq_binop_minus_default. rewrite instpred_dlist_singleton.
        rewrite instpred_formula_eq_com instpred_formula_relop_eq_val.
        constructor. intros ι _. cbn.
        repeat destruct inst; cbn; split; intro H; ty.rv_split.
        all: repeat destruct eq_dec; cbn in *; try discriminate; try reflexivity; lia.
      Qed.

      Lemma simplify_eq_binop_default_spec' [σ1 σ2 σ] (op : BinOp σ1 σ2 σ)
        (t1 : Term w σ1) (t2 : Term w σ2) (t : Term w σ) :
        secLeakT (term_binop op t1 t2) ->
        secLeakT t ->
        instpred (simplify_eq_binop_default (fun {σ} t1 t2 => dlist_eq t1 t2) op t1 t2 t) ⊣⊢
        eqₚ (term_binop op t1 t2) t.
      Proof.
        rewrite instpred_dlist_singleton.
        apply instpred_formula_relop_secLeak_eq.
      Qed.

      Lemma simplify_eq_unop_default_spec [σ1 σ] (op : UnOp σ1 σ)
        (t1 : Term w σ1) (t : Term w σ) :
        instpred (simplify_eq_unop_default (fun {σ} t1 t2 => dlist_eq t1 t2) op t1 t) ⊣⊢
          repₚ (ty.valToRelVal (σ := ty.bool) true) (term_eq (term_unop op t1) t).
      Proof.
        rewrite instpred_dlist_singleton.
        apply instpred_formula_relop_eq.
      Qed.

      Lemma simplify_eq_unop_default_spec' [σ1 σ] (op : UnOp σ1 σ)
        (t1 : Term w σ1) (t : Term w σ) :
        secLeakT (term_unop op t1) ->
        secLeakT t ->
        instpred (simplify_eq_unop_default (fun {σ} t1 t2 => dlist_eq t1 t2) op t1 t) ⊣⊢
        eqₚ (term_unop op t1) t.
      Proof.
        rewrite instpred_dlist_singleton.
        apply instpred_formula_relop_secLeak_eq.
      Qed.

      #[local] Hint Resolve simplify_eq_unop_default_spec
        simplify_eq_binop_default_spec : core.

      Lemma eqₚ_term_not_relop {σ} (op : RelOp σ) (t1 t2 : STerm σ w) tr :
        eqₚ (term_not (term_binop (bop.relop op) t1 t2)) tr ⊣⊢
        eqₚ (term_relop_neg op t1 t2) tr.
      Proof.
        unfold eqₚ. constructor. intros ι _.
        now rewrite term_negb_relop.
      Qed.

      Lemma repₚ_term_not_relop {σ} (op : RelOp σ) (t1 t2 : STerm σ w) tr :
        repₚ (ty.valToRelVal (σ := ty.bool) true) (term_eq (term_not (term_binop (bop.relop op) t1 t2)) tr) ⊣⊢
          repₚ (ty.valToRelVal (σ := ty.bool) true) (term_eq (term_relop_neg op t1 t2) tr).
      Proof.
        constructor. intros ι _.
        unfold repₚ. unfold inst, inst_term.
        by rewrite term_negb_relop.
      Qed.

      Lemma relop_eq_pair_split [σ1 σ2] (tl1 tr1 : Term w σ1) (tl2 tr2 : Term w σ2) :
        instpred (formula_eq tl1 tr1) ∗ instpred (formula_eq tl2 tr2) ⊣⊢
        repₚ (ty.valToRelVal (σ := ty.bool) true) (term_eq (term_pair tl1 tl2) (term_pair tr1 tr2)).
      Proof.
        rewrite <- instpred_formula_relop_eq.
        constructor. intros ι _. cbn. unfold instpred_formula_relop.
        split.
        - intros [[H1 H2] [H3 H4]]. cbn in *.
          destruct (inst tl1 ι), (inst tr1 ι), (inst tl2 ι), (inst tr2 ι); cbn in *.
          subst. split; reflexivity.
        - intros [H1 H2]. split; cbn in *;
          destruct (inst tl1 ι), (inst tr1 ι), (inst tl2 ι), (inst tr2 ι); cbn in *;
          injection H1 as -> ->; injection H2 as -> ->; split; reflexivity.
      Qed.

      Lemma relop_eq_cons_split [σ] (tl1 tr1 : Term w σ) (tl2 tr2 : Term w (ty.list σ)) :
        instpred (formula_eq tl1 tr1) ∗ instpred (formula_eq tl2 tr2) ⊣⊢
        instpred (formula_eq (term_cons tl1 tl2) (term_cons tr1 tr2)).
      Proof.
        constructor. intros ι _. cbn. unfold instpred_formula_relop.
        split.
        - intros [[H1 H2] [H3 H4]]. cbn in *.
          destruct (inst tl1 ι), (inst tr1 ι), (inst tl2 ι), (inst tr2 ι); cbn in *.
          subst. split; reflexivity.
        - intros [H1 H2]. split; cbn in *;
          destruct (inst tl1 ι), (inst tr1 ι), (inst tl2 ι), (inst tr2 ι); cbn in *;
          injection H1 as -> ->; injection H2 as -> ->; split; reflexivity.
      Qed.

      Lemma relop_eq_append_l [σ] (tl tl2 tr2 : Term w (ty.list σ)) :
        instpred (formula_eq tl2 tr2) ⊣⊢ instpred (formula_eq (term_append tl tl2) (term_append tl tr2)).
      Proof.
        constructor. intros ι _. cbn. unfold instpred_formula_relop. cbn.
        destruct (inst tl ι), (inst tl2 ι), (inst tr2 ι); cbn.
        split; intros [H1 H2]; split; try (now subst); now apply app_inv_head in H1 + apply app_inv_head in H2.
      Qed.

      Lemma relop_eq_append_r [σ] (tl1 tr1 tl : Term w (ty.list σ)) :
        instpred (formula_eq tl1 tr1) ⊣⊢ instpred (formula_eq (term_append tl1 tl) (term_append tr1 tl)).
      Proof.
        constructor. intros ι _. cbn. unfold instpred_formula_relop. cbn.
        destruct (inst tl1 ι), (inst tr1 ι), (inst tl ι); cbn.
        split; intros [H1 H2]; split; try (now subst); now apply app_inv_tail in H1 + apply app_inv_tail in H2.
      Qed.

      Lemma relop_eq_bvapp_split {m n} (tl1 tr1 : Term w (ty.bvec m)) (tl2 tr2 : Term w (ty.bvec n)) :
        instpred (formula_eq tl1 tr1) ∗ instpred (formula_eq tl2 tr2) ⊣⊢
        repₚ (ty.valToRelVal (σ := ty.bool) true) (term_eq (term_bvapp tl1 tl2) (term_bvapp tr1 tr2)).
      Proof.
        rewrite <- instpred_formula_relop_eq.
        constructor. intros ι _. cbn. unfold instpred_formula_relop.
        split.
        - intros [[H1 H2] [H3 H4]]. cbn in *.
          destruct (inst tl1 ι), (inst tr1 ι), (inst tl2 ι), (inst tr2 ι); cbn in *.
          subst. split; reflexivity.
        - intros [H1 H2]. split; cbn in *;
          destruct (inst tl1 ι), (inst tr1 ι), (inst tl2 ι), (inst tr2 ι); cbn in *;
          apply bv.app_inj in H1 as [-> ->]; apply bv.app_inj in H2 as [-> ->]; split; reflexivity.
      Qed.

      Lemma relop_eq_bvcons_split {m} (tl1 tr1 : Term w ty.bool) (tl2 tr2 : Term w (ty.bvec m)) :
        instpred (formula_eq tl1 tr1) ∗ instpred (formula_eq tl2 tr2) ⊣⊢
        repₚ (ty.valToRelVal (σ := ty.bool) true) (term_eq (term_binop bop.bvcons tl1 tl2) (term_binop bop.bvcons tr1 tr2)).
      Proof.
        rewrite <- instpred_formula_relop_eq.
        constructor. intros ι _. cbn. unfold instpred_formula_relop.
        split.
        - intros [[H1 H2] [H3 H4]]. cbn in *.
          destruct (inst tl1 ι), (inst tr1 ι), (inst tl2 ι), (inst tr2 ι); cbn in *.
          subst. split; reflexivity.
        - intros [H1 H2]. split; cbn in *;
          destruct (inst tl1 ι), (inst tr1 ι), (inst tl2 ι), (inst tr2 ι); cbn in *;
          apply bv.cons_inj in H1 as [-> ->]; apply bv.cons_inj in H2 as [-> ->]; split; reflexivity.
      Qed.

      (* Closer for pointwise RelVal goals: split conjunctions (relops hold on
         both projections), split RelVal equalities, decide the eq_dec's. *)
      Local Ltac rv_crush :=
        repeat match goal with
               | H : _ /\ _ |- _ => destruct H
               | |- _ /\ _ => split
               end;
        ty.rv_split; repeat destruct eq_dec; cbn in *; subst;
        try discriminate; try reflexivity; try lia; try congruence.
      Local Ltac rv_crush_if :=
        repeat match goal with
               | H : _ /\ _ |- _ => destruct H
               | |- _ /\ _ => split
               end;
        ty.rv_split;
        repeat match goal with
               | |- context[if ?c then _ else _] => destruct c
               | H : context[if ?c then _ else _] |- _ => destruct c
               end;
        cbn in *; subst; try discriminate; try reflexivity; try congruence.

      Local Ltac rv_crush2 :=
        repeat (first [ match goal with
                        | H : _ /\ _ |- _ => destruct H
                        | |- _ /\ _ => split
                        | H : (_ , _) = (_ , _) |- _ => injection H as ? ?
                        | |- (_ , _) = (_ , _) => f_equal
                        | H : @eq (ty.RV _) _ _ |- _ => ty.rv_split
                        | |- @eq (ty.RV _) _ _ => ty.rv_split
                        | H : @eq (@RelVal _ _ _) _ _ |- _ => ty.rv_split
                        | |- @eq (@RelVal _ _ _) _ _ => ty.rv_split
                        | |- context[eq_dec _ _] => destruct eq_dec
                        | H : context[eq_dec _ _] |- _ => destruct eq_dec
                        end
                      | progress (cbn in *; subst) ]);
        try discriminate; try reflexivity; try lia; try congruence.

      (* TODO: I changed eqₚ tl tr to instpred (formula_eq tl tr) mirroring simplify_eqb_spec 
      The simple reason is that with eqₚ it isn't true right now *)
      Lemma simplify_eq_spec [σ] (tl tr : Term w σ) :
        instpred (simplify_eq Term_eqb_relval (fun {σ} t1 t2 => dlist_eq t1 t2) tl tr) ⊣⊢ instpred (formula_eq tl tr).
      Proof.
        induction tl; cbn; arw.
        - by rewrite formula_relop_term'.
        - rewrite simplify_eq_val_spec. rewrite formula_relop_term'.
          by rewrite rep_val_eq_true.
        - rewrite simplify_eq_relval_spec. unfold instpred. cbn.
          by rewrite instpred_formula_eq_com'.
        - destruct op; cbn; auto; rewrite formula_relop_term';
            try apply simplify_eq_binop_default_spec.
          + (*plus*)
            destruct tr using Term_int_case; cbn; arw; try rewrite rep_val_eq_true;
              try (constructor; intros ι _; cbn; lia);
              try solve [arw; constructor; intros ι _; cbn; destruct inst, inst, inst, inst; cbn;
              split; intro H; rv_crush];
              try solve [arw; constructor; intros ι _; cbn; destruct inst, inst, inst; cbn;
                   split; intro H; rv_crush].
            * by rewrite rep_eq_terms_com.
              (* constructor; intros ι _; cbn. destruct inst, inst, ι.[? l∷ty.int]; cbn; *)
              (*   split; intro H; rv_crush. *)
            * rewrite simplify_eq_val_spec.
              constructor; intros ι _; cbn. destruct inst, inst; cbn;
                split; intro H; rv_crush.
            * by rewrite rep_eq_terms_com.
              (* constructor; intros ι _; cbn. destruct inst, inst, i; cbn; *)
              (*   split; intro H; rv_crush. *)
            * destruct (Term_eqb_relval_spec tl1 tr1); subst.
              { destruct a as (H1 & H2 & eq12). subst.
                rewrite IHtl2. rewrite formula_relop_term.
                apply secLeakT_spec in H1.
                destruct H1.
                constructor; cbn. intros ι Hwco; cbn.
                specialize (fromEntails0 ι Hwco I).
                cbn in fromEntails0. unfold instpred_formula_secLeak in fromEntails0.
                destruct inst, inst, inst; cbn;
                  split; intro H; rv_crush.
                all: try contradiction.
              }
              destruct (Term_eqb_relval_spec tl2 tr2); subst.
              { destruct a as (H1 & H2 & eq12). subst.
                rewrite IHtl1. rewrite formula_relop_term.
                apply secLeakT_spec in H1.
                destruct H1.
                constructor; cbn. intros ι Hwco; cbn.
                specialize (fromEntails0 ι Hwco I).
                cbn in fromEntails0. unfold instpred_formula_secLeak in fromEntails0.
                destruct inst, inst, inst; cbn;
                  split; intro H; rv_crush.
                all: try contradiction.
              }
              destruct (Term_eqb_relval_spec tl1 tr2); subst.
              { destruct a as (H1 & H2 & eq12). subst.
                rewrite IHtl2. rewrite formula_relop_term.
                apply secLeakT_spec in H1.
                destruct H1.
                constructor; cbn. intros ι Hwco; cbn.
                specialize (fromEntails0 ι Hwco I).
                cbn in fromEntails0. unfold instpred_formula_secLeak in fromEntails0.
                destruct inst, inst, inst; cbn;
                  split; intro H; rv_crush.
                all: try contradiction.
              }
              destruct (Term_eqb_relval_spec tl2 tr1); subst.
              {
                destruct a as (H1 & H2 & eq12). subst.
                rewrite IHtl1. rewrite formula_relop_term.
                apply secLeakT_spec in H1.
                destruct H1.
                constructor; cbn. intros ι Hwco; cbn.
                specialize (fromEntails0 ι Hwco I).
                cbn in fromEntails0. unfold instpred_formula_secLeak in fromEntails0.
                destruct inst, inst, inst; cbn;
                  split; intro H; rv_crush.
                all: try contradiction.
              }
              arw. constructor; intros ι _; cbn.
              destruct inst, inst, inst, inst; cbn;
                split; intro H; rv_crush.
            * destruct (Term_eqb_relval_spec tl1 tr1); subst.
              { destruct a as (H1 & H2 & eq12). subst.
                rewrite IHtl2. rewrite formula_relop_term.
                apply secLeakT_spec in H1.
                destruct H1.
                constructor; cbn. intros ι Hwco; cbn.
                specialize (fromEntails0 ι Hwco I).
                cbn in fromEntails0. unfold instpred_formula_secLeak in fromEntails0.
                destruct inst, inst, inst; cbn;
                  split; intro H; rv_crush.
                all: try contradiction.
              }
              destruct (Term_eqb_relval_spec tl2 tr1); subst.
              { destruct a as (H1 & H2 & eq12). subst.
                rewrite IHtl1. rewrite formula_relop_term.
                apply secLeakT_spec in H1.
                destruct H1.
                constructor; cbn. intros ι Hwco; cbn.
                specialize (fromEntails0 ι Hwco I).
                cbn in fromEntails0. unfold instpred_formula_secLeak in fromEntails0.
                destruct inst, inst, inst; cbn;
                  split; intro H; rv_crush.
                all: try contradiction.
              }
              arw. constructor; intros ι _; cbn.
              destruct inst, inst, inst, inst; cbn;
                split; intro H; rv_crush.
          + (*minus*) unfold simplify_eq_binop_minus.
            clear IHtl1 IHtl2.
            destruct tl2 using Term_int_case; arw; cbn.
            all: try by rewrite simplify_eq_binop_minus_default_spec.
            destruct i.
            * rewrite instpred_dlist_singleton. constructor. intros ι _. cbn.
              unfold instpred_formula_relop. destruct inst, inst; cbn.
              split; intro H; rv_crush.
            * by rewrite simplify_eq_binop_minus_default_spec.
            * by rewrite simplify_eq_binop_minus_default_spec.
          + (*times*) unfold simplify_eq_binop_times. arw.
            constructor; intros ι _; cbn.
            repeat destruct inst; cbn;
              split; intro H; rv_crush.
          + (*and*)
            destruct tr using Term_bool_case; cbn; arw.
            * apply rep_eq_terms_com.
            * rewrite simplify_eq_val_spec.
              by rewrite rep_eq_val_true.
            * destruct (Term_eqb_relval_spec tl1 tr1); cbn; subst; arw.
              destruct (Term_eqb_relval_spec tl2 tr2); subst; arw.
              destruct a as (Hl1 & Hr1 & eql1r1).
              destruct a0 as (Hl2 & Hr2 & eql2r2).
              subst.
              apply secLeakT_spec in Hl1. apply secLeakT_spec in Hl2.
              destruct Hl1, Hl2.
              constructor; cbn. intros ι Hwco; cbn.
              specialize (fromEntails0 ι Hwco I). specialize (fromEntails1 ι Hwco I).
              cbn in *. unfold instpred_formula_secLeak in fromEntails0, fromEntails1.
              split; intros _.
              -- repeat destruct inst; cbn; rv_crush.
              -- easy.
          + (*or*)
            destruct tr using Term_bool_case; cbn; arw.
            * apply rep_eq_terms_com.
            * rewrite simplify_eq_val_spec.
              by rewrite rep_eq_val_true.
            * destruct (Term_eqb_relval_spec tl1 tr1); cbn; subst; arw.
              destruct (Term_eqb_relval_spec tl2 tr2); subst; arw.
              destruct a as (Hl1 & Hr1 & eql1r1).
              destruct a0 as (Hl2 & Hr2 & eql2r2).
              subst.
              apply secLeakT_spec in Hl1. apply secLeakT_spec in Hl2.
              destruct Hl1, Hl2.
              constructor; cbn. intros ι Hwco; cbn.
              specialize (fromEntails0 ι Hwco I). specialize (fromEntails1 ι Hwco I).
              cbn in *. unfold instpred_formula_secLeak in fromEntails0, fromEntails1.
              split; intros H.
              -- repeat destruct inst; cbn; rv_crush.
              -- easy.
          + (*pair*)
            destruct tr using Term_prod_case; cbn; auto; arw.
            * apply rep_eq_terms_com.
            * rewrite simplify_eq_val_spec.
              by rewrite rep_eq_val_true.
            * rewrite IHtl1 IHtl2. exact (relop_eq_pair_split tl1 tr1 tl2 tr2).
          + (*cons*) destruct tr using Term_list_case; cbn; auto; arw.
            * now rewrite rep_eq_terms_com.
            * rewrite simplify_eq_val_spec. now rewrite rep_eq_val_true.
            * now rewrite rep_eq_terms_com.
            * rewrite IHtl1 IHtl2.
              rewrite <- instpred_formula_relop_eq'.
              exact (relop_eq_cons_split tl1 tr1 tl2 tr2).
          + (*append*)
            destruct tr using Term_list_case; cbn; auto; arw.
            * now rewrite rep_eq_terms_com.
            * rewrite simplify_eq_val_spec. now rewrite rep_eq_val_true.
            * now rewrite rep_eq_terms_com.
            * now rewrite rep_eq_terms_com.
            * destruct (Term_eqb_relval_spec tl1 tr1). destruct a as (sL1 & sL2 & <-).
              { rewrite IHtl2. try rewrite <- instpred_formula_relop_eq.
                exact (relop_eq_append_l tl1 tl2 tr2). }
              destruct (Term_eqb_relval_spec tl2 tr2). destruct a as (sL1 & sL2 & <-).
              { rewrite IHtl1. try rewrite <- instpred_formula_relop_eq.
                exact (relop_eq_append_r tl1 tr1 tl2). }
              arw.
          + (*bvapp*)
            assert (∀ mn (t : Term w (ty.bvec mn)) (e : m + n = mn),
                       instpred (simplify_eq_binop_bvapp' (λ (σ : Ty) (t1 t2 : Term w σ), dlist_eq t1 t2) (simplify_eq Term_eqb_relval (λ (σ : Ty) (t1 t2 : Term w σ), dlist_eq t1 t2))
                                 tl1 tl2 t e) ⊣⊢
                       repₚ (ty.valToRelVal (σ := ty.bool) true) (term_eq (term_bvapp tl1 tl2)
                       (eq_rect_r (fun l => Term w (ty.bvec l)) t e))); eauto.
            intros mn t e. destruct mn, t using Term_bvec_case; subst; cbn; arw.
            { apply rep_eq_terms_com. }
            { rewrite simplify_eq_val_spec. by rewrite rep_eq_val_true. }
            destruct eq_dec; arw; subst.
            destruct transparent.nat_add_cancel_l, (uip eq_refl e); cbn.
            rewrite instpred_dlist_cat.
            rewrite IHtl1 IHtl2.
            apply relop_eq_bvapp_split.
          + (*bvcons*)
            assert (∀ sm (t : Term w (ty.bvec sm)) (e : S m = sm),
                       instpred (simplify_eq_binop_bvcons' (λ (σ : Ty) (t1 t2 : Term w σ), dlist_eq t1 t2) (simplify_eq Term_eqb_relval (λ (σ : Ty) (t1 t2 : Term w σ), dlist_eq t1 t2))
                                  tl1 tl2 t e) ⊣⊢
                        repₚ (ty.valToRelVal (σ := ty.bool) true) (term_eq (term_binop bop.bvcons tl1 tl2)
                        (eq_rect_r (fun l => Term w (ty.bvec l)) t e))); eauto.
            intros sm t e. destruct sm, t using Term_bvec_case; subst; cbn; arw.
            { apply rep_eq_terms_com. }
            { rewrite simplify_eq_val_spec. by rewrite rep_eq_val_true. }
            rewrite IHtl1 IHtl2.
            dependent elimination e.
            apply relop_eq_bvcons_split.
          + (*relop*)
            clear IHtl1 IHtl2. revert r tl1 tl2.
            induction tr using Term_bool_ind; cbn; intros rop tl1 tl2; arw;
              try apply rep_eq_terms_com.
            * rewrite simplify_eq_val_spec. by rewrite rep_eq_val_true.
            * rewrite simplify_eq_relval_spec. by rewrite rep_eq_relval_true.
            * rewrite repₚ_term_eq_not.
              rewrite repₚ_term_not_relop.
              destruct rop; cbn; auto.
        - destruct op; cbn; auto;
            try (rewrite simplify_eq_unop_default_spec;
            by rewrite instpred_formula_relop_eq').
          + (*inl*) destruct tr using Term_sum_case; cbn; auto; arw; arw_slow.
            * rewrite simplify_eq_unop_default_spec.
              now rewrite instpred_formula_relop_eq'.
            * rewrite simplify_eq_unop_default_spec.
              now rewrite instpred_formula_relop_eq'.
            * rewrite IHtl. Search term_inl.
              constructor. intros ι _. unfold instpred_formula_relop.
              change (inst (term_inl tl) ι) with (uop.evalRel (@uop.inl _ σ1 σ2) (inst tl ι)).
              change (inst (term_inl tr) ι) with (uop.evalRel (@uop.inl _ σ1 σ2) (inst tr ι)).
              destruct inst, inst; cbn; try tauto.
              split; intros [H1 H2]; split; try (now subst); first [now injection H1 | now injection H2].
            * constructor. intros ι _. unfold instpred_formula_relop.
              change (inst (term_inl tl) ι) with (uop.evalRel (@uop.inl _ σ1 σ2) (inst tl ι)).
              change (inst (term_inr tr) ι) with (uop.evalRel (@uop.inr _ σ1 σ2) (inst tr ι)).
              destruct inst, inst; cbn; try tauto.
              split; intro H; try contradiction; destruct H as [H1 H2]; discriminate.
          + (*inr*) destruct tr using Term_sum_case; cbn; auto; arw; arw_slow.
            * rewrite simplify_eq_unop_default_spec.
              now rewrite instpred_formula_relop_eq'.
            * rewrite simplify_eq_unop_default_spec.
              now rewrite instpred_formula_relop_eq'.
            * constructor. intros ι _. unfold instpred_formula_relop.
              change (inst (term_inr tl) ι) with (uop.evalRel (@uop.inr _ σ1 σ2) (inst tl ι)).
              change (inst (term_inl tr) ι) with (uop.evalRel (@uop.inl _ σ1 σ2) (inst tr ι)).
              destruct inst, inst; cbn; try tauto.
              split; intro H; try contradiction; destruct H as [H1 H2]; discriminate.
            * rewrite IHtl.
              constructor. intros ι _. unfold instpred_formula_relop.
              change (inst (term_inr tl) ι) with (uop.evalRel (@uop.inr _ σ1 σ2) (inst tl ι)).
              change (inst (term_inr tr) ι) with (uop.evalRel (@uop.inr _ σ1 σ2) (inst tr ι)).
              destruct inst, inst; cbn; try tauto.
              split; intros [H1 H2]; split; try (now subst); first [now injection H1 | now injection H2].
          + (*get_slice_int*)
            unfold simplify_eq_unop_get_slice_int.
            destruct (Term_eqb_relval_spec (term_get_slice_int tl) tr); subst; arw.
            * destruct a as (Hl & Hr & ->).
              apply secLeakT_spec in Hr.
              constructor. intros ι Hwco. destruct Hr. specialize (fromEntails0 ι Hwco I). cbn in *.
              unfold  instpred_formula_relop. unfold instpred_formula_secLeak in fromEntails0.
              destruct inst; cbn; try easy; split; reflexivity.
            * Search repₚ instpred_formula_relop. by rewrite instpred_formula_relop_eq'.
          + (*signed*)
            destruct tr using Term_int_case; cbn; arw;
              try solve [constructor; intros ι Hwco; unfold instpred_formula_relop; cbn;
            repeat destruct inst; cbn in *; split; intros H; rv_crush].            
            * constructor. intros ι _. unfold instpred_formula_relop. cbn.
              destruct inst, ι.[? l∷ty.int]; cbn in *; split; intros H; rv_crush.
            * constructor. intros ι _. unfold instpred_formula_relop. cbn.
              destruct inst, i; cbn in *; split; intros H; rv_crush.
            * destruct eq_dec; subst.
              -- rewrite IHtl. Search term_signed. Search eqₚ_term_signed.
                 cbn. unfold instpred_formula_relop.
                 constructor. intros ι Hwco. cbn.
                 repeat destruct inst; cbn; try tauto.
                 split; intros [H1 H2]; split; try (now subst).
                 all: apply bv.signed_inj in H1, H2; assumption.
              -- rewrite instpred_dlist_singleton. cbn.
                 rewrite instpred_formula_eq_com'.
                 rewrite instpred_formula_relop_eq_val'.
                 unfold instpred_formula_relop.
                 constructor. intros ι Hwco.
                 cbn. repeat destruct inst; cbn in *.
                 all: split; intro H; rv_crush.                 
        - destruct tr using Term_tuple_case; cbn; arw.
          + constructor. intros ι _. unfold instpred_formula_relop. cbn.
            destruct  ι.[? l∷ty.tuple σs], (ty.envToRelValTuple (inst ts ι));
              cbn -[eq_dec]; split; intro H; rv_crush.
          + constructor. intros ι _. unfold instpred_formula_relop. cbn.
            destruct rv, (ty.envToRelValTuple (inst ts ι));
              cbn -[eq_dec]; split; intro H; rv_crush.
          + induction IH; cbn; destruct (env.view ts0); cbn; arw.
            rewrite q.
            now apply bi.sep_proper.
        - destruct tr using Term_union_case; cbn; arw.
          + constructor. intros ι Hwco. unfold instpred_formula_relop.
            cbn. destruct inst, ι.[? l∷ty.union U]; cbn;
              split; intro H; rv_crush.
          + constructor. intros ι Hwco. unfold instpred_formula_relop.
            cbn. destruct inst, rv; cbn;
              split; intro H; rv_crush.
          + destruct eq_dec; subst; arw.
            * rewrite IHtl.
              constructor. intros ι Hwco. cbn. unfold instpred_formula_relop.
              cbn. destruct inst, inst; cbn.
              split; intros [H1 H2]; split; try (now subst).
              all: apply unionv_fold_inj in H1, H2;
                   apply Eqdep_dec.inj_pair2_eq_dec in H1; [|intros x y; apply eq_dec];
                   apply Eqdep_dec.inj_pair2_eq_dec in H2; [|intros x y; apply eq_dec];
                   assumption.
            * constructor. intros ι Hwco.
              split; intro H.
              -- contradiction.
              -- apply instpred_formula_relop_eqₚ in H; auto.
                 by rewrite (fromBientails (eqₚ_term_union_neq n) ι) in H.
        - destruct tr using Term_record_case; cbn; arw; arw_slow.
          + constructor. intros ι Hwco. unfold instpred_formula_relop.
            cbn.
            destruct (ty.recordv_fold_rel _
           (@inst
              (λ Σ : LCtx,
                 Env
                   (λ xt,
                      Term Σ (@type _ _ xt))
                   _)
              _
              inst_env _ _ _)), ι.[? l∷ty.record R]; cbn;
              split; intro H; rv_crush_if.
          + rewrite -(ty.recordv_fold_unfold R v).
            rewrite repₚ_term_record.
            generalize (recordv_unfold R v); intros vs.
            unfold simplify_eq_record_val.
            rewrite recordv_unfold_fold.
            induction IH; destruct (env.view vs); arw.
            rewrite IHIH.
            Search env.snoc repₚ.
            rewrite <- repₚ_namedenv_snoc.
            rewrite simplify_eq_val_spec.
            apply bi.sep_proper; auto.
          + constructor. intros ι Hwco. unfold instpred_formula_relop.
            cbn.
            destruct (ty.recordv_fold_rel _
                        (@inst
                           (λ Σ : LCtx,
                               Env
                                 (λ xt,
                                   Term Σ (@type _ _ xt))
                                 _)
                           _
                           inst_env _ _ _)), rv; cbn;
              split; intro H; rv_crush_if.
          + induction IH.
            * env.destroy ts0. auto.
            * env.destroy ts0. arw.
            arw_slow. apply bi.sep_proper; auto.
      Qed.

    End SimplifyEqSpec.
    #[global] Arguments simplify_eq {Σ} Term_eqb dlist_eq {σ} tl tr.
    #[export] Hint Rewrite simplify_eq_spec : uniflogic.

    Section SimplifyPropeqSpec.
      Context [w : World].

      Lemma simplify_propeq_binop_default_val_spec [σ σ1 σ2] (op : BinOp σ1 σ2 σ)
        (t1 : Term w σ1) (t2 : Term w σ2) (v : Val σ) :
        instpred (simplify_eq_binop_default_val (fun {σ} t1 t2 => dlist_propeq t1 t2) op t1 t2 v) ⊣⊢
          repₚ (ty.valToRelVal v) (term_binop op t1 t2).
      Proof.
        unfold simplify_eq_binop_default_val; arw.
      Qed.

      Lemma simplify_propeq_unop_default_val_spec [σ1 σ2] (op : UnOp σ1 σ2)
        (t : Term w σ1) (v : Val σ2) :
        instpred (simplify_eq_unop_default_val (fun {σ} t1 t2 => dlist_propeq t1 t2) op t v) ⊣⊢
          repₚ (ty.valToRelVal v) (term_unop op t).
      Proof.
        unfold simplify_eq_unop_default_val; arw.
      Qed.
      #[local] Hint Resolve simplify_propeq_binop_default_val_spec
        simplify_propeq_unop_default_val_spec : core.

      Lemma simplify_propeq_val_spec [σ] (t : STerm σ w) (v : Val σ) :
        instpred (simplify_eq_val (fun {σ} t1 t2 => dlist_propeq t1 t2) t v) ⊣⊢ repₚ (ty.valToRelVal v) t.
      Proof.
        induction t; cbn [simplify_eq_val]; auto.
        - arw.
        - destruct eq_dec; arw; unfold ty.valToRelVal; rewrite <- eq_val_rep_l.
          + by subst.
          + constructor. intros.
            split; intros.
            * contradiction.
            * inversion H0. congruence.
        - destruct eq_dec as [->|n]; arw.
        - destruct op; cbn; auto.
          + (*and*) destruct v; cbn; arw. rewrite simplify_bool_spec. reflexivity.
          + (*or*) destruct v; cbn; arw. rewrite simplify_bool_neg_spec. reflexivity.
          + (*pair*) destruct v; cbn; arw. rewrite IHt1 IHt2.
            apply repₚ_term_prod_valToRelVal.
          + (*cons*) destruct v; cbn; arw; try (by rewrite rep_neq_nil_cons).
            rewrite IHt1 IHt2; arw.
            change (ty.valToRelVal (σ := ty.list _) (v :: v0)) with (ty.liftBinOpRV cons (ty.valToRelVal v) (ty.valToRelVal (σ := ty.list _) v0)).
            by rewrite <- rep_term_cons_sync.
          + (*bvapp*) unfold simplify_eq_binop_bvapp_val.
            destruct bv.appView; arw. rewrite IHt1 IHt2.
            apply repₚ_term_bvapp_valToRelVal.
          + (*bvcons*) unfold simplify_eq_binop_bvcons_val.
            destruct bv.view; arw. rewrite IHt1 IHt2.
            apply repₚ_term_bvcons_valToRelVal.
          + (*relop*) destruct v; cbn; arw.
        - destruct op; cbn; auto.
          + (*inl*) destruct v; cbn; arw; arw_slow.
            all: try rewrite IHt; constructor; intros ι _; unfold repₚ;
              change (inst (term_inl t) ι) with (uop.evalRel (@uop.inl _ σ1 σ2) (inst t ι));
              destruct inst; cbn; split; intro H; now inversion H.
          + (*inr*) destruct v; cbn; arw; arw_slow.
            all: try rewrite IHt; constructor; intros ι _; unfold repₚ;
              change (inst (term_inr t) ι) with (uop.evalRel (@uop.inr _ σ1 σ2) (inst t ι));
              destruct inst; cbn; split; intro H; now inversion H.
          + (*neg*) unfold simplify_eq_unop_neg_val; arw.
          + (*not*) destruct v; cbn; arw.
          + (*signed*)
            rewrite /simplify_eq_unop_signed_val -andb_lazy_alt.
            destruct andb eqn:H; arw.
            * rewrite IHt. constructor. intros ι Hpc. cbn.
              destruct (inst t ι) as [a b]; cbn; split; intro H'; ty.rv_split.
              1-2: subst; rewrite bv.signed_eq_z; intuition; lia.
              1: rewrite <- HL; by rewrite bv.of_Z_signed.
              1: rewrite <- HR; by rewrite bv.of_Z_signed.
            * rewrite instpred_dlist_error.
              iSplit; [iIntros ([])|].
              iIntros "Hsimpl".
              iDestruct (repₚ_inversion_term_signed with "Hsimpl")
                as "(%bv & %Heq & Hrep)".
              destruct bv as [a b]; cbn in *.
              pose proof (bv.signed_bounds a). inversion Heq. lia.
          + (*unsigned*)
            rewrite /simplify_eq_unop_unsigned_val -andb_lazy_alt.
            destruct andb eqn:H; arw.
            * rewrite IHt. constructor. intros ι Hpc. cbn.
              destruct (inst t ι) as [a b]; cbn; split; intro H'; ty.rv_split.
              1-2: subst; rewrite bv.unsigned_eq_z; intuition; lia.
              1: rewrite <- HL; by rewrite bv.of_Z_unsigned.
              1: rewrite <- HR; by rewrite bv.of_Z_unsigned.
            * rewrite instpred_dlist_error.
              iSplit; [iIntros ([])|].
              iIntros "Hsimpl".
              iDestruct (repₚ_inversion_term_unsigned with "Hsimpl")
                as "(%bv & %Heq & Hrep)".
              destruct bv as [a b]; cbn in *.
              pose proof (bv.unsigned_bounds a). inversion Heq. subst. lia.
        - induction IH.
          + now destruct v.
          + destruct v as [vs v]; arw. cbn.
            rewrite instpred_dlist_cat.
            rewrite q.
            rewrite repₚ_term_tuple_snoc.
            apply bi.sep_proper; eauto.
        - unfold simplify_eq_union_val.
          destruct unionv_unfold as [K2 v2] eqn:?.
          apply (f_equal (unionv_fold U)) in Heqs.
          rewrite unionv_fold_unfold in Heqs. subst.
          destruct eq_dec as [->|e]; arw.
          now rewrite (repₚ_unionv_neq e).
        - rewrite -(recordv_fold_unfold R v).
          rewrite repₚ_term_record.
          generalize (recordv_unfold R v); intros vs.
          unfold simplify_eq_record_val.
          rewrite recordv_unfold_fold.
          induction IH; destruct (env.view vs); arw.
          rewrite IHIH.
          rewrite q.
          apply repₚ_namedenv_snoc.
      Qed.
      #[local] Hint Resolve simplify_propeq_val_spec : core.

      Lemma simplify_propeq_binop_default_spec [σ1 σ2 σ] (op : BinOp σ1 σ2 σ)
        (t1 : Term w σ1) (t2 : Term w σ2) (t : Term w σ) :
        instpred (simplify_eq_binop_default (fun {σ} t1 t2 => dlist_propeq t1 t2) op t1 t2 t) ⊣⊢
          eqₚ (term_binop op t1 t2) t.
      Proof. unfold simplify_eq_binop_default; arw. Qed.

      Lemma simplify_propeq_unop_default_spec [σ1 σ] (op : UnOp σ1 σ)
        (t1 : Term w σ1) (t : Term w σ) :
        instpred (simplify_eq_unop_default (fun {σ} t1 t2 => dlist_propeq t1 t2) op t1 t) ⊣⊢
          eqₚ (term_unop op t1) t.
      Proof. unfold simplify_eq_unop_default; arw. Qed.

      #[local] Hint Resolve simplify_propeq_unop_default_spec
        simplify_propeq_binop_default_spec : core.

      (* The four injective constructors, exact on the pair. *)
      Lemma propeq_pair_split [σ1 σ2] (tl1 tr1 : Term w σ1) (tl2 tr2 : Term w σ2) :
        instpred (formula_propeq tl1 tr1) ∗ instpred (formula_propeq tl2 tr2) ⊣⊢
        instpred (formula_propeq (term_pair tl1 tl2) (term_pair tr1 tr2)).
      Proof.
        constructor. intros ι _. cbn. unfold instpred_formula_propeq. cbn.
        split.
        - intros [-> ->]. reflexivity.
        - intros H. pose proof (f_equal ty.projLeftRV H) as Hl.
          pose proof (f_equal ty.projRightRV H) as Hr. cbn in Hl, Hr.
          injection Hl as Hl1 Hl2. injection Hr as Hr1 Hr2.
          split; apply ty.RV_ext; assumption.
      Qed.

      Lemma propeq_cons_split [σ] (tl1 tr1 : Term w σ) (tl2 tr2 : Term w (ty.list σ)) :
        instpred (formula_propeq tl1 tr1) ∗ instpred (formula_propeq tl2 tr2) ⊣⊢
        instpred (formula_propeq (term_cons tl1 tl2) (term_cons tr1 tr2)).
      Proof.
        constructor. intros ι _. cbn. unfold instpred_formula_propeq. cbn.
        split.
        - intros [-> ->]. reflexivity.
        - intros H. pose proof (f_equal ty.projLeftRV H) as Hl.
          pose proof (f_equal ty.projRightRV H) as Hr. cbn in Hl, Hr.
          injection Hl as Hl1 Hl2. injection Hr as Hr1 Hr2.
          split; apply ty.RV_ext; assumption.
      Qed.

      Lemma propeq_bvapp_split {m n} (tl1 tr1 : Term w (ty.bvec m)) (tl2 tr2 : Term w (ty.bvec n)) :
        instpred (formula_propeq tl1 tr1) ∗ instpred (formula_propeq tl2 tr2) ⊣⊢
        instpred (formula_propeq (term_bvapp tl1 tl2) (term_bvapp tr1 tr2)).
      Proof.
        constructor. intros ι _. cbn. unfold instpred_formula_propeq. cbn.
        split.
        - intros [-> ->]. reflexivity.
        - intros H. pose proof (f_equal ty.projLeftRV H) as Hl.
          pose proof (f_equal ty.projRightRV H) as Hr. cbn in Hl, Hr.
          apply bv.app_inj in Hl as [Hl1 Hl2]. apply bv.app_inj in Hr as [Hr1 Hr2].
          split; apply ty.RV_ext; assumption.
      Qed.

      Lemma propeq_bvcons_split {m} (tl1 tr1 : Term w ty.bool) (tl2 tr2 : Term w (ty.bvec m)) :
        instpred (formula_propeq tl1 tr1) ∗ instpred (formula_propeq tl2 tr2) ⊣⊢
        instpred (formula_propeq (term_binop bop.bvcons tl1 tl2) (term_binop bop.bvcons tr1 tr2)).
      Proof.
        constructor. intros ι _. cbn. unfold instpred_formula_propeq. cbn.
        split.
        - intros [-> ->]. reflexivity.
        - intros H. pose proof (f_equal ty.projLeftRV H) as Hl.
          pose proof (f_equal ty.projRightRV H) as Hr. cbn in Hl, Hr.
          apply bv.cons_inj in Hl as [Hl1 Hl2]. apply bv.cons_inj in Hr as [Hr1 Hr2].
          split; apply ty.RV_ext; assumption.
      Qed.

      Lemma propeq_rev_split [σ] (t1 t2 : Term w (ty.list σ)) :
        instpred (formula_propeq t1 t2) ⊣⊢
        instpred (formula_propeq (term_unop uop.rev t1) (term_unop uop.rev t2)).
      Proof.
        constructor. intros ι _. cbn. unfold instpred_formula_propeq. cbn.
        split.
        - intros ->. reflexivity.
        - intros H. pose proof (f_equal ty.projLeftRV H) as Hl.
          pose proof (f_equal ty.projRightRV H) as Hr. cbn in Hl, Hr.
          apply rev_inj in Hl, Hr. apply ty.RV_ext; assumption.
      Qed.

      Lemma propeq_rev_val [σ] (t1 : Term w (ty.list σ)) (v : Val (ty.list σ)) :
        repₚ (ty.valToRelVal (σ := ty.list σ) (List.rev v)) t1 ⊣⊢
        instpred (formula_propeq (term_unop uop.rev t1) (term_val _ v)).
      Proof.
        constructor. intros ι _. unfold repₚ. cbn. unfold instpred_formula_propeq. cbn.
        unfold ty.valToRelVal.
        remember (inst t1 ι) as x eqn:Ex. clear Ex. destruct x as [l r]. cbn.
        split.
        - intros H. pose proof (f_equal ty.projLeftRV H) as Hl.
          pose proof (f_equal ty.projRightRV H) as Hr. cbn in Hl, Hr.
          subst l r. rewrite rev_involutive. reflexivity.
        - intros H. pose proof (f_equal ty.projLeftRV H) as Hl.
          pose proof (f_equal ty.projRightRV H) as Hr. cbn in Hl, Hr.
          subst v. apply rev_inj in Hr. subst r. rewrite rev_involutive. reflexivity.
      Qed.

      Lemma simplify_propeq_unop_rev_spec (sp : ∀ σ, Term w σ → Term w σ → DList w)
        [σ] (tl : Term w (ty.list σ))
        (IHtl : ∀ tr, instpred (sp _ tl tr) ⊣⊢ instpred (formula_propeq tl tr))
        (tr : Term w (ty.list σ)) :
        instpred (simplify_propeq_unop_rev (fun σ t1 t2 => dlist_propeq t1 t2) sp tl tr) ⊣⊢
          instpred (formula_propeq (term_unop uop.rev tl) tr).
      Proof.
        destruct tr using Term_list_case; cbn -[simplify_eq_val];
          try (unfold simplify_eq_unop_default; rewrite instpred_dlist_singleton; reflexivity).
        - rewrite simplify_propeq_val_spec. apply propeq_rev_val.
        - rewrite IHtl. apply propeq_rev_split.
      Qed.

      Lemma simplify_propeq_binop_spec (sp : ∀ σ, Term w σ → Term w σ → DList w)
        [σ1 σ2 σ] (op : BinOp σ1 σ2 σ) (tl1 : Term w σ1) (tl2 : Term w σ2)
        (IHtl1 : ∀ tr, instpred (sp _ tl1 tr) ⊣⊢ instpred (formula_propeq tl1 tr))
        (IHtl2 : ∀ tr, instpred (sp _ tl2 tr) ⊣⊢ instpred (formula_propeq tl2 tr))
        (tr : Term w σ) :
        instpred (simplify_propeq_binop Term_eqb (fun σ t1 t2 => dlist_propeq t1 t2) sp
                    op tl1 tl2 tr) ⊣⊢
          instpred (formula_propeq (term_binop op tl1 tl2) tr).
      Proof.
        destruct op; cbn [simplify_propeq_binop]; try apply simplify_propeqb_spec.
        - (*pair*)
          destruct tr using Term_prod_case; cbn -[simplify_eq_val];
            rewrite ?instpred_dlist_singleton ?instpred_dlist_cat.
          + apply instpred_formula_propeq_com.
          + rewrite simplify_propeq_val_spec -eq_val_rep_r. reflexivity.
          + reflexivity.
          + rewrite IHtl1 IHtl2. apply propeq_pair_split.
        - (*cons*)
          destruct tr using Term_list_case; cbn -[simplify_eq_val];
            rewrite ?instpred_dlist_singleton ?instpred_dlist_cat.
          all: first [ reflexivity | apply instpred_formula_propeq_com
                     | (rewrite simplify_propeq_val_spec -eq_val_rep_r; reflexivity)
                     | (rewrite IHtl1 IHtl2; apply propeq_cons_split) ].
        - (*bvapp*)
          unfold simplify_eq_binop_bvapp.
          assert (∀ mn (t : Term w (ty.bvec mn)) (e : m + n = mn),
                     instpred (simplify_eq_binop_bvapp' (λ σ t1 t2, dlist_propeq t1 t2) sp
                                 tl1 tl2 t e) ⊣⊢
                     instpred (formula_propeq (term_bvapp tl1 tl2)
                                 (eq_rect_r (fun l => Term w (ty.bvec l)) t e))) as H;
            [|apply (H _ tr eq_refl)].
          intros mn t e. destruct mn, t using Term_bvec_case; subst; cbn -[simplify_eq_val];
            rewrite ?instpred_dlist_singleton ?instpred_dlist_cat.
          all: try first [ reflexivity | apply instpred_formula_propeq_com
                         | (rewrite simplify_propeq_val_spec -eq_val_rep_r; reflexivity) ].
          destruct eq_dec; [|rewrite instpred_dlist_singleton; reflexivity]. subst.
          destruct transparent.nat_add_cancel_l, (uip eq_refl e); cbn.
          rewrite instpred_dlist_cat IHtl1 IHtl2. apply propeq_bvapp_split.
        - (*bvcons*)
          unfold simplify_eq_binop_bvcons.
          assert (∀ sm (t : Term w (ty.bvec sm)) (e : S m = sm),
                     instpred (simplify_eq_binop_bvcons' (λ σ t1 t2, dlist_propeq t1 t2) sp
                                 tl1 tl2 t e) ⊣⊢
                     instpred (formula_propeq (term_binop bop.bvcons tl1 tl2)
                                 (eq_rect_r (fun l => Term w (ty.bvec l)) t e))) as H;
            [|apply (H _ tr eq_refl)].
          intros sm t e. destruct sm, t using Term_bvec_case; subst; cbn -[simplify_eq_val];
            rewrite ?instpred_dlist_singleton ?instpred_dlist_cat.
          all: try first [ reflexivity | apply instpred_formula_propeq_com
                         | (rewrite simplify_propeq_val_spec -eq_val_rep_r; reflexivity) ].
          rewrite IHtl1 IHtl2. dependent elimination e. apply propeq_bvcons_split.
      Qed.

      Lemma instpred_dlist_propeq [σ] (t1 t2 : Term w σ) :
        instpred (dlist_propeq t1 t2)
        ⊣⊢ eqₚ t1 t2.
      Proof.
        arw.
      Qed.
        
      Lemma simplify_propeq_spec [σ] (tl tr : Term w σ) :
        instpred (simplify_propeq Term_eqb (fun σ t1 t2 => dlist_propeq t1 t2) tl tr) ⊣⊢ instpred (formula_propeq tl tr).
      Proof.
        induction tl; cbn; arw.
        (* - rewrite instpred_formula_propeq_com'. *)
        (*   arw. *)
        (* - destruct op; cbn; auto. *)
        (*   + (*plus*) *)
        (*     destruct tr using Term_int_case; cbn; arw. *)
        (*     * destruct (Term_eqb_relval_spec tl1 tr1); subst; try destruct a as (sL1 & sL2 & H); try apply secLeakT_spec in sL1; try apply secLeakT_spec in sL2. *)
        (*       cbn in sL1. *)
        (*       { rewrite IHtl2. subst. constructor; intros ι Hwco. *)
        (*         destruct sL1. specialize (fromEntails0 ι Hwco I). unfold instpred_formula_secLeak in fromEntails0. *)
        (*         cbn. unfold instpred_formula_propeq. cbn. *)
        (*         destruct inst, inst, inst; cbn. *)
        (*         all: try contradiction. *)
        (*         all: split; intro H'; try congruence. *)
        (*         all: inversion H'; try apply f_equal; try apply f_equal2. *)
        (*         all: try lia. } *)
        (*       destruct (Term_eqb_relval_spec tl2 tr2); subst; try destruct a as (sL1 & sL2 & H); try apply secLeakT_spec in sL1; try apply secLeakT_spec in sL2. *)
        (*       cbn in sL1. *)
        (*       { rewrite IHtl1. subst. constructor; intros ι Hwco. *)
        (*         destruct sL1. specialize (fromEntails0 ι Hwco I). unfold instpred_formula_secLeak in fromEntails0. *)
        (*         cbn. unfold instpred_formula_propeq. cbn. *)
        (*         destruct inst, inst, inst; cbn. *)
        (*         all: try contradiction. *)
        (*         all: split; intro H'; try congruence. *)
        (*         all: inversion H'; try apply f_equal; try apply f_equal2. *)
        (*         all: try lia. } *)
        (*       destruct (Term_eqb_relval_spec tl1 tr2); subst; try destruct a as (sL1 & sL2 & H); try apply secLeakT_spec in sL1; try apply secLeakT_spec in sL2. *)
        (*       cbn in sL1. *)
        (*       { rewrite IHtl2. subst. constructor; intros ι Hwco. *)
        (*         destruct sL1. specialize (fromEntails0 ι Hwco I). unfold instpred_formula_secLeak in fromEntails0. *)
        (*         cbn. unfold instpred_formula_propeq. cbn. *)
        (*         destruct inst, inst, inst; cbn. *)
        (*         all: try contradiction. *)
        (*         all: split; intro H'; try congruence. *)
        (*         all: inversion H'; try apply f_equal. *)
        (*         all: try lia. *)
        (*         all: apply f_equal2; try lia. *)
        (*       } *)
        (*       destruct (Term_eqb_relval_spec tl2 tr1); subst; try destruct a as (sL1 & sL2 & H); try apply secLeakT_spec in sL1; try apply secLeakT_spec in sL2. *)
        (*       cbn in sL1. *)
        (*       { rewrite IHtl1. subst. constructor; intros ι Hwco. *)
        (*         destruct sL1. specialize (fromEntails0 ι Hwco I). unfold instpred_formula_secLeak in fromEntails0. *)
        (*         cbn. unfold instpred_formula_propeq. cbn. *)
        (*         destruct inst, inst, inst; cbn. *)
        (*         all: try contradiction. *)
        (*         all: split; intro H'; try congruence. *)
        (*         all: inversion H'; try apply f_equal. *)
        (*         all: try lia. *)
        (*         all: apply f_equal2; try lia. *)
        (*       } *)
        (*       arw. *)
        (*     * destruct (Term_eqb_relval_spec tl1 tr1); subst; try destruct a as (sL1 & sL2 & H); try apply secLeakT_spec in sL1; try apply secLeakT_spec in sL2. *)
        (*       cbn in sL1. *)
        (*       { rewrite IHtl2. subst. constructor; intros ι Hwco. *)
        (*         destruct sL1. specialize (fromEntails0 ι Hwco I). unfold instpred_formula_secLeak in fromEntails0. *)
        (*         cbn. unfold instpred_formula_propeq. cbn. *)
        (*         destruct inst, inst, inst; cbn. *)
        (*         all: try contradiction. *)
        (*         all: split; intro H'; try congruence. *)
        (*         all: inversion H'; try apply f_equal. *)
        (*         all: try lia. *)
        (*         all: apply f_equal2; try lia. *)
        (*       } *)
        (*       destruct (Term_eqb_relval_spec tl2 tr1); subst; try destruct a as (sL1 & sL2 & H); try apply secLeakT_spec in sL1; try apply secLeakT_spec in sL2. *)
        (*       cbn in sL1. *)
        (*       { rewrite IHtl1. subst. constructor; intros ι Hwco. *)
        (*         destruct sL1. specialize (fromEntails0 ι Hwco I). unfold instpred_formula_secLeak in fromEntails0. *)
        (*         cbn. unfold instpred_formula_propeq. cbn. *)
        (*         destruct inst, inst, inst; cbn. *)
        (*         all: try contradiction. *)
        (*         all: split; intro H'; try congruence. *)
        (*         all: inversion H'; try apply f_equal. *)
        (*         all: try lia. *)
        (*         all: apply f_equal2; try lia. *)
        (*       } *)
        (*       arw. *)
        (*   + (*minus*) unfold simplify_eq_binop_minus. arw. *)
        (*     (* constructor; intros ι _; cbn. lia. *) *)
        (*   + (*times*) unfold simplify_eq_binop_times. arw. *)
        (*     (* constructor; intros ι _; cbn. lia. *) *)
        (*   + (*and*) *)
        (*     destruct tr using Term_bool_case; cbn -[simplify_eq_val]; try rewrite simplify_propeq_val_spec; arw. *)
        (*     destruct (Term_eqb_spec tl1 tr1); cbn; subst; arw. *)
        (*     destruct (Term_eqb_spec tl2 tr2); subst; arw. *)
        (*   + (*or*) *)
        (*     destruct tr using Term_bool_case; cbn -[simplify_eq_val]; try rewrite simplify_propeq_val_spec; arw. *)
        (*     destruct (Term_eqb_spec tl1 tr1); cbn; subst; arw. *)
        (*     destruct (Term_eqb_spec tl2 tr2); subst; arw. *)
        (*   + (*pair*) *)
        (*     destruct tr using Term_prod_case; cbn -[simplify_eq_val]; try rewrite simplify_propeq_val_spec; auto; arw. *)
        (*     (* rewrite IHtl1 IHtl2. *) *)
        (*     (* rewrite !instpred_formula_propeqₚ'. *) *)
        (*     (* apply eqₚ_term_prod. *) *)
        (*   + (*cons*) destruct tr using Term_list_case; cbn -[simplify_eq_val]; try rewrite simplify_propeq_val_spec; auto; arw. *)
        (*     (* rewrite IHtl1 IHtl2. *) *)
        (*   + (*append*) *)
        (*     destruct tr using Term_list_case; cbn; auto; arw. *)
        (*     destruct (Term_eqb_spec tl1 tr1). subst; cbn; arw. *)
        (*     { rewrite IHtl2. constructor; intros ι _; cbn. *)
        (*       now rewrite app_inv_head_iff. } *)
        (*     destruct (Term_eqb_spec tl2 tr2). subst; cbn; arw. *)
        (*     { rewrite IHtl1. constructor; intros ι _; cbn. *)
        (*       now rewrite app_inv_tail_iff. } *)
        (*     arw. *)
        (*   + (*bvapp*) *)
        (*     assert (∀ mn (t : Term w (ty.bvec mn)) (e : m + n = mn), *)
        (*              instpred (simplify_eq_binop_bvapp' simplify_eq *)
        (*                          tl1 tl2 t e) ⊣⊢ *)
        (*              eqₚ (term_binop bop.bvapp tl1 tl2) *)
        (*                (eq_rect_r (fun l => Term w (ty.bvec l)) t e)); eauto. *)
        (*     intros mn t e. destruct mn, t using Term_bvec_case; subst; cbn; arw. *)
        (*     destruct eq_dec; arw; subst. *)
        (*     destruct transparent.nat_add_cancel_l, (uip eq_refl e); cbn. *)
        (*     arw. rewrite IHtl1 IHtl2. arw_slow. *)
        (*   + (*bvcons*) *)
        (*     assert (∀ sm (t : Term w (ty.bvec sm)) (e : S m = sm), *)
        (*               instpred (simplify_eq_binop_bvcons' simplify_eq *)
        (*                           tl1 tl2 t e) ⊣⊢ *)
        (*               eqₚ (term_binop bop.bvcons tl1 tl2) *)
        (*                 (eq_rect_r (fun l => Term w (ty.bvec l)) t e)); eauto. *)
        (*     intros sm t e. destruct sm, t using Term_bvec_case; subst; cbn; arw. *)
        (*     rewrite IHtl1 IHtl2. dependent elimination e; arw; arw_slow. *)
        (*   + (*relop*) *)
        (*     clear IHtl1 IHtl2. revert r tl1 tl2. *)
        (*     induction tr using Term_bool_ind; cbn; intros rop tl1 tl2; arw. *)
        (*     rewrite eqₚ_term_not eqₚ_term_not_relop. *)
        (*     destruct rop; cbn; auto. *)
        - (*binop*) apply simplify_propeq_binop_spec; [exact IHtl1 | exact IHtl2].
        - destruct op; cbn; auto.
          + (*inl*) destruct tr using Term_sum_case; cbn; auto; arw; arw_slow.
            * destruct v.
              { rewrite simplify_propeq_val_spec.
                constructor; intros ι _; unfold repₚ; cbn.
                destruct (inst tl ι); cbn; split; intro H; ty.rv_split;
                  repeat match goal with H : inl _ = inl _ |- _ => injection H as H end;
                  subst; reflexivity.
              }
              unfold simplify_eq_unop_inl_val; cbn; rewrite ?instpred_dlist_error.
              constructor; intros ι _; unfold repₚ; cbn.
              destruct (inst tl ι); cbn; split; [intros []|intro H; ty.rv_split; discriminate].
          + (*inr*) destruct tr using Term_sum_case; cbn; auto; arw; arw_slow.
            * destruct v.
              { unfold simplify_eq_unop_inr_val; cbn; rewrite ?instpred_dlist_error.
                constructor; intros ι _; unfold repₚ; cbn.
                destruct (inst tl ι); cbn; split; [intros []|intro H; ty.rv_split; discriminate].
              }
              rewrite simplify_propeq_val_spec.
              constructor; intros ι _; unfold repₚ; cbn.
              destruct (inst tl ι); cbn; split; intro H; ty.rv_split;
                repeat match goal with H : inr _ = inr _ |- _ => injection H as H end;
                subst; reflexivity.
          + (*rev*) apply simplify_propeq_unop_rev_spec; exact IHtl.
          + (*get_slice_int*)
            unfold simplify_eq_unop_get_slice_int.
            destruct (Term_eqb_spec (term_get_slice_int tl) tr); subst; arw.
          + (*signed*)
            destruct tr using Term_int_case; cbn; arw;
              try (constructor; intros ι _; cbn; lia).
            destruct eq_dec; subst; arw;
              try (constructor; intros ι _; cbn; lia).
        (* - destruct tr using Term_tuple_case; cbn; arw. *)
        (*   induction IH; cbn. *)
        (*   { (* TODO: I didn't feel like making a lemma for this, but I should*) *)
        (*     constructor. intros ι _. destruct v. *)
        (*     split. *)
        (*     - cbn. auto. *)
        (*     - cbn. intro H. constructor. *)
        (*   } *)
        (*   destruct v; cbn; arw. *)
        (*   rewrite instpred_dlist_cat. *)
        (*   rewrite simplify_propeq_val_spec. *)
        (*   rewrite repₚ_term_tuple_snoc. apply bi.sep_proper. *)
        (*   by rewrite IHIH. auto. *)
        (*   induction ts0. *)
        (*   + env.destroy ts. cbn. (* TODO: Should have specialised lemma for this *) *)
        (*     constructor. intros ι _. unfold instpred_formula_propeq. cbn. split. *)
        (*     * auto. *)
        (*     * intro H. constructor. *)
        (*   + env.destroy ts. cbn. rewrite instpred_dlist_cat. rewrite IHts0. *)
        (*     rewrite IH. *)
        (*     Search instpred_formula_propeq term_tuple. *)

        - destruct tr using Term_union_case; cbn; arw.
          { unfold simplify_eq_union_val.
            rewrite repₚ_inversion_union.
            (* assert (forall t, ty.valToRelVal (σ := ty.union _) v = ty.unionv_fold_rel U (existT K0 t) <-> SyncVal (unionv_unfold U v) = ty.liftUnOpRV (λ a : Val (unionk_ty U K0), existT K0 a) t). *)
            (* { split; intros H. *)
            (*   + apply (f_equal (ty.unionv_unfold_rel U)) in H. *)
            (*     by rewrite ty.unionv_unfold_fold_rel in H. *)
            (*   + Search SyncVal ty.liftUnOpRV. *)
            (*     apply symmetry in H. *)
            (*     apply ty.liftUnOpRVSyncVal in H. *)
            (*     destruct H as (v' & -> & eqv). *)
            (*     cbn. rewrite eqv. by rewrite unionv_fold_unfold. *)
            (* } *)
            destruct (unionv_unfold U v) as [] eqn:eqv.
            destruct eq_dec.
            + rewrite simplify_propeq_val_spec.
              destruct e.
              cbn.
              constructor. intros ι _.
              split; intros H.
              * exists (ty.valToRelVal v0).
                split; auto. cbn. rewrite <- eqv. by rewrite unionv_fold_unfold.
              * destruct H as (rv & eqrv & rept).
                apply (f_equal (unionv_fold U)) in eqv. rewrite unionv_fold_unfold in eqv.
                rewrite eqv in eqrv.
                destruct rv as [a b]; cbn in *. rewrite rept. clear rept. hnf in eqrv.
                ty.rv_split;
                  apply unionv_fold_inj in HL, HR;
                  apply Eqdep_dec.inj_pair2_eq_dec in HL; try (intros x y; apply eq_dec);
                  apply Eqdep_dec.inj_pair2_eq_dec in HR; try (intros x y; apply eq_dec);
                  subst; reflexivity.
            + constructor. intros ι _. split; intro H; try contradiction.
              destruct H as (rv & eqrv & reprv). hnf in eqrv.
              apply (f_equal ty.projLeftRV) in eqrv. cbn in eqrv.
              apply (f_equal (unionv_unfold U)) in eqrv. rewrite unionv_unfold_fold in eqrv.
              rewrite eqv in eqrv. congruence.
          }
          destruct eq_dec; subst; arw.
          now rewrite eqₚ_term_union_neq.
        - destruct tr using Term_record_case; cbn; arw; arw_slow.
          + rewrite -(recordv_fold_unfold R v).
            rewrite repₚ_term_record.
            generalize (recordv_unfold R v); intros vs.
            unfold simplify_eq_record_val.
            rewrite recordv_unfold_fold.
            induction IH; destruct (env.view vs); arw.
            arw_slow. rewrite IHIH.
            rewrite <- repₚ_namedenv_snoc.
            rewrite simplify_propeq_val_spec.
            auto.
          + constructor. intros ι Hwco.
            assert ((instpred (dlist_propeq (term_record R ts0) (term_record R ts)) ι) <-> ty.unliftNamedEnv (inst ts ι) = ty.unliftNamedEnv (inst ts0 ι)) as Hdefault.
            { rewrite <- eqₚ_term_record.
              destruct (instpred_dlist_propeq (term_record R ts0) (term_record R ts)).
              by rewrite (fromBientails0 ι Hwco).
            }
            rewrite eqₚ_term_record.
            revert Hdefault.
            generalize (dlist_propeq (term_record R ts0) (term_record R ts)).
            revert ts ts0 IH.
            generalize (recordf_ty R) as Δ.
            clear R.
            intros Δ ts ts0 IH.
            induction IH; destruct (env.view ts0); arw.
            intros default eqdefault.
            destruct E; arw.
            clear default eqdefault IH IHIH.
            env.destroy E0.
            cbn.
            assert (∀ x y, instpred (cat x y) ι <-> instpred x ι /\ instpred y ι).
            { intros x y.
              destruct (instpred_dlist_cat x y).
              rewrite (fromBientails0 ι Hwco).
              auto.
            }
            rewrite H. clear H.
            destruct (q v). rewrite (fromBientails0 ι Hwco). clear fromBientails0.
            destruct (instpred_formula_propeqₚ' d v). rewrite (fromBientails0 ι Hwco). clear fromBientails0.
            destruct (@instpred_dlist_empty w). rewrite (fromBientails0 ι Hwco). clear fromBientails0.
            (* TODO: This proof is done at the wrong level leading to a lot of boilerplate, refactor this *)
            cbn.
            rewrite leftid_true_and.
            destruct inst, inst; cbn.
            all: split; intro H; by depelim H.
      Qed.

    End SimplifyPropeqSpec.


    #[export] Notation dlist_secLeak t := (singleton (formula_secLeak t)).
    #[export] Notation dlist_true := (singleton (formula_true)).

    (* Split off a literal summand, in EITHER argument order -- `peval` leaves
       both (`0x10 + sp` from a register spec, `q + 0` from a placement).  The
       returned pair is NON-DEPENDENT apart from the shared width `n`, which is
       what keeps Equations from having to let two type indices meet. *)
    Equations bvadd_split_val {Σ n} (t : Term Σ (ty.bvec n))
      : option (Val (ty.bvec n) * Term Σ (ty.bvec n)) :=
      bvadd_split_val (term_binop bop.bvadd (term_val _ v) s) := Some (v, s);
      bvadd_split_val (term_binop bop.bvadd s (term_val _ v)) := Some (v, s);
      bvadd_split_val _ := None.

    Lemma bvadd_split_val_spec {Σ n} (t : Term Σ (ty.bvec n)) v s :
      bvadd_split_val t = Some (v, s) ->
      t = term_binop bop.bvadd (term_val (ty.bvec n) v) s
      \/ t = term_binop bop.bvadd s (term_val (ty.bvec n) v).
    Proof.
      funelim (bvadd_split_val t); intros Heq; try discriminate;
        inversion Heq; subst; auto.
    Qed.

    (* The SEMANTIC form, which normalises both argument orders to ONE shape by
       paying `bv.add_comm` once here rather than doubling the case analysis in
       every consumer. *)
    Lemma bvadd_split_val_inst {Σ n} (t : Term Σ (ty.bvec n)) v s :
      bvadd_split_val t = Some (v, s) ->
      forall ι : Valuation Σ,
        inst t ι = bop.evalRel bop.bvadd (SyncVal v) (inst s ι).
    Proof.
      intros H ι. apply bvadd_split_val_spec in H as [-> | ->]; cbn; [reflexivity|].
      unfold bop.evalRel, ty.liftBinOp, ty.liftBinOpRV; cbn.
      destruct (inst s ι) as [a1 a2]; cbn; f_equal; apply bv.add_comm.
    Qed.

    (* R3 (PLAN-relval-pair §6, §12.3): the operators whose evaluation is
       injective PER PROJECTION, so [secLeak (op t1 t2)] IS
       [secLeak t1 /\ secLeak t2] -- exact, hence sound on assumptions and
       goals alike.  [cons] and [rev] at every element type, [bvapp] at fixed
       widths.  NOT [append] (needs length facts) and NOT [regroup] (junk at
       most type pairs).  CFGVer's arrv publicness-by-framing needs these:
       a take's [vs = x :: r] must hand [secLeak vs] to x and r. *)
    Definition binop_secLeak_split {σ1 σ2 σ} (op : BinOp σ1 σ2 σ) : bool :=
      match op with
      | bop.cons => true
      | bop.bvapp => true
      | _ => false
      end.
    Definition unop_secLeak_split {σ1 σ2} (op : UnOp σ1 σ2) : bool :=
      match op with
      | uop.rev => true
      | _ => false
      end.

    Lemma secLeak_binop_split {σ1 σ2 σ} (op : BinOp σ1 σ2 σ) a b :
      binop_secLeak_split op = true ->
      secLeak (bop.evalRel op a b) <-> secLeak a /\ secLeak b.
    Proof.
      intros Hop. revert a b. destruct op; try discriminate Hop;
        intros [a1 a2] [b1 b2]; unfold secLeak; cbn; split.
      - intros H. injection H as -> ->. split; reflexivity.
      - intros [-> ->]. reflexivity.
      - intros H. apply bv.app_inj in H as [-> ->]. split; reflexivity.
      - intros [-> ->]. reflexivity.
    Qed.

    Lemma secLeak_unop_split {σ1 σ2} (op : UnOp σ1 σ2) a :
      unop_secLeak_split op = true ->
      secLeak (uop.evalRel op a) <-> secLeak a.
    Proof.
      intros Hop. revert a. destruct op; try discriminate Hop;
        intros [a1 a2]; unfold secLeak; cbn; split; [|now intros ->].
      intros H. rewrite -(rev_involutive a1) -(rev_involutive a2) H. reflexivity.
    Qed.

    Section SimplifySecLeak.
      Context [w : World].


      (* [secLeak] is NOT decomposed over an operator: [secLeak (op t1 t2)] is
         implied by, but not equivalent to, [secLeak t1 /\ secLeak t2] ([x - x]
         is public for any [x]).  This simplifier runs on assumptions too, so a
         decomposition would assume publicness that was never established.
         Instead it is split where the operator is injective (R3, above),
         otherwise discharged when [secLeakT] proves it from the path
         condition, and kept as is otherwise.  The split comes FIRST: right
         after a substitution [vs := x :: r] the path condition holds the
         exact term [secLeak (x :: r)], so [secLeakT] would answer "known" and
         ResimpSecLeak would get [formula_true] instead of the parts. *)
      Definition simplify_secLeak_core [σ] (t : Term w σ) : DList w :=
        match t with
        | term_var x          => dlist_secLeak t
        | term_val _ v        => dlist_true
        | term_relval r rv     => singleton (formula_bool (term_val ty.bool (secLeak_bool rv)))
        | term_binop op t1 t2 =>
            if binop_secLeak_split op
            then cat (dlist_secLeak t1) (dlist_secLeak t2)
            else if secLeakT t then dlist_true else dlist_secLeak t
        | term_unop op t1     =>
            if unop_secLeak_split op then dlist_secLeak t1
            else if secLeakT t then dlist_true else dlist_secLeak t
        | term_tuple tls      => dlist_secLeak t (* TODO: Improve this by splitting this up into several smaller secLeak statements, I need a foldr function on Env for this *)
        | term_union U K tl   => dlist_secLeak tl
        | term_record R tls   => dlist_secLeak t (* TODO: Same as for tuples *)
        end.

      (* The one decomposition that IS exact: adding a literal is injective
         per projection, so [secLeak (c + s) <-> secLeak s] holds on
         assumptions and goals alike.  Strips ONE literal summand (peval folds
         literals, so a normal form has at most one).  Needed when the path
         condition knows [secLeak (0x8 + q)] and the goal is
         [secLeak (0xc + q)]: both become [secLeak q]. *)
      Definition simplify_secLeak [σ] (t : Term w σ) : DList w :=
        match σ return Term w σ -> DList w with
        | ty.bvec n => fun t =>
            match bvadd_split_val t with
            | Some (_, s) => simplify_secLeak_core s
            | None        => simplify_secLeak_core t
            end
        | _ => fun t => simplify_secLeak_core t
        end t.

    End SimplifySecLeak.
    #[global] Arguments simplify_secLeak_core [w] [σ] t.
    #[global] Arguments simplify_secLeak [w] [σ] t.

    Section SimplifySecLeakSpec.
      Context [w : World].

      Lemma instpred_formula_secLeak_union {U : unioni} {K0 : unionk U} (t : Term w (unionk_ty U K0)) :
        instpred (formula_secLeak t) ⊣⊢ instpred_formula_secLeak (term_union U K0 t).
      Proof.
        crushPredEntails2; unfold instpred_formula_secLeak, secLeak in *; cbn in *;
          destruct (inst t ι) as [a b]; cbn in *.
        - now rewrite H0.
        - apply unionv_fold_inj in H0.
          apply Eqdep_dec.inj_pair2_eq_dec in H0; [exact H0|intros x y; apply eq_dec].
      Qed.

      Lemma instpred_formula_secLeak_binop_split {σ1 σ2 σ3} (t1 : Term w σ1) (t2 : Term w σ2)
        (op : BinOp σ1 σ2 σ3) :
        binop_secLeak_split op = true ->
        instpred (formula_secLeak t1) ∗ instpred (formula_secLeak t2)
          ⊣⊢ instpred (formula_secLeak (term_binop op t1 t2)).
      Proof.
        intros Hop. constructor. intros ι _. cbn. unfold instpred_formula_secLeak; cbn.
        symmetry. apply (secLeak_binop_split op _ _ Hop).
      Qed.

      Lemma instpred_formula_secLeak_unop_split {σ1 σ2} (t1 : Term w σ1) (op : UnOp σ1 σ2) :
        unop_secLeak_split op = true ->
        instpred (formula_secLeak t1) ⊣⊢ instpred (formula_secLeak (term_unop op t1)).
      Proof.
        intros Hop. constructor. intros ι _. cbn. unfold instpred_formula_secLeak; cbn.
        symmetry. apply (secLeak_unop_split op _ Hop).
      Qed.

      Lemma simplify_secLeak_core_spec [σ] (t : Term w σ) :
        instpred (simplify_secLeak_core t) ⊣⊢ instpred (formula_secLeak t).
      Proof.
        induction t; cbn; arw.
        - rewrite ?instpred_dlist_singleton.
          destruct v as [l r]. constructor. intros ι _. cbn.
          unfold secLeak_bool, instpred_formula_secLeak, secLeak, repₚ in *. cbn.
          destruct (eq_dec l r); cbn; split; intros H; ty.rv_split;
            try assumption; try reflexivity; try discriminate; try contradiction; try done.
        - destruct (binop_secLeak_split op) eqn:Hop.
          + rewrite instpred_dlist_cat !instpred_dlist_singleton.
            apply instpred_formula_secLeak_binop_split; exact Hop.
          + match goal with |- context[if ?b then _ else _] => destruct b eqn:Hs end.
            * rewrite instpred_dlist_singleton.
              assert (Hs' : secLeakT (term_binop op t1 t2))
                by (rewrite /Is_true; first [rewrite Hs; exact I | cbn; rewrite Hs; exact I]).
              apply secLeakT_spec in Hs'.
              iSplit; [iIntros "_"; iApply Hs'|iIntros "_"; done].
            * rewrite instpred_dlist_singleton. reflexivity.
        - destruct (unop_secLeak_split op) eqn:Hop.
          + rewrite !instpred_dlist_singleton.
            apply instpred_formula_secLeak_unop_split; exact Hop.
          + match goal with |- context[if ?b then _ else _] => destruct b eqn:Hs end.
            * rewrite instpred_dlist_singleton.
              assert (Hs' : secLeakT (term_unop op t))
                by (rewrite /Is_true; first [rewrite Hs; exact I | cbn; rewrite Hs; exact I]).
              apply secLeakT_spec in Hs'.
              iSplit; [iIntros "_"; iApply Hs'|iIntros "_"; done].
            * rewrite instpred_dlist_singleton. reflexivity.
        - apply instpred_formula_secLeak_union.
      Qed.

      Lemma simplify_secLeak_spec [σ] (t : Term w σ) :
        instpred (simplify_secLeak t) ⊣⊢ instpred (formula_secLeak t).
      Proof.
        destruct σ; cbn [simplify_secLeak]; try apply simplify_secLeak_core_spec.
        destruct (bvadd_split_val t) as [[v s]|] eqn:Hsplit;
          [|apply simplify_secLeak_core_spec].
        rewrite simplify_secLeak_core_spec.
        constructor; intros ι _; cbn. unfold instpred_formula_secLeak; cbn.
        rewrite (bvadd_split_val_inst t Hsplit ι).
        destruct (inst s ι) as [a b]. unfold secLeak; cbn. split; intros H.
        - now rewrite H.
        - eapply bv.add_cancel_l; exact H.
      Qed.
    End SimplifySecLeakSpec.

    (* RE-SPLITTING a public variable after the unifier substitutes it
       (PLAN-arrv Phase D, 2026-10-25).  `wsubst` rewrites the OLD path
       condition by plain substitution, so `secLeak vs` becomes
       `secLeak (x :: r)` once `vs := x :: r`, and nothing simplifies it: a
       later `secLeak r` is not found (assumption_formula is syntactic).
       solver_generic therefore appends, after a non-trivial unification, the
       split of every `secLeak (term_var x)` of the old path condition whose x
       the substitution replaced by a non-variable.  Each appended formula is
       implied by the new path condition, so SolverSpec is unchanged.  Only
       secLeak, by decision: publicness must pass to the parts by framing. *)
    Section ResimpSecLeak.

      Definition resimp_secLeak1 {w : World} {σ} (t : Term w σ) : PathCondition w :=
        match run (simplify_secLeak (w := w) (peval t)) with
        | Some D => D
        | None => ctx.nil
        end.

      Definition resimp_secLeak_term {w : World} {σ} (R : PathCondition w)
        (u : Term w σ) : PathCondition w :=
        match u with
        | term_var _ => R
        | _ => ctx.cat R (resimp_secLeak1 u)
        end.

      Fixpoint resimp_secLeak {Σ0} {w1 : World} (ζ : Sub Σ0 w1)
        (C : PathCondition Σ0) : PathCondition w1 :=
        match C with
        | ctx.nil => ctx.nil
        | ctx.snoc C F =>
            let R := resimp_secLeak ζ C in
            match F with
            | formula_secLeak (term_var _ as t) => resimp_secLeak_term R (subst t ζ)
            | _ => R
            end
        end.

      Definition tri_is_id {w0 w1 : World} (ν : Tri w0 w1) : bool :=
        match ν with tri_id => true | _ => false end.

      Definition resimp_secLeak_tri {w0 w1 : World} (ν : Tri w0 w1) : PathCondition w1 :=
        if tri_is_id ν then ctx.nil else resimp_secLeak (sub_triangular ν) (wco w0).

      Lemma resimp_secLeak1_sound {w : World} {σ} (t : Term w σ) :
        instpred (formula_secLeak t) ⊢ instpred (resimp_secLeak1 t).
      Proof.
        unfold resimp_secLeak1.
        pose proof (instpred_run (simplify_secLeak (w := w) (peval t))) as Hrun.
        rewrite simplify_secLeak_spec in Hrun.
        assert (Hp : instpred (formula_secLeak (peval t)) ⊣⊢ instpred (w := w) (formula_secLeak t)).
        { constructor; intros ι Hwco; cbn; unfold instpred_formula_secLeak.
          now rewrite peval_sound. }
        rewrite Hp in Hrun.
        destruct run as [D|]; cbn in *.
        - apply (bi.equiv_entails_1_2 _ _ Hrun).
        - rewrite -Hrun. iIntros "[]".
      Qed.

      (* for a VARIABLE t: with a constructor, unification reduces
         resimp_secLeak1 and times out *)
      Lemma resimp_secLeak_cat {w : World} {τ} (t : Term w τ) (R : PathCondition w)
        (P : Pred w) :
        (P ⊢ instpred R) ->
        P ∗ instpred (formula_secLeak t) ⊢ instpred (ctx.cat R (resimp_secLeak1 t)).
      Proof.
        intros HR. rewrite instpred_cat.
        apply bi.sep_mono; [exact HR | apply resimp_secLeak1_sound].
      Qed.

      Lemma resimp_secLeak_term_sound {w : World} {τ} (u : Term w τ)
        (R : PathCondition w) (P : Pred w) :
        (P ⊢ instpred R) ->
        P ∗ instpred (formula_secLeak u) ⊢ instpred (resimp_secLeak_term R u).
      Proof.
        intros HR. destruct u; unfold resimp_secLeak_term;
          [iIntros "[H _]"; by iApply HR|..];
          exact (@resimp_secLeak_cat _ _ _ R P HR).
      Qed.

      Lemma resimp_secLeak_sound {Σ0} {w1 : World} (ζ : Sub Σ0 w1) (C : PathCondition Σ0) :
        instpred (w := w1) (subst C ζ) ⊢ instpred (resimp_secLeak ζ C).
      Proof.
        induction C as [|C IH F]; cbn -[resimp_secLeak_term].
        - iIntros "_"; done.
        - destruct F; cbn -[resimp_secLeak_term]; try (iIntros "[H _]"; by iApply IH).
          destruct t; cbn -[resimp_secLeak_term]; try (iIntros "[H _]"; by iApply IH).
          now apply resimp_secLeak_term_sound.
      Qed.

      Lemma resimp_secLeak_tri_valid {w0 w1 : World} (ν : Tri w0 w1) :
        ⊢ instpred (resimp_secLeak_tri ν).
      Proof.
        unfold resimp_secLeak_tri. destruct tri_is_id; [cbn; done|].
        rewrite -resimp_secLeak_sound -sub_acc_triangular.
        constructor. intros ι Hwco _. apply instpred_prop.
        now apply (ent_acc_sub (acc_triangular ν)).
      Qed.

    End ResimpSecLeak.


    Definition simplify_relopb {Σ σ} (op : RelOp σ)
      (t1 t2 : STerm σ Σ) : DList Σ :=
      match term_get_val t1 , term_get_val t2 with
      | Some v1 , Some v2 => if bop.eval_relop_val op v1 v2 then empty else error
      | _       , _       => singleton (formula_relop op t1 t2)
      end.

    Definition simplify_relopb_spec {w : World} {σ} (op : RelOp σ)
      (t1 t2 : STerm σ w) :
      instpred (simplify_relopb op t1 t2) ⊣⊢ instpred (formula_relop op t1 t2).
    Proof.
      unfold simplify_relopb.
      destruct (term_get_val_spec t1) as [v1|]; arw; try now rewrite formula_relop_term'. subst.
      destruct (term_get_val_spec t2) as [v2|]; arw; try now rewrite formula_relop_term'. subst.
      destruct (bop.eval_relop_val_spec op v1 v2); arw.
    Qed.
    #[local] Opaque simplify_relopb.
    #[export] Hint Rewrite @simplify_relopb_spec : uniflogic.

    (* [0 <= unsigned rv] holds on BOTH sides ([unsigned] is non-negative),
       whatever [rv] is: relops are pointwise.  Under the old tagged RelVal it
       collapsed to False on a NonSyncVal and so was equivalent to [secLeak rv];
       that equivalence is gone, and with it the rewrite to [secLeak]. *)
    Lemma unsigned_nonneg_relop {n} (rv : RelVal (ty.bvec n)) :
      let rp := bop.eval_relop_relprop bop.le (SyncVal 0%Z) (uop.evalRel uop.unsigned rv) in
      ty.projLeftRV rp /\ ty.projRightRV rp.
    Proof.
      destruct rv as [a b]; cbn.
      pose proof (bv.unsigned_bounds a); pose proof (bv.unsigned_bounds b);
        try unfold bv.unsigned in *; split; lia.
    Qed.

    Definition peval_formula_le' {Σ} (t : Term Σ ty.int) : Formula Σ :=
      let default := formula_le (term_val ty.int 0%Z) t in
      Term_int_case (fun _ => Formula Σ)
        (fun (*var*) l lIn => default)
        (fun (*val*) v => if (0 <=? v)%Z then formula_true else formula_false)
        (fun (*relval*) v => default)
        (fun (*plus*) _ _ => default)
        (fun (*minus*) _ _ => default)
        (fun (*times*) _ _ => default)
        (fun (*land*) _ _ => default)
        (fun (*neg*) _ => default)
        (fun (*signed*) _ _ => default)
        (* [0 <= unsigned t] is TRUE: relops hold pointwise, and [unsigned]
           is non-negative on each side (bv.unsigned_bounds).  It says NOTHING
           about [t] being public -- rewriting it to [secLeak t], as the
           tagged RelVal model allowed, would turn an assumed bound into an
           assumed publicness fact. *)
        (fun (*unsigned*) _ t' => formula_true)
        t.

    Definition peval_formula_le {Σ} (t1 t2 : Term Σ ty.int) : Formula Σ :=
      peval_formula_le' (peval (term_minus t2 t1)).

    Definition peval_formula_lt {Σ} (t1 t2 : Term Σ ty.int) : Formula Σ :=
      peval_formula_le (term_plus t1 (term_val ty.int 1%Z)) t2.

    (* Definition peval_formula_relop_neg {Σ σ} (op : RelOp σ) : *)
    (*   Term Σ σ → Term Σ σ → Formula Σ := *)
    (*   match op in (RelOp t) return (Term Σ t → Term Σ t → Formula Σ) with *)
    (*   | @bop.eq _ σ0 => formula_neq *)
    (*   | @bop.neq _ σ0 => formula_eq *)
    (*   | bop.le => flip peval_formula_lt *)
    (*   | bop.lt => flip peval_formula_le *)
    (*   | @bop.bvsle _ n => flip formula_bvslt *)
    (*   | @bop.bvslt _ n => flip formula_bvsle *)
    (*   | @bop.bvule _ n => flip formula_bvult *)
    (*   | @bop.bvult _ n => flip formula_bvule *)
    (*   end. *)

    Lemma peval_formula_le'_spec [w : World] (t : Term w ty.int) :
      instpred (peval_formula_le' t) ⊣⊢
      instpred (formula_le (term_val ty.int 0%Z) t).
    Proof.
      destruct t using Term_int_case; cbn; try reflexivity.
      - constructor; intros ι _; cbn.
        destruct (Z.leb_spec 0 i) as [Hi|Hi]; split; intros Hx;
          unfold instpred_formula_relop in *; cbn in *; try easy;
          try (destruct Hx; lia); try (split; lia); try exact I.
      (* [0 <= unsigned t] is always true: see unsigned_nonneg_relop. *)
      - constructor; intros ι _; cbn.
        unfold instpred_formula_relop; cbn.
        split; [intros _; apply unsigned_nonneg_relop | intros _; exact I].
    Qed.

    Lemma peval_formula_le_spec [w : World] (t1 t2 : Term w ty.int) :
      instpred (peval_formula_le t1 t2) ⊣⊢ instpred (formula_le t1 t2).
    Proof.
      unfold peval_formula_le. rewrite peval_formula_le'_spec.
      constructor; intros ι _. cbn.
      Search instpred "≡".
      unfold instpred_formula_relop.
      rewrite peval_sound. cbn. destruct inst, inst; cbn; lia.
    Qed.

    Lemma peval_formula_lt_spec [w : World] (t1 t2 : Term w ty.int) :
      instpred (peval_formula_lt t1 t2) ⊣⊢ instpred (formula_lt t1 t2).
    Proof.
      unfold peval_formula_lt. rewrite peval_formula_le_spec.
      constructor; intros ι _; cbn.
      unfold instpred_formula_relop.
      cbn. destruct inst, inst; cbn; lia.
    Qed.

    #[local] Hint Rewrite peval_formula_le_spec peval_formula_lt_spec : uniflogic.

    (* Lemma instpred_peval_formula_relop_neg [w : World] {σ} (op : RelOp σ) *)
    (*   (t1 t2 : Term w σ) : *)
    (*   instpred (peval_formula_relop_neg op t1 t2) ⊣⊢ *)
    (*   repₚ (T := STerm ty.bool) false (term_binop (bop.relop op) t1 t2). *)
    (* Proof. *)
    (*   destruct op; cbn; arw; *)
    (*     rewrite ?formula_relop_term' ?rep_binop_neq_eq ?rep_binop_lt_ge *)
    (*       ?rep_binop_slt_sge ?rep_binop_slt_sge ?rep_binop_ult_uge; easy. *)
    (* Qed. *)

    Definition simplify_le {Σ} (t1 t2 : Term Σ ty.int) : DList Σ :=
      singleton (peval_formula_le t1 t2).

    Definition simplify_lt {Σ} (t1 t2 : Term Σ ty.int) : DList Σ :=
      singleton (peval_formula_lt t1 t2).

    Lemma simplify_le_spec [w : World] (s t : Term w ty.int) :
      instpred (simplify_le s t) ⊣⊢ instpred (formula_relop bop.le s t).
    Proof.
      rewrite <- peval_formula_le_spec.
      unfold simplify_le. arw.
    Qed.

    Lemma simplify_lt_spec [w : World] (s t : Term w ty.int) :
      instpred (simplify_lt s t) ⊣⊢ instpred (formula_relop bop.lt s t).
    Proof.
      rewrite <- peval_formula_lt_spec.
      unfold simplify_lt. arw.
    Qed.

    #[export] Hint Resolve simplify_le_spec simplify_lt_spec : core.

    (* ---- eq/neq cancellation of a common summand -------------------------
       peval_bvadd canonicalises a symbolic sum to CONSTANT-HEADED form
       `c ⊕ t` (PartialEvaluation.v:549-552).  So a loop whose exit test is a
       pointer compare over a symbolic base -- `bne a0, a1` with both operands
       base-relative, which is what clang emits for a byte-array walk -- yields
       `formula_relop neq (c1 ⊕ p) (c2 ⊕ p)` at every taken iteration.  Nothing
       decides those, so they accumulate in the path condition and every later
       step pays for them.  Measured on BearSSL check_scalar loop 1: ~3x the
       total VC cost at 32 iterations, and it makes the growth EXPONENT itself
       climb rather than stay fixed.  See CFGVer/PLAN-byte-memory.md §10.

       bv.add is injective in each argument (bv.add_cancel_r), so at the Val
       level `c1 + a = c2 + a  <->  c1 = c2` holds UNCONDITIONALLY -- no no-wrap
       side condition, unlike most bitvector rules.  Both constants are values,
       so the cancelled comparison decides outright and no formula survives.

       TWO RESTRICTIONS, both load-bearing:

       - EQ/NEQ ONLY.  Ordering relops do NOT cancel, because bv addition
         wraps: 0 <=u 0xFFFFFFFF, yet 0+1 >u 0xFFFFFFFF+1.  Hence the explicit
         bop.neq arm below rather than folding this into the catch-all.

       - THE SHARED OPERAND MUST BE KNOWN PUBLIC.  instpred_formula_relop sends
         a NonSyncVal operand to False (Formulas.v:147), so over a SECRET base
         the original formula is False while the cancelled one is decidable and
         may be True; cancelling unguarded would be unsound in a goal position.
         `secLeakT` discharges this from the path condition, and the base of any
         verifiable program is public.  Same reasoning and same guard as the
         `0 <= unsigned rv` note at simplify_relopb above. *)
    (* No [(noeqns)]: the inversion proof below (`bvadd_cancel_pair_spec`)
       goes through `funelim`, which needs the generated `FunctionalElimination`
       instance -- `noeqns` suppresses exactly that, and `funelim` then fails
       with "Could not find an instance for FunctionalElimination t2 ...".
       Manually destructing t1/t2 down to shape instead was tried and works,
       but blows up into an unreadable term (the compiled Equations match
       exposes every other BinOp/Term constructor's impossibility proof
       inline); funelim discharges all of those automatically. *)
    Equations bvadd_cancel_pair {Σ n} (t1 t2 : Term Σ (ty.bvec n))
      : option (Val (ty.bvec n) * Val (ty.bvec n) * Term Σ (ty.bvec n)) :=
      bvadd_cancel_pair (term_binop bop.bvadd (term_val _ v1) s1)
                        (term_binop bop.bvadd (term_val _ v2) s2) :=
        if Term_eqb s1 s2 then Some (v1, v2, s1) else None;
      bvadd_cancel_pair _ _ := None.

    Lemma bvadd_cancel_pair_spec {Σ n} (t1 t2 : Term Σ (ty.bvec n)) v1 v2 s :
      bvadd_cancel_pair t1 t2 = Some (v1, v2, s) ->
      t1 = term_binop bop.bvadd (term_val _ v1) s /\
      t2 = term_binop bop.bvadd (term_val _ v2) s.
    Proof.
      funelim (bvadd_cancel_pair t1 t2); intros Heq; try discriminate.
      destruct (Term_eqb s1 s2) eqn:Heqb; cbn in Heq; try discriminate.
      pose proof (Term_eqb_spec s1 s2) as Hr; rewrite Heqb in Hr; inversion Hr; subst.
      inversion Heq; subst; auto.
    Qed.

    (* [op] is NOT restricted to eq/neq by [σ] alone -- [RelOp (ty.bvec n)]
       also contains the four ordering relops, for which cancellation is
       UNSOUND (bv addition wraps: 0 <=u 0xFFFFFFFF but 0+1 >u 0xFFFFFFFF+1,
       see the comment above).  Pattern-matching on [op] itself, not just on
       [σ], is what makes `try_bvadd_cancel_spec` below actually true for
       every [op] -- without it the statement is provably false at, e.g.,
       [op := bvult]. *)
    Definition try_bvadd_cancel {w : World} {σ} (op : RelOp σ)
      (t1 t2 : STerm σ w) : option (DList w) :=
      match σ return RelOp σ -> STerm σ w -> STerm σ w -> option (DList w) with
      | ty.bvec n =>
          fun op t1 t2 =>
            match op with
            | bop.eq | bop.neq =>
                match bvadd_cancel_pair t1 t2 with
                | Some (v1, v2, s) =>
                    if secLeakT s
                    then Some (if bop.eval_relop_val op v1 v2 then empty else error)
                    else None
                | None => None
                end
            | _ => None
            end
      | _ => fun _ _ _ => None
      end op t1 t2.

    (* ---- per-address access bounds, discharged against the base bound ----
       A parametric-base program asserts one access bound per distinct address
       it touches -- `unsigned a + K <= maxAddr`, K=4 for an instruction fetch,
       K=bytes for a load.  `simplify_le` normalises each to
       `0 <= L - (K + unsigned a)` (peval_formula_le, above), and at a SYMBOLIC
       base nothing decides them: they survive into the VC, one per address,
       and were 76-90% of the whole symbolic-base cost penalty
       (case_study/RiscvPmp/CFGVer/diagnostics/
        check-scalar-combined-cost-drivers.md, section 5.8; plans/
        PLAN-fetch-bound-vcs.md).  A concrete base emits none, since `unsigned`
       of a literal just computes.

       They are all implied by ONE hypothesis the contract already assumes --
       the base bound `unsigned p + B <= lenAddr`, which `gen_contract_rel`
       puts in the precondition and which therefore sits in `wco` in the SAME
       normalised shape `0 <= L - (B + unsigned p)`.  So this is a
       path-condition lookup, in the style of
       `pathconditions_contains_secLeakT` above, not new arithmetic: the
       reasoning is what `relval_fetch_upper_add` (CFGVer/Contracts.v) already
       proves per-goal, moved to where the goals are still cheap to kill.

       NO PUBLICNESS GUARD IS NEEDED, and for a stronger reason than
       `try_bvadd_cancel_propeq`'s.  `instpred_formula_relop` does send a
       NonSyncVal operand to False -- but it does so on the HYPOTHESIS too:
       if the base is secret then the base bound in `wco` is itself False and
       the entailment is vacuous.  So the `secLeakT` check that
       `try_bvadd_cancel` needs is here discharged by the very formula we
       reason from.  (`relval_fetch_upper_add` takes `secLeak v` as a separate
       premise only because it is stated without that hypothesis in scope.)

       NEVER `error` FROM HERE.  Failing to find the base bound means "cannot
       decide", not "false"; returning `error` would refute satisfiable paths.
       Every failure path below falls through to `simplify_le` untouched.

       COST: the `wco` scan is gated behind `int_bound_shape` on the goal, so
       only an already-bound-shaped `<=` pays for it -- that is exactly the
       #addresses obligations, not every formula the solver sees. *)

    (* `L - (K + u)`, with L and K literals; `u` is handed back uninspected. *)
    Equations int_bound_shape {Σ} (t : Term Σ ty.int)
      : option (Z * Z * Term Σ ty.int) :=
      int_bound_shape (term_binop bop.minus (term_val _ L)
                         (term_binop bop.plus (term_val _ K) u)) := Some (L, K, u);
      int_bound_shape _ := None.

    (* `unsigned (c (+) s)`  ->  (unsigned c, `unsigned s`, the width).
       EVERYTHING RETURNED IS NON-DEPENDENT -- a Z, a `Term Σ ty.int`, and a
       plain nat -- which is the whole point.  Two earlier shapes both failed
       with "The pattern _ should be equal to _, it is forced by typing":
       binding a width from each of TWO term patterns in one clause, and
       taking the width as a parameter to compare a `Term Σ (ty.bvec n)`
       against a pattern-bound one.  Equations will not let two widths meet,
       so the fix is to never compare across widths: rebuild `unsigned s` here
       and let the caller compare it to the path condition's own `unsigned s`
       at type `Term Σ ty.int`, where `Term_eqb` is homogeneous.  (Each of
       those dead ends cost a ~6-minute Solver.v build, since definitions
       inside this functor cannot be reached interactively -- see the
       rocq-implementation skill on restating shape questions.) *)
    Equations unsigned_bvadd_split {Σ} (u : Term Σ ty.int)
      : option (Z * Term Σ ty.int * nat) :=
      unsigned_bvadd_split
        (term_unop (@uop.unsigned n)
           (term_binop bop.bvadd (term_val _ c) s)) :=
        Some (Z.of_N (bv.bin c), term_unop uop.unsigned s, n);
      unsigned_bvadd_split _ := None.

    (* Does `B + unsigned s <= L1` imply `K + unsigned a <= L2`?  Sufficient
       when `unsigned a` IS `unsigned s` (offset 0, the bare base -- and then
       no no-wrap side condition is needed at all), or when it is
       `unsigned (c (+) s)` with `c + K <= B`, which needs `c + unsigned s`
       not to wrap: that follows from `c <= B` and `B + unsigned s <= L1`
       provided `L1 < 2^n`.  No term pattern-matching here, hence a plain
       Definition. *)
    Definition fetch_bound_entails {Σ} (L2 K L1 B : Z)
      (ug uw : Term Σ ty.int) : bool :=
      (L1 <=? L2)%Z && (0 <=? K)%Z &&
      (if Term_eqb ug uw then (K <=? B)%Z
       else match unsigned_bvadd_split ug with
            | Some (c, uw', n) =>
                Term_eqb uw' uw && (c + K <=? B)%Z &&
                (L1 <? Z.of_N (bv.exp2 n))%Z
            | None => false
            end).

    Equations formula_entails_fetch_bound {Σ} (f : Formula Σ)
      (L2 K : Z) (ug : Term Σ ty.int) : bool :=
      formula_entails_fetch_bound
        (formula_relop bop.le (term_val _ z) tw) L2 K ug :=
        (z =? 0)%Z &&
        (match int_bound_shape tw with
         | Some (L1, B, uw) => fetch_bound_entails L2 K L1 B ug uw
         | None => false
         end);
      formula_entails_fetch_bound _ _ _ _ := false.

    Fixpoint pathcondition_entails_fetch_bound {Σ} (C : PathCondition Σ)
      (L2 K : Z) (ug : Term Σ ty.int) : bool :=
      match C with
      | [ctx]  => false
      | (C ▻ f) => formula_entails_fetch_bound f L2 K ug
                   || pathcondition_entails_fetch_bound C L2 K ug
      end.

    Definition try_fetch_bound {w : World} (t1 t2 : STerm ty.int w)
      : option (DList w) :=
      match int_bound_shape (peval (term_minus t2 t1)) with
      | Some (L2, K, ug) =>
          if pathcondition_entails_fetch_bound (wco w) L2 K ug
          then Some empty
          else None
      | None => None
      end.

    (* ---- PLAN-bv-arith-solver S1: decide bv eq/neq/propeq by a LINEAR DIFFERENCE ----
       `t1 - t2` in canon_term normal form, read back as `c + sum k_i * atom_i`
       (lin_view).  If every coefficient is 0 mod 2^n the difference IS the
       constant c, so `t1 = t2` holds iff c = 0 -- whatever the orientation and
       nesting of the two sides.  This is what refutes `q = 0x180 + q`
       (PLAN-rsa O5), which the shape-matching rules below miss.
       NO PUBLICNESS GUARD: both sides differ by the SAME public constant in
       both runs, so pair equality (propeq) and the pointwise relop are decided
       componentwise by it.  None means "not a constant": fall through to the
       older rules (kept until PLAN-bv-arith-solver O6).
       Keep lin_diff FOLDED in proofs and use `cbn -[lin_const]`: unfolded,
       cbn / the kernel try to compute canon_term on open terms (timeout). *)
Section Lin.
  Context {Σ : LCtx} {n : nat}.
  Local Notation T := (Term Σ (ty.bvec n)).
  Add Ring LinTR : (Term_bv_ring_theory Σ n) (setoid (@term_equivalence Σ (ty.bvec n)) (Term_bv_ring_eq_ext Σ n)).
  Local Notation "a ⊕ b" := (term_binop bop.bvadd a b) (at level 50, left associativity).
  Local Notation "a ⊗ b" := (term_binop bop.bvmul a b) (at level 40, left associativity).

  Definition tvZ (z : Z) : T := term_val (ty.bvec n) (bv.of_Z z).

  Fixpoint lin_neg (ms : list (Z * T)) : list (Z * T) :=
    match ms with nil => nil | cons (k, a) ms' => cons ((- k)%Z, a) (lin_neg ms') end.

  (* linear view of a canon_term output: c + Σ k·atom (atoms: anything else).
     canon_term prints a NEGATIVE ring coefficient with bvsub (Pphi_dev;
     they arise from a bvsub in its input, e.g. peval_bvsub of a SUB), so
     QSub/QNeg must be read too: as atoms they hid a bare variable from S2
     (`a - k·c` one atom: S2 isolated the universal nl instead of the
     existential a, RsaCcopy valid_ccl_loop, 2026-11-05) *)
  Fixpoint lin_view (fuel : nat) (t : T) : Z * list (Z * T) :=
    match fuel with
    | O => (0%Z, cons (1%Z, t) nil)
    | S f =>
        match q_view t with
        | QVal v => (bv.unsigned v, nil)
        | QAdd a b => let '(c1, m1) := lin_view f a in let '(c2, m2) := lin_view f b in
                      ((c1 + c2)%Z, List.app m1 m2)
        | QSub a b => let '(c1, m1) := lin_view f a in let '(c2, m2) := lin_view f b in
                      ((c1 - c2)%Z, List.app m1 (lin_neg m2))
        | QNeg a => let '(c1, m1) := lin_view f a in ((- c1)%Z, lin_neg m1)
        | QMul a b => match q_view a with
                      | QVal k => (0%Z, cons (bv.unsigned k, b) nil)
                      | _ => (0%Z, cons (1%Z, t) nil)
                      end
        | _ => (0%Z, cons (1%Z, t) nil)
        end
    end.
  Definition lin_eval (c : Z) (ms : list (Z * T)) : T :=
    fold_right (fun '(k, a) acc => tvZ k ⊗ a ⊕ acc) (tvZ c) ms.

  Lemma tvZ_add (a b : Z) : (tvZ (a + b) : T) ≡ tvZ a ⊕ tvZ b.
  Proof. intros ι. cbn. unfold ty.valToRelVal. rewrite bv.of_Z_add. reflexivity. Qed.
  Lemma tvZ_opp (k : Z) : (tvZ (- k) : T) ≡ term_unop uop.negate (tvZ k).
  Proof. intros ι. cbn. unfold ty.valToRelVal. rewrite bv.of_Z_negate. reflexivity. Qed.
  Lemma tvZ_unsigned (v : bv n) : (tvZ (bv.unsigned v) : T) = term_val (ty.bvec n) v.
  Proof. unfold tvZ. now rewrite bv.of_Z_unsigned. Qed.
  Lemma tvZ_one : (tvZ 1 : T) ≡ term_val (ty.bvec n) bv.one.
  Proof. intros ι. cbn. now rewrite bv.of_Z_one. Qed.
  Lemma tvZ_zero : (tvZ 0 : T) ≡ term_val (ty.bvec n) bv.zero.
  Proof. reflexivity. Qed.
  Lemma tvZ_m1 : (tvZ (-1) : T) ≡ term_unop uop.negate (term_val (ty.bvec n) bv.one).
  Proof.
    intros ι. cbn. unfold ty.valToRelVal.
    replace (@bv.of_Z n (-1)) with (bv.negate (@bv.of_Z n 1)) by (rewrite bv.of_Z_negate; reflexivity).
    rewrite bv.of_Z_one. reflexivity.
  Qed.
  Lemma lin_eval_cons c k a ms : lin_eval c (cons (k, a) ms) = tvZ k ⊗ a ⊕ lin_eval c ms.
  Proof. reflexivity. Qed.
  Lemma lin_eval_nil c : lin_eval c nil = tvZ c.
  Proof. reflexivity. Qed.
  Lemma lin_eval_app c1 m1 c2 m2 :
    lin_eval (c1 + c2) (List.app m1 m2) ≡ lin_eval c1 m1 ⊕ lin_eval c2 m2.
  Proof.
    induction m1 as [|[k a] m1 IH]; cbn [List.app].
    - rewrite lin_eval_nil. induction m2 as [|[k a] m2 IH2].
      + rewrite !lin_eval_nil. apply tvZ_add.
      + rewrite !lin_eval_cons IH2. ring.
    - rewrite !lin_eval_cons IH. ring.
  Qed.
  Lemma lin_eval_neg c ms : lin_eval (- c) (lin_neg ms) ≡ term_unop uop.negate (lin_eval c ms).
  Proof.
    induction ms as [|[k a] ms IH]; cbn [lin_neg].
    - rewrite !lin_eval_nil. apply tvZ_opp.
    - rewrite !lin_eval_cons IH tvZ_opp. ring.
  Qed.
  Lemma lin_eval_sub c1 m1 c2 m2 :
    lin_eval (c1 - c2) (List.app m1 (lin_neg m2)) ≡ term_binop bop.bvsub (lin_eval c1 m1) (lin_eval c2 m2).
  Proof.
    replace (c1 - c2)%Z with (c1 + - c2)%Z by lia.
    rewrite lin_eval_app lin_eval_neg. ring.
  Qed.
  Lemma lin_view_sound fuel (t : T) :
    let '(c, ms) := lin_view fuel t in lin_eval c ms ≡ t.
  Proof.
    revert t; induction fuel as [|f IH]; intros t; cbn [lin_view].
    - rewrite lin_eval_cons lin_eval_nil tvZ_one tvZ_zero. ring.
    - pose proof (q_view_spec t) as Hs. destruct (q_view t) eqn:Hq.
      + specialize (IH a) as Ha. specialize (IH b) as Hb.
        destruct (lin_view f a) as [c1 m1]. destruct (lin_view f b) as [c2 m2].
        rewrite lin_eval_app Ha Hb. now subst t.
      + specialize (IH a) as Ha. specialize (IH b) as Hb.
        destruct (lin_view f a) as [c1 m1]. destruct (lin_view f b) as [c2 m2].
        rewrite lin_eval_sub Ha Hb. now subst t.
      + pose proof (q_view_spec a) as Ha. destruct (q_view a);
          rewrite lin_eval_cons lin_eval_nil;
          try (rewrite tvZ_one tvZ_zero; ring).
        rewrite tvZ_unsigned tvZ_zero. subst. ring.
      + specialize (IH a) as Ha. destruct (lin_view f a) as [c1 m1].
        rewrite lin_eval_neg Ha. now subst t.
      + rewrite lin_eval_cons lin_eval_nil tvZ_one tvZ_zero. ring.
      + rewrite lin_eval_nil tvZ_unsigned. now subst.
      + rewrite lin_eval_cons lin_eval_nil tvZ_one tvZ_zero. ring.
  Qed.

  (* drop monomials whose coefficient is 0 mod 2^n (canon_term keeps them) *)
  Definition lin_prune (ms : list (Z * T)) : list (Z * T) :=
    List.filter (fun '(k, _) => negb (bv.eqb (@bv.of_Z n k) bv.zero)) ms.
  Lemma lin_eval_prune c ms : lin_eval c (lin_prune ms) ≡ lin_eval c ms.
  Proof.
    induction ms as [|[k a] ms IH]; cbn [lin_prune List.filter]; [reflexivity|].
    destruct (bv.eqb_spec (@bv.of_Z n k) bv.zero) as [Hk|Hk]; cbn [negb].
    - fold (lin_prune ms). rewrite IH lin_eval_cons.
      assert (Hz : (tvZ k : T) ≡ tvZ 0) by (unfold tvZ; now rewrite Hk).
      rewrite Hz tvZ_zero. ring.
    - fold (lin_prune ms). rewrite !lin_eval_cons IH. reflexivity.
  Qed.

  (* S1 *)
  Definition lin_diff (t1 t2 : T) : T := canon_term (t1 ⊕ tvZ (-1) ⊗ t2).
  (* keep lin_diff FOLDED in proofs: unfolded, Qed's kernel check tries to
     compute canon_term on open terms (timed out, 2026-11-05) *)
  Lemma lin_diff_equiv t1 t2 : lin_diff t1 t2 ≡ t1 ⊕ tvZ (-1) ⊗ t2.
  Proof. apply canon_term_equiv. Qed.
  Definition lin_const (t1 t2 : T) : option (bv n) :=
    let '(c, ms) := lin_view qfuel (lin_diff t1 t2) in
    match lin_prune ms with nil => Some (bv.of_Z c) | _ => None end.
  Lemma lin_const_equiv t1 t2 v : lin_const t1 t2 = Some v ->
    t1 ≡ term_val (ty.bvec n) v ⊕ t2.
  Proof.
    unfold lin_const. pose proof (lin_view_sound qfuel (lin_diff t1 t2)) as Hs.
    destruct (lin_view qfuel (lin_diff t1 t2)) as [c ms].
    pose proof (lin_eval_prune c ms) as Hp.
    destruct (lin_prune ms) eqn:E; [|discriminate]. intros [= <-].
    rewrite lin_eval_nil in Hp. rewrite lin_diff_equiv in Hs.
    assert (Hv : term_val (ty.bvec n) (bv.of_Z c) ≡ t1 ⊕ tvZ (-1) ⊗ t2)
      by (change (term_val (ty.bvec n) (bv.of_Z c)) with (tvZ c : T); now rewrite Hp).
    clear -Hv. rewrite Hv tvZ_m1. ring.
  Qed.
  Lemma lin_const_inst t1 t2 v : lin_const t1 t2 = Some v ->
    forall ι, inst t1 ι = inst t2 ι <-> v = bv.zero.
  Proof.
    intros H ι. rewrite (lin_const_equiv t1 t2 H ι). cbn.
    destruct (inst t2 ι) as [a1 a2]. unfold ty.valToRelVal, bop.evalRel, ty.liftBinOp, ty.liftBinOpRV; cbn.
    split.
    - intros Hq. pose proof (f_equal ty.projLeftRV Hq) as HL. cbn in HL.
      apply (bv.add_cancel_r (z := a1)). rewrite bv.add_zero_l. exact HL.
    - intros ->. rewrite !bv.add_zero_l. reflexivity.
  Qed.
  Lemma lin_const_proj (t1 t2 : T) v : lin_const t1 t2 = Some v -> forall ι : Valuation Σ,
    ty.projLeftRV (inst t1 ι : RelVal (ty.bvec n)) = bv.add v (ty.projLeftRV (inst t2 ι : RelVal (ty.bvec n))) /\
    ty.projRightRV (inst t1 ι : RelVal (ty.bvec n)) = bv.add v (ty.projRightRV (inst t2 ι : RelVal (ty.bvec n))).
  Proof.
    intros H ι. rewrite (lin_const_equiv t1 t2 H ι). cbn.
    destruct (inst t2 ι) as [a1 a2]. unfold ty.valToRelVal, bop.evalRel, ty.liftBinOp, ty.liftBinOpRV; cbn.
    split; reflexivity.
  Qed.
End Lin.

    Definition lin_decide {w : World} {σ} (op : RelOp σ) (t1 t2 : STerm σ w) : option (DList w) :=
      match σ return RelOp σ -> STerm σ w -> STerm σ w -> option (DList w) with
      | ty.bvec n => fun op t1 t2 =>
          match op with
          | bop.eq => match lin_const t1 t2 with
                      | Some v => Some (if bv.eqb v bv.zero then empty else error)
                      | None => None end
          | bop.neq => match lin_const t1 t2 with
                      | Some v => Some (if bv.eqb v bv.zero then error else empty)
                      | None => None end
          | _ => None
          end
      | _ => fun _ _ _ => None
      end op t1 t2.
    Definition lin_decide_propeq {w : World} {σ} (t1 t2 : STerm σ w) : option (DList w) :=
      match σ return STerm σ w -> STerm σ w -> option (DList w) with
      | ty.bvec n => fun t1 t2 =>
          match lin_const t1 t2 with
          | Some v => Some (if bv.eqb v bv.zero then empty else error)
          | None => None end
      | _ => fun _ _ => None
      end t1 t2.
    Lemma lin_decide_propeq_spec {w : World} {σ} (t1 t2 : STerm σ w) (d : DList w) :
      lin_decide_propeq t1 t2 = Some d -> instpred d ⊣⊢ instpred (formula_propeq t1 t2).
    Proof.
      unfold lin_decide_propeq. intros Hc. destruct σ; cbn in Hc; try discriminate.
      destruct (lin_const t1 t2) as [v|] eqn:Hl; try discriminate. injection Hc as <-.
      rewrite instpred_formula_propeqₚ.
      pose proof (lin_const_inst t1 t2 Hl) as Hi.
      destruct (bv.eqb_spec v bv.zero) as [Hv|Hv];
        [rewrite instpred_dlist_empty | rewrite instpred_dlist_error];
        constructor; intros ι Hwco; cbn; specialize (Hi ι); split; intros HH;
        first [ solve [exact I] | solve [destruct HH] | solve [apply Hi; exact Hv]
              | solve [exfalso; apply Hv, Hi, HH] ].
    Qed.
    (* NB cbn -[lin_const]: a bare cbn unfolds canon_term on open terms -> timeout *)
    Lemma lin_decide_spec {w : World} {σ} (op : RelOp σ) (t1 t2 : STerm σ w) (d : DList w) :
      lin_decide op t1 t2 = Some d -> instpred d ⊣⊢ instpred (formula_relop op t1 t2).
    Proof.
      unfold lin_decide. destruct σ; cbn; try discriminate.
      depelim op; cbn -[lin_const]; try discriminate.
      all: destruct (lin_const t1 t2) as [v|] eqn:Hl; try discriminate; intros [= <-];
        pose proof (lin_const_proj t1 t2 Hl) as Hp;
        destruct (bv.eqb_spec v bv.zero) as [Hv|Hv];
        first [rewrite instpred_dlist_empty | rewrite instpred_dlist_error];
        constructor; intros ι Hwco; cbn -[lin_const]; unfold instpred_formula_relop;
        specialize (Hp ι); destruct (inst t1 ι) as [l1 r1], (inst t2 ι) as [l2 r2]; cbn in Hp;
        destruct Hp as [-> ->]; unfold bop.evalRel, ty.liftBinOp; cbn -[lin_const].
      all: assert (Hc : forall a : bv n, bv.add v a = a <-> v = bv.zero) by
           (intros a; split; [intros H; apply (bv.add_cancel_r (z := a)); now rewrite bv.add_zero_l
                             | intros ->; apply bv.add_zero_l]);
         rewrite ?Hc; split; intros HH;
         first [ solve [exact I] | solve [destruct HH] | solve [split; assumption]
               | solve [exfalso; destruct HH as [HH _]; now apply HH] | solve [exfalso; now apply Hv, HH] ].
    Qed.

    (* ---- PLAN-bv-arith-solver S3: decide bv eq/neq/ule/ult by INTERVALS from wco ----
       Seed an unsigned interval per atom from the path condition's relops
       against a literal (bvult/bvule/eq/neq/propeq), propagate it through the
       linear view of the term (rng_lin_int; rng_wrapf is exact only when no
       multiple of 2^n is crossed, else the full range), and decide the relop
       when the intervals of `t1 - t2` (eq/neq) or of t1, t2 (ule/ult) settle it.
       DECIDE ONLY (D1): it never rewrites, so a None is always safe.
       Projection-based: rng_uprj reads the unsigned value of each run of the
       pair, so the verdict holds componentwise.  Every helper is prefixed rng_
       because Machine.v has a `rng` notation.  Fuel rng_fuel bounds the
       recursion through the linear view. *)

    Section RngA.
      Context {Σ : LCtx} {n : nat}.
      Local Notation T := (Term Σ (ty.bvec n)).
      Local Notation "a ⊕ b" := (term_binop bop.bvadd a b) (at level 50, left associativity).
      Local Notation "a ⊗ b" := (term_binop bop.bvmul a b) (at level 40, left associativity).
      Local Notation m := (2 ^ Z.of_nat n)%Z.

      Definition rng_prj (p : bool) (rv : RelVal (ty.bvec n)) : bv n :=
        if p then ty.projLeft rv else ty.projRight rv.
      Definition rng_uprj (p : bool) (t : T) (ι : Valuation Σ) : Z := bv.unsigned (rng_prj p (inst t ι)).
      Lemma rng_uprj_add p (a b : T) ι : rng_uprj p (a ⊕ b) ι = ((rng_uprj p a ι + rng_uprj p b ι) mod m)%Z.
      Proof. unfold rng_uprj. cbn. destruct (inst a ι), (inst b ι), p; cbn; apply bv.unsigned_add. Qed.
      Lemma rng_uprj_mul p (a b : T) ι : rng_uprj p (a ⊗ b) ι = ((rng_uprj p a ι * rng_uprj p b ι) mod m)%Z.
      Proof. unfold rng_uprj. cbn. destruct (inst a ι), (inst b ι), p; cbn; apply bv.unsigned_mul. Qed.
      Lemma rng_uprj_tvZ p z ι : rng_uprj p (tvZ z : T) ι = (z mod m)%Z.
      Proof. unfold rng_uprj, tvZ. cbn. destruct p; apply bv.unsigned_of_Z. Qed.
      Lemma rng_uprj_val p v ι : rng_uprj p (term_val (ty.bvec n) v) ι = bv.unsigned v.
      Proof. unfold rng_uprj. cbn. now destruct p. Qed.
      Lemma rng_uprj_bounds p (t : T) ι : (0 <= rng_uprj p t ι < m)%Z.
      Proof. apply bv.unsigned_bounds. Qed.
      Lemma rng_uprj_equiv p (a b : T) ι : a ≡ b -> rng_uprj p a ι = rng_uprj p b ι.
      Proof. intros E. unfold rng_uprj. now rewrite (E ι). Qed.

      Definition rng_lin_sum (c : Z) (ms : list (Z * T)) (ι : Valuation Σ) (p : bool) : Z :=
        fold_right (fun '(k, a) acc => (k * rng_uprj p a ι + acc)%Z) c ms.
      Lemma rng_uprj_lin_eval p c ms ι : rng_uprj p (lin_eval c ms) ι = (rng_lin_sum c ms ι p mod m)%Z.
      Proof.
        induction ms as [|[k a] ms IH]; cbn [lin_eval fold_right rng_lin_sum].
        - apply rng_uprj_tvZ.
        - change (fold_right _ (tvZ c) ms) with (lin_eval c ms).
          change (fold_right _ c ms) with (rng_lin_sum c ms ι p).
          rewrite rng_uprj_add rng_uprj_mul rng_uprj_tvZ IH.
          rewrite Zplus_mod_idemp_r.
          rewrite Zplus_mod_idemp_l (Zplus_mod (k mod m * _)) (Zplus_mod (k * _)) Zmult_mod_idemp_l.
          reflexivity.
      Qed.

      (* signed representative of a coefficient, in (-m/2, m/2] *)
      Definition rng_sr (k : Z) : Z := let u := (k mod m)%Z in if (m <? 2 * u)%Z then (u - m)%Z else u.
      Lemma rng_sr_mod k : (rng_sr k mod m)%Z = (k mod m)%Z.
      Proof.
        unfold rng_sr. assert (Hm : (0 < m)%Z) by (apply Z.pow_pos_nonneg; lia).
        destruct (m <? 2 * (k mod m))%Z.
        - rewrite Zminus_mod Z_mod_same_full Z.sub_0_r !Zmod_mod. reflexivity.
        - apply Zmod_mod.
      Qed.
      Definition rng_sr_ms (ms : list (Z * T)) : list (Z * T) := List.map (fun '(k, a) => (rng_sr k, a)) ms.
      Lemma rng_lin_sum_sr c ms ι p : (rng_lin_sum (rng_sr c) (rng_sr_ms ms) ι p mod m)%Z = (rng_lin_sum c ms ι p mod m)%Z.
      Proof.
        induction ms as [|[k a] ms IH]; cbn [rng_lin_sum rng_sr_ms List.map fold_right].
        - apply rng_sr_mod.
        - change (fold_right _ (rng_sr c) (List.map _ ms)) with (rng_lin_sum (rng_sr c) (rng_sr_ms ms) ι p).
          change (fold_right _ c ms) with (rng_lin_sum c ms ι p).
          rewrite Zplus_mod IH (Zmult_mod (rng_sr k)) rng_sr_mod -Zmult_mod -Zplus_mod. reflexivity.
      Qed.

      (* intervals of unsigned values *)
      Definition rng_full : Z * Z := (0, m - 1)%Z.
      Definition rng_meet (r1 r2 : Z * Z) : Z * Z := (Z.max (fst r1) (fst r2), Z.min (snd r1) (snd r2)).
      Definition rng_inr (r : Z * Z) (z : Z) : Prop := (fst r <= z <= snd r)%Z.
      Lemma rng_inr_full p t ι : rng_inr rng_full (rng_uprj p t ι).
      Proof. pose proof (rng_uprj_bounds p t ι). unfold rng_inr, rng_full; cbn; lia. Qed.
      Lemma rng_inr_meet r1 r2 z : rng_inr r1 z -> rng_inr r2 z -> rng_inr (rng_meet r1 r2) z.
      Proof. unfold rng_inr, rng_meet; cbn; lia. Qed.

      (* seeds: one wco fact about t against a constant *)
      Variant rng_rk := RngRkUlt | RngRkUle | RngRkEq | RngRkNeq.
      Definition rng_rk_holds {j} (k : rng_rk) (x y : bv j) : Prop :=
        match k with RngRkUlt => bv.ult x y | RngRkUle => bv.ule x y | RngRkEq => x = y | RngRkNeq => x <> y end.
      Definition rng_qval (t : T) : option (bv n) := match q_view t with QVal v => Some v | _ => None end.
      Lemma rng_qval_spec t v : rng_qval t = Some v -> t = term_val (ty.bvec n) v.
      Proof. unfold rng_qval. pose proof (q_view_spec t) as H. destruct (q_view t); try discriminate. now intros [= <-]. Qed.
      Lemma rng_prj_val p v ι : rng_prj p (inst (term_val (ty.bvec n) v : T) ι) = v.
      Proof. now destruct p. Qed.

      Definition rng_seed_core (k : rng_rk) (a b t : T) : option (Z * Z) :=
        if Term_eqb a t then
          match rng_qval b with
          | Some v => let u := bv.unsigned v in
              match k with RngRkUlt => Some (0, u - 1)%Z | RngRkUle => Some (0, u)%Z | RngRkEq => Some (u, u)
                         | RngRkNeq => if (u =? 0)%Z then Some (1, m - 1)%Z else None end
          | None => None end
        else if Term_eqb b t then
          match rng_qval a with
          | Some v => let u := bv.unsigned v in
              match k with RngRkUlt => Some (u + 1, m - 1)%Z | RngRkUle => Some (u, m - 1)%Z | RngRkEq => Some (u, u)
                         | RngRkNeq => if (u =? 0)%Z then Some (1, m - 1)%Z else None end
          | None => None end
        else None.

      Lemma rng_ne0_ge1 (x v : bv n) : x <> v -> bv.unsigned v = 0%Z -> (1 <= bv.unsigned x)%Z.
      Proof.
        intros Hne Hv. pose proof (bv.unsigned_bounds x).
        destruct (Z.eq_dec (bv.unsigned x) 0) as [Hx|]; [|lia].
        exfalso. apply Hne, bv.unsigned_inj. now rewrite Hx Hv.
      Qed.

      Lemma rng_seed_core_sound k a b t r p ι : rng_seed_core k a b t = Some r ->
        rng_rk_holds k (rng_prj p (inst a ι)) (rng_prj p (inst b ι)) -> rng_inr r (rng_uprj p t ι).
      Proof.
        unfold rng_seed_core. pose proof (rng_uprj_bounds p t ι) as Hb. unfold rng_uprj in Hb |- *.
        destruct (Term_eqb_spec a t) as [<-|_].
        - destruct (rng_qval b) as [v|] eqn:Hq; [|discriminate]. apply rng_qval_spec in Hq as ->.
          rewrite rng_prj_val. pose proof (bv.unsigned_bounds v).
          destruct k; cbn [rng_rk_holds]; [| | |destruct (Z.eqb_spec (bv.unsigned v) 0)]; intros [= <-]; unfold rng_inr; cbn [fst snd];
            rewrite ?bv.ult_iff_unsigned_lt ?bv.ule_iff_unsigned_le; intros HH;
            [lia|lia|rewrite HH; lia|eapply rng_ne0_ge1 in HH; [lia|eassumption]].
        - destruct (Term_eqb_spec b t) as [<-|_]; [|discriminate].
          destruct (rng_qval a) as [v|] eqn:Hq; [|discriminate]. apply rng_qval_spec in Hq as ->.
          rewrite rng_prj_val. pose proof (bv.unsigned_bounds v).
          destruct k; cbn [rng_rk_holds]; [| | |destruct (Z.eqb_spec (bv.unsigned v) 0)]; intros [= <-]; unfold rng_inr; cbn [fst snd];
            rewrite ?bv.ult_iff_unsigned_lt ?bv.ule_iff_unsigned_le; intros HH;
            [lia|lia|rewrite -HH; lia|].
          assert (HH' : rng_prj p (inst b ι) <> v) by (intros E; now apply HH).
          eapply rng_ne0_ge1 in HH'; [lia|eassumption].
      Qed.
    End RngA.


    Section RngB.
      Context {Σ : LCtx} {n : nat}.
      Local Notation T := (Term Σ (ty.bvec n)).
      Local Notation m := (2 ^ Z.of_nat n)%Z.

      Definition rng_seed_rel {σ} (k : rng_rk) (a b : Term Σ σ) (t : T) : option (Z * Z) :=
        match σ return Term Σ σ -> Term Σ σ -> option (Z * Z) with
        | ty.bvec j => fun a b =>
            match Nat.eq_dec j n with
            | left e => rng_seed_core k (eq_rect j (fun j => Term Σ (ty.bvec j)) a n e)
                                    (eq_rect j (fun j => Term Σ (ty.bvec j)) b n e) t
            | right _ => None end
        | _ => fun _ _ => None end a b.

      Lemma rng_seed_rel_sound {j} k (a b : Term Σ (ty.bvec j)) t r p ι : rng_seed_rel k a b t = Some r ->
        rng_rk_holds k (rng_prj p (inst a ι)) (rng_prj p (inst b ι)) -> rng_inr r (rng_uprj p t ι).
      Proof.
        cbn. destruct (Nat.eq_dec j n) as [e|]; [subst j|discriminate]. cbn.
        apply rng_seed_core_sound.
      Qed.

      Definition rng_formula_seed (f : Formula Σ) (t : T) : option (Z * Z) :=
        match f with
        | formula_relop op a b =>
            match op in bop.RelOp σ return Term Σ σ -> Term Σ σ -> option (Z * Z) with
            | bop.bvult => fun a b => rng_seed_rel RngRkUlt a b t
            | bop.bvule => fun a b => rng_seed_rel RngRkUle a b t
            | bop.eq => fun a b => rng_seed_rel RngRkEq a b t
            | bop.neq => fun a b => rng_seed_rel RngRkNeq a b t
            | _ => fun _ _ => None end a b
        | formula_propeq a b => rng_seed_rel RngRkEq a b t
        | _ => None
        end.

      Lemma rng_relop_prj {j} (op : bop.RelOp (ty.bvec j)) (a b : Term Σ (ty.bvec j)) ι p :
        instprop (formula_relop op a b) ι -> bop.eval_relop_prop op (rng_prj p (inst a ι)) (rng_prj p (inst b ι)).
      Proof.
        cbn. rewrite bop.comProjLeftRVEval_relop_relprop bop.comProjRightRVEval_relop_relprop.
        destruct p; cbn; tauto.
      Qed.

      Lemma rng_formula_seed_sound f t r p ι : rng_formula_seed f t = Some r -> instprop f ι -> rng_inr r (rng_uprj p t ι).
      Proof.
        destruct f as [| | | σ op a b | | | | | σ a b |]; cbn [rng_formula_seed]; try discriminate.
        - destruct op as [τ|τ| | |j|j|j|j]; try discriminate;
            [destruct τ; try discriminate|destruct τ; try discriminate| |];
            intros Hs Hf; (eapply rng_seed_rel_sound; [exact Hs|]);
            apply (rng_relop_prj p) in Hf; exact Hf.
        - destruct σ; try discriminate. intros Hs Hf.
          eapply rng_seed_rel_sound; [exact Hs|]. cbn in Hf |- *. now rewrite Hf.
      Qed.

      Fixpoint rng_pc_seed (C : PathCondition Σ) (t : T) : Z * Z :=
        match C with
        | ctx.nil => rng_full (n := n)
        | ctx.snoc C f => match rng_formula_seed f t with
                          | Some r => rng_meet r (rng_pc_seed C t)
                          | None => rng_pc_seed C t end
        end.
      Lemma rng_pc_seed_sound C t p ι : instprop C ι -> rng_inr (rng_pc_seed C t) (rng_uprj p t ι).
      Proof.
        induction C as [|C IHC f]; cbn [rng_pc_seed].
        - intros _. apply rng_inr_full.
        - intros [HC Hf]. destruct (rng_formula_seed f t) as [r|] eqn:Hs; [|now apply IHC].
          apply rng_inr_meet; [|now apply IHC]. eapply rng_formula_seed_sound; eassumption.
      Qed.

      Definition rng_mulint (k : Z) (r : Z * Z) : Z * Z :=
        if (0 <=? k)%Z then (k * fst r, k * snd r)%Z else (k * snd r, k * fst r)%Z.
      Lemma rng_mulint_sound k r z : rng_inr r z -> rng_inr (rng_mulint k r) (k * z)%Z.
      Proof. unfold rng_inr, rng_mulint. destruct (Z.leb_spec 0 k); cbn [fst snd]; nia. Qed.
      Definition rng_addint (r1 r2 : Z * Z) : Z * Z := (fst r1 + fst r2, snd r1 + snd r2)%Z.
      Lemma rng_addint_sound r1 r2 z1 z2 : rng_inr r1 z1 -> rng_inr r2 z2 -> rng_inr (rng_addint r1 r2) (z1 + z2)%Z.
      Proof. unfold rng_inr, rng_addint; cbn [fst snd]; lia. Qed.
      Definition rng_lin_int (R : T -> Z * Z) (c : Z) (ms : list (Z * T)) : Z * Z :=
        fold_right (fun '(k, a) acc => rng_addint (rng_mulint k (R a)) acc) (c, c) ms.
      Lemma rng_lin_int_sound R c ms p ι : (forall a, rng_inr (R a) (rng_uprj p a ι)) ->
        rng_inr (rng_lin_int R c ms) (rng_lin_sum c ms ι p).
      Proof.
        intros HR. induction ms as [|[k a] ms IH]; cbn [rng_lin_int rng_lin_sum fold_right].
        - unfold rng_inr; cbn; lia.
        - change (fold_right _ (c, c) ms) with (rng_lin_int R c ms).
          change (fold_right _ c ms) with (rng_lin_sum c ms ι p).
          apply rng_addint_sound; [apply rng_mulint_sound, HR|exact IH].
      Qed.

      (* an unreduced-sum interval to an unsigned one: exact when it meets no multiple of m *)
      Definition rng_wrapf (r : Z * Z) : Z * Z :=
        if (fst r / m =? snd r / m)%Z then (fst r - fst r / m * m, snd r - fst r / m * m)%Z else rng_full (n := n).
      Lemma rng_wrapf_sound r s : rng_inr r s -> rng_inr (rng_wrapf r) (s mod m)%Z.
      Proof.
        assert (Hm : (0 < m)%Z) by (apply Z.pow_pos_nonneg; lia).
        unfold rng_wrapf, rng_inr. destruct r as [L H]; cbn [fst snd]. intros Hs.
        destruct (Z.eqb_spec (L / m) (H / m)) as [Hq|_].
        - assert (Hl : (L / m <= s / m)%Z) by (apply Z.div_le_mono; lia).
          assert (Hh : (s / m <= H / m)%Z) by (apply Z.div_le_mono; lia).
          assert (Hsq : (s / m)%Z = (L / m)%Z) by lia.
          rewrite (Z.mod_eq s m); [|lia]. rewrite Hsq. cbn [fst snd]. nia.
        - unfold rng_full; cbn [fst snd]. pose proof (Z.mod_pos_bound s m Hm). lia.
      Qed.

      Definition rng_is_self (ms : list (Z * T)) (t : T) : bool :=
        match ms with cons (_, a) nil => Term_eqb a t | _ => false end.
      Fixpoint rng_iv (fuel : nat) (C : PathCondition Σ) (t : T) {struct fuel} : Z * Z :=
        rng_meet (rng_pc_seed C t)
          match fuel with
          | O => rng_full (n := n)
          | S f => match rng_qval t with
                   | Some v => (bv.unsigned v, bv.unsigned v)
                   | None => let '(c, ms) := lin_view f t in
                             if rng_is_self ms t then rng_full (n := n)
                             else rng_wrapf (rng_lin_int (rng_iv f C) (rng_sr (n := n) c) (rng_sr_ms ms))
                   end
          end.
      Lemma rng_sound fuel C t p ι : instprop C ι -> rng_inr (rng_iv fuel C t) (rng_uprj p t ι).
      Proof.
        revert t; induction fuel as [|f IH]; intros t HC; cbn [rng_iv];
          (apply rng_inr_meet; [now apply rng_pc_seed_sound|]).
        - apply rng_inr_full.
        - destruct (rng_qval t) as [v|] eqn:Hq.
          + apply rng_qval_spec in Hq as ->. rewrite rng_uprj_val. unfold rng_inr; cbn [fst snd]; lia.
          + pose proof (lin_view_sound f t) as Hl. destruct (lin_view f t) as [c ms].
            destruct (rng_is_self ms t); [apply rng_inr_full|].
            assert (E : rng_uprj p t ι = rng_uprj p (lin_eval c ms) ι) by (apply rng_uprj_equiv; now symmetry).
            rewrite E rng_uprj_lin_eval -rng_lin_sum_sr. apply rng_wrapf_sound, rng_lin_int_sound.
            intros a. now apply IH.
      Qed.
    End RngB.


    Section RngDec.
      Context {Σ : LCtx} {n : nat}.
      Local Notation T := (Term Σ (ty.bvec n)).
      Local Notation m := (2 ^ Z.of_nat n)%Z.
      Lemma rng_uprj_diff_zero p (t1 t2 : T) ι :
        rng_uprj p (lin_diff t1 t2) ι = 0%Z <-> rng_prj p (inst t1 ι) = rng_prj p (inst t2 ι).
      Proof.
        assert (Hm : (0 < m)%Z) by (apply Z.pow_pos_nonneg; lia).
        rewrite (rng_uprj_equiv p ι (lin_diff_equiv t1 t2)) rng_uprj_add rng_uprj_mul rng_uprj_tvZ.
        pose proof (rng_uprj_bounds p t1 ι) as B1. pose proof (rng_uprj_bounds p t2 ι) as B2.
        rewrite Zplus_mod_idemp_r Zplus_mod Zmult_mod_idemp_l -Zplus_mod.
        transitivity (@eq Z (rng_uprj p t1 ι) (rng_uprj p t2 ι)).
        - set (u1 := rng_uprj p t1 ι) in *. set (u2 := rng_uprj p t2 ι) in *.
          pose proof (Z.div_mod (u1 + -1 * u2) m ltac:(lia)) as Hd.
          pose proof (Z.mod_pos_bound (u1 + -1 * u2) m Hm) as Hb.
          set (q := ((u1 + -1 * u2) / m)%Z) in *. set (r := ((u1 + -1 * u2) mod m)%Z) in *.
          split; intros H.
          + subst r. assert (q = 0%Z) by nia. nia.
          + assert (q = 0%Z \/ q = -1)%Z as [Hq|Hq] by nia; nia.
        - unfold rng_uprj. split; [apply bv.unsigned_inj|intros ->; reflexivity].
      Qed.
      Definition rng_fuel : nat := 8.
      Definition rng_eqb (C : PathCondition Σ) (t1 t2 : T) : option bool :=
        let r := rng_iv rng_fuel C (lin_diff t1 t2) in
        if (1 <=? fst r)%Z then Some false else if (snd r <=? 0)%Z then Some true else None.
      Lemma rng_eqb_sound C t1 t2 b ι p : rng_eqb C t1 t2 = Some b -> instprop C ι ->
        (rng_prj p (inst t1 ι) = rng_prj p (inst t2 ι) <-> b = true).
      Proof.
        unfold rng_eqb. intros Hb HC.
        pose proof (rng_sound rng_fuel C (lin_diff t1 t2) p ι HC) as Hr.
        pose proof (rng_uprj_bounds p (lin_diff t1 t2) ι) as Hu.
        transitivity (@eq Z (rng_uprj p (lin_diff t1 t2) ι) 0%Z); [symmetry; apply rng_uprj_diff_zero|].
        destruct (rng_iv rng_fuel C (lin_diff t1 t2)) as [lo hi]. unfold rng_inr in Hr; cbn [fst snd] in Hb, Hr.
        destruct (Z.leb_spec 1 lo); [injection Hb as <-; split; [lia|discriminate]|].
        destruct (Z.leb_spec hi 0); [injection Hb as <-; split; [reflexivity|intros _; lia]|discriminate].
      Qed.
      Definition rng_ultb (C : PathCondition Σ) (t1 t2 : T) : option bool :=
        let r1 := rng_iv rng_fuel C t1 in let r2 := rng_iv rng_fuel C t2 in
        if (snd r1 <? fst r2)%Z then Some true else if (snd r2 <=? fst r1)%Z then Some false else None.
      Lemma rng_ultb_sound C t1 t2 b ι p : rng_ultb C t1 t2 = Some b -> instprop C ι ->
        (bv.ult (rng_prj p (inst t1 ι)) (rng_prj p (inst t2 ι)) <-> b = true).
      Proof.
        unfold rng_ultb. intros Hb HC. rewrite bv.ult_iff_unsigned_lt.
        change (bv.unsigned (rng_prj p (inst t1 ι))) with (rng_uprj p t1 ι).
        change (bv.unsigned (rng_prj p (inst t2 ι))) with (rng_uprj p t2 ι).
        pose proof (rng_sound rng_fuel C t1 p ι HC) as H1. pose proof (rng_sound rng_fuel C t2 p ι HC) as H2.
        destruct (rng_iv rng_fuel C t1) as [l1 h1], (rng_iv rng_fuel C t2) as [l2 h2]. unfold rng_inr in H1, H2; cbn [fst snd] in Hb, H1, H2.
        destruct (Z.ltb_spec h1 l2); [injection Hb as <-; split; [reflexivity|intros _; lia]|].
        destruct (Z.leb_spec h2 l1); [injection Hb as <-; split; [lia|discriminate]|discriminate].
      Qed.
      Definition rng_uleb (C : PathCondition Σ) (t1 t2 : T) : option bool :=
        let r1 := rng_iv rng_fuel C t1 in let r2 := rng_iv rng_fuel C t2 in
        if (snd r1 <=? fst r2)%Z then Some true else if (snd r2 <? fst r1)%Z then Some false else None.
      Lemma rng_uleb_sound C t1 t2 b ι p : rng_uleb C t1 t2 = Some b -> instprop C ι ->
        (bv.ule (rng_prj p (inst t1 ι)) (rng_prj p (inst t2 ι)) <-> b = true).
      Proof.
        unfold rng_uleb. intros Hb HC. rewrite bv.ule_iff_unsigned_le.
        change (bv.unsigned (rng_prj p (inst t1 ι))) with (rng_uprj p t1 ι).
        change (bv.unsigned (rng_prj p (inst t2 ι))) with (rng_uprj p t2 ι).
        pose proof (rng_sound rng_fuel C t1 p ι HC) as H1. pose proof (rng_sound rng_fuel C t2 p ι HC) as H2.
        destruct (rng_iv rng_fuel C t1) as [l1 h1], (rng_iv rng_fuel C t2) as [l2 h2]. unfold rng_inr in H1, H2; cbn [fst snd] in Hb, H1, H2.
        destruct (Z.leb_spec h1 l2); [injection Hb as <-; split; [reflexivity|intros _; lia]|].
        destruct (Z.ltb_spec h2 l1); [injection Hb as <-; split; [lia|discriminate]|discriminate].
      Qed.
      Lemma rng_relop_iff {j} (op : bop.RelOp (ty.bvec j)) (a b : Term Σ (ty.bvec j)) ι :
        instprop (formula_relop op a b) ι <-> forall p, bop.eval_relop_prop op (rng_prj p (inst a ι)) (rng_prj p (inst b ι)).
      Proof.
        cbn. rewrite bop.comProjLeftRVEval_relop_relprop bop.comProjRightRVEval_relop_relprop.
        split; [intros [HL HR] [|]; assumption|intros H; split; [apply (H true)|apply (H false)]].
      Qed.
      Lemma rng_propeq_iff (a b : T) ι :
        instprop (formula_propeq a b) ι <-> forall p, rng_prj p (inst a ι) = rng_prj p (inst b ι).
      Proof.
        cbn. destruct (inst a ι) as [a1 a2], (inst b ι) as [b1 b2]. cbn.
        split; [intros [= -> ->] [|]; reflexivity|intros H; f_equal; [apply (H true)|apply (H false)]].
      Qed.
    End RngDec.

    Definition rng_decb {w : World} {σ} (op : RelOp σ) : STerm σ w -> STerm σ w -> option bool :=
      match op in RelOp σ return STerm σ w -> STerm σ w -> option bool with
      | @bop.eq _ τ => match τ return STerm τ w -> STerm τ w -> option bool with
                     | ty.bvec j => fun t1 t2 => rng_eqb (wco w) t1 t2 | _ => fun _ _ => None end
      | @bop.neq _ τ => match τ return STerm τ w -> STerm τ w -> option bool with
                     | ty.bvec j => fun t1 t2 => option_map negb (rng_eqb (wco w) t1 t2) | _ => fun _ _ => None end
      | bop.bvult => fun t1 t2 => rng_ultb (wco w) t1 t2
      | bop.bvule => fun t1 t2 => rng_uleb (wco w) t1 t2
      | _ => fun _ _ => None
      end.
    Definition rng_decide {w : World} {σ} (op : RelOp σ) (t1 t2 : STerm σ w) : option (DList w) :=
      option_map (fun b : bool => if b then empty else error) (rng_decb op t1 t2).
    Definition rng_decb_propeq {w : World} {σ} : STerm σ w -> STerm σ w -> option bool :=
      match σ return STerm σ w -> STerm σ w -> option bool with
      | ty.bvec j => fun t1 t2 => rng_eqb (wco w) t1 t2 | _ => fun _ _ => None end.
    Definition rng_decide_propeq {w : World} {σ} (t1 t2 : STerm σ w) : option (DList w) :=
      option_map (fun b : bool => if b then empty else error) (rng_decb_propeq t1 t2).

    (* ===================== world-level specs ===================== *)
    Lemma rng_dec_bridge {w : World} (f : Formula w) (b : bool) :
      (forall ι, instprop (wco w) ι -> (instprop f ι <-> b = true)) ->
      instpred (if b then empty else error) ⊣⊢ instpred f.
    Proof.
      intros H. destruct b; [rewrite instpred_dlist_empty | rewrite instpred_dlist_error];
      constructor; intros ι Hwco; specialize (H ι Hwco); rewrite instpred_prop; cbn.
      - split; [intros _; apply H; reflexivity|intros _; exact I].
      - split; [intros []|intros Hf; apply H in Hf; discriminate].
    Qed.
    Lemma rng_forall_iff (P : bool -> Prop) (B : Prop) : (forall p, P p <-> B) -> ((forall p, P p) <-> B).
    Proof. intros H; split; [intros HP; apply (H true), HP|intros HB p; apply H, HB]. Qed.
    Lemma rng_decb_sound {w : World} {σ} (op : RelOp σ) (t1 t2 : STerm σ w) b :
      rng_decb op t1 t2 = Some b -> forall ι, instprop (wco w) ι ->
      (instprop (formula_relop op t1 t2) ι <-> b = true).
    Proof.
      intros Hb ι Hwco.
      destruct op as [τ|τ| | |j|j|j|j]; try discriminate; [destruct τ; try discriminate|destruct τ; try discriminate| |];
        rewrite rng_relop_iff; apply rng_forall_iff; intros p; cbn [rng_decb] in Hb; cbn [bop.eval_relop_prop].
      - eapply rng_eqb_sound; [exact Hb|exact Hwco].
      - destruct (rng_eqb (wco w) t1 t2) as [b0|] eqn:He; [cbn in Hb; injection Hb as <-|discriminate].
        assert (Hs : rng_prj p (inst t1 ι) = rng_prj p (inst t2 ι) <-> b0 = true) by (eapply rng_eqb_sound; [exact He|exact Hwco]).
        destruct b0; cbn; split; intros HH;
          first [ discriminate | reflexivity | exfalso; apply HH, Hs; reflexivity
                | intros HE; apply Hs in HE; discriminate ].
      - eapply rng_uleb_sound; [exact Hb|exact Hwco].
      - eapply rng_ultb_sound; [exact Hb|exact Hwco].
    Qed.
    Lemma rng_decide_spec {w : World} {σ} (op : RelOp σ) (t1 t2 : STerm σ w) (d : DList w) :
      rng_decide op t1 t2 = Some d -> instpred d ⊣⊢ instpred (formula_relop op t1 t2).
    Proof.
      unfold rng_decide. destruct (rng_decb op t1 t2) as [b|] eqn:Hb; [|discriminate].
      intros [= <-]. apply rng_dec_bridge, rng_decb_sound, Hb.
    Qed.
    Lemma rng_decide_propeq_spec {w : World} {σ} (t1 t2 : STerm σ w) (d : DList w) :
      rng_decide_propeq t1 t2 = Some d -> instpred d ⊣⊢ instpred (formula_propeq t1 t2).
    Proof.
      unfold rng_decide_propeq. destruct (rng_decb_propeq t1 t2) as [b|] eqn:Hb; [|discriminate].
      intros [= <-]. apply rng_dec_bridge. intros ι Hwco.
      destruct σ; try discriminate. cbn [rng_decb_propeq] in Hb.
      rewrite rng_propeq_iff; apply rng_forall_iff; intros p.
      eapply rng_eqb_sound; [exact Hb|exact Hwco].
    Qed.


    Definition try_lin_cancel {w : World} {σ} (op : RelOp σ)
      (t1 t2 : STerm σ w) : option (DList w) :=
      match lin_decide op t1 t2 with
      | Some d => Some d
      | None =>
          match rng_decide op t1 t2 with
          | Some d => Some d
          | None => try_bvadd_cancel op t1 t2
          end
      end.

    Definition simplify_relop {w : World} {σ} (op : RelOp σ) :
      forall (t1 t2 : STerm σ w), DList w :=
      match op in RelOp σ return forall (t1 t2 : STerm σ w), DList w with
      (* NB: `peval t1` is written out rather than let-bound -- a `let` in the
         definition leaves let-bound locals in the goal, which stops the
         spec proof's `match goal with context[...]` from seeing the real
         terms. *)
      | bop.eq => fun t1 t2 =>
          match try_lin_cancel bop.eq (peval t1) (peval t2) with
          | Some d => d
          | None => simplify_eq Term_eqb_relval
                      (λ (σ : Ty) (t1 t2 : Term w σ), dlist_eq t1 t2)
                      (peval t1) (peval t2)
          end
      | bop.neq => fun t1 t2 =>
          match try_lin_cancel bop.neq (peval t1) (peval t2) with
          | Some d => d
          | None => simplify_relopb bop.neq (peval t1) (peval t2)
          end
      (* Dispatch through try_fetch_bound exactly as the eq/neq arms dispatch
         through try_bvadd_cancel; None falls straight through to the
         pre-existing simplify_le. *)
      | bop.le => fun t1 t2 =>
          match try_fetch_bound t1 t2 with
          | Some d => d
          | None => simplify_le t1 t2
          end
      | bop.lt => simplify_lt
      (* S3: unsigned comparisons decided by intervals from wco first. *)
      | bop.bvule => fun t1 t2 =>
          match rng_decide bop.bvule (peval t1) (peval t2) with
          | Some d => d
          | None => simplify_relopb bop.bvule (peval t1) (peval t2)
          end
      | bop.bvult => fun t1 t2 =>
          match rng_decide bop.bvult (peval t1) (peval t2) with
          | Some d => d
          | None => simplify_relopb bop.bvult (peval t1) (peval t2)
          end
      | op     => fun t1 t2 => simplify_relopb op (peval t1) (peval t2)
      end.

    Lemma try_bvadd_cancel_spec {w : World} {σ} (op : RelOp σ)
      (t1 t2 : STerm σ w) (d : DList w) :
      try_bvadd_cancel op t1 t2 = Some d ->
      instpred d ⊣⊢ instpred (formula_relop op t1 t2).
    Proof.
      unfold try_bvadd_cancel.
      destruct σ; cbn; try discriminate.
      (* [op : RelOp (ty.bvec n)] with [n] already fixed -- a genuinely
         dependent case split, unlike `simplify_relop_spec`'s plain
         [destruct op] on a still-generic [σ].  [depelim] (Equations,
         already `Require Import`ed above) handles it; a bare [destruct]
         fails trying to re-generalize [σ] because [bvadd_cancel_pair]
         elsewhere in the goal pins it down. *)
      depelim op; cbn; try discriminate;
        destruct (bvadd_cancel_pair t1 t2) as [[[v1 v2] s]|] eqn:Hpair; cbn; try discriminate;
        destruct (secLeakT s) eqn:Hleak; cbn; try discriminate;
        intros [= <-];
        apply bvadd_cancel_pair_spec in Hpair as [-> ->];
        (* [Hleak : secLeakT s = true] is a bool equation, not the
           coerced-to-Prop [secLeakT s] that `secLeakT_spec` expects --
           `apply secLeakT_spec in Hleak` fails on the mismatch, hence the
           detour through an intermediate [Is_true] proof. *)
        assert (Hpub : secLeakT s) by (rewrite Hleak; exact I);
        apply secLeakT_spec in Hpub; destruct Hpub as [fromEntails0];
        (* [secLeakT_spec]'s conclusion is [instpred (formula_secLeak s)],
           one [instpred]-on-[Formula] dispatch layer above
           [instpred_formula_secLeak s].  That layer is DEFINITIONALLY
           transparent here (`reflexivity` proves the two equal) but a bare
           [cbn]/[unfold instpred_formula_secLeak] does not fire through it
           -- `change ... with ...` (full conversion, not cbn's heuristics)
           does. *)
        change (instpred (formula_secLeak s)) with (instpred_formula_secLeak s) in fromEntails0;
        match goal with |- instpred (if ?b then _ else _) ⊣⊢ _ => destruct b eqn:Hev end;
        (* NOT a bracket: a bracket's slots count the FULL flat goal list at
           that point (here 4 = 2 depelim branches x 2 from this destruct),
           not "2 alternatives for this one destruct" -- that miscount is
           exactly what cost the "expected 8 tactics" error two attempts
           ago. [first] picks whichever alternative applies, per goal,
           independent of how many goals are in flight. *)
        first [rewrite instpred_dlist_empty | rewrite instpred_dlist_error];
        constructor; intros ι Hwco; cbn; unfold instpred_formula_relop;
        specialize (fromEntails0 ι Hwco I);
        (* Peel the SECOND fold: [instpred_formula_secLeak s ι] is still
           folded (specializing substitutes ι but does not itself unfold
           anything) -- until [inst s ι] appears LITERALLY in fromEntails0's
           type, destructing [inst s ι] below has nothing of fromEntails0's
           to substitute into, no matter how the destruct's own goal
           reduces. *)
        change (instpred_formula_secLeak s ι) with (secLeak (inst s ι)) in fromEntails0;
        unfold bop.evalRel; cbn;
        (* [s] is public (secLeakT), so it denotes the SAME value [c] in
           both worlds -- [inst s ι] is [SyncVal c], never [NonSyncVal],
           which is what lets the cancellation go through without any
           NonSyncVal/[secLeak] case split on [v1]/[v2] themselves (see
           `secret-data-walls`: they are already plain [term_val]s, hence
           trivially public).  Again NOT a bracket, for the same reason as
           above (8 goals here, not 2) -- [match goal] reads [l]/[r] off
           whichever hypothesis is actually in front of it, so it works
           uniformly regardless of how many goals are in flight. *)
        (* Under the pair model [s] need not even be public: [bv.add] cancels
           a shared summand on EACH projection separately. *)
        destruct (inst s ι) as [l r] eqn:Hs;
        unfold bop.evalRel, ty.liftBinOp; cbn;
        assert (HcancelL : v1 = v2 <-> bv.add v1 l = bv.add v2 l) by
          (split; [intro; subst; reflexivity | eapply bv.add_cancel_r]);
        assert (HcancelR : v1 = v2 <-> bv.add v1 r = bv.add v2 r) by
          (split; [intro; subst; reflexivity | eapply bv.add_cancel_r]);
        match type of Hev with (if ?E then _ else _) = _ => destruct E as [Heqv|Hne] end;
        cbn in Hev; try discriminate;
        subst; try rewrite <- HcancelL; try rewrite <- HcancelR;
        (* The outer [True]/[False] here (from `instpred_dlist_empty`/
           `_error` above) is [Pred w]'s own `bi_pure`-style embedding, not
           literally Coq's `True`/`False` -- opaque to `cbn`'s unfolding
           heuristics AND to [intuition]'s syntactic atom-matching, even
           though it is fully convertible to plain `True`/`False`
           (confirmed: an isolated opaque-wrapper replica reproduces
           [intuition] getting stuck needing to produce the wrapped [True]
           positively, or to eliminate the wrapped [False], exactly like
           here). [exact I] / [destruct] / [exfalso] all check up to full
           conversion rather than syntax, so they see through it where
           [intuition] alone cannot; [tauto] finishes whatever is left once
           the wrapper is gone. *)
        split; intro HH;
        first
          [ solve [exact I]
          | solve [destruct HH]
          | solve [exfalso; tauto]
          | solve [tauto]
          | solve [exact HH]
          | solve [split; reflexivity]
          | solve [intuition congruence] ].
    Qed.

    (* ---- bvadd cancellation for formula_propeq --------------------------
       The SAME cancellation as `try_bvadd_cancel` above, for the
       PROPOSITIONAL equality constructor -- and, unlike that one, with NO
       [secLeakT] guard, in either direction.

       Why the guard is needed there and not here: [formula_relop]'s
       interpretation (Formulas.v:138) goes through
       [bop.eval_relop_relprop] and maps a [NonSyncVal] result to [False],
       so for a secret shared operand the formula is False no matter what
       the constants are -- which makes the "it holds" direction unsound
       without [secLeakT].  [formula_propeq]'s interpretation is
       [inst t1 ι = inst t2 ι], a STRUCTURAL equality on [RelVal] with no
       such wall, so both directions are unconditional:

         inst s ι = SyncVal c        -> SyncVal (add v1 c) = SyncVal (add v2 c)
                                        <-> v1 = v2                (bv.add_cancel_r)
         inst s ι = NonSyncVal l r   -> NonSyncVal (add v1 l) (add v1 r)
                                      = NonSyncVal (add v2 l) (add v2 r)
                                        <-> v1 = v2   (injectivity, then cancel
                                                       in each component)

       WHY THIS EXISTS AT ALL.  A loop whose exit compares two base-relative
       pointers emits `formula_propeq (bvadd c1 p) (bvadd c2 p)` -- NOT
       [formula_relop bop.eq], which is what `try_bvadd_cancel` is wired
       into (`simplify_relop`, below).  With c1 <> c2 that is impossible, but
       unrefuted it leaves one live dead path per trip and the whole rest of
       the program is re-verified under each: residual goals grow as
       `A_first + A_second * T_first`.  Measured on check_scalar's two-loop
       rig: 92 goals where 29 addresses are touched
       (case_study/RiscvPmp/CFGVer/diagnostics/
        check-scalar-combined-cost-drivers.md, §5.5).

       Note [formula_eq] is NOTATION for [formula_relop bop.eq]
       (Formulas.v:409) -- do not confuse it with [formula_propeq]. *)
    Definition try_bvadd_cancel_propeq {w : World} {σ} (t1 t2 : STerm σ w)
      : option (DList w) :=
      match σ return STerm σ w -> STerm σ w -> option (DList w) with
      | ty.bvec n =>
          fun t1 t2 =>
            match bvadd_cancel_pair t1 t2 with
            | Some (v1, v2, _) =>
                Some (if bop.eval_relop_val bop.eq v1 v2 then empty else error)
            | None => None
            end
      | _ => fun _ _ => None
      end t1 t2.

    Lemma try_bvadd_cancel_propeq_spec {w : World} {σ} (t1 t2 : STerm σ w)
      (d : DList w) :
      try_bvadd_cancel_propeq t1 t2 = Some d ->
      instpred d ⊣⊢ instpred (formula_propeq t1 t2).
    Proof.
      (* [cbn] only in the HYPOTHESIS: cbn on the goal unfolds
         [instpred (formula_propeq _ _)] into [instpred_formula_propeq _ _],
         after which [instpred_formula_propeqₚ] no longer matches (its
         primed twin does -- but keeping the goal folded is simpler). *)
      unfold try_bvadd_cancel_propeq. intros Hc.
      destruct σ; cbn in Hc; try discriminate.
      destruct (bvadd_cancel_pair t1 t2) as [[[v1 v2] s]|] eqn:Hpair;
        try discriminate.
      injection Hc as <-.
      apply bvadd_cancel_pair_spec in Hpair as [-> ->].
      rewrite instpred_formula_propeqₚ.
      (* Read [v1 = v2] / [v1 <> v2] off the boolean test via its reflect
         lemma rather than by syntactically destructing the underlying
         decidable -- the [if] shape that `try_bvadd_cancel_spec` matches on
         is only exposed there by an earlier [depelim op; cbn]. *)
      match goal with |- instpred (if ?b then _ else _) ⊣⊢ _ => destruct b eqn:Hev end;
        pose proof (bop.eval_relop_val_spec bop.eq v1 v2) as Hrefl;
        (* [cbn in Hrefl] FIRST: destructing the goal's boolean already
           exposed it in reduced form ([eq_dec v1 v2 ||| false]), so [Hev]
           and [Hrefl] must be brought to the same normal form before the
           rewrite can see a match. *)
        cbn in Hrefl; rewrite Hev in Hrefl;
        [ rewrite instpred_dlist_empty | rewrite instpred_dlist_error ];
        constructor; intros ι Hwco; cbn;
        unfold bop.evalRel, ty.liftBinOp, ty.liftBinOpRV; cbn;
        (* the ONE case split: sync vs non-sync shared operand.  Both give
           the same answer -- that is the whole point of doing this on
           [formula_propeq], which has no NonSyncVal-to-False wall, rather
           than on [formula_relop]. *)
        destruct (inst s ι) as [l r] eqn:Hs; cbn;
        inversion Hrefl as [Heqv|Hne]; subst;
        split; intro HH;
        first
          [ solve [exact I]
          | solve [destruct HH]
          | solve [reflexivity]
          (* NEITHER [injection] NOR [inversion] here: both dig THROUGH
             [bv.add] into its [bv.truncn (bv.bin _ + bv.bin _)]
             representation, so the equation they hand back is not in
             [bv.add_cancel_r]'s shape and [exact] fails.  [congruence] on
             the constructor arguments -- grabbed from the hypothesis by
             pattern, since the shared operand is bound by the [destruct]
             above and is named differently per branch -- keeps [bv.add]
             folded.  (Verified in preamble mode before touching this file;
             see the rocq-implementation skill.) *)
          | solve [exfalso; apply Hne;
                   match goal with
                   | H : SyncVal ?a = SyncVal ?b |- _ =>
                       assert (Hc : a = b) by congruence;
                       exact (bv.add_cancel_r Hc)
                   | H : NonSyncVal ?a _ = NonSyncVal ?b _ |- _ =>
                       assert (Hc : a = b) by congruence;
                       exact (bv.add_cancel_r Hc)
                   end]
          | solve [assumption] ].
    Qed.

    (* ---- the DUAL of bvadd_cancel_pair ----------------------------------
       `bvadd_cancel_pair` recognises a shared TERM summand with differing
       LITERALS (`c1 + p` vs `c2 + p`) and DECIDES the equation.  The mirror
       shape -- a shared LITERAL with differing TERMS (`c + x` vs `c + y`) --
       cannot be decided, but it can be WEAKENED to `x = y`, and that is worth
       doing because the remaining equation is the one shape the evar
       machinery can act on: `unify_pathcondition` substitutes a VARIABLE
       equation, and no such substitution exists for a `bvadd` of one.

       WHERE THIS BITES.  CFGVer's block-contract hook (`sexec_block`,
       CFGVer/Verifier.v) instantiates a block's logic context ANGELICALLY and
       then consumes the block's precondition.  A register pinned as `base + k`
       -- `X2 |-> sp + 16`, a stack pointer -- yields exactly
       `formula_propeq (0x10 + sp.1) (0x10 + sp)` against the caller's heap.
       Unsolved, `sp.1` stays free, and the NEXT chunk addressed from it
       (`ptstomem sp.1 _`, the first stack cell) then matches nothing in the
       heap: the consume FAILS OUTRIGHT with a `debug_consume_chunk` error,
       not a residual.  A register pinned BARE (`A0 |-> xb`) is unaffected,
       which is what makes the failure look arbitrary from outside.  The same
       shape with k=0 on both sides (`q + 0` vs `q.1 + 0`, which every
       `gen_seg_contract` placement carries) is the other instance.

       NO PUBLICNESS GUARD, for `try_bvadd_cancel_propeq`'s reason exactly:
       `formula_propeq` is a STRUCTURAL equality on `RelVal` with no
       NonSyncVal-to-False wall, so the weakening holds in the SyncVal and the
       NonSyncVal case alike, componentwise.  Contrast `try_bvadd_cancel`,
       wired into `formula_relop`, which does need `secLeakT`.

       NEVER `error`: the returned DList is EQUIVALENT to the input formula
       (that is the spec), never a refutation. *)

    Definition try_bvadd_cancel_val_propeq {w : World} {σ} (t1 t2 : STerm σ w)
      : option (DList w) :=
      match σ return STerm σ w -> STerm σ w -> option (DList w) with
      | ty.bvec n =>
          fun t1 t2 =>
            match bvadd_split_val t1, bvadd_split_val t2 with
            | Some (v1, s1), Some (v2, s2) =>
                if bv.eqb v1 v2
                then
                  (* Fall THROUGH when the stripped terms are syntactically
                     equal: `simplify_propeq`'s own Term_eqb check closes that
                     to `empty`, whereas firing here would emit a redundant
                     `propeq x x` into the path condition.  (It would be
                     cleared by a later `combined_solver` pass rather than
                     survive, but a rule should not manufacture work for one.) *)
                  if Term_eqb s1 s2 then None else Some (dlist_propeq s1 s2)
                else None
            | _, _ => None
            end
      | _ => fun _ _ => None
      end t1 t2.

    Lemma try_bvadd_cancel_val_propeq_spec {w : World} {σ} (t1 t2 : STerm σ w)
      (d : DList w) :
      try_bvadd_cancel_val_propeq t1 t2 = Some d ->
      instpred d ⊣⊢ instpred (formula_propeq t1 t2).
    Proof.
      unfold try_bvadd_cancel_val_propeq. intros Hc.
      destruct σ; cbn in Hc; try discriminate.
      destruct (bvadd_split_val t1) as [[v1 s1]|] eqn:H1; try discriminate.
      destruct (bvadd_split_val t2) as [[v2 s2]|] eqn:H2; try discriminate.
      destruct (bv.eqb_spec v1 v2) as [Heq|Hne]; try discriminate.
      destruct (Term_eqb s1 s2); try discriminate.
      injection Hc as <-. subst v2.
      rewrite instpred_dlist_singleton. rewrite !instpred_formula_propeqₚ.
      constructor; intros ι Hwco; cbn.
      rewrite (bvadd_split_val_inst _ H1 ι) (bvadd_split_val_inst _ H2 ι).
      unfold bop.evalRel, ty.liftBinOp, ty.liftBinOpRV; cbn.
      (* Both RelVal cases give the SAME answer -- the point of doing this on
         formula_propeq rather than formula_relop.  `congruence` rather than
         `injection`/`inversion`, which dig through `bv.add` into its
         `bv.truncn` representation and hand back an equation that
         `bv.add_cancel_l` no longer matches. *)
      destruct (inst s1 ι) as [a1 a2]; destruct (inst s2 ι) as [b1 b2]; cbn;
        split; intro HH; try discriminate; try congruence.
      (* `bv.add` SPELLED OUT: this file does not `Import bv.notations`, so
         `(v1 + x)%bv` elaborates `+` to something expecting a nat and fails
         with "v1 has type Val (ty.bvec n) while it is expected to have type
         nat" -- far from the cause. *)
      all: f_equal;
        match goal with
        | |- ?x = ?y =>
            let Hc := fresh "Hc" in
            assert (Hc : bv.add v1 x = bv.add v1 y) by congruence;
            exact (bv.add_cancel_l Hc)
        end.
    Qed.

    Lemma secLeakT_inst {w : World} {σ} (a : Term w σ) (ι : Valuation w) :
      Is_true (secLeakT a) -> instprop (wco w) ι -> secLeak (inst a ι).
    Proof.
      intros H Hw. apply secLeakT_spec in H. destruct H as [H].
      specialize (H ι Hw I). cbn in H. exact H.
    Qed.

    (* ---- ISOLATE THE INNERMOST VARIABLE: `x + s = y` ⟶ `x = y + (-1)·s` -----
       (PLAN-rsa.md Phase 1, 2026-10-22.)  try_unify_eq solves only a BARE
       `var = term`, so on `x + s = y` it can only eliminate y.  In an ASSERT
       that is the wrong variable whenever x is an angelic one introduced by a
       consume -- a contract's or a block's logic variables are bound AFTER the
       state they are matched against -- and y a variable of that state: the
       obligation becomes `assert_vareq y (x + s)` on a universally bound y,
       which postprocess cannot discharge (it would have to invert the term),
       while `assert_vareq x (y − s)` is just a witness.  Worked case: a LoopN
       block entered from a callee precondition, `4 + (eX − 4·mw) = 4 + xa`,
       which try_bvadd_cancel_val_propeq weakens to `eX − 4·mw = xa`.

       The solver has no quantifier information, so the INNERMOST variable
       (smallest ctx.in_at) is the proxy for "the existential", which is
       faithful exactly where these equations arise (a consume's evars are
       innermost).  Where it is not (an inner universal against an outer
       existential), neither orientation is dischargeable, so nothing is lost.
       Either orientation states the same equation: this is a completeness
       rule, never a soundness one.

       GUARDED by secLeakT s.  The guard was load-bearing under the tagged
       RelVal (`y − s` with x = SyncVal a, s = NonSyncVal t1 t2 was
       NonSyncVal a a ≠ x); with RelVal a pair the inversion holds per
       projection for ANY s, so the guard is now only a cost filter -- a
       repair candidate, logged in relval-pair-baseline/AUDIT.md.  Fires only when the other side is a bare variable
       y OUTER to x: if y is inner, try_unify_eq already eliminates it. *)
    Equations bvadd_split_var {Σ n} (t : Term Σ (ty.bvec n))
      : option (Term Σ (ty.bvec n) * nat * Term Σ (ty.bvec n)) :=
      bvadd_split_var (term_binop bop.bvadd (@term_var _ x _ xIn) s) :=
        Some (@term_var _ x _ xIn, ctx.in_at xIn, s);
      bvadd_split_var (term_binop bop.bvadd s (@term_var _ x _ xIn)) :=
        Some (@term_var _ x _ xIn, ctx.in_at xIn, s);
      bvadd_split_var _ := None.

    Lemma relval_bvadd_comm {n} (a b : RelVal (ty.bvec n)) :
      bop.evalRel bop.bvadd a b = bop.evalRel bop.bvadd b a.
    Proof.
      unfold bop.evalRel, ty.liftBinOp, ty.liftBinOpRV; cbn.
      destruct a as [a1 a2]; destruct b as [b1 b2]; cbn; f_equal; apply bv.add_comm.
    Qed.

    Lemma bvadd_split_var_inst {Σ n} (t : Term Σ (ty.bvec n)) x i s :
      bvadd_split_var t = Some (x, i, s) ->
      forall ι : Valuation Σ,
        inst t ι = bop.evalRel bop.bvadd (inst x ι) (inst s ι).
    Proof.
      funelim (bvadd_split_var t); intros Heq; try discriminate;
        injection Heq as <- <- <-; intros ι; [reflexivity|..];
        apply relval_bvadd_comm.
    Qed.

    Lemma bv_add_sub_cancel {n} (a c : bv n) : bv.sub (bv.add a c) c = a.
    Proof. unfold bv.sub. rewrite <- bv.add_assoc. rewrite bv.add_negate2. apply bv.add_zero_r. Qed.
    Lemma bv_sub_add_cancel {n} (a c : bv n) : bv.add (bv.sub a c) c = a.
    Proof. unfold bv.sub. rewrite <- bv.add_assoc. rewrite bv.add_negate. apply bv.add_zero_r. Qed.
    (* multiplication by the literal -1 is negation; via the stdlib's almost-ring
       lemmas, since bv has no generically declared `ring` *)
    Lemma bv_mul_m1 {n} (c : bv n) : bv.mul (bv.of_Z (-1)) c = bv.negate c.
    Proof.
      pose proof (Coq.setoid_ring.Ring_theory.Rth_ARth
                    (Coq.setoid_ring.Ring_theory.Eqsth (bv n))
                    (Coq.setoid_ring.Ring_theory.Eq_ext bv.add bv.mul bv.negate)
                    (bv.ring_theory n)) as AR.
      (* `-1` is the numeral Z.neg 1, not syntactically `Z.opp 1` *)
      replace (@bv.of_Z n (-1)) with (bv.negate (@bv.of_Z n 1))
        by (rewrite bv.of_Z_negate; reflexivity).
      rewrite bv.of_Z_one.
      rewrite <- (Coq.setoid_ring.Ring_theory.ARopp_mul_l AR).
      now rewrite bv.mul_one_l.
    Qed.

    (* `x + c = y ⇔ x = y − c` over RelVals, for a SYNCHRONISED c *)
    Lemma relval_isolate {n} (x y : RelVal (ty.bvec n)) (c : bv n) :
      bop.evalRel bop.bvadd x (SyncVal c) = y <->
      x = bop.evalRel bop.bvsub y (SyncVal c).
    Proof.
      unfold bop.evalRel, ty.liftBinOp, ty.liftBinOpRV; cbn.
      destruct x as [a1 a2]; destruct y as [b1 b2]; cbn; split; intro H.
      (* projections, not injection: injection digs through bv.add into its
         bv.truncn representation (see try_bvadd_cancel_val_propeq_spec) *)
      all: pose proof (f_equal ty.projLeftRV H) as HL;
           pose proof (f_equal ty.projRightRV H) as HR;
           cbn in HL, HR; subst; f_equal;
           first [ symmetry; apply bv_add_sub_cancel | apply bv_sub_add_cancel ].
    Qed.

    (* ...in the form the rule EMITS, `y + (-1)·c`: peval's ring normal form
       folds it (`xa + (-1)·(-4·m)` is `xa + 4·m`), whereas `bvsub` is left
       alone by peval and by the closers, so `y − c` survived as a residual
       (measured, 2026-10-22) *)
    Lemma relval_isolate_mul {n} (x y : RelVal (ty.bvec n)) (c : bv n) :
      bop.evalRel bop.bvadd x (SyncVal c) = y <->
      x = bop.evalRel bop.bvadd y
            (bop.evalRel bop.bvmul (SyncVal (bv.of_Z (-1))) (SyncVal c)).
    Proof.
      rewrite (relval_isolate x y c).
      unfold bop.evalRel, ty.liftBinOp, ty.liftBinOpRV; cbn.
      rewrite bv_mul_m1. now destruct y.
    Qed.

    Definition term_var_at {Σ σ} (t : Term Σ σ) : option nat :=
      match t with @term_var _ _ _ yIn => Some (ctx.in_at yIn) | _ => None end.

    (* one orientation: l = x + s, r a bare variable outer to x *)
    Definition try_isolate_aux {w : World} {n} (l r : Term w (ty.bvec n))
      : option (Term w (ty.bvec n) * Term w (ty.bvec n)) :=
      match bvadd_split_var l, term_var_at r with
      | Some (x, i, s), Some j =>
          if andb (Nat.ltb i j) (secLeakT s)
          then Some (x, term_binop bop.bvadd r
                          (term_binop bop.bvmul (term_val (ty.bvec n) (bv.of_Z (-1))) s))
          else None
      | _, _ => None
      end.

    (* both orientations *)
    Definition try_isolate_pair {w : World} {n} (l r : Term w (ty.bvec n))
      : option (DList w) :=
      match try_isolate_aux l r with
      | Some (x, e) => Some (dlist_propeq x e)
      | None =>
          match try_isolate_aux r l with
          | Some (x, e) => Some (dlist_propeq x e)
          | None => None
          end
      end.

    (* ...also under a SHARED LITERAL, `c + l = c + r`.  That case is the one
       that matters, and it is why this runs BEFORE try_bvadd_cancel_val_propeq
       rather than on its output: solver_generic simplifies and then UNIFIES in
       the same pass, so the weakened `l = r` that rule emits reaches
       try_unify_eq before any later simplify pass could isolate it -- placed
       after it, this rule never fired (measured, 2026-10-22). *)
    Definition try_isolate_inner {w : World} {σ} (t1 t2 : STerm σ w)
      : option (DList w) :=
      match σ return STerm σ w -> STerm σ w -> option (DList w) with
      | ty.bvec n =>
          fun t1 t2 =>
            match try_isolate_pair t1 t2 with
            | Some d => Some d
            | None =>
                match bvadd_split_val t1, bvadd_split_val t2 with
                | Some (v1, s1), Some (v2, s2) =>
                    if bv.eqb v1 v2 then try_isolate_pair s1 s2 else None
                | _, _ => None
                end
            end
      | _ => fun _ _ => None
      end t1 t2.

    Lemma relval_bvadd_cancel_val {n} (v : bv n) (a b : RelVal (ty.bvec n)) :
      bop.evalRel bop.bvadd (SyncVal v) a = bop.evalRel bop.bvadd (SyncVal v) b <->
      a = b.
    Proof.
      split; [|now intros ->].
      unfold bop.evalRel, ty.liftBinOp, ty.liftBinOpRV; cbn.
      destruct a as [a1 a2]; destruct b as [b1 b2]; cbn; intro H;
        pose proof (f_equal ty.projLeftRV H) as HL;
        pose proof (f_equal ty.projRightRV H) as HR;
        cbn in HL, HR; f_equal; eapply bv.add_cancel_l; eassumption.
    Qed.

    Lemma try_isolate_aux_inst {w : World} {n} (l r : Term w (ty.bvec n)) x e
      (ι : Valuation w) :
      try_isolate_aux l r = Some (x, e) -> instprop (wco w) ι ->
      (inst l ι = inst r ι <-> inst x ι = inst e ι).
    Proof.
      unfold try_isolate_aux. intros H Hw.
      destruct (bvadd_split_var l) as [[[x' i] s]|] eqn:Hl; try discriminate.
      destruct (term_var_at r) as [j|]; try discriminate.
      destruct (andb (Nat.ltb i j) (secLeakT s)) eqn:Hg; try discriminate.
      injection H as <- <-.
      apply andb_prop in Hg as [_ Hs].
      pose proof (secLeakT_inst s ι (Is_true_eq_left _ Hs) Hw) as Hsl.
      rewrite (bvadd_split_var_inst _ Hl ι). cbn.
      destruct (inst s ι) as [c c2]; hnf in Hsl; cbn in Hsl; subst c2.
      apply (relval_isolate_mul _ _ c).
    Qed.

    Lemma try_isolate_pair_spec {w : World} {n} (l r : Term w (ty.bvec n)) (d : DList w) :
      try_isolate_pair l r = Some d ->
      instpred d ⊣⊢ instpred (formula_propeq l r).
    Proof.
      unfold try_isolate_pair. intros Hc.
      destruct (try_isolate_aux l r) as [[x e]|] eqn:H1.
      - injection Hc as <-.
        rewrite instpred_dlist_singleton. rewrite !instpred_formula_propeqₚ.
        constructor; intros ι Hwco; cbn.
        symmetry. apply (try_isolate_aux_inst l r ι H1 Hwco).
      - destruct (try_isolate_aux r l) as [[x e]|] eqn:H2; try discriminate.
        injection Hc as <-.
        rewrite instpred_dlist_singleton. rewrite !instpred_formula_propeqₚ.
        constructor; intros ι Hwco; cbn.
        rewrite <- (try_isolate_aux_inst r l ι H2 Hwco).
        split; intros; symmetry; assumption.
    Qed.

    Lemma try_isolate_inner_spec {w : World} {σ} (t1 t2 : STerm σ w) (d : DList w) :
      try_isolate_inner t1 t2 = Some d ->
      instpred d ⊣⊢ instpred (formula_propeq t1 t2).
    Proof.
      unfold try_isolate_inner. intros Hc.
      destruct σ; cbn in Hc; try discriminate.
      destruct (try_isolate_pair t1 t2) as [d'|] eqn:H1.
      - injection Hc as <-. now apply try_isolate_pair_spec.
      - destruct (bvadd_split_val t1) as [[v1 s1]|] eqn:E1; try discriminate.
        destruct (bvadd_split_val t2) as [[v2 s2]|] eqn:E2; try discriminate.
        destruct (bv.eqb_spec v1 v2) as [<-|]; try discriminate.
        apply try_isolate_pair_spec in Hc. rewrite Hc. rewrite !instpred_formula_propeqₚ.
        constructor; intros ι Hwco; cbn.
        rewrite (bvadd_split_val_inst _ E1 ι) (bvadd_split_val_inst _ E2 ι).
        symmetry. apply relval_bvadd_cancel_val.
    Qed.

    Lemma try_lin_cancel_spec {w : World} {σ} (op : RelOp σ) (t1 t2 : STerm σ w) (d : DList w) :
      try_lin_cancel op t1 t2 = Some d -> instpred d ⊣⊢ instpred (formula_relop op t1 t2).
    Proof.
      unfold try_lin_cancel. destruct (lin_decide op t1 t2) as [d'|] eqn:H.
      - intros [= <-]. now apply lin_decide_spec in H.
      - destruct (rng_decide op t1 t2) as [d'|] eqn:H2.
        + intros [= <-]. now apply rng_decide_spec in H2.
        + apply try_bvadd_cancel_spec.
    Qed.

    Definition try_lin_propeq {w : World} {σ} (t1 t2 : STerm σ w) : option (DList w) :=
      match lin_decide_propeq t1 t2 with
      | Some d => Some d
      | None =>
          match rng_decide_propeq t1 t2 with
          | Some d => Some d
          | None => try_bvadd_cancel_propeq t1 t2
          end
      end.
    Lemma try_lin_propeq_spec {w : World} {σ} (t1 t2 : STerm σ w) (d : DList w) :
      try_lin_propeq t1 t2 = Some d -> instpred d ⊣⊢ instpred (formula_propeq t1 t2).
    Proof.
      unfold try_lin_propeq. destruct (lin_decide_propeq t1 t2) as [d'|] eqn:H.
      - intros [= <-]. now apply lin_decide_propeq_spec in H.
      - destruct (rng_decide_propeq t1 t2) as [d'|] eqn:H2.
        + intros [= <-]. now apply rng_decide_propeq_spec in H2.
        + apply try_bvadd_cancel_propeq_spec.
    Qed.

    (* ---- PLAN-bv-arith-solver S2: solve a bv propeq for its INNERMOST unit variable ----
       Same linear view of `t1 - t2`.  Among the atoms that are a bare variable
       with coefficient +-1 and occur in no other atom, pick the innermost
       (smallest ctx.in_at) and emit `x = -k * rest`, so unification eliminates
       that variable whatever the equation's orientation -- try_isolate_inner
       needs the `x + s = y` shape.  UNGUARDED (D2): propeq is pair equality and
       the rewrite is an equivalence in both runs, secret or not. *)
Section Iso.
  Context {Σ : LCtx} {n : nat}.
  Local Notation T := (Term Σ (ty.bvec n)).
  Add Ring LinTR3 : (Term_bv_ring_theory Σ n) (setoid (@term_equivalence Σ (ty.bvec n)) (Term_bv_ring_eq_ext Σ n)).
  Local Notation "a ⊕ b" := (term_binop bop.bvadd a b) (at level 50, left associativity).
  Local Notation "a ⊗ b" := (term_binop bop.bvmul a b) (at level 40, left associativity).

  Fixpoint lin_splits (l : list (Z * T)) : list ((Z * T) * list (Z * T)) :=
    match l with
    | nil => nil
    | cons p l' => cons (p, l') (List.map (fun '(q, r) => (q, cons p r)) (lin_splits l'))
    end.
  Lemma lin_splits_sound c l k a r : List.In ((k, a), r) (lin_splits l) ->
    lin_eval c l ≡ tvZ k ⊗ a ⊕ lin_eval c r.
  Proof.
    revert r; induction l as [|[k' a'] l IH]; intros r; cbn [lin_splits List.In]; [easy|].
    intros [[= <- <- <-]|Hin]; [now rewrite lin_eval_cons|].
    apply List.in_map_iff in Hin as [[[k2 a2] r2] [Heq Hin]]. injection Heq as <- <- <-.
    rewrite !lin_eval_cons (IH _ Hin). ring.
  Qed.
  Definition var_free_in {τ} (a : T) (b : Term Σ τ) : bool :=
    match a with
    | @term_var _ x _ xIn => option.isSome (occurs_check xIn b)
    | _ => false
    end.
  Definition is_unit (k : Z) : bool :=
    orb (bv.eqb (@bv.of_Z n k) bv.one) (bv.eqb (@bv.of_Z n k) (bv.of_Z (-1))).
  Definition lin_cands (l : list (Z * T)) : list (nat * ((Z * T) * list (Z * T))) :=
    List.flat_map (fun '((k, a), r) =>
      match term_var_at a with
      | Some i => if andb (is_unit k) (List.forallb (fun '(_, b) => var_free_in a b) r)
                  then cons (i, ((k, a), r)) nil else nil
      | None => nil
      end) (lin_splits l).
  Fixpoint pick_min {X} (l : list (nat * X)) : option (nat * X) :=
    match l with
    | nil => None
    | cons p l' => match pick_min l' with
                   | Some q => if Nat.ltb (fst q) (fst p) then Some q else Some p
                   | None => Some p
                   end
    end.
  Lemma pick_min_in {X} (l : list (nat * X)) p : pick_min l = Some p -> List.In p l.
  Proof.
    induction l as [|p' l IH]; cbn [pick_min List.In]; [discriminate|].
    destruct (pick_min l) as [q|]; [destruct (Nat.ltb (fst q) (fst p'))|]; intros [= <-]; auto.
  Qed.
  Lemma lin_cands_in l i k a r : List.In (i, ((k, a), r)) (lin_cands l) ->
    List.In ((k, a), r) (lin_splits l) /\ is_unit k = true.
  Proof.
    unfold lin_cands. intros Hin. apply List.in_flat_map in Hin as [[[k' a'] r'] [Hs Hin]].
    destruct (term_var_at a'); [|destruct Hin].
    destruct (andb (is_unit k') _) eqn:Hu; [|destruct Hin].
    destruct Hin as [[= <- <- <- <-]|[]]. apply andb_prop in Hu as [Hu _]. auto.
  Qed.
  Lemma is_unit_sq k : is_unit k = true -> tvZ k ⊗ tvZ k ≡ (tvZ 1 : T).
  Proof.
    unfold is_unit. intros [Hk|Hk]%orb_prop.
    - destruct (bv.eqb_spec (@bv.of_Z n k) bv.one) as [E|]; [|discriminate].
      unfold tvZ at 1 2. rewrite E tvZ_one. ring.
    - destruct (bv.eqb_spec (@bv.of_Z n k) (bv.of_Z (-1))) as [E|]; [|discriminate].
      unfold tvZ at 1 2. rewrite E. change (tvZ (-1) ⊗ tvZ (-1) ≡ (tvZ 1 : T)).
      rewrite tvZ_m1 tvZ_one. ring.
  Qed.
  Lemma inst_diff_zero (u v : T) ι : inst u ι = inst v ι ->
    inst (u ⊕ tvZ (-1) ⊗ v) ι = inst (tvZ 0 : T) ι.
  Proof.
    intros H. assert (E : v ⊕ tvZ (-1) ⊗ v ≡ (tvZ 0 : T)) by (rewrite tvZ_m1 tvZ_zero; ring).
    specialize (E ι). cbn in E |- *. rewrite H. exact E.
  Qed.
  Lemma inst_of_diff (u v w kk : T) ι : u ≡ v ⊕ kk ⊗ w ->
    inst w ι = inst (tvZ 0 : T) ι -> inst u ι = inst v ι.
  Proof.
    intros E Hw. assert (E0 : v ⊕ kk ⊗ tvZ 0 ≡ v) by (rewrite tvZ_zero; ring).
    rewrite (E ι). specialize (E0 ι). cbn in E0, Hw |- *. rewrite Hw. exact E0.
  Qed.
  Definition lin_iso (t1 t2 : T) : option (T * T) :=
    let '(c, ms) := lin_view qfuel (lin_diff t1 t2) in
    match pick_min (lin_cands (lin_prune ms)) with
    | Some (_, ((k, a), r)) => Some (a, canon_term (tvZ (-1) ⊗ tvZ k ⊗ lin_eval c r))
    | None => None
    end.
  Lemma lin_iso_inst t1 t2 a b : lin_iso t1 t2 = Some (a, b) ->
    forall ι, inst t1 ι = inst t2 ι <-> inst a ι = inst b ι.
  Proof.
    unfold lin_iso.
    pose proof (lin_view_sound qfuel (lin_diff t1 t2)) as Hs.
    destruct (lin_view qfuel (lin_diff t1 t2)) as [c ms].
    pose proof (lin_eval_prune c ms) as Hp.
    destruct (pick_min (lin_cands (lin_prune ms))) as [[i [[k a'] r]]|] eqn:Hm; [|discriminate].
    intros [= <- <-] ι.
    apply pick_min_in, lin_cands_in in Hm as [Hsp Hu].
    pose proof (lin_splits_sound c _ _ _ _ Hsp) as Hsplit.
    pose proof (is_unit_sq _ Hu) as Hkk.
    rewrite lin_diff_equiv in Hs.
    assert (HD : t1 ⊕ tvZ (-1) ⊗ t2 ≡ tvZ k ⊗ a' ⊕ lin_eval c r)
      by (now rewrite <- Hs, <- Hp, Hsplit).
    set (R := lin_eval c r) in *.
    pose proof (canon_term_equiv (tvZ (-1) ⊗ tvZ k ⊗ R)) as Hb.
    set (b := canon_term _) in *.
    split; intros H.
    - apply (inst_of_diff (w := t1 ⊕ tvZ (-1) ⊗ t2) (kk := tvZ k)); [|now apply inst_diff_zero].
      rewrite Hb HD.
      transitivity ((tvZ k ⊗ tvZ k) ⊗ a' ⊕ tvZ (-1) ⊗ tvZ k ⊗ R ⊕ tvZ k ⊗ R); [|ring].
      rewrite Hkk tvZ_one tvZ_m1. ring.
    - apply (inst_of_diff (w := a' ⊕ tvZ (-1) ⊗ b) (kk := tvZ k)); [|now apply inst_diff_zero].
      rewrite Hb.
      transitivity (t2 ⊕ (t1 ⊕ tvZ (-1) ⊗ t2)); [rewrite tvZ_m1; ring|].
      rewrite HD.
      transitivity (t2 ⊕ tvZ k ⊗ a' ⊕ (tvZ k ⊗ tvZ k) ⊗ R); [|rewrite tvZ_m1; ring].
      rewrite Hkk tvZ_one. ring.
  Qed.
End Iso.

    Definition lin_isolate {w : World} {σ} (t1 t2 : STerm σ w) : option (DList w) :=
      match σ return STerm σ w -> STerm σ w -> option (DList w) with
      | ty.bvec n => fun t1 t2 =>
          match lin_iso t1 t2 with
          | Some (a, b) => Some (dlist_propeq a b)
          | None => None end
      | _ => fun _ _ => None
      end t1 t2.
    Lemma lin_isolate_spec {w : World} {σ} (t1 t2 : STerm σ w) (d : DList w) :
      lin_isolate t1 t2 = Some d -> instpred d ⊣⊢ instpred (formula_propeq t1 t2).
    Proof.
      unfold lin_isolate. intros Hc.
      destruct σ; cbn in Hc; try discriminate.
      destruct (lin_iso t1 t2) as [[a b]|] eqn:Hl; try discriminate. injection Hc as <-.
      rewrite instpred_dlist_singleton. rewrite !instpred_formula_propeqₚ.
      constructor; intros ι Hwco; cbn. symmetry. exact (lin_iso_inst _ _ Hl ι).
    Qed.

    Definition try_lin_isolate {w : World} {σ} (t1 t2 : STerm σ w) : option (DList w) :=
      match lin_isolate t1 t2 with
      | Some d => Some d
      | None => try_isolate_inner t1 t2
      end.
    Lemma try_lin_isolate_spec {w : World} {σ} (t1 t2 : STerm σ w) (d : DList w) :
      try_lin_isolate t1 t2 = Some d -> instpred d ⊣⊢ instpred (formula_propeq t1 t2).
    Proof.
      unfold try_lin_isolate. destruct (lin_isolate t1 t2) as [d'|] eqn:H.
      - intros [= <-]. now apply lin_isolate_spec in H.
      - apply try_isolate_inner_spec.
    Qed.

    (* ---- soundness of the fetch-bound discharge --------------------------
       Everything below stays at the `instprop` (plain Prop) level and is
       lifted to `Pred w` exactly once, in `try_fetch_bound_spec`.  That is
       deliberate: `instprop_formula`'s `formula_relop` case is literally the
       shape `relval_fetch_upper_add` (CFGVer/Contracts.v) reasons about, so
       the Prop level is where the argument is short. *)

    Lemma int_bound_shape_spec {Σ} (t : Term Σ ty.int) L K u :
      int_bound_shape t = Some (L, K, u) ->
      t = term_binop bop.minus (term_val ty.int L)
            (term_binop bop.plus (term_val ty.int K) u).
    Proof.
      funelim (int_bound_shape t); intros Heq; try discriminate.
      now inversion Heq.
    Qed.

    Lemma unsigned_bvadd_split_spec {Σ} (u : Term Σ ty.int)
      (c : Z) (u' : Term Σ ty.int) (n : nat) :
      unsigned_bvadd_split u = Some (c, u', n) ->
      exists (cbv : bv n) (s : Term Σ (ty.bvec n)),
        u = term_unop uop.unsigned
              (term_binop bop.bvadd (term_val (ty.bvec n) cbv) s) /\
        u' = term_unop uop.unsigned s /\
        c = Z.of_N (bv.bin cbv).
    Proof.
      funelim (unsigned_bvadd_split u); intros Heq; try discriminate.
      inversion Heq; subst; clear Heq.
      exists c, s; repeat split; auto.
    Qed.

    (* The whole semantic content.  Both RelVal cases were verified in
       isolation over `ty.liftBinOpRV`/`liftUnOpRV` (which is what
       `bop.evalRel`/`uop.evalRel` reduce to) before this file was compiled:
       the SyncVal case is `bv.bin_add_small` plus linear arithmetic, and the
       NonSyncVal case needs NO publicness guard because the HYPOTHESIS is
       itself `False` there -- `instprop_formula` sends a NonSyncVal operand to
       False on the path-condition side too. *)
    Lemma fetch_bound_entails_sound {Σ} (L2 K L1 B : Z)
      (ug uw : Term Σ ty.int) (ι : Valuation Σ) :
      fetch_bound_entails L2 K L1 B ug uw = true ->
      instprop (formula_relop bop.le (term_val ty.int 0%Z)
                  (term_binop bop.minus (term_val ty.int L1)
                     (term_binop bop.plus (term_val ty.int B) uw))) ι ->
      instprop (formula_relop bop.le (term_val ty.int 0%Z)
                  (term_binop bop.minus (term_val ty.int L2)
                     (term_binop bop.plus (term_val ty.int K) ug))) ι.
    Proof.
      unfold fetch_bound_entails. intros Hb Hpc.
      apply andb_prop in Hb as [Hb0 Hb1].
      apply andb_prop in Hb0 as [Hl12 HK0].
      apply Z.leb_le in Hl12. apply Z.leb_le in HK0.
      destruct (Term_eqb ug uw) eqn:Heqb.
      - (* offset 0 -- the bare base; no no-wrap side condition needed *)
        pose proof (Term_eqb_spec ug uw) as Hsp; rewrite Heqb in Hsp.
        inversion Hsp; subst.
        apply Z.leb_le in Hb1.
        revert Hpc. cbn.
        destruct (inst uw ι) as [a b]; cbn.
        unfold bv.unsigned in *. lia.
      - destruct (unsigned_bvadd_split ug) as [[[c uw'] n]|] eqn:Hsplit;
          [| discriminate].
        apply andb_prop in Hb1 as [Hb2 Hexp].
        apply andb_prop in Hb2 as [Heqw Hcb].
        apply Z.ltb_lt in Hexp. apply Z.leb_le in Hcb.
        apply unsigned_bvadd_split_spec in Hsplit as (cbv & s & Hug & Huw' & Hc).
        pose proof (Term_eqb_spec uw' uw) as Hsp; rewrite Heqw in Hsp.
        inversion Hsp; subst.
        revert Hpc. cbn.
        destruct (inst s ι) as [a b]; cbn.
        unfold bv.unsigned in *. intros [Hpa Hpb].
        assert (Hlt1 : (bv.bin cbv + bv.bin a < bv.exp2 n)%N) by lia.
        assert (Hlt2 : (bv.bin cbv + bv.bin b < bv.exp2 n)%N) by lia.
        rewrite (bv.bin_add_small Hlt1) (bv.bin_add_small Hlt2). split; lia.
    Qed.

    Lemma formula_entails_fetch_bound_sound {Σ} (f : Formula Σ)
      (L2 K : Z) (ug : Term Σ ty.int) (ι : Valuation Σ) :
      formula_entails_fetch_bound f L2 K ug = true ->
      instprop f ι ->
      instprop (formula_relop bop.le (term_val ty.int 0%Z)
                  (term_binop bop.minus (term_val ty.int L2)
                     (term_binop bop.plus (term_val ty.int K) ug))) ι.
    Proof.
      funelim (formula_entails_fetch_bound f L2 K ug); intros Hb Hpc;
        try discriminate.
      apply andb_prop in Hb as [Hz Hsh].
      apply Z.eqb_eq in Hz; subst.
      destruct (int_bound_shape tw) as [[[L1 B] uw]|] eqn:Hshape;
        [| discriminate].
      apply int_bound_shape_spec in Hshape; subst tw.
      eapply fetch_bound_entails_sound; eauto.
    Qed.

    Lemma pathcondition_entails_fetch_bound_sound {Σ} (C : PathCondition Σ)
      (L2 K : Z) (ug : Term Σ ty.int) (ι : Valuation Σ) :
      pathcondition_entails_fetch_bound C L2 K ug = true ->
      instprop C ι ->
      instprop (formula_relop bop.le (term_val ty.int 0%Z)
                  (term_binop bop.minus (term_val ty.int L2)
                     (term_binop bop.plus (term_val ty.int K) ug))) ι.
    Proof.
      induction C as [|C IHC f]; cbn; intros Hb Hpc; try discriminate.
      destruct Hpc as [HC Hf].
      apply orb_true_iff in Hb as [Hb|Hb].
      - eapply formula_entails_fetch_bound_sound; eauto.
      - eapply IHC; eauto.
    Qed.

    (* `t1 <= t2` and `0 <= t2 - t1` are interchangeable at the RelVal level in
       BOTH RelVal cases, which is what lets the recognizer work on
       `peval_formula_le`'s normalised form while the spec is stated about the
       original relop. *)
    Lemma instprop_le_sub {Σ} (t1 t2 : Term Σ ty.int) (ι : Valuation Σ) :
      instprop (formula_relop bop.le t1 t2) ι <->
      instprop (formula_relop bop.le (term_val ty.int 0%Z)
                  (term_binop bop.minus t2 t1)) ι.
    Proof.
      cbn. destruct (inst t1 ι) as [x y], (inst t2 ι) as [u v]; cbn;
        split; intros; first [ lia | tauto | contradiction ].
    Qed.

    (* `empty`, not a weaker formula: `instpred` at world `w` is already
       relative to `wco w` (cf. pathconditions_contains_secLeakT_spec, which
       derives a formula from the path condition alone), so an entailment from
       `wco w` legitimately proves the `⊣⊢`. *)
    Lemma try_fetch_bound_spec {w : World} (t1 t2 : STerm ty.int w) (d : DList w) :
      try_fetch_bound t1 t2 = Some d ->
      instpred d ⊣⊢ instpred (formula_relop bop.le t1 t2).
    Proof.
      unfold try_fetch_bound.
      destruct (int_bound_shape (peval (term_minus t2 t1)))
        as [[[L2 K] ug]|] eqn:Hshape; [| discriminate].
      destruct (pathcondition_entails_fetch_bound (wco w) L2 K ug) eqn:Hpc;
        [| discriminate].
      intros [= <-].
      apply int_bound_shape_spec in Hshape.
      (* `MkBientails { fromBientails : forall ι, instprop (wco w) ι ->
         P ι <-> Q ι }` (Worlds.v:594) -- so TWO intros, then an iff. *)
      constructor. intros ι Hwco.
      destruct (@instpred_dlist_empty w) as [Hemp].
      split; intros _.
      - (* the relop holds at ι, from the path condition alone *)
        apply (proj2 (instpred_prop ι _)).
        apply (proj2 (instprop_le_sub t1 t2 ι)).
        pose proof (pathcondition_entails_fetch_bound_sound
                      (wco w) L2 K ug ι Hpc Hwco) as Hgoal.
        (* peval is sound PER-VALUATION, so the recognizer's view of `t2 - t1`
           and the real one agree at ι. *)
        pose proof (peval_sound (term_minus t2 t1) ι) as Hpev.
        rewrite Hshape in Hpev.
        cbn in Hgoal, Hpev |- *.
        rewrite <- Hpev. exact Hgoal.
      - apply (proj2 (Hemp ι Hwco)). exact I.
    Qed.

    Lemma simplify_relop_spec {w : World} {σ} (op : RelOp σ) (t1 t2 : STerm σ w) :
      instpred (simplify_relop op t1 t2) ⊣⊢ instpred (formula_relop op t1 t2).
    Proof.
      unfold simplify_relop.
      (* The eq and neq arms now dispatch through try_bvadd_cancel, so their
         scrutinee has to be destructed.  Do it by NAME: an Ltac
         `context[match _ with _ => _ end]` pattern does not reliably match a
         match scrutinee, and silently not firing leaves the goal untouched.
         Eight branches, one per RelOp constructor, so a miscount is a loud
         error rather than a silent fallthrough. *)
      destruct op;
      [ destruct (try_lin_cancel bop.eq (peval t1) (peval t2)) as [d|] eqn:Hc;
        [ apply try_lin_cancel_spec in Hc; rewrite Hc | ]
      | destruct (try_lin_cancel bop.neq (peval t1) (peval t2)) as [d|] eqn:Hc;
        [ apply try_lin_cancel_spec in Hc; rewrite Hc | ]
      (* le now dispatches through try_fetch_bound as well -- same shape as the
         eq/neq arms above.  RelOp has 8 constructors (eq neq le lt bvsle
         bvslt bvule bvult): le is 3rd, then three idtacs (lt bvsle bvslt),
         then the S3 arms bvule/bvult.  Hr is CLEARED in both branches:
         left in context, arw's `cbn in *` reduces `rng_decide bop.bvule ..`
         (its head matches on the now-constructor op) into canon_term on
         open terms and times out. *)
      | destruct (try_fetch_bound t1 t2) as [d|] eqn:Hf;
        [ apply try_fetch_bound_spec in Hf; rewrite Hf | ]
      | idtac | idtac | idtac
      | destruct (rng_decide bop.bvule (peval t1) (peval t2)) as [d|] eqn:Hr;
        [ apply rng_decide_spec in Hr; rewrite Hr; clear Hr | clear Hr ]
      | destruct (rng_decide bop.bvult (peval t1) (peval t2)) as [d|] eqn:Hr;
        [ apply rng_decide_spec in Hr; rewrite Hr; clear Hr | clear Hr ] ];
      arw;
      rewrite ?simplify_eq_spec ?simplify_relopb_spec ?formula_relop_term' ?peval_sound;
      arw; arw_slow;
      (* Never reached before the [try_bvadd_cancel]-dispatch was added to
         this proof: the eq/neq arms' [try_bvadd_cancel] = None branch (the
         cancellation rule not firing) is left needing
         [instpred_formula_relop op (peval t1) (peval t2) ⊣⊢
          instpred_formula_relop op t1 t2] -- plain peval soundness for the
         relop (this file never actually compiled end-to-end before, see
         `try_bvadd_cancel_spec` above, so this branch was never exercised).
         [peval_sound : peval t ≡ t] is stated PER-VALUATION (it takes an
         explicit ι), so [rewrite peval_sound] cannot reach into the still-
         unapplied [⊣⊢] wrapper -- confirmed in an isolated replica of
         [instpred_formula_relop]/its `Proper` instance over `peval`/
         `peval_sound` from `RiscvPmp.Base` (no Solver.v dependency,
         ~90ms): the identical rewrite fails with "no subterm matching
         [inst (peval ?) ?]" until [ι] is introduced first, then succeeds
         immediately. *)
      try (constructor; intros ι Hwco; cbn; unfold instpred_formula_relop;
           now rewrite !peval_sound).
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

    Fixpoint simplify_formula {w : World} (fml : Formula w) : DList w :=
      match fml with
      | formula_user p ts      => singleton (formula_user p (pevals ts))
      | formula_bool t         => simplify_bool (peval t)
      | formula_prop ζ P       => singleton fml
      | formula_relop op t1 t2 => simplify_relop op t1 t2
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
      (* bvadd cancellation FIRST: a base-relative pointer-compare loop exit
         emits `formula_propeq (bvadd c1 p) (bvadd c2 p)`, which with
         c1 <> c2 is impossible but which `simplify_propeq` (syntactic
         equality + structural decomposition) cannot refute -- leaving one
         live dead path per trip.  See `try_bvadd_cancel_propeq` above. *)
      | formula_propeq t1 t2   =>
          let t1 := peval t1 in
          let t2 := peval t2 in
          match try_lin_propeq t1 t2 with
          | Some d => d
          | None =>
          (* ...then `x + s = y` (also under a shared literal) with x the
             INNERMOST variable is solved for x, so unification eliminates x
             and not y: see `try_isolate_inner` above.  BEFORE the weakening
             below, whose output unify would act on in the same pass. *)
          match try_lin_isolate t1 t2 with
          | Some d => d
          | None =>
              (* ...and if the shared summand is the LITERAL rather than the
                 term, WEAKEN instead of deciding: see
                 `try_bvadd_cancel_val_propeq` above. *)
              match try_bvadd_cancel_val_propeq t1 t2 with
              | Some d => d
              (* PEVAL'D, like every other arm of this match and like all four
                 arms of simplify_relop.  This branch was the ONE that passed
                 raw terms, and the consequence is invisible in ordinary
                 verification -- the executor pevals as it BUILDS terms
                 (eval_exp / peval_binop'), so its formulas are already in
                 normal form and the missing peval is a no-op.  A formula
                 coming from a hand-written `asn.formula` is not: consume and
                 produce apply peval_chunk to CHUNKS but only `subst` to
                 FORMULAS, so a contract's terms reach the solver exactly as
                 authored.  `q + 0 = q.1 + 0` (every gen_seg_contract
                 placement, head = 0) then survives to the residual, and
                 try_unify_eq -- which fires only on a BARE term_var -- can
                 never eliminate the angelic. *)
              | None => simplify_propeq Term_eqb (fun {σ} t1 t2 => dlist_propeq t1 t2)
                          t1 t2
              end
          end
          end
      | formula_secLeak t      => simplify_secLeak (peval t)
      end.

    Lemma PathCondition_to_Formula_sound' [w : World] (P : PathCondition w) :
      instpred_formula (PathCondition_to_Formula P) ⊣⊢ instpred P.
    Proof. now apply PathCondition_to_Formula_sound. Qed.
    #[export] Hint Rewrite @PathCondition_to_Formula_sound' : uniflogic.

    Lemma PathCondition_to_DList_sound [w : World] (P : PathCondition w) :
      instpred (PathCondition_to_DList P) ⊣⊢ instpred P.
    Proof. reflexivity. Qed.
    #[export] Hint Rewrite @PathCondition_to_DList_sound : uniflogic.

    Fixpoint simplify_pathcondition {w : World} (C : PathCondition w) : DList w :=
      match C with
      | [ctx] => empty
      | C ▻ F => cat (simplify_pathcondition C) (simplify_formula (w := w) F)
      end.
      
    Lemma simplify_formula_spec {w : World} (C : PathCondition w) (F : Formula w) :
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
      (* [match goal] rather than naming the two terms: [induction F]'s
         auto-generated names for [formula_propeq]'s arguments are not
         [t]/[t0] here. *)
      - match goal with
        | |- instpred (match ?scrut with | Some _ => _ | None => _ end) ⊣⊢ _ =>
            destruct scrut as [d|] eqn:Hc
        end.
        (* Endgame copied verbatim from `simplify_relop_spec`'s peval bridge
           just above: the cancellation ran on the PEVAL'd terms, and
           [peval_sound] is stated PER-VALUATION, so it cannot be rewritten
           under a still-unapplied [⊣⊢] -- ι must be introduced first. *)
        + apply try_lin_propeq_spec in Hc; rewrite Hc.
          constructor; intros ι Hwco; cbn; unfold instpred_formula_propeq.
          now rewrite !peval_sound.
        + match goal with
          | |- instpred (match ?scrut with | Some _ => _ | None => _ end) ⊣⊢ _ =>
              destruct scrut as [d|] eqn:Hv
          end.
          * apply try_lin_isolate_spec in Hv; rewrite Hv.
            constructor; intros ι Hwco; cbn; unfold instpred_formula_propeq.
            now rewrite !peval_sound.
          * match goal with
            | |- instpred (match ?scrut with | Some _ => _ | None => _ end) ⊣⊢ _ =>
                destruct scrut as [d|] eqn:Hi
            end.
            -- apply try_bvadd_cancel_val_propeq_spec in Hi; rewrite Hi.
               constructor; intros ι Hwco; cbn; unfold instpred_formula_propeq.
               now rewrite !peval_sound.
            -- rewrite simplify_propeq_spec.
               (* the peval bridge, same three lines as the cancellation cases
                  above: peval_sound is stated PER-VALUATION, so it cannot be
                  rewritten under a still-unapplied `⊣⊢` -- ι must come first. *)
               constructor; intros ι Hwco; cbn; unfold instpred_formula_propeq.
               now rewrite !peval_sound.
      - rewrite simplify_secLeak_spec.
        constructor; intros ι Hwco; cbn; unfold instpred_formula_secLeak.
        now rewrite peval_sound.
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
      | formula_propeq t1 t2 =>
        match try_unify_eq t1 t2 with
        | Some r => Some r
        | None => try_unify_eq t2 t1
        end
      | _ => None
      end.

    Lemma instTermNotBIsNegB Σ t (b : bool) ι :
      inst (term_not t) ι = ty.valToRelVal (σ := ty.bool) b <->
      inst (Σ := Σ) t ι = ty.valToRelVal (σ := ty.bool) (negb b)
    .
    Proof.
      cbn. destruct (inst t ι) as [l r]; cbn.
      split; intro H; ty.rv_split; destruct l, r, b; cbn in *; congruence.
    Qed.

    Lemma try_unify_bool_spec {w : World} (t : Term w ty.bool) :
      option.wlp
        (fun '(existT w' ν) => repₚ (T := STerm ty.bool) (ty.valToRelVal (σ := ty.bool) true) t ⊣⊢ inst_triangular ν)
        (try_unify_bool t).
    Proof.
      induction t using Term_bool_ind; cbn; try constructor; auto.
      - rewrite inst_triangular_knowing.
        rewrite (knowing_trans (w2 := wsubst _ _ _)).
        rewrite knowing_id knowing_acc_subst_right.
        now crushPredEntails3.
      - induction t using Term_bool_ind; cbn; try constructor.
        rewrite inst_triangular_knowing (knowing_trans (ω23 := acc_refl)) knowing_id knowing_acc_subst_right.
        unfold assuming; crushPredEntails3; cbn.
        + rewrite <- (inst_sub_id ι).
          rewrite <- inst_lookup.
          rewrite lookup_sub_id.
          rewrite instTermNotBIsNegB in H0. by rewrite H0.
        + rewrite <- (inst_sub_id ι).
          rewrite <- inst_lookup.
          rewrite lookup_sub_id.
          by rewrite H0.          
    Qed.

    Lemma try_unify_eq_spec {w : World} {σ} (t1 t2 : Term w σ) :
      option.wlp
        (fun '(existT w' ν) => eqₚ t1 t2 ⊣⊢ inst_triangular ν)
        (try_unify_eq t1 t2).
    Proof.
      unfold try_unify_eq. destruct t1; cbn; try (constructor; auto; fail).
      destruct occurs_check_lt eqn:Heq; constructor; auto.
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
      - (* destruct rop; try constructor; cbn. *)
        destruct (try_unify_eq_spec t1 t2) as [[w' ν] HYP|]. constructor. auto.
        destruct (try_unify_eq_spec t2 t1) as [[w' ν] HYP|]; constructor.
        rewrite <-HYP.
        now unfold eqₚ.
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
      (* [formula_propeq] had NO clause here until 2026-09-04, so two SYNTACTICALLY
         IDENTICAL propeq formulas compared as [false].  That silently disabled
         every [formula_eqb]-based discharge for the one formula shape
         [simplify_relop]'s [eq] arm produces -- including [formula_simplifies]'
         own first line, and [formula_refuted_by] below. *)
      formula_eqb (@formula_propeq _ σ t11 t12) (@formula_propeq _ τ t21 t22) with eq_dec σ τ => {
        formula_eqb (@formula_propeq _ σ t11 t12) (@formula_propeq _ ?(σ) t21 t22) (left eq_refl) :=
          Term_eqb t11 t21 &&& Term_eqb t12 t22;
        formula_eqb (@formula_propeq _ σ t11 t12) (@formula_propeq _ τ t21 t22) (right _) := false
      };
      formula_eqb (@formula_user _ p ts1) (@formula_user _ q ts2) with 𝑷_eq_dec p q => {
        formula_eqb (@formula_user _ p ts1) (@formula_user _ ?(p) ts2) (left eq_refl) :=
          env.eqb_hom (@Term_eqb _) ts1 ts2;
        formula_eqb (@formula_user _ p ts1) (@formula_user _ q ts2) (right _) := false
      };
      formula_eqb formula_true formula_true := true;
      formula_eqb formula_false formula_false := true;
      formula_eqb (formula_or f1 f2) (formula_or f3 f4) :=
        formula_eqb f1 f3 &&& formula_eqb f2 f4;
      formula_eqb (formula_and f1 f2) (formula_and f3 f4) :=
        formula_eqb f1 f3 &&& formula_eqb f2 f4;
      formula_eqb (@formula_secLeak _ σ t1) (@formula_secLeak _ τ t2) with eq_dec σ τ => {
          formula_eqb (@formula_secLeak _ σ t1) (@formula_secLeak _ ?(σ) t2) (left eq_refl) := Term_eqb t1 t2;
          formula_eqb (@formula_secLeak _ σ t1) (@formula_secLeak _ τ t2) (right _) := false;
          };
      formula_eqb _ _ := false.

    Lemma formula_eqb_spec {Σ} (f1 f2 : Formula Σ) :
      BoolSpec (f1 = f2) True (formula_eqb f1 f2).
    Proof.
      revert f2. induction f1; intros f2;
        dependent elimination f2; simp formula_eqb;
        repeat
          match goal with
          | |- BoolSpec _ _ false   => constructor; auto
          | |- BoolSpec _ _ true   => try (constructor; congruence; fail)
          | |- context[eq_dec _ _ ] => destruct eq_dec; subst; cbn
          | |- context[Term_eqb ?t1 ?t2] =>
              destruct (Term_eqb_spec t1 t2); cbn;
              try (constructor; congruence; fail)
          | IH: forall f2 : Formula _, BoolSpec _ _ (formula_eqb ?f f2)
            |- context[formula_eqb ?f ?f2] =>
              specialize (IH f2); destruct IH
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

    (* [formula_simplifies hyp fact] for a [hyp] with no structure to recurse
       into: such a [hyp] is discharged exactly when it *is* [fact].  Spelled out
       separately because [formula_simplifies] recurses structurally on [hyp], so
       it cannot call itself on formulas it *builds* -- which is precisely what
       the [bop.eq] case below needs. *)
    Definition formula_discharge {Σ} (hyp fact : Formula Σ) : Formula Σ :=
      if formula_eqb hyp fact then formula_true else hyp.

    Fixpoint formula_simplifies {Σ} (hyp : Formula Σ) (fact : Formula Σ) : option (Formula Σ) :=
      if formula_eqb hyp fact then Some formula_true else
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
      | @formula_relop _ σ' op t1 t2 =>
          match op with
          | bop.eq =>
              (* An equality relop holds pointwise on both projections, which is
                 EXACTLY propositional equality of the two RelVals.  (Under the
                 old tagged RelVal it was false on any NonSyncVal, so it also
                 implied publicness of both sides and was split into
                 [propeq /\ secLeak t1 /\ secLeak t2]; that split now
                 over-approximates and, on an assumption, would assume
                 publicness that was never established.)  The single conjunct
                 is tested against [fact] for the reason recorded in the git
                 history of this case (2026-07-28: freshly built conjuncts must
                 be checked against the entry being walked). *)
              Some (formula_discharge (formula_propeq t1 t2) fact)
          | _ => None
          end

          (*     match fact with *)
          (*     | @formula_secLeak _ σ t => *)
          (*         fun t1' t2' => *)
          (*           match eq_dec σ σ' with *)
          (*           | left Heqσ => *)
          (*               let t' := eq_rect σ (Term _) t σ' Heqσ in *)
          (*               if Term_eqb t' t1' || Term_eqb t' t2' *)
          (*               then Some (formula_propeq t1' t2') *)
          (*               else None *)
          (*           | right _ => None *)
          (*           end *)
          (*     | _ => fun _ _ => None *)
          (*     end *)
          (* | _ => fun _ _ => None *)
          (* end t1 t2 *)
          (* let hyp' := peval_formula_relop_neg op t1 t2 in *)
          (* if formula_eqb hyp' fact then Some formula_false else None *)
      (* | @formula_secLeak _ σ t => match fact with *)
      (*                             | @formula_relop _ σ' rop t1 t2 => *)
      (*                                 match rop with *)
      (*                                 | bop.eq => fun t1' t2' => *)
      (*                                               match eq_dec σ σ' with *)
      (*                                               | left Heqσ => *)
      (*                                                   let t' := eq_rect σ (Term _) t σ' Heqσ in *)
      (*                                                   if Term_eqb t' t1' || Term_eqb t' t2' *)
      (*                                                   then Some (formula_propeq t1' t2') *)
      (*                                                   else None *)
      (*                                               | right _ => None *)
      (*                                               end *)
      (*                                 | _ => fun _ _ => None *)
      (*                                 end t1 t2 *)
      (*                             | _ => None *)
      (*                             end *)
      | _ => None
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

    #[local] Hint Rewrite @formula_relop_term' : uniflogic.

    Lemma bi_wand_iff_or {w} {P1 P2 Q1 Q2 : Pred w} : (P1 ∗-∗ Q1) ∗ (P2 ∗-∗ Q2) ⊢ P1 ∨ P2 ∗-∗ Q1 ∨ Q2.
    Proof.
      iIntros "[H1 H2]"; iSplit.
      - iIntros "[HP1|HP2]"; [iLeft|iRight]; [now iApply "H1"|now iApply "H2"].
      - iIntros "[HQ1|HQ2]"; [iLeft|iRight]; [now iApply "H1"|now iApply "H2"].
    Qed.

    (* #[local] Hint Rewrite instpred_peval_formula_relop_neg : uniflogic. *)

    (* The [fact]-independent content of [formula_simplifies]' [bop.eq] case: an
       equality relop is equivalent to value agreement plus publicness of both
       sides.  Stated pointwise so the four [formula_discharge] cases below can
       be closed by propositional reasoning against whichever conjuncts [fact]
       already supplies. *)
    Lemma inst_relop_eq_split {w : World} {σ} (t1 t2 : Term w σ) (ι : Valuation w) :
      instpred (formula_relop bop.eq t1 t2) ι <-> instpred (formula_propeq t1 t2) ι.
    Proof.
      cbn.
      unfold instpred_formula_relop, instpred_formula_propeq.
      destruct (inst t1 ι), (inst t2 ι); cbn.
      split; [intros [-> ->]; reflexivity|intro H; injection H as -> ->; split; reflexivity].
    Qed.

    Lemma instpred_relop_eq_split {w : World} {σ} (t1 t2 : Term w σ) :
      ⊢ instpred (formula_relop bop.eq t1 t2) ∗-∗ instpred (formula_propeq t1 t2).
    Proof. constructor. intros ι Hwco _. apply inst_relop_eq_split. Qed.

    (* [instpred_formula] sends [formula_and] to [∗] definitionally (Worlds.v);
       naming it lets the congruence step below rewrite without [cbn], which would
       also unfold the constructor-headed conjuncts and break [iApply]. *)
    Lemma instpred_formula_and' {w : World} (F1 F2 : Formula w) :
      instpred (formula_and F1 F2) ⊣⊢ instpred F1 ∗ instpred F2.
    Proof. reflexivity. Qed.

    Lemma formula_discharge_spec {w : World} (hyp fact : Formula w) :
      ⊢ instpred fact -∗ (instpred hyp ∗-∗ instpred (formula_discharge hyp fact)).
    Proof.
      unfold formula_discharge.
      destruct (formula_eqb_spec hyp fact); subst; cbn.
      - now iApply bi_wand_iff_true.
      - iIntros "_". now iApply bi.wand_iff_refl.
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
        try (now iApply bi_wand_iff_true).
      {
        eapply option.wlp_some.
        destruct rop; try now eapply option.wlp_none.
        eapply option.wlp_some.
        clear H.
        (* Split off the [fact]-independent equivalence, then discharge each of the
           three conjuncts against [fact] pointwise.  Uniform in the number of
           conjuncts, so no case analysis on the [formula_eqb] tests. *)
        iIntros "#Hfact".
        iApply bi.wand_iff_trans; iSplit.
        - iApply instpred_relop_eq_split.
        - iApply (formula_discharge_spec (formula_propeq t1 t2) fact with "Hfact").

            (* eapply option.wlp_some. *)
        (* destruct rop; try now eapply option.wlp_none. *)
        (* destruct fact; try now eapply option.wlp_none. *)
        (* destruct eq_dec; try now eapply option.wlp_none. subst. cbn. *)
        (* destruct (Term_eqb_spec t t1); *)
        (*   destruct (Term_eqb_spec t t2); cbn; *)
        (*   try now eapply option.wlp_none. *)
        (* all: eapply option.wlp_some. *)
        (* all: constructor. *)
        (* all: intros ι Hwco _; cbn. *)
        (* all: clear H. *)
        (* all: unfold instpred_formula_relop, instpred_formula_secLeak, instpred_formula_propeq. *)
        (* all: subst. *)
        (* all: intros Heq. all: split; intros H. *)
        (* all: try (cbn; destruct inst, inst; cbn in *; try contradiction; by subst). *)
        (* - reflexivity. *)
        (* - cbn in *. destruct inst; cbn in *; try contradiction. auto. *)
        (* - rewrite H. destruct inst, inst; cbn in *; try contradiction. auto. inversion H. *)
        (* - rewrite H. destruct inst, inst; cbn in *; try contradiction. auto. inversion H. *)
      }
        all: arw; cbn; try iIntros "#Hfact";
        try (iApply bi_wand_iff_or || iApply bi_wand_iff_sep); try iSplit;
        try now (iApply H || iApply H0 || iApply H1 || iApply bi.wand_iff_refl).
      (* - iIntros "#Hfact'". *)
      (*   iDestruct (repₚ_antisym_left with "Hfact Hfact'") as "%Heq". *)
      (*   discriminate. *)
      (* - iIntros ([]). *)
    Qed.

    (* ---------------------------------------------------------------------- *)
    (* REFUTING a formula against the path condition.                           *)
    (*                                                                          *)
    (* [formula_simplifies] can only ever DISCHARGE a hypothesis (turn it into  *)
    (* [formula_true]); it has no way to report "this contradicts [fact]", so   *)
    (* an infeasible branch whose infeasibility follows from a single [wco]     *)
    (* entry stayed live and was left to the user as a residual.  Measured on   *)
    (* CFGVer's countdown loop (2026-09-04): the precondition carries           *)
    (* [k-1 <> 0], the BNE tests exactly that, and the fall-through branch --   *)
    (* which ends in an [error] -- survived to the VC anyway.                   *)
    (*                                                                          *)
    (* The shapes that actually meet, dumped from that VC, are NOT the two      *)
    (* halves of one relop: [simplify_relop]'s [eq] arm decomposes an equality  *)
    (* into [formula_propeq] + publicness, and the operands come back in the    *)
    (* opposite order, so the pair is                                           *)
    (*     wco   :  formula_relop bop.neq (-1 +ᵇ k) 0                           *)
    (*     new   :  formula_propeq        0 (-1 +ᵇ k)                           *)
    (* Hence the [formula_propeq] case below tests BOTH argument orders against *)
    (* a [bop.neq] relop, and is the case that fires in practice.               *)
    (*                                                                          *)
    (* Both directions are covered, because the loop BODY and the loop EXIT     *)
    (* contract hit opposite ones: the body assumes [k-1 <> 0] and the branch   *)
    (* offers the propeq, the exit assumes [k-1 = 0] and the branch offers the  *)
    (* relop.  The neq-vs-propeq direction needs [formula_eqb] to compare two   *)
    (* [formula_propeq]s, which it could not do until the clause added above.   *)
    (* ---------------------------------------------------------------------- *)

    (* [op] and its negation cannot both hold: under the relational semantics   *)
    (* each says the same term evaluates to a DIFFERENT boolean RelVal.  This   *)
    (* covers the [NonSyncVal] case for free -- neither side holds there.       *)
    Lemma formula_relop_contra {w : World} {σ} (op : bop.RelOp σ) (t1 t2 : Term w σ) :
      ⊢ instpred (formula_relop_neg op t1 t2) -∗
        (instpred (formula_relop op t1 t2) ∗-∗ instpred (@formula_false w)).
    Proof.
      rewrite formula_relop_term instpred_formula_relop_neg.
      unfold repₚ. crushPredEntails2. crushPredEntails3.
      rewrite H1 in H2. cbn in H2. unfold ty.valToRelVal in H2. inversion H2.
    Qed.

    (* [propeq] equates the two RelVals outright, so a [bop.neq] relop on the   *)
    (* same pair is false whether the values are Sync or NonSync.               *)
    Lemma formula_propeq_neq_contra {w : World} {σ} (t1 t2 : Term w σ) :
      ⊢ instpred (formula_relop bop.neq t1 t2) -∗
        (instpred (formula_propeq t1 t2) ∗-∗ instpred (@formula_false w)).
    Proof.
      rewrite formula_relop_term. unfold repₚ. crushPredEntails2. crushPredEntails3.
      cbn in H1. rewrite H2 in H1. destruct (inst t2 ι); cbn in H1;
        repeat destruct Classes.eq_dec; cbn in H1; try discriminate; try congruence.
    Qed.

    Lemma formula_propeq_neq_contra' {w : World} {σ} (t1 t2 : Term w σ) :
      ⊢ instpred (formula_relop bop.neq t2 t1) -∗
        (instpred (formula_propeq t1 t2) ∗-∗ instpred (@formula_false w)).
    Proof.
      rewrite formula_relop_term. unfold repₚ. crushPredEntails2. crushPredEntails3.
      cbn in H1. rewrite H2 in H1. destruct (inst t2 ι); cbn in H1;
        repeat destruct Classes.eq_dec; cbn in H1; try discriminate; try congruence.
    Qed.

    (* Mirror direction: the [propeq] is the [wco] fact and the [bop.neq] relop
       is the new formula.  This is the shape CFGVer's loop-EXIT contract hits
       (precondition [k-1 = 0], BNE's taken branch assumes [k-1 <> 0]), where
       the body contract hits the pair above. *)
    Lemma formula_neq_propeq_contra {w : World} {σ} (t1 t2 : Term w σ) :
      ⊢ instpred (formula_propeq t1 t2) -∗
        (instpred (formula_relop bop.neq t1 t2) ∗-∗ instpred (@formula_false w)).
    Proof.
      rewrite formula_relop_term. unfold repₚ. crushPredEntails2. crushPredEntails3.
      cbn in H1. rewrite H1 in H2. destruct (inst t2 ι); cbn in H2;
        repeat destruct Classes.eq_dec; cbn in H2; try discriminate; try congruence.
    Qed.

    Lemma formula_neq_propeq_contra' {w : World} {σ} (t1 t2 : Term w σ) :
      ⊢ instpred (formula_propeq t2 t1) -∗
        (instpred (formula_relop bop.neq t1 t2) ∗-∗ instpred (@formula_false w)).
    Proof.
      rewrite formula_relop_term. unfold repₚ. crushPredEntails2. crushPredEntails3.
      cbn in H1. rewrite H1 in H2. destruct (inst t1 ι); cbn in H2;
        repeat destruct Classes.eq_dec; cbn in H2; try discriminate; try congruence.
    Qed.

    (* [formula_refuted_by F fact]: [fact] alone makes [F] impossible.  Every    *)
    (* [false] is "cannot decide" and falls through untouched -- returning       *)
    (* [true] here refutes a path, so it must be a genuine syntactic match.      *)
    Definition formula_refuted_by {Σ} (F fact : Formula Σ) : bool :=
      match F with
      | @formula_relop _ σ op t1 t2 =>
          if formula_eqb (formula_relop_neg op t1 t2) fact then true else
          match op with
          | bop.neq =>
              if formula_eqb (formula_propeq t1 t2) fact then true
              else formula_eqb (formula_propeq t2 t1) fact
          | _ => false
          end
      | @formula_propeq _ σ t1 t2 =>
          if formula_eqb (formula_relop bop.neq t1 t2) fact then true
          else formula_eqb (formula_relop bop.neq t2 t1) fact
      | _ => false
      end.

    (* [cbn [formula_refuted_by]] rather than a bare [cbn]: the latter unfolds   *)
    (* [formula_eqb] into a match on [fact] whenever its first argument is       *)
    (* constructor-headed, and then [destruct (formula_eqb_spec ..)] no longer   *)
    (* abstracts anything and the false branch cannot be discriminated.          *)
    Lemma formula_refuted_by_spec {w : World} (F fact : Formula w) :
      formula_refuted_by F fact = true ->
      ⊢ instpred fact -∗ (instpred F ∗-∗ instpred (@formula_false w)).
    Proof.
      destruct F; cbn [formula_refuted_by]; try discriminate.
      - destruct (formula_eqb_spec (formula_relop_neg rop t1 t2) fact).
        { intros _. subst. apply formula_relop_contra. }
        destruct rop; try discriminate.
        destruct (formula_eqb_spec (formula_propeq t1 t2) fact).
        { intros _. subst. apply formula_neq_propeq_contra. }
        destruct (formula_eqb_spec (formula_propeq t2 t1) fact); [|discriminate].
        intros _. subst. apply formula_neq_propeq_contra'.
      - destruct (formula_eqb_spec (formula_relop bop.neq t1 t2) fact).
        { intros _. subst. apply formula_propeq_neq_contra. }
        destruct (formula_eqb_spec (formula_relop bop.neq t2 t1) fact); [|discriminate].
        intros _. subst. apply formula_propeq_neq_contra'.
    Qed.

    Fixpoint assumption_formula {Σ} (C : PathCondition Σ) (F : Formula Σ) (k : PathCondition Σ) {struct C} : PathCondition Σ :=
      match C with
      | [ctx]  => k ▻ F
      | C ▻ F' => if formula_refuted_by F F'
                  then k ▻ formula_false
                  else match formula_simplifies F F' with
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
      (* The refuted case: [F] is impossible under [F'], so both sides of the
         bi-implication are [False] -- the left because [F] is, the right
         because [formula_false] is. *)
      destruct (formula_refuted_by F F') eqn:Href.
      { iPoseProof (formula_refuted_by_spec F F' Href with "HF'") as "HFF".
        cbn. iSplit.
        - iIntros "[Hk HF]". iDestruct ("HFF" with "HF") as "H". iFrame.
        - iIntros "[Hk []]". }
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
        | Some C1 =>
            let '(existT w1 (ν, C2)) :=
              unify_pathcondition (assumption_pathcondition (wco w0) C1 ctx.nil) in
            (* the split of each substituted public variable (ResimpSecLeak) *)
            Some (existT w1 (ν, ctx.cat C2 (resimp_secLeak_tri ν)))
        | None => None
        end
    .

    Lemma solver_generic_spec : SolverSpec solver_generic.
    Proof.
      unfold solver_generic. intros w C0.
      pose proof (simplify_pathcondition_spec C0) as Hequiv.
      destruct run as [C0'|]; cbn.
      - pose proof (unify_pathcondition_spec (assumption_pathcondition (wco w) C0' ctx.nil)) as Hunify.
        destruct (unify_pathcondition (assumption_pathcondition (wco w) C0' ctx.nil)) as (w1 & ν01 & C1).
        constructor.
        assert (Hcat : instpred (ctx.cat C1 (resimp_secLeak_tri ν01)) ⊣⊢ instpred C1).
        { rewrite instpred_cat. pose proof (@resimp_secLeak_tri_valid _ _ ν01) as HE.
          iSplit; [iIntros "[$ _]" | iIntros "$"; iApply HE]. }
        rewrite Hcat.
        rewrite <-Hunify.
        rewrite <-Hequiv.
        pose proof (assumption_pathcondition_spec (wco w) C0' ctx.nil) as Hassumption.
        iPoseProof wco_valid as "Hwco".
        iDestruct (Hassumption with "Hwco") as "Hassumption".
        rewrite bi.emp_sep.
        now iApply (bi.wand_iff_sym with "Hassumption").
      - constructor. now rewrite <-Hequiv.
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
