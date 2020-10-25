(******************************************************************************)
(* Copyright (c) 2019 Steven Keuchel                                          *)
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
     Program.Equality
     Program.Tactics
     ZArith.ZArith
     Strings.String
     Classes.Morphisms
     Classes.Morphisms_Prop
     Classes.Morphisms_Relations.

From Equations Require Import
     Equations.

From MicroSail Require Import
     Sep.Spec
     Sep.Logic
     Sep.Hoare
     Syntax
     Tactics
     Symbolic.Mutator
     Symbolic.Outcome.

Set Implicit Arguments.

Import CtxNotations.
Import EnvNotations.

Module Soundness
       (Import typekit : TypeKit)
       (Import termkit : TermKit typekit)
       (Import progkit : ProgramKit typekit termkit)
       (Import assertkit : AssertionKit typekit termkit progkit)
       (Import contractkit : SymbolicContractKit typekit termkit progkit assertkit).
  Module MUT := Mutators typekit termkit progkit assertkit contractkit.
  Import MUT.
  Module LOG := ProgramLogic typekit termkit progkit assertkit contractkit.
  Import LOG.

  Program Instance proper_sub_comp {Σ1 Σ2 Σ3} : Proper (eq ==> eq ==> eq) (@sub_comp Σ1 Σ2 Σ3).
  Admit Obligations.

  Section Soundness.

    Context `{HL: IHeaplet L} {SLL: ISepLogicLaws L}.

    Definition inst_heap {Σ} (ι : SymInstance Σ) (h : SymbolicHeap Σ) : L :=
      List.fold_right (fun c h => inst_chunk ι c ∧ h) ltrue h.

    Axiom sub_comp_id_left : forall {Σ0 Σ1} (ζ : Sub Σ0 Σ1), sub_comp (sub_id Σ0) ζ = ζ.
    Axiom sub_comp_id_right : forall {Σ0 Σ1} (ζ : Sub Σ0 Σ1), sub_comp ζ (sub_id Σ1) = ζ.
    Axiom subst_sub_id : forall `{Subst T} Σ (t : T Σ), subst (sub_id _) t = t.
    Axiom subst_sub_comp : forall `{Subst T} Σ0 Σ1 Σ2 (ζ1 : Sub Σ0 Σ1) (ζ2 : Sub Σ1 Σ2) t, subst (sub_comp ζ1 ζ2) t = subst ζ2 (subst ζ1 t).
    Axiom sub_comp_comm : forall {Σ0 Σ1 Σ2 Σ3} (ζ1 : Sub Σ0 Σ1) (ζ2 : Sub Σ1 Σ2) (ζ3 : Sub Σ2 Σ3), sub_comp (sub_comp ζ1 ζ2) ζ3 = sub_comp ζ1 (sub_comp ζ2 ζ3).

    (* Lemma  *)
    (* subst ζ'' (symbolic_eval_exp δ0 e) *)
    (* = symbolic_eval_exp (inst_localstore ζ'' δ0) *)

    Ltac sauto :=
      repeat
        match goal with
        | [ |- ?P ⊢ ?P ] =>
          apply entails_refl
        | [ |- ?P ∧ _ ⊢ ?P ∧ _ ] =>
          apply land_right; [ apply land_left1, entails_refl | idtac ]
        | [ |- _ ⊢ _ ∧ !!(?x = ?x) ] =>
          apply land_right; [ idtac | apply lprop_right; reflexivity ]
        | [ |- !! _ ⊢ _ ] =>
          apply lprop_right; intro
        | [ H: ?P |- _ ⊢ !!?P ] =>
          apply lprop_right; exact H
        end.

    Local Ltac sound_inster :=
      match goal with
      | [ IH: outcome_satisfy (dmut_exec ?s _ _) |-
          outcome_satisfy (dmut_exec ?s _ _) _ ] =>
        refine (outcome_satisfy_monotonic _ _ IH); clear IH
      | [ IH: context[_ -> outcome_satisfy (dmut_exec ?s _ _) _] |-
          outcome_satisfy (dmut_exec ?s _ _) _ ] =>
        microsail_insterU (fail) IH; refine (outcome_satisfy_monotonic _ _ IH); clear IH
      end.

    Lemma subst_lookup {Γ Σ Σ' x σ} (xInΓ : (x ∶ σ)%ctx ∈ Γ) (ζ : Sub Σ Σ') (δ : SymbolicLocalStore Γ Σ) :
      (subst ζ (δ ‼ x) = (subst ζ δ ‼ x))%lit.
    Proof.
      unfold subst at 2, sub_localstore.
      now rewrite env_lookup_map.
    Qed.

    Lemma subst_symboliceval {Γ τ Σ Σ'} (e : Exp Γ τ) (ζ : Sub Σ Σ') (δ : SymbolicLocalStore Γ Σ) :
      subst (T := fun Σ => Term Σ _) ζ (symbolic_eval_exp δ e) = symbolic_eval_exp (subst ζ δ) e.
    Proof.
      induction e; cbn; f_equal; auto.
      { now rewrite (subst_lookup xInΓ). }
      all: induction es; cbn in *; destruct_conjs; f_equal; auto.
    Qed.

    Lemma eval_exp_inst {Γ Σ τ} (ι : SymInstance Σ) (δΓΣ : SymbolicLocalStore Γ Σ) (e : Exp Γ τ) :
      eval e (inst_localstore ι δΓΣ) = inst_term ι (symbolic_eval_exp δΓΣ e).
    Proof.
      induction e; cbn; repeat f_equal; auto.
      { unfold inst_localstore; now rewrite env_lookup_map. }
      2: {
        induction es as [|eb n es IHes]; cbn in *.
        { reflexivity. }
        { destruct X as [-> Heqs].
          destruct (inst_term ι (symbolic_eval_exp δΓΣ eb));
            cbn; f_equal; auto.
        }
      }
      all: induction es; cbn in *; destruct_conjs; f_equal; auto.
    Qed.

    Local Opaque inst_heap.

    Opaque env_tail.

    Notation "'dmutres_pathcondition' res" := (symbolicstate_pathcondition (mutator_result_state (dmutres_result res))) (at level 10).
    Notation "'dmutres_heap' res" := (symbolicstate_heap (mutator_result_state (dmutres_result res))) (at level 10).
    Notation "'dmutres_localstore' res" := (symbolicstate_localstore (mutator_result_state (dmutres_result res))) (at level 10).

    Lemma dmut_exec_sound {Γ σ} (POST : Lit σ -> LocalStore Γ -> L) (s : Stm Γ σ) :
      forall Σ0 Σ1  (ι : SymInstance Σ1) (ζ1 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (δ1 : SymbolicLocalStore Γ Σ1) (h1 : SymbolicHeap Σ1),
        let δ       := inst_localstore ι δ1 in
        let pre__pc   := !! inst_pathcondition ι pc1 in
        let pre__heap := inst_heap ι h1 in
        outcome_satisfy
          (dmut_exec s ζ1 (MkSymbolicState pc1 δ1 h1))
          (fun '(@MkDynMutResult _ _ _ Σ2 ζ2 (MkMutResult t (MkSymbolicState pc2 δ2 h2) x)) =>
             forall (ι' : SymInstance Σ2),
               ι = env_map (fun _ => inst_term ι') ζ2 ->
               let post__pc   := !! inst_pathcondition ι' pc2 in
               let post__heap := inst_heap ι' h2 in
               post__pc ∧ post__heap ⊢ POST (inst_term ι' t) (inst_localstore ι' δ2)) ->
        δ ⊢ ⦃ pre__pc ∧ pre__heap ⦄ s ⦃ POST ⦄.
    Proof.
      intros ? ? ? ? ? ? ?; cbn.
      revert pc1 h1.
      induction s.

      - intros.
        apply rule_stm_lit.
        apply H.
        admit.

      - intros.
        apply rule_stm_exp.
        rewrite eval_exp_inst.
        apply H.
        admit.

      - cbn.
        unfold dmut_bind_right, dmut_sub, dmut_bind; cbn.
        repeat
          (repeat setoid_rewrite outcome_satisfy_bind;
           repeat setoid_rewrite outcome_satisfy_map; cbn).
        repeat
          (repeat setoid_rewrite sub_comp_id_left at 1;
           repeat setoid_rewrite sub_comp_id_right at 1;
           repeat setoid_rewrite subst_sub_id at 1;
           cbn).
        cbn.
        intros.

        eapply rule_stm_let.
        + apply IHs1.
          refine (outcome_satisfy_monotonic _ _ H); clear H. intros ?.
          unfold dmut_bind_right, dmut_sub, dmut_bind; cbn.
          rewrite ?outcome_satisfy_bind, ?outcome_satisfy_map; cbn.
          intros.
          admit.
        + admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - cbn.
        unfold dmut_bind_right, dmut_sub, dmut_bind; cbn.
        repeat
          (repeat setoid_rewrite outcome_satisfy_bind;
           repeat setoid_rewrite outcome_satisfy_map; cbn).
        repeat
          (repeat setoid_rewrite sub_comp_id_left at 1;
           repeat setoid_rewrite sub_comp_id_right at 1;
           repeat setoid_rewrite subst_sub_id at 1;
           cbn).
        cbn.
        cbv [mutator_assume_term mutator_assume_formula].
        intros ? ? [H1 H2].
        apply rule_stm_if.
        + clear IHs2 H2.
          revert H1.
          destruct (try_solve_formula (formula_bool (symbolic_eval_exp δ1 e))) eqn:Heqfml.
          * destruct (try_solve_formula_spec Term_eqb_spec (formula_bool (symbolic_eval_exp δ1 e)) Heqfml ι).
            -- unfold mutator_pure; cbn.
               repeat
                 (repeat setoid_rewrite outcome_satisfy_bind;
                  repeat setoid_rewrite outcome_satisfy_map; cbn).
               repeat
                 (repeat setoid_rewrite sub_comp_id_left at 1;
                  repeat setoid_rewrite sub_comp_id_right at 1;
                  repeat setoid_rewrite subst_sub_id at 1;
                  cbn).
               intros H1.
               eapply rule_consequence; [ idtac | idtac | apply IHs1 ]; clear IHs1.
               apply land_left1. apply entails_refl.
               intros; apply entails_refl.
               admit.
               (* refine (outcome_satisfy_monotonic _ _ H1); clear H1. *)
               (* intros [Σ2 ζ2 [t2 [pc2 δ2 h2] oblig2]]; cbn; intros. *)
               (* apply H. *)
               (* now rewrite sub_comp_id_left. *)
            -- intros H1; clear H1.
               cbn in n.
               unfold is_true in n.
               rewrite eval_exp_inst.
               destruct (inst_term ι (symbolic_eval_exp δ1 e)) eqn:?; try contradiction.
               clear n.
               clear Heqfml.
               admit.
          * unfold mutator_modify, mutator_state; cbn.
            repeat
              (repeat setoid_rewrite outcome_satisfy_bind;
               repeat setoid_rewrite outcome_satisfy_map; cbn).
            repeat
              (repeat setoid_rewrite sub_comp_id_left at 1;
               repeat setoid_rewrite sub_comp_id_right at 1;
               repeat setoid_rewrite subst_sub_id at 1;
               cbn).
            intro.
            admit.
            (* eapply rule_consequence; *)
            (*   [ idtac *)
            (*   | idtac *)
            (*   | apply IHs1; refine (outcome_satisfy_monotonic _ _ H1) *)
            (*   ]; clear H1 IHs1. *)
            (* admit. *)
            (* intros; apply entails_refl. *)
            (* cbn. *)
            (* intros [Σ2 ζ2 [t2 [pc2 δ2 h2] oblig2]]; cbn; intros. *)
    Admitted.

    Lemma dmut_contract_sound {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
      ValidContractDynMut c body ->
      ValidContract c body.
    Proof.
    Admitted.

  End Soundness.

End Soundness.
