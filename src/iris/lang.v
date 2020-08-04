From MicroSail Require Import
     Notation
     Syntax
     Context
     SmallStep.Step
     .

Require Import Coq.Program.Equality.

From iris.algebra Require Export gmap excl auth.
From iris.base_logic Require Export gen_heap.
From iris.program_logic Require Export language ectx_language ectxi_language.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import tactics.

Set Implicit Arguments.

Module ValsAndTerms
       (Import typekit : TypeKit)
       (Import termkit : TermKit typekit)
       (Import progkit : ProgramKit typekit termkit).

  Inductive Tm σ : Type :=
  | MkTm {Γ : Ctx (𝑿 * Ty)} (δ : LocalStore Γ) (s : Stm Γ σ) : Tm σ.

  Inductive Val σ : Type :=
    (* we only keep the store around for technical reasons, essentially to be able to prove of_to_val. *)
  | MkVal {Γ : Ctx (𝑿 * Ty)} (δ : LocalStore Γ) (v : Lit σ) : Val σ.

  Definition of_val {σ} (v : Val σ) : Tm σ :=
    match v with
      MkVal _ δ v => MkTm δ (stm_lit _ v)
    end.

  Definition to_val {σ} (t : Tm σ) : option (Val σ) :=
    (* easier way to do the dependent pattern match here? *)
    match t with
    | MkTm δ s => match s with
                   stm_lit τ l => Some (MkVal _ δ l)
                 | _ => None
                 end
    end.

  Lemma to_of_val {σ} (v : Val σ) : to_val (of_val v) = Some v.
  Proof.
    by induction v.
  Qed.

  Lemma of_to_val {σ} (e : Tm σ) v : to_val e = Some v → of_val v = e.
  Proof.
    induction e.
    induction s; try done.
    by intros [= <-].
  Qed.

  Module SS := SmallStep typekit termkit progkit.
  Import SS.

  Lemma val_head_stuck_step {σ} {Γ : Ctx (𝑿 * Ty)} γ1 γ2 μ1 μ2 (δ1 : LocalStore Γ) δ2 (s1 : Stm Γ σ) s2 :
    Step γ1 γ2 μ1 μ2 δ1 δ2 s1 s2 -> to_val (MkTm δ1 s1) = None.
    by induction 1.
  Qed.
End ValsAndTerms.

Module IrisInstance
       (Import typekit : TypeKit)
       (Import termkit : TermKit typekit)
       (Import progkit : ProgramKit typekit termkit).

  Import CtxNotations.
  Import EnvNotations.

  Definition σt : Ty := ty_bool.

  Module SS := SmallStep typekit termkit progkit.
  Import SS.

  Module VT := ValsAndTerms typekit termkit progkit.

  Definition Val := VT.Val σt.
  Definition Tm := VT.Tm σt.

  Definition observation := Empty_set.

  Definition State := prod RegStore Memory.

  Inductive prim_step : Tm -> State -> Tm -> State -> Prop :=
  | mk_prim_step {Γ  Γ : Ctx (𝑿 * Ty)} γ1 γ2 μ1 μ2 (δ1 : LocalStore Γ) (δ2 : LocalStore Γ) s1 s2 :
      VT.SS.Step γ1 γ2 μ1 μ2 δ1 δ2 s1 s2 ->
      prim_step (VT.MkTm δ1 s1) (γ1 , μ1) (VT.MkTm δ2 s2) (γ2 , μ2)
  .

  Lemma val_head_stuck e1 s1 e2 s2 : prim_step e1 s1 e2 s2 → VT.to_val e1 = None.
  Proof.
    induction 1.
    by eapply VT.val_head_stuck_step.
  Qed.

  Lemma lang_mixin : @LanguageMixin _ _ State Empty_set VT.of_val VT.to_val (fun e1 s1 ls e2 s2 ks => prim_step e1 s1 e2 s2).
  Proof.
    split; apply _ || eauto using VT.to_of_val, VT.of_to_val, val_head_stuck.
  Qed.

  Canonical Structure stateO := leibnizO State.
  Canonical Structure valO := leibnizO Val.
  Canonical Structure exprO := leibnizO Tm.

  Canonical Structure lang : language := Language lang_mixin.

  Instance intoVal_lit {Γ} : IntoVal (VT.MkTm (Γ := Γ) δ (stm_lit _ l)) (VT.MkVal _ δ l).
  intros; eapply VT.of_to_val; by cbn.
  Qed.

  Inductive SomeReg : Type :=
  | mkSomeReg {τ} : 𝑹𝑬𝑮 τ -> SomeReg
  .
  (* Lemma SomeReg_eq_dec (x y : SomeReg) : {x = y} + {~ x = y}. *)
  (* Admitted. *)
  Instance eqDec_SomeReg : EqDecision SomeReg.
  Admitted.

  Instance countable_SomeReg : Countable SomeReg.
  Admitted.

  Inductive SomeLit : Type :=
  | mkSomeLit {τ} : Lit τ -> SomeLit
  .
  Instance eqDec_SomeLit : EqDecision SomeLit.
  Admitted.

  Parameter RegStore_to_gmap : RegStore -> gmap SomeReg SomeLit.

  Definition regUR := authR (gmapUR SomeReg (exclR (leibnizO SomeLit))).

  Definition regs_to_gmap (regs : RegStore) : gmap SomeReg (exclR (leibnizO SomeLit)) :=
    fmap (fun v => Excl (v : leibnizO SomeLit)) (RegStore_to_gmap regs).

  Class sailG Σ := SailG { (* resources for the implementation side *)
                       sailG_invG : invG Σ; (* for fancy updates, invariants... *)

                       reg_inG : inG Σ regUR;
                       reg_gv_name : gname
                     }.

  Definition reg_pointsTo `{sailG Σ} {τ} (r : 𝑹𝑬𝑮 τ) (v : Lit τ) : iProp Σ :=
    own (i := reg_inG) reg_gv_name (◯ {[ mkSomeReg r := Excl (mkSomeLit v) ]}).

  Instance sailG_irisG `{sailG Σ} : irisG lang Σ := {
    iris_invG := sailG_invG;
    state_interp σ κs n := own (i := reg_inG) reg_gv_name (● regs_to_gmap σ.1);
    fork_post _ := True%I; (* no threads forked in sail, so this is fine *)
                                                   }.
  Global Opaque iris_invG.

  Context `{sailG Σ}.

    Definition test : iProp Σ := WP (VT.MkTm env_nil (stm_lit ty_bool true)) {{ v, True }}%I.

  Lemma testHolds : ⊢ test.
    iApply wp_value; try done.
  Qed.
End IrisInstance.
