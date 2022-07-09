(******************************************************************************)
(* Copyright (c) 2020 Dominique Devriese, Sander Huyghebaert, Steven Keuchel  *)
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
     Program.Tactics
     ZArith.ZArith
     Strings.String
     Classes.Morphisms
     Classes.RelationClasses
     Classes.Morphisms_Prop
     Classes.Morphisms_Relations.
Require Import Basics.

From Coq Require Lists.List.

From Equations Require Import
     Equations.

From Katamaran Require Import
     Shallow.Executor
     Specification
     Symbolic.Executor
     Symbolic.Solver
     Symbolic.Worlds
     Symbolic.Propositions
     Syntax.ContractDecl
     Program
     Tactics.

Set Implicit Arguments.

Import ctx.notations.
Import env.notations.

Module Soundness
  (Import B    : Base)
  (Import SIG  : ProgramLogicSignature B)
  (Import SPEC : Specification B SIG)
  (Import SOLV : SolverKit B SIG)
  (Import SHAL : ShallowExecOn B SIG SPEC)
  (Import SYMB : SymbolicExecOn B SIG SPEC SOLV).

  Import ModalNotations.
  Import SymProp.

  (* The definition of the logical relation in the paper suggest a usual
     recursion over the structure of types. We could define a closed universe of
     types that we can recurse over. However, that is inconvenient for multiple
     reasons.

     1. We would need a somewhat automated mapping from types to their code in
        the universe. Doing any kinds of tricks with typeclasses to implement
        this is very brittle. The mechanics behind canonical structures could in
        theory (not in actuality) implement this as well, but would suffer from
        the same brittleness.

     2. Every time we define a new type (say yet another record type that holds
        debug information) we would have to add it to the universe.

     Instead of defining a closed universe of types, we leave it open (and modular)
     and use a type class whose method calculates the relation. This still suffers
     a bit from 1., but avoids 2..
     *)
  Class Refine (AT : TYPE) (A : Type) : Type :=
    refine :
      forall (w : World) (ι : Valuation w),
        AT w -> A -> Prop.
  Global Arguments refine {_ _ _ w} ι _ _.
  (* We use the same script ℛ as in the paper. This encodes (ι,x,y) ∈ ℛ[_,_]
     from the paper as (ℛ ι x y), i.e. the types of the relation are implicit. *)
  Local Notation ℛ := refine.

  (* This instance can be used for any (first-class) symbolic data that can be
     instantiated with a valuation, i.e. symbolic terms, stores, heaps etc. *)
  #[export] Instance RefineInst {AT A} `{instA : Inst AT A} : Refine AT A :=
    fun w ι t v =>
      v = inst t ι.
  Global Arguments RefineInst {_ _ _} w ι t v /.

  (* Relatedness of symbolic and shallow propositions. The driving base case! *)
  #[export] Instance RefineProp : Refine 𝕊 Prop :=
    fun w ι SP P => (wsafe SP ι -> P)%type.

  #[export] Instance RefineBox {AT A} `{Refine AT A} : Refine (Box AT) A :=
    fun w0 ι0 a0 a =>
      forall (w1 : World) (ω01 : w0 ⊒ w1) (ι1 : Valuation w1),
        ι0 = inst (sub_acc ω01) ι1 ->
        instpc (wco w1) ι1 ->
        ℛ ι1 (a0 w1 ω01) a.

  #[export] Instance RefineImpl {AT A BT B} `{Refine AT A, Refine BT B} :
    Refine (Impl AT BT) (A -> B) :=
    fun w ι fs fc =>
      forall (ta : AT w) (a : A),
        ℛ ι ta a ->
        ℛ ι (fs ta) (fc a).

  #[export] Instance RefineForall {𝑲} {AT : forall K : 𝑲, TYPE} {A : forall K : 𝑲, Type}
    {refA : forall K, Refine (AT K) (A K)} :
    Refine (@Forall 𝑲 AT) (forall K : 𝑲, A K) :=
    fun w ι fs fc =>
      forall K : 𝑲,
        ℛ ι (fs K) (fc K).

  (* Try to help type class resolution. :( )*)
  #[export] Instance RefineHeapSpecM {Γ1 Γ2 AT A} `{Refine AT A} :
    Refine (SHeapSpecM Γ1 Γ2 AT) (CHeapSpecM Γ1 Γ2 A) := RefineImpl.
  #[export] Instance RefineTermVal {σ} : Refine (STerm σ) (Val σ) :=
    RefineInst (AT := STerm σ).
  #[export] Instance RefineStore {Δ : PCtx} :
    Refine (SStore Δ) (CStore Δ) := RefineInst.
  #[export] Instance RefineEnv {Δ : Ctx Ty} :
    Refine (fun w => Env (Term w) Δ) (Env Val Δ) | 1 :=
    RefineInst.
  #[export] Instance RefineNamedEnv {N : Set} {Δ : NCtx N Ty} :
    Refine (fun w => NamedEnv (Term w) Δ) (NamedEnv Val Δ) | 1 :=
    RefineInst.

  Local Hint Unfold refine RefineBox RefineProp RefineInst RefineTermVal
    RefineStore : core.

  Import ModalNotations.
  Open Scope modal.

  Lemma refine_four {AT A} `{Refine AT A} {w0 : World} (ι0 : Valuation w0) :
    forall (a0 : Box AT w0) (a : A),
      ℛ ι0 a0 a ->
      forall w1 (ω01 : w0 ⊒ w1) (ι1 : Valuation w1),
        ι0 = inst (sub_acc ω01) ι1 ->
        ℛ ι1 (four a0 ω01) a.
  Proof.
    unfold ℛ, RefineBox.
    intros * H0 w1 ω01 ι1 ? w2 ω12 ι2 ? Hpc2.
    apply H0; auto.
    rewrite sub_acc_trans, inst_subst.
    now subst.
  Qed.
  Local Hint Resolve refine_four : core.

  Lemma refine_lift {AT A} `{InstLift AT A} {w0 : World} (ι0 : Valuation w0) (a : A) :
    ℛ ι0 (lift (T := AT) a) a.
  Proof. hnf. now rewrite inst_lift. Qed.

  Ltac wsimpl :=
    repeat
      (try change (wctx (wsnoc ?w ?b)) with (wctx w ▻ b);
       try change (wco (wsnoc ?w ?b)) with (subst (wco w) (sub_wk1 (b:=b)));
       try change (sub_acc (@acc_refl ?w)) with (sub_id (wctx w));
       try change (wctx (wformula ?w ?fml)) with (wctx w);
       try change (sub_acc (@acc_formula_right ?w ?fml)) with (sub_id (wctx w));
       try change (sub_acc (@acc_formulas_right ?w ?fmls)) with (sub_id (wctx w));
       try change (wco (wformula ?w ?fml)) with (cons fml (wco w));
       try change (wco (@wsubst ?w _ _ ?xIn ?t)) with (subst (wco w) (sub_single xIn t));
       try change (wctx (@wsubst ?w _ _ ?xIn ?t)) with (ctx.remove xIn);
       try change (sub_acc (@acc_subst_right ?w _ _ ?xIn ?t)) with (sub_single xIn t);
       rewrite <- ?sub_comp_wk1_tail, ?inst_subst, ?subst_sub_id,
         ?inst_sub_id, ?inst_sub_wk1, ?inst_sub_snoc,
         ?inst_lift, ?inst_sub_single_shift, ?inst_pathcondition_cons,
         ?sub_acc_trans, ?sub_acc_triangular, ?inst_triangular_right_inverse).

  Lemma refine_symprop_angelic_binary
    {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι) :
    ℛ ι (@angelic_binary w) (@or).
  Proof.
    intros PS1 PC1 HP1 PS2 PC2 HP2.
    intros [H1|H2]; [left|right]; auto.
  Qed.

  Lemma refine_symprop_demonic_binary
    {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι) :
    ℛ ι (@demonic_binary w) (@and).
  Proof.
    intros PS1 PC1 HP1 PS2 PC2 HP2.
    intros [H1 H2]; split; auto.
  Qed.

  Module PureSpecM.

    Lemma refine_pure {AT A} `{Refine AT A} {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι) :
      ℛ ι (@SPureSpecM.pure AT w) CPureSpecM.pure.
    Proof.
      intros t v tv.
      intros POST__s POST__c HPOST.
      unfold SPureSpecM.pure, CPureSpecM.pure.
      apply HPOST; auto. cbn.
      now rewrite inst_sub_id.
    Qed.

    Lemma refine_bind {AT A BT B} `{Refine AT A, Refine BT B}
          {w0 : World} (ι0 : Valuation w0)  :
      ℛ ι0 (@SPureSpecM.bind AT BT w0) (@CPureSpecM.bind A B).
    Proof.
      intros ms mc Hm fs fc Hf.
      intros POST__s POST__c HPOST.
      unfold SPureSpecM.bind, CPureSpecM.bind.
      apply Hm; eauto.
      intros w1 ω01 ι1 -> Hpc1.
      intros a1 a Ha.
      apply Hf; auto.
      eapply refine_four; eauto.
    Qed.

    Lemma refine_error {AT A M} `{Refine AT A, Subst M, OccursCheck M}
      {w0 : World} (ι0 : Valuation w0) (Hpc0 : instpc (wco w0) ι0) {msg : M w0} :
      ℛ ι0 (SPureSpecM.error (A := AT) msg) CPureSpecM.error.
    Proof. intros POST__s POST__c HPOST. auto. Qed.

    Lemma refine_angelic (x : option LVar) (σ : Ty) :
      forall {w0 : World} (ι0 : Valuation w0) (Hpc0 : instpc (wco w0) ι0),
        ℛ ι0 (@SPureSpecM.angelic x σ w0) (@CPureSpecM.angelic σ).
    Proof.
      intros w0 ι0 Hpc0.
      intros POST__s POST__c HPOST.
      intros [v Hwp]. exists v. revert Hwp.
      apply HPOST. cbn. now rewrite inst_sub_wk1.
      cbn. now rewrite inst_subst, inst_sub_wk1.
      reflexivity.
    Qed.

    Lemma refine_angelic_ctx {N : Set} {n : N -> LVar} {Δ : NCtx N Ty} :
      forall {w0 : World} (ι0 : Valuation w0) (Hpc0 : instpc (wco w0) ι0),
        ℛ ι0 (@SPureSpecM.angelic_ctx N n w0 Δ) (@CPureSpecM.angelic_ctx N Δ).
    Proof.
      induction Δ; cbn [SPureSpecM.angelic_ctx CPureSpecM.angelic_ctx].
      - intros w0 ι0 Hpc0.
        now apply refine_pure.
      - destruct b as [x σ].
        intros w0 ι0 Hpc0.
        apply refine_bind; [|intros w1 ω01 ι1 -> Hpc1].
        apply refine_angelic; auto.
        intros t v ->.
        apply refine_bind; [|intros w2 ω12 ι2 -> Hpc2].
        apply IHΔ; auto.
        intros ts vs ->.
        apply refine_pure; auto.
        rewrite <- inst_persist.
        reflexivity.
    Qed.

    Lemma refine_demonic (x : option LVar) (σ : Ty) :
      forall {w0 : World} (ι0 : Valuation w0) (Hpc0 : instpc (wco w0) ι0),
        ℛ ι0 (@SPureSpecM.demonic x σ w0) (@CPureSpecM.demonic σ).
    Proof.
      intros w0 ι0 Hpc0 POST__s POST__c HPOST; cbn.
        (* x : option LVar *)
        (* σ : Ty *)
        (* w0 : World *)
        (* ι0 : Valuation w0 *)
        (* Hpc0 : instpc (wco w0) ι0 *)
        (* POST__s : □(WTerm σ -> fun Σ : World => 𝕊 Σ) w0 *)
        (* POST__c : Val σ -> Prop *)
        (* HPOST : ℛ ι0 POST__s POST__c *)
        (* ============================ *)
        (* ℛ ι0 (SPureSpecM.demonic x σ POST__s) (CPureSpecM.demonic σ POST__c) *)
      intros Hwp v. cbn in Hwp. specialize (Hwp v). remember (fresh w0 x) as ℓ.
        (* x : option LVar *)
        (* σ : Ty *)
        (* w0 : World *)
        (* ι0 : Valuation w0 *)
        (* Hpc0 : instpc (wco w0) ι0 *)
        (* POST__s : □(WTerm σ -> fun Σ : World => 𝕊 Σ) w0 *)
        (* POST__c : Val σ -> Prop *)
        (* HPOST : ℛ ι0 POST__s POST__c *)
        (* v : Val σ *)
        (* ℓ : LVar *)
        (* Heqℓ : ℓ = fresh w0 x *)
        (* Hwp : wsafe (POST__s (wsnoc w0 (ℓ∷σ)) acc_snoc_right (term_var ℓ)) ι0.[ℓ∷σ ↦ v] *)
        (* ============================ *)
        (* POST__c v *)
      revert Hwp. apply HPOST;
        [ (* Boilerplate #1 *) cbn; now rewrite inst_sub_wk1
        | (* Boilerplate #2 *) cbn; now rewrite inst_subst, inst_sub_wk1
        |].
        (* x : option LVar *)
        (* σ : Ty *)
        (* w0 : World *)
        (* ι0 : Valuation w0 *)
        (* Hpc0 : instpc (wco w0) ι0 *)
        (* POST__s : □(WTerm σ -> fun Σ : World => 𝕊 Σ) w0 *)
        (* POST__c : Val σ -> Prop *)
        (* HPOST : ℛ ι0 POST__s POST__c *)
        (* v : Val σ *)
        (* ℓ : LVar *)
        (* Heqℓ : ℓ = fresh w0 x *)
        (* ============================ *)
        (* ℛ ι0.[ℓ∷σ ↦ v] (term_var ℓ) v *)
      reflexivity.
    Qed.

    Lemma refine_demonic_ctx {N : Set} {n : N -> LVar} {Δ : NCtx N Ty} :
      forall {w0 : World} (ι0 : Valuation w0) (Hpc0 : instpc (wco w0) ι0),
        ℛ ι0 (@SPureSpecM.demonic_ctx N n w0 Δ) (@CPureSpecM.demonic_ctx N Δ).
    Proof.
      induction Δ.
      - intros w0 ι0 Hpc0.
        intros POST__s POST__c HPOST.
        unfold SPureSpecM.demonic_ctx, CPureSpecM.demonic_ctx, T.
        apply HPOST; wsimpl; try reflexivity; auto.
      - destruct b as [x σ].
        intros w0 ι0 Hpc0 POST__s POST__c HPOST; cbn.
        apply refine_demonic; auto.
        intros w1 ω01 ι1 -> Hpc1.
        intros t v tv.
        apply IHΔ; auto.
        intros w2 ω12 ι2 -> Hpc2.
        intros ts vs tvs.
        apply HPOST; cbn; wsimpl; auto.
        rewrite tv, tvs. hnf.
        rewrite <- inst_persist.
        reflexivity.
    Qed.

    Lemma refine_assume_formulas {w0 : World} (ι0 : Valuation w0) (Hpc0 : instpc (wco w0) ι0)
      (fmls0 : List Formula w0) (P : Prop) (Heq : instpc fmls0 ι0 <-> P) :
      ℛ ι0 (@SPureSpecM.assume_formulas w0 fmls0) (@CPureSpecM.assume_formula P).
    Proof.
      intros POST__s POST__c HPOST. unfold SPureSpecM.assume_formulas.
      intros Hwp Hfmls0. apply Heq in Hfmls0.
      destruct (solver_spec fmls0) as [[w1 [ζ fmls1]] Hsolver|Hsolver].
      - specialize (Hsolver ι0 Hpc0).
        destruct Hsolver as [Hν Hsolver]. inster Hν by auto.
        specialize (Hsolver (inst (sub_triangular_inv ζ) ι0)).
        rewrite inst_triangular_right_inverse in Hsolver; auto.
        inster Hsolver by now try apply entails_triangular_inv.
        destruct Hsolver as [Hsolver _]. inster Hsolver by auto.
        rewrite safe_assume_triangular, safe_assume_formulas_without_solver in Hwp.
        specialize (Hwp Hν Hsolver). revert Hwp.
        unfold four. apply HPOST; cbn; wsimpl; auto.
        rewrite inst_pathcondition_app. split; auto.
        now apply entails_triangular_inv.
      - intuition.
    Qed.

    Lemma refine_assume_formula {w0 : World} (ι0 : Valuation w0) (Hpc0 : instpc (wco w0) ι0)
      (fml : Formula w0) (P : Prop) (Heq : inst fml ι0 <-> P) :
      ℛ ι0 (@SPureSpecM.assume_formula w0 fml) (@CPureSpecM.assume_formula P).
    Proof. unfold SPureSpecM.assume_formula. apply refine_assume_formulas; cbn; intuition. Qed.

    Lemma refine_assert_formulas {w0 : World} (ι0 : Valuation w0) (Hpc0 : instpc (wco w0) ι0)
      (msg : AMessage w0) (fmls0 : List Formula w0) (P : Prop) (Heq : instpc fmls0 ι0 <-> P) :
      ℛ ι0 (@SPureSpecM.assert_formulas w0 msg fmls0) (@CPureSpecM.assert_formula P).
    Proof.
      unfold SPureSpecM.assert_formulas, CPureSpecM.assert_formula.
      intros POST__s POST__c HPOST Hwp.
      destruct (solver_spec fmls0) as [[w1 [ζ fmls1]] Hsolver|Hsolver].
      - specialize (Hsolver ι0 Hpc0). destruct Hsolver as [_ Hsolver].
        rewrite safe_assert_triangular in Hwp. destruct Hwp as [Hν Hwp].
        rewrite safe_assert_formulas_without_solver in Hwp.
        destruct Hwp as [Hfmls Hwp].
        split.
        + apply Hsolver in Hfmls; rewrite ?inst_triangular_right_inverse; auto.
          now apply Heq.
          now apply entails_triangular_inv.
        + revert Hwp. unfold four.
          apply HPOST; cbn; wsimpl; eauto.
          rewrite inst_pathcondition_app. split; auto.
          now apply entails_triangular_inv.
      - intuition.
    Qed.

    Lemma refine_assert_formula {w0 : World} (ι0 : Valuation w0) (Hpc0 : instpc (wco w0) ι0)
      (msg : AMessage w0) (fml : Formula w0) (P : Prop) (Heq : inst fml ι0 <-> P) :
      ℛ ι0 (@SPureSpecM.assert_formula w0 msg fml) (@CPureSpecM.assert_formula P).
    Proof. unfold SPureSpecM.assert_formula. apply refine_assert_formulas; cbn; intuition. Qed.

    Lemma refine_assert_eq_nenv {N} {Δ : NCtx N Ty} {w0 : World} {ι0 : Valuation w0} (Hpc : instpc (wco w0) ι0)
      (msg : AMessage w0) :
      ℛ ι0 (@SPureSpecM.assert_eq_nenv N Δ w0 msg) CPureSpecM.assert_eq_nenv.
    Proof.
      intros E1 ? -> E2 ? ->.
      induction E1; [ destruct (env.nilView E2) | destruct (env.snocView E2) as [E2] ]; cbn.
      - now apply refine_pure.
      - apply refine_bind. apply IHE1.
        intros w1 ω01 ι1 -> Hpc1 _ _ _.
        apply refine_assert_formula; auto. cbn.
        now do 2 rewrite (inst_persist (AT := STerm (type b))).
    Qed.

    Lemma refine_assert_eq_env {Δ} {w0 : World} {ι0 : Valuation w0}
      (Hpc : instpc (wco w0) ι0) (msg : AMessage w0) :
      ℛ ι0 (@SPureSpecM.assert_eq_env Δ w0 msg) CPureSpecM.assert_eq_env.
    Proof.
      intros E1 ? -> E2 ? ->.
      induction E1; [ destruct (env.nilView E2) | destruct (env.snocView E2) as [E2] ]; cbn.
      - now apply refine_pure.
      - apply refine_bind. apply IHE1.
        intros w1 ω01 ι1 -> Hpc1 _ _ _.
        apply refine_assert_formula; auto. cbn.
        now do 2 rewrite (inst_persist (AT := STerm b)).
    Qed.

    Lemma refine_assert_eq_chunk {w0 : World} {ι0 : Valuation w0} (Hpc : instpc (wco w0) ι0)
      (msg : AMessage w0) :
      ℛ ι0 (@SPureSpecM.assert_eq_chunk w0 msg) CPureSpecM.assert_eq_chunk.
    Proof.
      intros c ? -> c' ? ->. revert c'.
      induction c; intros [] w1 ω01 ι1 -> Hpc1; cbn; auto;
        try (now apply refine_error).
      - destruct eq_dec.
        + destruct e; cbn.
          apply refine_assert_eq_env; auto; cbn;
            now rewrite <- inst_persist.
        + now apply refine_error.
      - destruct eq_dec_het.
        + dependent elimination e; cbn.
          apply refine_assert_formula; auto. cbn.
          now do 2 rewrite <- inst_persist.
        + now apply refine_error.
      - apply refine_bind. apply IHc1; auto.
        intros w2 ω12 ι2 -> Hpc2 _ _ _.
        apply IHc2; auto.
        rewrite sub_acc_trans.
        now rewrite inst_subst, <- inst_persist.
      - apply refine_bind. apply IHc1; auto.
        intros w2 ω12 ι2 -> Hpc2 _ _ _.
        apply IHc2; auto.
        rewrite sub_acc_trans.
        now rewrite inst_subst, <- inst_persist.
    Qed.

    Lemma refine_angelic_list {M} `{Subst M, OccursCheck M} {AT A} `{Inst AT A}
      {w0 : World} (ι0 : Valuation w0) (Hpc0 : instpc (wco w0) ι0) (msg : M w0) :
      ℛ ι0 (SPureSpecM.angelic_list (A := AT) msg) (CPureSpecM.angelic_list (A := A)).
    Proof.
      intros xs ? ->.
      induction xs; cbn - [inst];
        intros POST__s POST__c HPOST.
      - intros [].
      - cbn.
        apply refine_symprop_angelic_binary; auto.
        apply HPOST; wsimpl; auto.
    Qed.

    Lemma refine_demonic_list {AT A} `{Inst AT A}
      {w0 : World} (ι0 : Valuation w0) (Hpc0 : instpc (wco w0) ι0) :
      ℛ ι0 (@SPureSpecM.demonic_list AT w0) (@CPureSpecM.demonic_list A).
    Proof.
      intros xs ? ->.
      induction xs; cbn - [inst];
        intros POST__s POST__c HPOST.
      - constructor.
      - cbn.
        apply refine_symprop_demonic_binary; auto.
        apply HPOST; wsimpl; auto.
    Qed.

    Lemma refine_angelic_finite {F} `{finite.Finite F}
      {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι) msg :
      ℛ (AT := SPureSpecM (Const F)) ι (@SPureSpecM.angelic_finite F _ _ w msg) (@CPureSpecM.angelic_finite F _ _).
    Proof.
      unfold SPureSpecM.angelic_finite, CPureSpecM.angelic_finite.
      apply refine_angelic_list; auto.
      hnf. unfold inst, inst_const, inst_list.
      now rewrite List.map_id.
    Qed.

    Lemma refine_demonic_finite {F} `{finite.Finite F}
      {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι) :
      ℛ (AT := SPureSpecM (Const F)) ι (@SPureSpecM.demonic_finite F _ _ w) (@CPureSpecM.demonic_finite F _ _).
    Proof.
      unfold SPureSpecM.demonic_finite, CPureSpecM.demonic_finite.
      intros POST__s POST__c HPOST.
      apply refine_demonic_list; eauto.
      hnf. unfold inst, inst_const, inst_list.
      now rewrite List.map_id.
    Qed.

  End PureSpecM.

  Section Basics.

    Lemma refine_lift_purem {Γ AT A} `{Refine AT A}
      {w0 : World} (ι0 : Valuation w0) (Hpc0 : instpc (wco w0) ι0) :
      ℛ ι0 (@SHeapSpecM.lift_purem Γ AT w0) (@CHeapSpecM.lift_purem Γ A).
    Proof.
      intros ms mc Hm.
      intros POST__s POST__c HPOST.
      intros δs δc Hδ hs hc Hh.
      unfold SHeapSpecM.lift_purem, CHeapSpecM.lift_purem.
      apply Hm.
      intros w1 ω01 ι1 -> Hpc1.
      intros a1 a Ha.
      apply HPOST; auto.
      hnf. rewrite inst_persist. apply Hδ.
      hnf. rewrite inst_persist. apply Hh.
    Qed.
    Hint Resolve refine_lift_purem : core.

    Lemma refine_block {AT A} `{Refine AT A} {Γ1 Γ2} {w : World} (ι : Valuation w) :
      ℛ ι (@SHeapSpecM.block Γ1 Γ2 AT w) CHeapSpecM.block.
    Proof. unfold ℛ, RefineHeapSpecM, RefineImpl. auto. Qed.

    Lemma refine_error {AT A D} `{Refine AT A} {Γ1 Γ2} {w : World} {ι: Valuation w} (func msg : string) (d : D) (cm : CHeapSpecM Γ1 Γ2 A) :
      ℛ ι (@SHeapSpecM.error Γ1 Γ2 AT D func msg d w) cm.
    Proof.
      intros POST__s POST__c HPOST.
      intros δs δc Hδ hs hc Hh [].
    Qed.
    Hint Resolve refine_error : core.

    Lemma refine_pure {AT A} `{Refine AT A} {Γ} {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι) :
      ℛ ι (@SHeapSpecM.pure Γ AT w) CHeapSpecM.pure.
    Proof.
      intros t v tv.
      intros POST__s POST__c HPOST.
      unfold SHeapSpecM.pure, CHeapSpecM.pure.
      apply HPOST; auto. cbn.
      now rewrite inst_sub_id.
    Qed.

    Lemma refine_bind {AT A BT B} `{Refine AT A, Refine BT B}
      {Γ1 Γ2 Γ3} {w0 : World} (ι0 : Valuation w0) (* (Hpc0 : instpc (wco w0) ι0) *) :
      ℛ ι0 (@SHeapSpecM.bind Γ1 Γ2 Γ3 AT BT w0) (@CHeapSpecM.bind Γ1 Γ2 Γ3 A B).
    Proof.
      intros ms mc Hm fs fc Hf.
      intros POST__s POST__c HPOST.
      intros δs δc -> hs hc ->.
      unfold SHeapSpecM.bind, CHeapSpecM.bind.
      apply Hm; eauto.
      intros w1 ω01 ι1 -> Hpc1.
      intros a1 a Ha.
      apply Hf; auto.
      eapply refine_four; eauto.
    Qed.

    Lemma refine_angelic (x : option LVar) (σ : Ty)
      {Γ : PCtx} {w0 : World} (ι0 : Valuation w0)
      (Hpc0 : instpc (wco w0) ι0) :
      ℛ ι0 (@SHeapSpecM.angelic Γ x σ w0) (@CHeapSpecM.angelic Γ σ).
    Proof.
      intros POST__s POST__c HPOST.
      intros δs δc -> hs hc ->.
      intros [v Hwp]; exists v; revert Hwp.
      apply HPOST. cbn. now rewrite inst_sub_wk1.
      cbn. now rewrite inst_subst, inst_sub_wk1.
      reflexivity.
      hnf. cbn. now rewrite inst_subst, ?inst_sub_wk1.
      hnf. cbn. now rewrite inst_subst, ?inst_sub_wk1.
    Qed.
    Hint Resolve refine_angelic : core.

    Lemma refine_demonic (x : option LVar) (σ : Ty)
      {Γ : PCtx} {w0 : World} (ι0 : Valuation w0)
      (Hpc0 : instpc (wco w0) ι0) :
      ℛ ι0 (@SHeapSpecM.demonic Γ x σ w0) (@CHeapSpecM.demonic Γ σ).
    Proof.
      intros POST__s POST__c HPOST.
      intros δs δc -> hs hc ->.
      intros Hwp v. cbn in Hwp. specialize (Hwp v). revert Hwp.
      apply HPOST. cbn. now rewrite inst_sub_wk1.
      cbn. now rewrite inst_subst, inst_sub_wk1.
      reflexivity.
      hnf. cbn. now rewrite inst_subst, ?inst_sub_wk1.
      hnf. cbn. now rewrite inst_subst, ?inst_sub_wk1.
    Qed.
    Hint Resolve refine_demonic : core.

    Lemma refine_angelic_ctx {N : Set} (n : N -> LVar) {Γ : PCtx} (Δ : NCtx N Ty) :
      forall {w0 : World} (ι0 : Valuation w0) (Hpc0 : instpc (wco w0) ι0),
        ℛ ι0 (@SHeapSpecM.angelic_ctx N n Γ w0 Δ) (@CHeapSpecM.angelic_ctx N Γ Δ).
    Proof.
      intros w0 ι0 Hpc0. unfold SHeapSpecM.angelic_ctx, CHeapSpecM.angelic_ctx.
      apply refine_lift_purem; auto.
      now apply PureSpecM.refine_angelic_ctx.
    Qed.

    Lemma refine_demonic_ctx {N : Set} (n : N -> LVar) {Γ : PCtx} (Δ : NCtx N Ty) :
      forall {w0 : World} (ι0 : Valuation w0) (Hpc0 : instpc (wco w0) ι0),
        ℛ ι0 (@SHeapSpecM.demonic_ctx N n Γ w0 Δ) (@CHeapSpecM.demonic_ctx N Γ Δ).
    Proof.
      intros w0 ι0 Hpc0. unfold SHeapSpecM.demonic_ctx, CHeapSpecM.demonic_ctx.
      apply refine_lift_purem; auto.
      now apply PureSpecM.refine_demonic_ctx.
    Qed.

    Lemma refine_debug {AT A D} `{Refine AT A, Subst D, SubstLaws D, OccursCheck D} {Γ1 Γ2} {w0 : World} (ι0 : Valuation w0)
          (Hpc : instpc (wco w0) ι0) f ms mc :
      ℛ ι0 ms mc ->
      ℛ ι0 (@SHeapSpecM.debug AT D _ _ _ _ Γ1 Γ2 w0 f ms) mc.
    Proof.
      intros Hap.
      intros POST__s POST__c HPOST.
      intros δs0 δc0 -> hs0 hc0 ->.
      unfold SHeapSpecM.debug. hnf.
      cbn. intros [HP]. revert HP.
      apply Hap; auto.
    Qed.

    Lemma refine_angelic_binary {AT A} `{Refine AT A} {Γ1 Γ2} {w : World} (ι : Valuation w) :
      ℛ ι (@SHeapSpecM.angelic_binary Γ1 Γ2 AT w) (@CHeapSpecM.angelic_binary Γ1 Γ2 A).
    Proof.
      intros ms1 mc1 Hm1 ms2 mc2 Hm2.
      intros POST__s POST__c HPOST.
      intros δs0 δc0 -> hs0 hc0 ->.
      unfold SHeapSpecM.angelic_binary, CHeapSpecM.angelic_binary.
      intros [HYP|HYP]; [left|right]; revert HYP.
      - apply Hm1; auto.
      - apply Hm2; auto.
    Qed.

    Lemma refine_demonic_binary {AT A} `{Refine AT A} {Γ1 Γ2} {w : World} (ι : Valuation w) :
      ℛ ι (@SHeapSpecM.demonic_binary Γ1 Γ2 AT w) (@CHeapSpecM.demonic_binary Γ1 Γ2 A).
    Proof.
      intros ms1 mc1 Hm1 ms2 mc2 Hm2.
      intros POST__s POST__c HPOST.
      intros δs0 δc0 -> hs0 hc0 ->.
      unfold SHeapSpecM.demonic_binary, CHeapSpecM.demonic_binary.
      intros [H1 H2]. split.
      - revert H1. apply Hm1; auto.
      - revert H2. apply Hm2; auto.
    Qed.

    Lemma refine_angelic_list {M} {subM : Subst M} {occM : OccursCheck M} {AT A} `{Inst AT A} {Γ}
      {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι)
      (msg : SStore Γ w -> SHeap w -> M w) :
      ℛ ι (SHeapSpecM.angelic_list (A := AT) msg) (@CHeapSpecM.angelic_list A Γ).
    Proof.
      intros ls lc Hl.
      unfold SHeapSpecM.angelic_list, CHeapSpecM.angelic_list.
      intros POST__s POST__c HPOST.
      intros δs0 δc0 Hδ0 hs0 hc0 Hh0.
      apply refine_lift_purem; eauto.
      apply PureSpecM.refine_angelic_list; auto.
    Qed.

    Lemma refine_angelic_finite {F} `{finite.Finite F} {Γ}
      {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι) msg :
      ℛ (AT := SHeapSpecM Γ Γ (Const F)) ι (@SHeapSpecM.angelic_finite Γ F _ _ w msg) (@CHeapSpecM.angelic_finite Γ F _ _).
    Proof.
      unfold SHeapSpecM.angelic_finite, CHeapSpecM.angelic_finite.
      intros POST__s POST__c HPOST.
      intros δs0 δc0 Hδ0 hs0 hc0 Hh0.
      apply refine_lift_purem; eauto.
      apply PureSpecM.refine_angelic_finite; auto.
    Qed.

    Lemma refine_demonic_finite {F} `{finite.Finite F} {Γ}
      {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι) :
      ℛ (AT := SHeapSpecM Γ Γ (Const F)) ι (@SHeapSpecM.demonic_finite Γ F _ _ w) (@CHeapSpecM.demonic_finite Γ F _ _).
    Proof.
      unfold SHeapSpecM.demonic_finite, CHeapSpecM.demonic_finite.
      intros POST__s POST__c HPOST.
      intros δs0 δc0 Hδ0 hs0 hc0 Hh0.
      apply refine_lift_purem; eauto.
      apply PureSpecM.refine_demonic_finite; auto.
    Qed.

  End Basics.

  Section AssumeAssert.

    Lemma refine_assume_formula {Γ} {w0 : World} {ι0 : Valuation w0} (Hpc0 : instpc (wco w0) ι0)
      (fml__s : Formula w0) (fml__c : Prop) (Hfml : fml__c <-> inst fml__s ι0) :
      ℛ ι0 (@SHeapSpecM.assume_formula Γ w0 fml__s) (CHeapSpecM.assume_formula fml__c).
    Proof.
      unfold SHeapSpecM.assume_formula, CHeapSpecM.assume_formula.
      apply refine_lift_purem; auto.
      now apply PureSpecM.refine_assume_formula.
    Qed.

    Lemma refine_box_assume_formula {Γ} {w0 : World} {ι0 : Valuation w0} (Hpc0 : instpc (wco w0) ι0)
      (fml__s : Formula w0) (fml__c : Prop) (Hfml : fml__c <-> inst fml__s ι0) :
      ℛ ι0 (@SHeapSpecM.box_assume_formula Γ w0 fml__s) (CHeapSpecM.assume_formula fml__c).
    Proof.
      unfold SHeapSpecM.box_assume_formula, fmap_box.
      intros w1 ω01 ι1 -> Hpc1.
      apply refine_assume_formula; auto.
      now rewrite inst_persist.
    Qed.

    Lemma refine_assert_formula {Γ} {w0 : World} (ι0 : Valuation w0) (Hpc : instpc (wco w0) ι0)
      (fml__s : Formula w0) (fml__c : Prop) (Hfml : fml__c <-> inst fml__s ι0) :
      ℛ ι0 (@SHeapSpecM.assert_formula Γ w0 fml__s) (@CHeapSpecM.assert_formula Γ fml__c).
    Proof.
      unfold SHeapSpecM.assert_formula, CHeapSpecM.assert_formula.
      intros POST__s POST__c HPOST.
      intros δs δc Hδ hs hc Hh.
      apply refine_lift_purem; auto.
      now apply PureSpecM.refine_assert_formula.
    Qed.

    Lemma refine_box_assert_formula {Γ} {w0 : World} {ι0 : Valuation w0} (Hpc0 : instpc (wco w0) ι0)
      (fml__s : Formula w0) (fml__c : Prop) (Hfml : fml__c <-> inst fml__s ι0) :
      ℛ ι0 (@SHeapSpecM.box_assert_formula Γ w0 fml__s) (CHeapSpecM.assert_formula fml__c).
    Proof.
      unfold SHeapSpecM.box_assert_formula, fmap_box.
      intros w1 ω01 ι1 -> Hpc1.
      apply refine_assert_formula; auto.
      now rewrite inst_persist.
    Qed.

    Lemma refine_assert_formulas {Γ} {w0 : World} (ι0 : Valuation w0) (Hpc : instpc (wco w0) ι0)
      (fmls__s : List Formula w0) (fmls__c : Prop) (Hfmls : fmls__c <-> instpc fmls__s ι0) :
      ℛ ι0 (@SHeapSpecM.assert_formulas Γ w0 fmls__s) (@CHeapSpecM.assert_formula Γ fmls__c).
    Proof.
      intros POST__s POST__c HPOST.
      intros δs δc -> hs hc ->.
      unfold SHeapSpecM.assert_formulas, CHeapSpecM.assert_formula.
      apply refine_lift_purem; auto.
      now apply PureSpecM.refine_assert_formulas.
    Qed.

    Lemma refine_assert_eq_nenv {N Γ} (Δ : NCtx N Ty) {w0 : World} (ι0 : Valuation w0) (Hpc : instpc (wco w0) ι0) :
      ℛ ι0 (@SHeapSpecM.assert_eq_nenv N Γ Δ w0) (@CHeapSpecM.assert_eq_nenv N Γ Δ).
    Proof.
      intros E1 ? ? E2 ? ? POST__s POST__c HPOST δs δc -> hs hc ->.
      unfold SHeapSpecM.assert_eq_nenv, CHeapSpecM.assert_eq_nenv.
      apply refine_lift_purem; auto.
      apply PureSpecM.refine_assert_eq_nenv; auto.
    Qed.

    Lemma refine_assert_eq_chunk {Γ} {w0 : World} {ι0 : Valuation w0} (Hpc : instpc (wco w0) ι0) :
      ℛ ι0 (@SHeapSpecM.assert_eq_chunk Γ w0) CHeapSpecM.assert_eq_chunk.
    Proof.
      intros c1 ? ? E2 ? ? POST__s POST__c HPOST δs δc Hδ hs hc Hh.
      unfold SHeapSpecM.assert_eq_chunk, CHeapSpecM.assert_eq_chunk.
      apply refine_lift_purem; auto. unfold T.
      eapply PureSpecM.refine_assert_eq_chunk; cbn; eauto.
      now rewrite inst_sub_id.
    Qed.

  End AssumeAssert.

  Section PatternMatching.

    Lemma refine_angelic_match_bool' {AT A} `{Refine AT A} {Γ1 Γ2}
      {w : World} (ι : Valuation w) (Hpc: instpc (wco w) ι) :
      ℛ ι (@SHeapSpecM.angelic_match_bool' AT Γ1 Γ2 w) (CHeapSpecM.angelic_match_bool (A := A)).
    Proof.
      unfold SHeapSpecM.angelic_match_bool', CHeapSpecM.angelic_match_bool.
      intros t v ->.
      intros kt__s kt__c Hkt.
      intros kf__s kf__c Hkf.
      apply refine_angelic_binary; eauto.
      - apply refine_bind; eauto.
        apply refine_assert_formula; eauto.
        intros ? ? ? -> ? _ _ _. auto.
      - apply refine_bind; eauto.
        apply refine_assert_formula; eauto.
        cbn. unfold is_true. now rewrite negb_true_iff.
        intros ? ? ? -> ? _ _ _. auto.
    Qed.

    Lemma refine_angelic_match_bool {AT A} `{Refine AT A} {Γ1 Γ2}
      {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι) :
      ℛ ι (@SHeapSpecM.angelic_match_bool AT Γ1 Γ2 w) (CHeapSpecM.angelic_match_bool (A := A)).
    Proof.
      unfold SHeapSpecM.angelic_match_bool.
      intros t v ->.
      destruct (term_get_val_spec t).
      - rewrite H0.
        intros kt__s kt__c Hkt.
        intros kf__s kf__c Hkf.
        intros POST__s POST__c HPOST.
        intros δs δc Hδ hs hc Hh.
        hnf. rewrite CHeapSpecM.wp_angelic_match_bool.
        destruct a.
        + apply Hkt; wsimpl; eauto.
        + apply Hkf; wsimpl; eauto.
      - now apply refine_angelic_match_bool'.
    Qed.

    Lemma refine_box_angelic_match_bool {AT A} `{Refine AT A} {Γ1 Γ2}
      {w : World} (ι : Valuation w) :
      ℛ ι (@SHeapSpecM.box_angelic_match_bool AT Γ1 Γ2 w) (CHeapSpecM.angelic_match_bool (A := A)).
    Proof.
      unfold SHeapSpecM.box_angelic_match_bool, fmap_box, K.
      intros t v ->.
      intros kt__s kt__c Hkt.
      intros kf__s kf__c Hkf.
      intros w1 ω01 ι1 -> Hpc1.
      apply refine_angelic_match_bool; wsimpl; eauto.
      rewrite <- inst_persist; auto.
    Qed.

    Lemma refine_demonic_match_bool' {AT A} `{Refine AT A} {Γ1 Γ2}
      {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι) :
      ℛ ι (@SHeapSpecM.demonic_match_bool' AT Γ1 Γ2 w) (CHeapSpecM.demonic_match_bool (A := A)).
    Proof.
      unfold SHeapSpecM.demonic_match_bool, CHeapSpecM.demonic_match_bool.
      intros t v ->.
      intros kt__s kt__c Hkt.
      intros kf__s kf__c Hkf.
      apply refine_demonic_binary; eauto.
      - apply refine_bind; eauto.
        apply refine_assume_formula; eauto.
        intros ? ? ? -> ? _ _ _. auto.
      - apply refine_bind; eauto.
        apply refine_assume_formula; eauto.
        cbn. unfold is_true. now rewrite negb_true_iff.
        intros ? ? ? -> ? _ _ _. auto.
    Qed.

    Lemma refine_demonic_match_bool {AT A} `{Refine AT A} {Γ1 Γ2} {w : World}
      (ι : Valuation w) (Hpc : instpc (wco w) ι) :
      ℛ ι (@SHeapSpecM.demonic_match_bool AT Γ1 Γ2 w) (CHeapSpecM.demonic_match_bool (A := A)).
    Proof.
      unfold SHeapSpecM.demonic_match_bool.
      intros t v ->.
      destruct (term_get_val_spec t).
      - rewrite H0.
        intros kt__s kt__c Hkt.
        intros kf__s kf__c Hkf.
        intros POST__s POST__c HPOST.
        intros δs δc Hδ hs hc Hh.
        hnf. rewrite CHeapSpecM.wp_demonic_match_bool.
        destruct a.
        + apply Hkt; wsimpl; eauto.
        + apply Hkf; wsimpl; eauto.
      - now apply refine_demonic_match_bool'.
    Qed.

    Lemma refine_box_demonic_match_bool {AT A} `{Refine AT A} {Γ1 Γ2}
      {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι) :
      ℛ ι (@SHeapSpecM.box_demonic_match_bool AT Γ1 Γ2 w) (CHeapSpecM.demonic_match_bool (A := A)).
    Proof.
      unfold SHeapSpecM.box_demonic_match_bool, fmap_box, K.
      intros t v ->.
      intros kt__s kt__c Hkt.
      intros kf__s kf__c Hkf.
      intros w1 ω01 ι1 -> Hpc1.
      apply refine_demonic_match_bool; wsimpl; eauto.
      rewrite <- inst_persist. auto.
    Qed.

    Lemma refine_angelic_match_enum {AT A} `{Refine AT A} {E : enumi} {Γ1 Γ2 : PCtx}
      {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι) :
      ℛ ι (@SHeapSpecM.angelic_match_enum AT E Γ1 Γ2 w) (@CHeapSpecM.angelic_match_enum A E Γ1 Γ2).
    Proof.
      intros t v ->.
      intros ks kc Hk.
      unfold SHeapSpecM.angelic_match_enum, CHeapSpecM.angelic_match_enum.
      apply refine_bind.
      apply refine_angelic_finite; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros EK1 EK2 ->.
      apply refine_bind.
      apply refine_assert_formula; cbn; wsimpl; auto.
      now rewrite <- inst_persist.
      intros w2 ω12 ι2 -> Hpc2 _ _ _.
      apply Hk; wsimpl; auto.
    Qed.

    Lemma refine_demonic_match_enum {AT A} `{Refine AT A} {E : enumi} {Γ1 Γ2 : PCtx}
      {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι) :
      ℛ ι (@SHeapSpecM.demonic_match_enum AT E Γ1 Γ2 w) (@CHeapSpecM.demonic_match_enum A E Γ1 Γ2).
    Proof.
      intros t v ->.
      intros ks kc Hk.
      unfold SHeapSpecM.demonic_match_enum, CHeapSpecM.demonic_match_enum.
      apply refine_bind.
      apply refine_demonic_finite; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros EK1 EK2 ->.
      apply refine_bind.
      apply refine_assume_formula; cbn; wsimpl; auto.
      now rewrite <- inst_persist.
      intros w2 ω12 ι2 -> Hpc2 _ _ _.
      apply Hk; wsimpl; auto.
    Qed.

    Lemma refine_angelic_match_sum {AT A} `{Refine AT A} {Γ1 Γ2} x y σ τ
      {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι) :
      ℛ ι (@SHeapSpecM.angelic_match_sum AT Γ1 Γ2 x y σ τ w) (@CHeapSpecM.angelic_match_sum A Γ1 Γ2 σ τ).
    Proof.
      intros t v ->.
      intros kl kl__c Hk__l.
      intros kr kr__c Hk__r.
      unfold SHeapSpecM.angelic_match_sum, CHeapSpecM.angelic_match_sum.
      apply refine_angelic_binary, refine_bind.
      - apply refine_bind; try (apply refine_angelic; assumption).
        intros w1 r01 ι1 -> Hpc1.
        intros v1 vc1 Hv1. hnf in Hv1. subst.
        apply refine_bind.
        * apply refine_assert_formula; try assumption. cbn.
          now rewrite <- inst_persist.
        * intros w2 r12 ι2 -> Hpc2 _ _ _.
          eapply (refine_four Hk__l); cbn; eauto.
          now rewrite inst_sub_id, ?sub_acc_trans, ?inst_subst.
          now rewrite <- inst_persist.
      - now apply refine_angelic.
      - intros w1 r01 ι1 -> Hpc1.
        intros v1 vc1 Hv1. hnf in Hv1. subst.
        apply refine_bind.
        + apply refine_assert_formula; try assumption.
          now rewrite <- inst_persist.
        + intros w2 r12 ι2 -> Hpc2 _ _ _.
          eapply (refine_four Hk__r); cbn; eauto.
          now rewrite inst_sub_id, ?sub_acc_trans, ?inst_subst.
          now rewrite <- inst_persist.
    Qed.

    Lemma refine_demonic_match_sum {AT A} `{Refine AT A} {Γ1 Γ2} x y σ τ
      {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι) :
      ℛ ι (@SHeapSpecM.demonic_match_sum AT Γ1 Γ2 x y σ τ w) (@CHeapSpecM.demonic_match_sum A Γ1 Γ2 σ τ).
    Proof.
      intros t v ->.
      intros kl kl__c Hk__l.
      intros kr kr__c Hk__r.
      unfold SHeapSpecM.demonic_match_sum, CHeapSpecM.demonic_match_sum.
      apply refine_demonic_binary, refine_bind.
      - apply refine_bind; try (apply refine_demonic; assumption).
        intros w1 r01 ι1 -> Hpc1.
        intros v1 vc1 Hv. hnf in Hv. subst.
        apply refine_bind.
        * apply refine_assume_formula; try assumption.
          now rewrite <- inst_persist.
        * intros w2 r12 ι2 -> Hpc2 _ _ _.
          eapply (refine_four Hk__l); cbn; eauto.
          now rewrite inst_sub_id, ?sub_acc_trans, ?inst_subst.
          now rewrite <- inst_persist.
      - now apply refine_demonic.
      - intros w1 r01 ι1 -> Hpc1.
        intros v1 vc1 Hv. hnf in Hv. subst.
        apply refine_bind.
        + apply refine_assume_formula; try assumption.
          now rewrite <- inst_persist.
        + intros w2 r12 ι2 -> Hpc2 _ _ _.
          eapply (refine_four Hk__r); cbn; eauto.
          now rewrite inst_sub_id, ?sub_acc_trans, ?inst_subst.
          now rewrite <- inst_persist.
    Qed.

    Lemma refine_angelic_match_prod {AT A} `{Refine AT A} {Γ1 Γ2} x y σ τ
      {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι) :
      ℛ ι (@SHeapSpecM.angelic_match_prod AT Γ1 Γ2 x y σ τ w) (@CHeapSpecM.angelic_match_prod A Γ1 Γ2 σ τ).
    Proof.
      intros t v ->.
      intros k k__c Hk.
      unfold SHeapSpecM.angelic_match_prod, CHeapSpecM.angelic_match_prod.
      apply refine_bind; try (apply refine_angelic; assumption).
      intros w1 r01 ι1 -> Hpc1.
      intros v1 vc1 ->.
      apply refine_bind; try (apply refine_angelic; assumption).
      intros w2 r12 ι2 -> Hpc2.
      intros v2 vc2 ->.
      apply refine_bind.
      - apply refine_assert_formula; try assumption. cbn - [Val].
        change (inst_term ?t ?ι) with (inst t ι).
        rewrite (inst_persist (AT := STerm _) (A := Val _)).
        rewrite (inst_persist (AT := STerm _) (A := Val _)).
        now rewrite sub_acc_trans, inst_subst.
      - intros w3 r23 ι3 -> Hpc3 _ _ _.
        eapply (refine_four Hk); eauto.
        + now rewrite sub_acc_trans, inst_subst.
        + rewrite <- ?inst_subst, <- subst_sub_comp.
          now rewrite <- sub_acc_trans, inst_subst, <- inst_persist.
        + now rewrite <- inst_persist.
    Qed.

    Lemma refine_demonic_match_prod {AT A} `{Refine AT A} {Γ1 Γ2} x y σ τ
      {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι) :
      ℛ ι (@SHeapSpecM.demonic_match_prod AT Γ1 Γ2 x y σ τ w) (@CHeapSpecM.demonic_match_prod A Γ1 Γ2 σ τ).
    Proof.
      intros t v ->.
      intros k k__c Hk.
      unfold SHeapSpecM.demonic_match_prod, CHeapSpecM.demonic_match_prod.
      apply refine_bind; try (apply refine_demonic; assumption).
      intros w1 r01 ι1 -> Hpc1.
      intros v1 vc1 ->.
      apply refine_bind; try (apply refine_demonic; assumption).
      intros w2 r12 ι2 -> Hpc2.
      intros v2 vc2 ->.
      apply refine_bind.
      - apply refine_assume_formula; try assumption. cbn - [Val].
        change (inst_term ?t ?ι) with (inst t ι).
        rewrite (inst_persist (AT := STerm _) (A := Val _)).
        rewrite (inst_persist (AT := STerm _) (A := Val _)).
        now rewrite sub_acc_trans, inst_subst.
      - intros w3 r23 ι3 -> Hpc3 _ _ _.
        eapply (refine_four Hk); eauto.
        + now rewrite sub_acc_trans, inst_subst.
        + rewrite <- ?inst_subst, <- subst_sub_comp.
          now rewrite <- sub_acc_trans, inst_subst, <- inst_persist.
        + now rewrite <- inst_persist.
    Qed.

    Lemma refine_angelic_match_list {AT A} `{Refine AT A} {Γ1 Γ2} xhead xtail σ
      {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι) :
      ℛ ι (@SHeapSpecM.angelic_match_list AT Γ1 Γ2 xhead xtail σ w) (@CHeapSpecM.angelic_match_list A Γ1 Γ2 σ).
    Proof.
      intros t ? ->.
      intros sknil cknil Hknil.
      intros skcons ckcons Hkcons.
      unfold SHeapSpecM.angelic_match_list, CHeapSpecM.angelic_match_list.
      apply refine_angelic_binary.
      - apply refine_bind; auto.
        apply refine_assert_formula; auto.
        intros ? ? ? -> ? _ _ _; auto.
      - apply refine_bind; auto.
        apply refine_angelic; auto.
        intros w1 ω01 ι1 -> Hpc1.
        intros thead vhead ->.
        apply refine_bind; auto.
        apply refine_angelic; auto.
        intros w2 ω12 ι2 -> Hpc2.
        intros ttail vtail ->.
        apply refine_bind; auto.
        + apply refine_assert_formula; auto.
          cbn - [Val].
          change (inst_term ?t ?ι) with (inst t ι).
          rewrite (inst_persist (AT := STerm _) (A := Val _)).
          rewrite (inst_persist (AT := STerm _) (A := Val _)).
          now rewrite sub_acc_trans, inst_subst.
        + intros w3 ω23 ι3 -> Hpc3 _ _ _.
          apply Hkcons; wsimpl; eauto.
          rewrite <- ?inst_subst, <- subst_sub_comp.
          now rewrite <- sub_acc_trans, inst_subst, <- inst_persist.
          now rewrite <- inst_persist.
    Qed.

    Lemma refine_demonic_match_list {AT A} `{Refine AT A} {Γ1 Γ2} xhead xtail σ
      {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι) :
      ℛ ι (@SHeapSpecM.demonic_match_list AT Γ1 Γ2 xhead xtail σ w) (@CHeapSpecM.demonic_match_list A Γ1 Γ2 σ).
    Proof.
      intros t ? ->.
      intros sknil cknil Hknil.
      intros skcons ckcons Hkcons.
      unfold SHeapSpecM.demonic_match_list, CHeapSpecM.demonic_match_list.
      apply refine_demonic_binary.
      - apply refine_bind; auto.
        apply refine_assume_formula; auto.
        intros ? ? ? -> ? _ _ _; auto.
      - apply refine_bind; auto.
        apply refine_demonic; auto.
        intros w1 ω01 ι1 -> Hpc1.
        intros thead vhead ->.
        apply refine_bind; auto.
        apply refine_demonic; auto.
        intros w2 ω12 ι2 -> Hpc2.
        intros ttail vtail ->.
        apply refine_bind; auto.
        + apply refine_assume_formula; auto.
          cbn - [Val].
          change (inst_term ?t ?ι) with (inst t ι).
          rewrite (inst_persist (AT := STerm _) (A := Val _)).
          rewrite (inst_persist (AT := STerm _) (A := Val _)).
          now rewrite sub_acc_trans, inst_subst.
        + intros w3 ω23 ι3 -> Hpc3 _ _ _.
          apply Hkcons; wsimpl; eauto.
          rewrite <- ?inst_subst, <- subst_sub_comp.
          now rewrite <- sub_acc_trans, inst_subst, <- inst_persist.
          now rewrite <- inst_persist.
    Qed.

    Lemma refine_angelic_match_record' {N : Set} (n : N -> LVar) {R AT A} `{Refine AT A} {Γ1 Γ2}
      {Δ : NCtx N Ty} {p : RecordPat (recordf_ty R) Δ}
      {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι) :
      ℛ ι (@SHeapSpecM.angelic_match_record' N n AT R Γ1 Γ2 Δ p w) (@CHeapSpecM.angelic_match_record N A R Γ1 Γ2 Δ p).
    Proof.
      intros t v ->.
      intros k k__c Hk.
      unfold SHeapSpecM.angelic_match_record', CHeapSpecM.angelic_match_record.
      apply refine_bind; try (apply refine_angelic_ctx; assumption).
      intros w1 r01 ι1 -> Hpc1.
      intros v1 vc1 ->.
      apply refine_bind.
      - apply refine_assert_formula; try assumption. cbn - [Val].
        now rewrite <- inst_persist, (inst_record_pattern_match_reverse ι1 p).
      - intros w2 r12 ι2 -> Hpc2 _ _ _.
        eapply (refine_four Hk); eauto.
        now rewrite <- inst_persist.
    Qed.

    Lemma refine_angelic_match_record {N : Set} (n : N -> LVar) {R AT A} `{Refine AT A} {Γ1 Γ2}
      {Δ : NCtx N Ty} {p : RecordPat (recordf_ty R) Δ}
      {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι) :
      ℛ ι (@SHeapSpecM.angelic_match_record N n AT R Γ1 Γ2 Δ p w) (@CHeapSpecM.angelic_match_record N A R Γ1 Γ2 Δ p).
    Proof.
      intros t v ->.
      intros c c__c Hc.
      unfold SHeapSpecM.angelic_match_record.
      destruct (term_get_record_spec t).
      - intros P2 Pc2 HP2.
        intros c2 cc2 Hc2.
        intros s2 sc2 Hs2.
        hnf.
        rewrite CHeapSpecM.wp_angelic_match_record.
        apply Hc; wsimpl; eauto.
        hnf.
        unfold record_pattern_match_val.
        rewrite H0. rewrite recordv_unfold_fold.
        symmetry.
        apply inst_record_pattern_match.
      - apply refine_angelic_match_record'; auto.
    Qed.

    Lemma refine_demonic_match_record' {N : Set} (n : N -> LVar) {R AT A} `{Refine AT A} {Γ1 Γ2}
      {Δ : NCtx N Ty} {p : RecordPat (recordf_ty R) Δ}
      {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι) :
      ℛ ι (@SHeapSpecM.demonic_match_record' N n AT R Γ1 Γ2 Δ p w) (@CHeapSpecM.demonic_match_record N A R Γ1 Γ2 Δ p).
    Proof.
      intros t v ->.
      intros k k__c Hk.
      unfold SHeapSpecM.demonic_match_record', CHeapSpecM.demonic_match_record.
      apply refine_bind. try (apply refine_demonic_ctx; assumption).
      intros w1 r01 ι1 -> Hpc1.
      intros v1 vc1 ->.
      apply refine_bind.
      - apply refine_assume_formula; try assumption. cbn - [Val].
        now rewrite <- inst_persist, (inst_record_pattern_match_reverse ι1 p).
      - intros w2 r12 ι2 -> Hpc2 _ _ _.
        eapply (refine_four Hk); eauto.
        now rewrite <- inst_persist.
    Qed.

    Lemma refine_demonic_match_record {N : Set} (n : N -> LVar) {R AT A} `{Refine AT A} {Γ1 Γ2}
      {Δ : NCtx N Ty} {p : RecordPat (recordf_ty R) Δ}
      {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι) :
      ℛ ι (@SHeapSpecM.demonic_match_record N n AT R Γ1 Γ2 Δ p w) (@CHeapSpecM.demonic_match_record N A R Γ1 Γ2 Δ p).
    Proof.
      intros t v ->.
      intros c c__c Hc.
      unfold SHeapSpecM.demonic_match_record.
      destruct (term_get_record_spec t).
      - intros P2 Pc2 HP2.
        intros c2 cc2 Hc2.
        intros s2 sc2 Hs2.
        hnf.
        rewrite CHeapSpecM.wp_demonic_match_record.
        apply Hc; wsimpl; eauto.
        hnf.
        unfold record_pattern_match_val.
        rewrite H0. rewrite recordv_unfold_fold.
        change (fun Σ => @Env (N ∷ Ty) (fun τ => Term Σ (type τ)) Δ) with (fun Σ => @NamedEnv N Ty (Term Σ) Δ).
        now rewrite inst_record_pattern_match.
      - apply refine_demonic_match_record'; auto.
    Qed.

    Lemma refine_angelic_match_tuple {N : Set} (n : N -> LVar) {σs AT A} `{Refine AT A} {Γ1 Γ2}
      {Δ : NCtx N Ty} {p : TuplePat σs Δ}
      {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι) :
      ℛ ι (@SHeapSpecM.angelic_match_tuple N n AT σs Γ1 Γ2 Δ p w) (@CHeapSpecM.angelic_match_tuple N A σs Γ1 Γ2 Δ p).
    Proof.
      intros t v ->.
      intros k k__c Hk.
      unfold SHeapSpecM.angelic_match_tuple, CHeapSpecM.angelic_match_tuple.
      apply refine_bind; try (apply refine_angelic_ctx; assumption).
      intros w1 r01 ι1 -> Hpc1.
      intros v1 vc1 ->.
      change (fun Σ => @Env (N ∷ Ty) (fun τ => Term Σ (type τ)) Δ) with (fun Σ => @NamedEnv N Ty (Term Σ) Δ).
      apply refine_bind.
      - apply refine_assert_formula; try assumption. cbn - [Val].
        rewrite inst_term_tuple.
        rewrite inst_tuple_pattern_match_reverse.
        rewrite <- inst_persist.
        unfold tuple_pattern_match_val.
        split; intros <-.
        + now rewrite tuple_pattern_match_env_inverse_left, envrec.of_to_env.
        + now rewrite envrec.to_of_env, tuple_pattern_match_env_inverse_right.
      - intros w2 r12 ι2 -> Hpc2 _ _ _.
        eapply (refine_four Hk); eauto.
        now rewrite <- inst_persist.
    Qed.

    Lemma refine_demonic_match_tuple {N : Set} (n : N -> LVar) {σs AT A} `{Refine AT A} {Γ1 Γ2}
      {Δ : NCtx N Ty} {p : TuplePat σs Δ}
      {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι) :
      ℛ ι (@SHeapSpecM.demonic_match_tuple N n AT σs Γ1 Γ2 Δ p w) (@CHeapSpecM.demonic_match_tuple N A σs Γ1 Γ2 Δ p).
    Proof.
      intros t v ->.
      intros k k__c Hk.
      unfold SHeapSpecM.demonic_match_tuple, CHeapSpecM.demonic_match_tuple.
      apply refine_bind; try (apply refine_demonic_ctx; assumption).
      intros w1 r01 ι1 -> Hpc1.
      intros v1 vc1 ->.
      change (fun Σ => @Env (N ∷ Ty) (fun τ => Term Σ (type τ)) Δ) with (fun Σ => @NamedEnv N Ty (Term Σ) Δ).
      apply refine_bind.
      - apply refine_assume_formula; try assumption. cbn - [Val].
        rewrite inst_term_tuple.
        rewrite inst_tuple_pattern_match_reverse.
        rewrite <- inst_persist.
        unfold tuple_pattern_match_val.
        split; intros <-.
        + now rewrite tuple_pattern_match_env_inverse_left, envrec.of_to_env.
        + now rewrite envrec.to_of_env, tuple_pattern_match_env_inverse_right.
      - intros w2 r12 ι2 -> Hpc2 _ _ _.
        eapply (refine_four Hk); eauto.
        now rewrite <- inst_persist.
    Qed.

    Lemma refine_angelic_match_pattern {N : Set} (n : N -> LVar) {σ} {Δ : NCtx N Ty}
          {p : Pattern Δ σ} {Γ}
      {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι) {msg} :
      ℛ ι (@SHeapSpecM.angelic_match_pattern N n σ Δ p Γ w msg) (@CHeapSpecM.angelic_match_pattern N σ Δ p Γ).
    Proof.
      intros t v ->.
      intros k k__c Hk.
      unfold SHeapSpecM.angelic_match_pattern, CHeapSpecM.angelic_match_pattern.
      apply refine_bind; try (apply refine_angelic_ctx; assumption); try assumption.
      intros w1 r01 ι1 -> Hpc1.
      intros ts vs ->.
      change (fun Σ => @Env (N ∷ Ty) (fun τ => Term Σ (type τ)) Δ) with (fun Σ => @NamedEnv N Ty (Term Σ) Δ).
      apply refine_bind.
      - apply refine_assert_formula; try assumption. cbn - [Val].
        rewrite inst_pattern_match_env_reverse.
        rewrite <- inst_persist.
        split; intros <-.
        + now rewrite pattern_match_val_inverse_left.
        + now rewrite pattern_match_val_inverse_right.
      - intros w2 r12 ι2 -> Hpc2 _ _ _.
        apply refine_pure; try assumption.
        now rewrite <- inst_persist.
    Qed.

    Lemma refine_angelic_match_union {N : Set} (n : N -> LVar) {AT A} `{Refine AT A} {Γ1 Γ2 : PCtx} {U : unioni}
      {Δ : unionk U -> NCtx N Ty} {p : forall K : unionk U, Pattern (Δ K) (unionk_ty U K)}
      {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι) :
      ℛ ι (@SHeapSpecM.angelic_match_union N n AT Γ1 Γ2 U Δ p w) (@CHeapSpecM.angelic_match_union N A Γ1 Γ2 U Δ p).
    Proof.
      intros t v ->.
      intros k k__c Hk.
      unfold SHeapSpecM.angelic_match_union, CHeapSpecM.angelic_match_union.
      apply refine_bind; try (apply refine_angelic_finite; assumption).
      intros w1 r01 ι1 -> Hpc1.
      intros v1 vc1 ->.
      apply refine_bind; try (apply refine_angelic; assumption).
      intros w2 r12 ι2 -> Hpc2.
      intros v2 vc2 ->.
      apply refine_bind.
      - apply refine_assert_formula; try assumption. cbn - [Val].
        change (inst v1 _) with v1.
        change (inst_term ?t ?ι) with (inst t ι).
        rewrite (inst_persist (AT := STerm _) (A := Val _)).
        now rewrite sub_acc_trans, inst_subst.
      - intros w3 r23 ι3 -> Hpc3 _ _ _.
        apply refine_bind.
        + apply refine_angelic_match_pattern; try assumption.
          now rewrite <- inst_persist.
        + change (inst v1 _) with v1.
          specialize (Hk v1).
          eapply (refine_four Hk).
          now rewrite ?sub_acc_trans, ?inst_subst.
    Qed.

    Lemma refine_demonic_match_pattern {N : Set} (n : N -> LVar) {σ} {Δ : NCtx N Ty}
          {p : Pattern Δ σ} {Γ}
      {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι) :
      ℛ ι (@SHeapSpecM.demonic_match_pattern N n σ Δ p Γ w) (@CHeapSpecM.demonic_match_pattern N σ Δ p Γ).
    Proof.
      intros t v ->.
      intros k k__c Hk.
      unfold SHeapSpecM.demonic_match_pattern, CHeapSpecM.demonic_match_pattern.
      apply refine_bind; try (apply refine_demonic_ctx; assumption); try assumption.
      intros w1 r01 ι1 -> Hpc1.
      intros ts vs ->.
      change (fun Σ => @Env (N ∷ Ty) (fun τ => Term Σ (type τ)) Δ) with (fun Σ => @NamedEnv N Ty (Term Σ) Δ).
      apply refine_bind.
      - apply refine_assume_formula; try assumption. cbn - [Val].
        rewrite inst_pattern_match_env_reverse.
        rewrite <- inst_persist.
        split; intros <-.
        + now rewrite pattern_match_val_inverse_left.
        + now rewrite pattern_match_val_inverse_right.
      - intros w2 r12 ι2 -> Hpc2 _ _ _.
        apply refine_pure; try assumption.
        now rewrite <- inst_persist.
    Qed.

    Lemma refine_demonic_match_union {N : Set} (n : N -> LVar) {AT A} `{Refine AT A} {Γ1 Γ2 : PCtx} {U : unioni}
      {Δ : unionk U -> NCtx N Ty} {p : forall K : unionk U, Pattern (Δ K) (unionk_ty U K)}
      {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι) :
      ℛ ι (@SHeapSpecM.demonic_match_union N n AT Γ1 Γ2 U Δ p w) (@CHeapSpecM.demonic_match_union N A Γ1 Γ2 U Δ p).
    Proof.
      intros t v ->.
      intros k k__c Hk.
      unfold SHeapSpecM.demonic_match_union, CHeapSpecM.demonic_match_union.
      apply refine_bind; try (apply refine_demonic_finite; assumption).
      intros w1 r01 ι1 -> Hpc1.
      intros v1 vc1 ->.
      apply refine_bind; try (apply refine_demonic; assumption).
      intros w2 r12 ι2 -> Hpc2.
      intros v2 vc2 ->.
      apply refine_bind.
      - apply refine_assume_formula; try assumption. cbn - [Val].
        change (inst v1 _) with v1.
        change (inst_term ?t ?ι) with (inst t ι).
        rewrite (inst_persist (AT := STerm _) (A := Val _)).
        now rewrite sub_acc_trans, inst_subst.
      - intros w3 r23 ι3 -> Hpc3 _ _ _.
        apply refine_bind.
        + apply refine_demonic_match_pattern; try assumption.
          now rewrite <- inst_persist.
        + change (inst v1 _) with v1.
          specialize (Hk v1).
          eapply (refine_four Hk).
          now rewrite ?sub_acc_trans, ?inst_subst.
    Qed.

    Lemma refine_demonic_match_bvec' {AT A} `{Refine AT A} {n : nat} {Γ1 Γ2 : PCtx}
      {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι) :
      ℛ ι (@SHeapSpecM.demonic_match_bvec' AT n Γ1 Γ2 w) (@CHeapSpecM.demonic_match_bvec A n Γ1 Γ2).
    Proof.
      intros t v ->.
      intros ks kc Hk.
      unfold SHeapSpecM.demonic_match_bvec', CHeapSpecM.demonic_match_bvec.
      apply refine_bind.
      apply refine_demonic_finite; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros EK1 EK2 ->. unfold CHeapSpecM.bind_right.
      apply refine_bind.
      apply refine_assume_formula; cbn; wsimpl; auto.
      now rewrite <- inst_persist.
      intros w2 ω12 ι2 -> Hpc2.
      intros _ _ _.
      apply Hk; wsimpl; auto.
    Qed.

    Lemma refine_demonic_match_bvec {AT A} `{Refine AT A} {n : nat} {Γ1 Γ2 : PCtx}
      {w : World} (ι : Valuation w) (Hpc : instpc (wco w) ι) :
      ℛ ι (@SHeapSpecM.demonic_match_bvec AT n Γ1 Γ2 w) (@CHeapSpecM.demonic_match_bvec A n Γ1 Γ2).
    Proof.
      intros t v ->.
      intros c c__c Hc.
      unfold SHeapSpecM.demonic_match_bvec.
      destruct (term_get_val_spec t).
      - intros P2 Pc2 HP2.
        intros c2 cc2 Hc2.
        intros s2 sc2 Hs2.
        hnf.
        rewrite CHeapSpecM.wp_demonic_match_bvec.
        apply Hc; wsimpl; eauto.
      - apply refine_demonic_match_bvec'; auto.
    Qed.

  End PatternMatching.

  Section State.

    Lemma refine_pushpop {AT A} `{Refine AT A} {Γ1 Γ2 x σ} {w0 : World} (ι0 : Valuation w0)
          (Hpc : instpc (wco w0) ι0) :
      ℛ ι0 (@SHeapSpecM.pushpop AT Γ1 Γ2 x σ w0) (@CHeapSpecM.pushpop A Γ1 Γ2 x σ).
    Proof.
      intros t v ->.
      intros ms mc Hm.
      intros POST__s POST__c HPOST.
      intros δs0 δc0 -> hs0 hc0 Hh0.
      unfold SHeapSpecM.pushpop, CHeapSpecM.pushpop.
      apply Hm; eauto.
      intros w1 ω01 ι1 -> Hpc1.
      intros a1 a Ha.
      intros δs1 δc1 -> hs1 hc1 Hh1.
      apply HPOST; auto.
      now destruct (env.snocView δs1).
    Qed.

    Lemma refine_pushspops {AT A} `{Refine AT A} {Γ1 Γ2 Δ} {w0 : World} (ι0 : Valuation w0)
          (Hpc : instpc (wco w0) ι0) :
      ℛ ι0 (@SHeapSpecM.pushspops AT Γ1 Γ2 Δ w0) (@CHeapSpecM.pushspops A Γ1 Γ2 Δ).
    Proof.
      intros δΔ ? ->.
      intros ms mc Hm.
      intros POST__s POST__c HPOST.
      intros δs0 δc0 -> hs0 hc0 Hh0.
      unfold SHeapSpecM.pushspops, CHeapSpecM.pushspops.
      apply Hm; auto.
      - intros w1 ω01 ι1 -> Hpc1.
        intros a1 a Ha.
        intros δs1 δc1 -> hs1 hc1 ->.
        apply HPOST; auto.
        destruct (env.catView δs1).
        hnf.
        unfold inst, inst_store, inst_env at 1.
        rewrite <- env.map_drop.
        rewrite ?env.drop_cat.
        reflexivity.
      - hnf.
        unfold inst, inst_store, inst_env at 3.
        rewrite env.map_cat.
        reflexivity.
    Qed.

    Lemma refine_get_local {Γ}
      {w0 : World} (ι0 : Valuation w0) (Hpc : instpc (wco w0) ι0) :
      ℛ ι0 (@SHeapSpecM.get_local Γ w0) (@CHeapSpecM.get_local Γ).
    Proof.
      intros POST__s POST__c HPOST.
      intros δs0 δc0 Hδ hs0 hc0 Hh0.
      unfold SHeapSpecM.get_local, CHeapSpecM.get_local.
      apply HPOST; wsimpl; auto.
    Qed.

    Lemma refine_put_local {Γ1 Γ2}
      {w0 : World} (ι0 : Valuation w0) (Hpc : instpc (wco w0) ι0) :
      ℛ ι0 (@SHeapSpecM.put_local Γ1 Γ2 w0) (@CHeapSpecM.put_local Γ1 Γ2).
    Proof.
      intros δs2 δc2 Hδ2.
      intros POST__s POST__c HPOST.
      intros δs0 δc0 Hδ hs0 hc0 Hh0.
      unfold SHeapSpecM.put_local, CHeapSpecM.put_local.
      apply HPOST; wsimpl; auto.
    Qed.

    Lemma refine_get_heap {Γ}
      {w0 : World} (ι0 : Valuation w0) (Hpc : instpc (wco w0) ι0) :
      ℛ ι0 (@SHeapSpecM.get_heap Γ w0) (@CHeapSpecM.get_heap Γ).
    Proof.
      intros POST__s POST__c HPOST.
      intros δs0 δc0 Hδ hs0 hc0 Hh0.
      unfold SHeapSpecM.get_heap, CHeapSpecM.get_heap.
      apply HPOST; wsimpl; auto.
    Qed.

    Lemma refine_put_heap {Γ}
      {w0 : World} (ι0 : Valuation w0) (Hpc : instpc (wco w0) ι0) :
      ℛ ι0 (@SHeapSpecM.put_heap Γ w0) (@CHeapSpecM.put_heap Γ).
    Proof.
      intros hs hc Hh.
      intros POST__s POST__c HPOST.
      intros δs0 δc0 Hδ hs0 hc0 Hh0.
      unfold SHeapSpecM.put_heap, CHeapSpecM.put_heap.
      apply HPOST; wsimpl; auto.
    Qed.

    Lemma refine_eval_exp {Γ σ} (e : Exp Γ σ)
      {w0 : World} (ι0 : Valuation w0) (Hpc : instpc (wco w0) ι0) :
      ℛ ι0 (@SHeapSpecM.eval_exp Γ σ e w0) (@CHeapSpecM.eval_exp Γ σ e).
    Proof.
      intros POST__s POST__c HPOST.
      intros δs0 δc0 -> hs0 hc0 Hh.
      apply HPOST; wsimpl; rewrite ?inst_sub_id; auto.
      hnf. now rewrite peval_sound, eval_exp_inst.
    Qed.

    Lemma refine_eval_exps {Γ Δ} (es : NamedEnv (Exp Γ) Δ) {w0 : World} (ι0 : Valuation w0)
          (Hpc : instpc (wco w0) ι0) :
      ℛ ι0 (@SHeapSpecM.eval_exps Γ Δ es w0) (@CHeapSpecM.eval_exps Γ Δ es).
    Proof.
      intros POST__s POST__c HPOST.
      intros δs0 δc0 -> hs0 hc0 Hh.
      apply HPOST; auto. cbn. rewrite ?inst_sub_id; auto.
      apply env.lookup_extensional; cbn; intros [x σ] xIn.
      unfold evals, inst, inst_store, inst_env. rewrite ?env.lookup_map.
      now rewrite peval_sound, <- eval_exp_inst.
    Qed.

    Lemma refine_assign {Γ x σ} {xIn : x∷σ ∈ Γ}
      {w0 : World} (ι0 : Valuation w0) (Hpc : instpc (wco w0) ι0) :
      ℛ ι0 (@SHeapSpecM.assign Γ x σ xIn w0) (@CHeapSpecM.assign Γ x σ xIn).
    Proof.
      intros t v ->.
      intros POST__s POST__c HPOST.
      intros δs0 δc0 -> hs0 hc0 Hh.
      unfold SHeapSpecM.assign, CHeapSpecM.assign.
      apply HPOST; wsimpl; eauto.
      hnf. unfold inst, inst_store, inst_env.
      now rewrite env.map_update.
    Qed.

  End State.
  Local Hint Resolve refine_eval_exp : core.
  Local Hint Resolve refine_eval_exps : core.
  Local Hint Resolve refine_pushpop : core.
  Local Hint Resolve refine_pushspops : core.
  Local Hint Resolve refine_debug : core.

  Local Hint Resolve refine_demonic : core.
  Local Hint Resolve refine_bind : core.
  Local Hint Resolve refine_angelic_ctx : core.
  (* Local Hint Resolve refine_bind_right : core. *)

  Lemma refine_produce_chunk {Γ} {w0 : World} (ι0 : Valuation w0)
    (Hpc0 : instpc (wco w0) ι0) :
    ℛ ι0 (@SHeapSpecM.produce_chunk Γ w0) (CHeapSpecM.produce_chunk).
  Proof.
    intros cs cc ->.
    intros POST__s POST__c HPOST.
    intros δs δc -> hs hc ->.
    unfold SHeapSpecM.produce_chunk, CHeapSpecM.produce_chunk.
    apply HPOST; cbn; rewrite ?inst_sub_id; auto.
    hnf. cbn. now rewrite peval_chunk_sound.
  Qed.

  Lemma refine_produce {Γ Σ0 pc0} (asn : Assertion Σ0) :
    let w0 := @MkWorld Σ0 pc0 in
    forall
      (ι0 : Valuation w0)
      (Hpc0 : instpc (wco w0) ι0),
      ℛ ι0 (@SHeapSpecM.produce Γ w0 asn) (CHeapSpecM.produce ι0 asn).
  Proof.
    induction asn; intros w0 * Hpc; cbn - [wctx Val].
    - now apply refine_box_assume_formula.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      now apply refine_produce_chunk.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      now apply refine_produce_chunk.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply refine_demonic_match_bool; eauto.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply refine_demonic_match_enum; auto.
      intros EK1 EK2 HEK. hnf in HEK. subst EK2.
      eauto.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply refine_demonic_match_sum; auto.
      + intros w2 ω12 ι2 -> Hpc2.
        intros t v ->.
        apply IHasn1; cbn - [inst sub_wk1]; wsimpl; auto.
      + intros w2 ω12 ι2 -> Hpc2.
        intros t v ->.
        apply IHasn2; cbn - [inst sub_wk1]; wsimpl; auto.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply refine_demonic_match_list; auto.
      eapply refine_four; eauto.
      intros w2 ω12 ι2 -> Hpc2.
      intros thead vhead ->.
      intros ttail vtail ->.
      apply IHasn2; cbn - [inst sub_wk1]; wsimpl; auto.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply refine_demonic_match_prod; auto.
      intros w2 ω12 ι2 -> Hpc2.
      intros t1 v1 -> t2 v2 ->.
      apply IHasn; cbn - [inst sub_wk1]; wsimpl; auto.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply refine_demonic_match_tuple; auto.
      intros w2 ω12 ι2 -> Hpc2.
      intros ts vs ->.
      apply IHasn; cbn - [Sub inst sub_wk1 sub_id sub_cat_left]; wsimpl; auto.
      { rewrite <- ?inst_subst.
        unfold NamedEnv.
        fold (@inst_sub Δ).
        fold (Sub Δ).
        rewrite <- inst_sub_cat.
        rewrite <- inst_subst.
        rewrite <- subst_sub_comp.
        rewrite sub_comp_cat_left.
        now rewrite ?inst_subst.
      }
      now rewrite inst_sub_cat, inst_subst.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply refine_demonic_match_record; auto.
      intros w2 ω12 ι2 -> Hpc2.
      intros ts vs ->.
      apply IHasn; cbn - [Sub inst sub_wk1 sub_id sub_cat_left]; wsimpl; auto.
      { rewrite <- ?inst_subst.
        unfold NamedEnv.
        fold (@inst_sub Δ).
        fold (Sub Δ).
        rewrite <- inst_sub_cat.
        rewrite <- inst_subst.
        rewrite <- subst_sub_comp.
        rewrite sub_comp_cat_left.
        now rewrite ?inst_subst.
      }
      now rewrite inst_sub_cat, inst_subst.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply refine_demonic_match_union; auto.
      intros UK.
      intros w2 ω12 ι2 -> Hpc2.
      intros ts vs ->.
      apply H; cbn - [Sub inst sub_wk1 sub_id sub_cat_left]; wsimpl; auto.
      { rewrite <- ?inst_subst.
        unfold NamedEnv.
        fold (@inst_sub (alt__ctx UK)).
        fold (Sub (alt__ctx UK)).
        rewrite <- inst_sub_cat.
        rewrite <- inst_subst.
        rewrite <- subst_sub_comp.
        rewrite sub_comp_cat_left.
        now rewrite ?inst_subst.
      }
      now rewrite inst_sub_cat, inst_subst.
    - intros w1 ω01 ι1 -> Hpc1.
      apply refine_bind; eauto.
      apply IHasn1; auto.
      intros ? ? ? -> ? _ _ _.
      apply IHasn2; auto.
      rewrite ?inst_sub_snoc, ?sub_acc_trans, ?inst_subst, ?inst_sub_wk1; eauto.
    - intros w1 ω01 ι1 -> Hpc1.
      apply refine_demonic_binary;
        try apply IHasn1; try apply IHasn2;
        cbn - [inst sub_wk1];
        rewrite ?inst_sub_snoc, ?sub_acc_trans, ?inst_subst, ?inst_sub_wk1; eauto.
    - intros w1 ω01 ι1 -> Hpc1.
      apply refine_bind.
      apply refine_demonic; auto.
      intros w2 ω02 ι2 -> Hpc2. intros t v ->.
      apply IHasn; cbn - [inst sub_wk1];
        rewrite ?inst_sub_snoc, ?sub_acc_trans, ?inst_subst, ?inst_sub_wk1; eauto.
    - intros w1 ω01 ι1 -> Hpc1.
      apply refine_debug; auto.
      apply refine_pure; auto.
  Qed.

  Lemma try_consume_chunk_exact_spec {Σ} (h : SHeap Σ) (c : Chunk Σ) :
    option.wlp
      (fun h' => List.In (c , h') (heap_extractions h))
      (SHeapSpecM.try_consume_chunk_exact h c).
  Proof.
    induction h as [|c' h].
    - now constructor.
    - cbn -[is_duplicable].
      destruct (chunk_eqb_spec c c').
      + constructor. left. subst.
        remember (is_duplicable c') as dup.
        destruct dup; reflexivity.
      + apply option.wlp_map. revert IHh.
        apply option.wlp_monotonic; auto.
        intros h' HIn. right.
        rewrite List.in_map_iff.
        exists (c,h'). auto.
  Qed.

  Lemma inst_is_duplicable {w : World} (c : Chunk w) (ι : Valuation w) :
    is_duplicable (inst c ι) = is_duplicable c.
  Proof.
    destruct c; now cbn.
  Qed.

  Lemma inst_eq_rect {I} {T : I -> LCtx -> Type} {A : I -> Type}
    {instTA : forall i, Inst (T i) (A i)} (i j : I) (e : j = i) :
    forall Σ (t : T j Σ) (ι : Valuation Σ),
      inst (eq_rect j (fun i => T i Σ) t i e) ι =
      eq_rect j A (inst t ι) i e.
  Proof. now destruct e. Qed.

  Lemma inst_eq_rect_r {I} {T : I -> LCtx -> Type} {A : I -> Type}
    {instTA : forall i, Inst (T i) (A i)} (i j : I) (e : i = j) :
    forall Σ (t : T j Σ) (ι : Valuation Σ),
      inst (eq_rect_r (fun i => T i Σ) t e) ι = eq_rect_r A (inst t ι) e.
  Proof. now destruct e. Qed.

  Lemma find_chunk_user_precise_spec {Σ p ΔI ΔO} (prec : 𝑯_Ty p = ΔI ▻▻ ΔO) (tsI : Env (Term Σ) ΔI) (tsO : Env (Term Σ) ΔO) (h : SHeap Σ) :
    option.wlp
      (fun '(h', eqs) =>
         forall ι : Valuation Σ, instpc eqs ι ->
           List.In
             (inst (chunk_user p (eq_rect_r (fun c : Ctx Ty => Env (Term Σ) c) (tsI ►► tsO) prec)) ι, inst h' ι)
             (heap_extractions (inst h ι)))
      (SHeapSpecM.find_chunk_user_precise prec tsI tsO h).
  Proof.
    induction h as [|c h]; [now constructor|]. cbn [SHeapSpecM.find_chunk_user_precise].
    destruct SHeapSpecM.match_chunk_user_precise as [eqs|] eqn:?.
    - clear IHh. constructor. intros ι Heqs. left.
      destruct c; try discriminate Heqo. cbn in *.
      destruct (eq_dec p p0); cbn in Heqo; try discriminate Heqo. destruct e.
      remember (eq_rect (𝑯_Ty p) (Env (Term Σ)) ts (ΔI ▻▻ ΔO) prec) as ts'.
      destruct (env.catView ts') as [tsI' tsO'].
      destruct (env.eqb_hom_spec Term_eqb (@Term_eqb_spec Σ) tsI tsI'); try discriminate.
      apply noConfusion_inv in Heqo. cbn in Heqo. subst.
      apply inst_formula_eqs_ctx in Heqs.
      rewrite (@inst_eq_rect_r (Ctx Ty) (fun Δ Σ => Env (Term Σ) Δ) (Env Val)).
      rewrite inst_env_cat. rewrite Heqs. rewrite <- inst_env_cat.
      change (env.cat ?A ?B) with (env.cat A B). rewrite Heqts'.
      rewrite (@inst_eq_rect (Ctx Ty) (fun Δ Σ => Env (Term Σ) Δ) (Env Val)).
      rewrite rew_opp_l. now destruct is_duplicable.
    - apply option.wlp_map. revert IHh. apply option.wlp_monotonic; auto.
      intros [h' eqs] HYP ι Heqs. specialize (HYP ι Heqs).
      remember (inst (chunk_user p (eq_rect_r (fun c0 : Ctx Ty => Env (Term Σ) c0) (tsI ►► tsO) prec)) ι) as c'.
      change (inst (cons c h) ι) with (cons (inst c ι) (inst h ι)).
      cbn [fst heap_extractions]. right. apply List.in_map_iff.
      eexists (c', inst h' ι); auto.
  Qed.

  Lemma find_chunk_ptsreg_precise_spec {Σ σ} (r : 𝑹𝑬𝑮 σ) (t : Term Σ σ) (h : SHeap Σ) :
    option.wlp
      (fun '(h', eqs) =>
         forall ι : Valuation Σ, instpc eqs ι ->
           List.In
             (inst (chunk_ptsreg r t) ι, inst h' ι)
             (heap_extractions (inst h ι)))
      (SHeapSpecM.find_chunk_ptsreg_precise r t h).
  Proof.
    induction h; cbn [SHeapSpecM.find_chunk_ptsreg_precise]; [now constructor|].
    destruct SHeapSpecM.match_chunk_ptsreg_precise eqn:?.
    - constructor. intros ι. rewrite inst_pathcondition_cons. intros [Hf Hpc].
      clear IHh. destruct a; cbn in Heqo; try discriminate Heqo.
      destruct (eq_dec_het r r0); try discriminate Heqo.
      dependent elimination e. cbn in Heqo. dependent elimination Heqo.
      change (inst (cons ?c ?h) ι) with (cons (inst c ι) (inst h ι)).
      cbn. left. f_equal. f_equal. symmetry. exact Hf.
    - apply option.wlp_map. revert IHh. apply option.wlp_monotonic; auto.
      intros [h' eqs] HYP ι Heqs. specialize (HYP ι Heqs).
      remember (inst (chunk_ptsreg r t) ι) as c'.
      change (inst (cons ?c ?h) ι) with (cons (inst c ι) (inst h ι)).
      cbn [fst heap_extractions]. right. apply List.in_map_iff.
      eexists (c', inst h' ι); auto.
  Qed.

  Lemma refine_consume_chunk {Γ} {w0 : World} (ι0 : Valuation w0)
    (Hpc0 : instpc (wco w0) ι0) :
    ℛ ι0 (@SHeapSpecM.consume_chunk Γ w0) (CHeapSpecM.consume_chunk).
  Proof.
    intros cs cc ->.
    unfold SHeapSpecM.consume_chunk, CHeapSpecM.consume_chunk.
    apply refine_bind.
    apply refine_get_heap; auto.
    intros w1 ω01 ι1 -> Hpc1.
    intros hs hc ->.
    remember (peval_chunk (persist cs ω01)) as c1.
    destruct (try_consume_chunk_exact_spec hs c1) as [h' HIn|].
    { intros POST__s POST__c HPOST.
      intros δs δc -> hs' hc' ->.
      unfold ℛ, RefineProp. intros Hwp.
      cbv [CHeapSpecM.assert_formula CHeapSpecM.assert_eq_chunk CHeapSpecM.bind
           SHeapSpecM.put_heap CHeapSpecM.put_heap CHeapSpecM.bind_right T
           CHeapSpecM.angelic_list CHeapSpecM.lift_purem ].
      rewrite CPureSpecM.wp_angelic_list.
      change (SHeap w1) in h'.
      exists (inst c1 ι1, inst h' ι1).
      split.
      - unfold inst at 3, inst_heap, inst_list.
        rewrite heap_extractions_map, List.in_map_iff.
        + exists (c1 , h'). split. reflexivity. assumption.
        + eauto using inst_is_duplicable.
      - rewrite CPureSpecM.wp_assert_eq_chunk. subst.
        rewrite peval_chunk_sound, inst_persist.
        split; auto. revert Hwp. apply HPOST; wsimpl; auto.
    }
    destruct (SHeapSpecM.try_consume_chunk_precise hs c1) as [[h' eqs]|] eqn:?.
    { intros POST__s POST__c HPOST.
      intros δs δc -> hs' hc' ->.
      unfold ℛ, RefineProp.
      cbv [SHeapSpecM.put_heap SHeapSpecM.bind_right T]. cbn. intros Hwp.
      eapply (refine_assert_formulas Hpc1 eqs) in Hwp; eauto. destruct Hwp as [Heqs HPOST1].
      cbv [CHeapSpecM.bind CHeapSpecM.put_heap CHeapSpecM.bind_right CHeapSpecM.assert_formula
           T CHeapSpecM.angelic_list CHeapSpecM.lift_purem].
      rewrite CPureSpecM.wp_angelic_list.
      destruct c1; cbn in Heqo; try discriminate Heqo; cbn.
      - destruct (𝑯_precise p) as [[ΔI ΔO prec]|]; try discriminate Heqo.
        remember (eq_rect (𝑯_Ty p) (Env (Term w1)) ts (ΔI ▻▻ ΔO) prec) as ts'.
        destruct (env.catView ts') as [tsI tsO].
        destruct (find_chunk_user_precise_spec prec tsI tsO hs) as [[h'' eqs''] HIn|];
          inversion Heqo; subst; clear Heqo.
        specialize (HIn ι1 Heqs). rewrite Heqts' in HIn.
        rewrite rew_opp_l in HIn. rewrite Heqc1 in HIn.
        rewrite peval_chunk_sound in HIn.
        eexists; split; eauto. clear HIn.
        hnf. rewrite CPureSpecM.wp_assert_eq_chunk.
        split; auto. now rewrite <- inst_persist.
      - destruct (find_chunk_ptsreg_precise_spec r t hs) as [[h'' eqs''] HIn|];
          inversion Heqo; subst; clear Heqo.
        specialize (HIn ι1 Heqs). rewrite Heqc1 in HIn.
        rewrite peval_chunk_sound in HIn.
        eexists; split; eauto. clear HIn.
        hnf. rewrite CPureSpecM.wp_assert_eq_chunk.
        split; auto. now rewrite <- inst_persist.
    }
    { intros POST__s POST__c HPOST.
      intros δs δc ? hs' hc' ? [].
    }
  Qed.

  Lemma refine_consume_chunk_angelic {Γ} {w0 : World} (ι0 : Valuation w0)
    (Hpc0 : instpc (wco w0) ι0) :
    ℛ ι0 (@SHeapSpecM.consume_chunk_angelic Γ w0) (CHeapSpecM.consume_chunk).
  Proof.
    intros cs cc ->.
    unfold SHeapSpecM.consume_chunk_angelic, CHeapSpecM.consume_chunk.
    apply refine_bind.
    apply refine_get_heap; auto.
    intros w1 ω01 ι1 -> Hpc1.
    intros hs hc ->.
    remember (peval_chunk (persist cs ω01)) as c1.
    destruct (try_consume_chunk_exact_spec hs c1) as [h' HIn|].
    { intros POST__s POST__c HPOST.
      intros δs δc -> hs' hc' ->.
      unfold ℛ, RefineProp. intros Hwp.
      cbv [SHeapSpecM.put_heap CHeapSpecM.bind CHeapSpecM.put_heap CHeapSpecM.bind_right CHeapSpecM.assert_formula
                         T CHeapSpecM.angelic_list CHeapSpecM.lift_purem].
      rewrite CPureSpecM.wp_angelic_list.
      change (SHeap w1) in h'.
      exists (inst c1 ι1, inst h' ι1).
      split.
      - unfold inst at 3, inst_heap, inst_list.
        rewrite heap_extractions_map, List.in_map_iff.
        + exists (c1 , h'). split. reflexivity. assumption.
        + eauto using inst_is_duplicable.
      - hnf. subst. rewrite peval_chunk_sound, inst_persist.
        rewrite CPureSpecM.wp_assert_eq_chunk.
        split; auto. revert Hwp. apply HPOST; wsimpl; auto.
    }
    destruct (SHeapSpecM.try_consume_chunk_precise hs c1) as [[h' eqs]|] eqn:?.
    { intros POST__s POST__c HPOST.
      intros δs δc -> hs' hc' ->.
      unfold ℛ, RefineProp.
      cbv [SHeapSpecM.put_heap SHeapSpecM.bind_right T]. cbn. intros Hwp.
      eapply (refine_assert_formulas Hpc1 eqs) in Hwp; eauto. destruct Hwp as [Heqs HPOST1].
      cbv [CHeapSpecM.bind CHeapSpecM.put_heap CHeapSpecM.bind_right CHeapSpecM.assert_formula
           T CHeapSpecM.angelic_list CHeapSpecM.lift_purem].
      rewrite CPureSpecM.wp_angelic_list.
      destruct c1; cbn in Heqo; try discriminate Heqo; cbn.
      - destruct (𝑯_precise p) as [[ΔI ΔO prec]|]; try discriminate Heqo.
        remember (eq_rect (𝑯_Ty p) (Env (Term w1)) ts (ΔI ▻▻ ΔO) prec) as ts'.
        destruct (env.catView ts') as [tsI tsO].
        destruct (find_chunk_user_precise_spec prec tsI tsO hs) as [[h'' eqs''] HIn|];
          inversion Heqo; subst; clear Heqo.
        specialize (HIn ι1 Heqs). rewrite Heqts' in HIn.
        rewrite rew_opp_l in HIn. rewrite Heqc1 in HIn.
        rewrite peval_chunk_sound in HIn.
        eexists; split; eauto. clear HIn.
        hnf. rewrite CPureSpecM.wp_assert_eq_chunk.
        split; auto. now rewrite <- inst_persist.
      - destruct (find_chunk_ptsreg_precise_spec r t hs) as [[h'' eqs''] HIn|];
          inversion Heqo; subst.
        specialize (HIn ι1 Heqs). rewrite Heqc1 in HIn.
        rewrite peval_chunk_sound in HIn.
        eexists; split; eauto. clear HIn.
        hnf. rewrite CPureSpecM.wp_assert_eq_chunk.
        split; auto. now rewrite <- inst_persist.
    }
    { apply refine_bind.
      apply refine_angelic_list; eauto.
      { hnf. unfold inst at 1, inst_heap, inst_list.
        rewrite heap_extractions_map.
        apply List.map_ext. now intros [].
        eauto using inst_is_duplicable.
      }
      clear Heqo.
      intros w2 ω12 ι2 -> Hpc2.
      intros [cs' hs'] [cc' hc']. intros Hch'.
      inversion Hch'; subst; clear Hch'.
      apply refine_bind.
      - apply refine_assert_eq_chunk; auto. hnf.
        now rewrite inst_persist, peval_chunk_sound, inst_persist.
      - intros w3 ω23 ι3 -> Hpc3 _ _ _.
        apply refine_put_heap; auto.
        now rewrite <- inst_persist.
    }
  Qed.

  Lemma refine_consume {Γ Σ0 pc0} (asn : Assertion Σ0) :
    let w0 := @MkWorld Σ0 pc0 in
    forall
      (ι0 : Valuation w0)
      (Hpc0 : instpc (wco w0) ι0),
      ℛ ι0 (@SHeapSpecM.consume Γ w0 asn) (CHeapSpecM.consume ι0 asn).
  Proof.
    induction asn; intros w0 * Hpc; cbn - [wctx Val].
    - now apply refine_box_assert_formula.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      now apply refine_consume_chunk.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      now apply refine_consume_chunk_angelic.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply refine_angelic_match_bool; eauto.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply refine_angelic_match_enum; auto.
      intros EK1 EK2 HEK. hnf in HEK. subst EK2.
      eauto.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply refine_angelic_match_sum; auto.
      + intros w2 ω12 ι2 -> Hpc2.
        intros t v ->.
        apply IHasn1; cbn - [inst sub_wk1]; wsimpl; auto.
      + intros w2 ω12 ι2 -> Hpc2.
        intros t v ->.
        apply IHasn2; cbn - [inst sub_wk1]; wsimpl; auto.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply refine_angelic_match_list; auto.
      eapply refine_four; eauto.
      intros w2 ω12 ι2 -> Hpc2.
      intros thead vhead ->.
      intros ttail vtail ->.
      apply IHasn2; cbn - [inst sub_wk1]; wsimpl; auto.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply refine_angelic_match_prod; auto.
      intros w2 ω12 ι2 -> Hpc2.
      intros t1 v1 -> t2 v2 ->.
      apply IHasn; cbn - [inst sub_wk1]; wsimpl; auto.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply refine_angelic_match_tuple; auto.
      intros w2 ω12 ι2 -> Hpc2.
      intros ts vs ->.
      apply IHasn; cbn - [Sub inst sub_wk1 sub_id sub_cat_left]; wsimpl; auto.
      { rewrite <- ?inst_subst.
        unfold NamedEnv.
        fold (@inst_sub Δ).
        fold (Sub Δ).
        rewrite <- inst_sub_cat.
        rewrite <- inst_subst.
        rewrite <- subst_sub_comp.
        rewrite sub_comp_cat_left.
        now rewrite ?inst_subst.
      }
      now rewrite inst_sub_cat, inst_subst.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply refine_angelic_match_record; auto.
      intros w2 ω12 ι2 -> Hpc2.
      intros ts vs ->.
      apply IHasn; cbn - [Sub inst sub_wk1 sub_id sub_cat_left]; wsimpl; auto.
      { rewrite <- ?inst_subst.
        unfold NamedEnv.
        fold (@inst_sub Δ).
        fold (Sub Δ).
        rewrite <- inst_sub_cat.
        rewrite <- inst_subst.
        rewrite <- subst_sub_comp.
        rewrite sub_comp_cat_left.
        now rewrite ?inst_subst.
      }
      now rewrite inst_sub_cat, inst_subst.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply refine_angelic_match_union; auto.
      intros UK.
      intros w2 ω12 ι2 -> Hpc2.
      intros ts vs ->.
      apply H; cbn - [Sub inst sub_wk1 sub_id sub_cat_left]; wsimpl; auto.
      { rewrite <- ?inst_subst.
        unfold NamedEnv.
        fold (@inst_sub (alt__ctx UK)).
        fold (Sub (alt__ctx UK)).
        rewrite <- inst_sub_cat.
        rewrite <- inst_subst.
        rewrite <- subst_sub_comp.
        rewrite sub_comp_cat_left.
        now rewrite ?inst_subst.
      }
      now rewrite inst_sub_cat, inst_subst.
    - intros w1 ω01 ι1 -> Hpc1.
      apply refine_bind; eauto.
      apply IHasn1; auto.
      intros ? ? ? -> ? _ _ _.
      apply IHasn2; auto.
      rewrite ?inst_sub_snoc, ?sub_acc_trans, ?inst_subst, ?inst_sub_wk1; eauto.
    - intros w1 ω01 ι1 -> Hpc1.
      apply refine_angelic_binary;
        try apply IHasn1; try apply IHasn2;
        cbn - [inst sub_wk1];
        rewrite ?inst_sub_snoc, ?sub_acc_trans, ?inst_subst, ?inst_sub_wk1; eauto.
    - intros w1 ω01 ι1 -> Hpc1.
      apply refine_bind.
      apply refine_angelic; auto.
      intros w2 ω02 ι2 -> Hpc2. intros t v ->.
      apply IHasn; cbn - [inst sub_wk1];
        rewrite ?inst_sub_snoc, ?sub_acc_trans, ?inst_subst, ?inst_sub_wk1; eauto.
    - intros w1 ω01 ι1 -> Hpc1.
      apply refine_debug; auto.
      apply refine_pure; auto.
  Qed.

  Lemma refine_call_contract {Γ Δ : PCtx} {τ : Ty} (c : SepContract Δ τ) :
    forall {w0 : World} {ι0 : Valuation w0} (Hpc0 : instpc (wco w0) ι0),
      ℛ ι0 (@SHeapSpecM.call_contract Γ Δ τ c w0) (@CHeapSpecM.call_contract Γ Δ τ c).
  Proof.
    destruct c; cbv [SHeapSpecM.call_contract CHeapSpecM.call_contract].
    intros w0 ι0 Hpc0.
    intros args__s args__c Hargs.
    apply refine_bind; auto.
    intros w1 ω01 ι1 -> Hpc1.
    intros evars__s evars__c Hevars.
    apply refine_bind.
    { apply refine_assert_eq_nenv; auto; hnf.
      now rewrite Hevars, inst_subst.
      now rewrite Hargs, inst_persist.
    }
    intros w2 ω12 ι2 -> Hpc2 _ _ _.
    apply refine_bind.
    { apply refine_consume; wsimpl; auto.
      constructor.
    }
    intros w3 ω23 ι3 -> Hpc3 _ _ _.
    apply refine_bind.
    { apply refine_demonic; auto. }
    intros w4 ω34 ι4 -> Hpc4.
    intros res__s res__c Hres.
    apply refine_bind.
    { apply refine_produce; auto.
      constructor.
      cbn - [inst_env sub_snoc].
      rewrite inst_sub_snoc, inst_persist, ?sub_acc_trans, ?inst_subst.
      now rewrite Hevars, Hres.
    }
    intros w5 ω45 ι5 -> Hpc5 _ _ _.
    apply refine_pure; auto.
    rewrite Hres. rewrite <- inst_persist.
    reflexivity.
  Qed.

  Lemma refine_call_lemma {Γ Δ : PCtx} (lem : Lemma Δ) :
    forall {w0 : World} {ι0 : Valuation w0} (Hpc0 : instpc (wco w0) ι0),
      ℛ ι0 (@SHeapSpecM.call_lemma Γ Δ lem w0) (@CHeapSpecM.call_lemma Γ Δ lem).
  Proof.
    destruct lem; cbv [SHeapSpecM.call_lemma CHeapSpecM.call_lemma].
    intros w0 ι0 Hpc0.
    intros args__s args__c Hargs.
    apply refine_bind; auto.
    intros w1 ω01 ι1 -> Hpc1.
    intros evars__s evars__c Hevars.
    apply refine_bind.
    apply refine_assert_formulas; auto.
    { rewrite inst_formula_eqs_nctx.
      rewrite inst_persist, inst_subst.
      rewrite Hargs, Hevars.
      reflexivity.
    }
    intros w2 ω12 ι2 -> Hpc2 _ _ _.
    apply refine_bind.
    { apply refine_consume; wsimpl; auto.
      constructor.
    }
    intros w3 ω23 ι3 -> Hpc3 _ _ _.
    { apply refine_produce; auto.
      constructor.
      cbn - [inst_env sub_snoc].
      rewrite inst_persist, sub_acc_trans, inst_subst.
      now rewrite Hevars.
    }
  Qed.

  Definition ExecRefine (sexec : SHeapSpecM.Exec) (cexec : CHeapSpecM.Exec) :=
    forall Γ τ (s : Stm Γ τ) (w0 : World) (ι0 : Valuation w0) (Hpc0 : instpc (wco w0) ι0),
    ℛ ι0 (@sexec Γ τ s w0) (cexec Γ τ s).

  Lemma refine_exec_aux {cfg} srec crec (HYP : ExecRefine srec crec) :
    ExecRefine (@SHeapSpecM.exec_aux cfg srec) (@CHeapSpecM.exec_aux crec).
  Proof.
    unfold ExecRefine.
    induction s; cbn; intros * ?.
    - apply refine_pure; auto.
    - now apply refine_eval_exp.
    - apply refine_bind; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v Htv.
      apply refine_pushpop; auto.
    - apply refine_pushspops; auto.
      apply refine_lift.
    - apply refine_bind; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v ->.
      apply refine_bind.
      apply refine_assign; auto.
      intros w2 ω12 ι2 -> Hpc2 _ _ _.
      apply refine_pure; auto.
      hnf in H. now rewrite <- inst_persist in H.
    - apply refine_bind.
      apply refine_eval_exps; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros args__s args__c Hargs.
      destruct (CEnv f).
      + unfold SHeapSpecM.call_contract_debug.
        destruct (config_debug_function cfg f).
        apply refine_debug; auto.
        apply refine_call_contract; auto.
        apply refine_call_contract; auto.
      + intros POST__s POST__c HPOST.
        intros δs1 δc1 ->.
        apply HYP; auto.
        intros w2 ω12 ι2 -> Hpc2.
        intros t v ->.
        intros _ _ _.
        apply HPOST; auto.
        rewrite <- inst_persist.
        reflexivity.
    - apply refine_bind.
      apply refine_get_local; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros δs1 δc1 ->.
      apply refine_bind.
      apply refine_put_local; auto.
      apply refine_lift.
      intros w2 ω12 ι2 -> Hpc2 _ _ _.
      apply refine_bind; auto.
      intros w3 ω23 ι3 -> Hpc3.
      intros t v ->.
      apply refine_bind.
      apply refine_put_local; auto.
      rewrite persist_subst.
      hnf. rewrite sub_acc_trans, ?inst_subst; auto.
      intros w4 ω34 ι4 -> Hpc4 _ _ _.
      rewrite <- inst_persist.
      apply refine_pure; auto.
    - apply refine_bind.
      apply refine_eval_exps; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros args__s args__c Hargs.
      apply refine_call_contract; auto.
    - apply refine_bind.
      apply refine_eval_exps; auto.
      intros w1 ω01 ι1 -> Hpc1 δΔ ? ->.
      apply refine_bind.
      apply refine_call_lemma; auto.
      intros w2 ω12 ι2 -> Hpc2 _ _ _; auto.
    - apply refine_bind.
      intros POST__s POST__c HPOST.
      apply refine_eval_exp; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v Htv.
      apply refine_demonic_match_bool; auto.
    - apply refine_bind; auto.
      intros ? ? ? -> ? _ _ _; auto.
    - apply refine_bind; auto.
      intros POST__s POST__c HPOST.
      apply refine_eval_exp; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v ->.
      apply refine_bind.
      apply refine_assume_formula; auto.
      intros w2 ω12 ι2 -> Hpc2 _ _ _.
      now apply IHs.
    - apply refine_block.
    - apply refine_bind; auto.
      intros POST__s POST__c HPOST.
      apply refine_eval_exp; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v Htv.
      apply refine_demonic_match_list; auto.
      intros w2 ω12 ι2 -> Hpc2.
      intros thead vhead ->.
      intros ttail vtail ->.
      apply refine_pushspops; auto.
    - apply refine_bind; auto.
      intros POST__s POST__c HPOST.
      apply refine_eval_exp; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v Htv.
      apply refine_demonic_match_sum; auto.
      + intros w2 ω12 ι2 -> Hpc2.
        intros tl vl ->.
        apply refine_pushpop; auto.
      + intros w2 ω12 ι2 -> Hpc2.
        intros tr vr ->.
        apply refine_pushpop; auto.
    - apply refine_bind; auto.
      intros POST__s POST__c HPOST.
      apply refine_eval_exp; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v Htv.
      apply refine_demonic_match_prod; auto.
      intros w2 ω12 ι2 -> Hpc2.
      intros t1 v1 ->.
      intros t2 v2 ->.
      apply refine_pushspops; auto.
    - apply refine_bind; auto.
      intros POST__s POST__c HPOST.
      apply refine_eval_exp; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v Htv.
      apply refine_demonic_match_enum; auto.
      intros EK1 EK2 ->.
      intros w2 ω12 ι2 -> Hpc2; auto.
    - apply refine_bind; auto.
      intros POST__s POST__c HPOST.
      apply refine_eval_exp; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v Htv.
      apply refine_demonic_match_tuple; auto.
      intros w2 ω12 ι2 -> Hpc2.
      intros ts vs Htvs.
      apply refine_pushspops; auto.
    - apply refine_bind; auto.
      intros POST__s POST__c HPOST.
      apply refine_eval_exp; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v Htv.
      apply refine_demonic_match_union; auto.
      intros UK.
      intros w2 ω12 ι2 -> Hpc2.
      intros ts vs Htvs.
      apply refine_pushspops; auto.
    - apply refine_bind; auto.
      intros POST__s POST__c HPOST.
      apply refine_eval_exp; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v Htv.
      apply refine_demonic_match_record; auto.
      intros w2 ω12 ι2 -> Hpc2.
      intros ts vs Htvs.
      apply refine_pushspops; auto.
    - apply refine_bind; auto.
      intros POST__s POST__c HPOST.
      apply refine_eval_exp; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v Htv.
      apply refine_demonic_match_bvec; auto.
      intros v1 v2 ->.
      intros w2 ω12 ι2 -> Hpc2.
      auto.
    - apply refine_bind; auto.
      apply refine_angelic; auto.
      intros w1 ω01 ι1 -> Hpc1 t v Htv. hnf in Htv; subst.
      apply refine_bind; auto.
      apply refine_consume_chunk; auto.
      intros w2 ω12 ι2 -> Hpc2 _ _ _.
      apply refine_bind; auto.
      apply refine_produce_chunk; auto.
      rewrite <- inst_persist; auto.
      intros w3 ω23 ι3 -> Hpc3 _ _ _.
      apply refine_pure; auto. hnf.
      rewrite (persist_trans (A := STerm _)).
      now rewrite <- ?inst_persist.
    - apply refine_bind; auto.
      apply refine_angelic; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros told v ->.
      apply refine_bind; auto.
      apply refine_consume_chunk; auto.
      intros w2 ω12 ι2 -> Hpc2 _ _ _.
      apply refine_bind; auto.
      intros w3 ω23 ι3 -> Hpc3.
      intros tnew v Htnew. hnf in Htnew. subst v.
      apply refine_bind; auto.
      apply refine_produce_chunk; auto.
      intros w4 ω34 ι4 -> Hpc4 _ _ _.
      apply refine_pure; auto.
      now rewrite <- inst_persist.
    - apply refine_error.
    - apply refine_debug; auto.
  Qed.

  Lemma refine_exec {cfg n} :
    ExecRefine (@SHeapSpecM.exec cfg n) (@CHeapSpecM.exec n).
  Proof.
    induction n; cbn.
    - unfold ExecRefine. intros.
      intros POST__s POST__c HPOST.
      intros δs1 δc1 Hδ hs1 hc1 Hh.
      hnf. contradiction.
    - now apply refine_exec_aux.
  Qed.

  Lemma refine_exec_contract {cfg : Config} n {Γ τ} (c : SepContract Γ τ) (s : Stm Γ τ) :
    let w0 := {| wctx := sep_contract_logic_variables c; wco := nil |} in
    forall (ι0 : Valuation w0),
      ℛ (w := w0) ι0 (@SHeapSpecM.exec_contract cfg n Γ τ c s) (@CHeapSpecM.exec_contract n Γ τ c s ι0).
  Proof.
    unfold SHeapSpecM.exec_contract, CHeapSpecM.exec_contract; destruct c as [Σ δ pre result post]; cbn in *.
    intros ι0.
    apply refine_bind.
    apply refine_produce; wsimpl; cbn; auto.
    intros w1 ω01 ι1 -> Hpc1 _ _ _.
    apply refine_bind.
    apply refine_exec; auto.
    intros w2 ω12 ι2 -> Hpc2.
    intros res__s res__c Hres.
    apply refine_consume; cbn - [inst]; wsimpl; auto.
    constructor.
    f_equal; auto.
  Qed.

  Lemma refine_demonic_close {w : World} (P : 𝕊 w) (p : Valuation w -> Prop) :
    (forall (ι : Valuation w), ℛ ι P (p ι)) ->
    ℛ (w := wnil) env.nil (demonic_close P) (ForallNamed p).
  Proof.
    unfold ℛ, RefineProp, ForallNamed. intros HYP Hwp.
    rewrite env.Forall_forall. intros ι.
    apply HYP. revert Hwp. clear.
    rewrite ?wsafe_safe, ?safe_debug_safe.
    intros Hwp. now apply safe_demonic_close.
  Qed.

  Lemma refine_vcgen {Γ τ} n (c : SepContract Γ τ) (body : Stm Γ τ) :
    ℛ (w := wnil) env.nil (SHeapSpecM.vcgen default_config n c body) (CHeapSpecM.vcgen n c body).
  Proof.
    unfold SHeapSpecM.vcgen, CHeapSpecM.vcgen.
    apply (refine_demonic_close
             (w := {| wctx := sep_contract_logic_variables c; wco := nil |})).
    intros ι.
    apply refine_exec_contract; auto.
    now intros w1 ω01 ι1 -> Hpc1.
  Qed.

  Lemma symbolic_vcgen_soundness {Γ τ} (c : SepContract Γ τ) (body : Stm Γ τ) :
    Symbolic.ValidContract c body ->
    Shallow.ValidContract c body.
  Proof.
    unfold Symbolic.ValidContract. intros [Hwp%postprocess_sound].
    apply refine_vcgen. now rewrite wsafe_safe, safe_debug_safe.
  Qed.

  (* Print Assumptions symbolic_vcgen_soundness. *)

End Soundness.
