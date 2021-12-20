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
     Arith.PeanoNat
     Bool.Bool
     Classes.Morphisms
     Classes.Morphisms_Prop
     Classes.Morphisms_Relations
     Classes.RelationClasses
     Relations.Relation_Definitions
     Lists.List
     Program.Tactics
     Strings.String
     ZArith.ZArith
     micromega.Lia.
From Coq Require
     Classes.CRelationClasses.
From Equations Require Import Equations.

From Katamaran Require Import
     Sep.Spec
     Syntax.

From stdpp Require
     base.

Import CtxNotations.
Import EnvNotations.
Import ListNotations.

Set Implicit Arguments.

Delimit Scope mutator_scope with mut.
Delimit Scope smut_scope with smut.

Module Mutators
       (termkit : TermKit)
       (progkit : ProgramKit termkit)
       (assertkit : AssertionKit termkit progkit)
       (symcontractkit : SymbolicContractKit termkit progkit assertkit).

  Export symcontractkit.
  Import Entailment.
  Import ModalNotations.
  Open Scope modal.

  Module WorldInstance.

    Record WInstance (w : World) : Set :=
      MkWInstance
        { ιassign :> SymInstance w;
          ιvalid  : instpc (wco w) ιassign;
        }.

    Program Definition winstance_formula {w} (ι : WInstance w) (fml : Formula w) (p : inst (A := Prop) fml ι) :
      WInstance (wformula w fml) :=
      {| ιassign := ι; |}.
    Next Obligation.
    Proof.
      intros. cbn.
      apply inst_pathcondition_cons. split; auto.
      apply ιvalid.
    Qed.

    Program Definition winstance_snoc {w} (ι : WInstance w) {b : 𝑺 ∷ Ty} (v : Lit (type b)) :
      WInstance (wsnoc w b) :=
      {| ιassign := env_snoc (ιassign ι) b v; |}.
    Next Obligation.
    Proof.
      intros. unfold wsnoc. cbn [wctx wco].
      rewrite inst_subst, inst_sub_wk1.
      apply ιvalid.
    Qed.

    (* Fixpoint winstance_cat {Σ} (ι : WInstance Σ) {Δ} (ιΔ : SymInstance Δ) : *)
    (*   WInstance (wcat Σ Δ). *)
    (* Proof. *)
    (*   destruct ιΔ; cbn. *)
    (*   - apply ι. *)
    (*   - apply winstance_snoc. *)
    (*     apply winstance_cat. *)
    (*     apply ι. *)
    (*     apply ιΔ. *)
    (*     apply db. *)
    (* Defined. *)

    Program Definition winstance_subst {w} (ι : WInstance w) {x σ} {xIn : x∷σ ∈ w}
      (t : Term (w - x∷σ) σ) (p : inst t (env_remove (x∷σ) (ιassign ι) xIn) = env_lookup (ιassign ι) xIn) :
      WInstance (wsubst w x t) :=
      @MkWInstance (wsubst w x t) (env_remove _ (ιassign ι) xIn) _.
    Next Obligation.
      intros * p. cbn. rewrite inst_subst, <- inst_sub_shift in *.
      rewrite inst_sub_single_shift; auto using ιvalid.
    Qed.

    Program Definition instacc {w0 w1} (ω01 : w0 ⊒ w1) : WInstance w1 -> WInstance w0 :=
      match ω01 in (_ ⊒ w) return (WInstance w -> WInstance w0) with
      | acc_refl            => fun ι => ι
      | @acc_sub _ w1 ζ ent => fun ι1 => {| ιassign := inst ζ ι1; |}
      end.
    Next Obligation.
    Proof.
      intros. specialize (ent ι1).
      rewrite <- inst_subst.
      apply ent.
      apply ιvalid.
    Qed.

  End WorldInstance.

  Definition valid_box {A} :
    (⊢ A) -> (⊢ □A) :=
    fun a w0 w1 ω01 => a w1.
  Global Arguments valid_box {A} a {w} [w1].

  Definition PROP : TYPE :=
    fun _ => Prop.


  Import SymProp.

  Module Postprocessing.

    Definition angelic_binary_prune {Σ} (p1 p2 : 𝕊 Σ) : 𝕊 Σ :=
      match p1 , p2 with
      | block   , _       => block
      | _       , block   => block
      | error _ , _       => p2
      | _       , error _ => p1
      | _       , _       => angelic_binary p1 p2
      end.

    Definition demonic_binary_prune {Σ} (p1 p2 : 𝕊 Σ) : 𝕊 Σ :=
      match p1 , p2 with
      | block   , _       => p2
      | _       , block   => p1
      | error s , _       => error s
      | _       , error s => error s
      | _       , _       => demonic_binary p1 p2
      end.

    Definition assertk_prune {Σ} (fml : Formula Σ) (msg : Message Σ) (p : 𝕊 Σ) : 𝕊 Σ :=
      match p with
      | error s => @error Σ s
      | _       => assertk fml msg p
      end.
    Global Arguments assertk_prune {Σ} fml msg p.

    Definition assumek_prune {Σ} (fml : Formula Σ) (p : 𝕊 Σ) : 𝕊 Σ :=
      match p with
      | block => block
      | _     => assumek fml p
      end.
    Global Arguments assumek_prune {Σ} fml p.

    Definition angelicv_prune {Σ} b (p : 𝕊 (Σ ▻ b)) : 𝕊 Σ :=
      match p with
      | error msg => error (EMsgThere msg)
      | _         => angelicv b p
      end.

    Definition demonicv_prune {Σ} b (p : 𝕊 (Σ ▻ b)) : 𝕊 Σ :=
      (* match @occurs_check_spath AT _ (Σ ▻ b) b inctx_zero o with *)
      (* | Some o => o *)
      (* | None   => demonicv b o *)
      (* end. *)
      match p with
      | block => block
      | _     => demonicv b p
      end.

    Definition assume_vareq_prune {Σ} {x σ} {xIn : x∷σ ∈ Σ}
      (t : Term (Σ - x∷σ) σ) (k : 𝕊 (Σ - x∷σ)) : 𝕊 Σ :=
      match k with
      | block => block
      | _     => assume_vareq x t k
      end.
    Global Arguments assume_vareq_prune {Σ} x {σ xIn} t k.

    Definition assert_vareq_prune {Σ} {x σ} {xIn : x∷σ ∈ Σ}
      (t : Term (Σ - x∷σ) σ) (msg : Message (Σ - x∷σ)) (k : 𝕊 (Σ - x∷σ)) : 𝕊 Σ :=
      match k with
      | error emsg => error (shift_emsg xIn emsg)
      | _          => assert_vareq x t msg k
      end.
    Global Arguments assert_vareq_prune {Σ} x {σ xIn} t msg k.

    Fixpoint prune {Σ} (p : 𝕊 Σ) : 𝕊 Σ :=
      match p with
      | error msg => error msg
      | block => block
      | angelic_binary o1 o2 =>
        angelic_binary_prune (prune o1) (prune o2)
      | demonic_binary o1 o2 =>
        demonic_binary_prune (prune o1) (prune o2)
      | assertk fml msg o =>
        assertk_prune fml msg (prune o)
      | assumek fml o =>
        assumek_prune fml (prune o)
      | angelicv b o =>
        angelicv_prune (prune o)
      | demonicv b o =>
        demonicv_prune (prune o)
      | assert_vareq x t msg k =>
        assert_vareq_prune x t msg (prune k)
      | assume_vareq x t k =>
        assume_vareq_prune x t (prune k)
      | debug d k =>
        debug d (prune k)
      end.

    Lemma prune_angelic_binary_sound {Σ} (p1 p2 : 𝕊 Σ) (ι : SymInstance Σ) :
      safe (angelic_binary_prune p1 p2) ι <-> safe (angelic_binary p1 p2) ι.
    Proof.
      destruct p1; cbn; auto.
      - destruct p2; cbn; auto; intuition.
      - destruct p2; cbn; auto; intuition.
      - destruct p2; cbn; auto; intuition.
      - intuition.
      - destruct p2; cbn; auto;
          rewrite ?obligation_equiv; intuition.
      - destruct p2; cbn; auto; intuition.
      - destruct p2; cbn; auto; intuition.
      - destruct p2; cbn; auto; intuition.
      - destruct p2; cbn; auto;
          rewrite ?obligation_equiv; intuition.
      - destruct p2; cbn; auto; intuition.
      - destruct p2; cbn; auto; intuition.
    Qed.

    Lemma prune_demonic_binary_sound {Σ} (p1 p2 : 𝕊 Σ) (ι : SymInstance Σ) :
      safe (demonic_binary_prune p1 p2) ι <-> safe (demonic_binary p1 p2) ι.
    Proof.
      destruct p1; cbn; auto.
      - destruct p2; cbn; auto; intuition.
      - destruct p2; cbn; auto; intuition.
      - destruct p2; cbn; auto; intuition.
      - intuition.
      - destruct p2; cbn; auto;
          rewrite ?obligation_equiv; intuition.
      - destruct p2; cbn; auto; intuition.
      - destruct p2; cbn; auto; intuition.
      - destruct p2; cbn; auto; intuition.
      - destruct p2; cbn; auto;
          rewrite ?obligation_equiv; intuition.
      - destruct p2; cbn; auto; intuition.
      - destruct p2; cbn; auto; intuition.
    Qed.

    Lemma prune_assertk_sound {Σ} fml msg (p : 𝕊 Σ) (ι : SymInstance Σ) :
      safe (assertk_prune fml msg p) ι <-> safe (assertk fml msg p) ι.
    Proof. destruct p; cbn; rewrite ?obligation_equiv; auto; intuition. Qed.

    Lemma prune_assumek_sound {Σ} fml (p : 𝕊 Σ) (ι : SymInstance Σ) :
      safe (assumek_prune fml p) ι <-> safe (assumek fml p) ι.
    Proof. destruct p; cbn; auto; intuition. Qed.

    Lemma prune_angelicv_sound {Σ b} (p : 𝕊 (Σ ▻ b)) (ι : SymInstance Σ) :
      safe (angelicv_prune p) ι <-> safe (angelicv b p) ι.
    Proof. destruct p; cbn; auto; firstorder. Qed.

    Lemma prune_demonicv_sound {Σ b} (p : 𝕊 (Σ ▻ b)) (ι : SymInstance Σ) :
      safe (demonicv_prune p) ι <-> safe (demonicv b p) ι.
    Proof. destruct p; cbn; auto; intuition. Qed.

    Lemma prune_assert_vareq_sound {Σ x σ} {xIn : x∷σ ∈ Σ}
      (t : Term (Σ - x∷σ) σ) (msg : Message (Σ - x∷σ)) (p : 𝕊 (Σ - x∷σ)) (ι : SymInstance Σ) :
      safe (assert_vareq_prune x t msg p) ι <-> safe (assert_vareq x t msg p) ι.
    Proof. destruct p; cbn; auto; intuition. Qed.

    Lemma prune_assume_vareq_sound {Σ x σ} {xIn : x∷σ ∈ Σ}
      (t : Term (Σ - x∷σ) σ) (p : 𝕊 (Σ - x∷σ)) (ι : SymInstance Σ) :
      safe (assume_vareq_prune x t p) ι <-> safe (assume_vareq x t p) ι.
    Proof. destruct p; cbn; auto; intuition. Qed.

    Lemma prune_sound {Σ} (p : 𝕊 Σ) (ι : SymInstance Σ) :
      safe (prune p) ι <-> safe p ι.
    Proof.
      induction p; cbn [prune safe].
      - rewrite prune_angelic_binary_sound; cbn.
        now rewrite IHp1, IHp2.
      - rewrite prune_demonic_binary_sound; cbn.
        now rewrite IHp1, IHp2.
      - auto.
      - auto.
      - rewrite prune_assertk_sound; cbn.
        now rewrite IHp.
      - rewrite prune_assumek_sound; cbn.
        now rewrite IHp.
      - rewrite prune_angelicv_sound; cbn.
        apply base.exist_proper; intros.
        now rewrite IHp.
      - rewrite prune_demonicv_sound; cbn.
        apply base.forall_proper; intros.
        now rewrite IHp.
      - rewrite prune_assert_vareq_sound; cbn.
        now rewrite IHp.
      - rewrite prune_assume_vareq_sound; cbn.
        now rewrite IHp.
      - now rewrite ?debug_equiv.
    Qed.

    Section Util.

      Arguments InCtx_rect [_ _].
      Lemma ctx_remove_inctx_right {B : Set} {Γ Δ : Ctx B} {b : B} (bIn : InCtx b Δ) :
        @ctx_remove B (@ctx_cat B Γ Δ) b (@inctx_cat_right B b Γ Δ bIn) =
        @ctx_cat B Γ (@ctx_remove B Δ b bIn).
      Proof.
        induction bIn using InCtx_rect; cbn.
        - reflexivity.
        - f_equal. auto.
      Defined.

      Lemma exists_and {A : Type} {P : A -> Prop} {Q : Prop} :
        (exists (x : A), P x /\ Q) <-> ((exists (x : A), P x) /\ Q).
      Proof. firstorder. Qed.

      Lemma safe_eq_rect {Σ Σ'} (eq : Σ = Σ') (p : 𝕊 Σ) (ι : SymInstance Σ') :
        safe (eq_rect Σ 𝕊 p Σ' eq) ι = safe p (eq_rect Σ' (fun Σ => SymInstance Σ) ι Σ (eq_sym eq)).
      Proof.
        now destruct eq.
      Qed.

      (* Lemma env_insert_remove {x : 𝑺} {σ : Ty} {Σ0 Σe : LCtx} *)
      (*       (bIn : x :: σ ∈ Σe) : *)
      (*   env_insert bIn *)
      (*     (inst t *)
      (*        (eq_rect (Σ0 ▻▻ Σe - (x :: σ)) (fun Σ : LCtx => SymInstance Σ) (ι ►► env_remove (x :: σ) ιe bIn) *)
      (*           ((Σ0 ▻▻ Σe) - (x :: σ)) (eq_sym (ctx_remove_inctx_right bIn)))) (env_remove (x :: σ) ιe bIn)) *)
      Lemma inst_eq_rect `{Inst AT A} {Σ Σ'} (t : AT Σ) (eq : Σ = Σ') (ι : SymInstance Σ'):
        inst (eq_rect Σ AT t Σ' eq) ι = inst t (eq_rect Σ' (fun Σ => SymInstance Σ) ι Σ (eq_sym eq)).
      Proof.
        now subst.
      Qed.

      Lemma eq_rect_sym1 {A : Type} {P : A -> Type} {a a' : A} (eq : a = a') (v : P a) :
        eq_rect a' P (eq_rect a P v a' eq) a (eq_sym eq) = v.
      Proof.
        now subst.
      Qed.

      Lemma eq_rect_sym2 {A : Type} {P : A -> Type} {a a' : A} (eq : a' = a) (v : P a) :
        eq_rect a' P (eq_rect a P v a' (eq_sym eq)) a eq = v.
      Proof.
        now subst.
      Qed.

      Lemma match_snocView_eq_rect {Σ1 Σ2 b} {R : Type} (eq : Σ1 = Σ2) (E : SymInstance (Σ1 ▻ b))
        (f : SymInstance Σ2 -> Lit (type b) -> R) :
        match snocView (eq_rect Σ1 (fun Σ => SymInstance (Σ ▻ b)) E Σ2 eq) with
        | isSnoc E v => f E v
        end =
        match snocView E with
        | isSnoc E v => f (eq_rect Σ1 (fun Σ => SymInstance Σ) E Σ2 eq) v
        end.
      Proof.
        now destruct eq.
      Qed.

      Lemma snoc_eq_rect {Σ1 Σ2 b v} (eq : Σ1 = Σ2) (E : SymInstance Σ1) :
        eq_rect Σ1 (fun Σ => SymInstance Σ) E Σ2 eq ► (b ↦ v) =
        eq_rect Σ1 (fun Σ => SymInstance (Σ ▻ b)) (E ► (b ↦ v)) Σ2 eq.
      Proof.
        now destruct eq.
      Qed.

      Lemma env_insert_app {x : 𝑺} {σ : Ty} {Σ0 Σe : LCtx}
            (bIn : x∷σ ∈ Σe) (v : Lit σ)
            {ι : SymInstance Σ0} {ιe : SymInstance (Σe - x∷σ)} :
            (ι ►► env_insert bIn v ιe) = env_insert (inctx_cat_right bIn) v (eq_rect (Σ0 ▻▻ Σe - x∷σ) (fun Σ => SymInstance Σ) (ι ►► ιe) ((Σ0 ▻▻ Σe) - x∷σ) (eq_sym (ctx_remove_inctx_right bIn))).
      Proof.
        revert bIn ιe.
        induction Σe; intros bIn ιe;
          try destruct (Context.nilView bIn).
        cbn [env_insert ctx_remove_inctx_right].
        (* can't destruct Contxt.snocView bIn?*)
        destruct bIn as ([|n] & eq).
        - cbn in eq.
          now subst.
        - cbn in ιe.
          destruct (snocView ιe) as (ιe & v').
          change (ctx_remove_inctx_right {| inctx_at := S n; inctx_valid := eq |})
                 with (f_equal (fun f => f b) (eq_trans eq_refl (f_equal ctx_snoc (@ctx_remove_inctx_right _ Σ0 Σe _ {| inctx_at := n; inctx_valid := eq |})))).
          rewrite eq_trans_refl_l.
          cbn.
          rewrite (eq_sym_map_distr (fun f : 𝑺 ∷ Ty -> LCtx => f b)).
          rewrite eq_sym_map_distr.
          rewrite f_equal_compose.
          rewrite (map_subst_map (P := fun x => SymInstance (ctx_snoc x b)) (fun a : LCtx => a ▻ b) (fun _ x => x) ).
          rewrite match_snocView_eq_rect.
          now rewrite IHΣe.
      Qed.

      Lemma env_remove_app {x : 𝑺} {σ : Ty} {Σ0 Σe : LCtx} (bIn : x∷σ ∈ Σe)
        (ι : SymInstance Σ0) (ιe : SymInstance Σe) :
        env_remove (x∷σ) (ι ►► ιe) (inctx_cat_right bIn) =
        eq_rect (Σ0 ▻▻ Σe - x∷σ) (fun Σ : LCtx => SymInstance Σ) (ι ►► env_remove (x∷σ) ιe bIn)
                 ((Σ0 ▻▻ Σe) - x∷σ) (eq_sym (ctx_remove_inctx_right bIn)).
      Proof.
        revert bIn ιe.
        induction Σe; intros bIn ιe; try destruct (Context.nilView bIn).
        destruct (Context.snocView bIn).
        - now destruct (snocView ιe).
        - destruct (snocView ιe) as (ιe & v).
          change (ctx_remove_inctx_right (inctx_succ i))
                 with (f_equal (fun f => f b) (eq_trans eq_refl (f_equal ctx_snoc (@ctx_remove_inctx_right _ Σ0 Σe _ i)))).
          rewrite eq_trans_refl_l.
          cbn.
          rewrite (eq_sym_map_distr (fun f : 𝑺 ∷ Ty -> LCtx => f b)).
          rewrite eq_sym_map_distr.
          rewrite f_equal_compose.
          rewrite (map_subst_map (P := fun x => SymInstance (ctx_snoc x b)) (fun a : LCtx => a ▻ b) (fun _ x => x) ).
          rewrite IHΣe.
          now rewrite snoc_eq_rect.
      Qed.

    End Util.

    Module SolveEvars.

      Fixpoint assert_msgs_formulas {Σ} (mfs : List (Pair Message Formula) Σ) (p : 𝕊 Σ) : 𝕊 Σ :=
        match mfs with
        | nil => p
        | cons (msg,fml) mfs =>
          assert_msgs_formulas mfs (assertk fml msg p)
        end.

      Lemma safe_assert_msgs_formulas {Σ} {mfs : List (Pair Message Formula) Σ} {p : 𝕊 Σ} {ι : SymInstance Σ} :
        (safe (assert_msgs_formulas mfs p) ι <-> instpc (map snd mfs) ι /\ safe p ι).
      Proof.
        revert p.
        induction mfs; intros p; cbn.
        - now unfold inst_pathcondition.
        - rewrite inst_pathcondition_cons.
          destruct a; cbn.
          rewrite IHmfs.
          cbn.
          now rewrite obligation_equiv.
      Qed.

      Inductive ECtx (Σ : LCtx) : LCtx -> Type :=
      | ectx Σe (mfs : List (Pair Message Formula) (Σ ▻▻ Σe)) : ECtx Σ (Σ ▻▻ Σe).
      Arguments ectx {Σ} Σe mfs.

      Definition ectx_refl {Σ : LCtx} : ECtx Σ Σ := @ectx Σ ctx_nil nil.

      Definition ectx_formula {Σ1 Σ2} (e: ECtx Σ1 Σ2) : Message Σ2 -> Formula Σ2 -> ECtx Σ1 Σ2 :=
        match e with ectx Σe mfs => fun msg fml => ectx Σe (cons (msg,fml) mfs) end.
      Definition ectx_snoc {Σ1 Σ2} (e: ECtx Σ1 Σ2) b : ECtx Σ1 (Σ2 ▻ b) :=
        match e with ectx Σe mfs => ectx (Σe ▻ b) (subst mfs sub_wk1) end.
      Definition ectx_subst {Σ1 Σ2} (e : ECtx Σ1 Σ2) :
        forall x σ (xIn : x∷σ ∈ Σ2) (t : Term (Σ2 - x∷σ) σ),
          option (ECtx Σ1 (Σ2 - x∷σ)) :=
        match e with
        | ectx Σe mfs =>
            fun x σ xIn =>
              match Context.catView xIn with
              | isCatLeft bIn  => fun _ => None
              | isCatRight bIn =>
                  fun t =>
                    let e  := ctx_remove_inctx_right bIn in
                    let ζ  := sub_single (inctx_cat_right bIn) t in
                    let ζ' := eq_rect _ (Sub (Σ1 ▻▻ Σe)) ζ _ e in
                    Some (eq_rect_r _ (ectx _ (subst mfs ζ')) e)
              end
        end.

      Definition plug {Σ1 Σ2} (e : ECtx Σ1 Σ2) : 𝕊 Σ2 -> 𝕊 Σ1 :=
        match e with ectx Σe mfs => fun p => angelic_close0 Σe (assert_msgs_formulas mfs p) end.

      Definition plug_msg {Σ1 Σ2} (ec : ECtx Σ1 Σ2) : EMessage Σ2 -> EMessage Σ1 :=
        match ec with ectx _ _ => emsg_close end.

      Fixpoint push {Σ1 Σ2} (ec : ECtx Σ1 Σ2) (p : 𝕊 Σ2) {struct p} : 𝕊 Σ1 :=
        match p with
        | angelic_binary p1 p2   => angelic_binary (push ec p1) (push ec p2)
        | demonic_binary p1 p2   => plug ec (demonic_binary (push ectx_refl p1) (push ectx_refl p2))
        | error msg              => error (plug_msg ec msg)
        | block                  => plug ec block
        | assertk fml msg p      => push (ectx_formula ec msg fml) p
        | assumek fml p          => plug ec (assumek fml (push ectx_refl p))
        | angelicv b p           => push (ectx_snoc ec b) p
        | demonicv b p           => plug ec (demonicv b (push ectx_refl p))
        | assert_vareq x t msg p =>
            match ectx_subst ec _ t with
            | Some e' => push e' p
            | None    => plug ec (assert_vareq x t msg (push ectx_refl p))
            end
        | assume_vareq x t p     => plug ec (assume_vareq x t (push ectx_refl p))
        | debug b p              => plug ec (debug b (push ectx_refl p))
        end.

      Instance proper_assert_msgs_formulas {Σ} (mfs : List (Pair Message Formula) Σ) :
        Proper (sequiv Σ ==> sequiv Σ) (assert_msgs_formulas mfs).
      Proof. intros p q pq ι. rewrite ?safe_assert_msgs_formulas. intuition. Qed.

      Instance proper_plug {Σ1 Σ2} (ec : ECtx Σ1 Σ2) :
        Proper (sequiv Σ2 ==> sequiv Σ1) (plug ec).
      Proof.
        intros p q pq. destruct ec; cbn.
        now apply proper_angelic_close0, proper_assert_msgs_formulas.
      Qed.

      Lemma assert_msgs_formulas_angelic_binary {Σ} (mfs : List (Pair Message Formula) Σ) (p1  p2 : 𝕊 Σ) :
        assert_msgs_formulas mfs (angelic_binary p1 p2) <=>
        angelic_binary (assert_msgs_formulas mfs p1) (assert_msgs_formulas mfs p2).
      Proof.
        intros ι; cbn.
        rewrite ?safe_assert_msgs_formulas.
        cbn. intuition.
      Qed.

      Lemma map_snd_subst {Σ Σ' : LCtx} {ζ : Sub Σ Σ'}
            {mfs : List (Pair Message Formula) Σ} :
            map snd (subst mfs ζ) = subst (map snd mfs) ζ.
      Proof.
        induction mfs.
        - easy.
        - cbn.
          rewrite IHmfs.
          now destruct a.
      Qed.

      Lemma assert_msgs_formulas_angelicv {b Σ} (mfs : List (Pair Message Formula) Σ) (p : 𝕊 (Σ ▻ b)) :
        assert_msgs_formulas mfs (angelicv b p) <=>
        angelicv b (assert_msgs_formulas (subst mfs sub_wk1) p).
      Proof.
        intros ι; cbn.
        rewrite safe_assert_msgs_formulas. cbn.
        rewrite and_comm, <- exists_and.
        apply base.exist_proper. intros v.
        rewrite safe_assert_msgs_formulas.
        rewrite map_snd_subst.
        rewrite inst_subst.
        rewrite inst_sub_wk1.
        apply and_comm.
      Qed.

      Lemma plug_eq_rect {Σ1 Σ2 Σ2'} (eq : Σ2 = Σ2') (ec : ECtx Σ1 Σ2) (p : 𝕊 Σ2') :
        plug (eq_rect Σ2 (ECtx Σ1) ec Σ2' eq) p = plug ec (eq_rect_r (fun Σ3 : LCtx => 𝕊 Σ3) p eq).
      Proof. now destruct eq. Qed.

      Lemma ectx_subst_spec {Σ1 Σ2} (ec : ECtx Σ1 Σ2) {x σ} (xIn : x∷σ ∈ Σ2) (t : Term (Σ2 - x∷σ) σ) (msg : Message _) :
        OptionSpec
          (fun e => forall p, plug e p <=> plug ec (assert_vareq x t msg p))
          True
          (ectx_subst ec xIn t).
      Proof.
        destruct ec; cbn. destruct (Context.catView xIn); constructor; auto.
        intros p ι. unfold eq_rect_r. rewrite plug_eq_rect. cbn.
        rewrite ?safe_angelic_close0.
        split; intros [ιe HYP].
        - rewrite safe_assert_msgs_formulas in HYP. destruct HYP as [Hpc Hp].
          unfold eq_rect_r in Hp. rewrite safe_eq_rect, eq_sym_involutive in Hp.
          exists (env_insert bIn (inst (eq_rect ((Σ1 ▻▻ Σe) - x∷σ) (fun Σ => Term Σ σ) t (Σ1 ▻▻ Σe - x∷σ) (ctx_remove_inctx_right bIn)) (ι ►► ιe)) ιe).
          rewrite safe_assert_msgs_formulas. cbn. rewrite obligation_equiv. cbn.
          rewrite env_insert_app, env_remove_insert, env_insert_lookup.
          rewrite inst_subst, inst_sub_shift, env_remove_insert, ?inst_eq_rect.
          split; auto.
          rewrite map_snd_subst, inst_subst, inst_eq_rect in Hpc.
          now rewrite inst_sub_single2 in Hpc.
        - rewrite safe_assert_msgs_formulas in HYP. destruct HYP as [Hpc Hp].
          cbn in Hp. rewrite obligation_equiv in Hp. cbn in Hp. destruct Hp as [Ht Hp].
          rewrite env_remove_app in Hp.
          exists (env_remove (x∷σ) ιe bIn).
          rewrite safe_assert_msgs_formulas.
          rewrite map_snd_subst, inst_subst.
          unfold eq_rect_r. rewrite safe_eq_rect.
          rewrite eq_sym_involutive. split; auto.
          rewrite inst_subst in Ht.
          rewrite inst_eq_rect.
          rewrite <- env_remove_app.
          rewrite <- inst_sub_shift.
          now rewrite inst_sub_single_shift.
      Qed.

      Lemma error_plug_msg {Σ1 Σ2} (ec : ECtx Σ1 Σ2) (msg : EMessage Σ2) :
        error (plug_msg ec msg) <=> plug ec (error msg).
      Proof.
        destruct ec; intros ι; cbn.
        split; try contradiction.
        rewrite safe_angelic_close0.
        intros [ιe HYP].
        rewrite safe_assert_msgs_formulas in HYP.
        destruct HYP as [? []].
      Qed.

      Lemma push_plug {Σ1 Σ2} (ec : ECtx Σ1 Σ2) (p : 𝕊 Σ2) :
        push ec p <=> plug ec p.
      Proof.
        revert Σ1 ec; induction p; cbn; intros Σ1 ec.
        - rewrite IHp1, IHp2. clear IHp1 IHp2.
          destruct ec. cbn [plug].
          rewrite <- angelic_close0_angelic_binary.
          apply proper_angelic_close0.
          now rewrite <- assert_msgs_formulas_angelic_binary.
        - apply proper_plug, proper_demonic_binary;
           [now rewrite IHp1 | now rewrite IHp2].
        - apply error_plug_msg.
        - reflexivity.
        - rewrite IHp. clear IHp.
          destruct ec; cbn. reflexivity.
        - apply proper_plug, proper_assumek, IHp.
        - rewrite IHp. clear IHp.
          destruct ec; cbn.
          apply proper_angelic_close0.
          rewrite assert_msgs_formulas_angelicv.
          reflexivity.
        - apply proper_plug, proper_demonicv, IHp.
        - destruct (ectx_subst_spec ec xIn t msg).
          + rewrite IHp. rewrite H. reflexivity.
          + apply proper_plug, proper_assert_vareq, IHp.
        - apply proper_plug, proper_assume_vareq, IHp.
        - apply proper_plug, proper_debug, IHp.
      Qed.

    End SolveEvars.

    Definition solve_evars {Σ} (p : 𝕊 Σ) : 𝕊 Σ :=
      SolveEvars.push SolveEvars.ectx_refl p.

    Lemma solve_evars_sound {Σ} (p : 𝕊 Σ) :
      forall ι, safe (solve_evars p) ι <-> safe p ι.
    Proof. apply (SolveEvars.push_plug SolveEvars.ectx_refl). Qed.

    Module SolveUvars.

      Fixpoint assume_formulas {Σ} (fs : List Formula Σ) (p : 𝕊 Σ) : 𝕊 Σ :=
        match fs with
        | nil => p
        | cons fml mfs =>
          assume_formulas mfs (assumek fml p)
        end.

      Lemma safe_assume_formulas {Σ} {fs : List Formula Σ} {p : 𝕊 Σ} {ι : SymInstance Σ} :
        safe (assume_formulas fs p) ι <-> (instpc fs ι -> safe p ι).
      Proof.
        revert p.
        induction fs; intros p; cbn.
        - unfold inst_pathcondition; cbn; intuition.
        - rewrite inst_pathcondition_cons.
          rewrite IHfs. cbn. intuition.
      Qed.

      Inductive UCtx (Σ : LCtx) : LCtx -> Type :=
      | uctx Σu (mfs : List Formula (Σ ▻▻ Σu)) : UCtx Σ (Σ ▻▻ Σu).
      Arguments uctx {Σ} Σu mfs.

      Definition uctx_refl {Σ : LCtx} : UCtx Σ Σ := @uctx Σ ctx_nil nil.

      Definition uctx_formula {Σ1 Σ2} (e : UCtx Σ1 Σ2) : Formula Σ2 -> UCtx Σ1 Σ2 :=
        match e with uctx Σu mfs => fun fml => uctx Σu (cons fml mfs) end.
      Definition uctx_snoc {Σ1 Σ2} (e: UCtx Σ1 Σ2) b : UCtx Σ1 (Σ2 ▻ b) :=
        match e with uctx Σu mfs => uctx (Σu ▻ b) (subst mfs sub_wk1) end.
      Definition uctx_subst {Σ1 Σ2} (e : UCtx Σ1 Σ2) :
        forall x σ (xIn : x∷σ ∈ Σ2) (t : Term (Σ2 - x∷σ) σ),
          option (UCtx Σ1 (Σ2 - x∷σ)) :=
        match e with
        | uctx Σu mfs =>
            fun x σ xIn =>
              match Context.catView xIn with
              | isCatLeft bIn  => fun _ => None
              | isCatRight bIn =>
                  fun t =>
                    let e  := ctx_remove_inctx_right bIn in
                    let ζ  := sub_single (inctx_cat_right bIn) t in
                    let ζ' := eq_rect _ (Sub (Σ1 ▻▻ Σu)) ζ _ e in
                    Some (eq_rect_r _ (uctx _ (subst mfs ζ')) e)
              end
        end.

      Definition plug {Σ1 Σ2} (e : UCtx Σ1 Σ2) : 𝕊 Σ2 -> 𝕊 Σ1 :=
        match e with uctx Σu mfs => fun p => demonic_close0 Σu (assume_formulas mfs p) end.

      Fixpoint push {Σ1 Σ2} (ec : UCtx Σ1 Σ2) (p : 𝕊 Σ2) {struct p} : 𝕊 Σ1 :=
        match p with
        | angelic_binary p1 p2   => plug ec (angelic_binary (push uctx_refl p1) (push uctx_refl p2))
        | demonic_binary p1 p2   => plug ec (demonic_binary (push uctx_refl p1) (push uctx_refl p2))
            (* demonic_binary (push ec p1) (push ec p2) *)
        | error msg              => plug ec (error msg)
        | block                  => block
        | assertk fml msg p      => plug ec (assertk fml msg (push uctx_refl p))
        | assumek fml p          => push (uctx_formula ec fml) p
        | angelicv b p           => plug ec (angelicv b (push uctx_refl p))
        | demonicv b p           => push (uctx_snoc ec b) p
        | assert_vareq x t msg p => plug ec (assert_vareq x t msg (push uctx_refl p))
        | assume_vareq x t p     =>
            match uctx_subst ec _ t with
            | Some e' => push e' p
            | None    => plug ec (assume_vareq x t (push uctx_refl p))
            end
        | debug b p              => plug ec (debug b (push uctx_refl p))
        end.

      Instance proper_assume_formulas {Σ} (mfs : List Formula Σ) :
        Proper (sequiv Σ ==> sequiv Σ) (assume_formulas mfs).
      Proof. intros p q pq ι. rewrite ?safe_assume_formulas. intuition. Qed.

      Instance proper_plug {Σ1 Σ2} (ec : UCtx Σ1 Σ2) :
        Proper (sequiv Σ2 ==> sequiv Σ1) (plug ec).
      Proof.
        intros p q pq. destruct ec; cbn.
        now apply proper_demonic_close0, proper_assume_formulas.
      Qed.

      Lemma assume_formulas_demonic_binary {Σ} (fmls : List Formula Σ) (p1 p2 : 𝕊 Σ) :
        assume_formulas fmls (demonic_binary p1 p2) <=>
        demonic_binary (assume_formulas fmls p1) (assume_formulas fmls p2).
      Proof.
        intros ι; cbn.
        rewrite ?safe_assume_formulas.
        cbn. intuition.
      Qed.

      Lemma forall_impl {A : Type} {P : A -> Prop} {Q : Prop} :
        (Q -> forall (x : A), P x) <-> (forall (x : A), Q -> P x).
      Proof. firstorder. Qed.

      Lemma assume_formulas_demonicv {b Σ} (fmls : List Formula Σ) (p : 𝕊 (Σ ▻ b)) :
        assume_formulas fmls (demonicv b p) <=>
        demonicv b (assume_formulas (subst fmls sub_wk1) p).
      Proof.
        intros ι; cbn.
        rewrite safe_assume_formulas. cbn.
        rewrite forall_impl.
        apply base.forall_proper. intros v.
        rewrite safe_assume_formulas.
        rewrite inst_subst.
        rewrite inst_sub_wk1.
        reflexivity.
      Qed.

      Lemma plug_eq_rect {Σ1 Σ2 Σ2'} (eq : Σ2 = Σ2') (ec : UCtx Σ1 Σ2) (p : 𝕊 Σ2') :
        plug (eq_rect Σ2 (UCtx Σ1) ec Σ2' eq) p = plug ec (eq_rect_r (fun Σ3 : LCtx => 𝕊 Σ3) p eq).
      Proof. now destruct eq. Qed.

      Lemma uctx_subst_spec {Σ1 Σ2} (ec : UCtx Σ1 Σ2) {x σ} (xIn : x∷σ ∈ Σ2) (t : Term (Σ2 - x∷σ) σ) :
        OptionSpec
          (fun e => forall p, plug e p <=> plug ec (assume_vareq x t p))
          True
          (uctx_subst ec xIn t).
      Proof.
        destruct ec; cbn. destruct (Context.catView xIn); constructor; auto.
        intros p ι. unfold eq_rect_r. rewrite plug_eq_rect. cbn.
        rewrite ?safe_demonic_close0.
        split; intros HYP ιu.
        - specialize (HYP (env_remove (x∷σ) ιu bIn)).
          rewrite safe_assume_formulas. intros Hpc Heq.
          rewrite <- inst_sub_shift in Heq.
          rewrite safe_assume_formulas in HYP.
          rewrite inst_subst in HYP.
          rewrite inst_eq_rect in HYP.
          unfold eq_rect_r in HYP. rewrite safe_eq_rect, eq_sym_involutive in HYP.
          rewrite <- env_remove_app in HYP. apply HYP.
          rewrite <- inst_sub_shift.
          rewrite inst_sub_single_shift; auto.
        - specialize (HYP (env_insert bIn (inst (eq_rect ((Σ1 ▻▻ Σu) - x∷σ) (fun Σ => Term Σ σ) t (Σ1 ▻▻ Σu - x∷σ) (ctx_remove_inctx_right bIn)) (ι ►► ιu)) ιu)).
          rewrite safe_assume_formulas, inst_subst, inst_eq_rect. intros Hpc.
          unfold eq_rect_r. rewrite safe_eq_rect, eq_sym_involutive.
          rewrite safe_assume_formulas in HYP. cbn in HYP.
          rewrite env_insert_app, env_remove_insert, env_insert_lookup in HYP.
          rewrite inst_eq_rect in HYP.
          rewrite inst_sub_single2 in Hpc.
          now apply HYP.
      Qed.

      Lemma push_plug {Σ1 Σ2} (ec : UCtx Σ1 Σ2) (p : 𝕊 Σ2) :
        push ec p <=> plug ec p.
      Proof.
        revert Σ1 ec; induction p; cbn; intros Σ1 ec.
        - apply proper_plug, proper_angelic_binary;
           [now rewrite IHp1 | now rewrite IHp2].
        - rewrite IHp1, IHp2. clear IHp1 IHp2.
          reflexivity.
          (* destruct ec. cbn [plug]. *)
          (* rewrite <- demonic_close0_demonic_binary. *)
          (* apply proper_demonic_close0. *)
          (* now rewrite <- assume_formulas_demonic_binary. *)
        - reflexivity.
        - intros ι; cbn; split; auto. intros _.
          destruct ec; cbn.
          rewrite safe_demonic_close0; intros ιu.
          rewrite safe_assume_formulas; cbn; auto.
        - apply proper_plug, proper_assertk, IHp.
        - rewrite IHp. clear IHp.
          destruct ec; cbn. reflexivity.
        - apply proper_plug, proper_angelicv, IHp.
        - rewrite IHp. clear IHp.
          destruct ec; cbn.
          apply proper_demonic_close0.
          rewrite assume_formulas_demonicv.
          reflexivity.
        - apply proper_plug, proper_assert_vareq, IHp.
        - destruct (uctx_subst_spec ec xIn t).
          + rewrite IHp. rewrite H. reflexivity.
          + apply proper_plug, proper_assume_vareq, IHp.
        - apply proper_plug, proper_debug, IHp.
      Qed.

    End SolveUvars.

    Definition solve_uvars {Σ} (p : 𝕊 Σ) : 𝕊 Σ :=
      SolveUvars.push SolveUvars.uctx_refl p.

    Lemma solve_uvars_sound {Σ} (p : 𝕊 Σ) :
      forall ι, safe (solve_uvars p) ι <-> safe p ι.
    Proof. apply (SolveUvars.push_plug SolveUvars.uctx_refl). Qed.

    Module Experimental.

      Definition Ephemeral (Σ1 Σ2 : LCtx) : Type :=
        SolveEvars.ECtx Σ1 Σ2 + SolveUvars.UCtx Σ1 Σ2.

      Definition EProp : LCtx -> Type :=
        fun Σ : LCtx => forall Σ0, Ephemeral Σ0 Σ -> 𝕊 Σ0.

      Definition angelic_binary {Σ} (p q : EProp Σ) : EProp Σ :=
        fun Σ0 eph =>
          match eph with
          | inl ec => SymProp.angelic_binary (p Σ0 eph) (q Σ0 eph)
          | inr uc => let eph' : Ephemeral _ _ := inl SolveEvars.ectx_refl in
                      SolveUvars.plug uc (SymProp.angelic_binary (p Σ eph') (q Σ eph'))
          end.

      Definition angelicv {Σ} (b : 𝑺 ∷ Ty) (p : EProp (Σ ▻ b)) : EProp Σ :=
        fun Σ0 eph =>
          match eph with
          | inl ec => p Σ0 (inl (SolveEvars.ectx_snoc ec b))
          | inr uc => let eph' : Ephemeral _ _ := inl SolveEvars.ectx_refl in
                      SolveUvars.plug uc (angelicv b (p (Σ ▻ b) eph'))
          end.

      Definition demonic_binary {Σ} (p q : EProp Σ) : EProp Σ :=
        fun Σ0 eph =>
          match eph with
          | inl ec => let eph' : Ephemeral _ _ := inr SolveUvars.uctx_refl in
                      SolveEvars.plug ec (SymProp.demonic_binary (p Σ eph') (q Σ eph'))
          | inr uc => SymProp.demonic_binary (p Σ0 eph) (q Σ0 eph)
          end.

      Definition error {Σ} (msg : EMessage Σ) : EProp Σ :=
        fun Σ0 eph =>
          match eph with
          | inl ec => error (SolveEvars.plug_msg ec msg)
          | inr uc => SolveUvars.plug uc (error msg)
          end.

    End Experimental.

  End Postprocessing.
  Import Postprocessing.

  Section VerificationConditions.

    Inductive VerificationCondition (p : 𝕊 wnil) : Prop :=
    | vc (P : safe p env_nil).

  End VerificationConditions.

  Definition SDijkstra (A : TYPE) : TYPE :=
    □(A -> 𝕊) -> SymProp.

  Module SDijk.

    Definition pure {A : TYPE} :
      ⊢ A -> SDijkstra A :=
      fun w0 a POST => T POST a.

    Definition map {A B} :
      ⊢ □(A -> B) -> SDijkstra A -> SDijkstra B :=
      fun w0 f m POST => m (comp <$> POST <*> f).

    Definition bind {A B} :
      ⊢ SDijkstra A -> □(A -> SDijkstra B) -> SDijkstra B :=
      fun w0 m f POST => m (fun w1 ω01 a1 => f w1 ω01 a1 (four POST ω01)).

    Definition angelic (x : option 𝑺) σ :
      ⊢ SDijkstra (STerm σ) :=
      fun w k =>
        let y := fresh w x in
        angelicv
          (y∷σ) (k (wsnoc w (y∷σ)) acc_snoc_right (@term_var _ y σ inctx_zero)).
    Global Arguments angelic x σ [w] k.

    Definition angelic_ctx {N : Set} (n : N -> 𝑺) :
      ⊢ ∀ Δ : NCtx N Ty, SDijkstra (fun w => NamedEnv (Term w) Δ) :=
      fix rec {w} Δ {struct Δ} :=
        match Δ with
        | ctx_nil          => fun k => T k env_nil
        | ctx_snoc Δ (x∷σ) =>
          fun k =>
            angelic (Some (n x)) σ (fun w1 ω01 t =>
              rec Δ (fun w2 ω12 EΔ =>
                k w2 (acc_trans ω01 ω12) (EΔ ► (x∷σ ↦ persist__term t ω12))))
        end.
    Global Arguments angelic_ctx {N} n [w] Δ : rename.

    Definition demonic (x : option 𝑺) σ :
      ⊢ SDijkstra (STerm σ) :=
      fun w k =>
        let y := fresh w x in
        demonicv
          (y∷σ) (k (wsnoc w (y∷σ)) acc_snoc_right (@term_var _ y σ inctx_zero)).
    Global Arguments demonic x σ [w] k.

    Definition demonic_ctx {N : Set} (n : N -> 𝑺) :
      ⊢ ∀ Δ : NCtx N Ty, SDijkstra (fun w => NamedEnv (Term w) Δ) :=
      fix demonic_ctx {w} Δ {struct Δ} :=
        match Δ with
        | ctx_nil          => fun k => T k env_nil
        | ctx_snoc Δ (x∷σ) =>
          fun k =>
            demonic (Some (n x)) σ (fun w1 ω01 t =>
              demonic_ctx Δ (fun w2 ω12 EΔ =>
                k w2 (acc_trans ω01 ω12) (EΔ ► (x∷σ ↦ persist__term t ω12))))
        end.
    Global Arguments demonic_ctx {_} n [w] Δ : rename.

    Definition assume_formulas :
      ⊢ List Formula -> SDijkstra Unit :=
      fun w0 fmls0 POST =>
        match Solver.generic solver_user fmls0 with
        | Some (existT w1 (ν , fmls1)) =>
          (* Assume variable equalities and the residual constraints *)
          assume_triangular ν
            (assume_formulas_without_solver fmls1
               (* Run POST in the world with the variable and residual
                  formulas included. This is a critical piece of code since
                  this is the place where we really meaningfully change the
                  world. We changed the type of assume_formulas_without_solver
                  just to not forget adding the formulas to the path constraints.
               *)
               (four POST (acc_triangular ν) (acc_formulas_right w1 fmls1) tt))
        | None =>
          (* The formulas are inconsistent with the path constraints. *)
          block
        end.

    Definition assume_formula :
      ⊢ Formula -> SDijkstra Unit :=
      fun w0 fml0 =>
        assume_formulas (cons fml0 nil).

    Definition assert_formulas :
      ⊢ Message -> List Formula -> SDijkstra Unit :=
      fun w0 msg fmls0 POST =>
        match Solver.generic solver_user fmls0 with
        | Some (existT w1 (ν , fmls1)) =>
          (* Assert variable equalities and the residual constraints *)
          assert_triangular msg ν
            (fun msg' =>
               assert_formulas_without_solver msg' fmls1
                 (* Critical code. Like for assume_formulas. *)
                 (four POST (acc_triangular ν) (acc_formulas_right w1 fmls1) tt))
        | None =>
          (* The formulas are inconsistent with the path constraints. *)
          error (EMsgHere msg)
        end.

    Definition assert_formula :
      ⊢ Message -> Formula -> SDijkstra Unit :=
      fun w0 msg fml0 =>
        assert_formulas msg (cons fml0 nil).

    Definition angelic_binary {A} :
      ⊢ SDijkstra A -> SDijkstra A -> SDijkstra A :=
      fun w m1 m2 POST =>
        angelic_binary (m1 POST) (m2 POST).
    Definition demonic_binary {A} :
      ⊢ SDijkstra A -> SDijkstra A -> SDijkstra A :=
      fun w m1 m2 POST =>
        demonic_binary (m1 POST) (m2 POST).

    Definition angelic_list {A} :
      ⊢ Message -> List A -> SDijkstra A :=
      fun w msg =>
        fix rec xs :=
        match xs with
        | nil        => fun POST => error (EMsgHere msg)
        | cons x xs  => angelic_binary (pure x) (rec xs)
        end.

    Definition demonic_list {A} :
      ⊢ List A -> SDijkstra A :=
      fun w =>
        fix rec xs :=
        match xs with
        | nil        => fun POST => block
        | cons x xs  => demonic_binary (pure x) (rec xs)
        end.

    Definition angelic_finite F `{finite.Finite F} :
      ⊢ Message -> SDijkstra ⌜F⌝ :=
      fun w msg => angelic_list msg (finite.enum F).

    Definition demonic_finite F `{finite.Finite F} :
      ⊢ SDijkstra ⌜F⌝ :=
      fun w => demonic_list (finite.enum F).

    Definition angelic_match_bool' :
      ⊢ Message -> STerm ty_bool -> SDijkstra ⌜bool⌝ :=
      fun _ msg t =>
        angelic_binary
          (fun POST => assert_formula msg (formula_bool t) (fun w1 ω01 _ => POST w1 ω01 true))
          (fun POST => assert_formula msg (formula_bool (term_not t)) (fun w1 ω01 _ => POST w1 ω01 false)).

    Definition angelic_match_bool :
      ⊢ Message -> STerm ty_bool -> SDijkstra ⌜bool⌝ :=
      fun w msg t =>
        let t' := peval t in
        match term_get_lit t' with
        | Some l => pure  l
        | None   => angelic_match_bool' msg t'
        end.

    Definition demonic_match_bool' :
      ⊢ STerm ty_bool -> SDijkstra ⌜bool⌝ :=
      fun _ t =>
        demonic_binary
          (fun POST => assume_formula (formula_bool t) (fun w1 ω01 _ => POST w1 ω01 true))
          (fun POST => assume_formula (formula_bool (term_not t)) (fun w1 ω01 _ => POST w1 ω01 false)).

    Definition demonic_match_bool :
      ⊢ STerm ty_bool -> SDijkstra ⌜bool⌝ :=
      fun w t =>
        let t' := peval t in
        match term_get_lit t' with
        | Some l => pure  l
        | None   => demonic_match_bool' t'
        end.


    (* Definition angelic_match_enum {AT E} : *)
    (*   ⊢ Message -> STerm (ty_enum E) -> (⌜Lit (ty_enum E)⌝ -> □(𝕊 AT)) -> 𝕊 AT := *)
    (*   fun w msg t k => *)
    (*     match term_get_lit t with *)
    (*     | Some v => T (k v) *)
    (*     | None => angelic_finite *)
    (*                 msg (fun v => assert_formulak msg (formula_eq t (term_enum E v)) (k v)) *)
    (*     end. *)

    (* Definition demonic_match_enum {AT E} : *)
    (*   ⊢ STerm (ty_enum E) -> (⌜Lit (ty_enum E)⌝ -> □(𝕊 AT)) -> 𝕊 AT := *)
    (*   fun w t k => *)
    (*     match term_get_lit t with *)
    (*     | Some v => T (k v) *)
    (*     | None => demonic_finite *)
    (*                 (fun v => assume_formulak (formula_eq t (term_enum E v)) (k v)) *)
    (*     end. *)

    (* Definition angelic_match_list {AT} (x y : 𝑺) (σ : Ty) : *)
    (*   ⊢ Message -> STerm (ty_list σ) -> □(𝕊 AT) -> □(STerm σ -> STerm (ty_list σ) -> 𝕊 AT) -> 𝕊 AT := *)
    (*   fun w0 msg t knil kcons => *)
    (*     angelic_binary (assert_formulak msg (formula_eq (term_lit (ty_list σ) []) t) knil) *)
    (*       (angelic x σ *)
    (*          (fun w1 ω01 (th : Term w1 σ) => *)
    (*           angelic y (ty_list σ) *)
    (*             (fun w2 ω12 (tt : Term w2 (ty_list σ)) => *)
    (*              assert_formulak (subst msg (wtrans ω01 ω12)) *)
    (*                (formula_eq (term_binop binop_cons (subst th ω12) tt) (subst t (wtrans ω01 ω12))) *)
    (*                (fun w3 ω23 => *)
    (*                 four kcons (wtrans ω01 ω12) ω23 (subst th (wtrans ω12 ω23)) (subst tt ω23))))). *)

    (* Definition demonic_match_list {AT} (x y : 𝑺) (σ : Ty) : *)
    (*   ⊢ STerm (ty_list σ) -> □(𝕊 AT) -> □(STerm σ -> STerm (ty_list σ) -> 𝕊 AT) -> 𝕊 AT := *)
    (*   fun w0 t knil kcons => *)
    (*     demonic_binary (assume_formulak (formula_eq (term_lit (ty_list σ) []) t) knil) *)
    (*       (demonic x σ *)
    (*          (fun w1 ω01 (th : Term w1 σ) => *)
    (*           demonic y (ty_list σ) *)
    (*             (fun w2 ω12 (tt : Term w2 (ty_list σ)) => *)
    (*              assume_formulak *)
    (*                (formula_eq (term_binop binop_cons (subst th ω12) tt) (subst t (wtrans ω01 ω12))) *)
    (*                (fun w3 ω23 => *)
    (*                 four kcons (wtrans ω01 ω12) ω23 (subst th (wtrans ω12 ω23)) (subst tt ω23))))). *)

    Definition angelic_match_sum {A} (x : 𝑺) (σ : Ty) (y : 𝑺) (τ : Ty) :
      ⊢ Message -> STerm (ty_sum σ τ) -> □(STerm σ -> SDijkstra A) -> □(STerm τ -> SDijkstra A) -> SDijkstra A.
    Proof.
      intros w0 msg t kinl kinr.
      apply angelic_binary.
      - eapply bind.
        apply (angelic (Some x) σ).
        intros w1 ω01 t1.
        eapply bind.
        apply assert_formula. apply (persist (A := Message) msg ω01).
        apply (formula_eq (term_inl t1) (persist__term t ω01)).
        intros w2 ω12 _.
        apply (four kinl ω01). auto.
        apply (persist__term t1 ω12).
      - eapply bind.
        apply (angelic (Some y) τ).
        intros w1 ω01 t1.
        eapply bind.
        apply assert_formula. apply (persist (A := Message) msg ω01).
        apply (formula_eq (term_inr t1) (persist__term t ω01)).
        intros w2 ω12 _.
        apply (four kinr ω01). auto.
        apply (persist__term t1 ω12).
    Defined.

    (* Definition angelic_match_sum {A} (x : 𝑺) (σ : Ty) (y : 𝑺) (τ : Ty) : *)
    (*   ⊢ Message -> STerm (ty_sum σ τ) -> □(STerm σ -> SDijkstra A) -> □(STerm τ -> SDijkstra A) -> SDijkstra A. *)
    (* Proof. *)
    (*   intros w0. *)
    (*   fun w0 msg t kinl kinr => *)
    (*     match term_get_sum t with *)
    (*     | Some (inl tσ) => T kinl tσ *)
    (*     | Some (inr tτ) => T kinr tτ *)
    (*     | None => angelic_match_sum' x y msg t kinl kinr *)
    (*     end. *)

    Definition demonic_match_sum' {A} (x : 𝑺) (σ : Ty) (y : 𝑺) (τ : Ty) :
      ⊢ STerm (ty_sum σ τ) -> □(STerm σ -> SDijkstra A) -> □(STerm τ -> SDijkstra A) -> SDijkstra A.
    Proof.
      intros w0 t kinl kinr.
      apply demonic_binary.
      - eapply bind.
        apply (demonic (Some x) σ).
        intros w1 ω01 t1.
        eapply bind.
        apply assume_formula.
        apply (formula_eq (term_inl t1) (persist__term t ω01)).
        intros w2 ω12 _.
        apply (four kinl ω01). auto.
        apply (persist__term t1 ω12).
      - eapply bind.
        apply (demonic (Some y) τ).
        intros w1 ω01 t1.
        eapply bind.
        apply assume_formula.
        apply (formula_eq (term_inr t1) (persist__term t ω01)).
        intros w2 ω12 _.
        apply (four kinr ω01). auto.
        apply (persist__term t1 ω12).
    Defined.

    Definition demonic_match_sum {A} (x : 𝑺) (σ : Ty) (y : 𝑺) (τ : Ty) :
      ⊢ STerm (ty_sum σ τ) -> □(STerm σ -> SDijkstra A) -> □(STerm τ -> SDijkstra A) -> SDijkstra A :=
      fun w0 t kinl kinr =>
        match term_get_sum t with
        | Some (inl tσ) => T kinl tσ
        | Some (inr tτ) => T kinr tτ
        | None => demonic_match_sum' x y t kinl kinr
        end.

    Definition angelic_match_prod {A} (x : 𝑺) (σ : Ty) (y : 𝑺) (τ : Ty) :
      ⊢ Message -> STerm (ty_prod σ τ) -> □(STerm σ -> STerm τ -> SDijkstra A) -> SDijkstra A.
    Proof.
      intros w0 msg t k.
      eapply bind.
      apply (angelic (Some x) σ).
      intros w1 ω01 t1.
      eapply bind.
      apply (angelic (Some y) τ).
      intros w2 ω12 t2.
      eapply bind.
      apply assert_formula. apply (persist (A := Message) msg (acc_trans ω01 ω12)).
      refine (formula_eq _ (persist__term t (acc_trans ω01 ω12))).
      eapply (term_binop binop_pair).
      apply (persist__term t1 ω12).
      apply t2.
      intros w3 ω23 _.
      apply (four k (acc_trans ω01 ω12)).
      auto.
      apply (persist__term t1 (acc_trans ω12 ω23)).
      apply (persist__term t2 ω23).
    Defined.

    (* Definition angelic_match_prod {AT} (x : 𝑺) (σ : Ty) (y : 𝑺) (τ : Ty) : *)
    (*   ⊢ Message -> STerm (ty_prod σ τ) -> □(STerm σ -> STerm τ -> 𝕊 AT) -> 𝕊 AT := *)
    (*   fun w0 msg t k => *)
    (*     match term_get_pair t with *)
    (*     | Some (tσ,tτ) => T k tσ tτ *)
    (*     | None => angelic_match_prod' x y msg t k *)
    (*     end. *)

    Definition demonic_match_prod {A} (x : 𝑺) (σ : Ty) (y : 𝑺) (τ : Ty) :
      ⊢ STerm (ty_prod σ τ) -> □(STerm σ -> STerm τ -> SDijkstra A) -> SDijkstra A.
    Proof.
      intros w0 t k.
      eapply bind.
      apply (demonic (Some x) σ).
      intros w1 ω01 t1.
      eapply bind.
      apply (demonic (Some y) τ).
      intros w2 ω12 t2.
      eapply bind.
      apply assume_formula.
      refine (formula_eq _ (persist__term t (acc_trans ω01 ω12))).
      eapply (term_binop binop_pair).
      apply (persist__term t1 ω12).
      apply t2.
      intros w3 ω23 _.
      apply (four k (acc_trans ω01 ω12)).
      auto.
      apply (persist__term t1 (acc_trans ω12 ω23)).
      apply (persist__term t2 ω23).
    Defined.

    (* Definition demonic_match_prod {AT} (x : 𝑺) (σ : Ty) (y : 𝑺) (τ : Ty) : *)
    (*   ⊢ STerm (ty_prod σ τ) -> □(STerm σ -> STerm τ -> 𝕊 AT) -> 𝕊 AT := *)
    (*   fun w0 t k => *)
    (*     match term_get_pair t with *)
    (*     | Some (tσ,tτ) => T k tσ tτ *)
    (*     | None => demonic_match_prod' x y t k *)
    (*     end. *)

    (* Definition angelic_match_record' {N : Set} (n : N -> 𝑺) {AT R} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) : *)
    (*   ⊢ Message -> STerm (ty_record R) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> 𝕊 AT) -> 𝕊 AT. *)
    (* Proof. *)
    (*   intros w0 msg t k. *)
    (*   apply (angelic_freshen_ctx n Δ). *)
    (*   intros w1 ω01 ts. *)
    (*   apply assert_formulak. *)
    (*   apply (subst msg ω01). *)
    (*   apply (formula_eq (subst t ω01)). *)
    (*   apply (term_record R (record_pattern_match_env_reverse p ts)). *)
    (*   intros w2 ω12. *)
    (*   apply (k w2 (acc_trans ω01 ω12) (subst ts ω12)). *)
    (* Defined. *)

    (* Definition angelic_match_record {N : Set} (n : N -> 𝑺) {AT R} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) : *)
    (*   ⊢ Message -> STerm (ty_record R) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> 𝕊 AT) -> 𝕊 AT. *)
    (* Proof. *)
    (*   intros w0 msg t k. *)
    (*   destruct (term_get_record t). *)
    (*   - apply (T k). *)
    (*     apply (record_pattern_match_env p n0). *)
    (*   - apply (angelic_match_record' n p msg t k). *)
    (* Defined. *)

    (* Definition demonic_match_record' {N : Set} (n : N -> 𝑺) {AT R} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) : *)
    (*   ⊢ STerm (ty_record R) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> 𝕊 AT) -> 𝕊 AT. *)
    (* Proof. *)
    (*   intros w0 t k. *)
    (*   apply (demonic_ctx n Δ). *)
    (*   intros w1 ω01 ts. *)
    (*   apply assume_formulak. *)
    (*   apply (formula_eq (subst t ω01)). *)
    (*   apply (term_record R (record_pattern_match_env_reverse p ts)). *)
    (*   intros w2 ω12. *)
    (*   apply (k w2 (acc_trans ω01 ω12) (subst ts ω12)). *)
    (* Defined. *)

    (* Definition demonic_match_record {N : Set} (n : N -> 𝑺) {AT R} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) : *)
    (*   ⊢ STerm (ty_record R) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> 𝕊 AT) -> 𝕊 AT. *)
    (* Proof. *)
    (*   intros w0 t k. *)
    (*   destruct (term_get_record t). *)
    (*   - apply (T k). *)
    (*     apply (record_pattern_match_env p n0). *)
    (*   - apply (demonic_match_record' n p t k). *)
    (* Defined. *)

    (* Definition angelic_match_tuple' {N : Set} (n : N -> 𝑺) {AT σs} {Δ : NCtx N Ty} (p : TuplePat σs Δ) : *)
    (*   ⊢ Message -> STerm (ty_tuple σs) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> 𝕊 AT) -> 𝕊 AT. *)
    (* Proof. *)
    (*   intros w0 msg t k. *)
    (*   apply (angelic_freshen_ctx n Δ). *)
    (*   intros w1 ω01 ts. *)
    (*   apply assert_formulak. *)
    (*   apply (subst msg ω01). *)
    (*   apply (formula_eq (subst t ω01)). *)
    (*   apply (term_tuple (tuple_pattern_match_env_reverse p ts)). *)
    (*   intros w2 ω12. *)
    (*   apply (k w2 (acc_trans ω01 ω12) (subst ts ω12)). *)
    (* Defined. *)

    (* Definition angelic_match_tuple {N : Set} (n : N -> 𝑺) {AT σs} {Δ : NCtx N Ty} (p : TuplePat σs Δ) : *)
    (*   ⊢ Message -> STerm (ty_tuple σs) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> 𝕊 AT) -> 𝕊 AT. *)
    (* Proof. *)
    (*   intros w0 msg t k. *)
    (*   destruct (term_get_tuple t). *)
    (*   - apply (T k). *)
    (*     apply (tuple_pattern_match_env p e). *)
    (*   - apply (angelic_match_tuple' n p msg t k). *)
    (* Defined. *)

    (* Definition demonic_match_tuple' {N : Set} (n : N -> 𝑺) {AT σs} {Δ : NCtx N Ty} (p : TuplePat σs Δ) : *)
    (*   ⊢ STerm (ty_tuple σs) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> 𝕊 AT) -> 𝕊 AT. *)
    (* Proof. *)
    (*   intros w0 t k. *)
    (*   apply (demonic_ctx n Δ). *)
    (*   intros w1 ω01 ts. *)
    (*   apply assume_formulak. *)
    (*   apply (formula_eq (subst t ω01)). *)
    (*   apply (term_tuple (tuple_pattern_match_env_reverse p ts)). *)
    (*   intros w2 ω12. *)
    (*   apply (k w2 (acc_trans ω01 ω12) (subst ts ω12)). *)
    (* Defined. *)

    (* Definition demonic_match_tuple {N : Set} (n : N -> 𝑺) {AT σs} {Δ : NCtx N Ty} (p : TuplePat σs Δ) : *)
    (*   ⊢ STerm (ty_tuple σs) -> □((fun Σ => NamedEnv (Term Σ) Δ) -> 𝕊 AT) -> 𝕊 AT. *)
    (* Proof. *)
    (*   intros w0 t k. *)
    (*   destruct (term_get_tuple t). *)
    (*   - apply (T k). *)
    (*     apply (tuple_pattern_match_env p e). *)
    (*   - apply (demonic_match_tuple' n p t k). *)
    (* Defined. *)

    (* (* TODO: move to Syntax *) *)
    (* Definition pattern_match_env_reverse {N : Set} {Σ : LCtx} {σ : Ty} {Δ : NCtx N Ty} (p : Pattern Δ σ) : *)
    (*   NamedEnv (Term Σ) Δ -> Term Σ σ := *)
    (*   match p with *)
    (*   | pat_var x    => fun Ex => match snocView Ex with isSnoc _ t => t end *)
    (*   | pat_unit     => fun _ => term_lit ty_unit tt *)
    (*   | pat_pair x y => fun Exy => match snocView Exy with *)
    (*                                  isSnoc Ex ty => *)
    (*                                  match snocView Ex with *)
    (*                                    isSnoc _ tx => term_binop binop_pair tx ty *)
    (*                                  end *)
    (*                                end *)
    (*   | pat_tuple p  => fun EΔ => term_tuple (tuple_pattern_match_env_reverse p EΔ) *)
    (*   | pat_record p => fun EΔ => term_record _ (record_pattern_match_env_reverse p EΔ) *)
    (*   end. *)

    (* Definition angelic_match_pattern {N : Set} (n : N -> 𝑺) {AT σ} {Δ : NCtx N Ty} (p : Pattern Δ σ) : *)
    (*   ⊢ Message -> STerm σ -> □((fun Σ => NamedEnv (Term Σ) Δ) -> 𝕊 AT) -> 𝕊 AT := *)
    (*   fun w0 msg t k => *)
    (*     angelic_freshen_ctx n Δ *)
    (*       (fun w1 ω01 (ts : (fun Σ : LCtx => NamedEnv (Term Σ) Δ) w1) => *)
    (*        assert_formulak (subst msg ω01) (formula_eq (subst t ω01) (pattern_match_env_reverse p ts)) *)
    (*          (fun w2 ω12 => k w2 (acc_trans ω01 ω12) (subst ts ω12))). *)

    (* Definition demonic_match_pattern {N : Set} (n : N -> 𝑺) {AT σ} {Δ : NCtx N Ty} (p : Pattern Δ σ) : *)
    (*   ⊢ STerm σ -> □((fun Σ => NamedEnv (Term Σ) Δ) -> 𝕊 AT) -> 𝕊 AT := *)
    (*   fun w0 t k => *)
    (*     demonic_ctx n Δ *)
    (*       (fun w1 ω01 (ts : (fun Σ : LCtx => NamedEnv (Term Σ) Δ) w1) => *)
    (*        assume_formulak (formula_eq (subst t ω01) (pattern_match_env_reverse p ts)) *)
    (*          (fun w2 ω12 => k w2 (acc_trans ω01 ω12) (subst ts ω12))). *)

    (* Definition angelic_match_union' {N : Set} (n : N -> 𝑺) {AT U} {Δ : 𝑼𝑲 U -> NCtx N Ty} *)
    (*   (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)) : *)
    (*   ⊢ Message -> STerm (ty_union U) -> (∀ K, □((fun Σ => NamedEnv (Term Σ) (Δ K)) -> 𝕊 AT)) -> 𝕊 AT := *)
    (*   fun w0 msg t k => *)
    (*     angelic_finite msg *)
    (*       (fun K : 𝑼𝑲 U => *)
    (*        angelic None (𝑼𝑲_Ty K) *)
    (*          (fun w1 ω01 (t__field : Term w1 (𝑼𝑲_Ty K)) => *)
    (*           assert_formulak (subst msg ω01) (formula_eq (term_union U K t__field) (subst t ω01)) *)
    (*             (fun w2 ω12 => *)
    (*              let ω02 := wtrans ω01 ω12 in *)
    (*              angelic_match_pattern n (p K) (subst msg ω02) (subst t__field ω12) (four (k K) ω02)))). *)

    (* Definition angelic_match_union {N : Set} (n : N -> 𝑺) {AT U} {Δ : 𝑼𝑲 U -> NCtx N Ty} *)
    (*   (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)) : *)
    (*   ⊢ Message -> STerm (ty_union U) -> (∀ K, □((fun Σ => NamedEnv (Term Σ) (Δ K)) -> 𝕊 AT)) -> 𝕊 AT := *)
    (*   fun w0 msg t k => *)
    (*     match term_get_union t with *)
    (*     | Some (existT K t__field) => angelic_match_pattern n (p K) msg t__field (k K) *)
    (*     | None => angelic_match_union' n p msg t k *)
    (*     end. *)

    (* Definition demonic_match_union' {N : Set} (n : N -> 𝑺) {AT U} {Δ : 𝑼𝑲 U -> NCtx N Ty} *)
    (*   (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)) : *)
    (*   ⊢ STerm (ty_union U) -> (∀ K, □((fun Σ => NamedEnv (Term Σ) (Δ K)) -> 𝕊 AT)) -> 𝕊 AT := *)
    (*   fun w0 t k => *)
    (*     demonic_finite *)
    (*       (fun K : 𝑼𝑲 U => *)
    (*        demonic None (𝑼𝑲_Ty K) *)
    (*          (fun w1 ω01 (t__field : Term w1 (𝑼𝑲_Ty K)) => *)
    (*           assume_formulak (formula_eq (term_union U K t__field) (subst t ω01)) *)
    (*             (fun w2 ω12 => *)
    (*              demonic_match_pattern n (p K) (subst t__field ω12) (four (k K) (acc_trans ω01 ω12))))). *)

    (* Definition demonic_match_union {N : Set} (n : N -> 𝑺) {AT U} {Δ : 𝑼𝑲 U -> NCtx N Ty} *)
    (*   (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)) : *)
    (*   ⊢ STerm (ty_union U) -> (∀ K, □((fun Σ => NamedEnv (Term Σ) (Δ K)) -> 𝕊 AT)) -> 𝕊 AT := *)
    (*   fun w0 t k => *)
    (*     match term_get_union t with *)
    (*     | Some (existT K t__field) => demonic_match_pattern n (p K) t__field (k K) *)
    (*     | None => demonic_match_union' n p t k *)
    (*     end. *)

    Global Instance proper_debug {B} : Proper (eq ==> iff ==> iff) (@Debug B).
    Proof.
      unfold Proper, respectful.
      intros ? ? -> P Q PQ.
      split; intros []; constructor; intuition.
    Qed.

    (* Ltac wsimpl := *)
    (*   repeat *)
    (*     (try change (wctx (wsnoc ?w ?b)) with (ctx_snoc (wctx w) b); *)
    (*      try change (sub_acc (@wred_sup ?w ?b ?t)) with (sub_snoc (sub_id (wctx w)) b t); *)
    (*      try change (wco (wsnoc ?w ?b)) with (subst (wco w) (sub_wk1 (b:=b))); *)
    (*      try change (sub_acc (@wrefl ?w)) with (sub_id (wctx w)); *)
    (*      try change (sub_acc (@wsnoc_sup ?w ?b)) with (@sub_wk1 (wctx w) b); *)
    (*      try change (wctx (wformula ?w ?fml)) with (wctx w); *)
    (*      try change (sub_acc (acc_trans ?ω1 ?ω2)) with (subst (sub_acc ω1) (sub_acc ω2)); *)
    (*      try change (sub_acc (@wformula_sup ?w ?fml)) with (sub_id (wctx w)); *)
    (*      try change (wco (wformula ?w ?fml)) with (cons fml (wco w)); *)
    (*      try change (wco (@wsubst ?w _ _ ?xIn ?t)) with (subst (wco w) (sub_single xIn t)); *)
    (*      try change (wctx (@wsubst ?w _ _ ?xIn ?t)) with (ctx_remove xIn); *)
    (*      try change (sub_acc (@acc_subst_right ?w _ _ ?xIn ?t)) with (sub_single xIn t); *)
    (*      rewrite <- ?sub_comp_wk1_tail, ?inst_subst, ?subst_sub_id, *)
    (*        ?inst_sub_id, ?inst_sub_wk1, ?inst_sub_snoc, *)
    (*        ?inst_lift, ?inst_sub_single, ?inst_pathcondition_cons; *)
    (*      repeat *)
    (*        match goal with *)
    (*        | |- Debug _ _ <-> Debug _ _ => apply proper_debug *)
    (*        | |- (?A /\ ?B) <-> (?A /\ ?C) => apply and_iff_compat_l'; intro *)
    (*        | |- (?A -> ?B) <-> (?A -> ?C) => apply imp_iff_compat_l'; intro *)
    (*        | |- (exists x : ?X, _) <-> (exists y : ?X, _) => apply base.exist_proper; intro *)
    (*        | |- (forall x : ?X, _) <-> (forall y : ?X, _) => apply base.forall_proper; intro *)
    (*        | |- wp ?m _ ?ι -> wp ?m _ ?ι => apply wp_monotonic; intro *)
    (*        | |- wp ?m _ ?ι <-> wp ?m _ ?ι => apply wp_equiv; intro *)
    (*        | |- ?w ⊒ ?w => apply wrefl *)
    (*        | |- ?POST (@inst _ _ _ ?Σ1 ?x1 ?ι1) <-> ?POST (@inst _ _ _ ?Σ2 ?x2 ?ι2) => *)
    (*          assert (@inst _ _ _ Σ1 x1 ι1 = @inst _ _ _ Σ2 x2 ι2) as ->; auto *)
    (*        | |- ?POST (?inst _ _ _ ?Σ1 ?x1 ?ι1) -> ?POST (@inst _ _ _ ?Σ2 ?x2 ?ι2) => *)
    (*          assert (@inst _ _ _ Σ1 x1 ι1 = @inst _ _ _ Σ2 x2 ι2) as ->; auto *)
    (*        | Hdcl : mapping_dcl ?f |- *)
    (*          inst (?f ?w ?ω _) _ = inst (?f ?w ?ω _) _ => *)
    (*          apply (Hdcl w ω w ω wrefl) *)
    (*        | Hdcl : mapping_dcl ?f |- *)
    (*          inst (?f ?w0 wrefl _) _ = inst (?f ?w1 ?ω01 _) _ => *)
    (*          apply (Hdcl w0 wrefl w1 ω01 ω01) *)
    (*        | Hdcl : mapping_dcl ?f |- *)
    (*          inst (?f ?w1 ?ω01 _) _ = inst (?f ?w0 wrefl _) _ => *)
    (*          symmetry; apply (Hdcl w0 wrefl w1 ω01 ω01) *)
    (*        | Hdcl : arrow_dcl ?f |- *)
    (*          wp (?f ?w ?ω _) _ _ -> wp (?f ?w ?ω _) _ _  => *)
    (*          apply (Hdcl w ω w ω wrefl) *)
    (*        end). *)

  End SDijk.

  Section Configuration.

    Record Config : Type :=
      MkConfig
        { config_debug_function : forall Δ τ, 𝑭 Δ τ -> bool;
        }.

    Definition default_config : Config :=
      {| config_debug_function _ _ f := false;
      |}.

  End Configuration.

  Definition SMut (Γ1 Γ2 : PCtx) (A : TYPE) : TYPE :=
    □(A -> SStore Γ2 -> SHeap -> 𝕊) -> SStore Γ1 -> SHeap -> 𝕊.
  Bind Scope smut_scope with SMut.

  Module SMut.

    Section Basic.

      Definition dijkstra {Γ} {A : TYPE} :
        ⊢ SDijkstra A -> SMut Γ Γ A.
      Proof.
        intros w0 m POST δ0 h0.
        apply m.
        intros w1 ω01 a1.
        apply POST; auto.
        apply (persist (A := SStore Γ) δ0 ω01).
        apply (persist (A := SHeap) h0 ω01).
      Defined.

      Definition pure {Γ} {A : TYPE} :
        ⊢ A -> SMut Γ Γ A.
      Proof.
        intros w0 a k.
        apply k; auto. apply acc_refl.
      Defined.

      Definition bind {Γ1 Γ2 Γ3 A B} :
        ⊢ SMut Γ1 Γ2 A -> □(A -> SMut Γ2 Γ3 B) -> SMut Γ1 Γ3 B.
      Proof.
        intros w0 ma f k.
        unfold SMut, Impl, Box in *.
        apply ma; auto.
        intros w1 ω01 a1.
        apply f; auto.
        apply (four k ω01).
      Defined.

      Definition bind_box {Γ1 Γ2 Γ3 A B} :
        ⊢ □(SMut Γ1 Γ2 A) -> □(A -> SMut Γ2 Γ3 B) -> □(SMut Γ1 Γ3 B) :=
        fun w0 m f => bind <$> m <*> four f.

      (* Definition strength {Γ1 Γ2 A B Σ} `{Subst A, Subst B} (ma : SMut Γ1 Γ2 A Σ) (b : B Σ) : *)
      (*   SMut Γ1 Γ2 (fun Σ => A Σ * B Σ)%type Σ := *)
      (*   bind ma (fun _ ζ a => pure (a, subst b ζ)). *)

      Definition bind_right {Γ1 Γ2 Γ3 A B} :
        ⊢ SMut Γ1 Γ2 A -> □(SMut Γ2 Γ3 B) -> SMut Γ1 Γ3 B.
      Proof.
        intros w0 m k POST.
        apply m.
        intros w1 ω01 a1.
        apply k. auto.
        intros w2 ω12 b2.
        apply (four POST ω01); auto.
      Defined.

      (* Definition bind_left {Γ1 Γ2 Γ3 A B} `{Subst A} : *)
      (*   ⊢ □(SMut Γ1 Γ2 A) -> □(SMut Γ2 Γ3 B) -> □(SMut Γ1 Γ3 A). *)
      (* Proof. *)
      (*   intros w0 ma mb. *)
      (*   apply (bbind ma). *)
      (*   intros w1 ω01 a1 δ1 h1. *)
      (*   apply (bind (mb w1 ω01 δ1 h1)). *)
      (*   intros w2 ω12 [_ δ2 h2]. *)
      (*   apply (pure). *)
      (*   apply (subst a1 ω12). *)
      (*   auto. *)
      (*   auto. *)
      (* Defined. *)

      (* Definition map {Γ1 Γ2 A B} `{Subst A, Subst B} : *)
      (*   ⊢ □(SMut Γ1 Γ2 A) -> □(A -> B) -> □(SMut Γ1 Γ2 B) := *)
      (*   fun w0 ma f Σ1 ζ01 pc1 δ1 h1 => *)
      (*     map pc1 *)
      (*       (fun Σ2 ζ12 pc2 '(MkSMutResult a2 δ2 h2) => *)
      (*          MkSMutResult (f Σ2 (subst ζ01 ζ12) pc2 a2) δ2 h2) *)
      (*        (ma Σ1 ζ01 pc1 δ1 h1). *)

      Definition error {Γ1 Γ2 A D} (func : string) (msg : string) (data:D) :
        ⊢ SMut Γ1 Γ2 A :=
        fun w _ δ h =>
          error
            (EMsgHere
               {| msg_function := func;
                  msg_message := msg;
                  msg_program_context := Γ1;
                  msg_localstore := δ;
                  msg_heap := h;
                  msg_pathcondition := wco w
               |}).
      Global Arguments error {_ _ _ _} func msg data {w} _ _.

      Definition block {Γ1 Γ2 A} :
        ⊢ SMut Γ1 Γ2 A.
      Proof.
        intros w0 POST δ h.
        apply block.
      Defined.

      Definition angelic_binary {Γ1 Γ2 A} :
        ⊢ SMut Γ1 Γ2 A -> SMut Γ1 Γ2 A -> SMut Γ1 Γ2 A :=
        fun w m1 m2 POST δ1 h1 =>
          angelic_binary (m1 POST δ1 h1) (m2 POST δ1 h1).
      Definition demonic_binary {Γ1 Γ2 A} :
        ⊢ SMut Γ1 Γ2 A -> SMut Γ1 Γ2 A -> SMut Γ1 Γ2 A :=
        fun w m1 m2 POST δ1 h1 =>
          demonic_binary (m1 POST δ1 h1) (m2 POST δ1 h1).

      Definition angelic_list {A Γ} :
        ⊢ (SStore Γ -> SHeap -> Message) -> List A -> SMut Γ Γ A :=
        fun w msg xs POST δ h => dijkstra (SDijk.angelic_list (msg δ h) xs) POST δ h.

      Definition angelic_finite {Γ} F `{finite.Finite F} :
        ⊢ (SStore Γ -> SHeap -> Message) -> SMut Γ Γ ⌜F⌝ :=
        fun w msg POST δ h => dijkstra (SDijk.angelic_finite (msg δ h)) POST δ h.

      Definition demonic_finite {Γ} F `{finite.Finite F} :
        ⊢ SMut Γ Γ ⌜F⌝ :=
        fun w => dijkstra (SDijk.demonic_finite (w:=w)).

      Definition angelic {Γ} (x : option 𝑺) σ :
        ⊢ SMut Γ Γ (STerm σ) :=
        fun w => dijkstra (SDijk.angelic x σ (w:=w)).
      Global Arguments angelic {Γ} x σ {w}.

      Definition demonic {Γ} (x : option 𝑺) σ :
        ⊢ SMut Γ Γ (STerm σ) :=
        fun w => dijkstra (SDijk.demonic x σ (w:=w)).
      Global Arguments demonic {Γ} x σ {w}.

      Definition debug {AT DT D} `{Subst DT, Inst DT D, OccursCheck DT} {Γ1 Γ2} :
        ⊢ (SStore Γ1 -> SHeap -> DT) -> (SMut Γ1 Γ2 AT) -> (SMut Γ1 Γ2 AT).
      Proof.
        intros w0 d m POST δ h.
        eapply debug. eauto.
        eauto. eauto.
        apply d. auto. auto.
        apply m; auto.
      Defined.

      Definition angelic_ctx {N : Set} (n : N -> 𝑺) {Γ} :
        ⊢ ∀ Δ : NCtx N Ty, SMut Γ Γ (fun w => NamedEnv (Term w) Δ).
      Proof.
        intros w0 Δ. apply dijkstra.
        apply (SDijk.angelic_ctx n Δ).
      Defined.
      Global Arguments angelic_ctx {N} n {Γ} [w] Δ : rename.

      Definition demonic_ctx {N : Set} (n : N -> 𝑺) {Γ} :
        ⊢ ∀ Δ : NCtx N Ty, SMut Γ Γ (fun w => NamedEnv (Term w) Δ).
      Proof.
        intros w0 Δ. apply dijkstra.
        apply (SDijk.demonic_ctx n Δ).
      Defined.
      Global Arguments demonic_ctx {N} n {Γ} [w] Δ : rename.

    End Basic.

    Module SMutNotations.

      (* Notation "'⨂' x .. y => F" := *)
      (*   (smut_demonic (fun x => .. (smut_demonic (fun y => F)) .. )) : smut_scope. *)

      (* Notation "'⨁' x .. y => F" := *)
      (*   (smut_angelic (fun x => .. (smut_angelic (fun y => F)) .. )) : smut_scope. *)

      (* Infix "⊗" := smut_demonic_binary (at level 40, left associativity) : smut_scope. *)
      (* Infix "⊕" := smut_angelic_binary (at level 50, left associativity) : smut_scope. *)

      Notation "x <- ma ;; mb" := (bind ma (fun _ _ x => mb)) (at level 80, ma at level 90, mb at level 200, right associativity) : smut_scope.
      Notation "ma >>= f" := (bind ma f) (at level 50, left associativity) : smut_scope.
      Notation "ma >> mb" := (bind_right ma mb) (at level 50, left associativity) : smut_scope.
      (* Notation "m1 ;; m2" := (smut_bind_right m1 m2) : smut_scope. *)

    End SMutNotations.
    Import SMutNotations.
    Local Open Scope smut_scope.

    Section AssumeAssert.

      (* Add the provided formula to the path condition. *)
      Definition assume_formula {Γ} :
        ⊢ Formula -> SMut Γ Γ Unit.
      Proof.
        intros w0 fml. apply dijkstra.
        apply (SDijk.assume_formula fml).
      Defined.

      Definition box_assume_formula {Γ} :
        ⊢ Formula -> □(SMut Γ Γ Unit) :=
        fun w0 fml => assume_formula <$> persist fml.

      Definition assert_formula {Γ} :
        ⊢ Formula -> SMut Γ Γ Unit :=
        fun w0 fml POST δ0 h0 =>
          dijkstra
            (SDijk.assert_formula
               {| msg_function := "smut_assert_formula";
                  msg_message := "Proof obligation";
                  msg_program_context := Γ;
                  msg_localstore := δ0;
                  msg_heap := h0;
                  msg_pathcondition := wco w0
               |} fml)
            POST δ0 h0.

      Definition box_assert_formula {Γ} :
        ⊢ Formula -> □(SMut Γ Γ Unit) :=
        fun w0 fml => assert_formula <$> persist fml.

      Definition assert_formulas {Γ} :
        ⊢ List Formula -> SMut Γ Γ Unit.
      Proof.
        intros w0 fmls POST δ0 h0.
        eapply dijkstra.
        apply SDijk.assert_formulas.
        apply
          {| msg_function := "smut_assert_formula";
             msg_message := "Proof obligation";
             msg_program_context := Γ;
             msg_localstore := δ0;
             msg_heap := h0;
             msg_pathcondition := wco w0
          |}.
        apply fmls.
        apply POST.
        apply δ0.
        apply h0.
      Defined.

    End AssumeAssert.

    Section PatternMatching.

      (* Definition angelic_match_bool {Γ} : *)
      (*   ⊢ STerm ty_bool -> SMut Γ Γ ⌜bool⌝ := *)
      (*   fun w t POST δ h => *)
      (*     dijkstra *)
      (*       (SDijk.angelic_match_bool *)
      (*          {| msg_function := "SMut.angelic_match_bool"; *)
      (*             msg_message := "pattern match assertion"; *)
      (*             msg_program_context := Γ; *)
      (*             msg_localstore := δ; *)
      (*             msg_heap := h; *)
      (*             msg_pathcondition := wco w *)
      (*          |} t) *)
      (*       POST δ h. *)

      (* Definition demonic_match_bool {Γ} : *)
      (*   ⊢ STerm ty_bool -> SMut Γ Γ ⌜bool⌝ := *)
      (*   fun w t => dijkstra (SDijk.demonic_match_bool t). *)

      Definition angelic_match_bool' {AT} {Γ1 Γ2} :
        ⊢ STerm ty_bool -> □(SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t kt kf.
        apply angelic_binary.
        - eapply bind_right.
          apply assert_formula.
          (* apply *)
          (*   {| msg_function        := "smut_angelic_match_bool"; *)
          (*      msg_message         := "pattern match assertion"; *)
          (*      msg_program_context := Γ1; *)
          (*      msg_localstore      := δ0; *)
          (*      msg_heap            := h0; *)
          (*      msg_pathcondition   := wco w0; *)
          (*   |}. *)
          apply (formula_bool t).
          apply kt.
        - eapply bind_right.
          apply assert_formula.
          (* apply *)
          (*   {| msg_function        := "smut_angelic_match_bool"; *)
          (*      msg_message         := "pattern match assertion"; *)
          (*      msg_program_context := Γ1; *)
          (*      msg_localstore      := δ0; *)
          (*      msg_heap            := h0; *)
          (*      msg_pathcondition   := wco w0; *)
          (*   |}. *)
          apply (formula_bool (term_not t)).
          apply kf.
      Defined.

      Definition angelic_match_bool {AT} {Γ1 Γ2} :
        ⊢ STerm ty_bool -> □(SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT :=
        fun w0 t kt kf =>
          match term_get_lit t with
          | Some true => T kt
          | Some false => T kf
          | None => angelic_match_bool' t kt kf
          end.

      Definition box_angelic_match_bool {AT} {Γ1 Γ2} :
        ⊢ STerm ty_bool -> □(SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t kt kf =>
          angelic_match_bool <$> persist__term t <*> four kt <*> four kf.

      Definition demonic_match_bool' {AT} {Γ1 Γ2} :
        ⊢ STerm ty_bool -> □(SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t kt kf.
        apply demonic_binary.
        - eapply bind_right.
          apply assume_formula.
          apply (formula_bool t).
          apply kt.
        - eapply bind_right.
          apply assume_formula.
          apply (formula_bool (term_not t)).
          apply kf.
      Defined.

      Definition demonic_match_bool {AT} {Γ1 Γ2} :
        ⊢ STerm ty_bool -> □(SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT :=
        fun w0 t kt kf =>
          match term_get_lit t with
          | Some true => T kt
          | Some false => T kf
          | None => demonic_match_bool' t kt kf
          end.

      Definition box_demonic_match_bool {AT} {Γ1 Γ2} :
        ⊢ STerm ty_bool -> □(SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t kt kf =>
          demonic_match_bool <$> persist__term t <*> four kt <*> four kf.

      Definition angelic_match_enum {AT E} {Γ1 Γ2} :
        ⊢ STerm (ty_enum E) -> (⌜𝑬𝑲 E⌝ -> □(SMut Γ1 Γ2 AT)) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t cont.
        eapply bind.
        apply (angelic_finite (F := 𝑬𝑲 E)).
        intros δ h.
        apply
            {| msg_function        := "SMut.angelic_match_enum";
               msg_message         := "pattern match assertion";
               msg_program_context := Γ1;
               msg_localstore      := δ;
               msg_heap            := h;
               msg_pathcondition   := wco w0;
            |}.
        intros w1 ω01 EK.
        eapply bind_right.
        apply (assert_formula (formula_eq (persist__term t ω01) (term_enum E EK))).
        apply (four (cont EK)). auto.
      Defined.

      Definition demonic_match_enum {A E} {Γ1 Γ2} :
        ⊢ STerm (ty_enum E) -> (⌜𝑬𝑲 E⌝ -> □(SMut Γ1 Γ2 A)) -> SMut Γ1 Γ2 A.
      Proof.
        intros w0 t cont.
        eapply bind.
        apply (demonic_finite (F := 𝑬𝑲 E)).
        intros w1 ω01 EK.
        eapply bind_right.
        apply (assume_formula (formula_eq (persist__term t ω01) (term_enum E EK))).
        apply (four (cont EK)). auto.
      Defined.

      Definition box_demonic_match_enum {AT E} {Γ1 Γ2} :
        ⊢ STerm (ty_enum E) -> (⌜𝑬𝑲 E⌝ -> □(SMut Γ1 Γ2 AT)) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t k =>
          demonic_match_enum
            <$> persist__term t
            <*> (fun (w1 : World) (ω01 : w0 ⊒ w1) (EK : 𝑬𝑲 E) => four (k EK) ω01).

      Definition angelic_match_sum {AT Γ1 Γ2} (x y : 𝑺) {σ τ} :
        ⊢ STerm (ty_sum σ τ) -> □(STerm σ -> SMut Γ1 Γ2 AT) -> □(STerm τ -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t kinl kinr.
        apply angelic_binary.
        - eapply bind.
          apply (angelic (Some x) σ).
          intros w1 ω01 t1.
          eapply bind_right.
          apply assert_formula.
          apply (formula_eq (term_inl t1) (persist__term t ω01)).
          intros w2 ω12.
          apply (four kinl ω01). auto.
          apply (persist__term t1 ω12).
        - eapply bind.
          apply (angelic (Some y) τ).
          intros w1 ω01 t1.
          eapply bind_right.
          apply assert_formula.
          apply (formula_eq (term_inr t1) (persist__term t ω01)).
          intros w2 ω12.
          apply (four kinr ω01). auto.
          apply (persist__term t1 ω12).
      Defined.

      Definition demonic_match_sum {AT Γ1 Γ2} (x y : 𝑺) {σ τ} :
        ⊢ STerm (ty_sum σ τ) -> □(STerm σ -> SMut Γ1 Γ2 AT) -> □(STerm τ -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t kinl kinr.
        apply demonic_binary.
        - eapply bind.
          apply (demonic (Some x) σ).
          intros w1 ω01 t1.
          eapply bind_right.
          apply assume_formula.
          apply (formula_eq (term_inl t1) (persist__term t ω01)).
          intros w2 ω12.
          apply (four kinl ω01). auto.
          apply (persist__term t1 ω12).
        - eapply bind.
          apply (demonic (Some y) τ).
          intros w1 ω01 t1.
          eapply bind_right.
          apply assume_formula.
          apply (formula_eq (term_inr t1) (persist__term t ω01)).
          intros w2 ω12.
          apply (four kinr ω01). auto.
          apply (persist__term t1 ω12).
      Defined.

      Definition demonic_match_sum_lifted {AT Γ1 Γ2} (x y : 𝑺) {σ τ} :
        ⊢ STerm (ty_sum σ τ) -> □(STerm σ -> SMut Γ1 Γ2 AT) -> □(STerm τ -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t kinl kinr POST δ0 h0.
        eapply (SDijk.demonic_match_sum (A := fun w => SStore Γ2 w * SHeap w * AT w)%type x _ y _ _ t).
        - intros w1 ω01 t' POSTl.
          apply kinl. auto. auto.
          intros w2 ω12 a2 δ2 h2.
          apply POSTl. auto. auto.
          apply (persist (A := SStore _) δ0 ω01).
          apply (persist (A := SHeap) h0 ω01).
        - intros w1 ω01 t' POSTr.
          apply kinr. auto. auto.
          intros w2 ω12 a2 δ2 h2.
          apply POSTr. auto. auto.
          apply (persist (A := SStore _) δ0 ω01).
          apply (persist (A := SHeap) h0 ω01).
        - intros w1 ω01 [[δ1 h1] a1]. apply POST. auto. auto. auto. auto.
      Defined.

      Definition angelic_match_list {AT Γ1 Γ2} (x y : 𝑺) {σ} :
        ⊢ STerm (ty_list σ) -> □(SMut Γ1 Γ2 AT) -> □(STerm σ -> STerm (ty_list σ) -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t knil kcons.
        apply angelic_binary.
        - eapply bind_right.
          apply assert_formula.
          (* apply *)
          (*   {| msg_function        := "SMut.angelic_match_list"; *)
          (*      msg_message         := "pattern match assertion"; *)
          (*      msg_program_context := Γ1; *)
          (*      msg_localstore      := δ0; *)
          (*      msg_heap            := h0; *)
          (*      msg_pathcondition   := wco w0; *)
          (*   |}. *)
          apply (formula_eq (term_lit (ty_list σ) []) t).
          intros w1 ω01.
          apply knil. auto.
        - eapply bind.
          apply (angelic (Some x) σ).
          intros w1 ω01 thead.
          eapply bind.
          apply (angelic (Some y) (ty_list σ)).
          intros w2 ω12 ttail.
          eapply bind_right.
          apply assert_formula.
          (* apply *)
          (*   {| msg_function        := "SMut.angelic_match_list"; *)
          (*      msg_message         := "pattern match assertion"; *)
          (*      msg_program_context := Γ1; *)
          (*      msg_localstore      := subst δ0 (acc_trans ω01 ω12); *)
          (*      msg_heap            := subst h0 (acc_trans ω01 ω12); *)
          (*      msg_pathcondition   := wco w2; *)
          (*   |}. *)
          apply (formula_eq (term_binop binop_cons (persist__term thead ω12) ttail) (persist__term t (acc_trans ω01 ω12))).
          intros w3 ω23.
          apply (four kcons (acc_trans ω01 ω12)). auto.
          apply (persist__term thead (acc_trans ω12 ω23)).
          apply (persist__term ttail ω23).
      Defined.

      Definition box_angelic_match_list {AT Γ1 Γ2} (x y : 𝑺) {σ} :
        ⊢ STerm (ty_list σ) -> □(SMut Γ1 Γ2 AT) -> □(STerm σ -> STerm (ty_list σ) -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t knil kcons => angelic_match_list x y <$> persist__term t <*> four knil <*> four kcons.

      Definition demonic_match_list {AT Γ1 Γ2} (x y : 𝑺) {σ} :
        ⊢ STerm (ty_list σ) -> □(SMut Γ1 Γ2 AT) -> □(STerm σ -> STerm (ty_list σ) -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t knil kcons.
        apply demonic_binary.
        - eapply bind_right.
          apply assume_formula.
          apply (formula_eq (term_lit (ty_list σ) []) t).
          intros w1 ω01.
          apply knil. auto.
        - eapply bind.
          apply (demonic (Some x) σ).
          intros w1 ω01 thead.
          eapply bind.
          apply (demonic (Some y) (ty_list σ)).
          intros w2 ω12 ttail.
          eapply bind_right.
          apply assume_formula.
          apply (formula_eq (term_binop binop_cons (persist__term thead ω12) ttail) (persist__term t (acc_trans ω01 ω12))).
          intros w3 ω23.
          apply (four kcons (acc_trans ω01 ω12)). auto.
          apply (persist__term thead (acc_trans ω12 ω23)).
          apply (persist__term ttail ω23).
      Defined.

      Definition box_demonic_match_list {AT Γ1 Γ2} (x y : 𝑺) {σ} :
        ⊢ STerm (ty_list σ) -> □(SMut Γ1 Γ2 AT) -> □(STerm σ -> STerm (ty_list σ) -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t knil kcons => demonic_match_list x y <$> persist__term t <*> four knil <*> four kcons.

      Definition angelic_match_prod {AT} {Γ1 Γ2} (x y : 𝑺) {σ τ} :
        ⊢ STerm (ty_prod σ τ) -> □(STerm σ -> STerm τ -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        apply (bind (angelic (Some x) σ)).
        intros w1 ω01 tσ.
        apply (bind (angelic (Some y) τ)).
        intros w2 ω12 tτ.
        eapply bind_right.
        apply assert_formula.
          (* {| msg_function        := "SMut.angelic_match_prod"; *)
          (*    msg_message         := "pattern match assertion"; *)
          (*    msg_program_context := Γ1; *)
          (*    msg_localstore      := subst δ0 (acc_trans ω01 ω12); *)
          (*    msg_heap            := subst h0 (acc_trans ω01 ω12); *)
          (*    msg_pathcondition   := wco w2; *)
          (* |}. *)
        apply (formula_eq (term_binop binop_pair (persist__term tσ ω12) tτ) (persist__term t (acc_trans ω01 ω12))).
        intros w3 ω23.
        apply (four k (acc_trans ω01 ω12)). auto.
        apply (persist__term tσ (acc_trans ω12 ω23)).
        apply (persist__term tτ ω23).
      Defined.

      Definition box_angelic_match_prod {AT} {Γ1 Γ2} (x y : 𝑺) {σ τ} :
        ⊢ STerm (ty_prod σ τ) -> □(STerm σ -> STerm τ -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t k => angelic_match_prod x y <$> persist__term t <*> four k.

      Definition demonic_match_prod {AT} {Γ1 Γ2} (x y : 𝑺) {σ τ} :
        ⊢ STerm (ty_prod σ τ) -> □(STerm σ -> STerm τ -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        apply (bind (demonic (Some x) σ)).
        intros w1 ω01 tσ.
        apply (bind (demonic (Some y) τ)).
        intros w2 ω12 tτ.
        eapply bind_right.
        apply assume_formula.
        apply (formula_eq (term_binop binop_pair (persist__term tσ ω12) tτ) (persist__term t (acc_trans ω01 ω12))).
        intros w3 ω23.
        apply (four k (acc_trans ω01 ω12)). auto.
        apply (persist__term tσ (acc_trans ω12 ω23)).
        apply (persist__term tτ ω23).
      Defined.

      Definition box_demonic_match_prod {AT} {Γ1 Γ2} (x y : 𝑺) {σ τ} :
        ⊢ STerm (ty_prod σ τ) -> □(STerm σ -> STerm τ -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t k => demonic_match_prod x y <$> persist__term t <*> four k.

      Definition angelic_match_record' {N : Set} (n : N -> 𝑺) {AT R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) :
        ⊢ STerm (ty_record R) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        eapply bind.
        apply (angelic_ctx n Δ).
        intros w1 ω01 ts.
        eapply bind_right.
        apply assert_formula.
          (* {| msg_function        := "SMut.angelic_match_record"; *)
          (*    msg_message         := "pattern match assertion"; *)
          (*    msg_program_context := Γ1; *)
          (*    msg_localstore      := subst δ0 (acc_trans ω01 ω12); *)
          (*    msg_heap            := subst h0 (acc_trans ω01 ω12); *)
          (*    msg_pathcondition   := wco w2; *)
          (* |}. *)
        apply (formula_eq (term_record R (record_pattern_match_env_reverse p ts)) (persist__term t ω01)).
        intros w2 ω12.
        apply (four k ω01). auto.
        apply (persist (A := fun w => (fun Σ => NamedEnv (Term Σ) Δ) (wctx w)) ts ω12).
      Defined.

      Definition angelic_match_record {N : Set} (n : N -> 𝑺) {AT R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) :
        ⊢ STerm (ty_record R) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        destruct (term_get_record t).
        - apply (T k).
          apply (record_pattern_match_env p n0).
        - apply (angelic_match_record' n p t k).
      Defined.

      Definition box_angelic_match_record {N : Set} (n : N -> 𝑺) {AT R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) :
        ⊢ STerm (ty_record R) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t k => angelic_match_record n p <$> persist__term t <*> four k.

      Definition demonic_match_record' {N : Set} (n : N -> 𝑺) {AT R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) :
        ⊢ STerm (ty_record R) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        eapply bind.
        apply (demonic_ctx n Δ).
        intros w1 ω01 ts.
        eapply bind_right.
        apply assume_formula.
        apply (formula_eq (term_record R (record_pattern_match_env_reverse p ts)) (persist__term t ω01)).
        intros w2 ω12.
        apply (four k ω01). auto.
        apply (persist (A := fun w => (fun Σ => NamedEnv (Term Σ) Δ) (wctx w)) ts ω12).
      Defined.

      Definition demonic_match_record {N : Set} (n : N -> 𝑺) {AT R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) :
        ⊢ STerm (ty_record R) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        destruct (term_get_record t).
        - apply (T k).
          apply (record_pattern_match_env p n0).
        - apply (demonic_match_record' n p t k).
      Defined.

      Definition box_demonic_match_record {N : Set} (n : N -> 𝑺) {AT R Γ1 Γ2} {Δ : NCtx N Ty} (p : RecordPat (𝑹𝑭_Ty R) Δ) :
        ⊢ STerm (ty_record R) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t k => demonic_match_record n p <$> persist__term t <*> four k.

      Definition angelic_match_tuple {N : Set} (n : N -> 𝑺) {AT σs Γ1 Γ2} {Δ : NCtx N Ty} (p : TuplePat σs Δ) :
        ⊢ STerm (ty_tuple σs) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        eapply bind.
        apply (angelic_ctx n Δ).
        intros w1 ω01 ts.
        eapply bind_right.
        apply assert_formula.
          (* {| msg_function        := "SMut.angelic_match_tuple"; *)
          (*    msg_message         := "pattern match assertion"; *)
          (*    msg_program_context := Γ1; *)
          (*    msg_localstore      := subst δ0 (acc_trans ω01 ω12); *)
          (*    msg_heap            := subst h0 (acc_trans ω01 ω12); *)
          (*    msg_pathcondition   := wco w2; *)
        (* |}. *)
        apply (formula_eq (term_tuple (tuple_pattern_match_env_reverse p ts)) (persist__term t ω01)).
        intros w2 ω12.
        apply (four k ω01). auto.
        apply (persist (A := fun w => (fun Σ => NamedEnv (Term Σ) Δ) (wctx w)) ts ω12).
      Defined.

      Definition box_angelic_match_tuple {N : Set} (n : N -> 𝑺) {AT σs Γ1 Γ2} {Δ : NCtx N Ty} (p : TuplePat σs Δ) :
        ⊢ STerm (ty_tuple σs) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t k => angelic_match_tuple n p <$> persist__term t <*> four k.

      Definition demonic_match_tuple {N : Set} (n : N -> 𝑺) {AT σs Γ1 Γ2} {Δ : NCtx N Ty} (p : TuplePat σs Δ) :
        ⊢ STerm (ty_tuple σs) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t k.
        eapply bind.
        apply (demonic_ctx n Δ).
        intros w1 ω01 ts.
        eapply bind_right.
        apply assume_formula.
        apply (formula_eq (term_tuple (tuple_pattern_match_env_reverse p ts)) (persist__term t ω01)).
        intros w2 ω12.
        apply (four k ω01). auto.
        apply (persist (A := fun w => (fun Σ => NamedEnv (Term Σ) Δ) (wctx w)) ts ω12).
      Defined.

      Definition box_demonic_match_tuple {N : Set} (n : N -> 𝑺) {AT σs Γ1 Γ2} {Δ : NCtx N Ty} (p : TuplePat σs Δ) :
        ⊢ STerm (ty_tuple σs) -> □((fun w => NamedEnv (Term w) Δ) -> SMut Γ1 Γ2 AT) -> □(SMut Γ1 Γ2 AT) :=
        fun w0 t k => demonic_match_tuple n p <$> persist__term t <*> four k.

      Definition angelic_match_pattern {N : Set} (n : N -> 𝑺) {σ} {Δ : NCtx N Ty} (p : Pattern Δ σ) {Γ} :
        ⊢ (SStore Γ -> SHeap -> Message) -> STerm σ -> SMut Γ Γ (fun w => NamedEnv (Term w) Δ).
      Proof.
        intros w0 msg t.
        eapply (bind).
        apply (angelic_ctx n Δ).
        intros w1 ω01 ts.
        eapply (bind_right).
        apply assert_formula.
        apply (formula_eq (pattern_match_env_reverse p ts) (persist__term t ω01)).
        intros w2 ω12.
        apply pure.
        apply (persist (A := fun w => (fun Σ => NamedEnv (Term Σ) Δ) (wctx w)) ts ω12).
      Defined.

      Definition demonic_match_pattern {N : Set} (n : N -> 𝑺) {σ} {Δ : NCtx N Ty} (p : Pattern Δ σ) {Γ} :
        ⊢ STerm σ -> SMut Γ Γ (fun w => NamedEnv (Term w) Δ).
      Proof.
        intros w0 t.
        eapply (bind).
        apply (demonic_ctx n Δ).
        intros w1 ω01 ts.
        eapply (bind_right).
        apply assume_formula.
        apply (formula_eq (pattern_match_env_reverse p ts) (persist__term t ω01)).
        intros w2 ω12.
        apply pure.
        apply (persist (A := fun w => (fun Σ => NamedEnv (Term Σ) Δ) (wctx w)) ts ω12).
      Defined.

      Definition angelic_match_union {N : Set} (n : N -> 𝑺) {AT Γ1 Γ2 U}
        {Δ : 𝑼𝑲 U -> NCtx N Ty} (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)) :
        ⊢ STerm (ty_union U) -> (∀ K, □((fun w => NamedEnv (Term w) (Δ K)) -> SMut Γ1 Γ2 AT)) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t cont.
        eapply bind.
        apply (angelic_finite (F := 𝑼𝑲 U)).
        intros δ h.
        apply
            {| msg_function        := "SMut.angelic_match_union";
               msg_message         := "pattern match assertion";
               msg_program_context := Γ1;
               msg_localstore      := δ;
               msg_heap            := h;
               msg_pathcondition   := wco w0;
            |}.
        intros w1 ω01 UK.
        eapply bind.
        apply (angelic None (𝑼𝑲_Ty UK)).
        intros w2 ω12 t__field.
        eapply bind_right.
        apply assert_formula.
        apply (formula_eq (term_union U UK t__field) (persist__term t (acc_trans ω01 ω12))).
        intros w3 ω23.
        eapply bind.
        apply (angelic_match_pattern n (p UK)).
        intros δ h.
        apply
            {| msg_function        := "SMut.angelic_match_union";
               msg_message         := "pattern match assertion";
               msg_program_context := Γ1;
               msg_localstore      := δ;
               msg_heap            := h;
               msg_pathcondition   := wco w3;
            |}.
        apply (persist__term t__field ω23).
        apply (four (cont UK)).
        apply (acc_trans ω01 (acc_trans ω12 ω23)).
      Defined.

      Definition box_angelic_match_union {N : Set} (n : N -> 𝑺) {AT Γ1 Γ2 U}
        {Δ : 𝑼𝑲 U -> NCtx N Ty} (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)) :
        ⊢ STerm (ty_union U) -> (∀ K, □((fun w => NamedEnv (Term w) (Δ K)) -> SMut Γ1 Γ2 AT)) -> □(SMut Γ1 Γ2 AT).
      Proof.
        refine (fun w0 t k => angelic_match_union n p <$> persist__term t <*> _).
        intros w1 ω01 UK. apply (four (k UK) ω01).
      Defined.

      Definition demonic_match_union {N : Set} (n : N -> 𝑺) {AT Γ1 Γ2 U}
        {Δ : 𝑼𝑲 U -> NCtx N Ty} (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)) :
        ⊢ STerm (ty_union U) -> (∀ K, □((fun w => NamedEnv (Term w) (Δ K)) -> SMut Γ1 Γ2 AT)) -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t cont.
        eapply bind.
        apply (demonic_finite (F := 𝑼𝑲 U)).
        intros w1 ω01 UK.
        eapply bind.
        apply (demonic None (𝑼𝑲_Ty UK)).
        intros w2 ω12 t__field.
        eapply bind_right.
        apply assume_formula.
        apply (formula_eq (term_union U UK t__field) (persist__term t (acc_trans ω01 ω12))).
        intros w3 ω23.
        eapply bind.
        apply (demonic_match_pattern n (p UK)).
        apply (persist__term t__field ω23).
        apply (four (cont UK)).
        apply (acc_trans ω01 (acc_trans ω12 ω23)).
      Defined.

      Definition box_demonic_match_union {N : Set} (n : N -> 𝑺) {AT Γ1 Γ2 U}
        {Δ : 𝑼𝑲 U -> NCtx N Ty} (p : forall K : 𝑼𝑲 U, Pattern (Δ K) (𝑼𝑲_Ty K)) :
        ⊢ STerm (ty_union U) -> (∀ K, □((fun w => NamedEnv (Term w) (Δ K)) -> SMut Γ1 Γ2 AT)) -> □(SMut Γ1 Γ2 AT).
      Proof.
        refine (fun w0 t k => demonic_match_union n p <$> persist__term t <*> _).
        intros w1 ω01 UK. apply (four (k UK) ω01).
      Defined.

    End PatternMatching.

    Section State.

      Definition pushpop {AT Γ1 Γ2 x σ} :
        ⊢ STerm σ -> SMut (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) AT -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 t m POST δ h.
        apply m.
        intros w1 ω01 a1 δ1 h1.
        apply POST. auto. auto. apply (env_tail δ1). apply h1.
        apply env_snoc.
        apply δ.
        apply t.
        apply h.
      Defined.

      Definition pushspops {AT Γ1 Γ2 Δ} :
        ⊢ SStore Δ -> SMut (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) AT -> SMut Γ1 Γ2 AT.
      Proof.
        intros w0 δΔ m POST δ h.
        apply m.
        intros w1 ω01 a1 δ1 h1.
        apply POST. auto. auto. apply (env_drop Δ δ1). apply h1.
        apply env_cat.
        apply δ.
        apply δΔ.
        apply h.
      Defined.

      Definition get_local {Γ} : ⊢ SMut Γ Γ (SStore Γ) :=
        fun w0 POST δ => T POST δ δ.
      Definition put_local {Γ1 Γ2} : ⊢ SStore Γ2 -> SMut Γ1 Γ2 Unit :=
        fun w0 δ POST _ => T POST tt δ.
      Definition get_heap {Γ} : ⊢ SMut Γ Γ SHeap :=
        fun w0 POST δ h => T POST h δ h.
      Definition put_heap {Γ} : ⊢ SHeap -> SMut Γ Γ Unit :=
        fun w0 h POST δ _ => T POST tt δ h.

      Definition eval_exp {Γ σ} (e : Exp Γ σ) :
        ⊢ SMut Γ Γ (STerm σ).
        intros w POST δ h.
        apply (T POST).
        apply (seval_exp δ e).
        auto.
        auto.
      Defined.

      Definition eval_exps {Γ} {σs : PCtx} (es : NamedEnv (Exp Γ) σs) :
        ⊢ SMut Γ Γ (SStore σs).
        intros w POST δ h.
        apply (T POST).
        refine (env_map _ es).
        intros b. apply (seval_exp δ).
        auto.
        auto.
      Defined.

      Definition assign {Γ} x {σ} {xIn : x∷σ ∈ Γ} : ⊢ STerm σ -> SMut Γ Γ Unit :=
        fun w0 t POST δ => T POST tt (δ ⟪ x ↦ t ⟫).
      Global Arguments assign {Γ} x {σ xIn w} v.

    End State.

    Section ProduceConsume.

      Definition produce_chunk {Γ} :
        ⊢ Chunk -> SMut Γ Γ Unit :=
        fun w0 c k δ h => T k tt δ (cons c h).

      Fixpoint try_consume_chunk_exact {Σ} (h : SHeap Σ) (c : Chunk Σ) {struct h} : option (SHeap Σ) :=
        match h with
        | nil       => None
        | cons c' h =>
          if chunk_eqb c c'
          then Some (if is_duplicable c then (cons c h) else h)
          else option_map (cons c') (try_consume_chunk_exact h c)
        end.

      Equations(noeqns) match_chunk {w : World} (c1 c2 : Chunk w) : List Formula w :=
        match_chunk (chunk_user p1 vs1) (chunk_user p2 vs2)
        with eq_dec p1 p2 => {
          match_chunk (chunk_user p1 vs1) (chunk_user ?(p1) vs2) (left eq_refl) := formula_eqs_ctx vs1 vs2;
          match_chunk (chunk_user p1 vs1) (chunk_user p2 vs2) (right _) :=
            cons (formula_bool (term_lit ty_bool false)) nil
        };
        match_chunk (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2)
        with eq_dec_het r1 r2 => {
          match_chunk (chunk_ptsreg r1 v1) (chunk_ptsreg ?(r1) v2) (left eq_refl) := cons (formula_eq v1 v2) nil;
          match_chunk (chunk_ptsreg r1 v1) (chunk_ptsreg r2 v2) (right _)      :=
            cons (formula_bool (term_lit ty_bool false)) nil
        };
        match_chunk (chunk_conj c11 c12) (chunk_conj c21 c22) :=
          app (match_chunk c11 c21) (match_chunk c12 c22);
        match_chunk (chunk_wand c11 c12) (chunk_wand c21 c22) :=
          app (match_chunk c11 c21) (match_chunk c12 c22);
        match_chunk _ _  := cons (formula_bool (term_lit ty_bool false)) nil.

      Lemma inst_match_chunk {w : World} (c1 c2 : Chunk w) (ι : SymInstance w) :
        instpc (match_chunk c1 c2) ι <-> inst c1 ι = inst c2 ι.
      Proof.
        revert c2.
        induction c1 as [p1 ts1|σ1 r1 t1|c11 IHc11 c12 IHc12|c11 IHc11 c12 IHc12];
          intros [p2 ts2|σ2 r2 t2|c21 c22|c21 c22]; cbn; rewrite ?inst_pathcondition_cons;
            try (split; intros Heq; cbn in Heq; destruct_conjs; discriminate);
            change (inst_chunk ?c ?ι) with (inst c ι).
        - split.
          + destruct (eq_dec p1 p2) as [Heqp|Hneqp].
            * destruct Heqp; cbn. rewrite inst_formula_eqs_ctx. intuition.
            * intros HYP. cbv in HYP. discriminate.
          + remember (inst ts1 ι) as vs1.
            remember (inst ts2 ι) as vs2.
            intros Heq. dependent elimination Heq.
            rewrite EqDec.eq_dec_refl. cbn.
            rewrite inst_formula_eqs_ctx.
            subst. auto.
        - split.
          + destruct (eq_dec_het r1 r2).
            * dependent elimination e; cbn.
              rewrite inst_pathcondition_cons.
              now intros [-> _].
            * intros HYP; cbv in HYP. discriminate.
          + remember (inst t1 ι) as v1.
            remember (inst t2 ι) as v2.
            intros Heq. dependent elimination Heq.
            unfold eq_dec_het.
            rewrite EqDec.eq_dec_refl. cbn.
            rewrite inst_pathcondition_cons.
            subst. split; auto. constructor.
        - rewrite inst_pathcondition_app, IHc11, IHc12.
          split; [intuition|].
          generalize (inst c11 ι), (inst c12 ι), (inst c21 ι), (inst c22 ι).
          clear. intros * Heq. dependent elimination Heq; auto.
        - rewrite inst_pathcondition_app, IHc11, IHc12.
          split; [intuition|].
          generalize (inst c11 ι), (inst c12 ι), (inst c21 ι), (inst c22 ι).
          clear. intros * Heq. dependent elimination Heq; auto.
      Qed.

      Definition consume_chunk {Γ} :
        ⊢ Chunk -> SMut Γ Γ Unit.
      Proof.
        intros w0 c.
        eapply bind.
        apply get_heap.
        intros w1 ω01 h.
        destruct (try_consume_chunk_exact h (persist c ω01)) as [h'|].
        - apply put_heap.
          apply h'.
        - eapply bind.
          apply (angelic_list
                   (A := Pair Chunk SHeap)
                   (fun δ h =>
                      {| msg_function := "consume_chunk";
                         msg_message := "Empty extraction";
                         msg_program_context := Γ;
                         msg_localstore := δ;
                         msg_heap := h;
                         msg_pathcondition := wco w1
                      |})
                   (heap_extractions h)).
          intros w2 ω12 [c' h'].
          eapply bind_right.
          apply assert_formulas.
          apply (match_chunk (persist c (acc_trans ω01 ω12)) c').
          intros w3 ω23.
          apply put_heap.
          apply (persist (A := SHeap) h' ω23).
      Defined.

      (* Definition smut_leakcheck {Γ Σ} : SMut Γ Γ Unit Σ := *)
      (*   smut_get_heap >>= fun _ _ h => *)
      (*   match h with *)
      (*   | nil => smut_pure tt *)
      (*   | _   => smut_error "SMut.leakcheck" "Heap leak" h *)
      (*   end. *)

      Definition produce_fail_recursion {Γ} :
        ⊢ Assertion -> SMut Γ Γ Unit.
      Proof.
        refine
          (fix produce w0 asn {struct asn} :=
             match asn with
             | asn_sep asn1 asn2 =>
               bind_right
                 (produce w0 asn1)
                 (* Recursive call to produce has principal argument equal to "persist asn2 ω01" *)
                 (* instead of one of the following variables: "asn1" "asn2". *)
                 (produce <$> persist asn2)
             | _ => @block _ _ _ _
             end).
      Abort.

      Definition produce {Γ} :
        ⊢ Assertion -> □(SMut Γ Γ Unit).
      Proof.
        refine (fix produce w0 asn {struct asn} := _).
        destruct asn.
        - apply (box_assume_formula fml).
        - apply (produce_chunk <$> persist c).
        - apply (demonic_match_bool <$> persist__term b <*> four (produce _ asn1) <*> four (produce _ asn2)).
        - intros w1 ω01.
          apply (demonic_match_enum
                    (persist__term k ω01)
                    (fun EK : 𝑬𝑲 E => four (produce w0 (alts EK)) ω01)).
        - refine (demonic_match_sum (AT := Unit) (Γ1 := Γ) (Γ2 := Γ) xl xr <$> persist__term s <*> four _ <*> four _).
          intros w1 ω01 t1.
          apply (produce (wsnoc w0 (xl∷σ)) asn1).
          apply (acc_snoc_left ω01 (xl∷σ) t1).
          intros w1 ω01 t1.
          apply (produce (wsnoc w0 (xr∷τ)) asn2).
          apply (acc_snoc_left ω01 (xr∷τ) t1).
        - apply (box_demonic_match_list xh xt s).
          + apply (produce _ asn1).
          + intros w1 ω01 thead ttail.
            apply (produce (wsnoc (wsnoc w0 (xh∷_)) (xt∷_)) asn2 w1).
            apply (acc_snoc_left (acc_snoc_left ω01 (xh∷_) thead) (xt∷_) ttail).
        - apply (box_demonic_match_prod xl xr s).
          intros w1 ω01 t1 t2.
          apply (produce (wsnoc (wsnoc w0 (xl∷σ1)) (xr∷σ2)) asn w1).
          apply (acc_snoc_left (acc_snoc_left ω01 (xl∷σ1) t1) (xr∷σ2) t2).
        - apply (box_demonic_match_tuple id p s).
          intros w1 ω01 ts.
          apply (produce (wcat w0 Δ) asn w1).
          apply acc_cat_left; auto.
        - apply (box_demonic_match_record id p s).
          intros w1 ω01 ts.
          apply (produce (wcat w0 Δ) asn w1).
          apply acc_cat_left; auto.
        - apply (box_demonic_match_union id alt__pat s).
          intros UK w1 ω01 ts.
          apply (produce (wcat w0 (alt__ctx UK)) (alt__rhs UK) w1).
          apply acc_cat_left; auto.
        - apply (bind_right <$> produce _ asn1 <*> four (produce _ asn2)).
        - apply (demonic_binary <$> produce _ asn1 <*> produce _ asn2).
        - intros w1 ω01.
          eapply bind.
          apply (@demonic _ (Some ς) τ).
          intros w2 ω12 t2.
          apply (produce (wsnoc w0 (ς∷τ)) asn w2).
          apply (acc_snoc_left (acc_trans ω01 ω12) (ς∷τ) t2).
        - intros w1 ω01.
          apply debug.
          intros δ h.
          apply (MkSDebugAsn (wco w1) δ h).
          apply pure.
          constructor.
      Defined.

      Definition consume {Γ} :
        ⊢ Assertion -> □(SMut Γ Γ Unit).
      Proof.
        refine (fix consume w0 asn {struct asn} := _).
        destruct asn.
        - apply (box_assert_formula fml).
        - apply (consume_chunk <$> persist c).
        - apply (angelic_match_bool <$> persist__term b <*> four (consume _ asn1) <*> four (consume _ asn2)).
        - intros w1 ω01.
          apply (angelic_match_enum
                    (persist__term k ω01)
                    (fun EK : 𝑬𝑲 E => four (consume w0 (alts EK)) ω01)).
        - refine (angelic_match_sum (AT := Unit) (Γ1 := Γ) (Γ2 := Γ) xl xr <$> persist__term s <*> four _ <*> four _).
          intros w1 ω01 t1.
          apply (consume (wsnoc w0 (xl∷σ)) asn1).
          apply (acc_snoc_left ω01 (xl∷σ) t1).
          intros w1 ω01 t1.
          apply (consume (wsnoc w0 (xr∷τ)) asn2).
          apply (acc_snoc_left ω01 (xr∷τ) t1).
        - apply (box_angelic_match_list xh xt s).
          + apply (consume _ asn1).
          + intros w1 ω01 thead ttail.
            apply (consume (wsnoc (wsnoc w0 (xh∷_)) (xt∷_)) asn2 w1).
            apply (acc_snoc_left (acc_snoc_left ω01 (xh∷_) thead) (xt∷_) ttail).
        - apply (box_angelic_match_prod xl xr s).
          intros w1 ω01 t1 t2.
          apply (consume (wsnoc (wsnoc w0 (xl∷σ1)) (xr∷σ2)) asn w1).
          apply (acc_snoc_left (acc_snoc_left ω01 (xl∷σ1) t1) (xr∷σ2) t2).
        - apply (box_angelic_match_tuple id p s).
          intros w1 ω01 ts.
          apply (consume (wcat w0 Δ) asn w1).
          apply acc_cat_left; auto.
        - apply (box_angelic_match_record id p s).
          intros w1 ω01 ts.
          apply (consume (wcat w0 Δ) asn w1).
          apply acc_cat_left; auto.
        - apply (box_angelic_match_union id alt__pat s).
          intros UK w1 ω01 ts.
          apply (consume (wcat w0 (alt__ctx UK)) (alt__rhs UK) w1).
          apply acc_cat_left; auto.
        - apply (bind_right <$> consume _ asn1 <*> four (consume _ asn2)).
        - apply (angelic_binary <$> consume _ asn1 <*> consume _ asn2).
        - intros w1 ω01.
          eapply bind.
          apply (@angelic _ (Some ς) τ).
          intros w2 ω12 t2.
          apply (consume (wsnoc w0 (ς∷τ)) asn w2).
          apply (acc_snoc_left (acc_trans ω01 ω12) (ς∷τ) t2).
        - intros w1 ω01.
          apply debug.
          intros δ h.
          apply (MkSDebugAsn (wco w1) δ h).
          apply pure.
          constructor.
      Defined.

    End ProduceConsume.

    Section Exec.

      Variable cfg : Config.

      Definition call_contract {Γ Δ τ} (c : SepContract Δ τ) :
        ⊢ SStore Δ -> SMut Γ Γ (STerm τ).
      Proof.
        destruct c as [Σe δe req result ens].
        intros w0 args.
        eapply bind.
        apply (angelic_ctx id Σe).
        intros w1 ω01 evars.
        eapply bind_right.
        apply (assert_formulas
                 (* {| *)
                 (*   msg_function := "SMut.call"; *)
                 (*   msg_message := "argument pattern match"; *)
                 (*   msg_program_context := Γ; *)
                 (*   msg_localstore := subst δ0 ω01; *)
                 (*   msg_heap := subst h0 ω01; *)
                 (*   msg_pathcondition := wco w1; *)
                 (* |} *) (formula_eqs_nctx (subst δe evars) (persist args ω01))).
        intros w2 ω12.
        eapply bind_right.
        apply (consume (w := @MkWorld Σe nil) req).
        refine (acc_trans _ ω12).
        constructor 2 with evars. cbn. constructor.
        intros w3 ω23.
        eapply bind.
        apply (demonic (Some result)).
        intros w4 ω34 res.
        eapply bind_right.
        apply (produce
                 (w := @MkWorld (Σe ▻ (result∷τ)) nil)
                 ens).
        constructor 2 with (sub_snoc (persist (A := Sub _) evars (acc_trans ω12 (acc_trans ω23 ω34))) (result∷τ) res).
        cbn. constructor.
        intros w5 ω45. clear - res ω45.
        apply pure.
        apply (persist__term res ω45).
      Defined.

      Definition call_lemma {Γ Δ} (lem : Lemma Δ) :
        ⊢ SStore Δ -> SMut Γ Γ Unit.
      Proof.
        destruct lem as [Σe δe req ens].
        intros w0 args.
        eapply bind.
        apply (angelic_ctx id Σe).
        intros w1 ω01 evars.
        eapply bind_right.
        apply (assert_formulas
                 (* {| *)
                 (*   msg_function := "SMut.call"; *)
                 (*   msg_message := "argument pattern match"; *)
                 (*   msg_program_context := Γ; *)
                 (*   msg_localstore := subst δ0 ω01; *)
                 (*   msg_heap := subst h0 ω01; *)
                 (*   msg_pathcondition := wco w1; *)
                 (* |} *) (formula_eqs_nctx (subst δe evars) (persist args ω01))).
        intros w2 ω12.
        eapply bind_right.
        apply (consume (w := @MkWorld Σe nil) req).
        refine (acc_trans _ ω12).
        constructor 2 with evars. cbn. constructor.
        intros w3 ω23.
        apply (produce
                 (w := @MkWorld Σe nil)
                 ens).
        constructor 2 with (persist (A := Sub _) evars (acc_trans ω12 ω23)).
        cbn. constructor.
      Defined.

      Definition call_contract_debug {Γ Δ τ} (f : 𝑭 Δ τ) (c : SepContract Δ τ) :
        ⊢ SStore Δ -> SMut Γ Γ (STerm τ) :=
        fun w0 δΔ =>
          let o := call_contract c δΔ in
          if config_debug_function cfg f
          then
            debug
              (fun δ h => {| sdebug_call_function_parameters := Δ;
                             sdebug_call_function_result_type := τ;
                             sdebug_call_function_name := f;
                             sdebug_call_function_contract := c;
                             sdebug_call_function_arguments := δΔ;
                             sdebug_call_program_context := Γ;
                             sdebug_call_pathcondition := wco w0;
                             sdebug_call_localstore := δ;
                             sdebug_call_heap := h|})
              o
          else o.

      Definition Exec := forall {Γ τ} (s : Stm Γ τ), ⊢ SMut Γ Γ (STerm τ).

      Section ExecAux.

        Variable rec : Exec.

        Fixpoint exec_aux {Γ τ} (s : Stm Γ τ) {struct s} :
          ⊢ SMut Γ Γ (STerm τ).
        Proof.
          intros w0; destruct s.
          - apply pure. apply (term_lit τ l).
          - apply (eval_exp e).
          - eapply bind. apply (exec_aux _ _ s1).
            intros w1 ω01 t1.
            eapply (pushpop t1).
            apply (exec_aux _ _ s2).
          - eapply (pushspops (lift δ)).
            apply (exec_aux _ _ s).
          - eapply bind.
            apply (exec_aux _ _ s).
            intros w1 ω01 t.
            eapply bind_right.
            apply (assign x t).
            intros w2 ω12.
            apply pure.
            apply (subst (T := STerm τ) t (sub_acc ω12)).
          - eapply bind.
            apply (eval_exps es).
            intros w1 ω01 args.
            destruct (CEnv f) as [c|].
            + apply (call_contract_debug f c args).
            + intros POST δΓ. refine (rec (Pi f) _ args).
              intros w2 ω12 res _. apply POST. apply ω12.
              apply res. refine (persist δΓ ω12).
          - rename δ into δΔ.
            eapply bind.
            apply get_local.
            intros w1 ω01 δ1.
            eapply bind_right.
            apply (put_local (lift δΔ)).
            intros w2 ω12.
            eapply bind.
            apply (exec_aux _ _ s).
            intros w3 ω23 t.
            eapply bind_right.
            apply put_local.
            apply (persist (A := SStore _) δ1 (acc_trans ω12 ω23)).
            intros w4 ω34.
            apply pure.
            apply (persist__term t ω34).
          - eapply bind.
            apply (eval_exps es).
            intros w1 ω01 args.
            apply (call_contract (CEnvEx f) args).
          - eapply bind_right.
            eapply bind.
            apply (eval_exps es).
            intros w1 ω01 args.
            apply (call_lemma (LEnv l) args).
            intros w2 ω12.
            apply (exec_aux _ _ s).
          - eapply bind. apply (eval_exp e).
            intros w1 ω01 t.
            apply (demonic_match_bool t).
            + intros w2 ω12.
              apply (exec_aux _ _ s1).
            + intros w2 ω12.
              apply (exec_aux _ _ s2).
          - eapply bind_right.
            apply (exec_aux _ _ s1).
            intros w1 ω01.
            apply (exec_aux _ _ s2).
          - eapply bind. apply (eval_exp e1).
            intros w1 ω01 t.
            eapply bind_right.
            apply (assume_formula (formula_bool t)).
            intros w2 ω12.
            apply (exec_aux _ _ s).
          - apply block.
          - eapply bind.
            apply (eval_exp e).
            intros w1 ω01 t.
            apply (demonic_match_list (𝑿to𝑺 xh) (𝑿to𝑺 xt) t).
            + intros w2 ω12.
              apply (exec_aux _ _ s1).
            + intros w2 ω12 thead ttail.
              eapply (pushspops (env_snoc (env_snoc env_nil (xh∷_) thead) (xt∷_) ttail)).
              apply (exec_aux _ _ s2).
          - eapply bind.
            apply (eval_exp e).
            intros w1 ω01 t.
            apply (demonic_match_sum (𝑿to𝑺 xinl) (𝑿to𝑺 xinr) t).
            + intros w2 ω12 tl.
              eapply (pushpop tl).
              apply (exec_aux _ _ s1).
            + intros w2 ω12 tr.
              eapply (pushpop tr).
              apply (exec_aux _ _ s2).
          - eapply bind.
            apply (eval_exp e).
            intros w1 ω01 t.
            apply (demonic_match_prod (𝑿to𝑺 xl) (𝑿to𝑺 xr) t).
            intros w2 ω12 t1 t2.
            eapply (pushspops (env_snoc (env_snoc env_nil (_∷_) t1) (_∷_) t2)).
            apply (exec_aux _ _ s).
          - eapply bind.
            apply (eval_exp e).
            intros w1 ω01 t.
            apply (demonic_match_enum t).
            intros EK.
            intros w2 ω12.
            apply (exec_aux _ _ (alts EK)).
          - eapply bind.
            apply (eval_exp e).
            intros w1 ω01 t.
            apply (demonic_match_tuple 𝑿to𝑺 p t).
            intros w2 ω12 ts.
            eapply (pushspops ts).
            apply (exec_aux _ _ s).
          - eapply bind.
            apply (eval_exp e).
            intros w1 ω01 t.
            apply (demonic_match_union 𝑿to𝑺 alt__pat t).
            intros UK w2 ω12 ts.
            eapply (pushspops ts).
            apply (exec_aux _ _ (alt__rhs UK)).
          - eapply bind.
            apply (eval_exp e).
            intros w1 ω01 t.
            apply (demonic_match_record 𝑿to𝑺 p t).
            intros w2 ω12 ts.
            eapply (pushspops ts).
            apply (exec_aux _ _ s).
          - eapply bind.
            apply (angelic None τ).
            intros w1 ω01 t.
            eapply bind_right.
            apply (T (consume (asn_chunk (chunk_ptsreg reg t)))).
            intros w2 ω12.
            eapply bind_right.
            apply (T (produce (asn_chunk (chunk_ptsreg reg (persist__term t ω12))))).
            intros w3 ω23.
            apply pure.
            apply (persist__term t (acc_trans ω12 ω23)).
          - eapply bind.
            eapply (angelic None τ).
            intros w1 ω01 told.
            eapply bind_right.
            apply (T (consume (asn_chunk (chunk_ptsreg reg told)))).
            intros w2 ω12.
            eapply bind.
            apply (eval_exp e).
            intros w3 ω23 tnew.
            eapply bind_right.
            apply (T (produce (asn_chunk (chunk_ptsreg reg tnew)))).
            intros w4 ω34.
            apply pure.
            apply (persist__term tnew ω34).
          - apply (error "SMut.exec" "stm_bind not supported" tt).
          - apply debug.
            intros δ0 h0.
            econstructor.
            apply (wco w0).
            apply δ0.
            apply h0.
            apply (exec_aux _ _ s).
        Defined.

      End ExecAux.

      Fixpoint exec (inline_fuel : nat) : Exec :=
        match inline_fuel with
        | O   => fun _ _ _ _ => error "SMut.exec" "out of fuel for inlining" tt
        | S n => @exec_aux (@exec n)
        end.
      Proof.
      Global Arguments exec _ {_ _} _ {w} _ _ _.

      Import Notations.

      Variable inline_fuel : nat.

      Definition exec_contract {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) :
        SMut Δ Δ Unit {| wctx := sep_contract_logic_variables c; wco := [] |} :=
        match c with
        | MkSepContract _ _ Σ δ req result ens =>
          produce (w:=@MkWorld _ _) req acc_refl >> fun w1 ω01 =>
          exec inline_fuel s >>= fun w2 ω12 res =>
          consume
            (w:=wsnoc (@MkWorld _ []) (result∷τ)%ctx)
            ens
            (acc_snoc_left (acc_trans ω01 ω12) (result∷τ)%ctx res)
        end.

      Definition exec_contract_path {Δ : PCtx} {τ : Ty} (c : SepContract Δ τ) (s : Stm Δ τ) : 𝕊 wnil :=
        demonic_close (exec_contract c s (fun w1 ω01 _ δ1 h1 => SymProp.block) (sep_contract_localstore c) nil).

      Definition ValidContractWithConfig {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
        VerificationCondition (prune (solve_uvars (prune (solve_evars (prune (exec_contract_path c body)))))).

    End Exec.

    Definition ok {Σ} (p : 𝕊 Σ) : bool :=
      match prune p with
      | SymProp.block => true
      | _           => false
      end.

    Lemma ok_sound {Σ} (p : 𝕊 Σ) (ι : SymInstance Σ) :
      is_true (ok p) -> safe p ι.
    Proof.
      rewrite <- prune_sound. unfold ok.
      generalize (prune p) as q. clear. intros q.
      destruct q; try discriminate; cbn; auto.
    Qed.

    Definition ValidContract {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      VerificationCondition (prune (solve_uvars (prune (solve_evars (prune (exec_contract_path default_config 1 c body)))))).

    Definition ValidContractReflect {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      is_true (ok (prune (solve_uvars (prune (solve_evars (prune (exec_contract_path default_config 1 c body))))))).

    Lemma validcontract_reflect_sound {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
      ValidContractReflect c body ->
      ValidContract c body.
    Proof.
      unfold ValidContractReflect, ValidContract. intros Hok.
      apply (ok_sound _ env_nil) in Hok. now constructor.
    Qed.

  End SMut.

End Mutators.
