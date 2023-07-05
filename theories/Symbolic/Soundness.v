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
     Signature
     Shallow.Executor
     Specification
     Symbolic.Executor
     Program
     Tactics.

Set Implicit Arguments.

Import ctx.notations.
Import env.notations.

Module Soundness
  (Import B    : Base)
  (Import PROG : Program B)
  (Import SIG  : Signature B)
  (Import SPEC : Specification B PROG SIG)
  (Import SOLV : SolverKit B SIG)
  (Import SHAL : ShallowExecOn B PROG SIG SPEC)
  (Import SYMB : SymbolicExecOn B PROG SIG SPEC SOLV).

  Import ModalNotations.
  Import SymProp.

  Declare Scope rel_scope.
  Delimit Scope rel_scope with R.

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
  Class Rel (AT : TYPE) (A : Type) : Type :=
    MkRel { RSat : forall (w : World) (ι : Valuation w), AT w -> A -> Prop }.
  Bind Scope rel_scope with Rel.
  #[global] Arguments MkRel [AT A] &.
  #[global] Arguments RSat {_ _} _ {w} ι _ _.
  (* We use the same script ℛ as in the paper. This encodes (ι,x,y) ∈ ℛ[_,_]
     from the paper as (ℛ ι x y), i.e. the types of the relation are implicit. *)

  Definition RValid {AT A} (R : Rel AT A) (t : Valid AT) (v : A) : Prop :=
    forall (w : World) (ι : Valuation w),
      instprop (wco w) ι -> RSat R ι (t w) v.
  #[local] Notation "ℛ⟦ R ⟧@{ ι }" := (RSat R%R ι) (format "ℛ⟦ R ⟧@{ ι }") .
  #[local] Notation "ℛ⟦ R ⟧" := (RValid R%R) (format "ℛ⟦ R ⟧").

  (* This instance can be used for any (first-class) symbolic data that can be
     instantiated with a valuation, i.e. symbolic terms, stores, heaps etc. *)
  Definition RInst AT A {instA : Inst AT A} : Rel AT A :=
    MkRel (fun _ ι t v => v = inst t ι).
  Arguments RInst _ _ {_}.

  (* Relatedness of symbolic and shallow propositions. The driving base case! *)
  #[export] Instance RProp : Rel SymProp Prop :=
    MkRel (fun _ ι SP P => (wsafe SP ι -> P)%type).

  #[export] Instance RBox {AT A} (RA : Rel AT A) : Rel (Box AT) A :=
    MkRel (fun w0 ι0 a0 a =>
      forall (w1 : World) (ω01 : w0 ⊒ w1) (ι1 : Valuation w1),
        ι0 = inst (sub_acc ω01) ι1 ->
        instprop (wco w1) ι1 ->
        ℛ⟦RA⟧@{ι1} (a0 w1 ω01) a).

  #[export] Instance RImpl {AT A BT B} (RA : Rel AT A) (RB : Rel BT B) :
    Rel (Impl AT BT) (A -> B) :=
    MkRel (fun w ι fs fc =>
             forall (ta : AT w) (a : A),
               ℛ⟦RA⟧@{ι} ta a ->
               ℛ⟦RB⟧@{ι} (fs ta) (fc a)).

  #[export] Instance RForall {𝑲}
    {AT : forall K : 𝑲, TYPE} {A : forall K : 𝑲, Type}
    (RA : forall K, Rel (AT K) (A K)) :
    Rel (@Forall 𝑲 AT) (forall K : 𝑲, A K) :=
    MkRel (fun w ι fs fc =>
             forall K : 𝑲,
               ℛ⟦RA K⟧@{ι} (fs K) (fc K)).

  #[export] Instance RVal (σ : Ty) : Rel (fun Σ => Term Σ σ) (Val σ) :=
    RInst (fun Σ => Term Σ σ) (Val σ).

  #[export] Instance RNEnv (N : Set) (Δ : NCtx N Ty) : Rel _ _ :=
    RInst (fun Σ => Env (fun τ => Term Σ (type τ)) Δ) (NamedEnv Val Δ).
  #[export] Instance REnv (Δ : Ctx Ty) : Rel _ _ :=
      RInst (fun Σ : LCtx => Env (Term Σ) Δ) (Env Val Δ).
  #[export] Instance RUnit : Rel Unit unit := RInst Unit unit.
  #[export] Instance RChunk : Rel Chunk SCChunk := RInst Chunk SCChunk.

  #[export] Instance RPathCondition : Rel PathCondition Prop :=
    MkRel (fun w ι fs p => instprop fs ι <-> p).
  #[export] Instance RFormula : Rel Formula Prop :=
    MkRel (fun w ι f p => instprop f ι <-> p).

  #[export] Instance RMsg M {AT A} (RA : Rel AT A) : Rel (M -> AT) A :=
    MkRel (fun w ι t v => forall m, RSat RA ι (t m) v).

  Inductive RList' {AT A} (R : Rel AT A) [w : World] (ι : Valuation w) :
    WList AT w -> list A -> Prop :=
  | rlist_nil : RList' R ι nil nil
  | rlist_cons {t v ts vs}:
    RSat R ι t v -> RList' R ι ts vs ->
    RList' R ι (cons t ts) (cons v vs).

  #[export] Instance RList {AT A} (R : Rel AT A) : Rel (WList AT) (list A) :=
    MkRel (RList' R).

  #[export] Instance RConst A : Rel (Const A) A := RInst (Const A) A.

  #[export] Instance RProd `(RA : Rel AT A, RB : Rel BT B) :
    Rel (WProd AT BT) (A * B)%type :=
    MkRel (fun w ι '(ta,tb) '(va,vb) =>
             ℛ⟦RA⟧@{ι} ta va /\ ℛ⟦RB⟧@{ι} tb vb).

  #[export] Instance RMatchResult {N σ} (p : @Pattern N σ) :
    Rel (SMatchResult p) (MatchResult p) :=
    MkRel
      (fun w ι '(existT pc1 ts) '(existT pc2 vs) =>
         exists e : pc1 = pc2,
           ℛ⟦RNEnv (PatternCaseCtx pc2)⟧@{ι}
             (eq_rect pc1 (fun pc => NamedEnv (Term w) (PatternCaseCtx pc))
                ts pc2 e)
             vs).

  #[export] Instance RIn b : Rel (ctx.In b) (Val (type b)) :=
    MkRel (fun w ι bIn v => env.lookup ι bIn = v).

  Module refinement.
    Module notations.
      Open Scope rel_scope.
      Notation "ℛ⟦ R ⟧@{ ι }" := (RSat R%R ι) (format "ℛ⟦ R ⟧@{ ι }").
      Notation "ℛ⟦ R ⟧" := (RValid R%R) (format "ℛ⟦ R ⟧").
      Notation "'ℙ'"    := (RProp) : rel_scope.
      Notation "A -> B" := (RImpl A%R B%R) : rel_scope.
      Notation "□ A"    := (RBox A%R) : rel_scope.
      Notation "'∀' x .. y , R " :=
        (RForall (fun x => .. (RForall (fun y => R)) ..))
          (at level 99, x binder, y binder, right associativity,
            format "'[  ' '[  ' ∀  x  ..  y ']' ,  '/' R ']'")
          : rel_scope.
    End notations.
  End refinement.
  Import refinement.notations.

  Lemma refine_four {AT A} (RA : Rel AT A) :
    forall (w0 : World) t v (ι0 : Valuation w0),
    forall w1 (ω01 : w0 ⊒ w1) (ι1 : Valuation w1),
      ι0 = inst (sub_acc ω01) ι1 ->
      ℛ⟦□RA⟧@{ι0} t v ->
      ℛ⟦□RA⟧@{ι1} (four t ω01) v.
  Proof.
    intros w0 t v ι0 w1 r01 ι1 -> Htv w2 ω12 ι2 -> Hpc2.
    apply Htv; auto. now rewrite sub_acc_trans, inst_subst.
  Qed.

  Lemma refine_T {AT A} (R : Rel AT A) :
    forall (w : World) t v (ι : Valuation w), instprop (wco w) ι ->
      ℛ⟦□R⟧@{ι} t v -> ℛ⟦R⟧@{ι} (T t) v.
  Proof.
    intros * Hpc ra. apply ra; auto.
    cbn. now rewrite inst_sub_id.
  Qed.

  Lemma refine_apply {AT A BT B} (RA : Rel AT A) (RB : Rel BT B) :
    forall (w : World) (ι : Valuation w) F f t v,
      ℛ⟦RA -> RB⟧@{ι} F f -> ℛ⟦RA⟧@{ι} t v -> ℛ⟦RB⟧@{ι} (F t) (f v).
  Proof. intros * rf ra. apply rf, ra. Qed.

  Lemma refine_inst_persist {AT A} `{InstSubst AT A, @SubstLaws AT _} :
    forall (w1 w2 : World) (r12 : w1 ⊒ w2)
           (ι1 : Valuation w1) (ι2 : Valuation w2)
           (t : AT w1) (v : A),
      ι1 = inst (sub_acc r12) ι2 ->
      ℛ⟦RInst AT A⟧@{ι1} t v ->
      ℛ⟦RInst AT A⟧@{ι2} (persist t r12) v.
  Proof. intros * -> ->. now rewrite <- inst_persist. Qed.

  Lemma refine_formula_persist :
    forall (w1 w2 : World) (r12 : w1 ⊒ w2)
           (ι1 : Valuation w1) (ι2 : Valuation w2)
           (f : Formula w1) (p : Prop),
      ι1 = inst (sub_acc r12) ι2 ->
      ℛ⟦RFormula⟧@{ι1} f p ->
      ℛ⟦RFormula⟧@{ι2} (persist f r12) p.
  Proof. cbn. intros * ->. now rewrite instprop_persist. Qed.

  Lemma refine_env_snoc {N : Set} (Δ : NCtx N Ty) :
    ℛ⟦RNEnv Δ -> ∀ b, RVal (type b) -> RNEnv (Δ ▻ b)⟧
      (fun w => env.snoc) env.snoc.
  Proof. intros w ι Hpc ts vs Htvs b t v Htv; cbn; f_equal; auto. Qed.

  Lemma refine_lift {AT A} `{InstLift AT A} {w0 : World} (ι0 : Valuation w0) (a : A) :
    ℛ⟦RInst AT A⟧@{ι0} (lift (T := AT) a) a.
  Proof. hnf. now rewrite inst_lift. Qed.

  Ltac wsimpl :=
    repeat
      (try change (wctx (wsnoc ?w ?b)) with (wctx w ▻ b);
       try change (wco (wsnoc ?w ?b)) with (subst (wco w) (sub_wk1 (b:=b)));
       try change (sub_acc (@acc_refl ?w)) with (sub_id (wctx w));
       try change (wctx (wformula ?w ?fml)) with (wctx w);
       try change (sub_acc (@acc_formula_right ?w ?fml)) with (sub_id (wctx w));
       try change (sub_acc (@acc_pathcondition_right ?w ?fmls)) with (sub_id (wctx w));
       try change (wco (wformula ?w ?fml)) with (cons fml (wco w));
       try change (wco (@wsubst ?w _ _ ?xIn ?t)) with (subst (wco w) (sub_single xIn t));
       try change (wctx (@wsubst ?w _ _ ?xIn ?t)) with (ctx.remove xIn);
       try change (sub_acc (@acc_subst_right ?w _ _ ?xIn ?t)) with (sub_single xIn t);
       rewrite <- ?sub_comp_wk1_tail, ?inst_subst, ?subst_sub_id,
         ?inst_sub_id, ?inst_sub_wk1, ?inst_sub_snoc,
         ?inst_lift, ?inst_sub_single_shift, ?instprop_snoc,
         ?sub_acc_trans, ?sub_acc_triangular, ?inst_triangular_right_inverse).

  Section SymProp.
    Import SymProp.

    Lemma refine_symprop_angelic_binary :
      ℛ⟦ℙ -> ℙ -> ℙ⟧ (@angelic_binary) (@or).
    Proof.
      intros w ι Hpc.
      intros PS1 PC1 HP1 PS2 PC2 HP2.
      intros [H1|H2]; [left|right]; auto.
    Qed.

    Lemma refine_symprop_demonic_binary :
      ℛ⟦ℙ -> ℙ -> ℙ⟧ (@demonic_binary) (@and).
    Proof.
      intros w ι Hpc.
      intros PS1 PC1 HP1 PS2 PC2 HP2.
      intros [H1 H2]; split; auto.
    Qed.
  End SymProp.

  (* Notation RPureSpecM R := (□(R -> ℙ) -> ℙ)%R. *)

  #[export] Instance RPureSpecM {AT A} (R : Rel AT A) :
    Rel (SPureSpecM AT) (CPureSpecM A) := □(R -> ℙ) -> ℙ.


  Module PureSpecM.

    #[local] Ltac solve :=
      repeat
        match goal with
        | |- RValid _ (fun w => _) _ => intros ?w ?ι ?Hpc
        | |- RValid (RMsg _ _) _ _ => intros ?w ?ι ?Hpc ?msg
        | |- RSat (RImpl _ _) _ (fun x => _) (fun y => _) => intros ?t ?v ?Htv
        | |- RSat (RMsg _ _) ?ι _ _ => intros ?msg
        | |- RSat _ _ (T _) _ => apply refine_T
        | |- RSat (RBox _) _ (fun w r => _) _ => intros ?w ?r ?ι ?Hι ?Hpc
        | Hι: _ = inst (sub_acc ?r) ?ι |- RSat (RBox _) ?ι (four _ ?r) _ =>
            apply (refine_four r Hι)
        end; auto.

    Lemma refine_pure {AT A} {R : Rel AT A} :
      ℛ⟦R -> RPureSpecM R⟧ SPureSpecM.pure CPureSpecM.pure.
    Proof.
      unfold RPureSpecM, SPureSpecM.pure, CPureSpecM.pure.
      solve. eapply refine_apply; solve.
    Qed.

    Lemma refine_bind `{RA : Rel AT A, RB : Rel BT B} :
      forall {w : World} (ι : Valuation w),
        ℛ⟦RPureSpecM RA -> □(RA -> RPureSpecM RB) -> RPureSpecM RB⟧@{ι}
          (SPureSpecM.bind (w:=w))
          CPureSpecM.bind.
    Proof.
      unfold RPureSpecM, SPureSpecM.bind, CPureSpecM.bind.
      intros. solve.
      eapply refine_apply; solve.
      eapply refine_apply; solve.
      eapply refine_apply; solve.
    Qed.

    (* This lemma has a nicer type, but an unused assumption. *)
    Lemma refine_bind' `{RA : Rel AT A, RB : Rel BT B} :
      ℛ⟦RPureSpecM RA -> □(RA -> RPureSpecM RB) -> RPureSpecM RB⟧
        SPureSpecM.bind CPureSpecM.bind.
    Proof. intros ? ? _. apply refine_bind. Qed.

    Lemma refine_error `{RA : Rel AT A} :
      ℛ⟦RMsg AMessage (RPureSpecM RA)⟧ SPureSpecM.error CPureSpecM.error.
    Proof. intros w ι Hpc m POST__s POST__c HPOST. inversion 1. Qed.

    Lemma refine_angelic (x : option LVar) :
      ℛ⟦∀ σ, RPureSpecM (RVal σ)⟧ (SPureSpecM.angelic x) CPureSpecM.angelic.
    Proof.
      intros w0 ι0 Hpc0 σ POST__s POST__c HPOST.
      intros [v Hwp]. exists v. revert Hwp.
      apply HPOST; cbn; eauto.
      now rewrite inst_sub_wk1.
      now rewrite instprop_subst, inst_sub_wk1.
    Qed.

    Lemma refine_angelic_ctx {N : Set} {n : N -> LVar} :
      ℛ⟦∀ Δ, RPureSpecM (RNEnv Δ)⟧
        (SPureSpecM.angelic_ctx n) CPureSpecM.angelic_ctx.
    Proof.
      intros w ι Hpc Δ; revert w ι Hpc; induction Δ as [|Δ IHΔ [x σ]];
        intros w0 ι0 Hpc0; cbn [SPureSpecM.angelic_ctx CPureSpecM.angelic_ctx].
      - now apply refine_pure.
      - apply refine_bind; auto.
        intros w1 ω01 ι1 Hι1 Hpc1.
        intros ts vs Htvs.
        eapply refine_bind.
        apply refine_angelic; auto.
        intros w2 ω12 ι2 Hι2 Hpc2.
        intros t v Htv.
        apply refine_pure; auto.
        apply refine_env_snoc; auto.
        eapply refine_inst_persist; eauto.

    Qed.

    Lemma refine_demonic (x : option LVar) :
      ℛ⟦∀ σ, RPureSpecM (RVal σ)⟧ (SPureSpecM.demonic x) CPureSpecM.demonic.
    Proof.
      intros w0 ι0 Hpc0 σ POST__s POST__c HPOST.
      intros Hwp v. cbn in Hwp. specialize (Hwp v).
      remember (fresh_lvar w0 x) as ℓ.
      revert Hwp. apply HPOST;
        [ (* Boilerplate #1 *) cbn; now rewrite inst_sub_wk1
        | (* Boilerplate #2 *) cbn; now rewrite instprop_subst, inst_sub_wk1
        | ].
      reflexivity.
    Qed.

    Lemma refine_demonic_ctx {N : Set} {n : N -> LVar} :
      ℛ⟦∀ Δ : NCtx N Ty, RPureSpecM (RNEnv Δ)⟧
        (SPureSpecM.demonic_ctx n) CPureSpecM.demonic_ctx.
    Proof.
      intros w ι Hpc Δ; revert w ι Hpc; induction Δ as [|Δ IHΔ [x σ]];
        intros w0 ι0 Hpc0; cbn [SPureSpecM.demonic_ctx CPureSpecM.demonic_ctx].
      - now apply refine_pure.
      - eapply refine_bind; auto.
        intros w1 ω01 ι1 Hι1 Hpc1.
        intros ts vs Htvs.
        eapply refine_bind.
        apply refine_demonic; auto.
        intros w2 ω12 ι2 Hι2 Hpc2.
        intros t v Htv.
        apply refine_pure; auto.
        apply refine_env_snoc; auto.
        eapply refine_inst_persist; eauto.
    Qed.

    Lemma refine_assume_pathcondition :
      ℛ⟦RPathCondition -> RPureSpecM RUnit⟧
        SPureSpecM.assume_pathcondition CPureSpecM.assume_formula.
    Proof.
      unfold SPureSpecM.assume_pathcondition, symprop_assume_pathcondition.
      intros w0 ι0 Hpc0 fmls0 p Heq POST__s POST__c HPOST.
      intros Hwp Hfmls0. apply Heq in Hfmls0.
      destruct (solver_spec _ fmls0) as [[w1 [ζ fmls1]] Hsolver|Hsolver].
      - specialize (Hsolver ι0 Hpc0).
        destruct Hsolver as [Hν Hsolver]. inster Hν by auto.
        specialize (Hsolver (inst (sub_triangular_inv ζ) ι0)).
        rewrite inst_triangular_right_inverse in Hsolver; auto.
        inster Hsolver by now try apply entails_triangular_inv.
        destruct Hsolver as [Hsolver _]. inster Hsolver by auto.
        rewrite safe_assume_triangular, safe_assume_pathcondition_without_solver in Hwp.
        specialize (Hwp Hν Hsolver). revert Hwp.
        unfold four. apply HPOST; cbn; wsimpl; auto.
        unfold PathCondition. rewrite instprop_cat. split; auto.
        now apply entails_triangular_inv.
      - intuition.
    Qed.

    Lemma refine_assume_formula :
      ℛ⟦RFormula -> RPureSpecM RUnit⟧
        SPureSpecM.assume_formula CPureSpecM.assume_formula.
    Proof.
      unfold SPureSpecM.assume_formula, CPureSpecM.assume_formula.
      solve. apply refine_assume_pathcondition; cbn; intuition.
    Qed.

    Lemma refine_assert_pathcondition :
      ℛ⟦RMsg AMessage (RPathCondition -> RPureSpecM RUnit)⟧
        SPureSpecM.assert_pathcondition CPureSpecM.assert_formula.
    Proof.
      unfold SPureSpecM.assert_pathcondition, CPureSpecM.assert_formula.
      intros w0 ι0 Hpc0 msg fmls0 p Heq POST__s POST__c HPOST Hwp.
      destruct (solver_spec _ fmls0) as [[w1 [ζ fmls1]] Hsolver|Hsolver].
      - specialize (Hsolver ι0 Hpc0). destruct Hsolver as [_ Hsolver].
        rewrite safe_assert_triangular in Hwp. destruct Hwp as [Hν Hwp].
        rewrite safe_assert_pathcondition_without_solver in Hwp.
        destruct Hwp as [Hfmls Hwp].
        split.
        + apply Hsolver in Hfmls; rewrite ?inst_triangular_right_inverse; auto.
          now apply Heq.
          now apply entails_triangular_inv.
        + revert Hwp. unfold four.
          apply HPOST; cbn; wsimpl; eauto.
          unfold PathCondition. rewrite instprop_cat. split; auto.
          now apply entails_triangular_inv.
      - intuition.
    Qed.

    Lemma refine_assert_formula :
      ℛ⟦RMsg AMessage (RFormula -> RPureSpecM RUnit)⟧
        SPureSpecM.assert_formula CPureSpecM.assert_formula.
    Proof.
      unfold SPureSpecM.assert_formula, CPureSpecM.assert_formula.
      solve. apply refine_assert_pathcondition; cbn; intuition.
    Qed.

    Lemma refine_angelic_binary `{R : Rel AT A} :
      ℛ⟦RPureSpecM R -> RPureSpecM R -> RPureSpecM R⟧
          SPureSpecM.angelic_binary CPureSpecM.angelic_binary.
    Proof.
      unfold RPureSpecM, SPureSpecM.angelic_binary, CPureSpecM.angelic_binary.
      solve. apply refine_symprop_angelic_binary; solve.
    Qed.

    Lemma refine_demonic_binary `{R : Rel AT A} :
      ℛ⟦RPureSpecM R -> RPureSpecM R -> RPureSpecM R⟧
          SPureSpecM.demonic_binary CPureSpecM.demonic_binary.
    Proof.
      unfold RPureSpecM, SPureSpecM.demonic_binary, CPureSpecM.demonic_binary.
      solve. apply refine_symprop_demonic_binary; solve.
    Qed.

    Lemma refine_block `{R : Rel AT A} :
      ℛ⟦RPureSpecM R⟧ (@SPureSpecM.block AT) CPureSpecM.block.
    Proof. constructor. Qed.

    Opaque RPureSpecM.

    Lemma refine_assert_eq_nenv {N : Set} :
      ℛ⟦∀ Δ : NCtx N Ty, RMsg _ (RNEnv Δ -> RNEnv Δ -> RPureSpecM RUnit)⟧
        SPureSpecM.assert_eq_nenv CPureSpecM.assert_eq_nenv.
    Proof.
      intros w0 ι0 Hpc0 Δ msg E1 ? -> E2 ? ->.
      induction E1; env.destroy E2; cbn - [RSat].
      - now apply refine_pure.
      - eapply refine_bind; first apply IHE1.
        intros w1 ω01 ι1 Hι1 Hpc1 _ _ _.
        apply refine_assert_formula; auto.
        eapply refine_formula_persist; eauto.
        cbn. reflexivity.
    Qed.

    Lemma refine_assert_eq_env :
      ℛ⟦∀ Δ, RMsg _ (REnv Δ -> REnv Δ -> RPureSpecM RUnit)⟧
        SPureSpecM.assert_eq_env CPureSpecM.assert_eq_env.
    Proof.
      intros w0 ι0 Hpc0 Δ msg E1 ? -> E2 ? ->.
      induction E1; env.destroy E2; cbn - [RSat].
      - now apply refine_pure.
      - eapply refine_bind; eauto.
        intros w1 ω01 ι1 Hι1 Hpc1 _ _ _.
        apply refine_assert_formula; auto.
        eapply refine_formula_persist; eauto.
        cbn. reflexivity.
    Qed.

    Lemma refine_assert_eq_chunk :
      ℛ⟦RMsg _ (RChunk -> RChunk -> □(RPureSpecM RUnit))⟧
        SPureSpecM.assert_eq_chunk CPureSpecM.assert_eq_chunk.
    Proof.
      intros w0 ι0 Hpc0 msg c ? -> c' ? ->. revert c'.
      induction c; intros [] w1 ω01 ι1 Hι1 Hpc1; cbn;
        auto; try (now apply refine_error).
      - destruct eq_dec.
        + destruct e; cbn.
          apply refine_assert_eq_env; auto.
          eapply refine_inst_persist; eauto; easy.
          eapply refine_inst_persist; eauto; easy.
        + now apply refine_error.
      - destruct eq_dec_het.
        + dependent elimination e; cbn.
          apply refine_assert_formula; auto. subst.
          now do 2 rewrite <- inst_persist.
        + now apply refine_error.
      - eapply refine_bind. apply IHc1; auto.
        intros w2 ω12 ι2 Hι2 Hpc2 _ _ _. apply IHc2; auto.
        subst. now rewrite sub_acc_trans, inst_subst, <- inst_persist.
      - eapply refine_bind. apply IHc1; auto.
        intros w2 ω12 ι2 Hι2 Hpc2 _ _ _. apply IHc2; auto.
        subst. now rewrite sub_acc_trans, inst_subst, <- inst_persist.
    Qed.

    Lemma refine_angelic_list' `{R : Rel AT A} :
      ℛ⟦R -> RList R -> RPureSpecM R⟧
        SPureSpecM.angelic_list' CPureSpecM.angelic_list'.
    Proof.
      intros w ι Hpc t v Htv ts vs Htvs. revert t v Htv.
      induction Htvs; cbn; intros ?t ?v ?Htv.
      - now apply refine_pure.
      - apply refine_angelic_binary; auto.
        now apply refine_pure.
    Qed.

    Lemma refine_angelic_list `{R : Rel AT A} :
      ℛ⟦RMsg AMessage (RList R -> RPureSpecM R)⟧
        SPureSpecM.angelic_list CPureSpecM.angelic_list.
    Proof.
      intros w ι Hpc msg ts vs [].
      - now apply refine_error.
      - now apply refine_angelic_list'.
    Qed.

    Lemma refine_demonic_list' `{R : Rel AT A} :
      ℛ⟦R -> RList R -> RPureSpecM R⟧
        SPureSpecM.demonic_list' CPureSpecM.demonic_list'.
    Proof.
      intros w ι Hpc t v Htv ts vs Htvs. revert t v Htv.
      induction Htvs; cbn; intros ?t ?v ?Htv.
      - now apply refine_pure.
      - apply refine_demonic_binary; auto.
        now apply refine_pure.
    Qed.

    Lemma refine_demonic_list `{R : Rel AT A} :
      ℛ⟦RList R -> RPureSpecM R⟧
        SPureSpecM.demonic_list CPureSpecM.demonic_list.
    Proof.
      intros w ι Hpc ts vs [].
      - now apply refine_block.
      - now apply refine_demonic_list'.
    Qed.

    Lemma refine_angelic_finite {F} `{finite.Finite F} :
      ℛ⟦RMsg _ (RPureSpecM (RConst F))⟧
        (SPureSpecM.angelic_finite F) (CPureSpecM.angelic_finite F).
    Proof.
      intros w ι Hpc msg. apply refine_angelic_list; auto.
      induction (finite.enum F); now constructor.
    Qed.

    Lemma refine_demonic_finite {F} `{finite.Finite F} :
      ℛ⟦RPureSpecM (RConst F)⟧
        (SPureSpecM.demonic_finite F) (CPureSpecM.demonic_finite F).
    Proof.
      intros w ι Hpc. apply refine_demonic_list; auto.
      induction (finite.enum F); now constructor.
    Qed.

    Lemma refine_pattern_match_regular {N : Set} (n : N -> LVar) {σ} (p : @Pattern N σ) :
      ℛ⟦RVal σ -> RPureSpecM (RMatchResult p)⟧
        (SPureSpecM.pattern_match_regular n p)
        (CPureSpecM.pattern_match p).
    Proof.
      cbv beta delta [RPureSpecM SPureSpecM.pattern_match_regular
                        CPureSpecM.pattern_match CPureSpecM.pure] iota.
      intros w ι Hpc t v -> POST__s POST__c HPOST. hnf. cbn beta delta [wsafe] iota.
      rewrite <- (pattern_match_val_freshen n p (Σ := w)).
      pose proof (pattern_match_val_inverse_left (freshen_pattern n w p) (inst t ι)).
      destruct pattern_match_val as [pc vs]. cbn - [acc_trans].
      unfold pattern_match_val_reverse' in H. cbn in H.
      intros Hsafe. refine (HPOST _ _ _ _ _ _ _ _ Hsafe); clear Hsafe;
        cbn - [sub_cat_left sub_cat_right sub_id];
        rewrite ?inst_subst, ?instprop_subst, ?inst_sub_id, ?inst_sub_cat_left; try easy.
      - rewrite inst_pattern_match_term_reverse. split; auto. rewrite <- H.
        f_equal. symmetry. apply inst_sub_cat_right.
      - exists eq_refl; cbn. rewrite inst_unfreshen_patterncaseenv.
        f_equal. symmetry. apply inst_sub_cat_right.
    Qed.

    Lemma refine_pattern_match_var {N : Set} (n : N -> LVar) {σ} (p : @Pattern N σ) :
      ℛ⟦∀ x, RIn (x∷σ) -> RPureSpecM (RMatchResult p)⟧
        (SPureSpecM.pattern_match_var n p)
        (fun x => CPureSpecM.pattern_match p).
    Proof.
    Admitted.

    Lemma refine_pattern_match_basic {N : Set} (n : N -> LVar) {σ} (p : @Pattern N σ) :
      ℛ⟦RVal σ -> RPureSpecM (RMatchResult p)⟧
        (SPureSpecM.pattern_match_basic n p)
        (CPureSpecM.pattern_match p).
    Proof.
      intros w ι HCι t v Htv. destruct t; cbn.
      now apply refine_pattern_match_var.
      all: now apply refine_pattern_match_regular.
    Qed.

    Lemma refine_pattern_match {N : Set} (n : N -> LVar) {σ} (p : @Pattern N σ) :
      ℛ⟦RVal σ -> RPureSpecM (RMatchResult p)⟧
        (SPureSpecM.pattern_match n p)
        (CPureSpecM.pattern_match p).
    Proof.
      induction p; intros w ι HCι t v ->; cbn [SPureSpecM.pattern_match].
      - apply refine_pure; auto. exists eq_refl; cbn; auto.
      - destruct (term_get_val_spec t) as [? ->|]; cbn.
        + apply refine_pure; auto. exists eq_refl; cbn; auto.
        + now apply refine_pattern_match_basic with (p := pat_bool).
      - now apply refine_pattern_match_basic.
      - destruct (term_get_pair_spec t) as [[t1 t2] ->|]; cbn.
        + apply refine_pure; auto. exists eq_refl; cbn; auto.
        + now apply refine_pattern_match_basic with (p := pat_pair _ _).
      - destruct (term_get_sum_spec t) as [[] ->|]; cbn.
        + apply refine_pure; auto. exists eq_refl; cbn; auto.
        + apply refine_pure; auto. exists eq_refl; cbn; auto.
        + now apply refine_pattern_match_basic with (p := pat_sum _ _ _ _).
      - apply refine_pure; auto. exists eq_refl; cbn; auto.
      - destruct (term_get_val_spec t) as [? ->|]; cbn.
        + apply refine_pure; auto. exists eq_refl; cbn; auto.
        + now apply refine_pattern_match_basic with (p := pat_enum E).
      - now apply refine_pattern_match_basic.
      - destruct (term_get_val_spec t) as [? ->|]; cbn.
        + apply refine_pure; auto. exists eq_refl; cbn; auto.
        + now apply refine_pattern_match_basic with (p := pat_bvec_exhaustive m).
      - destruct (term_get_tuple_spec t) as [ts ->|].
        + apply refine_pure; auto. exists eq_refl; cbn; auto.
          unfold tuple_pattern_match_val.
          now rewrite envrec.to_of_env, inst_tuple_pattern_match.
        + now apply refine_pattern_match_basic.
      - destruct (term_get_record_spec t) as [ts ->|].
        + apply refine_pure; auto. exists eq_refl; cbn; auto.
          unfold record_pattern_match_val.
          rewrite recordv_unfold_fold. symmetry.
          apply inst_record_pattern_match.
        + now apply refine_pattern_match_basic.
      - destruct (term_get_union_spec t) as [[K tf] Heq|].
        + specialize (H K w ι HCι tf (inst tf ι) eq_refl).
          change (base.equiv t (term_union U K tf)) in Heq.
          admit.
        + now apply refine_pattern_match_basic.
    Admitted.

  End PureSpecM.

  Section Basics.

    #[export] Instance RStore (Γ : PCtx) : Rel (SStore Γ) (CStore Γ) :=
      RInst (SStore Γ) (CStore Γ).
    #[export] Instance RHeap : Rel SHeap SCHeap := RInst SHeap SCHeap.

    #[export] Instance RHeapSpecM Γ1 Γ2 `(R : Rel AT A) :
      Rel (SHeapSpecM Γ1 Γ2 AT) (CHeapSpecM Γ1 Γ2 A) :=
      □(R -> RStore Γ2 -> RHeap -> ℙ) -> RStore Γ1 -> RHeap -> ℙ.

    Lemma refine_lift_purem {Γ} `{R : Rel AT A} :
      ℛ⟦RPureSpecM R -> RHeapSpecM Γ Γ R⟧
        SHeapSpecM.lift_purem CHeapSpecM.lift_purem.
    Proof.
      unfold RPureSpecM, RHeapSpecM, SHeapSpecM.lift_purem, CHeapSpecM.lift_purem.
      intros w ι Hpc ms mc Hm POST__s POST__c HPOST.
      intros δs δc Hδ hs hc Hh. apply Hm.
      intros w1 r01 ι1 Hι1 Hpc1 a1 a Ha.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      eapply refine_inst_persist; eauto.
      eapply refine_inst_persist; eauto.
    Qed.

    Lemma refine_block {Γ1 Γ2} `{R : Rel AT A} :
      ℛ⟦RHeapSpecM Γ1 Γ2 R⟧ SHeapSpecM.block CHeapSpecM.block.
    Proof. constructor. Qed.

    Lemma refine_error `{Subst M, OccursCheck M, R : Rel AT A} {Γ1 Γ2} :
      forall (cm : CHeapSpecM Γ1 Γ2 A),
        ℛ⟦RMsg _ (RHeapSpecM Γ1 Γ2 R)⟧ SHeapSpecM.error cm.
    Proof. intros cm w ι Hpc msg POST__s POST__c HPOST δs δc Hδ hs hc Hh []. Qed.

    Lemma refine_pure `{R : Rel AT A} {Γ} :
      ℛ⟦R -> RHeapSpecM Γ Γ R⟧ SHeapSpecM.pure CHeapSpecM.pure.
    Proof.
      unfold SHeapSpecM.pure, CHeapSpecM.pure.
      intros w ι Hpc t v Htv POST__s POST__c HPOST.
      eapply refine_apply; eauto.
      eapply refine_T; eauto.
    Qed.

    Lemma refine_bind `{RA : Rel AT A, RB : Rel BT B} {Γ1 Γ2 Γ3} :
      forall (w : World) (ι : Valuation w),
        ℛ⟦RHeapSpecM Γ1 Γ2 RA -> □(RA -> RHeapSpecM Γ2 Γ3 RB) -> RHeapSpecM Γ1 Γ3 RB⟧@{ι}
          (SHeapSpecM.bind (w := w)) CHeapSpecM.bind.
    Proof.
      unfold SHeapSpecM.bind, CHeapSpecM.bind.
      intros w ι ms mc Hm fs fc Hf POST__s POST__c HPOST δs δc Hδ hs hc Hh.
      apply Hm; eauto. intros w1 r01 ι1 Hι1 Hpc1 t v Htv.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      eapply refine_four; eauto.
    Qed.

    Lemma refine_bind' `{RA : Rel AT A, RB : Rel BT B} {Γ1 Γ2 Γ3} :
      ℛ⟦RHeapSpecM Γ1 Γ2 RA -> □(RA -> RHeapSpecM Γ2 Γ3 RB) -> RHeapSpecM Γ1 Γ3 RB⟧
        SHeapSpecM.bind CHeapSpecM.bind.
    Proof. intros ? ? _. apply refine_bind. Qed.

    Lemma refine_angelic (x : option LVar) {Γ} :
      ℛ⟦∀ σ, RHeapSpecM Γ Γ (RVal σ)⟧ (SHeapSpecM.angelic x) CHeapSpecM.angelic.
    Proof.
      unfold SHeapSpecM.angelic, CHeapSpecM.angelic.
      intros w ι Hpc σ. apply refine_lift_purem; auto.
      apply PureSpecM.refine_angelic; auto.
    Qed.

    Lemma refine_demonic (x : option LVar) {Γ} :
      ℛ⟦∀ σ, RHeapSpecM Γ Γ (RVal σ)⟧ (SHeapSpecM.demonic x) CHeapSpecM.demonic.
    Proof.
      unfold SHeapSpecM.demonic, CHeapSpecM.demonic.
      intros w ι Hpc σ. apply refine_lift_purem; auto.
      apply PureSpecM.refine_demonic; auto.
    Qed.

    Lemma refine_angelic_ctx {N : Set} {n : N -> LVar} {Γ} :
      ℛ⟦∀ Δ, RHeapSpecM Γ Γ (RNEnv Δ)⟧
        (SHeapSpecM.angelic_ctx n) CHeapSpecM.angelic_ctx.
    Proof.
      unfold SHeapSpecM.angelic_ctx, CHeapSpecM.angelic_ctx.
      intros w ι Hpc Δ. apply refine_lift_purem; auto.
      apply PureSpecM.refine_angelic_ctx; auto.
    Qed.

    Lemma refine_demonic_ctx {N : Set} {n : N -> LVar} {Γ} :
      ℛ⟦∀ Δ, RHeapSpecM Γ Γ (RNEnv Δ)⟧
        (SHeapSpecM.demonic_ctx n) CHeapSpecM.demonic_ctx.
    Proof.
      unfold SHeapSpecM.demonic_ctx, CHeapSpecM.demonic_ctx.
      intros w ι Hpc Δ. apply refine_lift_purem; auto.
      apply PureSpecM.refine_demonic_ctx; auto.
    Qed.

    Lemma refine_debug {AT A} `{R : Rel AT A}
      {Γ1 Γ2} {w0 : World} (ι0 : Valuation w0)
          (Hpc : instprop (wco w0) ι0) f ms mc :
      ℛ⟦RHeapSpecM Γ1 Γ2 R⟧@{ι0} ms mc ->
      ℛ⟦RHeapSpecM Γ1 Γ2 R⟧@{ι0} (@SHeapSpecM.debug AT Γ1 Γ2 w0 f ms) mc.
    Proof.
      intros Hap POST__s POST__c HPOST δs0 δc0 Hδ0 hs0 hc0 Hh0.
      intros [HP]. revert HP. apply Hap; auto.
    Qed.

    Lemma refine_angelic_binary {AT A} `{R : Rel AT A} {Γ1 Γ2} :
      ℛ⟦RHeapSpecM Γ1 Γ2 R -> RHeapSpecM Γ1 Γ2 R -> RHeapSpecM Γ1 Γ2 R⟧
        SHeapSpecM.angelic_binary CHeapSpecM.angelic_binary.
    Proof.
      intros w ι Hpc ms1 mc1 Hm1 ms2 mc2 Hm2.
      intros POST__s POST__c HPOST δs0 δc0 Hδ0 hs0 hc0 Hh0.
      unfold SHeapSpecM.angelic_binary, CHeapSpecM.angelic_binary.
      apply refine_symprop_angelic_binary; auto.
      apply Hm1; auto. apply Hm2; auto.
    Qed.

    Lemma refine_demonic_binary {AT A} `{R : Rel AT A} {Γ1 Γ2} :
      ℛ⟦RHeapSpecM Γ1 Γ2 R -> RHeapSpecM Γ1 Γ2 R -> RHeapSpecM Γ1 Γ2 R⟧
        SHeapSpecM.demonic_binary CHeapSpecM.demonic_binary.
    Proof.
      intros w ι Hpc ms1 mc1 Hm1 ms2 mc2 Hm2.
      intros POST__s POST__c HPOST δs0 δc0 Hδ0 hs0 hc0 Hh0.
      unfold SHeapSpecM.angelic_binary, CHeapSpecM.angelic_binary.
      apply refine_symprop_demonic_binary; auto.
      apply Hm1; auto. apply Hm2; auto.
    Qed.

    Lemma refine_angelic_list `{Subst M, OccursCheck M, R : Rel AT A} {Γ} :
      ℛ⟦RMsg _ (RList R -> RHeapSpecM Γ Γ R)⟧
        SHeapSpecM.angelic_list CHeapSpecM.angelic_list.
    Proof.
      intros w ι Hpc msg ls lc Hl.
      intros POST__s POST__c HPOST δs0 δc0 Hδ0 hs0 hc0 Hh0.
      unfold SHeapSpecM.angelic_list, CHeapSpecM.angelic_list.
      apply refine_lift_purem; auto.
      apply PureSpecM.refine_angelic_list; auto.
    Qed.

    Lemma refine_angelic_finite `{finite.Finite F} {Γ} :
      ℛ⟦RMsg _ (RHeapSpecM Γ Γ (RConst F))⟧
        (@SHeapSpecM.angelic_finite F _ _ Γ)
        (CHeapSpecM.angelic_finite F).
    Proof.
      intros w ι Hpc msg.
      intros POST__s POST__c HPOST δs0 δc0 Hδ0 hs0 hc0 Hh0.
      unfold SHeapSpecM.angelic_finite, CHeapSpecM.angelic_finite.
      eapply refine_lift_purem; eauto.
      apply PureSpecM.refine_angelic_finite; auto.
    Qed.

    Lemma refine_demonic_finite `{finite.Finite F} {Γ} :
      ℛ⟦RHeapSpecM Γ Γ (RConst F)⟧
        (@SHeapSpecM.demonic_finite F _ _ Γ)
        (CHeapSpecM.demonic_finite F).
    Proof.
      intros w ι Hpc.
      intros POST__s POST__c HPOST δs0 δc0 Hδ0 hs0 hc0 Hh0.
      unfold SHeapSpecM.demonic_finite, CHeapSpecM.demonic_finite.
      eapply refine_lift_purem; eauto.
      apply PureSpecM.refine_demonic_finite; auto.
    Qed.

  End Basics.

  Section AssumeAssert.

    Lemma refine_assume_formula {Γ} :
      ℛ⟦RFormula -> RHeapSpecM Γ Γ RUnit⟧
        SHeapSpecM.assume_formula CHeapSpecM.assume_formula.
    Proof.
      unfold SHeapSpecM.assume_formula, CHeapSpecM.assume_formula.
      intros w ι Hpc P p Hp. apply refine_lift_purem; auto.
      apply PureSpecM.refine_assume_formula; auto.
    Qed.

    Lemma refine_box_assume_formula {Γ} :
      ℛ⟦RFormula -> □(RHeapSpecM Γ Γ RUnit)⟧
        SHeapSpecM.box_assume_formula CHeapSpecM.assume_formula.
    Proof.
      unfold SHeapSpecM.box_assume_formula, fmap_box.
      intros w0 ι0 Hpc0 P p Hp w1 r01 ι1 Hι1 Hpc1.
      apply refine_assume_formula; auto.
      eapply refine_formula_persist; eauto.
    Qed.

    Lemma refine_assert_formula {Γ} :
      ℛ⟦RFormula -> RHeapSpecM Γ Γ RUnit⟧
        SHeapSpecM.assert_formula CHeapSpecM.assert_formula.
    Proof.
      intros w ι Hpc P p Hp.
      unfold SHeapSpecM.assert_formula, CHeapSpecM.assert_formula.
      intros POST__s POST__c HPOST δs δc Hδ hs hc Hh.
      apply refine_lift_purem; auto.
      now apply PureSpecM.refine_assert_formula.
    Qed.

    Lemma refine_box_assert_formula {Γ} :
      ℛ⟦RFormula -> □(RHeapSpecM Γ Γ RUnit)⟧
        SHeapSpecM.box_assert_formula CHeapSpecM.assert_formula.
    Proof.
      unfold SHeapSpecM.box_assert_formula, fmap_box.
      intros w0 ι0 Hpc0 P p Hp w1 r01 ι1 Hι1 Hpc1.
      apply refine_assert_formula; auto.
      eapply refine_formula_persist; eauto.
    Qed.

    Lemma refine_assert_pathcondition {Γ} :
      ℛ⟦RPathCondition -> RHeapSpecM Γ Γ RUnit⟧
        SHeapSpecM.assert_pathcondition CHeapSpecM.assert_formula.
    Proof.
      intros w ι Hpc Ps ps Hps POST__s POST__c HPOST δs δc Hδ hs hc Hh.
      apply refine_lift_purem; auto.
      now apply PureSpecM.refine_assert_pathcondition.
    Qed.

    Lemma refine_assert_eq_nenv {N Γ} (Δ : NCtx N Ty) :
      ℛ⟦RNEnv Δ -> RNEnv Δ -> RHeapSpecM Γ Γ RUnit⟧
        SHeapSpecM.assert_eq_nenv CHeapSpecM.assert_eq_nenv.
    Proof.
      intros w ι Hpc E1 ? ? E2 ? ? POST__s POST__c HPOST δs δc Hδ hs hc Hh.
      unfold SHeapSpecM.assert_eq_nenv, CHeapSpecM.assert_eq_nenv.
      apply refine_lift_purem; auto.
      apply PureSpecM.refine_assert_eq_nenv; auto.
    Qed.

    Lemma refine_assert_eq_chunk {Γ} :
      ℛ⟦RChunk -> RChunk -> RHeapSpecM Γ Γ RUnit⟧
        SHeapSpecM.assert_eq_chunk CHeapSpecM.assert_eq_chunk.
    Proof.
      intros w ι Hpc c1 ? ? E2 ? ? POST__s POST__c HPOST δs δc Hδ hs hc Hh.
      unfold SHeapSpecM.assert_eq_chunk, CHeapSpecM.assert_eq_chunk.
      apply refine_lift_purem; auto. apply refine_T; auto.
      apply PureSpecM.refine_assert_eq_chunk; cbn; eauto.
    Qed.

  End AssumeAssert.

  Section PatternMatching.

    Lemma refine_angelic_pattern_match' {N : Set} (n : N -> LVar) `{R : Rel AT A}
      {Γ1 Γ2 σ} (pat : @Pattern N σ) :
      ℛ⟦RVal σ -> (∀ K, □(RNEnv (PatternCaseCtx K) -> RHeapSpecM Γ1 Γ2 R)) -> RHeapSpecM Γ1 Γ2 R⟧
        (SHeapSpecM.angelic_pattern_match' n pat)
        (CHeapSpecM.angelic_pattern_match pat).
    Proof.
      intros w ι Hpc.
      intros t v ->.
      intros k k__c Hk.
      unfold SHeapSpecM.angelic_pattern_match', CHeapSpecM.angelic_pattern_match.
      apply refine_bind; auto.
      { now apply refine_angelic_finite. }
      intros w1 r01 ι1 Hι1 Hpc1.
      intros pc ? ->.
      apply refine_bind; auto.
      { now apply refine_angelic_ctx. }
      intros w2 r12 ι2 Hι2 Hpc2.
      intros ts vs Htvs.
      apply refine_bind; auto.
      { apply refine_assert_formula; try assumption. cbn.
        rewrite (inst_persist (AT := fun Σ => Term Σ _)).
        rewrite !sub_acc_trans, inst_subst.
        rewrite inst_pattern_match_term_reverse.
        hnf in Htvs. subst. reflexivity.
      }
      intros w3 r23 ι3 Hι3 Hpc3 _ _ _.
      apply Hk; auto.
      now subst; rewrite ?sub_acc_trans, ?inst_subst.
      hnf in Htvs. subst.
      eapply refine_inst_persist; eauto.
      cbn. reflexivity.
    Qed.

    Lemma refine_demonic_pattern_match' {N : Set} (n : N -> LVar) `{R : Rel AT A}
      {Γ1 Γ2 σ} (pat : @Pattern N σ) :
      ℛ⟦RVal σ -> (∀ K, □(RNEnv (PatternCaseCtx K) -> RHeapSpecM Γ1 Γ2 R)) -> RHeapSpecM Γ1 Γ2 R⟧
        (SHeapSpecM.demonic_pattern_match' n pat)
        (CHeapSpecM.demonic_pattern_match pat).
    Proof.
      intros w ι Hpc.
      intros t v ->.
      intros k k__c Hk.
      unfold SHeapSpecM.demonic_pattern_match', CHeapSpecM.demonic_pattern_match.
      apply refine_bind; auto.
      { now apply refine_demonic_finite. }
      intros w1 r01 ι1 Hι1 Hpc1.
      intros pc ? ->.
      apply refine_bind; auto.
      { now apply refine_demonic_ctx. }
      intros w2 r12 ι2 Hι2 Hpc2.
      intros ts vs Htvs.
      apply refine_bind; auto.
      { apply refine_assume_formula; try assumption. cbn.
        rewrite (inst_persist (AT := fun Σ => Term Σ _)).
        rewrite !sub_acc_trans, inst_subst.
        rewrite inst_pattern_match_term_reverse.
        hnf in Htvs. subst. reflexivity.
      }
      intros w3 r23 ι3 Hι3 Hpc3 _ _ _.
      apply Hk; auto.
      now subst; rewrite ?sub_acc_trans, ?inst_subst.
      hnf in Htvs. subst.
      eapply refine_inst_persist; eauto.
      cbn. reflexivity.
    Qed.

    Lemma refine_angelic_pattern_match {N : Set} (n : N -> LVar) `{R : Rel AT A}
      {Γ1 Γ2 σ} (pat : @Pattern N σ) :
      ℛ⟦RVal σ -> (∀ K, □(RNEnv (PatternCaseCtx K) -> RHeapSpecM Γ1 Γ2 R)) -> RHeapSpecM Γ1 Γ2 R⟧
        (SHeapSpecM.angelic_pattern_match n pat)
        (CHeapSpecM.angelic_pattern_match pat).
    Proof.
      induction pat; cbn; intros w ι Hpc.
      - intros t v ->.
        intros k k__c Hk.
        intros POST__s POST__c HPOST.
        intros δs0 δc0 -> hs0 hc0 ->. hnf.
        rewrite CHeapSpecM.wp_angelic_pattern_match.
        apply Hk; cbn; rewrite ?inst_sub_id; auto.
      - intros t v ->.
        intros k k__c Hk.
        destruct (term_get_val_spec t); subst.
        + intros POST__s POST__c HPOST.
          intros δs0 δc0 -> hs0 hc0 ->. hnf.
          rewrite CHeapSpecM.wp_angelic_pattern_match. cbn.
          apply Hk; cbn; rewrite ?inst_sub_id; auto.
        + apply refine_angelic_pattern_match'; auto. reflexivity.
      - apply (refine_angelic_pattern_match' n (pat_list σ x y)); auto.
      - intros t v ->.
        intros k k__c Hk.
        destruct (term_get_pair_spec t) as [[tl tr] Heq|]; subst.
        + rewrite Heq. intros POST__s POST__c HPOST.
          intros δs0 δc0 -> hs0 hc0 ->. hnf.
          rewrite CHeapSpecM.wp_angelic_pattern_match. cbn.
          apply Hk; cbn; rewrite ?inst_sub_id; auto.
        + apply refine_angelic_pattern_match'; auto. reflexivity.
      - intros t v ->.
        intros k k__c Hk.
        destruct (term_get_sum_spec t) as [[tl|tr] Heq|]; subst.
        + rewrite Heq. intros POST__s POST__c HPOST.
          intros δs0 δc0 -> hs0 hc0 ->. hnf.
          rewrite CHeapSpecM.wp_angelic_pattern_match. cbn.
          apply Hk; cbn; rewrite ?inst_sub_id; auto.
        + rewrite Heq. intros POST__s POST__c HPOST.
          intros δs0 δc0 -> hs0 hc0 ->. hnf.
          rewrite CHeapSpecM.wp_angelic_pattern_match. cbn.
          apply Hk; cbn; rewrite ?inst_sub_id; auto.
        + apply refine_angelic_pattern_match'; auto. reflexivity.
      - intros t v ->.
        intros k k__c Hk.
        intros POST__s POST__c HPOST.
        intros δs0 δc0 -> hs0 hc0 ->. hnf.
        rewrite CHeapSpecM.wp_angelic_pattern_match.
        apply Hk; cbn; rewrite ?inst_sub_id; auto.
      - intros t v ->.
        intros k k__c Hk.
        destruct (term_get_val_spec t); subst.
        + intros POST__s POST__c HPOST.
          intros δs0 δc0 -> hs0 hc0 ->. hnf.
          rewrite CHeapSpecM.wp_angelic_pattern_match. cbn.
          apply Hk; cbn; rewrite ?inst_sub_id; auto.
        + apply refine_angelic_pattern_match'; auto. reflexivity.
      - apply (refine_angelic_pattern_match' n (pat_bvec_split _ _ x y)); auto.
      - intros t v ->.
        intros k k__c Hk.
        destruct (term_get_val_spec t); subst.
        + intros POST__s POST__c HPOST.
          intros δs0 δc0 -> hs0 hc0 ->. hnf.
          rewrite CHeapSpecM.wp_angelic_pattern_match. cbn.
          apply Hk; cbn; rewrite ?inst_sub_id; auto.
        + apply refine_angelic_pattern_match'; auto. reflexivity.
      - apply (refine_angelic_pattern_match' n (pat_tuple p)); auto.
      - intros t v ->.
        intros k k__c Hk.
        destruct (term_get_record_spec t) as [ts Heq|]; subst.
        + rewrite Heq.
          intros POST__s POST__c HPOST.
          intros δs0 δc0 -> hs0 hc0 ->. hnf.
          rewrite CHeapSpecM.wp_angelic_pattern_match. cbn.
          apply Hk; cbn; rewrite ?inst_sub_id; auto.
          hnf. unfold record_pattern_match_val.
          rewrite recordv_unfold_fold.
          symmetry. apply inst_record_pattern_match.
        + apply refine_angelic_pattern_match'; auto. reflexivity.
      - intros t v ->.
        intros k k__c Hk.
        destruct (term_get_union_spec t) as [[K scr'] Heq|]; subst.
        + intros POST__s POST__c HPOST.
          intros δs0 δc0 Hδ0 hs0 hc0 Hh0.
          intros Hwp.
          specialize (H K w ι Hpc scr' (inst scr' ι) eq_refl
                        (fun pc => k (existT K pc))
                        (fun pc => k__c (existT K pc))).
          eapply H in Hwp; eauto.
          revert Hwp.
          rewrite ?CHeapSpecM.wp_angelic_pattern_match. cbn.
          rewrite Heq. rewrite unionv_unfold_fold.
          now destruct pattern_match_val; cbn.
          intros pc. apply (Hk (existT K pc)).
        + apply refine_angelic_pattern_match'; auto. reflexivity.
    Qed.

    Lemma refine_demonic_pattern_match {N : Set} (n : N -> LVar) `{R : Rel AT A}
      {Γ1 Γ2 σ} (pat : @Pattern N σ) :
      ℛ⟦RVal σ -> (∀ K, □(RNEnv (PatternCaseCtx K) -> RHeapSpecM Γ1 Γ2 R)) -> RHeapSpecM Γ1 Γ2 R⟧
        (SHeapSpecM.demonic_pattern_match n pat)
        (CHeapSpecM.demonic_pattern_match pat).
    Proof.
      induction pat; cbn; intros w ι Hpc.
      - intros t v ->.
        intros k k__c Hk.
        intros POST__s POST__c HPOST.
        intros δs0 δc0 -> hs0 hc0 ->. hnf.
        rewrite CHeapSpecM.wp_demonic_pattern_match.
        apply Hk; cbn; rewrite ?inst_sub_id; auto.
      - intros t v ->.
        intros k k__c Hk.
        destruct (term_get_val_spec t); subst.
        + intros POST__s POST__c HPOST.
          intros δs0 δc0 -> hs0 hc0 ->. hnf.
          rewrite CHeapSpecM.wp_demonic_pattern_match. cbn.
          apply Hk; cbn; rewrite ?inst_sub_id; auto.
        + apply refine_demonic_pattern_match'; auto. reflexivity.
      - apply (refine_demonic_pattern_match' n (pat_list σ x y)); auto.
      - intros t v ->.
        intros k k__c Hk.
        destruct (term_get_pair_spec t) as [[tl tr] Heq|]; subst.
        + rewrite Heq. intros POST__s POST__c HPOST.
          intros δs0 δc0 -> hs0 hc0 ->. hnf.
          rewrite CHeapSpecM.wp_demonic_pattern_match. cbn.
          apply Hk; cbn; rewrite ?inst_sub_id; auto.
        + apply refine_demonic_pattern_match'; auto. reflexivity.
      - intros t v ->.
        intros k k__c Hk.
        destruct (term_get_sum_spec t) as [[tl|tr] Heq|]; subst.
        + rewrite Heq. intros POST__s POST__c HPOST.
          intros δs0 δc0 -> hs0 hc0 ->. hnf.
          rewrite CHeapSpecM.wp_demonic_pattern_match. cbn.
          apply Hk; cbn; rewrite ?inst_sub_id; auto.
        + rewrite Heq. intros POST__s POST__c HPOST.
          intros δs0 δc0 -> hs0 hc0 ->. hnf.
          rewrite CHeapSpecM.wp_demonic_pattern_match. cbn.
          apply Hk; cbn; rewrite ?inst_sub_id; auto.
        + apply refine_demonic_pattern_match'; auto. reflexivity.
      - intros t v ->.
        intros k k__c Hk.
        intros POST__s POST__c HPOST.
        intros δs0 δc0 -> hs0 hc0 ->. hnf.
        rewrite CHeapSpecM.wp_demonic_pattern_match.
        apply Hk; cbn; rewrite ?inst_sub_id; auto.
      - intros t v ->.
        intros k k__c Hk.
        destruct (term_get_val_spec t); subst.
        + intros POST__s POST__c HPOST.
          intros δs0 δc0 -> hs0 hc0 ->. hnf.
          rewrite CHeapSpecM.wp_demonic_pattern_match. cbn.
          apply Hk; cbn; rewrite ?inst_sub_id; auto.
        + apply refine_demonic_pattern_match'; auto. reflexivity.
      - apply (refine_demonic_pattern_match' n (pat_bvec_split _ _ x y)); auto.
      - intros t v ->.
        intros k k__c Hk.
        destruct (term_get_val_spec t); subst.
        + intros POST__s POST__c HPOST.
          intros δs0 δc0 -> hs0 hc0 ->. hnf.
          rewrite CHeapSpecM.wp_demonic_pattern_match. cbn.
          apply Hk; cbn; rewrite ?inst_sub_id; auto.
        + apply refine_demonic_pattern_match'; auto. reflexivity.
      - apply (refine_demonic_pattern_match' n (pat_tuple p)); auto.
      - intros t v ->.
        intros k k__c Hk.
        destruct (term_get_record_spec t) as [ts Heq|]; subst.
        + rewrite Heq.
          intros POST__s POST__c HPOST.
          intros δs0 δc0 -> hs0 hc0 ->. hnf.
          rewrite CHeapSpecM.wp_demonic_pattern_match. cbn.
          apply Hk; cbn; rewrite ?inst_sub_id; auto.
          hnf. unfold record_pattern_match_val.
          rewrite recordv_unfold_fold.
          symmetry. apply inst_record_pattern_match.
        + apply refine_demonic_pattern_match'; auto. reflexivity.
      - intros t v ->.
        intros k k__c Hk.
        destruct (term_get_union_spec t) as [[K scr'] Heq|]; subst.
        + intros POST__s POST__c HPOST.
          intros δs0 δc0 Hδ0 hs0 hc0 Hh0.
          intros Hwp.
          specialize (H K w ι Hpc scr' (inst scr' ι) eq_refl
                        (fun pc => k (existT K pc))
                        (fun pc => k__c (existT K pc))).
          eapply H in Hwp; eauto.
          revert Hwp.
          rewrite ?CHeapSpecM.wp_demonic_pattern_match. cbn.
          rewrite Heq. rewrite unionv_unfold_fold.
          now destruct pattern_match_val; cbn.
          intros pc. apply (Hk (existT K pc)).
        + apply refine_demonic_pattern_match'; auto. reflexivity.
    Qed.

  End PatternMatching.

  Section State.

    Lemma refine_pushpop `{R : Rel AT A} {Γ1 Γ2 x σ} :
      ℛ⟦RVal σ -> RHeapSpecM (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) R -> RHeapSpecM Γ1 Γ2 R⟧
        SHeapSpecM.pushpop CHeapSpecM.pushpop.
    Proof.
      intros w0 ι0 Hpc0 t v Htv ms mc Hm.
      unfold SHeapSpecM.pushpop, CHeapSpecM.pushpop.
      intros POST__s POST__c HPOST δs0 δc0 Hδ0 hs0 hc0 Hh0.
      apply Hm; eauto.
      - intros w1 r01 ι1 Hι1 Hpc1 a1 a Ha δs1 δc1 -> hs1 hc1 Hh1.
        apply HPOST; auto. now destruct (env.view δs1).
      - now apply refine_env_snoc.
    Qed.

    Lemma refine_pushspops `{R : Rel AT A} {Γ1 Γ2 Δ} :
      ℛ⟦RStore Δ -> RHeapSpecM (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) R -> RHeapSpecM Γ1 Γ2 R⟧
        SHeapSpecM.pushspops CHeapSpecM.pushspops.
    Proof.
      intros w0 ι0 Hpc0 ts vs -> ms mc Hm.
      intros POST__s POST__c HPOST δs0 δc0 -> hs0 hc0 Hh0.
      unfold SHeapSpecM.pushspops, CHeapSpecM.pushspops.
      apply Hm; auto.
      - intros w1 ω01 ι1 Hι1 Hpc1 a1 a Ha δs1 δc1 -> hs1 hc1 Hh1.
        apply HPOST; auto.
        destruct (env.catView δs1).
        unfold inst, inst_store, inst_env at 1.
        rewrite <- env.map_drop.
        rewrite ?env.drop_cat.
        reflexivity.
      - cbn.
        unfold inst, inst_store, inst_env at 3.
        now rewrite env.map_cat.
    Qed.

    Lemma refine_get_local {Γ} :
      ℛ⟦RHeapSpecM Γ Γ (RStore Γ)⟧
        SHeapSpecM.get_local CHeapSpecM.get_local.
    Proof.
      intros w ι Hpc POST__s POST__c HPOST.
      intros δs0 δc0 Hδ hs0 hc0 Hh0.
      unfold SHeapSpecM.get_local, CHeapSpecM.get_local.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      apply refine_T; eauto.
    Qed.

    Lemma refine_put_local {Γ1 Γ2} :
      ℛ⟦RStore Γ2 -> RHeapSpecM Γ1 Γ2 RUnit⟧
        SHeapSpecM.put_local CHeapSpecM.put_local.
    Proof.
      intros w ι Hpc δs2 δc2 Hδ2 POST__s POST__c HPOST.
      intros δs0 δc0 Hδ hs0 hc0 Hh0.
      unfold SHeapSpecM.put_local, CHeapSpecM.put_local.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      apply refine_T; eauto.
      reflexivity.
    Qed.

    Lemma refine_get_heap {Γ} :
      ℛ⟦RHeapSpecM Γ Γ RHeap⟧ SHeapSpecM.get_heap CHeapSpecM.get_heap.
    Proof.
      intros w ι Hpc POST__s POST__c HPOST δs0 δc0 Hδ hs0 hc0 Hh0.
      unfold SHeapSpecM.get_heap, CHeapSpecM.get_heap.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      apply refine_T; eauto.
    Qed.

    Lemma refine_put_heap {Γ} :
      ℛ⟦RHeap -> RHeapSpecM Γ Γ RUnit⟧ SHeapSpecM.put_heap CHeapSpecM.put_heap.
    Proof.
      intros w ι Hpc hs hc Hh POST__s POST__c HPOST δs0 δc0 Hδ hs0 hc0 Hh0.
      unfold SHeapSpecM.put_heap, CHeapSpecM.put_heap.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      apply refine_T; eauto.
      reflexivity.
    Qed.

    Lemma refine_peval {w : World} {ι : Valuation w} {σ} t v :
      ℛ⟦RVal σ⟧@{ι} t v -> ℛ⟦RVal σ⟧@{ι} (peval t) v.
    Proof. intros ->. symmetry. apply peval_sound. Qed.

    Lemma refine_eval_exp {Γ σ} (e : Exp Γ σ) :
      ℛ⟦RHeapSpecM Γ Γ (RVal σ)⟧ (SHeapSpecM.eval_exp e) (CHeapSpecM.eval_exp e).
    Proof.
      intros w ι Hpc POST__s POST__c HPOST δs0 δc0 Hδ0 hs0 hc0 Hh.
      unfold SHeapSpecM.eval_exp, CHeapSpecM.eval_exp.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      apply refine_T; eauto.
      apply refine_peval.
      cbn. rewrite <- eval_exp_inst.
      f_equal. exact Hδ0.
    Qed.

    Lemma refine_eval_exps {Γ Δ} (es : NamedEnv (Exp Γ) Δ) :
      ℛ⟦RHeapSpecM Γ Γ (RStore Δ)⟧
        (SHeapSpecM.eval_exps es) (CHeapSpecM.eval_exps es).
    Proof.
      intros w ι Hpc POST__s POST__c HPOST δs0 δc0 Hδ0 hs0 hc0 Hh.
      unfold SHeapSpecM.eval_exps, CHeapSpecM.eval_exps.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      apply refine_T; eauto.
      apply env.lookup_extensional; cbn; intros [x σ] xIn.
      unfold evals, inst, inst_store, inst_env. rewrite ?env.lookup_map.
      symmetry. etransitivity. apply peval_sound.
      rewrite <- eval_exp_inst. f_equal. symmetry. exact Hδ0.
    Qed.

    Lemma refine_env_update {Γ x σ} (xIn : x∷σ ∈ Γ) (w : World) (ι : Valuation w)
      (t : Term w σ) (v : Val σ) (Htv : ℛ⟦RVal σ⟧@{ι} t v)
      (δs : SStore Γ w) (δc : CStore Γ) (Hδ : ℛ⟦RStore Γ⟧@{ι} δs δc) :
      ℛ⟦RStore Γ⟧@{ι} (δs ⟪ x ↦ t ⟫) (δc ⟪ x ↦ v ⟫).
    Proof.
      cbn in *. subst.
      unfold inst, inst_store, inst_env.
      now rewrite env.map_update.
    Qed.

    Lemma refine_assign {Γ x σ} {xIn : x∷σ ∈ Γ} :
      ℛ⟦RVal σ -> RHeapSpecM Γ Γ RUnit⟧
        (SHeapSpecM.assign x) (CHeapSpecM.assign x).
    Proof.
      intros w ι Hpc t v Htv POST__s POST__c HPOST δs0 δc0 Hδ0 hs0 hc0 Hh.
      unfold SHeapSpecM.assign, CHeapSpecM.assign.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      eapply refine_apply; eauto.
      apply refine_T; eauto.
      reflexivity.
      now apply refine_env_update.
    Qed.

  End State.

  Lemma refine_produce_chunk {Γ} {w0 : World} (ι0 : Valuation w0)
    (Hpc0 : instprop (wco w0) ι0) :
    ℛ⟦_⟧@{ι0} (@SHeapSpecM.produce_chunk Γ w0) (CHeapSpecM.produce_chunk).
  Proof.
    intros cs cc ->.
    intros POST__s POST__c HPOST.
    intros δs δc -> hs hc ->.
    unfold SHeapSpecM.produce_chunk, CHeapSpecM.produce_chunk.
    apply HPOST; cbn; rewrite ?inst_sub_id; auto.
    hnf. cbn. now rewrite peval_chunk_sound.
  Qed.

  Local Hint Unfold RSat : core.
  Local Hint Unfold RInst : core.

  Lemma refine_produce {Γ Σ0 pc0} (asn : Assertion Σ0) :
    let w0 := @MkWorld Σ0 pc0 in
    forall
      (ι0 : Valuation w0)
      (Hpc0 : instprop (wco w0) ι0),
      ℛ⟦□(RHeapSpecM Γ Γ RUnit)⟧@{ι0} (@SHeapSpecM.produce Γ w0 asn) (CHeapSpecM.produce ι0 asn).
  Proof.
    induction asn; intros w0 * Hpc; cbn - [RSat wctx Val].
    - now apply refine_box_assume_formula.
    - intros w1 ω01 ι1 -> Hpc1.
      apply refine_produce_chunk; auto.
      eapply refine_inst_persist; auto.
      reflexivity.
    - intros w1 ω01 ι1 -> Hpc1.
      apply refine_produce_chunk; auto.
      eapply refine_inst_persist; auto.
      reflexivity.
    - intros w1 ω01 ι1 -> Hpc1.
      apply refine_demonic_pattern_match; eauto.
      eapply refine_inst_persist; auto.
      reflexivity.
      intros pc.
      intros w2 ω12 ι2 -> Hpc2.
      intros ts vs ->.
      apply H; cbn - [Sub inst sub_wk1 sub_id sub_cat_left]; wsimpl; auto.
      { rewrite <- ?inst_subst.
        unfold NamedEnv.
        fold (@inst_sub (PatternCaseCtx pc)).
        fold (Sub (PatternCaseCtx pc)).
        rewrite <- inst_sub_cat.
        rewrite <- instprop_subst.
        rewrite <- subst_sub_comp.
        rewrite sub_comp_cat_left.
        now rewrite instprop_subst, inst_subst.
      }
      now rewrite inst_sub_cat, inst_subst.
    - intros w1 ω01 ι1 -> Hpc1.
      apply refine_bind.
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
        rewrite ?inst_sub_snoc, ?sub_acc_trans, ?instprop_subst, ?inst_subst, ?inst_sub_wk1; eauto.
    - intros w1 ω01 ι1 -> Hpc1.
      apply refine_debug; auto.
      apply refine_pure; auto.
      reflexivity.
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
         forall ι : Valuation Σ, instprop eqs ι ->
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
      apply instprop_formula_eqs_ctx in Heqs.
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
         forall ι : Valuation Σ, instprop eqs ι ->
           List.In
             (inst (chunk_ptsreg r t) ι, inst h' ι)
             (heap_extractions (inst h ι)))
      (SHeapSpecM.find_chunk_ptsreg_precise r t h).
  Proof.
    induction h; cbn [SHeapSpecM.find_chunk_ptsreg_precise]; [now constructor|].
    destruct SHeapSpecM.match_chunk_ptsreg_precise eqn:?.
    - constructor. intros ι [Hpc Hf]. clear IHh.
      destruct a; cbn in Heqo; try discriminate Heqo.
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

  Lemma refine_consume_chunk {Γ} :
    ℛ⟦RChunk -> RHeapSpecM Γ Γ RUnit⟧
      SHeapSpecM.consume_chunk CHeapSpecM.consume_chunk.
  Proof.
    intros w0 ι0 Hpc0 cs cc ->.
    unfold SHeapSpecM.consume_chunk, CHeapSpecM.consume_chunk.
    apply refine_bind; auto.
    apply refine_get_heap; auto.
    intros w1 ω01 ι1 -> Hpc1.
    intros hs hc ->.
    remember (peval_chunk (persist cs ω01)) as c1.
    destruct (try_consume_chunk_exact_spec hs c1) as [h' HIn|].
    { intros POST__s POST__c HPOST.
      intros δs δc -> hs' hc' ->.
      cbn. intros Hwp.
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
        split; auto. revert Hwp.
        apply HPOST; wsimpl; auto; reflexivity.
    }
    destruct (SHeapSpecM.try_consume_chunk_precise hs c1) as [[h' eqs]|] eqn:?.
    { intros POST__s POST__c HPOST.
      intros δs δc Hδ hs' hc' Hh'.
      cbv [SHeapSpecM.put_heap SHeapSpecM.bind_right SHeapSpecM.bind  T]. cbn. intros Hwp.
      eapply (refine_assert_pathcondition Hpc1 (ta := eqs)) in Hwp; eauto.
      2: cbn; reflexivity.
      2: cbn; reflexivity.
      destruct Hwp as [Heqs HPOST1].
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

  Lemma refine_consume_chunk_angelic {Γ} :
    ℛ⟦RChunk -> RHeapSpecM Γ Γ RUnit⟧
      SHeapSpecM.consume_chunk_angelic CHeapSpecM.consume_chunk.
  Proof.
    intros w0 ι0 Hpc0 cs cc ->.
    unfold SHeapSpecM.consume_chunk_angelic, CHeapSpecM.consume_chunk.
    apply refine_bind; auto.
    apply refine_get_heap; auto.
    intros w1 ω01 ι1 -> Hpc1.
    intros hs hc ->.
    remember (peval_chunk (persist cs ω01)) as c1.
    destruct (try_consume_chunk_exact_spec hs c1) as [h' HIn|].
    { intros POST__s POST__c HPOST.
      intros δs δc -> hs' hc' ->.
      cbv [SHeapSpecM.put_heap CHeapSpecM.bind CHeapSpecM.put_heap CHeapSpecM.bind_right CHeapSpecM.assert_formula
                         T CHeapSpecM.angelic_list CHeapSpecM.lift_purem].
      intros Hwp.
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
        split; auto. revert Hwp. apply HPOST; wsimpl; auto; reflexivity.
    }
    destruct (SHeapSpecM.try_consume_chunk_precise hs c1) as [[h' eqs]|] eqn:?.
    { intros POST__s POST__c HPOST.
      intros δs δc -> hs' hc' ->.
      cbv [SHeapSpecM.put_heap SHeapSpecM.bind_right T]. cbn. intros Hwp.
      eapply (refine_assert_pathcondition Hpc1) in Hwp; eauto.
      2: cbn; reflexivity.
      2: cbn; reflexivity.
      2: cbn; reflexivity.
      destruct Hwp as [Heqs HPOST1].
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
    { apply refine_bind; auto.
      apply refine_angelic_list; auto.
      { hnf. unfold inst at 1, inst_heap, inst_list.
        rewrite heap_extractions_map.
        { clear. induction (heap_extractions hs) as [|[]];
            cbn; constructor; cbn; auto. }
        eauto using inst_is_duplicable.
      }
      clear Heqo.
      intros w2 ω12 ι2 -> Hpc2.
      intros [cs' hs'] [cc' hc']. intros Hch'.
      inversion Hch'; subst; clear Hch'.
      apply refine_bind; auto.
      - apply refine_assert_eq_chunk; auto. hnf.
        now rewrite peval_chunk_sound, inst_persist, sub_acc_trans, inst_subst.
      - intros w3 ω23 ι3 -> Hpc3 _ _ _.
        apply refine_put_heap; auto.
        eapply refine_inst_persist; eauto.
    }
  Qed.

  Lemma refine_consume {Γ Σ0 pc0} (asn : Assertion Σ0) :
    let w0 := @MkWorld Σ0 pc0 in
    forall
      (ι0 : Valuation w0)
      (Hpc0 : instprop (wco w0) ι0),
      ℛ⟦□(RHeapSpecM Γ Γ RUnit)⟧@{ι0}
        (@SHeapSpecM.consume Γ w0 asn) (CHeapSpecM.consume ι0 asn).
  Proof.
    induction asn; intros w0 * Hpc; cbn - [RSat wctx Val].
    - now apply refine_box_assert_formula.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      now apply refine_consume_chunk.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      now apply refine_consume_chunk_angelic.
    - intros w1 ω01 ι1 -> Hpc1.
      rewrite <- inst_persist.
      apply refine_angelic_pattern_match; eauto.
      cbn. reflexivity.
      intros pc.
      intros w2 ω12 ι2 -> Hpc2.
      intros ts vs ->.
      apply H; cbn - [Sub inst sub_wk1 sub_id sub_cat_left]; wsimpl; auto.
      { rewrite <- ?inst_subst.
        unfold NamedEnv.
        fold (@inst_sub (PatternCaseCtx pc)).
        fold (Sub (PatternCaseCtx pc)).
        rewrite <- inst_sub_cat.
        rewrite <- instprop_subst.
        rewrite <- subst_sub_comp.
        rewrite sub_comp_cat_left.
        now rewrite instprop_subst, inst_subst.
      }
      now rewrite inst_sub_cat, inst_subst.
    - intros w1 ω01 ι1 -> Hpc1.
      apply refine_bind.
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
      apply refine_bind; auto.
      apply refine_angelic; auto.
      intros w2 ω02 ι2 -> Hpc2. intros t v ->.
      apply IHasn; cbn - [inst sub_wk1];
        rewrite ?inst_sub_snoc, ?sub_acc_trans, ?instprop_subst, ?inst_subst, ?inst_sub_wk1; eauto.
    - intros w1 ω01 ι1 -> Hpc1.
      apply refine_debug; auto.
      apply refine_pure; auto.
      reflexivity.
  Qed.

  Lemma refine_call_contract {Γ Δ τ} (c : SepContract Δ τ) :
    ℛ⟦RStore Δ -> RHeapSpecM Γ Γ (RVal τ)⟧
      (SHeapSpecM.call_contract c) (CHeapSpecM.call_contract c).
  Proof.
    intros w0 ι0 Hpc0 args__s args__c Hargs.
    destruct c; cbv [SHeapSpecM.call_contract CHeapSpecM.call_contract].
    apply refine_bind; auto.
    apply refine_angelic_ctx; auto.
    intros w1 ω01 ι1 -> Hpc1 evars__s evars__c Hevars.
    apply refine_bind; auto.
    { apply refine_assert_eq_nenv; auto; hnf.
      now rewrite -> Hevars, inst_subst.
      now rewrite -> Hargs, inst_persist.
    }
    intros w2 ω12 ι2 -> Hpc2 _ _ _.
    apply refine_bind; auto.
    { apply refine_consume; wsimpl; auto.
      constructor.
    }
    intros w3 ω23 ι3 -> Hpc3 _ _ _.
    apply refine_bind; auto.
    { apply refine_demonic; auto. }
    intros w4 ω34 ι4 -> Hpc4.
    intros res__s res__c Hres.
    apply refine_bind; auto.
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
    ℛ⟦RStore Δ -> RHeapSpecM Γ Γ RUnit⟧
      (SHeapSpecM.call_lemma lem) (CHeapSpecM.call_lemma lem).
  Proof.
    destruct lem; cbv [SHeapSpecM.call_lemma CHeapSpecM.call_lemma].
    intros w0 ι0 Hpc0.
    intros args__s args__c Hargs.
    apply refine_bind; auto.
    apply refine_angelic_ctx; auto.
    intros w1 ω01 ι1 -> Hpc1.
    intros evars__s evars__c Hevars.
    apply refine_bind; auto.
    { apply refine_assert_eq_nenv; auto; hnf.
      now rewrite Hevars, inst_subst.
      now rewrite Hargs, inst_persist.
    }
    intros w2 ω12 ι2 -> Hpc2 _ _ _.
    apply refine_bind; auto.
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
    forall Γ τ (s : Stm Γ τ),
      ℛ⟦RHeapSpecM Γ Γ (RVal τ)⟧ (@sexec Γ τ s) (cexec Γ τ s).

  Lemma refine_exec_aux {cfg} srec crec (HYP : ExecRefine srec crec) :
    ExecRefine (@SHeapSpecM.exec_aux cfg srec) (@CHeapSpecM.exec_aux crec).
  Proof.
    unfold ExecRefine.
    induction s; cbn; intros * w0 ι0 Hpc0.
    - apply refine_pure; auto. reflexivity.
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
      apply refine_bind; auto.
      apply refine_assign; auto.
      reflexivity.
      intros w2 ω12 ι2 -> Hpc2 _ _ _.
      apply refine_pure; auto.
      hnf in H. now rewrite <- inst_persist in H.
    - apply refine_bind; auto.
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
        reflexivity.
        rewrite <- inst_persist.
        reflexivity.
    - apply refine_bind; auto.
      apply refine_get_local; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros δs1 δc1 ->.
      apply refine_bind; auto.
      apply refine_put_local; auto.
      apply refine_lift.
      intros w2 ω12 ι2 -> Hpc2 _ _ _.
      apply refine_bind; auto.
      intros w3 ω23 ι3 -> Hpc3.
      intros t v ->.
      apply refine_bind; auto.
      apply refine_put_local; auto.
      rewrite persist_subst.
      hnf. rewrite sub_acc_trans, ?inst_subst; auto.
      intros w4 ω34 ι4 -> Hpc4 _ _ _.
      apply refine_pure; auto.
      eapply refine_inst_persist; eauto.
      reflexivity.
    - apply refine_bind; auto.
      apply refine_eval_exps; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros args__s args__c Hargs.
      apply refine_call_contract; auto.
    - apply refine_bind; auto.
      apply refine_eval_exps; auto.
      intros w1 ω01 ι1 -> Hpc1 δΔ ? ?.
      apply refine_bind; auto.
      apply refine_call_lemma; auto.
      intros w2 ω12 ι2 -> Hpc2 _ _ _; auto.
    - apply refine_bind; auto.
      intros ? ? ? -> ? _ _ _; auto.
    - apply refine_bind; auto.
      apply (refine_eval_exp e1); auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v ->.
      apply refine_bind; auto.
      apply refine_assume_formula; auto.
      cbn. reflexivity.
      intros w2 ω12 ι2 -> Hpc2 _ _ _.
      now apply IHs.
    - apply refine_block; auto.
    - apply refine_bind; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros t v Htv.
      apply refine_demonic_pattern_match; auto.
      intros pc w2 r12 ι2 -> Hpc2.
      intros ts vs Htvs.
      apply refine_pushspops; auto.
      apply H; auto.
    - apply refine_bind; auto.
      apply refine_angelic; auto.
      intros w1 ω01 ι1 -> Hpc1 t v Htv. hnf in Htv; subst.
      apply refine_bind; auto.
      apply refine_consume_chunk; auto.
      cbn. reflexivity.
      intros w2 ω12 ι2 -> Hpc2 _ _ _.
      apply refine_bind; auto.
      apply refine_produce_chunk; auto.
      rewrite <- inst_persist; auto.
      cbn. reflexivity.
      intros w3 ω23 ι3 -> Hpc3 _ _ _.
      apply refine_pure; auto.
      rewrite (persist_trans (A := STerm _)).
      now rewrite <- ?inst_persist.
    - apply refine_bind; auto.
      apply refine_angelic; auto.
      intros w1 ω01 ι1 -> Hpc1.
      intros told v ->.
      apply refine_bind; auto.
      apply refine_consume_chunk; auto.
      cbn. reflexivity.
      intros w2 ω12 ι2 -> Hpc2 _ _ _.
      apply refine_bind; auto.
      apply (refine_eval_exp e); auto.
      intros w3 ω23 ι3 -> Hpc3.
      intros tnew v Htnew. hnf in Htnew. subst v.
      apply refine_bind; auto.
      apply refine_produce_chunk; auto.
      cbn. reflexivity.
      intros w4 ω34 ι4 -> Hpc4 _ _ _.
      apply refine_pure; auto.
      now rewrite <- inst_persist.
    - apply refine_error; auto.
    - apply refine_debug; auto.
  Qed.

  Lemma refine_exec {cfg n} :
    ExecRefine (@SHeapSpecM.exec cfg n) (@CHeapSpecM.exec n).
  Proof.
    induction n; cbn.
    - unfold ExecRefine. intros Γ τ s w ι Hpc.
      apply refine_error; auto.
    - now apply refine_exec_aux.
  Qed.

  Lemma refine_exec_contract {cfg : Config} n {Γ τ} (c : SepContract Γ τ) (s : Stm Γ τ) :
    let w0 := {| wctx := sep_contract_logic_variables c; wco := ctx.nil |} in
    forall (ι0 : Valuation w0),
      ℛ⟦RHeapSpecM Γ Γ RUnit⟧@{ι0}
        (SHeapSpecM.exec_contract cfg n c s) (CHeapSpecM.exec_contract n c s ι0).
  Proof.
    unfold SHeapSpecM.exec_contract, CHeapSpecM.exec_contract;
      destruct c as [Σ δ pre result post]; cbn - [RSat] in *.
    intros ι0.
    apply refine_bind.
    apply refine_produce; wsimpl; cbn; auto.
    intros w1 ω01 ι1 -> Hpc1 _ _ _.
    apply refine_bind; auto.
    apply refine_exec; auto.
    intros w2 ω12 ι2 -> Hpc2.
    intros res__s res__c Hres.
    apply refine_consume; cbn - [inst]; wsimpl; auto.
    f_equal; auto.
  Qed.

  Lemma refine_demonic_close {w : World} (P : 𝕊 w) (p : Valuation w -> Prop) :
    (forall (ι : Valuation w), ℛ⟦_⟧@{ι} P (p ι)) ->
    RSat RProp (w := wnil) env.nil (demonic_close P) (ForallNamed p).
  Proof.
    intros HYP Hwp. unfold ForallNamed.
    rewrite env.Forall_forall. intros ι.
    apply HYP. revert Hwp. clear.
    rewrite ?wsafe_safe, ?safe_debug_safe.
    intros Hwp. now apply safe_demonic_close.
  Qed.

  Lemma refine_vcgen {Γ τ} n (c : SepContract Γ τ) (body : Stm Γ τ) :
    RSat RProp (w := wnil) env.nil (SHeapSpecM.vcgen default_config n c body) (CHeapSpecM.vcgen n c body).
  Proof.
    unfold SHeapSpecM.vcgen, CHeapSpecM.vcgen.
    apply (refine_demonic_close
             (w := {| wctx := sep_contract_logic_variables c; wco := ctx.nil |})).
    intros ι.
    apply refine_exec_contract; auto.
    now intros w1 ω01 ι1 -> Hpc1.
    reflexivity.
    reflexivity.
  Qed.

  Lemma refine_replay_aux_debug :
    forall
      {Σ}
      {w : World}
      (b : AMessage Σ)
      (s : 𝕊 Σ)
      (ω : {| wctx := Σ; wco := [ctx] |} ⊒ w)
      (ι : Valuation w)
      (i : Valuation Σ),
      i = inst (sub_acc ω) ι ->
      ℛ⟦RPureSpecM RUnit⟧@{ι} (Replay.replay_aux s ω) (SHAL.Replay.replay_aux i s) ->
      ℛ⟦RPureSpecM RUnit⟧@{ι} (fun P => debug (subst b (sub_acc ω)) (Replay.replay_aux s ω P)) (SHAL.Replay.replay_aux i s).
  Proof.
    intros Σ w b s ω ι i Hi H.
    intros ta a ? Hdebug.
    cbn in Hdebug.
    rewrite debug_equiv in Hdebug.
    apply H with (ta := ta); auto.
  Qed.

  Lemma refine_replay_aux {Σ} (s : 𝕊 Σ) {w : World} :
    forall
      (ω : MkWorld Σ [ctx] ⊒ w)
      (ι : Valuation w)
      (i : Valuation Σ)
      (Hpc0 : instprop (wco w) ι),
      i = inst (sub_acc ω) ι ->
      ℛ⟦RPureSpecM RUnit⟧@{ι} (Replay.replay_aux s ω) (SHAL.Replay.replay_aux i s).
  Proof.
    revert w; induction s; intros * Hpc Hi; cbn - [RSat wctx Val].
    - apply PureSpecM.refine_angelic_binary; auto.
    - apply PureSpecM.refine_demonic_binary; auto.
    - apply PureSpecM.refine_error; auto.
    - apply PureSpecM.refine_block; auto.
    - apply PureSpecM.refine_bind.
      + apply PureSpecM.refine_assert_formula; auto.
        eapply refine_formula_persist; eauto.
        now cbn.
      + intros w2 ω12 ι2 Hι2 Hpc2 _ _ _. apply IHs; auto.
        subst. now rewrite sub_acc_trans, inst_subst, <- inst_persist.
    - apply PureSpecM.refine_bind.
      + apply PureSpecM.refine_assume_formula; auto.
        eapply refine_formula_persist; eauto.
        now cbn.
      + intros w2 ω12 ι2 Hι2 Hpc2 _ _ _. apply IHs; auto.
        subst. now rewrite sub_acc_trans, inst_subst, <- inst_persist.
    - intros ? ? Hrefine; cbn - [RSat wctx Val].
      cbn.
      intros [v H].
      unfold CPureSpecM.bind, CPureSpecM.angelic.
      exists v.
      unshelve eapply (IHs _ _ _ _ _ _ _ _ _ H).
      + cbn.
        now rewrite instprop_subst, inst_sub_wk1.
      +  cbn [sub_acc].
         subst.
         now rewrite <- inst_sub_up1.
      + unshelve eapply (refine_four _ _ Hrefine).
        cbn. now rewrite inst_sub_wk1.
    - intros ? ? Hrefine; cbn - [RSat wctx Val].
      cbn.
      intros H v.
      unshelve eapply (IHs _ _ _ _ _ _ _ _ _ (H v)).
      +  cbn.
         now rewrite instprop_subst, inst_sub_wk1.
      +  cbn [sub_acc].
         subst.
         now rewrite <- inst_sub_up1.
      + unshelve eapply (refine_four _ _ Hrefine).
        cbn. now rewrite inst_sub_wk1.
    - apply PureSpecM.refine_bind.
      + apply PureSpecM.refine_assert_formula; auto.
        cbn. subst.
        now rewrite <- inst_sub_shift, <- ?inst_subst, <- subst_sub_comp, <- inst_lookup.
      + intros w2 ω12 ι2 Hι2 Hpc2 _ _ _. apply IHs; auto.
        subst. rewrite sub_acc_trans. cbn [sub_acc]. now rewrite ?inst_subst, <- inst_sub_shift.
    - apply PureSpecM.refine_bind.
      + apply PureSpecM.refine_assume_formula; auto.
        cbn. subst.
        now rewrite <- inst_sub_shift, <- ?inst_subst, <- subst_sub_comp, <- inst_lookup.
      + intros w2 ω12 ι2 Hι2 Hpc2 _ _ _. apply IHs; auto.
        subst. rewrite sub_acc_trans. cbn [sub_acc]. now rewrite ?inst_subst, <- inst_sub_shift.
    - now cbn.
    - now cbn.
    - apply refine_replay_aux_debug; auto.
  Qed.

  Lemma refine_replay {Σ} (s : 𝕊 Σ) {w : World} :
    forall
      (ω : MkWorld Σ [ctx] ⊒ w)
      (ι : Valuation w),
      let i := inst (sub_acc ω) ι in
      ℛ⟦ℙ⟧@{i} (Replay.replay s) (SHAL.Replay.replay i s).
  Proof.
    intros.
    apply refine_replay_aux.
    - now cbn.
    - cbn [sub_acc sub_id].
      symmetry.
      apply inst_sub_id.
    - now cbn.
  Qed.

  Lemma shallow_replay_complete {Σ} (s : 𝕊 Σ) {w : World} :
    forall
      (ω : MkWorld Σ [ctx] ⊒ w)
      (ι : Valuation w)
      (i : Valuation Σ)
      (Hpc0 : instprop (wco w) ι),
      i = inst (sub_acc ω) ι ->
      SHAL.Replay.replay i s ->
      safe s i.
  Proof.
    revert w; induction s; intros w ω ι i Hpc0 Hi Hreplay.
    - destruct Hreplay as [H|H].
      + left.
        apply (IHs1 w ω ι i Hpc0 Hi H).
      + right.
        apply (IHs2 w ω ι i Hpc0 Hi H).
    - destruct Hreplay as [Hs1 Hs2].
      split.
      + apply (IHs1 w ω ι i Hpc0 Hi Hs1).
      + apply (IHs2 w ω ι i Hpc0 Hi Hs2).
    - auto.
    - auto.
    - cbn in Hreplay.
      unfold CPureSpecM.bind, CPureSpecM.assert_formula in Hreplay.
      destruct Hreplay as [Hfml Hs].
      split; auto.
      apply (IHs w ω ι i Hpc0 Hi Hs).
    - cbn in Hreplay.
      unfold CPureSpecM.bind, CPureSpecM.assume_formula in Hreplay.
      intros Hfml.
      apply (IHs w ω ι i Hpc0 Hi (Hreplay Hfml)).
    - cbn in Hreplay.
      unfold CPureSpecM.bind, CPureSpecM.angelic in Hreplay.
      destruct Hreplay as [v Hreplay].
      exists v.
      unshelve eapply (IHs (wsnoc w b) _ ι.[b ↦ v] _ _ _ Hreplay).
      + apply acc_sub with (ζ := sub_up1 (sub_acc ω)).
        apply Entailment.entails_nil.
      + cbn.
        now rewrite instprop_subst, inst_sub_wk1.
      + subst.
        now rewrite <- inst_sub_up1.
    - cbn in Hreplay.
      unfold CPureSpecM.bind, CPureSpecM.demonic in Hreplay.
      intros v.
      unshelve eapply (IHs (wsnoc w b) _ ι.[b ↦ v] _ _ _ (Hreplay v)).
      + apply acc_sub with (ζ := sub_up1 (sub_acc ω)).
        apply Entailment.entails_nil.
      + cbn.
        now rewrite instprop_subst, inst_sub_wk1.
      + subst.
        now rewrite <- inst_sub_up1.
    - cbn in Hreplay.
      unfold CPureSpecM.bind, CPureSpecM.assert_formula in Hreplay.
      destruct Hreplay as [Heq Hreplay].
      split; auto.
      unshelve eapply (IHs _ _ (inst (sub_acc ω) ι) _ _ _ Hreplay).
      + apply acc_sub with (ζ := sub_shift xIn).
        apply Entailment.entails_nil.
      + now cbn.
      + rewrite <- inst_sub_shift.
        cbn [sub_acc].
        now subst.
    - cbn in Hreplay.
      unfold CPureSpecM.bind, CPureSpecM.assume_formula in Hreplay.
      intros Heq.
      unshelve eapply (IHs _ _ (inst (sub_acc ω) ι) _ _ _ (Hreplay Heq)).
      + apply acc_sub with (ζ := sub_shift xIn).
        apply Entailment.entails_nil.
      + now cbn.
      + rewrite <- inst_sub_shift.
        cbn [sub_acc].
        now subst.
    - now cbn in Hreplay.
    - now cbn in Hreplay.
    - cbn in Hreplay.
      apply (IHs _ _ ι _ Hpc0 Hi Hreplay).
  Qed.

  Lemma replay_sound_nil (s : 𝕊 [ctx]) :
    forall ι,
      safe (Replay.replay s) ι -> safe s ι.
  Proof.
    intros ι H.
    destruct (env.view ι).
    rewrite <- ?safe_debug_safe in H.
    rewrite <- (@wsafe_safe wnil _ [env]) in H.
    apply (@refine_replay [ctx] s wnil acc_refl [env]) in H.
    assert (Hwco: instprop (wco wnil) [env]) by now cbn.
    apply (@shallow_replay_complete [ctx] s wnil acc_refl [env] [env] Hwco eq_refl H).
  Qed.

  Lemma symbolic_vcgen_soundness {Γ τ} (c : SepContract Γ τ) (body : Stm Γ τ) :
    Symbolic.ValidContract c body ->
    Shallow.ValidContract c body.
  Proof.
    unfold Symbolic.ValidContract. intros [Hwp%postprocess_sound].
    apply replay_sound_nil in Hwp. apply postprocess_sound in Hwp.
    apply refine_vcgen. now rewrite wsafe_safe, safe_debug_safe.
  Qed.

  Lemma symbolic_vcgen_fuel_soundness {Γ τ} (fuel : nat) (c : SepContract Γ τ) (body : Stm Γ τ) :
    Symbolic.ValidContractWithFuel fuel c body ->
    Shallow.ValidContractWithFuel fuel c body.
  Proof.
    unfold Symbolic.ValidContractWithFuel. intros [Hwp%postprocess_sound].
    apply replay_sound_nil in Hwp. apply postprocess_sound in Hwp.
    apply refine_vcgen. now rewrite wsafe_safe, safe_debug_safe.
  Qed.

  (* Print Assumptions symbolic_vcgen_soundness. *)

End Soundness.

Module MakeSymbolicSoundness
  (Import B    : Base)
  (Import PROG : Program B)
  (Import SIG  : Signature B)
  (Import SPEC : Specification B PROG SIG)
  (Import SOLV : SolverKit B SIG)
  (Import SHAL : ShallowExecOn B PROG SIG SPEC)
  (Import SYMB : SymbolicExecOn B PROG SIG SPEC SOLV).

  Include Soundness B PROG SIG SPEC SOLV SHAL SYMB.
End MakeSymbolicSoundness.
