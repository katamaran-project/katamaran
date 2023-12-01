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
     Classes.Morphisms.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Prelude
     Base
     Shallow.MonadInterface
     Symbolic.MonadInterface
     Symbolic.Worlds
     Syntax.Chunks
     Syntax.Assertions
     Syntax.Formulas
     Syntax.Predicates.

Import ctx.notations.
Import env.notations.

Set Implicit Arguments.

Module Type RefinementMonadInterfaceOn
  (Import B : Base)
  (Import PK   : PredicateKit B)
  (Import FML  : FormulasOn B PK)
  (Import CHK  : ChunksOn B PK)
  (Import ASN  : AssertionsOn B PK FML CHK)
  (Import SHAL : ShallowMonadInterfaceOn B PK FML CHK ASN)
  (Import WRLD : WorldsOn B PK FML CHK)
  (Import SYMB : SymbolicMonadInterfaceOn B PK FML CHK ASN WRLD).

  Import ModalNotations.
  Import logicalrelation.
  Import logicalrelation.notations.

  Section RPureSpecM.
    Import SPureSpecM (SPureSpecM) CPureSpecM (CPureSpecM).

    Context {MT : TYPE -> TYPE} {M : Type -> Type}
      {pureMT : SPureSpecM MT} {pureM : CPureSpecM M}
      (RM : forall {AT A} (R : Rel AT A), Rel (MT AT) (M A)).

    Class RPureSpecM : Type := {
        rel_pure `{R : Rel AT A} :
        ℛ⟦R -> RM R⟧ SPureSpecM.pure CPureSpecM.pure;
        rel_bind `{RA : Rel AT A, RB : Rel BT B} :
        ℛ⟦RM RA -> □(RA -> RM RB) -> RM RB⟧ SPureSpecM.bind CPureSpecM.bind;
        rel_error `{RA : Rel AT A} :
        ℛ⟦RMsg □(SHeap -> AMessage) (RM RA)⟧ SPureSpecM.error CPureSpecM.error;
        rel_block `{R : Rel AT A} :
        ℛ⟦RM R⟧ (@SPureSpecM.block MT _ AT) CPureSpecM.block;
        rel_angelic (x : option LVar) :
        ℛ⟦∀ σ, RM (RVal σ)⟧ (SPureSpecM.angelic x) CPureSpecM.angelic;
        rel_demonic (x : option LVar) :
        ℛ⟦∀ σ, RM (RVal σ)⟧ (SPureSpecM.demonic x) CPureSpecM.demonic;
        rel_angelic_ctx {N : Set} {n : N -> LVar} :
        ℛ⟦∀ Δ, RM (RNEnv Δ)⟧ (SPureSpecM.angelic_ctx n) CPureSpecM.angelic_ctx;
        rel_demonic_ctx {N : Set} {n : N -> LVar} :
        ℛ⟦∀ Δ : NCtx N Ty, RM (RNEnv Δ)⟧ (SPureSpecM.demonic_ctx n) CPureSpecM.demonic_ctx;
        rel_assert_pathcondition :
        ℛ⟦RMsg □(SHeap -> AMessage) (RPathCondition -> RM RUnit)⟧ SPureSpecM.assert_pathcondition CPureSpecM.assert_formula;
        rel_assert_formula :
        ℛ⟦RMsg □(SHeap -> AMessage) (RFormula -> RM RUnit)⟧ SPureSpecM.assert_formula CPureSpecM.assert_formula;
        rel_assume_pathcondition :
        ℛ⟦RPathCondition -> RM RUnit⟧ SPureSpecM.assume_pathcondition CPureSpecM.assume_formula;
        rel_assume_formula :
        ℛ⟦RFormula -> RM RUnit⟧ SPureSpecM.assume_formula CPureSpecM.assume_formula;
        rel_angelic_binary `{R : Rel AT A} :
        ℛ⟦RM R -> RM R -> RM R⟧ SPureSpecM.angelic_binary CPureSpecM.angelic_binary;
        rel_demonic_binary `{R : Rel AT A} :
        ℛ⟦RM R -> RM R -> RM R⟧ SPureSpecM.demonic_binary CPureSpecM.demonic_binary;
        rel_angelic_pattern_match {N : Set} (n : N -> LVar) {σ} (pat : @Pattern N σ) :
        ℛ⟦RMsg _ (RVal σ -> RM (RMatchResult pat))⟧ (SPureSpecM.angelic_pattern_match n pat) (CPureSpecM.angelic_pattern_match pat);
        rel_demonic_pattern_match {N : Set} (n : N -> LVar) {σ} (pat : @Pattern N σ) :
        ℛ⟦RVal σ -> RM (RMatchResult pat)⟧ (SPureSpecM.demonic_pattern_match n pat) (CPureSpecM.demonic_pattern_match pat);
        rel_new_pattern_match {N : Set} (n : N -> LVar) {σ} (pat : @Pattern N σ) :
        ℛ⟦RVal σ -> RM (RMatchResult pat)⟧ (SPureSpecM.new_pattern_match n pat) (CPureSpecM.new_pattern_match pat);
        rel_debug `{R : Rel AT A} :
        ℛ⟦RMsg _ (RM R -> RM R)⟧ SPureSpecM.debug CPureSpecM.debug;
      }.

    Context {rspecM : RPureSpecM}.

    Lemma refine_assert_eq_nenv {N : Set} :
      ℛ⟦∀ Δ : NCtx N Ty, RMsg _ (RNEnv Δ -> RNEnv Δ -> RM RUnit)⟧
        SPureSpecM.assert_eq_nenv CPureSpecM.assert_eq_nenv.
    Proof.
      intros w0 ι0 Hpc0 Δ msg E1 ? -> E2 ? ->.
      induction E1; env.destroy E2; cbn - [RSat].
      - now apply rel_pure.
      - eapply rel_bind. auto. apply IHE1.
        intros w1 ω01 ι1 Hι1 Hpc1 _ _ _.
        apply rel_assert_formula; auto.
        eapply refine_formula_persist; eauto.
        cbn. reflexivity.
    Qed.

    Lemma refine_assert_eq_env :
      ℛ⟦∀ Δ, RMsg _ (REnv Δ -> REnv Δ -> RM RUnit)⟧
        SPureSpecM.assert_eq_env CPureSpecM.assert_eq_env.
    Proof.
      intros w0 ι0 Hpc0 Δ msg E1 ? -> E2 ? ->.
      induction E1; env.destroy E2; cbn - [RSat].
      - now apply rel_pure.
      - eapply rel_bind; eauto.
        intros w1 ω01 ι1 Hι1 Hpc1 _ _ _.
        apply rel_assert_formula; auto.
        eapply refine_formula_persist; eauto.
        cbn. reflexivity.
    Qed.

    Lemma refine_assert_eq_chunk :
      ℛ⟦RMsg _ (RChunk -> RChunk -> □(RM RUnit))⟧
        SPureSpecM.assert_eq_chunk CPureSpecM.assert_eq_chunk.
    Proof.
      intros w0 ι0 Hpc0 msg c ? -> c' ? ->. revert c'.
      induction c; intros [] w1 ω01 ι1 Hι1 Hpc1; cbn;
        auto; try (now apply rel_error).
      - destruct eq_dec.
        + destruct e; cbn.
          apply refine_assert_eq_env; auto.
          eapply refine_inst_persist; eauto; easy.
          eapply refine_inst_persist; eauto; easy.
        + now apply rel_error.
      - destruct eq_dec_het.
        + dependent elimination e; cbn.
          apply rel_assert_formula; auto. subst.
          now do 2 rewrite <- inst_persist.
        + now apply rel_error.
      - eapply rel_bind. auto. apply IHc1; auto.
        intros w2 ω12 ι2 Hι2 Hpc2 _ _ _. apply IHc2; auto.
        subst. now rewrite sub_acc_trans, inst_subst, <- inst_persist.
      - eapply rel_bind. auto. apply IHc1; auto.
        intros w2 ω12 ι2 Hι2 Hpc2 _ _ _. apply IHc2; auto.
        subst. now rewrite sub_acc_trans, inst_subst, <- inst_persist.
    Qed.

  End RPureSpecM.
  #[global] Arguments RPureSpecM {MT M _ _} RM.

  Section RHeapSpecM.
    Import SPureSpecM (SPureSpecM) CPureSpecM (CPureSpecM).
    Import SHeapSpecM (SHeapSpecM) CHeapSpecM (CHeapSpecM).

    Context {MT : TYPE -> TYPE} {M : Type -> Type}
      {pureMT : SPureSpecM MT} {heapMT : SHeapSpecM MT}
      {pureM : CPureSpecM M} {heapM : CHeapSpecM M}
      (RM : forall {AT A} (R : Rel AT A), Rel (MT AT) (M A)).

    Class RHeapSpecM : Type := {
      rel_produce_chunk :
        ℛ⟦RChunk -> RM RUnit⟧ SHeapSpecM.produce_chunk CHeapSpecM.produce_chunk;
      rel_consume_chunk :
        ℛ⟦RChunk -> RM RUnit⟧ SHeapSpecM.consume_chunk CHeapSpecM.consume_chunk;
      rel_consume_chunk_angelic :
        ℛ⟦RChunk -> RM RUnit⟧ SHeapSpecM.consume_chunk_angelic CHeapSpecM.consume_chunk;
    }.

  End RHeapSpecM.
  #[global] Arguments RHeapSpecM {MT M _ _} RM.

  (* Module RReaderT. *)
  (*   Section RReaderT. *)

  (*     Context {RT R} {persR : Persistent RT} {RR : Rel RT R}. *)
  (*     Context `{spureM : SPureSpecM MT, sheapm : SHeapSpecM MT, *)
  (*               cpureM : CPureSpecM M, cheapM : CHeapSpecM M} *)
  (*              (RM : forall {AT A} (R : Rel AT A), Rel (MT AT) (M A)). *)

  (*     #[export] Instance RReaderT `{RA : Rel AT A} : *)
  (*       Rel (ReaderT RT MT AT) (CReaderT R M A) := *)
  (*       RR -> RM RA. *)

  (*     #[export] Instance rpurespecm : RPureSpecM (@RReaderT). *)
  (*     Proof. *)
  (*     Admitted. *)

  (*     #[export] Instance rheapspecm : RHeapSpecM (@RReaderT). *)
  (*     Proof. *)
  (*     Admitted. *)

  (*   End RReaderT. *)
  (*   #[global] Arguments RReaderT {RT R} RR {MT M} RM {AT A} RA. *)
  (* End RReaderT. *)
  (* Export (hints) RReaderT. *)
  (* Export RReaderT (RReaderT). *)

  Section ProduceConsume.

    Context {MT M} {spureMT : SPureSpecM MT} {cpureM : CPureSpecM M}.
    Context {sheapM : SHeapSpecM MT} {cheapM : CHeapSpecM M}.
    Context {RM : forall {AT A} (R : Rel AT A), Rel (MT AT) (M A)}.
    Context {rpureM : RPureSpecM RM} {rheapM : RHeapSpecM RM}.

    Lemma refine_produce {Σ} (asn : Assertion Σ) :
      ℛ⟦RInst (Sub Σ) (Valuation Σ) -> RM RUnit⟧
        (sproduce asn) (cproduce asn).
    Proof.
      induction asn; cbn [sproduce cproduce]; intros w0 ι0 Hpc0 sδ cδ Hδ.
      - apply rel_assume_formula; auto.
        now apply refine_formula_subst.
      - apply rel_produce_chunk; eauto.
        hnf. now rewrite inst_subst, Hδ.
      - apply rel_produce_chunk; eauto.
        hnf. now rewrite inst_subst, Hδ.
      - eapply rel_bind; auto.
        apply rel_demonic_pattern_match; auto.
        hnf. now rewrite inst_subst, Hδ.
        intros w1 θ1 ι1 -> Hpc1 [] [] []. subst. cbn in H0. subst.
        eapply H; eauto. hnf. hnf in Hδ. subst.
        symmetry. etransitivity.
        refine (inst_env_cat (persist sδ θ1) n ι1).
        f_equal. apply inst_persist.
      - eapply rel_bind; auto.
        apply IHasn1; auto. intros w1 θ1 ι1 ? Hpc1 _ _ _.
        apply IHasn2; auto. eapply refine_inst_persist; eauto.
      - eapply rel_demonic_binary; eauto.
        apply IHasn1; auto. apply IHasn2; auto.
      - eapply rel_bind; auto. apply rel_demonic; auto.
        intros w1 θ1 ι1 -> Hpc1 t v ->. apply IHasn; auto.
        cbn - [inst]. cbn in Hδ. subst.
        now rewrite <- inst_persist.
      - apply rel_debug; auto. apply rel_pure; auto.
        constructor.
    Qed.

    Lemma refine_consume {Σ} (asn : Assertion Σ) :
      ℛ⟦RInst (Sub Σ) (Valuation Σ) -> RM RUnit⟧
        (sconsume asn) (cconsume asn).
    Proof.
      induction asn; cbn [sconsume cconsume]; intros w0 ι0 Hpc0 sδ cδ Hδ.
      - apply rel_assert_formula; auto.
        now apply refine_formula_subst.
      - apply rel_consume_chunk; eauto.
        hnf. now rewrite inst_subst, Hδ.
      - apply rel_consume_chunk_angelic; eauto.
        hnf. now rewrite inst_subst, Hδ.
      - eapply rel_bind; auto.
        apply rel_angelic_pattern_match; auto.
        hnf. now rewrite inst_subst, Hδ.
        intros w1 θ1 ι1 -> Hpc1 [] [] []. subst. cbn in H0. subst.
        eapply H; eauto. hnf. hnf in Hδ. subst.
        symmetry. etransitivity.
        refine (inst_env_cat (persist sδ θ1) n ι1).
        f_equal. apply inst_persist.
      - eapply rel_bind; auto.
        apply IHasn1; auto. intros w1 θ1 ι1 ? Hpc1 _ _ _.
        apply IHasn2; auto. eapply refine_inst_persist; eauto.
      - eapply rel_angelic_binary; eauto.
        apply IHasn1; auto. apply IHasn2; auto.
      - eapply rel_bind; auto. apply rel_angelic; auto.
        intros w1 θ1 ι1 -> Hpc1 t v ->. apply IHasn; auto.
        cbn - [inst]. cbn in Hδ. subst.
        now rewrite <- inst_persist.
      - apply rel_debug; auto. apply rel_pure; auto.
        constructor.
    Qed.

    Lemma refine_call_contract {Δ τ} (c : SepContract Δ τ) :
      ℛ⟦RInst (SStore Δ) (CStore Δ) -> RM (RVal τ)⟧
        (scall_contract c) (ccall_contract c).
    Proof.
      intros w0 ι0 Hpc0 sδ cδ rδ.
      destruct c as [lvars pats req res ens]; cbn.
      eapply rel_bind; auto.
      { apply rel_angelic_ctx; auto. }
      intros w1 θ1 ι1 Heq1 Hpc1 slenv clenv rlenv.
      eapply rel_bind; auto.
      { apply refine_assert_eq_nenv; auto.
        rewrite rlenv. hnf. now rewrite inst_subst.
        eapply refine_inst_persist; eauto. }
      intros w2 θ2 ι2 Heq2 Hpc2 _ _ _.
      eapply rel_bind; auto.
      { apply refine_consume; auto. rewrite rlenv.
        hnf. subst. now rewrite <- inst_persist. }
      intros w3 θ3 ι3 Heq3 Hpc3 _ _ _.
      eapply rel_bind; auto.
      { apply rel_demonic; auto. }
      intros w4 θ4 ι4 Heq4 Hpc4 t v Htv.
      eapply rel_bind; auto.
      { apply refine_produce; auto.
        cbn - [inst_env sub_snoc].
        rewrite inst_sub_snoc, inst_persist.
        rewrite sub_acc_trans.
        rewrite inst_subst.
        cbn in rlenv, Htv. subst.
        now rewrite inst_persist.
      }
      intros w5 θ5 ι5 Heq5 Hpc5 _ _ _.
      apply rel_pure; auto.
      eapply refine_inst_persist; eauto.
    Qed.

    Lemma refine_call_lemma {Δ} (lem : Lemma Δ) :
      ℛ⟦RInst (SStore Δ) (CStore Δ) -> RM RUnit⟧
        (scall_lemma lem) (ccall_lemma lem).
    Proof.
      intros w0 ι0 Hpc0 sδ cδ rδ.
      destruct lem as [lvars pats req ens]; cbn.
      eapply rel_bind; auto.
      { apply rel_angelic_ctx; auto. }
      intros w1 θ1 ι1 Heq1 Hpc1 slenv clenv rlenv.
      eapply rel_bind; auto.
      { apply refine_assert_eq_nenv; auto.
        rewrite rlenv. hnf. now rewrite inst_subst.
        eapply refine_inst_persist; eauto. }
      intros w2 θ2 ι2 Heq2 Hpc2 _ _ _.
      eapply rel_bind; auto.
      { apply refine_consume; auto. rewrite rlenv.
        hnf. subst. now rewrite <- inst_persist. }
      intros w3 θ3 ι3 Heq3 Hpc3 _ _ _.
      apply refine_produce; auto.
      cbn - [inst_env sub_snoc].
      rewrite !inst_persist.
      cbn in rlenv. now subst.
    Qed.

  End ProduceConsume.

End RefinementMonadInterfaceOn.
