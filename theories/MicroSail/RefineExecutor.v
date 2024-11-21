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
  Program.Basics
  Program.Tactics
  ZArith.ZArith
  Strings.String
  Classes.Morphisms
  Classes.RelationClasses
  Classes.Morphisms_Prop
  Classes.Morphisms_Relations.

From Coq Require Lists.List.

From Equations Require Import
  Equations.

From Katamaran Require Import
  Signature
  MicroSail.ShallowExecutor
  MicroSail.SymbolicExecutor
  Program
  Tactics.

Set Implicit Arguments.

Import ctx.notations.
Import env.notations.

Module Type RefineExecutorOn
  (Import B    : Base)
  (Import SIG  : Signature B)
  (Import PROG : Program B)
  (Import SHAL : ShallowExecOn B SIG PROG)
  (Import SYMB : SymbolicExecOn B SIG PROG).

  Import ModalNotations.
  Import SymProp.
  Import logicalrelation.
  Import logicalrelation.notations.

  Section Exec.

    Context {MT M} {spureMT : SPureSpecM MT} {cpureM : CPureSpecM M}.
    Context {sheapM : SHeapSpecM MT} {cheapM : CHeapSpecM M}.
    Context {RM : forall {AT A} (R : Rel AT A), Rel (MT AT) (M A)}.
    Context {rpureM : RPureSpecM RM} {rheapM : RHeapSpecM RM}.

    #[export] Instance RStoreT Γ1 Γ2 {AT A} (RA : Rel AT A) :
      Rel (SStoreT MT Γ1 Γ2 AT) (CStoreT M Γ1 Γ2 A) :=
      RInst _ _ -> RM (RProd RA (RInst _ _)).

    Lemma rliftM {Γ} `{RA : Rel AT A} :
      ℛ⟦RM RA -> RStoreT Γ Γ RA⟧ SYMB.liftM SHAL.liftM.
    Proof.
      unfold SYMB.liftM, SHAL.liftM.
      intros w0 ι0 Hpc0 sm cm rm sδ cδ rδ.
      eapply rel_bind; auto.
      intros w1 θ1 ι1 Heq1 Hpc1 sa ca ra.
      apply rel_pure; auto.
      constructor; auto.
      eapply refine_inst_persist; eauto.
    Qed.

    Lemma rpure {Γ} `{RA : Rel AT A} :
      ℛ⟦RA -> RStoreT Γ Γ RA⟧ SYMB.pure SHAL.pure.
    Proof.
      unfold SYMB.pure, SHAL.pure.
      intros w0 ι0 Hpc0 sa ca ra.
      apply rliftM; auto.
      apply rel_pure; auto.
    Qed.

    Lemma rbind `{RA : Rel AT A, RB : Rel BT B} {Γ1 Γ2 Γ3} :
      ℛ⟦RStoreT Γ1 Γ2 RA -> □(RA -> RStoreT Γ2 Γ3 RB) -> RStoreT Γ1 Γ3 RB⟧
        SYMB.bind SHAL.bind.
    Proof.
      unfold SYMB.bind, SHAL.bind.
      intros w0 ι0 Hpc0 sm cm rm sf cf rf sδ cδ rδ.
      eapply rel_bind; auto.
      intros w1 θ1 ι1 Heq1 Hpc1 [sa sδ2] [ca cδ2] [ra rδ2].
      apply rf; auto.
    Qed.

    Lemma rstate {Γ1 Γ2} `{RA : Rel AT A} :
      ℛ⟦(RInst _ _ -> RProd RA (RInst _ _)) -> RStoreT Γ1 Γ2 RA⟧
        SYMB.state SHAL.state.
    Proof.
      unfold SYMB.state, SHAL.state.
      intros w0 ι0 Hpc0 sf cf rf sδ cδ rδ.
      apply rel_pure; auto.
    Qed.

    Lemma reval_exp {Γ τ} (e : Exp Γ τ) :
      ℛ⟦RStoreT Γ Γ (RVal τ)⟧ (@SYMB.eval_exp _ _ _ _ e) (SHAL.eval_exp e).
    Proof.
      unfold SYMB.eval_exp, SHAL.eval_exp.
      intros w0 ι0 Hpc0. apply rstate; auto.
      intros sδ cδ rδ. constructor; auto. cbn.
      rewrite peval_sound, <- eval_exp_inst. now f_equal.
    Qed.

    Lemma reval_exps {Γ Δ} (es : NamedEnv (Exp Γ) Δ) :
      ℛ⟦RStoreT Γ Γ (RNEnv Δ)⟧ (@SYMB.eval_exps _ _ _ _ es) (SHAL.eval_exps es).
    Proof.
      unfold SYMB.eval_exps, SHAL.eval_exps.
      intros w0 ι0 Hpc0. apply rstate; auto.
      intros sδ cδ rδ. constructor; auto. cbn.
      apply env.lookup_extensional; cbn; intros [x σ] xIn.
      unfold evals, inst, inst_store, inst_env. rewrite !env.lookup_map.
      rewrite peval_sound, <- eval_exp_inst. now f_equal.
    Qed.

    Lemma rpushpop `{RA : Rel AT A} {Γ1 Γ2} (x : PVar) (σ : Ty) :
      ℛ⟦RVal σ -> RStoreT (Γ1 ▻ x∷σ) (Γ2 ▻ x∷σ) RA -> RStoreT Γ1 Γ2 RA⟧
        SYMB.pushpop SHAL.pushpop.
    Proof.
      unfold SYMB.pushpop, SHAL.pushpop.
      intros w0 ι0 Hpc0 sv cv rv sm cm rm sδ cδ rδ.
      eapply rel_bind; auto.
      { apply rm. cbn. f_equal; auto. }
      intros w1 θ1 ι1 Heq1 Hpc1 [sa sδ2] [ca cδ2] [ra rδ2].
      apply rel_pure; auto.
      constructor; auto.
      destruct (env.view sδ2), (env.view cδ2); cbn.
      cbn in rδ2. apply env.inversion_eq_snoc in rδ2.
      now destruct rδ2.
    Qed.

    Lemma rpushspops `{RA : Rel AT A} {Γ1 Γ2 Δ} :
      ℛ⟦RInst (SStore Δ) (CStore Δ) ->
        RStoreT (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) RA ->
        RStoreT Γ1 Γ2 RA⟧
        SYMB.pushspops SHAL.pushspops.
    Proof.
      unfold SYMB.pushspops, SHAL.pushspops.
      intros w0 ι0 Hpc0 sv cv rv sm cm rm sδ cδ rδ.
      eapply rel_bind; auto.
      { apply rm. cbn.
        unfold inst, inst_store, inst_env.
        rewrite env.map_cat. now f_equal.
      }
      intros w1 θ1 ι1 Heq1 Hpc1 [sa sδ2] [ca cδ2] [ra rδ2].
      apply rel_pure; auto.
      constructor; auto.
      destruct (env.catView sδ2), (env.catView cδ2); cbn.
      rewrite !env.drop_cat.
      cbn in rδ2. unfold inst, inst_store, inst_env in rδ2.
      rewrite env.map_cat in rδ2. apply env.inversion_eq_cat in rδ2. now destruct rδ2.
    Qed.

    Lemma rassign {Γ x σ} (xIn : x∷σ ∈ Γ) :
      ℛ⟦RVal σ -> RStoreT Γ Γ RUnit⟧
        (@SYMB.assign _ _ _ x _ _) (SHAL.assign x).
    Proof.
      unfold SYMB.assign, SHAL.assign.
      intros w0 ι0 Hpc0 sv cv rv. apply rstate; auto.
      intros sδ cδ rδ. constructor. constructor. cbn in *.
      unfold inst, inst_store, inst_env.
      rewrite env.map_update. now subst.
    Qed.

    Lemma rputlocal {Γ Δ} :
      ℛ⟦RInst _ _ -> RStoreT Γ Δ (RNEnv Γ)⟧
        SYMB.put_local SHAL.put_local.
    Proof.
      unfold SYMB.put_local, SHAL.put_local.
      intros w0 ι0 Hpc0 sδΔ cδΔ rδΔ. apply rstate; auto.
      intros sδΓ cδΓ rδΓ. constructor; auto.
    Qed.

    Section WithExecs.

      Context (sexec_call_foreign : SYMB.ExecCallForeign MT).
      Context (sexec_lemma : SYMB.ExecLemma MT).
      Context (sexec_call : SYMB.ExecCall MT).

      Context (cexec_call_foreign : SHAL.ExecCallForeign M).
      Context (cexec_lemma : SHAL.ExecLemma M).
      Context (cexec_call : SHAL.ExecCall M).

      Context (rexec_call_foreign : forall [Δ τ] (f : 𝑭𝑿 Δ τ),
                 ℛ⟦RNEnv Δ -> RM (RVal τ)⟧
                   (sexec_call_foreign f)
                   (cexec_call_foreign f)).
      Context (rexec_call_lemma : forall [Δ] (lem : 𝑳 Δ),
                 ℛ⟦RNEnv Δ -> RM (RUnit)⟧
                   (sexec_lemma lem)
                   (cexec_lemma lem)).
      Context (rexec_call : forall [Δ τ] (f : 𝑭 Δ τ),
                 ℛ⟦RNEnv Δ -> RM (RVal τ)⟧ (sexec_call f) (cexec_call f)).

      Lemma rexec_aux [Γ τ] (s : Stm Γ τ) :
        ℛ⟦RStoreT Γ Γ (RVal τ)⟧
          (SYMB.exec_aux sexec_call_foreign sexec_lemma sexec_call s)
          (SHAL.exec_aux cexec_call_foreign cexec_lemma cexec_call s).
      Proof.
        induction s; cbn [SYMB.exec_aux SHAL.exec_aux]; intros w0 ι0 Hpc0.
        - apply rpure; auto. easy.
        - apply reval_exp; auto.
        - apply rbind; auto.
          intros w1 θ1 ι1 Heq1 Hpc1 sv cv rv.
          apply rpushpop; auto.
        - apply rpushspops; auto.
          apply refine_lift.
        - apply rbind; auto.
          intros w1 θ1 ι1 Heq1 Hpc1 sv cv rv.
          apply rbind; auto.
          apply rassign; auto.
          intros w2 θ2 ι2 Heq2 Hpc2 _ _ _.
          apply rpure; auto.
          eapply refine_inst_persist; subst; auto.
        - apply rbind; auto.
          apply reval_exps; auto.
          intros w1 θ1 ι1 Heq1 Hpc1 sδΔ cδΔ rδΔ.
          apply rliftM; auto.
          apply rexec_call; auto.
        - apply rbind; auto.
          apply rputlocal; auto.
          apply refine_lift.
          intros w1 θ1 ι1 Heq1 Hpc1 sδΓ cδΓ rδΓ.
          apply rbind; auto.
          intros w2 θ2 ι2 Heq2 Hpc2 sv cv rv.
          apply rbind; auto.
          apply rputlocal; auto.
          eapply refine_inst_persist; subst; auto.
          intros w3 θ3 ι3 Heq3 Hpc3 _ _ _.
          apply rpure; auto.
          eapply refine_inst_persist; subst; auto.
        - apply rbind; auto.
          apply reval_exps; auto.
          intros w1 θ1 ι1 Heq1 Hpc1 sδΔ cδΔ rδΔ.
          apply rliftM; auto.
          apply rexec_call_foreign; auto.
        - apply rbind; auto.
          apply reval_exps; auto.
          intros w1 θ1 ι1 Heq1 Hpc1 sδΔ cδΔ rδΔ.
          apply rbind; auto.
          apply rliftM; auto.
          apply rexec_call_lemma; auto.
          intros w2 θ2 ι2 Heq2 Hpc2 _ _ _; auto.
        - apply rbind; auto.
          intros w1 θ1 ι1 Heq1 Hpc1 sv cv rv; auto.
        - apply rbind; auto.
          apply reval_exp; auto.
          intros w1 θ1 ι1 Heq1 Hpc1 sv cv rv; auto.
          apply rbind; auto.
          apply rliftM; auto.
          apply rel_assume_formula; auto.
          cbn. now rewrite rv.
          intros w2 θ2 ι2 Heq2 Hpc2 _ _ _; auto.
        - apply rliftM; auto.
          apply rel_block; auto.
        - apply rbind; auto.
          intros w1 θ1 ι1 Heq1 Hpc1 sv cv rv; auto.
          apply rbind; auto.
          apply rliftM; auto.
          apply rel_demonic_pattern_match; auto.
          intros w2 θ2 ι2 Heq2 Hpc2 [pc sδpc] [pc' cδpc] [<- rδpc]; cbn in rδpc.
          apply rpushspops; auto.
          apply H; auto.
        - apply rbind; auto.
          apply rliftM; auto.
          apply rel_angelic; auto.
          intros w1 θ1 ι1 Heq1 Hpc1 sv cv rv; auto.
          apply rbind; auto.
          apply rliftM; auto.
          apply rel_consume_chunk; auto. cbn. now f_equal.
          intros w2 θ2 ι2 Heq2 Hpc2 _ _ _.
          apply rbind; auto.
          apply rliftM; auto.
          apply rel_produce_chunk; auto.
          cbn. f_equal. rewrite rv. subst.
          now rewrite <- inst_persist.
          intros w3 θ3 ι3 Heq3 Hpc3 _ _ _.
          apply rpure; auto. subst.
          rewrite rv.
          eapply refine_inst_persist; eauto.
          now rewrite sub_acc_trans, inst_subst.
        - apply rbind; auto.
          apply rliftM; auto.
          apply rel_angelic; auto.
          intros w1 θ1 ι1 Heq1 Hpc1 svold cvold rvold; auto.
          apply rbind; auto.
          apply rliftM; auto.
          apply rel_consume_chunk; auto. cbn. now f_equal.
          intros w2 θ2 ι2 Heq2 Hpc2 _ _ _.
          apply rbind; auto.
          apply reval_exp; auto.
          intros w3 θ3 ι3 Heq3 Hpc3 svnew cvnew rvnew.
          apply rbind; auto.
          apply rliftM; auto.
          apply rel_produce_chunk; auto. cbn. now f_equal.
          intros w4 θ4 ι4 Heq4 Hpc4 _ _ _.
          apply rpure; auto. subst.
          now eapply refine_inst_persist; eauto.
        - intros sδ cδ rδ. apply rel_error; auto.
        - intros sδ cδ rδ. apply rel_debug; auto.
          apply IHs; auto.
      Qed.

    End WithExecs.

    Section WithExec.

      Context (sexec : SYMB.Exec MT).
      Context (cexec : SHAL.Exec M).
      Context (rexec : forall [Γ τ] (s : Stm Γ τ),
                 ℛ⟦RStoreT Γ Γ (RVal τ)⟧ (sexec s) (cexec s)).

      Lemma rexec_contract [Δ τ] (c : SepContract Δ τ) (s : Stm Δ τ) :
        ℛ⟦RM RUnit⟧
          (SYMB.exec_contract sexec c s)
          (SHAL.exec_contract cexec c s).
      Proof.
        intros w0 ι0 Hpc0. destruct c as [lvars pats req res ens].
        unfold SYMB.exec_contract, SHAL.exec_contract.
        eapply rel_bind; auto with typeclass_instances.
        apply rel_demonic_ctx; auto with typeclass_instances.
        intros w1 θ1 ι1 Heq1 Hpc1 slenv clenv rlenv.
        eapply rel_bind; auto with typeclass_instances.
        unfold evalCReaderT.
        apply refine_produce; auto.
        intros w2 θ2 ι2 Heq2 Hpc2 _ _ _.
        eapply rel_bind; auto with typeclass_instances.
        { unfold evalStoreT, evalCStoreT.
          eapply rel_bind; auto with typeclass_instances.
          apply rexec; auto.
          rewrite rlenv. subst. cbn.
          now rewrite inst_subst, <- inst_persist.
          intros w3 θ3 ι3 Heq3 Hpc3.
          intros [sa _] [ca _] [ra _].
          now apply rel_pure.
        }
        intros w3 θ3 ι3 Heq3 Hpc3 sv cv rv.
        apply refine_consume; auto.
        cbn. subst. f_equal. rewrite rlenv.
        now rewrite <- !inst_persist.
        apply rv.
      Qed.

    End WithExec.

  End Exec.

End RefineExecutorOn.
