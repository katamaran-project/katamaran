(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel, Dominique Devriese, Sander Huyghebaert  *)
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
     ZArith.ZArith
     Lists.List
     micromega.Lia
     Strings.String.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Iris.Instance
     Iris.Model
     Notations
     Semantics
     Sep.Hoare
     Sep.Logic
     Shallow.Executor
     Shallow.Soundness
     Specification
     Symbolic.Executor
     Symbolic.Propositions
     Symbolic.Solver
     Symbolic.Soundness
     Symbolic.Worlds
     RiscvPmp.BlockVer.Spec
     RiscvPmp.IrisModel
     RiscvPmp.IrisInstance
     RiscvPmp.Machine
     RiscvPmp.Sig.
From Katamaran Require
     RiscvPmp.Contracts
     RiscvPmp.LoopVerification
     RiscvPmp.Model.
From iris.base_logic Require lib.gen_heap lib.iprop invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac.
From iris.program_logic Require weakestpre adequacy.
From iris.proofmode Require string_ident tactics.
From stdpp Require namespaces.

Import RiscvPmpProgram.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import env.notations.
Import ListNotations.
Open Scope string_scope.
Open Scope ctx_scope.
Open Scope Z_scope.

Module ns := stdpp.namespaces.

(*   Definition pmp_entry_cfg := ty_prod ty_pmpcfg_ent ty_xlenbits. *)

Module BlockVerification.
  Import RiscvPmpBlockVerifSpec.
  Import RiscvPmpBlockVerifExecutor.

  Notation "r '↦' val" := (chunk_ptsreg r val) (at level 79).

  Import ModalNotations.
  Import bv.notations.

  Definition M : TYPE -> TYPE := SHeapSpecM [] [].

  Definition pure {A} : ⊢ A -> M A := SHeapSpecM.pure.
  Definition bind {A B} : ⊢ M A -> □(A -> M B) -> M B := SHeapSpecM.bind.
  Definition angelic {σ} : ⊢ M (STerm σ) := @SHeapSpecM.angelic [] None σ.
  Definition assert : ⊢ Formula -> M Unit := SHeapSpecM.assert_formula.
  Definition assume : ⊢ Formula -> M Unit := SHeapSpecM.assume_formula.

  Definition produce_chunk : ⊢ Chunk -> M Unit := SHeapSpecM.produce_chunk.
  Definition consume_chunk : ⊢ Chunk -> M Unit := SHeapSpecM.consume_chunk.

  Definition produce : ⊢ Assertion -> □(M Unit) := SHeapSpecM.produce.
  Definition consume : ⊢ Assertion -> □(M Unit) := SHeapSpecM.consume.

  Notation "ω ∣ x <- ma ;; mb" :=
    (bind ma (fun _ ω x => mb))
      (at level 80, x at next level,
        ma at next level, mb at level 200,
        right associativity).

  Definition rX (r : Reg ty_xlenbits) : ⊢ M (STerm ty_xlenbits) :=
    fun _ =>
      ω01 ∣ v1 <- @angelic ty_xlenbits _ ;;
      ω12 ∣ _  <- consume_chunk (r ↦ v1) ;;
      let v2 := persist__term v1 ω12 in
      ω23 ∣ _ <- produce_chunk (r ↦ v2) ;;
      let v3 := persist__term v2 ω23 in
      pure v3.

  Definition wX (r : Reg ty_xlenbits) : ⊢ STerm ty_xlenbits -> M Unit :=
    fun _ u0 =>
      ω01 ∣ v1 <- @angelic ty_xlenbits _ ;;
      ω12 ∣ _  <- consume_chunk (r ↦ v1) ;;
      let u2 := persist__term u0 (acc_trans ω01 ω12) in
      produce_chunk (r ↦ u2).

  Definition exec_rtype (rs2 rs1 rd : Reg ty_xlenbits) (op : ROP) : ⊢ M Unit :=
    fun _ =>
      ω01 ∣ v11 <- @rX rs1 _ ;;
      ω12 ∣ v22 <- @rX rs2 _ ;;
      let v12 := persist__term v11 ω12 in
      let bop := match op with
                 | RISCV_ADD => bop.plus
                 | RISCV_SUB => bop.minus
                 end in
      wX rd (peval_binop bop v12 v22).

  Definition exec_instruction (i : AST) : ⊢ M Unit :=
    match i with
    | RTYPE rs2 rs1 rd op =>
        match reg_convert rs2, reg_convert rs1, reg_convert rd with
        | Some rs2, Some rs1, Some rd => exec_rtype rs2 rs1 rd op
        | _, _, _ => fun _ => pure tt
        end
    | _                   => fun _ => pure tt
    end.

  (* Ideally, a block should be a list of non-branching
     instruction plus one final branching instruction *)
  Fixpoint exec_block (b : list AST) : ⊢ M Unit :=
    fun _ =>
      match b with
      | nil       => pure tt
      | cons i b' =>
        _ ∣ _ <- @exec_instruction i _ ;;
        @exec_block b' _
      end.

  Definition exec_double {Σ : World}
    (req : Assertion Σ) (b : list AST) : M Unit Σ :=
    ω1 ∣ _ <- T (produce req) ;;
    @exec_block b _.

  Definition exec_triple {Σ : World}
    (req : Assertion Σ) (b : list AST) (ens : Assertion Σ) : M Unit Σ :=
    ω ∣ _ <- exec_double req b ;;
    consume ens ω.

  Module Post := Postprocessing.
  (* This is a VC for triples, for doubles we probably need to talk
     about the continuation of a block. *)
  Definition VC {Σ : LCtx} (req : Assertion Σ) (b : list AST) (ens : Assertion Σ) : 𝕊 Σ :=
    Post.prune (Post.solve_uvars (Post.prune (Post.solve_evars (Post.prune
      (@exec_triple
        {| wctx := Σ; wco := nil |}
        req b ens
        (* Could include leakcheck here *)
        (fun _ _ _ _ h => SymProp.block)
        []%env []%list))))).

End BlockVerification.

Module BlockVerificationDerived.

  Import Contracts.
  Import RiscvPmpBlockVerifSpec.
  Import RiscvPmpBlockVerifExecutor.
  Import Symbolic.

  Import ModalNotations.

  Definition M : TYPE -> TYPE := SHeapSpecM [] [].

  Definition pure {A} : ⊢ A -> M A := SHeapSpecM.pure.
  Definition bind {A B} : ⊢ M A -> □(A -> M B) -> M B := SHeapSpecM.bind.
  Definition angelic {σ} : ⊢ M (STerm σ) := @SHeapSpecM.angelic [] None σ.
  Definition demonic {σ} : ⊢ M (STerm σ) := @SHeapSpecM.demonic [] None σ.
  Definition assert : ⊢ Formula -> M Unit := SHeapSpecM.assert_formula.
  Definition assume : ⊢ Formula -> M Unit := SHeapSpecM.assume_formula.

  Definition produce_chunk : ⊢ Chunk -> M Unit := SHeapSpecM.produce_chunk.
  Definition consume_chunk : ⊢ Chunk -> M Unit := SHeapSpecM.consume_chunk.

  Definition produce : ⊢ Assertion -> □(M Unit) := SHeapSpecM.produce.
  Definition consume : ⊢ Assertion -> □(M Unit) := SHeapSpecM.consume.

  Notation "ω ∣ x <- ma ;; mb" :=
    (bind ma (fun _ ω x => mb))
      (at level 80, x at next level,
        ma at next level, mb at level 200,
        right associativity).

  Definition exec_instruction' (i : AST) : ⊢ M (STerm ty_retired) :=
    let inline_fuel := 3%nat in
    fun w0 POST _ =>
      SHeapSpecM.exec
        default_config inline_fuel (FunDef execute)
        (fun w1 ω01 res _ => POST w1 ω01 res []%env)
        [term_val (type ("ast" :: ty_ast)) i]%env.

  Definition exec_instruction (i : AST) : ⊢ M Unit :=
    fun _ =>
      _ ∣ msg <- @exec_instruction' i _ ;;
      assert (formula_eq msg (term_val ty_retired RETIRE_SUCCESS)).

  (* Ideally, a block should be a list of non-branching
     instruction plus one final branching instruction *)
  Fixpoint exec_block (b : list AST) : ⊢ M Unit :=
    fun _ =>
      match b with
      | nil       => pure tt
      | cons i b' =>
        _ ∣ _ <- @exec_instruction i _ ;;
        @exec_block b' _
      end.


  Definition exec_double {Σ : World}
    (req : Assertion Σ) (b : list AST) : M Unit Σ :=
    ω1 ∣ _ <- T (produce req) ;;
    @exec_block b _.

  Definition exec_triple {Σ : World}
    (req : Assertion Σ) (b : list AST) (ens : Assertion Σ) : M Unit Σ :=
    ω ∣ _ <- exec_double req b ;;
    consume ens ω.

  (* This is a VC for triples, for doubles we probably need to talk
     about the continuation of a block. *)
  Definition VC {Σ : LCtx} (req : Assertion Σ) (b : list AST) (ens : Assertion Σ) : 𝕊 ε :=
    SymProp.demonic_close
      (@exec_triple
         {| wctx := Σ; wco := nil |}
         req b ens
         (* Could include leakcheck here *)
         (fun _ _ _ _ h => SymProp.block)
         []%env []%list).

End BlockVerificationDerived.

Module BlockVerificationDerived2.

  Import Contracts.
  Import RiscvPmpBlockVerifSpec.
  Import RiscvPmpBlockVerifExecutor.
  Import Symbolic.

  Import ModalNotations.

  Definition M : TYPE -> TYPE := SHeapSpecM [] [].

  Definition pure {A} : ⊢ A -> M A := SHeapSpecM.pure.
  Definition bind {A B} : ⊢ M A -> □(A -> M B) -> M B := SHeapSpecM.bind.
  Definition angelic {σ} : ⊢ M (STerm σ) := @SHeapSpecM.angelic [] None σ.
  Definition demonic {σ} : ⊢ M (STerm σ) := @SHeapSpecM.demonic [] None σ.
  Definition assert : ⊢ Formula -> M Unit := SHeapSpecM.assert_formula.
  Definition assume : ⊢ Formula -> M Unit := SHeapSpecM.assume_formula.

  Definition produce_chunk : ⊢ Chunk -> M Unit := SHeapSpecM.produce_chunk.
  Definition consume_chunk : ⊢ Chunk -> M Unit := SHeapSpecM.consume_chunk.

  Definition produce : ⊢ Assertion -> □(M Unit) := SHeapSpecM.produce.
  Definition consume : ⊢ Assertion -> □(M Unit) := SHeapSpecM.consume.

  Notation "ω ∣ x <- ma ;; mb" :=
    (bind ma (fun _ ω x => mb))
      (at level 80, x at next level,
        ma at next level, mb at level 200,
        right associativity).

  Definition exec_instruction_any (i : AST) : ⊢ STerm ty_xlenbits -> M (STerm ty_xlenbits) :=
    let inline_fuel := 10%nat in
    fun _ a =>
      ω2 ∣ _ <- produce_chunk (chunk_ptsreg pc a) ;;
      ω4 ∣ _ <- produce_chunk (chunk_user ptstoinstr [persist__term a ω2; term_val ty_ast i]) ;;
      ω6 ∣ an <- @demonic _ _ ;;
      ω7 ∣ _ <- produce_chunk (chunk_ptsreg nextpc an) ;;
      ω8 ∣ _ <- SHeapSpecM.exec default_config inline_fuel (FunDef step) ;;
      ω9 ∣ _ <- consume_chunk (chunk_user ptstoinstr [persist__term a (ω2 ∘ ω4 ∘ ω6 ∘ ω7 ∘ ω8); term_val ty_ast i]) ;;
      ω10 ∣ na <- @angelic _ _ ;;
      ω11 ∣ _ <- consume_chunk (chunk_ptsreg nextpc na) ;;
      ω12 ∣ _ <- consume_chunk (chunk_ptsreg pc (persist__term na ω11)) ;;
      pure (persist__term na (ω11 ∘ ω12)).

  Definition exec_instruction (i : AST) : ⊢ M Unit :=
    let inline_fuel := 10%nat in
    fun _ =>
      ω1 ∣ a <- @demonic _ _ ;;
      ω2 ∣ na <- exec_instruction_any i a ;;
      assert (formula_eq na (term_binop bop.plus (persist__term a ω2) (term_val ty_exc_code 4))).


  Fixpoint exec_block_addr (b : list AST) : ⊢ STerm ty_xlenbits -> STerm ty_xlenbits -> M (STerm ty_xlenbits) :=
    fun _ ainstr apc =>
      match b with
      | nil       => pure apc
      | cons i b' =>
        ω1 ∣ _ <- assert (formula_eq ainstr apc) ;;
        ω2 ∣ apc' <- exec_instruction_any i (persist__term apc ω1) ;;
        @exec_block_addr b' _ (term_binop bop.plus (persist__term ainstr (ω1 ∘ ω2)) (term_val ty_xlenbits 4)) apc'
      end.

  Definition exec_double_addr {Σ : World}
    (req : Assertion (Σ ▻ ("a":: ty_xlenbits))) (b : list AST) : M (STerm ty_xlenbits) Σ :=
    ω1 ∣ an <- @demonic _ _ ;;
    ω2 ∣ _ <- produce (w := wsnoc _ _) req (acc_snoc_left ω1 _ an);;
    @exec_block_addr b _ (persist__term an ω2) (persist__term an ω2).

  Definition exec_triple_addr {Σ : World}
    (req : Assertion (Σ ▻ ("a"::ty_xlenbits))) (b : list AST)
    (ens : Assertion (Σ ▻ ("a"::ty_xlenbits) ▻ ("an"::ty_xlenbits))) : M Unit Σ :=
    ω1 ∣ a <- @demonic _ _ ;;
    ω2 ∣ _ <- produce (w := wsnoc _ _) req (acc_snoc_left ω1 _ a) ;;
    ω3 ∣ na <- @exec_block_addr b _ (persist__term a ω2) (persist__term a ω2) ;;
    consume (w := wsnoc (wsnoc _ ("a"::ty_xlenbits)) ("an"::ty_xlenbits)) ens
      (acc_snoc_left (acc_snoc_left (ω1 ∘ ω2 ∘ ω3) _ (persist__term a (ω2 ∘ ω3))) ("an"::ty_xlenbits) na).

  (* This is a VC for triples, for doubles we probably need to talk
     about the continuation of a block. *)
  Definition VC__addr {Σ : LCtx} (req : Assertion {| wctx := Σ ▻ ("a":: ty_xlenbits); wco := nil |}) (b : list AST)
    (ens : Assertion {| wctx := Σ ▻ ("a"::ty_xlenbits) ▻ ("an"::ty_xlenbits); wco := nil |}) : 𝕊 ε :=
    SymProp.demonic_close
      (@exec_triple_addr
         {| wctx := Σ; wco := nil |}
         req b ens
         (* Could include leakcheck here *)
         (fun _ _ _ _ h => SymProp.block)
         []%env []%list).

  Definition simplify {Σ} : 𝕊 Σ -> 𝕊 Σ :=
    fun P => let P2 := Postprocessing.prune P in
          let P3 := Postprocessing.solve_evars P2 in
          let P4 := Postprocessing.solve_uvars P3 in
          P4.

  Lemma simplify_sound {Σ} (p : 𝕊 Σ) (ι : Valuation Σ) : SymProp.safe (simplify p) ι -> SymProp.safe p ι.
  Proof.
    unfold simplify.
    intros Hs.
    now apply (Postprocessing.prune_sound p), Postprocessing.solve_evars_sound, Postprocessing.solve_uvars_sound.
  Qed.

  Definition safeE {Σ} : 𝕊 Σ -> Prop :=
    fun P => VerificationConditionWithErasure (Erasure.erase_symprop P).

  Definition safeE_safe (p : 𝕊 wnil) (ι : Valuation wnil) : safeE p -> SymProp.safe p [].
  Proof.
    unfold safeE.
    destruct 1 as [H].
    now eapply Erasure.erase_safe'.
  Qed.

End BlockVerificationDerived2.

Module BlockVerificationDerivedSem.
  Import Contracts.
  Import RiscvPmpIrisBase.
  Import RiscvPmpIrisInstance.
  Import RiscvPmpBlockVerifSpec.
  Import weakestpre.
  Import tactics.
  Import BlockVerificationDerived.
  Import RiscvPmpIrisInstanceWithContracts.

  Import ctx.resolution.
  Import ctx.notations.
  Import env.notations.

  Definition semTripleOneInstr `{sailGS Σ} (PRE : iProp Σ) (a : AST) (POST : iProp Σ) : iProp Σ :=
    semTriple [a : Val (type ("ast" :: ty_ast))]%env PRE (FunDef execute) (fun ret _ => ⌜ret = RETIRE_SUCCESS⌝ ∗ POST)%I.

  Module ValidContractsBlockVerif.
    Import RiscvPmpBlockVerifExecutor.
    Import Symbolic.


    (* Lemma sound_exec_instruction {ast} `{sailGS Σ} : *)
    (*   SymProp.safe (exec_instruction (w := wnil) ast (fun _ _ res _ h => SymProp.block) env.nil []%list) env.nil -> *)
    (*   ⊢ semTripleOneInstr emp%I ast emp%I. *)
    (* Proof. *)
    (*   unfold exec_instruction, exec_instruction', assert. *)
    (*   iIntros (safe_exec) "". *)
    (*   rewrite <-SymProp.safe_debug_safe in safe_exec. *)
    (*   rewrite <-SymProp.wsafe_safe in safe_exec. *)
    (*   iApply (sound_stm foreignSemBlockVerif lemSemBlockVerif). *)
    (* Admitted. *)
    (*   - refine (exec_sound 3 _ _ _ []%list _). *)
    (*     enough (CMut.bind (CMut.exec 3 (FunDef execute)) (fun v => CMut.assert_formula (v = RETIRE_SUCCESS)) (fun _ _ _ => True) [ast] []%list). *)
    (*     + unfold CMut.bind, CMut.assert_formula, CMut.dijkstra, CDijk.assert_formula in H0. *)
    (*       refine (exec_monotonic _ _ _ _ _ _ _ H0). *)
    (*       intros ret δ h [-> _]; cbn. *)
    (*       iIntros "_". iPureIntro. now split. *)
    (*     + refine (approx_exec _ _ _ _ _ safe_exec); cbn; try trivial; try reflexivity. *)
    (*       intros w ω ι _ Hpc tr ? -> δ δ' Hδ h h' Hh. *)
    (*       refine (approx_assert_formula _ _ _ (a := fun _ _ _ => True) _ _ _); *)
    (*         try assumption; try reflexivity. *)
    (*       constructor. *)
    (*   - do 2 iModIntro. *)
    (*     iApply contractsSound. *)
    (* Qed. *)
  End ValidContractsBlockVerif.

End BlockVerificationDerivedSem.

Module BlockVerificationDerived2Sound.
  Import Contracts.
  Import RiscvPmpBlockVerifSpec.
  Import RiscvPmpBlockVerifShalExecutor.
  Import RiscvPmpIrisInstanceWithContracts.

  Definition M : Type -> Type := CHeapSpecM [] [].

  Definition pure {A} : A -> M A := CHeapSpecM.pure.
  Definition bind {A B} : M A -> (A -> M B) -> M B := CHeapSpecM.bind.
  Definition angelic {σ} : M (Val σ) := @CHeapSpecM.angelic [] σ.
  Definition demonic {σ} : M (Val σ) := @CHeapSpecM.demonic [] σ.
  Definition assert : Prop -> M unit := CHeapSpecM.assert_formula.
  Definition assume : Prop -> M unit := CHeapSpecM.assume_formula.

  Definition produce_chunk : SCChunk -> M unit := CHeapSpecM.produce_chunk.
  Definition consume_chunk : SCChunk -> M unit := CHeapSpecM.consume_chunk.

  Definition produce {Σ} : Valuation Σ -> Assertion Σ -> M unit := CHeapSpecM.produce.
  Definition consume {Σ} : Valuation Σ -> Assertion Σ -> M unit := CHeapSpecM.consume.

  Local Notation "x <- ma ;; mb" :=
    (bind ma (fun x => mb))
      (at level 80, ma at level 90, mb at level 200, right associativity).

  Definition exec_instruction_any__c (i : AST) : Val ty_xlenbits -> M (Val ty_xlenbits) :=
    let inline_fuel := 10%nat in
    fun a =>
      _ <- produce_chunk (scchunk_ptsreg pc a) ;;
      _ <- produce_chunk (scchunk_user ptstoinstr [a; i]) ;;
      an <- @demonic _ ;;
      _ <- produce_chunk (scchunk_ptsreg nextpc an) ;;
      _ <- CHeapSpecM.exec inline_fuel (FunDef step) ;;
      _ <- consume_chunk (scchunk_user ptstoinstr [a ; i]) ;;
      na <- @angelic _ ;;
      _ <- consume_chunk (scchunk_ptsreg nextpc na) ;;
      _ <- consume_chunk (scchunk_ptsreg pc na) ;; (* TODO: a + 4! *)
      pure na.

  Lemma refine_exec_instruction_any  (i : AST) :
    forall {w0 : World} {ι0 : Valuation w0} (Hpc0 : instpc (wco w0) ι0),
      refine ι0 (@BlockVerificationDerived2.exec_instruction_any i w0)
        (exec_instruction_any__c i).
  Proof.
    unfold BlockVerificationDerived2.exec_instruction_any, exec_instruction_any__c.
    intros w0 ι0 Hpc0 a a0 ->.
    apply refine_bind.
    apply refine_produce_chunk; auto.
    { reflexivity. }
    intros w1 ω1 ι1 -> Hpc1 [] [] _.
    apply refine_bind.
    apply refine_produce_chunk; auto.
    { now rewrite H, <-inst_persist. }
    intros w2 ω2 ι2 -> Hpc2 [] [] _.
    apply refine_bind.
    apply refine_demonic; auto.
    intros w3 ω3 ι3 -> Hpc3 an anv ->.
    apply refine_bind.
    apply refine_produce_chunk; auto.
    { reflexivity. }
    intros w4 ω4 ι4 -> Hpc4 [] [] _.
    apply refine_bind.
    { apply refine_exec; auto. }
    intros w5 ω5 ι5 -> Hpc5 res ? ->.
    apply refine_bind.
    apply refine_consume_chunk; auto.
    { rewrite H.
      unfold refine, RefineInst. cbn. repeat f_equal.
      rewrite (inst_persist (H := inst_term) _ _ a).
      now rewrite ?sub_acc_trans, ?inst_subst.
    }
    intros w6 ω6 ι6 -> Hpc6 [] ? ->.
    apply refine_bind.
    apply refine_angelic; auto.
    intros w7 ω7 ι7 -> Hpc7 na ? ->.
    apply refine_bind.
    apply refine_consume_chunk; auto.
    { reflexivity. }
    intros w8 ω8 ι8 -> Hpc8 [] [] _.
    apply refine_bind.
    apply refine_consume_chunk; auto.
    { unfold refine, RefineInst. cbn. repeat f_equal.
      now rewrite (inst_persist (H := inst_term) _ _ na).
    }
    intros w9 ω9 ι9 -> Hpc9 [] [] _.
    apply refine_pure; auto.
    unfold refine, RefineTermVal, RefineInst.
    rewrite (inst_persist (H := inst_term) _ _ na).
    now rewrite ?sub_acc_trans, ?inst_subst.
  Qed.

  Fixpoint exec_block_addr__c (b : list AST) : Val ty_xlenbits -> Val ty_xlenbits -> M (Val ty_xlenbits) :=
    fun ainstr apc =>
      match b with
      | nil       => pure apc
      | cons i b' =>
        _ <- assert (ainstr = apc) ;;
        apc' <- exec_instruction_any__c i apc ;;
        @exec_block_addr__c b' (ainstr + 4) apc'
      end.

  Lemma refine_exec_block_addr  (b : list AST) :
    forall {w0 : World} {ι0 : Valuation w0} (Hpc0 : instpc (wco w0) ι0),
      refine ι0 (@BlockVerificationDerived2.exec_block_addr b w0)
        (exec_block_addr__c b).
  Proof.
    induction b.
    - intros w0 ι0 Hpc0 a ? ->.
      now apply refine_pure.
    - intros w0 ι0 Hpc0 ainstr ? -> apc ? ->.
      cbn.
      apply refine_bind.
      apply refine_assert_formula; auto.
      intros w1 ω1 ι1 -> Hpc1 [] [] _.
      apply refine_bind.
      apply refine_exec_instruction_any; auto.
      unfold refine, RefineTermVal, RefineInst.
      now rewrite (inst_persist (H := inst_term)).
      intros w2 ω2 ι2 -> Hpc2 napc ? ->.
      apply IHb; auto.
      {unfold refine, RefineTermVal, RefineInst.
        cbn. f_equal.
        change (inst_term ?t ?ι) with (inst t ι).
        rewrite (inst_persist (H := inst_term) (acc_trans ω1 ω2) _ ainstr).
        now rewrite ?sub_acc_trans, ?inst_subst.
      }
      { reflexivity. }
  Qed.

  Definition exec_double_addr__c {Σ : World} (ι : Valuation Σ)
    (req : Assertion (wsnoc Σ ("a"::ty_xlenbits))) (b : list AST) : M (Val ty_xlenbits) :=
    an <- @demonic _ ;;
    _ <- produce (env.snoc ι ("a"::ty_xlenbits) an) req ;;
    @exec_block_addr__c b an an.

  Definition exec_triple_addr__c {Σ : World} (ι : Valuation Σ)
    (req : Assertion (Σ ▻ ("a"::ty_xlenbits))) (b : list AST)
    (ens : Assertion (Σ ▻ ("a"::ty_xlenbits) ▻ ("an"::ty_xlenbits))) : M unit :=
    a <- @demonic _ ;;
    _ <- produce (ι ► ( _ ↦ a )) req ;;
    na <- @exec_block_addr__c b a a ;;
    consume (ι ► ( ("a"::ty_xlenbits) ↦ a ) ► ( ("an"::ty_xlenbits) ↦ na )) ens.

  Import ModalNotations.

  Lemma refine_exec_triple_addr {Σ : World}
    (req : Assertion (Σ ▻ ("a"::ty_xlenbits))) (b : list AST)
    (ens : Assertion (Σ ▻ ("a"::ty_xlenbits) ▻ ("an"::ty_xlenbits))) :
    forall {ι0 : Valuation Σ} (Hpc0 : instpc (wco Σ) ι0),
      refine ι0 (@BlockVerificationDerived2.exec_triple_addr Σ req b ens)
        (exec_triple_addr__c ι0 req b ens).
  Proof.
    intros ι0 Hpc0.
    unfold BlockVerificationDerived2.exec_triple_addr, exec_triple_addr__c.
    eapply refine_bind.
    { eapply refine_demonic; auto. }
    intros w1 ω1 ι1 -> Hpc1 a ? ->.
    eapply refine_bind.
    { eapply refine_produce; auto.
      cbn.
      now rewrite inst_subst, inst_sub_wk1.
    }
    intros w2 ω2 ι2 -> Hpc2 [] [] _.
    eapply refine_bind.
    {eapply refine_exec_block_addr; auto;
        unfold refine, RefineTermVal, RefineInst in *;
        change (persist__term a ω2) with (persist a ω2);
        now rewrite inst_persist.
    }
    intros w3 ω3 ι3 -> Hpc3 na ? ->.
    eapply refine_consume; auto.
    cbn -[sub_wk1].
    now rewrite ?inst_subst, ?inst_sub_wk1.
    cbn [acc_snoc_left sub_acc].
    refine (eq_trans _ (eq_sym (inst_sub_snoc ι3 (sub_snoc (sub_acc (ω1 ∘ ω2 ∘ ω3)) ("a"∷ty_exc_code) (persist__term a (ω2 ∘ ω3))) ("an"::ty_exc_code) na))).
    f_equal.
    rewrite inst_sub_snoc.
    rewrite <-?inst_subst.
    rewrite H, ?sub_acc_trans.
    repeat f_equal.
    change (persist__term a (ω2 ∘ ω3)) with (persist a (ω2 ∘ ω3)).
    now rewrite (inst_persist (ω2 ∘ ω3) ι3 a), sub_acc_trans, inst_subst.
  Qed.

End BlockVerificationDerived2Sound.

Module BlockVerificationDerived2Sem.
  Import Contracts.
  Import RiscvPmpBlockVerifSpec.
  Import weakestpre.
  Import tactics.
  Import BlockVerificationDerived2.
  Import Shallow.Executor.
  Import ctx.resolution.
  Import ctx.notations.
  Import env.notations.
  Import RiscvPmpIrisBase.
  Import RiscvPmpIrisInstance.
  Import RiscvPmpIrisInstanceWithContracts.
  Import RiscvPmpBlockVerifShalExecutor.
  (* Import Model.RiscvPmpModel. *)
  (* Import Model.RiscvPmpModel2. *)
  (* Import RiscvPmpIrisParams. *)
  (* Import RiscvPmpIrisPredicates. *)
  (* Import RiscvPmpIrisPrelims. *)
  (* Import RiscvPmpIrisResources. *)
  Import BlockVerificationDerived2Sound.
  (* Import RiscvPmpModelBlockVerif.PLOG. *)
  (* Import Sound. *)

  Definition semTripleOneInstrStep `{sailGS Σ} (PRE : iProp Σ) (instr : AST) (POST : Z -> iProp Σ) (a : Z) : iProp Σ :=
    semTriple [] (PRE ∗ (∃ v, lptsreg nextpc v) ∗ lptsreg pc a ∗ interp_ptsto_instr a instr)
      (FunDef RiscvPmpProgram.step)
      (fun ret _ => (∃ an, lptsreg nextpc an ∗ lptsreg pc an ∗ POST an) ∗ interp_ptsto_instr a instr)%I.

  Lemma mono_exec_instruction_any__c {i a} : Monotonic' (exec_instruction_any__c i a).
    cbv [Monotonic' exec_instruction_any__c bind CHeapSpecM.bind produce_chunk CHeapSpecM.produce_chunk demonic CHeapSpecM.demonic angelic CHeapSpecM.angelic pure CHeapSpecM.pure].
    intros δ P Q PQ h eP v.
    destruct (env.nilView δ).
    specialize (eP v); revert eP.
    apply exec_monotonic.
    clear -PQ. intros _ δ h.
    destruct (env.nilView δ).
    apply consume_chunk_monotonic.
    clear -PQ. intros _ h.
    intros [v H]; exists v; revert H.
    apply consume_chunk_monotonic.
    clear -PQ; intros _ h.
    apply consume_chunk_monotonic.
    clear -PQ; intros _ h.
    now apply PQ.
  Qed.


  Lemma sound_exec_instruction_any `{sailGS Σ} {instr} (h : SCHeap) (POST : Val ty_xlenbits -> CStore [ctx] -> iProp Σ) :
    forall a,
    exec_instruction_any__c instr a (fun res => liftP (POST res)) [] h ->
    ⊢ semTripleOneInstrStep (interpret_scheap h)%I instr (fun an => POST an [])%I a.
  Proof.
    intros a.
    intros Hverif.
    iIntros "(Hheap & [%npc Hnpc] & Hpc & Hinstrs)".
    unfold exec_instruction_any__c, bind, CHeapSpecM.bind, produce_chunk, CHeapSpecM.produce_chunk, demonic, CHeapSpecM.demonic, consume_chunk in Hverif.
    specialize (Hverif npc).
    assert (ProgramLogic.Triple [] (interpret_scheap (scchunk_ptsreg nextpc npc :: scchunk_user ptstoinstr [a; instr] :: scchunk_ptsreg pc a :: h)%list) (FunDef RiscvPmpProgram.step) (fun res => (fun δ' => interp_ptsto_instr a instr ∗ (∃ v, lptsreg nextpc v ∗ lptsreg pc v ∗ POST v δ'))%I)) as Htriple.
    { apply (exec_sound 10).
      refine (exec_monotonic 10 _ _ _ _ _ _ Hverif).
      intros [] δ0 h0 HYP.
      cbn.
      refine (consume_chunk_sound (scchunk_user ptstoinstr [a; instr]) (fun δ' => (∃ v, lptsreg nextpc v ∗ lptsreg pc v ∗ POST v δ'))%I δ0 h0 _).
      refine (consume_chunk_monotonic _ _ _ _ _ HYP).
      intros [] h1 [an Hrest]; revert Hrest.
      cbn.
      iIntros (HYP') "Hh1".
      iExists an.
      iStopProof.
      refine (consume_chunk_sound (scchunk_ptsreg nextpc an) (fun δ' => lptsreg pc an ∗ POST an δ')%I δ0 h1 _).
      refine (consume_chunk_monotonic _ _ _ _ _ HYP').
      intros [] h2 HYP2.
      refine (consume_chunk_sound (scchunk_ptsreg pc an) (fun δ' => POST an δ')%I δ0 h2 _).
      refine (consume_chunk_monotonic _ _ _ _ _ HYP2).
      now intros [] h3 HYP3.
    }
    apply sound_stm in Htriple.
    unfold semTriple in Htriple.
    iApply wp_mono.
    all: cycle 1.
    { iApply Htriple.
      iApply contractsSound.
      { cbn. now iFrame. }
    }
    apply foreignSemBlockVerif.
    apply lemSemBlockVerif.
    { iIntros ([[] store]) "[Hinstr [%an (Hnextpc & Hpc & HPOST)]]".
      destruct (env.nilView store).
      iFrame.
      iExists an.
      iFrame.
    }
  Qed.

  Local Notation "a '↦' t" := (reg_pointsTo a t) (at level 79).
  Local Notation "a '↦ₘ' t" := (interp_ptsto a t) (at level 79).

  Fixpoint ptsto_instrs `{sailGS Σ} (a : Z) (instrs : list AST) : iProp Σ :=
    match instrs with
    | cons inst insts => (interp_ptsto_instr a inst ∗ ptsto_instrs (a + 4) insts)%I
    | nil => True%I
    end.
  Arguments ptsto_instrs {Σ H} a%Z_scope instrs%list_scope : simpl never.

  Lemma mono_exec_block_addr {instrs ainstr apc} : Monotonic' (exec_block_addr__c instrs ainstr apc).
  Proof.
    revert ainstr apc.
    induction instrs; cbn.
    - intros ainstr apc δ P Q PQ h.
      cbv [pure CHeapSpecM.pure].
      eapply PQ.
    - intros ainstr apc.
      cbv [Monotonic' bind CHeapSpecM.bind assert CHeapSpecM.assert_formula CHeapSpecM.lift_purem CPureSpecM.assert_formula].
      intros δ P Q PQ h [<- Hverif].
      split; [reflexivity|].
      revert Hverif.
      eapply mono_exec_instruction_any__c.
      intros res h2.
      eapply IHinstrs.
      intros res2 h3.
      now eapply PQ.
  Qed.

  Lemma sound_exec_block_addr `{sailGS Σ} {instrs ainstr apc} (h : SCHeap) (POST : Val ty_xlenbits -> CStore [ctx] -> iProp Σ) :
    exec_block_addr__c instrs ainstr apc (fun res => liftP (POST res)) [] h ->
    ⊢ ((interpret_scheap h ∗ lptsreg pc apc ∗ (∃ v, lptsreg nextpc v) ∗ ptsto_instrs ainstr instrs) -∗
            (∀ an, lptsreg pc an ∗ (∃ v, lptsreg nextpc v) ∗ ptsto_instrs ainstr instrs ∗ POST an [] -∗ LoopVerification.WP_loop) -∗
            LoopVerification.WP_loop)%I.
  Proof.
    revert ainstr apc h POST.
    induction instrs as [|instr instrs]; cbn; intros ainstr apc h POST.
    - iIntros (Hverif) "(Hpre & Hpc & Hnpc & _) Hk".
      iApply "Hk"; iFrame.
      iSplitR; auto.
      now iApply Hverif.
    - unfold bind, CHeapSpecM.bind, assert, CHeapSpecM.assert_formula.
      unfold CHeapSpecM.lift_purem, CPureSpecM.assert_formula.
      intros [-> Hverif].
      unfold LoopVerification.WP_loop at 2, FunDef, fun_loop.
      assert (⊢ semTripleOneInstrStep (interpret_scheap h)%I instr
                (fun an =>
                   lptsreg pc an ∗ (∃ v, lptsreg nextpc v) ∗ ptsto_instrs (apc + 4) instrs -∗
                   (∀ an2 : Z, pc ↦ an2 ∗ (∃ v, lptsreg nextpc v) ∗ ptsto_instrs (apc + 4) instrs ∗ POST an2 [env] -∗ LoopVerification.WP_loop) -∗
                     LoopVerification.WP_loop) apc)%I as Hverif2.
      { apply (sound_exec_instruction_any (fun an δ => (lptsreg pc an : iProp Σ) ∗ (∃ v, lptsreg nextpc v : iProp Σ) ∗ ptsto_instrs (apc + 4) instrs -∗ (∀ an2 : Z, pc ↦ an2 ∗ (∃ v, nextpc ↦ v) ∗ ptsto_instrs (apc + 4) instrs ∗ POST an2 [env] -∗ LoopVerification.WP_loop) -∗ LoopVerification.WP_loop)%I).
        revert Hverif.
        eapply mono_exec_instruction_any__c.
        intros an h2.
        unfold liftP; cbn.
        iIntros (Hverif) "Hh2 (Hpc & Hnpc & Hinstrs) Hk".
        iApply (IHinstrs (apc + 4)%Z an _ _ Hverif with "[$]").
        iIntros (an2) "(Hpc & Hinstrs & HPOST)".
        iApply "Hk"; now iFrame.
      }
      iIntros "(Hh & Hpc & Hnpc & Hinstr & Hinstrs) Hk".
      iApply (iris_rule_stm_seq _ _ _ _ _ (fun _ _ => True%I) with "[] [Hk Hinstrs] [Hinstr Hpc Hh Hnpc]").
      + iPoseProof Hverif2 as "Hverif2".
        unfold semTripleOneInstrStep.
        iApply (iris_rule_stm_call_inline env.nil RiscvPmpProgram.step env.nil with "Hverif2").
      + iIntros (δ) "(([%an (Hnpc & Hpc & Hk2)] & Hinstr) & <-)".
        iSpecialize ("Hk2" with "[Hpc Hnpc Hinstrs]").
        iFrame. now iExists an.
        iApply (wp_mono _ _ _ (fun v => True ∧ _)%I (fun v => True%I)).
        all: cycle 1.
        iApply (iris_rule_stm_call_inline env.nil RiscvPmpProgram.loop env.nil True%I (fun v => True%I) with "[Hk Hk2 Hinstr] [$]").
        iIntros "_".
        iApply "Hk2".
        iIntros (an2) "(Hpc & Hnpc & Hinstrs & HPOST)".
        iApply "Hk".
        iFrame.
        now iIntros.
      + iFrame.
  Qed.

  Definition semTripleBlock `{sailGS Σ} (PRE : Z -> iProp Σ) (instrs : list AST) (POST : Z -> Z -> iProp Σ) : iProp Σ :=
    (∀ a,
    (PRE a ∗ pc ↦ a ∗ (∃ v, nextpc ↦ v) ∗ ptsto_instrs a instrs) -∗
      (∀ an, pc ↦ an ∗ (∃ v, nextpc ↦ v) ∗ ptsto_instrs a instrs ∗ POST a an -∗ LoopVerification.WP_loop) -∗
      LoopVerification.WP_loop)%I.

  Lemma sound_exec_triple_addr__c `{sailGS Σ} {W : World} {pre post instrs} {ι : Valuation W} :
      (exec_triple_addr__c ι pre instrs post (λ _ _ _ , True) [env] []%list) ->
    ⊢ semTripleBlock (λ a : Z, interpret_assertion pre (ι.[("a"::ty_xlenbits) ↦ a])) instrs
      (λ a na : Z, interpret_assertion post (ι.[("a"::ty_xlenbits) ↦ a].[("an"::ty_xlenbits) ↦ na])).
  Proof.
    intros Hexec.
    iIntros (a) "(Hpre & Hpc & Hnpc & Hinstrs) Hk".
    specialize (Hexec a).
    unfold bind, CHeapSpecM.bind, produce in Hexec.
    assert (interpret_scheap []%list ∗ interpret_assertion pre ι.[("a"::ty_exc_code) ↦ a] ⊢ 
    (True ∗ lptsreg pc a ∗ (∃ v, lptsreg nextpc v) ∗ ptsto_instrs a instrs) -∗
      (∀ an, lptsreg pc an ∗ (∃ v, lptsreg nextpc v) ∗ ptsto_instrs a instrs ∗ interpret_assertion post (ι.[("a"::ty_xlenbits) ↦ a].[("an"::ty_xlenbits) ↦ an]) -∗ LoopVerification.WP_loop) -∗
      LoopVerification.WP_loop)%I as Hverif.
    { refine (@produce_sound _ _ _ _ (ι.[("a"::ty_exc_code) ↦ a]) pre (fun _ =>
    (True ∗ lptsreg pc a ∗ (∃ v, lptsreg nextpc v) ∗ ptsto_instrs a instrs) -∗
      (∀ an, lptsreg pc an ∗ (∃ v, lptsreg nextpc v) ∗ ptsto_instrs a instrs ∗ interpret_assertion post (ι.[("a"::ty_xlenbits) ↦ a].[("an"::ty_xlenbits) ↦ an]) -∗ LoopVerification.WP_loop) -∗
      LoopVerification.WP_loop)%I [env] []%list _).
      revert Hexec.
      apply produce_monotonic.
      unfold consume.
      intros _ h Hexec.
      cbn.
      assert (
          ⊢ ((interpret_scheap h ∗ lptsreg pc a ∗ (∃ v, lptsreg nextpc v) ∗ ptsto_instrs a instrs) -∗
               (∀ an, lptsreg pc an ∗ (∃ v, lptsreg nextpc v) ∗ ptsto_instrs a instrs ∗
                        interpret_assertion post ι.["a"∷ty_exc_code ↦ a].["an"∷ty_exc_code ↦ an]
                         -∗ LoopVerification.WP_loop) -∗
               LoopVerification.WP_loop)%I) as Hverifblock.
      { eapply (sound_exec_block_addr h
                  (fun an δ => interpret_assertion post ι.["a"∷ty_exc_code ↦ a].["an"∷ty_exc_code ↦ an])%I).
        refine (mono_exec_block_addr _ _ _ _ _ Hexec).
        intros res h2 Hcons. cbn.
        rewrite <-(bi.sep_True (interpret_assertion post ι.["a"∷ty_exc_code ↦ a].["an"∷ty_exc_code ↦ res] : iProp Σ)).
        eapply (consume_sound (fun _ => True%I : iProp Σ)).
        revert Hcons.
        refine (consume_monotonic _ _ _ _ _).
        cbn. now iIntros.
      }
      iIntros "Hh".
      clear -Hverifblock.
      iIntros "(_ & Hpc & Hnpc & Hinstrs) Hk".
      iApply (Hverifblock with "[Hh Hpc Hnpc Hinstrs] Hk").
      iFrame.
    }
    iApply (Hverif with "[Hpre] [Hpc Hnpc Hinstrs]");
      cbn; iFrame.
  Qed.

  Lemma sound_VC__addr `{sailGS Σ} {Γ} {pre post instrs} :
    safeE (simplify (BlockVerificationDerived2.VC__addr (Σ := Γ) pre instrs post)) ->
    forall ι,
    ⊢ semTripleBlock (fun a => interpret_assertion pre (ι.[("a"::ty_xlenbits) ↦ a]))
      instrs
      (fun a na => interpret_assertion post (ι.[("a"::ty_xlenbits) ↦ a].[("an"::ty_xlenbits) ↦ na])).
  Proof.
    intros Hverif ι.
    eapply (sound_exec_triple_addr__c (W := {| wctx := Γ ; wco := [] |}) (pre := pre) (post := post) (instrs := instrs)).
    eapply (refine_exec_triple_addr (Σ := {| wctx := Γ ; wco := [] |}) I (ta := λ w1 _ _ _ _, SymProp.block)).
    all: cycle 3.
    - rewrite SymProp.wsafe_safe SymProp.safe_debug_safe.
      eapply (safeE_safe env.nil), simplify_sound in Hverif.
      rewrite SymProp.safe_demonic_close in Hverif.
      now eapply Hverif.
    - unfold refine, RefineBox, RefineImpl, refine, RefineProp.
      now intros.
    - reflexivity.
    - reflexivity.
  Qed.

End BlockVerificationDerived2Sem.
