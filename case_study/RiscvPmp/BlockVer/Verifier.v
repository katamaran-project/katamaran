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
     Bitvector
     Sep.Hoare
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

Module BlockVerificationDerived2.

  Import RiscvPmpBlockVerifSpec.
  Import RiscvPmpBlockVerifExecutor.
  Import Symbolic.

  Import ModalNotations.

  Definition M : TYPE -> TYPE := SStoreSpec [] [].

  Definition pure {A} : ⊢ A -> M A := SStoreSpec.pure.
  Definition bind {A B} : ⊢ M A -> □(A -> M B) -> M B := SStoreSpec.bind.
  Definition angelic : ⊢ ∀ σ : Ty, M (STerm σ) := @SStoreSpec.angelic [] None.
  Definition demonic : ⊢ ∀ σ : Ty, M (STerm σ) := @SStoreSpec.demonic [] None.
  Definition assert : ⊢ Formula -> M Unit := SStoreSpec.assert_formula.
  Definition assume : ⊢ Formula -> M Unit := SStoreSpec.assume_formula.

  Definition produce_chunk : ⊢ Chunk -> M Unit := SStoreSpec.produce_chunk.
  Definition consume_chunk : ⊢ Chunk -> M Unit := SStoreSpec.consume_chunk.

  Definition produce : ⊢ Assertion -> □(M Unit) := SStoreSpec.produce.
  Definition consume : ⊢ Assertion -> □(M Unit) := SStoreSpec.consume.

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
      ω8 ∣ _ <- SStoreSpec.exec default_config inline_fuel (FunDef step) ;;
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
      assert (formula_relop bop.eq na (term_binop bop.bvadd (persist__term a ω2) (term_val ty_word bv_instrsize))).


  Fixpoint exec_block_addr (b : list AST) : ⊢ STerm ty_xlenbits -> STerm ty_xlenbits -> M (STerm ty_xlenbits) :=
    fun _ ainstr apc =>
      match b with
      | nil       => pure apc
      | cons i b' =>
        ω1 ∣ _ <- assert (formula_relop bop.eq ainstr apc) ;;
        ω2 ∣ apc' <- exec_instruction_any i (persist__term apc ω1) ;;
        @exec_block_addr b' _ (term_binop bop.bvadd (persist__term ainstr (ω1 ∘ ω2)) (term_val ty_word bv_instrsize)) apc'
      end.

  (* Definition exec_double_addr {Σ : World} *)
  (*   (req : Assertion (Σ ▻ ("a":: ty_xlenbits))) (b : list AST) : M (STerm ty_xlenbits) Σ := *)
  (*   ω1 ∣ an <- @demonic _ _ ;; *)
  (*   ω2 ∣ _ <- produce (w := wsnoc _ _) req (acc_snoc_left ω1 _ an);; *)
  (*   @exec_block_addr b _ (persist__term an ω2) (persist__term an ω2). *)

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
  Definition VC__addr {Σ : LCtx} (req : Assertion {| wctx := Σ ▻ ("a":: ty_xlenbits); wco := []%ctx |}) (b : list AST)
    (ens : Assertion {| wctx := Σ ▻ ("a"::ty_xlenbits) ▻ ("an"::ty_xlenbits); wco := []%ctx |}) : 𝕊 ε :=
    SymProp.demonic_close
      (@exec_triple_addr
         {| wctx := Σ; wco := []%ctx |}
         req b ens
         (* Could include leakcheck here *)
         (fun _ _ _ _ h => SymProp.block)
         []%env []%list).

  Definition safeE {Σ} : 𝕊 Σ -> Prop :=
    fun P => VerificationConditionWithErasure (Erasure.erase_symprop P).

  Lemma safeE_safe (p : 𝕊 wnil) (ι : Valuation wnil) : safeE p -> SymProp.safe p [].
  Proof. apply verification_condition_with_erasure_sound. Qed.

End BlockVerificationDerived2.

Module BlockVerification3.

  Import RiscvPmpBlockVerifSpec.
  Import RiscvPmpBlockVerifExecutor.
  Import Symbolic.

  Import ModalNotations.
  Import BlockVerificationDerived2.

  Inductive AnnotInstr :=
  | AnnotAST : forall (i : AST), AnnotInstr
  | AnnotDebugBreak : AnnotInstr
  | AnnotLemmaInvocation : forall {Δ} (l : 𝑳 Δ) (es : NamedEnv (Exp [ctx]) Δ), AnnotInstr
  .

  Record DebugBlockver (Σ : LCtx) : Type :=
    MkDebugBlockver {
        debug_blockver_pathcondition          : PathCondition Σ;
        debug_blockver_heap                   : SHeap Σ;
      }.
  #[export] Instance SubstDebugBlockver : Subst DebugBlockver :=
    fun Σ0 d Σ1 ζ01 =>
      match d with
      | MkDebugBlockver pc1 h => MkDebugBlockver (subst pc1 ζ01) (subst h ζ01)
      end.

  #[export] Instance SubstLawsDebugBlockver : SubstLaws DebugBlockver.
  Proof.
    constructor.
    - intros ? []; cbn; now rewrite ?subst_sub_id.
    - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
  Qed.

  Import option.notations.
  #[export] Instance OccursCheckDebugBlockver : OccursCheck DebugBlockver :=
    fun Σ x xIn d =>
      match d with
      | MkDebugBlockver pc1 h =>
          pc' <- occurs_check xIn pc1 ;;
          h'  <- occurs_check xIn h ;;
          Some (MkDebugBlockver pc' h')
      end.


  Fixpoint exec_block_addr (b : list AnnotInstr) : ⊢ STerm ty_xlenbits -> STerm ty_xlenbits -> M (STerm ty_xlenbits) :=
    fun w0 ainstr apc =>
      match b with
      | nil       => pure apc
      | cons instr b' =>
          match instr with
          | AnnotAST i => ω1 ∣ _ <- assert (formula_relop bop.eq ainstr apc) ;;
                         ω2 ∣ apc' <- exec_instruction_any i (persist__term apc ω1) ;;
                         @exec_block_addr b' _ (term_binop bop.bvadd (persist__term ainstr (ω1 ∘ ω2)) (term_val ty_word bv_instrsize)) apc'
          | AnnotDebugBreak => SStoreSpec.debug
                                (fun (δ0 : SStore [ctx] w0) (h0 : SHeap w0) =>
                                   amsg.mk
                                     {| debug_blockver_pathcondition := wco w0;
                                       debug_blockver_heap := h0
                                     |})
                                (SStoreSpec.pure apc)
          | AnnotLemmaInvocation l es =>
              ω1 ∣ args <- SStoreSpec.eval_exps es (w:=w0) ;;
              ω2 ∣ _ <- SStoreSpec.call_lemma (LEnv l) args ;;
              @exec_block_addr b' _ (persist__term ainstr (ω1 ∘ ω2)) (persist__term apc (ω1 ∘ ω2))
          end
      end.

  Definition exec_triple_addr {Σ : World}
    (req : Assertion (Σ ▻ ("a"::ty_xlenbits))) (b : list AnnotInstr)
    (ens : Assertion (Σ ▻ ("a"::ty_xlenbits) ▻ ("an"::ty_xlenbits))) : M Unit Σ :=
    ω1 ∣ a <- @demonic _ _ ;;
    ω2 ∣ _ <- produce (w := wsnoc _ _) req (acc_snoc_left ω1 _ a) ;;
    ω3 ∣ na <- @exec_block_addr b _ (persist__term a ω2) (persist__term a ω2) ;;
    consume (w := wsnoc (wsnoc _ ("a"::ty_xlenbits)) ("an"::ty_xlenbits)) ens
      (acc_snoc_left (acc_snoc_left (ω1 ∘ ω2 ∘ ω3) _ (persist__term a (ω2 ∘ ω3))) ("an"::ty_xlenbits) na).

  (* This is a VC for triples, for doubles we probably need to talk *)
  (*    about the continuation of a block. *)
  Definition VC__addr {Σ : LCtx} (req : Assertion {| wctx := Σ ▻ ("a":: ty_xlenbits); wco := []%ctx |}) (b : list AnnotInstr)
    (ens : Assertion {| wctx := Σ ▻ ("a"::ty_xlenbits) ▻ ("an"::ty_xlenbits); wco := []%ctx |}) : 𝕊 ε :=
    SymProp.demonic_close
      (@exec_triple_addr
         {| wctx := Σ; wco := []%ctx |}
         req b ens
         (* Could include leakcheck here *)
         (fun _ _ _ _ h => SymProp.block)
         []%env []%list).
End BlockVerification3.

Module BlockVerificationDerived2Sound.
  Import RiscvPmpBlockVerifSpec.
  Import RiscvPmpBlockVerifShalExecutor.
  Import RiscvPmpIrisInstanceWithContracts.

  Definition M : Type -> Type := CStoreSpec [] [].

  Definition pure {A} : A -> M A := CStoreSpec.pure.
  Definition bind {A B} : M A -> (A -> M B) -> M B := CStoreSpec.bind.
  Definition angelic {σ} : M (Val σ) := @CStoreSpec.angelic [] σ.
  Definition demonic {σ} : M (Val σ) := @CStoreSpec.demonic [] σ.
  Definition assert : Prop -> M unit := CStoreSpec.assert_formula.
  Definition assume : Prop -> M unit := CStoreSpec.assume_formula.

  Definition produce_chunk : SCChunk -> M unit := CStoreSpec.produce_chunk.
  Definition consume_chunk : SCChunk -> M unit := CStoreSpec.consume_chunk.

  Definition produce {Σ} : Valuation Σ -> Assertion Σ -> M unit := CStoreSpec.produce.
  Definition consume {Σ} : Valuation Σ -> Assertion Σ -> M unit := CStoreSpec.consume.

  Notation "x <- ma ;; mb" :=
    (bind ma (fun x => mb))
      (at level 80, ma at level 90, mb at level 200, right associativity).

  Definition exec_instruction_any__c (i : AST) : Val ty_xlenbits -> M (Val ty_xlenbits) :=
    let inline_fuel := 10%nat in
    fun a =>
      _ <- produce_chunk (scchunk_ptsreg pc a) ;;
      _ <- produce_chunk (scchunk_user ptstoinstr [a; i]) ;;
      an <- @demonic _ ;;
      _ <- produce_chunk (scchunk_ptsreg nextpc an) ;;
      _ <- CStoreSpec.exec inline_fuel (FunDef step) ;;
      _ <- consume_chunk (scchunk_user ptstoinstr [a ; i]) ;;
      na <- @angelic _ ;;
      _ <- consume_chunk (scchunk_ptsreg nextpc na) ;;
      _ <- consume_chunk (scchunk_ptsreg pc na) ;; (* TODO: a + 4! *)
      pure na.

  Import logicalrelation logicalrelation.notations.
  Import StoreSpec.
  Import proofmode.
  Import iris.proofmode.tactics.

  Lemma refine_exec_instruction_any (i : AST) {w} :
    ⊢ ℛ⟦RVal ty_xlenbits -> RStoreSpec [ctx] [ctx] (RVal ty_xlenbits)⟧
      (exec_instruction_any__c i)
      (BlockVerificationDerived2.exec_instruction_any (w := w) i).
  Proof.
    unfold BlockVerificationDerived2.exec_instruction_any, exec_instruction_any__c.
    now rsolve.
  Qed.

  #[export] Instance refine_compat_exec_instruction_any {i : AST} {w} :
    RefineCompat (RVal ty_xlenbits -> RStoreSpec [ctx] [ctx] (RVal ty_xlenbits))
      (exec_instruction_any__c i) w (BlockVerificationDerived2.exec_instruction_any (w := w) i) _ :=
    MkRefineCompat (refine_exec_instruction_any i).

  Fixpoint exec_block_addr__c (b : list AST) : Val ty_xlenbits -> Val ty_xlenbits -> M (Val ty_xlenbits) :=
    fun ainstr apc =>
      match b with
      | nil       => pure apc
      | cons i b' =>
          _ <- assert (ainstr = apc) ;;
          apc' <- exec_instruction_any__c i apc ;;
          @exec_block_addr__c b' (bv.add ainstr bv_instrsize) apc'
      end.

  Lemma refine_exec_block_addr (b : list AST) {w} :
    ⊢ ℛ⟦RVal ty_xlenbits -> RVal ty_xlenbits -> RStoreSpec [ctx] [ctx] (RVal ty_xlenbits)⟧
      (exec_block_addr__c b)
      (@BlockVerificationDerived2.exec_block_addr b w).
  Proof.
    iAssert (ℛ⟦□ᵣ (RVal ty_xlenbits -> RVal ty_xlenbits -> RStoreSpec [ctx] [ctx] (RVal ty_xlenbits))⟧
               (exec_block_addr__c b)
               (fun w' ω => @BlockVerificationDerived2.exec_block_addr b w')) as "H".
    { 
      unfold exec_block_addr__c, BlockVerificationDerived2.exec_block_addr.
      iInduction b as [|*] "IHb"; rsolve.
      iApply ("IHb" with "[] [$]").
      now rsolve.
    } 
    iApply (unconditionally_T with "H").
  Qed.

  Definition exec_double_addr__c {Σ : World} (ι : Valuation Σ)
    (req : Assertion (wsnoc Σ ("a"∷ty_xlenbits))) (b : list AST) : M (Val ty_xlenbits) :=
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
    forall {ι : Valuation Σ},
      curval ι ⊢ ℛ⟦RStoreSpec [ctx] [ctx] RUnit⟧
        (exec_triple_addr__c ι req b ens)
        (@BlockVerificationDerived2.exec_triple_addr Σ req b ens).
  Proof.
    iIntros (ι) "Hι".
    unfold BlockVerificationDerived2.exec_triple_addr, exec_triple_addr__c.
    rsolve.
    - now iApply refine_rnenv_sub_acc.
    - iApply refine_exec_block_addr;
        rsolve.
    - now iApply refine_rnenv_sub_acc.
  Qed.

End BlockVerificationDerived2Sound.

Module BlockVerification3Sound.
  Import RiscvPmpBlockVerifSpec.
  Import RiscvPmpBlockVerifShalExecutor.
  Import RiscvPmpIrisInstanceWithContracts.
  Import BlockVerificationDerived2.
  Import BlockVerification3.
  Import BlockVerificationDerived2Sound.

  Fixpoint exec_block_addr__c (b : list AnnotInstr) : Val ty_xlenbits -> Val ty_xlenbits -> M (Val ty_xlenbits) :=
    fun ainstr apc =>
      match b with
      | nil       => pure apc
      | cons instr b' =>
          match instr with
          | AnnotAST i => _ <- assert (ainstr = apc) ;;
                         apc' <- exec_instruction_any__c i apc ;;
                         @exec_block_addr__c b' (bv.add ainstr bv_instrsize) apc'
          | AnnotDebugBreak => pure apc
          | AnnotLemmaInvocation l es =>
              args <- CStoreSpec.eval_exps es ;;
              _ <- CStoreSpec.call_lemma (LEnv l) args ;;
              exec_block_addr__c b' ainstr apc
          end
      end.

  Import logicalrelation logicalrelation.notations.
  Import iris.bi.interface iris.proofmode.tactics.
  Import StoreSpec.
  Import proofmode.

  Lemma refine_exec_block_addr (b : list AnnotInstr) {w} :
    ⊢ ℛ⟦RVal ty_xlenbits -> RVal ty_xlenbits -> RStoreSpec [ctx] [ctx] (RVal ty_xlenbits)⟧
      (exec_block_addr__c b)
      (@BlockVerification3.exec_block_addr b w).
  Proof.
    iAssert (ℛ⟦□ᵣ (RVal ty_xlenbits -> RVal ty_xlenbits -> RStoreSpec [ctx] [ctx] (RVal ty_xlenbits))⟧
               (exec_block_addr__c b)
               (fun w ω => @BlockVerification3.exec_block_addr b w)) as "H".
    { iInduction b as [|instr b] "IHb"; rsolve.
      destruct instr; cbn; rsolve.
      - iApply "IHb"; rsolve; now rewrite ?sub_acc_trans.
      - iApply "IHb"; rsolve; now rewrite ?sub_acc_trans. }
    now iApply (unconditionally_T with "H").
  Qed.

  Definition exec_triple_addr__c {Σ : World} (ι : Valuation Σ)
    (req : Assertion (Σ ▻ ("a"::ty_xlenbits))) (b : list AnnotInstr)
    (ens : Assertion (Σ ▻ ("a"::ty_xlenbits) ▻ ("an"::ty_xlenbits))) : M unit :=
    a <- @demonic _ ;;
    _ <- produce (ι ► ( _ ↦ a )) req ;;
    na <- @exec_block_addr__c b a a ;;
    consume (ι ► ( ("a"::ty_xlenbits) ↦ a ) ► ( ("an"::ty_xlenbits) ↦ na )) ens.

  Import ModalNotations.

  Lemma refine_exec_triple_addr {w : World}
    (req : Assertion (w ▻ ("a"::ty_xlenbits))) (b : list AnnotInstr)
    (ens : Assertion (w ▻ ("a"::ty_xlenbits) ▻ ("an"::ty_xlenbits))) :
    forall {ι0 : Valuation w},
      curval ι0 ⊢ ℛ⟦RStoreSpec [ctx] [ctx] RUnit⟧
        (exec_triple_addr__c ι0 req b ens)
        (@BlockVerification3.exec_triple_addr w req b ens).
  Proof.
    iIntros (ι) "Hι".
    unfold BlockVerification3.exec_triple_addr, exec_triple_addr__c.
    rsolve.
    - now iApply refine_rnenv_sub_acc.
    - iApply refine_exec_block_addr; now rsolve.
    - now iApply refine_rnenv_sub_acc.
  Qed.

End BlockVerification3Sound.

Module BlockVerificationDerived2Sem.
  Import iris.program_logic.weakestpre.
  Import iris.proofmode.tactics.
  Import RiscvPmpBlockVerifSpec.
  Import BlockVerificationDerived2.
  Import Shallow.Executor.
  Import ctx.resolution.
  Import ctx.notations.
  Import env.notations.
  Import RiscvPmpIrisBase.
  Import RiscvPmpIrisInstance.
  Import RiscvPmpIrisInstanceWithContracts.
  Import RiscvPmpBlockVerifShalExecutor.
  Import BlockVerificationDerived2Sound.

  Definition semTripleOneInstrStep `{sailGS Σ} (PRE : iProp Σ) (instr : AST) (POST : Val ty_word -> iProp Σ) (a : Val ty_word) : iProp Σ :=
    semTriple [] (PRE ∗ (∃ v, lptsreg nextpc v) ∗ lptsreg pc a ∗ interp_ptsto_instr a instr)
      (FunDef RiscvPmpProgram.step)
      (fun ret _ => (∃ an, lptsreg nextpc an ∗ lptsreg pc an ∗ POST an) ∗ interp_ptsto_instr a instr)%I.

  Lemma mono_exec_instruction_any__c {i a} : Monotonic' (exec_instruction_any__c i a).
  Proof.
    cbv [Monotonic' exec_instruction_any__c bind CStoreSpec.bind produce_chunk CStoreSpec.produce_chunk demonic CStoreSpec.demonic angelic CStoreSpec.angelic pure CStoreSpec.pure].
    intros δ P Q PQ h eP v.
    destruct (env.view δ).
    specialize (eP v); revert eP.
    apply exec_monotonic.
    clear -PQ. intros _ δ h.
    destruct (env.view δ).
    apply consume_chunk_monotonic.
    clear -PQ. intros _ h.
    intros [v H]; exists v; revert H.
    apply consume_chunk_monotonic.
    clear -PQ; intros _ h.
    apply consume_chunk_monotonic.
    clear -PQ; intros _ h.
    now apply PQ.
  Qed.

  Lemma sound_stm_aux `{sailGS Σ} {τ} {PRE} {s : Stm [ctx] τ} {POST} :
    ProgramLogic.Triple [env] PRE s POST ->
    ⊢ semTriple [env] PRE s POST.
  Proof.
    iIntros (Htrip) "PRE".
    iApply wp_mono.
    2: {
      iApply sound_stm.
      - apply foreignSemBlockVerif.
      - apply lemSemBlockVerif.
      - apply Htrip.
      - iApply contractsSound.
      - iFrame.
    }
    now iIntros.
  Qed.

  Lemma sound_exec_instruction_any_aux `{sailGS Σ} {instr} (h : SCHeap) (POST : Val ty_xlenbits -> CStore [ctx] -> iProp Σ) :
    forall a npc,
    exec_instruction_any__c instr a (fun res => liftP (POST res)) [] h ->
    ProgramLogic.Triple []
      (interpret_scheap (scchunk_ptsreg nextpc npc :: scchunk_user ptstoinstr [a; instr] :: scchunk_ptsreg pc a :: h)%list)
      (FunDef RiscvPmpProgram.step)
      (fun res => (fun δ' => interp_ptsto_instr a instr ∗ (∃ v, lptsreg nextpc v ∗ lptsreg pc v ∗ POST v δ'))%I).
  Proof.
    cbv [exec_instruction_any__c bind CStoreSpec.bind produce_chunk consume_chunk
      CStoreSpec.produce_chunk CHeapSpec.produce_chunk CPureSpec.produce_chunk
      CPureSpec.pure demonic CStoreSpec.demonic CStoreSpec.lift_purem
      CPureSpec.demonic].
    intros a npc Htrip. specialize (Htrip npc).
    apply (exec_sound 10). revert Htrip.
    apply exec_monotonic.
    intros _ δ0 h0 HYP.
    refine (consume_chunk_sound (scchunk_user ptstoinstr [a; instr]) (fun δ' => (∃ v, lptsreg nextpc v ∗ lptsreg pc v ∗ POST v δ'))%I δ0 h0 _).
    revert HYP. apply consume_chunk_monotonic.
    intros _ h1 [an Hrest]; revert Hrest.
    cbn.
    iIntros (HYP') "Hh1".
    iExists an.
    iStopProof.
    refine (consume_chunk_sound (scchunk_ptsreg nextpc an) (fun δ' => lptsreg pc an ∗ POST an δ')%I δ0 h1 _).
    revert HYP'.
    apply consume_chunk_monotonic.
    intros _ h2 HYP2.
    refine (consume_chunk_sound (scchunk_ptsreg pc an) (fun δ' => POST an δ')%I δ0 h2 _).
    revert HYP2.
    apply consume_chunk_monotonic.
    now intros _ h3 HYP3.
  Qed.


  Lemma sound_exec_instruction_any `{sailGS Σ} {instr} (h : SCHeap) (POST : Val ty_xlenbits -> CStore [ctx] -> iProp Σ) :
    forall a,
    exec_instruction_any__c instr a (fun res => liftP (POST res)) [] h ->
    ⊢ semTripleOneInstrStep (interpret_scheap h) instr (fun an => POST an []) a.
  Proof.
    intros a.
    intros Hverif.
    iIntros "(Hheap & [%npc Hnpc] & Hpc & Hinstrs)".
    apply (sound_exec_instruction_any_aux _ npc) in Hverif.
    iApply (semWP_mono with "[-]").
    iApply (sound_stm_aux Hverif with "[$Hnpc $Hinstrs $Hpc $Hheap]").
    iIntros ([] store) "[Hinstr [%an (Hnextpc & Hpc & HPOST)]]".
    destruct (env.view store).
    iFrame.
    iExists an.
    iFrame.
  Qed.

  Notation "a '↦' t" := (reg_pointsTo a t) (at level 70).
  Notation "a '↦ₘ' t" := (interp_ptsto a t) (at level 70).

  Fixpoint ptsto_instrs `{sailGS Σ} (a : Val ty_word) (instrs : list AST) : iProp Σ :=
    match instrs with
    | cons inst insts => (interp_ptsto_instr a inst ∗ ptsto_instrs (bv.add a bv_instrsize) insts)%I
    | nil => True%I
    end.
  (* Arguments ptsto_instrs {Σ H} a%Z_scope instrs%list_scope : simpl never. *)

  Lemma mono_exec_block_addr {instrs ainstr apc} : Monotonic' (exec_block_addr__c instrs ainstr apc).
  Proof.
    revert ainstr apc.
    induction instrs; cbn.
    - intros ainstr apc δ P Q PQ h.
      cbv [pure CStoreSpec.pure].
      apply PQ.
    - intros ainstr apc.
      cbv [Monotonic' bind CStoreSpec.bind assert CStoreSpec.assert_formula CStoreSpec.lift_purem CPureSpec.assert_formula].
      intros δ P Q PQ h [<- Hverif].
      split; [reflexivity|].
      revert Hverif.
      apply mono_exec_instruction_any__c.
      intros res h2.
      apply IHinstrs.
      intros res2 h3.
      now apply PQ.
  Qed.

  Lemma sound_exec_block_addr `{sailGS Σ} {instrs ainstr apc} (h : SCHeap) (POST : Val ty_xlenbits -> CStore [ctx] -> iProp Σ) :
    exec_block_addr__c instrs ainstr apc (fun res => liftP (POST res)) [] h ->
    ⊢ ((interpret_scheap h ∗ lptsreg pc apc ∗ (∃ v, lptsreg nextpc v) ∗ ptsto_instrs ainstr instrs) -∗
            (∀ an, lptsreg pc an ∗ (∃ v, lptsreg nextpc v) ∗ ptsto_instrs ainstr instrs ∗ POST an [] -∗ WP_loop) -∗
            WP_loop)%I.
  Proof.
    revert ainstr apc h POST.
    induction instrs as [|instr instrs]; cbn; intros ainstr apc h POST.
    - iIntros (Hverif) "(Hpre & Hpc & Hnpc & _) Hk".
      iApply "Hk"; iFrame.
      iSplitR; auto.
      now iApply Hverif.
    - intros [-> Hverif].
      iIntros "(Hh & Hpc & Hnpc & Hinstr & Hinstrs) Hk".
      iApply semWP_seq.
      iApply semWP_call_inline.
      cbn.
      iApply (semWP_mono with "[-Hinstrs Hk] [Hinstrs Hk]").
      { iApply (sound_exec_instruction_any (fun an δ => (lptsreg pc an) ∗ (∃ v, lptsreg nextpc v) ∗ ptsto_instrs (bv.add apc bv_instrsize) instrs -∗ (∀ an2 : Val ty_word, pc ↦ an2 ∗ (∃ v, nextpc ↦ v) ∗ ptsto_instrs (bv.add apc bv_instrsize) instrs ∗ POST an2 [env] -∗ WP_loop) -∗ WP_loop)%I with "[$]").
        revert Hverif.
        apply mono_exec_instruction_any__c.
        intros an h2.
        unfold liftP; cbn.
        iIntros (Hverif) "Hh2 (Hpc & Hnpc & Hinstrs) Hk".
        iApply (IHinstrs (bv.add apc bv_instrsize)%Z an _ _ Hverif with "[$]").
        iIntros (an2) "(Hpc & Hinstrs & HPOST)".
        iApply ("Hk" with "[$]").
      }
      iIntros (_ _) "([%an (Hnpc & Hpc & Hk2)] & Hinstr)".
      iSpecialize ("Hk2" with "[$Hpc Hnpc $Hinstrs]").
      { now iExists an. }
      iApply (semWP_call_inline loop).
      iApply "Hk2".
      iIntros (an2) "(Hpc & Hnpc & Hinstrs & HPOST)".
      iApply ("Hk" with "[$]").
  Qed.

  Definition semTripleBlock `{sailGS Σ} (PRE : Val ty_word -> iProp Σ) (instrs : list AST) (POST : Val ty_word -> Val ty_word -> iProp Σ) : iProp Σ :=
    (∀ a,
    (PRE a ∗ pc ↦ a ∗ (∃ v, nextpc ↦ v) ∗ ptsto_instrs a instrs) -∗
      (∀ an, pc ↦ an ∗ (∃ v, nextpc ↦ v) ∗ ptsto_instrs a instrs ∗ POST a an -∗ WP_loop) -∗
      WP_loop)%I.
  Global Arguments semTripleBlock {Σ} {_} PRE%I instrs POST%I.

  Lemma sound_exec_triple_addr__c `{sailGS Σ} {W : World} {pre post instrs} {ι : Valuation W} :
      (exec_triple_addr__c ι pre instrs post (λ _ _ _ , True) [env] []%list) ->
    ⊢ semTripleBlock (λ a : Val ty_word, asn.interpret pre (ι.[("a"::ty_xlenbits) ↦ a])) instrs
      (λ a na : Val ty_word, asn.interpret post (ι.[("a"::ty_xlenbits) ↦ a].[("an"::ty_xlenbits) ↦ na])).
  Proof.
    intros Hexec.
    iIntros (a) "(Hpre & Hpc & Hnpc & Hinstrs) Hk".
    specialize (Hexec a).
    unfold bind, CStoreSpec.bind, produce in Hexec.
    iApply (produce_sound (fun _ =>
                             (lptsreg pc a ∗ (∃ v, lptsreg nextpc v) ∗ ptsto_instrs a instrs) -∗
                             (∀ an, lptsreg pc an ∗ (∃ v, lptsreg nextpc v) ∗ ptsto_instrs a instrs ∗ asn.interpret post (ι.[("a"::ty_xlenbits) ↦ a].[("an"::ty_xlenbits) ↦ an]) -∗ WP_loop) -∗
                             WP_loop)%I [env] []%list with "[$Hpre //] [$Hpc $Hnpc $Hinstrs //] [$Hk]").
    revert Hexec.
    apply produce_monotonic.
    iIntros (_ h Hexec) "Hh (Hpc & Hnpc & Hinstrs) Hk".
    iApply (sound_exec_block_addr h
                  (fun an δ => asn.interpret post ι.["a"∷ty_word ↦ a].["an"∷ty_word ↦ an])%I
             with "[$Hh $Hpc $Hnpc $Hinstrs] Hk").
    revert Hexec.
    apply mono_exec_block_addr.
    intros res h2 Hcons. cbn.
    unfold liftP.
    rewrite <- (bi.sep_True (asn.interpret _ _)).
    eapply (consume_sound (fun _ => True%I) [env] ).
    revert Hcons.
    apply consume_monotonic.
    now iIntros.
  Qed.

  Lemma sound_VC__addr `{sailGS Σ} {Γ} {pre post instrs} :
    safeE (postprocess (BlockVerificationDerived2.VC__addr (Σ := Γ) pre instrs post)) ->
    forall ι,
    ⊢ semTripleBlock (fun a => asn.interpret pre (ι.[("a"::ty_xlenbits) ↦ a]))
      instrs
      (fun a na => asn.interpret post (ι.[("a"::ty_xlenbits) ↦ a].[("an"::ty_xlenbits) ↦ na])).
  Proof.
    intros Hverif ι.
    apply (sound_exec_triple_addr__c (W := {| wctx := Γ ; wco := []%ctx |}) (pre := pre) (post := post) (instrs := instrs)).
    eapply (fromEntails (w := wlctx Γ) (refine_exec_triple_addr (Σ := wlctx Γ) _ _ _) ι I eq_refl).
    all: cycle 3.
    - apply (fromBientails (w := wlctx Γ) (LogicalSoundness.psafe_safe) ι I).
      apply (safeE_safe env.nil), postprocess_sound in Hverif.
      rewrite SymProp.safe_demonic_close in Hverif.
      now apply Hverif.
    - done.
    - reflexivity.
    - constructor.
  Qed.

End BlockVerificationDerived2Sem.

Module BlockVerification3Sem.
  Import iris.program_logic.weakestpre.
  Import iris.proofmode.tactics.
  Import RiscvPmpBlockVerifSpec.
  Import BlockVerificationDerived2.
  Import Shallow.Executor.
  Import ctx.resolution.
  Import ctx.notations.
  Import env.notations.
  Import RiscvPmpIrisBase.
  Import RiscvPmpIrisInstance.
  Import RiscvPmpIrisInstanceWithContracts.
  Import RiscvPmpBlockVerifShalExecutor.
  Import BlockVerificationDerived2Sound.
  Import BlockVerificationDerived2Sem.
  Import BlockVerification3.
  Import BlockVerification3Sound.

  Lemma mono_exec_block_addr {instrs ainstr apc} : Monotonic' (exec_block_addr__c instrs ainstr apc).
  Proof.
    revert ainstr apc.
    induction instrs as [|instr instrs]; cbn.
    - intros ainstr apc δ P Q PQ h.
      cbv [pure CStoreSpec.pure].
      apply PQ.
    - destruct instr.
      + intros ainstr apc.
        cbv [Monotonic' bind CStoreSpec.bind assert CStoreSpec.assert_formula CStoreSpec.lift_purem CPureSpec.assert_formula].
        intros δ P Q PQ h [<- Hverif].
        split; [reflexivity|].
        revert Hverif.
        apply mono_exec_instruction_any__c.
        intros res h2.
        apply IHinstrs.
        intros res2 h3.
        now apply PQ.
      + intros ainstr apc.
        cbv [Monotonic' pure CStoreSpec.pure].
        intros. now apply PQ.
      + intros ainstr apc.
        cbv [Monotonic' bind CStoreSpec.bind assert CStoreSpec.assert_formula CStoreSpec.lift_purem CPureSpec.assert_formula].
        intros δ P Q PQ h.
        apply call_lemma_monotonic.
        intros res δ1 h2.
        apply IHinstrs.
        intros res2 h3.
        destruct (env.view δ), (env.view δ1).
        now apply PQ.
  Qed.

  Definition extract_AST (i : AnnotInstr) : option AST :=
    match i with
    | AnnotAST a => Some a
    | _ => None
    end.

  Lemma sound_exec_block_addr `{sailGS Σ} {instrs ainstr apc} (h : SCHeap) (POST : Val ty_xlenbits -> CStore [ctx] -> iProp Σ) :
    LemmaSem ->
    exec_block_addr__c instrs ainstr apc (fun res => liftP (POST res)) [] h ->
    ⊢ ((interpret_scheap h ∗ lptsreg pc apc ∗ (∃ v, lptsreg nextpc v) ∗ ptsto_instrs ainstr (omap extract_AST instrs)) -∗
            (∀ an, lptsreg pc an ∗ (∃ v, lptsreg nextpc v) ∗ ptsto_instrs ainstr (omap extract_AST instrs) ∗ POST an [] -∗ WP_loop) -∗
            WP_loop)%I.
  Proof.
    intros lemSem.
    revert ainstr apc h POST.
    induction instrs as [|instr instrs]; cbn; intros ainstr apc h POST.
    - iIntros (Hverif) "(Hpre & Hpc & Hnpc & _) Hk".
      iApply "Hk"; iFrame.
      iSplitR; auto.
      now iApply Hverif.
    - destruct instr as [instr| |Δ lem es].
      + intros [-> Hverif].
        iIntros "(Hh & Hpc & Hnpc & Hinstr & Hinstrs) Hk".
        iApply semWP_seq.
        iApply semWP_call_inline.
        iApply (semWP_mono with "[Hh Hnpc Hpc Hinstr]").
        { iApply ((sound_exec_instruction_any (fun an δ => (lptsreg pc an : iProp Σ) ∗ (∃ v, lptsreg nextpc v : iProp Σ) ∗ ptsto_instrs (bv.add apc bv_instrsize) (omap extract_AST instrs) -∗ (∀ an2 : Val ty_word, pc ↦ an2 ∗ (∃ v, nextpc ↦ v) ∗ ptsto_instrs (bv.add apc bv_instrsize) (omap extract_AST instrs) ∗ POST an2 [env] -∗ WP_loop) -∗ WP_loop)%I) with "[$]").
          revert Hverif.
          refine (mono_exec_instruction_any__c (h := h) _ _).
          intros an h2.
          unfold liftP; cbn.
          iIntros (Hverif) "Hh2 (Hpc & Hnpc & Hinstrs) Hk".
          iApply (IHinstrs (bv.add apc bv_instrsize)%Z an _ _ Hverif with "[$]").
          iIntros (an2) "(Hpc & Hinstrs & HPOST)".
          iApply "Hk"; now iFrame.
        }
        iIntros (_ _) "([%an (Hnpc & Hpc & Hk2)] & Hinstr)".
        iApply (semWP_call_inline loop).
        iApply ("Hk2" with "[$Hpc Hnpc $Hinstrs]"); first by iExists _.
        iIntros (an2) "(Hpc & Hnpc & Hinstrs & HPOST)".
        iApply ("Hk" with "[$]").
      + iIntros (Hpost) "(Hh & Hpc & Hnpc & Hinstrs) Hk".
        iApply ("Hk" with "[$Hpc $Hnpc $Hinstrs Hh]").
        now iApply Hpost.
      + iIntros (Hlemcall) "(Hh & Hpc & Hnpc & Hinstrs) Hk".
        unfold bind, CStoreSpec.bind in Hlemcall; cbn.
        unfold CStoreSpec.eval_exps in Hlemcall.
        assert (CStoreSpec.call_lemma (LEnv lem) (evals es [env]) (fun _ => liftP (fun δ => lptsreg pc apc ∗ (∃ v : Val ty_xlenbits, lptsreg nextpc v) ∗ ptsto_instrs ainstr (omap extract_AST instrs) -∗
                   (∀ an : Val ty_xlenbits, lptsreg pc an ∗ (∃ v : Val ty_xlenbits, lptsreg nextpc v) ∗ ptsto_instrs ainstr (omap extract_AST instrs) ∗ POST an [env] -∗ WP_loop) -∗ WP_loop)%I) [env] h) as Hcalllemma.
        { revert Hlemcall.
          apply call_lemma_monotonic.
          intros _ δ h2.
          destruct (env.view δ).
          unfold liftP; cbn.
          iIntros (Heb) "Hh2 (Hpc & Hnpc & Hinstrs) Hk".
          iApply (IHinstrs _ _ _ _ Heb with "[$Hh2 $Hpc $Hnpc $Hinstrs]").
          now iApply "Hk".
        }
        pose proof (Hlem := lemSem _ lem).
        destruct (call_lemma_sound _ _ h _ _ Hcalllemma).
        cbn in *.
        iPoseProof (H0 with "Hh") as "(%ι & _ & Hreq & Hk2)".
        iApply ("Hk2" with "[Hreq] [$Hpc $Hnpc $Hinstrs] Hk").
        now iApply Hlem.
  Qed.

  Definition semTripleBlock `{sailGS Σ} (PRE : Val ty_word -> iProp Σ) (instrs : list AnnotInstr) (POST : Val ty_word -> Val ty_word -> iProp Σ) : iProp Σ :=
    (∀ a,
    (PRE a ∗ pc ↦ a ∗ (∃ v, nextpc ↦ v) ∗ ptsto_instrs a (omap extract_AST instrs)) -∗
      (∀ an, pc ↦ an ∗ (∃ v, nextpc ↦ v) ∗ ptsto_instrs a (omap extract_AST instrs) ∗ POST a an -∗ WP_loop) -∗
      WP_loop)%I.
  Global Arguments semTripleBlock {Σ} {_} PRE%I instrs POST%I.

  Lemma sound_exec_triple_addr__c `{sailGS Σ} {W : World} {pre post instrs} {ι : Valuation W} :
    LemmaSem ->
      (exec_triple_addr__c ι pre instrs post (λ _ _ _ , True) [env] []%list) ->
    ⊢ semTripleBlock (λ a : Val ty_word, asn.interpret pre (ι.[("a"::ty_xlenbits) ↦ a])) instrs
      (λ a na : Val ty_word, asn.interpret post (ι.[("a"::ty_xlenbits) ↦ a].[("an"::ty_xlenbits) ↦ na])).
  Proof.
    intros lemSem Hexec.
    iIntros (a) "(Hpre & Hpc & Hnpc & Hinstrs) Hk".
    specialize (Hexec a).
    unfold bind, CStoreSpec.bind, produce in Hexec.
    iApply ((produce_sound (fun _ =>
    (lptsreg pc a ∗ (∃ v, lptsreg nextpc v) ∗ ptsto_instrs a (omap extract_AST instrs)) -∗
      (∀ an, lptsreg pc an ∗ (∃ v, lptsreg nextpc v) ∗ ptsto_instrs a (omap extract_AST instrs) ∗ asn.interpret post (ι.[("a"::ty_xlenbits) ↦ a].[("an"::ty_xlenbits) ↦ an]) -∗ WP_loop) -∗
      WP_loop)%I [env] []%list) with "[$Hpre //] [$Hpc $Hnpc $Hinstrs //] [$Hk]").
    revert Hexec.
    apply produce_monotonic.
    iIntros (_ h Hexec) "Hh (Hpc & Hnpc & Hinstrs) Hk".
    iApply ((sound_exec_block_addr (apc := a) h
                  (fun an δ => asn.interpret post ι.["a"∷ty_word ↦ a].["an"∷ty_word ↦ an])%I)
               with "[$Hh $Hpc $Hnpc $Hinstrs] Hk"); first easy.
    revert Hexec.
    apply mono_exec_block_addr.
    intros res h2 Hcons. cbn.
    unfold liftP.
    rewrite <-(bi.sep_True (asn.interpret _ _)).
    eapply (consume_sound (fun _ => True%I) [env]).
    revert Hcons.
    apply consume_monotonic.
    now iIntros.
  Qed.

  Lemma sound_VC__addr `{sailGS Σ} {Γ} {pre post instrs} :
    LemmaSem ->
    safeE (postprocess (BlockVerification3.VC__addr (Σ := Γ) pre instrs post)) ->
    forall ι,
    ⊢ semTripleBlock (fun a => asn.interpret pre (ι.[("a"::ty_xlenbits) ↦ a]))
      instrs
      (fun a na => asn.interpret post (ι.[("a"::ty_xlenbits) ↦ a].[("an"::ty_xlenbits) ↦ na])).
  Proof.
    intros lemSem Hverif ι.
    apply (sound_exec_triple_addr__c (W := {| wctx := Γ ; wco := []%ctx |}) (pre := pre) (post := post) (instrs := instrs)); first easy.
    eapply (fromEntails (w := wlctx Γ) (refine_exec_triple_addr _ _ _) ι I eq_refl _ (λ w1 _ _ _ _, SymProp.block)).
    all: cycle 3.
    - apply (fromBientails (w := wlctx Γ) (LogicalSoundness.psafe_safe) ι I).
      apply (safeE_safe env.nil), postprocess_sound in Hverif.
      rewrite SymProp.safe_demonic_close in Hverif.
      now apply Hverif.
    - now intros.
    - reflexivity.
    - constructor.
  Qed.

End BlockVerification3Sem.
