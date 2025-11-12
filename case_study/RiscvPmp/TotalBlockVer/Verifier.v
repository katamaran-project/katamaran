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
     Classes.Morphisms_Prop
     ZArith.ZArith
     Lists.List
     micromega.Lia
     Strings.String.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Iris.Instance
     Iris.Base
     Notations
     Semantics
     Bitvector
     Refinement.Monads
     Sep.Hoare
     Specification
     Symbolic.Propositions
     Symbolic.Solver
     Symbolic.Worlds
     MicroSail.ShallowExecutor
     MicroSail.ShallowSoundness
     MicroSail.SymbolicExecutor
     MicroSail.RefineExecutor
     MicroSail.Soundness
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

Import RiscvPmpIrisBase RiscvPmpIrisInstance.
#[local] Notation "a '↦' t" := (reg_pointsTo a t) (at level 70).
#[local] Notation "a '↦ₘ' t" := (interp_ptsto a t) (at level 70).

Module ns := stdpp.namespaces.

(*   Definition pmp_entry_cfg := ty_prod ty_pmpcfg_ent ty_xlenbits. *)

Section BlockVerificationDerived.

  Import RiscvPmpBlockVerifExecutor.
  Import RiscvPmpBlockVerifShalExecutor.

  Definition safeE {Σ} : 𝕊 Σ -> Prop :=
    fun P => VerificationConditionWithErasure (Erasure.erase_symprop P).

  Definition safeE_safe (p : 𝕊 wnil) (ι : Valuation wnil) : safeE p -> SymProp.safe p [].
  Proof.
    unfold safeE.
    destruct 1 as [H].
    now apply Erasure.erase_safe'.
  Qed.

  Section Symbolic.

    Import ModalNotations.
    Import SStoreSpec (evalStoreSpec).
    Import SHeapSpec SHeapSpec.notations.
    Import asn.notations.

    Definition exec_instruction_prologue (i : AST) :
      Assertion ([ctx] ▻ ("a":: ty_xlenbits)) :=
      pc     ↦ term_var "a" ∗
      asn.chunk (chunk_user ptstoinstr [term_var "a"; term_val ty_ast i]) ∗
      asn.exist "an" ty_xlenbits (nextpc ↦ term_var "an").

    Definition exec_instruction_epilogue (i : AST) :
      Assertion ([ctx] ▻ ("a":: ty_xlenbits) ▻ ("an":: ty_xlenbits)) :=
      pc     ↦ term_var "an" ∗
      asn.chunk (chunk_user ptstoinstr [term_var "a"; term_val ty_ast i]) ∗
      nextpc ↦ term_var "an".

    Definition sexec_instruction (i : AST) :
      ⊢ STerm ty_xlenbits -> SHeapSpec (STerm ty_xlenbits) :=
      let inline_fuel := 10%nat in
      fun _ a =>
        ⟨ θ1 ⟩ _  <- produce
                       (exec_instruction_prologue i)
                       [env].["a"∷_ ↦ a] ;;
        ⟨ θ2 ⟩ _  <- evalStoreSpec (sexec default_config inline_fuel (FunDef step) _) [env] ;;
        ⟨ θ3 ⟩ na <- angelic None _ ;;
        let a3 := persist__term a (θ1 ∘ θ2 ∘ θ3) in
        ⟨ θ4 ⟩ _  <- consume
                       (exec_instruction_epilogue i)
                       [env].["a"∷_ ↦ a3].["an"∷_ ↦ na] ;;
        pure (persist__term na θ4).

    Fixpoint sexec_block_addr (b : list AST) :
      ⊢ STerm ty_xlenbits -> STerm ty_xlenbits -> SHeapSpec (STerm ty_xlenbits) :=
      fun _ ainstr apc =>
        match b with
        | nil       => pure apc
        | cons i b' =>
            ⟨ θ1 ⟩ _    <- assert_formula (fun _ => amsg.empty)
                             (formula_relop bop.eq ainstr apc) ;;
            ⟨ θ2 ⟩ apc' <- sexec_instruction i (persist__term apc θ1) ;;
            sexec_block_addr b'
              (term_binop bop.bvadd
                 (persist__term ainstr (θ1 ∘ θ2))
                 (term_val ty_word bv_instrsize))
              apc'
        end.

    Definition sexec_triple_addr {Σ : LCtx}
      (req : Assertion (Σ ▻ ("a"::ty_xlenbits))) (b : list AST)
      (ens : Assertion (Σ ▻ ("a"::ty_xlenbits) ▻ ("an"::ty_xlenbits))) :
      ⊢ SHeapSpec Unit :=
      fun w =>
        ⟨ θ0 ⟩ δ <- demonic_ctx id Σ ;;
        ⟨ θ1 ⟩ a <- demonic (Some "a") _ ;;
        let δ1 := env.snoc (persist ( A:= Sub Σ) δ θ1) _ a in
        ⟨ θ2 ⟩ _ <- produce req δ1 ;;
        let a2 := persist__term a θ2 in
        ⟨ θ3 ⟩ na <- sexec_block_addr b a2 a2 ;;
        let δ3 := persist δ1 (θ2 ∘ θ3) in
        consume ens δ3.["an"∷ty_xlenbits ↦ na].

    (* This is a VC for triples, for doubles we probably need to talk
       about the continuation of a block. *)
    Definition sblock_verification_condition {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (b : list AST)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) : ⊢ 𝕊 :=
      fun w =>
        (* SHeapSpec does not perform a leakcheck. We could include one here. *)
        SHeapSpec.run (sexec_triple_addr req b ens (w := w)).

  End Symbolic.

  Section Shallow.

    Import CStoreSpec (evalStoreSpec).
    Import CHeapSpec CHeapSpec.notations.

    Definition cexec_instruction (i : AST) :
      Val ty_xlenbits -> CHeapSpec (Val ty_xlenbits) :=
      let inline_fuel := 10%nat in
      fun a =>
        _ <- produce
               (exec_instruction_prologue i)
               [env].["a"∷_ ↦ a] ;;
        _ <- evalStoreSpec (cexec inline_fuel (FunDef step)) [env] ;;
        na <- angelic _ ;;
        _ <- consume
               (exec_instruction_epilogue i)
               [env].["a"∷ty_xlenbits ↦ a].["an"∷_ ↦ na] ;;
        pure na.

    Fixpoint cexec_block_addr (b : list AST) :
      Val ty_xlenbits -> Val ty_xlenbits -> CHeapSpec (Val ty_xlenbits) :=
      fun ainstr apc =>
        match b with
        | nil       => pure apc
        | cons i b' =>
            _ <- assert_formula (ainstr = apc) ;;
            apc' <- cexec_instruction i apc ;;
            cexec_block_addr b' (bv.add ainstr bv_instrsize) apc'
        end.

    Definition cexec_triple_addr {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (b : list AST)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) :
      CHeapSpec unit :=
      lenv <- demonic_ctx Σ ;;
      a    <- demonic _ ;;
      _    <- produce req lenv.["a"∷ty_xlenbits ↦ a]  ;;
      na   <- cexec_block_addr b a a ;;
      consume ens lenv.["a"∷ty_xlenbits ↦ a].["an"∷ty_xlenbits ↦ na].

    Definition cblock_verification_condition {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (b : list AST)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) : Prop :=
      (* CHeapSpec.run does not perform a leakcheck. We could include one here. *)
      CHeapSpec.run (cexec_triple_addr req b ens).

    Import (hints) CStoreSpec.

    #[export] Instance mono_cexec_instruction {i a} :
      Monotonic (MHeapSpec eq) (cexec_instruction i a).
    Proof. typeclasses eauto. Qed.

    #[export] Instance mono_cexec_block_addr {instrs ainstr apc} :
      Monotonic (MHeapSpec eq) (cexec_block_addr instrs ainstr apc).
    Proof. revert ainstr apc. induction instrs; cbn; typeclasses eauto. Qed.

  End Shallow.

  Section Relational.

    Import iris.proofmode.tactics logicalrelation logicalrelation.notations.
    Import RiscvPmpIrisInstanceWithContracts.StoreSpec.
    Import RiscvPmpIrisInstanceWithContracts.
    Import RiscvPmpSignature.HeapSpec.
    Import RSolve HeapSpec.

    Lemma rexec_instruction (i : AST) {w} :
      ⊢ ℛ⟦RVal ty_xlenbits -> RHeapSpec (RVal ty_xlenbits)⟧
          (cexec_instruction i)
          (sexec_instruction (w := w) i).
    Proof.
      unfold cexec_instruction, sexec_instruction. rsolve.
    Qed.

    #[export] Instance refine_compat_exec_instruction {i : AST} {w} :
      RefineCompat (RVal ty_xlenbits -> RHeapSpec (RVal ty_xlenbits))
        (cexec_instruction i) w (sexec_instruction (w := w) i) _ :=
      MkRefineCompat (rexec_instruction i).

    Lemma rexec_block_addr (b : list AST) {w} :
      ⊢ ℛ⟦RVal ty_xlenbits -> RVal ty_xlenbits -> RHeapSpec (RVal ty_xlenbits)⟧
          (cexec_block_addr b)
          (sexec_block_addr b (w := w)).
    Proof.
      iAssert (ℛ⟦□ᵣ (RVal ty_xlenbits -> RVal ty_xlenbits -> RHeapSpec (RVal ty_xlenbits))⟧
                 (cexec_block_addr b)
                 (fun w' θ => sexec_block_addr b (w := w'))) as "H".
      {
        iInduction b as [|*] "IHb"; cbn; rsolve.
        iApply ("IHb" with "[] [$]").
        now rsolve.
      }
      iApply (unconditionally_T with "H").
    Qed.

    Lemma rexec_triple_addr {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (b : list AST)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) {w} :
      ⊢ ℛ⟦RHeapSpec RUnit⟧
          (cexec_triple_addr req b ens)
          (sexec_triple_addr req b ens (w := w)).
    Proof.
      unfold cexec_triple_addr, sexec_triple_addr.
      rsolve.
      iApply rexec_block_addr; rsolve.
      rewrite !forgetting_trans.
      iModIntro.
      iModIntro.
      rsolve.
    Qed.

    Lemma rblock_verification_condition {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (b : list AST)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) {w} :
      ⊢ RSat LogicalSoundness.RProp (w := w)
          (cblock_verification_condition req b ens)
          (sblock_verification_condition req b ens w).
    Proof.
      unfold cblock_verification_condition, sblock_verification_condition.
      rsolve.
      iApply refine_run.
      iApply rexec_triple_addr.
    Qed.

  End Relational.

  Section Soundness.

    Import iris.base_logic.lib.iprop iris.proofmode.tactics.
    Import RiscvPmpIrisInstanceWithContracts.
    Import ProgramLogic.
    Import CHeapSpec.

    Context {Σ} {GS : sailGS Σ}.

    Fixpoint ptsto_instrs (a : Val ty_word) (instrs : list AST) : iProp Σ :=
      match instrs with
      | cons inst insts => (interp_ptsto_instr a inst ∗ ptsto_instrs (bv.add a bv_instrsize) insts)%I
      | nil => True%I
      end.
    (* Arguments ptsto_instrs {Σ H} a%_Z_scope instrs%_list_scope : simpl never. *)

    Definition semTripleOneInstrStep (PRE : iProp Σ) (instr : AST) (POST : Val ty_word -> iProp Σ) (a : Val ty_word) : iProp Σ :=
      semTTriple [env] (PRE ∗ (∃ v, lptsreg nextpc v) ∗ lptsreg pc a ∗ interp_ptsto_instr a instr)
        (FunDef RiscvPmpProgram.step)
        (fun ret _ => (∃ an, lptsreg nextpc an ∗ lptsreg pc an ∗ POST an) ∗ interp_ptsto_instr a instr)%I.

    Definition semTripleBlock (PRE : Val ty_word -> iProp Σ) (instrs : list AST) (POST : Val ty_word -> Val ty_word -> iProp Σ) : iProp Σ :=
      (∀ a,
         (PRE a ∗ pc ↦ a ∗ (∃ v, nextpc ↦ v) ∗ ptsto_instrs a instrs) -∗
         (∀ an, pc ↦ an ∗ (∃ v, nextpc ↦ v) ∗ ptsto_instrs a instrs ∗ POST a an -∗ TWP_loop) -∗
         TWP_loop)%I.
    #[global] Arguments semTripleBlock PRE%_I instrs POST%_I.

    Lemma sound_exec_instruction {instr} a Φ (h : SCHeap) :
      cexec_instruction instr a Φ h ->
      ⊢ semTripleOneInstrStep (interpret_scheap h) instr
          (fun an => ∃ h' : SCHeap, interpret_scheap h' ∧ ⌜Φ an h'⌝) a.
    Proof.
      cbv [cexec_instruction exec_instruction_prologue bind produce demonic
             produce_chunk lift_purespec CPureSpec.produce_chunk CPureSpec.pure
             CPureSpec.demonic CStoreSpec.evalStoreSpec].
      cbn - [consume].
      iIntros (Hverif) "(Hheap & [%npc Hnpc] & Hpc & Hinstrs)".
      specialize (Hverif npc). apply sound_cexec in Hverif.
      iApply (semTWP_mono with "[-]").
      iApply (sound_tstm (callgraph.mkNode step) TforeignSemBlockVerif lemSemBlockVerif Hverif with "[] [$]").
      - apply callgraph.InvokedByStmList_WellFormed_aux; auto.
      - iIntros (n R) "!>". iApply TcontractsSound. iPureIntro.
        apply (Transitive_Closure.Acc_inv_trans _ _ _ _ R).
        apply accessible_step.
      - iIntros ([v|m] _); last done; iIntros "(%h1 & Hh1 & %Htrip)". clear Hverif.
        destruct Htrip as [an Htrip].
        iPoseProof (consume_sound _ _ Htrip with "Hh1")
          as "[(Hpc & $ & Han) (%h2 & Hh2 & %HΦ)]".
        iExists an. cbn. by iFrame.
    Qed.

    Lemma sound_exec_block_addr {instrs ainstr apc} Φ (h : SCHeap) :
      cexec_block_addr instrs ainstr apc Φ h ->
      interpret_scheap h ∗ lptsreg pc apc ∗ (∃ v, lptsreg nextpc v) ∗ ptsto_instrs ainstr instrs ⊢
      (∀ an, lptsreg pc an ∗ (∃ v, lptsreg nextpc v) ∗ ptsto_instrs ainstr instrs ∗
             (∃ h', interpret_scheap h' ∧ ⌜Φ an h'⌝) -∗ TWP_loop) -∗ TWP_loop.
    Proof.
      revert ainstr apc Φ h.
      induction instrs as [|instr instrs]; cbn; intros ainstr apc Φ h;
        cbv [bind assert_formula lift_purespec CPureSpec.assert_formula
               CPureSpec.assert_pathcondition pure CPureSpec.pure].
      - intros HΦ. iIntros "(Hpre & Hpc & Hnpc & _) Hk".
        iApply "Hk"; iFrame; auto.
      - intros [-> Hverif%sound_exec_instruction].
        unfold semTripleOneInstrStep, semTTriple in Hverif.
        iIntros "(Hh & Hpc & Hnpc & Hinstr & Hinstrs) Hk".
        iApply semTWP_seq.
        iApply semTWP_call_inline.
        iApply (semTWP_mono with "[-Hinstrs Hk] [Hinstrs Hk]").
        iApply Hverif. iFrame. clear Hverif.
        cbn.
        iIntros ([v|m] _); last (iIntros "_"; now rewrite semTWP_fail);
          iIntros "([%an (Hnpc & Hpc & Hk2)] & Hinstr)".
        iDestruct "Hk2" as "(%h' & Hh' & %Hexec)".
        specialize (IHinstrs _ _ _ _ Hexec). clear Hexec.
        iApply (semTWP_call_inline loop).
        iApply (IHinstrs with "[$Hh' $Hpc Hnpc $Hinstrs]").
        { now iExists an. }
        iIntros (an2) "(Hpc & Hnpc & Hinstrs & HPOST)".
        iApply ("Hk" with "[$]").
    Qed.

    Lemma sound_cexec_triple_addr {Γ : LCtx} {pre post instrs} {ι : Valuation Γ} :
      cexec_triple_addr pre instrs post (fun _ _ => True) []%list ->
      ⊢ semTripleBlock (λ a : Val ty_word, asn.interpret pre (ι.[("a"::ty_xlenbits) ↦ a])) instrs
          (λ a na : Val ty_word, asn.interpret post (ι.[("a"::ty_xlenbits) ↦ a].[("an"::ty_xlenbits) ↦ na])).
    Proof.
      cbv [cexec_triple_addr bind demonic_ctx demonic CPureSpec.demonic lift_purespec].
      iIntros (Htrip a) "(Hpre & Hpc & Hnpc & Hinstrs) Hk".
      rewrite CPureSpec.wp_demonic_ctx in Htrip.
      specialize (Htrip ι a). apply produce_sound in Htrip.
      iPoseProof (Htrip with "[$] Hpre") as "(%h2 & [Hh2 %Hexec])". clear Htrip.
      apply sound_exec_block_addr in Hexec.
      iApply (Hexec with "[$]"). clear Hexec.
      iIntros (an2) "(Hpc & Hnpc & Hinstrs & (%h3 & [Hh3 %Hconsume]))".
      apply consume_sound in Hconsume.
      iPoseProof (Hconsume with "Hh3") as "[HPOST Hheap]".
      iApply ("Hk" with "[$]").
    Qed.

    Lemma sound_cblock_verification_condition {Γ pre post instrs} :
      cblock_verification_condition pre instrs post ->
      forall ι : Valuation Γ,
      ⊢ semTripleBlock (fun a => asn.interpret pre (ι.[("a"::ty_xlenbits) ↦ a]))
          instrs
          (fun a na => asn.interpret post (ι.[("a"::ty_xlenbits) ↦ a].[("an"::ty_xlenbits) ↦ na])).
    Proof.
      intros Hverif ι.
      now apply sound_cexec_triple_addr.
    Qed.

    Lemma sound_sblock_verification_condition {Γ pre post instrs} :
      safeE (postprocess (sblock_verification_condition pre instrs post wnil)) ->
      forall ι : Valuation Γ,
      ⊢ semTripleBlock (fun a => asn.interpret pre (ι.[("a"::ty_xlenbits) ↦ a]))
          instrs
          (fun a na => asn.interpret post (ι.[("a"::ty_xlenbits) ↦ a].[("an"::ty_xlenbits) ↦ na])).
    Proof.
      intros Hverif ι.
      apply sound_cexec_triple_addr.
      apply (safeE_safe env.nil), postprocess_sound in Hverif.
      apply LogicalSoundness.psafe_safe in Hverif; [|done].
      revert Hverif.
      apply rexec_triple_addr.
      - easy.
      - easy.
      - easy.
      - constructor.
    Qed.

  End Soundness.

End BlockVerificationDerived.

Section AnnotatedBlockVerification.

  Inductive AnnotInstr :=
  | AnnotAST  (i : AST)
  | AnnotDebugBreak
  | AnnotLemmaInvocation {Δ} (l : 𝑳 Δ) (es : NamedEnv (Exp [ctx]) Δ)
  .

  Section Debug.

    Import option.notations.

    Record DebugBlockver (Σ : LCtx) : Type :=
      MkDebugBlockver
        { debug_blockver_pathcondition          : PathCondition Σ;
          debug_blockver_heap                   : SHeap Σ;
        }.
    #[export] Instance SubstDebugBlockver : Subst DebugBlockver :=
      fun Σ0 d Σ1 ζ01 =>
        match d with
        | MkDebugBlockver pc1 h => MkDebugBlockver (subst pc1 ζ01) (subst h ζ01)
        end.

    #[export] Instance SubstSUDebugBlockver `{SubstUniv Sb} : SubstSU Sb DebugBlockver :=
      fun Σ0 Σ1 d ζ01 =>
        match d with
        | MkDebugBlockver pc1 h => MkDebugBlockver (substSU pc1 ζ01) (substSU h ζ01)
        end.

    #[export] Instance SubstLawsDebugBlockver : SubstLaws DebugBlockver.
    Proof.
      constructor.
      - intros ? []; cbn; now rewrite ?subst_sub_id.
      - intros ? ? ? ? ? []; cbn; now rewrite ?subst_sub_comp.
    Qed.

    #[export] Instance OccursCheckDebugBlockver : OccursCheck DebugBlockver :=
      fun Σ x xIn d =>
        match d with
        | MkDebugBlockver pc1 h =>
            pc' <- occurs_check xIn pc1 ;;
            h'  <- occurs_check xIn h ;;
            Some (MkDebugBlockver pc' h')
        end.

    (* #[export] Instance GenOccursCheckDebugBlockver : GenOccursCheck DebugBlockver := *)
    (*   fun Σ d => *)
    (*     match d with *)
    (*     | MkDebugBlockver pc1 h => *)
    (*         liftBinOp (fun _ pc' h' => MkDebugBlockver pc' h') *)
    (*           (gen_occurs_check pc1) (gen_occurs_check h) *)
    (*     end. *)

  End Debug.

  Import RiscvPmpBlockVerifSpec.

  Section Symbolic.

    Import ModalNotations.
    Import SHeapSpec.
    Import SHeapSpec.notations.

    Fixpoint sexec_annotated_block_addr (b : list AnnotInstr) :
      ⊢ STerm ty_xlenbits -> STerm ty_xlenbits -> SHeapSpec (STerm ty_xlenbits) :=
      fun w0 ainstr apc =>
        match b with
        | nil       => pure apc
        | cons instr b' =>
            match instr with
            | AnnotAST i =>
                ⟨ θ1 ⟩ _    <- assert_formula
                                 (fun _ => amsg.empty)
                                 (formula_relop bop.eq ainstr apc) ;;
                ⟨ θ2 ⟩ apc' <- sexec_instruction i (persist__term apc θ1) ;;
                sexec_annotated_block_addr b'
                  (term_binop bop.bvadd
                     (persist__term ainstr (θ1 ∘ θ2))
                     (term_val ty_word bv_instrsize))
                  apc'
            | AnnotDebugBreak =>
                debug
                  (fun (h0 : SHeap w0) =>
                     amsg.mk
                       {| debug_blockver_pathcondition := wco w0;
                          debug_blockver_heap := h0
                       |})
                  (pure apc)
            | AnnotLemmaInvocation l es =>
                let args := seval_exps [env] es in
                ⟨ θ1 ⟩ _ <- call_lemma (LEnv l) args ;;
                sexec_annotated_block_addr b'
                  (persist__term ainstr θ1)
                  (persist__term apc θ1)
            end
        end.

    Definition sexec_annotated_block_triple_addr {Σ : LCtx}
      (req : Assertion (Σ ▻ ("a"::ty_xlenbits))) (b : list AnnotInstr)
      (ens : Assertion (Σ ▻ ("a"::ty_xlenbits) ▻ ("an"::ty_xlenbits))) :
      ⊢ SHeapSpec Unit :=
      fun _ =>
        ⟨ θ1 ⟩ lenv1 <- demonic_ctx id Σ ;;
        ⟨ θ2 ⟩ a2 <- demonic (Some "a") _ ;;
        let lenv2 := env.snoc (persist (A := Sub Σ) lenv1 θ2) _ a2 in
        ⟨ θ3 ⟩ _ <- produce req lenv2 ;;
        let a3 := persist__term a2 θ3 in
        ⟨ θ4 ⟩ na <- sexec_annotated_block_addr b a3 a3 ;;
        let lenv4 := persist lenv2 (θ3 ∘ θ4) in
        consume ens lenv4.["an"∷ty_xlenbits ↦ na].

    (* This is a VC for triples, for doubles we probably need to talk
     about the continuation of a block. *)
    Definition sannotated_block_verification_condition {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (b : list AnnotInstr)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) : ⊢ 𝕊 :=
      (* SHeapSpec does not perform a leakcheck. We could include one here. *)
      fun w => SHeapSpec.run (sexec_annotated_block_triple_addr req b ens (w := w)).

  End Symbolic.

  Section Shallow.

    Import CHeapSpec CHeapSpec.notations.

    Fixpoint cexec_annotated_block_addr (b : list AnnotInstr) :
      Val ty_xlenbits -> Val ty_xlenbits -> CHeapSpec (Val ty_xlenbits) :=
      fun ainstr apc =>
        match b with
        | nil       => pure apc
        | cons instr b' =>
            match instr with
            | AnnotAST i =>
                _ <- assert_formula (ainstr = apc) ;;
                apc' <- cexec_instruction i apc ;;
                cexec_annotated_block_addr b' (bv.add ainstr bv_instrsize) apc'
            | AnnotDebugBreak => debug (pure apc)
            | AnnotLemmaInvocation l es =>
                let args := evals es [env] in
                _ <- call_lemma (LEnv l) args ;;
                cexec_annotated_block_addr b' ainstr apc
            end
        end.

    Definition cexec_annotated_block_triple_addr {Σ}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (b : list AnnotInstr)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) :
      CHeapSpec unit :=
      lenv <- demonic_ctx Σ ;;
      a  <- demonic _ ;;
      _  <- produce req lenv.["a"∷ty_xlenbits ↦ a]  ;;
      na <- cexec_annotated_block_addr b a a ;;
      consume ens lenv.["a"∷ty_xlenbits ↦ a].["an"∷ty_xlenbits ↦ na].

    Definition cannotated_block_verification_condition {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (b : list AnnotInstr)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) : Prop :=
      (* SHeapSpec does not perform a leakcheck. We could include one here. *)
      CHeapSpec.run (cexec_annotated_block_triple_addr req b ens).

    #[export] Instance mono_cexec_annotated_block_addr {instrs ainstr apc} :
      Monotonic (MHeapSpec eq) (cexec_annotated_block_addr instrs ainstr apc).
    Proof.
      revert ainstr apc.
      induction instrs; cbn; try typeclasses eauto.
      destruct a; typeclasses eauto.
    Qed.

  End Shallow.

  Section Relational.

    Import RiscvPmpIrisInstanceWithContracts.
    Import RiscvPmpIrisInstanceWithContracts.StoreSpec.
    Import logicalrelation logicalrelation.notations.
    Import proofmode.
    Import iris.proofmode.tactics.
    Import RiscvPmpSignature.HeapSpec.
    Import RSolve.

    Lemma rexec_annotated_block_addr (b : list AnnotInstr) {w} :
      ⊢ ℛ⟦RVal ty_xlenbits -> RVal ty_xlenbits -> RHeapSpec (RVal ty_xlenbits)⟧
          (cexec_annotated_block_addr b)
          (sexec_annotated_block_addr b (w := w)).
    Proof.
      iAssert (ℛ⟦□ᵣ (RVal ty_xlenbits -> RVal ty_xlenbits -> RHeapSpec (RVal ty_xlenbits))⟧
                 (cexec_annotated_block_addr b)
                 (fun w' θ => sexec_annotated_block_addr b (w := w'))) as "H".
      { iInduction b as [|instr b] "IHb"; rsolve.
        destruct instr; cbn; rsolve.
        - iApply "IHb"; rsolve.
        - iApply "IHb"; rsolve.
      }
      now iApply (unconditionally_T with "H").
    Qed.

    Lemma rexec_annotated_block_triple_addr {Σ}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (b : list AnnotInstr)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) {w} :
      ⊢ ℛ⟦RHeapSpec RUnit⟧
          (cexec_annotated_block_triple_addr req b ens)
          (sexec_annotated_block_triple_addr req b ens (w := w)).
    Proof.
      unfold cexec_annotated_block_triple_addr, sexec_annotated_block_triple_addr.
      rsolve.
      iApply rexec_annotated_block_addr; rsolve.
      rewrite !forgetting_trans.
      iModIntro.
      iModIntro.
      rsolve.
    Qed.

    Lemma rannotated_block_verification_condition {Σ}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (b : list AnnotInstr)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) {w} :
      ⊢ ℛ⟦LogicalSoundness.RProp⟧
          (cannotated_block_verification_condition req b ens)
          (sannotated_block_verification_condition req b ens w).
    Proof.
      iApply HeapSpec.refine_run.
      iApply rexec_annotated_block_triple_addr.
    Qed.

  End Relational.

  Section Soundness.

    Import iris.base_logic.lib.iprop iris.proofmode.tactics.
    Import RiscvPmpIrisInstanceWithContracts.
    Import ProgramLogic.
    Import CHeapSpec.

    Context {Σ} {GS : sailGS Σ}.

    Definition extract_AST (i : AnnotInstr) : option AST :=
      match i with
      | AnnotAST a => Some a
      | _ => None
      end.

    Lemma sound_exec_annotated_block_addr {instrs ainstr apc} (h : SCHeap) (POST : Val ty_xlenbits -> iProp Σ) :
      LemmaSem ->
      cexec_annotated_block_addr instrs ainstr apc (fun res h' => interpret_scheap h' ⊢ POST res) h ->
      ⊢ ((interpret_scheap h ∗ lptsreg pc apc ∗ (∃ v, lptsreg nextpc v) ∗ ptsto_instrs ainstr (omap extract_AST instrs)) -∗
         (∀ an, lptsreg pc an ∗ (∃ v, lptsreg nextpc v) ∗ ptsto_instrs ainstr (omap extract_AST instrs) ∗ POST an -∗ TWP_loop) -∗
         TWP_loop)%I.
    Proof.
      intros lemSem.
      revert ainstr apc h POST.
      induction instrs as [|instr instrs]; cbn; intros ainstr apc h POST.
      - iIntros (->) "(Hpre & Hpc & Hnpc & _) Hk".
        iApply "Hk"; iFrame.
      - cbv [bind assert_formula lift_purespec CPureSpec.assert_formula
               CPureSpec.assert_pathcondition].
        destruct instr as [instr| |Δ lem es].
        + intros [-> Hverif]. cbn [extract_AST ptsto_instrs].
          iIntros "(Hh & Hpc & Hnpc & Hinstr & Hinstrs) Hk".
          iApply semTWP_seq.
          iApply semTWP_call_inline.
          iApply (semTWP_mono with "[Hh Hnpc Hpc Hinstr]").
          { iApply (sound_exec_instruction Hverif). iFrame. }
          clear Hverif.
          iIntros ([v|m] _); last (iIntros "_"; now rewrite semTWP_fail);
            iIntros "([%an (Hnpc & Hpc & (%h2 & Hh2 & %Hverif))] & Hinstr)".
          iApply (semTWP_call_inline loop).
          specialize (IHinstrs _ _ _ _ Hverif).
          iApply (IHinstrs with "[$Hh2 $Hpc Hnpc $Hinstrs]").
          by iExists _.
          iIntros (an2) "(Hpc & Hnpc & Hinstrs & HPOST)".
          iApply ("Hk" with "[$]").
        + cbv [debug pure lift_purespec CPureSpec.pure].
          iIntros (->) "(Hh & Hpc & Hnpc & Hinstrs) Hk".
          now iApply ("Hk" with "[$Hpc $Hnpc $Hinstrs Hh]").
        + iIntros (Hlemcall) "(Hh & Hpc & Hnpc & Hinstrs) Hk".
          pose proof (Hlem := lemSem _ lem).
          apply call_lemma_sound in Hlemcall. destruct Hlemcall. cbn in *.
          iPoseProof (H with "Hh") as "(%ι & %Heq & Hreq & Hk2)". clear H.
          iPoseProof (Hlem with "Hreq") as "Hens".
          iPoseProof ("Hk2" with "Hens") as "(%h' & Hh' & %Hk2)".
          apply IHinstrs in Hk2.
          iApply (Hk2 with "[$Hh' $Hpc $Hnpc $Hinstrs] Hk").
    Qed.

    Definition semTripleAnnotatedBlock (PRE : Val ty_word -> iProp Σ)
      (instrs : list AnnotInstr) (POST : Val ty_word -> Val ty_word -> iProp Σ) : iProp Σ :=
      (∀ a,
         (PRE a ∗ pc ↦ a ∗ (∃ v, nextpc ↦ v) ∗ ptsto_instrs a (omap extract_AST instrs)) -∗
         (∀ an, pc ↦ an ∗ (∃ v, nextpc ↦ v) ∗ ptsto_instrs a (omap extract_AST instrs) ∗ POST a an -∗ TWP_loop) -∗
         TWP_loop)%I.
    Global Arguments semTripleAnnotatedBlock PRE%_I instrs POST%_I.

    Lemma sound_cexec_annotated_block_triple_addr {Γ pre post instrs} :
      LemmaSem ->
      (cexec_annotated_block_triple_addr (Σ := Γ) pre instrs post (λ _ _ , True) []%list) ->
      forall ι : Valuation Γ,
      ⊢ semTripleAnnotatedBlock (λ a : Val ty_word, asn.interpret pre (ι.[("a"::ty_xlenbits) ↦ a])) instrs
          (λ a na : Val ty_word, asn.interpret post (ι.[("a"::ty_xlenbits) ↦ a].[("an"::ty_xlenbits) ↦ na])).
    Proof.
      intros lemSem Hexec ι.
      iIntros (a) "(Hpre & Hpc & Hnpc & Hinstrs) Hk".
      hnf in Hexec.
      rewrite CPureSpec.wp_demonic_ctx in Hexec.
      specialize (Hexec ι a).
      unfold bind in Hexec.
      iPoseProof (produce_sound _ _ Hexec with "[//] [$Hpre]") as "(%h2 & Hh2 & %Hexec')".
      clear Hexec.
      iApply (sound_exec_annotated_block_addr (apc := a) h2 with "[$Hh2 $Hpc $Hnpc $Hinstrs]"); auto.
      revert Hexec'.
      apply mono_cexec_annotated_block_addr.
      intros ? ? <- h3 Hcons.
      iIntros "Hh3".
      iPoseProof (consume_sound _ _ Hcons with "Hh3") as "[Hcons _]".
      iFrame.
    Qed.

    Lemma sound_sannotated_block_verification_condition {Γ pre post instrs} :
      LemmaSem ->
      safeE (postprocess (sannotated_block_verification_condition (Σ := Γ)
                            pre instrs post wnil)) ->
      forall ι : Valuation Γ,
      ⊢ semTripleAnnotatedBlock (fun a => asn.interpret pre (ι.[("a"::ty_xlenbits) ↦ a]))
          instrs (fun a na => asn.interpret post (ι.[("a"::ty_xlenbits) ↦ a].[("an"::ty_xlenbits) ↦ na])).
    Proof.
      unfold sannotated_block_verification_condition, SHeapSpec.run.
      intros lemSem Hverif ι.
      apply sound_cexec_annotated_block_triple_addr; auto.
      apply (safeE_safe env.nil), postprocess_sound in Hverif.
      apply LogicalSoundness.psafe_safe in Hverif; [|done].
      revert Hverif.
      apply rexec_annotated_block_triple_addr.
      - easy.
      - easy.
      - easy.
      - constructor.
    Qed.

  End Soundness.

End AnnotatedBlockVerification.
