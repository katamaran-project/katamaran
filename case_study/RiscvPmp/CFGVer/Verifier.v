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

(* ======================================================================== *)
(* CFGVer/Verifier.v                                                        *)
(*                                                                           *)
(* Role: defines the symbolic CFG executor (sexec_cfg_addr / cexec_cfg_addr) *)
(* and proves its soundness up to semTripleCFG.                             *)
(*                                                                           *)
(* Key differences from BlockVer/Verifier.v:                                *)
(*   - Address-indexed lookup: each step fetches instr at PC/bytes_per_instr *)
(*     instead of advancing linearly.  Supports backward and forward jumps.  *)
(*   - exitCond parameter: execution halts when exitCond (current PC) = true *)
(*     OR when fuel runs out.  The angelic_binary at each step models the    *)
(*     nondeterministic choice between exiting and executing one more instr.  *)
(*   - fuel bound: the executor always terminates (no coinduction needed).   *)
(*                                                                           *)
(* Import policy (IMPORTANT):                                                *)
(*   Examples.v does `From Katamaran Require RiscvPmp.CFGVer.Verifier`       *)
(*   (without Import!) to avoid notation/name clashes with BlockVer.        *)
(*   All CFGVer lemmas are then used with the qualified prefix               *)
(*   `Katamaran.RiscvPmp.CFGVer.Verifier.foo`.                              *)
(* ======================================================================== *)

From Coq Require Import
     Classes.Morphisms_Prop
     ZArith.ZArith
     Lists.List
     micromega.Lia
     Strings.String.
From Equations Require Import
     Equations.
From Katamaran Require Import
  (* Iris.Instance *) Iris.BinaryInstance
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
     RiscvPmp.IrisModelBinary
     RiscvPmp.IrisInstance
     RiscvPmp.IrisInstanceBinary
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

Import RiscvPmpIrisBase2 RiscvPmpIrisInstance2.

(* ======================================================================== *)
(* BlockVerificationDerived                                                  *)
(*                                                                           *)
(* Despite the name (inherited from BlockVer), this section now hosts the   *)
(* CFG verifier.  It is structured in four subsections:                     *)
(*   Symbolic  — sexec_cfg_addr and related definitions                     *)
(*   Shallow   — cexec_cfg_addr (concrete, propositional)                   *)
(*   Relational — rexec_cfg_addr (the key soundness bridge via rsolve)      *)
(*   Soundness — ptsto_instrs, semTripleCFG, sound_sblock_verification_condition *)
(* ======================================================================== *)
Section BlockVerificationDerived.

  Import RiscvPmpBlockVerifExecutor.
  Import RiscvPmpBlockVerifShalExecutor.

  (* safeE P: the symbolic proposition P is "safe" — i.e., the verification
     condition holds after erasure of all metadata.  This is the notion of
     validity used in CFGVerifierContract.ValidCFGVerifierContract.
     safeE_safe converts to the more basic SymProp.safe form. *)
  Definition safeE {Σ} : 𝕊 Σ -> Prop :=
    fun P => VerificationConditionWithErasure (Erasure.erase_symprop P).

  Definition safeE_safe (p : 𝕊 wnil) (ι : Valuation wnil) : safeE p -> SymProp.safe p [].
  Proof.
    unfold safeE.
    destruct 1 as [H].
    now apply Erasure.erase_safe'.
  Qed.

  (* instrAligned v: true iff v is a multiple of bytes_per_instr (= 4).
     Used in sexec/cexec_cfg_addr to reject misaligned PCs.
     `simpl never` prevents Rocq from unfolding it during cbn/simpl,
     keeping proof goals readable.  Use Nat.eqb_eq to convert to Prop. *)
  Definition instrAligned (v : bv xlenbits) : bool :=
    (N.to_nat (bv.bin v) mod bytes_per_instr =? 0)%nat.
  #[global] Arguments instrAligned : simpl never.

  Section Symbolic.

    Import ModalNotations.
    Import SStoreSpec (evalStoreSpec).
    Import SHeapSpec SHeapSpec.notations.
    Import asn.notations.

    (* exec_instruction_prologue i: the Hoare precondition for executing
       instruction i at address a.  Asserts:
         pc ↦ a, ptstoinstr a i (instruction ownership), ∃ an, nextpc ↦ an,
         secLeak a (PC is public → same instruction in both worlds).
       After execution, exec_instruction_epilogue i holds:
         pc ↦ an, ptstoinstr a i (unchanged), nextpc ↦ an, secLeak a, secLeak an
       The two assertions together form the frame for one `step` invocation. *)
    Definition exec_instruction_prologue (i : AST) :
      Assertion ([ctx] ▻ ("a":: ty_xlenbits)) :=
      pc     ↦ term_var "a" ∗
      asn.chunk (chunk_user ptstoinstr [term_var "a"; term_val ty_ast i]) ∗
      asn.exist "an" ty_xlenbits (nextpc ↦ term_var "an") ∗
      asn.formula (formula_secLeak (term_var "a"))
    .

    Definition exec_instruction_epilogue (i : AST) :
      Assertion ([ctx] ▻ ("a":: ty_xlenbits) ▻ ("an":: ty_xlenbits)) :=
      pc     ↦ term_var "an" ∗
      asn.chunk (chunk_user ptstoinstr [term_var "a"; term_val ty_ast i]) ∗
      nextpc ↦ term_var "an" ∗
      asn.formula (formula_secLeak (term_var "a")) ∗
      asn.formula (formula_secLeak (term_var "an"))
    .

    (* inputs:
     * - i: instruction to be executed
     * - a: term representing current pc value.
     * output: term representing nextpc value after executing the instruction.
     *)
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

    (* inputs:
     * - b : list of instructions (indexed by address / bytes_per_instr)
     * - fuel: maximum number of steps to execute
     * - apc: term representing the current pc value
     * output: term representing the pc value after executing up to fuel steps.
     *
     * apc must be a concrete bitvector (term_val) for execution to proceed;
     * if it is symbolic, or if the index apc/bytes_per_instr falls outside b,
     * execution halts and returns apc.  Backward and forward jumps are supported
     * because the instruction is looked up by address each step rather than
     * advancing linearly through the list.
     *)
    (* sexec_cfg_addr b exitCond fuel: the symbolic CFG executor.
       Inputs:
         b : list AST   — the program (indexed by address: instr at addr v
                          is b[v / bytes_per_instr])
         exitCond : bv xlenbits → bool   — halting criterion
         fuel : nat     — step bound (error when 0)
         apc : STerm ty_xlenbits   — current PC (must be a concrete term_val)
       Behaviour at each step:
         1. If fuel = 0 → error (stuck)
         2. If apc is symbolic (not term_val) → error
         3. If exitCond v = true → angelic_binary offers exit
         4. If instr is aligned and in bounds → execute one step, recurse
         5. Otherwise → error
       angelic_binary models the (existential) choice between exiting and
       continuing.  A concrete path through angelic_binary corresponds to
       one concrete execution trace.
       NOTE: execution can revisit the same address (backward jumps), so
       this is NOT a linear scan. *)
    Fixpoint sexec_cfg_addr (b : list AST) (exitCond : bv xlenbits -> bool) (fuel : nat) :
      ⊢ STerm ty_xlenbits -> SHeapSpec (STerm ty_xlenbits) :=
      fun _ apc =>
        match fuel with
        | O    => error (fun _ => amsg.empty)
        | S n' =>
            match term_get_val apc with
            | None   => error (fun _ => amsg.empty)
            | Some v =>
                angelic_binary
                  (if exitCond v then pure apc else error (fun _ => amsg.empty))
                  (if instrAligned v then
                    match List.nth_error b (N.to_nat (bv.bin v) / bytes_per_instr)%nat with
                    | None   => error (fun _ => amsg.empty)
                    | Some i =>
                        ⟨ θ1 ⟩ apc' <- sexec_instruction i apc ;;
                        sexec_cfg_addr b exitCond n' apc'
                    end
                  else
                    error (fun _ => amsg.empty))
            end
        end.

    (* Apply symbolic execution to verify a Hoare triple for a block of instructions.
     * The precondition can mention the address a where the block is loaded.
     * The postcondition can additionally mention the address an where the pc points after execution.
     *)
    Definition sexec_triple_addr {Σ : LCtx}
      (req : Assertion (Σ ▻ ("a"::ty_xlenbits))) (b : list AST) (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ ("a"::ty_xlenbits) ▻ ("an"::ty_xlenbits))) :
      ⊢ SHeapSpec Unit :=
      fun w =>
        ⟨ θ0 ⟩ δ <- demonic_ctx id Σ ;;
        ⟨ θ1 ⟩ a <- demonic (Some "a") _ ;;
        let δ1 := env.snoc (persist ( A:= Sub Σ) δ θ1) _ a in
        ⟨ θ2 ⟩ _ <- produce req δ1 ;;
        let a2 := persist__term a θ2 in
        ⟨ θ3 ⟩ na <- sexec_cfg_addr b exitCond fuel a2 ;;
        let δ3 := persist δ1 (θ2 ∘ θ3) in
        consume ens δ3.["an"∷ty_xlenbits ↦ na].

    (* sblock_verification_condition req b exitCond fuel ens:
       The final symbolic VC.  It runs sexec_triple_addr inside SHeapSpec.run,
       which discards the final heap (no leakcheck).  The result is a 𝕊 wnil
       proposition that can be checked by `safeE (postprocess ...)`.
       Call pattern (from Examples.v):
         sblock_verification_condition (Σ := [ctx]) req b ec fl ens wnil
       The explicit `Σ := [ctx]` is required because Rocq cannot infer it
       from the other arguments alone. *)
    Definition sblock_verification_condition {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (b : list AST) (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) : ⊢ 𝕊 :=
      fun w =>
        (* SHeapSpec does not perform a leakcheck. We could include one here. *)
        SHeapSpec.run (sexec_triple_addr req b exitCond fuel ens (w := w)).

  End Symbolic.

  Section Shallow.

    Import CStoreSpec (evalStoreSpec).
    Import CHeapSpec CHeapSpec.notations.

    Definition cexec_instruction (i : AST) :
      RelVal ty_xlenbits -> CHeapSpec (RelVal ty_xlenbits) :=
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

    Fixpoint cexec_cfg_addr (b : list AST) (exitCond : bv xlenbits -> bool) (fuel : nat) :
      RelVal ty_xlenbits -> CHeapSpec (RelVal ty_xlenbits) :=
      fun apc =>
        match fuel with
        | O    => error
        | S n' =>
            match ty.RVToOption apc with
            | None   => error
            | Some v =>
                angelic_binary
                  (if exitCond v then pure apc else error)
                  (if instrAligned v then
                    match List.nth_error b (N.to_nat (bv.bin v) / bytes_per_instr)%nat with
                    | None   => error
                    | Some i =>
                        apc' <- cexec_instruction i apc ;;
                        cexec_cfg_addr b exitCond n' apc'
                    end
                  else
                    error)
            end
        end.

    Definition cexec_triple_addr {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (b : list AST) (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) :
      CHeapSpec unit :=
      lenv <- demonic_ctx Σ ;;
      a    <- demonic _ ;;
      _    <- produce req lenv.["a"∷ty_xlenbits ↦ a]  ;;
      na   <- cexec_cfg_addr b exitCond fuel a ;;
      consume ens lenv.["a"∷ty_xlenbits ↦ a].["an"∷ty_xlenbits ↦ na].

    Definition cblock_verification_condition {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (b : list AST) (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) : Prop :=
      (* CHeapSpec.run does not perform a leakcheck. We could include one here. *)
      CHeapSpec.run (cexec_triple_addr req b exitCond fuel ens).

    Import (hints) CStoreSpec.

    #[export] Instance mono_cexec_instruction {i a} :
      Monotonic (MHeapSpec eq) (cexec_instruction i a).
    Proof. typeclasses eauto. Qed.

    #[export] Instance mono_cexec_cfg_addr {b exitCond fuel apc} :
      Monotonic (MHeapSpec eq) (cexec_cfg_addr b exitCond fuel apc).
    Proof.
      revert apc. induction fuel; cbn; intro apc.
      - typeclasses eauto.
      - destruct apc as [v | vl vr]; cbn.
        + destruct (exitCond v); destruct (instrAligned v);
            try destruct (List.nth_error b _); typeclasses eauto.
        + typeclasses eauto.
    Qed.

  End Shallow.

  (* ====================================================================== *)
  (* Relational layer                                                        *)
  (*                                                                         *)
  (* The relational layer connects the concrete (C) and symbolic (S)        *)
  (* executors via ℛ⟦R⟧, the logical relation used by `rsolve`.             *)
  (*                                                                         *)
  (* rexec_cfg_addr: the key lemma.  Proved by iInduction on fuel.           *)
  (*   At each step, term_get_val_spec is used to case-split on whether apc  *)
  (*   is a concrete bitvector (term_val v) or symbolic.  In the concrete   *)
  (*   case, repₚ_antisym_left unifies the relational apc with term_val.    *)
  (*   Then angelic_binary and nth_error cases are handled by rsolve.        *)
  (*                                                                         *)
  (* RefineCompat instances export the relational lemmas for use by rsolve:  *)
  (*   refine_compat_block_verification_condition — key instance that lets   *)
  (*   rsolve close goals of the form                                        *)
  (*   RSat RProp (cblock_vc ...) (sblock_vc ...)                           *)
  (* ====================================================================== *)
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

    (* rexec_cfg_addr: ℛ⟦RVal → RHeapSpec (RVal)⟧ cexec_cfg_addr sexec_cfg_addr
       Proof: iInduction on fuel.  Bullet nesting convention (from CLAUDE.md):
         - top-level bullets from iInduction use -
         + for angelic_binary sub-goals (two branches)
         -- for refine_bind sub-goals
         * for nth_error cases (Some / None)
       The key non-trivial step is using forgetting_unconditionally_drastic
       to project the boxed IH to the current world. *)
    Lemma rexec_cfg_addr (b : list AST) (exitCond : bv xlenbits -> bool) (fuel : nat) {w} :
      ⊢ ℛ⟦RVal ty_xlenbits -> RHeapSpec (RVal ty_xlenbits)⟧
          (cexec_cfg_addr b exitCond fuel)
          (sexec_cfg_addr b exitCond fuel (w := w)).
    Proof.
      iAssert (ℛ⟦□ᵣ (RVal ty_xlenbits -> RHeapSpec (RVal ty_xlenbits))⟧
                 (cexec_cfg_addr b exitCond fuel)
                 (fun w' θ => sexec_cfg_addr b exitCond fuel (w := w'))) as "H".
      {
        iInduction fuel as [|n'] "IHfuel"; cbn.
        - rsolve.
        - rsolve.
          destruct (term_get_val_spec ta) as [v ->|]; cbn.
          2: rsolve.
          iRename select (ℛ⟦RVal ty_xlenbits⟧ a (term_val ty_xlenbits v)) into "Ha".
          iPoseProof (refine_term_val (v := v)) as "Hv".
          iDestruct (repₚ_antisym_left with "Ha Hv") as "->"; cbn.
          rsolve.
          + destruct (exitCond v); rsolve.
          + destruct (instrAligned v).
            2: rsolve.
            destruct (List.nth_error b _) as [i|].
            * iApply (refine_bind (RA := RVal ty_xlenbits)).
              -- now iApply (rexec_instruction i with "Ha").
              -- rsolve.
                 iPoseProof (forgetting_unconditionally_drastic with "IHfuel") as "IH".
                 iApply ("IH" with "[$]").
            * rsolve.
      }
      iApply (unconditionally_T with "H").
    Qed.

    #[export] Instance refine_compat_exec_cfg_addr (b : list AST) (exitCond : bv xlenbits -> bool) (fuel : nat) {w} :
      RefineCompat (RVal ty_xlenbits -> RHeapSpec (RVal ty_xlenbits))
        (cexec_cfg_addr b exitCond fuel) w (sexec_cfg_addr b exitCond fuel (w := w)) _ :=
      MkRefineCompat (rexec_cfg_addr b exitCond fuel).

    Import PureSpec.

    Lemma rexec_triple_addr {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (b : list AST) (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) {w} :
      ⊢ ℛ⟦RHeapSpec RUnit⟧
          (cexec_triple_addr req b exitCond fuel ens)
          (sexec_triple_addr req b exitCond fuel ens (w := w)).
    Proof.
      unfold cexec_triple_addr, sexec_triple_addr.
      rsolve.
      all: repeat (rewrite ?forgetting_trans; try iModIntro; rsolve).
    Qed.

    #[export] Instance refine_compat_exec_triple_addr {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (b : list AST) (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) {w} :
      RefineCompat (RHeapSpec RUnit)
        (cexec_triple_addr req b exitCond fuel ens) w (sexec_triple_addr req b exitCond fuel ens (w := w)) _ :=
      MkRefineCompat (rexec_triple_addr req b exitCond fuel ens).

    Lemma rblock_verification_condition {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (b : list AST) (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) {w} :
      ⊢ RSat LogicalSoundness.RProp (w := w)
          (cblock_verification_condition req b exitCond fuel ens)
          (sblock_verification_condition req b exitCond fuel ens w).
    Proof.
      unfold cblock_verification_condition, sblock_verification_condition.
      rsolve.
    Qed.

    #[export] Instance refine_compat_block_verification_condition {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (b : list AST) (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) {w} :
      RefineCompat (LogicalSoundness.RProp)
        (cblock_verification_condition req b exitCond fuel ens) w (sblock_verification_condition req b exitCond fuel ens w) _ :=
      MkRefineCompat (rblock_verification_condition req b exitCond fuel ens).

  End Relational.

  (* ====================================================================== *)
  (* Soundness: symbolic VC → semTripleCFG                                  *)
  (*                                                                         *)
  (* ptsto_instrs a instrs: Iris predicate asserting instruction ownership   *)
  (*   at consecutive addresses starting at a.  The inductive structure      *)
  (*   mirrors the list of instructions; the address advances by bv_instrsize *)
  (*   (= 4 bytes) at each step.                                             *)
  (*   NOTE: unlike BlockVer, the base address is SyncVal bv.zero (not       *)
  (*   parameterized), so all programs are assumed loaded at address 0.      *)
  (*                                                                         *)
  (* semTripleCFG PRE b exitCond fuel POST:                                  *)
  (*   Iris semantic triple for a CFG program.  It states:                   *)
  (*     ∀ a, PRE a ∗ pc ↦ a ∗ ∃ v, nextpc ↦ v ∗ ptsto_instrs 0 b →       *)
  (*       (∀ an, ⌜exitCond an⌝ ∗ pc ↦ an ∗ ... ∗ POST a an → WP2_loop) → *)
  (*       WP2_loop                                                          *)
  (*   WP2_loop here is BlockVer.Verifier.WP2_loop (the plain infinite loop),*)
  (*   NOT myWP2_loop from Examples.v.  The bridge from semTripleCFG to      *)
  (*   myWP2_loop is done by sound_sblock_verification_condition_myWP2 in   *)
  (*   Examples.v.                                                           *)
  (*                                                                         *)
  (* sound_sblock_verification_condition:                                    *)
  (*   safeE (postprocess VC) → semTripleCFG                                *)
  (*   This is the main output of this section.  Examples.v uses the        *)
  (*   _myWP2 variant instead, which produces myWP2_loop directly.          *)
  (* ====================================================================== *)
  Section Soundness.

    Import iris.base_logic.lib.iprop iris.proofmode.tactics.
    Import RiscvPmpIrisInstanceWithContracts.
    Import ProgramLogic.
    Import CHeapSpec.

    Context {Σ} {GS : sailGS2 Σ}.

    Fixpoint ptsto_instrs (a : RelVal ty_word) (instrs : list AST) : iProp Σ :=
      match instrs with
      | cons inst insts => (interp_ptsto_instr a (SyncVal inst) ∗
                              ptsto_instrs (ty.liftUnOp (σ1 := ty.bvec _) (σ2 := ty.bvec _) (fun a => bv.add a bv_instrsize) a) insts)%I
      | nil => True%I
      end.
    (* Arguments ptsto_instrs {Σ H} a%_Z_scope instrs%_list_scope : simpl never. *)

    Definition semTripleOneInstrStep (PRE : iProp Σ) (instr : AST) (POST : RelVal ty_word -> iProp Σ) (a : RelVal ty_word) : iProp Σ :=
      semTriple [env] (PRE ∗ (∃ v, lptsreg nextpc v) ∗ lptsreg pc a ∗ interp_ptsto_instr a (SyncVal instr) ∗ ⌜ secLeak a ⌝)
        (FunDef RiscvPmpProgram.step)
        (fun ret _ => (∃ an, lptsreg nextpc an ∗ lptsreg pc an ∗ POST an) ∗ interp_ptsto_instr a (SyncVal instr)  ∗ ⌜ secLeak a ⌝)%I.

    Definition semTripleCFG (PRE : RelVal ty_word -> iProp Σ) (instrs : list AST) (exitCond : bv xlenbits -> bool) (fuel : nat) (POST : RelVal ty_word -> RelVal ty_word -> iProp Σ) : iProp Σ :=
      (∀ a,
         (PRE a ∗ pc ↦ᵣ a ∗ (∃ v, nextpc ↦ᵣ v) ∗ ptsto_instrs (SyncVal bv.zero) instrs) -∗
         (∀ an, ⌜match an with SyncVal v => exitCond v = true | NonSyncVal _ _ => True end⌝ ∗
                pc ↦ᵣ an ∗ (∃ v, nextpc ↦ᵣ v) ∗ ptsto_instrs (SyncVal bv.zero) instrs ∗ POST a an -∗ WP2_loop) -∗
         WP2_loop)%I.
    #[global] Arguments semTripleCFG PRE%_I instrs exitCond fuel POST%_I.

    Lemma sound_stm_aux {τ} {PRE} {s : Stm [ctx] τ} {POST} :
      ⦃ PRE ⦄ s; [env] ⦃ POST ⦄ → ⊢ semTriple [env] PRE s POST.
    Proof.
      iIntros (Htrip) "PRE".
      iApply sound_stm; eauto using foreignSemBlockVerif, lemSemBlockVerif.
      iApply contractsSound.
    Qed.

    Lemma sound_exec_instruction {instr} a Φ (h : SCHeap) :
      cexec_instruction instr a Φ h ->
      ⊢ semTripleOneInstrStep (interpret_scheap h) instr
          (fun an => ∃ h' : SCHeap, interpret_scheap h' ∧ ⌜Φ an h'⌝ ∧ ⌜ secLeak an ⌝) a.
    Proof.
      cbv [cexec_instruction exec_instruction_prologue bind produce demonic
             produce_chunk lift_purespec CPureSpec.produce_chunk CPureSpec.pure
             CPureSpec.demonic CStoreSpec.evalStoreSpec].
      cbn - [consume].
      iIntros (Hverif) "(Hheap & [%npc Hnpc] & Hpc & Hinstrs & %HsL)".
      specialize (Hverif npc). apply sound_cexec in Hverif.
      iApply (semWP2_mono with "[-]").
      iApply (sound_stm foreignSemBlockVerif lemSemBlockVerif Hverif with "[] [$]").
      iApply contractsSound.
      iIntros ([v1|m1] δ1 [v2|m2] δ2); last done.
      2-3: iIntros "(%δ' & H & HF)"; auto.
      iIntros "(%δ' & eqδ' & %rv & eqrv & (%h1 & Hh1 & %Htrip))". clear Hverif.
      iFrame "eqδ' eqrv".
      destruct Htrip as [an Htrip].
      iPoseProof (consume_sound _ _ Htrip with "Hh1")
        as "[(Hpc & $ & (Han & (HsLa & _) & (HsLan & _))) (%h2 & Hh2 & %HΦ)]".
      iSplitL. iExists an. cbn. by iFrame.
      auto.
      auto.
    Qed.

    Add Ring BitVectorRing : (bv.ring_theory xlenbits).

    (* ptsto_instrs_nth: extract instruction k from ptsto_instrs with a
       framing wand.  Used in sound_exec_cfg_addr to split out the
       instruction at the current PC address, execute it, then restore
       the full ptsto_instrs via the wand.
       Split out instruction k from ptsto_instrs (SyncVal start) b, with a framing wand. *)
    Lemma ptsto_instrs_nth (b : list AST) (k : nat) (i : AST) (start : bv xlenbits) :
      nth_error b k = Some i →
      ptsto_instrs (SyncVal start) b ⊢
        interp_ptsto_instr (SyncVal (bv.add start (bv.of_N (N.of_nat (k * bytes_per_instr))))) (SyncVal i) ∗
        (interp_ptsto_instr (SyncVal (bv.add start (bv.of_N (N.of_nat (k * bytes_per_instr))))) (SyncVal i) -∗
         ptsto_instrs (SyncVal start) b).
    Proof.
      revert k start.
      induction b as [|b0 bs IH]; intros k start Hnth.
      - destruct k; discriminate.
      - destruct k as [|k'].
        + injection Hnth as <-.
          cbn [ptsto_instrs].
          iIntros "[Hi Hrest]".
          replace (bv.add start (bv.of_N (N.of_nat (0 * bytes_per_instr)))) with start.
          2: { cbn. rewrite bv.add_zero_r. reflexivity. }
          iFrame. iIntros "Hi". iFrame.
        + cbn [nth_error] in Hnth.
          cbn [ptsto_instrs].
          change (ty.liftUnOp (σ1 := ty.bvec _) (σ2 := ty.bvec _) (fun a => bv.add a bv_instrsize) (SyncVal start))
            with (SyncVal (bv.add start bv_instrsize)).
          iIntros "[Hi0 Hrest]".
          iPoseProof (IH k' (bv.add start bv_instrsize) Hnth with "Hrest") as "[Hk Hframe]".
          have Haddr : bv.add (bv.add start bv_instrsize) (bv.of_N (N.of_nat (k' * bytes_per_instr))) =
                       bv.add start (bv.of_N (N.of_nat (S k' * bytes_per_instr))).
          { rewrite <- bv.add_assoc. f_equal. unfold bv_instrsize, bv.of_nat.
            rewrite bv.of_N_add. f_equal. rewrite <- Nat2N.inj_add. f_equal. }
          rewrite <- Haddr.
          iFrame "Hk". iIntros "Hk". rewrite Haddr.
          iPoseProof ("Hframe" with "Hk") as "Hrest'". iFrame.
    Qed.

    (* sound_exec_cfg_addr: the soundness theorem for cexec_cfg_addr.
       Given that cexec_cfg_addr succeeds (producing Φ an h), the Iris
       precondition (heap + pc + nextpc + instructions) entails semTripleCFG.
       Proof: induction on fuel.
         - Exit branch: exitCond holds → apply the continuation Hk.
         - Execute branch: extract instruction via ptsto_instrs_nth, run
           sound_exec_instruction, then recurse via IH.
       This lemma uses WP2_loop (not myWP2_loop); the myWP2_loop version
       is sound_exec_cfg_addr_myWP2 in Examples.v. *)
    Lemma sound_exec_cfg_addr {b exitCond fuel} (apc : RelVal ty_xlenbits) Φ (h : SCHeap) :
      cexec_cfg_addr b exitCond fuel apc Φ h →
      interpret_scheap h ∗ lptsreg pc apc ∗ (∃ v, lptsreg nextpc v) ∗ ptsto_instrs (SyncVal bv.zero) b ⊢
      (∀ an, ⌜match an with SyncVal v => exitCond v = true | NonSyncVal _ _ => True end⌝ ∗
             lptsreg pc an ∗ (∃ v, lptsreg nextpc v) ∗ ptsto_instrs (SyncVal bv.zero) b ∗
             (∃ h', interpret_scheap h' ∧ ⌜Φ an h'⌝) -∗ WP2_loop) -∗ WP2_loop.
    Proof.
      revert apc h.
      induction fuel as [|n' IH]; intros apc h Hexec.
      - cbn [cexec_cfg_addr CHeapSpec.error] in Hexec. contradiction.
      - destruct apc as [v|v1 v2].
        + cbn [cexec_cfg_addr ty.RVToOption CHeapSpec.angelic_binary] in Hexec.
          destruct Hexec as [Hexit | Hexec].
          * (* Exit condition branch *)
            destruct (exitCond v) eqn:Hexit_eq.
            -- cbn [CHeapSpec.pure] in Hexit.
               iIntros "(Hh & Hpc & Hnpc & Hinstrs) Hk".
               iApply ("Hk" $! (SyncVal v)).
               iSplit. { iPureIntro. exact Hexit_eq. }
               iFrame. iPureIntro. exact Hexit.
            -- cbn [CHeapSpec.error] in Hexit. contradiction.
          * (* Execute branch *)
            destruct (instrAligned v) eqn:Hmod.
            -- set (k := N.to_nat (bv.bin v) / bytes_per_instr) in *.
               destruct (List.nth_error b k) as [i|] eqn:Hnth.
               ++ unfold bind, CHeapSpec.bind in Hexec.
                  iIntros "(Hh & Hpc & Hnpc & Hinstrs) Hk".
                  unfold instrAligned in Hmod. apply Nat.eqb_eq in Hmod.
                  have Haddr : bv.add bv.zero (bv.of_N (N.of_nat (k * bytes_per_instr))) = v.
                  { have Hdiv : k * bytes_per_instr = N.to_nat (bv.bin v).
                    { have Hdm := Nat.div_mod (N.to_nat (bv.bin v)) bytes_per_instr.
                      unfold k, bytes_per_instr in *. lia. }
                    rewrite Hdiv. rewrite N2Nat.id. rewrite bv.of_N_bin.
                    rewrite bv.add_zero_l. reflexivity. }
                  iPoseProof (ptsto_instrs_nth b k bv.zero Hnth with "Hinstrs") as "[Hinstr Hframe]".
                  iEval (rewrite Haddr) in "Hinstr". iEval (rewrite Haddr) in "Hframe".
                  iApply semWP2_seq. iApply semWP2_call_inline.
                  iApply (semWP2_mono with "[Hh Hnpc Hpc Hinstr]").
                  { iApply (sound_exec_instruction Hexec). iFrame "Hh Hnpc Hpc Hinstr". }
                  iIntros ([v1|m1] δ1 [v2|m2] δ2); cbn; last (iIntros "_"; now rewrite <- semWP2_fail).
                  2-3: iIntros "(% & _ & HF)"; auto.
                  iIntros "(%δ' & eqδ' & %rv & eqrv & ([%an (Hnpc' & Hpc' & (%h' & Hh' & %Hcfg & %HsLan))] & Hinstr' & _))".
                  iApply (semWP2_call_inline loop).
                  iPoseProof ("Hframe" with "Hinstr'") as "Hinstrs'".
                  iRevert "Hk". iApply (IH an h' Hcfg).
                  iFrame "Hh' Hpc' Hinstrs'". iExists an. iExact "Hnpc'".
               ++ cbn [CHeapSpec.error] in Hexec. contradiction.
            -- cbn [CHeapSpec.error] in Hexec. contradiction.
        + cbn [cexec_cfg_addr ty.RVToOption CHeapSpec.error] in Hexec.
          contradiction.
    Qed.

    Lemma sound_cexec_triple_addr {Γ : LCtx} {pre post b} (exitCond : bv xlenbits -> bool) {fuel} {ι : Valuation Γ} :
      cexec_triple_addr pre b exitCond fuel post (fun _ _ => True) []%list ->
      ⊢ semTripleCFG (λ a : RelVal ty_word, asn.interpret pre (ι.[("a"::ty_xlenbits) ↦ a]) ∗ ⌜ secLeak a ⌝) b exitCond fuel
          (λ a na : RelVal ty_word, asn.interpret post (ι.[("a"::ty_xlenbits) ↦ a].[("an"::ty_xlenbits) ↦ na])).
    Proof.
      cbv [cexec_triple_addr bind demonic_ctx demonic CPureSpec.demonic lift_purespec].
      iIntros (Htrip a) "((Hpre & %HsLa) & Hpc & Hnpc & Hinstrs) Hk".
      rewrite CPureSpec.wp_demonic_ctx in Htrip.
      specialize (Htrip ι a).
      apply produce_sound in Htrip.
      iPoseProof (Htrip with "[$] Hpre") as "(%h2 & [Hh2 %Hexec])". clear Htrip.
      iPoseProof (sound_exec_cfg_addr a _ _ Hexec) as "Hsound". clear Hexec.
      iApply ("Hsound" with "[$Hpc $Hnpc $Hinstrs $Hh2]").
      iIntros (an2) "(%Hexit & Hpc & Hnpc & Hinstrs & (%h3 & [Hh3 %Hconsume]))".
      apply consume_sound in Hconsume.
      iPoseProof (Hconsume with "Hh3") as "[HPOST Hheap]".
      iApply ("Hk" $! an2).
      iSplit. { iPureIntro. exact Hexit. }
      iFrame.
    Qed.

    Lemma sound_cblock_verification_condition {Γ pre post b exitCond fuel} :
      cblock_verification_condition pre b exitCond fuel post ->
      forall ι : Valuation Γ,
        ⊢ semTripleCFG (fun a => asn.interpret pre (ι.[("a"::ty_xlenbits) ↦ a])  ∗ ⌜ secLeak a ⌝)
          b exitCond fuel
          (fun a na => asn.interpret post (ι.[("a"::ty_xlenbits) ↦ a].[("an"::ty_xlenbits) ↦ na])).
    Proof.
      intros Hverif ι.
      exact (sound_cexec_triple_addr exitCond Hverif).
    Qed.

    Lemma sound_sblock_verification_condition {Γ pre post b exitCond fuel} :
      safeE (postprocess (sblock_verification_condition pre b exitCond fuel post wnil)) ->
      forall ι : Valuation Γ,
        ⊢ semTripleCFG (fun a => asn.interpret pre (ι.[("a"::ty_xlenbits) ↦ a])  ∗ ⌜ secLeak a ⌝)
          b exitCond fuel
          (fun a na => asn.interpret post (ι.[("a"::ty_xlenbits) ↦ a].[("an"::ty_xlenbits) ↦ na])).
    Proof.
      intros Hverif ι.
      apply (sound_cexec_triple_addr exitCond).
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

(* ======================================================================== *)
(* AnnotatedBlockVerification                                               *)
(*                                                                          *)
(* A separate mechanism (from BlockVer) for annotated instruction lists.    *)
(* An AnnotInstr is either a real instruction, a debug break, or a lemma   *)
(* invocation.  The verifier executes annotated blocks linearly (no CFG).  *)
(*                                                                          *)
(* This section is NOT used by CFGVer end-to-end proofs.  It is included   *)
(* here as part of the shared Verifier.v infrastructure.  Future work could *)
(* combine CFG execution with lemma invocations via AnnotInstr.             *)
(* ======================================================================== *)
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
                                 (formula_propeq ainstr apc) ;;
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
        ⟨ θ2' ⟩ _ <- SHeapSpec.lift_purespec (SPureSpec.assertSecLeak amsg.empty a2) ;;
        let a2 := persist__term a2 θ2' in
        let lenv2 := env.snoc (persist (A := Sub Σ) lenv1 (θ2 ∘ θ2')) _ a2 in
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
      RelVal ty_xlenbits -> RelVal ty_xlenbits -> CHeapSpec (RelVal ty_xlenbits) :=
      fun ainstr apc =>
        match b with
        | nil       => pure apc
        | cons instr b' =>
            match instr with
            | AnnotAST i =>
                _ <- assert_formula (ainstr = apc) ;;
                apc' <- cexec_instruction i apc ;;
                cexec_annotated_block_addr b' (ty.liftUnOp (σ1 := ty.bvec _) (σ2 := ty.bvec _) (fun a => bv.add a bv_instrsize) ainstr) apc'
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
      a    <- demonic _ ;; CHeapSpec.lift_purespec (CPureSpec.assertSecLeak a);;
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
          replace (ty.liftUnOp (σ1 := ty.bvec _) (σ2 := ty.bvec _) _ a) with
            (ty.liftBinOp (σ1 := ty.bvec _) (σ2 := ty.bvec _) (σ3 := ty.bvec _) bv.add a (SyncVal bv_instrsize)).
          now rsolve.
          destruct a; cbn; auto.
        - iApply "IHb"; rsolve.
      }
      now iApply (unconditionally_T with "H").
    Qed.

    #[export] Instance refine_compat_exec_annotated_block_addr (b : list AnnotInstr) {w} :
      RefineCompat (RVal ty_xlenbits -> RVal ty_xlenbits -> RHeapSpec (RVal ty_xlenbits))
        (cexec_annotated_block_addr b) w (sexec_annotated_block_addr b (w := w)) _ :=
      MkRefineCompat (rexec_annotated_block_addr b).

    Import PureSpec.

    Lemma rexec_annotated_block_triple_addr {Σ}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (b : list AnnotInstr)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) {w} :
      ⊢ ℛ⟦RHeapSpec RUnit⟧
          (cexec_annotated_block_triple_addr req b ens)
          (sexec_annotated_block_triple_addr req b ens (w := w)).
    Proof.
      unfold cexec_annotated_block_triple_addr, sexec_annotated_block_triple_addr.
      rsolve.
      all: repeat (rewrite ?forgetting_trans; try iModIntro; rsolve).
    Qed.

    #[export] Instance refine_compat_exec_annotated_triple_addr {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (b : list AnnotInstr)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) {w} :
      RefineCompat (RHeapSpec RUnit)
        (cexec_annotated_block_triple_addr req b ens) w (sexec_annotated_block_triple_addr req b ens (w := w)) _ :=
      MkRefineCompat (rexec_annotated_block_triple_addr req b ens).

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

    #[export] Instance refine_compat_annotated_block_verification_condition {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (b : list AnnotInstr)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) {w} :
      RefineCompat (LogicalSoundness.RProp)
        (cannotated_block_verification_condition req b ens) w (sannotated_block_verification_condition req b ens w) _ :=
      MkRefineCompat (rannotated_block_verification_condition req b ens).

  End Relational.

  Section Soundness.

    Import iris.base_logic.lib.iprop iris.proofmode.tactics.
    Import RiscvPmpIrisInstanceWithContracts.
    Import ProgramLogic.
    Import CHeapSpec.

    Context {Σ} {GS : sailGS2 Σ}.

    Definition extract_AST (i : AnnotInstr) : option AST :=
      match i with
      | AnnotAST a => Some a
      | _ => None
      end.

    Lemma sound_exec_annotated_block_addr {instrs ainstr apc} (h : SCHeap) (POST : RelVal ty_xlenbits -> iProp Σ) :
      LemmaSem ->
      cexec_annotated_block_addr instrs ainstr apc (fun res h' => interpret_scheap h' ⊢ POST res) h ->
      ⊢ ((interpret_scheap h ∗ lptsreg pc apc ∗ (∃ v, lptsreg nextpc v) ∗ ptsto_instrs ainstr (omap extract_AST instrs)  ∗ ⌜ secLeak apc ⌝) -∗
         (∀ an, lptsreg pc an ∗ (∃ v, lptsreg nextpc v) ∗ ptsto_instrs ainstr (omap extract_AST instrs) ∗ POST an -∗ WP2_loop) -∗
         WP2_loop)%I.
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
          iIntros "(Hh & Hpc & Hnpc & (Hinstr & Hinstrs) & HsLa) Hk".
          iApply semWP2_seq.
          iApply semWP2_call_inline.
          iApply (semWP2_mono with "[Hh Hnpc Hpc Hinstr HsLa]").
          { iApply (sound_exec_instruction Hverif). iFrame "Hinstr". iFrame. }
          clear Hverif.
          iIntros ([v1|m1] δ1 [v2|m2] δ2); cbn; last (iIntros "_"; now rewrite <- semWP2_fail).
          2-3: iIntros "(% & _ & HF)"; auto.
          iIntros "(%δ' & eqδ' & %rv & eqrv & ([%an (Hnpc & Hpc & (%h2 & Hh2 & %Hverif & %HsLan))] & Hinstr & HsLapc))".
          iApply (semWP2_call_inline loop).
          specialize (IHinstrs _ _ _ _ Hverif).
          iApply (IHinstrs with "[$Hh2 $Hpc Hnpc $Hinstrs]").
          iSplitL. by iExists _. auto.
          iIntros (an2) "(Hpc & Hnpc & Hinstrs & HPOST)".
          iApply ("Hk" with "[$Hinstr $Hpc $Hnpc $Hinstrs $HPOST]").
        + cbv [debug pure lift_purespec CPureSpec.pure].
          iIntros (->) "(Hh & Hpc & Hnpc & Hinstrs & HsLapc) Hk".
          iApply ("Hk" with "[$Hpc $Hnpc $Hinstrs $Hh]").
        + iIntros (Hlemcall) "(Hh & Hpc & Hnpc & Hinstrs & %HsLapc) Hk".
          pose proof (Hlem := lemSem _ lem).
          apply call_lemma_sound in Hlemcall. destruct Hlemcall. cbn in *.
          iPoseProof (H with "Hh") as "(%ι & %Heq & Hreq & Hk2)". clear H.
          iPoseProof (Hlem with "Hreq") as "Hens".
          iPoseProof ("Hk2" with "Hens") as "(%h' & Hh' & %Hk2)".
          apply IHinstrs in Hk2.
          iApply (Hk2 with "[$Hh' $Hpc $Hnpc $Hinstrs] Hk").
          auto.
    Qed.

    Definition semTripleAnnotatedBlock (PRE : RelVal ty_word -> iProp Σ)
      (instrs : list AnnotInstr) (POST : RelVal ty_word -> RelVal ty_word -> iProp Σ) : iProp Σ :=
      (∀ a,
         (PRE a ∗ pc ↦ᵣ a ∗ (∃ v, nextpc ↦ᵣ v) ∗ ptsto_instrs a (omap extract_AST instrs)) -∗
         (∀ an, pc ↦ᵣ an ∗ (∃ v, nextpc ↦ᵣ v) ∗ ptsto_instrs a (omap extract_AST instrs) ∗ POST a an -∗ WP2_loop) -∗
         WP2_loop)%I.
    Global Arguments semTripleAnnotatedBlock PRE%_I instrs POST%_I.

    Lemma sound_cexec_annotated_block_triple_addr {Γ pre post instrs} :
      LemmaSem ->
      (cexec_annotated_block_triple_addr (Σ := Γ) pre instrs post (λ _ _ , True) []%list) ->
      forall ι : Valuation Γ,
      ⊢ semTripleAnnotatedBlock (λ a : RelVal ty_word, asn.interpret pre (ι.[("a"::ty_xlenbits) ↦ a])) instrs
          (λ a na : RelVal ty_word, asn.interpret post (ι.[("a"::ty_xlenbits) ↦ a].[("an"::ty_xlenbits) ↦ na])).
    Proof.
      intros lemSem Hexec ι.
      iIntros (a) "(Hpre & Hpc & Hnpc & Hinstrs) Hk".
      hnf in Hexec.
      rewrite CPureSpec.wp_demonic_ctx in Hexec.
      specialize (Hexec ι a).
      unfold bind in Hexec.
      destruct Hexec as [HsLa Hexec].
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
