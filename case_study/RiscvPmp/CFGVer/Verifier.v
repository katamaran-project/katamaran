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
From stdpp Require Import gmap.

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

  (* Keep the base<=pc load-address guard folded during cbn/simpl (like
     instrAligned above), so `destruct (instrAligned v && bv.uleb base v)`
     can abstract the whole boolean out of proof goals. vm_compute (used by
     solve_vc) ignores `simpl never`, so the VC still reduces the guard. *)
  #[local] Arguments bv.uleb : simpl never.

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
    (* instrs is a finite map from absolute address to instruction.  The
       instruction executed at pc = v is simply instrs !! v (exact match) --
       no base, no alignment check, no (pc - base)/bytes_per_instr arithmetic.
       Keying on the absolute pc keeps the pc a single concrete value all the
       way through: sexec_instruction returns the absolute next pc (constrained
       by the isolated nextpc = <val>, which the solver substitutes), so the
       next lookup instrs !! nextpc concretises cleanly even at nonzero base. *)
    Fixpoint sexec_cfg_addr (instrs : gmap (bv xlenbits) AST) (exitCond : bv xlenbits -> bool) (fuel : nat) :
      ⊢ STerm ty_xlenbits -> SHeapSpec (STerm ty_xlenbits) :=
      fun w apc =>
        let emsg (s : string) : SHeapSpec (STerm ty_xlenbits) w :=
          error (fun _ => amsg.mk {| debug_string_pathcondition := wco w;
                                     debug_string_message := s |}) in
        match fuel with
        | O    => emsg "sexec_cfg_addr: out of fuel"
        | S n' =>
            match term_get_val apc with
            | None   => emsg "sexec_cfg_addr: pc is not a concrete literal (term_get_val apc = None)"
            | Some v =>
                angelic_binary
                  (if exitCond v then pure apc
                   else emsg "sexec_cfg_addr: exit branch chosen but exitCond is false at this pc")
                  (match instrs !! v with
                   | None   => emsg "sexec_cfg_addr: no instruction at this address (instrs !! pc = None)"
                   | Some i =>
                       ⟨ θ1 ⟩ apc' <- sexec_instruction i apc ;;
                       sexec_cfg_addr instrs exitCond n' apc'
                   end)
            end
        end.

    (* ================================================================ *)
    (* PARAMETRIC-BASE SUPPORT — READING GUIDE (Verifier.v side).        *)
    (*                                                                    *)
    (* WHY a new executor at all:  the gmap executor (sexec_cfg_addr)     *)
    (* dispatches by `instrs !! v`, which needs a CONCRETE address v.     *)
    (* With a symbolic base `p : term_var`, the pc is a term like `p+8`   *)
    (* with no concrete value, so gmap lookup cannot fire.  The `_tbl`    *)
    (* executor instead keys instructions/exits by TERMS and dispatches   *)
    (* by syntactic term-matching (`Term_eqb (peval apc) (peval key)`) —  *)
    (* which works whether the base is a literal (`256+8` folds to `264`) *)
    (* or a variable (`p+8` matches the key term `p+8`).                  *)
    (*                                                                    *)
    (* Follow the chain in this order:                                    *)
    (*   1. SITable/SETable, lookup_instr/is_exit  — term-keyed tables    *)
    (*      and peval-modulo matching (below).                            *)
    (*   2. sexec_cfg_addr_tbl / sblock_verification_condition_tbl —      *)
    (*      the symbolic executor + VC, mirror of the gmap ones.          *)
    (*   3. itable_faith / etable_faith  — "the term table faithfully     *)
    (*      mirrors the concrete gmap / exitCond at valuation ι".  This   *)
    (*      is the semantic bridge between the two worlds.                *)
    (*   4. rexec_cfg_addr_tbl  — the gmap concrete executor is refined   *)
    (*      by the term-table symbolic executor UNDER faithfulness.       *)
    (*   5. cexec_triple_addr_tbl + refine_guard + rexec_triple_addr_tbl  *)
    (*      — the "Option B" guarded VC refinement: faithfulness is an    *)
    (*      ASSUMED guard on the concrete side, discharged end-to-end at  *)
    (*      the one valuation ι = [p ↦ of_N init_addr].                   *)
    (*   6. rblock_verification_condition_tbl  — VC-level refinement,     *)
    (*      the entry point the soundness chain uses.                     *)
    (* The Examples.v side (exits_of_offs, itable_faith_of_list,          *)
    (* etable_faith_exits_of_offs, gen_contract_param/_rel, concretize_*, *)
    (* gen_contract_noninterferent_rel) discharges the guard and builds   *)
    (* the base-relative specs; see the reading guide there.              *)
    (* ================================================================ *)

    (* ---------------------------------------------------------------- *)
    (* Phase 1 (PLAN-symbolic-base.md §2): table-based executor variants, *)
    (* added ADDITIVELY alongside the gmap-based sexec_cfg_addr above.    *)
    (* Nothing above this comment is touched.  Suffix `_tbl` throughout;  *)
    (* Phase 3 switches Examples.v to this path and Phase 5 drops the old *)
    (* path and the suffix.                                               *)
    (*                                                                     *)
    (* Locked design (plan §0, decision 1): instruction dispatch is a     *)
    (* syntactic term-table lookup, `Term_eqb (peval apc) (peval key)`.   *)
    (* No gmap lookup on terms, no offset arithmetic.  Tables are          *)
    (* world-indexed (TYPE-level), since their keys are symbolic terms    *)
    (* that must be persisted across worlds as the executor steps.        *)
    (* ---------------------------------------------------------------- *)

    (* SITable / SETable: the symbolic analogues of the gmap `instrs` and *)
    (* function `exitCond` above -- a table of (address term, instruction) *)
    (* pairs, and a list of address terms marking exits. *)
    Definition SITable : TYPE :=
      fun w => list (Term (wctx w) ty_xlenbits * AST).
    Definition SETable : TYPE :=
      fun w => list (Term (wctx w) ty_xlenbits).

    Definition persist_itable {w1 w2} (θ : w1 ⊒ w2) : SITable w1 -> SITable w2 :=
      List.map (fun '(t,i) => (persist__term t θ, i)).
    Definition persist_etable {w1 w2} (θ : w1 ⊒ w2) : SETable w1 -> SETable w2 :=
      List.map (fun t => persist__term t θ).

    (* lookup_instr / is_exit: syntactic-modulo-peval matching of the     *)
    (* current pc term against the table keys.  `peval` on BOTH sides is  *)
    (* required (plan §0): solver substitutions leave keys unnormalized   *)
    (* (e.g. `8 ⊕ 256`) while the semantics-produced pc is normalized      *)
    (* (`264`); peval reconciles the two before the syntactic Term_eqb    *)
    (* comparison.  Do not drop either peval call. *)
    Definition lookup_instr {w} (tbl : SITable w)
        (apc : STerm ty_xlenbits w) : option AST :=
      option_map snd
        (List.find (fun '(t,_) => Term_eqb (peval apc) (peval t)) tbl).
    Definition is_exit {w} (exits : SETable w)
        (apc : STerm ty_xlenbits w) : bool :=
      List.existsb (fun t => Term_eqb (peval apc) (peval t)) exits.

    (* --- Phase 1 self-tests (cheap sanity anchors for lookup_instr /    *)
    (* is_exit / peval; NOT part of the soundness chain). *)
    Section Phase1SelfTests.
      Let w1 : World := wlctx ([ctx] ▻ "p"∷ty_xlenbits).
      Let p1 : Term (wctx w1) ty_xlenbits := term_var "p".
      Let instrA : AST := RTYPE (bv.of_N 1) (bv.of_N 0) (bv.of_N 2) RISCV_SUB.
      Let instrB : AST := RTYPE (bv.of_N 2) (bv.of_N 1) (bv.of_N 0) RISCV_SUB.
      Let tbl1 : SITable w1 :=
        [ (p1, instrA)
        ; (term_bvadd (term_val ty_xlenbits (bv.of_N 4)) p1, instrB)
        ]%list.

      (* pc = 4 ⊕ p matches the second table entry. *)
      Example lookup_instr_hit :
        lookup_instr tbl1 (term_bvadd (term_val ty_xlenbits (bv.of_N 4)) p1) = Some instrB.
      Proof. vm_compute. reflexivity. Qed.

      (* pc = 8 ⊕ p matches no key in tbl1. *)
      Example lookup_instr_miss :
        lookup_instr tbl1 (term_bvadd (term_val ty_xlenbits (bv.of_N 8)) p1) = None.
      Proof. vm_compute. reflexivity. Qed.

      (* peval reconciliation: an unnormalized solver-substituted key     *)
      (* (8 ⊕ 256) and a normalized concrete pc (264) compare equal after *)
      (* peval on both sides. *)
      Example peval_reconcile :
        Term_eqb (peval (term_val ty_xlenbits (bv.of_N 264) : Term (wctx w1) ty_xlenbits))
                 (peval (term_bvadd (term_val ty_xlenbits (bv.of_N 8)) (term_val ty_xlenbits (bv.of_N 256))))
        = true.
      Proof. vm_compute. reflexivity. Qed.
    End Phase1SelfTests.

    (* sexec_cfg_addr_tbl: table-based variant of sexec_cfg_addr above,   *)
    (* same shape (fuel guard, angelic_binary between exit/execute), but  *)
    (* dispatching via lookup_instr/is_exit instead of gmap lookup on a   *)
    (* concrete literal.  `term_get_val` does not appear: apc may stay    *)
    (* symbolic, matching happens through peval instead of concretising.  *)
    (* tbl/exits are threaded as ARGUMENTS through the recursion (they    *)
    (* are world-dependent, persisted at each step via persist_itable /   *)
    (* persist_etable), unlike the old `instrs`/`exitCond` which are      *)
    (* plain (non-world-indexed) Fixpoint parameters. *)
    Fixpoint sexec_cfg_addr_tbl (fuel : nat) :
      ⊢ SITable -> SETable -> STerm ty_xlenbits -> SHeapSpec (STerm ty_xlenbits) :=
      fun w tbl exits apc =>
        let emsg (s : string) : SHeapSpec (STerm ty_xlenbits) w :=
          error (fun _ => amsg.mk {| debug_string_pathcondition := wco w;
                                     debug_string_message := s |}) in
        match fuel with
        | O    => emsg "sexec_cfg_addr_tbl: out of fuel"
        | S n' =>
            angelic_binary
              (if is_exit exits apc then pure apc
               else emsg "sexec_cfg_addr_tbl: exit branch chosen but pc matches no declared exit term")
              (match lookup_instr tbl apc with
               | None   => emsg "sexec_cfg_addr_tbl: no instruction key matches this pc term"
               | Some i =>
                   ⟨ θ1 ⟩ apc' <- sexec_instruction i apc ;;
                   sexec_cfg_addr_tbl n' (persist_itable θ1 tbl) (persist_etable θ1 exits) apc'
               end)
        end.

    (* Apply symbolic execution to verify a Hoare triple for a block of instructions.
     * The precondition can mention the address a where the block is loaded.
     * The postcondition can additionally mention the address an where the pc points after execution.
     *)
    Definition sexec_triple_addr {Σ : LCtx}
      (req : Assertion (Σ ▻ ("a"::ty_xlenbits))) (instrs : gmap (bv xlenbits) AST) (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ ("a"::ty_xlenbits) ▻ ("an"::ty_xlenbits))) :
      ⊢ SHeapSpec Unit :=
      fun w =>
        ⟨ θ0 ⟩ δ <- demonic_ctx id Σ ;;
        ⟨ θ1 ⟩ a <- demonic (Some "a") _ ;;
        let δ1 := env.snoc (persist ( A:= Sub Σ) δ θ1) _ a in
        ⟨ θ2 ⟩ _ <- produce req δ1 ;;
        let a2 := persist__term a θ2 in
        ⟨ θ3 ⟩ na <- sexec_cfg_addr instrs exitCond fuel a2 ;;
        let δ3 := persist δ1 (θ2 ∘ θ3) in
        consume ens δ3.["an"∷ty_xlenbits ↦ na].

    (* sblock_verification_condition base req b exitCond fuel ens:
       The final symbolic VC.  It runs sexec_triple_addr inside SHeapSpec.run,
       which discards the final heap (no leakcheck).  The result is a 𝕊 wnil
       proposition that can be checked by `safeE (postprocess ...)`.
       Call pattern (from Examples.v):
         sblock_verification_condition (Σ := [ctx]) base req b ec fl ens wnil
       The explicit `Σ := [ctx]` is required because Rocq cannot infer it
       from the other arguments alone. `base` is the concrete address the
       block is loaded at; `req` is expected to constrain "a" = base (e.g.
       via asn_init_pc base) so the executor's fetch index lines up with
       where ptsto_instrs base b actually places the instructions. *)
    Definition sblock_verification_condition {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (instrs : gmap (bv xlenbits) AST) (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) : ⊢ 𝕊 :=
      fun w =>
        (* SHeapSpec does not perform a leakcheck. We could include one here. *)
        SHeapSpec.run (sexec_triple_addr req instrs exitCond fuel ens (w := w)).

    (* sexec_triple_addr_tbl / sblock_verification_condition_tbl: table-  *)
    (* based variants of sexec_triple_addr / sblock_verification_condition *)
    (* above.  `tbl`/`exits` are given at the CONTRACT context Σ (plain    *)
    (* lists of Σ-level terms, like `req`/`ens`), and moved into the       *)
    (* current world the same way `req` is: by applying the substitution  *)
    (* `ζ : Sub Σ w` (obtained from `demonic_ctx`'s δ, persisted forward   *)
    (* to the world where `a` lives) to each key term via `subst`. *)
    Definition subst_itable {Σ : LCtx} {w : World} (ζ : Sub Σ w)
        (tbl : list (Term Σ ty_xlenbits * AST)) : SITable w :=
      List.map (fun '(t,i) => (subst t ζ, i)) tbl.
    Definition subst_etable {Σ : LCtx} {w : World} (ζ : Sub Σ w)
        (exits : list (Term Σ ty_xlenbits)) : SETable w :=
      List.map (fun t => subst t ζ) exits.

    Definition sexec_triple_addr_tbl {Σ : LCtx}
      (req : Assertion (Σ ▻ ("a"::ty_xlenbits)))
      (tbl : list (Term Σ ty_xlenbits * AST)) (exits : list (Term Σ ty_xlenbits)) (fuel : nat)
      (ens : Assertion (Σ ▻ ("a"::ty_xlenbits) ▻ ("an"::ty_xlenbits))) :
      ⊢ SHeapSpec Unit :=
      fun w =>
        ⟨ θ0 ⟩ δ <- demonic_ctx id Σ ;;
        ⟨ θ1 ⟩ a <- demonic (Some "a") _ ;;
        let δ1 := env.snoc (persist ( A:= Sub Σ) δ θ1) _ a in
        ⟨ θ2 ⟩ _ <- produce req δ1 ;;
        let a2 := persist__term a θ2 in
        let ζ := persist (A := Sub Σ) δ (θ1 ∘ θ2) in
        ⟨ θ3 ⟩ na <- sexec_cfg_addr_tbl fuel (subst_itable ζ tbl) (subst_etable ζ exits) a2 ;;
        let δ3 := persist δ1 (θ2 ∘ θ3) in
        consume ens δ3.["an"∷ty_xlenbits ↦ na].

    (* sblock_verification_condition_tbl: table-based mirror of           *)
    (* sblock_verification_condition above; same SHeapSpec.run/wnil shape, *)
    (* no leakcheck. *)
    Definition sblock_verification_condition_tbl {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits))
      (tbl : list (Term Σ ty_xlenbits * AST)) (exits : list (Term Σ ty_xlenbits)) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) : ⊢ 𝕊 :=
      fun w =>
        SHeapSpec.run (sexec_triple_addr_tbl req tbl exits fuel ens (w := w)).

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

    Fixpoint cexec_cfg_addr (instrs : gmap (bv xlenbits) AST) (exitCond : bv xlenbits -> bool) (fuel : nat) :
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
                  (match instrs !! v with
                   | None   => error
                   | Some i =>
                       apc' <- cexec_instruction i apc ;;
                       cexec_cfg_addr instrs exitCond n' apc'
                   end)
            end
        end.

    Definition cexec_triple_addr {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (instrs : gmap (bv xlenbits) AST) (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) :
      CHeapSpec unit :=
      lenv <- demonic_ctx Σ ;;
      a    <- demonic _ ;;
      _    <- produce req lenv.["a"∷ty_xlenbits ↦ a]  ;;
      na   <- cexec_cfg_addr instrs exitCond fuel a ;;
      consume ens lenv.["a"∷ty_xlenbits ↦ a].["an"∷ty_xlenbits ↦ na].

    Definition cblock_verification_condition {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (instrs : gmap (bv xlenbits) AST) (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) : Prop :=
      (* CHeapSpec.run does not perform a leakcheck. We could include one here. *)
      CHeapSpec.run (cexec_triple_addr req instrs exitCond fuel ens).

    Import (hints) CStoreSpec.

    #[export] Instance mono_cexec_instruction {i a} :
      Monotonic (MHeapSpec eq) (cexec_instruction i a).
    Proof. typeclasses eauto. Qed.

    #[export] Instance mono_cexec_cfg_addr {instrs exitCond fuel apc} :
      Monotonic (MHeapSpec eq) (cexec_cfg_addr instrs exitCond fuel apc).
    Proof.
      revert apc. induction fuel; intro apc.
      - typeclasses eauto.
      - destruct apc as [v | vl vr].
        + cbn [cexec_cfg_addr ty.RVToOption CHeapSpec.angelic_binary].
          destruct (exitCond v);
            cbn [CHeapSpec.pure CHeapSpec.error bind];
            try destruct (instrs !! v); typeclasses eauto.
        + cbn [cexec_cfg_addr ty.RVToOption]. typeclasses eauto.
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
    Lemma rexec_cfg_addr (instrs : gmap (bv xlenbits) AST) (exitCond : bv xlenbits -> bool) (fuel : nat) {w} :
      ⊢ ℛ⟦RVal ty_xlenbits -> RHeapSpec (RVal ty_xlenbits)⟧
          (cexec_cfg_addr instrs exitCond fuel)
          (sexec_cfg_addr instrs exitCond fuel (w := w)).
    Proof.
      iAssert (ℛ⟦□ᵣ (RVal ty_xlenbits -> RHeapSpec (RVal ty_xlenbits))⟧
                 (cexec_cfg_addr instrs exitCond fuel)
                 (fun w' θ => sexec_cfg_addr instrs exitCond fuel (w := w'))) as "H".
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
          + (* [instrs !! v] inside the ℛ⟦⟧ relation arguments is not
               syntactically matched by a freshly-elaborated [instrs !! v]
               (hidden implicit/instance mismatch), so [destruct (instrs !! v)]
               binds the case variable but fails to reduce the [match] — which
               makes [refine_bind] diverge on the unreduced match.  Capture the
               goal's *exact* scrutinee with [lazymatch] and destruct that. *)
            lazymatch goal with
            | |- context[match ?x with Some _ => _ | None => _ end] =>
                destruct x as [i|]
            end.
            * iApply (refine_bind (RA := RVal ty_xlenbits)).
              -- now iApply (rexec_instruction i with "Ha").
              -- rsolve.
                 iPoseProof (forgetting_unconditionally_drastic with "IHfuel") as "IH".
                 iApply ("IH" with "[$]").
            * rsolve.
      }
      iApply (unconditionally_T with "H").
    Qed.

    #[export] Instance refine_compat_exec_cfg_addr (instrs : gmap (bv xlenbits) AST) (exitCond : bv xlenbits -> bool) (fuel : nat) {w} :
      RefineCompat (RVal ty_xlenbits -> RHeapSpec (RVal ty_xlenbits))
        (cexec_cfg_addr instrs exitCond fuel) w (sexec_cfg_addr instrs exitCond fuel (w := w)) _ :=
      MkRefineCompat (rexec_cfg_addr instrs exitCond fuel).

    Import PureSpec.

    (* ------------------------------------------------------------------ *)
    (* Table faithfulness: bridge between the term-table symbolic executor *)
    (* (sexec_cfg_addr_tbl) and the gmap-based concrete executor            *)
    (* (cexec_cfg_addr).  itable_rel/etable_rel are Pred-level premises:    *)
    (* every key term must instantiate to a SyncVal address that the gmap   *)
    (* maps to the paired instruction (resp. that satisfies exitCond).      *)
    (* The ∃-SyncVal form is essential: with an implication form the        *)
    (* concrete executor errors at RVToOption on NonSyncVal keys while the  *)
    (* symbolic one proceeds, breaking refinement.                          *)
    (* ------------------------------------------------------------------ *)

    Definition itable_rel {w} (instrs : gmap (bv xlenbits) AST) (tbl : SITable w) : Pred w :=
      fun ι => List.Forall
        (fun p => exists v, inst (fst p) ι = ty.SyncVal v /\ instrs !! v = Some (snd p)) tbl.

    Definition etable_rel {w} (exitCond : bv xlenbits -> bool) (exits : SETable w) : Pred w :=
      fun ι => List.Forall
        (fun t => exists v,
           inst (T := fun Σ => Term Σ ty_xlenbits) t ι = ty.SyncVal v /\ exitCond v = true) exits.

    Lemma peval_eqb_inst {Σ : LCtx} {σ} (t1 t2 : Term Σ σ) (ι : Valuation Σ) :
      Term_eqb (peval t1) (peval t2) = true -> inst t1 ι = inst t2 ι.
    Proof.
      intros H.
      destruct (Term_eqb_spec (peval t1) (peval t2)) as [e|]; [|discriminate].
      rewrite <- (peval_sound t1 ι), <- (peval_sound t2 ι).
      now rewrite e.
    Qed.

    Lemma lookup_instr_sound {w} (instrs : gmap (bv xlenbits) AST) (tbl : SITable w)
        (apc : STerm ty_xlenbits w) (i : AST) (ι : Valuation w) :
      lookup_instr tbl apc = Some i ->
      itable_rel instrs tbl ι ->
      exists v, inst apc ι = ty.SyncVal v /\ instrs !! v = Some i.
    Proof.
      unfold lookup_instr, itable_rel.
      intros Hlk Hrel.
      destruct (List.find _ tbl) as [[t i']|] eqn:Hfind; cbn in Hlk; [|discriminate].
      injection Hlk as ->.
      apply find_some in Hfind as [Hin Heqb].
      rewrite List.Forall_forall in Hrel.
      specialize (Hrel _ Hin) as (v & Hv & Hmap).
      exists v.
      split; [|exact Hmap].
      rewrite (peval_eqb_inst apc t ι Heqb).
      exact Hv.
    Qed.

    Lemma is_exit_sound {w} (exitCond : bv xlenbits -> bool) (exits : SETable w)
        (apc : STerm ty_xlenbits w) (ι : Valuation w) :
      is_exit exits apc = true ->
      etable_rel exitCond exits ι ->
      exists v, inst apc ι = ty.SyncVal v /\ exitCond v = true.
    Proof.
      unfold is_exit, etable_rel.
      intros Hex Hrel.
      apply List.existsb_exists in Hex as (t & Hin & Heqb).
      rewrite List.Forall_forall in Hrel.
      specialize (Hrel _ Hin) as (v & Hv & Hcond).
      exists v.
      split; [|exact Hcond].
      rewrite (peval_eqb_inst apc t ι Heqb).
      exact Hv.
    Qed.

    Lemma forgetting_itable_rel {w1 w2} (θ : Acc w1 w2)
        (instrs : gmap (bv xlenbits) AST) (tbl : SITable w1) :
      (forgetting θ (itable_rel instrs tbl) ⊣⊢ itable_rel instrs (persist_itable θ tbl))%I.
    Proof.
      constructor.
      intros ι.
      unfold forgetting, itable_rel, persist_itable.
      rewrite List.Forall_map.
      cbn.
      split; apply List.Forall_impl; intros [t i] (v & Hv & Hm);
        exists v; (split; [|exact Hm]); cbn in *;
        rewrite inst_persist in Hv + rewrite inst_persist; exact Hv.
    Qed.

    Lemma forgetting_etable_rel {w1 w2} (θ : Acc w1 w2)
        (exitCond : bv xlenbits -> bool) (exits : SETable w1) :
      (forgetting θ (etable_rel exitCond exits) ⊣⊢ etable_rel exitCond (persist_etable θ exits))%I.
    Proof.
      constructor.
      intros ι.
      unfold forgetting, etable_rel, persist_etable.
      rewrite List.Forall_map.
      cbn.
      split; apply List.Forall_impl; intros t (v & Hv & Hc);
        exists v; (split; [|exact Hc]); cbn in *;
        rewrite inst_persist in Hv + rewrite inst_persist; exact Hv.
    Qed.

    Lemma persist_itable_refl {w} (tbl : SITable w) :
      persist_itable acc_refl tbl = tbl.
    Proof.
      unfold persist_itable.
      induction tbl as [|[t i] tbl' IH]; cbn; [reflexivity|].
      cbn in IH.
      f_equal.
      exact IH.
    Qed.

    Lemma persist_etable_refl {w} (exits : SETable w) :
      persist_etable acc_refl exits = exits.
    Proof.
      unfold persist_etable.
      induction exits as [|t exits' IH]; cbn; [reflexivity|].
      cbn in IH.
      f_equal.
      exact IH.
    Qed.

    Lemma persist_itable_trans {w1 w2 w3} (θ12 : Acc w1 w2) (θ23 : Acc w2 w3) (tbl : SITable w1) :
      persist_itable θ23 (persist_itable θ12 tbl) = persist_itable (acc_trans θ12 θ23) tbl.
    Proof.
      unfold persist_itable.
      rewrite List.map_map.
      apply List.map_ext.
      intros [t i].
      now rewrite persist_trans.
    Qed.

    Lemma persist_etable_trans {w1 w2 w3} (θ12 : Acc w1 w2) (θ23 : Acc w2 w3) (exits : SETable w1) :
      persist_etable θ23 (persist_etable θ12 exits) = persist_etable (acc_trans θ12 θ23) exits.
    Proof.
      unfold persist_etable.
      rewrite List.map_map.
      apply List.map_ext.
      intros t.
      now rewrite persist_trans.
    Qed.

    Lemma lookup_instr_sound_repₚ {w} (instrs : gmap (bv xlenbits) AST) (tbl : SITable w)
        (apc : STerm ty_xlenbits w) (i : AST) (a : RelVal ty_xlenbits) :
      lookup_instr tbl apc = Some i ->
      (itable_rel instrs tbl ∗ repₚ (T := fun Σ => Term Σ ty_xlenbits) a apc ⊢
       ⌜exists v, a = ty.SyncVal v /\ instrs !! v = Some i⌝)%I.
    Proof.
      intros Hlk.
      constructor.
      intros ι Hpc H.
      cbn in H.
      destruct H as [Hrel Ha].
      destruct (lookup_instr_sound apc Hlk Hrel) as (v & Hv & Hm).
      exists v.
      split; [|exact Hm].
      now rewrite <- Ha.
    Qed.

    Lemma is_exit_sound_repₚ {w} (exitCond : bv xlenbits -> bool) (exits : SETable w)
        (apc : STerm ty_xlenbits w) (a : RelVal ty_xlenbits) :
      is_exit exits apc = true ->
      (etable_rel exitCond exits ∗ repₚ (T := fun Σ => Term Σ ty_xlenbits) a apc ⊢
       ⌜exists v, a = ty.SyncVal v /\ exitCond v = true⌝)%I.
    Proof.
      intros Hex.
      constructor.
      intros ι Hpc H.
      cbn in H.
      destruct H as [Hrel Ha].
      destruct (is_exit_sound apc Hex Hrel) as (v & Hv & Hc).
      exists v.
      split; [|exact Hc].
      now rewrite <- Ha.
    Qed.

    (* rexec_cfg_addr_tbl: refinement of the gmap concrete executor by the  *)
    (* term-table symbolic executor, under table faithfulness.  Mirrors     *)
    (* rexec_cfg_addr above (iInduction on fuel, boxed IH projected by      *)
    (* forgetting_unconditionally_drastic); the four subgoals of the        *)
    (* is_exit/lookup_instr double destruct are discharged sequentially.    *)
    Lemma rexec_cfg_addr_tbl (instrs : gmap (bv xlenbits) AST) (exitCond : bv xlenbits -> bool)
        (fuel : nat) {w} (tbl : SITable w) (exits : SETable w) :
      (itable_rel instrs tbl ∗ etable_rel exitCond exits ⊢
       ℛ⟦RVal ty_xlenbits -> RHeapSpec (RVal ty_xlenbits)⟧
           (cexec_cfg_addr instrs exitCond fuel)
           (sexec_cfg_addr_tbl fuel tbl exits))%I.
    Proof.
      iIntros "#[Hi He]".
      iAssert (ℛ⟦□ᵣ (RVal ty_xlenbits -> RHeapSpec (RVal ty_xlenbits))⟧
                 (cexec_cfg_addr instrs exitCond fuel)
                 (fun w' θ => sexec_cfg_addr_tbl fuel (persist_itable θ tbl)
                                (persist_etable θ exits))) as "H".
      {
        iInduction fuel as [|n'] "IHfuel".
        - rsolve.
        - cbn [sexec_cfg_addr_tbl cexec_cfg_addr].
          rsolve.
          rewrite forgetting_itable_rel forgetting_etable_rel.
          iRename select (ℛ⟦RVal ty_xlenbits⟧ a ta) into "Ha".
          destruct (is_exit (persist_etable ω exits) ta) eqn:Hex;
            destruct (lookup_instr (persist_itable ω tbl) ta) as [i|] eqn:Hlk.
          (* exit-hit / lookup-hit *)
          iPoseProof (lookup_instr_sound_repₚ instrs _ _ a Hlk with "[$Hi $Ha]") as "%Hfact".
          destruct Hfact as (v & -> & Hm).
          iPoseProof (is_exit_sound_repₚ exitCond _ _ _ Hex with "[$He $Ha]") as "%Hfact2".
          destruct Hfact2 as (v' & Hveq & Hcond).
          injection Hveq as <-.
          cbn [ty.RVToOption].
          rewrite Hcond Hm.
          rsolve.
          rewrite (persist_itable_trans ω ω0 tbl) (persist_etable_trans ω ω0 exits).
          iPoseProof (forgetting_unconditionally_drastic with "IHfuel") as "IH".
          iApply ("IH" with "[$]").
          (* exit-hit / lookup-miss *)
          iPoseProof (is_exit_sound_repₚ exitCond _ _ _ Hex with "[$He $Ha]") as "%Hfact".
          destruct Hfact as (v & -> & Hcond).
          cbn [ty.RVToOption].
          rewrite Hcond.
          rsolve.
          (* exit-miss / lookup-hit *)
          iPoseProof (lookup_instr_sound_repₚ instrs _ _ a Hlk with "[$Hi $Ha]") as "%Hfact".
          destruct Hfact as (v & -> & Hm).
          cbn [ty.RVToOption].
          rewrite Hm.
          rsolve.
          rewrite (persist_itable_trans ω ω0 tbl) (persist_etable_trans ω ω0 exits).
          iPoseProof (forgetting_unconditionally_drastic with "IHfuel") as "IH".
          iApply ("IH" with "[$]").
          (* exit-miss / lookup-miss: symbolic errors twice; concrete side *)
          (* must also fail — NonSyncVal pc is rejected, SyncVal pc closed  *)
          (* by the empty angelic_binary of two errors.                     *)
          destruct a as [va|va1 va2]; cbn [ty.RVToOption]; rsolve.
          iIntros (cΦ sΦ) "#rΦ %ch %sh #rh".
          unfold LogicalSoundness.RProp; cbn.
          iIntros "[%HF|%HF]"; destruct HF.
      }
      iPoseProof (unconditionally_T with "H") as "HT".
      unfold T.
      cbv beta.
      rewrite (persist_itable_refl tbl) (persist_etable_refl exits).
      iApply "HT".
    Qed.

    (* ------------------------------------------------------------------ *)
    (* VC-level refinement for the term-table verifier (guarded form).     *)
    (* The concrete side cexec_triple_addr_tbl is the gmap triple with an   *)
    (* extra assumed faithfulness guard tying the Σ-level key terms to the  *)
    (* concrete gmap at the demonically chosen valuation.  At valuations    *)
    (* where the table does not match the gmap (e.g. a placement variable   *)
    (* instantiated to a different base) the triple holds vacuously; the    *)
    (* end-to-end user discharges the guard at the one valuation where the  *)
    (* program actually resides.  Scaffolding for refinement only — the     *)
    (* concrete executor and soundness chain are untouched.                 *)
    (* ------------------------------------------------------------------ *)

    Definition itable_faith {Σ : LCtx} (instrs : gmap (bv xlenbits) AST)
        (tbl : list (Term Σ ty_xlenbits * AST)) (ι : Valuation Σ) : Prop :=
      List.Forall
        (fun p => exists v, inst (fst p) ι = ty.SyncVal v /\ instrs !! v = Some (snd p)) tbl.

    Definition etable_faith {Σ : LCtx} (exitCond : bv xlenbits -> bool)
        (exits : list (Term Σ ty_xlenbits)) (ι : Valuation Σ) : Prop :=
      List.Forall
        (fun t => exists v,
           inst (T := fun Σ => Term Σ ty_xlenbits) t ι = ty.SyncVal v /\ exitCond v = true) exits.

    Definition cexec_triple_addr_tbl {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (instrs : gmap (bv xlenbits) AST)
      (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
      (tbl : list (Term Σ ty_xlenbits * AST)) (exits : list (Term Σ ty_xlenbits)) : CHeapSpec unit :=
      CHeapSpec.bind (CHeapSpec.demonic_ctx Σ) (fun lenv =>
      CHeapSpec.bind (CHeapSpec.lift_purespec (CPureSpec.assume_formula
          (itable_faith instrs tbl lenv /\ etable_faith exitCond exits lenv))) (fun _ =>
      CHeapSpec.bind (CHeapSpec.demonic _) (fun a =>
      CHeapSpec.bind (CHeapSpec.produce req lenv.["a"∷ty_xlenbits ↦ a]) (fun _ =>
      CHeapSpec.bind (cexec_cfg_addr instrs exitCond fuel a) (fun na =>
      CHeapSpec.consume ens lenv.["a"∷ty_xlenbits ↦ a].["an"∷ty_xlenbits ↦ na]))))).

    (* refine_guard: a concrete-side-only assume step.  Assuming more on   *)
    (* the concrete side weakens the concrete claim, which is the sound    *)
    (* direction for RHeapSpec refinement; the symbolic side is unchanged. *)
    Lemma refine_guard {SA CA} (RA : Rel SA CA) (P : Prop)
        (c : CHeapSpec CA) {w} (s : SHeapSpec SA w) :
      ((⌜P⌝ -∗ ℛ⟦RHeapSpec RA⟧ c s) ⊢
       ℛ⟦RHeapSpec RA⟧
         (CHeapSpec.bind (CHeapSpec.lift_purespec (CPureSpec.assume_formula P)) (fun _ => c))
         s)%I.
    Proof.
      constructor.
      intros ι Hpc H.
      cbn in H |- *.
      cbv [RSat RImpl RHeapSpec LogicalSoundness.RProp CHeapSpec.bind CHeapSpec.lift_purespec CPureSpec.assume_formula CPureSpec.assume_pathcondition] in H |- *.
      cbn in H |- *.
      intros cΦ sΦ HΦ ch sh Hh Hs HP.
      exact (H HP cΦ sΦ HΦ ch sh Hh Hs).
    Qed.

    Lemma itable_rel_of_faith_forget {Σ' : LCtx} {wa wb : World} (θ : Acc wa wb) (ζ : Sub Σ' wa)
        (instrs' : gmap (bv xlenbits) AST) (tbl' : list (Term Σ' ty_xlenbits * AST))
        (ιΣ : NamedEnv RelVal Σ') :
      itable_faith instrs' tbl' ιΣ ->
      (forgetting θ (ℛ⟦RNEnv LVar Σ'⟧ ιΣ ζ) ⊢ itable_rel instrs' (subst_itable (persist ζ θ) tbl'))%I.
    Proof.
      intros Hfaith.
      constructor.
      intros ι Hpc Hrel.
      unfold forgetting, RNEnv, RInst in Hrel.
      cbn in Hrel.
      unfold itable_rel, subst_itable.
      rewrite List.Forall_map.
      eapply List.Forall_impl; [|exact Hfaith].
      intros [t i] (v & Hv & Hm).
      exists v.
      split; [|exact Hm].
      cbn.
      rewrite inst_subst inst_persist Hrel.
      exact Hv.
    Qed.

    Lemma etable_rel_of_faith_forget {Σ' : LCtx} {wa wb : World} (θ : Acc wa wb) (ζ : Sub Σ' wa)
        (exitCond' : bv xlenbits -> bool) (exits' : list (Term Σ' ty_xlenbits))
        (ιΣ : NamedEnv RelVal Σ') :
      etable_faith exitCond' exits' ιΣ ->
      (forgetting θ (ℛ⟦RNEnv LVar Σ'⟧ ιΣ ζ) ⊢ etable_rel exitCond' (subst_etable (persist ζ θ) exits'))%I.
    Proof.
      intros Hfaith.
      constructor.
      intros ι Hpc Hrel.
      unfold forgetting, RNEnv, RInst in Hrel.
      cbn in Hrel.
      unfold etable_rel, subst_etable.
      rewrite List.Forall_map.
      eapply List.Forall_impl; [|exact Hfaith].
      intros t (v & Hv & Hc).
      exists v.
      split; [|exact Hc].
      rewrite inst_subst inst_persist Hrel.
      exact Hv.
    Qed.

    Lemma forgetting_RVal {σ} {wa wb : World} (θ : Acc wa wb) (v : RelVal σ) (t : STerm σ wa) :
      (forgetting θ (ℛ⟦RVal σ⟧ v t) ⊢ ℛ⟦RVal σ⟧ v (persist__term t θ))%I.
    Proof.
      constructor.
      intros ι Hpc H.
      unfold forgetting in H.
      cbn in H |- *.
      unfold RVal, RInst, repₚ in H |- *.
      cbn in H |- *.
      rewrite inst_persist.
      exact H.
    Qed.

    (* rexec_triple_addr_tbl: unconditional refinement of the guarded      *)
    (* concrete triple by the table-based symbolic triple.  The guard is   *)
    (* introduced via refine_guard; the executor bind is dispatched by     *)
    (* rexec_cfg_addr_tbl with faithfulness transported through the world  *)
    (* morphisms by the _forget lemmas.  rsolve must NOT be let loose on   *)
    (* the executor bind (no RefineCompat instance matches the table       *)
    (* executor's premise-free form; typeclass search diverges).           *)
    Lemma rexec_triple_addr_tbl {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (instrs : gmap (bv xlenbits) AST)
      (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
      (tbl : list (Term Σ ty_xlenbits * AST)) (exits : list (Term Σ ty_xlenbits)) {w} :
      ⊢ ℛ⟦RHeapSpec RUnit⟧
          (cexec_triple_addr_tbl req instrs exitCond fuel ens tbl exits)
          (sexec_triple_addr_tbl req tbl exits fuel ens (w := w)).
    Proof.
      unfold cexec_triple_addr_tbl, sexec_triple_addr_tbl.
      iApply (HeapSpec.refine_bind (RA := RNEnv LVar Σ) (RB := RUnit)).
      - rsolve.
      - iIntros (w1 θ0).
        iModIntro.
        iIntros (lenv δ) "#Hδ".
        iApply refine_guard.
        iIntros "%Hfaith".
        destruct Hfaith as [Hif Hef].
        iApply (HeapSpec.refine_bind (RA := RVal ty_xlenbits) (RB := RUnit)).
        { rsolve. }
        iIntros (w0 θ1).
        iModIntro.
        iIntros (a ta) "#Ha".
        iApply (HeapSpec.refine_bind (RA := RUnit) (RB := RUnit)).
        { rsolve. }
        iIntros (w2 θ2).
        iModIntro.
        iIntros (u tu) "#Hu".
        iApply (HeapSpec.refine_bind (RA := RVal ty_xlenbits) (RB := RUnit)).
        { iPoseProof (itable_rel_of_faith_forget (acc_trans θ1 θ2) δ Hif with "Hδ") as "#Hi".
          iPoseProof (etable_rel_of_faith_forget (acc_trans θ1 θ2) δ Hef with "Hδ") as "#He".
          iApply (rexec_cfg_addr_tbl instrs exitCond fuel _ _ with "[$Hi $He]").
          iApply (forgetting_RVal with "Ha"). }
        iIntros (w3 θ3).
        iModIntro.
        iIntros (na tna) "#Hna".
        rsolve.
        repeat (rewrite ?forgetting_trans; try iModIntro; rsolve).
    Qed.

    #[export] Instance refine_compat_exec_triple_addr_tbl {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (instrs : gmap (bv xlenbits) AST)
      (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
      (tbl : list (Term Σ ty_xlenbits * AST)) (exits : list (Term Σ ty_xlenbits)) {w} :
      RefineCompat (RHeapSpec RUnit)
        (cexec_triple_addr_tbl req instrs exitCond fuel ens tbl exits) w
        (sexec_triple_addr_tbl req tbl exits fuel ens (w := w)) _ :=
      MkRefineCompat (rexec_triple_addr_tbl req instrs exitCond fuel ens tbl exits).

    Definition cblock_verification_condition_tbl {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (instrs : gmap (bv xlenbits) AST)
      (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
      (tbl : list (Term Σ ty_xlenbits * AST)) (exits : list (Term Σ ty_xlenbits)) : Prop :=
      CHeapSpec.run (cexec_triple_addr_tbl req instrs exitCond fuel ens tbl exits).

    Lemma rblock_verification_condition_tbl {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (instrs : gmap (bv xlenbits) AST)
      (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
      (tbl : list (Term Σ ty_xlenbits * AST)) (exits : list (Term Σ ty_xlenbits)) {w} :
      ⊢ RSat LogicalSoundness.RProp (w := w)
          (cblock_verification_condition_tbl req instrs exitCond fuel ens tbl exits)
          (sblock_verification_condition_tbl req tbl exits fuel ens w).
    Proof.
      unfold cblock_verification_condition_tbl, sblock_verification_condition_tbl.
      rsolve.
    Qed.

    #[export] Instance refine_compat_block_verification_condition_tbl {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (instrs : gmap (bv xlenbits) AST)
      (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
      (tbl : list (Term Σ ty_xlenbits * AST)) (exits : list (Term Σ ty_xlenbits)) {w} :
      RefineCompat (LogicalSoundness.RProp)
        (cblock_verification_condition_tbl req instrs exitCond fuel ens tbl exits) w
        (sblock_verification_condition_tbl req tbl exits fuel ens w) _ :=
      MkRefineCompat (rblock_verification_condition_tbl req instrs exitCond fuel ens tbl exits).

    Lemma rexec_triple_addr {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (instrs : gmap (bv xlenbits) AST) (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) {w} :
      ⊢ ℛ⟦RHeapSpec RUnit⟧
          (cexec_triple_addr req instrs exitCond fuel ens)
          (sexec_triple_addr req instrs exitCond fuel ens (w := w)).
    Proof.
      unfold cexec_triple_addr, sexec_triple_addr.
      rsolve.
      all: repeat (rewrite ?forgetting_trans; try iModIntro; rsolve).
    Qed.

    #[export] Instance refine_compat_exec_triple_addr {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (instrs : gmap (bv xlenbits) AST) (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) {w} :
      RefineCompat (RHeapSpec RUnit)
        (cexec_triple_addr req instrs exitCond fuel ens) w (sexec_triple_addr req instrs exitCond fuel ens (w := w)) _ :=
      MkRefineCompat (rexec_triple_addr req instrs exitCond fuel ens).

    Lemma rblock_verification_condition {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (instrs : gmap (bv xlenbits) AST) (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) {w} :
      ⊢ RSat LogicalSoundness.RProp (w := w)
          (cblock_verification_condition req instrs exitCond fuel ens)
          (sblock_verification_condition req instrs exitCond fuel ens w).
    Proof.
      unfold cblock_verification_condition, sblock_verification_condition.
      rsolve.
    Qed.

    #[export] Instance refine_compat_block_verification_condition {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (instrs : gmap (bv xlenbits) AST) (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) {w} :
      RefineCompat (LogicalSoundness.RProp)
        (cblock_verification_condition req instrs exitCond fuel ens) w (sblock_verification_condition req instrs exitCond fuel ens w) _ :=
      MkRefineCompat (rblock_verification_condition req instrs exitCond fuel ens).

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

    (* ptsto_instrs instrs: instruction ownership for a finite map from
       absolute address to instruction.  Each entry a ↦ i asserts ownership
       of instruction i at address a (SyncVal: the same instruction lives at
       the same address in both worlds).  Keying by absolute address makes the
       address arithmetic of the old list-based version unnecessary. *)
    Definition ptsto_instrs (instrs : gmap (bv xlenbits) AST) : iProp Σ :=
      ([∗ map] a ↦ i ∈ instrs, interp_ptsto_instr (SyncVal a) (SyncVal i))%I.

    Definition semTripleOneInstrStep (PRE : iProp Σ) (instr : AST) (POST : RelVal ty_word -> iProp Σ) (a : RelVal ty_word) : iProp Σ :=
      semTriple [env] (PRE ∗ (∃ v, lptsreg nextpc v) ∗ lptsreg pc a ∗ interp_ptsto_instr a (SyncVal instr) ∗ ⌜ secLeak a ⌝)
        (FunDef RiscvPmpProgram.step)
        (fun ret _ => (∃ an, lptsreg nextpc an ∗ lptsreg pc an ∗ POST an) ∗ interp_ptsto_instr a (SyncVal instr)  ∗ ⌜ secLeak a ⌝)%I.

    Definition semTripleCFG (PRE : RelVal ty_word -> iProp Σ) (instrs : gmap (bv xlenbits) AST) (exitCond : bv xlenbits -> bool) (fuel : nat) (POST : RelVal ty_word -> RelVal ty_word -> iProp Σ) : iProp Σ :=
      (∀ a,
         (PRE a ∗ pc ↦ᵣ a ∗ (∃ v, nextpc ↦ᵣ v) ∗ ptsto_instrs instrs) -∗
         (∀ an, ⌜match an with SyncVal v => exitCond v = true | NonSyncVal _ _ => True end⌝ ∗
                pc ↦ᵣ an ∗ (∃ v, nextpc ↦ᵣ v) ∗ ptsto_instrs instrs ∗ POST a an -∗ WP2_loop) -∗
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

    (* ptsto_instrs_lookup: extract the instruction stored at address v from
       ptsto_instrs, with a framing wand to restore it.  Used in
       sound_exec_cfg_addr to split out the instruction at the current PC,
       execute it, then restore the full map.  This is now a direct
       big_sepM_lookup_acc — the address arithmetic of the old list version
       (base + k*bytes_per_instr = v) is gone: the map key IS the address. *)
    Lemma ptsto_instrs_lookup (instrs : gmap (bv xlenbits) AST) (v : bv xlenbits) (i : AST) :
      instrs !! v = Some i →
      ptsto_instrs instrs ⊢
        interp_ptsto_instr (SyncVal v) (SyncVal i) ∗
        (interp_ptsto_instr (SyncVal v) (SyncVal i) -∗ ptsto_instrs instrs).
    Proof.
      intros Hlk. unfold ptsto_instrs.
      by apply (big_sepM_lookup_acc (fun a j => interp_ptsto_instr (SyncVal a) (SyncVal j)) instrs v i).
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
    Lemma sound_exec_cfg_addr {instrs exitCond fuel} (apc : RelVal ty_xlenbits) Φ (h : SCHeap) :
      cexec_cfg_addr instrs exitCond fuel apc Φ h →
      interpret_scheap h ∗ lptsreg pc apc ∗ (∃ v, lptsreg nextpc v) ∗ ptsto_instrs instrs ⊢
      (∀ an, ⌜match an with SyncVal v => exitCond v = true | NonSyncVal _ _ => True end⌝ ∗
             lptsreg pc an ∗ (∃ v, lptsreg nextpc v) ∗ ptsto_instrs instrs ∗
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
          * (* Execute branch: the instruction is looked up at address v
               directly (instrs !! v).  No alignment / base guard / index
               arithmetic: the map key IS the current PC. *)
            destruct (instrs !! v) as [i|] eqn:Hlk.
            ++ unfold bind, CHeapSpec.bind in Hexec.
               iIntros "(Hh & Hpc & Hnpc & Hinstrs) Hk".
               iPoseProof (ptsto_instrs_lookup instrs v Hlk with "Hinstrs") as "[Hinstr Hframe]".
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
        + cbn [cexec_cfg_addr ty.RVToOption CHeapSpec.error] in Hexec.
          contradiction.
    Qed.

    Lemma sound_cexec_triple_addr {Γ : LCtx} {pre post instrs} (exitCond : bv xlenbits -> bool) {fuel} {ι : Valuation Γ} :
      cexec_triple_addr pre instrs exitCond fuel post (fun _ _ => True) []%list ->
      ⊢ semTripleCFG (λ a : RelVal ty_word, asn.interpret pre (ι.[("a"::ty_xlenbits) ↦ a]) ∗ ⌜ secLeak a ⌝) instrs exitCond fuel
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

    Lemma sound_cblock_verification_condition {Γ pre post instrs exitCond fuel} :
      cblock_verification_condition pre instrs exitCond fuel post ->
      forall ι : Valuation Γ,
        ⊢ semTripleCFG (fun a => asn.interpret pre (ι.[("a"::ty_xlenbits) ↦ a])  ∗ ⌜ secLeak a ⌝)
          instrs exitCond fuel
          (fun a na => asn.interpret post (ι.[("a"::ty_xlenbits) ↦ a].[("an"::ty_xlenbits) ↦ na])).
    Proof.
      intros Hverif ι.
      exact (sound_cexec_triple_addr exitCond Hverif).
    Qed.

    Lemma sound_sblock_verification_condition {Γ pre post instrs exitCond fuel} :
      safeE (postprocess (sblock_verification_condition pre instrs exitCond fuel post wnil)) ->
      forall ι : Valuation Γ,
        ⊢ semTripleCFG (fun a => asn.interpret pre (ι.[("a"::ty_xlenbits) ↦ a])  ∗ ⌜ secLeak a ⌝)
          instrs exitCond fuel
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
(* TODO(gmap-pivot): This AnnotatedBlockVerification section is commented out
   because it relies on the OLD list-based ptsto_instrs (linear, consecutive
   addresses), which was replaced by the finite-map (gmap) ptsto_instrs in
   BlockVerificationDerived during the CFGVer absolute-pc / gmap pivot.  The
   name ptsto_instrs is now the gmap version, so this section no longer
   type-checks.  It is not used by any CFGVer end-to-end proof.  To restore
   it, give this section its OWN linear instruction-ownership predicate
   (e.g. ptsto_instrs_list : RelVal ty_word -> list AST -> iProp) and update
   all references (sound_exec_annotated_block_addr, semTripleAnnotatedBlock,
   etc.).  Original code preserved on branch wip/cfgver-base-offset-split. *)
(*
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

    (* AnnotatedBlockVerification is linear (annotated blocks execute
       sequentially at consecutive addresses), so it keeps the original
       list-based ptsto_instrs, shadowing the map-based one from
       BlockVerificationDerived.  This section is not used by CFGVer. *)
    Fixpoint ptsto_instrs (a : RelVal ty_word) (instrs : list AST) : iProp Σ :=
      match instrs with
      | cons inst insts => (interp_ptsto_instr a (SyncVal inst) ∗
                              ptsto_instrs (ty.liftUnOp (σ1 := ty.bvec _) (σ2 := ty.bvec _) (fun a => bv.add a bv_instrsize) a) insts)%I
      | nil => True%I
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
*)
