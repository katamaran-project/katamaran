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
(* Role: defines the symbolic CFG executor (sexec_cfg_addr_tbl) and the     *)
(* concrete mirror (cexec_cfg_addr), and proves its soundness up to the     *)
(* myWP2_loop chain in Adequacy.v.                                          *)
(*                                                                           *)
(* Key differences from BlockVer/Verifier.v:                                *)
(*   - Address-indexed lookup: each step fetches instr at PC/bytes_per_instr *)
(*     instead of advancing linearly.  Supports backward and forward jumps.  *)
(*   - exitCond parameter: execution halts when exitCond (current PC) = true *)
(*     OR when fuel runs out.  The angelic_binary at each step models the    *)
(*     nondeterministic choice between exiting and executing one more instr.  *)
(*   - fuel bound: the executor always terminates (no coinduction needed).   *)
(*                                                                           *)
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
     RiscvPmp.CFGVer.Spec
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
(* CFGVerificationDerived                                                  *)
(*                                                                           *)
(* The CFG verifier, structured in four subsections:                        *)
(*   Symbolic  — sexec_cfg_addr_tbl and related definitions                 *)
(*   Shallow   — cexec_cfg_addr (concrete, propositional)                   *)
(*   Relational — rexec_cfg_addr_tbl (the key soundness bridge via rsolve)  *)
(*   Soundness — ptsto_instrs + the pieces reused by Adequacy.v's myWP2    *)
(*     soundness chain (sound_exec_instruction, ptsto_instrs_lookup)       *)
(* ======================================================================== *)
Section CFGVerificationDerived.

  Import RiscvPmpCFGVerifExecutor.
  Import RiscvPmpCFGVerifShalExecutor.

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

    (* ================================================================ *)
    (* PARAMETRIC-BASE SUPPORT — READING GUIDE (Verifier.v side).        *)
    (*                                                                    *)
    (* WHY a term-table executor at all:  a gmap executor dispatching by  *)
    (* `instrs !! v` needs a CONCRETE address v.  With a symbolic base    *)
    (* `p : term_var`, the pc is a term like `p+8` with no concrete       *)
    (* value, so gmap lookup cannot fire.  The `_tbl` executor instead    *)
    (* keys instructions/exits by TERMS and dispatches by syntactic       *)
    (* term-matching (`Term_eqb (peval apc) (peval key)`) — which works   *)
    (* whether the base is a literal (`256+8` folds to `264`) or a        *)
    (* variable (`p+8` matches the key term `p+8`).  It is the only       *)
    (* symbolic executor (the earlier gmap-based `sexec_cfg_addr` was     *)
    (* dead — nothing else used it, since even the fixed-address          *)
    (* examples build their contract via the term-table VC — and was      *)
    (* removed, 2026-07-17).                                              *)
    (*                                                                    *)
    (* Follow the chain in this order:                                    *)
    (*   1. SITable/SETable, lookup_instr/is_exit  — term-keyed tables    *)
    (*      and peval-modulo matching (below).                            *)
    (*   2. sexec_cfg_addr_tbl / scfg_verification_condition_tbl —      *)
    (*      the symbolic executor + VC.                                   *)
    (*   3. itable_rel / etable_rel (applied at w := wlctx Σ)  — "the term *)
    (*      table faithfully mirrors the concrete gmap / exitCond at       *)
    (*      valuation ι".  This is the semantic bridge between the two     *)
    (*      worlds.                                                        *)
    (*   4. rexec_cfg_addr_tbl  — the gmap concrete executor is refined   *)
    (*      by the term-table symbolic executor UNDER faithfulness.       *)
    (*   5. cexec_triple_addr_tbl + refine_guard + rexec_triple_addr_tbl  *)
    (*      — the guarded VC refinement: faithfulness is an ASSUMED guard *)
    (*      on the concrete side, discharged end-to-end at the one        *)
    (*      valuation ι = [p ↦ of_N init_addr].                           *)
    (*   6. rcfg_verification_condition_tbl  — VC-level refinement,     *)
    (*      the entry point the soundness chain uses.                     *)
    (* The Examples.v side (exits_of_offs, itable_faith_of_list,          *)
    (* etable_faith_exits_of_offs, gen_contract_param/_rel, concretize_*, *)
    (* gen_contract_noninterferent_rel) discharges the guard and builds   *)
    (* the base-relative specs; see the reading guide there.              *)
    (* ================================================================ *)

    (* ---------------------------------------------------------------- *)
    (* Table-based executor variants (suffix `_tbl` throughout).  Design:  *)
    (* instruction dispatch is a syntactic term-table lookup,             *)
    (* `Term_eqb (peval apc) (peval key)`.  No gmap lookup on terms, no    *)
    (* offset arithmetic.  Tables are world-indexed (TYPE-level), since    *)
    (* their keys are symbolic terms that must be persisted across worlds *)
    (* as the executor steps.  Dropping the `_tbl` suffix (now that it's  *)
    (* the only executor) is tracked as cleanup in .claude/TODO.md.        *)
    (* ---------------------------------------------------------------- *)


    (* TODO: We need more insightful names, than SITable and SETable, it was very unclear to me what they meant at first. *)
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
    (* required: solver substitutions leave keys unnormalized             *)
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

    (* TODO: Rename this as to not reference the process, keep these lemmas and tests though. *)
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
        Term_eqb (peval (term_val ty_xlenbits (bv.of_N 260) : Term (wctx w1) ty_xlenbits))
          (peval (term_bvsub (term_bvadd (term_val ty_xlenbits (bv.of_N 8)) (term_val ty_xlenbits (bv.of_N 256)))  (term_val ty_xlenbits (bv.of_N 4))))
        = true.
      Proof. vm_compute. reflexivity. Qed.
    End Phase1SelfTests.

    (* TODO: rename sexec_cfg_addr_tbl to sexec_cfg_addr and drop all other *)
    (* _tbl references, now that the gmap-based sexec_cfg_addr it used to  *)
    (* be contrasted with has been removed (2026-07-17). *)
    (* sexec_cfg_addr_tbl: the symbolic CFG executor.  Fuel-guarded,       *)
    (* angelic_binary between exit/execute at each step, dispatching via   *)
    (* lookup_instr/is_exit — a syntactic term-table match modulo peval —  *)
    (* instead of a concrete-literal gmap lookup, so apc may stay symbolic  *)
    (* (`term_get_val` does not appear).  tbl/exits are threaded as        *)
    (* ARGUMENTS through the recursion since they are world-dependent,     *)
    (* persisted at each step via persist_itable / persist_etable. *)
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

    (* TODO: rename to drop the _tbl suffix, now that this is the only    *)
    (* symbolic triple/VC (the gmap-based sexec_triple_addr /              *)
    (* scfg_verification_condition were dead — nothing used them, since    *)
    (* even the fixed-address examples build their contract via this       *)
    (* table-based VC — and were removed, 2026-07-17). *)
    (* sexec_triple_addr_tbl / scfg_verification_condition_tbl: apply     *)
    (* symbolic execution to verify a Hoare triple for a program.  The     *)
    (* precondition can mention the address a where the program is loaded; *)
    (* the postcondition can additionally mention the address an where the *)
    (* pc points after execution.  scfg_verification_condition_tbl runs   *)
    (* sexec_triple_addr_tbl inside SHeapSpec.run (no leakcheck), giving a *)
    (* 𝕊 wnil proposition checked by `safeE (postprocess ...)`.  `tbl`/    *)
    (* `exits` are given at the CONTRACT context Σ (plain    *)
    (* lists of Σ-level terms, like `req`/`ens`), and moved into the       *)
    (* current world the same way `req` is: by applying the substitution  *)
    (* `ζ : Sub Σ w` (obtained from `demonic_ctx`'s δ, persisted forward   *)
    (* to the world where `a` lives) to each key term via `subst`. *)
    (* tbl/exits here are SITable/SETable at the world wlctx Σ (empty path
       condition over the contract context) -- definitionally the same
       lists (Term Σ ty_xlenbits * AST) / (Term Σ ty_xlenbits) they used to
       be typed as, since wctx (wlctx Σ) reduces to Σ by record projection. *)
    Definition subst_itable {Σ : LCtx} {w : World} (ζ : Sub Σ w)
        (tbl : SITable (wlctx Σ)) : SITable w :=
      List.map (fun '(t,i) => (subst t ζ, i)) tbl.
    Definition subst_etable {Σ : LCtx} {w : World} (ζ : Sub Σ w)
        (exits : SETable (wlctx Σ)) : SETable w :=
      List.map (fun t => subst t ζ) exits.

    Definition sexec_triple_addr_tbl {Σ : LCtx}
      (req : Assertion (Σ ▻ ("a"::ty_xlenbits)))
      (tbl : SITable (wlctx Σ)) (exits : SETable (wlctx Σ)) (fuel : nat)
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

    (* scfg_verification_condition_tbl: runs sexec_triple_addr_tbl inside *)
    (* SHeapSpec.run; same wnil shape, no leakcheck. *)
    Definition scfg_verification_condition_tbl {Σ : LCtx}
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
  (* rexec_cfg_addr_tbl: the key lemma, refining the gmap concrete executor  *)
  (*   by the term-table symbolic executor under table faithfulness.        *)
  (*   Proved by iInduction on fuel; the is_exit/lookup_instr double         *)
  (*   destruct is discharged sequentially across its four subgoals.        *)
  (*                                                                         *)
  (* RefineCompat instances export the relational lemmas for use by rsolve:  *)
  (*   refine_compat_cfg_verification_condition_tbl — key instance that    *)
  (*   lets rsolve close goals of the form                                  *)
  (*   RSat RProp (ccfg_vc_tbl ...) (scfg_vc_tbl ...)                     *)
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

    (* TODO: All this machinery surrounding SITable and gmap and SETable deserves its own section, module or even file. *)
    Definition itable_rel {w} (instrs : gmap (bv xlenbits) AST) (tbl : SITable w) : Pred w :=
      fun ι => List.Forall
        (fun p => exists v, inst (fst p) ι = ty.SyncVal v /\ instrs !! v = Some (snd p)) tbl.

    Definition etable_rel {w} (exitCond : bv xlenbits -> bool) (exits : SETable w) : Pred w :=
      fun ι => List.Forall
        (fun t => exists v,
           inst (T := fun Σ => Term Σ ty_xlenbits) t ι = ty.SyncVal v /\ exitCond v = true) exits.

    (* TODO: It feels like this does not belong here. Maybe in PartialEvalution or in instantiation. *)
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
    (* term-table symbolic executor, under table faithfulness.  Proved by   *)
    (* iInduction on fuel, boxed IH projected by                            *)
    (* forgetting_unconditionally_drastic; the four subgoals of the         *)
    (* is_exit/lookup_instr double destruct are discharged sequentially.    *)
    (* TODO: This proof was not written in the phylosophy of rsolve. *)
    (* It should be relatively easy with most of the complexity handled by rsolve. *)
    (* I suspect there are a few missing RefineCompat instances for tables. *)
    (* This is maybe a good proof golf target. *)
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
    (* itable_faith/etable_faith used to duplicate itable_rel/etable_rel's  *)
    (* List.Forall body verbatim, differing only in the tbl/exits parameter *)
    (* type (a plain list vs SITable/SETable) -- but those are the same     *)
    (* type at w := wlctx Σ (wctx (wlctx Σ) reduces to Σ).  Deduped         *)
    (* 2026-07-17: itable_faith/etable_faith removed entirely; every call   *)
    (* site (here, Tables.v, Results.v, EndToEnd.v, Adequacy.v) now calls    *)
    (* itable_rel/etable_rel directly at w := wlctx Σ. *)

    (* cexec_triple_addr_tbl: the concrete triple — right after picking the *)
    (* demonic valuation lenv, ASSUME itable_rel/etable_rel at lenv (i.e.,  *)
    (* table faithfulness w.r.t. the gmap, at w := wlctx Σ) before producing *)
    (* req and running the (still gmap-based) cexec_cfg_addr.  This is the  *)
    (* concrete side of the guarded VC refinement from the reading guide    *)
    (* above (step 5): the guard makes the triple hold vacuously at         *)
    (* valuations where the table doesn't match the gmap, and meaningfully  *)
    (* only at the one valuation the end-to-end proof discharges it at. *)
    Definition cexec_triple_addr_tbl {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (instrs : gmap (bv xlenbits) AST)
      (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
      (tbl : SITable (wlctx Σ)) (exits : SETable (wlctx Σ)) : CHeapSpec unit :=
      CHeapSpec.bind (CHeapSpec.demonic_ctx Σ) (fun lenv =>
      CHeapSpec.bind (CHeapSpec.lift_purespec (CPureSpec.assume_formula
          (itable_rel instrs tbl lenv /\ etable_rel exitCond exits lenv))) (fun _ =>
      CHeapSpec.bind (CHeapSpec.demonic _) (fun a =>
      CHeapSpec.bind (CHeapSpec.produce req lenv.["a"∷ty_xlenbits ↦ a]) (fun _ =>
      CHeapSpec.bind (cexec_cfg_addr instrs exitCond fuel a) (fun na =>
      CHeapSpec.consume ens lenv.["a"∷ty_xlenbits ↦ a].["an"∷ty_xlenbits ↦ na]))))).

    (* refine_guard: a concrete-side-only assume step.  Assuming more on   *)
    (* the concrete side weakens the concrete claim, which is the sound    *)
    (* direction for RHeapSpec refinement; the symbolic side is unchanged. *)
    (* Checked Solver.v and Refinement/Monads.v: no existing lemma covers  *)
    (* this one-sided (concrete-only) assume; `refine_assume_formula`      *)
    (* there assumes on BOTH sides.  Generic over RA/SA/CA — a candidate   *)
    (* to promote to Refinement/Monads.v if a second use site appears, but *)
    (* not moved now (core-theories churn is out of scope for this pass). *)
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

    (* Not a duplicate of forgetting_itable_rel above, despite the similar *)
    (* proof shape: that lemma commutes forgetting with persist_itable     *)
    (* given an EXISTING itable_rel hypothesis at the SAME world (SITable  *)
    (* on both sides); this one instead DERIVES itable_rel at world wb     *)
    (* from an itable_rel fact given at the contract context Σ' (i.e., at  *)
    (* w := wlctx Σ') via a substitution ζ.  Both are needed (used         *)
    (* together at the rexec_triple_addr_tbl call site below). *)
    Lemma itable_rel_of_faith_forget {Σ' : LCtx} {wa wb : World} (θ : Acc wa wb) (ζ : Sub Σ' wa)
        (instrs' : gmap (bv xlenbits) AST) (tbl' : SITable (wlctx Σ'))
        (ιΣ : NamedEnv RelVal Σ') :
      itable_rel instrs' tbl' ιΣ ->
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
        (exitCond' : bv xlenbits -> bool) (exits' : SETable (wlctx Σ'))
        (ιΣ : NamedEnv RelVal Σ') :
      etable_rel exitCond' exits' ιΣ ->
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
        { (* TODO: It feels like rsolve should be able to handle this, if you have the right RefineCompat instances. *)
          iPoseProof (itable_rel_of_faith_forget (acc_trans θ1 θ2) δ Hif with "Hδ") as "#Hi".
          iPoseProof (etable_rel_of_faith_forget (acc_trans θ1 θ2) δ Hef with "Hδ") as "#He".
          iApply (rexec_cfg_addr_tbl instrs exitCond fuel _ _ with "[$Hi $He]").
          iApply (refine_inst_persist with "Ha"). }
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

    Definition ccfg_verification_condition_tbl {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (instrs : gmap (bv xlenbits) AST)
      (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
      (tbl : list (Term Σ ty_xlenbits * AST)) (exits : list (Term Σ ty_xlenbits)) : Prop :=
      CHeapSpec.run (cexec_triple_addr_tbl req instrs exitCond fuel ens tbl exits).

    Lemma rcfg_verification_condition_tbl {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (instrs : gmap (bv xlenbits) AST)
      (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
      (tbl : list (Term Σ ty_xlenbits * AST)) (exits : list (Term Σ ty_xlenbits)) {w} :
      ⊢ RSat LogicalSoundness.RProp (w := w)
          (ccfg_verification_condition_tbl req instrs exitCond fuel ens tbl exits)
          (scfg_verification_condition_tbl req tbl exits fuel ens w).
    Proof.
      unfold ccfg_verification_condition_tbl, scfg_verification_condition_tbl.
      rsolve.
    Qed.

    #[export] Instance refine_compat_cfg_verification_condition_tbl {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (instrs : gmap (bv xlenbits) AST)
      (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
      (tbl : list (Term Σ ty_xlenbits * AST)) (exits : list (Term Σ ty_xlenbits)) {w} :
      RefineCompat (LogicalSoundness.RProp)
        (ccfg_verification_condition_tbl req instrs exitCond fuel ens tbl exits) w
        (scfg_verification_condition_tbl req tbl exits fuel ens w) _ :=
      MkRefineCompat (rcfg_verification_condition_tbl req instrs exitCond fuel ens tbl exits).

  End Relational.

  (* ====================================================================== *)
  (* Soundness scaffolding shared with the myWP2_loop chain in Adequacy.v.  *)
  (*                                                                         *)
  (* ptsto_instrs instrs: Iris predicate asserting instruction ownership     *)
  (*   for a finite map from absolute address to instruction (SyncVal: the   *)
  (*   same instruction lives at the same address in both worlds).           *)
  (*   NOTE: unlike BlockVer, the base address is SyncVal bv.zero (not       *)
  (*   parameterized), so all programs are assumed loaded at address 0.      *)
  (*                                                                         *)
  (* sound_exec_instruction / ptsto_instrs_lookup below are the two pieces   *)
  (* Adequacy.v reuses (qualified) to build sound_exec_cfg_addr_myWP2 and    *)
  (* the rest of the myWP2_loop soundness chain.  The WP2_loop-based chain   *)
  (* that used to live here (semTripleCFG, sound_exec_cfg_addr,              *)
  (* sound_cexec_triple_addr, sound_ccfg/scfg_verification_condition) was    *)
  (* dead — nothing required it — and has been removed; use the _myWP2      *)
  (* variants in Adequacy.v instead.                                         *)
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
      iApply (sound_stm foreignSemCFGVerif lemSemCFGVerif Hverif with "[] [$]").
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
       sound_exec_cfg_addr_myWP2 (Adequacy.v) to split out the instruction at
       the current PC, execute it, then restore the full map.  This is a
       direct big_sepM_lookup_acc — the address arithmetic of the old list
       version (base + k*bytes_per_instr = v) is gone: the map key IS the
       address. *)
    Lemma ptsto_instrs_lookup (instrs : gmap (bv xlenbits) AST) (v : bv xlenbits) (i : AST) :
      instrs !! v = Some i →
      ptsto_instrs instrs ⊢
        interp_ptsto_instr (SyncVal v) (SyncVal i) ∗
        (interp_ptsto_instr (SyncVal v) (SyncVal i) -∗ ptsto_instrs instrs).
    Proof.
      intros Hlk. unfold ptsto_instrs.
      by apply (big_sepM_lookup_acc (fun a j => interp_ptsto_instr (SyncVal a) (SyncVal j)) instrs v i).
    Qed.

  End Soundness.

End CFGVerificationDerived.
