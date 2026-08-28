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
(* CFGVer/Verifier.v — the SYMBOLIC CFG executor.                           *)
(*                                                                          *)
(* Defines safeE and Section Symbolic: sexec_cfg_addr and                   *)
(* scfg_verification_condition — address-indexed lookup (each step fetches  *)
(* the instr at PC/bytes_per_instr rather than advancing linearly, so       *)
(* backward and forward jumps both work), an exitCond parameter (execution  *)
(* halts when exitCond of the current PC holds OR fuel runs out; the        *)
(* angelic_binary at each step models that choice), and a fuel bound making *)
(* the executor total.                                                      *)
(*                                                                          *)
(* DELIBERATELY Iris-free. The concrete mirror (Section Shallow), the       *)
(* relational bridge (Section Relational, rexec_cfg_addr + RefineCompat)    *)
(* and the soundness scaffolding (Section Soundness, ptsto_instrs) all need *)
(* the binary Iris model and the shallow/refine executors, so they live in  *)
(* VerifierRel.v. Downstream, only Contracts.v needs this file (for safeE   *)
(* and scfg_verification_condition) — which is what keeps the examples off  *)
(* the Iris stack. DON'T re-add an Iris/Shallow require here.               *)
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
     Notations
     Semantics
     Bitvector
     Sep.Hoare
     Specification
     Symbolic.Propositions
     Symbolic.Solver
     Symbolic.Worlds
     MicroSail.SymbolicExecutor
     RiscvPmp.CFGVer.Spec
     RiscvPmp.Machine
     RiscvPmp.Sig.
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

(* ========================================================================= *)
(* Ghost annotations for CFGVer instructions.                               *)
(* ========================================================================= *)

(* Ghost annotation kinds.  Both are interpreted (sexec_ghost, below);
   neither is used by any example yet, so no VC changes.

   AnnotLemmaInvocation's `es` lives at the EMPTY program context [ctx]
   (no program variables in scope at an instruction boundary), which is
   also why Annot is not world-indexed and needs no persist. *)
Inductive Annot :=
  | AnnotDebugBreak
  | AnnotLemmaInvocation {Δ} (l : 𝑳 Δ) (es : NamedEnv (Exp [ctx]) Δ).

(* One instruction together with the ghost annotations attached to it.
   A PRODUCT, not a sum (`AnnotAST i | AnnotGhost a` was reverted at
   13eb91e0): a sum can represent a ghost with no instruction to attach
   to, which forced a grouping fold in table_of_list, a "trailing ghost
   is an error" case, and — if a ghost were given its own table entry —
   a lookup_instr that returns the ghost forever and can never reach the
   instruction at that address.

   `list Annot`, not `option Annot` (which is what 0c8fd8cf landed):
   more than one annotation per instruction is a real case — dump the
   heap AND abstract a term at the same pc, once AnnotLemmaInvocation
   returns in Phase 4 — and the recursion `option` was chosen to avoid
   costs nothing, because ghosts are interpreted by folding TRANSFORMERS
   over the list (see sexec_ghosts), not by building a bind chain.
   Those are different things; conflating them is what motivated the
   `option`. *)
Record AnnotInstr := MkAnnotInstr
  { ai_ghost_before : list Annot
  ; ai_instr        : AST
  ; ai_ghost_after  : list Annot
  }.

Definition strip (instrs : list AnnotInstr) : list AST :=
  List.map (fun ai => ai_instr ai) instrs.

(* Ghosts occupy no address, so stripping cannot change the program's length.
   Needed wherever a TRUSTED premise is stated over `strip instrs` while the
   caller's bound is over `instrs` (EndToEnd.v's length side conditions).
   Under the PRODUCT AnnotInstr this is just map_length; under the reverted SUM
   it would have been a real fact about the grouping fold. *)
Lemma strip_length (l : list AnnotInstr) : length (strip l) = length l.
Proof. apply List.length_map. Qed.

(* Coercions: wrap plain AST values in AnnotInstr with no ghosts, so that
   existing programs like cmovznz4_instrs : list AST still typecheck as
   list AnnotInstr without modification.

   NOT Local: Prelude.v exports this file (CFGVer/CLAUDE.md) and every
   Example/*.v needs these coercions active. A Local Coercion would never
   reach the examples. *)
(* `nil` spelled out rather than `[]`: list_scope is not opened until
   further down this file (and ctx.notations, re-imported via RiscvPmp.Sig,
   hijacks list notation until it is). *)
Coercion AST_AnnotInstr (a : AST) : AnnotInstr :=
  {| ai_ghost_before := nil; ai_instr := a; ai_ghost_after := nil |}.

Local Arguments List.cons {_} & _ _.

Coercion list_AST_AnnotInstr (l : list AST) : list AnnotInstr :=
  List.map AST_AnnotInstr l.

(* REQUIRED (same trap as Tables.v): RiscvPmp.Sig re-imports ctx.notations,
   whose `_ :: _` Binding notation hijacks list cons. Without this, pattern
   matches on AnnotInstr lists fail with "Found a constructor of inductive
   type Term while a constructor of list is expected". *)
Open Scope list_scope.

(* ======================================================================== *)
(* CFGVerificationDerived                                                  *)
(*                                                                           *)
(* The CFG verifier, structured in four subsections:                        *)
(*   Symbolic  — sexec_cfg_addr and related definitions                 *)
(*   Shallow   — cexec_cfg_addr (concrete, propositional)                   *)
(*   Relational — rexec_cfg_addr (the key soundness bridge via rsolve)  *)
(*   Soundness — ptsto_instrs + the pieces reused by Adequacy.v's myWP2    *)
(*     soundness chain (sound_exec_instruction, ptsto_instrs_lookup)       *)
(* ======================================================================== *)
Section CFGVerificationDerived.

  Import RiscvPmpCFGVerifExecutor.

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
    (* ================================================================== *)
    (* DebugAnnot: AnnotDebugBreak's payload — a (pathcondition, heap)     *)
    (* snapshot at one program point.                                     *)
    (*                                                                     *)
    (* WHY a payload is needed at all: the symbolic heap is an SHeapSpec   *)
    (* ACCUMULATOR, not part of the VC, so the only position it can        *)
    (* otherwise be observed at is the precondition boundary — and a fuel  *)
    (* truncation carries no state either (`error msg => False` in both    *)
    (* `safe` and `safe_debug`).  A debug node planted mid-run is the only *)
    (* way to ask "what does the heap look like HERE".                     *)
    (*                                                                     *)
    (* WHY AN ALIAS AND NOT A RECORD.  The framework's DebugAsn            *)
    (* (theories/Symbolic/Monads.v:71-101) already has exactly these two   *)
    (* fields WITH Subst/SubstLaws/OccursCheck #[export]ed — the three     *)
    (* instances `amsg.mk` requires — so a CFGVer record would be pure     *)
    (* duplication.  It has been written as one three times already (the   *)
    (* reverted sum-type attempt 2274a22b, BlockVer's DebugBlockver, and   *)
    (* once more here on 2026-08-21 before this was noticed).  Do not add  *)
    (* a fourth.                                                          *)
    (*                                                                     *)
    (* But the two are CONCEPTUALLY DISTINCT and expected to diverge, so   *)
    (* ghost code names the payload through this alias rather than saying  *)
    (* DebugAsn directly.  DebugAsn fires when the executor produces or    *)
    (* consumes an `asn.debug` node inside an ASSERTION (Monads.v:1028,    *)
    (* :1075) — its commented-out fields (program context, localstore) are *)
    (* what assertion debugging wants.  A ghost break fires at an          *)
    (* INSTRUCTION BOUNDARY chosen by whoever wrote the program, and would *)
    (* plausibly want the pc or which annotation fired.  Neither field set *)
    (* belongs in the other.  Fork here if that day comes.                 *)
    (*                                                                     *)
    (* `Notation` and not `Definition` so instance resolution needs no     *)
    (* unfolding: `Subst DebugAnnot` IS `Subst DebugAsn`, syntactically.   *)
    (* Caveat: an alias does not change what a dump PRINTS — the           *)
    (* constructor stays MkDebugAsn and the fields stay debug_asn_*, so in *)
    (* a vc_debug output an assertion debug and a ghost break are still    *)
    (* told apart only by position in the tree.  If Phase 3 finds that     *)
    (* ambiguous, THEN a distinct record earns its 25 lines.               *)
    (* ================================================================== *)
    Notation DebugAnnot := DebugAsn.

    (* exec_instruction_prologue i: the Hoare precondition for executing
       instruction i at address a, with np the INCOMING nextpc value.  Asserts:
         pc ↦ a, ptstoinstr a i (instruction ownership), nextpc ↦ np,
         secLeak a (PC is public → same instruction in both worlds).
       After execution, exec_instruction_epilogue i holds:
         pc ↦ an, ptstoinstr a i (unchanged), nextpc ↦ an, secLeak a, secLeak an
       The two assertions together form the frame for one `step` invocation.

       WHY np is a PARAMETER and not `asn.exist "an" ...` (which is what this
       was until 2026-07-31): the prologue is PRODUCED (sexec_instruction
       below), so an existential here becomes a fresh DEMONIC variable in wctx
       on EVERY step, and demonic variables are never unified away, so |wctx|
       grows linearly in steps.  Keeping it flat is worth doing on its own
       merits, but do NOT read this as the cost driver of loop examples: with
       both this and `encoded_instr` fixed at source, |wctx| is measured flat
       (a constant 20.6 live variables per node at every trip count) and
       `vm_compute` is STILL an exact quadratic.  The measured law is
       `work ~ (heap size) x (steps + steps^2)`; see PLAN-encoded-instr.md §9.

       A ∀-parameter is exactly as general as an existential (∀n.{nextpc ↦ n}c{Q}
       and {∃n.nextpc ↦ n}c{Q} are the same statement), so this costs no
       generality, and it is NOT the same as assuming nextpc = pc — which would
       be a real strengthening and was rejected.  The caller supplies a term it
       already holds: after any step the epilogue below gives pc = nextpc = an,
       so from step two onward it is just apc'.  Only the first step needs a
       fresh variable, introduced ONCE in sexec_triple_addr.

       The incoming value is genuinely dead, for the record: fun_step
       (Machine.v) writes `nextpc := pc +ᵇ 4` BEFORE `call execute`.  nextpc IS
       read afterwards — execute_RISCV_JAL/JALR for the link register, and
       tick_pc — but always after that write.

       Full rationale, including why the world-GC that this replaces could not
       be proved sound: PLAN-nextpc-param.md. *)
    Definition exec_instruction_prologue (i : AST) :
      Assertion ([ctx] ▻ ("a":: ty_xlenbits) ▻ ("np":: ty_xlenbits)
                      ▻ ("w":: ty_word)) :=
      pc     ↦ term_var "a" ∗
      asn.chunk (chunk_user ptstoinstr [term_var "a"; term_var "w"; term_val ty_ast i]) ∗
      nextpc ↦ term_var "np" ∗
      asn.formula (formula_secLeak (term_var "a"))
    .

    Definition exec_instruction_epilogue (i : AST) :
      Assertion ([ctx] ▻ ("a":: ty_xlenbits) ▻ ("an":: ty_xlenbits)
                      ▻ ("w":: ty_word)) :=
      pc     ↦ term_var "an" ∗
      asn.chunk (chunk_user ptstoinstr [term_var "a"; term_var "w"; term_val ty_ast i]) ∗
      nextpc ↦ term_var "an" ∗
      asn.formula (formula_secLeak (term_var "a")) ∗
      asn.formula (formula_secLeak (term_var "an"))
    .

    (* inputs:
     * - i: instruction to be executed
     * - a: term representing current pc value.
     * - np: term representing the INCOMING nextpc value (see the prologue's
     *   comment for why this is a parameter rather than an existential).
     * output: term representing nextpc value after executing the instruction.
     *)
    Definition sexec_instruction (i : AST) :
      ⊢ STerm ty_xlenbits -> STerm ty_xlenbits -> STerm ty_word ->
        SHeapSpec (STerm ty_xlenbits) :=
      let inline_fuel := 10%nat in
      fun _ a np w =>
        ⟨ θ1 ⟩ _  <- produce
                       (exec_instruction_prologue i)
                       [env].["a"∷_ ↦ a].["np"∷_ ↦ np].["w"∷_ ↦ w] ;;
        ⟨ θ2 ⟩ _  <- evalStoreSpec (sexec default_config inline_fuel (FunDef step) _) [env] ;;
        ⟨ θ3 ⟩ na <- angelic None _ ;;
        let a3 := persist__term a (θ1 ∘ θ2 ∘ θ3) in
        let w3 := persist__term w (θ1 ∘ θ2 ∘ θ3) in
        ⟨ θ4 ⟩ _  <- consume
                       (exec_instruction_epilogue i)
                       [env].["a"∷_ ↦ a3].["an"∷_ ↦ na].["w"∷_ ↦ w3] ;;
        pure (persist__term na θ4).

    (* ================================================================ *)
    (* PARAMETRIC-BASE SUPPORT — READING GUIDE (Verifier.v side).        *)
    (*                                                                    *)
    (* WHY a term-table executor at all:  a gmap executor dispatching by  *)
    (* `instrs !! v` needs a CONCRETE address v.  With a symbolic base    *)
    (* `p : term_var`, the pc is a term like `p+8` with no concrete       *)
    (* value, so gmap lookup cannot fire.  This term-table executor      *)
    (* instead keys instructions/exits by TERMS and dispatches by         *)
    (* syntactic term-matching (`Term_eqb (peval apc) (peval key)`) —     *)
    (* which works whether the base is a literal (`256+8` folds to        *)
    (* `264`) or a variable (`p+8` matches the key term `p+8`).  It is     *)
    (* the only symbolic executor.                                        *)
    (*                                                                    *)
    (* Follow the chain in this order:                                    *)
    (*   1. SInstrTable/SExitTable, lookup_instr/is_exit — term-keyed tables *)
    (*      and peval-modulo matching (below).                            *)
    (*   2. sexec_cfg_addr / scfg_verification_condition —      *)
    (*      the symbolic executor + VC.                                   *)
    (*   3. itable_rel / etable_rel (applied at w := wlctx Σ)  — "the term *)
    (*      table faithfully mirrors the concrete gmap / exitCond at       *)
    (*      valuation ι".  This is the semantic bridge between the two     *)
    (*      worlds.                                                        *)
    (*   4. rexec_cfg_addr  — the gmap concrete executor is refined   *)
    (*      by the term-table symbolic executor UNDER faithfulness.       *)
    (*   5. cexec_triple_addr + refine_guard + rexec_triple_addr  *)
    (*      — the guarded VC refinement: faithfulness is an ASSUMED guard *)
    (*      on the concrete side, discharged end-to-end at the one        *)
    (*      valuation ι = [p ↦ of_N init_addr].                           *)
    (*   6. rcfg_verification_condition  — VC-level refinement,     *)
    (*      the entry point the soundness chain uses.                     *)
    (* The Examples.v side (exits_of_offs, itable_faith_of_list,          *)
    (* etable_faith_exits_of_offs, gen_contract_param/_rel, concretize_*, *)
    (* gen_contract_noninterferent_rel) discharges the guard and builds   *)
    (* the base-relative specs; see the reading guide there.              *)
    (* ================================================================ *)

    (* ---------------------------------------------------------------- *)
    (* Table-based executor variants.  Design: instruction dispatch is a  *)
    (* syntactic term-table lookup, `Term_eqb (peval apc) (peval key)`.   *)
    (* No gmap lookup on terms, no offset arithmetic.  Tables are          *)
    (* world-indexed (TYPE-level), since their keys are symbolic terms     *)
    (* that must be persisted across worlds as the executor steps.        *)
    (* ---------------------------------------------------------------- *)


    (* SInstrTable / SExitTable: the symbolic analogues of the gmap `instrs` and *)
    (* function `exitCond` above -- a table of (address term, instruction) *)
    (* pairs, and a list of address terms marking exits.  This is the      *)
    (* CONTRACT-LEVEL shape: what table_of_list builds, what itable_rel    *)
    (* relates to the gmap, and what TablesRel.v's faith lemmas discharge. *)
    Definition SInstrTable : TYPE :=
      fun w => list (Term (wctx w) ty_xlenbits * AnnotInstr).

    Definition SExitTable : TYPE :=
      fun w => list (Term (wctx w) ty_xlenbits).

    (* SInstrTableW: the EXECUTOR's shape — SInstrTable with a raw instruction
       WORD term added as a middle column.  sexec_cfg_addr runs on this; nothing
       outside this file's Section Symbolic and VerifierRel.v's mirror of it ever
       sees it, which is why table_of_list / Contracts.v / GenContract.v / the
       examples are all untouched by the word threading.

       WHY the word is a COLUMN rather than a parallel address→word table:
       one dispatch point.  A parallel table makes every step do two lookups
       that must agree, forcing a "tables disagree" error case the executor
       cannot rule out and the refinement proof must carry, plus a duplicate
       wtable_rel / persist / subst / faith family alongside itable_rel's.
       Fusing makes disagreement impossible by construction.  (Both shapes were
       implemented; fused is smaller.)

       WHY the word must be carried at all: `encoded_instr` used to be a
       per-step existential in fetch's postcondition, hence a fresh DEMONIC
       variable in wctx on every step, and |wctx| growth is the measured
       dominant cost of loop examples.  It cannot be eliminated in place —
       pure_decode is an uninterpreted Axiom (Machine.v:147) with no
       injectivity, so the word is genuinely not determined by the
       instruction and must be supplied from outside.  The words are
       introduced ONCE for the whole program (sexec_triple_addr below), not
       once per execution step and — since 2026-08-24 — not once per address
       either: there is a SINGLE demonic variable of width word * n and each
       address's word is a bvtake/bvdrop SLICE of it, so a loop re-executing
       the same addresses reuses the same slices every trip.  |Σ| for
       br_divrem is 15 rather than 63 as a result.  PLAN-encoded-instr.md for
       the per-step -> per-address step, PLAN-annotinstr.md's 2026-08-24 log
       for the per-address -> single-variable step. *)
    Definition SInstrTableW : TYPE :=
      fun w => list (Term (wctx w) ty_xlenbits * Term (wctx w) ty_word * AnnotInstr).

    Definition persist_itable {w1 w2} (θ : w1 ⊒ w2) : SInstrTable w1 -> SInstrTable w2 :=
      List.map (fun '(t,i) => (persist__term t θ, i)).
    Definition persist_itableW {w1 w2} (θ : w1 ⊒ w2) : SInstrTableW w1 -> SInstrTableW w2 :=
      List.map (fun '(t,x,i) => (persist__term t θ, persist__term x θ, i)).
    Definition persist_etable {w1 w2} (θ : w1 ⊒ w2) : SExitTable w1 -> SExitTable w2 :=
      List.map (fun t => persist__term t θ).

    (* Chunk GC.  Note there is NO justification test of any kind here:    *)
    (* this unconditionally drops every encodes_instr chunk.  That is safe *)
    (* because it fails in the SAFE DIRECTION — dropping leaves the        *)
    (* executor with strictly less, so if a later step needs the chunk its *)
    (* consume_chunk fails and the VC becomes unprovable.  An unjustified  *)
    (* drop costs completeness, never soundness.                          *)
    (*                                                                    *)
    (* Why encodes_instr specifically, and why this is NEEDED rather than  *)
    (* merely nice: encodes_instr is DUPLICABLE (Sig.v), and consuming a   *)
    (* duplicable chunk leaves it in the heap (Chunks.v,                   *)
    (* try_consume_chunk_exact).  So one accumulates per step and never    *)
    (* leaves, each keeping its own "encoded_instr" variable alive in the  *)
    (* heap root — which is exactly what blocks gc_dead_roots below.  The  *)
    (* two GCs are therefore superadditive, not independent wins: this one *)
    (* is what makes "encoded_instr" pass the occurs check at all.         *)
    Definition is_encodes_instr {V : Ty -> Set} (c : GChunk V) : bool :=
      match c with
      | chunk_user encodes_instr _ => true
      | _                          => false
      end.

    Definition gc_heap {Σ} (h : SHeap Σ) : SHeap Σ :=
      List.filter (fun c => negb (is_encodes_instr c)) h.

    Definition chunk_gc {w : World} : SHeapSpec Unit w :=
      fun POST h => POST w acc_refl tt (gc_heap h).

    (* Symbolic mirror of VerifierRel.v's cgc_binds_heap: chunk_gc's bind    *)
    (* rewrites the heap and never moves the world (acc_refl), so binding   *)
    (* it just applies the continuation box unconditionally (T) to the      *)
    (* filtered heap.  Reflexivity because chunk_gc's own acc_refl already  *)
    (* makes SHeapSpec.bind's world bookkeeping collapse away definitionally. *)
    (* USE THIS to eliminate chunk_gc's bind BEFORE letting rsolve near the *)
    (* NEXT bind in the sequence — otherwise the generic RefineCompat/      *)
    (* rsolve machinery treats chunk_gc as if it could move to an arbitrary *)
    (* fresh world, and the resulting (spurious) extra world's accessibility *)
    (* doesn't associate with the rest on the nose (Acc composition isn't   *)
    (* definitionally associative), stalling the proof. *)
    Lemma gc_binds_heap {A w} (f : Box (Impl Unit (SHeapSpec A)) w)
        (Φ : Box (Impl A (Impl (fun w' => SHeap w') (fun w' => 𝕊 w'))) w) (h : SHeap w) :
      SHeapSpec.bind chunk_gc f Φ h = T f tt Φ (gc_heap h).
    Proof. reflexivity. Qed.

    (* ================================================================== *)
    (* Ghost annotations: sexec_ghost interprets ONE annotation,           *)
    (* sexec_ghosts runs an instruction's ghost list in order.             *)
    (*                                                                     *)
    (* Both are ORDINARY SHeapSpec ACTIONS, bound into sexec_cfg_addr's    *)
    (* chain with ⟨θ⟩ _ <- like every other step, and declared with an     *)
    (* implicit {w : World} rather than ⊢ (chunk_gc's shape — see          *)
    (* core-executor-internals for why a niladic ⊢-typed action fails to   *)
    (* elaborate as a bind action).                                        *)
    (*                                                                     *)
    (* THIS FILE PREVIOUSLY USED A Box -> Box TRANSFORMER with a           *)
    (* continuation-nested call site, on the belief that a bound debug     *)
    (* differed from a wrapping one.  It does not: `bind (debug msg (pure  *)
    (* tt)) f` and `debug msg (f …)` are the SAME term, for exactly the    *)
    (* reason gc_binds_heap above holds by reflexivity — `pure` and        *)
    (* `debug` bind at acc_refl, so bind's world bookkeeping collapses     *)
    (* away (checked directly: `reflexivity` closes it in 2 ms).  The      *)
    (* transformer bought nothing and cost readability plus a              *)
    (* guard-checker risk (the recursive call left tail position).          *)
    (*                                                                     *)
    (* What IS true, and is the only real asymmetry: `debug` has no        *)
    (* concrete content — CHeapSpec.debug = fun m => m, the IDENTITY       *)
    (* (theories/Shallow/Monads.v:1112) — whereas call_lemma does.  So on  *)
    (* the RELATIONAL side the debug case cannot go through the ready-made *)
    (* refine_compat_debug (theories/Refinement/Monads.v:1683,1693), which *)
    (* is stated for debug as a transformer.  The lemma case binds on both *)
    (* sides and rsolve dispatches it through ordinary refine_bind (main's *)
    (* BlockVer/PartialVerifier.v closes it with `iApply "IHb"; rsolve`).  *)
    (* Phase 2 therefore needs an INDUCTIVE lemma over an arbitrary ghost  *)
    (* list — see the note on ghost_binds_nil below for why a rewrite in   *)
    (* gc_binds_heap's style cannot substitute for it.                     *)
    (*                                                                     *)
    (* Caveat kept from the reverted attempt (2274a22b), which also used   *)
    (* the action shape: its rexec_ghost hung at compile for 300 s+ and    *)
    (* the root cause was never found.  That risk lives in Phase 2 either  *)
    (* way — the term here is the same under both shapes — so it is not a  *)
    (* reason to distort this definition.                                  *)
    (*                                                                     *)
    (* PHASE 2 OBLIGATION: cexec_cfg_addr must mirror the LEMMA case (not   *)
    (* the debug one).  Nothing needs a new LEnv entry — these invoke       *)
    (* EXISTING lemmas — so there is no soundness debt here, only mirroring. *)
    (*                                                                     *)
    (* FUTURE-PROOFING (checked 2026-08-21, no change needed).  Two further *)
    (* annotation kinds have been discussed, and BOTH fit this signature as *)
    (* it stands — do not widen it for them:                               *)
    (*  - DROP CHUNKS (a user-directed chunk_gc).  Just another action,     *)
    (*    like chunk_gc itself.  Sound for ANY chunk by affineness of iProp *)
    (*    (a fold_right of ∗ can discard a conjunct) — see PLAN-encoded-    *)
    (*    instr.md §11, whose refine_chunk_gc/inst_gc_heap are audited      *)
    (*    Closed under the global context.  So it needs NO LEnv entry and   *)
    (*    no per-use soundness proof; the price is completeness, and it     *)
    (*    fails loudly at the next consume rather than silently.            *)
    (*  - DROP A DEAD LOGICAL VARIABLE.  *** TRIED IN FULL AND CLOSED        *)
    (*    NEGATIVE 2026-08-25.  DO NOT REOPEN WITHOUT READING                *)
    (*    plans/PLAN-lvar-drop.md, which records FIVE verdicts in one day    *)
    (*    and the proved dichotomy that ends them. ***                       *)
    (*                                                                       *)
    (*    The idea is semantically FINE: a variable occurring nowhere in the *)
    (*    present state can never reappear, because every future term is     *)
    (*    built from present ones, and occurs_check                          *)
    (*    (Symbolic/OccursCheck.v:56) decides that on data.  What defeats it *)
    (*    is the MODALITY.  `assuming` (Worlds.v:755) quantifies over the    *)
    (*    FIBRE of an accessibility, and the fibre size IS the freedom the   *)
    (*    accessibility grants.  Shrinking the world needs a substitution    *)
    (*    (acc_subst_right is the only way in), which needs a witness, and   *)
    (*    there are only two kinds:                                          *)
    (*      * a DUMMY value: fibre EMPTY at the generic i, so the hypothesis *)
    (*        is vacuous and the concrete goal is unreachable.               *)
    (*      * the FRESHLY MINTED variable: fibre non-empty, so the crux is   *)
    (*        provable (zz_fresh_witness, Qed) -- but SINGLETON.  zz_pins    *)
    (*        (Qed) shows every fibre element assigns the fresh variable the *)
    (*        value i(x), so the drop consumes exactly the freedom the mint  *)
    (*        created.  It is a RENAME.                                      *)
    (*    A havoc's shallow mirror is a demonic forall w, r |-> w, and       *)
    (*    refining that needs the symbolic side to cover every w.  A pinned  *)
    (*    fibre cannot.  Compare assuming_acc_snoc_right (UnifLogic.v:1248), *)
    (*    where a bare mint gives a genuine forall over ALL values.          *)
    (*                                                                       *)
    (*    SO: within the existing Acc machinery you cannot both shrink Sigma *)
    (*    and grant freedom.  Any fix is a NEW ACCESSIBILITY in Worlds.v     *)
    (*    whose `assuming` is forgetting-based rather than fibre-based --    *)
    (*    a framework change, not a client-side trick, and not something to  *)
    (*    attempt from this file.                                            *)
    (*                                                                       *)
    (*    THE HEURISTIC WORTH KEEPING, for any future question of this kind: *)
    (*    compute the FIBRE of the accessibility first -- empty, singleton   *)
    (*    or full.  All five verdicts on this question would have been       *)
    (*    settled immediately by asking that, and four rounds of reasoning   *)
    (*    settled none of them.                                              *)
    (*                                                                       *)
    (*    Motivation, still valid, and the measured alternative: an          *)
    (*    abstraction lemma shrinks terms but leaves its old binders in      *)
    (*    Sigma (demonicv_prune, Propositions.v:1175, collapses only on      *)
    (*    `block`), and variable count is quadratic in lookup cost           *)
    (*    (diagnostics/lvar-lookup-cost-drivers.md).  What DOES pay, and is  *)
    (*    landed: havoc fewer registers -- 2.66x at n=16, and it reaches     *)
    (*    br_divrem's real 31 trips (diagnostics/havoc-abstraction-          *)
    (*    payoff.md 8).                                                      *)
    (*                                                                       *)
    (*    Keep the contrast with DROP CHUNKS above: discarding a RESOURCE is *)
    (*    sound for any chunk by affineness and fails loudly at the next     *)
    (*    consume, whereas discarding a BINDER is sound only under the       *)
    (*    occurs_check and, without it, silently changes which statement was *)
    (*    proved.  The check is not bookkeeping; it is the proof.            *)
    (* ================================================================== *)
    Definition sexec_ghost (a : Annot) {w : World} : SHeapSpec Unit w :=
      match a with
      | AnnotDebugBreak =>
          debug
            (fun (h0 : SHeap w) =>
               amsg.mk {| debug_asn_pathcondition := wco w
                        ; debug_asn_heap          := h0 |})
            (pure tt)
      | AnnotLemmaInvocation l es =>
          (* PHASE 4 SPIKE (branch issue/annot-havoc-spike): this case is now
             REAL on the symbolic side only.  It was an `error` stub whose
             comment recorded the exact body to write, which is what is
             written here — LEnv QUALIFIED, because MakeExecutor does not
             re-export its Specification argument (Spec.v:720/723) and a bare
             `LEnv` fails under `make` while rocq_compile_file's dune fallback
             accepts it.  `es` lives at the empty program context, so the
             store passed to seval_exps is `[env]`.

             *** THE TWO SIDES ARE DELIBERATELY OUT OF SYNC ON THIS BRANCH. ***
             VerifierRel.v's cexec_ghost still returns `pure tt` and
             Adequacy.v still rewrites with cexec_ghosts_pure, so the HEAVY
             branch (SpecIris → … → Results) does NOT build here.  That is
             intentional and bounded: the spike measures whether a havoc at a
             loop head resets br_divrem's 10.5x/trip term growth, and a dump
             needs no VC proof, no refinement and no adequacy — only the light
             branch (Spec → Verifier → Tables → Contracts → GenContract →
             Example files).  Making the concrete side real without the soundness
             work is the mistake that produced the 2026-08-21 Adequacy blocker
             (a symbolic `error` refines anything; `pure tt` does not).  If
             this spike pays off, Phase 4 proper resyncs both sides:
             cexec_ghost calls CHeapSpec.call_lemma, rexec_ghost uses the
             ready-made refine_compat_call_lemma (Refinement/Monads.v:1875),
             and cexec_ghosts_pure is DELETED in favour of an inductive
             sound_cexec_ghosts built from call_lemma_sound
             (MicroSail/ShallowSoundness.v:91) + lemSemCFGVerif
             (SpecIris.v:364), following iris_rule_stm_lemmak's three-line
             discharge (BinaryInstance.v:196). *)
          call_lemma (RiscvPmpCFGVerifSpec.LEnv l) (seval_exps [env] es)
      end.

    (* Recurses in list order, so the first annotation runs first.  `nil` is
       `pure tt`, whose bind collapses definitionally — see ghost_binds_nil
       below, which is what makes cost-neutrality for unannotated programs a
       checked fact rather than an assertion. *)
    Fixpoint sexec_ghosts (gs : list Annot) {w : World} : SHeapSpec Unit w :=
      match gs with
      | nil      => pure tt
      | a :: gs' => ⟨ θ ⟩ _ <- sexec_ghost a ;; sexec_ghosts gs'
      end.

    (* A SELF-TEST, not machinery — nothing consumes it.  It pins the      *)
    (* migration's central cost claim: an instruction with no ghosts       *)
    (* contributes NOTHING to the term, because binding `sexec_ghosts nil` *)
    (* is definitionally the same as not binding at all.  That is why all  *)
    (* 12 existing examples' VCs are untouched.                            *)
    (*                                                                     *)
    (* Do NOT mistake this for gc_binds_heap's counterpart.  gc_binds_heap *)
    (* works as a rewrite in rexec_cfg_addr because `chunk_gc` is a CLOSED *)
    (* term, so one equation covers every use.  `sexec_ghosts` is applied  *)
    (* to `ai_ghost_before ai` with `ai` an OPAQUE variable coming out of  *)
    (* lookup_instr, so in the refinement proof the ghost list is          *)
    (* ARBITRARY and no finite set of instances can discharge it.  Phase 2 *)
    (* needs an INDUCTIVE relational lemma over `gs` (rexec_ghosts) — the  *)
    (* one that hung at 2274a22b.  Corollary worth stating plainly:        *)
    (* sexec_cfg_addr's shape has changed FOR THE PROOF whether or not any *)
    (* program ever writes a ghost; only the computed VC is unaffected.    *)
    Example ghost_binds_nil {A w} (f : Box (Impl Unit (SHeapSpec A)) w)
        (Φ : Box (Impl A (Impl (fun w' => SHeap w') (fun w' => 𝕊 w'))) w)
        (h : SHeap w) :
      SHeapSpec.bind (sexec_ghosts nil) f Φ h = T f tt Φ h.
    Proof. reflexivity. Qed.

    (* lookup_instr / is_exit: syntactic-modulo-peval matching of the     *)
    (* current pc term against the table keys.  `peval` on BOTH sides is  *)
    (* required: solver substitutions leave keys unnormalized             *)
    (* (e.g. `8 ⊕ 256`) while the semantics-produced pc is normalized      *)
    (* (`264`); peval reconciles the two before the syntactic Term_eqb    *)
    (* comparison.  Do not drop either peval call. *)
    (* Returns the word term AND the instruction: one lookup, so the two    *)
    (* can never disagree. *)
    (* NB an entry is ((addr, word), ast), so the key projection needs the   *)
    (* three-place pattern `'(t,_,_)`, not `'(t,_)`. *)
    Definition lookup_instr {w} (tbl : SInstrTableW w)
        (apc : STerm ty_xlenbits w) : option (Term (wctx w) ty_word * AnnotInstr) :=
      option_map (fun '(_,x,i) => (x,i))
        (List.find (fun '(t,_,_) => Term_eqb (peval apc) (peval t)) tbl).
    Definition is_exit {w} (exits : SExitTable w)
        (apc : STerm ty_xlenbits w) : bool :=
      List.existsb (fun t => Term_eqb (peval apc) (peval t)) exits.

    (* --- Self-tests (cheap sanity anchors for lookup_instr / is_exit /   *)
    (* peval; NOT part of the soundness chain). *)
    Section TableLookupSelfTests.
      Let w1 : World := wlctx ([ctx] ▻ "p"∷ty_xlenbits).
      Let p1 : Term (wctx w1) ty_xlenbits := term_var "p".
      Let instrA : AST := RTYPE (bv.of_N 1) (bv.of_N 0) (bv.of_N 2) RISCV_SUB.
      Let instrB : AST := RTYPE (bv.of_N 2) (bv.of_N 1) (bv.of_N 0) RISCV_SUB.
      Let wA : Term (wctx w1) ty_word := term_val ty_word (bv.of_N 11).
      Let wB : Term (wctx w1) ty_word := term_val ty_word (bv.of_N 22).
      Let tbl1 : SInstrTableW w1 :=
        [ (p1, wA, AST_AnnotInstr instrA)
        ; (term_bvadd (term_val ty_xlenbits (bv.of_N 4)) p1, wB, AST_AnnotInstr instrB)
        ]%list.

      (* pc = 4 ⊕ p matches the second table entry, yielding ITS word too. *)
      Example lookup_instr_hit :
        lookup_instr tbl1 (term_bvadd (term_val ty_xlenbits (bv.of_N 4)) p1)
        = Some (wB, AST_AnnotInstr instrB).
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
    End TableLookupSelfTests.

    (* sexec_cfg_addr: the symbolic CFG executor.  Fuel-guarded,       *)
    (* angelic_binary between exit/execute at each step, dispatching via   *)
    (* lookup_instr/is_exit — a syntactic term-table match modulo peval —  *)
    (* instead of a concrete-literal gmap lookup, so apc may stay symbolic  *)
    (* (`term_get_val` does not appear).  tbl/exits are threaded as        *)
    (* ARGUMENTS through the recursion since they are world-dependent,     *)
    (* persisted at each step via persist_itable / persist_etable.          *)
    (* anp: the current nextpc value, threaded rather than re-quantified    *)
    (* per step (exec_instruction_prologue's comment says why).  In every   *)
    (* recursive call it and the pc are the SAME term apc', because the     *)
    (* epilogue establishes pc = nextpc = an after each step; they are      *)
    (* separate parameters only so the FIRST step, which genuinely does not *)
    (* know nextpc, can differ. *)
    (* ================================================================== *)
    (* PHASE 3 (PLAN-dropk.md §6): the dead-logical-variable liveness       *)
    (* computation and the drop loop.                                      *)
    (*                                                                     *)
    (* NOT YET WIRED INTO sexec_cfg_addr — that is Phase 4, and it changes  *)
    (* the VC, which breaks rexec_cfg_addr until Phase 5 re-pairs it.       *)
    (* Everything here is dead code today and the gate is green with it.    *)
    (*                                                                     *)
    (* The plan warned that this needs a DEPENDENT FOLD (each step's type   *)
    (* mentioning the previous step's smaller context).  It does not, and   *)
    (* avoiding it is the whole shape below: rather than computing a SET of *)
    (* dead variables and removing them together, `drop_dead` finds ONE,    *)
    (* drops it as a single step, and RE-SCANS at the new world.  Recursion *)
    (* is on fuel; nothing is dependently folded.                           *)
    (* ================================================================== *)

    (* Enumerate a context with its In-proofs.  Also not a dependent fold:   *)
    (* every proof in the result lives at the one fixed Γ.                   *)
    Fixpoint all_ins (Γ : LCtx) : list (sigT (fun b => (b ∈ Γ)%katamaran)) :=
      match Γ with
      | ctx.nil       => List.nil
      | ctx.snoc Δ b0 =>
          cons (existT b0 ctx.in_zero)
            (List.map (fun p => existT (projT1 p) (ctx.in_succ (projT2 p))) (all_ins Δ))
      end.

    Definition oc_ok {AT} `{OccursCheck AT} {Σ} {b}
        (bIn : (b ∈ Σ)%katamaran) (a : AT Σ) : bool :=
      match occurs_check bIn a with Some _ => true | None => false end.

    (* SInstrTableW / SExitTable are bespoke tuple-lists with no OccursCheck
       instance, so the check is spelled out over their TERM columns rather
       than adding instances to theories/.  The AnnotInstr payload is
       world-independent and cannot mention a logical variable. *)
    Definition itableW_free {w : World} {b} (bIn : (b ∈ w)%katamaran)
        (tbl : SInstrTableW w) : bool :=
      List.forallb (fun e => match e with (t, x, _) =>
                      oc_ok (AT := STerm ty_xlenbits) bIn t
                      && oc_ok (AT := STerm ty_word) bIn x end) tbl.

    Definition etable_free {w : World} {b} (bIn : (b ∈ w)%katamaran)
        (exits : SExitTable w) : bool :=
      List.forallb (fun t => oc_ok (AT := STerm ty_xlenbits) bIn t) exits.

    (* ALL the roots.  `trans` is the one that is easy to forget and the one
       whose omission would be UNSOUND rather than merely incomplete — see
       sexec_cfg_addr's comment below and PLAN-dropk.md §4bis. *)
    Definition var_dead {Σ0 : LCtx} {w : World} {b}
        (bIn : (b ∈ w)%katamaran)
        (trans : Sub Σ0 w) (tbl : SInstrTableW w) (exits : SExitTable w)
        (apc anp : Term (wctx w) ty_xlenbits) (wd : Term (wctx w) ty_word)
        (h : SHeap (wctx w)) : bool :=
      oc_ok (AT := PathCondition) bIn (wco w)
      && oc_ok (AT := SHeap) bIn h
      && oc_ok (AT := Sub Σ0) bIn trans
      && oc_ok (AT := STerm ty_xlenbits) bIn apc
      && oc_ok (AT := STerm ty_xlenbits) bIn anp
      && itableW_free bIn tbl
      && etable_free bIn exits
      (* `wd` is REDUNDANT-but-true: it is one of the table's word column, so
         itableW_free above already implies it.  It is listed anyway because the
         drop's continuation captures `wd` and so the Factors CARRIER must cover
         it — and the carrier is read off this conjunction (PLAN-dropk.md §15). *)
      && oc_ok (AT := STerm ty_word) bIn wd.

    (* The witness term is needed for the ACCESSIBILITY, not for the tree:
       calling the continuation at the smaller world needs a Sub with an entry
       for every variable, x included.  `ty.inhabit`'s None on
       enum/tuple/union/record therefore still under-approximates — but every
       variable we actually want to drop is a havoced register, i.e. bvec, and
       `inhabit (bvec n) = Some bv.zero`. *)
    Definition drop_candidate (w : World) : Type :=
      sigT (fun b : LVar∷Ty =>
        sigT (fun bIn : (b ∈ w)%katamaran =>
          Term (@ctx.remove _ (wctx w) b bIn) (type b))).

    Definition find_dead {Σ0 : LCtx} {w : World}
        (trans : Sub Σ0 w) (tbl : SInstrTableW w) (exits : SExitTable w)
        (apc anp : Term (wctx w) ty_xlenbits) (wd : Term (wctx w) ty_word)
        (h : SHeap (wctx w))
        : option (drop_candidate w) :=
      List.fold_right
        (fun p acc =>
           match acc with
           | Some _ => acc
           | None =>
               if var_dead (projT2 p) trans tbl exits apc anp wd h
               then match ty.inhabit (type (projT1 p)) with
                    | Some v => Some (existT (projT1 p)
                                        (existT (projT2 p)
                                           (term_val (type (projT1 p)) v)))
                    | None   => None
                    end
               else None
           end)
        None (all_ins (wctx w)).

    (* One drop per iteration, re-scanning at the new world.  `fuel` bounds the
       number of drops per call; |wctx w| is the natural bound.

       Note `@acc_subst_right` and `@SymProp.dropk` are applied with `@`: both
       have trailing implicits that make their `x` argument maximally inserted,
       so the un-`@`-ed form silently shifts `name b` onto the witness slot. *)
    Fixpoint drop_dead (fuel : nat) {Σ0 : LCtx} {w : World}
        (trans : Sub Σ0 w) (tbl : SInstrTableW w) (exits : SExitTable w)
        (apc anp : Term (wctx w) ty_xlenbits) (wd : Term (wctx w) ty_word)
        {struct fuel} : SHeapSpec Unit w :=
      match fuel with
      | O   => SHeapSpec.pure tt
      | S n =>
          fun POST h =>
            match find_dead trans tbl exits apc anp wd h with
            | None   => POST w acc_refl tt h
            | Some c =>
                let b   := projT1 c in
                let bIn := projT1 (projT2 c) in
                let t0  := projT2 (projT2 c) in
                match occurs_check bIn h with
                | None    => POST w acc_refl tt h   (* unreachable: find_dead checked it *)
                | Some h' =>
                    (* Convoy match: the drop's forward accessibility needs the
                       occurs-check EQUATION, not just its success, so that it
                       can target `wdrop w x` — the same world `psafe (dropk …)`
                       is defined at.  Using acc_subst_right here would land at
                       `wsubst w x t0`, only propositionally equal, and force a
                       dependent rewrite of a World inside psafe. *)
                    (match occurs_check bIn (wco w) as o
                           return occurs_check bIn (wco w) = o -> 𝕊 (wctx w) with
                     | Some pc' =>
                         fun Hpc =>
                           let om := @acc_drop w (name b) (type b) bIn pc' Hpc t0 in
                           @SymProp.dropk (wctx w) (name b) (type b) bIn
                             (drop_dead n
                                (persist (A := Sub Σ0) trans om)
                                (persist_itableW om tbl) (persist_etable om exits)
                                (persist__term apc om) (persist__term anp om)
                                (persist__term wd om)
                                (four POST om) h')
                     | None => fun _ => POST w acc_refl tt h
                     end) eq_refl
                end
            end
      end.

    (* The A/B knob for the drop, and DELIBERATELY NOT A BOOLEAN FLAG.
       PLAN-chunk-gc.md §2 rejected a flag in this exact code for reasons that
       apply verbatim here — chiefly that flag SKEW is an established failure
       mode (a port left Adequacy.v at `false` while Contracts.v emitted `true`,
       so the fast VC could not reach the adequacy chain at all).

       Fuel is a better knob than a bool on every axis: `drop_dead 0` IS
       `SHeapSpec.pure tt`, which binds at acc_refl and collapses definitionally
       (the ghost_binds_nil precedent), so 0 gives a BYTE-IDENTICAL tree; there
       is ONE code path rather than two, so the refinement is proved once
       instead of per-branch; and being a single Definition with no threading,
       it cannot skew. A/B is two builds, which is what §2 asks for anyway.

       Kept at 0 until the refinement (Phase 5) is re-paired. rexec_cfg_addr
       must handle `drop_dead` for an ARBITRARY fuel, never by reducing this
       constant, or flipping it later would reopen the proof. *)
    Definition drop_fuel : nat := 0.

    (* `trans` is THE ACCUMULATED TRANSLATION: the contract context's variables
       as terms over the CURRENT world, i.e. `persist δ1 …` from
       sexec_triple_addr below.  It is threaded and persisted exactly like
       tbl/exits and is otherwise UNUSED — it exists so that the dead-variable
       drop (PLAN-dropk.md) can occurs-check it.

       Why it has to be here rather than inferred later: the outer continuation
       of the executor is `consume ens δ3` with `δ3 = persist δ1 (θ2 ∘ θ3)`, so
       δ1 is the ONLY thing that continuation's ω-dependence factors through
       (PLAN-dropk.md §4bis).  The executor cannot see that continuation, so a
       variable live only in δ1 would look dead against heap/pc/tbl/exits and be
       dropped unsoundly.  Occurs-checking `tbl` is NOT a substitute: a component
       of the translation unused by the table is invisible in
       `subst_itable ζ tbl` yet still present in δ3.  And it must be δ1, not ζ
       alone — δ1 = snoc ζ a2 with a2 the INITIAL pc, which the live `apc` no
       longer covers once the loop advances. *)
    (* THE POST-DROP STEP BODY, HOISTED OUT OF sexec_cfg_addr.
       It is a plain let-hoist — the same chain, in the same order, with the
       persist layers split at the drop instead of accumulated across it — and it
       exists for ONE reason, in the refinement proof rather than the executor:

       `rdrop_dead` needs `Factors (dbundle …) sΦ`, i.e. that drop_dead's
       continuation depends on the drop's accessibility ONLY through the persisted
       bundle.  Written inline, that continuation is `fun w1 θd _ => ⟨the chain⟩`
       and the witness `g` demanded by Factors would have to be a hand-copy of the
       chain living in VerifierRel.v, kept in sync by hand forever.  Hoisted, the
       continuation IS `step_after_drop rec ai (persist tr0 θd) … (four Φ' θd)`,
       so `g` is this very definition and there is nothing to keep in sync.

       Every argument at the call site below is literally `persist <the same thing
       drop_dead was given> θd`.  That is not stylistic: it is what makes Factors'
       witness definitional rather than a proof obligation. *)
    Definition step_after_drop {Σ0 : LCtx}
        (rec : forall w : World, Sub Σ0 w -> SInstrTableW w -> SExitTable w ->
                 Term (wctx w) ty_xlenbits -> Term (wctx w) ty_xlenbits ->
                 SHeapSpec (STerm ty_xlenbits) w)
        (ai : AnnotInstr) :
      ⊢ Sub Σ0 -> SInstrTableW -> SExitTable -> STerm ty_xlenbits ->
        STerm ty_xlenbits -> STerm ty_word -> SHeapSpec (STerm ty_xlenbits) :=
      fun w trans tbl exits apc anp wd =>
        ⟨ θ1 ⟩ _    <- sexec_ghosts (ai_ghost_before ai) ;;
        ⟨ θ2 ⟩ apc' <- sexec_instruction (ai_instr ai)
                         (persist__term apc θ1) (persist__term anp θ1)
                         (persist__term wd  θ1) ;;
        ⟨ θ3 ⟩ _    <- sexec_ghosts (ai_ghost_after ai) ;;
        rec _ (persist (A := Sub Σ0) trans (θ1 ∘ θ2 ∘ θ3))
              (persist_itableW (θ1 ∘ θ2 ∘ θ3) tbl)
              (persist_etable  (θ1 ∘ θ2 ∘ θ3) exits)
              (persist__term apc' θ3) (persist__term apc' θ3).

    Fixpoint sexec_cfg_addr {Σ0 : LCtx} (fuel : nat) :
      ⊢ Sub Σ0 -> SInstrTableW -> SExitTable -> STerm ty_xlenbits ->
        STerm ty_xlenbits -> SHeapSpec (STerm ty_xlenbits) :=
      fun w trans tbl exits apc anp =>
        let emsg (s : string) : SHeapSpec (STerm ty_xlenbits) w :=
          error (fun _ => amsg.mk {| debug_string_pathcondition := wco w;
                                     debug_string_message := s |}) in
        match fuel with
        | O    => emsg "sexec_cfg_addr: out of fuel"
        | S n' =>
            angelic_binary
              (if is_exit exits apc then pure apc
               else emsg "sexec_cfg_addr: exit branch chosen but pc matches no declared exit term")
              (match lookup_instr tbl apc with
               | None         => emsg "sexec_cfg_addr: no instruction key matches this pc term"
               | Some (wd, ai) =>
                   (* Ghosts run AFTER chunk_gc, so an AnnotDebugBreak dumps
                      the POST-GC heap — the one the executor actually carries
                      forward.  Given that a leaked encodes_instr chunk was the
                      O(steps²) driver, the filtered heap is the one worth
                      looking at.  Both slots are `nil` for every current
                      program and ghost_binds_nil shows that contributes
                      nothing to the term. *)
                   ⟨ θ0 ⟩ _    <- chunk_gc ;;
                   (* Drop dead logical variables AFTER chunk_gc, so the check
                      sees the post-GC heap — the leaked encodes_instr chunks
                      the GC removes are exactly what used to keep per-trip
                      variables alive in the heap root.  Placed inside this
                      branch rather than before the `match fuel`, so `emsg`
                      stays at world w and only the persist chains lengthen. *)
                   (* The bundle is named ONCE so that drop_dead's arguments and
                      step_after_drop's are visibly the same objects, the latter
                      persisted by θd.  Factors' witness reads straight off that. *)
                   let tr0 := persist (A := Sub Σ0) trans θ0 in
                   let tb0 := persist_itableW θ0 tbl in
                   let ex0 := persist_etable  θ0 exits in
                   let pc0 := persist__term apc θ0 in
                   let np0 := persist__term anp θ0 in
                   let wd0 := persist__term wd  θ0 in
                   ⟨ θd ⟩ _    <- drop_dead drop_fuel tr0 tb0 ex0 pc0 np0 wd0 ;;
                   step_after_drop (@sexec_cfg_addr Σ0 n') ai
                     (persist (A := Sub Σ0) tr0 θd)
                     (persist_itableW θd tb0)
                     (persist_etable  θd ex0)
                     (persist__term pc0 θd)
                     (persist__term np0 θd)
                     (persist__term wd0 θd)
               end)
        end.

    (* sexec_triple_addr / scfg_verification_condition: apply     *)
    (* symbolic execution to verify a Hoare triple for a program.  The     *)
    (* precondition can mention the address a where the program is loaded; *)
    (* the postcondition can additionally mention the address an where the *)
    (* pc points after execution.  scfg_verification_condition runs   *)
    (* sexec_triple_addr inside SHeapSpec.run (no leakcheck), giving a *)
    (* 𝕊 wnil proposition checked by `safeE (postprocess ...)`.  `tbl`/    *)
    (* `exits` are given at the CONTRACT context Σ (plain    *)
    (* lists of Σ-level terms, like `req`/`ens`), and moved into the       *)
    (* current world the same way `req` is: by applying the substitution  *)
    (* `ζ : Sub Σ w` (obtained from `demonic_ctx`'s δ, persisted forward   *)
    (* to the world where `a` lives) to each key term via `subst`. *)
    (* tbl/exits here are SInstrTable/SExitTable at the world wlctx Σ (empty path
       condition over the contract context) -- definitionally the same
       as `list (Term Σ ty_xlenbits * AnnotInstr)` / `list (Term Σ ty_xlenbits)`,
       since wctx (wlctx Σ) reduces to Σ by record projection. *)
    Definition subst_itable {Σ : LCtx} {w : World} (ζ : Sub Σ w)
        (tbl : SInstrTable (wlctx Σ)) : SInstrTable w :=
      List.map (fun '(t,i) => (subst t ζ, i)) tbl.
    Definition subst_etable {Σ : LCtx} {w : World} (ζ : Sub Σ w)
        (exits : SExitTable (wlctx Σ)) : SExitTable w :=
      List.map (fun t => subst t ζ) exits.

    (* ---------------------------------------------------------------- *)
    (* The word supplier.  ONE logic variable for the whole program, of   *)
    (* width word * n, with each address's word a SLICE of it — see       *)
    (* SInstrTableW's comment for why the words have to come from outside *)
    (* at all.                                                            *)
    (*                                                                   *)
    (* It used to be one variable PER ADDRESS (n of them).  That is not   *)
    (* wasteful in itself — a word is a pure identity token, and a logic  *)
    (* variable is the cheapest representation of one, since its identity *)
    (* lives in its de Bruijn INDEX and so stays decidable even though    *)
    (* its value is unknown.  What made n of them expensive is that |Σ|   *)
    (* drives lookup cost QUADRATICALLY (diagnostics/lvar-lookup-cost-    *)
    (* drivers.md), and on br_divrem the words were 49 of 63 binders.     *)
    (*                                                                   *)
    (* Slicing keeps the property that made variables work: the LEAF is   *)
    (* still a term_var, compared by index, and the bvtake/bvdrop         *)
    (* wrappers carry concrete nat indices that uop.tel_eq_dec settles.   *)
    (* So Term_eqb on two slices of the same variable is `true`, and on   *)
    (* different slices `false` — measured before writing this.  Every    *)
    (* attempt to make a word a term_val of a Coq-level value instead     *)
    (* FAILED, and not for a shallow reason: eq_dec on an opaque `bv`     *)
    (* exhausts memory under vm_compute (Bitvector.v's eqdec_bv builds an *)
    (* equality PROOF via bin_inj), and no reduction strategy can decide  *)
    (* equality of an opaque value at all.  Do not retry that.            *)
    (*                                                                   *)
    (* NO LOSS OF GENERALITY: ∀ W : bv (word*n) and ∀ w_0..w_{n-1} : bv   *)
    (* word are in bijection under slicing.                               *)
    (*                                                                   *)
    (* Shape copied from GenContract.v's mem_class_width /                *)
    (* gen_mem_cells_class, which does exactly this for memory cells.     *)
    (* words_width (S n) must stay DEFINITIONALLY `word + words_width n`  *)
    (* or the slices do not typecheck against uop.bvtake/bvdrop's         *)
    (* `bvec (m + k)` index — the same trap GenContract.v flags.          *)
    (*                                                                   *)
    (* n = 0 gives a width-0 binding rather than no binding.  Deliberate: *)
    (* it keeps words_ctx a single uniform shape, and an empty program    *)
    (* cannot occur.                                                      *)
    (* ---------------------------------------------------------------- *)
    Fixpoint words_width (n : nat) : nat :=
      match n with
      | O    => 0
      | S n' => word + words_width n'
      end.

    Definition words_ctx (n : nat) : LCtx :=
      [ctx] ▻ ("w"∷ty.bvec (words_width n)).

    (* Peel the n words off the class variable, word bits at a time.
       Generic in the value functor D — so the concrete mirror
       (VerifierRel.v, D := Val) and the symbolic side (D := Term w) still
       share ONE definition and hence one induction when relating them —
       but now PARAMETERISED by D's take/drop, because slicing needs
       operations and those differ per functor (term_unop for Term,
       bv.take/bv.drop for Val). *)
    Fixpoint words_of_slice {D : Ty -> Set}
        (dtake : forall m k, D (ty.bvec (m + k)) -> D (ty.bvec m))
        (ddrop : forall m k, D (ty.bvec (m + k)) -> D (ty.bvec k))
        (n : nat) : D (ty.bvec (words_width n)) -> list (D ty_word) :=
      match n return D (ty.bvec (words_width n)) -> list (D ty_word) with
      | O    => fun _ => nil
      | S n' => fun W =>
          cons (dtake word (words_width n') W)
               (words_of_slice dtake ddrop n' (ddrop word (words_width n') W))
      end.

    Definition words_of_env {D : Ty -> Set}
        (dtake : forall m k, D (ty.bvec (m + k)) -> D (ty.bvec m))
        (ddrop : forall m k, D (ty.bvec (m + k)) -> D (ty.bvec k))
        (n : nat) (E : NamedEnv D (words_ctx n)) : list (D ty_word) :=
      words_of_slice dtake ddrop n (env.head E).

    (* D := Term w.  NOTE `Set Implicit Arguments` is on in this file, so
       `n` is IMPLICIT in both words_of_env and words_of_env_term (it is
       inferable from E) — passing it explicitly is a type error whose
       message points at the wrong argument. *)
    Definition wterm_take {Σ} (m k : nat) (t : Term Σ (ty.bvec (m + k)))
      : Term Σ (ty.bvec m) := term_unop (uop.bvtake m) t.
    Definition wterm_drop {Σ} (m k : nat) (t : Term Σ (ty.bvec (m + k)))
      : Term Σ (ty.bvec k) := term_unop (uop.bvdrop m) t.

    Definition words_of_env_term {w} (n : nat)
        (E : NamedEnv (Term (wctx w)) (words_ctx n))
      : list (Term (wctx w) ty_word) :=
      words_of_env (@wterm_take (wctx w)) (@wterm_drop (wctx w)) E.

    (* Attach the word column.  Lengths always agree at the one call site
       (n := length tbl), so the []-fallback is never taken; if it ever were,
       the table would be short and the executor would fail with "no
       instruction key matches this pc term" — a failed VC, not unsoundness. *)
    Fixpoint zip_words {w} (tbl : SInstrTable w)
        (ws : list (Term (wctx w) ty_word)) : SInstrTableW w :=
      match tbl , ws with
      | cons (t,i) tbl' , cons x ws' => cons (t, x, i) (zip_words tbl' ws')
      | _ , _ => nil
      end.

    (* The one demonic_ctx call covers Σ AND the SINGLE wide word variable;
       δw is split back apart with env.drop / env.take.  The words are
       introduced HERE, before the execution loop, so nothing about them
       depends on the trip count — and since 2026-08-24 they cost ONE binder
       for the whole program rather than one per instruction. *)
    Definition sexec_triple_addr {Σ : LCtx}
      (req : Assertion (Σ ▻ ("a"::ty_xlenbits)))
      (tbl : SInstrTable (wlctx Σ)) (exits : SExitTable (wlctx Σ))
      (fuel : nat)
      (ens : Assertion (Σ ▻ ("a"::ty_xlenbits) ▻ ("an"::ty_xlenbits))) :
      ⊢ SHeapSpec Unit :=
      fun w =>
        let n := length tbl in
        ⟨ θ0 ⟩ δw <- demonic_ctx id (Σ ▻▻ words_ctx n) ;;
        let δ   := env.drop (words_ctx n) δw in
        let ws0 := words_of_env_term (env.take (words_ctx n) δw) in
        ⟨ θ1 ⟩ a <- demonic (Some "a") _ ;;
        (* The ONLY nextpc variable in the whole run.  The first step cannot
           know the incoming nextpc value, so it is quantified here — ONCE,
           rather than once per step as exec_instruction_prologue used to do.
           create_resources (Adequacy.v) already provides the matching
           `∃ v, nextpc ↦ᵣ v`, so ImplPre does not change. *)
        ⟨ θ1'⟩ np <- demonic (Some "np") _ ;;
        let δ1 := env.snoc (persist (A := Sub Σ) δ (θ1 ∘ θ1')) _ (persist__term a θ1') in
        ⟨ θ2 ⟩ _ <- produce req δ1 ;;
        let a2 := persist__term a (θ1' ∘ θ2) in
        let ζ := persist (A := Sub Σ) δ (θ1 ∘ θ1' ∘ θ2) in
        let ws := List.map (fun x => persist__term x (θ1 ∘ θ1' ∘ θ2)) ws0 in
        ⟨ θ3 ⟩ na <- sexec_cfg_addr fuel
                       (persist (A := Sub (Σ ▻ ("a"::ty_xlenbits))) δ1 θ2)
                       (zip_words (subst_itable ζ tbl) ws)
                       (subst_etable ζ exits) a2 (persist__term np θ2) ;;
        let δ3 := persist δ1 (θ2 ∘ θ3) in
        consume ens δ3.["an"∷ty_xlenbits ↦ na].

    (* scfg_verification_condition: runs sexec_triple_addr inside *)
    (* SHeapSpec.run; same wnil shape, no leakcheck. *)
    Definition scfg_verification_condition {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits))
      (* Use the ALIASES, never a spelled-out tuple: a literal type here
         silently fails to track a new table column (this signature missed
         both the word column and the AnnotInstr migration that way). *)
      (tbl : SInstrTable (wlctx Σ))
      (exits : SExitTable (wlctx Σ)) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) : ⊢ 𝕊 :=
      fun w =>
        SHeapSpec.run (sexec_triple_addr req tbl exits fuel ens (w := w)).

  End Symbolic.

End CFGVerificationDerived.
