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
       introduced ONCE per instruction ADDRESS (sexec_triple_addr below), not
       once per execution step, so a loop re-executing the same addresses
       reuses the same word variables every trip.  PLAN-encoded-instr.md. *)
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
    (* sexec_ghosts folds it over an instruction's ghost list.             *)
    (*                                                                     *)
    (* WHY □ -> □ AND NOT □ -> SHeapSpec.  A TRANSFORMER of                *)
    (* world-polymorphic computations composes with itself, so the list    *)
    (* case is a plain fold_right and `T` is applied exactly once, at the  *)
    (* end.  With the un-boxed result type the two could not be chained    *)
    (* (one returns SHeapSpec, the next needs □ SHeapSpec) and sexec_ghosts *)
    (* would have to be its own Fixpoint duplicating the match.  The box   *)
    (* also means each annotation's message is built at the world where    *)
    (* ITS node lands, not at the outer world.                             *)
    (*                                                                     *)
    (* THE TWO KINDS HAVE DIFFERENT SHAPES, AND THE ASYMMETRY IS CORRECT.  *)
    (* AnnotDebugBreak WRAPS (leaves the world alone); AnnotLemmaInvocation *)
    (* BINDS (call_lemma consumes and produces heap, so it moves the        *)
    (* world).  The Box -> Box signature accommodates both, which is why    *)
    (* it is worth writing now rather than discovering at Phase 4 that the  *)
    (* shape has to change in the middle of the relational proofs.         *)
    (*                                                                     *)
    (* The rule behind the asymmetry — a BOUND step is fine exactly when    *)
    (* the CONCRETE side binds too:                                        *)
    (*  - call_lemma HAS a concrete counterpart (CHeapSpec.call_lemma), so  *)
    (*    both sides bind, and rsolve dispatches it through the ordinary    *)
    (*    refine_bind machinery.  main's BlockVer/PartialVerifier.v does    *)
    (*    exactly this and closes the case with `iApply "IHb"; rsolve`.     *)
    (*  - debug has NO concrete content: CHeapSpec.debug = fun m => m, the  *)
    (*    IDENTITY (theories/Shallow/Monads.v:1112).  Binding it would move *)
    (*    the world on the symbolic side with nothing on the concrete side  *)
    (*    to match, and the framework's refine_debug /                      *)
    (*    refine_compat_debug (theories/Refinement/Monads.v:1683,1693) are  *)
    (*    stated for debug AS A TRANSFORMER, so they would not apply.       *)
    (*                                                                     *)
    (* DO NOT "simplify" AnnotDebugBreak into an SHeapSpec Unit action      *)
    (* bound with ⟨θ⟩ _ <- .  That was tried (2274a22b): it forced a        *)
    (* hand-written rexec_ghost bridge lemma, which hung at compile for     *)
    (* 300 s+ with no root cause found; it adds a third world to the        *)
    (* persist chain (a second copy of the chunk_gc problem above); and it  *)
    (* breaks cost-neutrality for unannotated programs, since               *)
    (* `bind (pure tt) f` is not `f` whereas `fold_right … nil` IS `T k`.   *)
    (*                                                                     *)
    (* PHASE 2 OBLIGATION: cexec_cfg_addr must mirror the LEMMA case (not   *)
    (* the debug one).  Nothing needs a new LEnv entry — these invoke       *)
    (* EXISTING lemmas — so there is no soundness debt here, only mirroring. *)
    (*                                                                     *)
    (* FUTURE-PROOFING (checked 2026-08-21, no change needed).  Two further *)
    (* annotation kinds have been discussed, and BOTH fit this signature as *)
    (* it stands — do not widen it for them:                               *)
    (*  - DROP CHUNKS (a user-directed chunk_gc).  A same-world WRAPPER,    *)
    (*    like the debug case.  Sound for ANY chunk by affineness of iProp  *)
    (*    (a fold_right of ∗ can discard a conjunct) — see PLAN-encoded-    *)
    (*    instr.md §11, whose refine_chunk_gc/inst_gc_heap are audited      *)
    (*    Closed under the global context.  So it needs NO LEnv entry and   *)
    (*    no per-use soundness proof; the price is completeness, and it     *)
    (*    fails loudly at the next consume rather than silently.            *)
    (*  - DROP AN UNREFERENCED LOGICAL VARIABLE.  A BIND, like the lemma    *)
    (*    case, and it composes with the SAME `θ ∘ θ'` code even though it  *)
    (*    moves to a SMALLER context: acc_subst_right gives                *)
    (*    `w ⊒ wsubst w x t` whose wctx is `w - x∷σ`, because ⊒ orders      *)
    (*    worlds by INFORMATION, not by size.  Motivation: demonicv_prune   *)
    (*    (Propositions.v:1175) only collapses on `block`, so a binder      *)
    (*    nothing references any more SURVIVES — an abstraction lemma       *)
    (*    shrinks terms but leaves the old binders in Σ, and variable count *)
    (*    is quadratic in lookup cost (diagnostics/lvar-lookup-cost-       *)
    (*    drivers.md).                                                      *)
    (*    Unimplemented and unproven; sketch only.                          *)
    (* ================================================================== *)
    Definition sexec_ghost {A} (a : Annot) {w : World}
        (k : Box (SHeapSpec A) w) : Box (SHeapSpec A) w :=
      match a with
      | AnnotDebugBreak =>
          fun w2 θ =>
            debug
              (fun (h0 : SHeap w2) =>
                 amsg.mk {| debug_asn_pathcondition := wco w2
                          ; debug_asn_heap          := h0 |})
              (k w2 θ)
      | AnnotLemmaInvocation l es =>
          fun w2 θ =>
            (* LEnv is QUALIFIED: Verifier.v imports
               RiscvPmpCFGVerifExecutor, but that is `MakeExecutor …
               RiscvPmpCFGVerifSpec` (Spec.v:720) and the functor does NOT
               re-export its Specification argument — which is why
               RiscvPmpSpecVerif (Spec.v:723) imports BOTH.  SpecIris.v names
               spec members the same qualified way.  A bare `LEnv` fails with
               "The reference LEnv was not found", and note rocq_compile_file's
               dune-fallback ACCEPTS the bare form — only `make` catches it. *)
            ⟨ θ' ⟩ _ <- call_lemma (RiscvPmpCFGVerifSpec.LEnv l)
                          (seval_exps [env] es) ;;
            k _ (θ ∘ θ')
      end.

    (* fold_right, so the FIRST annotation in the list is the OUTERMOST
       wrapper and therefore the first node encountered — list order is
       execution order.  `nil` gives `T k` with no residue: ghosts are
       cost-free for every program that has none, which is what makes the
       migration's cost-neutrality exact rather than approximate. *)
    Definition sexec_ghosts {A} (gs : list Annot) {w : World}
        (k : Box (SHeapSpec A) w) : SHeapSpec A w :=
      T (List.fold_right (fun a k' => sexec_ghost a k') k gs).

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
    Fixpoint sexec_cfg_addr (fuel : nat) :
      ⊢ SInstrTableW -> SExitTable -> STerm ty_xlenbits ->
        STerm ty_xlenbits -> SHeapSpec (STerm ty_xlenbits) :=
      fun w tbl exits apc anp =>
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
                   ⟨ θ0 ⟩ _    <- chunk_gc ;;
                   ⟨ θ1 ⟩ apc' <- sexec_instruction (ai_instr ai) (persist__term apc θ0) (persist__term anp θ0) (persist__term wd θ0) ;;
                   sexec_cfg_addr n' (persist_itableW (θ0 ∘ θ1) tbl) (persist_etable (θ0 ∘ θ1) exits)
                     apc' apc'
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
    (* The word supplier.  One logic variable per instruction ADDRESS,   *)
    (* introduced once at contract entry — see SInstrTableW's comment    *)
    (* for why the words have to come from outside at all.               *)
    (*                                                                   *)
    (* They are introduced by EXTENDING the context that sexec_triple_addr *)
    (* already hands to demonic_ctx, from Σ to Σ ▻▻ words_ctx n, rather   *)
    (* than by a fresh fold or by declaring them in the contract's own Σ. *)
    (* Both alternatives were considered; this one is why Tables.v,       *)
    (* Contracts.v, GenContract.v, TablesRel.v and all seven examples are *)
    (* untouched by the word threading, and it reuses the already-proved  *)
    (* refine_demonic_ctx instead of needing a new refinement lemma.      *)
    (*                                                                   *)
    (* All n bindings are named "w"; duplicate names in an LCtx are fine  *)
    (* here because the terms are read POSITIONALLY (words_of_env), never *)
    (* resolved by name — demonic_ctx alpha-renames them to w, w.1, ...   *)
    (* ---------------------------------------------------------------- *)
    Fixpoint words_ctx (n : nat) : LCtx :=
      match n with
      | O    => [ctx]
      | S n' => words_ctx n' ▻ ("w"∷ty_word)
      end.

    (* Read the n word entries off as a plain list.  Generic in the value
       functor D so the concrete mirror (VerifierRel.v, D := Val) and the
       symbolic side (D := Term w) share one definition, hence one induction
       when relating them. *)
    Fixpoint words_of_env {D : Ty -> Set} (n : nat) :
      NamedEnv D (words_ctx n) -> list (D ty_word) :=
      match n with
      | O    => fun _ => nil
      | S n' => fun E => cons (env.head E) (words_of_env n' (env.tail E))
      end.

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

    (* The one demonic_ctx call now covers Σ AND the n = length tbl word
       variables; δw is split back apart with env.drop / env.take.  Note the
       words are introduced HERE, before the execution loop, so their count is
       the PROGRAM's instruction count and is independent of the trip count. *)
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
        let ws0 := words_of_env n (env.take (words_ctx n) δw) in
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
        ⟨ θ3 ⟩ na <- sexec_cfg_addr fuel (zip_words (subst_itable ζ tbl) ws)
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
