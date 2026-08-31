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

(* CFGVer/VerifierRel.v — concrete mirror, relational bridge, soundness.    *)
(*                                                                          *)
(* Split out of Verifier.v (2026-07-27): everything in the verifier that    *)
(* needs the binary Iris model or the shallow/refine executors.             *)
(*   Shallow    — cexec_cfg_addr (concrete, propositional)                  *)
(*   Relational — rexec_cfg_addr, the soundness bridge via rsolve, plus the *)
(*                RefineCompat instances and itable_rel/etable_rel          *)
(*   Soundness  — ptsto_instrs + the pieces Adequacy.v's myWP2 chain reuses *)
(*                (sound_exec_instruction, ptsto_instrs_lookup)             *)
(*                                                                          *)
(* Kept OUT of Verifier.v so Contracts.v / GenContract.v / Example/*.v pay  *)
(* neither the ~0.98 GB Iris model nor the ~0.31 GB shallow/refine stack.   *)
(* Required by TablesRel.v, Adequacy.v and EndToEnd.v.                      *)
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
     RiscvPmp.CFGVer.SpecIris
     RiscvPmp.CFGVer.Verifier
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

Section CFGVerificationDerived.

  Import RiscvPmpCFGVerifExecutor.
  Import RiscvPmpCFGVerifShalExecutor.

  Section Shallow.

    Import CStoreSpec (evalStoreSpec).
    Import CHeapSpec CHeapSpec.notations.

    Definition cexec_instruction (i : AST) :
      RelVal ty_xlenbits -> RelVal ty_xlenbits -> RelVal ty_word ->
      CHeapSpec (RelVal ty_xlenbits) :=
      let inline_fuel := 10%nat in
      fun a np w =>
        _ <- produce
               (exec_instruction_prologue i)
               [env].["a"∷_ ↦ a].["np"∷_ ↦ np].["w"∷_ ↦ w] ;;
        _ <- evalStoreSpec (cexec inline_fuel (FunDef step)) [env] ;;
        na <- angelic _ ;;
        _ <- consume
               (exec_instruction_epilogue i)
               [env].["a"∷ty_xlenbits ↦ a].["an"∷_ ↦ na].["w"∷_ ↦ w] ;;
        pure na.

    Definition cgc_heap (h : SCHeap) : SCHeap :=
      List.filter (fun c => negb (is_encodes_instr c)) h.

    Definition cchunk_gc : CHeapSpec unit :=
      fun POST h => POST tt (cgc_heap h).

    (* The whole content of refine_chunk_gc (plan step 2d): instantiation      *)
    (* commutes with the chunk filter.  Nearly free because `inst` preserves   *)
    (* chunk_user's PREDICATE HEAD (Chunks.v: inst (chunk_user p ts) ι =       *)
    (* chunk_user p (inst ts ι)) and is_encodes_instr inspects only that head, *)
    (* so the filter predicate is invariant under `inst` and List.filter       *)
    (* commutes with List.map.                                                 *)
    (* Generic; belongs in a list library (theories/Prelude.v) rather than    *)
    (* here.  Kept local for now to avoid a framework-wide rebuild — move it  *)
    (* together with Verifier.v's find_map/ctx_len when those go up.          *)
    Lemma filter_map_comm {A B : Type} (f : A -> B) (p : A -> bool) (q : B -> bool) :
      (forall a, q (f a) = p a) ->
      forall l, List.filter q (List.map f l) = List.map f (List.filter p l).
    Proof.
      intros Hpq l. induction l as [|a l IHl]; cbn; [reflexivity|].
      rewrite Hpq. destruct (p a); cbn; [f_equal|]; exact IHl.
    Qed.

    Lemma inst_gc_heap {Σ} (sh : SHeap Σ) (ι : Valuation Σ) :
      inst (gc_heap sh) ι = cgc_heap (inst sh ι).
    Proof.
      unfold gc_heap, cgc_heap.
      symmetry. apply filter_map_comm.
      intros c. destruct c; reflexivity.
    Qed.

    #[export] Instance mono_cchunk_gc :
      Monotonic (MHeapSpec eq) cchunk_gc.
    Proof. firstorder. Qed.

    (* Concrete mirror of the dead-logical-variable drop.  There are no logical
       variables concretely, so it is the IDENTITY — but it must exist as a
       BIND, because refine_bind pairs a symbolic bind with a concrete one and
       drop_dead is bound on the symbolic side.  Costs nothing in the term:
       `bind (pure tt) k` is `k tt` definitionally (cdrop_binds below). *)
    Definition cdrop_dead : CHeapSpec unit :=
      fun POST h => POST tt h.

    #[export] Instance mono_cdrop_dead :
      Monotonic (MHeapSpec eq) cdrop_dead.
    Proof. firstorder. Qed.

    Lemma cdrop_binds {A} (k : CHeapSpec A) (Φ : A -> SCHeap -> Prop) (h : SCHeap) :
      (_ <- cdrop_dead ;; k) Φ h = k Φ h.
    Proof. reflexivity. Qed.

    (* The GC bind inserted into cexec_cfg_addr's step rewrites the heap and never inspects
       the postcondition, so the equation holds definitionally. *)
    Lemma cgc_binds_heap {A} (k : CHeapSpec A) (Φ : A -> SCHeap -> Prop) (h : SCHeap) :
      (_ <- cchunk_gc ;; k) Φ h = k Φ (cgc_heap h).
    Proof. reflexivity. Qed.

    (* USE THIS ONE, not the equality above, to discharge a hypothesis. *)
    (* `rewrite cgc_binds_heap in H` FAILS: rewrite matches keyed on the LHS *)
    (* head symbol (CHeapSpec.bind), whereas the occurrence actually *)
    (* produced by cexec_instruction's postcondition is already beta-reduced *)
    (* to `cchunk_gc (fun _ h1 => ...) h`.  `apply … in H` unifies up to *)
    (* full conversion instead, so it goes through. *)
    Lemma cgc_binds_heap_fwd {A} (k : CHeapSpec A) (Φ : A -> SCHeap -> Prop) (h : SCHeap) :
      (_ <- cchunk_gc ;; k) Φ h ->
      k Φ (cgc_heap h).
    Proof. now rewrite cgc_binds_heap. Qed.

    (* `words` gives the raw instruction word at each address — the concrete
       counterpart of the word column of the symbolic SInstrTableW
       (Verifier.v).  It stays a SEPARATE gmap from `instrs` (rather than
       fusing it into `instrs`) because `instrs` is what the trusted statement
       surface and TablesRel.v's faith lemmas talk about, whereas `words` is
       supplied by Adequacy.v out of the `∃ v` inside interp_ptsto_instr.  It
       is a total FUNCTION, not a gmap, so the lookup is
       total, so there is no "no word here" case to carry. *)
    (* ---------------------------------------------------------------- *)
    (* Concrete mirrors of Verifier.v's sexec_ghost/sexec_ghosts.        *)
    (*                                                                   *)
    (* AnnotDebugBreak is the IDENTITY here — CHeapSpec.debug is         *)
    (* `fun m => m` (theories/Shallow/Monads.v:1112) — which is exactly  *)
    (* why the symbolic debug node needs no concrete content.  The lemma *)
    (* case is real and mirrors the symbolic call_lemma one-for-one,     *)
    (* which is what makes binding it refinable by ordinary refine_bind. *)
    (* LEnv is qualified for the same reason as in Verifier.v: the       *)
    (* executor functor does not re-export its Specification argument.   *)
    (* ---------------------------------------------------------------- *)
    Definition cexec_ghost (a : Annot) : CHeapSpec unit :=
      match a with
      | AnnotDebugBreak           => debug (pure tt)
      (* REAL as of Phase 4.  Mirrors sexec_ghost's `call_lemma` one-for-one,
         which is what lets ordinary refine_bind dispatch it (rexec_ghosts
         below) instead of needing a bespoke lemma.  `es` lives at the empty
         program context, so the store to evaluate against is `[env]`.
         Previously `pure tt`, matching the symbolic `error` stub; making THIS
         side real while the symbolic side stayed stubbed is the 2026-08-21
         mistake, because then the concrete executor has a heap effect the
         symbolic VC does not account for.  Both sides move together or
         neither does. *)
      | AnnotLemmaInvocation l es =>
          call_lemma (RiscvPmpCFGVerifSpec.LEnv l) (evals es [env])
      end.

    (* List.nil/List.cons spelled out rather than []/:: — ctx.notations (in
       scope throughout this file) hijacks list cons, the same trap Tables.v
       and Verifier.v each carry a note about.  Those files fix it with a
       file-wide `Open Scope list_scope`; doing that HERE would change parsing
       across 1400 lines of existing proofs, so the local fix is better. *)
    Fixpoint cexec_ghosts (gs : list Annot) : CHeapSpec unit :=
      match gs with
      | List.nil        => pure tt
      | List.cons a gs' => _ <- cexec_ghost a ;; cexec_ghosts gs'
      end.

    (* cexec_ghosts_pure USED TO LIVE HERE and is DELETED, on purpose.  It
       said `cexec_ghosts gs = pure tt` — true only while every ghost was
       concretely the identity, which the real call_lemma above ends.  Its one
       user, sound_exec_cfg_addr_myWP2 (Adequacy.v), absorbed the two ghost
       binds by rewriting with it; that is now done by sound_cexec_ghosts
       there, an induction over the ghost list resting on call_lemma_sound
       (MicroSail/ShallowSoundness.v) and lemSemCFGVerif (SpecIris.v).  This is
       the Phase 4 soundness obligation PLAN-annotinstr.md said would land
       here, and it lands there instead — the shallow layer has no access to
       the Iris instance, so the obligation cannot be discharged in this
       section at all. *)

    (* `instrs` is AnnotInstr-valued, mirroring the symbolic SInstrTable.
       Ghosts are FUSED here rather than given a separate channel: they share
       the AST's origin (the `list AnnotInstr` the author wrote), so splitting
       them out would mean proving two halves agree.  Contrast `words` above,
       which is separate precisely because its origin IS separate (supplied by
       Adequacy.v out of interp_ptsto_instr's ∃v) — that split already costs a
       whole wtable_rel/itable_relW_zip family and is not a pattern to copy
       without the same justification.  MEMORY still speaks AST: see
       ptsto_instrs in Section Soundness, fed `ai_instr <$> instrs`. *)
    Fixpoint cexec_cfg_addr (instrs : gmap (bv xlenbits) AnnotInstr)
      (words : bv xlenbits -> bv word) (exitCond : bv xlenbits -> bool) (fuel : nat) :
      RelVal ty_xlenbits -> RelVal ty_xlenbits -> CHeapSpec (RelVal ty_xlenbits) :=
      fun apc anp =>
        match fuel with
        | O    => error
        | S n' =>
            match ty.RVToOption apc with
            | None   => error
            | Some v =>
                angelic_binary
                  (if exitCond v then pure apc else error)
                  (match instrs !! v with
                   | None    => error
                   | Some ai =>
                       _ <- cchunk_gc ;;
                       _ <- cdrop_dead ;;
                       _ <- cexec_ghosts (ai_ghost_before ai) ;;
                       apc' <- cexec_instruction (ai_instr ai) apc anp
                                 (ty.SyncVal (words v)) ;;
                       _ <- cexec_ghosts (ai_ghost_after ai) ;;
                       cexec_cfg_addr instrs words exitCond n' apc' apc'
                   end)
            end
        end.

    Import (hints) CStoreSpec.

    #[export] Instance mono_cexec_instruction {i a np w} :
      Monotonic (MHeapSpec eq) (cexec_instruction i a np w).
    Proof. typeclasses eauto. Qed.

    (* mono_cexec_cfg_addr's `typeclasses eauto` needs these for the two ghost
       binds, exactly as it needs mono_cchunk_gc for chunk_gc's. *)
    #[export] Instance mono_cexec_ghost {a} :
      Monotonic (MHeapSpec eq) (cexec_ghost a).
    Proof. destruct a; typeclasses eauto. Qed.

    #[export] Instance mono_cexec_ghosts {gs} :
      Monotonic (MHeapSpec eq) (cexec_ghosts gs).
    Proof. induction gs; cbn; typeclasses eauto. Qed.

    #[export] Instance mono_cexec_cfg_addr {instrs words exitCond fuel apc anp} :
      Monotonic (MHeapSpec eq) (cexec_cfg_addr instrs words exitCond fuel apc anp).
    Proof.
      revert apc anp. induction fuel; intros apc anp.
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
  (* rexec_cfg_addr: the key lemma, refining the gmap concrete executor  *)
  (*   by the term-table symbolic executor under table faithfulness.        *)
  (*   Proved by iInduction on fuel; the is_exit/lookup_instr double         *)
  (*   destruct is discharged sequentially across its four subgoals.        *)
  (*                                                                         *)
  (* RefineCompat instances export the relational lemmas for use by rsolve:  *)
  (*   refine_compat_cfg_verification_condition — key instance that    *)
  (*   lets rsolve close goals of the form                                  *)
  (*   RSat RProp (ccfg_vc ...) (scfg_vc ...)                     *)
  (* ====================================================================== *)
  Section Relational.

    Import iris.proofmode.tactics logicalrelation logicalrelation.notations.
    Import RiscvPmpIrisInstanceWithContracts.StoreSpec.
    Import RiscvPmpIrisInstanceWithContracts.
    Import RiscvPmpSignature.HeapSpec.
    Import RSolve HeapSpec.

    (* Second RVal argument: the incoming nextpc value, a PARAMETER rather   *)
    (* than a per-step existential (exec_instruction_prologue, Verifier.v).  *)
    (* Note this is CHEAPER than the pre-2026-07-31 version despite the      *)
    (* extra arrow — the prologue's demonic/refine_demonic pairing is gone,  *)
    (* replaced by an env entry rsolve discharges from the new hypothesis.   *)
    Lemma rexec_instruction (i : AST) {w} :
      ⊢ ℛ⟦RVal ty_xlenbits -> RVal ty_xlenbits -> RVal ty_word ->
           RHeapSpec (RVal ty_xlenbits)⟧
          (cexec_instruction i)
          (sexec_instruction (w := w) i).
    Proof.
      unfold cexec_instruction, sexec_instruction. rsolve.
    Qed.

    #[export] Instance refine_compat_exec_instruction {i : AST} {w} :
      RefineCompat (RVal ty_xlenbits -> RVal ty_xlenbits -> RVal ty_word ->
                    RHeapSpec (RVal ty_xlenbits))
        (cexec_instruction i) w (sexec_instruction (w := w) i) _ :=
      MkRefineCompat (rexec_instruction i).

    (* refine_chunk_gc: the GC step is sound relationally for any chunk,
       not just encodes_instr — its whole content is inst_gc_heap
       (Shallow section above), lifted from the inst/valuation level to the
       Iris/Pred level via RHeap = RInst SHeap SCHeap.  chunk_gc uses
       acc_refl (no world motion), which is why refine_T (not refine_four)
       is enough to discharge the □ᵣ box. *)
    Lemma refine_chunk_gc {w} :
      ⊢ ℛ⟦RHeapSpec RUnit⟧ cchunk_gc (chunk_gc (w := w)).
    Proof.
      unfold cchunk_gc, chunk_gc.
      iIntros (cΦ sΦ) "#rΦ %ch %sh #rh".
      iPoseProof (refine_T with "rΦ") as "rΦ'".
      iApply ("rΦ'" $! tt tt with "[] [rh]").
      - done.
      - iStopProof.
        unfold RHeap, RInst; crushPredEntails3.
        rewrite inst_gc_heap H2.
        reflexivity.
    Qed.

    #[export] Instance refine_compat_chunk_gc {w} :
      RefineCompat (RHeapSpec RUnit) cchunk_gc w (chunk_gc (w := w)) _ :=
      MkRefineCompat refine_chunk_gc.

    (* Heap-only companion to refine_chunk_gc, for bullets that need to
       transport an ALREADY-INTRODUCED heap fact (rh : ℛ⟦RHeap⟧ ch sh) across
       the GC filter directly — i.e. after iIntros'ing ch/sh but BEFORE
       calling rsolve on the next bind in the sequence.  Going through
       refine_chunk_gc's generic RefineCompat/rsolve pairing instead would
       introduce a spurious extra world for chunk_gc's step (rsolve cannot
       see that chunk_gc's own acc_refl makes that step's world motion
       trivial), and Acc composition doesn't associate definitionally, so
       that extra world's accessibility gets stuck later in the proof. *)
    Lemma refine_gc_heap {w : World} (ch : SCHeap) (sh : SHeap w) :
      (ℛ⟦RHeap⟧ ch sh ⊢ ℛ⟦RHeap⟧ (cgc_heap ch) (gc_heap sh))%I.
    Proof.
      constructor. intros ι Hpc Hrel.
      unfold RHeap, RInst, repₚ in *. cbn in *.
      now rewrite inst_gc_heap Hrel.
    Qed.

    Import PureSpec.

    (* ------------------------------------------------------------------ *)
    (* Table faithfulness: bridge between the term-table symbolic executor *)
    (* (sexec_cfg_addr) and the gmap-based concrete executor            *)
    (* (cexec_cfg_addr).  itable_rel/etable_rel are Pred-level premises:    *)
    (* every key term must instantiate to a SyncVal address that the gmap   *)
    (* maps to the paired instruction (resp. that satisfies exitCond).      *)
    (* The ∃-SyncVal form is essential: with an implication form the        *)
    (* concrete executor errors at RVToOption on NonSyncVal keys while the  *)
    (* symbolic one proceeds, breaking refinement.                          *)
    (* ------------------------------------------------------------------ *)

    (* TODO: All this machinery surrounding SInstrTable and gmap and SExitTable deserves its own section, module or even file. *)
    Definition itable_rel {w} (instrs : gmap (bv xlenbits) AnnotInstr) (tbl : SInstrTable w) : Pred w :=
      fun ι => List.Forall
        (fun p => exists v, inst (fst p) ι = ty.SyncVal v /\ instrs !! v = Some (snd p)) tbl.

    (* itable_relW: the same faithfulness statement for the EXECUTOR's table
       (SInstrTableW), i.e. with the word column.  Because one table entry
       carries both, the two gmap lookups the concrete executor performs are
       tied together here — which is what makes cexec_cfg_addr's
       `words !! v = None` branch unreachable under this relation.

       This is DERIVED, not assumed: the assumed guard stays the word-free
       itable_rel at the contract context Σ (so TablesRel.v's faith lemmas and
       EndToEnd.v are untouched), and itable_relW_zip below builds this from it
       plus the refinement of the per-address word variables. *)
    Definition itable_relW {w} (instrs : gmap (bv xlenbits) AnnotInstr)
        (words : bv xlenbits -> bv word) (tbl : SInstrTableW w) : Pred w :=
      fun ι => List.Forall
        (fun '(t,x,i) => exists v,
           inst (T := fun Σ => Term Σ ty_xlenbits) t ι = ty.SyncVal v
           /\ instrs !! v = Some i
           /\ inst (T := fun Σ => Term Σ ty_word) x ι = ty.SyncVal (words v)) tbl.

    (* wtable_rel: the boundary bookkeeping for the per-address words.  The n
       demonically chosen word values must be exactly the ones `words` holds at
       the table's addresses.  Used at TWO worlds: as the concrete-side assumed
       guard at the contract context Σ (cexec_triple_addr, alongside
       itable_rel), and as the transported fact at the executor's world
       (wtable_rel_of_faith_forget) that itable_relW_zip then consumes.

       Note what this is NOT: loop-carried.  It is consumed once, at the entry
       point, to build itable_relW — which is the payoff of fusing the word
       into the table instead of keeping a parallel word table.  Only ONE
       relation has to survive the induction on fuel, and it needs no
       persist/forgetting/lookup family of its own. *)
    Definition wtable_rel {w} (words : bv xlenbits -> bv word)
        (tbl : SInstrTable w) (cws : list (RelVal ty_word)) : Pred w :=
      fun ι => List.Forall2
        (fun p cx => exists v,
           inst (T := fun Σ => Term Σ ty_xlenbits) (fst p) ι = ty.SyncVal v
           /\ cx = ty.SyncVal (words v)) tbl cws.

    Definition etable_rel {w} (exitCond : bv xlenbits -> bool) (exits : SExitTable w) : Pred w :=
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

    (* One lookup yields BOTH the word term and the instruction, so this
       returns the gmap facts for both columns at once. *)
    Lemma lookup_instr_sound {w} (instrs : gmap (bv xlenbits) AnnotInstr)
        (words : bv xlenbits -> bv word) (tbl : SInstrTableW w)
        (apc : STerm ty_xlenbits w) (x : Term (wctx w) ty_word) (i : AnnotInstr)
        (ι : Valuation w) :
      lookup_instr tbl apc = Some (x, i) ->
      itable_relW instrs words tbl ι ->
      exists v, inst apc ι = ty.SyncVal v /\ instrs !! v = Some i
                /\ inst (T := fun Σ => Term Σ ty_word) x ι = ty.SyncVal (words v).
    Proof.
      unfold lookup_instr, itable_relW.
      intros Hlk Hrel.
      destruct (List.find _ tbl) as [[[t x'] i']|] eqn:Hfind; cbn in Hlk; [|discriminate].
      injection Hlk as -> ->.
      apply find_some in Hfind as [Hin Heqb].
      rewrite List.Forall_forall in Hrel.
      specialize (Hrel _ Hin) as (v & Hv & Hmap & Hx).
      exists v.
      split; [|split; [exact Hmap|exact Hx]].
      rewrite (peval_eqb_inst apc t ι Heqb).
      exact Hv.
    Qed.

    Lemma is_exit_sound {w} (exitCond : bv xlenbits -> bool) (exits : SExitTable w)
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
        (instrs : gmap (bv xlenbits) AnnotInstr) (tbl : SInstrTable w1) :
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

    Lemma forgetting_itable_relW {w1 w2} (θ : Acc w1 w2)
        (instrs : gmap (bv xlenbits) AnnotInstr) (words : bv xlenbits -> bv word)
        (tbl : SInstrTableW w1) :
      (forgetting θ (itable_relW instrs words tbl)
       ⊣⊢ itable_relW instrs words (persist_itableW θ tbl))%I.
    Proof.
      constructor.
      intros ι.
      unfold forgetting, itable_relW, persist_itableW.
      rewrite List.Forall_map.
      cbn.
      split; apply List.Forall_impl; intros [[t x] i] (v & Hv & Hm & Hx);
        exists v; cbn in *;
        rewrite ?inst_persist in Hv, Hx |- *;
        (split; [exact Hv|split; [exact Hm|exact Hx]]).
    Qed.

    Lemma persist_itableW_refl {w} (tbl : SInstrTableW w) :
      persist_itableW acc_refl tbl = tbl.
    Proof.
      unfold persist_itableW.
      induction tbl as [|[[t x] i] tbl' IH]; cbn; [reflexivity|].
      cbn in IH.
      f_equal.
      exact IH.
    Qed.

    Lemma persist_itableW_trans {w1 w2 w3} (θ12 : Acc w1 w2) (θ23 : Acc w2 w3)
        (tbl : SInstrTableW w1) :
      persist_itableW θ23 (persist_itableW θ12 tbl) = persist_itableW (acc_trans θ12 θ23) tbl.
    Proof.
      unfold persist_itableW.
      rewrite List.map_map.
      apply List.map_ext.
      intros [[t x] i].
      now rewrite !persist_trans.
    Qed.

    Lemma forgetting_etable_rel {w1 w2} (θ : Acc w1 w2)
        (exitCond : bv xlenbits -> bool) (exits : SExitTable w1) :
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

    Lemma persist_itable_refl {w} (tbl : SInstrTable w) :
      persist_itable acc_refl tbl = tbl.
    Proof.
      unfold persist_itable.
      induction tbl as [|[t i] tbl' IH]; cbn; [reflexivity|].
      cbn in IH.
      f_equal.
      exact IH.
    Qed.

    Lemma persist_etable_refl {w} (exits : SExitTable w) :
      persist_etable acc_refl exits = exits.
    Proof.
      unfold persist_etable.
      induction exits as [|t exits' IH]; cbn; [reflexivity|].
      cbn in IH.
      f_equal.
      exact IH.
    Qed.

    Lemma persist_itable_trans {w1 w2 w3} (θ12 : Acc w1 w2) (θ23 : Acc w2 w3) (tbl : SInstrTable w1) :
      persist_itable θ23 (persist_itable θ12 tbl) = persist_itable (acc_trans θ12 θ23) tbl.
    Proof.
      unfold persist_itable.
      rewrite List.map_map.
      apply List.map_ext.
      intros [t i].
      now rewrite persist_trans.
    Qed.

    Lemma persist_etable_trans {w1 w2 w3} (θ12 : Acc w1 w2) (θ23 : Acc w2 w3) (exits : SExitTable w1) :
      persist_etable θ23 (persist_etable θ12 exits) = persist_etable (acc_trans θ12 θ23) exits.
    Proof.
      unfold persist_etable.
      rewrite List.map_map.
      apply List.map_ext.
      intros t.
      now rewrite persist_trans.
    Qed.

    (* The word column comes out as a repₚ rather than a pure fact: the
       refinement of the recursive call needs ℛ⟦RVal ty_word⟧ (SyncVal y) x,
       which is exactly repₚ (SyncVal y) x. *)
    Lemma lookup_instr_sound_repₚ {w} (instrs : gmap (bv xlenbits) AnnotInstr)
        (words : bv xlenbits -> bv word) (tbl : SInstrTableW w)
        (apc : STerm ty_xlenbits w) (x : Term (wctx w) ty_word) (i : AnnotInstr)
        (a : RelVal ty_xlenbits) :
      lookup_instr tbl apc = Some (x, i) ->
      (itable_relW instrs words tbl ∗ repₚ (T := fun Σ => Term Σ ty_xlenbits) a apc ⊢
       ∃ v, ⌜a = ty.SyncVal v /\ instrs !! v = Some i⌝ ∗
            repₚ (T := fun Σ => Term Σ ty_word) (ty.SyncVal (words v)) x)%I.
    Proof.
      intros Hlk.
      constructor.
      intros ι Hpc H.
      cbn in H.
      destruct H as [Hrel Ha].
      destruct (lookup_instr_sound apc Hlk Hrel) as (v & Hv & Hm & Hx).
      exists v.
      split; [split; [|exact Hm]|exact Hx].
      now rewrite <- Ha.
    Qed.

    Lemma is_exit_sound_repₚ {w} (exitCond : bv xlenbits -> bool) (exits : SExitTable w)
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

    (* rexec_ghosts: refinement of the ghost interpreter, for an ARBITRARY
       ghost list.  It must be inductive: in rexec_cfg_addr the list is
       `ai_ghost_before ai` with `ai` opaque out of lookup_instr, so no finite
       set of instances (a gc_binds_heap-style rewrite) can discharge it —
       gc_binds_heap only works because chunk_gc is a CLOSED term.

       The □ᵣ / unconditionally_T wrapper is REQUIRED, not stylistic: without
       it the IH lands at the wrong world and iApply simply cannot apply it,
       which fails in a way that looks nothing like "you need a box".  Both
       rexec_cfg_addr below and main's rexec_annotated_block_addr open with the
       same iAssert.  The 2026-08-20 attempt at a ghost lemma copied main's
       TACTIC without this surrounding structure and was never made to work
       (it hung 300 s+, root cause never found); with the structure the whole
       thing is ~11 s and every step is an idiom already used in this file.
       Developed in isolation first — see the ZZGhostRefineProbe.v record in
       PLAN-annotinstr.md — precisely so a failure here would be attributable
       to the plumbing rather than to the lemma.  Re-validated in that same
       probe on 2026-08-24 with BOTH sides carrying a real call_lemma, which
       is the configuration Phase 4 lands: still no hang. *)
    Lemma rexec_ghosts (gs : list Annot) {w} :
      ⊢ ℛ⟦RHeapSpec RUnit⟧ (cexec_ghosts gs) (sexec_ghosts gs (w := w)).
    Proof.
      iAssert (ℛ⟦□ᵣ (RHeapSpec RUnit)⟧ (cexec_ghosts gs)
                 (fun w' θ => sexec_ghosts gs (w := w'))) as "H".
      { iInduction gs as [| a gs] "IH"; cbn; rsolve.
        2: { iPoseProof (forgetting_unconditionally_drastic with "IH") as "IH2".
             iApply "IH2". }
        (* No `iApply refine_unit` here, and that is not an oversight: it was
           needed ONLY while AnnotLemmaInvocation was an `error` stub, because
           the error case closed trivially and left the debug case's
           `ℛ⟦?RA⟧ () ()` with ?RA still an evar, so the registered
           `ℛ⟦RUnit⟧` hint could not fire.  With a real call_lemma on both
           sides rsolve resolves that evar from the pairing, exactly as
           predicted when the stub went in.  Both cases close here, 915 ms. *)
        destruct a; cbn; rsolve. }
      now iApply (unconditionally_T with "H").
    Qed.

    (* So rsolve dispatches the two ghost binds in sexec_cfg_addr's step the
       way it already dispatches sexec_instruction's, rather than needing them
       spelled out by hand in rexec_cfg_addr below. *)
    #[export] Instance refine_compat_exec_ghosts {gs : list Annot} {w} :
      RefineCompat (RHeapSpec RUnit)
        (cexec_ghosts gs) w (sexec_ghosts gs (w := w)) _ :=
      MkRefineCompat (rexec_ghosts gs).

    (* ================================================================== *)
    (* THE DROPK REFINEMENT FRAMEWORK.                                     *)
    (*                                                                    *)
    (* Ported verbatim from Example/ZZDropRefineProbe.v and                *)
    (* Example/ZZRexecDropProbe.v (2026-08-31), where it was built and       *)
    (* checked interactively -- pet cannot open THIS file, so everything     *)
    (* below was developed against those two probes.  cdrop_dead is NOT      *)
    (* re-declared here: it already exists above (the concrete mirror of the *)
    (* drop, an identity CHeapSpec action).                                  *)
    (* ================================================================== *)
  Section Fac.
    Context {A : LCtx -> Type} {SubstA : Subst A} {SubstLawsA : SubstLaws A}
            {OccA : OccursCheck A} {OccLawsA : OccursCheckLaws A}.

    (* Generic in the VALUE type V: rdrop_dead uses it at Unit (drop_dead returns
       nothing), but sexec_cfg_addr's own ambient continuation carries an
       STerm ty_xlenbits, and that is the Factors the drop's premise is derived
       from.  Nothing in the three lemmas below inspects V. *)
    Definition Factors {V : TYPE} {w : World} (a : A (wctx w))
        (sPhi : forall w2 : World, Acc w w2 -> V w2 -> SHeap w2 -> 𝕊 w2) : Prop :=
      exists g : forall w2 : World, A (wctx w2) -> V w2 -> SHeap w2 -> 𝕊 w2,
        forall (w2 : World) (om : Acc w w2) (v : V w2) (h : SHeap w2),
          sPhi w2 om v h = g w2 (persist (A := A) a om) v h.

    (* CLOSED: and note the new carrier is `persist a om`, which is EXACTLY
       what drop_dead already passes to its recursive call.  That is why the
       executor threads the carrier at all. *)
    Lemma factors_four {V : TYPE} {w : World} (a : A (wctx w))
        (sPhi : forall w2 : World, Acc w w2 -> V w2 -> SHeap w2 -> 𝕊 w2)
        {w1 : World} (om : Acc w w1) :
      Factors a sPhi -> Factors (persist (A := A) a om) (four sPhi om).
    Proof.
      intros [g Hg]. exists g. intros w2 om2 v h.
      unfold four. rewrite Hg. now rewrite persist_trans.
    Qed.

    (* SUFFICIENT: an x-free carrier makes the continuation blind to the drop's
       witness, which is the whole gap Phase 0's Hindep had to bridge.  The
       x-freeness premise is `occurs_check xIn a = Some a'` -- precisely what
       var_dead computes. *)
    Lemma factors_witness_indep {V : TYPE} {w : World} {x : LVar} {σ : Ty}
        {xIn : (x∷σ ∈ w)%katamaran} {pc' : PathCondition (wctx w - x∷σ)}
        (Hpc : occurs_check xIn (wco w) = Some pc')
        (a : A (wctx w)) (a' : A (wctx w - x∷σ))
        (Ha : occurs_check xIn a = Some a')
        (sPhi : forall w2 : World, Acc w w2 -> V w2 -> SHeap w2 -> 𝕊 w2)
        (Hfac : Factors a sPhi)
        (t1 t2 : Term (wctx w - x∷σ) σ) (w2 : World)
        (om2 : Acc (@wdrop w x σ xIn) w2) (v : V w2) (h : SHeap w2) :
      sPhi w2 (acc_trans (@acc_drop w x σ xIn pc' Hpc t1) om2) v h
      = sPhi w2 (acc_trans (@acc_drop w x σ xIn pc' Hpc t2) om2) v h.
    Proof.
      destruct Hfac as [g Hg]. rewrite !Hg. f_equal.
      rewrite !persist_trans. f_equal.
      rewrite !persist_subst. cbn.
      pose proof (occurs_check_sound xIn a) as HH.
      unfold OccursCheckSoundPoint in HH. rewrite Ha in HH.
      inversion HH as [? Heq|]. rewrite Heq.
      now rewrite !subst_shift_single.
    Qed.
    (* factors_witness_indep needs only substitution-invariance of the carrier,
       not an occurs-check on it.  Saying so directly DECOUPLES the carrier from
       OccursCheck instances -- which matters, because the real carrier bundles
       tbl/exits and those deliberately have none (Verifier.v spells their check
       out over the term columns instead). *)
    Definition WitnessBlind {w : World} {x : LVar} {σ : Ty}
        (xIn : (x∷σ ∈ w)%katamaran) (a : A (wctx w)) : Prop :=
      forall t1 t2 : Term (wctx w - x∷σ) σ,
        subst a (sub_single xIn t1) = subst a (sub_single xIn t2).

    (* ...and it follows from the occurs-check for any component that has one,
       so componentwise checks feed a bundled carrier. *)
    Lemma witness_blind_of_oc {w : World} {x : LVar} {σ : Ty}
        {xIn : (x∷σ ∈ w)%katamaran} (a : A (wctx w)) (a' : A (wctx w - x∷σ))
        (Ha : occurs_check xIn a = Some a') : WitnessBlind xIn a.
    Proof.
      intros t1 t2.
      pose proof (occurs_check_sound xIn a) as HH.
      unfold OccursCheckSoundPoint in HH. rewrite Ha in HH.
      inversion HH as [? Heq|]. rewrite Heq.
      now rewrite !subst_shift_single.
    Qed.

    Lemma factors_witness_indep' {V : TYPE} {w : World} {x : LVar} {σ : Ty}
        {xIn : (x∷σ ∈ w)%katamaran} {pc' : PathCondition (wctx w - x∷σ)}
        (Hpc : occurs_check xIn (wco w) = Some pc')
        (a : A (wctx w)) (Hbl : WitnessBlind xIn a)
        (sPhi : forall w2 : World, Acc w w2 -> V w2 -> SHeap w2 -> 𝕊 w2)
        (Hfac : Factors a sPhi)
        (t1 t2 : Term (wctx w - x∷σ) σ) (w2 : World)
        (om2 : Acc (@wdrop w x σ xIn) w2) (v : V w2) (h : SHeap w2) :
      sPhi w2 (acc_trans (@acc_drop w x σ xIn pc' Hpc t1) om2) v h
      = sPhi w2 (acc_trans (@acc_drop w x σ xIn pc' Hpc t2) om2) v h.
    Proof.
      destruct Hfac as [g Hg]. rewrite !Hg. f_equal.
      rewrite !persist_trans. f_equal.
      rewrite !persist_subst. cbn. apply Hbl.
    Qed.
  End Fac.

  (* ================================================================== *)
  (* The premise machinery, complete.  Together these give rdrop_dead's  *)
  (* induction exactly what it needs, with `Factors (dbundle ...) sPhi`  *)
  (* as the ONLY premise:                                                *)
  (*   - at the recursive call, factors_four + dbundle_persist           *)
  (*     re-establish it;                                                *)
  (*   - at the drop, wb_bundle + factors_witness_indep' kill the        *)
  (*     witness dependence.                                             *)
  (* WitnessBlind is therefore a LEMMA from var_dead, not a premise --   *)
  (* which is what makes the induction close at all.                     *)
  (* ================================================================== *)

  Lemma wb_of_ocok {A : LCtx -> Type} {SubstA : Subst A} {SubstLawsA : SubstLaws A}
      {OccA : OccursCheck A} {OccLawsA : OccursCheckLaws A}
      {w : World} {x σ} (xIn : (x∷σ ∈ w)%katamaran) (a : A (wctx w)) :
    oc_ok xIn a = true -> WitnessBlind xIn a.
  Proof.
    unfold oc_ok. destruct (occurs_check xIn a) eqn:E; [|discriminate].
    intros _. exact (witness_blind_of_oc E).
  Qed.

  Lemma wb_etable {w : World} {x σ} (xIn : (x∷σ ∈ w)%katamaran) (l : SExitTable w) :
    etable_free xIn l = true ->
    @WitnessBlind (fun Sg => list (Term Sg ty_xlenbits)) _ w x σ xIn l.
  Proof.
    unfold etable_free. intros H t1 t2.
    induction l as [|t l' IH]; cbn in *; [reflexivity|].
    apply Bool.andb_true_iff in H as [H1 H2].
    rewrite (IH H2). f_equal. exact (wb_of_ocok xIn t H1 t1 t2).
  Qed.

  Lemma wb_itableW {w : World} {x σ} (xIn : (x∷σ ∈ w)%katamaran) (l : SInstrTableW w) :
    itableW_free xIn l = true ->
    @WitnessBlind (fun Sg => list (Term Sg ty_xlenbits * Term Sg ty_word * AnnotInstr)) _ w x σ xIn l.
  Proof.
    unfold itableW_free. intros H t1 t2.
    induction l as [|[[t v] i] l' IH]; cbn in *; [reflexivity|].
    apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.andb_true_iff in H1 as [Ha Hb].
    rewrite (IH H2). f_equal. f_equal. f_equal.
    exact (wb_of_ocok xIn t Ha t1 t2).
    exact (wb_of_ocok xIn v Hb t1 t2).
  Qed.

  (* SIX components, not five.  `wd` (the instruction word out of lookup_instr)
     is captured by the drop's continuation -- step_after_drop persists it by
     theta_d like everything else -- so the Factors carrier must cover it or the
     witness does not exist.  It costs nothing operationally: var_dead's new
     conjunct is implied by itableW_free, since wd IS one of the table's words. *)
  Definition dcarrier (Sg0 : LCtx) : LCtx -> Type :=
    fun Sg => (Sub Sg0 Sg *
               list (Term Sg ty_xlenbits * Term Sg ty_word * AnnotInstr) *
               list (Term Sg ty_xlenbits) *
               Term Sg ty_xlenbits *
               Term Sg ty_xlenbits *
               Term Sg ty_word)%type.

  Definition dbundle {Sg0 : LCtx} {w : World}
      (trans : Sub Sg0 w) (tbl : SInstrTableW w) (exits : SExitTable w)
      (apc anp : Term (wctx w) ty_xlenbits) (wd : Term (wctx w) ty_word)
      : dcarrier Sg0 (wctx w) :=
    (trans, tbl, exits, apc, anp, wd).

  Lemma wb_bundle {Sg0 : LCtx} {w : World} {x σ} (xIn : (x∷σ ∈ w)%katamaran)
      (trans : Sub Sg0 w) (tbl : SInstrTableW w) (exits : SExitTable w)
      (apc anp : Term (wctx w) ty_xlenbits) (wd : Term (wctx w) ty_word)
      (h : SHeap (wctx w)) :
    var_dead xIn trans tbl exits apc anp wd h = true ->
    @WitnessBlind (dcarrier Sg0) _ w x σ xIn (dbundle trans tbl exits apc anp wd).
  Proof.
    unfold var_dead. intros H t1 t2.
    apply Bool.andb_true_iff in H as [H Hwd].
    apply Bool.andb_true_iff in H as [H Hex].
    apply Bool.andb_true_iff in H as [H Htbl].
    apply Bool.andb_true_iff in H as [H Hanp].
    apply Bool.andb_true_iff in H as [H Hapc].
    apply Bool.andb_true_iff in H as [H Htr].
    apply Bool.andb_true_iff in H as [Hpc Hh].
    unfold dbundle. cbn.
    f_equal. f_equal. f_equal. f_equal. f_equal.
    - exact (wb_of_ocok xIn trans Htr t1 t2).
    - exact (wb_itableW xIn tbl Htbl t1 t2).
    - exact (wb_etable xIn exits Hex t1 t2).
    - exact (wb_of_ocok xIn apc Hapc t1 t2).
    - exact (wb_of_ocok xIn anp Hanp t1 t2).
    - exact (wb_of_ocok xIn wd Hwd t1 t2).
  Qed.

  (* §4bis's flagged bridges.  destruct the ACCESSIBILITY first: SubstList is a
     Fixpoint not a List.map (so List.map_ext does not apply), and cbn unfolds
     persist__term to persistent_subst (after which persist_subst no longer
     matches syntactically).  Case-splitting the Acc sidesteps both. *)
  Lemma zz_persist_itableW_subst {w1 w2 : World} (th : Acc w1 w2) (tbl : SInstrTableW w1) :
    persist_itableW th tbl
    = subst (T := fun Sg : LCtx => list (Term Sg ty_xlenbits * Term Sg ty_word * AnnotInstr))
        tbl (sub_acc th).
  Proof.
    unfold persist_itableW. cbn. destruct th; cbn.
    - induction tbl as [|[[t v] i] tbl' IH]; cbn; [reflexivity|].
      rewrite IH. now rewrite !subst_sub_id.
    - induction tbl as [|[[t v] i] tbl' IH]; cbn; [reflexivity|].
      now rewrite IH.
  Qed.

  Lemma zz_persist_etable_subst {w1 w2 : World} (th : Acc w1 w2) (exits : SExitTable w1) :
    persist_etable th exits
    = subst (T := fun Sg : LCtx => list (Term Sg ty_xlenbits)) exits (sub_acc th).
  Proof.
    unfold persist_etable. destruct th; cbn.
    - induction exits as [|t exits' IH]; cbn; [reflexivity|].
      rewrite IH. now rewrite !subst_sub_id.
    - induction exits as [|t exits' IH]; cbn; [reflexivity|].
      now rewrite IH.
  Qed.

  (* CLOSURE at the value level: the bundle commutes with persisting, and the
     right-hand side is literally what drop_dead passes to its recursive call. *)
  Lemma dbundle_persist {Sg0 : LCtx} {w1 w2 : World} (om : Acc w1 w2)
      (trans : Sub Sg0 w1) (tbl : SInstrTableW w1) (exits : SExitTable w1)
      (apc anp : Term (wctx w1) ty_xlenbits) (wd : Term (wctx w1) ty_word) :
    persist (A := dcarrier Sg0) (dbundle trans tbl exits apc anp wd) om
    = dbundle (persist (A := Sub Sg0) trans om) (persist_itableW om tbl)
        (persist_etable om exits) (persist__term apc om) (persist__term anp om)
        (persist__term wd om).
  Proof.
    unfold dbundle, dcarrier.
    rewrite zz_persist_itableW_subst. rewrite zz_persist_etable_subst.
    unfold persist__term. destruct om; cbn; now rewrite ?subst_sub_id.
  Qed.

  (* ================================================================== *)
  (* rdrop_dead: the refinement of the drop chain.                       *)
  (*                                                                    *)
  (* Stated POINTWISE (`... iota -> ... iota`) per PLAN-dropk §10 -- the *)
  (* unary `⊢` will not parse after a binder here, and the probe has no  *)
  (* ModalNotations.  RProp/psafe need the LogicalSoundness. prefix.     *)
  (*                                                                    *)
  (* This is Phase 0's zz_dropk_step, generalised to the fuel-indexed    *)
  (* chain, with `Factors` as the SINGLE premise.                        *)
  (* ================================================================== *)
  Import logicalrelation logicalrelation.notations.

  Lemma rdrop_dead_base {Sg0 : LCtx} : forall (w : World)
      (trans : Sub Sg0 w) (tbl : SInstrTableW w) (exits : SExitTable w)
      (apc anp : Term (wctx w) ty_xlenbits) (wd : Term (wctx w) ty_word)
      (cPhi : unit -> SCHeap -> Prop)
      (sPhi : forall w2 : World, Acc w w2 -> Unit w2 -> SHeap w2 -> 𝕊 w2)
      (ch : SCHeap) (sh : SHeap (wctx w))
      (iota : Valuation w) (Hpc : instprop (wco w) iota),
      ℛ⟦RBox (RImpl RUnit (RImpl RHeap LogicalSoundness.RProp))⟧ cPhi sPhi iota ->
      ℛ⟦RHeap⟧ ch sh iota ->
      LogicalSoundness.psafe (drop_dead 0 trans tbl exits apc anp wd sPhi sh) iota ->
      cPhi tt ch.
  Proof.
    intros. cbn in *.
    unfold RBox, RImpl in H. cbn in H.
    unfold unconditionally, assuming in H.
    specialize (H w acc_refl iota (inst_sub_id iota) Hpc).
    cbn in H, H1.
    specialize (H tt tt).
    rewrite wand_unfold in H.
    specialize (H eq_refl ch sh).
    rewrite wand_unfold in H.
    specialize (H H0).
    unfold LogicalSoundness.RProp in H. cbn in H.
    rewrite wand_unfold in H. apply H.
    unfold SHeapSpec.pure, T in H1. exact H1.
  Qed.

  (* find_dead hands back a bare sigT with no proof attached, so var_dead's
     verdict has to be recovered by an induction over the fold.  cbn [List.fold_right]
     and NOT plain cbn: plain cbn normalises the LVar alias to string, after which
     the destruct's equation no longer matches syntactically. *)
  Lemma find_dead_sound {Sg0 : LCtx} {w : World}
      (trans : Sub Sg0 w) (tbl : SInstrTableW w) (exits : SExitTable w)
      (apc anp : Term (wctx w) ty_xlenbits) (wd : Term (wctx w) ty_word)
      (h : SHeap (wctx w)) (c : drop_candidate w) :
    find_dead trans tbl exits apc anp wd h = Some c ->
    var_dead (projT1 (projT2 c)) trans tbl exits apc anp wd h = true.
  Proof.
    unfold find_dead.
    generalize (all_ins (wctx w)) as l. intros l.
    revert c. induction l as [|p l' IH]; intros c; cbn [List.fold_right]; [discriminate|].
    destruct (List.fold_right _ None l') as [c'|] eqn:E.
    - exact (IH c).
    - destruct (var_dead (projT2 p) trans tbl exits apc anp wd h) eqn:Ev; [|discriminate].
      destruct (ty.inhabit (type (projT1 p))) as [v|]; [|discriminate].
      intros Hc. inversion Hc. cbn. exact Ev.
  Qed.

  (* BOX TRANSPORT ACROSS THE DROP -- the real content of rdrop_dead's step case.
     Phase 0 CONSUMED the box at the drop; the fuel-indexed chain must instead
     HAND ONE DOWN, so the box has to survive the world hop.

     The move is Phase 0's zz_box_at_chosen composed with factors_witness_indep':
     instantiate the box at `acc_trans (acc_drop t_iota) om2` with the witness READ
     OFF iota (which makes the fibre inhabited by construction, so `assuming` does
     not go vacuous), then slide from that witness to the tree's fixed t0.  The
     slide is exactly what Factors + WitnessBlind buy. *)
  (* Factors' equation is POINTWISE (fully applied) rather than an equality of
     functions.  That is load-bearing, not stylistic: the composite obligation in
     factors_drop_cont compares the executor applied to two POINTWISE-equal
     continuations, and turning that into an equality of the continuations
     themselves is exactly funext.  Pointwise, CExt closes it instead.

     The cost is that factors_witness_indep' can no longer be used as a `rewrite`
     at a function position inside the relation.  This lemma pays it: the relation
     only ever uses its continuation APPLIED, so a pointwise equality suffices. *)
  Lemma rel_pointwise {w2 : World} (cPhi : unit -> SCHeap -> Prop)
      (f1 f2 : Unit w2 -> SHeap w2 -> 𝕊 w2) (iota2 : Valuation w2) :
    (forall v h, f1 v h = f2 v h) ->
    ℛ⟦RImpl RUnit (RImpl RHeap LogicalSoundness.RProp)⟧ cPhi f1 iota2 ->
    ℛ⟦RImpl RUnit (RImpl RHeap LogicalSoundness.RProp)⟧ cPhi f2 iota2.
  Proof.
    intros Hpt H. unfold RSat, RImpl in *. cbn in *.
    intros a v. specialize (H a v).
    rewrite wand_unfold in H |- *. intros Hav ch sh.
    specialize (H Hav ch sh).
    rewrite wand_unfold in H |- *. intros Hheap.
    specialize (H Hheap).
    unfold LogicalSoundness.RProp in *. cbn in *.
    rewrite wand_unfold in H |- *. intros Hsafe.
    apply H. now rewrite Hpt.
  Qed.

  Section BoxDrop.
    Context {A : LCtx -> Type} {SubstA : Subst A} {SubstLawsA : SubstLaws A}.

    Lemma factors_box_drop {w : World} {x : LVar} {σ : Ty}
        {xIn : (x∷σ ∈ w)%katamaran} {pc' : PathCondition (wctx w - x∷σ)}
        (Hpc : occurs_check xIn (wco w) = Some pc')
        (a : A (wctx w)) (Hbl : WitnessBlind xIn a)
        (cPhi : unit -> SCHeap -> Prop)
        (sPhi : forall w2 : World, Acc w w2 -> Unit w2 -> SHeap w2 -> 𝕊 w2)
        (Hfac : Factors a sPhi)
        (t0 : Term (wctx w - x∷σ) σ)
        (iota : Valuation w) (Hpci : instprop (wco w) iota) :
      ℛ⟦RBox (RImpl RUnit (RImpl RHeap LogicalSoundness.RProp))⟧ cPhi sPhi iota ->
      ℛ⟦RBox (RImpl RUnit (RImpl RHeap LogicalSoundness.RProp))⟧ cPhi
        (four sPhi (@acc_drop w x σ xIn pc' Hpc t0)) (inst (sub_shift xIn) iota).
    Proof.
      intros HB. unfold RSat, RBox in *. cbn in *.
      unfold unconditionally, assuming in *.
      intros w2 om2 iota2 Hfib Hpc2.
      specialize (HB w2 (acc_trans (@acc_drop w x σ xIn pc' Hpc
                                      (term_relval σ (env.lookup iota xIn))) om2) iota2).
      assert (HB' : ℛ⟦RImpl RUnit (RImpl RHeap LogicalSoundness.RProp)⟧ cPhi
                      (sPhi w2 (acc_trans (@acc_drop w x σ xIn pc' Hpc
                         (term_relval σ (env.lookup iota xIn))) om2)) iota2).
      { apply HB; [|exact Hpc2].
        (* the fibre over iota is inhabited BY CONSTRUCTION: the witness was read
           off iota, so sub_single puts back exactly what sub_shift removed. *)
        cbn. rewrite sub_acc_trans. rewrite inst_subst. rewrite Hfib.
        cbn [sub_acc]. apply inst_sub_single_shift. reflexivity. }
      unfold four.
      eapply rel_pointwise; [|exact HB'].
      intros v h.
      apply (factors_witness_indep' Hpc Hbl Hfac
               (term_relval σ (env.lookup iota xIn)) t0 om2).
    Qed.
  End BoxDrop.

  (* CONVOY ELIMINATION.  drop_dead's inner match is a convoy -- it scrutinises
     `occurs_check bIn (wco w)` while its motive mentions that same term on the
     LEFT of the equation -- so a plain `destruct ... eqn:` abstracts the motive's
     LHS too and the branch's `acc_drop Hpc0 t0` stops typechecking (`o0 = Some pc'`
     is not `occurs_check bIn (wco w) = Some pc'`).  Abstracting the SCRUTINEE and
     the equation's RHS only is what this lemma packages: its `S` is a variable, so
     `destruct S` is legal, and the two branch obligations arrive with the equation
     intact. *)
  Lemma option_convoy {X : Type} {T : Type} {S : option X} {P : T -> Prop}
      (f : forall v : X, S = Some v -> T) (g : S = None -> T)
      (Hf : forall v (e : S = Some v), P (f v e))
      (Hg : forall e : S = None, P (g e)) :
    P (match S as o return S = o -> T with
       | Some v => f v
       | None   => g
       end eq_refl).
  Proof.
    revert f g Hf Hg. generalize (@eq_refl _ S).
    destruct S as [v|]; intros e f g Hf Hg; [apply Hf | apply Hg].
  Qed.

  (* Transport across the projection: path condition, dropped world's pc, heap. *)
  Lemma zz_wco_eq {w : World} {x σ} {xIn : (x∷σ ∈ w)%katamaran}
      {pc' : PathCondition (wctx w - x∷σ)}
      (Hoc : occurs_check xIn (wco w) = Some pc') :
    wco w = subst pc' (sub_shift xIn).
  Proof.
    pose proof (occurs_check_sound xIn (wco w)) as HH.
    unfold OccursCheckSoundPoint in HH. rewrite Hoc in HH. now inversion HH.
  Qed.

  (* `cbn [wco]`, NOT `cbn`: plain cbn normalises the LVar alias to string and
     then `rewrite Hoc` finds no subterm -- the same trap as find_dead_sound. *)
  Lemma wco_wdrop {w : World} {x σ} {xIn : (x∷σ ∈ w)%katamaran}
      {pc' : PathCondition (wctx w - x∷σ)}
      (Hoc : occurs_check xIn (wco w) = Some pc') :
    wco (@wdrop w x σ xIn) = pc'.
  Proof. unfold wdrop. cbn [wco]. now rewrite Hoc. Qed.

  Lemma zz_heap_transport {w : World} {x σ} {xIn : (x∷σ ∈ w)%katamaran}
      (sh : SHeap (wctx w)) (h' : SHeap (wctx w - x∷σ))
      (Hh : occurs_check xIn sh = Some h') (iota : Valuation w) :
    inst h' (inst (sub_shift xIn) iota) = inst sh iota.
  Proof.
    pose proof (occurs_check_sound (T := SHeap) xIn sh) as HH.
    unfold OccursCheckSoundPoint in HH. rewrite Hh in HH. inversion HH; subst.
    now rewrite inst_subst.
  Qed.

  (* THE LEAF.  Same content as rdrop_dead_base but stated at `sPhi w acc_refl tt sh`
     instead of `drop_dead 0 ...`, which matters: rdrop_dead reaches this leaf at
     FOUR places (fuel = 0, and the three degenerate branches of a step), and at
     three of them `trans`/`tbl`/`exits`/`apc`/`anp` are NOT determined by anything
     in the conclusion.  Going through rdrop_dead_base there leaves them as SHELVED
     evars and `Qed` fails with "the proof term is not complete" -- with no open goal
     shown.  Dropping the executor arguments from the leaf's statement removes the
     underdetermination at the source. *)
  Lemma rdrop_leaf {w : World}
      (cPhi : unit -> SCHeap -> Prop)
      (sPhi : forall w2 : World, Acc w w2 -> Unit w2 -> SHeap w2 -> 𝕊 w2)
      (ch : SCHeap) (sh : SHeap (wctx w))
      (iota : Valuation w) (Hpc : instprop (wco w) iota) :
    ℛ⟦RBox (RImpl RUnit (RImpl RHeap LogicalSoundness.RProp))⟧ cPhi sPhi iota ->
    ℛ⟦RHeap⟧ ch sh iota ->
    LogicalSoundness.psafe (sPhi w acc_refl tt sh) iota ->
    cPhi tt ch.
  Proof.
    intros H H0 H1. cbn in *.
    unfold RBox, RImpl in H. cbn in H.
    unfold unconditionally, assuming in H.
    specialize (H w acc_refl iota (inst_sub_id iota) Hpc).
    cbn in H, H1.
    specialize (H tt tt).
    rewrite wand_unfold in H.
    specialize (H eq_refl ch sh).
    rewrite wand_unfold in H.
    specialize (H H0).
    unfold LogicalSoundness.RProp in H. cbn in H.
    rewrite wand_unfold in H. apply H. exact H1.
  Qed.

  (* rdrop_dead: the same statement at arbitrary `fuel`, by induction, with
     `Factors` as the SINGLE premise.  This is Phase 0's zz_dropk_step generalised
     to the fuel-indexed chain.

     Four branches.  Three are leaves (fuel = 0; no dead variable found; the heap's
     own occurs-check fails) and go straight to rdrop_leaf.  The fourth is the drop:

       - option_convoy splits the convoy and hands back `e : occurs_check bIn (wco w)
         = Some v`, the equation acc_drop needs;
       - psafe of a dropk node IS `forgetting acc_forget`, so Hsafe arrives at the
         valuation `inst (sub_shift bIn) iota` -- exactly the IH's;
       - find_dead_sound + wb_bundle turn find_dead's verdict into WitnessBlind,
         which is what makes the box survive the hop (factors_box_drop);
       - factors_four + dbundle_persist re-establish Factors at the smaller world,
         and the carrier they produce is literally the tuple drop_dead already
         passes to its recursive call.  That is why drop_dead threads one. *)
  Lemma rdrop_dead {Sg0 : LCtx} (fuel : nat) : forall (w : World)
      (trans : Sub Sg0 w) (tbl : SInstrTableW w) (exits : SExitTable w)
      (apc anp : Term (wctx w) ty_xlenbits) (wd : Term (wctx w) ty_word)
      (cPhi : unit -> SCHeap -> Prop)
      (sPhi : forall w2 : World, Acc w w2 -> Unit w2 -> SHeap w2 -> 𝕊 w2)
      (ch : SCHeap) (sh : SHeap (wctx w))
      (Hfac : Factors (dbundle trans tbl exits apc anp wd) sPhi)
      (iota : Valuation w) (Hpc : instprop (wco w) iota),
      ℛ⟦RBox (RImpl RUnit (RImpl RHeap LogicalSoundness.RProp))⟧ cPhi sPhi iota ->
      ℛ⟦RHeap⟧ ch sh iota ->
      LogicalSoundness.psafe (drop_dead fuel trans tbl exits apc anp wd sPhi sh) iota ->
      cPhi tt ch.
  Proof.
    induction fuel as [|n IH];
      intros w trans tbl exits apc anp wd cPhi sPhi ch sh Hfac iota Hpc HB Hheap Hsafe.
    - exact (rdrop_leaf Hpc HB Hheap Hsafe).
    - cbn [drop_dead] in Hsafe.
      destruct (find_dead trans tbl exits apc anp wd sh) as [c|] eqn:Ec;
        [|exact (rdrop_leaf Hpc HB Hheap Hsafe)].
      pose proof (find_dead_sound trans tbl exits apc anp wd sh Ec) as Hdead.
      destruct c as [b [bIn t0]]. cbn [projT1 projT2] in Hsafe, Ec, Hdead.
      destruct (occurs_check bIn sh) as [h'|] eqn:Eh;
        [|exact (rdrop_leaf Hpc HB Hheap Hsafe)].
      revert Hsafe.
      (* %type: logicalrelation.notations overloads `->` as RImpl, so an unannotated
         motive is parsed in Rel scope and fails with "expected type Rel ?AT ?A". *)
      apply (option_convoy (P := fun s => (LogicalSoundness.psafe s iota -> cPhi tt ch)%type)).
      2: { intros _ Hsafe. exact (rdrop_leaf Hpc HB Hheap Hsafe). }
      intros v e Hsafe.
      cbn [LogicalSoundness.psafe] in Hsafe.
      unfold forgetting, acc_forget in Hsafe. cbn [sub_acc] in Hsafe.
      pose proof (wb_bundle bIn trans tbl exits apc anp wd sh Hdead) as Hbl.
      refine (IH (@wdrop w (name b) (type b) bIn) _ _ _ _ _ _ cPhi
                (four sPhi (acc_drop e t0)) ch h' _ (inst (sub_shift bIn) iota) _ _ _ Hsafe).
      + rewrite <- dbundle_persist. exact (factors_four _ Hfac).
      + rewrite (wco_wdrop e).
        apply (instprop_subst (sub_shift bIn) iota v).
        (* NOT `rewrite <- (zz_wco_eq e)`: the goal's `sub_shift bIn` is indexed by
           `b`, the lemma's by `MkB (name b) (type b)` -- convertible, not syntactically
           equal.  Rewriting in a COPY of Hpc, where `wco w` matches on the nose, and
           closing by conversion sidesteps it. *)
        pose proof Hpc as Hp. rewrite (zz_wco_eq e) in Hp. exact Hp.
      + exact (factors_box_drop e Hbl Hfac t0 Hpc HB).
      + exact (eq_trans (zz_heap_transport sh Eh iota) Hheap).
  Qed.


  (* ================================================================== *)
  (* THE PROPAGATION -- what the whole PExt/CExt framework was built for. *)
  (*                                                                    *)
  (* From Factors for sexec_cfg_addr's AMBIENT continuation, derive Factors *)
  (* for the continuation drop_dead actually receives.  This is the step    *)
  (* that needed funext before the framework existed:                       *)
  (*                                                                        *)
  (*   SHeapSpec.bind m f Phi = m (fun w1 th1 a1 => f w1 th1 a1 (four Phi th1)) *)
  (*                                                                        *)
  (* so drop_dead's continuation is `step_after_drop ... (four Phi thd)`, and  *)
  (* the witness g must reproduce it from the persisted bundle alone.  The     *)
  (* persisted arguments match on the nose (dbundle_persist); the two          *)
  (* CONTINUATIONS are only POINTWISE equal, and cext_step_after_drop is what   *)
  (* turns that into the tree equality Factors asks for. *)
  (* ================================================================== *)
  Lemma factors_drop_cont {Sg0 : LCtx} {w : World} (n' : nat) (ai : AnnotInstr)
      (trans : Sub Sg0 w) (tbl : SInstrTableW w) (exits : SExitTable w)
      (apc anp : Term (wctx w) ty_xlenbits) (wd : Term (wctx w) ty_word)
      (Phi : forall w2 : World, Acc w w2 -> STerm ty_xlenbits w2 -> SHeap w2 -> 𝕊 w2)
      (HPhi : Factors (dbundle trans tbl exits apc anp wd) Phi) :
    Factors (dbundle trans tbl exits apc anp wd)
      (fun w1 (om : Acc w w1) (_ : Unit w1) =>
         step_after_drop (@sexec_cfg_addr Sg0 n') ai
           (persist (A := Sub Sg0) trans om) (persist_itableW om tbl)
           (persist_etable om exits) (persist__term apc om) (persist__term anp om)
           (persist__term wd om) (four Phi om)).
  Proof.
    destruct HPhi as [g Hg].
    (* q1..q6 and NOT tr/tb/ex/pc/np/wd: `pc` is a RISC-V REGISTER constructor,
       so that pattern name is read as a Reg and the `exists` fails with
       "Found a constructor of inductive type Reg while a constructor of Term
       is expected". *)
    exists (fun w1 (bnd : dcarrier Sg0 (wctx w1)) (_ : Unit w1) =>
              let '(q1, q2, q3, q4, q5, q6) := bnd in
              step_after_drop (@sexec_cfg_addr Sg0 n') ai q1 q2 q3 q4 q5 q6
                (fun w' om' => g w' (persist (A := dcarrier Sg0) bnd om'))).
    intros w2 om v h.
    rewrite dbundle_persist. cbn [dbundle].
    apply cext_step_after_drop.
    - intros. apply cext_sexec_cfg_addr.
    - intros w' th' a' h'. unfold four. rewrite Hg.
      f_equal. rewrite persist_trans. now rewrite dbundle_persist.
  Qed.


  (* ================================================================== *)
  (* CARRIER WEAKENING -- what lets rexec_cfg_addr carry a FIVE-component  *)
  (* premise while the drop needs six.                                     *)
  (*                                                                       *)
  (* At the top of sexec_cfg_addr there is no `wd` yet: it comes out of      *)
  (* lookup_instr, INSIDE the step.  So the premise threaded through the     *)
  (* fuel induction is over (trans, tbl, exits, apc, anp) and the sixth       *)
  (* column is added at the drop site.  That is sound because Factors is      *)
  (* MONOTONE in the carrier -- a bigger carrier gives g more to work with,   *)
  (* so it is the WEAKER condition. *)
  (* ================================================================== *)
  Definition dcarrier5 (Sg0 : LCtx) : LCtx -> Type :=
    fun Sg => (Sub Sg0 Sg *
               list (Term Sg ty_xlenbits * Term Sg ty_word * AnnotInstr) *
               list (Term Sg ty_xlenbits) *
               Term Sg ty_xlenbits *
               Term Sg ty_xlenbits)%type.

  Definition dbundle5 {Sg0 : LCtx} {w : World}
      (trans : Sub Sg0 w) (tbl : SInstrTableW w) (exits : SExitTable w)
      (apc anp : Term (wctx w) ty_xlenbits) : dcarrier5 Sg0 (wctx w) :=
    (trans, tbl, exits, apc, anp).

  (* The six-tuple IS the five-tuple paired with wd, definitionally -- which is
     what makes factors_pair_l applicable without any repackaging. *)
  Lemma dbundle6_eq {Sg0 : LCtx} {w : World}
      (trans : Sub Sg0 w) (tbl : SInstrTableW w) (exits : SExitTable w)
      (apc anp : Term (wctx w) ty_xlenbits) (wd : Term (wctx w) ty_word) :
    dbundle trans tbl exits apc anp wd = (dbundle5 trans tbl exits apc anp, wd).
  Proof. reflexivity. Qed.

  Lemma factors_pair_l {A B : LCtx -> Type}
      {SubstA : Subst A} {SubstLawsA : SubstLaws A}
      {SubstB : Subst B} {SubstLawsB : SubstLaws B}
      {V : TYPE} {w : World} (a : A (wctx w)) (b : B (wctx w))
      (sPhi : forall w2 : World, Acc w w2 -> V w2 -> SHeap w2 -> 𝕊 w2) :
    Factors a sPhi -> Factors (A := fun Sg => (A Sg * B Sg)%type) (a, b) sPhi.
  Proof.
    intros [g Hg]. exists (fun w2 p => g w2 (fst p)).
    intros w2 om v h. rewrite Hg. cbn. f_equal.
    (* `cbn` alone will NOT reduce (persist (a,b) om).1 -- persistent_subst
       matches on the accessibility, so it has to be destructed. *)
    destruct om; cbn; reflexivity.
  Qed.

  Lemma dbundle5_persist {Sg0 : LCtx} {w1 w2 : World} (om : Acc w1 w2)
      (trans : Sub Sg0 w1) (tbl : SInstrTableW w1) (exits : SExitTable w1)
      (apc anp : Term (wctx w1) ty_xlenbits) :
    persist (A := dcarrier5 Sg0) (dbundle5 trans tbl exits apc anp) om
    = dbundle5 (persist (A := Sub Sg0) trans om) (persist_itableW om tbl)
        (persist_etable om exits) (persist__term apc om) (persist__term anp om).
  Proof.
    unfold dbundle5, dcarrier5.
    rewrite zz_persist_itableW_subst. rewrite zz_persist_etable_subst.
    unfold persist__term. destruct om; cbn; now rewrite ?subst_sub_id.
  Qed.

  (* THE FORM rexec_cfg_addr WILL ACTUALLY USE at the drop's bind: from the
     five-component premise threaded through the fuel induction, produce exactly
     the six-component Factors that rdrop_dead consumes.

     factors_pair_l's A and B must be given EXPLICITLY -- the goal's carrier is
     `dcarrier Sg0`, not syntactically `fun Sg => (?A Sg * ?B Sg)`, so
     unification cannot invert it. *)
  Lemma factors_drop_at_step {Sg0 : LCtx} {w : World} (n' : nat) (ai : AnnotInstr)
      (trans : Sub Sg0 w) (tbl : SInstrTableW w) (exits : SExitTable w)
      (apc anp : Term (wctx w) ty_xlenbits) (wd : Term (wctx w) ty_word)
      (Phi : forall w2 : World, Acc w w2 -> STerm ty_xlenbits w2 -> SHeap w2 -> 𝕊 w2)
      (HPhi : Factors (dbundle5 trans tbl exits apc anp) Phi) :
    Factors (dbundle trans tbl exits apc anp wd)
      (fun w1 (om : Acc w w1) (_ : Unit w1) =>
         step_after_drop (@sexec_cfg_addr Sg0 n') ai
           (persist (A := Sub Sg0) trans om) (persist_itableW om tbl)
           (persist_etable om exits) (persist__term apc om) (persist__term anp om)
           (persist__term wd om) (four Phi om)).
  Proof.
    apply factors_drop_cont.
    rewrite dbundle6_eq.
    apply (factors_pair_l (A := dcarrier5 Sg0) (B := fun Sg => Term Sg ty_word)).
    exact HPhi.
  Qed.

    Definition dcarrier3 (Sg0 : LCtx) : LCtx -> Type :=
      fun Sg => (Sub Sg0 Sg *
                 list (Term Sg ty_xlenbits * Term Sg ty_word * AnnotInstr) *
                 list (Term Sg ty_xlenbits))%type.

    Definition dbundle3 {Sg0 : LCtx} {w : World}
        (trans : Sub Sg0 w) (tbl : SInstrTableW w) (exits : SExitTable w)
        : dcarrier3 Sg0 (wctx w) := (trans, tbl, exits).

    Lemma dbundle5_eq {Sg0 : LCtx} {w : World}
        (trans : Sub Sg0 w) (tbl : SInstrTableW w) (exits : SExitTable w)
        (apc anp : Term (wctx w) ty_xlenbits) :
      dbundle5 trans tbl exits apc anp = ((dbundle3 trans tbl exits, apc), anp).
    Proof. reflexivity. Qed.

    Lemma dbundle3_persist {Sg0 : LCtx} {w1 w2 : World} (om : Acc w1 w2)
        (trans : Sub Sg0 w1) (tbl : SInstrTableW w1) (exits : SExitTable w1) :
      persist (A := dcarrier3 Sg0) (dbundle3 trans tbl exits) om
      = dbundle3 (persist (A := Sub Sg0) trans om) (persist_itableW om tbl)
          (persist_etable om exits).
    Proof.
      unfold dbundle3, dcarrier3.
      rewrite zz_persist_itableW_subst. rewrite zz_persist_etable_subst.
      destruct om; cbn; now rewrite ?subst_sub_id.
    Qed.

    Lemma factors_widen5 {Sg0 : LCtx} {w : World} {V : TYPE}
        (trans : Sub Sg0 w) (tbl : SInstrTableW w) (exits : SExitTable w)
        (apc anp : Term (wctx w) ty_xlenbits)
        (Phi : forall w2 : World, Acc w w2 -> V w2 -> SHeap w2 -> 𝕊 w2) :
      Factors (dbundle3 trans tbl exits) Phi ->
      Factors (dbundle5 trans tbl exits apc anp) Phi.
    Proof.
      intros H. rewrite dbundle5_eq.
      apply (factors_pair_l (A := fun Sg => (dcarrier3 Sg0 Sg * Term Sg ty_xlenbits)%type)
                            (B := fun Sg => Term Sg ty_xlenbits)).
      apply (factors_pair_l (A := dcarrier3 Sg0) (B := fun Sg => Term Sg ty_xlenbits)).
      exact H.
    Qed.

    (* ================================================================== *)
    (* OMEGA-INDEPENDENCE -- the premise the OUTER triple needs.           *)
    (*                                                                    *)
    (* PLAN-dropk.md §20 predicted four carriers threaded through five     *)
    (* binds.  It is less than that: the outer continuations only ever     *)
    (* need to be omega-INDEPENDENT, a property `four` preserves for free, *)
    (* and a carrier is needed at exactly ONE bind -- the executor's,      *)
    (* whose tail is `consume ens (persist delta1 (theta2 o theta3)).[..]`.*)
    (* ================================================================== *)
    Definition OmegaIndep {V : TYPE} {w : World}
        (sPhi : forall w2 : World, Acc w w2 -> V w2 -> SHeap w2 -> 𝕊 w2) : Prop :=
      exists g : forall w2 : World, V w2 -> SHeap w2 -> 𝕊 w2,
        forall (w2 : World) (om : Acc w w2) (v : V w2) (h : SHeap w2),
          sPhi w2 om v h = g w2 v h.

    Lemma omega_indep_four {V : TYPE} {w w1 : World} (om : Acc w w1)
        (sPhi : forall w2 : World, Acc w w2 -> V w2 -> SHeap w2 -> 𝕊 w2) :
      OmegaIndep sPhi -> OmegaIndep (four sPhi om).
    Proof. intros [g Hg]. exists g. intros w2 om2 v h. unfold four. apply Hg. Qed.

    (* SHeapSpec.run's constant continuation: what discharges the premise
       at the top of the chain, in rcfg_verification_condition. *)
    Lemma omega_indep_block {V : TYPE} {w : World} :
      OmegaIndep (fun (w1 : World) (_ : Acc w w1) (_ : V w1) (_ : SHeap w1) => SymProp.block).
    Proof. exists (fun w1 _ _ => SymProp.block). reflexivity. Qed.

    Lemma factors_of_omega_indep {A : LCtx -> Type} {SubstA : Subst A}
        {V : TYPE} {w : World} (a : A (wctx w))
        (sPhi : forall w2 : World, Acc w w2 -> V w2 -> SHeap w2 -> 𝕊 w2) :
      OmegaIndep sPhi -> Factors (A := A) a sPhi.
    Proof. intros [g Hg]. exists (fun w2 _ v h => g w2 v h). exact Hg. Qed.

    (* THE LINCHPIN.  The executor call site's own continuation Factors,
       given only omega-independence of the triple's ambient one.
       `consume` is applied to `four sPhi om`, which MENTIONS om, so no
       carrier can see it syntactically -- that is §16's funext wall in
       miniature.  CExt closes it pointwise: consume respects
       pointwise-equal continuations. *)
    Lemma factors_consume_tail {Sg0 : LCtx} {w1 w : World}
        (ens : Assertion (Sg0 ▻ "an"∷ty_xlenbits))
        (th : Acc w1 w) (d1 : Sub Sg0 w1)
        (tbl : SInstrTableW w) (exits : SExitTable w)
        (sPhi : forall w2 : World, Acc w w2 -> Unit w2 -> SHeap w2 -> 𝕊 w2)
        (Hoi : OmegaIndep sPhi) :
      Factors (dbundle3 (persist d1 th) tbl exits)
        (fun (w3 : World) (om : Acc w w3) (na : Term w3 ty_xlenbits) (h3 : SHeap w3) =>
           SHeapSpec.consume ens (persist d1 (acc_trans th om)).["an"∷ty_xlenbits ↦ na]
             (four sPhi om) h3).
    Proof.
      destruct Hoi as [g2 Hg2].
      exists (fun (w3 : World) (bnd : dcarrier3 Sg0 w3) (na : Term w3 ty_xlenbits) (h3 : SHeap w3) =>
                SHeapSpec.consume ens (fst (fst bnd)).["an"∷ty_xlenbits ↦ na]
                  (fun (w4 : World) (_ : Acc w3 w4) (v : Unit w4) (h : SHeap w4) => g2 w4 v h) h3).
      intros w3 om na h3.
      rewrite persist_trans.
      rewrite dbundle3_persist.
      cbn [dbundle3 fst].
      apply SHeapSpec.cext_consume.
      intros w4 th4 v h. unfold four. apply Hg2.
    Qed.

    Lemma rprop_error {w : World} (c : Prop) (msg : AMessage w) :
      ⊢ ℛ⟦LogicalSoundness.RProp⟧ c (SymProp.error msg).
    Proof. unfold LogicalSoundness.RProp; cbn. iIntros "%HF". destruct HF. Qed.

    Lemma rprop_or {w : World} (c1 c2 : Prop) (s1 s2 : 𝕊 w) :
      ℛ⟦LogicalSoundness.RProp⟧ c1 s1 -∗
      ℛ⟦LogicalSoundness.RProp⟧ c2 s2 -∗
      ℛ⟦LogicalSoundness.RProp⟧ (c1 \/ c2) (SymProp.angelic_binary s1 s2).
    Proof.
      unfold LogicalSoundness.RProp; cbn.
      iIntros "H1 H2 [Hs|Hs]".
      - iDestruct ("H1" with "Hs") as "%Hc". iPureIntro. now left.
      - iDestruct ("H2" with "Hs") as "%Hc". iPureIntro. now right.
    Qed.

    (* rdrop_dead is stated POINTWISE at a valuation; this lifts it to an Iris
       entailment so it can be iApply'd.  Phase 0's idiom (zz_dropk_step):
       `constructor. intros iota Hpc _. rewrite !wand_unfold.` *)
    Lemma rdrop_dead_iris {Sg0 : LCtx} (fuel : nat) {w : World}
        (trans : Sub Sg0 w) (tbl : SInstrTableW w) (exits : SExitTable w)
        (apc anp : Term w ty_xlenbits) (wd : Term w ty_word)
        (cPhi : unit -> SCHeap -> Prop)
        (sPhi : forall w2 : World, Acc w w2 -> Unit w2 -> SHeap w2 -> 𝕊 w2)
        (ch : SCHeap) (sh : SHeap w)
        (Hfac : Factors (dbundle trans tbl exits apc anp wd) sPhi) :
      ℛ⟦□ᵣ (RUnit -> RHeap -> LogicalSoundness.RProp)⟧ cPhi sPhi -∗
      ℛ⟦RHeap⟧ ch sh -∗
      ℛ⟦LogicalSoundness.RProp⟧ (cPhi tt ch)
         (drop_dead fuel trans tbl exits apc anp wd sPhi sh).
    Proof.
      constructor. intros iota Hpc _.
      rewrite !wand_unfold. intros HB Hheap Hsafe.
      exact (rdrop_dead fuel Hfac Hpc HB Hheap Hsafe).
    Qed.

    Lemma rexF0 (instrs : gmap (bv xlenbits) AnnotInstr)
        (words : bv xlenbits -> bv word) (exitCond : bv xlenbits -> bool)
        {Σ0 : LCtx} :
      forall (w : World) (trans : Sub Σ0 w)
        (tbl : SInstrTableW w) (exits : SExitTable w),
      (itable_relW instrs words tbl ∗ etable_rel exitCond exits ⊢
       ∀ a ta, ℛ⟦RVal ty_xlenbits⟧ a ta -∗
       ∀ na tna, ℛ⟦RVal ty_xlenbits⟧ na tna -∗
       ∀ cΦ sΦ, ⌜Factors (dbundle3 trans tbl exits) sΦ⌝ -∗
         ℛ⟦□ᵣ (RVal ty_xlenbits -> RHeap -> LogicalSoundness.RProp)⟧ cΦ sΦ -∗
       ∀ ch sh, ℛ⟦RHeap⟧ ch sh -∗
         ℛ⟦LogicalSoundness.RProp⟧
            (cexec_cfg_addr instrs words exitCond 0 a na cΦ ch)
            (sexec_cfg_addr 0 trans tbl exits ta tna sΦ sh))%I.
    Proof.
      intros w trans tbl exits.
      iIntros "#[Hi He]".
      iIntros (a ta) "#Ha". iIntros (na tna) "#Hna".
      iIntros (cΦ sΦ) "%Hfac". iIntros "#rΦ". iIntros (ch sh) "#rh".
      cbn [sexec_cfg_addr cexec_cfg_addr].
      unfold LogicalSoundness.RProp; cbn.
      iIntros "%HF". destruct HF.
    Qed.

    Lemma rexFS (instrs : gmap (bv xlenbits) AnnotInstr)
        (words : bv xlenbits -> bv word) (exitCond : bv xlenbits -> bool)
        {Σ0 : LCtx} (n' : nat)
        (IH : forall (w : World) (trans : Sub Σ0 w)
                (tbl : SInstrTableW w) (exits : SExitTable w),
           (itable_relW instrs words tbl ∗ etable_rel exitCond exits ⊢
            ∀ a ta, ℛ⟦RVal ty_xlenbits⟧ a ta -∗
            ∀ na tna, ℛ⟦RVal ty_xlenbits⟧ na tna -∗
            ∀ cΦ sΦ, ⌜Factors (dbundle3 trans tbl exits) sΦ⌝ -∗
              ℛ⟦□ᵣ (RVal ty_xlenbits -> RHeap -> LogicalSoundness.RProp)⟧ cΦ sΦ -∗
            ∀ ch sh, ℛ⟦RHeap⟧ ch sh -∗
              ℛ⟦LogicalSoundness.RProp⟧
                 (cexec_cfg_addr instrs words exitCond n' a na cΦ ch)
                 (sexec_cfg_addr n' trans tbl exits ta tna sΦ sh))%I) :
      forall (w : World) (trans : Sub Σ0 w)
        (tbl : SInstrTableW w) (exits : SExitTable w),
      (itable_relW instrs words tbl ∗ etable_rel exitCond exits ⊢
       ∀ a ta, ℛ⟦RVal ty_xlenbits⟧ a ta -∗
       ∀ na tna, ℛ⟦RVal ty_xlenbits⟧ na tna -∗
       ∀ cΦ sΦ, ⌜Factors (dbundle3 trans tbl exits) sΦ⌝ -∗
         ℛ⟦□ᵣ (RVal ty_xlenbits -> RHeap -> LogicalSoundness.RProp)⟧ cΦ sΦ -∗
       ∀ ch sh, ℛ⟦RHeap⟧ ch sh -∗
         ℛ⟦LogicalSoundness.RProp⟧
            (cexec_cfg_addr instrs words exitCond (S n') a na cΦ ch)
            (sexec_cfg_addr (S n') trans tbl exits ta tna sΦ sh))%I.
    Proof.
      intros w trans tbl exits.
      iIntros "#[Hi He]".
      iIntros (a ta) "#Ha". iIntros (na tna) "#Hna".
      iIntros (cΦ sΦ) "%Hfac". iIntros "#rΦ". iIntros (ch sh) "#rh".
      cbn [sexec_cfg_addr cexec_cfg_addr].
      destruct (is_exit exits ta) eqn:Hex;
        destruct (lookup_instr tbl ta) as [[wd ai]|] eqn:Hlk.

      (* ---- 4: exit-miss / lookup-miss.  Both symbolic branches are errors, *)
      (* so psafe is False on either side of the angelic split.               *)
      4: { destruct a as [va|va1 va2]; cbn [ty.RVToOption];
           unfold LogicalSoundness.RProp; cbn;
           iIntros "[%HF|%HF]"; destruct HF. }

      (* ---- 3: exit-miss / lookup-hit.  THE CORE -- this is the branch that *)
      (* actually contains the drop.  Driven to the frontier below.           *)
      3: { iDestruct (lookup_instr_sound_repₚ instrs words _ _ a Hlk with "[$Hi $Ha]")
             as (v) "[%Hfact #Hx]".
           destruct Hfact as (-> & Hm).
           cbn [ty.RVToOption]. rewrite Hm.
           (* BOTH angelic_binary's must be unfolded before rprop_or applies:
              the concrete one is CHeapSpec's, the symbolic one SHeapSpec's, and
              rprop_or is stated over SymProp.angelic_binary. *)
           unfold CHeapSpec.angelic_binary, SHeapSpec.angelic_binary.
           iApply rprop_or; [iApply rprop_error|].
           (* Eliminate both chunk_gc binds and the concrete drop bind.  After
              this the goal is EXACTLY rdrop_dead_iris's shape. *)
           rewrite cgc_binds_heap cdrop_binds gc_binds_heap.
           unfold T; cbv beta.
           unfold SHeapSpec.bind at 1.
           rewrite (persist_itableW_refl tbl) (persist_etable_refl exits).
           (* `persist x acc_refl` needs NO rewrite -- persistent_subst matches on
              the accessibility, so acc_refl reduces definitionally.  Only the
              bespoke table persists need their _refl lemmas. *)
           match goal with |- context [ ?C cΦ (cgc_heap ch) ] => set (crest := C) end.
           unshelve iApply (rdrop_dead_iris drop_fuel (fun _ ch' => crest cΦ ch')
                              (cgc_heap ch) (gc_heap sh) _).
           - (* Factors for the drop's own continuation: widen the loop-carried
                3-carrier to the 5-carrier the drop wants, then hand it over. *)
             apply factors_drop_at_step. apply factors_widen5. exact Hfac.
           - (* THE CONTINUATION BOX -- the frontier.  `iModIntro` introduces
                `assuming`, so the box opens cleanly and everything in context
                lands under `forgetting θ1`. *)
             iIntros (w1 θ1). iModIntro. iIntros (u tu) "_".
             iIntros (ch' sh') "#rh'".
             unfold step_after_drop.
             iClear "rh".
             (* ---- THE BOX-LOCKSTEP RULE, and it is the whole trick here. ----
                The goal's continuation grows a `four` tower, one layer per bind:
                  four (four (four (four sΦ θ1) θ0) θ2) θ3
                while the IPM context ACCUMULATES the accessibility the other
                way -- `into_assuming_forgetting` merges each intro into a single
                left-nested forgetting (((θ1∘θ0)∘θ2)∘θ3).  Those two are equal
                only up to associativity of acc_trans, which is NOT definitional
                and has no lemma (Acc carries an entailment PROOF, so proving it
                would need proof irrelevance).
                Fix: convert the box with `forgetting_unconditionally` AFTER EVERY
                intro, so it grows its own `four` layer in step with the goal and
                the two never have to be reconciled.  Do NOT batch the intros and
                convert once at the end -- that is exactly the shape that cannot
                be closed.  (forgetting_unconditionally_drastic, which the old
                rexec_cfg_addr used, is the WRONG tool here: it lands the relation
                at ONE world instead of rebuilding the box.) *)
             iPoseProof (forgetting_unconditionally with "rΦ") as "rQ1".
             iClear "rΦ".
             (* `unfold crest` is REQUIRED before any of this: rsolve and the
                pointwise binds both need to SEE the concrete side's bind chain,
                and `set` had hidden it behind a local definition. *)
             unfold crest.
             (* ---- ghosts-before.  Note this is NOT rsolve.  rsolve dispatches
                a bind through the generic refine_bind, whose box obligation
                UNIVERSALLY QUANTIFIES the symbolic continuation -- and with the
                drop inside sexec_cfg_addr that goal is FALSE.  Unfolding the two
                binds by hand and applying the component's own RHeapSpec
                refinement keeps sΦ concrete, which is what lets factors_four
                re-establish Factors at the recursive call. *)
             unfold CHeapSpec.bind at 1, SHeapSpec.bind at 1.
             iApply (rexec_ghosts (ai_ghost_before ai)).
             2: iApply "rh'".
             iIntros (w0 θ0). iModIntro. iIntros (u0 tu0) "_".
             iIntros (ch0 sh0) "#rh0".
             iPoseProof (forgetting_unconditionally with "rQ1") as "rQ2".
             iClear "rQ1".
             (* ---- the instruction.  Its three RVal arguments come out as
                persist towers; refine_inst_persist needs them collapsed to a
                SINGLE persist first, hence the `<- persist_trans`.  The innermost
                `persist _ acc_refl` needs no lemma -- persistent_subst matches on
                the accessibility, so it reduces definitionally (checked). *)
             unfold CHeapSpec.bind at 1, SHeapSpec.bind at 1.
             iApply (rexec_instruction (ai_instr ai)).
             1: (rewrite <- (persist_trans (A := STerm ty_xlenbits));
                 iApply (refine_inst_persist with "Ha")).
             1: (rewrite <- (persist_trans (A := STerm ty_xlenbits));
                 iApply (refine_inst_persist with "Hna")).
             1: (rewrite <- (persist_trans (A := STerm ty_word));
                 iApply (refine_inst_persist with "Hx")).
             2: iApply "rh0".
             iIntros (w2 θ2). iModIntro. iIntros (apc' tapc') "#Hapc".
             iIntros (ch2 sh2) "#rh2".
             iPoseProof (forgetting_unconditionally with "rQ2") as "rQ3".
             iClear "rQ2".
             (* ---- ghosts-after *)
             unfold CHeapSpec.bind at 1, SHeapSpec.bind at 1.
             iApply (rexec_ghosts (ai_ghost_after ai)).
             2: iApply "rh2".
             iIntros (w3 θ3). iModIntro. iIntros (u3 tu3) "_".
             iIntros (ch3 sh3) "#rh3".
             iPoseProof (forgetting_unconditionally with "rQ3") as "rQ4".
             iClear "rQ3".
             (* ---- THE RECURSIVE CALL.  Re-establish Factors by walking the
                SAME four layers the goal walked -- one factors_four per bind, in
                the same order -- so F4's continuation is syntactically the goal's
                tower.  Applying factors_four once at the composed accessibility
                would give `four sΦ Θ` instead, and hit the same associativity
                wall as the box. *)
             pose proof (factors_four θ1 Hfac) as F1.
             pose proof (factors_four θ0 F1) as F2.
             pose proof (factors_four θ2 F2) as F3.
             pose proof (factors_four θ3 F3) as F4.
             rewrite !dbundle3_persist in F4.
             clear F1 F2 F3.
             (* Normalise the three loop-carried arguments to F4's FULLY-EXPANDED
                persist form (one layer per hop).  Mind the two orientations:
                persist_itableW_trans/persist_etable_trans are stated
                nested = collapsed, so `<-` expands; persist_trans is stated
                collapsed = nested, so it expands FORWARDS.  Getting persist_trans
                backwards collapses `trans` to an acc_trans chain that then cannot
                match F4. *)
             rewrite forgetting_itable_relW. rewrite forgetting_etable_rel.
             rewrite <- !persist_itableW_trans. rewrite <- !persist_etable_trans.
             rewrite !(persist_trans (A := Sub Σ0)).
             (* The IH is a PLAIN COQ hypothesis applied directly -- `w` is
                generalised in the statement and this is a plain `induction fuel`,
                so there is no boxed IH and no forgetting_unconditionally_drastic. *)
             iApply (IH _ _ _ _ with "[$Hi $He]").
             1: iApply (refine_inst_persist with "Hapc").
             1: iApply (refine_inst_persist with "Hapc").
             1: (iPureIntro; exact F4).
             1: iApply "rQ4".
             1: iApply "rh3".
           - (* the heap argument of rdrop_dead_iris: the drop runs on the
                POST-GC heap on both sides, which is exactly refine_gc_heap. *)
             iApply (refine_gc_heap with "rh"). }

      (* ---- 2: exit-hit / lookup-miss.  Symbolic takes the exit branch. *)
      2: { iPoseProof (is_exit_sound_repₚ exitCond _ _ _ Hex with "[$He $Ha]")
             as "%Hfact".
           destruct Hfact as (v & -> & Hcond).
           cbn [ty.RVToOption]. rewrite Hcond.
           unfold LogicalSoundness.RProp; cbn.
           (* LEFT disjunct is an Iris hypothesis, RIGHT is pure False --
              "[%Hs|%Hs]" fails with "iPure: … not pure". *)
           iIntros "[Hs|%Hs]"; [|destruct Hs].
           iPoseProof (unconditionally_T with "rΦ") as "rΦ0".
           iDestruct ("rΦ0" $! (SyncVal v) ta with "Ha") as "rΦ1".
           iDestruct ("rΦ1" $! ch sh with "rh") as "rΦ2".
           iDestruct ("rΦ2" with "Hs") as "%Hc".
           iPureIntro. left. exact Hc. }

      (* ---- 1: exit-hit / lookup-hit.  BOTH branches of the angelic split are
         live here, so this is case 2 and case 3 glued by rprop_or: the concrete
         LEFT branch is `pure` (not `error`), so rprop_or's first obligation is
         case 2's tail, and its second is case 3 verbatim.
         The opener needs BOTH soundness facts, and `injection Hveq as <-` is
         what identifies the `v` that lookup_instr_sound_repₚ produced with the
         one is_exit_sound_repₚ produced -- they are separately existentially
         quantified and nothing else ties them together. *)
      iDestruct (lookup_instr_sound_repₚ instrs words _ _ a Hlk with "[$Hi $Ha]")
        as (v) "[%Hfact #Hx]".
      destruct Hfact as (-> & Hm).
      iPoseProof (is_exit_sound_repₚ exitCond _ _ _ Hex with "[$He $Ha]")
        as "%Hfact2".
      destruct Hfact2 as (v' & Hveq & Hcond).
      injection Hveq as <-.
      cbn [ty.RVToOption].
      rewrite Hcond. rewrite Hm.
      unfold CHeapSpec.angelic_binary, SHeapSpec.angelic_binary.
      iApply rprop_or.
      - (* exit taken on both sides: pure/pure.  Both `pure`s bind at acc_refl,
           so unfolding T collapses the world bookkeeping and what is left is
           the continuation applied at acc_refl -- i.e. unconditionally_T. *)
        unfold CHeapSpec.pure, SHeapSpec.pure, T; cbv beta.
        iPoseProof (unconditionally_T with "rΦ") as "rΦ0".
        iDestruct ("rΦ0" $! (SyncVal v) ta with "Ha") as "rΦ1".
        iApply ("rΦ1" $! ch sh with "rh").
      - (* execute: case 3 verbatim, bullets renumbered to `+`. *)
        rewrite cgc_binds_heap cdrop_binds gc_binds_heap.
        unfold T; cbv beta.
        unfold SHeapSpec.bind at 1.
        rewrite (persist_itableW_refl tbl) (persist_etable_refl exits).
        match goal with |- context [ ?C cΦ (cgc_heap ch) ] => set (crest := C) end.
        unshelve iApply (rdrop_dead_iris drop_fuel (fun _ ch' => crest cΦ ch')
                           (cgc_heap ch) (gc_heap sh) _).
        + apply factors_drop_at_step. apply factors_widen5. exact Hfac.
        + iIntros (w1 θ1). iModIntro. iIntros (u tu) "_".
          iIntros (ch' sh') "#rh'".
          unfold step_after_drop.
          iClear "rh".
          iPoseProof (forgetting_unconditionally with "rΦ") as "rΦ1".
          iClear "rΦ".
          unfold crest.
          unfold CHeapSpec.bind at 1, SHeapSpec.bind at 1.
          iApply (rexec_ghosts (ai_ghost_before ai)).
          2: iApply "rh'".
          iIntros (w0 θ0). iModIntro. iIntros (u0 tu0) "_".
          iIntros (ch0 sh0) "#rh0".
          iPoseProof (forgetting_unconditionally with "rΦ1") as "rQ2".
          iClear "rΦ1".
          unfold CHeapSpec.bind at 1, SHeapSpec.bind at 1.
          iApply (rexec_instruction (ai_instr ai)).
          1: (rewrite <- (persist_trans (A := STerm ty_xlenbits));
              iApply (refine_inst_persist with "Ha")).
          1: (rewrite <- (persist_trans (A := STerm ty_xlenbits));
              iApply (refine_inst_persist with "Hna")).
          1: (rewrite <- (persist_trans (A := STerm ty_word));
              iApply (refine_inst_persist with "Hx")).
          2: iApply "rh0".
          iIntros (w2 θ2). iModIntro. iIntros (apc' tapc') "#Hapc".
          iIntros (ch2 sh2) "#rh2".
          iPoseProof (forgetting_unconditionally with "rQ2") as "rQ3".
          iClear "rQ2".
          unfold CHeapSpec.bind at 1, SHeapSpec.bind at 1.
          iApply (rexec_ghosts (ai_ghost_after ai)).
          2: iApply "rh2".
          iIntros (w3 θ3). iModIntro. iIntros (u3 tu3) "_".
          iIntros (ch3 sh3) "#rh3".
          iPoseProof (forgetting_unconditionally with "rQ3") as "rQ4".
          iClear "rQ3".
          pose proof (factors_four θ1 Hfac) as F1.
          pose proof (factors_four θ0 F1) as F2.
          pose proof (factors_four θ2 F2) as F3.
          pose proof (factors_four θ3 F3) as F4.
          rewrite !dbundle3_persist in F4.
          clear F1 F2 F3.
          rewrite forgetting_itable_relW. rewrite forgetting_etable_rel.
          rewrite <- !persist_itableW_trans. rewrite <- !persist_etable_trans.
          rewrite !(persist_trans (A := Sub Σ0)).
          iApply (IH _ _ _ _ with "[$Hi $He]").
          1: iApply (refine_inst_persist with "Hapc").
          1: iApply (refine_inst_persist with "Hapc").
          1: (iPureIntro; exact F4).
          1: iApply "rQ4".
          1: iApply "rh3".
        + iApply (refine_gc_heap with "rh").
    Qed.

    (* rexec_cfg_addr: refinement of the gmap concrete executor by the  *)
    (* term-table symbolic executor, under table faithfulness.           *)
    (*                                                                    *)
    (* STATEMENT CHANGED 2026-08-31 (the dropk integration): the folded     *)
    (* `ℛ⟦RVal -> RVal -> RHeapSpec (RVal ty_xlenbits)⟧` form is GONE.       *)
    (* `RHeapSpec RA = □ᵣ(RA -> RHeap -> ℙ) -> RHeap -> ℙ` quantifies its     *)
    (* continuation UNIVERSALLY, and the drop inside sexec_cfg_addr's own    *)
    (* recursion is only sound for a continuation that FACTORS through        *)
    (* persisting trans/tbl/exits (see the Factors framework above) -- an      *)
    (* arbitrary continuation genuinely can violate this, so the premise has   *)
    (* to be an explicit hypothesis, inserted before the box.  Unfolding        *)
    (* RHeapSpec here is otherwise purely mechanical.                           *)
    (*                                                                    *)
    (* Proved by `induction fuel` with `w`/`trans`/`tbl`/`exits` GENERALISED  *)
    (* first -- that is what gives a strong enough IH, so unlike the OLD       *)
    (* proof there is no boxed IH / iInduction / forgetting_unconditionally_  *)
    (* drastic anywhere here.  rexF0/rexFS carry the actual case analysis;     *)
    (* this lemma is three lines.                                             *)
    (*                                                                    *)
    (* `trans` (the accumulated translation) is threaded on the SYMBOLIC side
       only and carries NO relational premise: the concrete executor has no
       logical variables, so there is nothing for it to be related to.  It is a
       fixed argument like tbl/exits, present so the dead-variable drop can
       occurs-check it (PLAN-dropk.md §4bis / Verifier.v's comment on
       sexec_cfg_addr).  cexec_cfg_addr is therefore UNCHANGED. *)
    Lemma rexec_cfg_addr (instrs : gmap (bv xlenbits) AnnotInstr)
        (words : bv xlenbits -> bv word) (exitCond : bv xlenbits -> bool)
        (* `{w : World}` must be ANNOTATED: `trans : Sub Σ0 w` now precedes the
           table arguments, and `Sub` takes an LCtx, so leaving `w` to be
           inferred elaborates it as an LCtx and `SInstrTableW w` then fails. *)
        (fuel : nat) {w : World} {Σ0 : LCtx} (trans : Sub Σ0 w)
        (tbl : SInstrTableW w) (exits : SExitTable w) :
      (itable_relW instrs words tbl ∗ etable_rel exitCond exits ⊢
       ∀ a ta, ℛ⟦RVal ty_xlenbits⟧ a ta -∗
       ∀ na tna, ℛ⟦RVal ty_xlenbits⟧ na tna -∗
       ∀ cΦ sΦ, ⌜Factors (dbundle3 trans tbl exits) sΦ⌝ -∗
         ℛ⟦□ᵣ (RVal ty_xlenbits -> RHeap -> LogicalSoundness.RProp)⟧ cΦ sΦ -∗
       ∀ ch sh, ℛ⟦RHeap⟧ ch sh -∗
         ℛ⟦LogicalSoundness.RProp⟧
            (cexec_cfg_addr instrs words exitCond fuel a na cΦ ch)
            (sexec_cfg_addr fuel trans tbl exits ta tna sΦ sh))%I.
    Proof.
      revert w trans tbl exits.
      induction fuel as [|n' IH]; intros w trans tbl exits.
      - apply rexF0.
      - (* `Set Implicit Arguments` (file top) makes rexFS's instrs/words/
           exitCond IMPLICIT -- they are inferable from IH -- so its first
           EXPLICIT argument is n'.  Passing them positionally mis-slots and
           reports "instrs ... expected to have type nat". *)
        apply (rexFS n' IH).
    Qed.

    (* ------------------------------------------------------------------ *)
    (* VC-level refinement for the term-table verifier (guarded form).     *)
    (* The concrete side cexec_triple_addr is the gmap triple with an   *)
    (* extra assumed faithfulness guard tying the Σ-level key terms to the  *)
    (* concrete gmap at the demonically chosen valuation.  At valuations    *)
    (* where the table does not match the gmap (e.g. a placement variable   *)
    (* instantiated to a different base) the triple holds vacuously; the    *)
    (* end-to-end user discharges the guard at the one valuation where the  *)
    (* program actually resides.  Scaffolding for refinement only — the     *)
    (* concrete executor and soundness chain are untouched.                 *)
    (* ------------------------------------------------------------------ *)

    (* cexec_triple_addr: the concrete triple — right after picking the *)
    (* demonic valuation lenv, ASSUME itable_rel/etable_rel at lenv (i.e.,  *)
    (* table faithfulness w.r.t. the gmap, at w := wlctx Σ) before producing *)
    (* req and running the (still gmap-based) cexec_cfg_addr.  This is the  *)
    (* concrete side of the guarded VC refinement from the reading guide    *)
    (* above (step 5): the guard makes the triple hold vacuously at         *)
    (* valuations where the table doesn't match the gmap, and meaningfully  *)
    (* only at the one valuation the end-to-end proof discharges it at. *)
    (* The concrete-side slicing ops for the word variable.  Defined AS
       uop.evalRel of the very same UnOp the symbolic side applies
       (Verifier.v's wterm_take/wterm_drop), so `inst` of a symbolic slice and
       the concrete slice are the same function up to the standard
       inst-of-term_unop clause — which is why words_of_slice_inst below closes
       on `reflexivity` rather than needing a bridging lemma. *)
    Definition rvtake (m k : nat) : RelVal (ty.bvec (m + k)) -> RelVal (ty.bvec m) :=
      uop.evalRel (uop.bvtake m).
    Definition rvdrop (m k : nat) : RelVal (ty.bvec (m + k)) -> RelVal (ty.bvec k) :=
      uop.evalRel (uop.bvdrop m).

    Definition cexec_triple_addr {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (instrs : gmap (bv xlenbits) AnnotInstr)
      (words : bv xlenbits -> bv word)
      (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
      (tbl : SInstrTable (wlctx Σ)) (exits : SExitTable (wlctx Σ)) : CHeapSpec unit :=
      (* Mirrors sexec_triple_addr's demonic_ctx over Σ ▻▻ words_ctx (length tbl):
         the per-address instruction words are demonically chosen here, ONCE,
         and split back out with env.drop / env.take. *)
      CHeapSpec.bind (CHeapSpec.demonic_ctx (Σ ▻▻ words_ctx (length tbl))) (fun lenvw =>
      let lenv := env.drop (words_ctx (length tbl)) lenvw in
      let cws  := words_of_env rvtake rvdrop (env.take (words_ctx (length tbl)) lenvw) in
      CHeapSpec.bind (CHeapSpec.lift_purespec (CPureSpec.assume_formula
          (itable_rel instrs tbl lenv /\ etable_rel exitCond exits lenv
           /\ wtable_rel words tbl cws lenv))) (fun _ =>
      CHeapSpec.bind (CHeapSpec.demonic _) (fun a =>
      (* Mirrors sexec_triple_addr's single `demonic (Some "np")`: the initial
         nextpc value, quantified ONCE for the whole run rather than once per
         step.  See exec_instruction_prologue (Verifier.v). *)
      CHeapSpec.bind (CHeapSpec.demonic _) (fun np =>
      CHeapSpec.bind (CHeapSpec.produce req lenv.["a"∷ty_xlenbits ↦ a]) (fun _ =>
      CHeapSpec.bind (cexec_cfg_addr instrs words exitCond fuel a np) (fun na =>
      CHeapSpec.consume ens lenv.["a"∷ty_xlenbits ↦ a].["an"∷ty_xlenbits ↦ na])))))).

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

    (* ================================================================== *)
    (* APPLIED-LEVEL PAIRING.  rexec_triple_addr below carries a premise   *)
    (* about its OWN continuation (OmegaIndep), and HeapSpec.refine_bind   *)
    (* destroys that link -- it states its m-premise for ALL continuations *)
    (* while SHeapSpec.bind only ever USES one.  So the five binds are     *)
    (* paired one level down, at RProp, where the continuation stays       *)
    (* concrete.  This is the `cfgver-rsolve` skill's documented remedy    *)
    (* ("pair the binds manually, run rsolve only on the aligned atomic    *)
    (* subgoals"), applied at RProp instead of RHeapSpec; each lemma below *)
    (* is the applied counterpart of one the old proof already used by     *)
    (* hand (refine_bind, refine_guard, and rsolve-on-consume).            *)
    (*                                                                    *)
    (* Do NOT replace these by a bare rsolve on the applied goal: there is *)
    (* no RefineCompat instance at that pairing, so the search DIVERGES    *)
    (* rather than failing -- measured twice at >7.6 GB.                   *)
    (* ================================================================== *)

    Lemma rbind_at `{RA : Rel SA CA, RB : Rel SB CB} {w}
        (cm : CHeapSpec CA) (sm : SHeapSpec SA w)
        (cf : CA -> CHeapSpec CB)
        (sf : forall w1 : World, Acc w w1 -> SA w1 -> SHeapSpec SB w1)
        (cPhi : CB -> SCHeap -> Prop)
        (sPhi : forall w1 : World, Acc w w1 -> SB w1 -> SHeap w1 -> 𝕊 w1)
        (ch : SCHeap) (sh : SHeap w) :
      ℛ⟦RHeapSpec RA⟧ cm sm -∗
      ℛ⟦□ᵣ (RA -> RHeap -> LogicalSoundness.RProp)⟧
         (fun a => cf a cPhi) (fun w1 om a1 h1 => sf w1 om a1 (four sPhi om) h1) -∗
      ℛ⟦RHeap⟧ ch sh -∗
      ℛ⟦LogicalSoundness.RProp⟧
         (CHeapSpec.bind cm cf cPhi ch) (SHeapSpec.bind sm sf sPhi sh).
    Proof.
      iIntros "Hm Hk Hh".
      unfold CHeapSpec.bind. unfold SHeapSpec.bind.
      iApply ("Hm" with "Hk Hh").
    Qed.

    (* The concrete-only guard is DEFINITIONALLY an implication once
       applied to a continuation and a heap, so refine_guard's
       RHeapSpec-level statement is not needed down here. *)
    Lemma guard_reduce {CA} (P : Prop) (c : CHeapSpec CA)
        (cPhi : CA -> SCHeap -> Prop) (ch : SCHeap) :
      CHeapSpec.bind (CHeapSpec.lift_purespec (CPureSpec.assume_formula P)) (fun _ => c) cPhi ch
      = (P -> c cPhi ch)%type.
    Proof. reflexivity. Qed.

    Lemma rprop_guard {P : Prop} {c : Prop} {w : World} {s : 𝕊 w} :
      (⌜P⌝ -∗ ℛ⟦LogicalSoundness.RProp⟧ c s) ⊢ ℛ⟦LogicalSoundness.RProp⟧ (P -> c)%type s.
    Proof.
      constructor. intros ι Hpc H.
      cbn in H |- *.
      cbv [RSat LogicalSoundness.RProp] in H |- *.
      cbn in H |- *.
      intros Hs HP.
      exact (H HP Hs).
    Qed.

    Lemma rconsume_at {Sg0 : LCtx} (asn : Assertion Sg0) {w : World}
        (cs : Valuation Sg0) (ss : Sub Sg0 w)
        (cPhi : unit -> SCHeap -> Prop)
        (sPhi : forall w1 : World, Acc w w1 -> Unit w1 -> SHeap w1 -> 𝕊 w1)
        (ch : SCHeap) (sh : SHeap w) :
      ℛ⟦RInst (Sub Sg0) (Valuation Sg0)⟧ cs ss -∗
      ℛ⟦□ᵣ (RUnit -> RHeap -> LogicalSoundness.RProp)⟧ cPhi sPhi -∗
      ℛ⟦RHeap⟧ ch sh -∗
      ℛ⟦LogicalSoundness.RProp⟧
        (CHeapSpec.consume asn cs cPhi ch) (SHeapSpec.consume asn ss sPhi sh).
    Proof.
      iIntros "Hs Hk Hh". iApply (refine_consume with "Hs Hk Hh").
    Qed.

    (* Five nested `four`s, ISOLATED ON PURPOSE.  The same script inline
       inside rexec_triple_addr makes iModIntro act on a twenty-hypothesis
       context and rsolve diverge; here the context is one hypothesis. *)
    Lemma refine_four5 {AT A} (RA : Rel AT A)
        {w0 w1 w2 w3 w4 w5 : World}
        (o0 : Acc w0 w1) (o1 : Acc w1 w2) (o2 : Acc w2 w3) (o3 : Acc w3 w4) (o4 : Acc w4 w5)
        (v : A) (vs : Box AT w0) :
      forgetting (acc_trans (acc_trans (acc_trans (acc_trans o0 o1) o2) o3) o4)
        (ℛ⟦□ᵣ RA⟧ v vs)
      ⊢ ℛ⟦□ᵣ RA⟧ v (four (four (four (four (four vs o0) o1) o2) o3) o4).
    Proof.
      iIntros "H".
      rewrite !forgetting_trans.
      do 5 (iApply refine_four; iModIntro).
      iApply "H".
    Qed.

    (* Not a duplicate of forgetting_itable_rel above, despite the similar *)
    (* proof shape: that lemma commutes forgetting with persist_itable     *)
    (* given an EXISTING itable_rel hypothesis at the SAME world (SInstrTable  *)
    (* on both sides); this one instead DERIVES itable_rel at world wb     *)
    (* from an itable_rel fact given at the contract context Σ' (i.e., at  *)
    (* w := wlctx Σ') via a substitution ζ.  Both are needed (used         *)
    (* together at the rexec_triple_addr call site below). *)
    Lemma itable_rel_of_faith_forget {Σ' : LCtx} {wa wb : World} (θ : Acc wa wb) (ζ : Sub Σ' wa)
        (instrs' : gmap (bv xlenbits) AnnotInstr) (tbl' : SInstrTable (wlctx Σ'))
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
        (exitCond' : bv xlenbits -> bool) (exits' : SExitTable (wlctx Σ'))
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

    (* ------------------------------------------------------------------ *)
    (* Word-column boundary lemmas.  These are what replace a full parallel *)
    (* wtable_rel family: three lemmas used ONCE each, at the entry point,  *)
    (* rather than a relation threaded through the fuel induction.          *)
    (* ------------------------------------------------------------------ *)

    (* Forall2 transported along a map on the left, weakening the predicate at
       the same time — the shape both _of_faith_forget lemmas below need
       (their tables are literally `List.map … tbl'`). *)
    Lemma forall2_map_impl {A B C : Type} (f : A -> C) (P : A -> B -> Prop)
        (Q : C -> B -> Prop) (l1 : list A) (l2 : list B) :
      (forall a b, P a b -> Q (f a) b) ->
      List.Forall2 P l1 l2 -> List.Forall2 Q (List.map f l1) l2.
    Proof.
      intros Himp H.
      induction H; cbn; constructor; auto.
    Qed.

    (* env.take's counterpart to the existing env.map_drop.  Not in
       theories/Environment.v (which has map_drop but no map_take); kept local
       rather than adding core churn for two uses. *)
    Lemma env_map_take {B : Set} {D1 D2 : B -> Set} (f : forall b, D1 b -> D2 b)
        {Γ Δ : Ctx B} (E : env.Env D1 (Γ ▻▻ Δ)) :
      env.map f (env.take Δ E) = env.take Δ (env.map f E).
    Proof.
      induction Δ; cbn; [reflexivity|].
      destruct (env.view E) as [E' v].
      cbn.
      f_equal.
      apply IHΔ.
    Qed.

    (* inst commutes with both halves of the split.  Needed because the
       demonic_ctx now covers Σ ▻▻ words_ctx n and the two halves are consumed
       by different lemmas. *)
    Lemma inst_env_take {Σ' Δ : LCtx} {w : World} (E : Sub (Σ' ▻▻ Δ) w) (ι : Valuation w) :
      inst (env.take Δ E) ι = env.take Δ (inst E ι).
    Proof. unfold inst, inst_env. apply env_map_take. Qed.

    Lemma inst_env_drop {Σ' Δ : LCtx} {w : World} (E : Sub (Σ' ▻▻ Δ) w) (ι : Valuation w) :
      inst (env.drop Δ E) ι = env.drop Δ (inst E ι).
    Proof. unfold inst, inst_env. apply env.map_drop. Qed.

    (* The Σ half of the extended demonic env, as an ℛ⟦RNEnv⟧ fact, so the
       existing itable_rel_of_faith_forget / etable_rel_of_faith_forget apply
       unchanged. *)
    Lemma refine_env_drop {Σ' Δ : LCtx} {w : World}
        (lenv : NamedEnv RelVal (Σ' ▻▻ Δ)) (δ : Sub (Σ' ▻▻ Δ) w) :
      (ℛ⟦RNEnv LVar (Σ' ▻▻ Δ)⟧ lenv δ ⊢ ℛ⟦RNEnv LVar Σ'⟧ (env.drop Δ lenv) (env.drop Δ δ))%I.
    Proof.
      constructor.
      intros ι Hpc Hrel.
      unfold RNEnv, RInst in Hrel |- *.
      cbn in Hrel |- *.
      rewrite inst_env_drop Hrel.
      reflexivity.
    Qed.

    (* Reading the word column off a symbolic env and off its instantiation
       gives pointwise-related lists.  This is the ONLY place the positional
       (rather than by-name) reading of the word variables has to be justified,
       and it is justified by using the very same words_of_env on both sides. *)
    (* Stated about words_of_slice, not words_of_env: the recursive call is on
       `drop`-of-the-wide-term, so the induction must generalise over the WIDE
       TERM and not merely over n. *)
    Lemma words_of_slice_inst (n : nat) {w : World}
        (W : Term (wctx w) (ty.bvec (words_width n))) (ι : Valuation w) :
      List.Forall2 (fun (x : Term (wctx w) ty_word) (cx : RelVal ty_word) =>
                      inst (T := fun Σ => Term Σ ty_word) x ι = cx)
        (words_of_slice (@wterm_take (wctx w)) (@wterm_drop (wctx w)) n W)
        (words_of_slice rvtake rvdrop n
           (inst (T := fun Σ => Term Σ (ty.bvec (words_width n))) W ι)).
    Proof.
      revert w W ι. induction n; intros w W ι; cbn; [constructor|].
      constructor.
      - reflexivity.
      - apply IHn.
    Qed.

    Lemma words_of_env_inst {n : nat} {w : World}
        (E : Sub (words_ctx n) w) (ι : Valuation w) :
      List.Forall2 (fun (x : Term (wctx w) ty_word) (cx : RelVal ty_word) =>
                      inst (T := fun Σ => Term Σ ty_word) x ι = cx)
        (words_of_env (@wterm_take (wctx w)) (@wterm_drop (wctx w)) E)
        (words_of_env rvtake rvdrop (inst E ι)).
    Proof.
      unfold words_of_env.
      destruct (env.view E) as [E' t].
      cbn.
      apply words_of_slice_inst.
    Qed.

    (* The word half of the extended demonic env: the symbolic word terms and
       the demonically chosen concrete word values are pointwise related. *)
    Lemma words_of_env_take_inst {Σ' : LCtx} {n : nat} {w : World}
        (lenv : NamedEnv RelVal (Σ' ▻▻ words_ctx n)) (δ : Sub (Σ' ▻▻ words_ctx n) w)
        (ι : Valuation w) :
      inst δ ι = lenv ->
      List.Forall2 (fun (x : Term (wctx w) ty_word) (cx : RelVal ty_word) =>
                      inst (T := fun Σ => Term Σ ty_word) x ι = cx)
        (words_of_env (@wterm_take (wctx w)) (@wterm_drop (wctx w))
           (env.take (words_ctx n) δ))
        (words_of_env rvtake rvdrop (env.take (words_ctx n) lenv)).
    Proof.
      intros <-.
      (* `rewrite <- inst_env_take` does NOT fire here even fully instantiated —
         the goal contains `env.take (words_ctx n) (inst δ ι)` textually, but
         inst's resolved instance arguments differ from the lemma's.  `replace`
         matches the terms as written, which sidesteps it. *)
      (* An explicit assert, not `replace ... by ...`: with SSReflect loaded the
         `by` clause does not run `symmetry` before `apply`. *)
      assert (Hcomm : env.take (words_ctx n) (inst δ ι)
                      = inst (env.take (words_ctx n) δ) ι).
      { symmetry. apply inst_env_take. }
      rewrite Hcomm.
      apply words_of_env_inst.
    Qed.

    (* itable_relW_zip: build the loop-carried fused relation out of the two
       assumed guards.  The address column comes from itable_rel, the word
       column from wtable_rel, and they agree because both are indexed by the
       same table entry — the SyncVal address is shared, so the two gmap
       lookups are at the same key by construction. *)
    Lemma itable_relW_zip {w} (instrs : gmap (bv xlenbits) AnnotInstr)
        (words : bv xlenbits -> bv word) (T : SInstrTable w)
        (ws : list (Term (wctx w) ty_word)) (cws : list (RelVal ty_word))
        (ι : Valuation w) :
      itable_rel instrs T ι ->
      List.Forall2 (fun x cx => inst (T := fun Σ => Term Σ ty_word) x ι = cx) ws cws ->
      wtable_rel words T cws ι ->
      itable_relW instrs words (zip_words T ws) ι.
    Proof.
      unfold itable_rel, itable_relW, wtable_rel.
      intros Hi Hw Hg.
      revert ws Hw Hi.
      induction Hg as [|[t i] cx T' cws' Hhd Htl IH]; intros ws Hw Hi.
      - destruct ws; cbn; constructor.
      - destruct ws as [|x ws']; [inversion Hw|].
        inversion Hw as [|x' cx' ws'' cws'' Hx Hws]; subst.
        inversion Hi as [|p T'' Hihd Hitl]; subst.
        cbn.
        constructor.
        + (* NB no `->` intro pattern for the word component: the `subst` above
             already eliminated cx via Hx, so Hhd's third conjunct arrives as
             `inst x ι = SyncVal (words v)` — exactly the goal — and a rewrite
             would find nothing left to act on. *)
          destruct Hhd as (v & Hv & Hcx).
          destruct Hihd as (v' & Hv' & Him).
          cbn in Hv, Hv', Him, Hcx.
          assert (v' = v) as -> by (rewrite Hv in Hv'; now injection Hv').
          exists v.
          split; [exact Hv|split; [exact Him|exact Hcx]].
        + apply IH; assumption.
    Qed.

    (* ---- Supplying the word half of the demonic valuation (used by the
       soundness chain in Adequacy.v, which has to INSTANTIATE the demonic
       choice with the real words rather than merely relate to it). ---- *)

    (* env.take's counterpart to env.drop_cat.  Also absent from
       theories/Environment.v. *)
    Lemma env_take_cat {B : Set} {D : B -> Set} {Γ Δ : Ctx B}
        (EΓ : env.Env D Γ) (EΔ : env.Env D Δ) :
      env.take Δ (env.cat EΓ EΔ) = EΔ.
    Proof.
      induction EΔ; cbn; [reflexivity|].
      f_equal.
      apply IHEΔ.
    Qed.

    (* The inverse of words_of_env.  It used to snoc n bindings; now it has to
       CONCATENATE the n words into the single wide value, so bv.app replaces
       env.snoc and the recursion is right-nested to match words_width's
       `word + rest`.

       Built over PLAIN bv and wrapped in SyncVal exactly once.  That is not a
       restriction: wtable_rel already requires every concrete word to be
       `ty.SyncVal (words v)`, so the per-word RelVal generality was never
       used — instruction words are memory contents at public addresses and are
       always sync.  It also avoids a real trap: a general RelVal concatenation
       (liftBinOp bv.app) does NOT round-trip on a MIXED list, because
       liftBinOp app (SyncVal a) (NonSyncVal b1 b2) sliced back gives
       NonSyncVal a a rather than SyncVal a. *)
    Fixpoint bv_of_words (n : nat) (d : bv word) (l : list (bv word))
      : bv (words_width n) :=
      match n return bv (words_width n) with
      | O    => bv.zero
      | S n' => bv.app (List.hd d l) (bv_of_words n' d (List.tl l))
      end.

    Definition env_of_words (n : nat) (d : bv word) (l : list (bv word))
      : NamedEnv RelVal (words_ctx n) :=
      env.snoc env.nil _ (ty.SyncVal (bv_of_words n d l)).

    Lemma words_of_env_of_words (n : nat) (d : bv word) (l : list (bv word)) :
      length l = n ->
      words_of_env rvtake rvdrop (env_of_words n d l) = List.map ty.SyncVal l.
    Proof.
      unfold env_of_words, words_of_env. cbn.
      revert l. induction n; intros l Hl; cbn.
      - destruct l; [reflexivity|discriminate].
      - destruct l as [|x l']; [discriminate|]. cbn.
        unfold rvtake, rvdrop. cbn.
        (* SSReflect's rewrite is in scope here and takes SPACE-separated
           rules, not comma-separated ones — hence two calls. *)
        rewrite bv.take_app.
        rewrite bv.drop_app.
        f_equal. apply IHn. cbn in Hl. now injection Hl.
    Qed.

    (* The concrete word values at the table's addresses.  Total because `words`
       is a function, so no address needs a fallback justification. *)
    Definition cws_of (words : bv xlenbits -> bv word) {w} (tbl : SInstrTable w)
        (ι : Valuation w) : list (RelVal ty_word) :=
      List.map (fun p =>
         match ty.RVToOption (inst (T := fun Σ => Term Σ ty_xlenbits) (fst p) ι) with
         | Some v => ty.SyncVal (words v)
         | None   => ty.SyncVal bv.zero
         end) tbl.

    Lemma cws_of_length (words : bv xlenbits -> bv word) {w} (tbl : SInstrTable w)
        (ι : Valuation w) :
      length (cws_of words tbl ι) = length tbl.
    Proof. apply List.map_length. Qed.

    (* The same list at the PLAIN bv level.  env_of_words now needs raw words to
       concatenate, while wtable_rel and itable_relW_zip still speak RelVal, so
       both forms exist and cws_of_bv_spec is the one-line bridge.  Keeping
       cws_of's own definition and proofs untouched is deliberate: it is what
       stops this change reaching wtable_rel_cws_of and itable_relW_zip. *)
    Definition cws_of_bv (words : bv xlenbits -> bv word) {w} (tbl : SInstrTable w)
        (ι : Valuation w) : list (bv word) :=
      List.map (fun p =>
         match ty.RVToOption (inst (T := fun Σ => Term Σ ty_xlenbits) (fst p) ι) with
         | Some v => words v
         | None   => bv.zero
         end) tbl.

    Lemma cws_of_bv_length (words : bv xlenbits -> bv word) {w} (tbl : SInstrTable w)
        (ι : Valuation w) :
      length (cws_of_bv words tbl ι) = length tbl.
    Proof. apply List.map_length. Qed.

    Lemma cws_of_bv_spec (words : bv xlenbits -> bv word) {w} (tbl : SInstrTable w)
        (ι : Valuation w) :
      List.map ty.SyncVal (cws_of_bv words tbl ι) = cws_of words tbl ι.
    Proof.
      unfold cws_of, cws_of_bv.
      rewrite List.map_map.
      apply List.map_ext.
      intros [t i].
      now destruct (ty.RVToOption _).
    Qed.

    (* wtable_rel holds for cws_of BY CONSTRUCTION, given only that the table's
       keys instantiate to SyncVal addresses — which itable_rel already says.
       This is what lets Adequacy.v discharge the word guard without any extra
       hypothesis travelling down from the end theorems. *)
    Lemma wtable_rel_cws_of (instrs : gmap (bv xlenbits) AnnotInstr)
        (words : bv xlenbits -> bv word) {w} (tbl : SInstrTable w) (ι : Valuation w) :
      itable_rel instrs tbl ι -> wtable_rel words tbl (cws_of words tbl ι) ι.
    Proof.
      unfold itable_rel, wtable_rel, cws_of.
      intros H.
      induction H as [|p tbl' Hp Htl IH]; cbn; [constructor|].
      destruct Hp as (v & Hv & Hm).
      constructor; [|exact IH].
      exists v.
      rewrite Hv.
      cbn.
      split; reflexivity.
    Qed.

    (* Iris-level form of itable_relW_zip, so the call site can `iApply` it with
       a framing pattern naming exactly the three hypotheses it needs.  Going
       through iStopProof instead is fragile: it folds the WHOLE persistent
       context into one conjunction, so the intro pattern has to be adjusted
       every time an unrelated hypothesis appears earlier in the proof. *)
    Lemma itable_relW_zip_pred {w} (instrs : gmap (bv xlenbits) AnnotInstr)
        (words : bv xlenbits -> bv word) (T : SInstrTable w)
        (ws : list (Term (wctx w) ty_word)) (cws : list (RelVal ty_word)) :
      (itable_rel instrs T ∗
       ((fun ι => List.Forall2
           (fun (x : Term (wctx w) ty_word) (cx : RelVal ty_word) =>
              inst (T := fun Σ => Term Σ ty_word) x ι = cx) ws cws) : Pred w) ∗
       wtable_rel words T cws
       ⊢ itable_relW instrs words (zip_words T ws))%I.
    Proof.
      constructor.
      intros ι Hpc (Hi & Hw & Hg).
      (* eapply, not apply: cws does not occur in the conclusion, so it stays an
         evar until the Forall2 premise pins it from Hw. *)
      eapply itable_relW_zip; eassumption.
    Qed.

    (* Transport of wtable_rel from the contract context Σ' to the executor's
       world, exactly mirroring itable_rel_of_faith_forget above. *)
    Lemma wtable_rel_of_faith_forget {Σ' : LCtx} {wa wb : World} (θ : Acc wa wb) (ζ : Sub Σ' wa)
        (words' : bv xlenbits -> bv word) (tbl' : SInstrTable (wlctx Σ'))
        (ιΣ : NamedEnv RelVal Σ') (cws : list (RelVal ty_word)) :
      wtable_rel words' tbl' cws ιΣ ->
      (forgetting θ (ℛ⟦RNEnv LVar Σ'⟧ ιΣ ζ) ⊢
       wtable_rel words' (subst_itable (persist ζ θ) tbl') cws)%I.
    Proof.
      intros Hfaith.
      constructor.
      intros ι Hpc Hrel.
      unfold forgetting, RNEnv, RInst in Hrel.
      cbn in Hrel.
      unfold wtable_rel, subst_itable.
      eapply forall2_map_impl; [|exact Hfaith].
      intros [t i] cx (v & Hv & Hy).
      exists v.
      cbn.
      rewrite inst_subst inst_persist Hrel.
      split; [exact Hv|exact Hy].
    Qed.

    (* The word half at the executor's world: the persisted symbolic word terms
       are pointwise related to the demonically chosen concrete words. *)
    Lemma words_rel_of_faith_forget {Σ' : LCtx} {n : nat} {wa wb : World} (θ : Acc wa wb)
        (δw : Sub (Σ' ▻▻ words_ctx n) wa) (lenvw : NamedEnv RelVal (Σ' ▻▻ words_ctx n)) :
      (forgetting θ (ℛ⟦RNEnv LVar (Σ' ▻▻ words_ctx n)⟧ lenvw δw) ⊢
       (fun ι => List.Forall2
          (fun (x : Term (wctx wb) ty_word) (cx : RelVal ty_word) =>
             inst (T := fun Σ => Term Σ ty_word) x ι = cx)
          (List.map (fun x => persist__term x θ)
             (words_of_env (@wterm_take (wctx wa)) (@wterm_drop (wctx wa))
                (env.take (words_ctx n) δw)))
          (words_of_env rvtake rvdrop (env.take (words_ctx n) lenvw))) : Pred wb)%I.
    Proof.
      constructor.
      intros ι Hpc Hrel.
      unfold forgetting, RNEnv, RInst in Hrel.
      cbn in Hrel.
      eapply forall2_map_impl; [|exact (words_of_env_take_inst _ _ Hrel)].
      intros x cx Hx.
      rewrite inst_persist.
      exact Hx.
    Qed.

    (* rexec_triple_addr: unconditional refinement of the guarded      *)
    (* concrete triple by the table-based symbolic triple.  The guard is   *)
    (* introduced via refine_guard; the executor bind is dispatched by     *)
    (* rexec_cfg_addr with faithfulness transported through the world  *)
    (* morphisms by the _forget lemmas.  rsolve must NOT be let loose on   *)
    (* the executor bind (no RefineCompat instance matches the table       *)
    (* executor's premise-free form; typeclass search diverges).           *)
    (* rexec_triple_addr: unconditional refinement of the guarded          *)
    (* concrete triple by the table-based symbolic triple.                  *)
    (*                                                                      *)
    (* STATED IN PEELED FORM, and carrying a premise on its own ambient     *)
    (* continuation, for the reason PLAN-dropk.md §19/§20 records: the      *)
    (* executor now demands `Factors (dbundle3 trans tbl exits) sPhi`, and  *)
    (* for a truly unconstrained sPhi that is FALSE (an adversarial sPhi    *)
    (* can distinguish two accessibilities that agree on their persisted    *)
    (* substitution -- Acc's constructors are genuinely different terms).   *)
    (* OmegaIndep is the weakest thing that suffices, and SHeapSpec.run     *)
    (* supplies it (omega_indep_block).                                     *)
    (*                                                                      *)
    (* The five binds are paired with rbind_at rather than                  *)
    (* HeapSpec.refine_bind -- see the comment on rbind_at above for why    *)
    (* the latter cannot work here.  Otherwise this is the old proof:       *)
    (* the guard, the four _forget transports, itable_relW_zip_pred, and    *)
    (* the executor dispatched by rexec_cfg_addr are all unchanged.         *)
    Lemma rexec_triple_addr {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (instrs : gmap (bv xlenbits) AnnotInstr)
      (words : bv xlenbits -> bv word)
      (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
      (tbl : SInstrTable (wlctx Σ)) (exits : SExitTable (wlctx Σ)) {w : World} :
      ⊢ ∀ (cPhi : unit -> SCHeap -> Prop)
          (sPhi : forall w1 : World, Acc w w1 -> Unit w1 -> SHeap w1 -> 𝕊 w1),
        ⌜OmegaIndep sPhi⌝ -∗
        ℛ⟦□ᵣ (RUnit -> RHeap -> LogicalSoundness.RProp)⟧ cPhi sPhi -∗
        ∀ (ch : SCHeap) (sh : SHeap w), ℛ⟦RHeap⟧ ch sh -∗
          ℛ⟦LogicalSoundness.RProp⟧
            (cexec_triple_addr req instrs words exitCond fuel ens tbl exits cPhi ch)
            (sexec_triple_addr req tbl exits fuel ens (w := w) sPhi sh).
    Proof.
      iIntros (cPhi sPhi) "%Hoi #rPhi". iIntros (ch sh) "#rh".
      unfold cexec_triple_addr, sexec_triple_addr.
      iApply (rbind_at (RA := RNEnv LVar (Σ ▻▻ words_ctx (length tbl))) (RB := RUnit) with "[] [] rh").
      - rsolve.
      - iIntros (w1 om0) "!>". iIntros (lenvw δw) "#Hδw". iIntros (ch1 sh1) "#rh1".
        rewrite guard_reduce.
        iApply rprop_guard. iIntros "%Hfaith".
        destruct Hfaith as [Hif [Hef Hwg]].
        (* Split the extended demonic env: the Σ half feeds the existing
           itable_rel/etable_rel transport, the word half feeds
           words_of_env_take_inst. *)
        iPoseProof (refine_env_drop with "Hδw") as "#Hδ".
        iApply (rbind_at (RA := RVal ty_xlenbits) (RB := RUnit) with "[] [] rh1").
        + rsolve.
        + iIntros (w2 th1) "!>". iIntros (a ta) "#Ha". iIntros (ch2 sh2) "#rh2".
          (* The initial-nextpc demonic, paired here.  Both executors introduce
             it ONCE, right after `a` and before `produce req` -- see
             exec_instruction_prologue (Verifier.v) for why it is a parameter
             threaded inward rather than an existential minted per step. *)
          iApply (rbind_at (RA := RVal ty_xlenbits) (RB := RUnit) with "[] [] rh2").
          * rsolve.
          * iIntros (w3 th1') "!>". iIntros (np tnp) "#Hnp". iIntros (ch3 sh3) "#rh3".
            (* Established HERE, where the forgetting nesting is still
               shallow.  Left to the consume at the leaf it becomes a
               residual under forgetting (θ2 ∘ θ3) that rsolve diverges on. *)
            iAssert (ℛ⟦RInst (fun Sig : LCtx => NamedEnv (Term Sig) (Σ ▻ "a"∷ty_xlenbits))
                         (Valuation (Σ ▻ "a"∷ty_xlenbits))⟧
                       (env.drop (words_ctx (length tbl)) lenvw).["a"∷ty_xlenbits ↦ a]
                       (persist (env.drop (words_ctx (length tbl)) δw)
                          (acc_trans th1 th1')).["a"∷ty_xlenbits ↦ persist__term ta th1'])
              as "#Hd1".
            { rsolve. }
            iApply (rbind_at (RA := RUnit) (RB := RUnit) with "[] [] rh3").
            -- rsolve.
            -- iIntros (w4 th2) "!>". iIntros (u tu) "#Hu". iIntros (ch4 sh4) "#rh4".
               (* TODO: It feels like rsolve should be able to handle the
                  executor bind, if you have the right RefineCompat
                  instances -- it cannot today, and diverges rather than
                  failing (cfgver-rsolve). *)
               iPoseProof (itable_rel_of_faith_forget (acc_trans (acc_trans th1 th1') th2)
                             (env.drop (words_ctx (length tbl)) δw) Hif with "Hδ") as "#Hi0".
               iPoseProof (etable_rel_of_faith_forget (acc_trans (acc_trans th1 th1') th2)
                             (env.drop (words_ctx (length tbl)) δw) Hef with "Hδ") as "#He".
               (* Build the loop-carried itable_relW out of the two guards:
                  address column from Hi0, word column from Hwg + the demonic
                  refinement. *)
               iPoseProof (wtable_rel_of_faith_forget (acc_trans (acc_trans th1 th1') th2)
                             (env.drop (words_ctx (length tbl)) δw) Hwg with "Hδ") as "#Hw0".
               iPoseProof (words_rel_of_faith_forget (acc_trans (acc_trans th1 th1') th2)
                             δw lenvw with "Hδw") as "#Hws".
               iAssert (itable_relW instrs words
                          (zip_words
                             (subst_itable (persist (env.drop (words_ctx (length tbl)) δw)
                                              (acc_trans (acc_trans th1 th1') th2)) tbl)
                             (List.map (fun x => persist__term x (acc_trans (acc_trans th1 th1') th2))
                                (words_of_env (@wterm_take _) (@wterm_drop _)
                                   (env.take (words_ctx (length tbl)) δw))))) as "#Hi".
               { iApply (itable_relW_zip_pred with "[$Hi0 $Hws $Hw0]"). }
               unfold CHeapSpec.bind. unfold SHeapSpec.bind.
               iApply (rexec_cfg_addr instrs words exitCond fuel _ _ _ with "[$Hi $He]").
               (* FIVE premises: two RVal, the Factors one, then the □ᵣ/RHeap
                  pair, which the RHeapSpec-folded statement used to supply
                  automatically. *)
               ++ iApply (refine_inst_persist with "Ha").
               ++ iApply (refine_inst_persist with "Hnp").
               ++ (* PLAN-dropk.md §19's `admit.`, closed 2026-08-31.  The
                     carrier is dbundle3's FIRST component and nothing else --
                     which is exactly what Verifier.v's comment on `trans`
                     says the outer continuation's ω-dependence factors
                     through, so this is the last mile of that design. *)
                  iPureIntro. apply factors_consume_tail.
                  apply omega_indep_four. apply omega_indep_four.
                  apply omega_indep_four. apply omega_indep_four. exact Hoi.
               ++ iIntros (w5 th3) "!>". iIntros (na tna) "#Hna". iIntros (ch5 sh5) "#rh5".
                  iApply (rconsume_at with "[] [] rh5").
                  ** rsolve.
                  ** iApply (refine_four5 with "rPhi").
               ++ iApply "rh4".
    Qed.

    (* NO RefineCompat instance for rexec_triple_addr any more: an instance
       cannot carry the OmegaIndep premise.  Its sole consumer was
       rcfg_verification_condition's bare `rsolve`, which now applies the
       lemma by hand (three goals, two of them still rsolve). *)

    Definition ccfg_verification_condition {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (instrs : gmap (bv xlenbits) AnnotInstr)
      (words : bv xlenbits -> bv word)
      (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
      (tbl : SInstrTable (wlctx Σ)) (exits : SExitTable (wlctx Σ)) : Prop :=
      CHeapSpec.run (cexec_triple_addr req instrs words exitCond fuel ens tbl exits).

    Lemma rcfg_verification_condition {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (instrs : gmap (bv xlenbits) AnnotInstr)
      (words : bv xlenbits -> bv word)
      (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
      (tbl : SInstrTable (wlctx Σ)) (exits : SExitTable (wlctx Σ)) {w} :
      ⊢ RSat LogicalSoundness.RProp (w := w)
          (ccfg_verification_condition req instrs words exitCond fuel ens tbl exits)
          (scfg_verification_condition req tbl exits fuel ens w).
    Proof.
      unfold ccfg_verification_condition, scfg_verification_condition.
      (* Was a bare `rsolve`, which went through refine_compat_exec_triple_addr.
         That instance is gone (it cannot carry rexec_triple_addr's OmegaIndep
         premise), so the run is unfolded and the lemma applied by hand.  The
         constant continuation `fun w1 θ1 _ h1 => block` is what makes the
         premise true, by omega_indep_block. *)
      unfold CHeapSpec.run. unfold SHeapSpec.run.
      iApply (rexec_triple_addr req instrs words exitCond fuel ens tbl exits).
      - iPureIntro. apply omega_indep_block.
      - rsolve.
      - rsolve.
    Qed.

    #[export] Instance refine_compat_cfg_verification_condition {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (instrs : gmap (bv xlenbits) AnnotInstr)
      (words : bv xlenbits -> bv word)
      (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
      (tbl : SInstrTable (wlctx Σ)) (exits : SExitTable (wlctx Σ)) {w} :
      RefineCompat (LogicalSoundness.RProp)
        (ccfg_verification_condition req instrs words exitCond fuel ens tbl exits) w
        (scfg_verification_condition req tbl exits fuel ens w) _ :=
      MkRefineCompat (rcfg_verification_condition req instrs words exitCond fuel ens tbl exits).

  End Relational.

  (* ====================================================================== *)
  (* Soundness scaffolding shared with the myWP2_loop chain in Adequacy.v.  *)
  (*                                                                         *)
  (* ptsto_instrs instrs: Iris predicate asserting instruction ownership     *)
  (*   for a finite map from absolute address to instruction (SyncVal: the   *)
  (*   same instruction lives at the same address in both worlds).           *)
  (*                                                                         *)
  (* sound_exec_instruction / ptsto_instrs_lookup below are the two pieces   *)
  (* Adequacy.v reuses (qualified) to build sound_exec_cfg_addr_myWP2 and    *)
  (* the rest of the myWP2_loop soundness chain.                            *)
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
    (* ptsto_instrs_w: the WORD-INDEXED form — ownership of a specific raw
       instruction word at each address, as the concrete executor's `words`
       gmap names them.  This is what the soundness chain threads. *)
    Definition ptsto_instrs_w (words : bv xlenbits -> bv word)
        (instrs : gmap (bv xlenbits) AST) : iProp Σ :=
      ([∗ map] a ↦ i ∈ instrs,
         interp_ptsto_instr (SyncVal a) (SyncVal (words a)) (SyncVal i))%I.

    (* ptsto_instrs keeps its old MEANING — "some word that decodes to i lives
       at each address" — and hence its old role in ImplPre / the end theorems,
       which is why the trusted statement surface does not change.  The word is
       merely named: ∃-over-a-gmap-of-words is equivalent to the old
       ∃-inside-each-entry (interp_ptsto_instr used to carry `∃ v` itself), and
       here that equivalence is DEFINITIONAL in one direction and discharged by
       intro_ptsto_instrs in the other — it already receives the word list `ws`.
       PLAN-encoded-instr.md §4-SPIKE. *)
    Definition ptsto_instrs (instrs : gmap (bv xlenbits) AST) : iProp Σ :=
      (∃ words : bv xlenbits -> bv word, ptsto_instrs_w words instrs)%I.

    (* Extending the word map at an address the instruction map does not
       mention leaves ownership unchanged.  Needed by intro_ptsto_instrs, whose
       induction peels one instruction off `instrs` while the word map grows by
       one insert: the tail's entries must be unaffected by the head's key. *)
    (* Two word functions that AGREE on the program's addresses give the same
       ownership.  Needed by intro_ptsto_instrs, whose induction peels one
       instruction off `instrs` while the word function gains one case: the
       tail's addresses must be unaffected by the head's. *)
    Lemma ptsto_instrs_w_agree (w1 w2 : bv xlenbits -> bv word)
        (instrs : gmap (bv xlenbits) AST) :
      (forall a i, instrs !! a = Some i -> w1 a = w2 a) ->
      ptsto_instrs_w w1 instrs ⊢ ptsto_instrs_w w2 instrs.
    Proof.
      intros Hagree.
      unfold ptsto_instrs_w.
      apply big_sepM_mono.
      intros a i Hlk.
      by rewrite (Hagree a i Hlk).
    Qed.

    (* np: the incoming nextpc value, a PARAMETER here rather than the `∃ v`
       this used to hold, mirroring exec_instruction_prologue (Verifier.v).
       The POSTcondition's `∃ an` stays — that one is real, it is the step's
       output (tick_pc leaves pc = nextpc = an). *)
    (* w: the raw instruction word at address a, a PARAMETER for the same
       reason np is — the prologue owns ptstoinstr a w i, so the word is
       supplied rather than re-quantified per step. *)
    Definition semTripleOneInstrStep (PRE : iProp Σ) (instr : AST) (POST : RelVal ty_word -> iProp Σ) (a np w : RelVal ty_word) : iProp Σ :=
      semTriple [env] (PRE ∗ lptsreg nextpc np ∗ lptsreg pc a ∗ interp_ptsto_instr a w (SyncVal instr) ∗ ⌜ secLeak a ⌝)
        (FunDef RiscvPmpProgram.step)
        (fun ret _ => (∃ an, lptsreg nextpc an ∗ lptsreg pc an ∗ POST an) ∗ interp_ptsto_instr a w (SyncVal instr)  ∗ ⌜ secLeak a ⌝)%I.

    Lemma sound_exec_instruction {instr} a np w Φ (h : SCHeap) :
      cexec_instruction instr a np w Φ h ->
      ⊢ semTripleOneInstrStep (interpret_scheap h) instr
          (fun an => ∃ h' : SCHeap, interpret_scheap h' ∧ ⌜Φ an h'⌝ ∧ ⌜ secLeak an ⌝) a np w.
    Proof.
      cbv [cexec_instruction exec_instruction_prologue bind produce demonic
             produce_chunk lift_purespec CPureSpec.produce_chunk CPureSpec.pure
             CPureSpec.demonic CStoreSpec.evalStoreSpec].
      cbn - [consume].
      (* No `[%npc Hnpc]` destruct and no `specialize (Hverif npc)` any more:
         the prologue no longer produces a demonic variable for nextpc, so the
         value arrives as the parameter np instead of being quantified here. *)
      iIntros (Hverif) "(Hheap & Hnpc & Hpc & Hinstrs & %HsL)".
      apply sound_cexec in Hverif.
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
    Lemma ptsto_instrs_lookup (words : bv xlenbits -> bv word)
        (instrs : gmap (bv xlenbits) AST) (v : bv xlenbits) (i : AST) :
      instrs !! v = Some i →
      ptsto_instrs_w words instrs ⊢
        interp_ptsto_instr (SyncVal v) (SyncVal (words v)) (SyncVal i) ∗
        (interp_ptsto_instr (SyncVal v) (SyncVal (words v)) (SyncVal i) -∗
           ptsto_instrs_w words instrs).
    Proof.
      intros Hlk. unfold ptsto_instrs_w.
      by apply (big_sepM_lookup_acc
                  (fun a j => interp_ptsto_instr (SyncVal a) (SyncVal (words a)) (SyncVal j))
                  instrs v i).
    Qed.

  End Soundness.

End CFGVerificationDerived.
