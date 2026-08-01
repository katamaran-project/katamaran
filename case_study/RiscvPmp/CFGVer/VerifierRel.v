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

    (* `words` gives the raw instruction word at each address — the concrete
       counterpart of the word column of the symbolic SInstrTableW
       (Verifier.v).  It stays a SEPARATE gmap from `instrs` (rather than
       fusing it into `instrs`) because `instrs` is what the trusted statement
       surface and TablesRel.v's faith lemmas talk about, whereas `words` is
       supplied by Adequacy.v out of the `∃ v` inside interp_ptsto_instr.  It
       is a total FUNCTION, not a gmap, so the lookup is
       total, so there is no "no word here" case to carry. *)
    Fixpoint cexec_cfg_addr (instrs : gmap (bv xlenbits) AST)
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
                   | None   => error
                   | Some i =>
                       apc' <- cexec_instruction i apc anp (ty.SyncVal (words v)) ;;
                       cexec_cfg_addr instrs words exitCond n' apc' apc'
                   end)
            end
        end.

    Import (hints) CStoreSpec.

    #[export] Instance mono_cexec_instruction {i a np w} :
      Monotonic (MHeapSpec eq) (cexec_instruction i a np w).
    Proof. typeclasses eauto. Qed.

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
    Definition itable_rel {w} (instrs : gmap (bv xlenbits) AST) (tbl : SInstrTable w) : Pred w :=
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
    Definition itable_relW {w} (instrs : gmap (bv xlenbits) AST)
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
    Lemma lookup_instr_sound {w} (instrs : gmap (bv xlenbits) AST)
        (words : bv xlenbits -> bv word) (tbl : SInstrTableW w)
        (apc : STerm ty_xlenbits w) (x : Term (wctx w) ty_word) (i : AST)
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
        (instrs : gmap (bv xlenbits) AST) (tbl : SInstrTable w1) :
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
        (instrs : gmap (bv xlenbits) AST) (words : bv xlenbits -> bv word)
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
    Lemma lookup_instr_sound_repₚ {w} (instrs : gmap (bv xlenbits) AST)
        (words : bv xlenbits -> bv word) (tbl : SInstrTableW w)
        (apc : STerm ty_xlenbits w) (x : Term (wctx w) ty_word) (i : AST)
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

    (* rexec_cfg_addr: refinement of the gmap concrete executor by the  *)
    (* term-table symbolic executor, under table faithfulness.  Proved by   *)
    (* iInduction on fuel, boxed IH projected by                            *)
    (* forgetting_unconditionally_drastic; the four subgoals of the         *)
    (* is_exit/lookup_instr double destruct are discharged sequentially.    *)
    (* TODO: This proof was not written in the phylosophy of rsolve. *)
    (* It should be relatively easy with most of the complexity handled by rsolve. *)
    (* I suspect there are a few missing RefineCompat instances for tables. *)
    (* This is maybe a good proof golf target. *)
    Lemma rexec_cfg_addr (instrs : gmap (bv xlenbits) AST)
        (words : bv xlenbits -> bv word) (exitCond : bv xlenbits -> bool)
        (fuel : nat) {w} (tbl : SInstrTableW w) (exits : SExitTable w) :
      (itable_relW instrs words tbl ∗ etable_rel exitCond exits ⊢
       ℛ⟦RVal ty_xlenbits -> RVal ty_xlenbits -> RHeapSpec (RVal ty_xlenbits)⟧
           (cexec_cfg_addr instrs words exitCond fuel)
           (sexec_cfg_addr fuel tbl exits))%I.
    Proof.
      iIntros "#[Hi He]".
      iAssert (ℛ⟦□ᵣ (RVal ty_xlenbits -> RVal ty_xlenbits -> RHeapSpec (RVal ty_xlenbits))⟧
                 (cexec_cfg_addr instrs words exitCond fuel)
                 (fun w' θ => sexec_cfg_addr fuel (persist_itableW θ tbl)
                                (persist_etable θ exits))) as "H".
      {
        iInduction fuel as [|n'] "IHfuel".
        - rsolve.
        - cbn [sexec_cfg_addr cexec_cfg_addr].
          rsolve.
          rewrite forgetting_itable_relW forgetting_etable_rel.
          iRename select (ℛ⟦RVal ty_xlenbits⟧ a ta) into "Ha".
          destruct (is_exit (persist_etable ω exits) ta) eqn:Hex;
            destruct (lookup_instr (persist_itableW ω tbl) ta) as [[x i]|] eqn:Hlk.
          (* The four cases are BULLETED deliberately.  This script used to be
             positional, and when sexec_cfg_addr gained the anp argument the
             first case stopped closing its goal (the IH now takes TWO RVal
             premises, see below) — which silently shifted every later block by
             one goal and surfaced as an unresolvable evar in case 2's
             is_exit_sound_repₚ, i.e. nowhere near the actual cause.  Bullets
             pin each block to its own goal so the next such change fails
             locally instead. *)
          + (* exit-hit / lookup-hit *)
            iDestruct (lookup_instr_sound_repₚ instrs words _ _ a Hlk with "[$Hi $Ha]")
              as (v) "[%Hfact #Hx]".
            destruct Hfact as (-> & Hm).
            iPoseProof (is_exit_sound_repₚ exitCond _ _ _ Hex with "[$He $Ha]") as "%Hfact2".
            destruct Hfact2 as (v' & Hveq & Hcond).
            injection Hveq as <-.
            cbn [ty.RVToOption].
            rewrite Hcond Hm.
            rsolve.
            rewrite (persist_itableW_trans ω ω0 tbl) (persist_etable_trans ω ω0 exits).
            iPoseProof (forgetting_unconditionally_drastic with "IHfuel") as "IH".
            (* TWO "[$]", one per RVal argument: the recursive call passes apc'
               as both the pc and the incoming nextpc.  Both premises are the
               same persistent ℛ⟦RVal⟧ fact, so it frames twice over. *)
            iApply ("IH" with "[$] [$]").
          + (* exit-hit / lookup-miss *)
            iPoseProof (is_exit_sound_repₚ exitCond _ _ _ Hex with "[$He $Ha]") as "%Hfact".
            destruct Hfact as (v & -> & Hcond).
            cbn [ty.RVToOption].
            rewrite Hcond.
            rsolve.
          + (* exit-miss / lookup-hit *)
            iDestruct (lookup_instr_sound_repₚ instrs words _ _ a Hlk with "[$Hi $Ha]")
              as (v) "[%Hfact #Hx]".
            destruct Hfact as (-> & Hm).
            cbn [ty.RVToOption].
            rewrite Hm.
            rsolve.
            rewrite (persist_itableW_trans ω ω0 tbl) (persist_etable_trans ω ω0 exits).
            iPoseProof (forgetting_unconditionally_drastic with "IHfuel") as "IH".
            iApply ("IH" with "[$] [$]").
          + (* exit-miss / lookup-miss: symbolic errors twice; concrete side *)
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
      rewrite (persist_itableW_refl tbl) (persist_etable_refl exits).
      iApply "HT".
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
    Definition cexec_triple_addr {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (instrs : gmap (bv xlenbits) AST)
      (words : bv xlenbits -> bv word)
      (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
      (tbl : SInstrTable (wlctx Σ)) (exits : SExitTable (wlctx Σ)) : CHeapSpec unit :=
      (* Mirrors sexec_triple_addr's demonic_ctx over Σ ▻▻ words_ctx (length tbl):
         the per-address instruction words are demonically chosen here, ONCE,
         and split back out with env.drop / env.take. *)
      CHeapSpec.bind (CHeapSpec.demonic_ctx (Σ ▻▻ words_ctx (length tbl))) (fun lenvw =>
      let lenv := env.drop (words_ctx (length tbl)) lenvw in
      let cws  := words_of_env (length tbl) (env.take (words_ctx (length tbl)) lenvw) in
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

    (* Not a duplicate of forgetting_itable_rel above, despite the similar *)
    (* proof shape: that lemma commutes forgetting with persist_itable     *)
    (* given an EXISTING itable_rel hypothesis at the SAME world (SInstrTable  *)
    (* on both sides); this one instead DERIVES itable_rel at world wb     *)
    (* from an itable_rel fact given at the contract context Σ' (i.e., at  *)
    (* w := wlctx Σ') via a substitution ζ.  Both are needed (used         *)
    (* together at the rexec_triple_addr call site below). *)
    Lemma itable_rel_of_faith_forget {Σ' : LCtx} {wa wb : World} (θ : Acc wa wb) (ζ : Sub Σ' wa)
        (instrs' : gmap (bv xlenbits) AST) (tbl' : SInstrTable (wlctx Σ'))
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
    Lemma words_of_env_inst {n : nat} {w : World}
        (E : Sub (words_ctx n) w) (ι : Valuation w) :
      List.Forall2 (fun (x : Term (wctx w) ty_word) (cx : RelVal ty_word) =>
                      inst (T := fun Σ => Term Σ ty_word) x ι = cx)
        (words_of_env n E) (words_of_env n (inst E ι)).
    Proof.
      induction n; cbn; [constructor|].
      destruct (env.view E) as [E' v].
      cbn.
      constructor; [reflexivity|].
      apply IHn.
    Qed.

    (* The word half of the extended demonic env: the symbolic word terms and
       the demonically chosen concrete word values are pointwise related. *)
    Lemma words_of_env_take_inst {Σ' : LCtx} {n : nat} {w : World}
        (lenv : NamedEnv RelVal (Σ' ▻▻ words_ctx n)) (δ : Sub (Σ' ▻▻ words_ctx n) w)
        (ι : Valuation w) :
      inst δ ι = lenv ->
      List.Forall2 (fun (x : Term (wctx w) ty_word) (cx : RelVal ty_word) =>
                      inst (T := fun Σ => Term Σ ty_word) x ι = cx)
        (words_of_env n (env.take (words_ctx n) δ))
        (words_of_env n (env.take (words_ctx n) lenv)).
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
    Lemma itable_relW_zip {w} (instrs : gmap (bv xlenbits) AST)
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

    (* The inverse of words_of_env: package a list of word values back into the
       env shape demonic_ctx quantifies over. *)
    Fixpoint env_of_words {D : Ty -> Set} (n : nat) (d : D ty_word)
        (l : list (D ty_word)) : NamedEnv D (words_ctx n) :=
      match n with
      | O    => env.nil
      | S n' => env.snoc (env_of_words n' d (List.tl l)) _ (List.hd d l)
      end.

    Lemma words_of_env_of_words {D : Ty -> Set} (n : nat) (d : D ty_word)
        (l : list (D ty_word)) :
      length l = n -> words_of_env n (env_of_words n d l) = l.
    Proof.
      revert l.
      induction n; intros l Hl; cbn.
      - destruct l; [reflexivity|discriminate].
      - destruct l as [|x l']; [discriminate|].
        cbn.
        f_equal.
        apply IHn.
        cbn in Hl.
        now injection Hl.
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

    (* wtable_rel holds for cws_of BY CONSTRUCTION, given only that the table's
       keys instantiate to SyncVal addresses — which itable_rel already says.
       This is what lets Adequacy.v discharge the word guard without any extra
       hypothesis travelling down from the end theorems. *)
    Lemma wtable_rel_cws_of (instrs : gmap (bv xlenbits) AST)
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
    Lemma itable_relW_zip_pred {w} (instrs : gmap (bv xlenbits) AST)
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
             (words_of_env n (env.take (words_ctx n) δw)))
          (words_of_env n (env.take (words_ctx n) lenvw))) : Pred wb)%I.
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
    Lemma rexec_triple_addr {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (instrs : gmap (bv xlenbits) AST)
      (words : bv xlenbits -> bv word)
      (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
      (tbl : list (Term Σ ty_xlenbits * AST)) (exits : list (Term Σ ty_xlenbits)) {w} :
      ⊢ ℛ⟦RHeapSpec RUnit⟧
          (cexec_triple_addr req instrs words exitCond fuel ens tbl exits)
          (sexec_triple_addr req tbl exits fuel ens (w := w)).
    Proof.
      unfold cexec_triple_addr, sexec_triple_addr.
      iApply (HeapSpec.refine_bind (RA := RNEnv LVar (Σ ▻▻ words_ctx (length tbl)))
                (RB := RUnit)).
      - rsolve.
      - iIntros (w1 θ0).
        iModIntro.
        iIntros (lenvw δw) "#Hδw".
        iApply refine_guard.
        iIntros "%Hfaith".
        destruct Hfaith as [Hif [Hef Hwg]].
        (* Split the extended demonic env: the Σ half feeds the existing
           itable_rel/etable_rel transport, the word half feeds
           words_of_env_take_inst. *)
        iPoseProof (refine_env_drop with "Hδw") as "#Hδ".
        iApply (HeapSpec.refine_bind (RA := RVal ty_xlenbits) (RB := RUnit)).
        { rsolve. }
        iIntros (w0 θ1).
        iModIntro.
        iIntros (a ta) "#Ha".
        (* The initial-nextpc demonic, paired here.  Both executors introduce it
           ONCE, right after `a` and before `produce req` — see
           exec_instruction_prologue (Verifier.v) for why it is a parameter
           threaded inward rather than an existential minted per step. *)
        iApply (HeapSpec.refine_bind (RA := RVal ty_xlenbits) (RB := RUnit)).
        { rsolve. }
        iIntros (w1' θ1').
        iModIntro.
        iIntros (np tnp) "#Hnp".
        iApply (HeapSpec.refine_bind (RA := RUnit) (RB := RUnit)).
        { rsolve. }
        iIntros (w2 θ2).
        iModIntro.
        iIntros (u tu) "#Hu".
        iApply (HeapSpec.refine_bind (RA := RVal ty_xlenbits) (RB := RUnit)).
        { (* TODO: It feels like rsolve should be able to handle this, if you have the right RefineCompat instances. *)
          iPoseProof (itable_rel_of_faith_forget (acc_trans (acc_trans θ1 θ1') θ2)
                        (env.drop (words_ctx (length tbl)) δw) Hif with "Hδ") as "#Hi0".
          iPoseProof (etable_rel_of_faith_forget (acc_trans (acc_trans θ1 θ1') θ2)
                        (env.drop (words_ctx (length tbl)) δw) Hef with "Hδ") as "#He".
          (* Build the loop-carried itable_relW out of the two guards: address
             column from Hi0, word column from Hwg + the demonic refinement. *)
          iPoseProof (wtable_rel_of_faith_forget (acc_trans (acc_trans θ1 θ1') θ2)
                        (env.drop (words_ctx (length tbl)) δw) Hwg with "Hδ") as "#Hw0".
          iPoseProof (words_rel_of_faith_forget (acc_trans (acc_trans θ1 θ1') θ2)
                        δw lenvw with "Hδw") as "#Hws".
          iAssert (itable_relW instrs words
                     (zip_words
                        (subst_itable (persist (env.drop (words_ctx (length tbl)) δw)
                                         (acc_trans (acc_trans θ1 θ1') θ2)) tbl)
                        (List.map (fun x => persist__term x (acc_trans (acc_trans θ1 θ1') θ2))
                           (words_of_env (length tbl)
                              (env.take (words_ctx (length tbl)) δw))))) as "#Hi".
          { iApply (itable_relW_zip_pred with "[$Hi0 $Hws $Hw0]"). }
          iApply (rexec_cfg_addr instrs words exitCond fuel _ _ with "[$Hi $He]").
          (* TWO RVal premises now: the pc, persisted across θ1' ∘ θ2, and the
             initial nextpc, persisted across θ2.  Bulleted rather than
             sequenced — a positional script here is what turned a missing
             premise into a type error 12 lines away in rexec_cfg_addr. *)
          - iApply (refine_inst_persist with "Ha").
          - iApply (refine_inst_persist with "Hnp"). }
        iIntros (w3 θ3).
        iModIntro.
        iIntros (na tna) "#Hna".
        rsolve.
        repeat (rewrite ?forgetting_trans; try iModIntro; rsolve).
    Qed.

    #[export] Instance refine_compat_exec_triple_addr {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (instrs : gmap (bv xlenbits) AST)
      (words : bv xlenbits -> bv word)
      (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
      (tbl : list (Term Σ ty_xlenbits * AST)) (exits : list (Term Σ ty_xlenbits)) {w} :
      RefineCompat (RHeapSpec RUnit)
        (cexec_triple_addr req instrs words exitCond fuel ens tbl exits) w
        (sexec_triple_addr req tbl exits fuel ens (w := w)) _ :=
      MkRefineCompat (rexec_triple_addr req instrs words exitCond fuel ens tbl exits).

    Definition ccfg_verification_condition {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (instrs : gmap (bv xlenbits) AST)
      (words : bv xlenbits -> bv word)
      (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
      (tbl : list (Term Σ ty_xlenbits * AST)) (exits : list (Term Σ ty_xlenbits)) : Prop :=
      CHeapSpec.run (cexec_triple_addr req instrs words exitCond fuel ens tbl exits).

    Lemma rcfg_verification_condition {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (instrs : gmap (bv xlenbits) AST)
      (words : bv xlenbits -> bv word)
      (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
      (tbl : list (Term Σ ty_xlenbits * AST)) (exits : list (Term Σ ty_xlenbits)) {w} :
      ⊢ RSat LogicalSoundness.RProp (w := w)
          (ccfg_verification_condition req instrs words exitCond fuel ens tbl exits)
          (scfg_verification_condition req tbl exits fuel ens w).
    Proof.
      unfold ccfg_verification_condition, scfg_verification_condition.
      rsolve.
    Qed.

    #[export] Instance refine_compat_cfg_verification_condition {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty_xlenbits)) (instrs : gmap (bv xlenbits) AST)
      (words : bv xlenbits -> bv word)
      (exitCond : bv xlenbits -> bool) (fuel : nat)
      (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
      (tbl : list (Term Σ ty_xlenbits * AST)) (exits : list (Term Σ ty_xlenbits)) {w} :
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
