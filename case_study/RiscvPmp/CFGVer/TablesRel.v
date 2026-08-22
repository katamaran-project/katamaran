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
(* CFGVer/TablesRel.v — table-faithfulness lemmas (itable_rel/etable_rel).  *)
(*                                                                          *)
(* Split out of Tables.v (2026-07-27). These five lemmas are the only part  *)
(* of the table layer whose STATEMENTS mention itable_rel/etable_rel, which *)
(* are `Pred w` — i.e. Iris — and so live in VerifierRel.v. Keeping them    *)
(* here lets Tables.v itself stay Iris-free, which matters because          *)
(* Contracts.v requires Tables.v and every Example/*.v requires Contracts.v *)
(* transitively; otherwise the whole example chain would pull in Iris.      *)
(*                                                                          *)
(* Sole consumer: EndToEnd.v.                                               *)
(* ======================================================================== *)

From Coq Require Import
     ZArith.ZArith
     Lists.List
     micromega.Lia
     Strings.String.
From Katamaran Require Import
     Notations
     Bitvector
     Semantics
     RiscvPmp.CFGVer.Spec
     RiscvPmp.CFGVer.Verifier
     RiscvPmp.CFGVer.VerifierRel
     RiscvPmp.CFGVer.Tables
     RiscvPmp.Machine
     RiscvPmp.Sig.
From stdpp Require Import gmap.
From iris.proofmode Require Import string_ident tactics.

Import RiscvPmpProgram.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import bv.notations.
Import env.notations.
Import ListNotations.

Import RiscvPmpCFGVerifExecutor.
Import Assembly.
Import RiscvPmp.Sig.

  (* itable_rel is monotone in the instruction map: enlarging the map
     preserves faithfulness of every table entry. *)
  Lemma itable_faith_weaken {Σ : LCtx} (m m' : gmap (bv xlenbits) AnnotInstr)
      (* the ALIAS, never a spelled-out tuple — five signatures in VerifierRel.v
         silently missed both new table columns that way *)
      (tbl : Katamaran.RiscvPmp.CFGVer.Verifier.SInstrTable (wlctx Σ))
      (ι : Valuation Σ) :
    m ⊆ m' ->
    Katamaran.RiscvPmp.CFGVer.VerifierRel.itable_rel (w := wlctx Σ) m tbl ι ->
    Katamaran.RiscvPmp.CFGVer.VerifierRel.itable_rel (w := wlctx Σ) m' tbl ι.
  Proof.
    intros Hsub. apply List.Forall_impl. intros [t i] (v & Hv & Hm).
    exists v. split; [exact Hv|]. eapply lookup_weaken; eauto.
  Qed.

  (* Once-and-for-all faithfulness of the constructed table w.r.t. the
     gmap store, at any valuation where the placement term resolves to a
     concrete base (generalized over the running offset). *)
  Lemma itable_faith_of_list_aux {Σ : LCtx} (p : Term Σ ty_xlenbits) (ι : Valuation Σ)
      (cbase : bv xlenbits) (instrs : list AnnotInstr) :
    inst (T := fun Σ => Term Σ ty_xlenbits) p ι = ty.SyncVal cbase ->
    forall off : N,
    (bv.bin cbase + off + 4 * N.of_nat (length instrs) < bv.exp2 xlenbits)%N ->
    Katamaran.RiscvPmp.CFGVer.VerifierRel.itable_rel (w := wlctx Σ)
      (instrs_of_list (bv.add cbase (bv.of_N off)) instrs)
      (table_of_list p off instrs) ι.
  Proof.
    intros Hp.
    induction instrs as [|i rest IH]; intros off Hbound.
    - constructor.
    - cbn [table_of_list instrs_of_list length] in *.
      constructor.
      + exists (bv.add cbase (bv.of_N off)). split.
        * cbn [fst].
          rewrite (peval_bvadd_sound (term_val ty_xlenbits (bv.of_N off)) p ι).
          cbn. rewrite Hp. cbn. f_equal. apply bv.add_comm.
        * cbn [snd]. apply lookup_insert.
      + rewrite Nat2N.inj_succ in Hbound.
        assert (Hb1 : (bv.bin (cbase + bv.of_N off)%bv <= bv.bin cbase + off)%N).
        { rewrite bv.bin_add.
          etransitivity.
          { apply N.Div0.mod_le. }
          apply N.add_le_mono_l. apply bv.bin_of_N_decr. }
        apply (itable_faith_weaken
                 (m := instrs_of_list (bv.add (bv.add cbase (bv.of_N off)) (bv.of_N 4)) rest)).
        { apply insert_subseteq.
          apply (instrs_of_list_fresh rest (bv.add cbase (bv.of_N off)) (d := 4)); [lia|].
          set (E := bv.exp2 xlenbits) in *; clearbody E. lia. }
        rewrite <- bv.add_assoc, bv.of_N_add.
        apply IH.
        set (E := bv.exp2 xlenbits) in *; clearbody E. lia.
  Qed.

  Lemma itable_faith_of_list {Σ : LCtx} (p : Term Σ ty_xlenbits) (ι : Valuation Σ)
      (cbase : bv xlenbits) (instrs : list AnnotInstr) :
    inst (T := fun Σ => Term Σ ty_xlenbits) p ι = ty.SyncVal cbase ->
    (bv.bin cbase + 4 * N.of_nat (length instrs) < bv.exp2 xlenbits)%N ->
    Katamaran.RiscvPmp.CFGVer.VerifierRel.itable_rel (w := wlctx Σ)
      (instrs_of_list cbase instrs) (table_of_list p 0 instrs) ι.
  Proof.
    intros Hp Hbound.
    replace cbase with (bv.add cbase (bv.of_N 0)) at 1
      by apply bv.add_zero_r.
    apply itable_faith_of_list_aux; [exact Hp|lia].
  Qed.

  (* Exit-table analog: the fall-through exit term is faithful to any
     exit condition that accepts the first address past the program. *)
  Lemma etable_faith_exits_of_list {Σ : LCtx} (p : Term Σ ty_xlenbits) (ι : Valuation Σ)
      (cbase : bv xlenbits) (exitCond : bv xlenbits -> bool) (instrs : list AnnotInstr) :
    inst (T := fun Σ => Term Σ ty_xlenbits) p ι = ty.SyncVal cbase ->
    exitCond (bv.add cbase (bv.of_N (4 * N.of_nat (length instrs)))) = true ->
    Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx Σ)
      exitCond (exits_of_list p instrs) ι.
  Proof.
    intros Hp Hexit.
    constructor; [|constructor].
    exists (bv.add cbase (bv.of_N (4 * N.of_nat (length instrs)))).
    split.
    - rewrite (peval_bvadd_sound
                 (term_val ty_xlenbits (bv.of_N (4 * N.of_nat (length instrs)))) p ι).
      cbn. rewrite Hp. cbn. f_equal. apply bv.add_comm.
    - exact Hexit.
  Qed.

  (* Offset-list analog: every listed exit offset is a genuine exit at any
     valuation resolving the placement term, provided the exit condition
     accepts each concrete address base + off. *)
  Lemma etable_faith_exits_of_offs {Σ : LCtx} (p : Term Σ ty_xlenbits) (ι : Valuation Σ)
      (cbase : bv xlenbits) (exitCond : bv xlenbits -> bool) (offs : list N) :
    inst (T := fun Σ => Term Σ ty_xlenbits) p ι = ty.SyncVal cbase ->
    List.Forall (fun o => exitCond (bv.add cbase (bv.of_N o)) = true) offs ->
    Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx Σ)
      exitCond (exits_of_offs p offs) ι.
  Proof.
    intros Hp Hoffs.
    unfold exits_of_offs, Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel.
    rewrite List.Forall_map.
    eapply List.Forall_impl; [|exact Hoffs].
    intros o Hex.
    exists (bv.add cbase (bv.of_N o)).
    split.
    - rewrite (peval_bvadd_sound (term_val ty_xlenbits (bv.of_N o)) p ι).
      cbn. rewrite Hp. cbn. f_equal. apply bv.add_comm.
    - exact Hex.
  Qed.
