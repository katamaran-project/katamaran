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


(* ========================================================================= *)
(* Tables.v — assembly vocabulary and list→table builders.                   *)
(*                                                                           *)
(* Register aliases (X0–A7), assembler macros (JAL/NOP/LW/SW), the gmap      *)
(* instruction store builder instrs_of_list, the symbolic term-table         *)
(* builders table_of_list / exits_of_list / exits_of_offs, and the           *)
(* faithfulness lemmas linking them to Verifier.v's itable_faith /           *)
(* etable_faith guards.                                                      *)
(* ========================================================================= *)

From Coq Require Import
     ZArith.ZArith
     Lists.List
     micromega.Lia
     Strings.String.
From Katamaran Require Import
     Notations
     Bitvector
     Semantics
     RiscvPmp.BlockVer.Spec
     RiscvPmp.BlockVer.Verifier
     RiscvPmp.Machine
     RiscvPmp.Sig.
From stdpp Require Import gmap.
From Katamaran Require
     RiscvPmp.CFGVer.Verifier.

From iris.proofmode Require string_ident tactics.

Import RiscvPmpProgram.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import bv.notations.
Import env.notations.
Import ListNotations.

Import RiscvPmpBlockVerifExecutor.
Import Assembly.
Import RiscvPmp.Sig.
Import iris.proofmode.tactics.

  Definition X0 : RegIdx := bv.zero.
  Definition X1 : RegIdx := bv.one.
  Definition X2 : RegIdx := bv.of_nat 2.
  Definition X3 : RegIdx := bv.of_nat 3.
  Definition X4 : RegIdx := bv.of_nat 4.

  (* RISC-V ABI register names, needed for examples translated straight
     from compiler-generated assembly (e.g. cmovznz4) instead of
     hand-picked X0..X4. *)
  Definition T0 : RegIdx := bv.of_nat 5.
  Definition T1 : RegIdx := bv.of_nat 6.
  Definition A0 : RegIdx := bv.of_nat 10.
  Definition A1 : RegIdx := bv.of_nat 11.
  Definition A2 : RegIdx := bv.of_nat 12.
  Definition A3 : RegIdx := bv.of_nat 13.
  Definition A4 : RegIdx := bv.of_nat 14.
  Definition A5 : RegIdx := bv.of_nat 15.
  Definition A6 : RegIdx := bv.of_nat 16.
  Definition A7 : RegIdx := bv.of_nat 17.

  (* Convert a contiguous instruction list into the finite map the CFG
     verifier now consumes.  Instruction k of the list is placed at the
     absolute address [base + 4*k] (4 = bytes_per_instr).  This is the
     "moment to convert" that keeps the ergonomic list syntax in the
     contracts while the verifier works purely with exact-match gmap
     lookups. *)
  Fixpoint instrs_of_list (base : bv xlenbits) (b : list AST)
    : gmap (bv xlenbits) AST :=
    match b with
    | []          => ∅
    | i :: rest   => <[ base := i ]> (instrs_of_list (bv.add base (bv.of_N 4)) rest)
    end.

  (* An instruction address never collides with a later one, provided the
     whole block fits below 2^xlenbits (no wraparound).  This is the side
     condition [big_sepM_insert] needs to peel the head of a block off the
     gmap. *)
  Lemma instrs_of_list_fresh (b : list AST) (base : bv xlenbits) (d : N) :
    (0 < d)%N ->
    (bv.bin base + d + 4 * N.of_nat (length b) < bv.exp2 xlenbits)%N ->
    instrs_of_list (bv.add base (bv.of_N d)) b !! base = None.
  Proof.
    revert d. induction b as [|i rest IH]; intros d Hd Hbound.
    - apply lookup_empty.
    - cbn [instrs_of_list length] in *.
      rewrite lookup_insert_ne.
      + rewrite <- bv.add_assoc, bv.of_N_add.
        apply IH; [lia|].
        rewrite Nat2N.inj_succ in Hbound.
        (* lia chokes when it evaluates bv.exp2 xlenbits to 2^32, so make it
           an opaque atom first. *)
        set (E := bv.exp2 xlenbits) in *; clearbody E. lia.
      + intro Heq.
        apply (f_equal (@bv.bin xlenbits)) in Heq.
        (* SSReflect's rewrite (in scope here) rejects the Ltac `by` clause,
           so provide bin_of_N_small / bin_add_small's side conditions as
           explicit hypotheses.  Each exp2 bound is discharged with exp2
           made opaque (see above). *)
        assert (Hd_lt : (d < bv.exp2 xlenbits)%N).
        { set (E := bv.exp2 xlenbits) in *; clearbody E. lia. }
        pose proof (bv.bin_of_N_small Hd_lt) as Hdd.
        assert (Hsmall : (bv.bin base + bv.bin (@bv.of_N xlenbits d) < bv.exp2 xlenbits)%N).
        { rewrite Hdd. set (E := bv.exp2 xlenbits) in *; clearbody E. lia. }
        rewrite (bv.bin_add_small Hsmall) in Heq.
        rewrite Hdd in Heq. lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Term-level instruction/exit tables (symbolic placement).            *)
  (*                                                                     *)
  (* table_of_list builds the address-term instruction table for the     *)
  (* table-based symbolic executor (sexec_cfg_addr_tbl): the key for the *)
  (* k-th instruction is peval_bvadd (term_val (4k+off)) p, constructed  *)
  (* THROUGH peval_bvadd so keys are born canonical — for a concrete     *)
  (* placement term p = term_val b they fold to literals, for a symbolic *)
  (* p they take the constant-first `c ⊕ p` shape the step semantics     *)
  (* produces (offset 0 collapses to p itself via the zero rule).        *)
  (*                                                                     *)
  (* NOTE: `is` is an SSReflect keyword in this file, hence `instrs`.    *)
  (* ------------------------------------------------------------------ *)
  Fixpoint table_of_list {Σ : LCtx} (p : Term Σ ty_xlenbits) (off : N) (instrs : list AST)
    : list (Term Σ ty_xlenbits * AST) :=
    match instrs with
    | []        => []
    | i :: rest => (peval_bvadd (term_val ty_xlenbits (bv.of_N off)) p, i)
                     :: table_of_list p (off + 4)%N rest
    end.

  (* Default exit table: the single fall-through address just past the
     instruction block. *)
  Definition exits_of_list {Σ : LCtx} (p : Term Σ ty_xlenbits) (instrs : list AST)
    : list (Term Σ ty_xlenbits) :=
    [peval_bvadd (term_val ty_xlenbits (bv.of_N (4 * N.of_nat (length instrs)))) p].

  (* General exit table from base-relative byte offsets.  Programs whose
     control flow leaves the block anywhere other than the fall-through
     address (e.g. a branch whose taken target lies past the block) list
     ALL their exit offsets here; exits_of_list is the [4·len] special
     case.  Keys go through peval_bvadd like the instruction table. *)
  Definition exits_of_offs {Σ : LCtx} (p : Term Σ ty_xlenbits) (offs : list N)
    : list (Term Σ ty_xlenbits) :=
    List.map (fun o => peval_bvadd (term_val ty_xlenbits (bv.of_N o)) p) offs.

  (* itable_faith is monotone in the instruction map: enlarging the map
     preserves faithfulness of every table entry. *)
  Lemma itable_faith_weaken {Σ : LCtx} (m m' : gmap (bv xlenbits) AST)
      (tbl : list (Term Σ ty_xlenbits * AST)) (ι : Valuation Σ) :
    m ⊆ m' ->
    Katamaran.RiscvPmp.CFGVer.Verifier.itable_faith m tbl ι ->
    Katamaran.RiscvPmp.CFGVer.Verifier.itable_faith m' tbl ι.
  Proof.
    intros Hsub. apply List.Forall_impl. intros [t i] (v & Hv & Hm).
    exists v. split; [exact Hv|]. eapply lookup_weaken; eauto.
  Qed.

  (* Once-and-for-all faithfulness of the constructed table w.r.t. the
     gmap store, at any valuation where the placement term resolves to a
     concrete base (generalized over the running offset). *)
  Lemma itable_faith_of_list_aux {Σ : LCtx} (p : Term Σ ty_xlenbits) (ι : Valuation Σ)
      (cbase : bv xlenbits) (instrs : list AST) :
    inst (T := fun Σ => Term Σ ty_xlenbits) p ι = ty.SyncVal cbase ->
    forall off : N,
    (bv.bin cbase + off + 4 * N.of_nat (length instrs) < bv.exp2 xlenbits)%N ->
    Katamaran.RiscvPmp.CFGVer.Verifier.itable_faith
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
      (cbase : bv xlenbits) (instrs : list AST) :
    inst (T := fun Σ => Term Σ ty_xlenbits) p ι = ty.SyncVal cbase ->
    (bv.bin cbase + 4 * N.of_nat (length instrs) < bv.exp2 xlenbits)%N ->
    Katamaran.RiscvPmp.CFGVer.Verifier.itable_faith
      (instrs_of_list cbase instrs) (table_of_list p 0 instrs) ι.
  Proof.
    intros Hp Hbound.
    replace cbase with (bv.add cbase (bv.of_N 0)) at 1
      by apply bv.add_zero_r.
    apply itable_faith_of_list_aux; [exact Hp|lia].
  Qed.

  (* Exit-table analog: the fall-through exit term is faithful to any
     exit condition that accepts the first address past the block. *)
  Lemma etable_faith_exits_of_list {Σ : LCtx} (p : Term Σ ty_xlenbits) (ι : Valuation Σ)
      (cbase : bv xlenbits) (exitCond : bv xlenbits -> bool) (instrs : list AST) :
    inst (T := fun Σ => Term Σ ty_xlenbits) p ι = ty.SyncVal cbase ->
    exitCond (bv.add cbase (bv.of_N (4 * N.of_nat (length instrs)))) = true ->
    Katamaran.RiscvPmp.CFGVer.Verifier.etable_faith
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
    Katamaran.RiscvPmp.CFGVer.Verifier.etable_faith
      exitCond (exits_of_offs p offs) ι.
  Proof.
    intros Hp Hoffs.
    unfold exits_of_offs, Katamaran.RiscvPmp.CFGVer.Verifier.etable_faith.
    rewrite List.Forall_map.
    eapply List.Forall_impl; [|exact Hoffs].
    intros o Hex.
    exists (bv.add cbase (bv.of_N o)).
    split.
    - rewrite (peval_bvadd_sound (term_val ty_xlenbits (bv.of_N o)) p ι).
      cbn. rewrite Hp. cbn. f_equal. apply bv.add_comm.
    - exact Hex.
  Qed.

  (* Transit the end-to-end layer's lenAddr bound into the no-wrap bound
     itable_faith_of_list needs.  lia cannot handle bv.exp2 xlenbits (2^32)
     directly, so bound below lenAddr = 2^10 first and transit. *)
  Lemma table_bound_of_lenAddr (ia : N) (len : nat) :
    (ia + 4 * N.of_nat len < lenAddr)%N ->
    (bv.bin (@bv.of_N xlenbits ia) + 4 * N.of_nat len < bv.exp2 xlenbits)%N.
  Proof.
    intros H.
    pose proof (@bv.bin_of_N_decr xlenbits ia) as Hdec.
    set (B := bv.bin (@bv.of_N xlenbits ia)) in *; clearbody B.
    unfold lenAddr in H.
    assert (Hsmall : (B + 4 * N.of_nat len < 2 ^ 10)%N) by lia.
    eapply N.lt_trans; [exact Hsmall|].
    now vm_compute.
  Qed.

    (* TODO: move into Spec.v *)
    Definition JAL (rd : RegIdx) (imm : bv 21) : AST :=
      RISCV_JAL imm rd.
    Definition NOP : AST := MV X0 X0.
    Definition LW (rd rs : RegIdx) (imm : bv 12) : AST :=
      LOAD imm rs rd false WORD.
    Definition SW (rs2 rs1 : RegIdx) (imm : bv 12) : AST :=
      STORE imm rs2 rs1 WORD.
