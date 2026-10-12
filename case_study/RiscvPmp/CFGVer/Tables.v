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
(* instruction store builder instrs_of_list, and the symbolic term-table     *)
(* builders table_of_list / exit_of_off.                                      *)
(*                                                                           *)
(* DELIBERATELY Iris-free. The faithfulness lemmas linking these builders to *)
(* itable_rel / etable_rel live in TablesRel.v, because those guards are     *)
(* `Pred w` (Iris) and now sit in VerifierRel.v. That split matters: this    *)
(* file is required by Contracts.v, hence transitively by every             *)
(* Example/*.v, so keeping it Iris-free is what keeps the example chain off  *)
(* the ~0.98 GB binary Iris model. DON'T re-add an Iris require here.        *)
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
     RiscvPmp.CFGVer.Spec
     RiscvPmp.Machine
     RiscvPmp.Sig.
From stdpp Require Import gmap.
From Katamaran Require Import
     RiscvPmp.CFGVer.Verifier
     RiscvPmp.CFGVer.Noninterference.

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
Import ListNotations.
(* REQUIRED, and must stay after the imports above: ctx.notations (re-imported
   by RiscvPmp.Sig) declares `_ :: _` for Binding, which otherwise hijacks list
   cons — instrs_of_list / table_of_list then fail with "Found a constructor of
   inductive type Binding while a constructor of list is expected". This file
   used to get list cons back by accident, because `Import
   iris.proofmode.tactics.` came last; that import is gone now that the
   Iris-using faith lemmas live in TablesRel.v. Opening the scope explicitly is
   order-independent, unlike relying on which Import happens to come last. *)
Open Scope list_scope.

  (* Register names are `gpr`s (PLAN-spec-layer D15): statements use them as
     register keys, and instructions -- which take a 5-bit RegIdx -- get the
     index back through the coercion gpr_idx.  X0 is NOT a gpr (it is
     hardwired to zero), so it stays a bare RegIdx and can never be a key. *)
  Definition reg_idx_of {t} (r : Reg t) : RegIdx :=
    match r with
    | x1 => bv.of_nat 1 | x2 => bv.of_nat 2 | x3 => bv.of_nat 3 | x4 => bv.of_nat 4
    | x5 => bv.of_nat 5 | x6 => bv.of_nat 6 | x7 => bv.of_nat 7 | x8 => bv.of_nat 8
    | x9 => bv.of_nat 9 | x10 => bv.of_nat 10 | x11 => bv.of_nat 11 | x12 => bv.of_nat 12
    | x13 => bv.of_nat 13 | x14 => bv.of_nat 14 | x15 => bv.of_nat 15 | x16 => bv.of_nat 16
    | x17 => bv.of_nat 17 | x18 => bv.of_nat 18 | x19 => bv.of_nat 19 | x20 => bv.of_nat 20
    | x21 => bv.of_nat 21 | x22 => bv.of_nat 22 | x23 => bv.of_nat 23 | x24 => bv.of_nat 24
    | x25 => bv.of_nat 25 | x26 => bv.of_nat 26 | x27 => bv.of_nat 27 | x28 => bv.of_nat 28
    | x29 => bv.of_nat 29 | x30 => bv.of_nat 30 | x31 => bv.of_nat 31
    | _ => bv.zero
    end.

  Definition gpr_idx (g : gpr) : RegIdx := reg_idx_of (gpr_reg g).
  Coercion gpr_idx : gpr >-> RegIdx.

  (* The machine's own register decoding agrees with the gpr a key names. *)
  Lemma reg_convert_gpr_idx (g : gpr) : reg_convert (gpr_idx g) = Some (gpr_reg g).
  Proof.
    destruct g as [r H]. unfold gpr_idx, gpr_reg; cbn [proj1_sig].
    unfold is_gpr in H. apply decidable.bool_decide_eq_true in H as Hin.
    cbn [gpr_list] in Hin.
    repeat (apply list.elem_of_cons in Hin as [->|Hin]; [reflexivity|]).
    apply list.elem_of_nil in Hin as [].
  Qed.

  Definition X0 : RegIdx := bv.zero.
  Definition X1 : gpr := exist _ x1 eq_refl.
  Definition X2 : gpr := exist _ x2 eq_refl.
  Definition X3 : gpr := exist _ x3 eq_refl.
  Definition X4 : gpr := exist _ x4 eq_refl.

  (* RISC-V ABI register names, needed for examples translated straight
     from compiler-generated assembly (e.g. cmovznz4) instead of
     hand-picked X0..X4. *)
  Definition T0 : gpr := exist _ x5 eq_refl.
  Definition T1 : gpr := exist _ x6 eq_refl.
  Definition T2 : gpr := exist _ x7 eq_refl.
  Definition A0 : gpr := exist _ x10 eq_refl.
  Definition A1 : gpr := exist _ x11 eq_refl.
  Definition A2 : gpr := exist _ x12 eq_refl.
  Definition A3 : gpr := exist _ x13 eq_refl.
  Definition A4 : gpr := exist _ x14 eq_refl.
  Definition A5 : gpr := exist _ x15 eq_refl.
  Definition A6 : gpr := exist _ x16 eq_refl.
  Definition A7 : gpr := exist _ x17 eq_refl.
  Definition T3 : gpr := exist _ x28 eq_refl.
  Definition T4 : gpr := exist _ x29 eq_refl.
  Definition T5 : gpr := exist _ x30 eq_refl.
  Definition T6 : gpr := exist _ x31 eq_refl.
  (* Saved registers.  Added 2026-09-09: only S0..S3 are ever referenced, but
     they were being re-defined LOCALLY in 163 files under Example/ because
     they were missing here.  Same values as those copies (s0=x8, s1=x9,
     s2=x18, s3=x19), so a file that still defines them locally merely shadows
     these with identical bindings. *)
  Definition S0 : gpr := exist _ x8 eq_refl.
  Definition S1 : gpr := exist _ x9 eq_refl.
  Definition S2 : gpr := exist _ x18 eq_refl.
  Definition S3 : gpr := exist _ x19 eq_refl.

  (* Convert a contiguous instruction list into the finite map the CFG
     verifier now consumes.  Instruction k of the list is placed at the
     absolute address [base + 4*k] (4 = bytes_per_instr).  This is the
     "moment to convert" that keeps the ergonomic list syntax in the
     contracts while the verifier works purely with exact-match gmap
     lookups.

     POLYMORPHIC in the element type (2026-08-21, AnnotInstr migration).  The
     recursion is purely about ADDRESSES, so one definition serves both
     consumers: the executor instantiates it at AnnotInstr (cexec_cfg_addr,
     itable_rel) and the MEMORY predicates at AST (ptsto_instrs — memory holds
     instructions, not annotations), the latter by feeding it `strip instrs`.
     Deliberately ONE Fixpoint rather than a second `annots_of_list`: a near-copy
     would be duplication, and a `Definition instrs_of_list := @map_of_list AST`
     wrapper would break the `cbn [instrs_of_list]` in existing proofs. *)
  Fixpoint instrs_of_list {A} (base : bv xlenbits) (b : list A)
    : gmap (bv xlenbits) A :=
    match b with
    | []          => ∅
    | i :: rest   => <[ base := i ]> (instrs_of_list (bv.add base (bv.of_N 4)) rest)
    end.

  (* The bridge between the two instantiations: projecting the elements of the
     map is the same as projecting the list first.  This is a THEOREM about one
     shared recursion, not a faithfulness assumption two separate maps would
     have needed — which is why generalising is safe where a second symbolic
     table would not have been. *)
  Lemma fmap_instrs_of_list {A B} (f : A -> B) (base : bv xlenbits) (b : list A) :
    f <$> instrs_of_list base b = instrs_of_list base (List.map f b).
  Proof.
    revert base. induction b as [|i rest IH]; intros base; cbn [instrs_of_list List.map].
    - apply fmap_empty.
    - now rewrite fmap_insert, IH.
  Qed.

  (* words_of_list: the raw instruction WORD at each absolute address, keyed by
     the same addresses instrs_of_list uses.  A TOTAL FUNCTION rather than a
     gmap, deliberately: a partial word map would add a "no word at this
     address" case to the concrete executor, a domain side condition to
     ptsto_instrs_w, and a matching case to every proof downstream — none of
     which carry information, since the word list is exactly as long as the
     instruction list.  Off the program it reads bv.zero, which is never
     observed.  The word list is the `ws` that mem_has_instrs already carries,
     so nothing new has to be invented to supply it. *)
  Fixpoint words_of_list (base : bv xlenbits) (ws : list (bv word))
    : bv xlenbits -> bv word :=
    match ws with
    | []          => fun _ => bv.zero
    | x :: rest   => fun k => if bv.eqb k base then x
                              else words_of_list (bv.add base (bv.of_N 4)) rest k
    end.

  (* bv.eqb reflected both ways.  Destructing bv.eqb_spec directly inside
     words_of_list's `if` does NOT work — the scrutinee is a closed term there,
     so Coq will not abstract it and the `if` survives; decide the boolean
     first and rewrite. *)
  Lemma bv_eqb_refl {n} (x : bv n) : bv.eqb x x = true.
  Proof. unfold bv.eqb. apply N.eqb_refl. Qed.

  Lemma bv_eqb_neq {n} (x y : bv n) : x <> y -> bv.eqb x y = false.
  Proof.
    intros Hne.
    destruct (bv.eqb_spec x y) as [Heq|_]; [contradiction|reflexivity].
  Qed.

  Lemma words_of_list_here (base : bv xlenbits) (x : bv word) (ws : list (bv word)) :
    words_of_list base (x :: ws) base = x.
  Proof. cbn [words_of_list]. rewrite bv_eqb_refl. reflexivity. Qed.

  Lemma words_of_list_there (base k : bv xlenbits) (x : bv word) (ws : list (bv word)) :
    k <> base ->
    words_of_list base (x :: ws) k = words_of_list (bv.add base (bv.of_N 4)) ws k.
  Proof. intros Hne. cbn [words_of_list]. rewrite (bv_eqb_neq Hne). reflexivity. Qed.

  (* An instruction address never collides with a later one, provided the
     whole program fits below 2^xlenbits (no wraparound).  This is the side
     condition [big_sepM_insert] needs to peel the head instruction off the
     gmap. *)
  Lemma instrs_of_list_fresh {A} (b : list A) (base : bv xlenbits) (d : N) :
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
  (* SEGMENT CONTAINMENT (2026-09-04).                                    *)
  (*                                                                     *)
  (* A contract that only knows the instructions it actually executes    *)
  (* carries a table over a SEGMENT of the program, while the machine    *)
  (* owns the whole program's store.  itable_rel is indexed by the TABLE *)
  (* and only asks that the map CONTAIN each entry (see VerifierRel.v),  *)
  (* and TablesRel.v's itable_faith_weaken lifts it along map inclusion  *)
  (* -- so the whole soundness obligation for a sub-table contract       *)
  (* reduces to the three gmap containments below.                       *)
  (*                                                                     *)
  (* Measured motivation: a segment contract whose branch condition the  *)
  (* solver cannot decide by computation costs                           *)
  (* 93.81 + 4.05*P + 0.531*P^2 M words in the number P of              *)
  (* NEVER-EXECUTED instructions sharing its table, so trimming the      *)
  (* table is worth (K/k)^2 -- 26.93x already at 64 filler instructions. *)
  (* diagnostics/prefix-length-cost.md.                                  *)

  (* A prefix of the list occupies a sub-map: same base, fewer entries.
     No bound needed -- insert_mono is structural, and any address
     collision from wraparound would only make the RIGHT side smaller in
     the same way. *)
  Lemma instrs_of_list_prefix {A} (l1 l2 : list A) (base : bv xlenbits) :
    instrs_of_list base l1 ⊆ instrs_of_list base (l1 ++ l2).
  Proof.
    revert base. induction l1 as [|i rest IH]; intros base; cbn [instrs_of_list app].
    - apply map_empty_subseteq.
    - apply insert_mono. apply IH.
  Qed.

  (* Dropping l1 from the front shifts the base by 4*|l1| and lands inside
     the full map.  The no-wrap bound is the same one instrs_of_list_fresh
     needs, and is used for exactly that: to peel each head insert. *)
  Lemma instrs_of_list_suffix {A} (l1 l2 : list A) (base : bv xlenbits) :
    (bv.bin base + 4 * N.of_nat (length l1 + length l2) < bv.exp2 xlenbits)%N ->
    instrs_of_list (bv.add base (bv.of_N (4 * N.of_nat (length l1)))) l2
      ⊆ instrs_of_list base (l1 ++ l2).
  Proof.
    revert base. induction l1 as [|i rest IH]; intros base Hbound;
      cbn [instrs_of_list app length] in *.
    - (* bv.of_N 0 is only CONVERTIBLE to bv.zero, so rewrite bv.add_zero_r
         finds no subterm; apply does, through conversion. *)
      replace (bv.add base (bv.of_N (4 * N.of_nat 0))) with base
        by (symmetry; apply bv.add_zero_r).
      reflexivity.
    - replace (4 * N.of_nat (S (length rest)))%N
        with (4 + 4 * N.of_nat (length rest))%N by lia.
      rewrite <- bv.of_N_add, bv.add_assoc.
      assert (Hb1 : (bv.bin (bv.add base (bv.of_N 4)) <= bv.bin base + 4)%N).
      { rewrite bv.bin_add. etransitivity; [apply N.Div0.mod_le|].
        apply N.add_le_mono_l. apply bv.bin_of_N_decr. }
      etransitivity.
      + apply IH.
        (* lia chokes on 2^32; make bv.exp2 xlenbits an opaque atom first. *)
        set (E := bv.exp2 xlenbits) in *; clearbody E. lia.
      + apply insert_subseteq.
        apply (instrs_of_list_fresh (rest ++ l2) base (d := 4)); [lia|].
        rewrite length_app.
        set (E := bv.exp2 xlenbits) in *; clearbody E. lia.
  Qed.

  (* The combination a segment contract needs: the store of the segment,
     based at its own address, sits inside the store of the whole program.
     `off` is 4 * |pre|, i.e. the segment's byte offset -- which a segment
     contract carries in its PLACEMENT term rather than as a table prefix. *)
  Lemma instrs_of_list_segment {A} (pre seg post : list A) (base : bv xlenbits) :
    (bv.bin base + 4 * N.of_nat (length (pre ++ seg ++ post)) < bv.exp2 xlenbits)%N ->
    instrs_of_list (bv.add base (bv.of_N (4 * N.of_nat (length pre)))) seg
      ⊆ instrs_of_list base (pre ++ seg ++ post).
  Proof.
    intros Hbound.
    etransitivity; [apply (instrs_of_list_prefix seg post)|].
    apply instrs_of_list_suffix.
    rewrite !length_app in *. lia.
  Qed.


  (* ------------------------------------------------------------------ *)
  (* Term-level instruction/exit tables (symbolic placement).            *)
  (*                                                                     *)
  (* table_of_list builds the address-term instruction table for the     *)
  (* table-based symbolic executor (sexec_cfg_addr), pairing each        *)
  (* address with its AnnotInstr record (instruction + optional ghosts). *)
  (* The base address can be concrete (term_val b) or symbolic (e.g.     *)
  (* term_var "p" in parametric contracts); addresses are computed via   *)
  (* peval_bvadd so they're born canonical — concrete bases fold to      *)
  (* literals, symbolic bases take the constant-first shape (offset 0    *)
  (* collapses to base itself).                                          *)
  (*                                                                     *)
  (* NOTE: `is` is an SSReflect keyword in this file, hence `instrs`.    *)
  (* ------------------------------------------------------------------ *)
  Fixpoint table_of_list {Σ : LCtx} (base : Term Σ ty_xlenbits) (off : N) (instrs : list AnnotInstr)
    : list (Term Σ ty_xlenbits * AnnotInstr) :=
    match instrs with
    | []        => []
    | ai :: rest =>
        let addr := peval_bvadd (term_val ty_xlenbits (bv.of_N off)) base in
        (addr, ai) :: table_of_list base (off + 4)%N rest
    end.

  (* THE EXIT TERM, from a base-relative byte offset (PLAN-exit-targets.md).
     A contract has exactly ONE exit, so this replaced the two list builders
     `exits_of_list` (the fall-through, [4·len]) and `exits_of_offs` (a list
     of offsets).  The key goes through peval_bvadd like the instruction
     table's, so `is_exit` can match it syntactically.  For a program whose
     only exit is its fall-through, pass `4 * length instrs`. *)
  Definition exit_of_off {Σ : LCtx} (p : Term Σ ty_xlenbits) (off : N)
    : Term Σ ty_xlenbits :=
    peval_bvadd (term_val ty_xlenbits (bv.of_N off)) p.


  (* Transit the end-to-end layer's lenAddr bound into the no-wrap bound
     itable_faith_of_list needs.  lia cannot handle bv.exp2 xlenbits (2^32)
     directly, so bound below lenAddr first and transit. *)
  Lemma table_bound_of_lenAddr (ia : N) (len : nat) :
    (ia + 4 * N.of_nat len < lenAddr)%N ->
    (bv.bin (@bv.of_N xlenbits ia) + 4 * N.of_nat len < bv.exp2 xlenbits)%N.
  Proof.
    intros H.
    pose proof (@bv.bin_of_N_decr xlenbits ia) as Hdec.
    set (B := bv.bin (@bv.of_N xlenbits ia)) in *; clearbody B.
    assert (Hsmall : (B + 4 * N.of_nat len < lenAddr)%N) by lia.
    eapply N.lt_trans; [exact Hsmall|].
    exact lenAddr_rep.
  Qed.

    (* TODO: move into Spec.v *)
    Definition JAL (rd : RegIdx) (imm : bv 21) : AST :=
      RISCV_JAL imm rd.
    Definition NOP : AST := MV X0 X0.
    Definition LW (rd rs : RegIdx) (imm : bv 12) : AST :=
      LOAD imm rs rd false WORD.
    Definition SW (rs2 rs1 : RegIdx) (imm : bv 12) : AST :=
      STORE imm rs2 rs1 WORD.

    (* Byte load, zero-extended: rd := zext(mem[rs + imm]).  Field order is
       LOAD imm rs1 rd is_unsigned width (Base.v:287); is_unsigned = true
       makes fun_execute_LOAD's process_load/extend_value take the
       uop.zext 8 -> 32 branch (Machine.v:619).  LW above passes false, which
       is immaterial at WORD but decisive here.  This is the first BYTE-width
       memory access in the case study -- see PLAN-byte-memory.md. *)
    Definition LBU (rd rs : RegIdx) (imm : bv 12) : AST :=
      LOAD imm rs rd true BYTE.
