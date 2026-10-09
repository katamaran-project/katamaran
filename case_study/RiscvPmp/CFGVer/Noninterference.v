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
(* Noninterference.v — the TRUSTED STATEMENT layer of CFGVer.                *)
(*                                                                           *)
(* Everything the concrete end-to-end theorems (Results.v) mention in their  *)
(* STATEMENTS lives here: the machine-level step relations, the memory/      *)
(* register initialization and publicness predicates, the spec types, and    *)
(* noninterferent_strong itself.  This file deliberately does NOT depend on  *)
(* the verifier (CFGVer.Verifier), the contract layer, or the Iris model:    *)
(* the meaning of the end-to-end theorems can be audited from this file,     *)
(* Results.v, and the per-example instruction/spec definitions alone.        *)
(* Changes here change WHAT is being proved — review accordingly.            *)
(* ========================================================================= *)

From Coq Require Import
     ZArith.ZArith
     Lists.List
     micromega.Lia
     Strings.String.
(* This file deliberately requires NEITHER RiscvPmp.CFGVer.Spec NOR RiscvPmp.Sig,
   and so pulls in no symbolic executor, no predicate signature and no (binary)
   Iris model. It is the trusted STATEMENT layer: small-step relations,
   declare_*, spec types and noninterferent_strong, all expressible with the
   operational semantics alone.

   This is worth 2.5 GB of peak RSS (3.63 -> 1.15 GB) and 6.5 s (9.6 -> 3.0 s),
   and it takes the file off the serial Spec -> Verifier critical path so it
   builds in parallel with them. It used to require both only because of a
   vestigial preamble inherited from the old monolithic Examples.v: the sole
   references to either were three bare `Import RiscvPmpCFGVerifExecutor.` /
   `Import Assembly.` / `Import RiscvPmp.Sig.` lines, and nothing here used a
   single name from them.

   Verified 2026-07-27: all 30 definitions below elaborate to byte-identical
   terms under `Set Printing All` before and after the removal, so the trusted
   statements are unchanged. DON'T re-add either require — doing so silently
   costs 2.5 GB on a file that is the reason the statement layer is auditable
   without the verifier. *)
From Katamaran Require Import
     Notations
     Bitvector
     Semantics
     RiscvPmp.Machine.
From stdpp Require Import gmap.

Import RiscvPmpProgram.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import bv.notations.
Import env.notations.
Import ListNotations.
Import RiscvPmpSemantics.
Import SmallStepNotations.

  (* Default load address for examples that don't care about a nonzero
     start (the {{ }} contract notations in Contracts.v and the concrete
     theorems in Results.v use it as their default init_addr). *)
  Definition init_addr     : N := 0.

(* ---- What a statement says about ONE value (PLAN-spec-layer D10) ----------
   One type for every register and memory word, instantiated per layer (the
   front-ends map it with val_spec_map, which cannot turn Secret into Public):
     Secret  : unconstrained -- the two runs may differ.  Produces NO premise.
     Public  : equal in both runs, value unknown.
     Known v : exactly v in both runs.                                       *)
    Inductive val_spec (V : Type) : Type :=
    | Secret
    | Public
    | Known (v : V).
    Arguments Secret {V}.
    Arguments Public {V}.
    Arguments Known {V} v.

    Definition val_spec_map {A B} (f : A -> B) (s : val_spec A) : val_spec B :=
      match s with
      | Secret  => Secret
      | Public  => Public
      | Known v => Known (f v)
      end.

(* ---- Register keys: the 31 general-purpose registers (D15) ----------------
   x0 is hardwired to zero, and pc / cur_privilege / mtvec / pmp* are not
   general-purpose, so none of them can be written as a key. *)
    Definition gpr_list : list (Reg ty_xlenbits) :=
      [x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15; x16;
       x17; x18; x19; x20; x21; x22; x23; x24; x25; x26; x27; x28; x29; x30; x31].

    Definition is_gpr (r : Reg ty_xlenbits) : bool :=
      bool_decide (existT ty_xlenbits r ∈ List.map (existT ty_xlenbits) gpr_list).

    Definition gpr : Type := { r : Reg ty_xlenbits | is_gpr r = true }.

    Definition gpr_reg (g : gpr) : Reg ty_xlenbits := proj1_sig g.

    (* A register entry of a statement. *)
    Definition reg_spec : Type := gpr * val_spec (Val ty_xlenbits).

    (* THE STOP TEST (PLAN-exit-targets.md, 2026-09-25): a run stops exactly
       when the pc IS the program's single exit address.  It replaced
       `pcOutOfInstrs_exitCond init_addr instrs` (pc >= init_addr + 4|instrs|),
       so a run that leaves the code anywhere else is no longer a stopping run.
       Boolean, like the old condition, because the stepping relations below
       test `~ exitCond pc` through the Is_true coercion. *)
    Definition atPc (exit_addr : N) : bv xlenbits -> bool :=
      fun v => bv.eqb v (bv.of_N exit_addr).

  (* Registers both runs must agree on: the Public entries. *)
  Definition gen_public_regs (specs : list reg_spec) : list (Reg ty_xlenbits) :=
    base.omap (fun '(r, s) =>
      match s with Public => Some (gpr_reg r) | _ => None end) specs.

(* ---- Reading memory -------------------------------------------------------
   get_word is THE data-word reader.  It assembles the bytes at a, a+1, a+2,
   a+3 with the byte at a in the LOW position -- exactly what the machine's
   own load reads (get_word_read_ram; Base.v tests read_ram to be little
   endian).  mem_has_word is the same fact, phrased for instructions
   (mem_has_word_get_word). *)
    Definition get_word (μ : Memory) (a : Val ty_word) : Val ty_word :=
      bv.app (memory_ram μ a)
        (bv.app (memory_ram μ (bv.add bv.one a))
          (bv.app (memory_ram μ (bv.add (bv.of_N 2) a))
            (bv.app (memory_ram μ (bv.add (bv.of_N 3) a)) bv.nil))).

    Lemma get_word_read_ram (μ : Memory) (a : Val ty_word) :
      get_word μ a = fun_read_ram μ 4 a.
    Proof.
      unfold get_word. cbn [fun_read_ram].
      rewrite !bv.add_assoc.
      change (bv.add bv.one bv.one) with (@bv.of_N xlenbits 2).
      change (bv.add bv.one (@bv.of_N xlenbits 2)) with (@bv.of_N xlenbits 3).
      reflexivity.
    Qed.

    Definition mem_has_word (μ : Memory) (a : Val ty_word) (w : Val ty_word) : Prop :=
      exists v0 v1 v2 v3, List.map (memory_ram μ) (bv.seqBv a 4) = [v0; v1; v2; v3]%list /\ bv.app v0 (bv.app v1 (bv.app v2 (bv.app v3 bv.nil))) = w.

    Lemma mem_has_word_get_word (μ : Memory) (a w : Val ty_word) :
      mem_has_word μ a w <-> get_word μ a = w.
    Proof.
      assert (Hseq : bv.seqBv a 4 = [a; bv.add bv.one a; bv.add (bv.of_N 2) a; bv.add (bv.of_N 3) a]%list).
      { unfold bv.seqBv, seqZ.
        change (Z.to_nat (Z.of_N 4)) with 4%nat.
        cbn [seq fmap list_fmap List.map].
        repeat f_equal.
        all: rewrite <- bv.of_Z_add, bv.of_Z_unsigned.
        - apply bv.add_zero_l.
        - change (Z.of_nat 1) with (Z.of_N 1). now rewrite bv.of_Z_N.
        - change (Z.of_nat 2) with (Z.of_N 2). now rewrite bv.of_Z_N.
        - change (Z.of_nat 3) with (Z.of_N 3). now rewrite bv.of_Z_N. }
      unfold mem_has_word, get_word. rewrite Hseq. cbn [List.map]. split.
      - intros (v0 & v1 & v2 & v3 & Hm & <-). injection Hm as E0 E1 E2 E3. subst. reflexivity.
      - intros <-. eauto 10.
    Qed.

    Definition mem_has_instr (μ : Memory) (a : Val ty_word) w (instr : AST) : Prop :=
      mem_has_word μ a w /\ pure_decode w = inr instr.

    Fixpoint mem_has_instrs (μ : Memory) (a : Val ty_word) ws (instrs : list AST) : Prop :=
      match ws , instrs with
      | cons w ws , cons inst instrs => mem_has_instr μ a w inst /\ mem_has_instrs μ (bv.add (bv.of_N 4) a) ws instrs
      | nil , nil => True
      | _ , _ => False
      end.

(* ---- Data memory: a layout of disjoint blocks (D11, P1) -------------------
   A block is a start address and the spec of each consecutive WORD from
   there.  A layout is a list of blocks plus a proof that no two overlap, so
   an overlapping layout cannot be written at all.  Addresses are N, so the
   overlap test cannot wrap around; staying below lenAddr is the statement's
   own premise.  Clear of the code is a conjunct of noninterferent_strong
   (D19), not part of the type. *)
    Record mem_block : Type := {
      blk_addr  : N;
      blk_words : list (val_spec (Val ty_word))
    }.

    Definition blk_end (b : mem_block) : N :=
      blk_addr b + 4 * N.of_nat (length (blk_words b)).

    Definition blocks_disjoint (bs : list mem_block) : Prop :=
      ForallOrdPairs (fun b c => blk_end b <= blk_addr c \/ blk_end c <= blk_addr b)%N bs.

    Record mem_layout : Type := {
      blocks    : list mem_block;
      blocks_ok : blocks_disjoint blocks
    }.

    (* One word of a layout: its address and its spec. *)
    Definition mem_cell : Type := N * val_spec (Val ty_word).

    (* The words of a block, each at its own address: a, a+4, a+8, ... *)
    Fixpoint words_at (a : N) (ws : list (val_spec (Val ty_word))) :
        list mem_cell :=
      match ws with
      | nil       => nil
      | cons w ws => cons (a, w) (words_at (a + 4) ws)
      end.

    Definition cells (m : mem_layout) : list mem_cell :=
      concat (List.map (fun b => words_at (blk_addr b) (blk_words b)) (blocks m)).

    (* Every block lies entirely below or entirely above the code. *)
    Definition clear_of_code (init_addr : N) (instrs : list AST) (m : mem_layout) : Prop :=
      Forall (fun b => blk_end b <= init_addr \/
                       init_addr + 4 * N.of_nat (length instrs) <= blk_addr b)%N
        (blocks m).

    (* declare_public_memory: the two worlds agree on the word value at
       every address listed as public *)
    Definition declare_public_memory (μ1 μ2 : Memory)
        (public_addrs : list (Val ty_word)) : Prop :=
      List.Forall (fun a => get_word μ1 a = get_word μ2 a) public_addrs.

    (* Words both runs must agree on: the Public cells. *)
    Definition gen_public_addrs (cs : list mem_cell) : list (Val ty_word) :=
      base.omap (fun '(a, s) =>
        match s with Public => Some (bv.of_N a) | _ => None end) cs.

    (* reg_init_spec: a register with its required initial value in both worlds *)
    Definition reg_init_spec : Type := 𝑹𝑬𝑮 ty_xlenbits * Val ty_xlenbits.

    (* mem_init_spec: a word address with its required initial value in both worlds *)
    Definition mem_init_spec : Type := Val ty_word * Val ty_word.

    (* Each register r in specs holds value v in γ *)
    Definition declare_init_registers (γ : RegStore)
        (specs : list reg_init_spec) : Prop :=
      List.Forall (fun s => read_register γ s.1 = s.2) specs.

    (* Each address a in specs holds word value v in μ *)
    Definition declare_init_memory (μ : Memory)
        (specs : list mem_init_spec) : Prop :=
      List.Forall (fun s => get_word μ s.1 = s.2) specs.

    (* The Known registers, with their values. *)
    Definition gen_init_regs (specs : list reg_spec) : list reg_init_spec :=
      base.omap (fun '(r, s) =>
        match s with Known v => Some (gpr_reg r, v) | _ => None end) specs.

    (* The Known words, with their values. *)
    Definition gen_init_mem (cs : list mem_cell) : list mem_init_spec :=
      base.omap (fun '(a, s) =>
        match s with Known v => Some (bv.of_N a, v) | _ => None end) cs.

    Definition RiscVStep (γ1 : RegStore) (μ1 : Memory) :
      forall (γ2 : RegStore) (μ2 : Memory), Prop :=
      fun γ2 μ2 => ⟨ γ1, μ1, [env], fun_step ⟩ --->* ⟨ γ2, μ2, [env], stm_val ty.unit tt ⟩.

    Definition RiscVStepN (γ1 : RegStore) (μ1 : Memory) :
      forall (γ2 : RegStore) (μ2 : Memory) n, Prop :=
      fun γ2 μ2 n => ⟨ γ1, μ1, [env], fun_step ⟩ -{ n }-> ⟨ γ2, μ2, [env], stm_val ty.unit tt ⟩.

    Inductive RiscVStepsWithExitCond (exitCond : Val ty_xlenbits -> Prop) (γ1 : RegStore) (μ1 : Memory) : RegStore -> Memory -> Prop :=
    | riscVStepWithExitCond_refl : RiscVStepsWithExitCond exitCond γ1 μ1 γ1 μ1
    | riscVStepWithExitCond_trans {γ2 γ3 : RegStore} {μ2 μ3 : Memory} :
      ~ exitCond (read_register γ1 pc) ->
      RiscVStep γ1 μ1 γ2 μ2 ->
      RiscVStepsWithExitCond exitCond  γ2 μ2 γ3 μ3 ->
      RiscVStepsWithExitCond exitCond  γ1 μ1 γ3 μ3.
    Notation "⟨ γ1 , μ1 ⟩ -( exitCond )->* ⟨ γ2 , μ2 ⟩" := (@RiscVStepsWithExitCond exitCond γ1 μ1 γ2 μ2)
                                                             (at level 75, only parsing, right associativity).

    Inductive RiscVNStepsWithExitCond  (exitCond : Val ty_xlenbits -> Prop) (γ1 : RegStore) (μ1 : Memory) : RegStore -> Memory -> nat -> Prop :=
    | riscVNStepWithExitCond_refl : RiscVNStepsWithExitCond exitCond γ1 μ1 γ1 μ1 0
    | riscVNStepWithExitCond_trans {n} {γ2 γ3 : RegStore} {μ2 μ3 : Memory} :
      ~ exitCond (read_register γ1 pc) ->
      RiscVStep γ1 μ1 γ2 μ2 ->
      RiscVNStepsWithExitCond exitCond  γ2 μ2 γ3 μ3 n ->
      RiscVNStepsWithExitCond exitCond  γ1 μ1 γ3 μ3 (S n)
    .
    Notation "⟨ γ1 , μ1 ⟩ -( exitCond , n )->* ⟨ γ2 , μ2 ⟩" := (@RiscVNStepsWithExitCond exitCond γ1 μ1 γ2 μ2 n)
                                                             (at level 75, only parsing, right associativity).

    Inductive RiscVlistNStepsWithExitCond  (exitCond : Val ty_xlenbits -> Prop) (γ1 : RegStore) (μ1 : Memory) : RegStore -> Memory -> list nat -> Prop :=
    | riscVlistNStepWithExitCond_refl : RiscVlistNStepsWithExitCond exitCond γ1 μ1 γ1 μ1 []
    | riscVlistNStepWithExitCond_trans {n} {l} {γ2 γ3 : RegStore} {μ2 μ3 : Memory} :
      ~ exitCond (read_register γ1 pc) ->
      RiscVStepN γ1 μ1 γ2 μ2 n ->
      RiscVlistNStepsWithExitCond exitCond  γ2 μ2 γ3 μ3 l ->
      RiscVlistNStepsWithExitCond exitCond  γ1 μ1 γ3 μ3 (n :: l)
    .
    Notation "⟨ γ1 , μ1 ⟩ -l( exitCond , n )->* ⟨ γ2 , μ2 ⟩" := (@RiscVlistNStepsWithExitCond exitCond γ1 μ1 γ2 μ2 n)
                                                                 (at level 75, only parsing, right associativity).

    Inductive RiscVNSteps (γ1 : RegStore) (μ1 : Memory) : RegStore -> Memory -> nat -> Prop :=
    | riscVNSteps_refl : RiscVNSteps γ1 μ1 γ1 μ1 0
    | riscVNSteps_trans {n} {γ2 γ3 : RegStore} {μ2 μ3 : Memory} :
      RiscVStep γ1 μ1 γ2 μ2 ->
      RiscVNSteps  γ2 μ2 γ3 μ3 n ->
      RiscVNSteps  γ1 μ1 γ3 μ3 (S n)
    .
    Notation "⟨ γ1 , μ1 ⟩ -( n )->* ⟨ γ2 , μ2 ⟩" := (@RiscVNSteps γ1 μ1 γ2 μ2 n)
                                                                  (at level 75, only parsing, right associativity).

    Inductive RiscVlistNSteps (γ1 : RegStore) (μ1 : Memory) : RegStore -> Memory -> list nat -> Prop :=
    | riscVlistNSteps_refl : RiscVlistNSteps γ1 μ1 γ1 μ1 []
    | riscVlistNSteps_trans {n} {l} {γ2 γ3 : RegStore} {μ2 μ3 : Memory} :
      RiscVStepN γ1 μ1 γ2 μ2 n ->
      RiscVlistNSteps  γ2 μ2 γ3 μ3 l ->
      RiscVlistNSteps  γ1 μ1 γ3 μ3 (n :: l)
    .
    Notation "⟨ γ1 , μ1 ⟩ -l( l )->* ⟨ γ2 , μ2 ⟩" := (@RiscVlistNSteps γ1 μ1 γ2 μ2 l)
                                                      (at level 75, only parsing, right associativity).

    Definition declare_public_registers γ1 γ2 (public_registers : list (Reg ty_xlenbits)) :=
      List.Forall (fun r => read_register γ1 r = read_register γ2 r) public_registers.

  (* noninterferent_strong: termination-sensitive non-interference.
     For EVERY n: if world 1 takes n steps without being at the exit before
     any of them, world 2 takes the same n steps, and both produce the same
     leakage trace.  This covers every prefix of a run, including prefixes of
     runs that never reach `exit_addr` -- stronger than "if world 1 reaches
     the exit".  The data layout must lie clear of the code (first conjunct,
     D19): an overlap makes the theorem unprovable, not vacuous. *)
  Definition noninterferent_strong
      (init_addr : N)
      (instrs : list AST)
      (exit_addr : N)
      (reg_specs : list reg_spec)
      (mem : mem_layout) : Prop :=
    clear_of_code init_addr instrs mem /\
    ∀ (γ1 γ2 : RegStore) (μ1 μ2 : Memory) ws,
      mem_has_instrs μ1 (bv.of_N init_addr) ws instrs →
      mem_has_instrs μ2 (bv.of_N init_addr) ws instrs →
      declare_public_registers γ1 γ2 (gen_public_regs reg_specs) →
      declare_public_memory μ1 μ2 (gen_public_addrs (cells mem)) →
      declare_init_registers γ1 (gen_init_regs reg_specs) →
      declare_init_registers γ2 (gen_init_regs reg_specs) →
      declare_init_memory μ1 (gen_init_mem (cells mem)) →
      declare_init_memory μ2 (gen_init_mem (cells mem)) →
      RiscvPmpProgram.read_register γ1 cur_privilege = Machine →
      RiscvPmpProgram.read_register γ2 cur_privilege = Machine →
      RiscvPmpProgram.read_register γ1 pc = bv.of_N init_addr →
      RiscvPmpProgram.read_register γ2 pc = bv.of_N init_addr →
      leakage_trace μ1 = leakage_trace μ2 →
      ∀ n (γ1' : RegStore) (μ1' : Memory),
        ⟨ γ1, μ1 ⟩ -(atPc exit_addr, n)->* ⟨ γ1', μ1' ⟩ →
        ∃ γ2' μ2',
          ⟨ γ2, μ2 ⟩ -(atPc exit_addr, n)->* ⟨ γ2', μ2' ⟩ ∧
          leakage_trace μ1' = leakage_trace μ2'.
