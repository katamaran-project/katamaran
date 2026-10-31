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
(* STATEMENTS lives here: the machine-level step relations, the spec types,  *)
(* what a spec says about two runs (val_sat / regs_sat / mem_sat), and       *)
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
   spec types, the sat-predicates and noninterferent_strong, all expressible with the
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

    (* The two runs SATISFY a spec: what a spec says about the value x1 in
       run 1 and x2 in run 2.  Not "they agree": only Public makes them equal;
       Secret lets them differ, Known initialises each run (so is public too). *)
    Definition val_sat {V} (x1 x2 : V) (s : val_spec V) : Prop :=
      match s with
      | Secret  => True              (* unconstrained *)
      | Public  => x1 = x2           (* equal in both runs *)
      | Known v => x1 = v /\ x2 = v  (* initialised in each run *)
      end.

(* ---- Register keys: the 31 general-purpose registers (D15) ----------------
   x0 is hardwired to zero, and pc / cur_privilege / mtvec / pmp* are not
   general-purpose, so none of them can be written as a key. *)
    Definition gpr_list : list (Reg ty_xlenbits) :=
      [x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15; x16;
       x17; x18; x19; x20; x21; x22; x23; x24; x25; x26; x27; x28; x29; x30; x31].

    (* Decidable equality of xlen-wide registers.  The machine only provides
       it on the sigma type ({ τ & Reg τ }); this unpacks it.  Any instance
       gives the same is_gpr: bool_decide P = true <-> P. *)
    #[export] Instance reg_xlen_eq_dec : EqDecision (Reg ty_xlenbits) :=
      fun r1 r2 =>
        match Classes.eq_dec (existT ty_xlenbits r1) (existT ty_xlenbits r2) with
        | left e  => left (Eqdep_dec.inj_pair2_eq_dec _ Classes.eq_dec _ _ _ _ e)
        | right n => right (fun e => n (f_equal _ e))
        end.

    Definition is_gpr (r : Reg ty_xlenbits) : bool :=
      bool_decide (r ∈ gpr_list).

    Definition gpr : Type := { r : Reg ty_xlenbits | is_gpr r = true }.

    Definition gpr_reg (g : gpr) : Reg ty_xlenbits := proj1_sig g.

    (* A register entry of a statement. *)
    Definition reg_spec : Type := gpr * val_spec (Val ty_xlenbits).

    (* The two register stores satisfy every entry. *)
    Definition regs_sat (γ1 γ2 : RegStore) (specs : list reg_spec) : Prop :=
      Forall (fun e => val_sat (read_register γ1 (gpr_reg e.1))
                                 (read_register γ2 (gpr_reg e.1)) e.2) specs.

    (* THE STOP TEST (PLAN-exit-targets.md, 2026-09-25): a run stops exactly
       when the pc IS the program's single exit address.  It replaced
       `pcOutOfInstrs_exitCond init_addr instrs` (pc >= init_addr + 4|instrs|),
       so a run that leaves the code anywhere else is no longer a stopping run.
       Boolean, like the old condition, because the stepping relations below
       test `~ exitCond pc` through the Is_true coercion. *)
    Definition atPc (exit_addr : N) : bv xlenbits -> bool :=
      fun v => bv.eqb v (bv.of_N exit_addr).

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
   overlap test cannot wrap around; the blocks stay below lenAddr, and clear
   of the code, by two conjuncts of noninterferent_strong (in_range, D19's
   clear_of_code), not by the type. *)
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

    (* Every block lies entirely below or entirely above the code. *)
    Definition clear_of_code (init_addr : N) (instrs : list AST) (m : mem_layout) : Prop :=
      Forall (fun b => blk_end b <= init_addr \/
                       init_addr + 4 * N.of_nat (length instrs) <= blk_addr b)%N
        (blocks m).

    (* The code and every block end below lenAddr (< 2^32), so no address
       below wraps around when read as a machine word: blocks disjoint in N
       are disjoint in memory. *)
    Definition in_range (init_addr : N) (instrs : list AST) (m : mem_layout) : Prop :=
      (init_addr + 4 * N.of_nat (length instrs) < lenAddr)%N /\
      Forall (fun b => blk_end b < lenAddr)%N (blocks m).

    (* The two memories satisfy every word of a block, starting at address a
       (a machine word); then of every block of a layout. *)
    Fixpoint words_sat (μ1 μ2 : Memory) (a : Addr)
        (ws : list (val_spec (Val ty_word))) : Prop :=
      match ws with
      | nil       => True
      | cons w ws => val_sat (get_word μ1 a) (get_word μ2 a) w /\
                     words_sat μ1 μ2 (bv.add a (bv.of_N 4)) ws
      end.

    Definition mem_sat (μ1 μ2 : Memory) (m : mem_layout) : Prop :=
      Forall (fun b => words_sat μ1 μ2 (bv.of_N (blk_addr b)) (blk_words b))
        (blocks m).

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

  (* noninterferent_strong: termination-sensitive non-interference.
     For EVERY n: if world 1 takes n steps without being at the exit before
     any of them, world 2 takes the same n steps, and both produce the same
     leakage trace.  This covers every prefix of a run, including prefixes of
     runs that never reach `exit_addr` -- stronger than "if world 1 reaches
     the exit".  The data layout must lie clear of the code (D19) and, with
     the code, below lenAddr (in_range): the first two conjuncts, so an
     overlap or a wrap-around makes the theorem unprovable, not vacuous. *)
  Definition noninterferent_strong
      (init_addr : N)
      (instrs : list AST)
      (exit_addr : N)
      (reg_specs : list reg_spec)
      (mem : mem_layout) : Prop :=
    clear_of_code init_addr instrs mem /\
    in_range init_addr instrs mem /\
    ∀ (γ1 γ2 : RegStore) (μ1 μ2 : Memory) ws,
      mem_has_instrs μ1 (bv.of_N init_addr) ws instrs →
      mem_has_instrs μ2 (bv.of_N init_addr) ws instrs →
      regs_sat γ1 γ2 reg_specs →
      mem_sat μ1 μ2 mem →
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
