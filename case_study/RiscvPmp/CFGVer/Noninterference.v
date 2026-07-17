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
From Katamaran Require Import
     Notations
     Bitvector
     Semantics
     RiscvPmp.CFGVer.Spec
     RiscvPmp.Machine
     RiscvPmp.Sig.
From stdpp Require Import gmap.

Import RiscvPmpProgram.
Import RiscvPmpCFGVerifExecutor.
Import Assembly.
Import RiscvPmp.Sig.

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

(* reg_spec: (register, is_public, optional_init_value) — the register-side
   spec vocabulary shared by the statements below and the contract generator
   (GenContract.v).  mem_full_spec is the memory-side analog. *)
    Definition reg_spec : Type := RegIdx * bool * option (Val ty_xlenbits).

    Definition mem_full_spec : Type :=
      Val ty_xlenbits * bool * option (Val ty_xlenbits).

    Definition pcOutOfInstrs_exitCond (init_addr : N) (instrs : list AST) : bv xlenbits -> bool :=
      fun v => bv.ugeb v (bv.of_N (init_addr + 4 * N.of_nat (length instrs))).

    (* The fall-through address (first address past the program) satisfies
       pcOutOfInstrs_exitCond — the fact etable_faith_exits_of_list needs
       to discharge the default exit table against this exit condition. *)
    Lemma pcOutOfInstrs_fallthrough (ia : N) (instrs : list AST) :
      pcOutOfInstrs_exitCond ia instrs
        (bv.add (bv.of_N ia) (bv.of_N (4 * N.of_nat (length instrs)))) = true.
    Proof.
      unfold pcOutOfInstrs_exitCond.
      rewrite bv.of_N_add.
      cbn [bv.ugeb]. apply bv.uleb_ule, bv.ule_refl.
    Qed.

  (* Public registers for a spec list: registers whose is_pub flag is true.
     Defined outside WithAsnNotations to avoid notation-scope interference. *)
  Definition gen_public_regs (specs : list reg_spec) : list {x : Ty & 𝑹𝑬𝑮 x} :=
    base.omap (fun (spec : reg_spec) =>
      let '(r, pub, _) := spec in
      if pub then option_map (@existT Ty 𝑹𝑬𝑮 ty_xlenbits) (reg_convert r)
      else None) specs.

  Definition reg_spec_idx (s : reg_spec) : RegIdx :=
    let '(r, _, _) := s in r.

    Definition mem_has_word (μ : Memory) (a : Val ty_word) (w : Val ty_word) : Prop :=
      exists v0 v1 v2 v3, List.map (memory_ram μ) (bv.seqBv a 4) = [v0; v1; v2; v3]%list /\ bv.app v0 (bv.app v1 (bv.app v2 (bv.app v3 bv.nil))) = w.

    (* byte order correct? *)
    Definition mem_has_instr (μ : Memory) (a : Val ty_word) w (instr : AST) : Prop :=
      mem_has_word μ a w /\ pure_decode w = inr instr.

    Fixpoint mem_has_instrs (μ : Memory) (a : Val ty_word) ws (instrs : list AST) : Prop :=
      match ws , instrs with
      | cons w ws , cons inst instrs => mem_has_instr μ a w inst /\ mem_has_instrs μ (bv.add (bv.of_N 4) a) ws instrs
      | nil , nil => True
      | _ , _ => False
      end.

    (* Word extraction: assemble 4 consecutive bytes into a 32-bit word *)
    Definition get_word (μ : Memory) (a : Val ty_word) : Val ty_word :=
      bv.app (memory_ram μ a)
        (bv.app (memory_ram μ (bv.add bv.one a))
          (bv.app (memory_ram μ (bv.add (bv.of_N 2) a))
            (bv.app (memory_ram μ (bv.add (bv.of_N 3) a)) bv.nil))).

    (* mem_spec: a word address paired with a public/private flag *)
    Definition mem_spec : Type := Val ty_word * bool.

    (* declare_public_memory: the two worlds agree on the word value at
       every address listed as public *)
    Definition declare_public_memory (μ1 μ2 : Memory)
        (public_addrs : list (Val ty_word)) : Prop :=
      List.Forall (fun a => get_word μ1 a = get_word μ2 a) public_addrs.

    (* gen_public_addrs: filter a mem_spec list to keep only public addresses *)
    Definition gen_public_addrs (specs : list mem_spec) : list (Val ty_word) :=
      base.omap (fun s : mem_spec => let '(a, pub) := s in
        if pub then Some a else None) specs.

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

    Definition gen_init_regs (specs : list reg_spec) : list reg_init_spec :=
      base.omap (fun '(r, _, opt_v) =>
        match opt_v with
        | Some v => option_map (fun x => (x, v)) (reg_convert r)
        | None => None
        end) specs.

    Definition mem_full_to_spec (s : mem_full_spec) : mem_spec :=
      let '(a, pub, _) := s in (a, pub).

    Definition gen_full_public_addrs (specs : list mem_full_spec) :
        list (Val ty_word) :=
      gen_public_addrs (map mem_full_to_spec specs).

    Definition gen_init_mem (specs : list mem_full_spec) : list mem_init_spec :=
      base.omap (fun '(a, _, opt_v) =>
        match opt_v with
        | Some v => Some (a, v)
        | None => None
        end) specs.

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

    Definition declare_public_registers γ1 γ2 (public_registers : list {x : Ty & Reg x}) :=
      List.Forall
        (fun x => match x with
                  |existT x0 r => read_register γ1 r = read_register γ2 r
                  end)
        public_registers
    .

  (* noninterferent_strong: termination-sensitive non-interference.
     If world 1 terminates in n steps under exitCond, so does world 2 in
     exactly n steps, and both worlds produce the same leakage trace. *)
  Definition noninterferent_strong
      (init_addr : N)
      (instrs : list AST)
      (exitCond : bv xlenbits -> bool)
      (reg_specs : list reg_spec)
      (mem_specs : list mem_full_spec) : Prop :=
    ∀ (γ1 γ2 : RegStore) (μ1 μ2 : Memory) ws,
      mem_has_instrs μ1 (bv.of_N init_addr) ws instrs →
      mem_has_instrs μ2 (bv.of_N init_addr) ws instrs →
      declare_public_registers γ1 γ2 (gen_public_regs reg_specs) →
      declare_public_memory μ1 μ2 (gen_full_public_addrs mem_specs) →
      declare_init_registers γ1 (gen_init_regs reg_specs) →
      declare_init_registers γ2 (gen_init_regs reg_specs) →
      declare_init_memory μ1 (gen_init_mem mem_specs) →
      declare_init_memory μ2 (gen_init_mem mem_specs) →
      RiscvPmpProgram.read_register γ1 cur_privilege = Machine →
      RiscvPmpProgram.read_register γ2 cur_privilege = Machine →
      RiscvPmpProgram.read_register γ1 pc = bv.of_N init_addr →
      RiscvPmpProgram.read_register γ2 pc = bv.of_N init_addr →
      leakage_trace μ1 = leakage_trace μ2 →
      ∀ n (γ1' : RegStore) (μ1' : Memory),
        ⟨ γ1, μ1 ⟩ -(exitCond, n)->* ⟨ γ1', μ1' ⟩ →
        ∃ γ2' μ2',
          ⟨ γ2, μ2 ⟩ -(exitCond, n)->* ⟨ γ2', μ2' ⟩ ∧
          leakage_trace μ1' = leakage_trace μ2'.
