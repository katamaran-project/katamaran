(* ========================================================================= *)
(* SpecLists.v — the LIST forms of a statement's specs (proof side).         *)
(*                                                                           *)
(* The kernel (Noninterference.v) states what a spec says about two runs     *)
(* directly: regs_sat / mem_sat.  The generators and bridges work on     *)
(* flat lists instead -- memory as one (address, spec) cell per word, and    *)
(* the Public / Known entries filtered out into declare_* premises.  Those   *)
(* lists live here, with the two lemmas that take the kernel's predicates    *)
(* to them (regs_sat_declare, mem_sat_declare).  NOT on the statement    *)
(* surface: no end theorem mentions anything in this file.                   *)
(* Requires only the kernel; keep it free of the verifier and of Iris.       *)
(* ========================================================================= *)

From Coq Require Import
     ZArith.ZArith
     Lists.List
     micromega.Lia.
From Katamaran Require Import
     Notations
     Bitvector
     Semantics
     RiscvPmp.Machine
     RiscvPmp.CFGVer.Noninterference.
From stdpp Require Import base list.

Import RiscvPmpProgram.
Import ListNotations.

Set Implicit Arguments.

(* ---- Registers ----------------------------------------------------------- *)

(* The two worlds agree on every listed register. *)
Definition declare_public_registers γ1 γ2 (public_registers : list (Reg ty_xlenbits)) :=
  List.Forall (fun r => read_register γ1 r = read_register γ2 r) public_registers.

(* Registers both runs must agree on: the Public entries. *)
Definition gen_public_regs (specs : list reg_spec) : list (Reg ty_xlenbits) :=
  base.omap (fun '(r, s) =>
    match s with Public => Some (gpr_reg r) | _ => None end) specs.

(* reg_init_spec: a register with its required initial value in both worlds *)
Definition reg_init_spec : Type := 𝑹𝑬𝑮 ty_xlenbits * Val ty_xlenbits.

(* Each register r in specs holds value v in γ *)
Definition declare_init_registers (γ : RegStore)
    (specs : list reg_init_spec) : Prop :=
  List.Forall (fun s => read_register γ s.1 = s.2) specs.

(* The Known registers, with their values. *)
Definition gen_init_regs (specs : list reg_spec) : list reg_init_spec :=
  base.omap (fun '(r, s) =>
    match s with Known v => Some (gpr_reg r, v) | _ => None end) specs.

(* ---- Memory: one cell per word --------------------------------------------- *)

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

(* declare_public_memory: the two worlds agree on the word value at
   every address listed as public *)
Definition declare_public_memory (μ1 μ2 : Memory)
    (public_addrs : list (Val ty_word)) : Prop :=
  List.Forall (fun a => get_word μ1 a = get_word μ2 a) public_addrs.

(* Words both runs must agree on: the Public cells. *)
Definition gen_public_addrs (cs : list mem_cell) : list (Val ty_word) :=
  base.omap (fun '(a, s) =>
    match s with Public => Some (bv.of_N a) | _ => None end) cs.

(* mem_init_spec: a word address with its required initial value in both worlds *)
Definition mem_init_spec : Type := Val ty_word * Val ty_word.

(* Each address a in specs holds word value v in μ *)
Definition declare_init_memory (μ : Memory)
    (specs : list mem_init_spec) : Prop :=
  List.Forall (fun s => get_word μ s.1 = s.2) specs.

(* The Known words, with their values. *)
Definition gen_init_mem (cs : list mem_cell) : list mem_init_spec :=
  base.omap (fun '(a, s) =>
    match s with Known v => Some (bv.of_N a, v) | _ => None end) cs.

(* ---- From the kernel's predicates to the lists ----------------------------- *)

Lemma regs_sat_declare γ1 γ2 (specs : list reg_spec) :
  regs_sat γ1 γ2 specs ->
  declare_public_registers γ1 γ2 (gen_public_regs specs) /\
  declare_init_registers γ1 (gen_init_regs specs) /\
  declare_init_registers γ2 (gen_init_regs specs).
Proof.
  unfold regs_sat, declare_public_registers, declare_init_registers,
    gen_public_regs, gen_init_regs.
  induction specs as [|[r [| | v]] specs IH]; intros H; cbn.
  - repeat split; constructor.
  - inversion H as [|? ? _ H']. exact (IH H').
  - inversion H as [|? ? Hx H']. destruct (IH H') as (? & ? & ?).
    repeat split; try constructor; assumption.
  - inversion H as [|? ? Hx H']; cbn in Hx; destruct Hx as [Hx1 Hx2].
    destruct (IH H') as (? & ? & ?).
    repeat split; try constructor; assumption.
Qed.

(* The kernel's word-by-word reading, as a cell list. *)
Definition cells_sat (μ1 μ2 : Memory) (cs : list mem_cell) : Prop :=
  Forall (fun c => val_sat (get_word μ1 (bv.of_N c.1)) (get_word μ2 (bv.of_N c.1)) c.2) cs.

Lemma words_sat_cells μ1 μ2 (a : N) ws :
  words_sat μ1 μ2 (bv.of_N a) ws -> cells_sat μ1 μ2 (words_at a ws).
Proof.
  revert a. induction ws as [|w ws IH]; intros a H; cbn in *; [constructor|].
  destruct H as [Hw H]. constructor; [exact Hw|].
  apply IH. rewrite bv.of_N_add in H. exact H.
Qed.

Lemma mem_sat_cells μ1 μ2 (m : mem_layout) :
  mem_sat μ1 μ2 m -> cells_sat μ1 μ2 (cells m).
Proof.
  unfold mem_sat, cells, cells_sat.
  induction (blocks m) as [|b bs IH]; intros H; cbn; [constructor|].
  inversion H as [|? ? Hb H']. apply Forall_app; split.
  - apply words_sat_cells. exact Hb.
  - exact (IH H').
Qed.

Lemma cells_sat_declare μ1 μ2 (cs : list mem_cell) :
  cells_sat μ1 μ2 cs ->
  declare_public_memory μ1 μ2 (gen_public_addrs cs) /\
  declare_init_memory μ1 (gen_init_mem cs) /\
  declare_init_memory μ2 (gen_init_mem cs).
Proof.
  unfold cells_sat, declare_public_memory, declare_init_memory,
    gen_public_addrs, gen_init_mem.
  induction cs as [|[a [| | v]] cs IH]; intros H; cbn.
  - repeat split; constructor.
  - inversion H as [|? ? _ H']. exact (IH H').
  - inversion H as [|? ? Hx H']. destruct (IH H') as (? & ? & ?).
    repeat split; try constructor; assumption.
  - inversion H as [|? ? Hx H']; cbn in Hx; destruct Hx as [Hx1 Hx2].
    destruct (IH H') as (? & ? & ?).
    repeat split; try constructor; assumption.
Qed.

Lemma mem_sat_declare μ1 μ2 (m : mem_layout) :
  mem_sat μ1 μ2 m ->
  declare_public_memory μ1 μ2 (gen_public_addrs (cells m)) /\
  declare_init_memory μ1 (gen_init_mem (cells m)) /\
  declare_init_memory μ2 (gen_init_mem (cells m)).
Proof. intros H. exact (cells_sat_declare (mem_sat_cells H)). Qed.
