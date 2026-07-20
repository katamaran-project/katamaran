(* TEMP: isolated N=8 check, split out of ZZProbeKeyScheduleTiming.v to avoid
   pet's OOM ceiling and cross-lemma interference while re-measuring timing
   after the select_last_k fold redesign (PLAN-solver-fold.md). Throwaway;
   not in _CoqProject. *)
From Coq Require Import
     ZArith.ZArith Lists.List micromega.Lia Strings.String.
From Katamaran Require Import
     Notations Bitvector Semantics
     RiscvPmp.CFGVer.Spec RiscvPmp.Machine RiscvPmp.Sig.
From stdpp Require Import gmap.
From Katamaran Require Import
     RiscvPmp.CFGVer.Verifier RiscvPmp.CFGVer.Noninterference
     RiscvPmp.CFGVer.Tables RiscvPmp.CFGVer.Contracts
     RiscvPmp.CFGVer.GenContract
     RiscvPmp.CFGVer.Example.KeyScheduleLoop.

Import RiscvPmpProgram.
Set Implicit Arguments.
Import ctx.resolution ctx.notations bv.notations env.notations ListNotations.
Import RiscvPmpCFGVerifExecutor Assembly.
Import RiscvPmp.Sig.
Import TermNotations.

Definition ksl_reg_specs (n : nat) : list reg_spec :=
  [(A0, false, None); (A1, false, None); (A2, false, None);
   (A3, false, Some (bv.of_N 56));
   (A4, true, Some (bv.of_N (N.of_nat n)))].

Definition ksl_mem_specs (n : nat) : list mem_full_spec :=
  map (fun i => (bv.of_N (56 + 4 * N.of_nat i)%N, false, None)) (seq 0 n).

Definition ksl_contract (n : nat) (fuel : nat) : CFGVerifierContract :=
  gen_contract init_addr (ksl_reg_specs n) (ksl_mem_specs n)
    key_schedule_loop2_instrs [] key_schedule_loop2_exitCond fuel.

Lemma valid_ksl_N8 : ValidCFGVerifierContract (ksl_contract 8 142).
Proof. vm_compute. solve_vc. Qed.
