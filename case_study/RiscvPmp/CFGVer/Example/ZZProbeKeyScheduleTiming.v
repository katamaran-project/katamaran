(* TEMP Phase-1 probe: real (non-simulated) N-sweep of ValidCFGVerifierContract
   on key_schedule_loop2, with the peval_bvxor accumulator fold
   (theories/Symbolic/PartialEvaluation.v, PLAN-solver-fold.md) now wired
   into the real framework. Reuses KeyScheduleLoop.v's instruction list and
   mem spec, only varying the loop-count register spec (A4) and fuel.
   Throwaway; not in _CoqProject. *)
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

(* Table has one word per iteration at 56, 60, 64, ...; key_schedule_loop2's
   own mem_specs only covers 2 words (matching its fixed N=2), so sweeping
   the trip count needs a matching N-sized table here. *)
Definition ksl_mem_specs (n : nat) : list mem_full_spec :=
  map (fun i => (bv.of_N (56 + 4 * N.of_nat i)%N, false, None)) (seq 0 n).

Definition ksl_contract (n : nat) (fuel : nat) : CFGVerifierContract :=
  gen_contract init_addr (ksl_reg_specs n) (ksl_mem_specs n)
    key_schedule_loop2_instrs [] key_schedule_loop2_exitCond fuel.

(* fuel = 14*n + 30 slack, mirroring key_schedule_loop2's own 40 = 14*2 + 12 margin *)

(* Real (coqc, isolated single-lemma files) timings, fold ON + mem-spec fix
   (2026-07-20). All well short of the pre-fold 3^N wall (e.g. 3^4/3^2 = 9x
   alone dwarfs what's seen from N2->N4 here), but still clearly superlinear
   -- roughly quadratic-to-cubic, not linear -- so pushing to N=32/64 is a
   real time investment, not a quick check; see PLAN-solver-fold.md / memory
   project_key_schedule_loop_scaling.md before re-running blind.
     N=2:  vm_compute  9.8s, solve_vc  2.4s, Qed   2.5s  (total ~14.8s)
     N=3:  vm_compute 14.3s, solve_vc  5.1s, Qed   7.1s  (total ~26.5s)
     N=4:  vm_compute 21.5s, solve_vc  8.5s, Qed  14.0s  (total ~43.9s)
     N=8:  vm_compute  104s, solve_vc 35.8s, Qed 142.4s  (total ~282s)
   N4->N8 (2x N) is a ~6.4x time jump -- extrapolating that curve puts N=16
   in the ~20-30 min range and N=32/64 likely into the hour(s) range; NOT
   run yet as of this note. *)
Lemma valid_ksl_N2 : ValidCFGVerifierContract (ksl_contract 2 58).
Proof. vm_compute. solve_vc. Qed.

Lemma valid_ksl_N3 : ValidCFGVerifierContract (ksl_contract 3 72).
Proof. vm_compute. solve_vc. Qed.

Lemma valid_ksl_N4 : ValidCFGVerifierContract (ksl_contract 4 86).
Proof. vm_compute. solve_vc. Qed.

Lemma valid_ksl_N8 : ValidCFGVerifierContract (ksl_contract 8 142).
Proof. vm_compute. solve_vc. Qed.

(* Not yet run for real (see cost note above) -- kept as the intended next
   steps once the growth-rate question is settled. *)
Lemma valid_ksl_N16 : ValidCFGVerifierContract (ksl_contract 16 254).
Proof. vm_compute. solve_vc. Qed.

Lemma valid_ksl_N32 : ValidCFGVerifierContract (ksl_contract 32 478).
Proof. vm_compute. solve_vc. Qed.

Lemma valid_ksl_N64 : ValidCFGVerifierContract (ksl_contract 64 926).
Proof. vm_compute. solve_vc. Qed.
