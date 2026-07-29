(* ========================================================================= *)
(* ZZProbeStages.v — THROWAWAY diagnostic probe (delete after use).          *)
(*                                                                           *)
(* Step 2 of the scaling diagnosis: decompose the cost of                    *)
(*   ValidCFGVerifierContract = safeE (postprocess (CFG_VC_triple ...))      *)
(* into its pipeline stages, to find out whether the time is spent           *)
(*   (A) building the raw SymProp (executor + combined_solver interleaved),  *)
(*   (B) in postprocess's five walks (prune/solve_evars/prune/solve_uvars/   *)
(*       prune), or                                                          *)
(*   (C) in erase_symprop + safeE.                                          *)
(*                                                                           *)
(* Each stage is forced with a CHEAP consumer (SymProp.Statistics.size,      *)
(* returning N) instead of being printed -- printing a ~100 MB term is what  *)
(* made the historical "raw VC times out >90 s at N=2" figure meaningless.   *)
(* vm_compute is call-by-value, so `size (stage X)` fully builds X.          *)
(*                                                                           *)
(* Measurements are CUMULATIVE (stage k re-does stages 1..k-1); the per-     *)
(* stage cost is the DELTA between consecutive timings.  size also doubles   *)
(* as a node-count metric: if raw >> postprocess, work is being built and    *)
(* then discarded.                                                           *)
(*                                                                           *)
(* Subject: the flat reproducer -- key_schedule_loop2's shape byte-for-byte  *)
(* (14 instrs/trip, same STORE/addi/addi/BNE tail, same specs, ia=0) with    *)
(* the 10-instruction masking chain replaced by `addi a0, a1, 1` x10.  A0 is *)
(* written from A1 and A1 is never written, so EVERY symbolic term stays     *)
(* O(1) forever: term growth is eliminated by construction.                  *)
(* ========================================================================= *)

From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.

(* -52 in 13-bit two's complement: back-branch from the BNE at offset 52 to
   offset 0.  Same as key_schedule_loop2 (also 14 instructions). *)
Definition zz_back_offset : bv 13 := bv.of_N 8140.

(* 10x `addi a0, a1, 1` (ITYPE imm rs rd op), then key_schedule_loop2's tail
   verbatim: table store, pointer bump, counter decrement, back-branch. *)
Definition zz_instrs : list AST :=
  [ ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ; ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ; ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ; ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ; ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ; ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ; ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ; ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ; ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ; ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ; STORE (bv.of_Z 0) A0 A3 WORD             (* sw   a0, 0(a3) *)
  ; ITYPE (bv.of_Z 4) A3 A3 RISCV_ADDI       (* addi a3, a3, 4 *)
  ; ITYPE (bv.of_Z (-1)) A4 A4 RISCV_ADDI    (* addi a4, a4, -1 *)
  ; BNE A4 X0 zz_back_offset                 (* bne  a4, x0, back *)
  ].

(* Everything that must scale WITH the trip count, in one place: counter,
   fuel, one table word per trip, and the access bound. *)
Definition zz_reg_specs (n : nat) : list reg_spec_rel :=
  [(A0, false, PVExist); (A1, false, PVExist); (A2, false, PVExist);
   (A3, false, PVBaseOff 56);
   (A4, true, PVConst (bv.of_N (N.of_nat n)))].

Definition zz_mem_specs (n : nat) : list mem_spec_rel :=
  List.map (fun k => ((56 + 4 * N.of_nat k)%N, false, PVExist)) (List.seq 0 n).

Definition zz_contract (n : nat) : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_rel 0 (zz_reg_specs n) (zz_mem_specs n)
    zz_instrs [] (56 + 4 * N.of_nat n)%N
    (pcOutOfInstrs_exitCond 0 zz_instrs) (14 * n + 12).

(* ---------------------------------------------------------------------- *)
(* The six pipeline stages, each consumed by `size`.                       *)
(* postprocess = prune (solve_uvars (prune (solve_evars (prune P))))       *)
(* ---------------------------------------------------------------------- *)

Definition zz_raw (n : nat) : N :=
  cfg_map (zz_contract n) (fun ia p exits P i ec fl =>
    SymProp.Statistics.size (CFG_VC_triple p exits P i fl)).

Definition zz_p1 (n : nat) : N :=
  cfg_map (zz_contract n) (fun ia p exits P i ec fl =>
    SymProp.Statistics.size (Postprocessing.prune (CFG_VC_triple p exits P i fl))).

Definition zz_ev (n : nat) : N :=
  cfg_map (zz_contract n) (fun ia p exits P i ec fl =>
    SymProp.Statistics.size
      (Postprocessing.solve_evars
         (Postprocessing.prune (CFG_VC_triple p exits P i fl)))).

Definition zz_p2 (n : nat) : N :=
  cfg_map (zz_contract n) (fun ia p exits P i ec fl =>
    SymProp.Statistics.size
      (Postprocessing.prune
         (Postprocessing.solve_evars
            (Postprocessing.prune (CFG_VC_triple p exits P i fl))))).

Definition zz_uv (n : nat) : N :=
  cfg_map (zz_contract n) (fun ia p exits P i ec fl =>
    SymProp.Statistics.size
      (Postprocessing.solve_uvars
         (Postprocessing.prune
            (Postprocessing.solve_evars
               (Postprocessing.prune (CFG_VC_triple p exits P i fl)))))).

Definition zz_pp (n : nat) : N :=
  cfg_map (zz_contract n) (fun ia p exits P i ec fl =>
    SymProp.Statistics.size (postprocess (CFG_VC_triple p exits P i fl))).

(* ---------------------------------------------------------------------- *)
(* MEASURED N=2 (first run): raw 2801 nodes / 3.40 s, prune 1294 / 3.67,   *)
(* solve_evars 618 / 3.76, prune 551 / 3.71, solve_uvars 99 / 3.59,        *)
(* postprocess 99 / 3.32, full ValidCFGVerifierContract 3.44.  Cumulative  *)
(* time is FLAT (spread is noise, the last is faster than the first), so    *)
(* ~100% of the cost is raw construction: postprocess + erase + safeE are  *)
(* free.  2801 nodes built, 99 survive -> 96.5% discarded, and discarding  *)
(* is free, so the cost was all in BUILDING them.                          *)
(*                                                                         *)
(* Hence the N-sweep below only needs zz_raw, plus one zz_pp at the top N   *)
(* to confirm postprocess stays free at scale.                             *)
(* ---------------------------------------------------------------------- *)

Goal True. idtac "ZZ === raw construction sweep (size / time) ===". exact I. Qed.

Time Eval vm_compute in (zz_raw 1).
Time Eval vm_compute in (zz_raw 2).
Time Eval vm_compute in (zz_raw 3).
Time Eval vm_compute in (zz_raw 4).
Time Eval vm_compute in (zz_raw 6).

Goal True. idtac "ZZ === postprocess still free at N=6? ===". exact I. Qed.

Time Eval vm_compute in (zz_pp 6).

Goal True. idtac "ZZ === surviving node count at each N ===". exact I. Qed.

Time Eval vm_compute in (zz_pp 1).
Time Eval vm_compute in (zz_pp 2).
Time Eval vm_compute in (zz_pp 3).
Time Eval vm_compute in (zz_pp 4).
