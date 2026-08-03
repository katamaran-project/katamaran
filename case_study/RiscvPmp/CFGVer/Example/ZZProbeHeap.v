(* ========================================================================= *)
(* ZZProbeHeap.v — THROWAWAY diagnostic probe (delete after use).            *)
(*                                                                           *)
(* Step 2b: ZZProbeStages.v established that ~100% of the VC cost is RAW     *)
(* construction (postprocess/erase/safeE are free), that raw node count is   *)
(* EXACTLY linear in the trip count (+1389/trip), yet time is ~N^2.6.  So    *)
(* the per-node cost itself grows ~N^1.5.  Something whose size grows with   *)
(* step count is being re-walked at every emission.                          *)
(*                                                                           *)
(* Three candidates all grow linearly with N in that reproducer:             *)
(*   (1) wco   — one `assume secLeak encoded_instr` per fetch, re-walked by  *)
(*               all 8 combined_solver passes (assumption_formula has no     *)
(*               early exit and no memoisation),                             *)
(*   (2) heap  — one table word per trip => consume_chunk's linear scan and  *)
(*               every heap persist get costlier per step,                   *)
(*   (3) wctx  — one fresh logic var per fetch; term persistence into a      *)
(*               deeper world.                                              *)
(*                                                                           *)
(* This file separates (2) from (1)+(3) WITHOUT touching the framework:      *)
(*   variant G (growing heap):  addi a3,a3,4 ; N table words ; bound 56+4N   *)
(*   variant C (constant heap): addi a3,a3,0 ; 1 table word  ; bound 60      *)
(* Identical instruction COUNT and shape, identical fetch/branch structure,  *)
(* so wco and wctx grow the same in both.  Only the heap differs.            *)
(*                                                                           *)
(* Both variants are measured in ONE file so they share cache state (see     *)
(* rocq-timeout-triage Step 1b: cross-run wall times on this box are not     *)
(* comparable).                                                              *)
(*                                                                           *)
(* Reading the result:                                                       *)
(*   C flattens to ~linear      => the heap was the driver (candidate 2).    *)
(*   C still ~N^2.6 like G      => heap is innocent; it is wco and/or wctx,  *)
(*                                 which needs the framework-level ablation  *)
(*                                 A1 (pass ctx.nil as assumption_formula's  *)
(*                                 fact list) to separate.                   *)
(* ========================================================================= *)

From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.

Definition zzh_back_offset : bv 13 := bv.of_N 8140.

(* 10x `addi a0, a1, 1` (A0 written from A1, never from itself => every
   symbolic term stays O(1) forever), then the tail.  `bump` is the only
   difference between the two variants: 4 advances the table pointer,
   0 is a nop that pins every store to the same address. *)
Definition zzh_instrs (bump : Z) : list AST :=
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
  ; ITYPE (bv.of_Z bump) A3 A3 RISCV_ADDI    (* addi a3, a3, bump *)
  ; ITYPE (bv.of_Z (-1)) A4 A4 RISCV_ADDI    (* addi a4, a4, -1 *)
  ; BNE A4 X0 zzh_back_offset                (* bne  a4, x0, back *)
  ].

Definition zzh_reg_specs (n : nat) : list reg_spec_rel :=
  [(A0, false, PVExist); (A1, false, PVExist); (A2, false, PVExist);
   (A3, false, PVBaseOff 56);
   (A4, true, PVConst (bv.of_N (N.of_nat n)))].

(* ---- variant G: heap grows, one table word per trip -------------------- *)

Definition zzhG_mem_specs (n : nat) : list mem_spec_rel :=
  List.map (fun k => ((56 + 4 * N.of_nat k)%N, false, PVExist)) (List.seq 0 n).

Definition zzhG_contract (n : nat) : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_rel 0 (zzh_reg_specs n) (zzhG_mem_specs n)
    (zzh_instrs 4) [] (56 + 4 * N.of_nat n)%N
    (pcOutOfInstrs_exitCond 0 (zzh_instrs 4)) (14 * n + 12).

(* ---- variant C: heap constant, every store hits address p+56 ----------- *)

Definition zzhC_mem_specs : list mem_spec_rel :=
  [(56%N, false, PVExist)].

Definition zzhC_contract (n : nat) : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_rel 0 (zzh_reg_specs n) zzhC_mem_specs
    (zzh_instrs 0) [] 60%N
    (pcOutOfInstrs_exitCond 0 (zzh_instrs 0)) (14 * n + 12).

(* Raw construction only: ZZProbeStages.v showed postprocess/erase/safeE are
   free, so this is the whole cost. *)
Definition zzhG_raw (n : nat) : N :=
  cfg_map (zzhG_contract n) (fun ia p exits P i ec fl =>
    SymProp.Statistics.size (CFG_VC_triple p exits P i fl)).

Definition zzhC_raw (n : nat) : N :=
  cfg_map (zzhC_contract n) (fun ia p exits P i ec fl =>
    SymProp.Statistics.size (CFG_VC_triple p exits P i fl)).

Goal True. idtac "ZZ === G: growing heap (baseline) ===". exact I. Qed.

Time Eval vm_compute in (zzhG_raw 1).
Time Eval vm_compute in (zzhG_raw 2).
Time Eval vm_compute in (zzhG_raw 4).
Time Eval vm_compute in (zzhG_raw 6).

Goal True. idtac "ZZ === C: constant heap ===". exact I. Qed.

Time Eval vm_compute in (zzhC_raw 1).
Time Eval vm_compute in (zzhC_raw 2).
Time Eval vm_compute in (zzhC_raw 4).
Time Eval vm_compute in (zzhC_raw 6).
