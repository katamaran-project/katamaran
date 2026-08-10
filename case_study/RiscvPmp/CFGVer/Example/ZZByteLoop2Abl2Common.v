(* ========================================================================= *)
(* Example/ZZByteLoop2Abl2Common.v — THROWAWAY diagnostic ablation #2 of      *)
(* ZZByteLoop2Common.v, PLAN-check-scalar-full.md §4 follow-up.              *)
(*                                                                           *)
(* Second single-instruction change: the "lbu a5,0(a1)" step is replaced by  *)
(* a non-memory ALU instruction with the same destination register (A5),    *)
(* so the loop keeps the SAME instruction count (13, same L) but drops from *)
(* TWO memory reads/resident byte arrays per iteration to ONE (k[] only;    *)
(* n[] is no longer read and is dropped from loop2_byte_specs_rel).          *)
(* Purpose: separate "longer instruction body" (L=13, same as the real body) *)
(* from "two resident memory arrays / two chunk reads per iteration" as the *)
(* driver of the accelerating cost curve. Ablation #1 (ZZByteLoop2AblCommon) *)
(* already ruled out the accumulator A3 being read twice per iteration.     *)
(* ========================================================================= *)

From Katamaran Require Export RiscvPmp.CFGVer.Example.Prelude.

Definition loop2_back_offset : bv 13 := bv.of_N 8144.

Definition loop2_instrs : list AST :=
  [ LBU A4 A0 (bv.of_N 0)                    (* lbu  a4, 0(a0) *)
  ; RTYPE X0 A0 A5 RISCV_ADD                  (* ABLATED: was "LBU A5 A1 (bv.of_N 0)" (lbu a5, 0(a1)) — now a non-memory mv a5,a0 *)
  ; RTYPE A4 A5 A6 RISCV_SLTU                (* sltu a6, a5, a4 *)
  ; RTYPE A5 A4 A4 RISCV_SLTU                (* sltu a4, a4, a5 *)
  ; RTYPE A4 X0 A4 RISCV_SUB                 (* neg  a4, a4 *)
  ; RTYPE A6 A4 A4 RISCV_OR                  (* or   a4, a4, a6 *)
  ; RTYPE A3 X0 A5 RISCV_SLTU                (* snez a5, a3 *)
  ; ITYPE (bv.of_Z (-1)) A5 A5 RISCV_ADDI    (* addi a5, a5, -1 *)
  ; RTYPE A4 A5 A4 RISCV_AND                 (* and  a4, a5, a4 *)
  ; RTYPE A4 A3 A3 RISCV_OR                  (* or   a3, a4, a3 *)
  ; ITYPE (bv.of_Z 1) A1 A1 RISCV_ADDI       (* addi a1, a1, 1 *)
  ; ITYPE (bv.of_Z 1) A0 A0 RISCV_ADDI       (* addi a0, a0, 1 *)
  ; BNE A1 A2 loop2_back_offset              (* bne  a1, a2, .LBB0_2 *)
  ].

Definition loop2_reg_specs_rel (n : N) : list reg_spec_rel :=
  [ (A0, true,  PVBaseOff 52)
  ; (A1, true,  PVBaseOff (52 + n)%N)
  ; (A2, true,  PVBaseOff (52 + n + n)%N)
  ; (A3, true,  PVConst (bv.of_N 0))
  ; (A4, false, PVExist)
  ; (A5, false, PVExist)
  ; (A6, false, PVExist)
  ].

Definition loop2_k_specs_rel (n : N) : list mem_spec_rel :=
  map (fun i => ((52 + 4 * N.of_nat i)%N, false, PVExist))
      (seq 0 (Nat.div (N.to_nat n) 4)).

(* n[] dropped entirely — nothing reads it in this ablation. *)
Definition loop2_byte_specs_rel (n : N) : list mem_spec_rel :=
  loop2_k_specs_rel n.

Definition loop2_cfg_contract_param (n : N) (ia : N)
    : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_rel_bytes ia (loop2_reg_specs_rel n) [] (loop2_byte_specs_rel n)
    loop2_instrs [] (52 + n + n)%N
    (pcOutOfInstrs_exitCond ia loop2_instrs)
    (Nat.add (Nat.mul 13 (N.to_nat n)) 20).
