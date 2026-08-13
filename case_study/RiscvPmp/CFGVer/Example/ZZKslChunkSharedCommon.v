(* ========================================================================= *)
(* Example/ZZKslChunkSharedCommon.v -- THROWAWAY, parametric-N version of     *)
(* ZZKslChunkShared.v's reproducer.  Byte-identical to                       *)
(* ZZKslChunkDistinctCommon.v except instruction 12 is a no-op               *)
(* (`addi a3,a3,0`) instead of an advance, so all N iterations write to the  *)
(* SAME single address -- 1 shared mem chunk regardless of N.  Bound/fuel    *)
(* formulas kept identical to the DISTINCT common file (same n) to avoid     *)
(* introducing a second confound.                                           *)
(* ------------------------------------------------------------------------ *)

From Katamaran Require Export RiscvPmp.CFGVer.Example.Prelude.

Definition zzkcs_back_offset : bv 13 := bv.of_N 8140.

Definition zzkcs_instrs : list AST :=
  [ ITYPE (bv.of_Z 1) A0 A1 RISCV_ANDI
  ; ITYPE (bv.of_Z (-1)) A1 A2 RISCV_XORI
  ; ITYPE (bv.of_Z (-1)) A1 A1 RISCV_ADDI
  ; RTYPE A2 A1 A1 RISCV_AND
  ; SHIFTIOP (bv.of_Z 31) A1 A1 RISCV_SRLI
  ; ITYPE (bv.of_Z (-1)) A1 A1 RISCV_ADDI
  ; UTYPE (bv.of_Z 921600) A2 RISCV_LUI
  ; RTYPE A2 A1 A1 RISCV_AND
  ; SHIFTIOP (bv.of_Z 1) A0 A0 RISCV_SRLI
  ; RTYPE A0 A1 A0 RISCV_XOR
  ; STORE (bv.of_Z 0) A0 A3 WORD
  ; ITYPE (bv.of_Z 0) A3 A3 RISCV_ADDI       (* SHARED: no-op, pointer fixed *)
  ; ITYPE (bv.of_Z (-1)) A4 A4 RISCV_ADDI
  ; BNE A4 X0 zzkcs_back_offset
  ].

Definition zzkcs_reg_specs_rel (n : N) : list reg_spec_rel :=
  [ (A0, false, PVExist); (A1, false, PVExist); (A2, false, PVExist)
  ; (A3, false, PVBaseOff 56)
  ; (A4, true, PVConst (bv.of_N n))
  ].

Definition zzkcs_mem_specs_rel (n : N) : list mem_spec_rel :=
  [ (56%N, false, PVExist) ].

Definition zzkcs_cfg_contract_param (n : N) (ia : N)
    : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_rel ia (zzkcs_reg_specs_rel n) (zzkcs_mem_specs_rel n)
    zzkcs_instrs [] (56 + 4 * n)%N
    (pcOutOfInstrs_exitCond ia zzkcs_instrs)
    (Nat.add (Nat.mul 14 (N.to_nat n)) 20).
