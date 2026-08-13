(* ========================================================================= *)
(* Example/ZZKslChunkDistinctCommon.v -- THROWAWAY, parametric-N version of   *)
(* ZZKslChunkDistinct.v's reproducer (definitions only, no Eval/proof, so     *)
(* per-N runners don't contaminate each other's allocation counters).        *)
(* Same 14-instruction body; table pointer A3 genuinely advances each         *)
(* iteration, so N declared mem chunks are needed for N iterations.          *)
(* ------------------------------------------------------------------------ *)

From Katamaran Require Export RiscvPmp.CFGVer.Example.Prelude.

Definition zzkcd_back_offset : bv 13 := bv.of_N 8140.

Definition zzkcd_instrs : list AST :=
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
  ; ITYPE (bv.of_Z 4) A3 A3 RISCV_ADDI       (* DISTINCT: pointer advances *)
  ; ITYPE (bv.of_Z (-1)) A4 A4 RISCV_ADDI
  ; BNE A4 X0 zzkcd_back_offset
  ].

Definition zzkcd_reg_specs_rel (n : N) : list reg_spec_rel :=
  [ (A0, false, PVExist); (A1, false, PVExist); (A2, false, PVExist)
  ; (A3, false, PVBaseOff 56)
  ; (A4, true, PVConst (bv.of_N n))
  ].

Definition zzkcd_mem_specs_rel (n : N) : list mem_spec_rel :=
  map (fun i => ((56 + 4 * N.of_nat i)%N, false, PVExist))
      (seq 0 (N.to_nat n)).

Definition zzkcd_cfg_contract_param (n : N) (ia : N)
    : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_rel ia (zzkcd_reg_specs_rel n) (zzkcd_mem_specs_rel n)
    zzkcd_instrs [] (56 + 4 * n)%N
    (pcOutOfInstrs_exitCond ia zzkcd_instrs)
    (Nat.add (Nat.mul 14 (N.to_nat n)) 20).
