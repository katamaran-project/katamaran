(* ========================================================================= *)
(* Example/ZZKslChunkShared.v -- THROWAWAY diagnostic, matched pair for       *)
(* ZZKslChunkDistinct.v.  Byte-identical 14-instruction body, same N=8 trips, *)
(* same fuel/bound -- the ONLY difference is instruction 12: `addi a3,a3,0`   *)
(* (true no-op, same length/step cost as the other file's `addi a3,a3,4`)     *)
(* instead of an advance, so A3 never changes and all 8 iterations write to   *)
(* the SAME single address (p+56) -- 1 SHARED memory chunk instead of 8       *)
(* distinct ones.  Everything else (step count, fuel, bound, branch offset)   *)
(* is identical to ZZKslChunkDistinct.v, so any cost delta isolates the       *)
(* declared-chunk-count effect at fixed step count.                          *)
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

Definition zzkcs_reg_specs_rel : list reg_spec_rel :=
  [ (A0, false, PVExist); (A1, false, PVExist); (A2, false, PVExist)
  ; (A3, false, PVBaseOff 56)
  ; (A4, true, PVConst (bv.of_N 8))
  ].

Definition zzkcs_mem_specs_rel : list mem_spec_rel :=
  [ (56%N, false, PVExist) ].

Definition zzkcs_cfg_contract_param (ia : N) : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_rel ia zzkcs_reg_specs_rel zzkcs_mem_specs_rel
    zzkcs_instrs [] 88%N
    (pcOutOfInstrs_exitCond ia zzkcs_instrs) 140.

Lemma valid_zzkcs_cfg_contract_param (ia : N) :
  ValidCFGVerifierContract (zzkcs_cfg_contract_param ia).
Proof. intros. Time vm_compute. Time solve_vc. Time solve_symbase_fetch. Qed.
