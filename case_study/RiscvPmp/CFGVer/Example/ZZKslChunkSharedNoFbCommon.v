(* ========================================================================= *)
(* Example/ZZKslChunkSharedNoFbCommon.v -- THROWAWAY, tests whether the       *)
(* self-referential masking recurrence (H := (H>>1) ^ mask(H), i.e. A0 fed    *)
(* into itself every iteration) is a SECOND cost driver independent of chunk  *)
(* count.  Byte-identical to ZZKslChunkSharedCommon.v (14 instrs, 1 shared    *)
(* mem chunk, same fuel/bound formulas) EXCEPT the two reads of A0 (the       *)
(* self-feeding masking input) are rerouted to read A3 instead -- A3 is the   *)
(* PVBaseOff pointer, a genuine constant across the whole run in this         *)
(* variant, so A0's computed value no longer depends on its own previous      *)
(* iteration.  If cost collapses to ~linear here, the self-reference (not     *)
(* chunk count) explains the quadratic-at-fixed-heap result.                 *)
(* ------------------------------------------------------------------------ *)

From Katamaran Require Export RiscvPmp.CFGVer.Example.Prelude.

Definition zzkcsnf_back_offset : bv 13 := bv.of_N 8140.

Definition zzkcsnf_instrs : list AST :=
  [ ITYPE (bv.of_Z 1) A3 A1 RISCV_ANDI       (* was: andi a1,a0,1 -- now reads A3 *)
  ; ITYPE (bv.of_Z (-1)) A1 A2 RISCV_XORI
  ; ITYPE (bv.of_Z (-1)) A1 A1 RISCV_ADDI
  ; RTYPE A2 A1 A1 RISCV_AND
  ; SHIFTIOP (bv.of_Z 31) A1 A1 RISCV_SRLI
  ; ITYPE (bv.of_Z (-1)) A1 A1 RISCV_ADDI
  ; UTYPE (bv.of_Z 921600) A2 RISCV_LUI
  ; RTYPE A2 A1 A1 RISCV_AND
  ; SHIFTIOP (bv.of_Z 1) A3 A0 RISCV_SRLI    (* was: srli a0,a0,1 -- now reads A3 *)
  ; RTYPE A0 A1 A0 RISCV_XOR
  ; STORE (bv.of_Z 0) A0 A3 WORD
  ; ITYPE (bv.of_Z 0) A3 A3 RISCV_ADDI       (* SHARED: no-op, pointer fixed *)
  ; ITYPE (bv.of_Z (-1)) A4 A4 RISCV_ADDI
  ; BNE A4 X0 zzkcsnf_back_offset
  ].

Definition zzkcsnf_reg_specs_rel (n : N) : list reg_spec_rel :=
  [ (A0, false, PVExist); (A1, false, PVExist); (A2, false, PVExist)
  ; (A3, false, PVBaseOff 56)
  ; (A4, true, PVConst (bv.of_N n))
  ].

Definition zzkcsnf_mem_specs_rel : list mem_spec_rel :=
  [ (56%N, false, PVExist) ].

Definition zzkcsnf_cfg_contract_param (n : N) (ia : N)
    : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_rel ia (zzkcsnf_reg_specs_rel n) zzkcsnf_mem_specs_rel
    zzkcsnf_instrs [] (56 + 4 * n)%N
    (pcOutOfInstrs_exitCond ia zzkcsnf_instrs)
    (Nat.add (Nat.mul 14 (N.to_nat n)) 20).
