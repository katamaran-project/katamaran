(* ========================================================================= *)
(* Example/ZZKslNUsedFlatCommon.v -- THROWAWAY.  The missing cell: N chunks   *)
(* genuinely USED (table pointer A3 really advances, `addi a3,a3,4`, as in    *)
(* ZZKslChunkDistinctCommon.v) but with H computed from A3 (the advancing     *)
(* pointer) instead of from itself, exactly as                              *)
(* ZZKslChunkSharedNoFbCommon.v/ZZKslChunkPaddedCommon.v do -- so the FLAT    *)
(* term axis is held fixed while the chunk axis moves from 1-used to N-used. *)
(* This isolates the chunk-usage effect cleanly, without the term-growth     *)
(* driver riding along the way it did in the DISTINCT-vs-PADDED comparison   *)
(* (that comparison changed BOTH axes at once: DISTINCT has growing H,       *)
(* PADDED has flat H, so the "N used vs N declared-but-dead" conclusion      *)
(* drawn from it was confounded).                                           *)
(*                                                                           *)
(* Caveat worth checking, not just assuming: A3 itself now changes every      *)
(* iteration (unlike the no-op variants where it's a true constant). Its own *)
(* representation should stay a flat `p + offset` term (constant-folded, the  *)
(* same address-arithmetic pattern every prior base-relative example already *)
(* relies on) rather than nesting like H's XOR/shift chain did -- if this    *)
(* variant's numbers come back looking anomalously steep, that assumption is *)
(* the first thing to check.                                                *)
(* ------------------------------------------------------------------------ *)

From Katamaran Require Export RiscvPmp.CFGVer.Example.Prelude.

Definition zzknuf_back_offset : bv 13 := bv.of_N 8140.

Definition zzknuf_instrs : list AST :=
  [ ITYPE (bv.of_Z 1) A3 A1 RISCV_ANDI       (* mask bit from A3 (advancing) *)
  ; ITYPE (bv.of_Z (-1)) A1 A2 RISCV_XORI
  ; ITYPE (bv.of_Z (-1)) A1 A1 RISCV_ADDI
  ; RTYPE A2 A1 A1 RISCV_AND
  ; SHIFTIOP (bv.of_Z 31) A1 A1 RISCV_SRLI
  ; ITYPE (bv.of_Z (-1)) A1 A1 RISCV_ADDI
  ; UTYPE (bv.of_Z 921600) A2 RISCV_LUI
  ; RTYPE A2 A1 A1 RISCV_AND
  ; SHIFTIOP (bv.of_Z 1) A3 A0 RISCV_SRLI    (* H from A3 (advancing), not A0 *)
  ; RTYPE A0 A1 A0 RISCV_XOR
  ; STORE (bv.of_Z 0) A0 A3 WORD
  ; ITYPE (bv.of_Z 4) A3 A3 RISCV_ADDI       (* REAL advance -- N distinct addresses *)
  ; ITYPE (bv.of_Z (-1)) A4 A4 RISCV_ADDI
  ; BNE A4 X0 zzknuf_back_offset
  ].

Definition zzknuf_reg_specs_rel (n : N) : list reg_spec_rel :=
  [ (A0, false, PVExist); (A1, false, PVExist); (A2, false, PVExist)
  ; (A3, false, PVBaseOff 56)
  ; (A4, true, PVConst (bv.of_N n))
  ].

(* N distinct chunks, all genuinely written -- same shape as
   ZZKslChunkDistinctCommon.v's zzkcd_mem_specs_rel. *)
Definition zzknuf_mem_specs_rel (n : N) : list mem_spec_rel :=
  map (fun i => ((56 + 4 * N.of_nat i)%N, false, PVExist))
      (seq 0 (N.to_nat n)).

Definition zzknuf_cfg_contract_param (n : N) (ia : N)
    : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_rel ia (zzknuf_reg_specs_rel n) (zzknuf_mem_specs_rel n)
    zzknuf_instrs [] (56 + 4 * n)%N
    (pcOutOfInstrs_exitCond ia zzknuf_instrs)
    (Nat.add (Nat.mul 14 (N.to_nat n)) 20).
