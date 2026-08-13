(* ========================================================================= *)
(* Example/ZZKslChunkPaddedCommon.v -- THROWAWAY, tests declared-but-UNUSED   *)
(* chunk count scaling with N, on top of NO-FEEDBACK's body (no self-         *)
(* reference).  Byte-identical instructions to                              *)
(* ZZKslChunkSharedNoFbCommon.v (H built from the constant A3, table pointer *)
(* A3 never advances -- `addi a3,a3,0` -- so the STORE always targets the    *)
(* SAME address, p+56) -- but the PRECONDITION now declares N memory chunks  *)
(* (p+56, p+60, ..., same address-generation shape as                       *)
(* ZZKslChunkDistinctCommon.v), of which only the FIRST is ever read or      *)
(* written.  The other N-1 are pure declared-but-dead weight, same idea as   *)
(* ZZDivremProbe2HeapUp.v's unused registers/cells but scaling with N here.  *)
(* Isolates: does merely DECLARING N chunks cost like DISTINCT (N chunks,    *)
(* each genuinely used once), or like NO-FEEDBACK (1 chunk, genuinely used   *)
(* N times), or something else entirely?                                    *)
(* ------------------------------------------------------------------------ *)

From Katamaran Require Export RiscvPmp.CFGVer.Example.Prelude.

Definition zzkcp_back_offset : bv 13 := bv.of_N 8140.

Definition zzkcp_instrs : list AST :=
  [ ITYPE (bv.of_Z 1) A3 A1 RISCV_ANDI       (* mask bit from A3 (constant) *)
  ; ITYPE (bv.of_Z (-1)) A1 A2 RISCV_XORI
  ; ITYPE (bv.of_Z (-1)) A1 A1 RISCV_ADDI
  ; RTYPE A2 A1 A1 RISCV_AND
  ; SHIFTIOP (bv.of_Z 31) A1 A1 RISCV_SRLI
  ; ITYPE (bv.of_Z (-1)) A1 A1 RISCV_ADDI
  ; UTYPE (bv.of_Z 921600) A2 RISCV_LUI
  ; RTYPE A2 A1 A1 RISCV_AND
  ; SHIFTIOP (bv.of_Z 1) A3 A0 RISCV_SRLI    (* H from A3 (constant), not A0 *)
  ; RTYPE A0 A1 A0 RISCV_XOR
  ; STORE (bv.of_Z 0) A0 A3 WORD             (* always writes p+56 -- A3 fixed *)
  ; ITYPE (bv.of_Z 0) A3 A3 RISCV_ADDI       (* no-op: pointer never advances *)
  ; ITYPE (bv.of_Z (-1)) A4 A4 RISCV_ADDI
  ; BNE A4 X0 zzkcp_back_offset
  ].

Definition zzkcp_reg_specs_rel (n : N) : list reg_spec_rel :=
  [ (A0, false, PVExist); (A1, false, PVExist); (A2, false, PVExist)
  ; (A3, false, PVBaseOff 56)
  ; (A4, true, PVConst (bv.of_N n))
  ].

(* N declared chunks, same address-generation shape as
   ZZKslChunkDistinctCommon.v's zzkcd_mem_specs_rel -- but the instructions
   above only ever touch p+56 (the first one). The rest are dead weight. *)
Definition zzkcp_mem_specs_rel (n : N) : list mem_spec_rel :=
  map (fun i => ((56 + 4 * N.of_nat i)%N, false, PVExist))
      (seq 0 (N.to_nat n)).

Definition zzkcp_cfg_contract_param (n : N) (ia : N)
    : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_rel ia (zzkcp_reg_specs_rel n) (zzkcp_mem_specs_rel n)
    zzkcp_instrs [] (56 + 4 * n)%N
    (pcOutOfInstrs_exitCond ia zzkcp_instrs)
    (Nat.add (Nat.mul 14 (N.to_nat n)) 20).
