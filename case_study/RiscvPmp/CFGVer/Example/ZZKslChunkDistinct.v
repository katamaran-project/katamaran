(* ========================================================================= *)
(* Example/ZZKslChunkDistinct.v -- THROWAWAY diagnostic, not part of any      *)
(* existing PLAN's own file set.                                            *)
(*                                                                           *)
(* Causal check requested in conversation: same 14-instruction loop body as *)
(* KeyScheduleLoop.v (Botan-style masking step + advancing table write),     *)
(* same N=8 trip count / same fuel / same bound, but here the table pointer  *)
(* A3 genuinely ADVANCES each iteration (`addi a3,a3,4`), so 8 DISTINCT      *)
(* memory chunks are declared (56,60,...,84) -- one touched per iteration.   *)
(* Compare directly against ZZKslChunkShared.v, which is byte-identical      *)
(* except A3 never advances (1 SHARED chunk, consumed+reproduced 8 times).  *)
(* Both have EXACTLY the same instruction count / step count / fuel / bound. *)
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

Definition zzkcd_reg_specs_rel : list reg_spec_rel :=
  [ (A0, false, PVExist); (A1, false, PVExist); (A2, false, PVExist)
  ; (A3, false, PVBaseOff 56)
  ; (A4, true, PVConst (bv.of_N 8))
  ].

Definition zzkcd_mem_specs_rel : list mem_spec_rel :=
  [ (56%N, false, PVExist); (60%N, false, PVExist)
  ; (64%N, false, PVExist); (68%N, false, PVExist)
  ; (72%N, false, PVExist); (76%N, false, PVExist)
  ; (80%N, false, PVExist); (84%N, false, PVExist)
  ].

Definition zzkcd_cfg_contract_param (ia : N) : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_rel ia zzkcd_reg_specs_rel zzkcd_mem_specs_rel
    zzkcd_instrs [] 88%N
    (pcOutOfInstrs_exitCond ia zzkcd_instrs) 140.

Lemma valid_zzkcd_cfg_contract_param (ia : N) :
  ValidCFGVerifierContract (zzkcd_cfg_contract_param ia).
Proof. intros. Time vm_compute. Time solve_vc. Time solve_symbase_fetch. Qed.
