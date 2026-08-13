(* ========================================================================= *)
(* Example/ZZDivremProbe2Ctrl.v -- THROWAWAY diagnostic, matched control for  *)
(* ZZDivremProbe2HeapUp.v.  Byte-identical to ZZDivremProbe2.v's instrs/specs *)
(* but the proof stops right after `solve_vc` (Admitted, not Qed) so the      *)
(* measured cost is ONLY vm_compute + solve_vc -- the same stopping point     *)
(* HeapUp is measured at -- rather than being contaminated by whether         *)
(* solve_symbase_fetch/Qed happens to succeed for one variant and not the     *)
(* other, which is a confound ZZDivremProbe2.v's OWN failure introduced.      *)
(* ------------------------------------------------------------------------ *)

From Katamaran Require Export RiscvPmp.CFGVer.Example.Prelude.

Definition zzdivrem2ctrl_instrs : list AST :=
  [ ITYPE (bv.of_Z 0) X0 A4 RISCV_ADDI
  ; RTYPE A2 A0 A5 RISCV_XOR
  ; ITYPE (bv.of_Z 1) A5 A5 RISCV_SLTIU
  ; ITYPE (bv.of_Z (-1)) A5 A5 RISCV_ADDI
  ; RTYPE A0 A5 A0 RISCV_AND
  ; ITYPE (bv.of_Z 3) X0 A5 RISCV_ADDI
  ; ITYPE (bv.of_Z 1) X0 A6 RISCV_ADDI
  ; ITYPE (bv.of_Z 1) X0 A7 RISCV_ADDI
  ; ITYPE (bv.of_Z (-1)) A5 A5 RISCV_ADDI
  ; RTYPE A7 A0 T0 RISCV_SLL
  ; RTYPE A5 A1 T1 RISCV_SRL
  ; RTYPE T1 T0 T0 RISCV_OR
  ; RTYPE A2 T0 T1 RISCV_SUB
  ; RTYPE A2 T0 T0 RISCV_XOR
  ; RTYPE A2 T1 T2 RISCV_XOR
  ; RTYPE T0 T2 T0 RISCV_AND
  ; RTYPE T1 T0 T0 RISCV_XOR
  ; ITYPE (bv.of_Z (-1)) T0 T0 RISCV_XORI
  ; SHIFTIOP (bv.of_Z 31) T0 T0 RISCV_SRLI
  ; RTYPE A5 A0 T2 RISCV_SRL
  ; RTYPE T0 T2 T0 RISCV_OR
  ; RTYPE A7 T1 T1 RISCV_SRL
  ; RTYPE A5 A2 T2 RISCV_SLL
  ; RTYPE T2 A1 T2 RISCV_SUB
  ; RTYPE T0 X0 T3 RISCV_SUB
  ; RTYPE A0 T1 T1 RISCV_XOR
  ; RTYPE T3 T1 T1 RISCV_AND
  ; RTYPE A0 T1 A0 RISCV_XOR
  ; RTYPE A1 T2 T1 RISCV_XOR
  ; RTYPE T3 T1 T1 RISCV_AND
  ; RTYPE A1 T1 A1 RISCV_XOR
  ; RTYPE A5 T0 T0 RISCV_SLL
  ; RTYPE A4 T0 A4 RISCV_OR
  ; ITYPE (bv.of_Z 1) A7 A7 RISCV_ADDI
  ; BTYPE (bv.of_Z (-104)) A5 A6 RISCV_BLTU
  ; RTYPE A2 A1 A5 RISCV_SUB
  ; RTYPE A2 A1 A6 RISCV_XOR
  ; RTYPE A2 A5 A2 RISCV_XOR
  ; RTYPE A6 A2 A2 RISCV_AND
  ; RTYPE A5 A2 A2 RISCV_XOR
  ; ITYPE (bv.of_Z (-1)) A2 A2 RISCV_XORI
  ; SHIFTIOP (bv.of_Z 31) A2 A2 RISCV_SRLI
  ; RTYPE A2 A0 A2 RISCV_OR
  ; RTYPE A4 A2 A0 RISCV_OR
  ; RTYPE A2 X0 A2 RISCV_SUB
  ; RTYPE A1 A5 A5 RISCV_XOR
  ; RTYPE A2 A5 A2 RISCV_AND
  ; RTYPE A1 A2 A1 RISCV_XOR
  ; STORE (bv.of_Z 0) A1 A3 WORD
  ].

Definition zzdivrem2ctrl_reg_specs_rel : list reg_spec_rel :=
  [ (A0, false, PVExist); (A1, false, PVExist); (A2, false, PVExist)
  ; (A3, true,  PVBaseOff 176)
  ; (A4, false, PVExist); (A5, false, PVExist); (A6, false, PVExist)
  ; (A7, false, PVExist)
  ; (T0, false, PVExist); (T1, false, PVExist); (T2, false, PVExist)
  ; (T3, false, PVExist)
  ].

Definition zzdivrem2ctrl_mem_specs_rel : list mem_spec_rel :=
  [ (176%N, false, PVExist) ].

Definition zzdivrem2ctrl_cfg_contract_param (ia : N)
    : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_rel ia zzdivrem2ctrl_reg_specs_rel zzdivrem2ctrl_mem_specs_rel
    zzdivrem2ctrl_instrs [] 180%N
    (pcOutOfInstrs_exitCond ia zzdivrem2ctrl_instrs) 100.

Lemma valid_zzdivrem2ctrl_cfg_contract_param (ia : N) :
  ValidCFGVerifierContract (zzdivrem2ctrl_cfg_contract_param ia).
Proof. intros. Time vm_compute. Time solve_vc. Admitted.
