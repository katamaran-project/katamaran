(* ========================================================================= *)
(* Example/ZZDivremProbe2.v -- THROWAWAY diagnostic, PLAN-muladd-full.md.     *)
(*                                                                           *)
(* ISOLATES just BearSSL br_divrem's own bit-serial division loop (patched   *)
(* to 2 iterations, same technique as ZZMuladdFullN2.v) to measure its OWN   *)
(* vm_compute cost, independent of everything else in the whole-function     *)
(* muladd probe -- ZZMuladdFullN2.v's own vm_compute timed out at 300s and   *)
(* this isolates whether the division loop itself is the expensive part.    *)
(* No secrecy/publicness design here -- this is a pure timing diagnostic,    *)
(* all register/memory values left maximally unconstrained (PVExist).       *)
(* ------------------------------------------------------------------------ *)

From Katamaran Require Export RiscvPmp.CFGVer.Example.Prelude.

Definition zzdivrem2_instrs : list AST :=
  [ ITYPE (bv.of_Z 0) X0 A4 RISCV_ADDI   (* li	A4, 0 *)
  ; RTYPE A2 A0 A5 RISCV_XOR   (* xor	A5, A0, A2 *)
  ; ITYPE (bv.of_Z 1) A5 A5 RISCV_SLTIU   (* seqz	A5, A5 *)
  ; ITYPE (bv.of_Z (-1)) A5 A5 RISCV_ADDI   (* addi	A5, A5, -1 *)
  ; RTYPE A0 A5 A0 RISCV_AND   (* and	A0, A5, A0 *)
  ; ITYPE (bv.of_Z 3) X0 A5 RISCV_ADDI   (* li	A5, 3 *)
  ; ITYPE (bv.of_Z 1) X0 A6 RISCV_ADDI   (* li	A6, 1 *)
  ; ITYPE (bv.of_Z 1) X0 A7 RISCV_ADDI   (* li	A7, 1 *)
  ; ITYPE (bv.of_Z (-1)) A5 A5 RISCV_ADDI   (* addi	A5, A5, -1 *)
  ; RTYPE A7 A0 T0 RISCV_SLL   (* sll	T0, A0, A7 *)
  ; RTYPE A5 A1 T1 RISCV_SRL   (* srl	T1, A1, A5 *)
  ; RTYPE T1 T0 T0 RISCV_OR   (* or	T0, T0, T1 *)
  ; RTYPE A2 T0 T1 RISCV_SUB   (* sub	T1, T0, A2 *)
  ; RTYPE A2 T0 T0 RISCV_XOR   (* xor	T0, T0, A2 *)
  ; RTYPE A2 T1 T2 RISCV_XOR   (* xor	T2, T1, A2 *)
  ; RTYPE T0 T2 T0 RISCV_AND   (* and	T0, T2, T0 *)
  ; RTYPE T1 T0 T0 RISCV_XOR   (* xor	T0, T0, T1 *)
  ; ITYPE (bv.of_Z (-1)) T0 T0 RISCV_XORI   (* not	T0, T0 *)
  ; SHIFTIOP (bv.of_Z 31) T0 T0 RISCV_SRLI   (* srli	T0, T0, 31 *)
  ; RTYPE A5 A0 T2 RISCV_SRL   (* srl	T2, A0, A5 *)
  ; RTYPE T0 T2 T0 RISCV_OR   (* or	T0, T2, T0 *)
  ; RTYPE A7 T1 T1 RISCV_SRL   (* srl	T1, T1, A7 *)
  ; RTYPE A5 A2 T2 RISCV_SLL   (* sll	T2, A2, A5 *)
  ; RTYPE T2 A1 T2 RISCV_SUB   (* sub	T2, A1, T2 *)
  ; RTYPE T0 X0 T3 RISCV_SUB   (* neg	T3, T0 *)
  ; RTYPE A0 T1 T1 RISCV_XOR   (* xor	T1, T1, A0 *)
  ; RTYPE T3 T1 T1 RISCV_AND   (* and	T1, T1, T3 *)
  ; RTYPE A0 T1 A0 RISCV_XOR   (* xor	A0, T1, A0 *)
  ; RTYPE A1 T2 T1 RISCV_XOR   (* xor	T1, T2, A1 *)
  ; RTYPE T3 T1 T1 RISCV_AND   (* and	T1, T1, T3 *)
  ; RTYPE A1 T1 A1 RISCV_XOR   (* xor	A1, T1, A1 *)
  ; RTYPE A5 T0 T0 RISCV_SLL   (* sll	T0, T0, A5 *)
  ; RTYPE A4 T0 A4 RISCV_OR   (* or	A4, T0, A4 *)
  ; ITYPE (bv.of_Z 1) A7 A7 RISCV_ADDI   (* addi	A7, A7, 1 *)
  ; BTYPE (bv.of_Z (-104)) A5 A6 RISCV_BLTU   (* bltu	A6, A5, .LBB0_1 *)
  ; RTYPE A2 A1 A5 RISCV_SUB   (* sub	A5, A1, A2 *)
  ; RTYPE A2 A1 A6 RISCV_XOR   (* xor	A6, A1, A2 *)
  ; RTYPE A2 A5 A2 RISCV_XOR   (* xor	A2, A5, A2 *)
  ; RTYPE A6 A2 A2 RISCV_AND   (* and	A2, A2, A6 *)
  ; RTYPE A5 A2 A2 RISCV_XOR   (* xor	A2, A2, A5 *)
  ; ITYPE (bv.of_Z (-1)) A2 A2 RISCV_XORI   (* not	A2, A2 *)
  ; SHIFTIOP (bv.of_Z 31) A2 A2 RISCV_SRLI   (* srli	A2, A2, 31 *)
  ; RTYPE A2 A0 A2 RISCV_OR   (* or	A2, A0, A2 *)
  ; RTYPE A4 A2 A0 RISCV_OR   (* or	A0, A2, A4 *)
  ; RTYPE A2 X0 A2 RISCV_SUB   (* neg	A2, A2 *)
  ; RTYPE A1 A5 A5 RISCV_XOR   (* xor	A5, A5, A1 *)
  ; RTYPE A2 A5 A2 RISCV_AND   (* and	A2, A5, A2 *)
  ; RTYPE A1 A2 A1 RISCV_XOR   (* xor	A1, A2, A1 *)
  ; STORE (bv.of_Z 0) A1 A3 WORD   (* sw	A1, 0(A3) *)
  ].

Definition zzdivrem2_reg_specs_rel : list reg_spec_rel :=
  [ (A0, false, PVExist); (A1, false, PVExist); (A2, false, PVExist)
  ; (A3, true,  PVBaseOff 176)
  ; (A4, false, PVExist); (A5, false, PVExist); (A6, false, PVExist)
  ; (A7, false, PVExist)
  ; (T0, false, PVExist); (T1, false, PVExist); (T2, false, PVExist)
  ; (T3, false, PVExist)
  ].

Definition zzdivrem2_mem_specs_rel : list mem_spec_rel :=
  [ (176%N, false, PVExist) ].

Definition zzdivrem2_cfg_contract_param (ia : N)
    : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_rel ia zzdivrem2_reg_specs_rel zzdivrem2_mem_specs_rel
    zzdivrem2_instrs [] 180%N
    (pcOutOfInstrs_exitCond ia zzdivrem2_instrs) 100.

Lemma valid_zzdivrem2_cfg_contract_param (ia : N) :
  ValidCFGVerifierContract (zzdivrem2_cfg_contract_param ia).
Proof. intros; vm_compute; solve_vc; solve_symbase_fetch. Qed.
