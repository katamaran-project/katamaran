(* THROWAWAY: a truly minimal 2-instruction straight-line (no loop, no
   memory) reproducer, purpose-built to eyeball the raw VC directly rather
   than reuse ZZCommon's 14-instruction timing harness (which is far larger
   than needed for "show me one cross-instruction reference"). *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
Import SymProp.notations.

Definition zzmini_instrs : list AST :=
  [ ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ; ITYPE (bv.of_Z 1) A1 A0 RISCV_ADDI
  ].

Definition zzmini_reg_specs : list reg_spec_rel :=
  [(A0, false, PVExist); (A1, false, PVExist)].

Definition zzmini_contract : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_rel 0 zzmini_reg_specs [] zzmini_instrs [] 8
    (pcOutOfInstrs_exitCond 0 zzmini_instrs) 6.

Set Printing Depth 10000.
Eval vm_compute in
  (cfg_map zzmini_contract (fun ia p exits P i ec fl =>
    CFG_VC_triple p exits P i fl)).
