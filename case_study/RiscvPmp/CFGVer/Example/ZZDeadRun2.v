(* THROWAWAY: one heavy Eval per coqc process (see ZZCommon.v). *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZDead.
Time Eval vm_compute in (zz_dnames_count 2, zz_dead_count 2, zz_an_count 2, zz_encoded_instr_count 2).
