(* THROWAWAY: one heavy Eval per coqc process (see ZZCommon.v). *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZDead.
Time Eval vm_compute in (zz_dnames_count 4, zz_dead_count 4, zz_an_count 4, zz_encoded_instr_count 4).
