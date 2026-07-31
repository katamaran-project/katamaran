(* THROWAWAY: one heavy Eval per coqc process (see ZZCommon.v). *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZCommon.
Time Eval vm_compute in (zzn_raw_nc 8).
