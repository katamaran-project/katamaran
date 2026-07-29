(* THROWAWAY: one heavy Eval per coqc process. GC on, mode 2, N=1. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZFwdCommon.
Time Eval vm_compute in (zzn_fwdgc_nc 2 1).
