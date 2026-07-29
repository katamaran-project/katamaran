(* THROWAWAY: one heavy Eval per coqc process. GC on, mode 0, N=2. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZFwdCommon.
Time Eval vm_compute in (zzn_fwdgc_nc 0 2).
