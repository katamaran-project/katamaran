(* THROWAWAY: one heavy Eval per coqc process (see ZZCommon.v).
   mode 0, N=4.  mode 0 = |wctx| total, 1 = dead ignoring wco,
   2 = dead including wco (the forward-GC number).  Counts ride on nc_debug. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZFwdCommon.
Time Eval vm_compute in (zzn_fwd_nc 0 4).
