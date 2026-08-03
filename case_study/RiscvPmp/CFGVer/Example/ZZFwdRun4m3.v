(* THROWAWAY: one heavy Eval per coqc process (see ZZCommon.v).
   mode 3, N=4 -- name-resolved breakdown of the FORWARD-LIVE half. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZFwdCommon.
Time Eval vm_compute in (zzn_fwd_nc 3 4).
