(* THROWAWAY: one heavy Eval per coqc process (see ZZCommon.v). Postprocess-
   first unquantify (the composition main actually uses), N=1. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZUnqCommon.
Time Eval vm_compute in (zzn_postprocess_unq_nc 1).
