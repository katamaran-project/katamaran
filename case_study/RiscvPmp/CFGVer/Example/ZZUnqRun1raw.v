(* THROWAWAY: one heavy Eval per coqc process (see ZZCommon.v). Unquantify
   over the RAW (pre-postprocess) VC, N=1. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZUnqCommon.
Time Eval vm_compute in (zzn_unq_nc 1).
