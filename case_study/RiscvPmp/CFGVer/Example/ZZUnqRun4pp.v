(* THROWAWAY: one heavy Eval per coqc process (see ZZCommon.v). Postprocess-
   first unquantify, N=4. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZUnqCommon.
Time Eval vm_compute in (zzn_postprocess_unq_nc 4).
