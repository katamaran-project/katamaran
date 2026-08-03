(* THROWAWAY: one heavy Eval per coqc process (see ZZCommon.v). Postprocess
   alone (no unquantify), N=2. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZUnqCommon.
Time Eval vm_compute in (zzn_postprocess_nc 2).
