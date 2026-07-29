(* THROWAWAY: one heavy Eval per coqc process (see ZZCommon.v).
   encodes_instr chunk GC at the recursion point, mode 4, N=4. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZFwdCommon.
Time Eval vm_compute in (zzn_fwdgc_nc 4 4).
