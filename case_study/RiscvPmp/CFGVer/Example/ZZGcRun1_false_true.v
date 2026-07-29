(* THROWAWAY: one heavy Eval per coqc process. chunk_gc=false world_gc=true, N=1. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZGcCommon.
Time Eval vm_compute in (zzn_gc_nc false true 1).
