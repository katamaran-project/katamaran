(* THROWAWAY: one heavy Eval per coqc process. chunk_gc=true world_gc=true, N=4. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZGcCommon.
Time Eval vm_compute in (zzn_gc_nc true true 4).
