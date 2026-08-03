(* THROWAWAY: read the per-step probe out of nc_debug. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZDiagCommon.
Definition zzf_nc (k : nat) : NC :=
  cfg_map (zzf_contract k) (fun ia p exits P i ec fl =>
    ncount (CFG_VC_triple p exits P i fl)).
Time Eval vm_compute in (zzf_nc 4).
