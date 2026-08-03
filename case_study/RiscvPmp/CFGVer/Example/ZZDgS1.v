(* THROWAWAY control: cheapest possible consumer. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZDiagCommon.
Definition zzf_sz (n : nat) : N :=
  cfg_map (zzf_contract n) (fun ia p exits P i ec fl =>
    SymProp.Statistics.size (CFG_VC_triple p exits P i fl)).
Time Eval vm_compute in (zzf_sz 1).
