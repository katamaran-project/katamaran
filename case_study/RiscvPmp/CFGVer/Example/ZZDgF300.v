(* THROWAWAY fuel ablation at N=4. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZDiagCommon.
Definition zzfuel : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_rel 0 (zzn_reg_specs 4) [(56%N, false, PVExist)]
    zzf_instrs [] 60 (pcOutOfInstrs_exitCond 0 zzf_instrs) 300.
Definition zzfuel_dc : DC :=
  cfg_map zzfuel (fun ia p exits P i ec fl => dcensus (CFG_VC_triple p exits P i fl)).
Time Eval vm_compute in zzfuel_dc.
