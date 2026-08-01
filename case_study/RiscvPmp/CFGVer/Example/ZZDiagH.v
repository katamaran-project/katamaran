(* THROWAWAY: heap held LARGE and CONSTANT (8 cells) while trips grow.
   Separates driver 1 (per-step cost ~ heap size) from driver 2 (per-step
   cost ~ steps taken).  If the quadratic coefficient c is unchanged vs the
   1-cell arm, driver 2 is heap-independent. *)
From Katamaran Require Export RiscvPmp.CFGVer.Example.ZZDiagCommon.

Definition zzh_contract (n : nat) : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_rel 0 (zzn_reg_specs n) (zzn_mem_specs 8)
    zzf_instrs [] 88
    (pcOutOfInstrs_exitCond 0 zzf_instrs) (30 * n + 40).

Definition zzh_dc (n : nat) : DC :=
  cfg_map (zzh_contract n) (fun ia p exits P i ec fl =>
    dcensus (CFG_VC_triple p exits P i fl)).
