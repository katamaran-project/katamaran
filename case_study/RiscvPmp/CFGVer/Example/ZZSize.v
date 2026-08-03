(* THROWAWAY: node census of the POSTPROCESSED tree -- the thing safeE unfolds
   and the thing Qed re-checks -- for both the parametric and concrete base. *)
From Katamaran Require Export RiscvPmp.CFGVer.Example.ZZQ.

Definition zzn_pp_nc (n : nat) : NC :=
  cfg_map (zzn_contract n) (fun ia p exits P i ec fl =>
    ncount (postprocess (CFG_VC_triple p exits P i fl))).

Definition zzc_pp_nc (n : nat) : NC :=
  cfg_map (zzc_contract n) (fun ia p exits P i ec fl =>
    ncount (postprocess (CFG_VC_triple p exits P i fl))).
