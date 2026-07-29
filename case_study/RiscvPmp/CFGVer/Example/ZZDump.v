(* THROWAWAY: direct dump, no custom traversal, no notations import. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZCommon.
Eval vm_compute in
  (cfg_map (zzn_contract 1) (fun ia p exits P i ec fl =>
    postprocess (CFG_VC_triple p exits P i fl))).
