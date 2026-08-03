(* THROWAWAY: print the raw VC directly for eyeballing (one heavy Eval per
   coqc process, see ZZCommon.v). *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZCommon.
Import SymProp.notations.
Set Printing Depth 10000.
Eval vm_compute in
  (cfg_map (zzn_contract 1) (fun ia p exits P i ec fl =>
    CFG_VC_triple p exits P i fl)).
