(* THROWAWAY: one heavy Eval per process (see ZZCommon.v). Copies = 2. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZCsUnroll.
Import SymProp.notations.
Set Printing Depth 100000.
Set Printing Width 200.
Eval vm_compute in
  (cfg_map (zzcs_contract 2 0) (fun ia p exits P i ec fl =>
     postprocess (CFG_VC_triple p exits P i fl))).
