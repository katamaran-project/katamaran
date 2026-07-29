(* THROWAWAY: concrete witness for "an is referenced downstream" (one heavy
   Eval per coqc process, see ZZCommon.v). *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZDead.
Time Eval vm_compute in (List.length (zz_show_an 1)).
Time Eval vm_compute in (List.firstn 3 (zz_show_an 1)).
