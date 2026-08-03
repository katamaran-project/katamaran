(* THROWAWAY probe. UPDATE: this file uses zzn_contract, which conflates trip
   count with mem-cell count (zzn_mem_specs n declares n cells) -- see
   PLAN-chunk-gc.md §13. Untried at N=64 (its N=32 sibling still balloons post
   chunk-GC due to the cell-count confound, not tried this far). For a clean
   trip-count-only reading at this N use ZZProveRunZf64.v (zzf_contract)
   instead, which completes at 7.29GB/213.78s. Kept so this rung is
   reproducible. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZCommon.
Lemma zz_valid_64 : ValidCFGVerifierContract (zzn_contract 64).
Proof. intros; vm_compute; solve_vc; solve_symbase_fetch. Qed.
