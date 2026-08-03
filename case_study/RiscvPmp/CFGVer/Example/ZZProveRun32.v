(* THROWAWAY probe. UPDATE: this file uses zzn_contract, which conflates trip
   count with mem-cell count (zzn_mem_specs n declares n cells) -- see
   PLAN-chunk-gc.md §13. It earlyoom-killed at ~5.8 GB pre-chunk-GC, and even
   post-fix it still balloons (killed at 8.55GB/236s, 2026-08-03) because the
   cell-count confound is untouched by chunk_gc. For a clean trip-count-only
   reading at this N use ZZProveRunZf32.v (zzf_contract) instead, which
   completes at 4.86GB/85.92s. Kept so this rung is reproducible. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZCommon.
Lemma zz_valid_32 : ValidCFGVerifierContract (zzn_contract 32).
Proof. intros; vm_compute; solve_vc; solve_symbase_fetch. Qed.
