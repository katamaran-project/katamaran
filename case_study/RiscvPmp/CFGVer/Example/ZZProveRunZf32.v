(* THROWAWAY probe. zzf_contract isolates trip-count growth from zzn's
   confounding memory-cell growth (heap/mem-spec list pinned at size 1 for
   all N) -- see PLAN-chunk-gc.md §13 / ZZDiagCommon.v's Arm B comment.
   COMPLETED: allocated_words 12,549,778,473, wall 85.92s, RSS 4.86GB (compare
   the confounded zzn_contract 32, which had to be killed at 8.55GB/236s).
   Kept so this rung is reproducible (part of the N=8/16/32/64 affine series). *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZDiagCommon.
Lemma zzf_valid_32 : ValidCFGVerifierContract (zzf_contract 32).
Proof. intros; vm_compute; solve_vc; solve_symbase_fetch. Qed.
