(* THROWAWAY probe. zzf_contract isolates trip-count growth from zzn's
   confounding memory-cell growth (heap/mem-spec list pinned at size 1 for
   all N) -- see PLAN-chunk-gc.md §13 / ZZDiagCommon.v's Arm B comment.
   COMPLETED: allocated_words 23,332,716,671, wall 213.78s, RSS 7.29GB -- never
   attempted before this investigation.
   Kept so this rung is reproducible (part of the N=8/16/32/64 affine series). *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZDiagCommon.
Lemma zzf_valid_64 : ValidCFGVerifierContract (zzf_contract 64).
Proof. intros; vm_compute; solve_vc; solve_symbase_fetch. Qed.
