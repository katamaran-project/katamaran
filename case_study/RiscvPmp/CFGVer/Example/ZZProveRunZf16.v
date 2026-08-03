(* THROWAWAY probe. zzf_contract isolates trip-count growth from zzn's
   confounding memory-cell growth (heap/mem-spec list pinned at size 1 for
   all N) -- see PLAN-chunk-gc.md §13 / ZZDiagCommon.v's Arm B comment.
   COMPLETED: allocated_words 7,158,303,103, wall 40.60s, RSS 3.94GB.
   Kept so this rung is reproducible (part of the N=8/16/32/64 affine series). *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZDiagCommon.
Lemma zzf_valid_16 : ValidCFGVerifierContract (zzf_contract 16).
Proof. intros; vm_compute; solve_vc; solve_symbase_fetch. Qed.
