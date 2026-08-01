(* THROWAWAY probe. N=64 was NOT completed: N=32 is earlyoom-killed at ~5.8 GB
   on this box, N=64 was never attempted.  Kept so the rung is reproducible. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZCommon.
Lemma zz_valid_64 : ValidCFGVerifierContract (zzn_contract 64).
Proof. intros; vm_compute; solve_vc; solve_symbase_fetch. Qed.
