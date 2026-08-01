From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZCommon.
Lemma zz_valid_8 : ValidCFGVerifierContract (zzn_contract 8).
Proof. intros; vm_compute; solve_vc; solve_symbase_fetch. Qed.
