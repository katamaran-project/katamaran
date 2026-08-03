From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZCommon.
Lemma zz_valid_1 : ValidCFGVerifierContract (zzn_contract 1).
Proof. intros; vm_compute; solve_vc; solve_symbase_fetch. Qed.
