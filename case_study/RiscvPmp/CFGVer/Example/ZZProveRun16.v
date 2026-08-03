From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZCommon.
Lemma zz_valid_16 : ValidCFGVerifierContract (zzn_contract 16).
Proof. intros; vm_compute; solve_vc; solve_symbase_fetch. Qed.
