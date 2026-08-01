From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZCommon.
Lemma ctl_zzn : ValidCFGVerifierContract (zzn_contract 2).
Proof.
  intros. vm_compute.
  solve_vc.
  all: (let n := numgoals in idtac "ZZN after solve_vc:" n).
  try solve_symbase_fetch.
  all: (let n := numgoals in idtac "ZZN after fetch:" n).
Admitted.
