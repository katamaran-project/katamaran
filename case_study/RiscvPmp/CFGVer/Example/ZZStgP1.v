From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZQ.
Lemma stgp_1 : ValidCFGVerifierContract (zzn_contract 1).
Proof.
  intros.
  Time vm_compute.
  Time solve_vc.
  all: (let g := numgoals in idtac "PARAM N=1 goals after solve_vc:" g).
  Time (all: solve_symbase_fetch).
Time Qed.
