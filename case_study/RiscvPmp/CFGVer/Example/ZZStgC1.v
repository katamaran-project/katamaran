From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZQ.
Lemma stgc_1 : ValidCFGVerifierContract (zzc_contract 1).
Proof.
  intros.
  Time vm_compute.
  Time solve_vc.
  all: (let g := numgoals in idtac "CONC N=1 goals after solve_vc:" g).
Time Qed.
