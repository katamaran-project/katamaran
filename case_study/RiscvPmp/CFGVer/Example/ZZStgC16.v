From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZQ.
Lemma stgc_16 : ValidCFGVerifierContract (zzc_contract 16).
Proof.
  intros.
  Time vm_compute.
  Time solve_vc.
  all: (let g := numgoals in idtac "CONC N=16 goals after solve_vc:" g).
Time Qed.
