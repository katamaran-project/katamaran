(* Example/Muladd/MuladdParamTailVC.v -- the tail block's own VC (probe). *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamClose.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamTail.

Lemma valid_tail : cfg_vc tailRec tail_annot.
Proof.
  Time solve_mb_vc.
  (* witnesses of ∃s in dead branches (refuted from their hypotheses) are
     never fixed; any value will do *)
  Unshelve. all: exact (ty.SyncVal bv.zero).
Qed.
