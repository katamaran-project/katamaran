(* Example/MuladdParamVC.v -- (on D0N + the n-only tail) the whole-function VC at symbolic mlen, cut at the
   mblr merge (probe). *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.Example.MuladdParamClose.
From Katamaran Require Import RiscvPmp.CFGVer.Example.MuladdParam.

Lemma valid_sym6 : cfg_vc sym6 sym6_annot.
Proof.
  Time solve_mb_vc.
  (* witnesses of ∃s in dead branches (refuted from their hypotheses) are
     never fixed; any value will do *)
  Unshelve. all: exact (ty.SyncVal bv.zero).
Qed.
