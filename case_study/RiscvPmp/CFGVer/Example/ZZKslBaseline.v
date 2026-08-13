(* ========================================================================= *)
(* Example/ZZKslBaseline.v -- THROWAWAY, imports-only baseline for the        *)
(* allocated_words comparison between ZZKslChunkDistinct.v and               *)
(* ZZKslChunkShared.v.  No Eval, no proof body -- just the shared Prelude     *)
(* import both files pay for, so its allocated_words can be subtracted out.  *)
(* ------------------------------------------------------------------------ *)

From Katamaran Require Export RiscvPmp.CFGVer.Example.Prelude.
