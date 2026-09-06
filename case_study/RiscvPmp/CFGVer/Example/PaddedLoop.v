(* ========================================================================= *)
(* Example/PaddedLoop.v -- SUB-TABLE segment contracts (light half).          *)
(*                                                                           *)
(* THE REGRESSION TEST FOR itable_faith_of_segment.  This is the only proof  *)
(* in the tree where a contract's instruction table covers a PROPER SUBSET   *)
(* of the program, so if the sub-table path breaks, it breaks here.          *)
(*                                                                           *)
(* Same countdown loop as Example/CountdownComposed.v, but sitting INSIDE a  *)
(* 66-instruction program: 64 never-executed filler instructions, then the   *)
(* loop at byte offset 256.  Both segment contracts carry ONLY the two       *)
(* instructions the segment executes; the segment's byte offset lives in the *)
(* PLACEMENT term (bv.of_N 256) rather than as a 64-entry prefix of the      *)
(* table, so table_of_list p 0 pl_seg emits exactly addresses 256 and 260.   *)
(* No new field on CFGVerifierContract was needed for this.                  *)
(*                                                                           *)
(* WHY (diagnostics/prefix-length-cost.md): a segment contract whose branch  *)
(* condition the solver cannot decide by computation costs                    *)
(* 93.81 + 4.05*P + 0.531*P^2 M words in the number P of NEVER-EXECUTED      *)
(* instructions sharing its table (held out at P=64 to +0.0024% and at       *)
(* P=128 to +0.0079%).  Measured here: this cut costs 177.21 M against       *)
(* 177.96 M for the IDENTICAL cut in a 2-instruction program -- 0.42%        *)
(* CHEAPER -- where the same cut with untrimmed tables would cost ~5053 M.   *)
(* So program length is now free for a composed proof; it was 28.5x.          *)
(*                                                                           *)
(* Soundness is Tables.v's instrs_of_list_segment (three gmap containments)  *)
(* plus TablesRel.v's itable_faith_of_segment; used in PaddedLoopResult.v,   *)
(* whose pl_loop is gate-checked axiom-clean.                                *)
(* ========================================================================= *)

From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Export RiscvPmp.CFGVer.Example.CountdownComposed.

(* 64 never-executed filler instructions in front of the loop. *)
Definition pl_filler : list AST := List.repeat (MV X4 X4) 64.

(* The whole program: 66 instructions, loop head at byte offset 256. *)
Definition padded_instrs : list AST := pl_filler ++ cd_instrs.

(* AnnotInstr-level decomposition of the SAME program.
   Needed because `list_AST_AnnotInstr` is `List.map AST_AnnotInstr`, NOT an
   identity (Verifier.v:145 -- and coqc warns about exactly that), so a
   `list AST` cannot stand in for the `list AnnotInstr` that ptsto_instrs and
   itable_rel are stated over.  Naming pre/seg/post separately makes
   itable_faith_of_segment's `pre ++ seg ++ post` match SYNTACTICALLY, which
   spares the caller an `app_nil_r` rewrite that would otherwise also hit the
   `seg` occurrence inside table_of_list. *)
Definition pl_pre  : list AnnotInstr := pl_filler.
Definition pl_seg  : list AnnotInstr := cd_instrs.
Definition pl_post : list AnnotInstr := [].
Definition padded_annot : list AnnotInstr := pl_pre ++ pl_seg ++ pl_post.

Definition pl_head : N := 256.

(* exit condition of the CUT: back at the loop head (offset 256). *)
Definition pl_headExitCond : bv xlenbits -> bool :=
  fun v => bv.eqb v (bv.of_N pl_head).

(* ---- LOOP BODY: head -> head, one trip.  cfg_instrs is the SEGMENT. ---- *)
Definition plBody : @CFGVerifierContract cdCtx :=
  @MkCFGVerifierContract cdCtx 0%N
    (term_val ty_xlenbits (bv.of_N pl_head))
    (exits_of_offs (term_val ty_xlenbits (bv.of_N pl_head)) [0%N])
    (asn_init_pc (bv.of_N pl_head)
       ∗ X1 ↦ᵣ term_var "k" ∗ secLeakvar "k"
       ∗ asn.formula (formula_relop bop.neq (dec (term_var "k"))
                        (term_val ty_xlenbits bv.zero)))
    pl_seg
    pl_headExitCond
    3
    (X1 ↦ᵣ dec (term_var "k") ∗ secLeakvar "k" ∗ minimal_pre).

Lemma valid_plBody : ValidCFGVerifierContract plBody.
Proof.
  vm_compute. solve_vc.
Qed.

(* ---- LOOP EXIT: head -> 264 (one past the 66-instruction program). ---- *)
Definition plFinal : @CFGVerifierContract cdCtx :=
  @MkCFGVerifierContract cdCtx 0%N
    (term_val ty_xlenbits (bv.of_N pl_head))
    (exits_of_offs (term_val ty_xlenbits (bv.of_N pl_head)) [8%N])
    (asn_init_pc (bv.of_N pl_head)
       ∗ X1 ↦ᵣ term_var "k" ∗ secLeakvar "k"
       ∗ asn.formula (formula_relop bop.eq (dec (term_var "k"))
                        (term_val ty_xlenbits bv.zero)))
    pl_seg
    (pcOutOfInstrs_exitCond 0 padded_instrs)
    3
    asn_no_post.

Lemma valid_plFinal : ValidCFGVerifierContract plFinal.
Proof.
  vm_compute. solve_vc.
Qed.
