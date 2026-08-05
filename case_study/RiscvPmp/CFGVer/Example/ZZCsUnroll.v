(* ========================================================================= *)
(* ZZCsUnroll.v — THROWAWAY demo (delete after use).                          *)
(*                                                                           *)
(* The REAL check_scalar body (`check_scalar_instrs`, imported, not copied),   *)
(* straight-line unrolled 1x and 2x, with the accumulator made observable.     *)
(* Two things to read off:                                                    *)
(*                                                                           *)
(*  (1) the mask idiom inside the real 16 instructions is canonicalized to a   *)
(*      single `uop.expand` node over one relop;                              *)
(*  (2) the ACCUMULATOR DOUBLES: A0 occurs twice per copy, so counting         *)
(*      `uop.expand` occurrences in the dumped formula goes 1 -> 3 from one    *)
(*      copy to two (copy 2's own mask, plus two copies of copy 1's term).     *)
(*      That is the 2^N wall `coalesce` is meant to collapse to O(N).          *)
(*                                                                           *)
(* Between copies A1/A2 are restored from A6/A7, because the body clobbers     *)
(* them as scratch — in the real loop they are reloaded from k[u]/P256_N[u].    *)
(* The trailing BNE is an observation instrument only (see ZZExpandDump.v);    *)
(* publicness affects the secLeak hypotheses, not term shape.                  *)
(* ========================================================================= *)
(* Export, not Import: the ZZCsRun* runners need Prelude's notations (SymProp,
   the N numeral scope) — the Require-vs-Require-Import landmine ZZCommon.v
   documents. *)
From Katamaran Require Export RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.Example.BearSSLCheckScalar.
Import SymProp.notations.
(* Required: RiscvPmp.Sig re-imports ctx.notations, which hijacks `::` and `++`
   for Term-level lists — the same trap Tables.v documents. *)
Open Scope list_scope.
Set Printing Depth 100000.
Set Printing Width 200.

(* mv a1, a6 ; mv a2, a7 *)
Definition zzcs_reload : list AST :=
  [ ITYPE (bv.of_Z 0) A6 A1 RISCV_ADDI
  ; ITYPE (bv.of_Z 0) A7 A2 RISCV_ADDI ].

Definition zzcs_observe : list AST :=
  [ BNE A0 X0 (bv.of_N 8) ; NOP ].

Definition zzcs_instrs (copies : nat) : list AST :=
  List.concat (List.repeat (zzcs_reload ++ check_scalar_instrs) copies)
  ++ zzcs_observe.

Definition zzcs_reg_specs : list reg_spec :=
  [(A0, true, None); (A1, true, None); (A2, true, None); (A3, true, None);
   (A4, true, None); (A5, true, None); (A6, true, None); (A7, true, None)].

Definition zzcs_contract (copies : nat) (ia : N)
  : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_param ia zzcs_reg_specs [] (zzcs_instrs copies) []
    (pcOutOfInstrs_exitCond ia (zzcs_instrs copies))
    (30 + 20 * copies).
