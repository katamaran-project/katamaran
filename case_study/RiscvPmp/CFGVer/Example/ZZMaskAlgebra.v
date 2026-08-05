(* ========================================================================= *)
(* ZZMaskAlgebra.v — THROWAWAY demo (delete after use).                       *)
(*                                                                           *)
(* Exercises ALL FOUR expand-homomorphism peval rules in one term.  Forms two *)
(* independent constant-time masks and combines them with and / or / xor:      *)
(*                                                                           *)
(*   a2 = mask(a0 == 0)      snez a2,a0 ; addi a2,a2,-1                       *)
(*   a3 = mask(a1 == 0)      snez a3,a1 ; addi a3,a3,-1                       *)
(*   a4 = ((a2 & a3) | a2) ^ a3                                              *)
(*                                                                           *)
(* Without the rules a4 is a bvand/bvor/bvxor tree over two 5-node arithmetic *)
(* mask chains.  With them it must collapse to ONE `uop.expand` node over a   *)
(* boolean formula, with every mask operation pushed into the bool layer.      *)
(*                                                                           *)
(* Registers are public+symbolic for the same reason as ZZExpandDump.v: the    *)
(* final BNE is only an OBSERVATION instrument (masks are unobservable by      *)
(* design), and branching needs a public condition.  Publicness does not       *)
(* affect term SHAPE — it only adds the formula_secLeak hypotheses.            *)
(* ========================================================================= *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
Import SymProp.notations.
Set Printing Depth 100000.
Set Printing Width 200.

Definition zzma_instrs : list AST :=
  [ RTYPE A0 X0 A2 RISCV_SLTU              (* snez a2, a0     *)
  ; ITYPE (bv.of_Z (-1)) A2 A2 RISCV_ADDI  (* addi a2, a2, -1 *)
  ; RTYPE A1 X0 A3 RISCV_SLTU              (* snez a3, a1     *)
  ; ITYPE (bv.of_Z (-1)) A3 A3 RISCV_ADDI  (* addi a3, a3, -1 *)
  ; RTYPE A3 A2 A4 RISCV_AND               (* and  a4, a2, a3   -> rule 2 *)
  ; RTYPE A2 A4 A4 RISCV_OR                (* or   a4, a4, a2   -> rule 3 *)
  ; RTYPE A3 A4 A4 RISCV_XOR               (* xor  a4, a4, a3   -> rule 4 *)
  ; BNE A4 X0 (bv.of_N 8)                  (* bne  a4, x0, +8 -> exit *)
  ; NOP
  ].

Definition zzma_reg_specs : list reg_spec :=
  [(A0, true, None); (A1, true, None); (A2, true, None);
   (A3, true, None); (A4, true, None)].

Definition zzma_contract (ia : N) : @CFGVerifierContract ["p" :: ty_xlenbits] :=
  gen_contract_param ia zzma_reg_specs [] zzma_instrs []
    (pcOutOfInstrs_exitCond ia zzma_instrs) 14.

Eval vm_compute in
  (cfg_map (zzma_contract 0) (fun ia p exits P i ec fl =>
     postprocess (CFG_VC_triple p exits P i fl))).
