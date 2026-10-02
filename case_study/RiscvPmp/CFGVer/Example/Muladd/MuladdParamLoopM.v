(* Example/Muladd/MuladdParamLoopM.v -- loop M (ZZArrMA.v), via the template -- must agree with ZZArrMN.v on the n-only template MuladdParamLoopN.v
   (promoted 2026-10-02 from the ZZ probes, 2026-09-30).  Instructions and scratch copied from ZZArrMA.v. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamClose.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamLoopN.

Definition k_mask31 : Val ty_xlenbits := bv.of_N 2147483647.

Definition k_instrs : list AST :=
  [ LOAD (bv.of_Z 0) A0 A5 false WORD
  ; LOAD (bv.of_Z 0) A4 A6 false WORD
  ; RTYPE T1 A5 T1 RISCV_ADD
  ; RTYPE A6 T1 A6 RISCV_SUB
  ; SHIFTIOP (bv.of_Z 31) A6 T1 RISCV_SRAI
  ; RTYPE A3 A6 A6 RISCV_AND
  ; RTYPE A5 A6 A6 RISCV_XOR
  ; RTYPE A1 A6 A6 RISCV_AND
  ; RTYPE A5 A6 A5 RISCV_XOR
  ; STORE (bv.of_Z 0) A5 A0 WORD
  ; ITYPE (bv.of_Z 4) A4 A4 RISCV_ADDI
  ; ITYPE (bv.of_Z 4) A0 A0 RISCV_ADDI
  ; BTYPE (bv.of_Z (-48)) A2 A4 RISCV_BNE ].

Definition k_scratch {Σ} : Assertion Σ :=
  ( A3 ↦ᵣ term_val ty_xlenbits k_mask31
    ∗ asn.exist "v1" ty_xlenbits (T1 ↦ᵣ term_var "v1")
    ∗ asn.exist "v2" ty_xlenbits (A1 ↦ᵣ term_var "v2")
    ∗ asn.exist "v3" ty_xlenbits (A5 ↦ᵣ term_var "v3")
    ∗ asn.exist "v4" ty_xlenbits (A6 ↦ᵣ term_var "v4") )%asn.

Definition lnMT : LoopN :=
  MkLoopN A0 A4 A2 false k_instrs 9 52 20.

Lemma valid_mt : cfg_vc (lnRec lnMT (@k_scratch)) (ln_annot lnMT (@k_scratch)).
Proof. Time solve_mb_vc. Qed.
