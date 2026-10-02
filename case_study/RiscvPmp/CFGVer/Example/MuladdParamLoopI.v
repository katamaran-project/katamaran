(* Example/MuladdParamLoopI.v -- loop I (ZZArrIA.v) on the n-only template MuladdParamLoopN.v
   (promoted 2026-10-02 from the ZZ probes, 2026-09-30).  Instructions and scratch copied from ZZArrIA.v. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.MuladdParamClose.
From Katamaran Require Import RiscvPmp.CFGVer.Example.MuladdParamLoopN.

Definition k_mask31 : Val ty_xlenbits := bv.of_N 2147483647.

Definition k_instrs : list AST :=
  [ LOAD (bv.of_Z 0) A7 T2 false WORD
  ; MULHU T3 T2 T0
  ; MUL T4 T2 T0
  ; RTYPE A6 T4 A6 RISCV_ADD
  ; RTYPE T4 A6 T4 RISCV_SLTU
  ; RTYPE T4 T3 T3 RISCV_ADD
  ; SHIFTIOP (bv.of_Z 1) T3 T3 RISCV_SLLI
  ; LOAD (bv.of_Z 0) A1 T4 false WORD
  ; SHIFTIOP (bv.of_Z 31) A6 T5 RISCV_SRLI
  ; RTYPE T3 T5 T3 RISCV_OR
  ; RTYPE A3 A6 A6 RISCV_AND
  ; RTYPE A6 T4 T4 RISCV_SUB
  ; SHIFTIOP (bv.of_Z 31) T4 A6 RISCV_SRLI
  ; RTYPE T3 A6 A6 RISCV_ADD
  ; RTYPE A3 T4 T3 RISCV_AND
  ; STORE (bv.of_Z 0) T3 A1 WORD
  ; RTYPE T3 T2 T4 RISCV_XOR
  ; ITYPE (bv.of_Z 1) T4 T4 RISCV_SLTIU
  ; RTYPE T3 T2 T3 RISCV_SUB
  ; ITYPE (bv.of_Z (-1)) T2 T2 RISCV_XORI
  ; RTYPE T2 T3 T2 RISCV_AND
  ; SHIFTIOP (bv.of_Z 31) T2 T2 RISCV_SRLI
  ; RTYPE T4 X0 T3 RISCV_SUB
  ; RTYPE A5 T2 A5 RISCV_XOR
  ; RTYPE T3 A5 A5 RISCV_AND
  ; RTYPE T2 A5 A5 RISCV_XOR
  ; ITYPE (bv.of_Z 4) A1 A1 RISCV_ADDI
  ; ITYPE (bv.of_Z 4) A7 A7 RISCV_ADDI
  ; BTYPE (bv.of_Z (-112)) T1 A1 RISCV_BNE ].

Definition k_scratch {Σ} : Assertion Σ :=
  ( A3 ↦ᵣ term_val ty_xlenbits k_mask31
    ∗ asn.exist "v0" ty_xlenbits (T0 ↦ᵣ term_var "v0")   (* q, secret *)
    ∗ asn.exist "v6" ty_xlenbits (A6 ↦ᵣ term_var "v6")   (* cc *)
    ∗ asn.exist "v5" ty_xlenbits (A5 ↦ᵣ term_var "v5")   (* tb *)
    ∗ asn.exist "v2" ty_xlenbits (T2 ↦ᵣ term_var "v2")
    ∗ asn.exist "v3" ty_xlenbits (T3 ↦ᵣ term_var "v3")
    ∗ asn.exist "v4" ty_xlenbits (T4 ↦ᵣ term_var "v4")
    ∗ asn.exist "v7" ty_xlenbits (T5 ↦ᵣ term_var "v7") )%asn.

Definition lnIN : LoopN :=
  MkLoopN A1 A7 T1 true k_instrs 15 116 40.

Lemma valid_in : cfg_vc (lnRec lnIN (@k_scratch)) (ln_annot lnIN (@k_scratch)).
Proof. Time solve_mb_vc. Qed.
