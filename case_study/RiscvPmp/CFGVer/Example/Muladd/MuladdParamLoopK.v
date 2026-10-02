(* Example/Muladd/MuladdParamLoopK.v -- loop K (ZZArrKA.v) on the n-only template MuladdParamLoopN.v
   (promoted 2026-10-02 from the ZZ probes, 2026-09-30).  Instructions and scratch copied from ZZArrKA.v. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamClose.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamLoopN.

Definition k_mask31 : Val ty_xlenbits := bv.of_N 2147483647.

Definition k_instrs : list AST :=
  [ LOAD (bv.of_Z 0) T6 S1 false WORD
  ; LOAD (bv.of_Z 0) T5 S2 false WORD
  ; RTYPE T3 S1 T3 RISCV_ADD
  ; RTYPE S2 T3 S2 RISCV_ADD
  ; SHIFTIOP (bv.of_Z 31) S2 T3 RISCV_SRLI
  ; RTYPE A3 S2 S2 RISCV_AND
  ; RTYPE S1 S2 S2 RISCV_XOR
  ; RTYPE T4 S2 S2 RISCV_AND
  ; RTYPE S1 S2 S1 RISCV_XOR
  ; STORE (bv.of_Z 0) S1 T6 WORD
  ; ITYPE (bv.of_Z 4) T5 T5 RISCV_ADDI
  ; ITYPE (bv.of_Z 4) T6 T6 RISCV_ADDI
  ; BTYPE (bv.of_Z (-48)) S0 T5 RISCV_BNE ].

Definition k_scratch {Σ} : Assertion Σ :=
  ( A3 ↦ᵣ term_val ty_xlenbits k_mask31
    ∗ asn.exist "v3" ty_xlenbits (T3 ↦ᵣ term_var "v3")
    ∗ asn.exist "v4" ty_xlenbits (T4 ↦ᵣ term_var "v4")
    ∗ asn.exist "v1" ty_xlenbits (S1 ↦ᵣ term_var "v1")
    ∗ asn.exist "v2" ty_xlenbits (S2 ↦ᵣ term_var "v2") )%asn.

Definition lnKN : LoopN :=
  MkLoopN T6 T5 S0 false k_instrs 9 52 20.

Lemma valid_kn : cfg_vc (lnRec lnKN (@k_scratch)) (ln_annot lnKN (@k_scratch)).
Proof. Time solve_mb_vc. Qed.
