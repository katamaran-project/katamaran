(* ========================================================================= *)
(* Example/Muladd/MuladdParamLoopD0.v -- ZZArrD0.v (muladd's second memmove on the mblr = 0   *)
(* path, idx 113-117) restated with the REMAINING COUNT `c` as its varying    *)
(* logic variable (promoted 2026-10-02 from the ZZ probes, 2026-10-01).  Every address is written    *)
(* from the FIXED end t0 (the source array ends at t0 - 4) and c:             *)
(*   source start     dp = t0 + 4c - 4     (stride -4, c elements)            *)
(*   destination        T1 = t0 + 4c                                          *)
(* so the pointer/count relation the loop's pointer-compare exit needs is     *)
(* stated in the invariant, and no arr chunk has to supply it.  The post is   *)
(* phrased in the remaining count c' at exit (bound to c - 1 by the angelic   *)
(* source match) with c' = 0 a pure obligation, as in MuladdParamLoopN.v.           *)
(* ========================================================================= *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamLoopD.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamClose.

Definition d0_instrs : list AST :=
  [ LOAD (bv.of_Z (-4)) T1 T2 false WORD
  ; ITYPE (bv.of_Z (-4)) T1 T3 RISCV_ADDI
  ; STORE (bv.of_Z 0) T2 T1 WORD
  ; ITYPE (bv.of_Z 0) T3 T1 RISCV_ADDI
  ; BTYPE (bv.of_Z (-16)) T0 T3 RISCV_BNE ].

Definition d0Ctx : LCtx :=
  ["q"∷ty_xlenbits; "t0"∷ty_xlenbits; "c"∷ty_xlenbits; "k"∷ty_xlenbits;
   "T"∷ty_xlenbits].

(* t0 + 4 * cnt + off *)
Definition d0_at {Σ} (t0 cnt : Term Σ ty_xlenbits) (off : Z) : Term Σ ty_xlenbits :=
  term_binop bop.bvadd t0
    (term_binop bop.bvadd
       (term_binop bop.bvmul (term_val ty_xlenbits (bv.of_Z 4)) cnt)
       (term_val ty_xlenbits (bv.of_Z off))).

Definition d0_inv : Assertion (d0Ctx ▻ "a"∷ty_xlenbits) :=
  ( (* t0 FIRST, bare, from its register *)
    T0 ↦ᵣ term_var "t0" ∗ secLeakvar "t0"
    (* the source array: its angelic match binds c *)
    ∗ asn.chunk_angelic (chunk_user (arr false (-4))
        [d0_at (term_var "t0") (term_var "c") (-4); term_var "c"; t_off (term_var "t0") (-4)])
    ∗ T1 ↦ᵣ d0_at (term_var "t0") (term_var "c") 0
    ∗ asn.exist "v2" ty_xlenbits (T2 ↦ᵣ term_var "v2")
    ∗ asn.exist "v3" ty_xlenbits (T3 ↦ᵣ term_var "v3")
    ∗ asn.exist "w" ty_xlenbits
        (asn.chunk_angelic (chunk_user (ptstomem bytes_per_word)
           [d0_at (term_var "t0") (term_var "c") 0; term_var "w"]))
    ∗ asn_in_range (d0_at (term_var "t0") (term_var "c") 0)
    ∗ asn.chunk_angelic (chunk_user (arr false 4)
        [d0_at (term_var "t0") (term_var "c") 4; term_var "k"; term_var "T"])
    (* counts are public (an arr's count must be, interp_arr is False otherwise) *)
    ∗ secLeakvar "c" ∗ secLeakvar "k"
    ∗ asn.formula (formula_relop bop.neq (term_var "c") (term_val ty_xlenbits bv.zero))
    ∗ asn.formula (formula_relop bop.bvult (term_var "c")
        (term_val ty_xlenbits (bv.of_N 0x40000000))) )%asn.

Definition d0_post : Assertion (d0Ctx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( asn.exist "c'" ty_xlenbits
      ( (* the remaining source, matched angelically: binds c' := c - 1 *)
        asn.chunk_angelic (chunk_user (arr false (-4))
          [d0_at (term_var "t0") (term_var "c'") (-4); term_var "c'"; t_off (term_var "t0") (-4)])
        (* ... and it is empty: arithmetic, for the closer *)
        ∗ asn.formula (formula_propeq (term_var "c'") (term_val ty_xlenbits bv.zero))
        ∗ T1 ↦ᵣ d0_at (term_var "t0") (term_var "c'") 0
        ∗ T0 ↦ᵣ term_var "t0"
        ∗ asn.exist "w" ty_xlenbits
            (d0_at (term_var "t0") (term_var "c'") 0 ↦ₘ term_var "w")
        (* the count exactly: moved so far + still to move, which a re-entry
           preserves; a caller gets 0 + its source count *)
        ∗ asn_arr false 4 (d0_at (term_var "t0") (term_var "c'") 4)
            (term_binop bop.bvadd (term_var "k") (term_var "c")) (term_var "T")
        ∗ asn.exist "v2" ty_xlenbits (T2 ↦ᵣ term_var "v2")
        ∗ asn.exist "v3" ty_xlenbits (T3 ↦ᵣ term_var "v3") ))%asn.

Definition d0Rec : @CFGVerifierContract d0Ctx :=
  gen_seg_contract (term_var "q") (term_var "q") d0_instrs 20 10 [] d0_inv d0_post.
Definition d0Blk : BlkAnnot := {| blk_ctx := d0Ctx ; blk_contract := d0Rec |}.

Definition d0_annot_with (blk : BlkAnnot) : list AnnotInstr :=
  [ {| ai_ghost_before := [ AnnotCLemma (clem_arr_take_first false (-4)) ]
     ; ai_instr        := LOAD (bv.of_Z (-4)) T1 T2 false WORD
     ; ai_ghost_after  := []
     ; ai_block        := None
     ; ai_loop         := Some blk |}
  ; AST_AnnotInstr (ITYPE (bv.of_Z (-4)) T1 T3 RISCV_ADDI)
  ; {| ai_ghost_before := []
     ; ai_instr        := STORE (bv.of_Z 0) T2 T1 WORD
     ; ai_ghost_after  := [AnnotCLemma (clem_arr_add_first false 4)]
     ; ai_block        := None
     ; ai_loop         := None |}
  ; AST_AnnotInstr (ITYPE (bv.of_Z 0) T3 T1 RISCV_ADDI)
  ; AST_AnnotInstr (BTYPE (bv.of_Z (-16)) T0 T3 RISCV_BNE) ].

Lemma valid_d0_rec : cfg_vc d0Rec (d0_annot_with d0Blk).
Proof. Time solve_mb_vc. Qed.
