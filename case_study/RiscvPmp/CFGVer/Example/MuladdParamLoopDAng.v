(* ========================================================================= *)
(* Example/MuladdParamLoopDAng.v -- PARAMETRIC-mlen line: loop D with its ENTRY chunks  *)
(* (source array, destination cell) matched ANGELICALLY .    *)
(* A caller at symbolic mlen names these addresses in the code's other         *)
(* syntactic form (masked count), so a precise match would miss them; the      *)
(* angelic one leaves the equality to the caller's closer.  Here: does the     *)
(* LOOP's own VC (its re-entry) still close?                                   *)
(* ========================================================================= *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.MuladdParamLoopD.
From Katamaran Require Import RiscvPmp.CFGVer.Example.MuladdParamClose.

(* The MOVED array walks UP (stride 4): its END T is fixed (one past the
   first destination, x[mlen] + 4 for a caller) and it grows at its START,
   which is always the last destination written, by add_first after each
   store.  A caller then reaches x[mlen], x[mlen-1] by take_last, and every
   x array downstream (the loops I, K, M) walks up too.

   `dp` here is the SOURCE start (the next destination is dp + 4), bound
   FIRST by the angelic source-array match, and the registers are checked
   against it afterwards.  A caller computes S0 and T6 from the MASKED count
   `(mlen - 1) & 0x3fffffff`, but names the arrays unmasked; binding from the
   registers would carry the masked spelling into everything D hands back,
   so every later read would miss its cell.  This way the mismatch is two
   residual equalities at the entry, once. *)
Definition d_inv_ang : Assertion (dCtx ▻ "a"∷ty_xlenbits) :=
  ( asn.chunk_angelic (chunk_user (arr false (-4))
        [term_var "dp"; term_var "c"; term_var "E"])
    ∗ S0 ↦ᵣ t_off (term_var "dp") 4 ∗ secLeakvar "dp"
    ∗ T6 ↦ᵣ term_var "c" ∗ secLeakvar "c" ∗ asn_ne0 (term_var "c")
    ∗ asn.exist "v1" ty_xlenbits (S1 ↦ᵣ term_var "v1")
    ∗ asn.exist "v2" ty_xlenbits (S2 ↦ᵣ term_var "v2")
    ∗ asn.exist "w" ty_xlenbits
        (asn.chunk_angelic (chunk_user (ptstomem bytes_per_word)
           [t_off (term_var "dp") 4; term_var "w"]))
    ∗ asn_in_range (t_off (term_var "dp") 4)
    ∗ asn.chunk_angelic (chunk_user (arr false 4)
        [t_off (term_var "dp") 8; term_var "k"; term_var "T"])
    (* an array's count is public (interp_arr is False otherwise); stated,
       so the post's exact count k + c is arithmetic on public values *)
    ∗ secLeakvar "k" )%asn.

Definition d_post_ang
    : Assertion (dCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( asn.exist "g" ty_xlenbits
      ( asn.chunk_angelic (chunk_user (arr false (-4))
          [term_var "g"; term_val ty_xlenbits bv.zero; term_var "E"])
        ∗ S0 ↦ᵣ t_off (term_var "g") 4
        ∗ T6 ↦ᵣ term_val ty_xlenbits bv.zero
        ∗ asn.exist "w" ty_xlenbits (t_off (term_var "g") 4 ↦ₘ term_var "w")
        (* the count EXACTLY: moved so far + still to move, which a
           re-entry preserves; a caller gets 0 + its source count *)
        ∗ asn_arr false 4 (t_off (term_var "g") 8)
            (term_binop bop.bvadd (term_var "k") (term_var "c")) (term_var "T")
        ∗ asn.exist "v1" ty_xlenbits (S1 ↦ᵣ term_var "v1")
        ∗ asn.exist "v2" ty_xlenbits (S2 ↦ᵣ term_var "v2") ) )%asn.

Definition dAngRec : @CFGVerifierContract dCtx :=
  gen_seg_contract (term_var "q") (term_var "q") d_instrs 24 10 [] d_inv_ang d_post_ang.
Definition dAngBlk : BlkAnnot := {| blk_ctx := dCtx ; blk_contract := dAngRec |}.

Definition d_ang_annot_with (blk : BlkAnnot) : list AnnotInstr :=
  [ {| ai_ghost_before := [AnnotCLemma (clem_arr_take_first false (-4))]
     ; ai_instr        := LOAD (bv.of_Z (-4)) S0 S1 false WORD
     ; ai_ghost_after  := []
     ; ai_block        := None
     ; ai_loop         := Some blk |}
  ; AST_AnnotInstr (ITYPE (bv.of_Z (-1)) T6 T6 RISCV_ADDI)
  ; AST_AnnotInstr (ITYPE (bv.of_Z (-4)) S0 S2 RISCV_ADDI)
  ; {| ai_ghost_before := []
     ; ai_instr        := STORE (bv.of_Z 0) S1 S0 WORD
     ; ai_ghost_after  := [AnnotCLemma (clem_arr_add_first false 4)]
     ; ai_block        := None
     ; ai_loop         := None |}
  ; AST_AnnotInstr (ITYPE (bv.of_Z 0) S2 S0 RISCV_ADDI)
  ; AST_AnnotInstr (BTYPE (bv.of_Z (-20)) X0 T6 RISCV_BNE) ].

(* Two private stride -4 arrays are in the heap, so take_first's angelic
   match has two candidates: the left (the done array) needs k <> 0 and
   dies; the right (the sources) leaves only the benign `secLeak false`
   literal that solve_vc cannot reach under the angelic choice. *)
Lemma valid_d_ang_rec : cfg_vc dAngRec (d_ang_annot_with dAngBlk).
Proof. Time solve_mb_vc. Qed.
