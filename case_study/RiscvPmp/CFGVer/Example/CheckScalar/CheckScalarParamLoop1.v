(* ========================================================================= *)
(* Example/CheckScalar/CheckScalarParamLoop1.v -- check_scalar's loop 1,     *)
(* `z |= k[u]` (cs_instrs 9..12), as a loop block over BYTES, on the shape   *)
(* of Muladd/MuladdParamLoopN.v: the remaining count `n` is the only         *)
(* varying logic variable and every address is END - n.                       *)
(*                                                                           *)
(* k's remaining bytes are an `arrv 1 1` read from its start; each read       *)
(* byte joins a DONE array `arrv 1 (-1)` (grown at its start by add_first),  *)
(* which the caller flips back into k for loop 2.  The two arrays differ in  *)
(* stride, so every angelic array match has one candidate.  Their values    *)
(* are ∃ (PLAN-arrv Phase D): no post of check_scalar mentions them.        *)
(* ========================================================================= *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamClose.

(* The PARAMETERS: what does not change across trips -- the code base q, k's
   end e, the done array's end kE, and the TOTAL byte count T.  The counts n
   (to go) and d (done) change, so they are existential in the invariant
   (PLAN-loop-rule.md, decision L2); T = d + n is what lets the post say how
   many bytes were done. *)
Definition l1Ctx : LCtx :=
  ["q"∷ty_xlenbits; "e"∷ty_xlenbits; "kE"∷ty_xlenbits; "T"∷ty_xlenbits].

(* end - cnt + off *)
Definition bk {Σ} (end_ cnt : Term Σ ty_xlenbits) (off : Z) : Term Σ ty_xlenbits :=
  term_binop bop.bvadd end_
    (term_binop bop.bvadd
       (term_binop bop.bvmul (term_val ty_xlenbits (bv.of_Z (-1))) cnt)
       (term_val ty_xlenbits (bv.of_Z off))).

Definition l1_instrs : list AST :=
  [ LOAD (bv.of_Z 0) A5 A6 true BYTE
  ; ITYPE (bv.of_Z 1) A5 A5 RISCV_ADDI
  ; RTYPE A6 A2 A2 RISCV_OR
  ; BTYPE (bv.of_Z (-12)) A4 A5 RISCV_BNE ].

(* `cnt` bytes still to go (holding rK), `done` read (holding dK) *)
Definition l1_state {Σ} (cnt done e kE : Term Σ ty_xlenbits)
    (rK dK : Term Σ (clemv_ty 1)) : Assertion Σ :=
  ( clem_arrv_angelic 1 1 "vK" (bk e cnt 0) cnt e rK
    ∗ clem_arrv_angelic 1 (-1) "dK" (bk e cnt (-1)) done kE dK
    ∗ A5 ↦ᵣ bk e cnt 0
    ∗ A4 ↦ᵣ e )%asn.

Definition l1_scratch {Σ} : Assertion Σ :=
  ( asn.exist "z" ty_xlenbits (A2 ↦ᵣ term_var "z")      (* z, secret *)
    ∗ asn.exist "v6" ty_xlenbits (A6 ↦ᵣ term_var "v6") )%asn.

Definition l1_inv : Assertion (l1Ctx ▻ "a"∷ty_xlenbits) :=
  ( asn.exist "n" ty_xlenbits (asn.exist "d" ty_xlenbits
    (asn.exist "rK" (clemv_ty 1) (asn.exist "dK" (clemv_ty 1)
      ( l1_state (term_var "n") (term_var "d") (term_var "e") (term_var "kE")
          (term_var "rK") (term_var "dK")
        ∗ secLeakvar "n" ∗ secLeakvar "d"
        ∗ asn.formula (formula_relop bop.neq (term_var "n") (term_val ty_xlenbits bv.zero))
        ∗ asn.formula (formula_relop bop.bvult (term_var "n")
            (term_val ty_xlenbits (bv.of_N 0x40000000)))
        ∗ asn.formula (formula_relop bop.bvult (term_var "d")
            (term_val ty_xlenbits (bv.of_N 0x40000000)))
        ∗ asn.formula (formula_relop bop.bvult
            (term_binop bop.bvadd (term_var "d") (term_var "n"))
            (term_val ty_xlenbits (bv.of_N 0x40000000)))
        ∗ asn.formula (formula_propeq (term_var "T")
            (term_binop bop.bvadd (term_var "d") (term_var "n")))
        (* T public too, AFTER its equation (MuladdParamLoopN.ln_inv): the
           solver eliminates d := T - n, so without it only the compound
           secLeak(T - n) survives and T stays a plain RelVal binder *)
        ∗ secLeakvar "T"))))
    ∗ secLeakvar "e"
    ∗ l1_scratch )%asn.

Definition l1_post : Assertion (l1Ctx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( asn.exist "c" ty_xlenbits
    (asn.exist "rK" (clemv_ty 1) (asn.exist "dK" (clemv_ty 1)
      ( l1_state (term_var "c") (term_var "T") (term_var "e") (term_var "kE")
          (term_var "rK") (term_var "dK")
        ∗ asn.formula (formula_propeq (term_var "c") (term_val ty_xlenbits bv.zero))
        ∗ l1_scratch ))))%asn.

Definition l1Rec : @CFGVerifierContract l1Ctx :=
  gen_seg_contract (term_var "q") (term_var "q") l1_instrs 16 12 [] l1_inv l1_post.
Definition l1Blk : BlkAnnot := {| blk_ctx := l1Ctx ; blk_contract := l1Rec |}.

Definition l1_annot : list AnnotInstr :=
  [ {| ai_ghost_before := [ AnnotCLemma (clem_arrv_take_first 1 1 "vK") ]
     ; ai_instr := LOAD (bv.of_Z 0) A5 A6 true BYTE
     ; ai_ghost_after := [ AnnotCLemma (clem_arrv_add_first 1 (-1) "dK") ]
     ; ai_block := None |}
  ; AST_AnnotInstr (ITYPE (bv.of_Z 1) A5 A5 RISCV_ADDI)
  ; AST_AnnotInstr (RTYPE A6 A2 A2 RISCV_OR)
  ; AST_AnnotInstr (BTYPE (bv.of_Z (-12)) A4 A5 RISCV_BNE) ].

Lemma valid_l1 : cfg_vc_loop l1Rec l1_annot.
Proof. Time solve_mb_vc. Qed.
