(* ========================================================================= *)
(* Example/CheckScalar/CheckScalarParamLoop2.v -- check_scalar's loop 2,     *)
(* `c |= -EQ0(c) & CMP(k[u], P256_N[u])` (cs_instrs 20..32), as a loop      *)
(* block over BYTES: k and P256_N walked in lockstep, both `arr false 1 1`,    *)
(* latched on P256_N's end.  The read bytes are left as cells (dropped).    *)
(*                                                                           *)
(* Both arrays have the same predicate, so each take_first sits right       *)
(* before ITS load: a take from the wrong array leaves the load without its *)
(* cell, and that angelic branch dies at once.                               *)
(* ========================================================================= *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamClose.
From Katamaran Require Import RiscvPmp.CFGVer.Example.CheckScalar.CheckScalarParamLoop1.

(* The PARAMETERS: the code base and the two arrays' ends.  The count n
   changes, so it is existential in the invariant (PLAN-loop-rule.md, L2);
   the post needs no total, both arrays being walked to their fixed ends. *)
Definition l2Ctx : LCtx :=
  ["q"∷ty_xlenbits; "eK"∷ty_xlenbits; "eN"∷ty_xlenbits].

Definition l2_instrs : list AST :=
  [ LOAD (bv.of_Z 0) A0 A5 true BYTE
  ; LOAD (bv.of_Z 0) A1 A6 true BYTE
  ; RTYPE A5 A6 A7 RISCV_SLTU
  ; RTYPE A6 A5 A5 RISCV_SLTU
  ; RTYPE A5 X0 A5 RISCV_SUB
  ; RTYPE A7 A5 A5 RISCV_OR
  ; RTYPE A3 X0 A6 RISCV_SLTU
  ; ITYPE (bv.of_Z (-1)) A6 A6 RISCV_ADDI
  ; RTYPE A5 A6 A5 RISCV_AND
  ; RTYPE A3 A5 A3 RISCV_OR
  ; ITYPE (bv.of_Z 1) A1 A1 RISCV_ADDI
  ; ITYPE (bv.of_Z 1) A0 A0 RISCV_ADDI
  ; BTYPE (bv.of_Z (-48)) A4 A1 RISCV_BNE ].

Definition l2_state {Σ} (cnt eK eN : Term Σ ty_xlenbits) : Assertion Σ :=
  ( cs_arr_ang false 1 1 (bk eK cnt 0) cnt eK
    ∗ cs_arr_ang false 1 1 (bk eN cnt 0) cnt eN
    ∗ A0 ↦ᵣ bk eK cnt 0
    ∗ A1 ↦ᵣ bk eN cnt 0
    ∗ A4 ↦ᵣ eN )%asn.

Definition l2_scratch {Σ} : Assertion Σ :=
  ( asn.exist "c" ty_xlenbits (A3 ↦ᵣ term_var "c")      (* c, secret *)
    ∗ asn.exist "v5" ty_xlenbits (A5 ↦ᵣ term_var "v5")
    ∗ asn.exist "v6" ty_xlenbits (A6 ↦ᵣ term_var "v6")
    ∗ asn.exist "v7" ty_xlenbits (A7 ↦ᵣ term_var "v7") )%asn.

Definition l2_inv : Assertion (l2Ctx ▻ "a"∷ty_xlenbits) :=
  ( asn.exist "n" ty_xlenbits
      ( l2_state (term_var "n") (term_var "eK") (term_var "eN")
        ∗ secLeakvar "n"
        ∗ asn.formula (formula_relop bop.neq (term_var "n") (term_val ty_xlenbits bv.zero))
        ∗ asn.formula (formula_relop bop.bvult (term_var "n")
            (term_val ty_xlenbits (bv.of_N 0x40000000))))
    ∗ secLeakvar "eK" ∗ secLeakvar "eN"
    ∗ l2_scratch )%asn.

Definition l2_post : Assertion (l2Ctx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( asn.exist "r" ty_xlenbits
      ( l2_state (term_var "r") (term_var "eK") (term_var "eN")
        ∗ asn.formula (formula_propeq (term_var "r") (term_val ty_xlenbits bv.zero))
        ∗ l2_scratch ))%asn.

Definition l2Rec : @CFGVerifierContract l2Ctx :=
  gen_seg_contract (term_var "q") (term_var "q") l2_instrs 52 30 [] l2_inv l2_post.
Definition l2Blk : BlkAnnot := {| blk_ctx := l2Ctx ; blk_contract := l2Rec |}.

Definition l2_annot : list AnnotInstr :=
  match l2_instrs with
  | cons i0 (cons i1 rest) =>
      cons {| ai_ghost_before := [ AnnotCLemma (clem_arr_take_first false 1 1) ]
            ; ai_instr := i0 ; ai_ghost_after := []
            ; ai_block := None |}
        (cons {| ai_ghost_before := [ AnnotCLemma (clem_arr_take_first false 1 1) ]
               ; ai_instr := i1 ; ai_ghost_after := []
               ; ai_block := None |}
           (List.map AST_AnnotInstr rest))
  | _ => nil
  end.

Lemma valid_l2 : cfg_vc_loop l2Rec l2_annot.
Proof. Time solve_mb_vc. Qed.
