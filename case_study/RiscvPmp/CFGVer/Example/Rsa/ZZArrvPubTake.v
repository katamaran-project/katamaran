(* PROBE (PLAN-arrv O2): does a PLAIN take from a public arrv give public
   parts by the solver alone?  secLeak vs (framed) + vs = x :: r (propeq,
   Leibniz on RelVal) + lifted cons is SyncVal iff both args are. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamClose.

Definition NOP : AST := ITYPE (bv.of_Z 0) X0 X0 RISCV_ADDI.

Definition ptCtx : LCtx :=
  ["q"∷ty_xlenbits; "p"∷ty_xlenbits; "n"∷ty_xlenbits; "e"∷ty_xlenbits; "vs"∷clemv_ty 1].

Definition pt_pre (pub : bool) : Assertion (ptCtx ▻ "a"∷ty_xlenbits) :=
  ( clem_arrv 1 1 (term_var "p") (term_var "n") (term_var "e") (term_var "vs")
    ∗ clem_nonzero (term_var "n")
    ∗ (if pub then secLeakvar "vs" else ⊤) )%asn.

Definition pt_post : Assertion (ptCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( asn.exist "v" (clem_cell_ty 1)
      (clem_ptsto 1 (term_var "p") (term_var "v") ∗ clem_range 1 (term_var "p")
       ∗ asn.formula (formula_secLeak (term_var "v")))
    ∗ asn.exist "r" (clemv_ty 1)
      (clem_arrv 1 1 (clem_off (term_var "p") 1) (clem_off (term_var "n") (-1))
         (term_var "e") (term_var "r")
       ∗ asn.formula (formula_secLeak (term_var "r"))) )%asn.

Definition pt_annot : list AnnotInstr :=
  [ {| ai_ghost_before := [ AnnotCLemma (clem_arrv_take_first 1 1) ]; ai_instr := NOP
     ; ai_ghost_after := []; ai_block := None |} ].

Definition ptRec (pub : bool) : @CFGVerifierContract ptCtx :=
  gen_seg_contract (term_var "q") (term_var "q") [NOP] 4 4 [] (pt_pre pub) pt_post.

Lemma valid_pt : cfg_vc_loop (ptRec true) pt_annot.
Proof. Time solve_mb_vc. Qed.

(* NEGATIVE CONTROL: a secret vs gives no public parts *)
Goal cfg_vc_loop (ptRec false) pt_annot.
Proof. Fail solve_mb_vc. Abort.

(* NON-VACUITY: the public path condition is not inconsistent *)
Goal cfg_vc_loop (gen_seg_contract (term_var "q") (term_var "q") [NOP] 4 4 [] (pt_pre true)
                    (pt_post ∗ asn.formula (formula_relop bop.neq (term_var "p") (term_var "p")))%asn)
                 pt_annot.
Proof. Fail solve_mb_vc. Abort.
