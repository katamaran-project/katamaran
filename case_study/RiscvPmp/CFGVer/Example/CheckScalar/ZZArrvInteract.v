(* ZZ probe (not built): the ambiguity x values INTERACTION, measured on
   check_scalar's two loops (PLAN-arrv Phase D, 2026-10-26).  Loop1's arrays
   differ in stride (unambiguous under arr AND arrv); Loop2's two arrays have
   the same shape (ambiguous under both).  Counts (nodes, angelic branches,
   asserts, surviving existentials) of the postprocessed VC, old arr vs new
   arrv. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamClose.
From Katamaran Require RiscvPmp.CFGVer.Example.CheckScalar.CheckScalarParamLoop1.
From Katamaran Require RiscvPmp.CFGVer.Example.CheckScalar.CheckScalarParamLoop2.
Module NewL1 := RiscvPmp.CFGVer.Example.CheckScalar.CheckScalarParamLoop1.
Module NewL2 := RiscvPmp.CFGVer.Example.CheckScalar.CheckScalarParamLoop2.
Module OldL1.

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

Definition cs_arr_ang {Σ} (pub : bool) (w : nat) (s : Z) (a n e : Term Σ ty_xlenbits) : Assertion Σ :=
  asn.chunk_angelic (chunk_user (arr pub w s) [a; n; e]).

Definition l1_instrs : list AST :=
  [ LOAD (bv.of_Z 0) A5 A6 true BYTE
  ; ITYPE (bv.of_Z 1) A5 A5 RISCV_ADDI
  ; RTYPE A6 A2 A2 RISCV_OR
  ; BTYPE (bv.of_Z (-12)) A4 A5 RISCV_BNE ].

(* `cnt` bytes still to go, `done` read *)
Definition l1_state {Σ} (cnt done e kE : Term Σ ty_xlenbits) : Assertion Σ :=
  ( cs_arr_ang false 1 1 (bk e cnt 0) cnt e
    ∗ cs_arr_ang false 1 (-1) (bk e cnt (-1)) done kE
    ∗ A5 ↦ᵣ bk e cnt 0
    ∗ A4 ↦ᵣ e )%asn.

Definition l1_scratch {Σ} : Assertion Σ :=
  ( asn.exist "z" ty_xlenbits (A2 ↦ᵣ term_var "z")      (* z, secret *)
    ∗ asn.exist "v6" ty_xlenbits (A6 ↦ᵣ term_var "v6") )%asn.

Definition l1_inv : Assertion (l1Ctx ▻ "a"∷ty_xlenbits) :=
  ( asn.exist "n" ty_xlenbits (asn.exist "d" ty_xlenbits
      ( l1_state (term_var "n") (term_var "d") (term_var "e") (term_var "kE")
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
            (term_binop bop.bvadd (term_var "d") (term_var "n")))))
    ∗ secLeakvar "e"
    ∗ l1_scratch )%asn.

Definition l1_post : Assertion (l1Ctx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( asn.exist "c" ty_xlenbits
      ( l1_state (term_var "c") (term_var "T") (term_var "e") (term_var "kE")
        ∗ asn.formula (formula_propeq (term_var "c") (term_val ty_xlenbits bv.zero))
        ∗ l1_scratch ))%asn.

Definition l1Rec : @CFGVerifierContract l1Ctx :=
  gen_seg_contract (term_var "q") (term_var "q") l1_instrs 16 12 [] l1_inv l1_post.
Definition l1Blk : BlkAnnot := {| blk_ctx := l1Ctx ; blk_contract := l1Rec |}.

Definition l1_annot : list AnnotInstr :=
  [ {| ai_ghost_before := [ AnnotCLemma (clem_arr_take_first false 1 1) ]
     ; ai_instr := LOAD (bv.of_Z 0) A5 A6 true BYTE
     ; ai_ghost_after := [ AnnotCLemma (clem_arr_add_first false 1 (-1)) ]
     ; ai_block := None |}
  ; AST_AnnotInstr (ITYPE (bv.of_Z 1) A5 A5 RISCV_ADDI)
  ; AST_AnnotInstr (RTYPE A6 A2 A2 RISCV_OR)
  ; AST_AnnotInstr (BTYPE (bv.of_Z (-12)) A4 A5 RISCV_BNE) ].

End OldL1.
Module OldL2.
Import OldL1.

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

End OldL2.
Fixpoint zzcnt {Σ} (p : SymProp.SymProp Σ) : nat * nat * nat * nat :=
  (* (nodes, angelic_binary, assertk, angelicv) *)
  let add4 '(a,b,c,d) '(e,f,g,h) := (Nat.add a e, Nat.add b f, Nat.add c g, Nat.add d h) in
  match p with
  | SymProp.angelic_binary o1 o2 => add4 (1,1,0,0) (add4 (zzcnt o1) (zzcnt o2))
  | SymProp.demonic_binary o1 o2 => add4 (1,0,0,0) (add4 (zzcnt o1) (zzcnt o2))
  | SymProp.assertk _ _ k => add4 (1,0,1,0) (zzcnt k)
  | SymProp.assumek _ k => add4 (1,0,0,0) (zzcnt k)
  | SymProp.angelicv _ k => add4 (1,0,0,1) (zzcnt k)
  | SymProp.demonicv _ k => add4 (1,0,0,0) (zzcnt k)
  | @SymProp.assert_vareq _ _ _ _ _ _ k => add4 (1,0,0,0) (zzcnt k)
  | @SymProp.assume_vareq _ _ _ _ _ k => add4 (1,0,0,0) (zzcnt k)
  | @SymProp.dropk _ _ _ _ k => add4 (1,0,0,0) (zzcnt k)
  | SymProp.debug _ k => add4 (1,0,0,0) (zzcnt k)
  | _ => (1,0,0,0)
  end.


Module CntOldL1.
Import OldL1.
Definition pp := cfg_map l1Rec
  (fun p ex P _ fl Q => cfg_postprocess (CFG_VC_loop_triple p ex P l1_annot fl Q)).
Eval vm_compute in ("CntOldL1", zzcnt pp).
End CntOldL1.

Module CntNewL1.
Import NewL1.
Definition pp := cfg_map NewL1.l1Rec
  (fun p ex P _ fl Q => cfg_postprocess (CFG_VC_loop_triple p ex P NewL1.l1_annot fl Q)).
Eval vm_compute in ("CntNewL1", zzcnt pp).
End CntNewL1.

Module CntOldL2.
Import OldL2.
Definition pp := cfg_map l2Rec
  (fun p ex P _ fl Q => cfg_postprocess (CFG_VC_loop_triple p ex P l2_annot fl Q)).
Eval vm_compute in ("CntOldL2", zzcnt pp).
End CntOldL2.

Module CntNewL2.
Import NewL2.
Definition pp := cfg_map NewL2.l2Rec
  (fun p ex P _ fl Q => cfg_postprocess (CFG_VC_loop_triple p ex P NewL2.l2_annot fl Q)).
Eval vm_compute in ("CntNewL2", zzcnt pp).
End CntNewL2.
