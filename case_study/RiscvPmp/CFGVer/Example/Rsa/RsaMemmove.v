(* ========================================================================= *)
(* Example/Rsa/RsaMemmove.v -- PLAN-rsa.md Phase 2 (D5): picolibc 1.8.12's  *)
(* size-optimised memmove as a FUNCTION contract, BACKWARD direction (both   *)
(* BearSSL call sites have dst > src).  LIGHT, VCs only.                     *)
(*                                                                           *)
(*   0:  jal ra, memmove         the harness: call once,                     *)
(*   4:  j   _etext              then leave at the fall-through end (64)     *)
(*   8:  memmove                 beqz a2,ret; a3 := +1, or (dst >= src) -1  *)
(*                               and both pointers += n; .Lincrement: both   *)
(*                               += a3; .Lcopy: lbu; a2--; sb; bnez          *)
(*                               .Lincrement; ret                            *)
(*                                                                           *)
(* This file: contract (a), DISJOINT arrays (rsa_i31_priv.c:136 moves p to   *)
(* the slot right after it).  Precondition src <u dst refutes the forward    *)
(* branch.  The post is memcpy's: the destination holds exactly vs.          *)
(*                                                                           *)
(* The walk is downward, so both arrays are FLIPPED to stride -1 at entry    *)
(* (before the beqz, so both paths see the same shapes); the loop is then    *)
(* memcpy's at stride -1 (seeds by empty_at at the flipped starts, done      *)
(* grown by add_last), and the exit glue flips back.  The value equation     *)
(* is vs = rev (done ++ rest), a VARIABLE on the left so that the solver can *)
(* substitute it at the exit (peval_rev: rev (rev v) ~> v).                  *)
(*                                                                           *)
(* Instructions: tools/bearssl/picolibc.sh (memmove.o) +                    *)
(* tools/bearssl/spike/harness_memmove.s, `ld.lld --relax -Ttext=0`,        *)
(* `llvm-objdump -d --no-show-raw-insn`, `asm_to_ast.py --objdump           *)
(* --tables-aliases --name mmf`.  Regenerate, do not edit.                  *)
(* ========================================================================= *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamClose.

Definition mmf_instrs : list AST :=
  [ RISCV_JAL (bv.of_Z 8) X1   (* jal	L_8	# 0x0: jal 0x8 <memmove> *)
  ; RISCV_JAL (bv.of_Z 60) X0   (* j	L_40	# 0x4: j 0x40 <_etext> *)
  ; BTYPE (bv.of_Z 52) X0 A2 RISCV_BEQ   (* beqz	a2, L_3c	# 0x8: beqz a2, 0x3c <.Ldone> *)
  ; ITYPE (bv.of_Z 0) A0 A4 RISCV_ADDI   (* mv	a4, a0	# 0xc: mv a4, a0 *)
  ; ITYPE (bv.of_Z 1) X0 A3 RISCV_ADDI   (* li	a3, 1	# 0x10: li a3, 0x1 *)
  ; BTYPE (bv.of_Z 24) A1 A0 RISCV_BLTU   (* bltu	a0, a1, L_2c	# 0x14: bltu a0, a1, 0x2c <.Lcopy> *)
  ; ITYPE (bv.of_Z (-1)) X0 A3 RISCV_ADDI   (* li	a3, -1	# 0x18: li a3, -0x1 *)
  ; RTYPE A2 A4 A4 RISCV_ADD   (* add	a4, a4, a2	# 0x1c: add a4, a4, a2 *)
  ; RTYPE A2 A1 A1 RISCV_ADD   (* add	a1, a1, a2	# 0x20: add a1, a1, a2 *)
  ; RTYPE A3 A4 A4 RISCV_ADD   (* add	a4, a4, a3	# 0x24: add a4, a4, a3 *)
  ; RTYPE A3 A1 A1 RISCV_ADD   (* add	a1, a1, a3	# 0x28: add a1, a1, a3 *)
  ; LOAD (bv.of_Z 0) A1 A5 true BYTE   (* lbu	a5, 0(a1)	# 0x2c: lbu a5, 0x0(a1) *)
  ; ITYPE (bv.of_Z (-1)) A2 A2 RISCV_ADDI   (* addi	a2, a2, -1	# 0x30: addi a2, a2, -0x1 *)
  ; STORE (bv.of_Z 0) A5 A4 BYTE   (* sb	a5, 0(a4)	# 0x34: sb a5, 0x0(a4) *)
  ; BTYPE (bv.of_Z (-20)) X0 A2 RISCV_BNE   (* bnez	a2, L_24	# 0x38: bnez a2, 0x24 <.Lincrement> *)
  ; RISCV_JALR (bv.of_Z 0) X1 X0   (* ret		# 0x3c: ret *)
  ].

(* memmove's own code, from its first instruction (byte offset 8) *)
Definition memmove_instrs : list AST := List.skipn 2 mmf_instrs.
(* the loop, from .Lincrement: instructions 7..12 of memmove_instrs *)
Definition mvl_instrs : list AST := List.firstn 6 (List.skipn 7 memmove_instrs).

Definition t_end {Σ} (a n : Term Σ ty_xlenbits) : Term Σ ty_xlenbits :=
  term_binop bop.bvadd a n.
Definition t_dec {Σ} (a : Term Σ ty_xlenbits) : Term Σ ty_xlenbits := clem_off a (-1).

(* the source's DONE array: a tag of memmove's own *)
Definition mv_sd : string := "memmove.sd".

(* ------------------------------------------------------------------------ *)
(* 1. THE LOOP (backward; arrays at stride -1)                              *)
(* ------------------------------------------------------------------------ *)
(* Parameters: the flipped arrays' starts S, D (the top bytes) and ends E, F *)
(* (one below the bottom bytes), the count n, and the SOURCE's value V.     *)
(* State: cursors p, r one ABOVE the next cell (the body decrements first), *)
(* c to go, k done.                                                         *)
Definition mvlCtx : LCtx :=
  ["q"∷ty_xlenbits; "S"∷ty_xlenbits; "D"∷ty_xlenbits; "E"∷ty_xlenbits;
   "F"∷ty_xlenbits; "n"∷ty_xlenbits; "V"∷clemv_ty 1].

Definition mvl_annot (ts td : string) : list AnnotInstr :=
  [ AST_AnnotInstr (RTYPE A3 A4 A4 RISCV_ADD)
  ; AST_AnnotInstr (RTYPE A3 A1 A1 RISCV_ADD)
  ; {| ai_ghost_before := [ AnnotCLemma (clem_arrv_take_first 1 (-1) ts) ]
     ; ai_instr := LOAD (bv.of_Z 0) A1 A5 true BYTE
     ; ai_ghost_after := [ AnnotCLemma (clem_arrv_add_last 1 (-1) mv_sd) ]; ai_block := None |}
  ; AST_AnnotInstr (ITYPE (bv.of_Z (-1)) A2 A2 RISCV_ADDI)
  ; {| ai_ghost_before := [ AnnotCLemma (clem_arrv_take_first 1 (-1) td) ]
     ; ai_instr := STORE (bv.of_Z 0) A5 A4 BYTE
     ; ai_ghost_after := [ AnnotCLemma (clem_arrv_add_last 1 (-1) td) ]; ai_block := None |}
  ; AST_AnnotInstr (BTYPE (bv.of_Z (-20)) X0 A2 RISCV_BNE) ].

Definition mvl_state {Σ} (ts td : string) (S D E F n c k p r : Term Σ ty_xlenbits)
    (done rest drest : Term Σ (clemv_ty 1)) : Assertion Σ :=
  ( clem_arrv_angelic 1 (-1) mv_sd S k (t_dec p) done
    ∗ clem_arrv_angelic 1 (-1) ts (t_dec p) c E rest
    ∗ clem_arrv_angelic 1 (-1) td D k (t_dec r) done
    ∗ clem_arrv_angelic 1 (-1) td (t_dec r) c F drest
    ∗ A1 ↦ᵣ p ∗ A4 ↦ᵣ r ∗ A2 ↦ᵣ c ∗ A3 ↦ᵣ term_val ty_xlenbits (bv.of_Z (-1))
    ∗ asn.formula (formula_relop bop.eq (term_binop bop.bvadd k c) n) )%asn.

Definition mvl_inv (ts td : string) : Assertion (mvlCtx ▻ "a"∷ty_xlenbits) :=
  ( asn.exist "c" ty_xlenbits (asn.exist "k" ty_xlenbits
    (asn.exist "p" ty_xlenbits (asn.exist "r" ty_xlenbits
    (asn.exist "done" (clemv_ty 1) (asn.exist "rest" (clemv_ty 1)
    (asn.exist "drest" (clemv_ty 1)
      ( mvl_state ts td (term_var "S") (term_var "D") (term_var "E") (term_var "F")
          (term_var "n") (term_var "c") (term_var "k") (term_var "p") (term_var "r")
          (term_var "done") (term_var "rest") (term_var "drest")
        ∗ secLeakvar "c" ∗ secLeakvar "p" ∗ secLeakvar "r"
        ∗ clem_nonzero (term_var "c")
        ∗ asn.formula (formula_propeq (term_var "V")
            (term_unop uop.rev (term_binop bop.append (term_var "done") (term_var "rest")))))))))))
    ∗ asn.exist "v5" ty_xlenbits (A5 ↦ᵣ term_var "v5") )%asn.

Definition mvl_post (ts td : string) : Assertion (mvlCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( asn.exist "k" ty_xlenbits
    (asn.exist "p" ty_xlenbits (asn.exist "r" ty_xlenbits
    (asn.exist "done" (clemv_ty 1) (asn.exist "rest" (clemv_ty 1)
    (asn.exist "drest" (clemv_ty 1)
      ( mvl_state ts td (term_var "S") (term_var "D") (term_var "E") (term_var "F")
          (term_var "n") (term_val ty_xlenbits bv.zero) (term_var "k") (term_var "p")
          (term_var "r") (term_var "done") (term_var "rest") (term_var "drest")
        ∗ asn.formula (formula_propeq (term_var "V")
            (term_unop uop.rev (term_binop bop.append (term_var "done") (term_var "rest"))))))))))
    ∗ asn.exist "v5" ty_xlenbits (A5 ↦ᵣ term_var "v5") )%asn.

Definition mvlRec (ts td : string) : @CFGVerifierContract mvlCtx :=
  gen_seg_contract (term_var "q") (term_var "q") mvl_instrs 24 16 [] (mvl_inv ts td) (mvl_post ts td).
Definition mvlBlk (ts td : string) : BlkAnnot := {| blk_ctx := mvlCtx ; blk_contract := mvlRec ts td |}.

Lemma valid_mvl_loop : cfg_vc_loop (mvlRec "vs" "dv") (mvl_annot "vs" "dv").
Proof. Time solve_mb_vc. Qed.

(* ------------------------------------------------------------------------ *)
(* 2. memmove (a), ITS EXIT THE RETURN ADDRESS                              *)
(* ------------------------------------------------------------------------ *)
Definition mvfCtx : LCtx :=
  ["q"∷ty_xlenbits; "r"∷ty_xlenbits; "s"∷ty_xlenbits; "d"∷ty_xlenbits;
   "n"∷ty_xlenbits; "vs"∷clemv_ty 1; "dv"∷clemv_ty 1].

Definition mvf_pre (ts td : string) : Assertion (mvfCtx ▻ "a"∷ty_xlenbits) :=
  ( X1 ↦ᵣ term_var "r"
    ∗ A0 ↦ᵣ term_var "d" ∗ secLeakvar "d"
    ∗ A1 ↦ᵣ term_var "s" ∗ secLeakvar "s"
    ∗ A2 ↦ᵣ term_var "n" ∗ secLeakvar "n"
    (* backward: src <u dst *)
    ∗ asn.formula (formula_relop bop.bvult (term_var "s") (term_var "d"))
    ∗ clem_arrv 1 1 ts (term_var "s") (term_var "n") (t_end (term_var "s") (term_var "n")) (term_var "vs")
    ∗ clem_arrv 1 1 td (term_var "d") (term_var "n") (t_end (term_var "d") (term_var "n")) (term_var "dv") )%asn.

Definition mvf_post (ts td : string) : Assertion (mvfCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( X1 ↦ᵣ term_var "r"
    ∗ A0 ↦ᵣ term_var "d"
    ∗ clem_arrv 1 1 ts (term_var "s") (term_var "n") (t_end (term_var "s") (term_var "n")) (term_var "vs")
    ∗ clem_arrv 1 1 td (term_var "d") (term_var "n") (t_end (term_var "d") (term_var "n")) (term_var "vs")
    ∗ asn.exist "w1" ty_xlenbits (A1 ↦ᵣ term_var "w1")
    ∗ asn.exist "w2" ty_xlenbits (A2 ↦ᵣ term_var "w2")
    ∗ asn.exist "w3" ty_xlenbits (A3 ↦ᵣ term_var "w3")
    ∗ asn.exist "w4" ty_xlenbits (A4 ↦ᵣ term_var "w4")
    ∗ asn.exist "w5" ty_xlenbits (A5 ↦ᵣ term_var "w5") )%asn.

Definition mvf_regs : list reg_spec_rel := [ (A3, Secret); (A4, Secret); (A5, Secret) ].

Definition mvfRec (ts td : string) : @CFGVerifierContract mvfCtx :=
  gen_seg_contract_at (term_var "q") (term_var "q") (term_var "r")
    memmove_instrs 14 mvf_regs (secLeakvar "r" ∗ mvf_pre ts td)%asn (mvf_post ts td).
Definition mvfBlk (ts td : string) : BlkAnnot := {| blk_ctx := mvfCtx ; blk_contract := mvfRec ts td |}.

Definition cl (k : CLem) : Annot := AnnotCLemma k.

(* Entry, BEFORE the beqz (both paths): flip both arrays to stride -1 and
   seed the done arrays at the flipped starts.  Exit, before the ret (both
   paths): memcpy's glue at stride -1, then flip back. *)
Definition mvf_entry (ts td : string) : list Annot :=
  [ cl (clem_arrv_flip 1 1 ts); cl (clem_arrv_flip 1 1 td)
  ; cl (clem_arrv_empty_at 1 (-1) ts mv_sd); cl (clem_arrv_empty_at 1 (-1) td td) ].
Definition mvf_glue (ts td : string) : list Annot :=
  [ cl (clem_arrv_pad 1 (-1) td ts); cl (clem_arrv_join 1 (-1) mv_sd ts ts)
  ; cl (clem_arrv_empty_elim 1 (-1) td)
  ; cl (clem_arrv_flip 1 (-1) ts); cl (clem_arrv_flip 1 (-1) td) ].

Definition mvf_annot (ts td : string) : list AnnotInstr :=
  List.map (fun '(i, ins) =>
              {| ai_ghost_before := if Nat.eqb i 0 then mvf_entry ts td
                                    else if Nat.eqb i 13 then mvf_glue ts td else nil
               ; ai_instr := ins
               ; ai_ghost_after := nil
               ; ai_block := if Nat.eqb i 7 then Some (mvlBlk ts td) else None |})
    (List.combine (List.seq 0 (length memmove_instrs)) memmove_instrs).

Lemma valid_mvf : cfg_vc_loop (mvfRec "vs" "dv") (mvf_annot "vs" "dv").
Proof. Time solve_mb_vc. Qed.

(* ------------------------------------------------------------------------ *)
(* 3. THE WHOLE PROGRAM: the harness calls memmove                          *)
(* ------------------------------------------------------------------------ *)
Definition mmfCtx : LCtx := ["q"∷ty_xlenbits; "s"∷ty_xlenbits; "d"∷ty_xlenbits; "n"∷ty_xlenbits].

Definition mmf_regs : list (reg_spec_q mmfCtx) :=
  [ (A0, Known (PVVar "d")); (A1, Known (PVVar "s")); (A2, Known (PVVar "n")); (X1, Secret)
  ; (A3, Secret); (A4, Secret); (A5, Secret) ].

Definition mmf_facts : Assertion (mmfCtx ▻ "a"∷ty_xlenbits) :=
  asn.formula (formula_relop bop.bvult (term_var "s") (term_var "d")).

(* a PUBLIC source, a SECRET destination *)
Definition mmf_data (spub : bool) : list (data_spec mmfCtx) :=
  [ DPtr (term_var "s"); DBytes spub (term_var "n") "vs"
  ; DPtr (term_var "d"); DBytes false (term_var "n") "dv" ]%list.

Definition mmfCtxV : LCtx := mmfCtx ▻▻ data_vctx (mmf_data true).

(* the destination holds vs and is therefore PUBLIC *)
Definition mmf_post : Assertion (mmfCtxV ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( clem_arrv 1 1 "vs" (term_var "s") (term_var "n") (t_end (term_var "s") (term_var "n")) (term_var "vs")
    ∗ clem_arrv 1 1 "dv" (term_var "d") (term_var "n") (t_end (term_var "d") (term_var "n")) (term_var "vs")
    ∗ secLeakvar "vs"
    ∗ asn.exist "w1" ty_xlenbits (X1 ↦ᵣ term_var "w1")
    ∗ asn.exist "w0" ty_xlenbits (A0 ↦ᵣ term_var "w0")
    ∗ asn.exist "w8" ty_xlenbits (A1 ↦ᵣ term_var "w8")
    ∗ asn.exist "w2" ty_xlenbits (A2 ↦ᵣ term_var "w2")
    ∗ asn.exist "w3" ty_xlenbits (A3 ↦ᵣ term_var "w3")
    ∗ asn.exist "w4" ty_xlenbits (A4 ↦ᵣ term_var "w4")
    ∗ asn.exist "w5" ty_xlenbits (A5 ↦ᵣ term_var "w5") )%asn.

(* exit: the fall-through end, +64 = 4 * 16 *)
Definition mmfRec (spub : bool) : @CFGVerifierContract mmfCtxV :=
  gen_prog_contract "q" _ mmf_regs mmf_facts 64 (mmf_data spub) mmf_instrs 10 mmf_post.

(* memmove is a block on ITS first instruction, index 2 *)
Definition mmf_annot : list AnnotInstr :=
  List.map (fun '(i, ins) =>
              {| ai_ghost_before := nil ; ai_instr := ins ; ai_ghost_after := nil
               ; ai_block := if Nat.eqb i 2 then Some (mvfBlk "vs" "dv") else None |})
    (List.combine (List.seq 0 (length mmf_instrs)) mmf_instrs).

Lemma valid_mmf : cfg_vc (mmfRec true) mmf_annot.
Proof. Time solve_mb_vc. Qed.

(* NEGATIVE CONTROLS *)

(* a SECRET source: the destination is not public *)
Goal cfg_vc (mmfRec false) mmf_annot.
Proof. Fail solve_mb_vc. Abort.

(* memmove really copies: a post keeping the destination's OLD value fails *)
Goal cfg_vc_loop (gen_seg_contract_at (term_var "q") (term_var "q") (term_var "r")
    memmove_instrs 14 mvf_regs (secLeakvar "r" ∗ mvf_pre "vs" "dv")%asn
    ( X1 ↦ᵣ term_var "r"
      ∗ clem_arrv 1 1 "dv" (term_var "d") (term_var "n") (t_end (term_var "d") (term_var "n")) (term_var "dv") )%asn)
  (mvf_annot "vs" "dv").
Proof. Fail solve_mb_vc. Abort.
