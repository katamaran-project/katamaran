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
  [ cl (clem_arrv_count0 1 (-1) ts); cl (clem_arrv_join 1 (-1) mv_sd ts ts)
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

(* ======================================================================== *)
(* 4. CONTRACT (b): the OVERLAPPING shift by one word (i31_muladd.c:86,93,  *)
(*    memmove(x + 2, x + 1, (mlen - 1) * 4)): dst = src + 4.  Values are    *)
(*    unnamed (D5: the limbs moved are secret; the caller overwrites the    *)
(*    low word next).                                                        *)
(*                                                                           *)
(* Memory: L = the n bytes moved, at s; M = the 4 bytes above them, at s+n. *)
(* The walk is downward, so the 4-byte WINDOW just above the read cursor is *)
(* kept flipped (stride -1, top cell first): each step reads L's top byte   *)
(* and appends it at the window's bottom, then writes the window's TOP byte *)
(* into T, the destination's done array (stride -1 from d+n-1 down), seeded *)
(* by empty_at on the flipped M -- the top byte, where T begins.  After the *)
(* loop L is empty, the window is the low 4 bytes, T is the destination;    *)
(* flip both back.  No two arrays share a tag.                              *)
(* ======================================================================== *)
Definition t_off {Σ} (a : Term Σ ty_xlenbits) (z : Z) : Term Σ ty_xlenbits := clem_off a z.

(* Parameters: the region's base s, T's top byte Top (= d+n-1), the count n.
   State: cursor p (one above L's top byte = the window's bottom), c to go,
   k done. *)
Definition mwlCtx : LCtx := ["q"∷ty_xlenbits; "s"∷ty_xlenbits; "Top"∷ty_xlenbits; "n"∷ty_xlenbits].

Definition mwl_annot (ts tg td : string) : list AnnotInstr :=
  [ AST_AnnotInstr (RTYPE A3 A4 A4 RISCV_ADD)
  ; AST_AnnotInstr (RTYPE A3 A1 A1 RISCV_ADD)
  ; {| ai_ghost_before := [ AnnotCLemma (clem_arrv_take_last 1 1 ts) ]
     ; ai_instr := LOAD (bv.of_Z 0) A1 A5 true BYTE
     ; ai_ghost_after := [ AnnotCLemma (clem_arrv_add_last 1 (-1) tg) ]; ai_block := None |}
  ; AST_AnnotInstr (ITYPE (bv.of_Z (-1)) A2 A2 RISCV_ADDI)
  ; {| ai_ghost_before := [ AnnotCLemma (clem_arrv_take_first 1 (-1) tg) ]
     ; ai_instr := STORE (bv.of_Z 0) A5 A4 BYTE
     ; ai_ghost_after := [ AnnotCLemma (clem_arrv_add_last 1 (-1) td) ]; ai_block := None |}
  ; AST_AnnotInstr (BTYPE (bv.of_Z (-20)) X0 A2 RISCV_BNE) ].

Definition mwl_state {Σ} (ts tg td : string) (s Top n c k p : Term Σ ty_xlenbits)
    (vl vm vt : Term Σ (clemv_ty 1)) : Assertion Σ :=
  ( clem_arrv_angelic 1 1 ts s c p vl
    ∗ clem_arrv_angelic 1 (-1) tg (t_off p 3) (term_val ty_xlenbits (bv.of_N 4)) (t_off p (-1)) vm
    ∗ clem_arrv_angelic 1 (-1) td Top k (t_off p 3) vt
    ∗ A1 ↦ᵣ p ∗ A4 ↦ᵣ t_off p 4 ∗ A2 ↦ᵣ c ∗ A3 ↦ᵣ term_val ty_xlenbits (bv.of_Z (-1))
    ∗ asn.formula (formula_relop bop.eq (term_binop bop.bvadd k c) n) )%asn.

Definition mwl_inv (ts tg td : string) : Assertion (mwlCtx ▻ "a"∷ty_xlenbits) :=
  ( asn.exist "c" ty_xlenbits (asn.exist "k" ty_xlenbits (asn.exist "p" ty_xlenbits
    (asn.exist "vl" (clemv_ty 1) (asn.exist "vm" (clemv_ty 1) (asn.exist "vt" (clemv_ty 1)
      ( mwl_state ts tg td (term_var "s") (term_var "Top") (term_var "n") (term_var "c")
          (term_var "k") (term_var "p") (term_var "vl") (term_var "vm") (term_var "vt")
        ∗ secLeakvar "c" ∗ secLeakvar "p"
        ∗ clem_nonzero (term_var "c")))))))
    ∗ asn.exist "v5" ty_xlenbits (A5 ↦ᵣ term_var "v5") )%asn.

Definition mwl_post (ts tg td : string) : Assertion (mwlCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( asn.exist "k" ty_xlenbits (asn.exist "p" ty_xlenbits
    (asn.exist "vl" (clemv_ty 1) (asn.exist "vm" (clemv_ty 1) (asn.exist "vt" (clemv_ty 1)
      (mwl_state ts tg td (term_var "s") (term_var "Top") (term_var "n")
         (term_val ty_xlenbits bv.zero) (term_var "k") (term_var "p")
         (term_var "vl") (term_var "vm") (term_var "vt"))))))
    ∗ asn.exist "v5" ty_xlenbits (A5 ↦ᵣ term_var "v5") )%asn.

Definition mwlRec (ts tg td : string) : @CFGVerifierContract mwlCtx :=
  gen_seg_contract (term_var "q") (term_var "q") mvl_instrs 24 16 [] (mwl_inv ts tg td) (mwl_post ts tg td).
Definition mwlBlk (ts tg td : string) : BlkAnnot := {| blk_ctx := mwlCtx ; blk_contract := mwlRec ts tg td |}.

Lemma valid_mwl_loop : cfg_vc_loop (mwlRec "vs" "vg" "vd") (mwl_annot "vs" "vg" "vd").
Proof. Time solve_mb_vc. Qed.

(* the function: s (A1), dst s+4 (A0), n (A2); L at s, M at s+n *)
Definition mwfCtx : LCtx :=
  ["q"∷ty_xlenbits; "r"∷ty_xlenbits; "s"∷ty_xlenbits; "n"∷ty_xlenbits;
   "vs"∷clemv_ty 1; "vg"∷clemv_ty 1].

Definition mwf_pre (ts tg : string) : Assertion (mwfCtx ▻ "a"∷ty_xlenbits) :=
  ( X1 ↦ᵣ term_var "r"
    ∗ A1 ↦ᵣ term_var "s" ∗ secLeakvar "s"
    ∗ A0 ↦ᵣ t_off (term_var "s") 4
    ∗ A2 ↦ᵣ term_var "n" ∗ secLeakvar "n"
    (* backward, and s + 4 does not wrap *)
    ∗ asn.formula (formula_relop bop.bvult (term_var "s") (t_off (term_var "s") 4))
    ∗ clem_arrv 1 1 ts (term_var "s") (term_var "n") (t_end (term_var "s") (term_var "n")) (term_var "vs")
    ∗ clem_arrv 1 1 tg (t_end (term_var "s") (term_var "n")) (term_val ty_xlenbits (bv.of_N 4))
        (t_off (t_end (term_var "s") (term_var "n")) 4) (term_var "vg") )%asn.

(* the low 4 bytes (tg) and the destination s+4 .. s+4+n (td), values unnamed *)
Definition mwf_post (tg td : string) : Assertion (mwfCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( X1 ↦ᵣ term_var "r"
    ∗ A0 ↦ᵣ t_off (term_var "s") 4
    ∗ asn.exist "wl" (clemv_ty 1)
        (clem_arrv 1 1 tg (term_var "s") (term_val ty_xlenbits (bv.of_N 4))
           (t_off (term_var "s") 4) (term_var "wl"))
    ∗ asn.exist "wd" (clemv_ty 1)
        (clem_arrv 1 1 td (t_off (term_var "s") 4) (term_var "n")
           (t_end (t_off (term_var "s") 4) (term_var "n")) (term_var "wd"))
    ∗ asn.exist "w1" ty_xlenbits (A1 ↦ᵣ term_var "w1")
    ∗ asn.exist "w2" ty_xlenbits (A2 ↦ᵣ term_var "w2")
    ∗ asn.exist "w3" ty_xlenbits (A3 ↦ᵣ term_var "w3")
    ∗ asn.exist "w4" ty_xlenbits (A4 ↦ᵣ term_var "w4")
    ∗ asn.exist "w5" ty_xlenbits (A5 ↦ᵣ term_var "w5") )%asn.

Definition mwfRec (ts tg td : string) : @CFGVerifierContract mwfCtx :=
  gen_seg_contract_at (term_var "q") (term_var "q") (term_var "r")
    memmove_instrs 14 mvf_regs (secLeakvar "r" ∗ mwf_pre ts tg)%asn (mwf_post tg td).
Definition mwfBlk (ts tg td : string) : BlkAnnot := {| blk_ctx := mwfCtx ; blk_contract := mwfRec ts tg td |}.

(* Entry, BEFORE the beqz (both paths): flip the window, seed T at its top
   byte.  Exit, before the ret: L is empty; flip the window and T back. *)
Definition mwf_entry (tg td : string) : list Annot :=
  [ cl (clem_arrv_flip 1 1 tg); cl (clem_arrv_empty_at 1 (-1) tg td) ].
Definition mwf_glue (ts tg td : string) : list Annot :=
  [ cl (clem_arrv_empty_elim 1 1 ts); cl (clem_arrv_flip 1 (-1) tg); cl (clem_arrv_flip 1 (-1) td) ].

Definition mwf_annot (ts tg td : string) : list AnnotInstr :=
  List.map (fun '(i, ins) =>
              {| ai_ghost_before := if Nat.eqb i 0 then mwf_entry tg td
                                    else if Nat.eqb i 13 then mwf_glue ts tg td else nil
               ; ai_instr := ins
               ; ai_ghost_after := nil
               ; ai_block := if Nat.eqb i 7 then Some (mwlBlk ts tg td) else None |})
    (List.combine (List.seq 0 (length memmove_instrs)) memmove_instrs).

Lemma valid_mwf : cfg_vc_loop (mwfRec "vs" "vg" "vd") (mwf_annot "vs" "vg" "vd").
Proof. Time solve_mb_vc. Qed.

(* NEGATIVE CONTROL: the move really happens -- the window is not handed
   back where M was (s+n), it is the LOW 4 bytes *)
Goal cfg_vc_loop (gen_seg_contract_at (term_var "q") (term_var "q") (term_var "r")
    memmove_instrs 14 mvf_regs (secLeakvar "r" ∗ mwf_pre "vs" "vg")%asn
    ( X1 ↦ᵣ term_var "r"
      ∗ asn.exist "wl" (clemv_ty 1)
          (clem_arrv 1 1 "vg" (t_end (term_var "s") (term_var "n")) (term_val ty_xlenbits (bv.of_N 4))
             (t_off (t_end (term_var "s") (term_var "n")) 4) (term_var "wl")) )%asn)
  (mwf_annot "vs" "vg" "vd").
Proof. Fail solve_mb_vc. Abort.
