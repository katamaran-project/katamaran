(* ========================================================================= *)
(* Example/Rsa/RsaSpikeArrv.v -- PLAN-rsa.md Phase 2, SPIKE: arrays whose   *)
(* contents are NAMED (`arrv`, Sig.v), so that a callee's post that names   *)
(* the same value term keeps the caller's facts about it by FRAMING.        *)
(* LIGHT, VCs only.                                                          *)
(*                                                                           *)
(* v4: the caller side.  memcpy is a block with the VALUE contract          *)
(*   arrv s n e vs ∗ arrv d n f ws  ⊢  arrv s n e vs ∗ arrv d n f vs        *)
(* (a STAND-IN on a one-instruction segment: its validity is v3's business, *)
(* not this file's).  The caller holds a PUBLIC header byte h and SECRET    *)
(* limbs ls, joins them into one array h :: ls, calls memcpy, and takes the *)
(* destination's first cell back: it holds h, so it is public -- no flag,   *)
(* no ghost about publicness.                                                *)
(* ========================================================================= *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamClose.

Definition t_inc {Σ} (a : Term Σ ty_xlenbits) : Term Σ ty_xlenbits :=
  term_binop bop.bvadd a (term_val ty_xlenbits (bv.of_Z 1)).

Definition NOP : AST := ITYPE (bv.of_Z 0) X0 X0 RISCV_ADDI.

(* ------------------------------------------------------------------------ *)
(* memcpy's contract, on a stand-in body                                    *)
(* ------------------------------------------------------------------------ *)
Definition cpCtx : LCtx :=
  ["q"∷ty_xlenbits; "s"∷ty_xlenbits; "d"∷ty_xlenbits; "n"∷ty_xlenbits;
   "e"∷ty_xlenbits; "f"∷ty_xlenbits; "vs"∷clemv_ty 1; "ws"∷clemv_ty 1].

(* angelic: the block's variables are bound by the heap search *)
Definition cp_pre : Assertion (cpCtx ▻ "a"∷ty_xlenbits) :=
  ( clem_arrv_angelic 1 1 "src" (term_var "s") (term_var "n") (term_var "e") (term_var "vs")
    ∗ clem_arrv_angelic 1 1 "dst" (term_var "d") (term_var "n") (term_var "f") (term_var "ws") )%asn.

(* the destination now holds the SAME term vs -- no existential *)
Definition cp_post : Assertion (cpCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( clem_arrv 1 1 "src" (term_var "s") (term_var "n") (term_var "e") (term_var "vs")
    ∗ clem_arrv 1 1 "dst" (term_var "d") (term_var "n") (term_var "f") (term_var "vs") )%asn.

(* NEGATIVE: the usual existential post *)
Definition cp_post_ex : Assertion (cpCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( clem_arrv 1 1 "src" (term_var "s") (term_var "n") (term_var "e") (term_var "vs")
    ∗ asn.exist "ws2" (clemv_ty 1)
        (clem_arrv 1 1 "dst" (term_var "d") (term_var "n") (term_var "f") (term_var "ws2")) )%asn.

Definition cpBlk (post : Assertion (cpCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) : BlkAnnot :=
  {| blk_ctx := cpCtx
   ; blk_contract := gen_seg_contract (term_var "q") (term_var "q") [NOP] 4 4 [] cp_pre post |}.

(* ------------------------------------------------------------------------ *)
(* the caller                                                               *)
(* ------------------------------------------------------------------------ *)
Definition clCtx : LCtx :=
  ["q"∷ty_xlenbits; "p"∷ty_xlenbits; "d"∷ty_xlenbits; "n"∷ty_xlenbits;
   "e"∷ty_xlenbits; "f"∷ty_xlenbits; "h"∷clem_cell_ty 1; "ls"∷clemv_ty 1;
   "ws"∷clemv_ty 1].

Definition cl_instrs : list AST := [NOP; NOP; NOP].

(* join h onto ls after instruction 0 (an instruction carrying a block runs
   the block INSTEAD of itself, ghosts included); memcpy on instruction 1;
   take the destination's first cell back before instruction 2 *)
Definition cl_annot (post : Assertion (cpCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) : list AnnotInstr :=
  [ {| ai_ghost_before := []; ai_instr := NOP
     ; ai_ghost_after := [ AnnotCLemma (clem_arrv_add_first 1 1 "src") ]; ai_block := None |}
  ; {| ai_ghost_before := []; ai_instr := NOP; ai_ghost_after := []
     ; ai_block := Some (cpBlk post) |}
  ; {| ai_ghost_before := [ AnnotCLemma (clem_arrv_take_cons 1 1 "dst") ]; ai_instr := NOP
     ; ai_ghost_after := []; ai_block := None |} ].

(* h at p, then n limbs; a destination of n+1 cells *)
Definition cl_pre (hpub : bool) : Assertion (clCtx ▻ "a"∷ty_xlenbits) :=
  ( clem_ptsto 1 (term_var "p") (term_var "h")
    ∗ clem_range 1 (term_var "p")
    ∗ clem_arrv 1 1 "src" (t_inc (term_var "p")) (term_var "n") (term_var "e") (term_var "ls")
    ∗ clem_arrv 1 1 "dst" (term_var "d") (t_inc (term_var "n")) (term_var "f") (term_var "ws")
    ∗ asn.formula (formula_relop bop.bvult (term_var "n")
        (term_val ty_xlenbits (bv.of_N 0x40000000)))
    ∗ (if hpub then secLeakvar "h" else ⊤) )%asn.

(* the copy's first cell is PUBLIC; the source is still h :: ls *)
Definition cl_post : Assertion (clCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( clem_arrv 1 1 "src" (term_var "p") (t_inc (term_var "n")) (term_var "e")
      (term_binop bop.cons (term_var "h") (term_var "ls"))
    ∗ asn.exist "v" (clem_cell_ty 1)
        (clem_ptsto 1 (term_var "d") (term_var "v") ∗ asn.formula (formula_secLeak (term_var "v")))
    ∗ clem_arrv 1 1 "dst" (t_inc (term_var "d")) (term_var "n") (term_var "f") (term_var "ls") )%asn.

Definition clRec (hpub : bool) : @CFGVerifierContract clCtx :=
  gen_seg_contract (term_var "q") (term_var "q") cl_instrs 12 8 [] (cl_pre hpub) cl_post.

Lemma valid_cl : cfg_vc_loop (clRec true) (cl_annot cp_post).
Proof. Time solve_mb_vc. Qed.

(* NEGATIVE CONTROLS.  A secret h: the copy is not public (the publicness
   came from the caller's fact, not from nowhere). *)
Goal cfg_vc_loop (clRec false) (cl_annot cp_post).
Proof. Fail solve_mb_vc. Abort.

(* The usual existential post loses it. *)
Goal cfg_vc_loop (clRec true) (cl_annot cp_post_ex).
Proof. Fail solve_mb_vc. Abort.

(* ------------------------------------------------------------------------ *)
(* v3: memcpy's own LOOP, with values -- picolibc 1.8.12 -Os memcpy-asm.S   *)
(* (tools/bearssl/picolibc.sh), the loop at .Ltmp1:                          *)
(*   lbu a4,0(a1); sb a4,0(a3); addi a2,a2,-1; addi a3,a3,1;                 *)
(*   addi a1,a1,1; bnez a2,.Ltmp1                                            *)
(* Invariant: the source is DONE ++ REST, the destination DONE ++ (old), and *)
(* vs = done ++ rest.  One step: take rest's first cell (by equation: rest  *)
(* is a variable), load it, put it back at the end of the source's done;    *)
(* take the destination's next cell, store, add it to the destination's     *)
(* done.  The stored byte is `bvtake 8 (zext x)`; peval_bvtake_zext makes   *)
(* it x, and peval_append re-associates (done ++ [x]) ++ rest'.             *)
(* ------------------------------------------------------------------------ *)
Definition mcCtx : LCtx :=
  ["q"∷ty_xlenbits; "s"∷ty_xlenbits; "d"∷ty_xlenbits; "e"∷ty_xlenbits;
   "f"∷ty_xlenbits; "vs"∷clemv_ty 1].

Definition mc_instrs : list AST :=
  [ LOAD (bv.of_Z 0) A1 A4 true BYTE             (* lbu  a4, 0(a1) *)
  ; STORE (bv.of_Z 0) A4 A3 BYTE                 (* sb   a4, 0(a3) *)
  ; ITYPE (bv.of_Z (-1)) A2 A2 RISCV_ADDI        (* addi a2, a2, -1 *)
  ; ITYPE (bv.of_Z 1) A3 A3 RISCV_ADDI           (* addi a3, a3, 1 *)
  ; ITYPE (bv.of_Z 1) A1 A1 RISCV_ADDI           (* addi a1, a1, 1 *)
  ; BTYPE (bv.of_Z (-20)) X0 A2 RISCV_BNE ].     (* bnez a2, .Ltmp1 *)

Definition mc_annot : list AnnotInstr :=
  [ {| ai_ghost_before := [ AnnotCLemma (clem_arrv_take_first 1 1 "srest") ]
     ; ai_instr := LOAD (bv.of_Z 0) A1 A4 true BYTE
     ; ai_ghost_after := [ AnnotCLemma (clem_arrv_add_last 1 1 "sdone") ]; ai_block := None |}
  ; {| ai_ghost_before := [ AnnotCLemma (clem_arrv_take_first 1 1 "drest") ]
     ; ai_instr := STORE (bv.of_Z 0) A4 A3 BYTE
     ; ai_ghost_after := [ AnnotCLemma (clem_arrv_add_last 1 1 "ddone") ]; ai_block := None |}
  ; AST_AnnotInstr (ITYPE (bv.of_Z (-1)) A2 A2 RISCV_ADDI)
  ; AST_AnnotInstr (ITYPE (bv.of_Z 1) A3 A3 RISCV_ADDI)
  ; AST_AnnotInstr (ITYPE (bv.of_Z 1) A1 A1 RISCV_ADDI)
  ; AST_AnnotInstr (BTYPE (bv.of_Z (-20)) X0 A2 RISCV_BNE) ].

(* the loop state with c bytes to go, k done, cursors p (source) r (dest) *)
Definition mc_state {Σ} (s d e f c k p r : Term Σ ty_xlenbits)
    (done rest drest : Term Σ (clemv_ty 1)) : Assertion Σ :=
  ( clem_arrv 1 1 "sdone" s k p done ∗ clem_arrv 1 1 "srest" p c e rest
    ∗ clem_arrv 1 1 "ddone" d k r done ∗ clem_arrv 1 1 "drest" r c f drest
    ∗ A1 ↦ᵣ p ∗ A3 ↦ᵣ r ∗ A2 ↦ᵣ c )%asn.

Definition mc_inv : Assertion (mcCtx ▻ "a"∷ty_xlenbits) :=
  ( asn.exist "c" ty_xlenbits (asn.exist "k" ty_xlenbits
    (asn.exist "p" ty_xlenbits (asn.exist "r" ty_xlenbits
    (asn.exist "done" (clemv_ty 1) (asn.exist "rest" (clemv_ty 1)
    (asn.exist "drest" (clemv_ty 1)
      ( mc_state (term_var "s") (term_var "d") (term_var "e") (term_var "f")
          (term_var "c") (term_var "k") (term_var "p") (term_var "r")
          (term_var "done") (term_var "rest") (term_var "drest")
        ∗ secLeakvar "c" ∗ secLeakvar "p" ∗ secLeakvar "r"
        ∗ clem_nonzero (term_var "c")
        ∗ asn.formula (formula_propeq (term_var "vs")
            (term_binop bop.append (term_var "done") (term_var "rest"))))))))))
    ∗ asn.exist "v4" ty_xlenbits (A4 ↦ᵣ term_var "v4") )%asn.

Definition mc_post : Assertion (mcCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( asn.exist "k" ty_xlenbits
    (asn.exist "p" ty_xlenbits (asn.exist "r" ty_xlenbits
    (asn.exist "done" (clemv_ty 1) (asn.exist "rest" (clemv_ty 1)
    (asn.exist "drest" (clemv_ty 1)
      ( mc_state (term_var "s") (term_var "d") (term_var "e") (term_var "f")
          (term_val ty_xlenbits bv.zero) (term_var "k") (term_var "p") (term_var "r")
          (term_var "done") (term_var "rest") (term_var "drest")
        ∗ asn.formula (formula_propeq (term_var "vs")
            (term_binop bop.append (term_var "done") (term_var "rest")))))))))
    ∗ asn.exist "v4" ty_xlenbits (A4 ↦ᵣ term_var "v4") )%asn.

Definition mcRec : @CFGVerifierContract mcCtx :=
  gen_seg_contract (term_var "q") (term_var "q") mc_instrs 24 16 [] mc_inv mc_post.

Lemma valid_mc_loop : cfg_vc_loop mcRec mc_annot.
Proof. Time solve_mb_vc. Qed.

(* NEGATIVE CONTROLS.  The value equation is really checked: the swapped
   order rest ++ done is rejected. *)
Definition mc_post_swap : Assertion (mcCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( asn.exist "k" ty_xlenbits
    (asn.exist "p" ty_xlenbits (asn.exist "r" ty_xlenbits
    (asn.exist "done" (clemv_ty 1) (asn.exist "rest" (clemv_ty 1)
    (asn.exist "drest" (clemv_ty 1)
      ( mc_state (term_var "s") (term_var "d") (term_var "e") (term_var "f")
          (term_val ty_xlenbits bv.zero) (term_var "k") (term_var "p") (term_var "r")
          (term_var "done") (term_var "rest") (term_var "drest")
        ∗ asn.formula (formula_propeq (term_var "vs")
            (term_binop bop.append (term_var "rest") (term_var "done")))))))))
    ∗ asn.exist "v4" ty_xlenbits (A4 ↦ᵣ term_var "v4") )%asn.
Goal cfg_vc_loop (gen_seg_contract (term_var "q") (term_var "q") mc_instrs 24 16 []
                    mc_inv mc_post_swap) mc_annot.
Proof. Fail solve_mb_vc. Abort.

(* ... and the invariant is not vacuous *)
Goal cfg_vc_loop (gen_seg_contract (term_var "q") (term_var "q") mc_instrs 24 16 []
                    mc_inv (mc_post ∗ asn.formula (formula_relop bop.neq (term_var "s") (term_var "s")))%asn)
                 mc_annot.
Proof. Fail solve_mb_vc. Abort.

(* peval_append fires on concrete terms (inside PartialEvaluation's functor
   the terms are abstract, so its self-tests live here) *)
Definition zzΣ : LCtx := ["d"∷clemv_ty 1; "r"∷clemv_ty 1; "x"∷clem_cell_ty 1].
Lemma selftest_peval_append :
  peval (Σ := zzΣ) (term_binop bop.append
           (term_binop bop.append (term_var "d")
              (term_binop bop.cons (term_var "x") (term_val (clemv_ty 1) nil)))
           (term_var "r"))
  = term_binop bop.append (term_var "d") (term_binop bop.cons (term_var "x") (term_var "r")).
Proof. vm_compute. reflexivity. Qed.
