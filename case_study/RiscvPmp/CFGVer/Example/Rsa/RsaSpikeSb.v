(* ========================================================================= *)
(* Example/Rsa/RsaSpikeSb.v -- PLAN-rsa.md Phase 2, step 2: `sb` at WIDTH 1. *)
(* LIGHT, VCs only.                                                          *)
(*                                                                           *)
(* sep_contract_mem_write_value is width-generic but had never run at width  *)
(* 1.  Three segments, the loop bodies of picolibc's -Os memset and memcpy   *)
(* (PLAN-rsa.md §3 O1), over byte arrays `arrv 1 1` (PLAN-arrv Phase D: a    *)
(* public array is one whose VALUE is public, `secLeak vs`):                *)
(*  - valid_sb_sec: `sb a1,0(a0); addi a0,a0,1`, a SECRET byte into a       *)
(*    secret array: take the first cell, store, add it back.                 *)
(*  - valid_sb_pub: the same into a PUBLIC array with a public fill byte --  *)
(*    needs secLeak (truncate v) from secLeak v.  The store overwrites a     *)
(*    cell, so the array's new value is ∃ (PLAN-arrv D13).                   *)
(*  - valid_cpy: `lbu a4,0(a1); sb a4,0(a3)`, one byte between two public   *)
(*    arrays of the SAME shape (both stride 1); the source comes back with   *)
(*    its own value.                                                         *)
(* plus a negative control: a secret byte into a public array is rejected.  *)
(* ========================================================================= *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamClose.

Definition t_inc {Σ} (a : Term Σ ty_xlenbits) : Term Σ ty_xlenbits :=
  term_binop bop.bvadd a (term_val ty_xlenbits (bv.of_Z 1)).

(* an array whose value is public *)
Definition pub_val {Σ} (pub : bool) (vs : Term Σ (clemv_ty 1)) : Assertion Σ :=
  if pub then asn.formula (formula_secLeak vs) else ⊤%asn.

(* ------------------------------------------------------------------------ *)
(* memset's body                                                            *)
(* ------------------------------------------------------------------------ *)
Definition sbCtx : LCtx :=
  ["q"∷ty_xlenbits; "p"∷ty_xlenbits; "n"∷ty_xlenbits; "e"∷ty_xlenbits;
   "v"∷ty_xlenbits; "vs"∷clemv_ty 1].

Definition sb_instrs : list AST :=
  [ STORE (bv.of_Z 0) A1 A0 BYTE              (* sb   a1, 0(a0) *)
  ; ITYPE (bv.of_Z 1) A0 A0 RISCV_ADDI ].     (* addi a0, a0, 1 *)

Definition sb_annot : list AnnotInstr :=
  [ {| ai_ghost_before := [ AnnotCLemma (clem_arrv_take_first 1 1) ]
     ; ai_instr := STORE (bv.of_Z 0) A1 A0 BYTE
     ; ai_ghost_after := [ AnnotCLemma (clem_arrv_add_first 1 1) ]
     ; ai_block := None |}
  ; AST_AnnotInstr (ITYPE (bv.of_Z 1) A0 A0 RISCV_ADDI) ].

(* the array at p keeps its shape, its value is overwritten; a0 moved one
   byte on *)
Definition sb_pre (pub vpub : bool) : Assertion (sbCtx ▻ "a"∷ty_xlenbits) :=
  ( clem_arrv 1 1 (term_var "p") (term_var "n") (term_var "e") (term_var "vs")
    ∗ pub_val pub (term_var "vs")
    ∗ asn.formula (formula_relop bop.neq (term_var "n") (term_val ty_xlenbits bv.zero))
    ∗ secLeakvar "p" ∗ secLeakvar "n" ∗ secLeakvar "e"
    ∗ (if vpub then secLeakvar "v" else ⊤)
    ∗ A0 ↦ᵣ term_var "p" ∗ A1 ↦ᵣ term_var "v" )%asn.

Definition sb_post (pub : bool) : Assertion (sbCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( asn.exist "ws" (clemv_ty 1)
      (clem_arrv 1 1 (term_var "p") (term_var "n") (term_var "e") (term_var "ws")
       ∗ pub_val pub (term_var "ws"))
    ∗ A0 ↦ᵣ t_inc (term_var "p") ∗ A1 ↦ᵣ term_var "v" )%asn.

Definition sbRec (pub vpub : bool) : @CFGVerifierContract sbCtx :=
  gen_seg_contract (term_var "q") (term_var "q") sb_instrs 8 6 []
    (sb_pre pub vpub) (sb_post pub).

Lemma valid_sb_sec : cfg_vc_loop (sbRec false false) sb_annot.
Proof. Time solve_mb_vc. Qed.

Lemma valid_sb_pub : cfg_vc_loop (sbRec true true) sb_annot.
Proof. Time solve_mb_vc. Qed.

(* NEGATIVE CONTROLS: a secret byte into a public array is rejected; and
   valid_sb_sec is not vacuous -- its precondition does not prove p ≠ p. *)
Goal cfg_vc_loop (sbRec true false) sb_annot.
Proof. Fail solve_mb_vc. Abort.
Goal cfg_vc_loop (gen_seg_contract (term_var "q") (term_var "q") sb_instrs 8 6 []
                    (sb_pre false false)
                    (sb_post false
                     ∗ asn.formula (formula_relop bop.neq (term_var "p") (term_var "p"))))%asn
                 sb_annot.
Proof. Fail solve_mb_vc. Abort.

(* ------------------------------------------------------------------------ *)
(* memcpy's body: one byte from the array at s to the PUBLIC one at d      *)
(* ------------------------------------------------------------------------ *)
Definition cpyCtx : LCtx :=
  ["q"∷ty_xlenbits; "s"∷ty_xlenbits; "n"∷ty_xlenbits; "e"∷ty_xlenbits;
   "d"∷ty_xlenbits; "m"∷ty_xlenbits; "f"∷ty_xlenbits;
   "vs"∷clemv_ty 1; "ws"∷clemv_ty 1].

Definition cpy_instrs : list AST :=
  [ LOAD (bv.of_Z 0) A1 A4 true BYTE           (* lbu  a4, 0(a1) *)
  ; STORE (bv.of_Z 0) A4 A3 BYTE ].            (* sb   a4, 0(a3) *)

Definition cpy_annot : list AnnotInstr :=
  [ {| ai_ghost_before := [ AnnotCLemma (clem_arrv_take_first 1 1) ]
     ; ai_instr := LOAD (bv.of_Z 0) A1 A4 true BYTE
     ; ai_ghost_after := [ AnnotCLemma (clem_arrv_add_first 1 1) ]
     ; ai_block := None |}
  ; {| ai_ghost_before := [ AnnotCLemma (clem_arrv_take_first 1 1) ]
     ; ai_instr := STORE (bv.of_Z 0) A4 A3 BYTE
     ; ai_ghost_after := [ AnnotCLemma (clem_arrv_add_first 1 1) ]
     ; ai_block := None |} ].

Definition cpy_pre (spub : bool) : Assertion (cpyCtx ▻ "a"∷ty_xlenbits) :=
  ( clem_arrv 1 1 (term_var "s") (term_var "n") (term_var "e") (term_var "vs")
    ∗ pub_val spub (term_var "vs")
    ∗ clem_arrv 1 1 (term_var "d") (term_var "m") (term_var "f") (term_var "ws")
    ∗ secLeakvar "ws"
    ∗ asn.formula (formula_relop bop.neq (term_var "n") (term_val ty_xlenbits bv.zero))
    ∗ asn.formula (formula_relop bop.neq (term_var "m") (term_val ty_xlenbits bv.zero))
    ∗ secLeakvar "s" ∗ secLeakvar "n" ∗ secLeakvar "e"
    ∗ secLeakvar "d" ∗ secLeakvar "m" ∗ secLeakvar "f"
    ∗ A1 ↦ᵣ term_var "s" ∗ A3 ↦ᵣ term_var "d"
    ∗ asn.exist "v4" ty_xlenbits (A4 ↦ᵣ term_var "v4") )%asn.

(* the source comes back with its own value; the destination's is ∃ but
   public *)
Definition cpy_post : Assertion (cpyCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( clem_arrv 1 1 (term_var "s") (term_var "n") (term_var "e") (term_var "vs")
    ∗ asn.exist "ws2" (clemv_ty 1)
        (clem_arrv 1 1 (term_var "d") (term_var "m") (term_var "f") (term_var "ws2")
         ∗ secLeakvar "ws2")
    ∗ A1 ↦ᵣ term_var "s" ∗ A3 ↦ᵣ term_var "d"
    ∗ asn.exist "v4" ty_xlenbits (A4 ↦ᵣ term_var "v4") )%asn.

Definition cpyRec (spub : bool) : @CFGVerifierContract cpyCtx :=
  gen_seg_contract (term_var "q") (term_var "q") cpy_instrs 8 6 []
    (cpy_pre spub) cpy_post.

Lemma valid_cpy : cfg_vc_loop (cpyRec true) cpy_annot.
Proof. Time solve_mb_vc. Qed.

(* NEGATIVE CONTROL: copying out of a SECRET array into the public one is
   rejected -- the loaded byte really reaches the store, and the angelic arrv
   match cannot dodge it by picking the other array. *)
Goal cfg_vc_loop (cpyRec false) cpy_annot.
Proof. Fail solve_mb_vc. Abort.

(* ... and valid_cpy is not vacuous. *)
Goal cfg_vc_loop (gen_seg_contract (term_var "q") (term_var "q") cpy_instrs 8 6 []
                    (cpy_pre true)
                    (cpy_post
                     ∗ asn.formula (formula_relop bop.neq (term_var "d") (term_var "d"))))%asn
                 cpy_annot.
Proof. Fail solve_mb_vc. Abort.
