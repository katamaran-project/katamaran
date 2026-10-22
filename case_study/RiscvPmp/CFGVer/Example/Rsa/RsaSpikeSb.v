(* ========================================================================= *)
(* Example/Rsa/RsaSpikeSb.v -- PLAN-rsa.md Phase 2, step 2: `sb` at WIDTH 1. *)
(* LIGHT, VCs only.                                                          *)
(*                                                                           *)
(* sep_contract_mem_write_value is width-generic but had never run at width  *)
(* 1.  Three segments, the loop bodies of picolibc's -Os memset and memcpy   *)
(* (PLAN-rsa.md §3 O1), over byte arrays `arr pub 1 1`:                      *)
(*  - valid_sb_sec: `sb a1,0(a0); addi a0,a0,1`, a SECRET byte into a       *)
(*    secret array: take the first cell, store, add it back.                 *)
(*  - valid_sb_pub: the same into a PUBLIC array with a public fill byte --  *)
(*    needs secLeak (truncate v) from secLeak v.                             *)
(*  - valid_cpy: `lbu a4,0(a1); sb a4,0(a3)`, one byte between two public   *)
(*    arrays of the SAME shape (both stride 1).                              *)
(* plus a negative control: a secret byte into a public array is rejected.  *)
(* ========================================================================= *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamClose.

Definition sb_arr {Σ} (pub : bool) (a n e : Term Σ ty_xlenbits) : Assertion Σ :=
  asn.chunk (chunk_user (arr pub 1 1) [a; n; e]).

Definition t_inc {Σ} (a : Term Σ ty_xlenbits) : Term Σ ty_xlenbits :=
  term_binop bop.bvadd a (term_val ty_xlenbits (bv.of_Z 1)).

(* ------------------------------------------------------------------------ *)
(* memset's body                                                            *)
(* ------------------------------------------------------------------------ *)
Definition sbCtx : LCtx :=
  ["q"∷ty_xlenbits; "p"∷ty_xlenbits; "n"∷ty_xlenbits; "e"∷ty_xlenbits;
   "v"∷ty_xlenbits].

Definition sb_instrs : list AST :=
  [ STORE (bv.of_Z 0) A1 A0 BYTE              (* sb   a1, 0(a0) *)
  ; ITYPE (bv.of_Z 1) A0 A0 RISCV_ADDI ].     (* addi a0, a0, 1 *)

Definition sb_annot (pub : bool) : list AnnotInstr :=
  [ {| ai_ghost_before := [ AnnotCLemma (clem_arr_take_first pub 1 1) ]
     ; ai_instr := STORE (bv.of_Z 0) A1 A0 BYTE
     ; ai_ghost_after := [ AnnotCLemma (clem_arr_add_first pub 1 1) ]
     ; ai_block := None |}
  ; AST_AnnotInstr (ITYPE (bv.of_Z 1) A0 A0 RISCV_ADDI) ].

(* the array at p is unchanged as a chunk; a0 moved one byte on *)
Definition sb_pre (pub vpub : bool) : Assertion (sbCtx ▻ "a"∷ty_xlenbits) :=
  ( sb_arr pub (term_var "p") (term_var "n") (term_var "e")
    ∗ asn.formula (formula_relop bop.neq (term_var "n") (term_val ty_xlenbits bv.zero))
    ∗ secLeakvar "p" ∗ secLeakvar "n" ∗ secLeakvar "e"
    ∗ (if vpub then secLeakvar "v" else ⊤)
    ∗ A0 ↦ᵣ term_var "p" ∗ A1 ↦ᵣ term_var "v" )%asn.

Definition sb_post (pub : bool) : Assertion (sbCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( sb_arr pub (term_var "p") (term_var "n") (term_var "e")
    ∗ A0 ↦ᵣ t_inc (term_var "p") ∗ A1 ↦ᵣ term_var "v" )%asn.

Definition sbRec (pub vpub : bool) : @CFGVerifierContract sbCtx :=
  gen_seg_contract (term_var "q") (term_var "q") sb_instrs 8 6 []
    (sb_pre pub vpub) (sb_post pub).

Lemma valid_sb_sec : cfg_vc_loop (sbRec false false) (sb_annot false).
Proof. Time solve_mb_vc. Qed.

Lemma valid_sb_pub : cfg_vc_loop (sbRec true true) (sb_annot true).
Proof. Time solve_mb_vc. Qed.

(* NEGATIVE CONTROLS: a secret byte into a public array is rejected; and
   valid_sb_sec is not vacuous -- its precondition does not prove p ≠ p.
   (A post saying `arr true` after a secret store is NOT a test of secrecy:
   arr true and arr false are different predicates, so it fails on the name.) *)
Goal cfg_vc_loop (sbRec true false) (sb_annot true).
Proof. Fail solve_mb_vc. Abort.
Goal cfg_vc_loop (gen_seg_contract (term_var "q") (term_var "q") sb_instrs 8 6 []
                    (sb_pre false false)
                    (sb_post false
                     ∗ asn.formula (formula_relop bop.neq (term_var "p") (term_var "p"))))%asn
                 (sb_annot false).
Proof. Fail solve_mb_vc. Abort.

(* ------------------------------------------------------------------------ *)
(* memcpy's body: one byte from the array at s to the PUBLIC one at d      *)
(* ------------------------------------------------------------------------ *)
Definition cpyCtx : LCtx :=
  ["q"∷ty_xlenbits; "s"∷ty_xlenbits; "n"∷ty_xlenbits; "e"∷ty_xlenbits;
   "d"∷ty_xlenbits; "m"∷ty_xlenbits; "f"∷ty_xlenbits].

Definition cpy_instrs : list AST :=
  [ LOAD (bv.of_Z 0) A1 A4 true BYTE           (* lbu  a4, 0(a1) *)
  ; STORE (bv.of_Z 0) A4 A3 BYTE ].            (* sb   a4, 0(a3) *)

Definition cpy_annot (spub : bool) : list AnnotInstr :=
  [ {| ai_ghost_before := [ AnnotCLemma (clem_arr_take_first spub 1 1) ]
     ; ai_instr := LOAD (bv.of_Z 0) A1 A4 true BYTE
     ; ai_ghost_after := [ AnnotCLemma (clem_arr_add_first spub 1 1) ]
     ; ai_block := None |}
  ; {| ai_ghost_before := [ AnnotCLemma (clem_arr_take_first true 1 1) ]
     ; ai_instr := STORE (bv.of_Z 0) A4 A3 BYTE
     ; ai_ghost_after := [ AnnotCLemma (clem_arr_add_first true 1 1) ]
     ; ai_block := None |} ].

Definition cpy_pre (spub : bool) : Assertion (cpyCtx ▻ "a"∷ty_xlenbits) :=
  ( sb_arr spub (term_var "s") (term_var "n") (term_var "e")
    ∗ sb_arr true (term_var "d") (term_var "m") (term_var "f")
    ∗ asn.formula (formula_relop bop.neq (term_var "n") (term_val ty_xlenbits bv.zero))
    ∗ asn.formula (formula_relop bop.neq (term_var "m") (term_val ty_xlenbits bv.zero))
    ∗ secLeakvar "s" ∗ secLeakvar "n" ∗ secLeakvar "e"
    ∗ secLeakvar "d" ∗ secLeakvar "m" ∗ secLeakvar "f"
    ∗ A1 ↦ᵣ term_var "s" ∗ A3 ↦ᵣ term_var "d"
    ∗ asn.exist "v4" ty_xlenbits (A4 ↦ᵣ term_var "v4") )%asn.

Definition cpy_post (spub : bool) : Assertion (cpyCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( sb_arr spub (term_var "s") (term_var "n") (term_var "e")
    ∗ sb_arr true (term_var "d") (term_var "m") (term_var "f")
    ∗ A1 ↦ᵣ term_var "s" ∗ A3 ↦ᵣ term_var "d"
    ∗ asn.exist "v4" ty_xlenbits (A4 ↦ᵣ term_var "v4") )%asn.

Definition cpyRec (spub : bool) : @CFGVerifierContract cpyCtx :=
  gen_seg_contract (term_var "q") (term_var "q") cpy_instrs 8 6 []
    (cpy_pre spub) (cpy_post spub).

Lemma valid_cpy : cfg_vc_loop (cpyRec true) (cpy_annot true).
Proof. Time solve_mb_vc. Qed.

(* NEGATIVE CONTROL: copying out of a SECRET array into the public one is
   rejected -- the loaded byte really reaches the store, and the angelic arr
   match cannot dodge it by picking the other array. *)
Goal cfg_vc_loop (cpyRec false) (cpy_annot false).
Proof. Fail solve_mb_vc. Abort.

(* ... and valid_cpy is not vacuous. *)
Goal cfg_vc_loop (gen_seg_contract (term_var "q") (term_var "q") cpy_instrs 8 6 []
                    (cpy_pre true)
                    (cpy_post true
                     ∗ asn.formula (formula_relop bop.neq (term_var "d") (term_var "d"))))%asn
                 (cpy_annot true).
Proof. Fail solve_mb_vc. Abort.
