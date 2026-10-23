(* PROBE (PLAN-arrv GATE B): the v4 caller of RsaSpikeArrv.v redone with a
   WORD array (public header word h, secret limbs ls) and the BYTE memcpy
   contract: to_bytes before the call, of_bytes after it, and the copy's
   first WORD comes back public -- by framing, through the view change.
   LIGHT, VCs only. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamClose.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Rsa.RsaSpikeArrv.

Definition wCtx : LCtx :=
  ["q"∷ty_xlenbits; "p"∷ty_xlenbits; "d"∷ty_xlenbits; "c"∷ty_xlenbits;
   "e"∷ty_xlenbits; "f"∷ty_xlenbits; "h"∷clem_cell_ty 4; "ls"∷clemv_ty 4;
   "ws"∷clemv_ty 1].

Definition w_instrs : list AST := [NOP; NOP; NOP].

(* bytes view before the call (instruction 0's ghosts); memcpy is the block
   on instruction 1 (its own ghosts would not run); words view and the take
   before instruction 2 *)
Definition w_annot : list AnnotInstr :=
  [ {| ai_ghost_before := [ AnnotCLemma clem_arrv_to_bytes ]; ai_instr := NOP
     ; ai_ghost_after := []; ai_block := None |}
  ; {| ai_ghost_before := []; ai_instr := NOP; ai_ghost_after := []
     ; ai_block := Some (cpBlk cp_post) |}
  ; {| ai_ghost_before := [ AnnotCLemma clem_arrv_of_bytes; AnnotCLemma (clem_arrv_take_cons 4 4) ]
     ; ai_instr := NOP; ai_ghost_after := []; ai_block := None |} ].

(* one word array h :: ls of c words at p; a destination of 4c bytes *)
Definition w_pre (hpub bound : bool) : Assertion (wCtx ▻ "a"∷ty_xlenbits) :=
  ( clem_arrv 4 4 (term_var "p") (term_var "c") (term_var "e")
      (term_binop bop.cons (term_var "h") (term_var "ls"))
    ∗ clem_arrv 1 1 (term_var "d") (clem_x4 (term_var "c")) (term_var "f") (term_var "ws")
    ∗ (if bound then asn.formula (formula_relop bop.bvult (term_var "c")
                       (term_val ty_xlenbits (bv.of_N 0x40000000))) else ⊤)
    ∗ (if hpub then secLeakvar "h" else ⊤) )%asn.

(* the copy's first WORD is public *)
Definition w_post : Assertion (wCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( asn.exist "v" (clem_cell_ty 4)
      (clem_ptsto 4 (term_var "d") (term_var "v") ∗ asn.formula (formula_secLeak (term_var "v"))) )%asn.

Definition wRec (hpub bound : bool) : @CFGVerifierContract wCtx :=
  gen_seg_contract (term_var "q") (term_var "q") w_instrs 12 8 [] (w_pre hpub bound) w_post.

Lemma valid_w : cfg_vc (wRec true true) w_annot.
Proof. Time solve_mb_vc. Qed.

(* NEGATIVE CONTROLS.  A secret h: the copy is not public. *)
Goal cfg_vc (wRec false true) w_annot.
Proof. Fail solve_mb_vc. Abort.

(* of_bytes needs the word-count bound (·4 is not injective mod 2^32). *)
Goal cfg_vc (wRec true false) w_annot.
Proof. Fail solve_mb_vc. Abort.

(* to_bytes then of_bytes alone is the identity on the value *)
Definition rt_post : Assertion (wCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  clem_arrv 4 4 (term_var "p") (term_var "c") (term_var "e")
    (term_binop bop.cons (term_var "h") (term_var "ls")).
Lemma valid_rt :
  cfg_vc (gen_seg_contract (term_var "q") (term_var "q") [NOP] 4 4 [] (w_pre false true) rt_post)
    [ {| ai_ghost_before := [ AnnotCLemma clem_arrv_to_bytes; AnnotCLemma clem_arrv_of_bytes ]
       ; ai_instr := NOP; ai_ghost_after := []; ai_block := None |} ].
Proof. solve_mb_vc. Qed.
