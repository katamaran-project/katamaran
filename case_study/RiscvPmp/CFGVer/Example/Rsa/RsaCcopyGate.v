(* ========================================================================= *)
(* Example/Rsa/RsaCcopyGate.v -- PLAN-rsa.md GATE 2: br_ccopy over WORD      *)
(* arrays, called from a word-accessing caller, the word ⇄ byte view        *)
(* changed at the CALL SITE.  LIGHT half (the end theorem: the Result file). *)
(*                                                                           *)
(*   0:  jal ra, br_ccopy        the harness: call once,                     *)
(*   4:  j   _etext              then leave at the fall-through end (64)     *)
(*   8:  br_ccopy                (RsaCcopy.v)                                *)
(*                                                                           *)
(* The caller holds two i31-style integers x (dst) and y (src): a PUBLIC     *)
(* header word h -- the SAME h in both, as for modpow's x and t1 -- and ml   *)
(* secret limb words.  ctl is SECRET.  Afterwards both headers still hold h *)
(* (so h is still public by framing), y is unchanged, x's limbs are unnamed. *)
(*                                                                           *)
(* The view change, before the jal: the header joins the limbs (add_first), *)
(* the whole word array becomes bytes (to_bytes: value regroup (h :: v)) and *)
(* its first word's bytes come into the open (regroup_cons: x₀ .. x₃ ::     *)
(* regroup v, x_k the slices le_bytes takes) -- br_ccopy's precondition    *)
(* shape, with the SAME four terms in both arrays.  After the call, before   *)
(* the j: the four header bytes come off into an array of their own         *)
(* (empty_at + take_cons ×4 + add_last ×4) and become one word again        *)
(* (word_of_bytes1); the limb bytes become words (of_bytes for y, whose      *)
(* value is still regroup v; of_bytes_any for x, whose value br_ccopy left  *)
(* unnamed); the two join, and the header comes off as a cell.               *)
(* ========================================================================= *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamClose.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Rsa.RsaCcopy.

(* q: the code base; x, y: dst and src (A1, A2); n: the byte length (A3);
   ml: the limb words; h: the header word *)
Definition cgCtx : LCtx :=
  ["q"∷ty_xlenbits; "x"∷ty_xlenbits; "y"∷ty_xlenbits; "n"∷ty_xlenbits;
   "ml"∷ty_xlenbits; "h"∷ty_xlenbits].

Definition cg_regs : list (reg_spec_q cgCtx) :=
  [ (A0, Secret); (A1, Known (PVVar "x")); (A2, Known (PVVar "y")); (A3, Known (PVVar "n"))
  ; (X1, Secret); (A4, Secret); (A5, Secret); (A6, Secret) ].

(* n = 4·ml + 4 bytes, 0 < ml < 2^29 *)
Definition cg_facts : Assertion (cgCtx ▻ "a"∷ty_xlenbits) :=
  ( asn.formula (formula_propeq (term_var "n") (clem_off (clem_x4 (term_var "ml")) 4))
    ∗ secLeakvar "ml" ∗ clem_nonzero (term_var "ml")
    ∗ asn.formula (formula_relop bop.bvult (term_var "ml") (term_val ty_xlenbits (bv.of_N 0x20000000))) )%asn.

(* each integer: its header word (public, h) and its limbs (secret), the two
   headers listed first (the statement's layout lemma takes cells in front
   of runs); the values are named "dv"/"vs" because br_ccopy was verified at
   those tags *)
Definition cg_data (ypub : bool) : list (data_spec cgCtx) :=
  [ DPtr (term_var "x"); DCell (Known (term_var "h"))
  ; DPtr (term_var "y"); DCell (Known (term_var "h"))
  ; DPtr (clem_off (term_var "x") 4); DArr false ArrUp (term_var "ml") "dv"
  ; DPtr (clem_off (term_var "y") 4); DArr ypub ArrUp (term_var "ml") "vs" ]%list.

Definition cgCtxV : LCtx := cgCtx ▻▻ data_vctx (cg_data false).

Definition t4 {Σ} (a : Term Σ ty_xlenbits) : Term Σ ty_xlenbits := clem_off a 4.

(* both headers hold h again; y unchanged; x's limbs unnamed *)
Definition cg_post : Assertion (cgCtxV ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( clem_ptsto 4 (term_var "x") (term_var "h")
    ∗ asn.exist "dv'" (clemv_ty 4)
        (clem_arrv 4 4 "dv" (t4 (term_var "x")) (term_var "ml")
           (term_binop bop.bvadd (t4 (term_var "x")) (clem_x4 (term_var "ml"))) (term_var "dv'"))
    ∗ clem_ptsto 4 (term_var "y") (term_var "h")
    ∗ clem_arrv 4 4 "vs" (t4 (term_var "y")) (term_var "ml")
        (term_binop bop.bvadd (t4 (term_var "y")) (clem_x4 (term_var "ml"))) (term_var "vs")
    ∗ asn.exist "w0" ty_xlenbits (A0 ↦ᵣ term_var "w0")
    ∗ asn.exist "w1" ty_xlenbits (X1 ↦ᵣ term_var "w1")
    ∗ asn.exist "w2" ty_xlenbits (A1 ↦ᵣ term_var "w2")
    ∗ asn.exist "w3" ty_xlenbits (A2 ↦ᵣ term_var "w3")
    ∗ asn.exist "w4" ty_xlenbits (A3 ↦ᵣ term_var "w4")
    ∗ asn.exist "w5" ty_xlenbits (A4 ↦ᵣ term_var "w5")
    ∗ asn.exist "w6" ty_xlenbits (A5 ↦ᵣ term_var "w6")
    ∗ asn.exist "w7" ty_xlenbits (A6 ↦ᵣ term_var "w7") )%asn.

(* exit: the fall-through end, +64 = 4 * 16 *)
Definition cgRec (ypub : bool) (post : Assertion (cgCtxV ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
    : @CFGVerifierContract cgCtxV :=
  gen_prog_contract "q" _ cg_regs cg_facts 64 (cg_data ypub) ccf_instrs 10 post.

Definition way_in (t : string) : list Annot :=
  [ cl (clem_arrv_add_first 4 4 t); cl (clem_arrv_to_bytes t); cl (clem_arrv_regroup_cons t) ].
(* `ofb` turns the limb bytes back into words: of_bytes when their value is
   still syntactically regroup v, of_bytes_any when it is not *)
Definition way_back (t th : string) (ofb : CLem) : list Annot :=
  [ cl (clem_arrv_empty_at 1 1 t th)
  ; cl (clem_arrv_take_cons 1 1 t); cl (clem_arrv_take_cons 1 1 t)
  ; cl (clem_arrv_take_cons 1 1 t); cl (clem_arrv_take_cons 1 1 t)
  ; cl (clem_arrv_add_last 1 1 th); cl (clem_arrv_add_last 1 1 th)
  ; cl (clem_arrv_add_last 1 1 th); cl (clem_arrv_add_last 1 1 th)
  ; cl (clem_arrv_word_of_bytes1 th); cl ofb
  ; cl (clem_arrv_join 4 4 th t t); cl (clem_arrv_take_cons 4 4 t) ].

(* br_ccopy is a block on ITS first instruction, index 2 *)
Definition cg_annot : list AnnotInstr :=
  List.map (fun '(i, ins) =>
              {| ai_ghost_before :=
                   if Nat.eqb i 0 then List.app (way_in "dv") (way_in "vs")
                   else if Nat.eqb i 1 then List.app (way_back "dv" "hx" (clem_arrv_of_bytes_any "dv"))
                                                     (way_back "vs" "hy" (clem_arrv_of_bytes "vs"))
                   else nil
               ; ai_instr := ins ; ai_ghost_after := nil
               ; ai_block := if Nat.eqb i 2 then Some (ccfBlk "vs" "dv") else None |})
    (List.combine (List.seq 0 (length ccf_instrs)) ccf_instrs).

Lemma valid_cg : cfg_vc (cgRec false cg_post) cg_annot.
Proof. Time solve_cc_all. Qed.

(* NEGATIVE CONTROL: br_ccopy does not COPY x's limbs from y under a secret
   ctl -- a post claiming x's limbs equal y's is refused *)
Goal cfg_vc (cgRec false
  (( clem_ptsto 4 (term_var "x") (term_var "h")
     ∗ clem_arrv 4 4 "dv" (t4 (term_var "x")) (term_var "ml")
         (term_binop bop.bvadd (t4 (term_var "x")) (clem_x4 (term_var "ml"))) (term_var "vs") )%asn))
  cg_annot.
Proof. Fail solve_cc_all. Abort.
