(* PROBE (PLAN-arrv Phase A): every new arrv ghost lemma used once in a
   green VC, each with a negative control.  One NOP, the ghosts before it;
   pre/post say what the lemma must do.  LIGHT, VCs only. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamClose.

Definition NOP : AST := ITYPE (bv.of_Z 0) X0 X0 RISCV_ADDI.

Definition zΣ : LCtx :=
  ["q"∷ty_xlenbits; "p"∷ty_xlenbits; "n"∷ty_xlenbits; "e"∷ty_xlenbits;
   "g"∷ty_xlenbits; "f"∷ty_xlenbits; "n2"∷ty_xlenbits; "x"∷clem_cell_ty 1;
   "vs"∷clemv_ty 1; "ws"∷clemv_ty 1].

Definition zpre := Assertion (zΣ ▻ "a"∷ty_xlenbits).
Definition zpost := Assertion (zΣ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits).

(* the VC of one NOP with ghosts gs before it, exit at the fall-through
   (plain cfg_vc: a loop VC's exit-or-head disjunction would hide an
   angelic variable's equation from postprocessing) *)
Definition zvc (gs : list Annot) (pre : zpre) (post : zpost) : Prop :=
  cfg_vc (gen_seg_contract (term_var "q") (term_var "q") [NOP] 4 4 [] pre post)
    [ {| ai_ghost_before := gs; ai_instr := NOP; ai_ghost_after := []; ai_block := None |} ].

Notation V s := (term_var s).
Definition nil1 {Σ} : Term Σ (clemv_ty 1) := term_val (clemv_ty 1) nil.
Definition cons1 {Σ} (x : Term Σ (clem_cell_ty 1)) (r : Term Σ (clemv_ty 1)) := term_binop bop.cons x r.
Definition app1 {Σ} (u v : Term Σ (clemv_ty 1)) := term_binop bop.append u v.
Definition rev1 {Σ} (u : Term Σ (clemv_ty 1)) := term_unop uop.rev u.
Definition eqf {Σ σ} (t u : Term Σ σ) : Assertion Σ := asn.formula (formula_propeq t u).

(* ---- take_last: the last cell, by equation; public parts by framing ---- *)
Definition tl_pre (pub : bool) : zpre :=
  ( clem_arrv 1 1 (V "p") (V "n") (V "e") (V "vs") ∗ clem_nonzero (V "n")
    ∗ (if pub then secLeakvar "vs" else ⊤) )%asn.
Definition tl_post (swap : bool) : zpost :=
  ( asn.exist "v" (clem_cell_ty 1)
      (clem_ptsto 1 (clem_off (V "e") (-1)) (V "v") ∗ asn.formula (formula_secLeak (V "v"))
       ∗ asn.exist "r" (clemv_ty 1)
           (clem_arrv 1 1 (V "p") (clem_off (V "n") (-1)) (clem_off (V "e") (-1)) (V "r")
            ∗ eqf (V "vs") (if swap then cons1 (V "v") (V "r") else app1 (V "r") (cons1 (V "v") nil1)))) )%asn.
Lemma zz_take_last : zvc [AnnotCLemma (clem_arrv_take_last 1 1)] (tl_pre true) (tl_post false).
Proof. solve_mb_vc. Qed.
Goal zvc [AnnotCLemma (clem_arrv_take_last 1 1)] (tl_pre false) (tl_post false).
Proof. Fail solve_mb_vc. Abort.
Goal zvc [AnnotCLemma (clem_arrv_take_last 1 1)] (tl_pre true) (tl_post true).
Proof. Fail solve_mb_vc. Abort.

(* ---- nonempty: a ≠ e is enough for a take ---- *)
Definition ne_pre (hyp : bool) : zpre :=
  ( clem_arrv 1 1 (V "p") (V "n") (V "e") (V "vs")
    ∗ (if hyp then asn.formula (formula_relop bop.neq (V "p") (V "e")) else ⊤) )%asn.
Definition ne_post : zpost :=
  ( asn.exist "v" (clem_cell_ty 1) (clem_ptsto 1 (V "p") (V "v")) )%asn.
Lemma zz_nonempty :
  zvc [AnnotCLemma (clem_arrv_nonempty 1 1); AnnotCLemma (clem_arrv_take_first 1 1)] (ne_pre true) ne_post.
Proof. solve_mb_vc. Qed.
Goal zvc [AnnotCLemma (clem_arrv_nonempty 1 1); AnnotCLemma (clem_arrv_take_first 1 1)] (ne_pre false) ne_post.
Proof. Fail solve_mb_vc. Abort.

(* ---- empty: a seed holding [] (its address is bound by a later ANGELIC
   match, as at a loop block's entry) ---- *)
Definition em_pre : zpre := secLeakvar "p".
Definition em_post : zpost := clem_arrv_angelic 1 1 (V "p") (term_val ty_xlenbits bv.zero) (V "p") nil1.
Lemma zz_empty : zvc [AnnotCLemma (clem_arrv_empty 1 1)] em_pre em_post.
Proof. solve_mb_vc. Qed.
Goal zvc [] em_pre em_post.
Proof. Fail solve_mb_vc. Abort.

(* ---- empty_elim: start = end, and nothing about the value ---- *)
Definition ee_pre : zpre := clem_arrv 1 1 (V "p") (term_val ty_xlenbits bv.zero) (V "e") (V "vs").
Definition ee_post (val : bool) : zpost :=
  ( asn.formula (formula_relop bop.eq (V "p") (V "e"))
    ∗ (if val then eqf (V "vs") nil1 else ⊤) )%asn.
Lemma zz_empty_elim : zvc [AnnotCLemma (clem_arrv_empty_elim 1 1)] ee_pre (ee_post false).
Proof. solve_mb_vc. Qed.
Goal zvc [] ee_pre (ee_post false).
Proof. Fail solve_mb_vc. Abort.
Goal zvc [AnnotCLemma (clem_arrv_empty_elim 1 1)] ee_pre (ee_post true).
Proof. Fail solve_mb_vc. Abort.

(* ---- lockstep: the second array's end follows ---- *)
Definition ls_pre : zpre :=
  ( clem_arrv 1 1 (V "p") (V "n") (V "e") (V "vs") ∗ clem_arrv 1 1 (V "g") (V "n") (V "f") (V "ws")
    ∗ asn.formula (formula_relop bop.eq (V "p") (V "e")) )%asn.
Definition ls_post : zpost := asn.formula (formula_relop bop.eq (V "g") (V "f")).
Lemma zz_lockstep : zvc [AnnotCLemma (clem_arrv_lockstep 1 1)] ls_pre ls_post.
Proof. solve_mb_vc. Qed.
Goal zvc [] ls_pre ls_post.
Proof. Fail solve_mb_vc. Abort.

(* ---- drop: the array is gone ---- *)
Definition dr_pre : zpre := clem_arrv 1 1 (V "p") (V "n") (V "e") (V "vs").
Lemma zz_drop : zvc [AnnotCLemma (clem_arrv_drop 1 1)] dr_pre ⊤%asn.
Proof. solve_mb_vc. Qed.
Goal zvc [AnnotCLemma (clem_arrv_drop 1 1)] dr_pre
       (clem_arrv 1 1 (V "p") (V "n") (V "e") (V "vs")).
Proof. Fail solve_mb_vc. Abort.

(* ---- flip, after an add_first at stride -1 (muladd's DONE shape, O1):
   rev (x :: done) must meet rev done ++ [x] -- peval_rev ---- *)
Definition fl_pre : zpre :=
  ( clem_arrv 1 (-1) (V "p") (V "n") (V "e") (V "vs")
    ∗ clem_ptsto 1 (clem_off (V "p") 1) (V "x") ∗ clem_range 1 (clem_off (V "p") 1) )%asn.
Definition fl_post (swap : bool) : zpost :=
  clem_arrv 1 1 (clem_off (V "e") 1) (clem_off (V "n") 1) (clem_off (V "p") 2)
    (if swap then cons1 (V "x") (rev1 (V "vs")) else app1 (rev1 (V "vs")) (cons1 (V "x") nil1)).
Lemma zz_flip :
  zvc [AnnotCLemma (clem_arrv_add_first 1 (-1)); AnnotCLemma (clem_arrv_flip 1 (-1))] fl_pre (fl_post false).
Proof. solve_mb_vc. Qed.
Goal zvc [AnnotCLemma (clem_arrv_add_first 1 (-1)); AnnotCLemma (clem_arrv_flip 1 (-1))] fl_pre (fl_post true).
Proof. Fail solve_mb_vc. Abort.

(* ---- join: adjacent arrays, values appended in order ---- *)
Definition jn_pre : zpre :=
  ( clem_arrv 1 1 (V "p") (V "n") (V "e") (V "vs") ∗ clem_arrv 1 1 (V "e") (V "n2") (V "f") (V "ws") )%asn.
Definition jn_post (swap : bool) : zpost :=
  clem_arrv 1 1 (V "p") (term_binop bop.bvadd (V "n") (V "n2")) (V "f")
    (if swap then app1 (V "ws") (V "vs") else app1 (V "vs") (V "ws")).
Lemma zz_join : zvc [AnnotCLemma (clem_arrv_join 1 1)] jn_pre (jn_post false).
Proof. solve_mb_vc. Qed.
Goal zvc [AnnotCLemma (clem_arrv_join 1 1)] jn_pre (jn_post true).
Proof. Fail solve_mb_vc. Abort.

(* ---- pad: absorb an empty remainder's value (memcpy's exit) ---- *)
Definition pd_pre : zpre :=
  ( clem_arrv 1 1 (V "p") (V "n") (V "e") (V "vs")
    ∗ clem_arrv 1 1 (V "g") (term_val ty_xlenbits bv.zero) (V "f") (V "ws") )%asn.
Definition pd_post : zpost :=
  ( clem_arrv 1 1 (V "p") (V "n") (V "e") (app1 (V "vs") (V "ws"))
    ∗ clem_arrv 1 1 (V "g") (term_val ty_xlenbits bv.zero) (V "f") (V "ws") )%asn.
Lemma zz_pad : zvc [AnnotCLemma (clem_arrv_pad 1 1)] pd_pre pd_post.
Proof. solve_mb_vc. Qed.
Goal zvc [] pd_pre pd_post.
Proof. Fail solve_mb_vc. Abort.

(* ---- split at a constant index ---- *)
Definition sp_pre : zpre :=
  ( clem_arrv 1 1 (V "p") (V "n") (V "e") (V "vs")
    ∗ asn.formula (formula_relop bop.bvule (term_val ty_xlenbits (bv.of_N 1)) (V "n")) )%asn.
Definition sp_post (swap : bool) : zpost :=
  asn.exist "v1" (clemv_ty 1) (asn.exist "v2" (clemv_ty 1)
    ( clem_arrv 1 1 (V "p") (term_val ty_xlenbits (bv.of_N 1)) (clem_off (V "p") 1) (V "v1")
      ∗ clem_arrv 1 1 (clem_off (V "p") 1) (clem_off (V "n") (-1)) (V "e") (V "v2")
      ∗ eqf (V "vs") (if swap then app1 (V "v2") (V "v1") else app1 (V "v1") (V "v2")) ))%asn.
Lemma zz_split : zvc [AnnotCLemma (clem_arrv_split 1 1 1)] sp_pre (sp_post false).
Proof. solve_mb_vc. Qed.
Goal zvc [AnnotCLemma (clem_arrv_split 1 1 1)] sp_pre (sp_post true).
Proof. Fail solve_mb_vc. Abort.

(* peval_rev fires on concrete terms (abstract inside its functor) *)
Definition zzΣ : LCtx := ["d"∷clemv_ty 1; "r"∷clemv_ty 1; "x"∷clem_cell_ty 1].
Lemma selftest_peval_rev :
  peval (Σ := zzΣ) (rev1 (app1 (cons1 (term_var "x") (term_var "d")) (rev1 (term_var "r"))))
  = app1 (term_var "r") (app1 (rev1 (term_var "d")) (cons1 (term_var "x") nil1)).
Proof. vm_compute. reflexivity. Qed.
