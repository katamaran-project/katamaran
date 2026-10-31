(* ========================================================================= *)
(* Example/Muladd/MuladdParamLoopD.v -- PLAN-array-invariants Phase 0 probe (untracked).      *)
(*                                                                           *)
(* muladd's loop D (idx 84-89, the in-place memmove), ON ITS OWN, as ONE     *)
(* loop contract (PLAN-loop-rule.md) over `arrv` chunks (PLAN-arrv: values  *)
(* ∃, nothing mentions them; tags "vx" for x's source, "Dx" for the moved   *)
(* array, D's done array):                                                  *)
(*                                                                           *)
(*   +0  lw   S1, -4(S0)     <- ghost clem_arrv_take_first (stride -4) before          *)
(*   +4  addi T6, T6, -1                                                     *)
(*   +8  addi S2, S0, -4                                                     *)
(*   +12 sw   S1, 0(S0)      <- ghost clem_arrv_add_first (stride 4) after             *)
(*   +16 mv   S0, S2                                                         *)
(*   +20 bnez T6, -20                                                        *)
(*   +24 exit                                                                *)
(* ========================================================================= *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.


Definition d_instrs : list AST :=
  [ LOAD (bv.of_Z (-4)) S0 S1 false WORD
  ; ITYPE (bv.of_Z (-1)) T6 T6 RISCV_ADDI
  ; ITYPE (bv.of_Z (-4)) S0 S2 RISCV_ADDI
  ; STORE (bv.of_Z 0) S1 S0 WORD
  ; ITYPE (bv.of_Z 0) S2 S0 RISCV_ADDI
  ; BTYPE (bv.of_Z (-20)) X0 T6 RISCV_BNE ].

(* ------------------------------------------------------------------------ *)
(* Vocabulary                                                               *)
(* ------------------------------------------------------------------------ *)

Definition t_off {Σ} (t : Term Σ ty_xlenbits) (z : Z) : Term Σ ty_xlenbits :=
  term_binop bop.bvadd t (term_val ty_xlenbits (bv.of_Z z)).

(* an array tagged t whose VALUE no assertion mentions: ∃, bound by the
   chunk's own match *)
Definition asn_arr {Σ} (w : nat) (s : Z) (t : string) (a n e : Term Σ ty_xlenbits)
    : Assertion Σ :=
  asn.exist "vs" (clemv_ty w)
    (clem_arrv w s t (subst a sub_wk1) (subst n sub_wk1) (subst e sub_wk1)
       (@term_var _ "vs" _ ctx.in_zero)).
Definition asn_arr_angelic {Σ} (w : nat) (s : Z) (t : string) (a n e : Term Σ ty_xlenbits)
    : Assertion Σ :=
  asn.exist "vs" (clemv_ty w)
    (clem_arrv_angelic w s t (subst a sub_wk1) (subst n sub_wk1) (subst e sub_wk1)
       (@term_var _ "vs" _ ctx.in_zero)).

Definition asn_in_range {Σ} (x : Term Σ ty_xlenbits) : Assertion Σ :=
  asn.formula (formula_relop bop.le
    (term_binop bop.plus (term_unop uop.unsigned x) (term_val ty.int 4%Z))
    (term_val ty.int (Z.of_N maxAddr))).

Definition asn_ne0 {Σ} (t : Term Σ ty_xlenbits) : Assertion Σ :=
  asn.formula (formula_relop bop.neq t (term_val ty_xlenbits bv.zero)).

(* ------------------------------------------------------------------------ *)
(* The loop block                                                           *)
(* ------------------------------------------------------------------------ *)

(* The PARAMETERS (PLAN-loop-rule.md, L2): q the code base, E and T the two
   arrays' far ends -- nothing else stays fixed across trips.  The
   destination dp, the counter c and the moved count k change, so they are
   existential in the invariant (d_inv_core is its body). *)
Definition dCtx : LCtx :=
  ["q"∷ty_xlenbits; "E"∷ty_xlenbits; "T"∷ty_xlenbits].

Definition dTripCtx : LCtx :=
  dCtx ▻ "a"∷ty_xlenbits ▻ "dp"∷ty_xlenbits ▻ "c"∷ty_xlenbits ▻ "k"∷ty_xlenbits.

Definition asn_trip (body : Assertion dTripCtx) : Assertion (dCtx ▻ "a"∷ty_xlenbits) :=
  asn.exist "dp" ty_xlenbits (asn.exist "c" ty_xlenbits (asn.exist "k" ty_xlenbits body)).

Definition d_inv_core : Assertion dTripCtx :=
  ( S0 ↦ᵣ term_var "dp" ∗ secLeakvar "dp"
    ∗ T6 ↦ᵣ term_var "c" ∗ secLeakvar "c" ∗ asn_ne0 (term_var "c")
    ∗ asn.exist "v1" ty_xlenbits (S1 ↦ᵣ term_var "v1")
    ∗ asn.exist "v2" ty_xlenbits (S2 ↦ᵣ term_var "v2")
    (* sources not yet moved, walking DOWN *)
    ∗ asn_arr 4 (-4) "vx" (t_off (term_var "dp") (-4)) (term_var "c") (term_var "E")
    (* this trip's destination *)
    ∗ asn.exist "w" ty_xlenbits (term_var "dp" ↦ₘ term_var "w")
    ∗ asn_in_range (term_var "dp")
    (* already moved -- EMPTY at a caller's entry, so it comes from a seed
       (clem_arrv_empty) and is matched ANGELICALLY *)
    ∗ asn_arr_angelic 4 4 "Dx" (t_off (term_var "dp") 4) (term_var "k") (term_var "T") )%asn.

Definition d_inv : Assertion (dCtx ▻ "a"∷ty_xlenbits) := asn_trip d_inv_core.

Definition d_post
    : Assertion (dCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  (* `g`, the empty source remainder's START, is the post's one existential
     and it comes FIRST, bare, in an angelically matched chunk: consuming
     the post binds it by a solved-form equation, and a CALLER learns it by
     clem_arrv_empty_elim as `g = E`, again solved form (the solver does not
     solve `c + f = t` for f, so a post stated over `f - 4` could not be
     located again -- Example/ZZArrDExit.v). *)
  ( asn.exist "g" ty_xlenbits
      ( asn_arr_angelic 4 (-4) "vx" (term_var "g") (term_val ty_xlenbits bv.zero) (term_var "E")
        ∗ S0 ↦ᵣ t_off (term_var "g") 4
        ∗ T6 ↦ᵣ term_val ty_xlenbits bv.zero
        ∗ asn.exist "w" ty_xlenbits (t_off (term_var "g") 4 ↦ₘ term_var "w")
        ∗ asn.exist "m" ty_xlenbits
            (asn_arr 4 4 "Dx" (t_off (term_var "g") 8) (term_var "m") (term_var "T"))
        (* hand back what the precondition consumed *)
        ∗ asn.exist "v1" ty_xlenbits (S1 ↦ᵣ term_var "v1")
        ∗ asn.exist "v2" ty_xlenbits (S2 ↦ᵣ term_var "v2") ) )%asn.

Definition dRec : @CFGVerifierContract dCtx :=
  gen_seg_contract (term_var "q") (term_var "q") d_instrs 24 10 [] d_inv d_post.

Definition dRecBlk : BlkAnnot := {| blk_ctx := dCtx ; blk_contract := dRec |}.

Definition d_annot : list AnnotInstr :=
  [ {| ai_ghost_before := [AnnotCLemma (clem_arrv_take_first 4 (-4) "vx")]
     ; ai_instr        := LOAD (bv.of_Z (-4)) S0 S1 false WORD
     ; ai_ghost_after  := []
     ; ai_block        := None |}
  ; AST_AnnotInstr (ITYPE (bv.of_Z (-1)) T6 T6 RISCV_ADDI)
  ; AST_AnnotInstr (ITYPE (bv.of_Z (-4)) S0 S2 RISCV_ADDI)
  ; {| ai_ghost_before := []
     ; ai_instr        := STORE (bv.of_Z 0) S1 S0 WORD
     ; ai_ghost_after  := [AnnotCLemma (clem_arrv_add_first 4 4 "Dx")]
     ; ai_block        := None |}
  ; AST_AnnotInstr (ITYPE (bv.of_Z 0) S2 S0 RISCV_ADDI)
  ; AST_AnnotInstr (BTYPE (bv.of_Z (-20)) X0 T6 RISCV_BNE) ].

Lemma valid_d_rec : cfg_vc_loop dRec d_annot.
Proof. solve_param_vc. Qed.

(* ------------------------------------------------------------------------ *)
(* NEGATIVE CONTROLS: the loop VC is not vacuous.                           *)
(* ------------------------------------------------------------------------ *)

Definition d_contract_of (inv : Assertion (dCtx ▻ "a"∷ty_xlenbits))
    (post : Assertion (dCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
    : @CFGVerifierContract dCtx :=
  gen_seg_contract (term_var "q") (term_var "q") d_instrs 24 10 [] inv post.

(* (1) No destination cell: the `sw` has nothing to write to. *)
Definition d_inv_nodest : Assertion (dCtx ▻ "a"∷ty_xlenbits) := asn_trip
  ( S0 ↦ᵣ term_var "dp" ∗ secLeakvar "dp"
    ∗ T6 ↦ᵣ term_var "c" ∗ secLeakvar "c" ∗ asn_ne0 (term_var "c")
    ∗ asn.exist "v1" ty_xlenbits (S1 ↦ᵣ term_var "v1")
    ∗ asn.exist "v2" ty_xlenbits (S2 ↦ᵣ term_var "v2")
    ∗ asn_arr 4 (-4) "vx" (t_off (term_var "dp") (-4)) (term_var "c") (term_var "E")
    ∗ asn_arr 4 4 "Dx" (t_off (term_var "dp") 4) (term_var "k") (term_var "T") )%asn.

Goal let c := d_contract_of d_inv_nodest d_post in
     cfg_vc_loop c d_annot.
Proof. intros c. Fail solve_param_vc. Abort.

(* (2) A false post: the counter is 0 at exit, not 1. *)
Definition d_post_bad
    : Assertion (dCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( asn.exist "f" ty_xlenbits
      ( S0 ↦ᵣ term_var "f"
        ∗ T6 ↦ᵣ term_val ty_xlenbits (bv.of_N 1)
        ∗ asn.exist "w" ty_xlenbits (term_var "f" ↦ₘ term_var "w")
        ∗ asn.exist "m" ty_xlenbits
            (asn_arr 4 4 "Dx" (t_off (term_var "f") 4) (term_var "m") (term_var "T"))
        ∗ asn_arr 4 (-4) "vx" (t_off (term_var "f") (-4))
            (term_val ty_xlenbits bv.zero) (term_var "E") ) )%asn.

Goal let c := d_contract_of d_inv d_post_bad in
     cfg_vc_loop c d_annot.
Proof. intros c. Fail solve_param_vc. Abort.

(* (3) An invariant the body does NOT preserve: with `c <> 1`, at c = 2 the
   back edge is taken and owes `c-1 <> 1`, i.e. `1 <> 1`.  Rejected only if
   the stop at the head really re-establishes the invariant. *)
Definition d_inv_not1 : Assertion (dCtx ▻ "a"∷ty_xlenbits) := asn_trip
  ( d_inv_core ∗ asn.formula (formula_relop bop.neq (term_var "c")
                                (term_val ty_xlenbits (bv.of_N 1))) )%asn.

Goal let c := d_contract_of d_inv_not1 d_post in
     cfg_vc_loop c d_annot.
Proof. intros c. Fail solve_param_vc. Abort.

(* ------------------------------------------------------------------------ *)
(* THE LOOP AS A WHOLE PROGRAM (Phase 2): dLink starts AT the loop, with     *)
(* dRecBlk as an ORDINARY ai_block (fires at step 0, like CountdownRec's     *)
(* cdLink), so the loop is one step and the run exits at +24.  Its           *)
(* precondition is D's invariant; the block's own code bound is the outer    *)
(* one (both 24 bytes), so nothing else is needed.                           *)
(* ------------------------------------------------------------------------ *)
Definition dLink : @CFGVerifierContract dCtx :=
  gen_seg_contract (term_var "q") (term_var "q") d_instrs 24 4 [] d_inv d_post.

Definition d_link_annot : list AnnotInstr :=
  [ {| ai_ghost_before := []
     ; ai_instr        := LOAD (bv.of_Z (-4)) S0 S1 false WORD
     ; ai_ghost_after  := []
     ; ai_block        := Some dRecBlk |}
  ; AST_AnnotInstr (ITYPE (bv.of_Z (-1)) T6 T6 RISCV_ADDI)
  ; AST_AnnotInstr (ITYPE (bv.of_Z (-4)) S0 S2 RISCV_ADDI)
  ; AST_AnnotInstr (STORE (bv.of_Z 0) S1 S0 WORD)
  ; AST_AnnotInstr (ITYPE (bv.of_Z 0) S2 S0 RISCV_ADDI)
  ; AST_AnnotInstr (BTYPE (bv.of_Z (-20)) X0 T6 RISCV_BNE) ].

Lemma valid_d_link : cfg_vc dLink d_link_annot.
Proof. solve_param_vc. Qed.
