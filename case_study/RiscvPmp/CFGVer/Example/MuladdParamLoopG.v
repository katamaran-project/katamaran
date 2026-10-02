(* ========================================================================= *)
(* Example/MuladdParamLoopG.v -- muladd's loop G (br_divrem's k-loop, idx 135-161, 27  *)
(* instructions, 31 real trips) as ONE self-referential loop block.          *)
(* REGISTER-ONLY, like countdown: the invariant is register publicness.      *)
(*   T4 = k, public, decremented at the head; T5 pinned to 1 (the latch      *)
(*   bltu T5, T4); T0 = d and T6 = j public; T1 = q, T2 = hi, T3 = lo,       *)
(*   S0..S3 secret.  Exit at +108.                                           *)
(* ========================================================================= *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.

Definition S1 : RegIdx := bv.of_nat 9.
Definition S2 : RegIdx := bv.of_nat 18.
Definition S3 : RegIdx := bv.of_nat 19.

Definition g_instrs : list AST :=
  [ ITYPE (bv.of_Z (-1)) T4 T4 RISCV_ADDI
  ; RTYPE T6 T2 S0 RISCV_SLL
  ; RTYPE T4 T3 S1 RISCV_SRL
  ; RTYPE S1 S0 S0 RISCV_OR
  ; RTYPE T0 S0 S1 RISCV_SUB
  ; RTYPE T0 S0 S0 RISCV_XOR
  ; RTYPE T0 S1 S2 RISCV_XOR
  ; RTYPE S0 S2 S0 RISCV_AND
  ; RTYPE S1 S0 S0 RISCV_XOR
  ; ITYPE (bv.of_Z (-1)) S0 S0 RISCV_XORI
  ; SHIFTIOP (bv.of_Z 31) S0 S0 RISCV_SRLI
  ; RTYPE T4 T2 S2 RISCV_SRL
  ; RTYPE S0 S2 S0 RISCV_OR
  ; RTYPE T6 S1 S1 RISCV_SRL
  ; RTYPE T4 T0 S2 RISCV_SLL
  ; RTYPE S2 T3 S2 RISCV_SUB
  ; RTYPE S0 X0 S3 RISCV_SUB
  ; RTYPE T2 S1 S1 RISCV_XOR
  ; RTYPE S3 S1 S1 RISCV_AND
  ; RTYPE T2 S1 T2 RISCV_XOR
  ; RTYPE T3 S2 S1 RISCV_XOR
  ; RTYPE S3 S1 S1 RISCV_AND
  ; RTYPE T3 S1 T3 RISCV_XOR
  ; RTYPE T4 S0 S0 RISCV_SLL
  ; RTYPE T1 S0 T1 RISCV_OR
  ; ITYPE (bv.of_Z 1) T6 T6 RISCV_ADDI
  ; BTYPE (bv.of_Z (-104)) T4 T5 RISCV_BLTU ].

Definition gCtx : LCtx := ["q"∷ty_xlenbits; "k"∷ty_xlenbits].

(* the registers G only needs to exist, at their publicness *)
Definition g_regs_with {Σ} (t5 : Term Σ ty_xlenbits) (t6 : Assertion Σ) : Assertion Σ :=
  ( asn.exist "d" ty_xlenbits (T0 ↦ᵣ term_var "d" ∗ secLeakvar "d")
    ∗ asn.exist "vq" ty_xlenbits (T1 ↦ᵣ term_var "vq")
    ∗ asn.exist "hi" ty_xlenbits (T2 ↦ᵣ term_var "hi")
    ∗ asn.exist "lo" ty_xlenbits (T3 ↦ᵣ term_var "lo")
    ∗ T5 ↦ᵣ t5
    ∗ t6
    ∗ asn.exist "s0" ty_xlenbits (S0 ↦ᵣ term_var "s0")
    ∗ asn.exist "s1" ty_xlenbits (S1 ↦ᵣ term_var "s1")
    ∗ asn.exist "s2" ty_xlenbits (S2 ↦ᵣ term_var "s2")
    ∗ asn.exist "s3" ty_xlenbits (S3 ↦ᵣ term_var "s3") )%asn.

Definition g_j_pub {Σ} : Assertion Σ :=
  asn.exist "j" ty_xlenbits (T6 ↦ᵣ term_var "j" ∗ secLeakvar "j")%asn.

Definition g_inv_with (t6 : Assertion (gCtx ▻ "a"∷ty_xlenbits))
    : Assertion (gCtx ▻ "a"∷ty_xlenbits) :=
  ( T4 ↦ᵣ term_var "k" ∗ secLeakvar "k"
    ∗ g_regs_with (term_val ty_xlenbits (bv.of_N 1)) t6 )%asn.

Definition g_inv := g_inv_with g_j_pub.

Definition g_post_with (t5 : Val ty_xlenbits)
    : Assertion (gCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( asn.exist "kf" ty_xlenbits (T4 ↦ᵣ term_var "kf" ∗ secLeakvar "kf")
    ∗ g_regs_with (term_val ty_xlenbits t5) g_j_pub )%asn.

Definition g_post := g_post_with (bv.of_N 1).

Definition g_contract_of inv post : @CFGVerifierContract gCtx :=
  gen_seg_contract (term_var "q") (term_var "q") g_instrs 108 35 [] inv post.

Definition g_blk_of (c : @CFGVerifierContract gCtx) : BlkAnnot :=
  {| blk_ctx := gCtx ; blk_contract := c |}.

Definition gRec : @CFGVerifierContract gCtx := g_contract_of g_inv g_post.
Definition gRecBlk : BlkAnnot := g_blk_of gRec.

Definition g_annot_with (blk : BlkAnnot) : list AnnotInstr :=
  [ {| ai_ghost_before := []
     ; ai_instr        := ITYPE (bv.of_Z (-1)) T4 T4 RISCV_ADDI
     ; ai_ghost_after  := []
     ; ai_block        := None
     ; ai_loop         := Some blk |}
  ; AST_AnnotInstr (RTYPE T6 T2 S0 RISCV_SLL)
  ; AST_AnnotInstr (RTYPE T4 T3 S1 RISCV_SRL)
  ; AST_AnnotInstr (RTYPE S1 S0 S0 RISCV_OR)
  ; AST_AnnotInstr (RTYPE T0 S0 S1 RISCV_SUB)
  ; AST_AnnotInstr (RTYPE T0 S0 S0 RISCV_XOR)
  ; AST_AnnotInstr (RTYPE T0 S1 S2 RISCV_XOR)
  ; AST_AnnotInstr (RTYPE S0 S2 S0 RISCV_AND)
  ; AST_AnnotInstr (RTYPE S1 S0 S0 RISCV_XOR)
  ; AST_AnnotInstr (ITYPE (bv.of_Z (-1)) S0 S0 RISCV_XORI)
  ; AST_AnnotInstr (SHIFTIOP (bv.of_Z 31) S0 S0 RISCV_SRLI)
  ; AST_AnnotInstr (RTYPE T4 T2 S2 RISCV_SRL)
  ; AST_AnnotInstr (RTYPE S0 S2 S0 RISCV_OR)
  ; AST_AnnotInstr (RTYPE T6 S1 S1 RISCV_SRL)
  ; AST_AnnotInstr (RTYPE T4 T0 S2 RISCV_SLL)
  ; AST_AnnotInstr (RTYPE S2 T3 S2 RISCV_SUB)
  ; AST_AnnotInstr (RTYPE S0 X0 S3 RISCV_SUB)
  ; AST_AnnotInstr (RTYPE T2 S1 S1 RISCV_XOR)
  ; AST_AnnotInstr (RTYPE S3 S1 S1 RISCV_AND)
  ; AST_AnnotInstr (RTYPE T2 S1 T2 RISCV_XOR)
  ; AST_AnnotInstr (RTYPE T3 S2 S1 RISCV_XOR)
  ; AST_AnnotInstr (RTYPE S3 S1 S1 RISCV_AND)
  ; AST_AnnotInstr (RTYPE T3 S1 T3 RISCV_XOR)
  ; AST_AnnotInstr (RTYPE T4 S0 S0 RISCV_SLL)
  ; AST_AnnotInstr (RTYPE T1 S0 T1 RISCV_OR)
  ; AST_AnnotInstr (ITYPE (bv.of_Z 1) T6 T6 RISCV_ADDI)
  ; AST_AnnotInstr (BTYPE (bv.of_Z (-104)) T4 T5 RISCV_BLTU) ].

Lemma valid_g_rec : cfg_vc gRec (g_annot_with gRecBlk).
Proof. solve_param_vc. Qed.

(* NEGATIVE CONTROLS *)

(* (1) A false post: T5 claimed to be 2 at exit. *)
Goal let c := g_contract_of g_inv (g_post_with (bv.of_N 2)) in
     cfg_vc c (g_annot_with (g_blk_of c)).
Proof. intros c. Fail solve_param_vc. Abort.

(* (2) An invariant the body does not preserve: T6 pinned to 1, but the body
   increments it. *)
Goal let c := g_contract_of (g_inv_with (T6 ↦ᵣ term_val ty_xlenbits (bv.of_N 1))%asn)
                g_post in
     cfg_vc c (g_annot_with (g_blk_of c)).
Proof. intros c. Fail solve_param_vc. Abort.

(* (3) Without the head annotation the executor must unroll a loop with a
   symbolic trip count, and cannot. *)
Goal cfg_vc gRec (list_AST_AnnotInstr g_instrs).
Proof. Fail solve_param_vc. Abort.
