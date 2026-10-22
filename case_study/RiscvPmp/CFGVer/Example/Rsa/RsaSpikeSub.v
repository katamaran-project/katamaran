(* ========================================================================= *)
(* Example/Rsa/RsaSpikeSub.v -- PLAN-rsa.md Phase 1, spike S1a: a FUNCTION   *)
(* CALL as a block.  LIGHT half.                                             *)
(*                                                                           *)
(*   0:  jal ra, br_i31_sub      the harness: call once,                     *)
(*   4:  j   _etext              then leave at the fall-through end (124)    *)
(*   8:  br_i31_sub              BearSSL src/int/i31_sub.c, hardened build   *)
(*       (29 instrs; its word loop at +44..+96 is muladd's loop M)           *)
(*                                                                           *)
(* Three VCs, innermost first:                                               *)
(*  - valid_sub_loop: the word loop, a LOOP VC on the LoopN template.        *)
(*  - valid_sub: br_i31_sub as a CALLEE (gen_callee_contract): from its      *)
(*    entry to whichever `ret` -- its exit is the RETURN ADDRESS r, the      *)
(*    value X1 holds on entry.  The loop is a block inside it.               *)
(*  - valid_s1a: the whole program; the `jal` lands on br_i31_sub's first    *)
(*    instruction, which carries the callee as a block, so the call is ONE   *)
(*    step and the run resumes at the jal's return address.                  *)
(*                                                                           *)
(* Instructions: tools/bearssl/build.sh (hardened i31_sub.o) +               *)
(* tools/bearssl/spike/harness_sub.s, `ld.lld --relax -Ttext=0`,             *)
(* `llvm-objdump -d --no-show-raw-insn`, `asm_to_ast.py --objdump            *)
(* --tables-aliases --name s1a`.  Regenerate, do not edit.                  *)
(* ========================================================================= *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamClose.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamLoopN.

Definition s1a_instrs : list AST :=
  [ RISCV_JAL (bv.of_Z 8) X1   (* jal	L_8	# 0x0: jal 0x8 <br_i31_sub> *)
  ; RISCV_JAL (bv.of_Z 120) X0   (* j	L_7c	# 0x4: j 0x7c <_etext> *)
  ; LOAD (bv.of_Z 0) A0 A3 false WORD   (* lw	a3, 0(a0)	# 0x8: lw a3, 0x0(a0) *)
  ; ITYPE (bv.of_Z 63) A3 A4 RISCV_ADDI   (* addi	a4, a3, 63	# 0xc: addi a4, a3, 0x3f *)
  ; ITYPE (bv.of_Z 64) X0 A3 RISCV_ADDI   (* li	a3, 64	# 0x10: li a3, 0x40 *)
  ; BTYPE (bv.of_Z 96) A3 A4 RISCV_BLTU   (* bltu	a4, a3, L_74	# 0x14: bltu a4, a3, 0x74 <.LBB0_4> *)
  ; ITYPE (bv.of_Z 0) X0 A3 RISCV_ADDI   (* li	a3, 0	# 0x18: li a3, 0x0 *)
  ; SHIFTIOP (bv.of_Z 5) A4 A5 RISCV_SRLI   (* srli	a5, a4, 5	# 0x1c: srli a5, a4, 0x5 *)
  ; RTYPE A2 X0 A2 RISCV_SUB   (* neg	a2, a2	# 0x20: neg a2, a2 *)
  ; ITYPE (bv.of_Z 4) A1 A4 RISCV_ADDI   (* addi	a4, a1, 4	# 0x24: addi a4, a1, 0x4 *)
  ; ITYPE (bv.of_Z 4) A0 A0 RISCV_ADDI   (* addi	a0, a0, 4	# 0x28: addi a0, a0, 0x4 *)
  ; SHIFTIOP (bv.of_Z 2) A5 A5 RISCV_SLLI   (* slli	a5, a5, 2	# 0x2c: slli a5, a5, 0x2 *)
  ; RTYPE A5 A1 A1 RISCV_ADD   (* add	a1, a1, a5	# 0x30: add a1, a1, a5 *)
  ; LOAD (bv.of_Z 0) A0 A6 false WORD   (* lw	a6, 0(a0)	# 0x34: lw a6, 0x0(a0) *)
  ; LOAD (bv.of_Z 0) A4 A5 false WORD   (* lw	a5, 0(a4)	# 0x38: lw a5, 0x0(a4) *)
  ; RTYPE A3 A6 A3 RISCV_ADD   (* add	a3, a6, a3	# 0x3c: add a3, a6, a3 *)
  ; RTYPE A5 A3 A5 RISCV_SUB   (* sub	a5, a3, a5	# 0x40: sub a5, a3, a5 *)
  ; SHIFTIOP (bv.of_Z 31) A5 A3 RISCV_SRAI   (* srai	a3, a5, 31	# 0x44: srai a3, a5, 0x1f *)
  ; SHIFTIOP (bv.of_Z 1) A5 A7 RISCV_SLLI   (* slli	a7, a5, 1	# 0x48: slli a7, a5, 0x1 *)
  ; SHIFTIOP (bv.of_Z 1) A7 A7 RISCV_SRLI   (* srli	a7, a7, 1	# 0x4c: srli a7, a7, 0x1 *)
  ; RTYPE A6 A7 A7 RISCV_XOR   (* xor	a7, a7, a6	# 0x50: xor a7, a7, a6 *)
  ; RTYPE A2 A7 A7 RISCV_AND   (* and	a7, a7, a2	# 0x54: and a7, a7, a2 *)
  ; RTYPE A6 A7 A6 RISCV_XOR   (* xor	a6, a7, a6	# 0x58: xor a6, a7, a6 *)
  ; STORE (bv.of_Z 0) A6 A0 WORD   (* sw	a6, 0(a0)	# 0x5c: sw a6, 0x0(a0) *)
  ; ITYPE (bv.of_Z 4) A4 A4 RISCV_ADDI   (* addi	a4, a4, 4	# 0x60: addi a4, a4, 0x4 *)
  ; ITYPE (bv.of_Z 4) A0 A0 RISCV_ADDI   (* addi	a0, a0, 4	# 0x64: addi a0, a0, 0x4 *)
  ; BTYPE (bv.of_Z (-52)) A1 A4 RISCV_BNE   (* bne	a4, a1, L_34	# 0x68: bne a4, a1, 0x34 <.LBB0_2> *)
  ; SHIFTIOP (bv.of_Z 31) A5 A0 RISCV_SRLI   (* srli	a0, a5, 31	# 0x6c: srli a0, a5, 0x1f *)
  ; RISCV_JALR (bv.of_Z 0) X1 X0   (* ret		# 0x70: ret *)
  ; ITYPE (bv.of_Z 0) X0 A0 RISCV_ADDI   (* li	a0, 0	# 0x74: li a0, 0x0 *)
  ; RISCV_JALR (bv.of_Z 0) X1 X0   (* ret		# 0x78: ret *)
  ].

(* br_i31_sub's own code, from its first instruction (byte offset 8) *)
Definition sub_instrs : list AST := List.skipn 2 s1a_instrs.
(* its word loop: instructions 11..24 of sub_instrs (+44..+96) *)
Definition sub_loop_instrs : list AST := List.firstn 14 (List.skipn 11 sub_instrs).

(* ------------------------------------------------------------------------ *)
(* 1. THE WORD LOOP -- muladd's loop M (MuladdParamLoopM.v), as compiled      *)
(*    here: x pointer A0 (private), m pointer A4 (public), latch A1 = the     *)
(*    end of m, store at index 10, exit +56.                                  *)
(* ------------------------------------------------------------------------ *)

(* what the body uses besides the two arrays and three pointers: the mask
   -ctl (A2), the borrow (A3), temporaries A5 A6 A7 -- all secret *)
Definition sub_scratch {Σ} : Assertion Σ :=
  ( asn.exist "v1" ty_xlenbits (A2 ↦ᵣ term_var "v1")
    ∗ asn.exist "v2" ty_xlenbits (A3 ↦ᵣ term_var "v2")
    ∗ asn.exist "v3" ty_xlenbits (A5 ↦ᵣ term_var "v3")
    ∗ asn.exist "v4" ty_xlenbits (A6 ↦ᵣ term_var "v4")
    ∗ asn.exist "v5" ty_xlenbits (A7 ↦ᵣ term_var "v5") )%asn.

Definition lnSub : LoopN := MkLoopN A0 A4 A1 false sub_loop_instrs 10 56 20.

Lemma valid_sub_loop : cfg_vc_loop (lnRec lnSub (@sub_scratch)) (ln_annot lnSub).
Proof. Time solve_mb_vc. Qed.

(* ------------------------------------------------------------------------ *)
(* 2. br_i31_sub AS A CALLEE                                                *)
(* ------------------------------------------------------------------------ *)

(* q: the function's code base; r: the return address (X1 on entry); xa, xb:
   the two array arguments (A0, A1); h: a[0], the header, public. *)
Definition subCtx : LCtx :=
  ["q"∷ty_xlenbits; "r"∷ty_xlenbits; "xa"∷ty_xlenbits; "xb"∷ty_xlenbits;
   "h"∷ty_xlenbits].

(* the word count the code computes: m = (h + 63) >> 5, so m - 1 limbs.
   `sext h`, not `h`: that is the term `lw` produces (a same-width sign
   extension, the identity, but a different term -- muladd's t_mlen) *)
Definition t_mw {Σ} (h : Term Σ ty_xlenbits) : Term Σ ty_xlenbits :=
  term_binop bop.shiftr
    (term_binop bop.bvadd (term_val ty_xlenbits (bv.of_N 63)) (term_unop uop.sext h))
    (term_val (ty.bvec 5) (bv.of_N 5)).
Definition t_limbs {Σ} (h : Term Σ ty_xlenbits) : Term Σ ty_xlenbits :=
  term_binop bop.bvadd (term_val ty_xlenbits (bv.of_Z (-1))) (t_mw h).
(* p + (m << 2): one past the last limb *)
Definition t_end {Σ} (p h : Term Σ ty_xlenbits) : Term Σ ty_xlenbits :=
  term_binop bop.bvadd p
    (term_binop bop.shiftl (t_mw h) (term_val (ty.bvec 5) (bv.of_N 2))).
Definition t_off4 {Σ} (p : Term Σ ty_xlenbits) : Term Σ ty_xlenbits :=
  term_binop bop.bvadd p (term_val ty_xlenbits (bv.of_N 4)).

(* a's header and limbs (private), b's limbs (public: LoopN fixes m public;
   a secret m is Phase 3), at the arguments' addresses *)
Definition sub_mem {Σ} (xa xb h : Term Σ ty_xlenbits) : Assertion Σ :=
  ( xa ↦ₘ h
    ∗ asn.chunk (chunk_user (arr false 4 4) [t_off4 xa; t_limbs h; t_end xa h])
    ∗ asn.chunk (chunk_user (arr true 4 4) [t_off4 xb; t_limbs h; t_end xb h]) )%asn.

Definition sub_regs : list reg_spec_rel :=
  [ (A2, Secret); (A3, Secret); (A4, Secret); (A5, Secret); (A6, Secret); (A7, Secret) ].

Definition sub_pre : Assertion (subCtx ▻ "a"∷ty_xlenbits) :=
  ( X1 ↦ᵣ term_var "r"
    ∗ A0 ↦ᵣ term_var "xa" ∗ secLeakvar "xa"
    ∗ A1 ↦ᵣ term_var "xb" ∗ secLeakvar "xb"
    ∗ sub_mem (term_var "xa") (term_var "xb") (term_var "h") ∗ secLeakvar "h"
    (* 0 < h < 2^16: at least one limb, and nothing wraps *)
    ∗ asn.formula (formula_relop bop.bvult (term_val ty_xlenbits bv.zero) (term_var "h"))
    ∗ asn.formula (formula_relop bop.bvult (term_var "h") (term_val ty_xlenbits (bv.of_N 65536)))
    ∗ asn.formula (formula_relop bop.le
        (term_binop bop.plus (term_unop uop.unsigned (term_var "xa")) (term_val ty.int 4%Z))
        (term_val ty.int (Z.of_N maxAddr))) )%asn.

(* the same memory back, X1 unchanged; A0 (the borrow) and the scratch are
   handed back with any value *)
Definition sub_post : Assertion (subCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( X1 ↦ᵣ term_var "r"
    ∗ sub_mem (term_var "xa") (term_var "xb") (term_var "h")
    ∗ asn.exist "w0" ty_xlenbits (A0 ↦ᵣ term_var "w0")
    ∗ asn.exist "w1" ty_xlenbits (A1 ↦ᵣ term_var "w1")
    ∗ asn.exist "w2" ty_xlenbits (A2 ↦ᵣ term_var "w2")
    ∗ asn.exist "w3" ty_xlenbits (A3 ↦ᵣ term_var "w3")
    ∗ asn.exist "w4" ty_xlenbits (A4 ↦ᵣ term_var "w4")
    ∗ asn.exist "w5" ty_xlenbits (A5 ↦ᵣ term_var "w5")
    ∗ asn.exist "w6" ty_xlenbits (A6 ↦ᵣ term_var "w6")
    ∗ asn.exist "w7" ty_xlenbits (A7 ↦ᵣ term_var "w7") )%asn.

Definition subRec : @CFGVerifierContract subCtx :=
  gen_callee_contract (term_var "q") (term_var "q") (term_var "r") (term_var "r")
    sub_instrs 30 sub_regs sub_pre sub_post.
Definition subBlk : BlkAnnot := {| blk_ctx := subCtx ; blk_contract := subRec |}.

Definition cl (k : CLem) : Annot := AnnotCLemma k.

(* before the loop: seed its two DONE arrays (empty, address bound by the
   loop's angelic entry); after it: drop the emptied sources and turn the
   done arrays back into forward arrays (muladd's hand_over, without the
   next loop's seeds) *)
Definition sub_seeds : list Annot :=
  [ cl (clem_arr_empty true 4 (-4)); cl (clem_arr_empty false 4 (-4)) ].
Definition sub_hand_back : list Annot :=
  [ cl (clem_arr_drop true 4 4); cl (clem_arr_drop false 4 4)
  ; cl (clem_arr_flip true 4 (-4)); cl (clem_arr_flip false 4 (-4)) ].

(* The seeds go AFTER instruction 10, not before 11: an instruction that
   carries a block runs the block INSTEAD of itself, ghosts included
   (Verifier.v, the `Some b` branch of the step) -- muladd's tail places its
   build_i the same way. *)
Definition sub_annot : list AnnotInstr :=
  List.map (fun '(i, ins) =>
              {| ai_ghost_before := if Nat.eqb i 25 then sub_hand_back else nil
               ; ai_instr := ins
               ; ai_ghost_after := if Nat.eqb i 10 then sub_seeds else nil
               ; ai_block := if Nat.eqb i 11 then Some (lnBlk lnSub (@sub_scratch))
                             else None |})
    (List.combine (List.seq 0 (length sub_instrs)) sub_instrs).

Lemma valid_sub : cfg_vc_loop subRec sub_annot.
Proof. Time solve_mb_vc. Qed.

(* ------------------------------------------------------------------------ *)
(* 3. THE WHOLE PROGRAM: the harness calls br_i31_sub                       *)
(* ------------------------------------------------------------------------ *)

(* q: the program's code base (the harness at +0, br_i31_sub at +8); the
   arguments as for the callee.  X1 is owned with any value: the `jal`
   overwrites it with the return address q + 4. *)
Definition s1aCtx : LCtx :=
  ["q"∷ty_xlenbits; "xa"∷ty_xlenbits; "xb"∷ty_xlenbits; "h"∷ty_xlenbits].

Definition s1a_regs : list reg_spec_rel :=
  [ (X1, Secret); (A2, Secret); (A3, Secret); (A4, Secret); (A5, Secret)
  ; (A6, Secret); (A7, Secret) ].

Definition s1a_pre : Assertion (s1aCtx ▻ "a"∷ty_xlenbits) :=
  ( A0 ↦ᵣ term_var "xa" ∗ secLeakvar "xa"
    ∗ A1 ↦ᵣ term_var "xb" ∗ secLeakvar "xb"
    ∗ sub_mem (term_var "xa") (term_var "xb") (term_var "h") ∗ secLeakvar "h"
    ∗ asn.formula (formula_relop bop.bvult (term_val ty_xlenbits bv.zero) (term_var "h"))
    ∗ asn.formula (formula_relop bop.bvult (term_var "h") (term_val ty_xlenbits (bv.of_N 65536)))
    ∗ asn.formula (formula_relop bop.le
        (term_binop bop.plus (term_unop uop.unsigned (term_var "xa")) (term_val ty.int 4%Z))
        (term_val ty.int (Z.of_N maxAddr))) )%asn.

(* the memory back, every register with any value *)
Definition s1a_post : Assertion (s1aCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( sub_mem (term_var "xa") (term_var "xb") (term_var "h")
    ∗ asn.exist "w1" ty_xlenbits (X1 ↦ᵣ term_var "w1")
    ∗ asn.exist "w0" ty_xlenbits (A0 ↦ᵣ term_var "w0")
    ∗ asn.exist "w8" ty_xlenbits (A1 ↦ᵣ term_var "w8")
    ∗ asn.exist "w2" ty_xlenbits (A2 ↦ᵣ term_var "w2")
    ∗ asn.exist "w3" ty_xlenbits (A3 ↦ᵣ term_var "w3")
    ∗ asn.exist "w4" ty_xlenbits (A4 ↦ᵣ term_var "w4")
    ∗ asn.exist "w5" ty_xlenbits (A5 ↦ᵣ term_var "w5")
    ∗ asn.exist "w6" ty_xlenbits (A6 ↦ᵣ term_var "w6")
    ∗ asn.exist "w7" ty_xlenbits (A7 ↦ᵣ term_var "w7") )%asn.

(* exit: the fall-through end, +124 = 4 * 31 *)
Definition s1aRec : @CFGVerifierContract s1aCtx :=
  gen_seg_contract (term_var "q") (term_var "q") s1a_instrs 124 10 s1a_regs
    s1a_pre s1a_post.

(* the callee is a block on ITS first instruction, index 2; the rest is code *)
Definition s1a_annot : list AnnotInstr :=
  List.map (fun '(i, ins) =>
              {| ai_ghost_before := nil ; ai_instr := ins ; ai_ghost_after := nil
               ; ai_block := if Nat.eqb i 2 then Some subBlk else None |})
    (List.combine (List.seq 0 (length s1a_instrs)) s1a_instrs).

Lemma valid_s1a : cfg_vc s1aRec s1a_annot.
Proof. Time solve_mb_vc. Qed.

(* NEGATIVE CONTROLS: valid_s1a is not vacuous (it closes in ~0.2 s). *)

(* Without the block the callee's body runs inline, and its word loop has a
   symbolic trip count the executor cannot unroll. *)
Goal cfg_vc s1aRec (list_AST_AnnotInstr s1a_instrs).
Proof. Fail solve_mb_vc. Abort.

(* A post claiming a's SECRET limbs public is rejected -- so the precondition
   is not inconsistent. *)
Goal cfg_vc (gen_seg_contract (term_var "q") (term_var "q") s1a_instrs 124 10 s1a_regs s1a_pre
   (( term_var "xa" ↦ₘ term_var "h"
      ∗ asn.chunk (chunk_user (arr true 4 4)
          [t_off4 (term_var "xa"); t_limbs (term_var "h"); t_end (term_var "xa") (term_var "h")])
      ∗ asn.chunk (chunk_user (arr true 4 4)
          [t_off4 (term_var "xb"); t_limbs (term_var "h"); t_end (term_var "xb") (term_var "h")]) )%asn))
  s1a_annot.
Proof. Fail solve_mb_vc. Abort.
