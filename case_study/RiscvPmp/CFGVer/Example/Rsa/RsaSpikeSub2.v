(* ========================================================================= *)
(* Example/Rsa/RsaSpikeSub2.v -- PLAN-rsa.md Phase 1, spike S1b: a CALLER    *)
(* that is itself a function, calling br_i31_sub twice.  LIGHT half.         *)
(*                                                                           *)
(*   0:  jal ra, rsa_spike_sub2   the harness: call once,                    *)
(*   4:  j   _etext               then leave at the fall-through end (204)   *)
(*   8:  rsa_spike_sub2           tools/bearssl/spike/sub2.c, hardened build:*)
(*       br_i31_montymul's last line, br_i31_sub(d, m, NEQ(dh, 0) |          *)
(*       NOT(br_i31_sub(d, m, 0))) -- a 16-byte frame (ra, s0, s1, s2), one *)
(*       `jal` to br_i31_sub, then a TAIL `j br_i31_sub` after restoring ra  *)
(*  88:  br_i31_sub               the same 29 instructions as in S1a         *)
(*                                                                           *)
(* Two function contracts, one generator (gen_seg_contract_at, exit r):      *)
(*  - br_i31_sub: RsaSpikeSub.subBlk, reused unchanged -- a block valid      *)
(*    anywhere, so wherever this link puts it;                               *)
(*  - rsa_spike_sub2 (valid_sub2): its code is ITSELF AND ITS CALLEE as       *)
(*    linked (a function's table must hold every pc it reaches), br_i31_sub  *)
(*    a block on its first instruction, entered twice: from the `jal` (exit  *)
(*    the call site + 4) and from the tail `j` (exit the CALLER's r, so the  *)
(*    block's exit is the caller's own exit).  s0-s2 and sp are pinned --    *)
(*    the same logic variable in pre and post -- and the frame is owned.    *)
(*  - the whole program (valid_s1b), rsa_spike_sub2 a block on index 2.      *)
(*                                                                           *)
(* Instructions: tools/bearssl/build.sh (hardened i31_sub.o), sub2.c with    *)
(* the same flags against the hardened tree, tools/bearssl/spike/          *)
(* harness_sub2.s, `ld.lld --relax -Ttext=0 harness sub2                   *)
(* i31_sub`, `llvm-objdump-18 -d --no-show-raw-insn`, `asm_to_ast.py         *)
(* --objdump --tables-aliases --name s1b`.  Regenerate, do not edit.        *)
(* ========================================================================= *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamClose.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Rsa.RsaSpikeSub.

Definition s1b_instrs : list AST :=
  [ RISCV_JAL (bv.of_Z 8) X1   (* jal	L_8	# 0x0: jal 0x8 <rsa_spike_sub2> *)
  ; RISCV_JAL (bv.of_Z 200) X0   (* j	L_cc	# 0x4: j 0xcc <_etext> *)
  ; ITYPE (bv.of_Z (-16)) X2 X2 RISCV_ADDI   (* addi	sp, sp, -16	# 0x8: addi sp, sp, -0x10 *)
  ; STORE (bv.of_Z 12) X1 X2 WORD   (* sw	ra, 12(sp)	# 0xc: sw ra, 0xc(sp) *)
  ; STORE (bv.of_Z 8) S0 X2 WORD   (* sw	s0, 8(sp)	# 0x10: sw s0, 0x8(sp) *)
  ; STORE (bv.of_Z 4) S1 X2 WORD   (* sw	s1, 4(sp)	# 0x14: sw s1, 0x4(sp) *)
  ; STORE (bv.of_Z 0) S2 X2 WORD   (* sw	s2, 0(sp)	# 0x18: sw s2, 0x0(sp) *)
  ; ITYPE (bv.of_Z 0) A1 S0 RISCV_ADDI   (* mv	s0, a1	# 0x1c: mv s0, a1 *)
  ; ITYPE (bv.of_Z 0) A0 S1 RISCV_ADDI   (* mv	s1, a0	# 0x20: mv s1, a0 *)
  ; RTYPE A2 X0 S2 RISCV_SLTU   (* snez	s2, a2	# 0x24: snez s2, a2 *)
  ; ITYPE (bv.of_Z 0) X0 A2 RISCV_ADDI   (* li	a2, 0	# 0x28: li a2, 0x0 *)
  ; RISCV_JAL (bv.of_Z 44) X1   (* jal	L_58	# 0x2c: jal 0x58 <br_i31_sub> *)
  ; ITYPE (bv.of_Z 1) A0 A0 RISCV_XORI   (* xori	a0, a0, 1	# 0x30: xori a0, a0, 0x1 *)
  ; RTYPE S2 A0 A2 RISCV_OR   (* or	a2, a0, s2	# 0x34: or a2, a0, s2 *)
  ; ITYPE (bv.of_Z 0) S1 A0 RISCV_ADDI   (* mv	a0, s1	# 0x38: mv a0, s1 *)
  ; ITYPE (bv.of_Z 0) S0 A1 RISCV_ADDI   (* mv	a1, s0	# 0x3c: mv a1, s0 *)
  ; LOAD (bv.of_Z 12) X2 X1 false WORD   (* lw	ra, 12(sp)	# 0x40: lw ra, 0xc(sp) *)
  ; LOAD (bv.of_Z 8) X2 S0 false WORD   (* lw	s0, 8(sp)	# 0x44: lw s0, 0x8(sp) *)
  ; LOAD (bv.of_Z 4) X2 S1 false WORD   (* lw	s1, 4(sp)	# 0x48: lw s1, 0x4(sp) *)
  ; LOAD (bv.of_Z 0) X2 S2 false WORD   (* lw	s2, 0(sp)	# 0x4c: lw s2, 0x0(sp) *)
  ; ITYPE (bv.of_Z 16) X2 X2 RISCV_ADDI   (* addi	sp, sp, 16	# 0x50: addi sp, sp, 0x10 *)
  ; RISCV_JAL (bv.of_Z 4) X0   (* j	L_58	# 0x54: j 0x58 <br_i31_sub> *)
  ; LOAD (bv.of_Z 0) A0 A3 false WORD   (* lw	a3, 0(a0)	# 0x58: lw a3, 0x0(a0) *)
  ; ITYPE (bv.of_Z 63) A3 A4 RISCV_ADDI   (* addi	a4, a3, 63	# 0x5c: addi a4, a3, 0x3f *)
  ; ITYPE (bv.of_Z 64) X0 A3 RISCV_ADDI   (* li	a3, 64	# 0x60: li a3, 0x40 *)
  ; BTYPE (bv.of_Z 96) A3 A4 RISCV_BLTU   (* bltu	a4, a3, L_c4	# 0x64: bltu a4, a3, 0xc4 <.LBB0_4> *)
  ; ITYPE (bv.of_Z 0) X0 A3 RISCV_ADDI   (* li	a3, 0	# 0x68: li a3, 0x0 *)
  ; SHIFTIOP (bv.of_Z 5) A4 A5 RISCV_SRLI   (* srli	a5, a4, 5	# 0x6c: srli a5, a4, 0x5 *)
  ; RTYPE A2 X0 A2 RISCV_SUB   (* neg	a2, a2	# 0x70: neg a2, a2 *)
  ; ITYPE (bv.of_Z 4) A1 A4 RISCV_ADDI   (* addi	a4, a1, 4	# 0x74: addi a4, a1, 0x4 *)
  ; ITYPE (bv.of_Z 4) A0 A0 RISCV_ADDI   (* addi	a0, a0, 4	# 0x78: addi a0, a0, 0x4 *)
  ; SHIFTIOP (bv.of_Z 2) A5 A5 RISCV_SLLI   (* slli	a5, a5, 2	# 0x7c: slli a5, a5, 0x2 *)
  ; RTYPE A5 A1 A1 RISCV_ADD   (* add	a1, a1, a5	# 0x80: add a1, a1, a5 *)
  ; LOAD (bv.of_Z 0) A0 A6 false WORD   (* lw	a6, 0(a0)	# 0x84: lw a6, 0x0(a0) *)
  ; LOAD (bv.of_Z 0) A4 A5 false WORD   (* lw	a5, 0(a4)	# 0x88: lw a5, 0x0(a4) *)
  ; RTYPE A3 A6 A3 RISCV_ADD   (* add	a3, a6, a3	# 0x8c: add a3, a6, a3 *)
  ; RTYPE A5 A3 A5 RISCV_SUB   (* sub	a5, a3, a5	# 0x90: sub a5, a3, a5 *)
  ; SHIFTIOP (bv.of_Z 31) A5 A3 RISCV_SRAI   (* srai	a3, a5, 31	# 0x94: srai a3, a5, 0x1f *)
  ; SHIFTIOP (bv.of_Z 1) A5 A7 RISCV_SLLI   (* slli	a7, a5, 1	# 0x98: slli a7, a5, 0x1 *)
  ; SHIFTIOP (bv.of_Z 1) A7 A7 RISCV_SRLI   (* srli	a7, a7, 1	# 0x9c: srli a7, a7, 0x1 *)
  ; RTYPE A6 A7 A7 RISCV_XOR   (* xor	a7, a7, a6	# 0xa0: xor a7, a7, a6 *)
  ; RTYPE A2 A7 A7 RISCV_AND   (* and	a7, a7, a2	# 0xa4: and a7, a7, a2 *)
  ; RTYPE A6 A7 A6 RISCV_XOR   (* xor	a6, a7, a6	# 0xa8: xor a6, a7, a6 *)
  ; STORE (bv.of_Z 0) A6 A0 WORD   (* sw	a6, 0(a0)	# 0xac: sw a6, 0x0(a0) *)
  ; ITYPE (bv.of_Z 4) A4 A4 RISCV_ADDI   (* addi	a4, a4, 4	# 0xb0: addi a4, a4, 0x4 *)
  ; ITYPE (bv.of_Z 4) A0 A0 RISCV_ADDI   (* addi	a0, a0, 4	# 0xb4: addi a0, a0, 0x4 *)
  ; BTYPE (bv.of_Z (-52)) A1 A4 RISCV_BNE   (* bne	a4, a1, L_84	# 0xb8: bne a4, a1, 0x84 <.LBB0_2> *)
  ; SHIFTIOP (bv.of_Z 31) A5 A0 RISCV_SRLI   (* srli	a0, a5, 31	# 0xbc: srli a0, a5, 0x1f *)
  ; RISCV_JALR (bv.of_Z 0) X1 X0   (* ret		# 0xc0: ret *)
  ; ITYPE (bv.of_Z 0) X0 A0 RISCV_ADDI   (* li	a0, 0	# 0xc4: li a0, 0x0 *)
  ; RISCV_JALR (bv.of_Z 0) X1 X0   (* ret		# 0xc8: ret *)
  ].

(* rsa_spike_sub2 and its callee, as linked (byte offset 8 on) *)
Definition sub2_instrs : list AST := List.skipn 2 s1b_instrs.

(* ------------------------------------------------------------------------ *)
(* 1. rsa_spike_sub2, ITS EXIT THE RETURN ADDRESS                          *)
(* ------------------------------------------------------------------------ *)

(* q: its code base; r: the return address; sp: the stack pointer on entry;
   v0-v2: s0-s2 on entry (any value, secret or not); xa, xb, h: the
   arguments as for br_i31_sub.  dh (A2) is secret, unnamed. *)
Definition sub2Ctx : LCtx :=
  ["q"∷ty_xlenbits; "r"∷ty_xlenbits; "sp"∷ty_xlenbits;
   "v0"∷ty_xlenbits; "v1"∷ty_xlenbits; "v2"∷ty_xlenbits;
   "xa"∷ty_xlenbits; "xb"∷ty_xlenbits; "h"∷ty_xlenbits;
   "va"∷clemv_ty 4; "vb"∷clemv_ty 4].

(* the frame: the four words below sp, any value -- the generator's cell
   form, so a caller that states them with gen_data_at hands them over as is *)
Definition sub2_frame {Σ} (sp : Term Σ ty_xlenbits) : Assertion Σ :=
  gen_data_at (sub_id Σ) (t_add sp (-16)) [DCell Secret; DCell Secret; DCell Secret; DCell Secret] [env].

(* the callee-saved registers and sp, at the same logic variables in pre and
   post: what lets a caller keep its own pointers across the call *)
Definition sub2_saved {Σ} (sp v0 v1 v2 : Term Σ ty_xlenbits) : Assertion Σ :=
  ( X2 ↦ᵣ sp ∗ S0 ↦ᵣ v0 ∗ S1 ↦ᵣ v1 ∗ S2 ↦ᵣ v2 )%asn.

(* dh and the callee's scratch *)
Definition sub2_regs : list reg_spec_rel :=
  [ (A2, Secret); (A3, Secret); (A4, Secret); (A5, Secret); (A6, Secret); (A7, Secret) ].

Definition sub2_pre : Assertion (sub2Ctx ▻ "a"∷ty_xlenbits) :=
  ( X1 ↦ᵣ term_var "r"
    ∗ sub2_saved (term_var "sp") (term_var "v0") (term_var "v1") (term_var "v2")
    ∗ secLeakvar "sp" ∗ sub2_frame (term_var "sp")
    ∗ A0 ↦ᵣ term_var "xa" ∗ secLeakvar "xa"
    ∗ A1 ↦ᵣ term_var "xb" ∗ secLeakvar "xb"
    ∗ sub_mem "va" "vb" (term_var "xa") (term_var "xb") (term_var "h") (term_var "va") (term_var "vb")
    ∗ secLeakvar "h"
    ∗ asn.formula (formula_relop bop.bvult (term_val ty_xlenbits bv.zero) (term_var "h"))
    ∗ asn.formula (formula_relop bop.bvult (term_var "h") (term_val ty_xlenbits (bv.of_N 65536)))
    ∗ asn.formula (formula_relop bop.le
        (term_binop bop.plus (term_unop uop.unsigned (term_var "xa")) (term_val ty.int 4%Z))
        (term_val ty.int (Z.of_N maxAddr))) )%asn.

Definition sub2_post : Assertion (sub2Ctx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( X1 ↦ᵣ term_var "r"
    ∗ sub2_saved (term_var "sp") (term_var "v0") (term_var "v1") (term_var "v2")
    ∗ sub2_frame (term_var "sp")
    ∗ sub_mem_out "va" "vb" (term_var "xa") (term_var "xb") (term_var "h") (term_var "vb")
    ∗ asn.exist "w0" ty_xlenbits (A0 ↦ᵣ term_var "w0")
    ∗ asn.exist "w1" ty_xlenbits (A1 ↦ᵣ term_var "w1")
    ∗ asn.exist "w2" ty_xlenbits (A2 ↦ᵣ term_var "w2")
    ∗ asn.exist "w3" ty_xlenbits (A3 ↦ᵣ term_var "w3")
    ∗ asn.exist "w4" ty_xlenbits (A4 ↦ᵣ term_var "w4")
    ∗ asn.exist "w5" ty_xlenbits (A5 ↦ᵣ term_var "w5")
    ∗ asn.exist "w6" ty_xlenbits (A6 ↦ᵣ term_var "w6")
    ∗ asn.exist "w7" ty_xlenbits (A7 ↦ᵣ term_var "w7") )%asn.

Definition sub2Rec : @CFGVerifierContract sub2Ctx :=
  gen_seg_contract_at (term_var "q") (term_var "q") (term_var "r")
    sub2_instrs 40 sub2_regs (secLeakvar "r" ∗ sub2_pre)%asn sub2_post.
Definition sub2Blk : BlkAnnot := {| blk_ctx := sub2Ctx ; blk_contract := sub2Rec |}.

(* br_i31_sub is a block on ITS first instruction, index 20 *)
Definition sub2_annot : list AnnotInstr :=
  List.map (fun '(i, ins) =>
              {| ai_ghost_before := nil ; ai_instr := ins ; ai_ghost_after := nil
               ; ai_block := if Nat.eqb i 20 then Some subBlk else None |})
    (List.combine (List.seq 0 (length sub2_instrs)) sub2_instrs).

Lemma valid_sub2 : cfg_vc_loop sub2Rec sub2_annot.
Proof. Time solve_mb_vc. Qed.

(* ------------------------------------------------------------------------ *)
(* 2. THE WHOLE PROGRAM: the harness calls rsa_spike_sub2                   *)
(* ------------------------------------------------------------------------ *)

(* q: the program's code base; sp: the stack pointer; the rest as above *)
Definition s1bCtx : LCtx :=
  ["q"∷ty_xlenbits; "sp"∷ty_xlenbits; "xa"∷ty_xlenbits; "xb"∷ty_xlenbits; "h"∷ty_xlenbits].

(* the two array pointers and sp public; X1 (overwritten by the jal), dh,
   the scratch and the callee-saved registers secret *)
Definition s1b_regs : list (reg_spec_q s1bCtx) :=
  [ (A0, Known (PVVar "xa")); (A1, Known (PVVar "xb")); (X2, Known (PVVar "sp")); (X1, Secret)
  ; (A2, Secret); (A3, Secret); (A4, Secret); (A5, Secret); (A6, Secret); (A7, Secret)
  ; (S0, Secret); (S1, Secret); (S2, Secret) ].

Definition s1b_facts : Assertion (s1bCtx ▻ "a"∷ty_xlenbits) :=
  ( asn.formula (formula_relop bop.bvult (term_val ty_xlenbits bv.zero) (term_var "h"))
    ∗ asn.formula (formula_relop bop.bvult (term_var "h") (term_val ty_xlenbits (bv.of_N 65536))) )%asn.

(* S1a's two arrays, then the callee's frame: four words below sp *)
Definition s1b_data : list (data_spec s1bCtx) :=
  [ DPtr (term_var "xa"); DCell (Known (term_var "h")); DArr false ArrUp (t_limbs (term_var "h")) "va"
  ; DPtr (t_off4 (term_var "xb")); DArr true ArrUp (t_limbs (term_var "h")) "vb"
  ; DPtr (t_add (term_var "sp") (-16)); DCell Secret; DCell Secret; DCell Secret; DCell Secret ]%list.

(* the contract's context: s1bCtx and the arrays' values *)
Definition s1bCtxV : LCtx := s1bCtx ▻▻ data_vctx s1b_data.

(* the memory back (b with its own value, PLAN-arrv D13), every register
   with any value *)
Definition s1b_post : Assertion (s1bCtxV ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( sub_mem_out "va" "vb" (term_var "xa") (term_var "xb") (term_var "h") (term_var "vb")
    ∗ sub2_frame (term_var "sp")
    ∗ asn.exist "w1" ty_xlenbits (X1 ↦ᵣ term_var "w1")
    ∗ asn.exist "w9" ty_xlenbits (X2 ↦ᵣ term_var "w9")
    ∗ asn.exist "w0" ty_xlenbits (A0 ↦ᵣ term_var "w0")
    ∗ asn.exist "w8" ty_xlenbits (A1 ↦ᵣ term_var "w8")
    ∗ asn.exist "w2" ty_xlenbits (A2 ↦ᵣ term_var "w2")
    ∗ asn.exist "w3" ty_xlenbits (A3 ↦ᵣ term_var "w3")
    ∗ asn.exist "w4" ty_xlenbits (A4 ↦ᵣ term_var "w4")
    ∗ asn.exist "w5" ty_xlenbits (A5 ↦ᵣ term_var "w5")
    ∗ asn.exist "w6" ty_xlenbits (A6 ↦ᵣ term_var "w6")
    ∗ asn.exist "w7" ty_xlenbits (A7 ↦ᵣ term_var "w7")
    ∗ asn.exist "s0" ty_xlenbits (S0 ↦ᵣ term_var "s0")
    ∗ asn.exist "s1" ty_xlenbits (S1 ↦ᵣ term_var "s1")
    ∗ asn.exist "s2" ty_xlenbits (S2 ↦ᵣ term_var "s2") )%asn.

(* exit: the fall-through end, +204 = 4 * 51 *)
Definition s1bRec : @CFGVerifierContract s1bCtxV :=
  gen_prog_contract "q" _ s1b_regs s1b_facts 204 s1b_data s1b_instrs 10 s1b_post.

(* the caller is a block on ITS first instruction, index 2 *)
Definition s1b_annot : list AnnotInstr :=
  List.map (fun '(i, ins) =>
              {| ai_ghost_before := nil ; ai_instr := ins ; ai_ghost_after := nil
               ; ai_block := if Nat.eqb i 2 then Some sub2Blk else None |})
    (List.combine (List.seq 0 (length s1b_instrs)) s1b_instrs).

Lemma valid_s1b : cfg_vc s1bRec s1b_annot.
Proof. Time solve_mb_vc. Qed.

(* NEGATIVE CONTROLS: valid_sub2 is not vacuous. *)

(* s0 handed back as v1, not v0: rejected -- the pinning is checked. *)
Goal cfg_vc_loop (gen_seg_contract_at (term_var "q") (term_var "q") (term_var "r")
    sub2_instrs 40 sub2_regs (secLeakvar "r" ∗ sub2_pre)%asn
    ( X1 ↦ᵣ term_var "r"
      ∗ sub2_saved (term_var "sp") (term_var "v1") (term_var "v1") (term_var "v2")
      ∗ sub2_frame (term_var "sp")
      ∗ sub_mem_out "va" "vb" (term_var "xa") (term_var "xb") (term_var "h") (term_var "vb")
      ∗ asn.exist "w0" ty_xlenbits (A0 ↦ᵣ term_var "w0")
      ∗ asn.exist "w1" ty_xlenbits (A1 ↦ᵣ term_var "w1")
      ∗ asn.exist "w2" ty_xlenbits (A2 ↦ᵣ term_var "w2")
      ∗ asn.exist "w3" ty_xlenbits (A3 ↦ᵣ term_var "w3")
      ∗ asn.exist "w4" ty_xlenbits (A4 ↦ᵣ term_var "w4")
      ∗ asn.exist "w5" ty_xlenbits (A5 ↦ᵣ term_var "w5")
      ∗ asn.exist "w6" ty_xlenbits (A6 ↦ᵣ term_var "w6")
      ∗ asn.exist "w7" ty_xlenbits (A7 ↦ᵣ term_var "w7") )%asn)
  sub2_annot.
Proof. Fail solve_mb_vc. Abort.

(* a's SECRET limbs claimed public: rejected. *)
Goal cfg_vc_loop (gen_seg_contract_at (term_var "q") (term_var "q") (term_var "r")
    sub2_instrs 40 sub2_regs (secLeakvar "r" ∗ sub2_pre)%asn
    ( X1 ↦ᵣ term_var "r"
      ∗ sub2_saved (term_var "sp") (term_var "v0") (term_var "v1") (term_var "v2")
      ∗ sub2_frame (term_var "sp")
      ∗ term_var "xa" ↦ₘ term_var "h"
      ∗ asn.exist "va'" (clemv_ty 4)
          (clem_arrv 4 4 "va" (t_off4 (term_var "xa")) (t_limbs (term_var "h"))
             (t_end (term_var "xa") (term_var "h")) (term_var "va'") ∗ secLeakvar "va'")
      ∗ clem_arrv 4 4 "vb" (t_off4 (term_var "xb")) (t_limbs (term_var "h"))
          (t_end (term_var "xb") (term_var "h")) (term_var "vb")
      ∗ asn.exist "w0" ty_xlenbits (A0 ↦ᵣ term_var "w0")
      ∗ asn.exist "w1" ty_xlenbits (A1 ↦ᵣ term_var "w1")
      ∗ asn.exist "w2" ty_xlenbits (A2 ↦ᵣ term_var "w2")
      ∗ asn.exist "w3" ty_xlenbits (A3 ↦ᵣ term_var "w3")
      ∗ asn.exist "w4" ty_xlenbits (A4 ↦ᵣ term_var "w4")
      ∗ asn.exist "w5" ty_xlenbits (A5 ↦ᵣ term_var "w5")
      ∗ asn.exist "w6" ty_xlenbits (A6 ↦ᵣ term_var "w6")
      ∗ asn.exist "w7" ty_xlenbits (A7 ↦ᵣ term_var "w7") )%asn)
  sub2_annot.
Proof. Fail solve_mb_vc. Abort.
