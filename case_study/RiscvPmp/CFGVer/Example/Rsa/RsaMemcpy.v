(* ========================================================================= *)
(* Example/Rsa/RsaMemcpy.v -- PLAN-rsa.md Phase 2 (D5): picolibc 1.8.12's   *)
(* size-optimised memcpy as a FUNCTION contract.  LIGHT, VCs only.           *)
(*                                                                           *)
(*   0:  jal ra, memcpy          the harness: call once,                     *)
(*   4:  j   _etext              then leave at the fall-through end (44)     *)
(*   8:  memcpy                  mv a3,a0; beqz a2,ret; then the byte loop   *)
(*                               (RsaSpikeArrv's mc loop) at +16..+36; ret   *)
(*                                                                           *)
(* The post names the copied value: the destination holds EXACTLY the       *)
(* source's value vs, so a caller's facts about vs (publicness) carry over   *)
(* to the destination by framing (memory feedback-framing-keeps-info).       *)
(*                                                                           *)
(* Tags (PLAN-arrv D14-D17): the contracts take the caller's two tags ts,   *)
(* td as Coq parameters.  The destination's DONE array carries td too (a     *)
(* join cannot rename a tag without also appending the emptied remainder's  *)
(* unknown value), so two td arrays are live in the loop; the executor's    *)
(* angelic match tells them apart by address and count.                     *)
(*                                                                           *)
(* Instructions: tools/bearssl/picolibc.sh (memcpy-asm.o) +                 *)
(* tools/bearssl/spike/harness_memcpy.s, `ld.lld --relax -Ttext=0`,         *)
(* `llvm-objdump -d --no-show-raw-insn`, `asm_to_ast.py --objdump           *)
(* --tables-aliases --name mcf`.  Regenerate, do not edit.                  *)
(* ========================================================================= *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamClose.

Definition mcf_instrs : list AST :=
  [ RISCV_JAL (bv.of_Z 8) X1   (* jal	L_8	# 0x0: jal 0x8 <memcpy> *)
  ; RISCV_JAL (bv.of_Z 40) X0   (* j	L_2c	# 0x4: j 0x2c <_etext> *)
  ; ITYPE (bv.of_Z 0) A0 A3 RISCV_ADDI   (* mv	a3, a0	# 0x8: mv a3, a0 *)
  ; BTYPE (bv.of_Z 28) X0 A2 RISCV_BEQ   (* beqz	a2, L_28	# 0xc: beqz a2, 0x28 <.Ltmp0> *)
  ; LOAD (bv.of_Z 0) A1 A4 true BYTE   (* lbu	a4, 0(a1)	# 0x10: lbu a4, 0x0(a1) *)
  ; STORE (bv.of_Z 0) A4 A3 BYTE   (* sb	a4, 0(a3)	# 0x14: sb a4, 0x0(a3) *)
  ; ITYPE (bv.of_Z (-1)) A2 A2 RISCV_ADDI   (* addi	a2, a2, -1	# 0x18: addi a2, a2, -0x1 *)
  ; ITYPE (bv.of_Z 1) A3 A3 RISCV_ADDI   (* addi	a3, a3, 1	# 0x1c: addi a3, a3, 0x1 *)
  ; ITYPE (bv.of_Z 1) A1 A1 RISCV_ADDI   (* addi	a1, a1, 1	# 0x20: addi a1, a1, 0x1 *)
  ; BTYPE (bv.of_Z (-20)) X0 A2 RISCV_BNE   (* bnez	a2, L_10	# 0x24: bnez a2, 0x10 <.Ltmp1> *)
  ; RISCV_JALR (bv.of_Z 0) X1 X0   (* ret		# 0x28: ret *)
  ].

(* memcpy's own code, from its first instruction (byte offset 8) *)
Definition memcpy_instrs : list AST := List.skipn 2 mcf_instrs.
(* its byte loop: instructions 2..7 of memcpy_instrs (+8..+28) *)
Definition mcl_instrs : list AST := List.firstn 6 (List.skipn 2 memcpy_instrs).

Definition t_end {Σ} (a n : Term Σ ty_xlenbits) : Term Σ ty_xlenbits :=
  term_binop bop.bvadd a n.

(* the source's DONE array: a tag of memcpy's own, no caller array has it *)
Definition mc_sd : string := "memcpy.sd".

(* ------------------------------------------------------------------------ *)
(* 1. THE BYTE LOOP                                                         *)
(* ------------------------------------------------------------------------ *)
(* Invariant: the source is DONE ++ REST, the destination DONE ++ (old), vs = *)
(* done ++ rest, and k + c = n (so the caller's count comes back).  One     *)
(* step: take rest's first cell, load it, add it to the source's done; take *)
(* the destination's next cell, store, add it to the destination's done.    *)
Definition mlCtx : LCtx :=
  ["q"∷ty_xlenbits; "s"∷ty_xlenbits; "d"∷ty_xlenbits; "e"∷ty_xlenbits;
   "f"∷ty_xlenbits; "n"∷ty_xlenbits; "vs"∷clemv_ty 1].

Definition ml_annot (ts td : string) : list AnnotInstr :=
  [ {| ai_ghost_before := [ AnnotCLemma (clem_arrv_take_first 1 1 ts) ]
     ; ai_instr := LOAD (bv.of_Z 0) A1 A4 true BYTE
     ; ai_ghost_after := [ AnnotCLemma (clem_arrv_add_last 1 1 mc_sd) ]; ai_block := None |}
  ; {| ai_ghost_before := [ AnnotCLemma (clem_arrv_take_first 1 1 td) ]
     ; ai_instr := STORE (bv.of_Z 0) A4 A3 BYTE
     ; ai_ghost_after := [ AnnotCLemma (clem_arrv_add_last 1 1 td) ]; ai_block := None |}
  ; AST_AnnotInstr (ITYPE (bv.of_Z (-1)) A2 A2 RISCV_ADDI)
  ; AST_AnnotInstr (ITYPE (bv.of_Z 1) A3 A3 RISCV_ADDI)
  ; AST_AnnotInstr (ITYPE (bv.of_Z 1) A1 A1 RISCV_ADDI)
  ; AST_AnnotInstr (BTYPE (bv.of_Z (-20)) X0 A2 RISCV_BNE) ].

(* the loop state with c bytes to go, k done, cursors p (source) r (dest) *)
Definition ml_state {Σ} (ts td : string) (s d e f n c k p r : Term Σ ty_xlenbits)
    (done rest drest : Term Σ (clemv_ty 1)) : Assertion Σ :=
  ( clem_arrv_angelic 1 1 mc_sd s k p done ∗ clem_arrv_angelic 1 1 ts p c e rest
    ∗ clem_arrv_angelic 1 1 td d k r done ∗ clem_arrv_angelic 1 1 td r c f drest
    ∗ A1 ↦ᵣ p ∗ A3 ↦ᵣ r ∗ A2 ↦ᵣ c
    ∗ asn.formula (formula_relop bop.eq (term_binop bop.bvadd k c) n) )%asn.

Definition ml_inv (ts td : string) : Assertion (mlCtx ▻ "a"∷ty_xlenbits) :=
  ( asn.exist "c" ty_xlenbits (asn.exist "k" ty_xlenbits
    (asn.exist "p" ty_xlenbits (asn.exist "r" ty_xlenbits
    (asn.exist "done" (clemv_ty 1) (asn.exist "rest" (clemv_ty 1)
    (asn.exist "drest" (clemv_ty 1)
      ( ml_state ts td (term_var "s") (term_var "d") (term_var "e") (term_var "f")
          (term_var "n") (term_var "c") (term_var "k") (term_var "p") (term_var "r")
          (term_var "done") (term_var "rest") (term_var "drest")
        ∗ secLeakvar "c" ∗ secLeakvar "p" ∗ secLeakvar "r"
        ∗ clem_nonzero (term_var "c")
        ∗ asn.formula (formula_propeq (term_var "vs")
            (term_binop bop.append (term_var "done") (term_var "rest"))))))))))
    ∗ asn.exist "v4" ty_xlenbits (A4 ↦ᵣ term_var "v4") )%asn.

Definition ml_post (ts td : string) : Assertion (mlCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( asn.exist "k" ty_xlenbits
    (asn.exist "p" ty_xlenbits (asn.exist "r" ty_xlenbits
    (asn.exist "done" (clemv_ty 1) (asn.exist "rest" (clemv_ty 1)
    (asn.exist "drest" (clemv_ty 1)
      ( ml_state ts td (term_var "s") (term_var "d") (term_var "e") (term_var "f")
          (term_var "n") (term_val ty_xlenbits bv.zero) (term_var "k") (term_var "p")
          (term_var "r") (term_var "done") (term_var "rest") (term_var "drest")
        ∗ asn.formula (formula_propeq (term_var "vs")
            (term_binop bop.append (term_var "done") (term_var "rest")))))))))
    ∗ asn.exist "v4" ty_xlenbits (A4 ↦ᵣ term_var "v4") )%asn.

Definition mlRec (ts td : string) : @CFGVerifierContract mlCtx :=
  gen_seg_contract (term_var "q") (term_var "q") mcl_instrs 24 16 [] (ml_inv ts td) (ml_post ts td).
Definition mlBlk (ts td : string) : BlkAnnot := {| blk_ctx := mlCtx ; blk_contract := mlRec ts td |}.

Lemma valid_ml_loop : cfg_vc_loop (mlRec "vs" "dv") (ml_annot "vs" "dv").
Proof. Time solve_mb_vc. Qed.

(* ------------------------------------------------------------------------ *)
(* 2. memcpy, ITS EXIT THE RETURN ADDRESS                                   *)
(* ------------------------------------------------------------------------ *)
(* q: the code base; r: the return address; s, d: source and destination   *)
(* (A1, A0); n: the byte count (A2); vs: the source's value; dv: the         *)
(* destination's old value.                                                 *)
Definition mfCtx : LCtx :=
  ["q"∷ty_xlenbits; "r"∷ty_xlenbits; "s"∷ty_xlenbits; "d"∷ty_xlenbits;
   "n"∷ty_xlenbits; "vs"∷clemv_ty 1; "dv"∷clemv_ty 1].

Definition mf_pre (ts td : string) : Assertion (mfCtx ▻ "a"∷ty_xlenbits) :=
  ( X1 ↦ᵣ term_var "r"
    ∗ A0 ↦ᵣ term_var "d" ∗ secLeakvar "d"
    ∗ A1 ↦ᵣ term_var "s" ∗ secLeakvar "s"
    ∗ A2 ↦ᵣ term_var "n" ∗ secLeakvar "n"
    ∗ clem_arrv 1 1 ts (term_var "s") (term_var "n") (t_end (term_var "s") (term_var "n")) (term_var "vs")
    ∗ clem_arrv 1 1 td (term_var "d") (term_var "n") (t_end (term_var "d") (term_var "n")) (term_var "dv") )%asn.

(* the source back unchanged, the destination holding vs, A0 = d (memcpy's
   return value), X1 unchanged; A1..A4 with any value *)
Definition mf_post (ts td : string) : Assertion (mfCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( X1 ↦ᵣ term_var "r"
    ∗ A0 ↦ᵣ term_var "d"
    ∗ clem_arrv 1 1 ts (term_var "s") (term_var "n") (t_end (term_var "s") (term_var "n")) (term_var "vs")
    ∗ clem_arrv 1 1 td (term_var "d") (term_var "n") (t_end (term_var "d") (term_var "n")) (term_var "vs")
    ∗ asn.exist "w1" ty_xlenbits (A1 ↦ᵣ term_var "w1")
    ∗ asn.exist "w2" ty_xlenbits (A2 ↦ᵣ term_var "w2")
    ∗ asn.exist "w3" ty_xlenbits (A3 ↦ᵣ term_var "w3")
    ∗ asn.exist "w4" ty_xlenbits (A4 ↦ᵣ term_var "w4") )%asn.

Definition mf_regs : list reg_spec_rel := [ (A3, Secret); (A4, Secret) ].

Definition mfRec (ts td : string) : @CFGVerifierContract mfCtx :=
  gen_seg_contract_at (term_var "q") (term_var "q") (term_var "r")
    memcpy_instrs 12 mf_regs (secLeakvar "r" ∗ mf_pre ts td)%asn (mf_post ts td).
Definition mfBlk (ts td : string) : BlkAnnot := {| blk_ctx := mfCtx ; blk_contract := mfRec ts td |}.

Definition cl (k : CLem) : Annot := AnnotCLemma k.

(* Entry: seed the two DONE arrays AFTER the beqz -- the next instruction
   carries the loop block, which runs INSTEAD of it, ghosts included.  The
   seeds are made on the n = 0 path too, so they must sit at a KNOWN address:
   empty_at puts each at its array's start (clem_arrv_empty's address is an
   existential only the loop's entry would pin, and on the n = 0 path the
   exit join then looks for the source at that unknown address).
   Exit, before the ret (both paths): the destination's done array absorbs
   the source's emptied remainder's value (pad: done ++ rest = vs), the
   source's done and remainder join back into one array (done ++ rest), and
   the destination's emptied remainder goes (empty_elim). *)
Definition mf_seeds (ts td : string) : list Annot :=
  [ cl (clem_arrv_empty_at 1 1 ts mc_sd); cl (clem_arrv_empty_at 1 1 td td) ].
Definition mf_glue (ts td : string) : list Annot :=
  [ cl (clem_arrv_pad 1 1 td ts); cl (clem_arrv_join 1 1 mc_sd ts ts)
  ; cl (clem_arrv_empty_elim 1 1 td) ].

Definition mf_annot (ts td : string) : list AnnotInstr :=
  List.map (fun '(i, ins) =>
              {| ai_ghost_before := if Nat.eqb i 8 then mf_glue ts td else nil
               ; ai_instr := ins
               ; ai_ghost_after := if Nat.eqb i 1 then mf_seeds ts td else nil
               ; ai_block := if Nat.eqb i 2 then Some (mlBlk ts td) else None |})
    (List.combine (List.seq 0 (length memcpy_instrs)) memcpy_instrs).

Lemma valid_mf : cfg_vc_loop (mfRec "vs" "dv") (mf_annot "vs" "dv").
Proof. Time solve_mb_vc. Qed.

(* ------------------------------------------------------------------------ *)
(* 3. THE WHOLE PROGRAM: the harness calls memcpy                           *)
(* ------------------------------------------------------------------------ *)
Definition mcfCtx : LCtx := ["q"∷ty_xlenbits; "s"∷ty_xlenbits; "d"∷ty_xlenbits; "n"∷ty_xlenbits].

Definition mcf_regs : list (reg_spec_q mcfCtx) :=
  [ (A0, Known (PVVar "d")); (A1, Known (PVVar "s")); (A2, Known (PVVar "n")); (X1, Secret)
  ; (A3, Secret); (A4, Secret) ].

(* a PUBLIC source, a SECRET destination *)
Definition mcf_data (spub : bool) : list (data_spec mcfCtx) :=
  [ DPtr (term_var "s"); DBytes spub (term_var "n") "vs"
  ; DPtr (term_var "d"); DBytes false (term_var "n") "dv" ]%list.

Definition mcfCtxV : LCtx := mcfCtx ▻▻ data_vctx (mcf_data true).

(* the destination holds vs and is therefore PUBLIC -- by framing, no ghost *)
Definition mcf_post : Assertion (mcfCtxV ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( clem_arrv 1 1 "vs" (term_var "s") (term_var "n") (t_end (term_var "s") (term_var "n")) (term_var "vs")
    ∗ clem_arrv 1 1 "dv" (term_var "d") (term_var "n") (t_end (term_var "d") (term_var "n")) (term_var "vs")
    ∗ secLeakvar "vs"
    ∗ asn.exist "w1" ty_xlenbits (X1 ↦ᵣ term_var "w1")
    ∗ asn.exist "w0" ty_xlenbits (A0 ↦ᵣ term_var "w0")
    ∗ asn.exist "w8" ty_xlenbits (A1 ↦ᵣ term_var "w8")
    ∗ asn.exist "w2" ty_xlenbits (A2 ↦ᵣ term_var "w2")
    ∗ asn.exist "w3" ty_xlenbits (A3 ↦ᵣ term_var "w3")
    ∗ asn.exist "w4" ty_xlenbits (A4 ↦ᵣ term_var "w4") )%asn.

(* exit: the fall-through end, +44 = 4 * 11 *)
Definition mcfRec (spub : bool) : @CFGVerifierContract mcfCtxV :=
  gen_prog_contract "q" _ mcf_regs ⊤%asn 44 (mcf_data spub) mcf_instrs 10 mcf_post.

(* memcpy is a block on ITS first instruction, index 2 *)
Definition mcf_annot : list AnnotInstr :=
  List.map (fun '(i, ins) =>
              {| ai_ghost_before := nil ; ai_instr := ins ; ai_ghost_after := nil
               ; ai_block := if Nat.eqb i 2 then Some (mfBlk "vs" "dv") else None |})
    (List.combine (List.seq 0 (length mcf_instrs)) mcf_instrs).

Lemma valid_mcf : cfg_vc (mcfRec true) mcf_annot.
Proof. Time solve_mb_vc. Qed.

(* NEGATIVE CONTROLS *)

(* a SECRET source: the destination is not public *)
Goal cfg_vc (mcfRec false) mcf_annot.
Proof. Fail solve_mb_vc. Abort.

(* memcpy really copies: a post keeping the destination's OLD value fails *)
Goal cfg_vc_loop (gen_seg_contract_at (term_var "q") (term_var "q") (term_var "r")
    memcpy_instrs 12 mf_regs (secLeakvar "r" ∗ mf_pre "vs" "dv")%asn
    ( X1 ↦ᵣ term_var "r"
      ∗ clem_arrv 1 1 "dv" (term_var "d") (term_var "n") (t_end (term_var "d") (term_var "n")) (term_var "dv") )%asn)
  (mf_annot "vs" "dv").
Proof. Fail solve_mb_vc. Abort.
