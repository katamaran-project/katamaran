(* ========================================================================= *)
(* Example/Rsa/RsaMemset.v -- PLAN-rsa.md Phase 2 (D5): picolibc 1.8.12's   *)
(* size-optimised memset as a FUNCTION contract.  LIGHT, VCs only.           *)
(*                                                                           *)
(*   0:  jal ra, memset          the harness: call once,                     *)
(*   4:  j   _etext              then leave at the fall-through end (36)     *)
(*   8:  memset                  mv a3,a0; beqz a2,ret; then the byte loop   *)
(*                               at +16..+28; ret                            *)
(*                                                                           *)
(* The post does NOT name the written value (D5: every BearSSL call passes   *)
(* c = 0, and callers need lengths and publicness, not the zeros): given a   *)
(* public c, the destination comes back holding SOME public value.           *)
(* As in RsaMemcpy.v, the destination's done array shares its tag td.        *)
(*                                                                           *)
(* Instructions: tools/bearssl/picolibc.sh (memset.o) +                     *)
(* tools/bearssl/spike/harness_memset.s, `ld.lld --relax -Ttext=0`,         *)
(* `llvm-objdump -d --no-show-raw-insn`, `asm_to_ast.py --objdump           *)
(* --tables-aliases --name msf`.  Regenerate, do not edit.                  *)
(* ========================================================================= *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamClose.

Definition msf_instrs : list AST :=
  [ RISCV_JAL (bv.of_Z 8) X1   (* jal	L_8	# 0x0: jal 0x8 <memset> *)
  ; RISCV_JAL (bv.of_Z 32) X0   (* j	L_24	# 0x4: j 0x24 <_etext> *)
  ; ITYPE (bv.of_Z 0) A0 A3 RISCV_ADDI   (* mv	a3, a0	# 0x8: mv a3, a0 *)
  ; BTYPE (bv.of_Z 20) X0 A2 RISCV_BEQ   (* beqz	a2, L_20	# 0xc: beqz a2, 0x20 <.Ldone> *)
  ; STORE (bv.of_Z 0) A1 A3 BYTE   (* sb	a1, 0(a3)	# 0x10: sb a1, 0x0(a3) *)
  ; ITYPE (bv.of_Z (-1)) A2 A2 RISCV_ADDI   (* addi	a2, a2, -1	# 0x14: addi a2, a2, -0x1 *)
  ; ITYPE (bv.of_Z 1) A3 A3 RISCV_ADDI   (* addi	a3, a3, 1	# 0x18: addi a3, a3, 0x1 *)
  ; BTYPE (bv.of_Z (-12)) X0 A2 RISCV_BNE   (* bnez	a2, L_10	# 0x1c: bnez a2, 0x10 <.Lset> *)
  ; RISCV_JALR (bv.of_Z 0) X1 X0   (* ret		# 0x20: ret *)
  ].

(* memset's own code, from its first instruction (byte offset 8) *)
Definition memset_instrs : list AST := List.skipn 2 msf_instrs.
(* its byte loop: instructions 2..5 of memset_instrs (+8..+20) *)
Definition msl_instrs : list AST := List.firstn 4 (List.skipn 2 memset_instrs).

Definition t_end {Σ} (a n : Term Σ ty_xlenbits) : Term Σ ty_xlenbits :=
  term_binop bop.bvadd a n.

(* ------------------------------------------------------------------------ *)
(* 1. THE BYTE LOOP                                                         *)
(* ------------------------------------------------------------------------ *)
(* Invariant: the destination is DONE ++ (old), done is public, k + c = n.  *)
(* One step: take the destination's next cell, store c's low byte (public,  *)
(* since c is), add the cell to the done array.                             *)
Definition mslCtx : LCtx :=
  ["q"∷ty_xlenbits; "d"∷ty_xlenbits; "f"∷ty_xlenbits; "n"∷ty_xlenbits; "v"∷ty_xlenbits].

Definition msl_annot (td : string) : list AnnotInstr :=
  [ {| ai_ghost_before := [ AnnotCLemma (clem_arrv_take_first 1 1 td) ]
     ; ai_instr := STORE (bv.of_Z 0) A1 A3 BYTE
     ; ai_ghost_after := [ AnnotCLemma (clem_arrv_add_last 1 1 td) ]; ai_block := None |}
  ; AST_AnnotInstr (ITYPE (bv.of_Z (-1)) A2 A2 RISCV_ADDI)
  ; AST_AnnotInstr (ITYPE (bv.of_Z 1) A3 A3 RISCV_ADDI)
  ; AST_AnnotInstr (BTYPE (bv.of_Z (-12)) X0 A2 RISCV_BNE) ].

(* the loop state with c bytes to go, k done, cursor r *)
Definition msl_state {Σ} (td : string) (d f n c k r : Term Σ ty_xlenbits)
    (done drest : Term Σ (clemv_ty 1)) : Assertion Σ :=
  ( clem_arrv_angelic 1 1 td d k r done ∗ clem_arrv_angelic 1 1 td r c f drest
    ∗ A3 ↦ᵣ r ∗ A2 ↦ᵣ c
    ∗ asn.formula (formula_relop bop.eq (term_binop bop.bvadd k c) n)
    ∗ asn.formula (formula_secLeak done) )%asn.

Definition msl_inv (td : string) : Assertion (mslCtx ▻ "a"∷ty_xlenbits) :=
  ( asn.exist "c" ty_xlenbits (asn.exist "k" ty_xlenbits (asn.exist "r" ty_xlenbits
    (asn.exist "done" (clemv_ty 1) (asn.exist "drest" (clemv_ty 1)
      ( msl_state td (term_var "d") (term_var "f") (term_var "n") (term_var "c")
          (term_var "k") (term_var "r") (term_var "done") (term_var "drest")
        ∗ secLeakvar "c" ∗ secLeakvar "r"
        ∗ clem_nonzero (term_var "c"))))))
    ∗ A1 ↦ᵣ term_var "v" ∗ secLeakvar "v" )%asn.

Definition msl_post (td : string) : Assertion (mslCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( asn.exist "k" ty_xlenbits (asn.exist "r" ty_xlenbits
    (asn.exist "done" (clemv_ty 1) (asn.exist "drest" (clemv_ty 1)
      (msl_state td (term_var "d") (term_var "f") (term_var "n")
         (term_val ty_xlenbits bv.zero) (term_var "k") (term_var "r")
         (term_var "done") (term_var "drest")))))
    ∗ A1 ↦ᵣ term_var "v" )%asn.

Definition mslRec (td : string) : @CFGVerifierContract mslCtx :=
  gen_seg_contract (term_var "q") (term_var "q") msl_instrs 16 12 [] (msl_inv td) (msl_post td).
Definition mslBlk (td : string) : BlkAnnot := {| blk_ctx := mslCtx ; blk_contract := mslRec td |}.

Lemma valid_msl_loop : cfg_vc_loop (mslRec "dv") (msl_annot "dv").
Proof. Time solve_mb_vc. Qed.

(* ------------------------------------------------------------------------ *)
(* 2. memset, ITS EXIT THE RETURN ADDRESS                                   *)
(* ------------------------------------------------------------------------ *)
(* q: the code base; r: the return address; d: the destination (A0); v: the *)
(* fill value (A1, public); n: the byte count (A2); dv: the old value.      *)
Definition mfsCtx : LCtx :=
  ["q"∷ty_xlenbits; "r"∷ty_xlenbits; "d"∷ty_xlenbits; "v"∷ty_xlenbits;
   "n"∷ty_xlenbits; "dv"∷clemv_ty 1].

Definition mfs_pre (td : string) : Assertion (mfsCtx ▻ "a"∷ty_xlenbits) :=
  ( X1 ↦ᵣ term_var "r"
    ∗ A0 ↦ᵣ term_var "d" ∗ secLeakvar "d"
    ∗ A1 ↦ᵣ term_var "v" ∗ secLeakvar "v"
    ∗ A2 ↦ᵣ term_var "n" ∗ secLeakvar "n"
    ∗ clem_arrv 1 1 td (term_var "d") (term_var "n") (t_end (term_var "d") (term_var "n")) (term_var "dv") )%asn.

(* the destination holding SOME public value, A0 = d (memset's return
   value), A1 = v, X1 unchanged; A2, A3 with any value *)
Definition mfs_post (td : string) : Assertion (mfsCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( X1 ↦ᵣ term_var "r"
    ∗ A0 ↦ᵣ term_var "d" ∗ A1 ↦ᵣ term_var "v"
    ∗ asn.exist "vs" (clemv_ty 1)
        (clem_arrv 1 1 td (term_var "d") (term_var "n") (t_end (term_var "d") (term_var "n"))
           (term_var "vs") ∗ secLeakvar "vs")
    ∗ asn.exist "w2" ty_xlenbits (A2 ↦ᵣ term_var "w2")
    ∗ asn.exist "w3" ty_xlenbits (A3 ↦ᵣ term_var "w3") )%asn.

Definition mfs_regs : list reg_spec_rel := [ (A3, Secret) ].

Definition mfsRec (td : string) : @CFGVerifierContract mfsCtx :=
  gen_seg_contract_at (term_var "q") (term_var "q") (term_var "r")
    memset_instrs 10 mfs_regs (secLeakvar "r" ∗ mfs_pre td)%asn (mfs_post td).
Definition mfsBlk (td : string) : BlkAnnot := {| blk_ctx := mfsCtx ; blk_contract := mfsRec td |}.

Definition cl (k : CLem) : Annot := AnnotCLemma k.

(* Entry, after the beqz: the done seed at the destination's start (it is
   made on the n = 0 path too, see RsaMemcpy.v).  Exit, before the ret (both
   paths): the destination's emptied remainder goes; what is left is the
   done array -- or, for n = 0, the seed or the untouched destination, the
   angelic match picking the public one. *)
Definition mfs_annot (td : string) : list AnnotInstr :=
  List.map (fun '(i, ins) =>
              {| ai_ghost_before := if Nat.eqb i 6 then [ cl (clem_arrv_empty_elim 1 1 td) ] else nil
               ; ai_instr := ins
               ; ai_ghost_after := if Nat.eqb i 1 then [ cl (clem_arrv_empty_at 1 1 td td) ] else nil
               ; ai_block := if Nat.eqb i 2 then Some (mslBlk td) else None |})
    (List.combine (List.seq 0 (length memset_instrs)) memset_instrs).

Lemma valid_mfs : cfg_vc_loop (mfsRec "dv") (mfs_annot "dv").
Proof. Time solve_mb_vc. Qed.

(* ------------------------------------------------------------------------ *)
(* 3. THE WHOLE PROGRAM: the harness calls memset on a SECRET destination   *)
(* ------------------------------------------------------------------------ *)
Definition msfCtx : LCtx := ["q"∷ty_xlenbits; "d"∷ty_xlenbits; "v"∷ty_xlenbits; "n"∷ty_xlenbits].

Definition msf_regs (vpub : bool) : list (reg_spec_q msfCtx) :=
  [ (A0, Known (PVVar "d")); (A1, if vpub then Known (PVVar "v") else Secret)
  ; (A2, Known (PVVar "n")); (X1, Secret); (A3, Secret) ].

Definition msf_data : list (data_spec msfCtx) :=
  [ DPtr (term_var "d"); DBytes false (term_var "n") "dv" ]%list.

Definition msfCtxV : LCtx := msfCtx ▻▻ data_vctx msf_data.

(* afterwards the destination is PUBLIC *)
Definition msf_post : Assertion (msfCtxV ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( asn.exist "vs" (clemv_ty 1)
      (clem_arrv 1 1 "dv" (term_var "d") (term_var "n") (t_end (term_var "d") (term_var "n"))
         (term_var "vs") ∗ secLeakvar "vs")
    ∗ asn.exist "w1" ty_xlenbits (X1 ↦ᵣ term_var "w1")
    ∗ asn.exist "w0" ty_xlenbits (A0 ↦ᵣ term_var "w0")
    ∗ asn.exist "w8" ty_xlenbits (A1 ↦ᵣ term_var "w8")
    ∗ asn.exist "w2" ty_xlenbits (A2 ↦ᵣ term_var "w2")
    ∗ asn.exist "w3" ty_xlenbits (A3 ↦ᵣ term_var "w3") )%asn.

(* exit: the fall-through end, +36 = 4 * 9 *)
Definition msfRec (vpub : bool) : @CFGVerifierContract msfCtxV :=
  gen_prog_contract "q" _ (msf_regs vpub) ⊤%asn 36 msf_data msf_instrs 8 msf_post.

(* memset is a block on ITS first instruction, index 2 *)
Definition msf_annot : list AnnotInstr :=
  List.map (fun '(i, ins) =>
              {| ai_ghost_before := nil ; ai_instr := ins ; ai_ghost_after := nil
               ; ai_block := if Nat.eqb i 2 then Some (mfsBlk "dv") else None |})
    (List.combine (List.seq 0 (length msf_instrs)) msf_instrs).

Lemma valid_msf : cfg_vc (msfRec true) msf_annot.
Proof. Time solve_mb_vc. Qed.

(* NEGATIVE CONTROLS *)

(* a SECRET fill value: the call's precondition (secLeak v) fails *)
Goal cfg_vc (msfRec false) msf_annot.
Proof. Fail solve_mb_vc. Abort.

(* the loop really needs c public: without secLeak v the done array is not *)
Goal cfg_vc_loop (gen_seg_contract (term_var "q") (term_var "q") msl_instrs 16 12 []
    ( asn.exist "c" ty_xlenbits (asn.exist "k" ty_xlenbits (asn.exist "r" ty_xlenbits
      (asn.exist "done" (clemv_ty 1) (asn.exist "drest" (clemv_ty 1)
        ( msl_state "dv" (term_var "d") (term_var "f") (term_var "n") (term_var "c")
            (term_var "k") (term_var "r") (term_var "done") (term_var "drest")
          ∗ secLeakvar "c" ∗ secLeakvar "r"
          ∗ clem_nonzero (term_var "c"))))))
      ∗ A1 ↦ᵣ term_var "v" )%asn
    (msl_post "dv")) (msl_annot "dv").
Proof. Fail solve_mb_vc. Abort.
