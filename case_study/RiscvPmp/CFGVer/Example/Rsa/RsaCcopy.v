(* ========================================================================= *)
(* Example/Rsa/RsaCcopy.v -- PLAN-rsa.md Phase 2 (O4): BearSSL's br_ccopy   *)
(* (src/codec/ccopy.c, hardened build), `dst[i] = MUX(ctl, src[i], dst[i])` *)
(* byte-wise, as a FUNCTION contract that keeps a SHARED HEADER public under *)
(* a secret ctl.  LIGHT, VCs only.                                          *)
(*                                                                           *)
(*   0:  jal ra, br_ccopy        the harness: call once,                     *)
(*   4:  j   _etext              then leave at the fall-through end (64)     *)
(*   8:  br_ccopy                beqz len,ret; a0 := -ctl; a3 := src + len;  *)
(*                               loop (+20..+56): lbu x,src; lbu y,dst;      *)
(*                               ((y^x) & a0) ^ y; sb; both += 1; until      *)
(*                               src = a3; ret                               *)
(*                                                                           *)
(* Why the header needs care: under a secret ctl the stored byte is a        *)
(* NonSyncVal even where x and y are the same public term h, and no rewrite  *)
(* may make it public (≡ is Leibniz on RelVal).  Both arrays therefore carry *)
(* their 4 header bytes as the SAME named terms h0..h3 (`h0 :: .. :: h3 ::   *)
(* rest`); the loop invariant tracks the header phase explicitly (one        *)
(* disjunct per header byte, k = 0..3, the cells as cons lists, plus the     *)
(* limb phase), so the written header bytes are syntactically                *)
(* clem_mux_byte h_k m; and before the ret the ghost clem_resync_mux puts    *)
(* h_k back in each (memory reads only the two projections, which are equal *)
(* there).  The ghosts in the loop body are the same in every phase.         *)
(*                                                                           *)
(* Instructions: tools/bearssl/build.sh (hardened ccopy.o) +                *)
(* tools/bearssl/spike/harness_ccopy.s, `ld.lld --relax -Ttext=0`,          *)
(* `llvm-objdump -d --no-show-raw-insn`, `asm_to_ast.py --objdump           *)
(* --tables-aliases --name ccf`.  Regenerate, do not edit.                  *)
(* ========================================================================= *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamClose.
From Coq Require Import ZArith Lia.

(* ------------------------------------------------------------------------ *)
(* The closer, extended for this file (kept local: MuladdParamClose's       *)
(* closer serves the muladd/check_scalar VCs, whose leaves must not start   *)
(* case-splitting every value).  Two leaf shapes the header phase leaves:  *)
(* `[] ++ v = v` and a ring identity over values that are NOT public (the   *)
(* limb pointers' arithmetic, the remainder's value): both hold for either  *)
(* RelVal case, so split them all.                                          *)
(* ------------------------------------------------------------------------ *)
Lemma rv_app_nil_l {σ} (v : RelVal (ty.list σ)) : v = bop.evalRel bop.append (ty.SyncVal nil) v.
Proof. destruct v; reflexivity. Qed.

Ltac bv_lin_cc :=
  first
    [ bv_lin
    | apply bv.unsigned_inj;
      repeat first [ rewrite bv.unsigned_add | rewrite bv.unsigned_sub
                   | rewrite bv.unsigned_negate | rewrite bv.unsigned_mul ];
      unfold bv.truncz;
      repeat match goal with x : bv _ |- _ =>
        lazymatch goal with _ : (0 <= bv.unsigned x < _)%Z |- _ => fail
                          | _ => pose proof (bv.unsigned_bounds x) end end;
      unfold bv.unsigned in *; cbn [bv.bin] in *; bv_consts; cbn [Z.of_N] in *;
      Z.to_euclidean_division_equations; lia ].

Ltac rv_leaf_cc :=
  first
    [ rv_leaf
    | apply rv_app_nil_l
    (* only an evar-free equation, splitting only the values IN it: on a
       wrong angelic branch's leaf this would otherwise split every value in
       scope (2^k), measured as a >3x slowdown before this guard *)
    | (cbn -[Erasure.inst_symprop] in *;
       lazymatch goal with |- @eq (RelVal _) ?l ?r =>
         tryif has_evar l then fail else tryif has_evar r then fail else idtac end;
       repeat match goal with |- context [?v] =>
         is_var v; lazymatch type of v with RelVal (ty.bvec _) => destruct v end end;
       cbn -[Erasure.inst_symprop bv.add bv.mul bv.sub bv.negate bv.shiftl bv.shiftr bv.land
             bv.sext bv.unsigned bv.of_N bv.ult bv.ule] in *;
       f_equal; bv_lin_cc) ].

Ltac mb_search_cc :=
  lazymatch goal with
  | |- exists _, _ =>
      (repeat eexists; repeat split;
       try (lazymatch goal with
            | |- Erasure.inst_eformula' _ _ => cbn -[Erasure.inst_symprop]
            | |- Erasure.inst_eq _ _ => cbn -[Erasure.inst_symprop] end);
       try mb_eq_evar); mb_search_cc
  | |- _ /\ _ => split; mb_search_cc
  | |- True => exact I
  | |- forall _, _ => intro; mb_search_cc
  | |- _ \/ _ => first [ left; mb_search_cc | right; mb_search_cc ]
  | |- _ => solve [ rv_leaf_cc ]
  end.

Ltac solve_cc_vc :=
  intros; vm_compute; solve_vc;
  try solve_symbase_fetch;
  cbn [Erasure.inst_symprop];
  cbn -[Erasure.inst_symprop] in * |- ;
  mb_search_cc.

Definition ccf_instrs : list AST :=
  [ RISCV_JAL (bv.of_Z 8) X1   (* jal	L_8	# 0x0: jal 0x8 <br_ccopy> *)
  ; RISCV_JAL (bv.of_Z 60) X0   (* j	L_40	# 0x4: j 0x40 <_etext> *)
  ; BTYPE (bv.of_Z 52) X0 A3 RISCV_BEQ   (* beqz	a3, L_3c	# 0x8: beqz a3, 0x3c <.LBB0_3> *)
  ; RTYPE A0 X0 A0 RISCV_SUB   (* neg	a0, a0	# 0xc: neg a0, a0 *)
  ; RTYPE A3 A2 A3 RISCV_ADD   (* add	a3, a2, a3	# 0x10: add a3, a2, a3 *)
  ; LOAD (bv.of_Z 0) A2 A4 true BYTE   (* lbu	a4, 0(a2)	# 0x14: lbu a4, 0x0(a2) *)
  ; LOAD (bv.of_Z 0) A1 A5 true BYTE   (* lbu	a5, 0(a1)	# 0x18: lbu a5, 0x0(a1) *)
  ; ITYPE (bv.of_Z 1) A2 A6 RISCV_ADDI   (* addi	a6, a2, 1	# 0x1c: addi a6, a2, 0x1 *)
  ; RTYPE A4 A5 A4 RISCV_XOR   (* xor	a4, a5, a4	# 0x20: xor a4, a5, a4 *)
  ; RTYPE A0 A4 A4 RISCV_AND   (* and	a4, a4, a0	# 0x24: and a4, a4, a0 *)
  ; RTYPE A5 A4 A4 RISCV_XOR   (* xor	a4, a4, a5	# 0x28: xor a4, a4, a5 *)
  ; STORE (bv.of_Z 0) A4 A1 BYTE   (* sb	a4, 0(a1)	# 0x2c: sb a4, 0x0(a1) *)
  ; ITYPE (bv.of_Z 1) A1 A1 RISCV_ADDI   (* addi	a1, a1, 1	# 0x30: addi a1, a1, 0x1 *)
  ; ITYPE (bv.of_Z 0) A6 A2 RISCV_ADDI   (* mv	a2, a6	# 0x34: mv a2, a6 *)
  ; BTYPE (bv.of_Z (-36)) A3 A6 RISCV_BNE   (* bne	a6, a3, L_14	# 0x38: bne a6, a3, 0x14 <.LBB0_2> *)
  ; RISCV_JALR (bv.of_Z 0) X1 X0   (* ret		# 0x3c: ret *)
  ].

(* br_ccopy's own code, from its first instruction (byte offset 8) *)
Definition ccopy_instrs : list AST := List.skipn 2 ccf_instrs.
(* its loop: instructions 3..12 of ccopy_instrs (+12..+48) *)
Definition ccl_instrs : list AST := List.firstn 10 (List.skipn 3 ccopy_instrs).

Definition t_end {Σ} (a n : Term Σ ty_xlenbits) : Term Σ ty_xlenbits :=
  term_binop bop.bvadd a n.
Definition t_sub {Σ} (a b : Term Σ ty_xlenbits) : Term Σ ty_xlenbits :=
  term_binop bop.bvsub a b.
Definition t_lit {Σ} (k : nat) : Term Σ ty_xlenbits := term_val ty_xlenbits (bv.of_N (N.of_nat k)).

(* `x0 :: .. :: xk :: tl` *)
Fixpoint cons_terms {Σ σ} (xs : list (Term Σ σ)) (tl : Term Σ (ty.list σ)) : Term Σ (ty.list σ) :=
  match xs with
  | nil => tl
  | List.cons x xs => term_binop bop.cons x (cons_terms xs tl)
  end.
Definition lnil {Σ σ} : Term Σ (ty.list σ) := term_val (ty.list σ) nil.
(* the four header bytes *)
Definition hl4 {Σ σ} (a b c d : Term Σ σ) : list (Term Σ σ) :=
  List.cons a (List.cons b (List.cons c (List.cons d nil))).

(* The loop takes each byte with clem_arrv_take_any: by PATTERN in the
   header phase (the remainder is h_k :: .., and only a pattern take keeps
   h_k's identity -- lifted cons is not injective under the tag), by
   EQUATION in the limb phase (the remainder is a variable).  The choice is
   angelic, so the ghosts are the same every trip. *)

(* the source's DONE array: a tag of br_ccopy's own *)
Definition cc_sd : string := "ccopy.sd".

(* ------------------------------------------------------------------------ *)
(* 1. THE LOOP                                                              *)
(* ------------------------------------------------------------------------ *)
(* Parameters: src s, dst d, the limb count nl (total n = nl + 4), the mask  *)
(* M (A0 = -ctl), the header bytes h0..h3, the limbs' values sl (src) and   *)
(* dl (dst, its old value).                                                 *)
Definition cclCtx : LCtx :=
  ["q"∷ty_xlenbits; "s"∷ty_xlenbits; "d"∷ty_xlenbits; "nl"∷ty_xlenbits; "M"∷ty_xlenbits;
   "h0"∷clem_cell_ty 1; "h1"∷clem_cell_ty 1; "h2"∷clem_cell_ty 1; "h3"∷clem_cell_ty 1;
   "sl"∷clemv_ty 1; "dl"∷clemv_ty 1].

Definition ccl_annot (ts td : string) : list AnnotInstr :=
  [ {| ai_ghost_before := [ AnnotCLemma (clem_arrv_take_any 1 1 ts) ]
     ; ai_instr := LOAD (bv.of_Z 0) A2 A4 true BYTE
     ; ai_ghost_after := [ AnnotCLemma (clem_arrv_add_last 1 1 cc_sd) ]; ai_block := None |}
  ; {| ai_ghost_before := [ AnnotCLemma (clem_arrv_take_any 1 1 td) ]
     ; ai_instr := LOAD (bv.of_Z 0) A1 A5 true BYTE
     ; ai_ghost_after := nil; ai_block := None |}
  ; AST_AnnotInstr (ITYPE (bv.of_Z 1) A2 A6 RISCV_ADDI)
  ; AST_AnnotInstr (RTYPE A4 A5 A4 RISCV_XOR)
  ; AST_AnnotInstr (RTYPE A0 A4 A4 RISCV_AND)
  ; AST_AnnotInstr (RTYPE A5 A4 A4 RISCV_XOR)
  ; {| ai_ghost_before := nil
     ; ai_instr := STORE (bv.of_Z 0) A4 A1 BYTE
     ; ai_ghost_after := [ AnnotCLemma (clem_arrv_add_last 1 1 td) ]; ai_block := None |}
  ; AST_AnnotInstr (ITYPE (bv.of_Z 1) A1 A1 RISCV_ADDI)
  ; AST_AnnotInstr (ITYPE (bv.of_Z 0) A6 A2 RISCV_ADDI)
  ; AST_AnnotInstr (BTYPE (bv.of_Z (-36)) A3 A6 RISCV_BNE) ].

(* k done, cnt to go, cursors p (src) r (dst); E = s + n the src end *)
Definition ccl_state {Σ} (ts td : string) (s d n M k cnt p r : Term Σ ty_xlenbits)
    (sdv srv ddv drv : Term Σ (clemv_ty 1)) : Assertion Σ :=
  ( clem_arrv_angelic 1 1 cc_sd s k p sdv ∗ clem_arrv_angelic 1 1 ts p cnt (t_end s n) srv
    ∗ clem_arrv_angelic 1 1 td d k r ddv ∗ clem_arrv_angelic 1 1 td r cnt (t_end d n) drv
    ∗ A2 ↦ᵣ p ∗ A1 ↦ᵣ r ∗ A3 ↦ᵣ t_end s n ∗ A0 ↦ᵣ M )%asn.

(* the header phase, at header byte k (0..3): everything a literal *)
Definition ccl_hdr {Σ} (ts td : string) (s d nl M : Term Σ ty_xlenbits)
    (hs : list (Term Σ (clem_cell_ty 1))) (sl dl : Term Σ (clemv_ty 1)) (k : nat) : Assertion Σ :=
  ccl_state ts td s d (clem_off nl 4) M (t_lit k) (clem_off nl (4 - Z.of_nat k))
    (clem_off s (Z.of_nat k)) (clem_off d (Z.of_nat k))
    (cons_terms (List.firstn k hs) lnil) (cons_terms (List.skipn k hs) sl)
    (cons_terms (List.map (fun h => clem_mux_byte h M) (List.firstn k hs)) lnil)
    (cons_terms (List.skipn k hs) dl).

(* the limb phase, c to go: all addresses END - c *)
Definition ccl_limb {Σ} (ts td : string) (s d nl M c : Term Σ ty_xlenbits)
    (hs : list (Term Σ (clem_cell_ty 1))) (sd sr dd dr : Term Σ (clemv_ty 1)) : Assertion Σ :=
  let n := clem_off nl 4 in
  ccl_state ts td s d n M (t_sub n c) c (t_sub (t_end s n) c) (t_sub (t_end d n) c)
    (cons_terms hs sd) sr (cons_terms (List.map (fun h => clem_mux_byte h M) hs) dd) dr.

Definition ccl_inv (ts td : string) : Assertion (cclCtx ▻ "a"∷ty_xlenbits) :=
  let hs := (hl4 (term_var "h0") (term_var "h1") (term_var "h2") (term_var "h3")) in
  let hdr := ccl_hdr ts td (term_var "s") (term_var "d") (term_var "nl") (term_var "M") hs
               (term_var "sl") (term_var "dl") in
  ( asn.or (hdr 0) (asn.or (hdr 1) (asn.or (hdr 2) (asn.or (hdr 3)
      (asn.exist "c" ty_xlenbits (asn.exist "sd" (clemv_ty 1) (asn.exist "sr" (clemv_ty 1)
       (asn.exist "dd" (clemv_ty 1) (asn.exist "dr" (clemv_ty 1)
        ( ccl_limb ts td (term_var "s") (term_var "d") (term_var "nl") (term_var "M") (term_var "c")
            (hl4 (term_var "h0") (term_var "h1") (term_var "h2") (term_var "h3"))
            (term_var "sd") (term_var "sr") (term_var "dd") (term_var "dr")
          ∗ secLeakvar "c" ∗ clem_nonzero (term_var "c")
          ∗ asn.formula (formula_propeq (term_var "sl")
              (term_binop bop.append (term_var "sd") (term_var "sr"))))))))))))
    ∗ secLeakvar "s" ∗ secLeakvar "d" ∗ secLeakvar "nl"
    (* 0 < nl < 2^31: limbs after the header, and nothing wraps -- the
       header phase's counts and early exits close from these by bv_lin *)
    ∗ clem_nonzero (term_var "nl")
    ∗ asn.formula (formula_relop bop.bvult (term_var "nl") (term_val ty_xlenbits (bv.of_N 0x80000000)))
    ∗ asn.exist "v4" ty_xlenbits (A4 ↦ᵣ term_var "v4")
    ∗ asn.exist "v5" ty_xlenbits (A5 ↦ᵣ term_var "v5")
    ∗ asn.exist "v6" ty_xlenbits (A6 ↦ᵣ term_var "v6") )%asn.

(* done: the limb phase with nothing to go *)
Definition ccl_post (ts td : string) : Assertion (cclCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( asn.exist "sd" (clemv_ty 1) (asn.exist "sr" (clemv_ty 1)
     (asn.exist "dd" (clemv_ty 1) (asn.exist "dr" (clemv_ty 1)
      ( ccl_limb ts td (term_var "s") (term_var "d") (term_var "nl") (term_var "M")
          (term_val ty_xlenbits bv.zero)
          (hl4 (term_var "h0") (term_var "h1") (term_var "h2") (term_var "h3"))
          (term_var "sd") (term_var "sr") (term_var "dd") (term_var "dr")
        ∗ asn.formula (formula_propeq (term_var "sl")
            (term_binop bop.append (term_var "sd") (term_var "sr")))))))
    ∗ asn.exist "v4" ty_xlenbits (A4 ↦ᵣ term_var "v4")
    ∗ asn.exist "v5" ty_xlenbits (A5 ↦ᵣ term_var "v5")
    ∗ asn.exist "v6" ty_xlenbits (A6 ↦ᵣ term_var "v6") )%asn.

Definition cclRec (ts td : string) : @CFGVerifierContract cclCtx :=
  gen_seg_contract (term_var "q") (term_var "q") ccl_instrs 40 14 [] (ccl_inv ts td) (ccl_post ts td).
Definition cclBlk (ts td : string) : BlkAnnot := {| blk_ctx := cclCtx ; blk_contract := cclRec ts td |}.

Lemma valid_ccl_loop : cfg_vc_loop (cclRec "vs" "dv") (ccl_annot "vs" "dv").
Proof. Time solve_cc_vc. Qed.
