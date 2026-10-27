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
(* clem_mux_byte h_k m; and before the ret clem_arrv_resync_head puts h_k *)
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

Ltac bv_lin_rw_cc :=
  repeat first
    [ rewrite bv.unsigned_add | rewrite bv.unsigned_sub | rewrite bv.unsigned_negate
    | rewrite bv.unsigned_mul | rewrite unsigned_shiftl_c | rewrite unsigned_shiftr_c
    | rewrite sext_id32 ].
Ltac bv_lin_rw_cc_in H :=
  repeat first
    [ rewrite bv.unsigned_add in H | rewrite bv.unsigned_sub in H | rewrite bv.unsigned_negate in H
    | rewrite bv.unsigned_mul in H | rewrite unsigned_shiftl_c in H | rewrite unsigned_shiftr_c in H
    | rewrite sext_id32 in H ].

(* MuladdParamClose.bv_lin with subtraction and negation (the limb phase's
   addresses are END - c) *)
Ltac bv_lin_cc :=
  bv_rel_to_Z;
  try (apply bv.unsigned_inj);
  try (match goal with |- _ <> _ => let E := fresh "E" in intro E; apply (f_equal bv.unsigned) in E end);
  repeat match goal with
  | H : @eq (bv ?n) ?a ?b |- _ =>
      apply (f_equal bv.unsigned) in H; revert H
  | H : @eq (bv ?n) ?a ?b -> False |- _ =>
      let H' := fresh "Hne" in
      pose proof (fun E => H (bv.unsigned_inj a b E)) as H'; clear H; revert H'
  | H : ~ (@eq (bv ?n) ?a ?b) |- _ =>
      let H' := fresh "Hne" in
      pose proof (fun E => H (bv.unsigned_inj a b E)) as H'; clear H; revert H'
  end; intros;
  bv_lin_rw_cc;
  repeat match goal with H : _ |- _ => progress (bv_lin_rw_cc_in H) end;
  unfold bv.truncz, bv.ult, bv.ule in *;
  repeat match goal with x : bv _ |- _ =>
    lazymatch goal with _ : (0 <= bv.unsigned x < _)%Z |- _ => fail
                      | _ => pose proof (bv.unsigned_bounds x) end end;
  unfold bv.unsigned in *; cbn [bv.bin] in *; bv_consts; cbn [Z.of_N] in *;
  Z.to_euclidean_division_equations; lia.

(* MuladdParamClose.rv_leaf with bv_lin_cc, bv.sub/bv.negate kept folded *)
Ltac rv_leaf_core :=
  cbn -[Erasure.inst_symprop] in *;
  repeat match goal with v : RelVal _, H : RiscvPmpSignature.secLeak ?v |- _ =>
    is_var v; destruct v; [|destruct H] end;
  cbn -[Erasure.inst_symprop bv.add bv.mul bv.sub bv.negate bv.shiftl bv.shiftr bv.land bv.sext
        bv.unsigned bv.of_N bv.ult bv.ule] in *;
  first [ exact I
        | lazymatch goal with
          | |- RiscvPmpSignature.secLeak ?v =>
              is_evar v; unify v (ty.SyncVal (@bv.zero xlenbits)); exact I
          end
        | assumption | reflexivity | (f_equal; bv_lin_cc) | bv_lin_cc
        | (exfalso; bv_lin_cc) ].

Ltac rv_leaf_cc :=
  first
    [ rv_leaf_core
    | apply rv_app_nil_l
    (* a value fixed by an equation in the context (the loop's `sl = sd ++
       sr`): substitute it first *)
    | (cbn -[Erasure.inst_symprop] in *;
       progress (repeat match goal with H : ?v = _ |- _ => is_var v; subst v end);
       first [ reflexivity | rv_leaf_core ])
    (* only an evar-free equation, splitting only the values IN it: on a
       wrong angelic branch's leaf this would otherwise split every value in
       scope (2^k), measured as a >3x slowdown before this guard *)
    | (cbn -[Erasure.inst_symprop] in *;
       lazymatch goal with |- @eq (RelVal _) ?l ?r =>
         tryif has_evar l then fail else tryif has_evar r then fail else idtac end;
       repeat match goal with |- context [?v] =>
         is_var v; lazymatch type of v with RelVal _ => destruct v end end;
       cbn -[Erasure.inst_symprop bv.add bv.mul bv.sub bv.negate bv.shiftl bv.shiftr bv.land
             bv.sext bv.unsigned bv.of_N bv.ult bv.ule app] in *;
       f_equal;
       first [ bv_lin_cc
             (* a list identity (the remainder's value): associativity *)
             | (repeat rewrite <- List.app_assoc; reflexivity) ]) ].

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

(* evars no leaf constrains -- the unused side of a take_any (its pattern
   head and tail, or its equation's value): any value *)
Ltac fill_evar :=
  first [ exact (ty.SyncVal bv.zero) | exact (ty.SyncVal nil) | exact (ty.SyncVal true) ].

Ltac solve_cc_vc :=
  intros; vm_compute; solve_vc;
  try solve_symbase_fetch;
  cbn [Erasure.inst_symprop];
  cbn -[Erasure.inst_symprop] in * |- ;
  mb_search_cc.

(* the whole discharge: an angelic step leaves `∃ (_ : P), Q`, and eexists
   SHELVES the obligation P (for the function VC: everything from the loop
   block's entry on) -- bring the shelf back and close it the same way; all
   inside `solve` so that a negative control really fails *)
Ltac solve_cc_all :=
  solve [ unshelve solve_cc_vc;
          try fill_evar;
          try (cbn [Erasure.inst_symprop]; cbn -[Erasure.inst_symprop] in * |- ;
               unshelve mb_search_cc; try fill_evar) ].

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
Proof. Time solve_cc_all. Qed.

(* ------------------------------------------------------------------------ *)
(* 2. br_ccopy, ITS EXIT THE RETURN ADDRESS                                 *)
(* ------------------------------------------------------------------------ *)
(* r: the return address; ctl (A0, SECRET); dst d (A1), src s (A2), len n   *)
(* (A3) = nl + 4.  Both arrays START with the same four bytes h0..h3.       *)
Definition ccfCtx : LCtx :=
  ["q"∷ty_xlenbits; "r"∷ty_xlenbits; "s"∷ty_xlenbits; "d"∷ty_xlenbits; "n"∷ty_xlenbits;
   "nl"∷ty_xlenbits; "ctl"∷ty_xlenbits;
   "h0"∷clem_cell_ty 1; "h1"∷clem_cell_ty 1; "h2"∷clem_cell_ty 1; "h3"∷clem_cell_ty 1;
   "sl"∷clemv_ty 1; "dl"∷clemv_ty 1].

Definition ccf_pre (ts td : string) : Assertion (ccfCtx ▻ "a"∷ty_xlenbits) :=
  let hs := hl4 (term_var "h0") (term_var "h1") (term_var "h2") (term_var "h3") in
  ( X1 ↦ᵣ term_var "r"
    ∗ A2 ↦ᵣ term_var "s" ∗ secLeakvar "s"
    ∗ A1 ↦ᵣ term_var "d" ∗ secLeakvar "d"
    ∗ A3 ↦ᵣ term_var "n" ∗ secLeakvar "n"
    ∗ A0 ↦ᵣ term_var "ctl"
    ∗ asn.formula (formula_propeq (term_var "n") (clem_off (term_var "nl") 4))
    ∗ secLeakvar "nl" ∗ clem_nonzero (term_var "nl")
    ∗ asn.formula (formula_relop bop.bvult (term_var "nl") (term_val ty_xlenbits (bv.of_N 0x80000000)))
    ∗ clem_arrv 1 1 ts (term_var "s") (term_var "n") (t_end (term_var "s") (term_var "n"))
        (cons_terms hs (term_var "sl"))
    ∗ clem_arrv 1 1 td (term_var "d") (term_var "n") (t_end (term_var "d") (term_var "n"))
        (cons_terms hs (term_var "dl")) )%asn.

(* the source unchanged; the destination with the SAME header bytes (so a
   caller keeps their publicness by framing), limbs unnamed *)
Definition ccf_post (ts td : string) : Assertion (ccfCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( X1 ↦ᵣ term_var "r"
    ∗ clem_arrv 1 1 ts (term_var "s") (term_var "n") (t_end (term_var "s") (term_var "n"))
        (cons_terms (hl4 (term_var "h0") (term_var "h1") (term_var "h2") (term_var "h3")) (term_var "sl"))
    ∗ asn.exist "dl'" (clemv_ty 1)
        (clem_arrv 1 1 td (term_var "d") (term_var "n") (t_end (term_var "d") (term_var "n"))
           (cons_terms (hl4 (term_var "h0") (term_var "h1") (term_var "h2") (term_var "h3"))
              (term_var "dl'")))
    ∗ asn.exist "w0" ty_xlenbits (A0 ↦ᵣ term_var "w0")
    ∗ asn.exist "w1" ty_xlenbits (A1 ↦ᵣ term_var "w1")
    ∗ asn.exist "w2" ty_xlenbits (A2 ↦ᵣ term_var "w2")
    ∗ asn.exist "w3" ty_xlenbits (A3 ↦ᵣ term_var "w3")
    ∗ asn.exist "w4" ty_xlenbits (A4 ↦ᵣ term_var "w4")
    ∗ asn.exist "w5" ty_xlenbits (A5 ↦ᵣ term_var "w5")
    ∗ asn.exist "w6" ty_xlenbits (A6 ↦ᵣ term_var "w6") )%asn.

Definition ccf_regs : list reg_spec_rel := [ (A4, Secret); (A5, Secret); (A6, Secret) ].

Definition ccfRec (ts td : string) : @CFGVerifierContract ccfCtx :=
  gen_seg_contract_at (term_var "q") (term_var "q") (term_var "r")
    ccopy_instrs 12 ccf_regs (secLeakvar "r" ∗ ccf_pre ts td)%asn (ccf_post ts td).
Definition ccfBlk (ts td : string) : BlkAnnot := {| blk_ctx := ccfCtx ; blk_contract := ccfRec ts td |}.

Definition cl (k : CLem) : Annot := AnnotCLemma k.

(* Entry, after the `add a3` (the beqz's taken path is refuted: n = nl + 4,
   nl < 2^31): seed both DONE arrays at their array's start.  Exit, before
   the ret: the source joins back; the destination's emptied remainder goes;
   then, header byte by header byte, the destination's head (syntactically
   clem_mux_byte h_k M) is re-synchronised against the source's head (h_k)
   and both heads come off by pattern; the cells go back at the end. *)
Definition ccf_seeds (ts td : string) : list Annot :=
  [ cl (clem_arrv_empty_at 1 1 ts cc_sd); cl (clem_arrv_empty_at 1 1 td td) ].
Definition ccf_glue (resync : bool) (ts td : string) : list Annot :=
  let rs := if resync then [cl (clem_arrv_resync_head td ts)] else nil in
  let next := [cl (clem_arrv_take_cons 1 1 td); cl (clem_arrv_take_cons 1 1 ts)] in
  [ cl (clem_arrv_join 1 1 cc_sd ts ts); cl (clem_arrv_empty_elim 1 1 td) ]
  ++ rs ++ next ++ rs ++ next ++ rs ++ next ++ rs
  ++ [ cl (clem_arrv_add_first 1 1 ts); cl (clem_arrv_add_first 1 1 ts); cl (clem_arrv_add_first 1 1 ts)
     ; cl (clem_arrv_add_first 1 1 td); cl (clem_arrv_add_first 1 1 td); cl (clem_arrv_add_first 1 1 td) ].

Definition ccf_annot_g (resync : bool) (ts td : string) : list AnnotInstr :=
  List.map (fun '(i, ins) =>
              {| ai_ghost_before := if Nat.eqb i 13 then ccf_glue resync ts td else nil
               ; ai_instr := ins
               ; ai_ghost_after := if Nat.eqb i 2 then ccf_seeds ts td else nil
               ; ai_block := if Nat.eqb i 3 then Some (cclBlk ts td) else None |})
    (List.combine (List.seq 0 (length ccopy_instrs)) ccopy_instrs).
Definition ccf_annot := ccf_annot_g true.

Lemma valid_ccf : cfg_vc_loop (ccfRec "vs" "dv") (ccf_annot "vs" "dv").
Proof. Time solve_cc_all. Qed.

(* NEGATIVE CONTROL: without the re-synchronisation the header written under
   the secret ctl is NOT the header -- the post is refused *)
Goal cfg_vc_loop (ccfRec "vs" "dv") (ccf_annot_g false "vs" "dv").
Proof. Fail solve_cc_all. Abort.
