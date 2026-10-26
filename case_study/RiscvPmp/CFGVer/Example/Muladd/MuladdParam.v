(* ========================================================================= *)
(* Example/Muladd/MuladdParam.v -- ZZMbSym6N.v with its data THROUGH THE GENERATOR      *)
(* (GenSegment.gen_data_at, 2026-10-02).                                     *)
(* The WHOLE function at symbolic mlen, cut at the mblr merge: both mblr      *)
(* paths (D at 84, D0 at 113) run to idx 123, where ONE block (ZZMbTail, the  *)
(* rest of the function with G/I/K/M inside) stands in for the tail, so the  *)
(* tail is verified once instead of once per path.                            *)
(* m[0] = x[0] = b symbolic public; mlen >= 3.  A gen_prog_contract (PLAN-  *)
(* arrv Phase D, as CheckScalarParam): the end theorem is one               *)
(* gen_prog_noninterferent.  Arrays (arrv): m's limbs "vm", x's "vx" (their *)
(* value names, D15); loop D's moved array "Dx".                            *)
(* ========================================================================= *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamInstrs.
From Katamaran Require RiscvPmp.CFGVer.Example.Muladd.MuladdParamLoopD
  RiscvPmp.CFGVer.Example.Muladd.MuladdParamLoopDAng RiscvPmp.CFGVer.Example.Muladd.MuladdParamLoopD0
  RiscvPmp.CFGVer.Example.Muladd.MuladdParamTail.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamClose.

Definition t_off {Σ} (t : Term Σ ty_xlenbits) (z : Z) : Term Σ ty_xlenbits :=
  term_binop bop.bvadd t (term_val ty_xlenbits (bv.of_Z z)).

Definition asn_in_range {Σ} (x : Term Σ ty_xlenbits) : Assertion Σ :=
  asn.formula (formula_relop bop.le
    (term_binop bop.plus (term_unop uop.unsigned x) (term_val ty.int 4%Z))
    (term_val ty.int (Z.of_N maxAddr))).

Definition asn_neq0 {Σ} (t : Term Σ ty_xlenbits) : Assertion Σ :=
  asn.formula (formula_relop bop.neq t (term_val ty_xlenbits bv.zero)).

(* mlen as the code computes it: (31 + sext b) >> 5 *)
Definition t_mlen {Σ} (b : Term Σ ty_xlenbits) : Term Σ ty_xlenbits :=
  term_binop bop.shiftr
    (term_binop bop.bvadd (term_val ty_xlenbits (bv.of_N 31)) (term_unop uop.sext b))
    (term_val (ty.bvec 5) (bv.of_N 5)).

(* base + ((mlen + k) << 2), the constant on the LEFT of the add *)
Definition t_mlen_addr {Σ} (base b : Term Σ ty_xlenbits) (k : Z) : Term Σ ty_xlenbits :=
  term_binop bop.bvadd base
    (term_binop bop.shiftl
       (if Z.eqb k 0 then t_mlen b
        else term_binop bop.bvadd (term_val ty_xlenbits (bv.of_Z k)) (t_mlen b))
       (term_val (ty.bvec 5) (bv.of_N 2))).

Definition symCtx : LCtx := ["p"∷ty_xlenbits; "b"∷ty_xlenbits; "x"∷ty_xlenbits].

(* A0 = &x[0], A2 = &m[0] = sp = p + 1144, the rest scratch *)
Definition sym_regs : list (reg_spec_q symCtx) :=
  [ (A0, Known (PVVar "x"))
  ; (A1, Secret)
  ; (A2, Known (PVOff "p" 1144))
  ; (X2, Known (PVOff "p" 1144))
  ; (A3, Secret); (A4, Secret); (A5, Secret)
  ; (A6, Secret); (A7, Secret)
  ; (T0, Secret); (T1, Secret); (T2, Secret)
  ; (T3, Secret); (T4, Secret); (T5, Secret)
  ; (T6, Secret)
  ; (S0, Secret); (S1, Secret); (S2, Secret)
  ; (S3, Secret) ].

Definition bvult_c {Σ} (lo : N) (t : Term Σ ty_xlenbits) : Assertion Σ :=
  asn.formula (formula_relop bop.bvult (term_val ty_xlenbits (bv.of_N lo)) t).

(* M - 2, the arrays' count, as the code's own term *)
Definition t_mm2 {Σ} (b : Term Σ ty_xlenbits) : Term Σ ty_xlenbits :=
  term_binop bop.bvadd (term_val ty_xlenbits (bv.of_Z (-2))) (t_mlen b).

(* THE DATA, through the generator (GenSegment.gen_data_at), contiguous from
   the end of the code (p + 1128): the 4 spill slots; m = sp = p + 1144 with
   its header b, the public limbs m[1..M-2] as an array walking up and
   m[M-1], m[M] as cells; then x (anchored at the variable x) with its header
   b, the private limbs x[1..M-2] as an array walking down and x[M-1], x[M]. *)
Definition sym_data : list (data_spec symCtx) :=
  [ DCell Secret; DCell Secret; DCell Secret; DCell Secret
  ; DCell (Known (term_var "b"))
  ; DArr true ArrUp (t_mm2 (term_var "b")) "vm"
  ; DCell Public; DCell Public
  ; DAt (term_var "x")
  ; DCell (Known (term_var "b"))
  ; DArr false ArrDown (t_mm2 (term_var "b")) "vx"
  ; DCell Secret; DCell Secret ]%list.

(* the contract's context: symCtx and the arrays' values *)
Definition symCtxV : LCtx := symCtx ▻▻ data_vctx sym_data.

(* the pure facts: b public, the code's own branch conditions, the family's
   bounds, and the data's end (p + 1148 + ...) clear of the address space's
   end at the base *)
Definition sym_facts : Assertion (symCtx ▻ "a"∷ty_xlenbits) :=
  ( secLeakvar "b"
    ∗ asn_neq0 (term_unop uop.sext (term_var "b")) ∗ bvult_c 31 (term_unop uop.sext (term_var "b")) ∗ bvult_c 64 (term_unop uop.sext (term_var "b"))
    ∗ asn.formula (formula_relop bop.bvult (term_unop uop.sext (term_var "b")) (term_val ty_xlenbits (bv.of_N 65536)))
    ∗ asn_neq0 (term_binop bop.bvand
        (term_binop bop.bvadd (term_val ty_xlenbits (bv.of_Z (-1))) (t_mlen (term_var "b")))
        (term_val ty_xlenbits (bv.of_N 0x3fffffff)))
    ∗ asn_neq0 (term_binop bop.bvand
        (term_binop bop.bvadd (term_val ty_xlenbits (bv.of_N 0x3fffffff)) (t_mlen (term_var "b")))
        (term_val ty_xlenbits (bv.of_N 0x3fffffff)))
    ∗ gen_base_bound (term_var "p") 1148 )%asn.

Definition cl (k : CLem) : Annot := AnnotCLemma k.
Definition take_top : list Annot :=
  [ cl (clem_arrv_nonempty 4 4 "Dx"); cl (clem_arrv_take_last 4 4 "Dx") ].
Definition sym6_before (i : nat) : list Annot :=
  if Nat.eqb i 90 then [cl (clem_arrv_empty_elim 4 (-4) "vx")]
  else if Nat.eqb i 91 then take_top
  else if Nat.eqb i 92 then take_top
  (* the mblr = 0 path reads only x[M]; take x[M-1] too, so both paths
     reach the merge with the same heap shape *)
  else if Nat.eqb i 119 then List.app take_top take_top
  else nil.
Definition sym6_after (i : nat) : list Annot :=
  if Nat.eqb i 83 then [cl (clem_arrv_add_first 4 (-4) "vx"); cl (clem_arrv_empty 4 4 "Dx")]
  else if Nat.eqb i 112 then [cl (clem_arrv_add_first 4 (-4) "vx"); cl (clem_arrv_empty 4 4 "Dx")]
  else nil.
Definition sym6_block (i : nat) : option BlkAnnot :=
  if Nat.eqb i 84 then Some MuladdParamLoopDAng.dAngBlk
  else if Nat.eqb i 113 then Some MuladdParamLoopD0.d0Blk
  else if Nat.eqb i 123 then Some MuladdParamTail.tailBlk
  else None.

Definition sym6_instrs : list AST := mb_instrs.
Definition sym6_annot : list AnnotInstr :=
  List.map (fun '(i, ins) =>
              {| ai_ghost_before := sym6_before i; ai_instr := ins
               ; ai_ghost_after := sym6_after i
               ; ai_block := sym6_block i |})
    (List.combine (List.seq 0 (length sym6_instrs)) sym6_instrs).

Lemma sym6_len : length sym6_instrs = 282.
Proof. reflexivity. Qed.

Definition sym6 : @CFGVerifierContract symCtxV :=
  gen_prog_contract "p" _ sym_regs sym_facts 1128 sym_data sym6_instrs 250
    (asn.formula formula_true).

