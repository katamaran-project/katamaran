(* ========================================================================= *)
(* Example/Muladd/MuladdParam.v -- ZZMbSym6N.v with its data THROUGH THE GENERATOR      *)
(* (GenSegment.gen_data_at, 2026-10-02).                                     *)
(* The WHOLE function at symbolic mlen, cut at the mblr merge: both mblr      *)
(* paths (D at 84, D0 at 113) run to idx 123, where ONE block (ZZMbTail, the  *)
(* rest of the function with G/I/K/M inside) stands in for the tail, so the  *)
(* tail is verified once instead of once per path.                            *)
(* m[0] = x[0] = b symbolic public; mlen >= 3.                               *)
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

Definition sym_regs : list reg_spec_rel :=
  [ (A1, false, PVExist)
  ; (A2, true,  PVBaseOff 1144)
  ; (X2, true,  PVBaseOff 1144)
  ; (A3, false, PVExist); (A4, false, PVExist); (A5, false, PVExist)
  ; (A6, false, PVExist); (A7, false, PVExist)
  ; (T0, false, PVExist); (T1, false, PVExist); (T2, false, PVExist)
  ; (T3, false, PVExist); (T4, false, PVExist); (T5, false, PVExist)
  ; (T6, false, PVExist)
  ; (S0, false, PVExist); (S1, false, PVExist); (S2, false, PVExist)
  ; (S3, false, PVExist) ].

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
Definition sym_data : list (data_spec (symCtx ▻ "a"∷ty_xlenbits)) :=
  [ DCell false None; DCell false None; DCell false None; DCell false None
  ; DCell true (Some (term_var "b"))
  ; DArr true ArrUp (t_mm2 (term_var "b"))
  ; DCell true None; DCell true None
  ; DAt (term_var "x")
  ; DCell true (Some (term_var "b"))
  ; DArr false ArrDown (t_mm2 (term_var "b"))
  ; DCell false None; DCell false None ]%list.

Definition sym_pre : Assertion (symCtx ▻ "a"∷ty_xlenbits) :=
  ( A0 ↦ᵣ term_var "x" ∗ secLeakvar "x" ∗ secLeakvar "b"
    (* the code's own branch conditions, and the family's bounds *)
    ∗ asn_neq0 (term_unop uop.sext (term_var "b")) ∗ bvult_c 31 (term_unop uop.sext (term_var "b")) ∗ bvult_c 64 (term_unop uop.sext (term_var "b"))
    ∗ asn.formula (formula_relop bop.bvult (term_unop uop.sext (term_var "b")) (term_val ty_xlenbits (bv.of_N 65536)))
    ∗ asn_neq0 (term_binop bop.bvand
        (term_binop bop.bvadd (term_val ty_xlenbits (bv.of_Z (-1))) (t_mlen (term_var "b")))
        (term_val ty_xlenbits (bv.of_N 0x3fffffff)))
    ∗ asn_neq0 (term_binop bop.bvand
        (term_binop bop.bvadd (term_val ty_xlenbits (bv.of_N 0x3fffffff)) (t_mlen (term_var "b")))
        (term_val ty_xlenbits (bv.of_N 0x3fffffff)))
    ∗ gen_data_at (t_off (term_var "p") 1128) sym_data
    ∗ gen_base_bound (term_var "p") 1148 )%asn.

Definition sym_post : Assertion (symCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  (asn.formula formula_true)%asn.

Definition cl (k : CLem) : Annot := AnnotCLemma k.
Definition take_top : list Annot :=
  [ cl (clem_arr_nonempty false 4 4); cl (clem_arr_take_last false 4 4) ].
Definition sym6_before (i : nat) : list Annot :=
  if Nat.eqb i 90 then [cl (clem_arr_empty_elim false 4 (-4))]
  else if Nat.eqb i 91 then take_top
  else if Nat.eqb i 92 then take_top
  (* the mblr = 0 path reads only x[M]; take x[M-1] too, so both paths
     reach the merge with the same heap shape *)
  else if Nat.eqb i 119 then List.app take_top take_top
  else nil.
Definition sym6_after (i : nat) : list Annot :=
  if Nat.eqb i 83 then [cl (clem_arr_add_first false 4 (-4)); cl (clem_arr_empty false 4 4)]
  else if Nat.eqb i 112 then [cl (clem_arr_add_first false 4 (-4)); cl (clem_arr_empty false 4 4)]
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
               ; ai_block := sym6_block i; ai_loop := None |})
    (List.combine (List.seq 0 (length sym6_instrs)) sym6_instrs).

Lemma sym6_len : length sym6_instrs = 282.
Proof. reflexivity. Qed.

Definition sym6 : @CFGVerifierContract symCtx :=
  gen_seg_contract (term_var "p") (term_var "p") sym6_instrs 1128 250 sym_regs
    sym_pre sym_post.

