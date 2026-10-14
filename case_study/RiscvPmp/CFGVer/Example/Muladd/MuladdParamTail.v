(* ========================================================================= *)
(* Example/Muladd/MuladdParamTail.v -- ZZMbTail.v with loops I, K, M on the n-only       *)
(* template MuladdParamLoopN.v (2026-09-30).  Was: ZZMbTail.v -- muladd from       *)
(* the mblr merge (idx 123, .LBB3_15) to the end, as ONE block contract that  *)
(* both mblr paths call.  Without the cut, symbolic execution carries this    *)
(* whole tail (G, I, K, M) once per path, and the whole-function VC does not  *)
(* fit in memory on a 14 GB machine.                                          *)
(*                                                                           *)
(* Binding order matters: every logic variable is bound DIRECTLY (a          *)
(* register's value, a precise chunk's output) before it occurs inside a     *)
(* compound term.  An angelic variable first met inside one (heap = v - 4)   *)
(* leaves the caller an equation postprocess cannot solve, i.e. an ∃ over    *)
(* the caller's whole continuation.                                           *)
(* ========================================================================= *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamInstrs.
From Katamaran Require RiscvPmp.CFGVer.Example.Muladd.MuladdParamLoopG
  RiscvPmp.CFGVer.Example.Muladd.MuladdParamLoopI RiscvPmp.CFGVer.Example.Muladd.MuladdParamLoopK
  RiscvPmp.CFGVer.Example.Muladd.MuladdParamLoopM.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamLoopN.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamClose.

Definition t_off {Σ} (t : Term Σ ty_xlenbits) (z : Z) : Term Σ ty_xlenbits :=
  term_binop bop.bvadd t (term_val ty_xlenbits (bv.of_Z z)).

Definition asn_in_range {Σ} (x : Term Σ ty_xlenbits) : Assertion Σ :=
  asn.formula (formula_relop bop.le
    (term_binop bop.plus (term_unop uop.unsigned x) (term_val ty.int 4%Z))
    (term_val ty.int (Z.of_N maxAddr))).

Definition asn_neq0 {Σ} (t : Term Σ ty_xlenbits) : Assertion Σ :=
  asn.formula (formula_relop bop.neq t (term_val ty_xlenbits bv.zero)).

Definition bvult_c {Σ} (lo : N) (t : Term Σ ty_xlenbits) : Assertion Σ :=
  asn.formula (formula_relop bop.bvult (term_val ty_xlenbits (bv.of_N lo)) t).

(* mlen as the code computes it: (31 + sext b) >> 5 *)
Definition t_mlen {Σ} (b : Term Σ ty_xlenbits) : Term Σ ty_xlenbits :=
  term_binop bop.shiftr
    (term_binop bop.bvadd (term_val ty_xlenbits (bv.of_N 31)) (term_unop uop.sext b))
    (term_val (ty.bvec 5) (bv.of_N 5)).

(* base + ((mlen + k) << 2) *)
Definition t_mlen_addr {Σ} (base b : Term Σ ty_xlenbits) (k : Z) : Term Σ ty_xlenbits :=
  term_binop bop.bvadd base
    (term_binop bop.shiftl
       (if Z.eqb k 0 then t_mlen b
        else term_binop bop.bvadd (term_val ty_xlenbits (bv.of_Z k)) (t_mlen b))
       (term_val (ty.bvec 5) (bv.of_N 2))).

Definition t_cnt {Σ} (k : Z) (b : Term Σ ty_xlenbits) : Term Σ ty_xlenbits :=
  term_binop bop.bvadd (term_val ty_xlenbits (bv.of_Z k)) (t_mlen b).

Definition k_mask31 : Val ty_xlenbits := bv.of_N 2147483647.

Definition tailCtx : LCtx :=
  ["q"∷ty_xlenbits; "x"∷ty_xlenbits; "m"∷ty_xlenbits; "sp"∷ty_xlenbits;
   "b"∷ty_xlenbits].

(* the registers the tail only needs to own (their values are dead, or
   carried as existentials); A0 A2 A3 A5 A6 X2 are stated in tail_pre *)
Definition tail_regs : list reg_spec_rel :=
  [ (A1, Secret); (A4, Secret); (A7, Secret)
  ; (T0, Public)                     (* m[mlen], G's public d *)
  ; (T1, Secret); (T2, Secret)
  ; (T3, Secret); (T4, Secret); (T5, Secret)
  ; (T6, Secret)
  ; (S0, Secret); (S1, Secret); (S2, Secret)
  ; (S3, Secret) ].

Definition tail_pre : Assertion (tailCtx ▻ "a"∷ty_xlenbits) :=
  ( A0 ↦ᵣ term_var "x" ∗ secLeakvar "x"
    ∗ A2 ↦ᵣ term_var "m" ∗ secLeakvar "m"
    ∗ X2 ↦ᵣ term_var "sp" ∗ secLeakvar "sp"
    (* x[0], the header; b is bound HERE *)
    ∗ term_var "x" ↦ₘ term_var "b" ∗ secLeakvar "b"
    ∗ asn_neq0 (term_unop uop.sext (term_var "b")) ∗ bvult_c 31 (term_unop uop.sext (term_var "b")) ∗ bvult_c 64 (term_unop uop.sext (term_var "b"))
    ∗ asn.formula (formula_relop bop.bvult (term_unop uop.sext (term_var "b")) (term_val ty_xlenbits (bv.of_N 65536)))
    ∗ A3 ↦ᵣ term_val ty_xlenbits k_mask31
    ∗ A5 ↦ᵣ term_binop bop.shiftl (t_mlen (term_var "b")) (term_val (ty.bvec 5) (bv.of_N 2))
    ∗ A6 ↦ᵣ term_binop bop.bvadd (term_val ty_xlenbits (bv.of_N 31)) (term_unop uop.sext (term_var "b"))
    (* x: x[1] (the new limb), the moved limbs x[2..mlen-2] as an array walking
       UP, and x[mlen-1], x[mlen] as cells.  Their address terms differ
       between the two mblr paths, so they are matched ANGELICALLY *)
    ∗ asn.exist "x1" ty_xlenbits
        (asn.chunk_angelic (chunk_user (ptstomem bytes_per_word) [t_off (term_var "x") 4; term_var "x1"]))
    ∗ asn.chunk_angelic (chunk_user (arr false 4 4)
        [t_off (term_var "x") 8; t_cnt (-3) (term_var "b"); t_mlen_addr (term_var "x") (term_var "b") (-1)])
    ∗ asn.exist "xu" ty_xlenbits
        (asn.chunk_angelic (chunk_user (ptstomem bytes_per_word) [t_mlen_addr (term_var "x") (term_var "b") (-1); term_var "xu"]))
    ∗ asn.exist "xt" ty_xlenbits
        (asn.chunk_angelic (chunk_user (ptstomem bytes_per_word) [t_mlen_addr (term_var "x") (term_var "b") 0; term_var "xt"]))
    (* m (public), as the caller has it: m[1..mlen-2] walking UP, two cells *)
    ∗ asn.chunk (chunk_user (arr true 4 4)
        [t_off (term_var "m") 4; t_cnt (-2) (term_var "b"); t_mlen_addr (term_var "m") (term_var "b") (-1)])
    ∗ asn.exist "mu" ty_xlenbits (t_mlen_addr (term_var "m") (term_var "b") (-1) ↦ₘ term_var "mu" ∗ secLeakvar "mu")
    ∗ asn.exist "mt" ty_xlenbits (t_mlen_addr (term_var "m") (term_var "b") 0 ↦ₘ term_var "mt" ∗ secLeakvar "mt")
    ∗ asn_in_range (term_var "x") ∗ asn_in_range (t_off (term_var "x") 4)
    ∗ asn_in_range (t_mlen_addr (term_var "x") (term_var "b") 0)
    ∗ asn_in_range (t_mlen_addr (term_var "x") (term_var "b") (-1))
    ∗ asn_in_range (t_mlen_addr (term_var "m") (term_var "b") 0)
    ∗ asn_in_range (t_mlen_addr (term_var "m") (term_var "b") (-1))
    (* the spill slots the epilogue reloads *)
    ∗ asn.exist "s3" ty_xlenbits (term_var "sp" ↦ₘ term_var "s3")
    ∗ asn.exist "s2" ty_xlenbits (t_off (term_var "sp") 4 ↦ₘ term_var "s2")
    ∗ asn.exist "s1" ty_xlenbits (t_off (term_var "sp") 8 ↦ₘ term_var "s1")
    ∗ asn.exist "s0" ty_xlenbits (t_off (term_var "sp") 12 ↦ₘ term_var "s0")
    ∗ asn_in_range (term_var "sp") ∗ asn_in_range (t_off (term_var "sp") 4)
    ∗ asn_in_range (t_off (term_var "sp") 8) ∗ asn_in_range (t_off (term_var "sp") 12) )%asn.

Definition tail_post : Assertion (tailCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  (asn.formula formula_true)%asn.

Definition cl (k : CLem) : Annot := AnnotCLemma k.

(* before I: x = x[1] ++ moved ++ x[mlen-1] ++ x[mlen], m = arr ++ m[mlen-1]
   ++ m[mlen], and I's two done seeds *)
Definition build_i : list Annot :=
  [ cl (clem_arr_add_first false 4 4)
  ; cl (clem_arr_add_last false 4 4); cl (clem_arr_add_last false 4 4)
  ; cl (clem_arr_add_last true 4 4); cl (clem_arr_add_last true 4 4)
  ; cl (clem_arr_empty true 4 (-4)); cl (clem_arr_empty false 4 (-4)) ].
(* after a loop: learn where the other pointer ended, drop the two empty
   remainders, turn the two done arrays around (the next loop's sources),
   and seed the next loop's done arrays *)
(* The n-only loop posts state BOTH pointers (end - 4c, c = 0), so the old
   clem_arr_lockstep step (learn where the other pointer ended) is gone. *)
Definition hand_over : list Annot :=
  [ cl (clem_arr_drop true 4 4); cl (clem_arr_drop false 4 4)
  ; cl (clem_arr_flip true 4 (-4)); cl (clem_arr_flip false 4 (-4))
  ; cl (clem_arr_empty true 4 (-4)); cl (clem_arr_empty false 4 (-4)) ].

(* local indices: program index - 123 *)
Definition tail_before (i : nat) : list Annot :=
  if Nat.eqb i 96 then hand_over          (* 219 *)
  else if Nat.eqb i 127 then hand_over    (* 250 *)
  else nil.
Definition tail_after (i : nat) : list Annot :=
  if Nat.eqb i 66 then build_i else nil.                                    (* 189 *)
Definition tail_block (i : nat) : option BlkAnnot :=
  if Nat.eqb i 12 then Some MuladdParamLoopG.gRecBlk            (* 135 *)
  else if Nat.eqb i 67 then Some (lnBlk MuladdParamLoopI.lnIN (@MuladdParamLoopI.k_scratch))    (* 190 *)
  else if Nat.eqb i 114 then Some (lnBlk MuladdParamLoopK.lnKN (@MuladdParamLoopK.k_scratch))   (* 237 *)
  else if Nat.eqb i 141 then Some (lnBlk MuladdParamLoopM.lnMT (@MuladdParamLoopM.k_scratch))   (* 264 *)
  else None.

Definition tail_instrs : list AST := List.skipn 123 mb_instrs.
Lemma tail_len : length tail_instrs = 159.
Proof. reflexivity. Qed.

Definition tail_annot : list AnnotInstr :=
  List.map (fun '(i, ins) =>
              {| ai_ghost_before := tail_before i; ai_instr := ins
               ; ai_ghost_after := tail_after i
               ; ai_block := tail_block i |})
    (List.combine (List.seq 0 (length tail_instrs)) tail_instrs).

Definition tailRec : @CFGVerifierContract tailCtx :=
  gen_seg_contract (term_var "q") (term_var "q") tail_instrs 636 250 tail_regs
    tail_pre tail_post.
Definition tailBlk : BlkAnnot := {| blk_ctx := tailCtx ; blk_contract := tailRec |}.
