(* ========================================================================= *)
(* Example/CheckScalar/CheckScalarParam.v -- the WHOLE check_scalar at       *)
(* symbolic klen `l`, both loops as blocks (CheckScalarParamLoop1/2.v).      *)
(*                                                                           *)
(* Every path is live: klen > 32 returns early, klen = 0 skips both loops,  *)
(* klen <> 32 skips loop 2.  Both `ret`s jump to ra, pinned to the exit     *)
(* p + 144 (the caller's return address).  The data, through the generator: *)
(* P256_N's 32 bytes right after the code, then k (anchored at the variable *)
(* k) with its l bytes -- all private: the code never branches on them.     *)
(* Their values vN, vK are contract variables only because the data spec    *)
(* names them (PLAN-arrv D12); nothing mentions them.                       *)
(* ========================================================================= *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.CheckScalar.CheckScalarParamInstrs.
From Katamaran Require Import RiscvPmp.CFGVer.Example.CheckScalar.CheckScalarParamLoop1.
From Katamaran Require Import RiscvPmp.CFGVer.Example.CheckScalar.CheckScalarParamLoop2.

Definition csCtx : LCtx := ["p"∷ty_xlenbits; "l"∷ty_xlenbits; "k"∷ty_xlenbits].

(* A0 = k, A1 = klen (public), ra = the exit p + 144, the rest scratch *)
Definition cs_regs : list (reg_spec_q csCtx) :=
  [ (A0, Known (PVVar "k")); (A1, Known (PVVar "l")); (X1, Known (PVOff "p" 144))
  ; (A2, Secret); (A3, Secret); (A4, Secret)
  ; (A5, Secret); (A6, Secret); (A7, Secret) ].

Definition cs_data : list (data_spec csCtx) :=
  [ DBytes false (term_val ty_xlenbits (bv.of_N 32)) "vN"   (* P256_N *)
  ; DAt (term_var "k")
  ; DBytes false (term_var "l") "vK" ]%list.                (* k[0 .. l-1] *)

(* the contract's context: csCtx and the arrays' values *)
Definition csCtxV : LCtx := csCtx ▻▻ data_vctx cs_data.

Definition cl (k : CLem) : Annot := AnnotCLemma k.
Definition cs_before (i : nat) : list Annot :=
  (* loop 1 is done: drop k's empty remainder, turn the done bytes back
     into k for loop 2 *)
  if Nat.eqb i 13 then [cl (clem_arrv_drop 1 1); cl (clem_arrv_flip 1 (-1))]
  else nil.
Definition cs_after (i : nat) : list Annot :=
  (* loop 1's done array, empty *)
  if Nat.eqb i 8 then [cl (clem_arrv_empty 1 (-1))] else nil.
Definition cs_block (i : nat) : option BlkAnnot :=
  if Nat.eqb i 9 then Some l1Blk
  else if Nat.eqb i 20 then Some l2Blk
  else None.

Definition cs_annot : list AnnotInstr :=
  List.map (fun '(i, ins) =>
              {| ai_ghost_before := cs_before i; ai_instr := ins
               ; ai_ghost_after := cs_after i
               ; ai_block := cs_block i |})
    (List.combine (List.seq 0 (length cs_instrs)) cs_instrs).

Lemma cs_len : length cs_instrs = 36.
Proof. reflexivity. Qed.

(* the generator form (PLAN-arrv Phase D, Emiel 2026-10-25): k's bytes right
   after P256_N via DAt, so the end theorem is one gen_prog_noninterferent;
   CheckScalarPtr.v is the same contract with DPtr *)
Definition cs : @CFGVerifierContract csCtxV :=
  gen_prog_contract "p" _ cs_regs (asn.formula formula_true) 144 cs_data cs_instrs 40
    (asn.formula formula_true).
