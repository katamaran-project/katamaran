(* ========================================================================= *)
(* Example/CheckScalar/CheckScalarParam.v -- the WHOLE check_scalar at       *)
(* symbolic klen `l`, both loops as blocks (CheckScalarParamLoop1/2.v).      *)
(*                                                                           *)
(* Every path is live: klen > 32 returns early, klen = 0 skips both loops,  *)
(* klen <> 32 skips loop 2.  Both `ret`s jump to ra, pinned to the exit     *)
(* p + 144 (the caller's return address).  The data, through the generator: *)
(* P256_N's 32 bytes right after the code, then k (anchored at the variable *)
(* k) with its l bytes -- all private: the code never branches on them.     *)
(* ========================================================================= *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.CheckScalar.CheckScalarParamInstrs.
From Katamaran Require Import RiscvPmp.CFGVer.Example.CheckScalar.CheckScalarParamLoop1.
From Katamaran Require Import RiscvPmp.CFGVer.Example.CheckScalar.CheckScalarParamLoop2.

Definition csCtx : LCtx := ["p"∷ty_xlenbits; "l"∷ty_xlenbits; "k"∷ty_xlenbits].

Definition cs_regs : list reg_spec_rel :=
  [ (X1, Known (PVBaseOff 144))                 (* ra: the exit *)
  ; (A2, Secret); (A3, Secret); (A4, Secret)
  ; (A5, Secret); (A6, Secret); (A7, Secret) ].

Definition cs_data : list (data_spec (csCtx ▻ "a"∷ty_xlenbits)) :=
  [ DBytes false (term_val ty_xlenbits (bv.of_N 32))   (* P256_N *)
  ; DAt (term_var "k")
  ; DBytes false (term_var "l") ]%list.               (* k[0 .. l-1] *)

Definition cs_pre : Assertion (csCtx ▻ "a"∷ty_xlenbits) :=
  ( A0 ↦ᵣ term_var "k" ∗ secLeakvar "k"
    ∗ A1 ↦ᵣ term_var "l" ∗ secLeakvar "l"
    ∗ gen_data_at (t_add (term_var "p") 144) cs_data )%asn.

Definition cs_post : Assertion (csCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  (asn.formula formula_true)%asn.

Definition cl (k : CLem) : Annot := AnnotCLemma k.
Definition cs_before (i : nat) : list Annot :=
  (* loop 1 is done: drop k's empty remainder, turn the done bytes back
     into k for loop 2 *)
  if Nat.eqb i 13 then [cl (clem_arr_drop false 1 1); cl (clem_arr_flip false 1 (-1))]
  else nil.
Definition cs_after (i : nat) : list Annot :=
  (* loop 1's done array, empty *)
  if Nat.eqb i 8 then [cl (clem_arr_empty false 1 (-1))] else nil.
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

Definition cs : @CFGVerifierContract csCtx :=
  gen_seg_contract (term_var "p") (term_var "p") cs_instrs 144 40 cs_regs cs_pre cs_post.
