(* ZZ probe (not built by the project): matched baseline + one-factor
   ablation for the RsaSpikeSub VC cost regression of PLAN-arrv Gate C. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamClose.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Rsa.RsaSpikeSub.

(* OLD: arr, as committed at HEAD *)
Module Old.
Definition lnCtx : LCtx :=
  ["q"∷ty_xlenbits; "eM"∷ty_xlenbits; "eX"∷ty_xlenbits;
   "mE"∷ty_xlenbits; "xE"∷ty_xlenbits; "T"∷ty_xlenbits].

(* end - 4 * cnt + off *)
Definition ln_back {Σ} (end_ cnt : Term Σ ty_xlenbits) (off : Z) : Term Σ ty_xlenbits :=
  term_binop bop.bvadd end_
    (term_binop bop.bvadd
       (term_binop bop.bvmul (term_val ty_xlenbits (bv.of_Z (-4))) cnt)
       (term_val ty_xlenbits (bv.of_Z off))).

Definition ln_arr {Σ} (pub : bool) (w : nat) (s : Z) (a n e : Term Σ ty_xlenbits) : Assertion Σ :=
  asn.chunk (chunk_user (arr pub w s) [a; n; e]).
Definition ln_arr_ang {Σ} (pub : bool) (w : nat) (s : Z) (a n e : Term Σ ty_xlenbits) : Assertion Σ :=
  asn.chunk_angelic (chunk_user (arr pub w s) [a; n; e]).

Record LoopN := MkLoopN
  { ln_rx      : RegIdx          (* x pointer register *)
  ; ln_rm      : RegIdx          (* m pointer register *)
  ; ln_rlatch  : RegIdx          (* holds the latch array's end *)
  ; ln_latch_x : bool            (* the latch array is x (else m) *)
  ; ln_instrs  : list AST
  ; ln_store   : nat             (* index of the store (add_first after it) *)
  ; ln_exit    : N               (* exit offset *)
  ; ln_fuel    : nat
  }.

Section Template.
  Context (L : LoopN) (scratch : forall {Σ}, Assertion Σ).

  Definition ln_latch_end {Σ} (eM eX : Term Σ ty_xlenbits) : Term Σ ty_xlenbits :=
    if ln_latch_x L then eX else eM.

  (* the loop's state, `cnt` elements still to go *)
  Definition ln_state {Σ} (cnt : Term Σ ty_xlenbits) (done : Term Σ ty_xlenbits)
      (eM eX mE xE : Term Σ ty_xlenbits) (latch : Term Σ ty_xlenbits) : Assertion Σ :=
    ( ln_arr_ang true 4 4 (ln_back eM cnt 0) cnt eM
      ∗ ln_arr_ang false 4 4 (ln_back eX cnt 0) cnt eX
      ∗ ln_arr_ang true 4 (-4) (ln_back eM cnt (-4)) done mE
      ∗ ln_arr_ang false 4 (-4) (ln_back eX cnt (-4)) done xE
      ∗ ln_rx L ↦ᵣ ln_back eX cnt 0
      ∗ ln_rm L ↦ᵣ ln_back eM cnt 0
      ∗ ln_rlatch L ↦ᵣ latch )%asn.

  Definition ln_inv : Assertion (lnCtx ▻ "a"∷ty_xlenbits) :=
    ( asn.exist "n" ty_xlenbits (asn.exist "k" ty_xlenbits (
      ln_state (term_var "n") (term_var "k") (term_var "eM") (term_var "eX")
        (term_var "mE") (term_var "xE") (ln_latch_end (term_var "eM") (term_var "eX"))
      ∗ secLeakvar "eM" ∗ secLeakvar "eX"
      (* the count is public: stated here, the reverted chunk-facts hook
         (PLAN-chunk-facts.md) used to assume it from the arr chunk *)
      ∗ secLeakvar "n" ∗ secLeakvar "k"
      ∗ asn.formula (formula_relop bop.neq (term_var "n") (term_val ty_xlenbits bv.zero))
      ∗ asn.formula (formula_relop bop.bvult (term_var "n")
          (term_val ty_xlenbits (bv.of_N 0x40000000)))
      (* the done count k, and the total k + n the post hands back as the next
         loop's count: both summands below 2^30, so k + n cannot wrap and is
         nonzero; its own bound is the next loop's n <u 2^30 *)
      ∗ asn.formula (formula_relop bop.bvult (term_var "k")
          (term_val ty_xlenbits (bv.of_N 0x40000000)))
      ∗ asn.formula (formula_relop bop.bvult
          (term_binop bop.bvadd (term_var "k") (term_var "n"))
          (term_val ty_xlenbits (bv.of_N 0x40000000)))
      ∗ asn.formula (formula_propeq (term_var "T")
          (term_binop bop.bvadd (term_var "k") (term_var "n")))
      ∗ scratch _ )))%asn.

  Definition ln_post : Assertion (lnCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
    ( asn.exist "c" ty_xlenbits
        ( (* the done count exactly: the total T.  Was a fresh ∃ c1: the next
             loop, taking the done array as its source, then had a count
             nothing constrained *)
          ln_state (term_var "c") (term_var "T")
            (term_var "eM") (term_var "eX")
            (term_var "mE") (term_var "xE") (ln_latch_end (term_var "eM") (term_var "eX"))
          ∗ asn.formula (formula_propeq (term_var "c") (term_val ty_xlenbits bv.zero))
          ∗ scratch _ ))%asn.

  Definition lnRec : @CFGVerifierContract lnCtx :=
    gen_seg_contract (term_var "q") (term_var "q") (ln_instrs L) (ln_exit L) (ln_fuel L) []
      ln_inv ln_post.
  Definition lnBlk : BlkAnnot := {| blk_ctx := lnCtx ; blk_contract := lnRec |}.

  Fixpoint ln_annot_go (i : nat) (l : list AST) : list AnnotInstr :=
    match l with
    | nil => nil
    | cons x r =>
        cons
          (if Nat.eqb i 0 then
             {| ai_ghost_before := [ AnnotCLemma (clem_arr_take_first false 4 4)
                                   ; AnnotCLemma (clem_arr_take_first true 4 4) ]
              ; ai_instr := x ; ai_ghost_after := []
              ; ai_block := None |}
           else if Nat.eqb i (ln_store L) then
             {| ai_ghost_before := [] ; ai_instr := x
              ; ai_ghost_after := [ AnnotCLemma (clem_arr_add_first false 4 (-4))
                                  ; AnnotCLemma (clem_arr_add_first true 4 (-4)) ]
              ; ai_block := None |}
           else AST_AnnotInstr x)
          (ln_annot_go (S i) r)
    end.
  Definition ln_annot : list AnnotInstr := ln_annot_go 0 (ln_instrs L).
End Template.

Definition lnSub : LoopN := MkLoopN A0 A4 A1 false sub_loop_instrs 10 56 20.

Lemma o_valid_sub_loop : cfg_vc_loop (lnRec lnSub (@sub_scratch)) (ln_annot lnSub).
Proof. Time solve_mb_vc. Qed.

(* ------------------------------------------------------------------------ *)
(* 2. br_i31_sub, ITS EXIT THE RETURN ADDRESS                              *)
(* ------------------------------------------------------------------------ *)

(* q: the function's code base; r: the return address (X1 on entry); xa, xb:
   the two array arguments (A0, A1); h: a[0], the header, public. *)
Definition subCtx : LCtx :=
  ["q"∷ty_xlenbits; "r"∷ty_xlenbits; "xa"∷ty_xlenbits; "xb"∷ty_xlenbits;
   "h"∷ty_xlenbits].

(* the word count the code computes: m = (h + 63) >> 5, so m - 1 limbs.
   `sext h`: the term `lw` produced before peval_sext (2026-10-22) dropped
   that same-width sign extension; kept, since the solver normalizes both
   spellings and the VCs are unchanged -- muladd's t_mlen likewise *)
(* a's header and limbs (private), b's limbs (public: LoopN fixes m public;
   a secret m is Phase 3), at the arguments' addresses *)
Definition sub_mem {Σ} (xa xb h : Term Σ ty_xlenbits) : Assertion Σ :=
  ( xa ↦ₘ h
    ∗ asn.chunk (chunk_user (arr false 4 4) [t_off4 xa; t_limbs h; t_end xa h])
    ∗ asn.chunk (chunk_user (arr true 4 4) [t_off4 xb; t_limbs h; t_end xb h]) )%asn.

Definition sub_regs : list reg_spec_rel :=
  [ (A2, Secret); (A3, Secret); (A4, Secret); (A5, Secret); (A6, Secret); (A7, Secret) ].

Definition sub_pre : Assertion (subCtx ▻ "a"∷ty_xlenbits) :=
  ( X1 ↦ᵣ term_var "r"
    ∗ A0 ↦ᵣ term_var "xa" ∗ secLeakvar "xa"
    ∗ A1 ↦ᵣ term_var "xb" ∗ secLeakvar "xb"
    ∗ sub_mem (term_var "xa") (term_var "xb") (term_var "h") ∗ secLeakvar "h"
    (* 0 < h < 2^16: at least one limb, and nothing wraps *)
    ∗ asn.formula (formula_relop bop.bvult (term_val ty_xlenbits bv.zero) (term_var "h"))
    ∗ asn.formula (formula_relop bop.bvult (term_var "h") (term_val ty_xlenbits (bv.of_N 65536)))
    ∗ asn.formula (formula_relop bop.le
        (term_binop bop.plus (term_unop uop.unsigned (term_var "xa")) (term_val ty.int 4%Z))
        (term_val ty.int (Z.of_N maxAddr))) )%asn.

(* the same memory back, X1 unchanged; A0 (the borrow) and the scratch are
   handed back with any value *)
Definition sub_post : Assertion (subCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( X1 ↦ᵣ term_var "r"
    ∗ sub_mem (term_var "xa") (term_var "xb") (term_var "h")
    ∗ asn.exist "w0" ty_xlenbits (A0 ↦ᵣ term_var "w0")
    ∗ asn.exist "w1" ty_xlenbits (A1 ↦ᵣ term_var "w1")
    ∗ asn.exist "w2" ty_xlenbits (A2 ↦ᵣ term_var "w2")
    ∗ asn.exist "w3" ty_xlenbits (A3 ↦ᵣ term_var "w3")
    ∗ asn.exist "w4" ty_xlenbits (A4 ↦ᵣ term_var "w4")
    ∗ asn.exist "w5" ty_xlenbits (A5 ↦ᵣ term_var "w5")
    ∗ asn.exist "w6" ty_xlenbits (A6 ↦ᵣ term_var "w6")
    ∗ asn.exist "w7" ty_xlenbits (A7 ↦ᵣ term_var "w7") )%asn.

(* The same generator as every loop and segment; only the exit differs: the
   term `r`, not an offset.  `secLeak r` comes first in the precondition --
   the return address is control flow, and it is what makes the exit a
   SyncVal (GenCompose.seg_exit_sync_pub). *)
Definition subRec : @CFGVerifierContract subCtx :=
  gen_seg_contract_at (term_var "q") (term_var "q") (term_var "r")
    sub_instrs 30 sub_regs (secLeakvar "r" ∗ sub_pre)%asn sub_post.
Definition subBlk : BlkAnnot := {| blk_ctx := subCtx ; blk_contract := subRec |}.

Definition cl (k : CLem) : Annot := AnnotCLemma k.

(* before the loop: seed its two DONE arrays (empty, address bound by the
   loop's angelic entry); after it: drop the emptied sources and turn the
   done arrays back into forward arrays (muladd's hand_over, without the
   next loop's seeds) *)
Definition sub_seeds : list Annot :=
  [ cl (clem_arr_empty true 4 (-4)); cl (clem_arr_empty false 4 (-4)) ].
Definition sub_hand_back : list Annot :=
  [ cl (clem_arr_drop true 4 4); cl (clem_arr_drop false 4 4)
  ; cl (clem_arr_flip true 4 (-4)); cl (clem_arr_flip false 4 (-4)) ].

(* The seeds go AFTER instruction 10, not before 11: an instruction that
   carries a block runs the block INSTEAD of itself, ghosts included
   (Verifier.v, the `Some b` branch of the step) -- muladd's tail places its
   build_i the same way. *)
Definition sub_annot : list AnnotInstr :=
  List.map (fun '(i, ins) =>
              {| ai_ghost_before := if Nat.eqb i 25 then sub_hand_back else nil
               ; ai_instr := ins
               ; ai_ghost_after := if Nat.eqb i 10 then sub_seeds else nil
               ; ai_block := if Nat.eqb i 11 then Some (lnBlk lnSub (@sub_scratch))
                             else None |})
    (List.combine (List.seq 0 (length sub_instrs)) sub_instrs).

Lemma o_valid_sub : cfg_vc_loop subRec sub_annot.
Proof. Time solve_mb_vc. Qed.

End Old.

(* NV: the new arrv LoopN WITHOUT the VM equation (value tracking off) *)
Module NV.
Definition lnCtx : LCtx :=
  ["q"∷ty_xlenbits; "eM"∷ty_xlenbits; "eX"∷ty_xlenbits;
   "mE"∷ty_xlenbits; "xE"∷ty_xlenbits; "T"∷ty_xlenbits; "VM"∷clemv_ty 4].

(* end - 4 * cnt + off *)
Definition ln_back {Σ} (end_ cnt : Term Σ ty_xlenbits) (off : Z) : Term Σ ty_xlenbits :=
  term_binop bop.bvadd end_
    (term_binop bop.bvadd
       (term_binop bop.bvmul (term_val ty_xlenbits (bv.of_Z (-4))) cnt)
       (term_val ty_xlenbits (bv.of_Z off))).

(* m's value, as done and rest: rev dM ++ rM *)
Definition ln_mval {Σ} (dM rM : Term Σ (clemv_ty 4)) : Term Σ (clemv_ty 4) :=
  term_binop bop.append (term_unop uop.rev dM) rM.

Record LoopN := MkLoopN
  { ln_rx      : RegIdx          (* x pointer register *)
  ; ln_rm      : RegIdx          (* m pointer register *)
  ; ln_rlatch  : RegIdx          (* holds the latch array's end *)
  ; ln_latch_x : bool            (* the latch array is x (else m) *)
  ; ln_instrs  : list AST
  ; ln_store   : nat             (* index of the store (add_first after it) *)
  ; ln_exit    : N               (* exit offset *)
  ; ln_fuel    : nat
  }.

Section Template.
  Context (L : LoopN) (scratch : forall {Σ}, Assertion Σ).

  Definition ln_latch_end {Σ} (eM eX : Term Σ ty_xlenbits) : Term Σ ty_xlenbits :=
    if ln_latch_x L then eX else eM.

  (* the loop's state, `cnt` elements still to go; the arrays' values rM/rX
     (still to go) and dM/dX (done, most recent first) *)
  Definition ln_state {Σ} (cnt : Term Σ ty_xlenbits) (done : Term Σ ty_xlenbits)
      (eM eX mE xE : Term Σ ty_xlenbits) (latch : Term Σ ty_xlenbits)
      (rM rX dM dX : Term Σ (clemv_ty 4)) : Assertion Σ :=
    ( clem_arrv_angelic 4 4 (ln_back eM cnt 0) cnt eM rM
      ∗ clem_arrv_angelic 4 4 (ln_back eX cnt 0) cnt eX rX
      ∗ clem_arrv_angelic 4 (-4) (ln_back eM cnt (-4)) done mE dM
      ∗ clem_arrv_angelic 4 (-4) (ln_back eX cnt (-4)) done xE dX
      ∗ ln_rx L ↦ᵣ ln_back eX cnt 0
      ∗ ln_rm L ↦ᵣ ln_back eM cnt 0
      ∗ ln_rlatch L ↦ᵣ latch )%asn.

  Definition ln_inv : Assertion (lnCtx ▻ "a"∷ty_xlenbits) :=
    ( asn.exist "n" ty_xlenbits (asn.exist "k" ty_xlenbits (
      asn.exist "rM" (clemv_ty 4) (asn.exist "rX" (clemv_ty 4)
      (asn.exist "dM" (clemv_ty 4) (asn.exist "dX" (clemv_ty 4) (
      ln_state (term_var "n") (term_var "k") (term_var "eM") (term_var "eX")
        (term_var "mE") (term_var "xE") (ln_latch_end (term_var "eM") (term_var "eX"))
        (term_var "rM") (term_var "rX") (term_var "dM") (term_var "dX")
      ∗ secLeakvar "eM" ∗ secLeakvar "eX"
      (* the count is public: stated here, the reverted chunk-facts hook
         (PLAN-chunk-facts.md) used to assume it from the arr chunk *)
      ∗ secLeakvar "n" ∗ secLeakvar "k"
      ∗ asn.formula (formula_relop bop.neq (term_var "n") (term_val ty_xlenbits bv.zero))
      ∗ asn.formula (formula_relop bop.bvult (term_var "n")
          (term_val ty_xlenbits (bv.of_N 0x40000000)))
      (* the done count k, and the total k + n the post hands back as the next
         loop's count: both summands below 2^30, so k + n cannot wrap and is
         nonzero; its own bound is the next loop's n <u 2^30 *)
      ∗ asn.formula (formula_relop bop.bvult (term_var "k")
          (term_val ty_xlenbits (bv.of_N 0x40000000)))
      ∗ asn.formula (formula_relop bop.bvult
          (term_binop bop.bvadd (term_var "k") (term_var "n"))
          (term_val ty_xlenbits (bv.of_N 0x40000000)))
      ∗ asn.formula (formula_propeq (term_var "T")
          (term_binop bop.bvadd (term_var "k") (term_var "n")))
      ∗ scratch _ )))))))%asn.

  Definition ln_post : Assertion (lnCtx ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
    ( asn.exist "c" ty_xlenbits (
      asn.exist "rM" (clemv_ty 4) (asn.exist "rX" (clemv_ty 4)
      (asn.exist "dM" (clemv_ty 4) (asn.exist "dX" (clemv_ty 4)
        ( (* the done count exactly: the total T.  Was a fresh ∃ c1: the next
             loop, taking the done array as its source, then had a count
             nothing constrained *)
          ln_state (term_var "c") (term_var "T")
            (term_var "eM") (term_var "eX")
            (term_var "mE") (term_var "xE") (ln_latch_end (term_var "eM") (term_var "eX"))
            (term_var "rM") (term_var "rX") (term_var "dM") (term_var "dX")
              ∗ asn.formula (formula_propeq (term_var "c") (term_val ty_xlenbits bv.zero))
          ∗ scratch _ ))))))%asn.

  Definition lnRec : @CFGVerifierContract lnCtx :=
    gen_seg_contract (term_var "q") (term_var "q") (ln_instrs L) (ln_exit L) (ln_fuel L) []
      ln_inv ln_post.
  Definition lnBlk : BlkAnnot := {| blk_ctx := lnCtx ; blk_contract := lnRec |}.

  Fixpoint ln_annot_go (i : nat) (l : list AST) : list AnnotInstr :=
    match l with
    | nil => nil
    | cons x r =>
        cons
          (if Nat.eqb i 0 then
             {| ai_ghost_before := [ AnnotCLemma (clem_arrv_take_first 4 4)
                                   ; AnnotCLemma (clem_arrv_take_first 4 4) ]
              ; ai_instr := x ; ai_ghost_after := []
              ; ai_block := None |}
           else if Nat.eqb i (ln_store L) then
             {| ai_ghost_before := [] ; ai_instr := x
              ; ai_ghost_after := [ AnnotCLemma (clem_arrv_add_first 4 (-4))
                                  ; AnnotCLemma (clem_arrv_add_first 4 (-4)) ]
              ; ai_block := None |}
           else AST_AnnotInstr x)
          (ln_annot_go (S i) r)
    end.
  Definition ln_annot : list AnnotInstr := ln_annot_go 0 (ln_instrs L).
End Template.

Definition lnSub : LoopN := MkLoopN A0 A4 A1 false sub_loop_instrs 10 56 20.

Lemma nv_valid_sub_loop : cfg_vc_loop (lnRec lnSub (@sub_scratch)) (ln_annot lnSub).
Proof. Time solve_mb_vc. Qed.
End NV.
