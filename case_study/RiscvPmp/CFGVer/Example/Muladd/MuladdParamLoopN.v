(* ========================================================================= *)
(* Example/Muladd/MuladdParamLoopN.v -- the muladd tail's "two arrays in lockstep" loop     *)
(* (I, K, M) as ONE template, stated with the REMAINING COUNT `n` as the only  *)
(* varying logic variable (promoted 2026-10-02 from the ZZ probes, 2026-09-30; hand-written first as  *)
(* ZZArrMN.v).  Every address is FIXED END - 4n: no current-pointer variable,  *)
(* so arr chunks' end facts (PLAN-chunk-facts.md) cannot respell anything.     *)
(*                                                                           *)
(* Arrays (arrv, PLAN-arrv D13): m (end eM) and x (end eX) are read from     *)
(* their starts; the two DONE arrays (stride -4) grow at their start by       *)
(* add_first after the store.  m is READ-ONLY, so its value is tracked: the   *)
(* contract variable VM is `rev dM ++ rM` throughout, which the caller's      *)
(* hand-back (flip the done array, join the emptied source) turns back into   *)
(* m's value.  x is overwritten: its values are fresh.  No secLeak on either  *)
(* array -- the loop does not branch on them; a caller keeps m's publicness   *)
(* by framing.  The latch compares one of the two pointers against its       *)
(* array's end.  The post is phrased in the remaining count `c` at exit (the  *)
(* angelic array match binds c := n - 1), with `c = 0` a separate pure        *)
(* obligation.                                                                *)
(* ========================================================================= *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamClose.

(* The PARAMETERS (PLAN-loop-rule.md, L2): the code base, the four arrays'
   ends, and the TOTAL count T.  The counts n (to go) and k (done) change,
   so they are existential in the invariant, with T = k + n: that is what
   lets the post hand the done count to the next loop. *)
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
      ∗ asn.formula (formula_propeq (term_var "VM") (ln_mval (term_var "dM") (term_var "rM")))
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
          ∗ asn.formula (formula_propeq (term_var "VM") (ln_mval (term_var "dM") (term_var "rM")))
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
