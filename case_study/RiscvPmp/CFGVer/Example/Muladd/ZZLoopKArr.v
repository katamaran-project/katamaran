(* ZZ probe (not built): matched arr BASELINE for muladd loop K before PLAN-arrv
   Phase D (2026-10-26): ZZArrvCost.v's Old LoopN (arr, as at HEAD before the
   arrv port) on MuladdParamLoopK's own instructions and scratch.  One VC per
   file, so it is cold like MuladdParamLoopK.valid_* . *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.
From Katamaran Require Import RiscvPmp.CFGVer.GenSegment.
From Katamaran Require Import RiscvPmp.CFGVer.Example.Muladd.MuladdParamClose.
From Katamaran Require RiscvPmp.CFGVer.Example.Muladd.MuladdParamLoopK.

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
End Old.

Definition oL : Old.LoopN := Old.MkLoopN T6 T5 S0 false MuladdParamLoopK.k_instrs 9 52 20.
Lemma o_valid : cfg_vc_loop (Old.lnRec oL (@MuladdParamLoopK.k_scratch)) (Old.ln_annot oL).
Proof. Time solve_mb_vc. Qed.
