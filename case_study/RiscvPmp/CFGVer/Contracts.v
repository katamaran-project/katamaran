(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel, Dominique Devriese, Sander Huyghebaert  *)
(* All rights reserved.                                                       *)
(*                                                                            *)
(* Redistribution and use in source and binary forms, with or without         *)
(* modification, are permitted provided that the following conditions are     *)
(* met:                                                                       *)
(*                                                                            *)
(* 1. Redistributions of source code must retain the above copyright notice,  *)
(*    this list of conditions and the following disclaimer.                   *)
(*                                                                            *)
(* 2. Redistributions in binary form must reproduce the above copyright       *)
(*    notice, this list of conditions and the following disclaimer in the     *)
(*    documentation and/or other materials provided with the distribution.    *)
(*                                                                            *)
(* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS        *)
(* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED  *)
(* TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR *)
(* PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR          *)
(* CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,      *)
(* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,        *)
(* PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR         *)
(* PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF     *)
(* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING       *)
(* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS         *)
(* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.               *)
(******************************************************************************)


(* ========================================================================= *)
(* Contracts.v — the CFG verifier contract layer.                            *)
(*                                                                           *)
(* CFGVerifierContract (+ Valid/Debug variants over the term-table VC),      *)
(* minimal_pre, the assertion vocabulary for hand-written contracts          *)
(* (r ↦ᵣ v, a ↦ₘ t, asn_init_pc / asn_pc_eq), the Phase-0 symbolic-base      *)
(* helper lemmas, and the solve_vc tactic that discharges example VCs.       *)
(* The gen_contract generator machinery lives in GenContract.v.              *)
(* ========================================================================= *)

From Coq Require Import
     ZArith.ZArith
     Lists.List
     micromega.Lia
     Strings.String.
From Katamaran Require Import
     Notations
     Bitvector
     Semantics
     RiscvPmp.CFGVer.Spec
     RiscvPmp.Machine
     RiscvPmp.Sig.
From stdpp Require Import gmap.
From Katamaran Require Import
     RiscvPmp.CFGVer.Verifier
     RiscvPmp.CFGVer.Noninterference
     RiscvPmp.CFGVer.Tables.

From iris.proofmode Require string_ident tactics.

Import RiscvPmpProgram.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import bv.notations.
Import env.notations.
Import ListNotations.

Import RiscvPmpCFGVerifExecutor.
Import Assembly.
Import RiscvPmp.Sig.
Import iris.proofmode.tactics.
Import asn.notations.

Notation "x + y" := (term_binop bop.bvadd x y) : exp_scope.
Notation "x - y" := (term_binop bop.bvsub x y) : exp_scope.
Notation "a <=ᵘ b" := (term_binop (bop.relop bop.bvule) a b) : exp_scope.
Notation "a = b" := (term_binop (bop.relop bop.eq) a b) : exp_scope.
Notation "e1 ',ₜ' e2" := (term_binop bop.pair e1 e2) (at level 100).

    (* minimal_pre / extend_to_minimal_pre MOVED TO Verifier.v on 2026-09-23
       (PLAN-contract-ast Phase 4).  sexec_block must consume the EXTENDED
       precondition, so that a block's obligation is exactly what CFG_VC_triple
       proves -- i.e. so that `cfg_vc c a` IS the block's obligation.  The
       executor is below this file, so the definitions had to follow the
       contract record down.  Same layering wall, same fix. *)

    (* The TRIVIAL exit assertion — what a whole-program contract carries,
       and what every generator below supplies.  A contract that is one
       SEGMENT of a program supplies a real one instead: the resources and
       publicness facts the next segment needs.  See
       plans/PLAN-loop-invariant.md U6. *)
    Definition asn_no_post {Σ} :
      Assertion (Σ ▻ "a" ∷ ty_xlenbits ▻ "an" ∷ ty_xlenbits) :=
      asn.formula (formula_bool (term_val ty.bool true)).

    (* CFGVerifierContract: unlike a plain Hoare-triple contract, the CFG
       verifier requires an explicit exit address and fuel bound.
       Postconditions are not exposed: SHeapSpec has no leakcheck, so the final
       heap state is unconstrained and any leftover resources are silently dropped.

       Post table-pivot (PLAN-symbolic-base.md Phase 3): the verifier side is
       the TABLE VC (scfg_verification_condition) over address-term
       table built from the placement term `cfg_placement` by table_of_list,
       and ONE exit term `cfg_exit` (PLAN-exit-targets.md).  Concrete contracts pass term_val (bv.of_N init_addr)
       (the keys then fold to literals inside peval_bvadd — same behavior as
       the old gmap VC); parameterized contracts may pass a variable term.
       The concrete load address is NOT part of the contract (its old field
       cfg_init_addr was dropped, PLAN-valid-blk-annot §8.2): the end-to-end
       side takes init_addr itself and links it through the hypothesis
       inst cfg_placement ι = SyncVal (bv.of_N init_addr). *)
    Definition CFG_VC_triple {Σ}
      (p     : Term Σ ty_xlenbits)
      (exits : Term Σ ty_xlenbits)
      (P  : Assertion (Σ ▻ "a" ∷ ty_xlenbits))
      (i  : list AnnotInstr)
      (fl : nat)
      (* The exit assertion, RE-EXPOSED 2026-09-03 (it was hardwired to
         `true` by 2b6c7753).  `consume`d at the moment the pc reaches the
         exit, with "an" bound to it; the
         soundness bridge hands it back to the caller, which is what makes
         two segment contracts composable.  Pass asn_no_post for an
         ordinary whole-program contract. *)
      (Q  : Assertion (Σ ▻ "a" ∷ ty_xlenbits ▻ "an" ∷ ty_xlenbits)) :=
      scfg_verification_condition (Σ := Σ)
        (extend_to_minimal_pre P) (table_of_list p 0 i) exits fl Q wnil.

    (* THE VC PIPELINE: postprocess, then REPLAY, then postprocess again --
       MicroSail's own (SymbolicExecutor.v, ValidContractWithFuel).  The first
       postprocess solves evars and substitutes their witnesses; replay
       re-runs the solved tree through the solver-backed monad, so every
       assert is re-offered to the solver in its SUBSTITUTED form.  Without
       it, a formula built before an angelic block-entry variable was pinned
       reached the closer as a ring identity peval never saw, e.g.
       `-4*M + (4 + (m + 4*M)) = 4 + m` (parametric muladd tail: 20 leaves
       -> 14, closer 398 -> 248 s, construction +1.7%; 2026-10-01).
       Soundness: postprocess_sound + replay_sound (Adequacy.v). *)
    Definition cfg_postprocess (s : SymProp.SymProp [ctx]) : SymProp.SymProp [ctx] :=
      postprocess (SPureSpec.replay (w := wnil) (postprocess s)).

    (* init_addr is unused by the symbolic VC; it is kept in the signature so
       Valid_CFG_VC remains a direct cfg_map target. *)
    Definition Valid_CFG_VC {Σ}
      (p     : Term Σ ty_xlenbits)
      (exits : Term Σ ty_xlenbits)
      (P  : Assertion (Σ ▻ "a" ∷ ty_xlenbits))
      (i  : list AnnotInstr)
      (fl : nat)
      (Q  : Assertion (Σ ▻ "a" ∷ ty_xlenbits ▻ "an" ∷ ty_xlenbits)) :=
      safeE (cfg_postprocess (CFG_VC_triple p exits P i fl Q)).

    (* CFGVerifierContract and cfg_map MOVED TO Verifier.v on 2026-09-22
       (PLAN-contract-ast Phase 4).  `ai_block` must carry a real contract, and
       ai_block lives in Verifier.v, which Contracts.v REQUIRES -- so the record
       had to sit below AnnotInstr, not above it.  Flipping cfg_instrs to
       `list AST` made the record well-founded as a TYPE; it did nothing about
       FILE ORDER, and that is what this move fixes.  Both files are light, and
       Contracts.v is not on CLAUDE.md's trusted-statement list, so nothing about
       the audit surface changes. *)


    (* THE VERIFICATION CONDITION.  This was `ValidCFGVerifierContract c`
       until 2026-09-22 (PLAN-contract-ast Phase 1).  Two changes:

       - it takes the ANNOTATED instruction list `a` as an argument.  That is
         the proof hint: the same program as `cfg_instrs c`, carrying ghost
         annotations and block contracts;
       - the name.  `Valid…` is now reserved for the ANNOTATION-FREE semantic
         form, which lands in Phase 4 and is what a block premise quotes and
         what nests.  A verification condition is not valid, it is discharged,
         so this one is named as the plumbing it is -- next to `cfg_map`.

       The record's own `cfg_instrs` is deliberately IGNORED here: it is the
       `list AST` statement side, and `Valid_CFG_VC` has always taken its
       instruction list as an argument anyway.  The equation tying the two
       together, `strip a = cfg_instrs c`, is a hypothesis of the SOUNDNESS
       BRIDGE rather than of the VC (PLAN §2.5) -- so `cfg_vc c a` does not
       force `a` to be a version of `c`'s program.  Harmless: such a proof
       establishes nothing, because the bridge will not accept it. *)
    Definition cfg_vc {Σ} (c : @CFGVerifierContract Σ) (a : list AnnotInstr) : Prop :=
      cfg_map c (fun p exits P _ fl Q => Valid_CFG_VC p exits P a fl Q).

    (* ---- THE LOOP VC (PLAN-loop-rule.md) ----------------------------------
       A LOOP CONTRACT's precondition is the invariant: its parameters are the
       logic variables that never change, and everything that changes across
       trips is existential INSIDE the precondition (decision L2).  Its VC runs
       the body ONCE from the invariant, and the run stops either at the exit
       or back at the head (Verifier.is_head).  `loop_post` says what each stop
       owes: the post at the exit; the (extended) precondition -- the
       invariant -- at the head, with "a" rebound to the pc reached.  The pc
       equations decide which disjunct applies.  The induction over the trips
       happens only in the meta-level loop rule (Adequacy.v), never here.

       Every `subst` below names its instance (`T :=` / `Subst :=`).  Left to
       inference, elaborating loop_post ran past 600 s and 9.7 GB (measured
       2026-10-14); annotated it takes milliseconds. *)
    (* THE POST'S CONTEXT.  `ex` and `p` are terms over the contract's
       context Σ; a post lives over Σ ▻ "a" ▻ "an".  sub_to_post_ctx is the
       weakening between the two: every variable of Σ to itself. *)
    Definition sub_to_post_ctx {Σ : LCtx} :
      Sub Σ (Σ ▻ "a" ∷ ty_xlenbits ▻ "an" ∷ ty_xlenbits) :=
      subst (T := Sub Σ) (sub_wk1 (b := "a" ∷ ty_xlenbits)) (sub_wk1 (b := "an" ∷ ty_xlenbits)).

    (* A term over Σ, read in the post's context. *)
    Definition to_post {Σ : LCtx} (t : Term Σ ty_xlenbits) :
      Term (Σ ▻ "a" ∷ ty_xlenbits ▻ "an" ∷ ty_xlenbits) ty_xlenbits :=
      subst (T := fun Σ => Term Σ ty_xlenbits) t sub_to_post_ctx.

    (* REBIND "a" TO "an": Σ to itself and the entry pc "a" to the pc reached,
       "an".  Applied to the invariant it gives Inv[a := an], the invariant
       at the pc the run came back to. *)
    Definition sub_a_to_an {Σ : LCtx} :
      Sub (Σ ▻ "a" ∷ ty_xlenbits) (Σ ▻ "a" ∷ ty_xlenbits ▻ "an" ∷ ty_xlenbits) :=
      env.snoc sub_to_post_ctx ("a" ∷ ty_xlenbits) (term_var "an").

    Definition loop_post {Σ : LCtx}
      (p ex : Term Σ ty_xlenbits)
      (P  : Assertion (Σ ▻ "a" ∷ ty_xlenbits))
      (Q  : Assertion (Σ ▻ "a" ∷ ty_xlenbits ▻ "an" ∷ ty_xlenbits)) :
      Assertion (Σ ▻ "a" ∷ ty_xlenbits ▻ "an" ∷ ty_xlenbits) :=
      asn.or
        (* stopped at the exit: the loop's post *)
        (asn.sep (asn.formula (formula_propeq (term_var "an") (to_post ex))) Q)
        (* stopped back at the head: the invariant, at the pc reached *)
        (asn.sep (asn.formula (formula_propeq (term_var "an") (to_post p)))
           (subst (Subst := asn.sub_assertion) (extend_to_minimal_pre P) sub_a_to_an)).

    Definition CFG_VC_loop_triple {Σ}
      (p ex : Term Σ ty_xlenbits)
      (P  : Assertion (Σ ▻ "a" ∷ ty_xlenbits))
      (i  : list AnnotInstr)
      (fl : nat)
      (Q  : Assertion (Σ ▻ "a" ∷ ty_xlenbits ▻ "an" ∷ ty_xlenbits)) :=
      scfg_loop_verification_condition (Σ := Σ)
        (extend_to_minimal_pre P) (table_of_list p 0 i) ex fl (loop_post p ex P Q) wnil.

    (* THE HEAD IS THE PLACEMENT.  The executor's head test (Verifier.is_head)
       reads the head off the table's first key.  For the table the loop VC
       builds -- table_of_list from offset 0, then the triple's substitution
       and words -- that key is the placement `p + 0`, so the head test is
       exactly "pc = placement".  Stated here so that this is a fact, not a
       convention; the soundness proof does not need it (a wrong head would
       make loop_post's pc equation fail, never pass). *)
    Lemma is_head_table_of_list {Σ : LCtx} {w : World} (ζ : Sub Σ w)
        (p : Term Σ ty_xlenbits) (ai : AnnotInstr) (i : list AnnotInstr)
        (x : Term (wctx w) ty_word) (ws : list (Term (wctx w) ty_word))
        (apc : Term (wctx w) ty_xlenbits) :
      is_head (zip_words (subst_itable ζ (table_of_list p 0 (ai :: i))) (x :: ws)) apc
      = Term_eqb (peval apc)
          (peval (subst (peval_bvadd (term_val ty_xlenbits (bv.of_N 0)) p) ζ)).
    Proof. reflexivity. Qed.

    Lemma inst_sub_to_post_ctx {Γ : LCtx} (ι : Valuation Γ) (x y : RelVal ty_xlenbits) :
      inst (T := Sub Γ) sub_to_post_ctx (ι.["a"∷ty_xlenbits ↦ x].["an"∷ty_xlenbits ↦ y]) = ι.
    Proof. unfold sub_to_post_ctx. rewrite inst_subst. rewrite !inst_sub_wk1. reflexivity. Qed.

    Lemma inst_to_post {Γ : LCtx} (ι : Valuation Γ) (x y : RelVal ty_xlenbits)
        (t : Term Γ ty_xlenbits) :
      inst (T := fun Σ => Term Σ ty_xlenbits) (to_post t)
        (ι.["a"∷ty_xlenbits ↦ x].["an"∷ty_xlenbits ↦ y]) = inst t ι.
    Proof. unfold to_post. rewrite inst_subst. now rewrite inst_sub_to_post_ctx. Qed.

    (* What the loop post SAYS, at a valuation: the post at the exit, or the
       invariant at the head with "a" rebound to the pc reached. *)
    Lemma loop_post_interpret {PROP : bi} {PI : PredicateDef PROP} {Σ : LCtx}
        (p ex : Term Σ ty_xlenbits) (P : Assertion (Σ ▻ "a"∷ty_xlenbits))
        (Q : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
        (ι : Valuation Σ) (x y : RelVal ty_xlenbits) :
      asn.interpret (loop_post p ex P Q) (ι.["a"∷ty_xlenbits ↦ x].["an"∷ty_xlenbits ↦ y]) ⊣⊢
      ((⌜y = inst (T := fun Σ => Term Σ ty_xlenbits) ex ι⌝ ∧ emp) ∗
         asn.interpret Q (ι.["a"∷ty_xlenbits ↦ x].["an"∷ty_xlenbits ↦ y])) ∨
      ((⌜y = inst (T := fun Σ => Term Σ ty_xlenbits) p ι⌝ ∧ emp) ∗
         asn.interpret (extend_to_minimal_pre P) (ι.["a"∷ty_xlenbits ↦ y]))%I.
    Proof.
      unfold loop_post. cbn [asn.interpret].
      rewrite asn.interpret_subst.
      cbn [instprop instprop_formula].
      rewrite !inst_to_post.
      unfold sub_a_to_an. rewrite inst_sub_snoc inst_sub_to_post_ctx.
      now cbn.
    Qed.

    (* The loop contract's VC.  `c`'s placement is the loop head. *)
    Definition cfg_vc_loop {Σ} (c : @CFGVerifierContract Σ) (a : list AnnotInstr) : Prop :=
      cfg_map c (fun p ex P _ fl Q =>
        safeE (cfg_postprocess (CFG_VC_loop_triple p ex P a fl Q))).

    Definition DebugCFGVerifierContract {Σ} (c : @CFGVerifierContract Σ)
      (a : list AnnotInstr) : Prop :=
      cfg_map c (fun p exits P _ fl Q =>
        VerificationCondition (cfg_postprocess (CFG_VC_triple p exits P a fl Q))).

    (* NOTE: the sugar  {{ P }} i @cfg[ ec , fl ]  for building a
       CFGVerifierContract literal lives as a Local Notation in
       Example/MvSwap.v (its only user).  It is deliberately NOT exported
       from here: the notation turns {{ and }} into lexer keywords, which
       breaks any downstream occurrence of "}}" (e.g. a sigma type ending
       in "... & Reg x}}"). *)

    (* An `Ltac solve_bv` (rewrite `x + 0` to `x`) used to live here, and
       solve_vc called `try solve_bv`.  That call NEVER reached it:
       theories/Bitvector.v declares `Tactic Notation "solve_bv" :=
       bv.bv_zify`, and a tactic notation wins over an Ltac of the same
       name, so solve_vc ran the full bv decision procedure (zify + lia) on
       every VC goal.  On muladd with loop blocks that was 77 of 79 s per
       prefix (PLAN-array-invariants, 2026-09-29).  Removed both: all 18
       tracked light examples verify without the call. *)

    (* ===================================================================
       Phase 0 (PLAN-symbolic-base.md, §1): helper lemmas anticipating the
       residual VC obligation shapes that the symbolic-base executor
       (Phase 1-4, not yet implemented) will leave for solve_vc to close.

       Level note (deviation from the plan's phrasing): solve_vc closes
       goals that come out of safeE/postprocess, i.e. the plain Coq `Prop`
       built by `safe`/`instprop` (Symbolic/Propositions.v, Syntax/Formulas.v)
       -- NOT the iProp/UnifLogic `Pred w` layer (`instpred`) that
       `instpred_formula_secLeak_binop`/`_val` (Solver.v/Worlds.v) live in.
       That iProp layer is what Phase 2's rsolve/RefineCompat machinery in
       Verifier.v uses. So instead of composing those two iProp lemmas
       (as the plan literally suggested), we restate the same compositional
       fact about `secLeak`/`RelVal` at the `instprop` level below -- probe-
       confirmed against this file's actual notion of validity
       (`safeE := VerificationConditionWithErasure` grounds out in
       `SymProp.safe`, whose `assertk`/`assumek` cases use `instprop`, see
       Symbolic/Propositions.v:315-348).

       gotcha (new, not yet in CLAUDE.md's pitfall table): a blanket `cbn`
       silently unfolds `xlenbits` (`:= xlenbytes * byte`) into unary Peano
       form `S (S (... O))`.  A lemma about `bv xlenbits` proved *before*
       such a `cbn` and one invoked *after* then have differently-shaped
       (but convertible) `n` indices on `bv.bin`/`bv.add`/`bv.of_N`, which
       silently breaks `set`/`rewrite`-based matching (though `apply`/`exact`
       still work via full conversion). Use `cbn -[xlenbits]` whenever the
       goal will later be matched against an externally-proved bv-indexed
       lemma. *)
    Section Phase0SymbolicBaseHelpers.

      (* --- (1) Compound secLeak discharge ---
         Probe-confirmed residual shape: `formula_secLeak (c ⊕ t)` asserted
         under a path-condition assumption `formula_secLeak t` (t a variable
         term, c a literal), arising from `peval_bvadd`'s constant-first
         canonicalization of the pc term after k steps from a symbolic base. *)

      (* Prop-level analogs of Solver.v's instpred_formula_secLeak_val/binop,
         restated at the instprop level solve_vc actually sees. *)
      Lemma instprop_formula_secLeak_val {Σ} (ι : Valuation Σ) {σ} (v : Val σ) :
        instprop (formula_secLeak (term_val σ v)) ι.
      Proof. cbn. auto. Qed.

      Lemma instprop_formula_secLeak_binop {Σ} (ι : Valuation Σ) {σ1 σ2 σ3}
        (op : BinOp σ1 σ2 σ3) (t1 : Term Σ σ1) (t2 : Term Σ σ2) :
        instprop (formula_secLeak t1) ι ->
        instprop (formula_secLeak t2) ι ->
        instprop (formula_secLeak (term_binop op t1 t2)) ι.
      Proof.
        cbn. intros H1 H2. destruct (inst t1 ι), (inst t2 ι); cbn in *; auto.
      Qed.

      (* The compound discharge helper solve_vc will actually reach for:
         a concrete literal bvadd'ed onto a variable term whose secLeak is
         already assumed (in the path condition). *)
      Lemma secLeak_bvadd_val_compat {Σ} (ι : Valuation Σ) (c : Val ty_xlenbits)
        (t : Term Σ ty_xlenbits) :
        instprop (formula_secLeak t) ι ->
        instprop (formula_secLeak (term_binop bop.bvadd (term_val ty_xlenbits c) t)) ι.
      Proof.
        intro H. apply instprop_formula_secLeak_binop; auto.
        apply instprop_formula_secLeak_val.
      Qed.

      (* --- (2) Fetch-bounds discharge ---
         Probe-confirmed shapes at step k: `0 <= unsigned pc_k` and
         `unsigned pc_k + 4 <= maxAddr`, where `pc_k = bv.add (bv.of_N c) a`
         (c = 4k the constant offset, a the symbolic base), with `unsigned
         (c ⊕ a)` NOT distributed by the solver (decision #5: never ask the
         solver to cancel bvadd). *)

      (* Value-level core, exactly as specified in the plan. *)
      Lemma fetch_bound_step (a : bv xlenbits) (c X : N) :
        (bv.bin a + X <= maxAddr)%N -> (c + 4 <= X)%N ->
        (bv.bin (bv.add (bv.of_N c) a) + 4 <= maxAddr)%N.
      Proof.
        intros Hbound Hc.
        (* was `c + bin a <= 4092`, i.e. maxAddr - 4 spelled out; phrasing it
           as a `+ 4 <=` keeps maxAddr symbolic and subtraction-free. *)
        assert (Hsum : (c + bv.bin a + 4 <= maxAddr)%N) by lia.
        pose proof maxAddr_rep as Hexp.
        assert (HcE : (c < bv.exp2 xlenbits)%N).
        { set (E := bv.exp2 xlenbits) in *; clearbody E. lia. }
        pose proof (bv.bin_of_N_small HcE) as Heq.
        assert (Hlt : (bv.bin (@bv.of_N xlenbits c) + bv.bin a < bv.exp2 xlenbits)%N).
        { rewrite Heq. set (E := bv.exp2 xlenbits) in *; clearbody E. lia. }
        rewrite (bv.bin_add_small Hlt). rewrite Heq. lia.
      Qed.

      (* Same fact lifted to Z via bv.unsigned (= Z.of_N ∘ bv.bin), matching
         the ty.int level the fetch-bound VC obligations are phrased at
         (term_unsigned = term_unop uop.unsigned, eval = bv.unsigned). *)
      Lemma fetch_bound_step_Z (a : bv xlenbits) (c X : N) :
        (bv.bin a + X <= maxAddr)%N -> (c + 4 <= X)%N ->
        (bv.unsigned (bv.add (bv.of_N c) a) + 4 <= Z.of_N maxAddr)%Z.
      Proof.
        intros H1 H2. pose proof (@fetch_bound_step a c X H1 H2) as Hn.
        unfold bv.unsigned. set (B := bv.bin (bv.add (bv.of_N c) a)) in *. lia.
      Qed.

      (* unsigned is always nonnegative: discharges the lower fetch bound
         unconditionally, once the base term is known to be in sync (the
         base is always SyncVal, never a genuine two-execution RelVal --
         PLAN-symbolic-base.md §0, decision 4: the pc is leaked, so
         instruction addresses are public in any verifiable contract). *)
      Lemma instprop_fetch_bound_lower {Σ} (ι : Valuation Σ)
        (base : Term Σ ty_xlenbits) (a : Val ty_xlenbits) (c : N)
        (Hsync : inst base ι = SyncVal a) :
        instprop (formula_relop bop.le (term_val ty.int 0%Z)
          (term_unop uop.unsigned
             (term_binop bop.bvadd (term_val ty_xlenbits (bv.of_N c)) base))) ι.
      Proof.
        cbn -[xlenbits]. rewrite Hsync. cbn -[xlenbits]. unfold bv.unsigned. lia.
      Qed.

      (* Upper fetch bound: needs the window hypotheses fetch_bound_step_Z
         requires (Hwin from the contract's length bound, Hc identifying
         which instruction slot c picks out). *)
      Lemma instprop_fetch_bound_upper {Σ} (ι : Valuation Σ)
        (base : Term Σ ty_xlenbits) (a : Val ty_xlenbits) (c X : N)
        (Hsync : inst base ι = SyncVal a)
        (Hwin : (bv.bin a + X <= maxAddr)%N) (Hc : (c + 4 <= X)%N) :
        instprop (formula_relop bop.le
          (term_binop bop.plus
             (term_unop uop.unsigned
                (term_binop bop.bvadd (term_val ty_xlenbits (bv.of_N c)) base))
             (term_val ty.int 4%Z))
          (term_val ty.int (Z.of_N maxAddr))) ι.
      Proof.
        cbn -[xlenbits]. rewrite Hsync. cbn -[xlenbits].
        exact (@fetch_bound_step_Z a c X Hwin Hc).
      Qed.

    End Phase0SymbolicBaseHelpers.

    (* Phase 0 self-tests (regression anchors): replicate the target VC
       obligation shapes described in PLAN-symbolic-base.md §1 and close
       them with the helpers above.  These do not exercise a real VC (Phase
       1's symbolic executor doesn't exist yet); they pin down the exact
       Prop shape the Phase 1-4 work must eventually produce. *)

    (* (a) compound secLeak, discharged from a bare secLeak assumption. *)
    Goal forall (Σ : LCtx) (ι : Valuation Σ) (c : Val ty_xlenbits)
      (t : Term Σ ty_xlenbits),
      instprop (formula_secLeak t) ι ->
      instprop (formula_secLeak (term_binop bop.bvadd (term_val ty_xlenbits c) t)) ι.
    Proof. intros. apply secLeak_bvadd_val_compat; auto. Qed.

    (* (b) fetch bounds, concrete instantiation: a 10-instruction program
       (X = 4*10 = 40) and the 4th instruction (c = 4*3 = 12). *)
    Goal forall (Σ : LCtx) (ι : Valuation Σ) (base : Term Σ ty_xlenbits)
      (a : Val ty_xlenbits),
      inst base ι = SyncVal a ->
      (bv.bin a + 40 <= maxAddr)%N ->
      instprop (formula_relop bop.le (term_val ty.int 0%Z)
        (term_unop uop.unsigned
           (term_binop bop.bvadd (term_val ty_xlenbits (bv.of_N 12)) base))) ι /\
      instprop (formula_relop bop.le
        (term_binop bop.plus
           (term_unop uop.unsigned
              (term_binop bop.bvadd (term_val ty_xlenbits (bv.of_N 12)) base))
           (term_val ty.int 4%Z))
        (term_val ty.int (Z.of_N maxAddr))) ι.
    Proof.
      intros Σ ι base a Hsync Hwin. split.
      - eapply instprop_fetch_bound_lower; eauto.
      - eapply (@instprop_fetch_bound_upper Σ ι base a 12 40 Hsync Hwin); lia.
    Qed.

    (* --- (3) evalRel-level fetch-bound residuals of a SYMBOLIC-base VC ---
       After `vm_compute; solve_vc`, a parametric-base (term_var "p") VC leaves
       the fetch obligations for each instruction slot fully reduced to the
       `bop.evalRel` / `match _ with SyncVal p => p | NonSyncVal _ _ => False end`
       level -- one layer BELOW the `instprop (formula_relop ...)` shape the
       Phase-0 helpers (1)-(2) above are phrased at, so those never fire here.
       The base register value `v` is always `secLeak` (public: instruction
       addresses are leaked in any verifiable contract), hence a `SyncVal`.
       These four lemmas discharge the three residual shapes -- secLeak of a
       constant-offset pc, the fetch lower bound, and the fetch upper bound
       (bare pc = base, and pc = base + constant) -- and are applied by the
       `solve_symbase_fetch` tactic below.  solve_vc itself is deliberately
       left untouched: it stays a general VC solver, and these symbolic-base
       residuals are closed by a separate tactic run after it. *)

    Lemma relval_secLeak_bvadd (c : Val ty_xlenbits) (v : RelVal ty_xlenbits) :
      RiscvPmpSignature.secLeak v ->
      RiscvPmpSignature.secLeak (bop.evalRel bop.bvadd (SyncVal c) v).
    Proof. intros H; destruct v as [a|a b]; [exact I | destruct H]. Qed.

    Lemma relval_fetch_lower (X : RelVal ty_xlenbits) :
      RiscvPmpSignature.secLeak X ->
      match bop.eval_relop_relprop bop.le (SyncVal 0%Z) (uop.evalRel uop.unsigned X) with
      | SyncVal p => p | NonSyncVal _ _ => False end.
    Proof. intros H; destruct X as [a|a b]; [cbn; unfold bv.unsigned; lia | destruct H]. Qed.

    (* The GOAL-side offset `A` is a parameter rather than the hardcoded word
       width 4.  Instruction fetch and word accesses instantiate it at 4, but
       a BYTE access (`lbu`, via mem_read 1) leaves an upper bound with offset
       1, and HALF would leave 2: sep_contract_mem_read's bound is
       `unsigned paddr + bytes <= maxAddr`, width-generic (Spec.v:439).  See
       PLAN-byte-memory.md. *)
    Lemma relval_fetch_upper_bare (v : RelVal ty_xlenbits) (A B : Z) :
      RiscvPmpSignature.secLeak v ->
      match bop.eval_relop_relprop bop.le (SyncVal 0%Z)
        (bop.evalRel bop.minus (SyncVal (Z.of_N maxAddr))
           (bop.evalRel bop.plus (SyncVal B) (uop.evalRel uop.unsigned v)))
      with SyncVal p => p | NonSyncVal _ _ => False end ->
      (A <= B)%Z ->
      match bop.eval_relop_relprop bop.le (SyncVal 0%Z)
        (bop.evalRel bop.minus (SyncVal (Z.of_N maxAddr))
           (bop.evalRel bop.plus (SyncVal A) (uop.evalRel uop.unsigned v)))
      with SyncVal p => p | NonSyncVal _ _ => False end.
    Proof.
      intros H Hb Hle; destruct v as [a|a b];
        [cbn in *; unfold bv.unsigned in *; lia | destruct H].
    Qed.

    (* Same generalisation, plus the `0 <= A` the no-wrap step needs: bounding
       `bin cbv + bin a` below exp2 goes through `maxAddr - A`, which only stays
       under 2^32 for a non-negative A. *)
    Lemma relval_fetch_upper_add (v : RelVal ty_xlenbits) (cbv : bv xlenbits) (A B : Z) :
      RiscvPmpSignature.secLeak v ->
      match bop.eval_relop_relprop bop.le (SyncVal 0%Z)
        (bop.evalRel bop.minus (SyncVal (Z.of_N maxAddr))
           (bop.evalRel bop.plus (SyncVal B) (uop.evalRel uop.unsigned v)))
      with SyncVal p => p | NonSyncVal _ _ => False end ->
      (Z.of_N (bv.bin cbv) + A <= B)%Z ->
      (0 <= A)%Z ->
      match bop.eval_relop_relprop bop.le (SyncVal 0%Z)
        (bop.evalRel bop.minus (SyncVal (Z.of_N maxAddr))
           (bop.evalRel bop.plus (SyncVal A)
              (uop.evalRel uop.unsigned (bop.evalRel bop.bvadd (SyncVal cbv) v))))
      with SyncVal p => p | NonSyncVal _ _ => False end.
    Proof.
      intros H Hb Hle HA; destruct v as [a|a b]; [| destruct H].
      (* Every constant must reach `lia` as a CONSISTENT atom, and a bare
         `cbn in *` gives none of them: it reduces maxAddr in Hb but not in
         the freshly-stated Hexp, and reduces `bv.exp2 xlenbits` to
         `bv.exp2 32` in Hexp but not in the freshly-stated Hlt (xlenbits is
         only Opaque inside ModelBinary.v).  Either mismatch shows up as
         `Cannot find witness`.  Blocking delta on all three keeps every
         occurrence folded, so the atoms line up. *)
      pose proof maxAddr_rep as Hexp.
      cbn -[maxAddr bv.exp2 xlenbits] in *; unfold bv.unsigned in *.
      assert (Hlt : (bv.bin cbv + bv.bin a < bv.exp2 xlenbits)%N) by lia.
      rewrite (bv.bin_add_small Hlt). lia.
    Qed.

    (* The same bound for an access BELOW the base -- `lw rd, -4(rs)`, which
       is what clang emits for any loop walking a pointer DOWNWARD (muladd's
       memmove-down at idx 84..89, and its sibling at 113..117).  The address
       is `cbv + v` with cbv the wrapped representation of -D, so `bv.bin`
       WRAPS and relval_fetch_upper_add's no-overflow step does not apply.

       The extra premise is a LOWER bound on the base (`D <= unsigned v`),
       which a contract must supply -- without it `v - D` underflows and the
       access really is out of range.  `Hc` pins cbv as the two's-complement
       encoding of -D and is `vm_compute; reflexivity` at any concrete offset. *)
    Lemma relval_fetch_upper_neg (v : RelVal ty_xlenbits) (cbv : bv xlenbits)
      (A B D : Z) :
      RiscvPmpSignature.secLeak v ->
      match bop.eval_relop_relprop bop.le (SyncVal 0%Z)
        (bop.evalRel bop.minus (SyncVal (Z.of_N maxAddr))
           (bop.evalRel bop.plus (SyncVal B) (uop.evalRel uop.unsigned v)))
      with SyncVal p => p | NonSyncVal _ _ => False end ->
      match bop.eval_relop_relprop bop.le (SyncVal 0%Z)
        (bop.evalRel bop.minus (uop.evalRel uop.unsigned v) (SyncVal D))
      with SyncVal p => p | NonSyncVal _ _ => False end ->
      (* D is a plain Z, NOT `Z.of_N D`: the goal's offset arrives as a Z
         LITERAL, and unifying `Z.of_N ?D` with `4` would require inverting
         Z.of_N -- the same trap as seg_fits_Z. *)
      @eq Z (Z.add (Z.of_N (bv.bin cbv)) D) (Z.of_N (bv.exp2 xlenbits)) ->
      (A <= B + D)%Z ->
      match bop.eval_relop_relprop bop.le (SyncVal 0%Z)
        (bop.evalRel bop.minus (SyncVal (Z.of_N maxAddr))
           (bop.evalRel bop.plus (SyncVal A)
              (uop.evalRel uop.unsigned (bop.evalRel bop.bvadd (SyncVal cbv) v))))
      with SyncVal p => p | NonSyncVal _ _ => False end.
    Proof.
      intros Hs Hub Hlb Hc HA; destruct v as [a | x y]; [| destruct Hs].
      pose proof maxAddr_rep as Hexp.
      pose proof (bv.bv_is_wf a) as Ha.
      pose proof (bv.bv_is_wf cbv) as Hc2.
      cbn -[maxAddr bv.exp2 xlenbits] in *; unfold bv.unsigned in *.
      rewrite bv.bin_add.
      (* exp2 <= bin cbv + bin a < 2 * exp2, so the mod is one subtraction.
         `set` both atoms first and restrict the replace with `at 1`: without
         it the rewrite also fires inside its own right-hand side. *)
      set (E := bv.exp2 xlenbits) in *.
      set (S := N.add (bv.bin cbv) (bv.bin a)) in *.
      assert (HS : (E <= S)%N /\ (S < E + E)%N) by (unfold S; lia).
      assert (Hm : @eq N (N.modulo S E) (N.sub S E)).
      { replace S with (N.add (N.sub S E) (N.mul 1 E)) at 1 by lia.
        rewrite N.Div0.mod_add. apply N.mod_small. lia. }
      rewrite Hm. unfold S. lia.
    Qed.

    (* Loop-EXIT residual, not a fetch bound.  A loop whose exit test is a
       POINTER COMPARE (`bne a0, a1` with a0/a1 both base-relative, as clang
       emits for BearSSL check_scalar's byte loops) leaves, on the final
       not-taken iteration, the obligation that the two now-equal pointers
       being unequal is absurd.  A counter-vs-zero loop (Example/
       KeyScheduleLoop.v) never produces this shape, which is why it appears
       only now.  Both RelVal cases are immediate: SyncVal gives `x <> x`,
       NonSyncVal collapses the match to False outright. *)
    Lemma relval_neq_irrefl (X : RelVal ty_xlenbits) :
      match bop.eval_relop_relprop bop.neq X X with
      | SyncVal p => p | NonSyncVal _ _ => False end -> False.
    Proof. destruct X as [a|a b]; cbn; [intros H; now apply H | exact (fun H => H)]. Qed.

    (* A public pointer differs from itself plus a NONZERO constant, and two
       different constant offsets of it differ.  Left by array ghosts
       (PLAN-array-invariants): clem_arr_nonempty asserts `a ≠ e` for an
       array whose start and end are the same base at different offsets,
       e.g. `dp ≠ 4 + dp`, which the solver does not decide. *)
    Lemma relval_neq_offset (X : RelVal ty_xlenbits) (c : bv xlenbits) :
      RiscvPmpSignature.secLeak X -> bv.bin c <> 0%N ->
      match bop.eval_relop_relprop bop.neq X
              (bop.evalRel bop.bvadd (ty.valToRelVal (σ := ty_xlenbits) c) X) with
      | SyncVal p => p | NonSyncVal _ _ => False end.
    Proof.
      intros HX Hc. destruct X as [x|]; [|destruct HX]. cbn. intros Hx.
      apply Hc. assert (bv.add c x = bv.add bv.zero x) as E
        by (rewrite bv.add_zero_l; symmetry; exact Hx).
      apply bv.add_cancel_r in E. now subst c.
    Qed.

    Lemma relval_neq_offsets (X : RelVal ty_xlenbits) (c1 c2 : bv xlenbits) :
      RiscvPmpSignature.secLeak X -> bv.bin c1 <> bv.bin c2 ->
      match bop.eval_relop_relprop bop.neq
              (bop.evalRel bop.bvadd (ty.valToRelVal (σ := ty_xlenbits) c1) X)
              (bop.evalRel bop.bvadd (ty.valToRelVal (σ := ty_xlenbits) c2) X) with
      | SyncVal p => p | NonSyncVal _ _ => False end.
    Proof.
      intros HX Hc. destruct X as [x|]; [|destruct HX]. cbn. intros Hx.
      apply Hc. apply bv.add_cancel_r in Hx. now subst c1.
    Qed.

    Ltac solve_vc_closers :=
      try (solve [eapply secLeak_bvadd_val_compat; eauto]);
      try (solve [eapply instprop_fetch_bound_lower; eauto]);
      try (solve [eapply instprop_fetch_bound_upper; eauto]).

    Ltac solve_vc :=
      (* `cbn -[Erasure.inst_symprop]`, not a bare `cbn` (2026-09-08).
         inst_symprop (Propositions.v:2297) unfolds edemonicv to
           `forall v : RelVal (type b), inst_symprop (cons (existT (type b) v) i) k`
         -- a valuation accumulator that carries the BINDER'S TYPE as a value
         and is rebuilt at every one of the ~22 binder levels.  One of those
         binders is the instruction-word variable at `ty.bvec (32*K)`, a UNARY
         nat, so cbn paid O(binders x width) and that was 95% of everything the
         table-size sweeps ever measured.  Blocking this one constant is
         exactly as cheap as disabling delta entirely (0.0898 -> 0.00297 M per
         bit of width, i.e. 30x) while leaving every other constant
         unfoldable, because the rest of the delta cost only exists inside what
         inst_symprop produces.  All 16 examples are unaffected.
         See diagnostics/vm-vs-tactic-split.md. *)
      vm_compute; constructor; cbn -[Erasure.inst_symprop]; intros; repeat split;
      (* No `try solve_bv` here any more: see the note where solve_bv used
         to be defined (it silently ran bv.bv_zify on every goal). *)
      (* Phase 0 extension (PLAN-symbolic-base.md §1): try the compound
         secLeak / fetch-bound helpers on any residual goal before falling
         back to auto.  The `solve [...]` wrapper is required for failure
         atomicity: `eauto` never fails (it succeeds doing nothing), so a
         bare `try (eapply L; eauto)` on a conclusion-matching goal whose
         side conditions eauto cannot close would *leave those side
         conditions behind* instead of reverting.  With solve, each unit
         either fully discharges the goal or is a no-op, so this is
         strictly additive -- existing (non symbolic-base) examples never
         reach these branches and fall through to `auto` exactly as before. *)
      solve_vc_closers;
      auto.

    (* Closes the symbolic-base fetch residuals a parametric VC leaves behind
       (see the relval_fetch_* lemmas above).  Kept SEPARATE from solve_vc so
       solve_vc remains a general-purpose VC solver; a parametric-base VC is
       discharged with `vm_compute; solve_vc; solve_symbase_fetch`, the `;`
       distributing this per-goal closer over every residual (a no-op when
       solve_vc already closed everything, as for concrete-base VCs).  The
       upper-bound-with-offset numeric side (`Z.of_N (bv.bin cbv) + 4 <= B`)
       is discharged via Z.leb_le rather than lia: with stdpp's gmap Zify
       instances in scope, lia mis-handles `bv.bin` of a literal (see
       gmap-pitfalls), whereas the boolean form vm_computes to `true`. *)
    Ltac solve_symbase_fetch :=
      solve
        [ apply relval_secLeak_bvadd; assumption
        | apply relval_fetch_lower;
            solve [ assumption | apply relval_secLeak_bvadd; assumption ]
        | eapply relval_fetch_upper_add;
            [ eassumption | eassumption
            | apply Z.leb_le; vm_compute; reflexivity
            | apply Z.leb_le; vm_compute; reflexivity ]
        | eapply relval_fetch_upper_bare; [ eassumption | eassumption | lia ]
        | (* base MINUS a constant: the eassumption for the LOWER bound is what
             fixes ?D, so it must come before the encoding check. *)
          eapply relval_fetch_upper_neg;
            [ eassumption | eassumption | eassumption
            | vm_compute; reflexivity
            | apply Z.leb_le; vm_compute; reflexivity ]
        | apply relval_neq_irrefl
        | apply relval_neq_offset; [assumption | vm_compute; discriminate]
        | apply relval_neq_offsets; [assumption | vm_compute; discriminate]
        (* BASE MINUS A CONSTANT, with both offsets READ OFF THE GOAL.  The
           alternative above leaves `B` and `D` as evars, and that cannot
           work: the premises are stated over `bop.eval_relop_relprop` while
           the hypotheses are still ERASED (`Erasure.inst_eformula' …`), so
           what closes them is CONVERSION, not unification -- and conversion
           needs every numeric parameter concrete before `eassumption` runs.
           Pinning them at literals would only move the problem (`D` is the
           program's own offset, not a fixed width), so both come from the
           goal: `A` is the access width it already mentions, and `D` is
           recovered from the two's-complement constant `cbv` as 2^32 - cbv.
           `B := A` is the bound the contract registers for the pointer
           itself, which is what the fetch/word case leaves in context.
           Found 2026-09-13 on loop C's exit contract -- the first DESCENDING
           pointer loop, which is what makes every access sit below its
           base. *)
        | match goal with
          | |- context [ Erasure.eterm_binop bop.plus (Erasure.eterm_val ty.int ?A)
                           (Erasure.eterm_unop uop.unsigned
                              (Erasure.eterm_binop bop.bvadd
                                 (Erasure.eterm_val (ty.bvec _) ?cbv) _)) ] =>
              let d := eval vm_compute in
                ((Z.of_N (bv.exp2 xlenbits) - Z.of_N (bv.bin cbv))%Z) in
              eapply (relval_fetch_upper_neg _ _ A d);
                [ eassumption | eassumption | eassumption
                | vm_compute; reflexivity
                | apply Z.leb_le; vm_compute; reflexivity ]
          end ].

    (* THE PARAMETRIC-BASE DISCHARGE, once.  Every contract whose base is a
       TERM rather than a literal -- which is every `gen_contract_param` and
       every mid-program segment, since a segment is by construction cut at a
       symbolic base -- is discharged by exactly these four steps.  It lived in
       GenSegment.v as `solve_param_vc` and was ALSO written out at 154 sites, so
       there were two spellings of one tactic split by vintage rather than by
       meaning; and the name said "segment" when the property that matters is
       "parametric base".  It belongs here, beside the two tactics it calls.

       Spelling out the stages is still the right move when one FAILS: this
       abbreviation reports a bare `No applicable tactic`, and on 2026-09-13 a
       failure in the last component cost a detour through the Ltac body to
       localise.  If a VC will not close, inline the four steps and see which
       one stops. *)
    Ltac solve_param_vc :=
      intros; vm_compute; solve_vc; solve_symbase_fetch.

    (* Definition with_regidx {Σ} (r : RegIdx) (P : Reg ty_xlenbits -> Assertion Σ) : Assertion Σ := *)
    (*   match reg_convert r with *)
    (*   | None     => ⊤ *)
    (*   | Some reg => P reg *)
    (*   end. *)

    (* Notation "r '↦ᵣ' v" := (with_regidx r (fun reg => asn.chunk (chunk_ptsreg reg v))) (at level 70) : asn_scope. *)
    Definition asn_regidx_pts {Σ} (r : RegIdx) (v : Term Σ ty_xlenbits) : Assertion Σ :=
      match reg_convert r with
      | None     => ⊤
      | Some reg => asn.chunk (chunk_ptsreg reg v)
      end.
    Arguments asn_regidx_pts : simpl never.

    Notation "r '↦ᵣ' v" := (asn_regidx_pts r v) (at level 70) : asn_scope.

    Ltac unfold_asn_regidx_pts :=
      match goal with
      | |- context[asn.interpret (asn_regidx_pts ?r ?v) ?ι] =>
          change (asn.interpret (asn_regidx_pts ?r ?v) ?ι) with
          (lptsreg r (inst_term v ι))
      end.
    Notation "a '↦ₘ' t" := (asn.chunk (chunk_user (@ptstomem bytes_per_word) [a; t])) (at level 70).

    Definition asn_init_pc {Σ} (start : Val ty_xlenbits) : Assertion (Σ ▻ "a" :: ty_xlenbits) :=
      term_var "a" = term_val ty_xlenbits start.

    Definition asn_pc_eq {Σ} (t : Term (Σ ▻ "a" :: ty_xlenbits) ty_xlenbits) : Assertion (Σ ▻ "a" :: ty_xlenbits) :=
      term_var "a" = t.

    Local Notation term_pc_val := (term_var "a").

    Definition asn_next_pc_eq {Σ} (t : Term (Σ ▻ "an" :: ty_xlenbits) ty_xlenbits) : Assertion (Σ ▻ "an" :: ty_xlenbits) :=
      term_var "an" = t.

    Import SymProp.notations.
    Import Erasure.notations.
