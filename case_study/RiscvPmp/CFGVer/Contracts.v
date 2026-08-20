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
     RiscvPmp.CFGVer.Noninterference
     RiscvPmp.CFGVer.Tables.
From Katamaran Require Import
     RiscvPmp.CFGVer.Verifier.

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

    (* minimal_pre asserts that we start executing at address 0 in Machine mode.
       We choose an arbitrary list for the pmp entries (pmp is not used in these
       examples). *)
    Definition minimal_pre {Σ} : Assertion Σ :=
      (* asn.exist "_" _ (nextpc ↦ term_var "_")
      ∗ *)cur_privilege ↦ term_val ty_privilege Machine
      (* ∗ asn_pmp_entries (term_list [(term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ term_val ty_xlenbits bv.zero) ; *)
      (*                               (term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ term_val ty_xlenbits bv.zero)]) *) ∗
            asn.chunk (chunk_user inv_leakage [env])
    .

    Definition extend_to_minimal_pre {Σ} (P : Assertion Σ) : Assertion Σ :=
      P ∗ minimal_pre.

    (* CFGVerifierContract: unlike a plain Hoare-triple contract, the CFG
       verifier requires an explicit exit condition and fuel bound.
       Postconditions are not exposed: SHeapSpec has no leakcheck, so the final
       heap state is unconstrained and any leftover resources are silently dropped.

       Post table-pivot (PLAN-symbolic-base.md Phase 3): the verifier side is
       the TABLE VC (scfg_verification_condition) over address-term
       tables built from the placement term `cfg_placement` by table_of_list /
       exits_of_list.  Concrete contracts pass term_val (bv.of_N init_addr)
       (the keys then fold to literals inside peval_bvadd — same behavior as
       the old gmap VC); parameterized contracts may pass a variable term.
       `cfg_init_addr : N` remains the concrete load address used by the
       memory/end-to-end side; the two are linked in the soundness chain by
       the hypothesis  inst cfg_placement ι = SyncVal (bv.of_N init_addr). *)
    Definition CFG_VC_triple {Σ}
      (p     : Term Σ ty_xlenbits)
      (exits : list (Term Σ ty_xlenbits))
      (P  : Assertion (Σ ▻ "a" ∷ ty_xlenbits))
      (i  : list AnnotInstr)
      (fl : nat) :=
      Katamaran.RiscvPmp.CFGVer.Verifier.scfg_verification_condition (Σ := Σ)
        (extend_to_minimal_pre P) (table_of_list p 0 i) exits fl
        (asn.formula (formula_bool (term_val ty.bool true))) wnil.

    (* init_addr and ec are unused by the symbolic VC (the exit condition
       lives in the exit TABLE now); they are kept in the signature so
       Valid_CFG_VC remains a direct cfg_map target. *)
    Definition Valid_CFG_VC {Σ}
      (init_addr : N)
      (p     : Term Σ ty_xlenbits)
      (exits : list (Term Σ ty_xlenbits))
      (P  : Assertion (Σ ▻ "a" ∷ ty_xlenbits))
      (i  : list AnnotInstr)
      (ec : bv xlenbits -> bool)
      (fl : nat) :=
      safeE (postprocess (CFG_VC_triple p exits P i fl)).

    Record CFGVerifierContract {Σ} :=
      MkCFGVerifierContract
      { cfg_init_addr     : N
      ; cfg_placement     : Term Σ ty_xlenbits
      ; cfg_exits         : list (Term Σ ty_xlenbits)
      ; cfg_precondition  : Assertion (Σ ▻ "a" ∷ ty_xlenbits)
      ; cfg_instrs        : list AnnotInstr
      ; cfg_exitCond      : bv xlenbits -> bool
      ; cfg_fuel          : nat
      }.

    Definition cfg_map {Σ A} (c : @CFGVerifierContract Σ)
      (f : N -> Term Σ ty_xlenbits -> list (Term Σ ty_xlenbits) ->
           Assertion (Σ ▻ "a" ∷ ty_xlenbits) -> list AnnotInstr ->
           (bv xlenbits -> bool) -> nat -> A) : A :=
      match c with
      | {| cfg_init_addr := ia; cfg_placement := p; cfg_exits := exits;
           cfg_precondition := pre; cfg_instrs := i;
           cfg_exitCond := ec; cfg_fuel := fl |} => f ia p exits pre i ec fl
      end.

    Definition ValidCFGVerifierContract {Σ} (c : @CFGVerifierContract Σ) : Prop :=
      cfg_map c Valid_CFG_VC.

    Definition DebugCFGVerifierContract {Σ} (c : @CFGVerifierContract Σ) : Prop :=
      cfg_map c (fun ia p exits P i ec fl =>
        VerificationCondition (postprocess (CFG_VC_triple p exits P i fl))).

    (* NOTE: the sugar  {{ P }} i @cfg[ ec , fl ]  for building a
       CFGVerifierContract literal lives as a Local Notation in
       Example/MvSwap.v (its only user).  It is deliberately NOT exported
       from here: the notation turns {{ and }} into lexer keywords, which
       breaks any downstream occurrence of "}}" (e.g. a sigma type ending
       in "... & Reg x}}"). *)

    Ltac solve_bv :=
      repeat match goal with
        | |- context[bv.add ?x (@bv.mk ?n 0 I)] =>
            fold (@bv.zero n)
        | |- context[bv.add ?x bv.zero] =>
            rewrite bv.add_zero_r
        end.

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
         `unsigned pc_k + 4 <= 1024`, where `pc_k = bv.add (bv.of_N c) a`
         (c = 4k the constant offset, a the symbolic base), with `unsigned
         (c ⊕ a)` NOT distributed by the solver (decision #5: never ask the
         solver to cancel bvadd). *)

      (* Value-level core, exactly as specified in the plan. *)
      Lemma fetch_bound_step (a : bv xlenbits) (c X : N) :
        (bv.bin a + X <= 1024)%N -> (c + 4 <= X)%N ->
        (bv.bin (bv.add (bv.of_N c) a) + 4 <= 1024)%N.
      Proof.
        intros Hbound Hc.
        assert (Hsum : (c + bv.bin a <= 1020)%N) by lia.
        assert (Hexp : (1024 < bv.exp2 xlenbits)%N) by (vm_compute; reflexivity).
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
        (bv.bin a + X <= 1024)%N -> (c + 4 <= X)%N ->
        (bv.unsigned (bv.add (bv.of_N c) a) + 4 <= 1024)%Z.
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
        (Hwin : (bv.bin a + X <= 1024)%N) (Hc : (c + 4 <= X)%N) :
        instprop (formula_relop bop.le
          (term_binop bop.plus
             (term_unop uop.unsigned
                (term_binop bop.bvadd (term_val ty_xlenbits (bv.of_N c)) base))
             (term_val ty.int 4%Z))
          (term_val ty.int 1024%Z)) ι.
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
      (bv.bin a + 40 <= 1024)%N ->
      instprop (formula_relop bop.le (term_val ty.int 0%Z)
        (term_unop uop.unsigned
           (term_binop bop.bvadd (term_val ty_xlenbits (bv.of_N 12)) base))) ι /\
      instprop (formula_relop bop.le
        (term_binop bop.plus
           (term_unop uop.unsigned
              (term_binop bop.bvadd (term_val ty_xlenbits (bv.of_N 12)) base))
           (term_val ty.int 4%Z))
        (term_val ty.int 1024%Z)) ι.
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
        (bop.evalRel bop.minus (SyncVal 1024%Z)
           (bop.evalRel bop.plus (SyncVal B) (uop.evalRel uop.unsigned v)))
      with SyncVal p => p | NonSyncVal _ _ => False end ->
      (A <= B)%Z ->
      match bop.eval_relop_relprop bop.le (SyncVal 0%Z)
        (bop.evalRel bop.minus (SyncVal 1024%Z)
           (bop.evalRel bop.plus (SyncVal A) (uop.evalRel uop.unsigned v)))
      with SyncVal p => p | NonSyncVal _ _ => False end.
    Proof.
      intros H Hb Hle; destruct v as [a|a b];
        [cbn in *; unfold bv.unsigned in *; lia | destruct H].
    Qed.

    (* Same generalisation, plus the `0 <= A` the no-wrap step needs: bounding
       `bin cbv + bin a` below exp2 goes through `1024 - A`, which only stays
       under 2^32 for a non-negative A. *)
    Lemma relval_fetch_upper_add (v : RelVal ty_xlenbits) (cbv : bv xlenbits) (A B : Z) :
      RiscvPmpSignature.secLeak v ->
      match bop.eval_relop_relprop bop.le (SyncVal 0%Z)
        (bop.evalRel bop.minus (SyncVal 1024%Z)
           (bop.evalRel bop.plus (SyncVal B) (uop.evalRel uop.unsigned v)))
      with SyncVal p => p | NonSyncVal _ _ => False end ->
      (Z.of_N (bv.bin cbv) + A <= B)%Z ->
      (0 <= A)%Z ->
      match bop.eval_relop_relprop bop.le (SyncVal 0%Z)
        (bop.evalRel bop.minus (SyncVal 1024%Z)
           (bop.evalRel bop.plus (SyncVal A)
              (uop.evalRel uop.unsigned (bop.evalRel bop.bvadd (SyncVal cbv) v))))
      with SyncVal p => p | NonSyncVal _ _ => False end.
    Proof.
      intros H Hb Hle HA; destruct v as [a|a b]; [| destruct H].
      cbn in *; unfold bv.unsigned in *.
      assert (Hexp : (1024 < bv.exp2 xlenbits)%N) by (vm_compute; reflexivity).
      assert (Hlt : (bv.bin cbv + bv.bin a < bv.exp2 xlenbits)%N) by lia.
      rewrite (bv.bin_add_small Hlt). lia.
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

    Ltac solve_vc :=
      vm_compute; constructor; cbn; intros; repeat split; try solve_bv;
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
      try (solve [eapply secLeak_bvadd_val_compat; eauto]);
      try (solve [eapply instprop_fetch_bound_lower; eauto]);
      try (solve [eapply instprop_fetch_bound_upper; eauto]);
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
        | apply relval_neq_irrefl ].

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
