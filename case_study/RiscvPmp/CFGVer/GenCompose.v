(******************************************************************************)
(*  GenCompose.v -- the COMPOSITION combinators for segment contracts.        *)
(*                                                                            *)
(*  GenSegment.v generates a mid-program segment's contract; this file is what *)
(*  turns a bag of such contracts into a proof.  It exists because the two     *)
(*  hand-written compositional proofs in this project (muladd's tail, and its  *)
(*  br_divrem loop) turned out to share an IDENTICAL skeleton, of which only   *)
(*  three things ever varied: the invariant's index arithmetic, the branch     *)
(*  guard, and the resource shift.  Everything else -- 20 itable_faith call    *)
(*  sites, 10 etable_faith call sites, 3 copies of an `exit_hit` tactic, and   *)
(*  the whole `iApply sound_scfg_verification_condition_myWP2 ... $! ...       *)
(*  with "[...]"` ritual -- was copied.                                       *)
(*                                                                            *)
(*  WHAT IS AND IS NOT AUTOMATED HERE.  seg_run reduces one loop trip to two  *)
(*  ordinary iProp implications (HPre / HPost).  It does NOT try to generate   *)
(*  those: the invariant's shape is genuinely program-specific (a fixed        *)
(*  register footprint wants an opaque frame; a sliding memory window wants a  *)
(*  cell-range fixpoint), and pretending otherwise would force both into one   *)
(*  mould.  That split -- mechanical plumbing here, invariant logic at the     *)
(*  call site -- is the intended division of labour.                           *)
(******************************************************************************)
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
     RiscvPmp.CFGVer.VerifierRel
     RiscvPmp.CFGVer.SpecIris
     RiscvPmp.CFGVer.TablesRel
     RiscvPmp.CFGVer.Noninterference
     RiscvPmp.CFGVer.Tables
     RiscvPmp.CFGVer.Contracts
     RiscvPmp.CFGVer.GenContract
     RiscvPmp.CFGVer.GenSegment
     RiscvPmp.CFGVer.Adequacy.
From iris.base_logic Require Import lib.gen_heap lib.iprop invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac big_op.
From iris.program_logic Require weakestpre adequacy.
From iris.proofmode Require string_ident tactics.
From stdpp Require namespaces.
From Equations Require Import Equations.

Import RiscvPmpProgram.

(* See GenSegment.v's note: GenContract.v's non-Local `Set Implicit Arguments`
   persists into every consumer, and it silently made `iota` implicit on a first
   draft of seg_run -- which then could not be supplied by name, because only
   IMPLICIT arguments are nameable.  Off here, Local so it does not leak. *)
Local Unset Implicit Arguments.

Import ctx.resolution.
Import ctx.notations.
Import bv.notations.
Import env.notations.
Import ListNotations.

Import RiscvPmpCFGVerifExecutor.
Import Assembly.
Import RiscvPmp.Sig.
Import iris.proofmode.tactics.
Import IrisInstanceBinary.
Import RiscvPmpIrisInstance2.
Import RiscvPmpSemantics.
Import RiscvPmpIrisAdeqParams2.
Import SmallStepNotations.
Import IrisModelBinary.RiscvPmpIrisBase2.
Import iris.algebra.excl.
Import iris.algebra.gmap.
Import IrisModel.RiscvPmpIrisBase.

Section SegCompose.
  Context {Σ} {GS : sailGS2 Σ}.

  (* ======================================================================== *)
  (* 1. SUB-TABLE FAITHFULNESS                                                *)
  (* ======================================================================== *)

  (* The reassembled program is LITERALLY the original -- an identity, not a
     computation.  Every hand-written Hif instead asserted
     `length (firstn m L ++ firstn n (skipn m L) ++ skipn (m+n) L) = length L`
     and closed it by `vm_compute`, i.e. computed a 282-element list per call
     site, eight times over. *)
  Lemma split_id {A : Type} (m n : nat) (L : list A) :
    List.firstn m L ++ List.firstn n (List.skipn m L)
      ++ List.skipn (m + n) L = L.
  Proof. rewrite <- drop_drop, take_drop, take_drop. reflexivity. Qed.

  (* One lemma for all 20 call sites.  `Hoff : 4 * skip = head` is what makes
     GenSegment's head/skip agreement a PROOF OBLIGATION rather than a silent
     convention -- get it wrong and this will not apply. *)
  Lemma instr_table_ok_at {R : LCtx} (place : Term R ty_xlenbits) (iota : Valuation R)
      (cbase : bv xlenbits) (L : list AnnotInstr) (skip take : nat) (head : N)
      (Hoff : @eq N (N.mul 4 (N.of_nat skip)) head)
      (Hskip : Nat.le skip (length L))
      (Hp : inst (T := fun Σ => Term Σ ty_xlenbits) place iota
            = ty.SyncVal (bv.add cbase (bv.of_N head)))
      (Hrep : (bv.bin cbase + 4 * N.of_nat (length L) < bv.exp2 xlenbits)%N) :
    Katamaran.RiscvPmp.CFGVer.VerifierRel.itable_rel (w := wlctx R)
      (instrs_of_list cbase L)
      (table_of_list place 0 (List.firstn take (List.skipn skip L))) iota.
  Proof.
    subst head.
    replace (instrs_of_list cbase L)
       with (instrs_of_list cbase
               (List.firstn skip L ++ List.firstn take (List.skipn skip L)
                ++ List.skipn (skip + take) L))
       by (rewrite split_id; reflexivity).
    apply (itable_faith_of_segment (cbase := cbase)
             (off := (4 * N.of_nat skip)%N) place iota
             (List.firstn skip L) (List.firstn take (List.skipn skip L))
             (List.skipn (skip + take) L)).
    - rewrite length_firstn. lia.
    - exact Hp.
    - rewrite split_id. exact Hrep.
  Qed.

  (* ======================================================================== *)
  (* 2. EXIT-TABLE FAITHFULNESS                                               *)
  (* ======================================================================== *)

  (* seg_exitCond_hit / seg_exitCond_inv / seg_exitCond_inv1 live in
     GenSegment.v, next to seg_exitCond itself -- they are pure boolean
     algebra with no Iris in them. *)

  (* One lemma for all 10 call sites, replacing the copied `exit_hit` tactic.
     No per-call offset arithmetic: the caller supplies only
     `Forall (fun t => head <= t) targets`, by `repeat constructor; lia`. *)
  Lemma seg_exit_table_ok {R : LCtx} (place : Term R ty_xlenbits) (iota : Valuation R)
      (ia head : N) (targets : list N)
      (Hle : List.Forall (fun t => N.le head t) targets)
      (* widths ANNOTATED: `bv.of_N ia` alone leaves `bv ?n` and the Inst
         instance cannot be resolved ("Could not find an instance for
         Inst (STerm ty_xlenbits) (RV (bv ?n))"). *)
      (Hp : inst (T := fun Σ => Term Σ ty_xlenbits) place iota
            = ty.SyncVal (bv.add (@bv.of_N xlenbits ia) (@bv.of_N xlenbits head))) :
    Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx R)
      (seg_exitCond ia targets)
      (exits_of_offs place (List.map (fun t => (t - head)%N) targets)) iota.
  Proof.
    apply etable_faith_exits_of_offs
      with (cbase := bv.add (@bv.of_N xlenbits ia) (@bv.of_N xlenbits head));
      [exact Hp |].
    apply List.Forall_forall. intros o Hin.
    apply List.in_map_iff in Hin as [t [Heq Hint]].
    subst o.
    (* the exit address is p+head+(t-head) = p+t *)
    rewrite !bv.of_N_add.
    replace (ia + head + (t - head))%N with (ia + t)%N
      by (rewrite List.Forall_forall in Hle; specialize (Hle t Hint); lia).
    apply seg_exitCond_hit. exact Hint.
  Qed.

  (* ---- ...and the same two obligations with every DECIDABLE side condition
         bundled, so a call site can pass them INLINE as `eq_refl eq_refl Hwf`
         instead of naming a lemma per (contract x table).  On segment G the
         four named lemmas this replaces were 45 lines, of which the only
         non-ritual content was the numbers `135 27 540 1168` and the target
         list -- all five of which the caller had ALREADY handed to
         gen_seg_contract.  Argument order is chosen so that every argument
         before Hok is inferable from the conclusion. --------------------- *)
  Lemma seg_instr_table_ok {R : LCtx} (place : Term R ty_xlenbits)
      (iota : Valuation R) (ia : N) (L : list AnnotInstr) (skip take : nat)
      (head bound : N) (targets : list N)
      (Hok : seg_placement_ok L skip head bound targets = true)
      (Hp : inst (T := fun Σ => Term Σ ty_xlenbits) place iota
            = ty.SyncVal (bv.add (@bv.of_N xlenbits ia) (@bv.of_N xlenbits head)))
      (Hwf : seg_fits_memory ia bound) :
    Katamaran.RiscvPmp.CFGVer.VerifierRel.itable_rel (w := wlctx R)
      (instrs_of_list (@bv.of_N xlenbits ia) L)
      (table_of_list place 0 (List.firstn take (List.skipn skip L))) iota.
  Proof.
    exact (instr_table_ok_at place iota (@bv.of_N xlenbits ia) L skip take head
             (seg_placement_off L skip head bound targets Hok)
             (seg_placement_skip L skip head bound targets Hok)
             Hp
             (seg_fits_rep ia bound L (seg_placement_size L skip head bound targets Hok) Hwf)).
  Qed.

  Lemma seg_exit_table_ok_at {R : LCtx} (place : Term R ty_xlenbits)
      (iota : Valuation R) (ia : N) (L : list AnnotInstr) (skip : nat)
      (head bound : N) (targets : list N)
      (Hok : seg_placement_ok L skip head bound targets = true)
      (Hp : inst (T := fun Σ => Term Σ ty_xlenbits) place iota
            = ty.SyncVal (bv.add (@bv.of_N xlenbits ia) (@bv.of_N xlenbits head))) :
    Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx R)
      (seg_exitCond ia targets)
      (exits_of_offs place (List.map (fun t => (t - head)%N) targets)) iota.
  Proof.
    exact (seg_exit_table_ok place iota ia head targets
             (seg_placement_targets L skip head bound targets Hok) Hp).
  Qed.


  (* ---- A1' : ...and the two table obligations, stated ON the generated
         contract.  With these a hand-cut segment discharges `itable_rel` and
         `etable_rel` exactly the way `loop_runs` does for a loop -- from the
         `seg_placement_ok` boolean and one placement fact -- instead of
         re-spelling gen_seg_contract's internals to reach the `_at` forms. *)
  Section GenSegTables.
    Context {R : LCtx}
      (base : Term R ty_xlenbits)
      (base_a : Term (R ▻ "a"∷ty_xlenbits) ty_xlenbits)
      (ia head : N) (prog : list AnnotInstr) (skip take : nat)
      (targets : list N) (bound : N) (fl : nat) (regs : list reg_spec_rel)
      (extra_pre : Assertion (R ▻ "a"∷ty_xlenbits))
      (post : Assertion (R ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
      (iota : Valuation R)
      (Hok : seg_placement_ok prog skip head bound targets = true)
      (Hp : inst (T := fun Σ => Term Σ ty_xlenbits)
              (cfg_placement (gen_seg_contract base base_a ia head prog skip take
                                targets bound fl regs extra_pre post)) iota
            = ty.SyncVal (bv.add (@bv.of_N xlenbits ia) (@bv.of_N xlenbits head))).

    Lemma gen_seg_instr_table_ok (Hwf : seg_fits_memory ia bound) :
      Katamaran.RiscvPmp.CFGVer.VerifierRel.itable_rel (w := wlctx R)
        (instrs_of_list (@bv.of_N xlenbits ia) prog)
        (table_of_list
           (cfg_placement (gen_seg_contract base base_a ia head prog skip take
                             targets bound fl regs extra_pre post)) 0
           (cfg_instrs (gen_seg_contract base base_a ia head prog skip take
                          targets bound fl regs extra_pre post))) iota.
    Proof.
      exact (seg_instr_table_ok _ iota ia prog skip take head bound targets
               Hok Hp Hwf).
    Qed.

    Lemma gen_seg_exit_table_ok :
      Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx R)
        (cfg_exitCond (gen_seg_contract base base_a ia head prog skip take
                         targets bound fl regs extra_pre post))
        (cfg_exits (gen_seg_contract base base_a ia head prog skip take
                      targets bound fl regs extra_pre post)) iota.
    Proof.
      exact (seg_exit_table_ok_at _ iota ia prog skip head bound targets Hok Hp).
    Qed.
  End GenSegTables.

  (* ======================================================================== *)
  (* 3. THE STEP COMBINATOR                                                   *)
  (* ======================================================================== *)

  (* `cfg_map` is STUCK on an abstract record, so a combinator cannot consume
     ValidCFGVerifierContract directly -- it has to be handed the projected
     form.  `destruct c` unblocks the projections and both sides become
     identical. *)
  Lemma seg_vc {R : LCtx} (c : @CFGVerifierContract R) :
    ValidCFGVerifierContract c ->
    safeE (postprocess (Katamaran.RiscvPmp.CFGVer.Verifier.scfg_verification_condition
      (extend_to_minimal_pre (cfg_precondition c))
      (table_of_list (cfg_placement c) 0 (cfg_instrs c))
      (cfg_exits c) (cfg_fuel c) (cfg_postcondition c) wnil)).
  Proof. destruct c; exact (fun H => H). Qed.

  (* The resources the soundness bridge CONSUMES at entry. *)
  Definition seg_entry {R : LCtx} (c : @CFGVerifierContract R) (iota : Valuation R)
      (a : bv xlenbits) (L : list AnnotInstr) (cbase : bv xlenbits) : iProp Σ :=
    ( asn.interpret (extend_to_minimal_pre (cfg_precondition c))
        (iota.["a"∷ty_xlenbits ↦ SyncVal a])
      ∗ pc ↦ᵣ SyncVal a
      ∗ (bi_exist (fun v => nextpc ↦ᵣ v))
      ∗ Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs
          (ai_instr <$> instrs_of_list cbase L) )%I.

  (* ...and the ones it HANDS BACK at the exit, for the taken exit `an`. *)
  Definition seg_exit {R : LCtx} (c : @CFGVerifierContract R) (iota : Valuation R)
      (a : bv xlenbits) (L : list AnnotInstr) (cbase : bv xlenbits)
      (an : RelVal ty_xlenbits) : iProp Σ :=
    ( ⌜match an with
        | SyncVal v => cfg_exitCond c v = true
        | NonSyncVal _ _ => False
        end⌝
      ∗ pc ↦ᵣ an
      ∗ (bi_exist (fun v => nextpc ↦ᵣ v))
      ∗ Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs
          (ai_instr <$> instrs_of_list cbase L)
      ∗ asn.interpret (cfg_postcondition c)
          ((iota.["a"∷ty_xlenbits ↦ SyncVal a]).["an"∷ty_xlenbits ↦ an]) )%I.

  (* ONE segment execution, with an explicit FRAME.
     `Fr` is what the contract never sees: it is not selected by the soundness
     bridge's `with "[...]"` selector, so it survives untouched into the
     continuation.  That is the entire framing mechanism, and making it a
     parameter is what lets a segment be dropped into the middle of a chain
     without restating the registers and memory it does not touch.

     `a` is a plain bitvector, hence always SyncVal, hence always public -- so
     the bridge's `secLeak a` side condition is discharged here once and never
     appears at a call site.

     Argument ORDER is load-bearing: Pre/Post are implicit (inferred from the
     conclusion) and everything the caller must choose is explicit and early,
     because only IMPLICIT arguments can be passed by name. *)
  Lemma seg_run {R : LCtx} (c : @CFGVerifierContract R) (iota : Valuation R)
    (a : bv xlenbits) (L : list AnnotInstr) (cbase : bv xlenbits) (Fr : iProp Σ)
    {Pre Post : iProp Σ}
    (Hv : ValidCFGVerifierContract c)
    (Hif : Katamaran.RiscvPmp.CFGVer.VerifierRel.itable_rel (w := wlctx R)
             (instrs_of_list cbase L)
             (table_of_list (cfg_placement c) 0 (cfg_instrs c)) iota)
    (Hef : Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx R)
             (cfg_exitCond c) (cfg_exits c) iota)
    (* Every BLOCK CONTRACT in this segment's program is justified -- vacuous
       today, and dischargeable from a segment VC once blocks are real.  See
       cfg_instrs_verified (EndToEnd.v) for why this rather than "no blocks". *)
    (Hbs : forall wds : bv xlenbits -> bv word,
             ⊢ blocksSound wds (instrs_of_list cbase L))
    (HPre  : Pre -∗ Fr ∗ seg_entry c iota a L cbase)
    (HPost : forall an, Fr ∗ seg_exit c iota a L cbase an -∗ Post) :
    Pre -∗ myWP2_loop Post.
  Proof.
    iIntros "HP".
    iDestruct (HPre with "HP") as "(HF & Hpre & Hpc & Hnpc & Hinstrs)".
    iApply (sound_scfg_verification_condition_myWP2
              (seg_vc c Hv) Post Hif Hef
              Hbs
              $! (SyncVal a) with "[Hpre Hpc Hnpc Hinstrs]").
    (* iFrame also closes the `secLeak (SyncVal a)` conjunct. *)
    - iFrame.
    - iIntros (an) "Hex". iApply HPost. iFrame.
  Qed.

  (* ---- SINGLE-EXIT specialisation -----------------------------------------
     A segment with ONE declared target has its exit pc PINNED by the exit
     condition, so all of this can go away at the call site: the `forall an`,
     the `destruct an as [av|..]; [|contradiction]` for SyncVal-vs-NonSyncVal,
     the `unfold <seg>_exitCond`, and the
     `assert (Hav : av = ...) by (destruct (bv.eqb_spec ...); congruence)`.
     Measured across the live compositional files before this existed: 6 + 6 +
     13 occurrences of exactly that ritual.

     `Hec` is `eq_refl` for any contract built by gen_seg_contract with a
     one-element `targets`. *)
  Definition seg_exit_state {R : LCtx} (c : @CFGVerifierContract R) (iota : Valuation R)
      (a : bv xlenbits) (L : list AnnotInstr) (cbase : bv xlenbits)
      (v : bv xlenbits) : iProp Σ :=
    ( pc ↦ᵣ SyncVal v
      ∗ (bi_exist (fun u => nextpc ↦ᵣ u))
      ∗ Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs
          (ai_instr <$> instrs_of_list cbase L)
      ∗ asn.interpret (cfg_postcondition c)
          ((iota.["a"∷ty_xlenbits ↦ SyncVal a]).["an"∷ty_xlenbits ↦ SyncVal v]) )%I.

  Lemma seg_run_single_exit {R : LCtx} (c : @CFGVerifierContract R) (iota : Valuation R)
    (a : bv xlenbits) (L : list AnnotInstr) (cbase : bv xlenbits) (Fr : iProp Σ)
    (ia t : N)
    {Pre Post : iProp Σ}
    (Hec : cfg_exitCond c = seg_exitCond ia [t])
    (Hv : ValidCFGVerifierContract c)
    (Hif : Katamaran.RiscvPmp.CFGVer.VerifierRel.itable_rel (w := wlctx R)
             (instrs_of_list cbase L)
             (table_of_list (cfg_placement c) 0 (cfg_instrs c)) iota)
    (Hef : Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx R)
             (cfg_exitCond c) (cfg_exits c) iota)
    (* Every BLOCK CONTRACT in this segment's program is justified -- vacuous
       today, and dischargeable from a segment VC once blocks are real.  See
       cfg_instrs_verified (EndToEnd.v) for why this rather than "no blocks". *)
    (Hbs : forall wds : bv xlenbits -> bv word,
             ⊢ blocksSound wds (instrs_of_list cbase L))
    (HPre  : Pre -∗ Fr ∗ seg_entry c iota a L cbase)
    (HPost : Fr ∗ seg_exit_state c iota a L cbase (seg_addr ia t) -∗ Post) :
    Pre -∗ myWP2_loop Post.
  Proof.
    apply (seg_run c iota a L cbase Fr Hv Hif Hef Hbs HPre).
    iIntros (an) "H".
    destruct an as [av | a1 a2].
    2:{ iDestruct "H" as "(_ & %Hf & _)". destruct Hf. }
    iDestruct "H" as "(HF & %Hex & Hpc & Hnpc & Hinstrs & Hpost)".
    rewrite Hec in Hex. apply seg_exitCond_inv1 in Hex. subst av.
    iApply HPost. unfold seg_exit_state. iFrame.
  Qed.

  (* ---- WHEN THE DECLARED EXITS EXCEED THE REACHABLE ONES ------------------

     seg_run_single_exit pins the exit pc from the EXIT CONDITION, so it needs a
     one-element target list.  A segment ending in a conditional branch whose
     condition its own precondition decides has more DECLARED exits than
     reachable ones -- muladd's sgL declares the fall-through into the tail
     loop and a branch that skips the loop when the trip count is zero, but
     that count is pinned to 12, so the skip is dead.

     Such a segment can still be composed as if single-exit, provided its
     POSTCONDITION says which exit was taken (`an = <addr>` as a pure
     conjunct).  Then the VC has to prove the other exits unreachable, which
     is where that obligation belongs.  Verified on sgL: adding the equation
     left `solve_param_vc` unchanged.

     `iAssert … as %H` rather than `iDestruct`: the pin is a PURE consequence
     of the postcondition, and iDestruct would consume the postcondition to
     get it. *)
  Lemma seg_run_pinned_exit {R : LCtx} (c : @CFGVerifierContract R)
    (iota : Valuation R) (a : bv xlenbits) (L : list AnnotInstr)
    (cbase : bv xlenbits) (Fr : iProp Σ) (v : bv xlenbits)
    {Pre Post : iProp Σ}
    (Hv : ValidCFGVerifierContract c)
    (Hif : Katamaran.RiscvPmp.CFGVer.VerifierRel.itable_rel (w := wlctx R)
             (instrs_of_list cbase L)
             (table_of_list (cfg_placement c) 0 (cfg_instrs c)) iota)
    (Hef : Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx R)
             (cfg_exitCond c) (cfg_exits c) iota)
    (* Every BLOCK CONTRACT in this segment's program is justified -- vacuous
       today, and dischargeable from a segment VC once blocks are real.  See
       cfg_instrs_verified (EndToEnd.v) for why this rather than "no blocks". *)
    (Hbs : forall wds : bv xlenbits -> bv word,
             ⊢ blocksSound wds (instrs_of_list cbase L))
    (Hpin : forall an : RelVal ty_xlenbits,
              asn.interpret (cfg_postcondition c)
                ((iota.["a"∷ty_xlenbits ↦ SyncVal a]).["an"∷ty_xlenbits ↦ an])
              ⊢ ⌜an = ty.SyncVal v⌝)
    (HPre  : Pre -∗ Fr ∗ seg_entry c iota a L cbase)
    (HPost : Fr ∗ seg_exit_state c iota a L cbase v -∗ Post) :
    Pre -∗ myWP2_loop Post.
  Proof.
    apply (seg_run c iota a L cbase Fr Hv Hif Hef Hbs HPre).
    iIntros (an) "(HF & %Hex & Hpc & Hnpc & Hinstrs & Hpost)".
    iAssert (⌜an = ty.SyncVal v⌝)%I as %Han; [ iApply (Hpin an); iExact "Hpost" |].
    subst an.
    iApply HPost. unfold seg_exit_state. iFrame.
  Qed.

  (* SEQUENTIAL composition: run one segment, then continue.  This is the
     shape the STRAIGHT-LINE cuts need -- nine of muladd's fourteen segments,
     i.e. most of the remaining work -- and it is what the hand-written tail
     spelled out per link as linkN / linkFN.  Trivial on top of
     myWP2_loop_bind, but it is exactly the kind of five-line wrapper that
     otherwise gets re-derived at every call site (which is how the 21 copies
     of the register builder happened). *)
  Lemma seg_then (Pre Mid Post : iProp Σ)
    (H1 : Pre -∗ myWP2_loop Mid)
    (H2 : Mid -∗ myWP2_loop Post) :
    Pre -∗ myWP2_loop Post.
  Proof.
    iIntros "H". iApply (myWP2_loop_bind Mid Post with "[] [H]").
    - iApply H2.
    - iApply H1. iExact "H".
  Qed.

  (* MONOTONICITY.  This did not exist, and its absence was recorded as a
     design constraint -- "myWP2_loop has no monotonicity lemma, so a per-trip
     lemma must take Post as a PARAMETER and reach the trip-indexed invariant
     from inside the step".  That was wrong: `myWP2_loop` is a monad in its
     ExitCond, `exitCondImpliesMyWP2_loop` is its unit and `myWP2_loop_bind`
     its bind, and mono is the two-line corollary.  A per-trip lemma can now
     say what it means -- `Inv (m+1) -∗ myWP2_loop (Inv m)` -- and be weakened
     afterwards. *)
  Lemma myWP2_loop_mono (P Q : iProp Σ) (H : P -∗ Q) :
    myWP2_loop P -∗ myWP2_loop Q.
  Proof.
    iApply myWP2_loop_bind. iIntros "HP".
    iApply exitCondImpliesMyWP2_loop. iApply H. iExact "HP".
  Qed.

  (* ======================================================================== *)
  (* 4. THE LOOP COMBINATOR                                                   *)
  (* ======================================================================== *)

  (* myWP2_loop_induction, packaged so the loop's EXIT can hand off to an
     arbitrary continuation instead of terminating the proof.  That is the
     difference between a loop lemma usable mid-function and one usable only
     for the last segment: muladd's hand-written `am_loop` hardwired its
     conclusion to the final segment's exit condition and so could not be
     reused for a loop with anything after it. *)
  Lemma seg_loop (Inv : nat -> iProp Σ) (Out Post : iProp Σ)
    (Hstep : forall n, Inv (S n) -∗ myWP2_loop (Inv n))
    (Hexit : Inv 0 -∗ myWP2_loop Out)
    (Hcont : Out -∗ myWP2_loop Post) :
    forall n, Inv n -∗ myWP2_loop Post.
  Proof.
    apply (myWP2_loop_induction Inv Post).
    - exact Hstep.
    - iIntros "H". iApply (myWP2_loop_bind Out Post with "[] [H]").
      + iApply Hcont.
      + iApply Hexit. iExact "H".
  Qed.

  (* ======================================================================== *)
  (* 5. CROSSING A CUT: WHEN THE VALUATION CHANGES                            *)
  (* ======================================================================== *)

  (* A cut hands the next segment a postcondition interpreted at the valuation
     the PREVIOUS segment ran under -- extended with "an", and generally with a
     different counter -- while the next segment's precondition wants its own
     valuation.  MEASURED 2026-09-10, on segment G's body cut: `iFrame` DOES
     match the generated register block (0.6 s) and `minimal_pre` (0.8 s)
     across that change on its own, because for those the two iProps are
     convertible.  So do NOT reach for a lemma there; the earlier claim that
     iFrame refuses them was wrong, and the two lemmas written for it
     (`gen_regs_at_inst`, `minimal_pre_inst`) were deleted unused.

     What iFrame genuinely CANNOT cross is a register whose VALUE changed --
     the thing a segment is for.  That is this lemma, and its premise is
     exactly the arithmetic the segment did.

     PREFER NOT TO NEED IT (2026-09-11).  A postcondition that BINDS a fresh
     variable and states the change as a PURE equation --
     `asn.exist "k2" (T4 |-> term_var "k2" ∗ formula (k2 = dvdec k) ∗ …)` --
     keeps the spatial half DATA, so it frames like any other cut, and reduces
     the arithmetic to `destruct`/`subst`/`rewrite` on a hypothesis. Measured on
     segment G: the `asn_regidx_pts_inst` rewrite and BOTH written-out
     valuations disappear (ZZMladDvLoop2.v 202 -> 196), the VC still discharges,
     and this lemma is now referenced by NO call site. Keep it as the fallback
     for a post that cannot be restructured; reach for the fresh variable
     first. *)
  Lemma asn_regidx_pts_inst {R1 R2 : LCtx} (r : RegIdx)
    (t1 : Term R1 ty_xlenbits) (t2 : Term R2 ty_xlenbits)
    (i1 : Valuation R1) (i2 : Valuation R2)
    (H : inst (T := fun Σ => Term Σ ty_xlenbits) t1 i1
         = inst (T := fun Σ => Term Σ ty_xlenbits) t2 i2) :
    asn.interpret (asn_regidx_pts r t1) i1 ⊣⊢ asn.interpret (asn_regidx_pts r t2) i2.
  Proof.
    unfold asn_regidx_pts.
    destruct (reg_convert r); cbn; [rewrite H |]; reflexivity.
  Qed.

  (* PERFORMANCE, and it is not a detail: SPLIT THE GOAL BEFORE FRAMING.
     `iFrame` searches every conjunct of the goal for each named hypothesis,
     so framing the ambient resources (F / pc / nextpc / the instruction
     store) while the generated blocks are still in the goal costs 46-66 s on
     segment G -- and framing them ONE at a time is worse still (`iFrame "Hpc"`
     alone did not finish in 300 s).  Peel the ambient half off first with
     `iSplitR "HF Hpc Hnpc Hinstrs"; [| iFrame]` and the same work is 0.4 s.
     Measured on ZZMladDvLoop2.v: 47.8 s -> 28.5 s for the whole file. *)


  (* ======================================================================== *)
  (* 6. COUNTED LOOPS                                                         *)
  (* ======================================================================== *)

  (* Exit-table faithfulness for a RE-BASED segment: the contract is stated at
     its own entry address, so head is 0 and the targets are already relative.
     seg_exit_table_ok's head-shifted form does not apply definitionally
     (`t - 0` and `q +b of_N 0` are both stuck on a symbolic argument). *)
  Lemma seg_exit_table_ok_head {R : LCtx} (place : Term R ty_xlenbits)
      (iota : Valuation R) (iq : N) (targets : list N)
      (Hp : inst (T := fun Σ => Term Σ ty_xlenbits) place iota
            = ty.SyncVal (@bv.of_N xlenbits iq)) :
    Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx R)
      (seg_exitCond iq targets) (exits_of_offs place targets) iota.
  Proof.
    apply etable_faith_exits_of_offs with (cbase := @bv.of_N xlenbits iq);
      [exact Hp |].
    (* NB: offs IS targets here -- there is no `map (.- head)` to invert, unlike
       seg_exit_table_ok.  Copying its `in_map_iff` line does not typecheck. *)
    apply List.Forall_forall. intros o Hin.
    now apply seg_exitCond_hit0.
  Qed.

  (* THE LOOP INVARIANT.  Generated: the counter pinned at `ls_at n` (via the
     caller's valuation family), the frame, and the four ambient resources
     every segment carries.

     `iotaf` is a FAMILY of valuations, one per trip: the context is the
     loop's own, so only the caller knows how its variables move.  For a
     counted loop with a fixed footprint only the counter changes; for a loop
     walking a pointer, the pointer's variable moves too, and THAT is how a
     sliding footprint is expressed -- the contract stays trip-independent
     (it is verified once and used at every trip), while the invariant
     instantiates the moving variables per trip.

     `Fr` is what the loop never touches, and it is opaque.

     `P` is a pure side condition carried per trip.  It is NOT decoration:
     a counter's no-wrap bound (`ls_at n + 1 < 2^32`) holds only below 2^32,
     while seg_loop's step is quantified over ALL n, so without somewhere to
     put it the step is unprovable.  The hand-written dvInvN carried exactly
     this.  The caller also supplies P (S n) -> P n, which is immediate for a
     bound that shrinks with the counter. *)
  Definition loop_invariant {R : LCtx} (ls : LoopSpec R)
      (iotaf : nat -> Valuation R) (q : bv xlenbits)
      (Fr : nat -> iProp Σ) (Instrs : iProp Σ) (P : nat -> Prop) (n : nat)
      : iProp Σ :=
    ( bi_pure (P n)
      ∗ asn.interpret (gen_loop_at_head ls)
        ((iotaf n).["a"∷ty_xlenbits ↦ ty.SyncVal q])
      ∗ Fr n ∗ pc ↦ᵣ ty.SyncVal q
      ∗ (bi_exist (fun v => nextpc ↦ᵣ v))
      ∗ Instrs )%I.

  (* ---- ONE TRIP ---------------------------------------------------------- *)

  (* ---- THE PLACEMENT BUNDLE (C5) ------------------------------------------

     Six of loop_runs's twenty arguments said nothing about the loop and
     everything about WHERE THE HOST PROGRAM PUT IT.  They travel together and
     are proved together, so they are one record.  `place_body_table_ok`/`place_exit_table_ok` stay two
     fields rather than one because seg_placement_ok is per-target: the back edge and the
     fall-through are different targets. *)
  Record LoopPlace {R : LCtx} (ls : LoopSpec R) : Type := MkLoopPlace
    { place_prog_base    : N                (* the HOST program's base address       *)
    ; place_prog_extent : N                (* the HOST program's extent             *)
    ; place_head_eq     : @bv.of_N xlenbits (loop_head_addr ls)
                 = bv.add (@bv.of_N xlenbits place_prog_base)
                     (@bv.of_N xlenbits (4 * N.of_nat (loop_first_instr ls)))
    ; place_fits_memory    : seg_fits_memory place_prog_base place_prog_extent
    (* NOTE THE TARGET CONVENTION, and that it was WRONG until 2026-09-14.
       These lists used to read `[0%N]` and `[loop_exit_off ls]` -- the loop's own
       head-relative offsets, which is the convention its EXIT table uses.
       But seg_placement_ok's last conjunct is `forallb (fun t => head <=? t) targets`
       with head = 4*skip, so `1056 <=? 0` made the field UNSATISFIABLE for
       every loop at a nonzero offset, and every loop theorem that took it as
       a hypothesis was vacuous.  seg_instr_table_ok -- the only consumer -- uses
       only seg_placement_ok's offset/skip/size parts and ignores the targets, so the
       fix is simply to state them program-relative. *)
    ; place_body_table_ok    : seg_placement_ok (loop_prog ls) (loop_first_instr ls)
                   (4 * N.of_nat (loop_first_instr ls))%N place_prog_extent
                   [(4 * N.of_nat (loop_first_instr ls) + 0)%N] = true
    ; place_exit_table_ok   : seg_placement_ok (loop_prog ls) (loop_first_instr ls)
                   (4 * N.of_nat (loop_first_instr ls))%N place_prog_extent
                   [(4 * N.of_nat (loop_first_instr ls) + loop_exit_off ls)%N] = true }.
  (* `#[global]`, not bare `Arguments`: inside a Section an Arguments command
     is section-LOCAL and silently reverts at `End`, so callers saw R and ls
     as explicit and record syntax elaborated the fields before it could learn
     `ls` from the ascribed type. *)
  #[global] Arguments MkLoopPlace {R ls}.
  #[global] Arguments place_prog_base {R ls}.    #[global] Arguments place_prog_extent {R ls}.
  #[global] Arguments place_head_eq {R ls}.     #[global] Arguments place_fits_memory {R ls}.
  #[global] Arguments place_body_table_ok {R ls}.    #[global] Arguments place_exit_table_ok {R ls}.

  Definition loop_instr_block {R : LCtx} (ls : LoopSpec R) (pl : LoopPlace ls) : iProp Σ :=
    Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs
      (ai_instr <$> instrs_of_list (@bv.of_N xlenbits (place_prog_base pl)) (loop_prog ls)).

  (* ---- ONE TRIP, EITHER KIND (A3) ----------------------------------------

     loop_body_trip and loop_final_trip used to be two ~40-line lemmas differing only in
     the guard, the target, the valuation and the continuation -- everything
     else, including the two faith arguments and the whole HPre bullet, was
     duplicated verbatim.  Since A3 made a loop's contract an ordinary
     gen_seg_contract, they are ONE lemma parameterised by exactly those four
     things, and both are corollaries below.

     What the caller supplies is the loop's own content:
       Hpl : the valuation pins the code base (reflexivity in practice, since
             a caller's iota maps "q" to a literal).  The "a"-context version
             is no longer a second premise -- C4 made it follow by
             inst_loop_base_pre;
       Hg  : the branch decision holds at this trip -- one arithmetic fact;
       HOut: what to do with the segment's exit state. *)
  Lemma loop_one_trip {R : LCtx} (ls : LoopSpec R) (pl : LoopPlace ls)
      (g : Term (R ▻ "a"∷ty_xlenbits) ty_xlenbits -> Formula (R ▻ "a"∷ty_xlenbits))
      (target : N)
      (post : Assertion (R ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
      (i : Valuation R) (F Out : iProp Σ)
      (* program-relative, matching place_body_table_ok / place_exit_table_ok -- see the note there *)
      (Hokt : seg_placement_ok (loop_prog ls) (loop_first_instr ls)
                (4 * N.of_nat (loop_first_instr ls))%N (place_prog_extent pl)
                [(4 * N.of_nat (loop_first_instr ls) + target)%N] = true)
      (Hv  : ValidCFGVerifierContract (gen_loop_contract ls g target post))
      (* Every block contract in this loop's program is justified.  Vacuous
         today (blocksSound_of_none); the premise exists because the lemma is
         generic in the program.  See cfg_instrs_verified (EndToEnd.v). *)
      (Hbs : forall wds : bv xlenbits -> bv word,
               ⊢ blocksSound wds (instrs_of_list
                   (@bv.of_N xlenbits (place_prog_base pl)) (loop_prog ls)))
      (Hpl : inst (T := fun Σ => Term Σ ty_xlenbits) (loop_base ls) i
             = ty.SyncVal (@bv.of_N xlenbits (loop_head_addr ls)))
      (Hg  : instprop (g (counter_after_step (loop_counter_step ls) (loop_counter_pre ls)))
               (i.["a"∷ty_xlenbits ↦ ty.SyncVal (@bv.of_N xlenbits (loop_head_addr ls))]))
      (HOut : F ∗ seg_exit_state (gen_loop_contract ls g target post) i
                    (@bv.of_N xlenbits (loop_head_addr ls)) (loop_prog ls)
                    (@bv.of_N xlenbits (place_prog_base pl))
                    (seg_addr (loop_head_addr ls) target)
              -∗ Out) :
    asn.interpret (gen_loop_at_head ls)
      (i.["a"∷ty_xlenbits ↦ ty.SyncVal (@bv.of_N xlenbits (loop_head_addr ls))])
    ∗ F ∗ pc ↦ᵣ ty.SyncVal (@bv.of_N xlenbits (loop_head_addr ls))
    ∗ (bi_exist (fun v => nextpc ↦ᵣ v))
    ∗ loop_instr_block ls pl
    -∗ myWP2_loop Out.
  Proof.
    assert (Hplace : inst (T := fun Σ => Term Σ ty_xlenbits)
                       (cfg_placement (gen_loop_contract ls g target post)) i
                     = ty.SyncVal (@bv.of_N xlenbits (loop_head_addr ls))).
    { rewrite gen_loop_place. exact (inst_addr_plus0 _ _ _ Hpl). }
    assert (Hif : Katamaran.RiscvPmp.CFGVer.VerifierRel.itable_rel (w := wlctx R)
                    (instrs_of_list (@bv.of_N xlenbits (place_prog_base pl)) (loop_prog ls))
                    (table_of_list (cfg_placement (gen_loop_contract ls g target post))
                       0 (cfg_instrs (gen_loop_contract ls g target post))) i).
    { rewrite gen_loop_instrs.
      (* the placement premise is BUILT, not tactic-proved: as an `ltac:(...)`
         it ran before unification had fixed seg_instr_table_ok's `place`, so
         `rewrite Hplace` found nothing to rewrite. *)
      exact (seg_instr_table_ok
               (cfg_placement (gen_loop_contract ls g target post)) i
               (place_prog_base pl) (loop_prog ls) (loop_first_instr ls) (loop_num_instrs ls)
               (4 * N.of_nat (loop_first_instr ls))%N (place_prog_extent pl)
               [(4 * N.of_nat (loop_first_instr ls) + target)%N] Hokt
               (eq_trans Hplace (f_equal ty.SyncVal (place_head_eq pl))) (place_fits_memory pl)). }
    assert (Hef : Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx R)
                    (cfg_exitCond (gen_loop_contract ls g target post))
                    (cfg_exits (gen_loop_contract ls g target post)) i).
    { rewrite gen_loop_exits. rewrite gen_loop_exitCond.
      exact (seg_exit_table_ok_head
               (term_binop bop.bvadd (loop_base ls) (term_val ty_xlenbits (bv.of_N 0)))
               i (loop_head_addr ls) [target] (inst_addr_plus0 _ _ _ Hpl)). }
    iIntros "H".
    iApply (seg_run_single_exit (gen_loop_contract ls g target post) i
             (@bv.of_N xlenbits (loop_head_addr ls)) (loop_prog ls)
             (@bv.of_N xlenbits (place_prog_base pl)) F (loop_head_addr ls) target
             (gen_loop_exitCond ls g target post) Hv Hif Hef Hbs with "H").
    - (* HPre: the invariant IS the precondition minus the branch decision and
         the pc equation, at the SAME valuation.  Since A3 the two orders
         differ (gen_seg_contract puts the code bound second and the registers
         last), so this is an iFrame over the pieces rather than one iFrame of
         a single conjunct. *)
      unfold seg_entry, extend_to_minimal_pre, loop_instr_block,
        gen_loop_at_head, gen_loop_state, gen_loop_frame_pre, loop_all_bounds_pre.
      iIntros "(H & HF & Hpc & Hnpc & Hinstrs)".
      iSplitL "HF"; [ iFrame |].
      iSplitR "Hpc Hnpc Hinstrs"; [| iFrame].
      cbn [cfg_precondition gen_loop_contract gen_seg_contract gen_loop_contract_pre
           gen_loop_bounds List.fold_right asn.interpret].
      unfold asn_pc_eq; cbn [asn.interpret].
      unfold gen_base_bound.
      iDestruct "H" as "((Hk & Hsl & (Hbq & Hbs) & Hregs & Hex) & Hmin)".
      iFrame "Hk Hsl Hbq Hbs Hregs Hex Hmin".
      (* what is left is the two PURE conjuncts the invariant does not carry:
         the pc equation (which is where the `+ 0` A3 introduced has to be
         discharged) and the branch decision. *)
      iSplit; [iPureIntro | iSplit; [iPureIntro; exact Hg | done]].
      (* `-[loop_base_pre]` for the same reason the latch lemmas need it: with ls a
         variable, cbn unfolds the C4 accessor and inst_loop_base_pre stops matching. *)
      cbn -[loop_base_pre]. split; [| exact I].
      rewrite (eq_trans (inst_loop_base_pre ls i _) Hpl). cbn.
      now rewrite bv.add_zero_r.
    - exact HOut.
  Qed.

  (* ---- THE TWO KINDS, AS COROLLARIES --------------------------------------

     The BODY trip: guard holds, back edge to offset 0, and the continuation is
     the next trip's invariant.  `Htrans` is where a sliding footprint lives:
     the contract is trip-independent, and iotaf moves the pointers. *)
  Lemma loop_body_trip {R : LCtx} (ls : LoopSpec R) (pl : LoopPlace ls)
      (Fr : nat -> iProp Σ) (iotaf : nat -> Valuation R) (P : nat -> Prop)
      (n : nat)
      (HPm : P (S n) -> P n)
      (Hv  : ValidCFGVerifierContract (loop_body_contract ls))
      (* Vacuous today; see loop_one_trip. *)
      (Hbs : forall wds : bv xlenbits -> bv word,
               ⊢ blocksSound wds (instrs_of_list
                   (@bv.of_N xlenbits (place_prog_base pl)) (loop_prog ls)))
      (Hpl : inst (T := fun Σ => Term Σ ty_xlenbits) (loop_base ls) (iotaf (S n))
             = ty.SyncVal (@bv.of_N xlenbits (loop_head_addr ls)))
      (Hg  : P (S n) ->
             instprop (loop_guard ls (counter_after_step (loop_counter_step ls) (loop_counter_pre ls)))
               ((iotaf (S n)).["a"∷ty_xlenbits
                  ↦ ty.SyncVal (@bv.of_N xlenbits (loop_head_addr ls))]))
      (Htrans : P (S n) ->
         asn.interpret (cfg_postcondition (loop_body_contract ls))
           (((iotaf (S n)).["a"∷ty_xlenbits
               ↦ ty.SyncVal (@bv.of_N xlenbits (loop_head_addr ls))])
              .["an"∷ty_xlenbits ↦ ty.SyncVal (@bv.of_N xlenbits (loop_head_addr ls))])
         ∗ Fr (S n)
         ⊢ asn.interpret (gen_loop_at_head ls)
             ((iotaf n).["a"∷ty_xlenbits
                ↦ ty.SyncVal (@bv.of_N xlenbits (loop_head_addr ls))])
           ∗ Fr n) :
    loop_invariant ls iotaf (@bv.of_N xlenbits (loop_head_addr ls)) Fr (loop_instr_block ls pl) P (S n)
    -∗ myWP2_loop (loop_invariant ls iotaf (@bv.of_N xlenbits (loop_head_addr ls)) Fr
                     (loop_instr_block ls pl) P n).
  Proof.
    (* Peel the pure side condition FIRST: the two bullets of loop_one_trip are
       separate goals, so an iIntros inside HOut would not scope over it, and
       HOut is where P n has to be re-established. *)
    unfold loop_invariant at 1.
    iIntros "(%HP & H)".
    iApply (loop_one_trip ls pl (loop_guard ls) 0%N (gen_loop_contract_post ls) (iotaf (S n))
             (Fr (S n)) _ (place_body_table_ok pl) Hv Hbs Hpl (Hg HP) with "H").
    unfold loop_invariant, seg_exit_state.
    rewrite seg_addr_0.
    iIntros "(HF & Hpc & Hnpc & Hinstrs & Hpost)".
    iSplit; [iPureIntro; exact (HPm HP) |].
    iDestruct ((Htrans HP) with "[$Hpost $HF]") as "(Hwin & HFn)".
    iFrame.
  Qed.

  (* The EXIT trip: the exit guard holds, the target is the fall-through, and
     `Out` is whatever the caller hands the next segment -- the cut out of the
     loop, and genuine specification. *)
  Lemma loop_final_trip {R : LCtx} (ls : LoopSpec R)
      (post : Assertion (R ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
      (pl : LoopPlace ls) (Fr : nat -> iProp Σ) (Out : iProp Σ)
      (iotaf : nat -> Valuation R)
      (P : nat -> Prop) (HP0 : P 0)
      (Hv  : ValidCFGVerifierContract (loop_final_contract ls post))
      (* Vacuous today; see loop_one_trip. *)
      (Hbs : forall wds : bv xlenbits -> bv word,
               ⊢ blocksSound wds (instrs_of_list
                   (@bv.of_N xlenbits (place_prog_base pl)) (loop_prog ls)))
      (Hpl : inst (T := fun Σ => Term Σ ty_xlenbits) (loop_base ls) (iotaf 0)
             = ty.SyncVal (@bv.of_N xlenbits (loop_head_addr ls)))
      (Hg  : instprop (loop_exit_guard ls (counter_after_step (loop_counter_step ls) (loop_counter_pre ls)))
               ((iotaf 0).["a"∷ty_xlenbits
                  ↦ ty.SyncVal (@bv.of_N xlenbits (loop_head_addr ls))]))
      (HOut : Fr 0 ∗ seg_exit_state (loop_final_contract ls post) (iotaf 0)
                     (@bv.of_N xlenbits (loop_head_addr ls)) (loop_prog ls)
                     (@bv.of_N xlenbits (place_prog_base pl))
                     (seg_addr (loop_head_addr ls) (loop_exit_off ls))
              -∗ Out) :
    loop_invariant ls iotaf (@bv.of_N xlenbits (loop_head_addr ls)) Fr (loop_instr_block ls pl) P 0
    -∗ myWP2_loop Out.
  Proof.
    unfold loop_invariant at 1.
    iIntros "(%HP & H)".
    iApply (loop_one_trip ls pl (loop_exit_guard ls) (loop_exit_off ls) post (iotaf 0)
             (Fr 0) Out (place_exit_table_ok pl) Hv Hbs Hpl Hg HOut with "H").
  Qed.

  (* ---- ENTERING A LOOP (D3) ----------------------------------------------

     The mirror of loop_final_trip.  loop_final_trip turns the loop's last trip into a
     `seg_exit_state` for whatever follows; this turns a PREDECESSOR's
     `seg_exit_state` into the loop's invariant, which is what `seg_then` needs to
     put a segment and a loop in sequence.  Until this existed, nothing in the
     tree entered a loop at all -- `seg_exit_state` appeared only as a loop's
     output.

     NOTE THE TWO CONTEXTS.  The predecessor lives at its own S (muladd's
     segments are all at `["p"]`) while the loop lives at R (its pointers and
     its code base).  They are related only through the two VALUATIONS, j and
     `iota n`, which is why the assertion-level obligation below is stated
     across both and cannot be a re-indexing the way the back edge is. *)
  Definition loop_entry_obligation {R S : LCtx} (ls : LoopSpec R)
      (c : @CFGVerifierContract S) (j : Valuation S) (a q : bv xlenbits)
      (iota : nat -> Valuation R) (Fin : iProp Σ) (Fr : nat -> iProp Σ)
      (n : nat) : Prop :=
    asn.interpret (cfg_postcondition c)
      ((j.["a"∷ty_xlenbits ↦ ty.SyncVal a]).["an"∷ty_xlenbits ↦ ty.SyncVal q])
    ∗ Fin
    ⊢ asn.interpret (gen_loop_at_head ls)
        ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])
      ∗ Fr n.

  (* `v` is taken as a parameter with a proof rather than fixed at
     `bv.of_N (loop_head_addr ls)`, because what a caller HAS is whatever seg_run_single_exit
     handed back -- `seg_addr ia t` for the predecessor's own base and target.
     Hv is then `f_equal; lia`, or reflexivity when both are literals. *)
  Lemma loop_enter_from_seg {R S : LCtx} (ls : LoopSpec R) (pl : LoopPlace ls)
      (c : @CFGVerifierContract S) (j : Valuation S) (a v : bv xlenbits)
      (iota : nat -> Valuation R) (Fin : iProp Σ) (Fr : nat -> iProp Σ)
      (P : nat -> Prop) (n : nat)
      (Hv : v = @bv.of_N xlenbits (loop_head_addr ls))
      (HP : P n)
      (Hent : loop_entry_obligation ls c j a (@bv.of_N xlenbits (loop_head_addr ls)) iota Fin Fr n) :
    Fin ∗ seg_exit_state c j a (loop_prog ls) (@bv.of_N xlenbits (place_prog_base pl)) v
    ⊢ loop_invariant ls iota (@bv.of_N xlenbits (loop_head_addr ls)) Fr (loop_instr_block ls pl) P n.
  Proof.
    subst v. unfold seg_exit_state, loop_invariant, loop_instr_block.
    iIntros "(HF & Hpc & Hnpc & Hinstrs & Hpost)".
    iSplit; [iPureIntro; exact HP |].
    iDestruct (Hent with "[$Hpost $HF]") as "(Hwin & HFn)".
    iFrame.
  Qed.

  (* ---- THE ENTRY OBLIGATION, DISCHARGED BY SUBSTITUTION -------------------

     The first attempt at an entry proof reconciled a hand-written cut
     assertion with the loop's invariant resource by resource: fifteen
     cross-context `iApply`s of loop_reg_shift / loop_cell_shift.  It did not
     finish in four and a half minutes, and the diagnosis was that the whole
     activity is at the wrong layer.  A cut assertion is determined by its
     SUCCESSOR's precondition (PLAN-loop-automation F2), so it should be
     GENERATED from it -- and then the obligation is not a separation-logic
     proof at all but a VALUATION EQUALITY.

     One substitution does both jobs at once: `ζ` carries the predecessor's
     context S to the loop's R (muladd's segments live at ["p"], the tail loop
     at ["q";"ap";"bp";"e"]) AND absorbs the extra "an" binder, so no separate
     shifted copy of gen_loop_at_head is needed.  `Fin` is `Fr n` because with the
     post generated there is nothing left to transfer.

     Hval is `reflexivity` / `vm_compute` whenever ζ and the valuations are
     concrete, which they are at every call site.

     `Rest` is NOT optional and not a generalisation for its own sake: a
     predecessor's postcondition has to return everything its PREcondition
     consumed, or the executor drops it (sgL owns ten data cells and hands the
     loop two).  So the cut assertion is `successor's precondition ∗ frame`,
     and the frame is exactly what the loop never touches.  Pass `⊤%asn` when
     there is none. *)
  (* The `Subst Assertion` instance lives inside `Module Import asn` and is
     not in scope here, so `subst` on an Assertion does not resolve. *)
  #[local] Existing Instance asn.sub_assertion.

  Lemma loop_entry_by_subst {R S : LCtx} (ls : LoopSpec R)
      (c : @CFGVerifierContract S)
      (ζ : Sub (R ▻ "a"∷ty_xlenbits)
               (S ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
      (Rest : Assertion (S ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
      (j : Valuation S) (a q : bv xlenbits)
      (iota : nat -> Valuation R) (Fin : iProp Σ) (Fr : nat -> iProp Σ) (n : nat)
      (* `asn.sep`, not `_ ∗ _`: this file does not import asn.notations,
         and the iProp `∗` it does have is a different scope. *)
      (Hpost : cfg_postcondition c = asn.sep (subst (gen_loop_at_head ls) ζ) Rest)
      (Hval : inst ζ (((j.["a"∷ty_xlenbits ↦ ty.SyncVal a])
                         .["an"∷ty_xlenbits ↦ ty.SyncVal q]))
              = (iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])
      (Hfr : asn.interpret Rest ((j.["a"∷ty_xlenbits ↦ ty.SyncVal a])
                                   .["an"∷ty_xlenbits ↦ ty.SyncVal q]) ∗ Fin
             ⊢ Fr n) :
    loop_entry_obligation ls c j a q iota Fin Fr n.
  Proof.
    unfold loop_entry_obligation. rewrite Hpost.
    cbn [asn.interpret]. rewrite asn.interpret_subst. rewrite Hval.
    iIntros "((Hwin & Hrest) & HF)". iFrame "Hwin".
    iApply Hfr. iFrame.
  Qed.

  (* Segment THEN loop, in one step: run the predecessor, land in the loop,
     run the loop.  This is `seg_then` with the cut assertion filled in, and it
     is the shape a chain into a loop actually wants. *)
  Lemma seg_then_loop {R S : LCtx} (ls : LoopSpec R) (pl : LoopPlace ls)
      (c : @CFGVerifierContract S) (j : Valuation S) (a v : bv xlenbits)
      (iota : nat -> Valuation R) (Fin : iProp Σ) (Fr : nat -> iProp Σ)
      (P : nat -> Prop) (n : nat) (Pre Post : iProp Σ)
      (Hv : v = @bv.of_N xlenbits (loop_head_addr ls))
      (HP : P n)
      (Hent : loop_entry_obligation ls c j a (@bv.of_N xlenbits (loop_head_addr ls)) iota Fin Fr n)
      (Hpred : Pre -∗ myWP2_loop
                 (Fin ∗ seg_exit_state c j a (loop_prog ls)
                         (@bv.of_N xlenbits (place_prog_base pl)) v))
      (Hloop : loop_invariant ls iota (@bv.of_N xlenbits (loop_head_addr ls)) Fr
                 (loop_instr_block ls pl) P n
               -∗ myWP2_loop Post) :
    Pre -∗ myWP2_loop Post.
  Proof.
    apply (seg_then Pre (Fin ∗ seg_exit_state c j a (loop_prog ls)
                          (@bv.of_N xlenbits (place_prog_base pl)) v) Post Hpred).
    iIntros "H".
    iApply Hloop.
    iApply (loop_enter_from_seg ls pl c j a v iota Fin Fr P n Hv HP Hent).
    iExact "H".
  Qed.


  (* ---- THE WHOLE LOOP ----------------------------------------------------- *)

  (* seg_loop, instantiated.  Given a step for every trip and an exit, the
     loop runs to its continuation. *)
  Lemma loop_by_induction {R : LCtx} (ls : LoopSpec R) (pl : LoopPlace ls)
      (Fr : nat -> iProp Σ) (Out Post : iProp Σ)
      (iotaf : nat -> Valuation R) (P : nat -> Prop)
      (Hstep : forall n,
         loop_invariant ls iotaf (@bv.of_N xlenbits (loop_head_addr ls)) Fr
           (loop_instr_block ls pl)
           P (S n)
         -∗ myWP2_loop (loop_invariant ls iotaf (@bv.of_N xlenbits (loop_head_addr ls)) Fr
              (loop_instr_block ls pl) P n))
      (Hexit :
         loop_invariant ls iotaf (@bv.of_N xlenbits (loop_head_addr ls)) Fr
           (loop_instr_block ls pl)
           P 0
         -∗ myWP2_loop Out)
      (Hcont : Out -∗ myWP2_loop Post) :
    forall n,
      loop_invariant ls iotaf (@bv.of_N xlenbits (loop_head_addr ls)) Fr
        (loop_instr_block ls pl)
        P n
      -∗ myWP2_loop Post.
  Proof. apply (seg_loop _ Out Post Hstep Hexit Hcont). Qed.

  (* ---- THE TRANSFER, GENERICALLY ----------------------------------------

     `loop_body_trip`'s `Htrans` -- one trip's postcondition establishes the next
     trip's invariant -- is the same four moves for every counted loop: open
     the post's counter existential, kill the NonSyncVal branch (the counter
     is public, so `secLeak` refutes it), rewrite the machine's step, and
     frame.  Only two things are the loop's own, and they are the hypotheses:

       Hstep  : the counter's arithmetic (bv_of_N_wrap_dec for a decrement,
                eq_sym (bv.of_N_add ..) for an increment);
       Hframe : the frame at trip S n implies the frame at trip n.  For a
                loop whose footprint does not move this is `iIntros; iFrame`;
                for a pointer walk it is where the SLIDING WINDOW lives, and
                it is genuine specification.

     Hk/Hkn read the counter off the two valuations.  Hk quantifies over the
     existential's witness because `loop_counter_post_ex` sits under the post's binder;
     in practice it does not mention "c" and the caller passes `fun _ => _`. *)
  Lemma loop_counter_transfer {R : LCtx} (ls : LoopSpec R) (iS iN : Valuation R)
    (q : bv xlenbits) (kv w : N) (FS Fn : iProp Σ)
    (Hk : forall x : ty.RelVal ty_xlenbits,
            inst (T := fun Σ => Term Σ ty_xlenbits) (loop_counter_post_ex ls)
              (((iS.["a"∷ty_xlenbits ↦ ty.SyncVal q]).["an"∷ty_xlenbits ↦ ty.SyncVal q])
                 .["c"∷ty_xlenbits ↦ x])
            = ty.SyncVal (@bv.of_N xlenbits kv))
    (Hstep : bv.add (@bv.of_N xlenbits kv) (loop_counter_step ls) = @bv.of_N xlenbits w)
    (Hkn : inst (T := fun Σ => Term Σ ty_xlenbits) (loop_counter_pre ls)
             (iN.["a"∷ty_xlenbits ↦ ty.SyncVal q])
           = ty.SyncVal (@bv.of_N xlenbits w))
    (Hframe : asn.interpret (gen_loop_frame_post ls)
                ((iS.["a"∷ty_xlenbits ↦ ty.SyncVal q]).["an"∷ty_xlenbits ↦ ty.SyncVal q])
              ∗ FS
              ⊢ asn.interpret (gen_loop_frame_pre ls) (iN.["a"∷ty_xlenbits ↦ ty.SyncVal q])
                ∗ Fn) :
    asn.interpret (cfg_postcondition (loop_body_contract ls))
      ((iS.["a"∷ty_xlenbits ↦ ty.SyncVal q]).["an"∷ty_xlenbits ↦ ty.SyncVal q])
    ∗ FS
    ⊢ asn.interpret (gen_loop_at_head ls) (iN.["a"∷ty_xlenbits ↦ ty.SyncVal q]) ∗ Fn.
  Proof.
    cbn [cfg_postcondition loop_body_contract gen_loop_contract].
    unfold gen_loop_at_head, gen_loop_state, gen_loop_contract_post.
    iIntros "(((Hex & Hfr) & Hmin) & HFS)".
    iDestruct "Hex" as (v) "(Hc & (%Heq & _) & (%Hsl & _))".
    destruct v as [w' | va vb]; [| destruct Hsl].
    cbn -[loop_counter_post_ex] in Heq. rewrite (Hk (ty.SyncVal w')) in Heq. cbn in Heq.
    rewrite Hstep in Heq. subst w'.
    cbn [asn.interpret].
    assert (Hc2 : inst (T := fun Σ => Term Σ ty_xlenbits) (term_var "c")
                    (((iS.["a"∷ty_xlenbits ↦ ty.SyncVal q]).["an"∷ty_xlenbits ↦ ty.SyncVal q])
                       .["c"∷ty_xlenbits ↦ ty.SyncVal (@bv.of_N xlenbits w)])
                  = inst (T := fun Σ => Term Σ ty_xlenbits) (loop_counter_pre ls)
                      (iN.["a"∷ty_xlenbits ↦ ty.SyncVal q]))
      by (cbn -[loop_counter_pre]; now rewrite Hkn).
    rewrite <- (asn_regidx_pts_inst (loop_counter_reg ls) (term_var "c") (loop_counter_pre ls) _ _ Hc2).
    iDestruct (Hframe with "[$Hfr $HFS]") as "(Hfr' & HFn)".
    iSplitR "HFn"; [| iExact "HFn"].
    iSplitR "Hmin"; [| iExact "Hmin"].
    iSplitL "Hc"; [iExact "Hc" |].
    iSplitR; [iPureIntro; cbn -[loop_counter_pre]; now rewrite Hkn |].
    iExact "Hfr'".
  Qed.

  (* ---- THE RESERVOIR -----------------------------------------------------

     An ARRAY loop cannot close its own back edge with a trip-independent
     frame: the body consumes the cell at the current pointer and the next
     trip needs the cell at the next one, which was never in the frame.  The
     reservoir is where the not-yet-reached cells live, and `loop_invariant`'s `Fr`
     is trip-indexed so that it can hold them.

     The definition avoids ALL binder machinery by a trick: the cells trip i
     needs are, by construction, `A` interpreted at trip i's own valuation --
     so the reservoir is just that assertion at every future trip, and peeling
     one off is `big_sepL`'s app lemma.  `A` is the CELL half of the loop's
     `loop_extra_pre`; the carried half (registers, pure facts) crosses the back
     edge in the frame as usual. *)
  Definition loop_reservoir {R : LCtx} (A : Assertion (R ▻ "a"∷ty_xlenbits))
      (iota : nat -> Valuation R) (q : bv xlenbits) (n : nat) : iProp Σ :=
    ([∗ list] i ∈ seq 0 n,
       asn.interpret A ((iota i).["a"∷ty_xlenbits ↦ ty.SyncVal q]))%I.

  Lemma loop_reservoir_peel {R : LCtx} (A : Assertion (R ▻ "a"∷ty_xlenbits))
      (iota : nat -> Valuation R) (q : bv xlenbits) (n : nat) :
    loop_reservoir A iota q (S n)
    ⊣⊢ loop_reservoir A iota q n
        ∗ asn.interpret A ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q]).
  Proof.
    unfold loop_reservoir. rewrite seq_S. rewrite big_opL_app. cbn.
    now rewrite bi.sep_emp.
  Qed.

  (* The whole bounds block of a frame, from a Forall of per-base facts --
     each of which is `loop_bound_le`.  Rebuilding the bounds is necessary
     rather than framing them across the back edge: a walking pointer's bound
     at trip n is NOT implied by its bound at trip S n. *)
  Lemma gen_loop_bounds_intro {R : LCtx} (bs : list (Term R ty_xlenbits * N))
      (ι : Valuation R)
      (H : List.Forall (fun b =>
             instprop (formula_relop bop.le
               (term_binop bop.plus (term_unop uop.unsigned (fst b))
                  (term_val ty.int (Z.of_N (snd b))))
               (term_val ty.int (Z.of_N lenAddr))) ι) bs) :
    ⊢ asn.interpret (gen_loop_bounds bs) ι.
  Proof.
    induction bs as [| b bs IH];
      cbn [gen_loop_bounds List.fold_right asn.interpret].
    - iSplit; [iPureIntro; cbn; reflexivity | done].
    - inversion H as [| ?? Hb Hbs]; subst.
      iSplitR; [iSplit; [iPureIntro; exact Hb | done] |].
      iApply IH. exact Hbs.
  Qed.

  (* The MEMORY analogue of asn_regidx_pts_inst, which did not exist before
     2026-09-12 (it is what a sliding two-cell window needs when one cell
     CROSSES the back edge: the post holds it under one address term and
     binder name, the next trip's frame wants it under another).

     Note `@term_var _ x _ ctx.in_zero` rather than `term_var x`: with an
     abstract `x : string`, ctx.resolution cannot compute the In-proof, and
     writing the index explicitly is the whole fix. *)
  Lemma asn_cell_inst {R1 R2 : LCtx} (x1 x2 : string)
    (T1 : Term (R1 ▻ x1∷ty.bvec (bytes_per_word * byte)) ty_xlenbits)
    (T2 : Term (R2 ▻ x2∷ty.bvec (bytes_per_word * byte)) ty_xlenbits)
    (i1 : Valuation R1) (i2 : Valuation R2)
    (H : forall v : ty.RelVal (ty.bvec (bytes_per_word * byte)),
           inst (T := fun Σ => Term Σ ty_xlenbits) T1
             (i1.[x1∷ty.bvec (bytes_per_word * byte) ↦ v])
           = inst (T := fun Σ => Term Σ ty_xlenbits) T2
               (i2.[x2∷ty.bvec (bytes_per_word * byte) ↦ v])) :
    asn.interpret (asn.exist x1 (ty.bvec (bytes_per_word * byte))
                     (T1 ↦ₘ @term_var _ x1 _ ctx.in_zero)) i1
    ⊣⊢ asn.interpret (asn.exist x2 (ty.bvec (bytes_per_word * byte))
                        (T2 ↦ₘ @term_var _ x2 _ ctx.in_zero)) i2.
  Proof.
    cbn. apply bi.exist_proper. intros v. now rewrite (H v).
  Qed.

  (* ---- THE TWO MOVES A FRAME PROOF MAKES --------------------------------

     Both are `*_inst` plus the arithmetic, packaged so that a call site says
     only WHAT THE TWO SIDES EVALUATE TO (as N) and why those are equal.  That
     is the whole content of "this register advanced by 4" / "this cell is the
     one the previous trip handed back". *)
  Lemma loop_reg_shift {R1 R2 : LCtx} (r : RegIdx)
    (t1 : Term R1 ty_xlenbits) (t2 : Term R2 ty_xlenbits)
    (i1 : Valuation R1) (i2 : Valuation R2) (x y : N)
    (H1 : inst (T := fun Σ => Term Σ ty_xlenbits) t1 i1
          = ty.SyncVal (@bv.of_N xlenbits x))
    (H2 : inst (T := fun Σ => Term Σ ty_xlenbits) t2 i2
          = ty.SyncVal (@bv.of_N xlenbits y))
    (Hxy : x = y) :
    asn.interpret (asn_regidx_pts r t1) i1
    ⊢ asn.interpret (asn_regidx_pts r t2) i2.
  Proof.
    apply bi.equiv_entails_1_1, (asn_regidx_pts_inst r t1 t2 i1 i2).
    rewrite H1. rewrite H2. now subst y.
  Qed.

  Lemma loop_cell_shift {R1 R2 : LCtx} (x1 x2 : string)
    (T1 : Term (R1 ▻ x1∷ty.bvec (bytes_per_word * byte)) ty_xlenbits)
    (T2 : Term (R2 ▻ x2∷ty.bvec (bytes_per_word * byte)) ty_xlenbits)
    (i1 : Valuation R1) (i2 : Valuation R2) (x y : N)
    (H1 : forall v, inst (T := fun Σ => Term Σ ty_xlenbits) T1
                      (i1.[x1∷ty.bvec (bytes_per_word * byte) ↦ v])
                    = ty.SyncVal (@bv.of_N xlenbits x))
    (H2 : forall v, inst (T := fun Σ => Term Σ ty_xlenbits) T2
                      (i2.[x2∷ty.bvec (bytes_per_word * byte) ↦ v])
                    = ty.SyncVal (@bv.of_N xlenbits y))
    (Hxy : x = y) :
    asn.interpret (asn.exist x1 (ty.bvec (bytes_per_word * byte))
                     (T1 ↦ₘ @term_var _ x1 _ ctx.in_zero)) i1
    ⊢ asn.interpret (asn.exist x2 (ty.bvec (bytes_per_word * byte))
                        (T2 ↦ₘ @term_var _ x2 _ ctx.in_zero)) i2.
  Proof.
    apply bi.equiv_entails_1_1, (asn_cell_inst x1 x2 T1 T2 i1 i2).
    intros v. rewrite (H1 v). rewrite (H2 v). now subst y.
  Qed.

  (* ---- THE WHOLE FRAME, STRUCTURALLY -------------------------------------

     A loop's frame is always `bounds ∗ regs ∗ extra`, and the first two are
     the SAME argument every time: the bounds are rebuilt from N-level facts,
     the register block crosses on its base's value.  Only `extra` is the
     loop's own.  This lemma says exactly that, so a per-loop frame proof is
     a Forall of bounds plus the extra entailment -- and nothing else.

     (`gen_regs_at_inst` was written once before, deleted as unused because
     `iFrame` crosses the register block at a CONCRETE call site.  Stating
     the step generically is what brings it back: over abstract valuations
     the two interpretations are no longer convertible.) *)
  Lemma gen_regs_at_inst {R1 R2 : LCtx} (b1 : Term R1 ty_xlenbits)
    (b2 : Term R2 ty_xlenbits) (i1 : Valuation R1) (i2 : Valuation R2)
    (specs : list reg_spec_rel)
    (Hb : inst (T := fun Σ => Term Σ ty_xlenbits) b1 i1
          = inst (T := fun Σ => Term Σ ty_xlenbits) b2 i2) :
    asn.interpret (gen_regs_at b1 specs) i1
    ⊣⊢ asn.interpret (gen_regs_at b2 specs) i2.
  Proof.
    induction specs as [| s specs IH];
      cbn [gen_regs_at List.fold_right asn.interpret].
    - reflexivity.
    - destruct s as [[r pub] pv]; destruct pv;
        cbn [gen_reg_asn_at asn.interpret].
      + apply bi.sep_proper; [| exact IH].
        destruct pub; cbn [asn.interpret];
          apply bi.exist_proper; intros v;
          unfold asn_regidx_pts; destruct (reg_convert r); cbn; reflexivity.
      + apply bi.sep_proper; [| exact IH].
        unfold asn_regidx_pts; destruct (reg_convert r); cbn; reflexivity.
      + apply bi.sep_proper; [| exact IH].
        unfold asn_regidx_pts; destruct (reg_convert r); cbn;
          [now rewrite Hb | reflexivity].
  Qed.

  Lemma loop_frame_transfer {R : LCtx} (ls : LoopSpec R) (iS iN : Valuation R)
    (q : bv xlenbits) (FS Fn : iProp Σ)
    (Hq : inst (T := fun Σ => Term Σ ty_xlenbits) (loop_base_post ls)
            ((iS.["a"∷ty_xlenbits ↦ ty.SyncVal q]).["an"∷ty_xlenbits ↦ ty.SyncVal q])
          = inst (T := fun Σ => Term Σ ty_xlenbits) (loop_base_pre ls)
              (iN.["a"∷ty_xlenbits ↦ ty.SyncVal q]))
    (Hb : List.Forall (fun b =>
            instprop (formula_relop bop.le
              (term_binop bop.plus (term_unop uop.unsigned (fst b))
                 (term_val ty.int (Z.of_N (snd b))))
              (term_val ty.int (Z.of_N lenAddr)))
              (iN.["a"∷ty_xlenbits ↦ ty.SyncVal q])) (loop_all_bounds_pre ls))
    (Hex : asn.interpret (loop_extra_post ls)
             ((iS.["a"∷ty_xlenbits ↦ ty.SyncVal q]).["an"∷ty_xlenbits ↦ ty.SyncVal q])
           ∗ FS
           ⊢ asn.interpret (loop_extra_pre ls) (iN.["a"∷ty_xlenbits ↦ ty.SyncVal q]) ∗ Fn) :
    asn.interpret (gen_loop_frame_post ls)
      ((iS.["a"∷ty_xlenbits ↦ ty.SyncVal q]).["an"∷ty_xlenbits ↦ ty.SyncVal q])
    ∗ FS
    ⊢ asn.interpret (gen_loop_frame_pre ls) (iN.["a"∷ty_xlenbits ↦ ty.SyncVal q]) ∗ Fn.
  Proof.
    unfold gen_loop_frame_post, gen_loop_frame_pre. cbn [asn.interpret].
    iIntros "((_ & Hregs & Hex') & HFS)".
    iDestruct (Hex with "[$Hex' $HFS]") as "(Hea & HFn)".
    iSplitR "HFn"; [| iExact "HFn"].
    iSplitR; [iApply gen_loop_bounds_intro; exact Hb |].
    iSplitL "Hregs"; [| iExact "Hea"].
    iApply (bi.equiv_entails_1_1 _ _
              (gen_regs_at_inst (loop_base_post ls) (loop_base_pre ls) _ _ (loop_regs ls) Hq)).
    iExact "Hregs".
  Qed.

  (* ---- THE TWO OBLIGATIONS, NAMED ---------------------------------------

     What a caller proves per loop is exactly these two, and without a name
     each one's STATEMENT is a dozen lines of re-spelled valuation.  Same
     disease, same cure, as `dvInv` for the assembly block. *)
  Definition loop_frame_obligation {R : LCtx} (ls : LoopSpec R)
      (iota : nat -> Valuation R) (q : bv xlenbits) (Fr : nat -> iProp Σ)
      (n : nat) : Prop :=
    asn.interpret (gen_loop_frame_post ls)
      (((iota (S n)).["a"∷ty_xlenbits ↦ ty.SyncVal q]).["an"∷ty_xlenbits ↦ ty.SyncVal q])
    ∗ Fr (S n)
    ⊢ asn.interpret (gen_loop_frame_pre ls)
        ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])
      ∗ Fr n.

  Definition loop_back_edge {R : LCtx} (ls : LoopSpec R)
      (iota : nat -> Valuation R) (q : bv xlenbits) (Fr : nat -> iProp Σ)
      (n : nat) : Prop :=
    asn.interpret (cfg_postcondition (loop_body_contract ls))
      (((iota (S n)).["a"∷ty_xlenbits ↦ ty.SyncVal q]).["an"∷ty_xlenbits ↦ ty.SyncVal q])
    ∗ Fr (S n)
    ⊢ asn.interpret (gen_loop_at_head ls)
        ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])
      ∗ Fr n.

  (* A loop's back edge does not care about resources it never touches, so an
     edge proved for one frame holds for that frame plus any constant carry.
     This is what lets a composition thread a predecessor's leftovers (spill
     slots, callee-saved blocks) through a loop whose own edge lemma was
     stated for the reservoir alone. *)
  Lemma loop_back_edge_frame {R : LCtx} (ls : LoopSpec R)
    (iota : nat -> Valuation R) (q : bv xlenbits) (Fr : nat -> iProp Σ)
    (C : iProp Σ) (n : nat) (H : loop_back_edge ls iota q Fr n) :
    loop_back_edge ls iota q (fun m => Fr m ∗ C)%I n.
  Proof.
    unfold loop_back_edge in *.
    iIntros "(Hpost & Hfr & Hc)".
    iDestruct (H with "[$Hpost $Hfr]") as "(Hwin & Hfn)".
    iFrame.
  Qed.

  (* ---- THE EXTRA, STEPPED GENERICALLY ------------------------------------

     With `ls_extra_*` built from data (GenSegment §5), the walk of iSplits
     that every loop's frame proof used to spell out becomes one lemma.  What
     a caller supplies is three things, and each is exactly the loop's own
     content:

       Hw : per walking register, what both sides evaluate to and why equal;
       Hf : the pure facts the postcondition DROPS, at trip n;
       Hc : the cell trade with the reservoir.

     Nothing else survives -- the registers, their secLeak facts and the
     nesting are all discharged here, once. *)

  Lemma walk_secLeak {R : LCtx} (v : string) (vIn : (v∷ty_xlenbits ∈ R)%katamaran)
    (i : Valuation R) (y : N)
    (Hy : inst (T := fun Σ => Term Σ ty_xlenbits) (@term_var _ v _ vIn) i
          = ty.SyncVal (@bv.of_N xlenbits y)) :
    instprop (formula_secLeak (@term_var _ v _ vIn)) i.
  Proof. cbn. cbn in Hy. rewrite Hy. exact I. Qed.

  Lemma gen_walk_step {R : LCtx} (ws : list (walk_reg R)) (iS iN : Valuation R)
    (q : bv xlenbits)
    (Hw : List.Forall (fun w => exists x : N,
            inst (T := fun Σ => Term Σ ty_xlenbits)
              (addr_off (@term_var _ (walk_var w) _ (ctx.in_succ (ctx.in_succ (walk_var_in w))))
                 (walk_step w))
              ((iS.["a"∷ty_xlenbits ↦ ty.SyncVal q]).["an"∷ty_xlenbits ↦ ty.SyncVal q])
            = ty.SyncVal (@bv.of_N xlenbits x)
         /\ inst (T := fun Σ => Term Σ ty_xlenbits)
              (@term_var _ (walk_var w) _ (ctx.in_succ (walk_var_in w)))
              (iN.["a"∷ty_xlenbits ↦ ty.SyncVal q])
            = ty.SyncVal (@bv.of_N xlenbits x)) ws) :
    asn.interpret (gen_walk_post ws)
      ((iS.["a"∷ty_xlenbits ↦ ty.SyncVal q]).["an"∷ty_xlenbits ↦ ty.SyncVal q])
    ⊢ asn.interpret (gen_walk_pre ws) (iN.["a"∷ty_xlenbits ↦ ty.SyncVal q]).
  Proof.
    induction ws as [| w ws IH]; cbn [gen_walk_post gen_walk_pre List.fold_right].
    - iIntros "_". iSplit; [iPureIntro; cbn; reflexivity | done].
    - inversion Hw as [| ?? Hh Ht]; subst.
      destruct Hh as (x & Hx & Hy).
      destruct (walk_is_public w); cbn [asn.interpret].
      + iIntros "(Hr & Hsl & Hrest)".
        iSplitL "Hr";
          [ iApply (loop_reg_shift (walk_register w) _ _ _ _ x x Hx Hy eq_refl); iExact "Hr" |].
        iSplitR;
          [ iSplit; [ iPureIntro; exact (walk_secLeak _ _ _ x Hy) | done ] |].
        iApply (IH Ht). iExact "Hrest".
      + iIntros "(Hr & Hrest)".
        iSplitL "Hr";
          [ iApply (loop_reg_shift (walk_register w) _ _ _ _ x x Hx Hy eq_refl); iExact "Hr" |].
        iApply (IH Ht). iExact "Hrest".
  Qed.

  Lemma gen_pures_interp {R : LCtx} (fs : list (Formula (R ▻ "a"∷ty_xlenbits)))
    (tail : Assertion (R ▻ "a"∷ty_xlenbits)) (i : Valuation (R ▻ "a"∷ty_xlenbits))
    (Hf : List.Forall (fun f => instprop f i) fs) :
    asn.interpret tail i ⊢ asn.interpret (gen_pures fs tail) i.
  Proof.
    induction fs as [| f fs IH]; cbn [gen_pures List.fold_right asn.interpret].
    - auto.
    - inversion Hf as [| ?? Hh Ht]; subst.
      iIntros "H". iSplitR; [iSplit; [iPureIntro; exact Hh | done] |].
      iApply (IH Ht). iExact "H".
  Qed.

  Lemma loop_extra_transfer {R : LCtx} (ws : list (walk_reg R))
    (fs : list (Formula (R ▻ "a"∷ty_xlenbits))) (cs : list (cell_spec R))
    (iS iN : Valuation R) (q : bv xlenbits) (FS Fn : iProp Σ)
    (Hw : List.Forall (fun w => exists x : N,
            inst (T := fun Σ => Term Σ ty_xlenbits)
              (addr_off (@term_var _ (walk_var w) _ (ctx.in_succ (ctx.in_succ (walk_var_in w))))
                 (walk_step w))
              ((iS.["a"∷ty_xlenbits ↦ ty.SyncVal q]).["an"∷ty_xlenbits ↦ ty.SyncVal q])
            = ty.SyncVal (@bv.of_N xlenbits x)
         /\ inst (T := fun Σ => Term Σ ty_xlenbits)
              (@term_var _ (walk_var w) _ (ctx.in_succ (walk_var_in w)))
              (iN.["a"∷ty_xlenbits ↦ ty.SyncVal q])
            = ty.SyncVal (@bv.of_N xlenbits x)) ws)
    (Hf : List.Forall (fun f => instprop f (iN.["a"∷ty_xlenbits ↦ ty.SyncVal q])) fs)
    (Hc : asn.interpret (gen_cells_post cs)
            ((iS.["a"∷ty_xlenbits ↦ ty.SyncVal q]).["an"∷ty_xlenbits ↦ ty.SyncVal q])
          ∗ FS
          ⊢ asn.interpret (gen_cells_pre cs) (iN.["a"∷ty_xlenbits ↦ ty.SyncVal q]) ∗ Fn) :
    asn.interpret (gen_extra_post ws cs)
      ((iS.["a"∷ty_xlenbits ↦ ty.SyncVal q]).["an"∷ty_xlenbits ↦ ty.SyncVal q])
    ∗ FS
    ⊢ asn.interpret (gen_extra_pre ws fs cs) (iN.["a"∷ty_xlenbits ↦ ty.SyncVal q]) ∗ Fn.
  Proof.
    unfold gen_extra_post, gen_extra_pre. cbn [asn.interpret].
    iIntros "((Hw' & Hc') & HFS)".
    iDestruct (Hc with "[$Hc' $HFS]") as "(Hca & HFn)".
    iSplitR "HFn"; [| iExact "HFn"].
    iSplitL "Hw'"; [ iApply (gen_walk_step ws iS iN q Hw); iExact "Hw'" |].
    iApply (gen_pures_interp fs (gen_cells_pre cs) _ Hf). iExact "Hca".
  Qed.

  (* ---- WHAT THE LOOP HAS ALREADY DONE ------------------------------------

     `loop_reservoir` is the RESERVOIR: the trips the loop has not reached yet.  At
     trip 0 it is `emp`, which is why every loop so far simply DROPPED the
     cells it wrote -- each `_trans_closed`'s cell trade discards them
     (`iIntros "(_ & ...)"`).  Harmless for a loop nobody reads afterwards,
     fatal for one whose whole point is the array it writes.

     `loop_completed` is the other half: the trips it HAS run, from `lo` up to the
     total count `hi`.  A caller that wants the array back uses

       Fr n := loop_reservoir A iota q n ∗ loop_completed A iota q n N

     and the per-trip trade becomes "move one cell across" instead of "drop
     it".  NOTHING in loop_invariant/loop_runs changes: `Fr` was always an arbitrary
     `nat -> iProp`, and `loop_runs`'s `HOut` already hands `Fr 0` back.  At
     entry (n = N) the done block is `seq (S N) 0` = emp; at exit (n = 0) it
     is trips 1..N, which is every trip the body ran. *)
  Definition loop_completed {R : LCtx} (A : Assertion (R ▻ "a"∷ty_xlenbits))
      (iota : nat -> Valuation R) (q : bv xlenbits) (lo hi : nat) : iProp Σ :=
    ([∗ list] i ∈ seq (S lo) (hi - lo),
       asn.interpret A ((iota i).["a"∷ty_xlenbits ↦ ty.SyncVal q]))%I.

  (* The mirror of `loop_reservoir_peel`, peeling the OTHER end: the trip just
     finished is the FIRST entry of the done block, not the last. *)
  Lemma loop_completed_push {R : LCtx} (A : Assertion (R ▻ "a"∷ty_xlenbits))
      (iota : nat -> Valuation R) (q : bv xlenbits) (n N : nat)
      (H : (n < N)%nat) :
    loop_completed A iota q n N
    ⊣⊢ asn.interpret A ((iota (S n)).["a"∷ty_xlenbits ↦ ty.SyncVal q])
        ∗ loop_completed A iota q (S n) N.
  Proof.
    unfold loop_completed.
    replace (N - n)%nat with (S (N - S n)) by lia.
    cbn [seq]. now rewrite big_sepL_cons.
  Qed.

  (* The `_an` and `_a` cell blocks differ by exactly ONE weakening -- the
     extra `an` binder cannot change what a `term_var` of R resolves to -- so
     at the SAME trip they are the same resources.  This is what lets a
     finished trip be filed into `loop_completed`, whose entries are `_a`-shaped,
     from the post, which hands them back `_an`-shaped. *)
  Lemma gen_cells_drop_exit_pc {R : LCtx} (cs : list (cell_spec R))
      (i : Valuation R) (q : bv xlenbits) :
    asn.interpret (gen_cells_post cs)
      ((i.["a"∷ty_xlenbits ↦ ty.SyncVal q]).["an"∷ty_xlenbits ↦ ty.SyncVal q])
    ⊣⊢ asn.interpret (gen_cells_pre cs) (i.["a"∷ty_xlenbits ↦ ty.SyncVal q]).
  Proof.
    induction cs as [| c cs IH];
      cbn [gen_cells_post gen_cells_pre List.fold_right asn.interpret].
    - reflexivity.
    - rewrite IH. apply bi.sep_proper; [| reflexivity].
      (* `addr_off`'s `if bv.eqb off bv.zero` is STUCK on a variable offset,
         which is the only thing stopping conversion here -- force the branch
         and both sides reduce to the same term.  (The underlying fact,
         `inst (term_var x (in_succ h)) (E.[y↦w]) = inst (term_var x h) E`,
         is already `reflexivity`.)  A CONSTANT cell has no binder, so it needs
         neither `exist_proper` nor the publicness split. *)
      destruct (cell_value c).
      + unfold addr_off; destruct (bv.eqb (cell_offset c) bv.zero); reflexivity.
      + apply bi.exist_proper. intros v.
        unfold addr_off; destruct (bv.eqb (cell_offset c) bv.zero);
          destruct (cell_is_public c); reflexivity.
  Qed.

  (* ---- WHERE THE RESERVOIR COMES FROM ------------------------------------

     Everything above ASSUMES the reservoir: `loop_invariant` carries `Fr n`, the
     trip step trades with it, and at trip 0 it is empty.  Nothing so far said
     where a caller GETS one, which is what a real program proof has to supply
     before it can instantiate any of this.

     `loop_reservoir_intro` is the general answer: a reservoir IS a block of per-trip
     resources, so producing one is producing `A` at each future trip's
     valuation.  `loop_reservoir_words` is the case that actually occurs -- a loop
     walking an array of words -- where the block is n memory cells at
     addresses the caller computes, and the per-trip obligation collapses to
     one arithmetic fact about `addr i`. *)

  Lemma loop_reservoir_intro {R : LCtx} (A : Assertion (R ▻ "a"∷ty_xlenbits))
    (iota : nat -> Valuation R) (q : bv xlenbits) (n : nat) (blk : nat -> iProp Σ)
    (H : forall i,
           blk i ⊢ asn.interpret A ((iota i).["a"∷ty_xlenbits ↦ ty.SyncVal q])) :
    ([∗ list] i ∈ seq 0 n, blk i) ⊢ loop_reservoir A iota q n.
  Proof.
    unfold loop_reservoir. apply big_sepL_mono. intros k i _. apply H.
  Qed.

  (* one word of memory at a PUBLIC address, contents arbitrary *)
  Definition mem_word (a : bv xlenbits) : iProp Σ :=
    asn.interpret (Σ := ["p"∷ty_xlenbits])
      (asn.exist "w" ty_xlenbits (term_var "p" ↦ₘ term_var "w"))
      ([env].["p"∷ty_xlenbits ↦ ty.SyncVal a]).

  Lemma loop_reservoir_words {R : LCtx} (c : cell_spec R) (iota : nat -> Valuation R)
    (q : bv xlenbits) (n : nat) (addr : nat -> bv xlenbits)
    (Hpub : cell_is_public c = false)
    (* the cell is EXISTENTIAL: `mem_word` is an existential resource and
       cannot produce a constant cell's `addr ↦ₘ term_val v`.  Stated rather
       than assumed, since `cell_value` became a field (2026-09-14). *)
    (Hex : cell_value c = None)
    (Haddr : forall i (v : ty.RelVal (ty.bvec (bytes_per_word * byte))),
       inst (T := fun Σ => Term Σ ty_xlenbits)
         (addr_off (@term_var _ (cell_base_var c) _ (ctx.in_succ (ctx.in_succ (cell_base_in c))))
            (cell_offset c))
         ((((iota i).["a"∷ty_xlenbits ↦ ty.SyncVal q]))
            .[cell_binder c ∷ty.bvec (bytes_per_word * byte) ↦ v])
       = ty.SyncVal (addr i)) :
    ([∗ list] i ∈ seq 0 n, mem_word (addr i)) ⊢ loop_reservoir (gen_cells_pre [c]) iota q n.
  Proof.
    unfold loop_reservoir. apply big_sepL_mono. intros k i _.
    unfold mem_word.
    cbn [gen_cells_pre List.fold_right asn.interpret].
    rewrite Hex. rewrite Hpub.
    iIntros "H". iSplitL "H"; [| iSplit; [iPureIntro; cbn; reflexivity | done]].
    iApply (bi.equiv_entails_1_1 _ _
              (asn_cell_inst "w" (cell_binder c) (term_var "p")
                 (addr_off (@term_var _ (cell_base_var c) _ (ctx.in_succ (ctx.in_succ (cell_base_in c))))
                    (cell_offset c))
                 ([env].["p"∷ty_xlenbits ↦ ty.SyncVal (addr i)])
                 ((iota i).["a"∷ty_xlenbits ↦ ty.SyncVal q])
                 ltac:(intros v; cbn; symmetry; exact (Haddr i v)))).
    iExact "H".
  Qed.

  (* ---- CARRYING THE ARRAY ACROSS THE TRIPS -------------------------------

     Everything above builds the reservoir and files finished trips away, but
     never JOINED the two: every loop so far instantiated `Hc` by DISCARDING
     the cells it wrote.  That is fatal for a loop whose whole point is the
     array it writes, and it is the last hand-written premise of
     `loop_back_edge_std`.

     `loop_carry` is the frame that does both halves at once, and
     `loop_cells_trade` IS `Hc` for it.  The trade turns out to be a PURE
     PERMUTATION -- peel one cell off the reservoir, push the finished one onto
     the done block, and the two sides are the same resources -- so it carries
     no arithmetic and no per-loop content.  That is what makes it machinery:
     one lemma serves every loop, for any number of cells, at any publicness.

     Publicness is a FIELD of `cell_spec`, so the reservoir's per-cell resource
     has to branch on it too: `mem_cell true` additionally knows its contents
     are public, which is what a loop reading a public array (muladd's I, K, M
     all read one) needs.  `mem_cell false` IS `mem_word`, by conversion. *)

  Definition mem_cell (val : option (Val ty_xlenbits)) (pub : bool) (a : bv xlenbits)
      : iProp Σ :=
    match val with
    | Some v =>
        asn.interpret (Σ := ["p"∷ty_xlenbits])
          (term_var "p" ↦ₘ term_val ty_xlenbits v)
          ([env].["p"∷ty_xlenbits ↦ ty.SyncVal a])
    | None =>
        asn.interpret (Σ := ["p"∷ty_xlenbits])
          (asn.exist "w" ty_xlenbits
             (if pub
              then asn.sep (term_var "p" ↦ₘ term_var "w")
                     (asn.formula (formula_secLeak (@term_var _ "w" _ ctx.in_zero)))
              else (term_var "p" ↦ₘ term_var "w")%asn))
          ([env].["p"∷ty_xlenbits ↦ ty.SyncVal a])
    end.

  Lemma mem_cell_false (a : bv xlenbits) : mem_cell None false a = mem_word a.
  Proof. reflexivity. Qed.

  (* the public twin of `asn_cell_inst`.  The `secLeak` conjunct mentions only
     the BINDER, which both sides share, so the proof is the same one-liner. *)
  Lemma asn_cell_inst_pub {R1 R2 : LCtx} (x1 x2 : string)
    (T1 : Term (R1 ▻ x1∷ty.bvec (bytes_per_word * byte)) ty_xlenbits)
    (T2 : Term (R2 ▻ x2∷ty.bvec (bytes_per_word * byte)) ty_xlenbits)
    (i1 : Valuation R1) (i2 : Valuation R2)
    (H : forall v : ty.RelVal (ty.bvec (bytes_per_word * byte)),
           inst (T := fun Σ => Term Σ ty_xlenbits) T1
             (i1.[x1∷ty.bvec (bytes_per_word * byte) ↦ v])
           = inst (T := fun Σ => Term Σ ty_xlenbits) T2
               (i2.[x2∷ty.bvec (bytes_per_word * byte) ↦ v])) :
    asn.interpret (asn.exist x1 (ty.bvec (bytes_per_word * byte))
                     (asn.sep (T1 ↦ₘ @term_var _ x1 _ ctx.in_zero)
                        (asn.formula (formula_secLeak (@term_var _ x1 _ ctx.in_zero))))) i1
    ⊣⊢ asn.interpret (asn.exist x2 (ty.bvec (bytes_per_word * byte))
                        (asn.sep (T2 ↦ₘ @term_var _ x2 _ ctx.in_zero)
                           (asn.formula (formula_secLeak (@term_var _ x2 _ ctx.in_zero))))) i2.
  Proof.
    cbn. apply bi.exist_proper. intros v. now rewrite (H v).
  Qed.

  (* the CONSTANT twin: no binder at all, so the two sides agree as soon as the
     two address terms denote the same address. *)
  Lemma asn_cell_inst_const {R1 R2 : LCtx}
    (T1 : Term R1 ty_xlenbits) (T2 : Term R2 ty_xlenbits)
    (i1 : Valuation R1) (i2 : Valuation R2) (v : Val ty_xlenbits)
    (H : inst (T := fun Σ => Term Σ ty_xlenbits) T1 i1
         = inst (T := fun Σ => Term Σ ty_xlenbits) T2 i2) :
    asn.interpret (T1 ↦ₘ term_val ty_xlenbits v) i1
    ⊣⊢ asn.interpret (T2 ↦ₘ term_val ty_xlenbits v) i2.
  Proof. cbn. now rewrite H. Qed.

  (* what a cell's reservoir entry must sit at: the address the contract's own
     `addr_off` evaluates to at this trip.  Independent of the cell's VALUE,
     which is why it quantifies over `v`. *)
  Definition cell_addr_ok {R : LCtx} (c : cell_spec R) (i : Valuation R)
      (q : bv xlenbits) (a : bv xlenbits) : Prop :=
    match cell_value c with
    | Some _ =>
        (* no binder, hence one fewer weakening and no quantifier *)
        inst (T := fun Σ => Term Σ ty_xlenbits)
          (addr_off (@term_var _ (cell_base_var c) _ (ctx.in_succ (cell_base_in c)))
             (cell_offset c))
          (i.["a"∷ty_xlenbits ↦ ty.SyncVal q])
        = ty.SyncVal a
    | None =>
        forall v : ty.RelVal (ty.bvec (bytes_per_word * byte)),
          inst (T := fun Σ => Term Σ ty_xlenbits)
            (addr_off (@term_var _ (cell_base_var c) _
                         (ctx.in_succ (ctx.in_succ (cell_base_in c))))
               (cell_offset c))
            ((i.["a"∷ty_xlenbits ↦ ty.SyncVal q])
               .[cell_binder c ∷ty.bvec (bytes_per_word * byte) ↦ v])
          = ty.SyncVal a
    end.

  (* the same zero-offset convention `addr_off` uses, on VALUES *)
  Definition cell_addr_at (b off : bv xlenbits) : bv xlenbits :=
    if bv.eqb off bv.zero then b else bv.add b off.

  Lemma cell_addr_ok_of_base {R : LCtx} (c : cell_spec R) (i : Valuation R)
    (q : bv xlenbits) (b : bv xlenbits)
    (Hb : env.lookup i (cell_base_in c) = ty.SyncVal b) :
    cell_addr_ok c i q (cell_addr_at b (cell_offset c)).
  Proof.
    unfold cell_addr_ok, addr_off, cell_addr_at.
    (* `env.lookup_at_fold` is needed because cbn pushes `inst` through to
       `env.lookup_at`, at which point `Hb` stops matching syntactically. *)
    destruct (cell_value c);
      [ | intros v ];
      destruct (bv.eqb (cell_offset c) bv.zero); cbn;
        rewrite env.lookup_at_fold; rewrite Hb; reflexivity.
  Qed.

  Lemma gen_cells_pre_intro {R : LCtx} (cs : list (cell_spec R))
    (i : Valuation R) (q : bv xlenbits) (addr : cell_spec R -> bv xlenbits)
    (H : List.Forall (fun c => cell_addr_ok c i q (addr c)) cs) :
    ([∗ list] c ∈ cs, mem_cell (cell_value c) (cell_is_public c) (addr c))
    ⊢ asn.interpret (gen_cells_pre cs) (i.["a"∷ty_xlenbits ↦ ty.SyncVal q]).
  Proof.
    induction cs as [| c cs IH];
      cbn [gen_cells_pre List.fold_right asn.interpret].
    - iIntros "_". iSplit; [iPureIntro; cbn; reflexivity | done].
    - inversion H as [| ?? Haddr Ht]; subst.
      rewrite big_sepL_cons.
      iIntros "(Hc & Hrest)". iSplitL "Hc".
      + unfold mem_cell, cell_addr_ok in *.
        destruct (cell_value c) as [cv |].
        { iApply (bi.equiv_entails_1_1 _ _
                    (asn_cell_inst_const (term_var "p")
                       (addr_off (@term_var _ (cell_base_var c) _
                                    (ctx.in_succ (cell_base_in c)))
                          (cell_offset c))
                       ([env].["p"∷ty_xlenbits ↦ ty.SyncVal (addr c)])
                       (i.["a"∷ty_xlenbits ↦ ty.SyncVal q]) cv
                       ltac:(cbn; symmetry; exact Haddr))).
          iExact "Hc". }
        destruct (cell_is_public c).
        * iApply (bi.equiv_entails_1_1 _ _
                    (asn_cell_inst_pub "w" (cell_binder c) (term_var "p")
                       (addr_off (@term_var _ (cell_base_var c) _
                                    (ctx.in_succ (ctx.in_succ (cell_base_in c))))
                          (cell_offset c))
                       ([env].["p"∷ty_xlenbits ↦ ty.SyncVal (addr c)])
                       (i.["a"∷ty_xlenbits ↦ ty.SyncVal q])
                       ltac:(intros v; cbn; symmetry; exact (Haddr v)))).
          iExact "Hc".
        * iApply (bi.equiv_entails_1_1 _ _
                    (asn_cell_inst "w" (cell_binder c) (term_var "p")
                       (addr_off (@term_var _ (cell_base_var c) _
                                    (ctx.in_succ (ctx.in_succ (cell_base_in c))))
                          (cell_offset c))
                       ([env].["p"∷ty_xlenbits ↦ ty.SyncVal (addr c)])
                       (i.["a"∷ty_xlenbits ↦ ty.SyncVal q])
                       ltac:(intros v; cbn; symmetry; exact (Haddr v)))).
          iExact "Hc".
      + iApply (IH Ht). iExact "Hrest".
  Qed.

  (* the many-cell generalisation of `loop_reservoir_words` (which stays: it is
     the one-cell form, and ZZLoopTransCheck2 uses it). *)
  Lemma loop_reservoir_cells {R : LCtx} (cs : list (cell_spec R))
    (iota : nat -> Valuation R) (q : bv xlenbits) (n : nat)
    (addr : nat -> cell_spec R -> bv xlenbits)
    (H : forall i, List.Forall (fun c => cell_addr_ok c (iota i) q (addr i c)) cs) :
    ([∗ list] i ∈ seq 0 n, [∗ list] c ∈ cs, mem_cell (cell_value c) (cell_is_public c) (addr i c))
    ⊢ loop_reservoir (gen_cells_pre cs) iota q n.
  Proof.
    apply loop_reservoir_intro. intros i.
    exact (gen_cells_pre_intro cs (iota i) q (addr i) (H i)).
  Qed.

  Lemma loop_reservoir_sep {R : LCtx} (A B : Assertion (R ▻ "a"∷ty_xlenbits))
    (iota : nat -> Valuation R) (q : bv xlenbits) (n : nat) :
    loop_reservoir (asn.sep A B) iota q n
    ⊣⊢ loop_reservoir A iota q n ∗ loop_reservoir B iota q n.
  Proof.
    unfold loop_reservoir. rewrite <- big_sepL_sep.
    apply big_sepL_proper. intros k i _. cbn [asn.interpret]. reflexivity.
  Qed.

  (* THE FRAME: what is still to come, plus what has already been done. *)
  Definition loop_carry {R : LCtx} (A : Assertion (R ▻ "a"∷ty_xlenbits))
      (iota : nat -> Valuation R) (q : bv xlenbits) (N n : nat) : iProp Σ :=
    (loop_reservoir A iota q n ∗ loop_completed A iota q n N)%I.

  Lemma loop_carry_entry {R : LCtx} (A : Assertion (R ▻ "a"∷ty_xlenbits))
    (iota : nat -> Valuation R) (q : bv xlenbits) (N : nat) :
    loop_reservoir A iota q N ⊢ loop_carry A iota q N N.
  Proof.
    unfold loop_carry, loop_completed. rewrite Nat.sub_diag. cbn.
    now rewrite bi.sep_emp.
  Qed.

  (* at exit the reservoir is empty and the done block is every trip the body
     ran -- which is the array the loop wrote, handed back to the caller. *)
  Lemma loop_carry_exit {R : LCtx} (A : Assertion (R ▻ "a"∷ty_xlenbits))
    (iota : nat -> Valuation R) (q : bv xlenbits) (N : nat) :
    loop_carry A iota q N 0
    ⊢ [∗ list] i ∈ seq 1 N,
        asn.interpret A ((iota i).["a"∷ty_xlenbits ↦ ty.SyncVal q]).
  Proof.
    unfold loop_carry, loop_reservoir, loop_completed. rewrite Nat.sub_0_r. cbn.
    now rewrite bi.emp_sep.
  Qed.

  Lemma loop_carry_cells {R : LCtx} (cs : list (cell_spec R))
    (iota : nat -> Valuation R) (q : bv xlenbits) (N : nat)
    (addr : nat -> cell_spec R -> bv xlenbits)
    (H : forall i, List.Forall (fun c => cell_addr_ok c (iota i) q (addr i c)) cs) :
    ([∗ list] i ∈ seq 0 N, [∗ list] c ∈ cs, mem_cell (cell_value c) (cell_is_public c) (addr i c))
    ⊢ loop_carry (gen_cells_pre cs) iota q N N.
  Proof.
    iIntros "H". iApply loop_carry_entry.
    iApply (loop_reservoir_cells cs iota q N addr H). iExact "H".
  Qed.

  (* ---- Hc ---------------------------------------------------------------- *)
  Lemma loop_cells_trade {R : LCtx} (cs : list (cell_spec R))
    (iota : nat -> Valuation R) (q : bv xlenbits) (N n : nat) (Hn : (n < N)%nat) :
    asn.interpret (gen_cells_post cs)
      (((iota (S n)).["a"∷ty_xlenbits ↦ ty.SyncVal q])
         .["an"∷ty_xlenbits ↦ ty.SyncVal q])
    ∗ loop_carry (gen_cells_pre cs) iota q N (S n)
    ⊢ asn.interpret (gen_cells_pre cs) ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])
      ∗ loop_carry (gen_cells_pre cs) iota q N n.
  Proof.
    unfold loop_carry.
    rewrite gen_cells_drop_exit_pc.
    rewrite loop_reservoir_peel.
    rewrite (loop_completed_push (gen_cells_pre cs) iota q n N Hn).
    iIntros "(Hs & (Hres & Hnew) & Hdone)". iFrame.
  Qed.

  (* ---- A CELL THAT SURVIVES THE TRIP, UNDER A NEW DESCRIPTION -----------

     `loop_cells_trade` assumes the per-trip footprints are DISJOINT: the
     reservoir is `[∗ list] i, A@(iota i)`, so if two trips' cells share an
     address that separating conjunction is `False` and no caller can supply
     it.  Checkable from the cell list alone -- two cells sharing a base whose
     offsets differ by a multiple of the walk step overlap across trips.
     muladd's I, K and M read and write DIFFERENT arrays and are fine; D
     (memmove, an in-place shift) is not: its source cell at `dp-4` is the next
     trip's destination at `dp`.

     For an overlapping window the shared cell must CROSS the back edge rather
     than be retired and re-acquired -- and it is described with one offset
     before and another after (`dp-4` at trip `S n`, `dp` at trip `n`), two
     names for one address.  This is the cell analogue of `walk_step_ok`, and
     the enabling fact is the same walk-step arithmetic.

     NOT SUFFICIENT on its own for D -- see PLAN-muladd-composed.md §R11: an
     in-place shift touches N+1 cells in N trips, so its exit window is
     narrower than its body window, and `LoopSpec` carries ONE `gen_loop_at_head`
     for every trip. *)
  Lemma gen_cell_shift {R : LCtx} (cfrom cto : cell_spec R)
    (iota : nat -> Valuation R) (q : bv xlenbits) (n : nat) (a : bv xlenbits)
    (Hbind : cell_binder cfrom = cell_binder cto)
    (Hpub  : cell_is_public cfrom = cell_is_public cto)
    (Hval  : cell_value cfrom = cell_value cto)
    (Hfrom : cell_addr_ok cfrom (iota (S n)) q a)
    (Hto   : cell_addr_ok cto (iota n) q a) :
    asn.interpret (gen_cells_post [cfrom])
      (((iota (S n)).["a"∷ty_xlenbits ↦ ty.SyncVal q])
         .["an"∷ty_xlenbits ↦ ty.SyncVal q])
    ⊣⊢ asn.interpret (gen_cells_pre [cto]) ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q]).
  Proof.
    rewrite gen_cells_drop_exit_pc.
    cbn [gen_cells_pre List.fold_right asn.interpret].
    apply bi.sep_proper; [| reflexivity].
    unfold cell_addr_ok in *.
    rewrite <- Hval in Hto. rewrite <- Hbind in Hto.
    rewrite <- Hbind. rewrite <- Hpub. rewrite <- Hval.
    destruct (cell_value cfrom) as [cv |].
    - exact (asn_cell_inst_const _ _ _ _ cv (eq_trans Hfrom (eq_sym Hto))).
    - destruct (cell_is_public cfrom).
      + exact (asn_cell_inst_pub _ _ _ _ _ _
                 (fun v => eq_trans (Hfrom v) (eq_sym (Hto v)))).
      + exact (asn_cell_inst _ _ _ _ _ _
                 (fun v => eq_trans (Hfrom v) (eq_sym (Hto v)))).
  Qed.

  (* ---- ONE SIDE CONDITION PER LOOP, NOT PER CELL -------------------------

     `loop_carry_cells` still asks the caller for an ADDRESS per cell per trip.
     Two of muladd's three sliding loops (I, K) walk TWO independent bases, so
     writing that function by hand means matching on the cell -- exactly the
     per-loop special-casing this layer exists to remove.  Reading the address
     off the valuation instead makes it a PROJECTION, and what is left for the
     caller is one fact: every cell's base is a public address at every trip. *)
  Definition cell_addr_of {R : LCtx} (i : Valuation R) (c : cell_spec R)
      : bv xlenbits :=
    match env.lookup i (cell_base_in c) with
    | ty.SyncVal b => cell_addr_at b (cell_offset c)
    | _ => bv.zero
    end.

  (* `@eq` spelled out: a bare `=` here elaborates against `Term _ ty.int`. *)
  Definition cell_base_sync {R : LCtx} (i : Valuation R) (c : cell_spec R) : Prop :=
    exists b : bv xlenbits,
      @eq (ty.RelVal ty_xlenbits) (env.lookup i (cell_base_in c)) (ty.SyncVal b).

  Lemma cell_addr_ok_of_sync {R : LCtx} (c : cell_spec R) (i : Valuation R)
    (q : bv xlenbits) (H : cell_base_sync i c) :
    cell_addr_ok c i q (cell_addr_of i c).
  Proof.
    destruct H as (b & Hb). unfold cell_addr_of. rewrite Hb.
    exact (cell_addr_ok_of_base c i q b Hb).
  Qed.

  Lemma loop_carry_cells_sync {R : LCtx} (cs : list (cell_spec R))
    (iota : nat -> Valuation R) (q : bv xlenbits) (N : nat)
    (H : forall i, List.Forall (cell_base_sync (iota i)) cs) :
    ([∗ list] i ∈ seq 0 N, [∗ list] c ∈ cs,
       mem_cell (cell_value c) (cell_is_public c) (cell_addr_of (iota i) c))
    ⊢ loop_carry (gen_cells_pre cs) iota q N N.
  Proof.
    apply (loop_carry_cells cs iota q N (fun i c => cell_addr_of (iota i) c)).
    intros i. apply List.Forall_forall. intros c Hin.
    apply cell_addr_ok_of_sync.
    exact (proj1 (List.Forall_forall _ _) (H i) c Hin).
  Qed.

  (* ---- THE EDGE, FROM THE DATA ------------------------------------------

     `loop_back_edge` is a Prop, so it can be BUILT rather than proved by hand.
     Every counted loop whose extra is data (GenSegment §5) gets its back edge
     from exactly this composition -- loop_counter_transfer over loop_frame_transfer over
     loop_extra_transfer -- and the caller is left with the six facts that are
     genuinely its own:

       Hk/Hstep/Hkn : the counter's arithmetic across the trip;
       Hqan         : the code base is the same on both sides (eq_refl);
       Hb           : each base is in range at trip n;
       Hw/Hf/Hc     : the walk, the dropped pure facts, the reservoir trade.

     `Hea`/`Hean` are `eq_refl` whenever `ls_extra_*` was defined as the
     generator applied to the loop's own lists, which is the point of defining
     them that way. *)
  Lemma loop_back_edge_std {R : LCtx} (ls : LoopSpec R)
    (ws : list (walk_reg R)) (fs : list (Formula (R ▻ "a"∷ty_xlenbits)))
    (cs : list (cell_spec R))
    (iota : nat -> Valuation R) (q : bv xlenbits) (Fr : nat -> iProp Σ)
    (n : nat) (kv w : N)
    (Hea  : loop_extra_pre ls = gen_extra_pre ws fs cs)
    (Hean : loop_extra_post ls = gen_extra_post ws cs)
    (Hk : forall x : ty.RelVal ty_xlenbits,
            inst (T := fun Σ => Term Σ ty_xlenbits) (loop_counter_post_ex ls)
              ((((iota (S n)).["a"∷ty_xlenbits ↦ ty.SyncVal q])
                  .["an"∷ty_xlenbits ↦ ty.SyncVal q])
                 .["c"∷ty_xlenbits ↦ x])
            = ty.SyncVal (@bv.of_N xlenbits kv))
    (Hstep : bv.add (@bv.of_N xlenbits kv) (loop_counter_step ls) = @bv.of_N xlenbits w)
    (Hkn : inst (T := fun Σ => Term Σ ty_xlenbits) (loop_counter_pre ls)
             ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])
           = ty.SyncVal (@bv.of_N xlenbits w))
    (Hqan : inst (T := fun Σ => Term Σ ty_xlenbits) (loop_base_post ls)
              (((iota (S n)).["a"∷ty_xlenbits ↦ ty.SyncVal q])
                 .["an"∷ty_xlenbits ↦ ty.SyncVal q])
            = inst (T := fun Σ => Term Σ ty_xlenbits) (loop_base_pre ls)
                ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q]))
    (Hb : List.Forall (fun b =>
            instprop (formula_relop bop.le
              (term_binop bop.plus (term_unop uop.unsigned (fst b))
                 (term_val ty.int (Z.of_N (snd b))))
              (term_val ty.int (Z.of_N lenAddr)))
              ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])) (loop_all_bounds_pre ls))
    (Hw : List.Forall (fun v => exists x : N,
            inst (T := fun Σ => Term Σ ty_xlenbits)
              (addr_off (@term_var _ (walk_var v) _ (ctx.in_succ (ctx.in_succ (walk_var_in v))))
                 (walk_step v))
              (((iota (S n)).["a"∷ty_xlenbits ↦ ty.SyncVal q])
                 .["an"∷ty_xlenbits ↦ ty.SyncVal q])
            = ty.SyncVal (@bv.of_N xlenbits x)
         /\ inst (T := fun Σ => Term Σ ty_xlenbits)
              (@term_var _ (walk_var v) _ (ctx.in_succ (walk_var_in v)))
              ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])
            = ty.SyncVal (@bv.of_N xlenbits x)) ws)
    (Hf : List.Forall
            (fun f => instprop f ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])) fs)
    (Hc : asn.interpret (gen_cells_post cs)
            (((iota (S n)).["a"∷ty_xlenbits ↦ ty.SyncVal q])
               .["an"∷ty_xlenbits ↦ ty.SyncVal q])
          ∗ Fr (S n)
          ⊢ asn.interpret (gen_cells_pre cs)
              ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q]) ∗ Fr n) :
    loop_back_edge ls iota q Fr n.
  Proof.
    unfold loop_back_edge.
    apply (loop_counter_transfer ls (iota (S n)) (iota n) q kv w (Fr (S n)) (Fr n)
             Hk Hstep Hkn).
    apply (loop_frame_transfer ls (iota (S n)) (iota n) q (Fr (S n)) (Fr n)
             Hqan Hb).
    rewrite Hea. rewrite Hean.
    exact (loop_extra_transfer ws fs cs (iota (S n)) (iota n) q (Fr (S n)) (Fr n)
             Hw Hf Hc).
  Qed.



  (* ---- D2, CONTINUED: ONE WALKING REGISTER ACROSS THE BACK EDGE ----------

     `Hw`'s element obligation is an existential -- "there is an `x` that the
     register holds at trip `n` and that it reaches from trip `S n` after its
     own step" -- and every loop discharged it by guessing `x`, splitting, and
     then doing the step arithmetic inside the second half with the `addr_off`
     still folded.  The guess is never a guess: `x` IS the value at trip `n`,
     which the loop already knows.

     So the only real content is the step arithmetic, and that is exactly the
     counter's -- a walking register is a counter with its own anchor, which is
     why C2's vocabulary fits it unchanged.

     ONE lemma, not a down/up pair, because the two directions differ only in
     how `Hstep` is discharged (a plain increment versus the wrap-around form)
     and that is the caller's one line either way.  The ZERO-STEP case is
     handled here rather than left to the caller: `addr_off` deliberately
     returns the BARE term on a zero offset (a register the loop does not move
     must be written `r |-> term_var v`, not `v + 0`, or the contract stops
     matching what the executor builds), so the two branches of that `if` have
     genuinely different shapes and a caller would have to know which. *)
  Lemma walk_step_ok {R : LCtx} (v : walk_reg R) (iota : nat -> Valuation R)
    (q : bv xlenbits) (n : nat) (xn xSn : N)
    (HSn : inst (T := fun Σ => Term Σ ty_xlenbits)
             (@term_var _ (walk_var v) _ (ctx.in_succ (ctx.in_succ (walk_var_in v))))
             (((iota (S n)).["a"∷ty_xlenbits ↦ ty.SyncVal q])
                .["an"∷ty_xlenbits ↦ ty.SyncVal q])
           = ty.SyncVal (@bv.of_N xlenbits xSn))
    (Hn : inst (T := fun Σ => Term Σ ty_xlenbits)
            (@term_var _ (walk_var v) _ (ctx.in_succ (walk_var_in v)))
            ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])
          = ty.SyncVal (@bv.of_N xlenbits xn))
    (Hstep : bv.add (@bv.of_N xlenbits xSn) (walk_step v) = @bv.of_N xlenbits xn) :
    exists x : N,
      inst (T := fun Σ => Term Σ ty_xlenbits)
        (addr_off (@term_var _ (walk_var v) _ (ctx.in_succ (ctx.in_succ (walk_var_in v))))
           (walk_step v))
        (((iota (S n)).["a"∷ty_xlenbits ↦ ty.SyncVal q])
           .["an"∷ty_xlenbits ↦ ty.SyncVal q])
      = ty.SyncVal (@bv.of_N xlenbits x)
   (* `x`, not `xn`, in BOTH conjuncts: the target is `exists x, P x /\ Q x`,
      and pinning the second to xn would make this a different proposition
      that happens to be provable -- and would not unify. *)
   /\ inst (T := fun Σ => Term Σ ty_xlenbits)
        (@term_var _ (walk_var v) _ (ctx.in_succ (walk_var_in v)))
        ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])
      = ty.SyncVal (@bv.of_N xlenbits x).
  Proof.
    exists xn. split; [| exact Hn].
    unfold addr_off. destruct (bv.eqb (walk_step v) bv.zero) eqn:Hz.
    - (* the register does not move: addr_off is the bare term, and Hstep
         degenerates to xSn = xn *)
      assert (walk_step v = bv.zero) as Hz0
        by (destruct (bv.eqb_spec (walk_step v) bv.zero); congruence).
      rewrite Hz0 in Hstep. rewrite bv.add_zero_r in Hstep.
      rewrite HSn. now rewrite Hstep.
    - (* `cbn in HSn` too, not just the goal: cbn pushes `inst` through the
         bvadd into a raw `env.lookup_at`, after which HSn's folded LHS
         matches no subterm. *)
      cbn. cbn in HSn. rewrite HSn. cbn. now rewrite Hstep.
  Qed.

  (* ---- D2: THE BACK EDGE, WITH ITS COUNTER THREE DERIVED -----------------

     `loop_back_edge_std` takes ten premises.  Three of them -- the counter at
     trip `S n` before the step (`Hk`), the step itself (`Hstep`), and the
     counter at trip `n` after it (`Hkn`) -- are not independent: given C2's
     closed form they are the SAME recurrence read at two trips, and `Hstep` is
     the arithmetic between them.  Every loop restated all three, passing `kv`
     and `w` as hand-written N expressions, and then paid a `do 2 f_equal; lia`
     to reconcile `w` with what its own `iota` actually said.

     Taking the anchor and stride instead removes both.  `Hstep` goes entirely
     (it is proved here from the no-wrap bound), and `Hkn` improves from
     `cbn. do 2 f_equal; lia.` to `cbn. reflexivity.` -- because `w` is now
     `loop_ctr_down anch stride n`, which is literally what `iota n` holds,
     rather than `kv + stride`, which is only equal to it.

     A LEMMA, not the tactic the plan called D2.  Same reason C2 went this way:
     the dispatch a tactic would do (guard family, step sign) is exactly the
     choice between these two lemmas, and the caller already knows it.  The
     remaining premises -- the bounds, the walking registers, the dropped
     facts, the cell trade -- stay the caller's, because each is genuinely
     loop-specific data rather than a consequence of the recurrence. *)
  Lemma loop_back_edge_affine_down {R : LCtx} (ls : LoopSpec R)
    (ws : list (walk_reg R)) (fs : list (Formula (R ▻ "a"∷ty_xlenbits)))
    (cs : list (cell_spec R))
    (iota : nat -> Valuation R) (q : bv xlenbits) (Fr : nat -> iProp Σ)
    (n : nat) (anch stride : N)
    (Hea  : loop_extra_pre ls = gen_extra_pre ws fs cs)
    (Hean : loop_extra_post ls = gen_extra_post ws cs)
    (Himm : loop_counter_step ls = @bv.of_N xlenbits stride)
    (Hk : forall x : ty.RelVal ty_xlenbits,
            inst (T := fun Σ => Term Σ ty_xlenbits) (loop_counter_post_ex ls)
              ((((iota (S n)).["a"∷ty_xlenbits ↦ ty.SyncVal q])
                  .["an"∷ty_xlenbits ↦ ty.SyncVal q])
                 .["c"∷ty_xlenbits ↦ x])
            = ty.SyncVal (@bv.of_N xlenbits (loop_ctr_down anch stride (S n))))
    (Hkn : inst (T := fun Σ => Term Σ ty_xlenbits) (loop_counter_pre ls)
             ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])
           = ty.SyncVal (@bv.of_N xlenbits (loop_ctr_down anch stride n)))
    (Hqan : inst (T := fun Σ => Term Σ ty_xlenbits) (loop_base_post ls)
              (((iota (S n)).["a"∷ty_xlenbits ↦ ty.SyncVal q])
                 .["an"∷ty_xlenbits ↦ ty.SyncVal q])
            = inst (T := fun Σ => Term Σ ty_xlenbits) (loop_base_pre ls)
                ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q]))
    (* the ONE arithmetic fact, and it is C3's clause for this axis at trip n *)
    (HPle : (stride * (N.of_nat n + 2) <= anch)%N)
    (Hb : List.Forall (fun b =>
            instprop (formula_relop bop.le
              (term_binop bop.plus (term_unop uop.unsigned (fst b))
                 (term_val ty.int (Z.of_N (snd b))))
              (term_val ty.int (Z.of_N lenAddr)))
              ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])) (loop_all_bounds_pre ls))
    (Hw : List.Forall (fun v => exists x : N,
            inst (T := fun Σ => Term Σ ty_xlenbits)
              (addr_off (@term_var _ (walk_var v) _ (ctx.in_succ (ctx.in_succ (walk_var_in v))))
                 (walk_step v))
              (((iota (S n)).["a"∷ty_xlenbits ↦ ty.SyncVal q])
                 .["an"∷ty_xlenbits ↦ ty.SyncVal q])
            = ty.SyncVal (@bv.of_N xlenbits x)
         /\ inst (T := fun Σ => Term Σ ty_xlenbits)
              (@term_var _ (walk_var v) _ (ctx.in_succ (walk_var_in v)))
              ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])
            = ty.SyncVal (@bv.of_N xlenbits x)) ws)
    (Hf : List.Forall
            (fun f => instprop f ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])) fs)
    (Hc : asn.interpret (gen_cells_post cs)
            (((iota (S n)).["a"∷ty_xlenbits ↦ ty.SyncVal q])
               .["an"∷ty_xlenbits ↦ ty.SyncVal q])
          ∗ Fr (S n)
          ⊢ asn.interpret (gen_cells_pre cs)
              ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q]) ∗ Fr n) :
    loop_back_edge ls iota q Fr n.
  Proof.
    refine (loop_back_edge_std ls ws fs cs iota q Fr n
              (loop_ctr_down anch stride (S n)) (loop_ctr_down anch stride n)
              Hea Hean Hk _ Hkn Hqan Hb Hw Hf Hc).
    (* one increment, no wrap -- the whole of `Hstep`, from HPle *)
    rewrite Himm. rewrite bv.of_N_add. f_equal.
    unfold loop_ctr_down. cbn [N.of_nat] in *. lia.
  Qed.

  (* The mirror, for a counter that GROWS as trips remain (B, C).  Same two
     differences as in C2's latch pair: the step is the wrap-around form, and
     the no-wrap fact bounds the value from ABOVE rather than below. *)
  Lemma loop_back_edge_affine_up {R : LCtx} (ls : LoopSpec R)
    (ws : list (walk_reg R)) (fs : list (Formula (R ▻ "a"∷ty_xlenbits)))
    (cs : list (cell_spec R))
    (iota : nat -> Valuation R) (q : bv xlenbits) (Fr : nat -> iProp Σ)
    (n : nat) (anch stride : N)
    (Hea  : loop_extra_pre ls = gen_extra_pre ws fs cs)
    (Hean : loop_extra_post ls = gen_extra_post ws cs)
    (Himm : loop_counter_step ls
            = @bv.of_N xlenbits (bv.exp2 xlenbits - stride))
    (Hk : forall x : ty.RelVal ty_xlenbits,
            inst (T := fun Σ => Term Σ ty_xlenbits) (loop_counter_post_ex ls)
              ((((iota (S n)).["a"∷ty_xlenbits ↦ ty.SyncVal q])
                  .["an"∷ty_xlenbits ↦ ty.SyncVal q])
                 .["c"∷ty_xlenbits ↦ x])
            = ty.SyncVal (@bv.of_N xlenbits (loop_ctr_up anch stride (S n))))
    (Hkn : inst (T := fun Σ => Term Σ ty_xlenbits) (loop_counter_pre ls)
             ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])
           = ty.SyncVal (@bv.of_N xlenbits (loop_ctr_up anch stride n)))
    (Hqan : inst (T := fun Σ => Term Σ ty_xlenbits) (loop_base_post ls)
              (((iota (S n)).["a"∷ty_xlenbits ↦ ty.SyncVal q])
                 .["an"∷ty_xlenbits ↦ ty.SyncVal q])
            = inst (T := fun Σ => Term Σ ty_xlenbits) (loop_base_pre ls)
                ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q]))
    (Hs : (stride <= bv.exp2 xlenbits)%N)
    (Hb : List.Forall (fun b =>
            instprop (formula_relop bop.le
              (term_binop bop.plus (term_unop uop.unsigned (fst b))
                 (term_val ty.int (Z.of_N (snd b))))
              (term_val ty.int (Z.of_N lenAddr)))
              ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])) (loop_all_bounds_pre ls))
    (Hw : List.Forall (fun v => exists x : N,
            inst (T := fun Σ => Term Σ ty_xlenbits)
              (addr_off (@term_var _ (walk_var v) _ (ctx.in_succ (ctx.in_succ (walk_var_in v))))
                 (walk_step v))
              (((iota (S n)).["a"∷ty_xlenbits ↦ ty.SyncVal q])
                 .["an"∷ty_xlenbits ↦ ty.SyncVal q])
            = ty.SyncVal (@bv.of_N xlenbits x)
         /\ inst (T := fun Σ => Term Σ ty_xlenbits)
              (@term_var _ (walk_var v) _ (ctx.in_succ (walk_var_in v)))
              ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])
            = ty.SyncVal (@bv.of_N xlenbits x)) ws)
    (Hf : List.Forall
            (fun f => instprop f ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])) fs)
    (Hc : asn.interpret (gen_cells_post cs)
            (((iota (S n)).["a"∷ty_xlenbits ↦ ty.SyncVal q])
               .["an"∷ty_xlenbits ↦ ty.SyncVal q])
          ∗ Fr (S n)
          ⊢ asn.interpret (gen_cells_pre cs)
              ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q]) ∗ Fr n) :
    loop_back_edge ls iota q Fr n.
  Proof.
    refine (loop_back_edge_std ls ws fs cs iota q Fr n
              (loop_ctr_up anch stride (S n)) (loop_ctr_up anch stride n)
              Hea Hean Hk _ Hkn Hqan Hb Hw Hf Hc).
    rewrite Himm.
    replace (loop_ctr_up anch stride (S n))
      with ((loop_ctr_up anch stride n) + stride)%N
      by (unfold loop_ctr_up; cbn [N.of_nat] in *; lia).
    apply bv_of_N_wrap_dec. exact Hs.
  Qed.

  (* ---- THE WHOLE LOOP, FROM ITS OBLIGATIONS ------------------------------

     The analogue of `cfg_instrs_endToEnd`: everything generic about a counted
     loop is discharged here, and what a caller passes is a fixed list of
     example-specific arguments.  Assembling a loop used to mean writing out
     `loop_body_trip`, `loop_final_trip` and `loop_by_induction` -- three lemmas whose
     statements are mostly re-spelled valuations -- for every example.

     The arguments group as:
       placement  pl              -- ONE `LoopPlace` record (C5): where the
                  segment sits in the program.  Was four arguments plus two
                  bare N's, none of them about the loop;
       the VCs    Hvb/Hvf         -- `solve_param_vc` on body and final;
       the base   Hpl             -- eq_refl whenever iotaf maps "q" to a
                  literal.  Was a PAIR Hpl/Hpa until C4 made the second
                  follow from the first by `inst_loop_base_pre`;
       the count  HP0/HPm         -- the trip predicate survives decrement;
       THE TWO    Hlatch/Hedge    -- the latch (guard + exit guard, as one
                  `loop_latch_obligation`, built by `loop_latch_ptr`/`_ctr`) and the
                  back edge (built by `loop_back_edge_std` above).  Nothing else:
                  the frame lives inside `loop_back_edge`;
       the cut    HOut/Hcont      -- what the loop hands the next segment.

     Both `Hlatch`'s guard half and `Hedge` take `P (S n)`, so a loop whose
     guard needs a no-wrap bound gets it from the trip predicate rather than
     from a side hypothesis. *)
  Lemma loop_runs {R : LCtx} (ls : LoopSpec R)
      (post : Assertion (R ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
      (pl : LoopPlace ls) (Fr : nat -> iProp Σ) (Out Post : iProp Σ)
      (iotaf : nat -> Valuation R) (P : nat -> Prop)
      (Hvb : ValidCFGVerifierContract (loop_body_contract ls))
      (Hvf : ValidCFGVerifierContract (loop_final_contract ls post))
      (* Vacuous today; see loop_one_trip. *)
      (Hbs : forall wds : bv xlenbits -> bv word,
               ⊢ blocksSound wds (instrs_of_list
                   (@bv.of_N xlenbits (place_prog_base pl)) (loop_prog ls)))
      (Hpl : forall n, inst (T := fun Σ => Term Σ ty_xlenbits) (loop_base ls) (iotaf n)
                       = ty.SyncVal (@bv.of_N xlenbits (loop_head_addr ls)))
      (HP0 : P 0) (HPm : forall n, P (S n) -> P n)
      (* guard + exit guard, as the single obligation `loop_latch_obligation`
         (GenSegment): both are the same branch read two ways, and the two
         builders there produce the pair from the loop's counter alone. *)
      (Hlatch : loop_latch_obligation ls iotaf (@bv.of_N xlenbits (loop_head_addr ls)) P)
      (Hedge : forall n, P (S n) ->
             loop_back_edge ls iotaf (@bv.of_N xlenbits (loop_head_addr ls)) Fr n)
      (HOut : Fr 0 ∗ seg_exit_state (loop_final_contract ls post) (iotaf 0)
                     (@bv.of_N xlenbits (loop_head_addr ls)) (loop_prog ls)
                     (@bv.of_N xlenbits (place_prog_base pl))
                     (seg_addr (loop_head_addr ls) (loop_exit_off ls))
              -∗ Out)
      (Hcont : Out -∗ myWP2_loop Post) :
    forall n,
      loop_invariant ls iotaf (@bv.of_N xlenbits (loop_head_addr ls)) Fr
        (loop_instr_block ls pl) P n
      -∗ myWP2_loop Post.
  Proof.
    apply (loop_by_induction ls pl Fr Out Post iotaf P
             (fun n => loop_body_trip ls pl Fr iotaf P n (HPm n)
                         Hvb Hbs (Hpl (S n)) (proj1 Hlatch n) (Hedge n))
             (loop_final_trip ls post pl Fr Out iotaf P HP0 Hvf Hbs
                (Hpl 0) (proj2 Hlatch) HOut)
             Hcont).
  Qed.

End SegCompose.

(* Ltac defined INSIDE a Section does not survive `End`, so these live after
   it.  They need no section variable -- a tactic is syntax. *)
(* ---- THE PER-TRIP LEMMA, as two tactics ---------------------------------
   `seg_run_single_exit` leaves HPre and HPost; these discharge everything in them
   that is not the loop's own arithmetic.  What each leaves behind:
     solve_step_pre  -> the GUARD at trip m (the latch condition)
     solve_step_post -> the counter's DECREMENT (`Hc`, `v`, `Heq` in scope)
   which is exactly the content of a counted for-loop and nothing else.

   `repeat (iDestruct … as "[Hx H]"; iFrame "Hx")` is what makes these
   arity-blind, and the shape of that line is load-bearing.  MEASURED on this
   goal: a NAMED, explicit frame list is 0.35-2.1 s whichever way the
   hypothesis is split (correct arity or over-split), while a BARE `iFrame`
   after splitting does not finish in 300 s -- and `iFrame` on ONE hypothesis
   at a time, with the instruction block still in the goal, also does not
   finish.  So: peel one, frame it BY NAME, repeat; never bare `iFrame`, and
   always after the ambient half has been split off. *)
Ltac solve_step_pre c win instrRes :=
  iIntros "(H & HF & Hpc & Hnpc & Hinstrs)";
  unfold seg_entry, win, extend_to_minimal_pre, instrRes, c;
  iSplitL "HF"; [ iFrame |];
  iSplitR "Hpc Hnpc Hinstrs"; [| iFrame];
  cbn [cfg_precondition gen_seg_contract asn.interpret];
  repeat (iDestruct "H" as "[Hx H]"; iFrame "Hx");
  iFrame "H";
  rewrite ?seg_addr_add; repeat iSplit; try done.

(* The post's TOP-LEVEL shape is prescribed by the blueprint --
   `(counter-block ∗ rest) ∗ minimal_pre`, where the counter block binds a
   fresh variable and states the decrement as a pure equation (§3j).  That is
   why this one is not arity-blind at the top: it is matching a generated
   shape, not guessing. *)
Ltac solve_step_post c inv win instrRes :=
  iIntros "(HF & Hpc & Hnpc & Hinstrs & Hpost)";
  unfold inv, win, instrRes, c;
  iSplitR "HF Hpc Hnpc Hinstrs"; [| iFrame];
  cbn [cfg_postcondition gen_seg_contract asn.interpret];
  iDestruct "Hpost" as "((Hex & Hrest) & Hmin)";
  iDestruct "Hex" as (v) "(Hc & (%Heq & _) & (%Hsl & _))";
  iFrame "Hrest Hmin".


