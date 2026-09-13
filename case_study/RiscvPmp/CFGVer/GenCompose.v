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
(*  WHAT IS AND IS NOT AUTOMATED HERE.  seg_step reduces one loop trip to two  *)
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
   draft of seg_step -- which then could not be supplied by name, because only
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
  Lemma itable_faith_at {R : LCtx} (place : Term R ty_xlenbits) (iota : Valuation R)
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
  Lemma seg_exits_faith {R : LCtx} (place : Term R ty_xlenbits) (iota : Valuation R)
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
  Lemma seg_itable_faith {R : LCtx} (place : Term R ty_xlenbits)
      (iota : Valuation R) (ia : N) (L : list AnnotInstr) (skip take : nat)
      (head bound : N) (targets : list N)
      (Hok : seg_ok L skip head bound targets = true)
      (Hp : inst (T := fun Σ => Term Σ ty_xlenbits) place iota
            = ty.SyncVal (bv.add (@bv.of_N xlenbits ia) (@bv.of_N xlenbits head)))
      (Hwf : seg_wf ia bound) :
    Katamaran.RiscvPmp.CFGVer.VerifierRel.itable_rel (w := wlctx R)
      (instrs_of_list (@bv.of_N xlenbits ia) L)
      (table_of_list place 0 (List.firstn take (List.skipn skip L))) iota.
  Proof.
    exact (itable_faith_at place iota (@bv.of_N xlenbits ia) L skip take head
             (seg_ok_off L skip head bound targets Hok)
             (seg_ok_skip L skip head bound targets Hok)
             Hp
             (seg_wf_rep ia bound L (seg_ok_sz L skip head bound targets Hok) Hwf)).
  Qed.

  Lemma seg_etable_faith {R : LCtx} (place : Term R ty_xlenbits)
      (iota : Valuation R) (ia : N) (L : list AnnotInstr) (skip : nat)
      (head bound : N) (targets : list N)
      (Hok : seg_ok L skip head bound targets = true)
      (Hp : inst (T := fun Σ => Term Σ ty_xlenbits) place iota
            = ty.SyncVal (bv.add (@bv.of_N xlenbits ia) (@bv.of_N xlenbits head))) :
    Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx R)
      (seg_exitCond ia targets)
      (exits_of_offs place (List.map (fun t => (t - head)%N) targets)) iota.
  Proof.
    exact (seg_exits_faith place iota ia head targets
             (seg_ok_tgts L skip head bound targets Hok) Hp).
  Qed.

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
  Lemma seg_step {R : LCtx} (c : @CFGVerifierContract R) (iota : Valuation R)
    (a : bv xlenbits) (L : list AnnotInstr) (cbase : bv xlenbits) (Fr : iProp Σ)
    {Pre Post : iProp Σ}
    (Hv : ValidCFGVerifierContract c)
    (Hif : Katamaran.RiscvPmp.CFGVer.VerifierRel.itable_rel (w := wlctx R)
             (instrs_of_list cbase L)
             (table_of_list (cfg_placement c) 0 (cfg_instrs c)) iota)
    (Hef : Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx R)
             (cfg_exitCond c) (cfg_exits c) iota)
    (HPre  : Pre -∗ Fr ∗ seg_entry c iota a L cbase)
    (HPost : forall an, Fr ∗ seg_exit c iota a L cbase an -∗ Post) :
    Pre -∗ myWP2_loop Post.
  Proof.
    iIntros "HP".
    iDestruct (HPre with "HP") as "(HF & Hpre & Hpc & Hnpc & Hinstrs)".
    iApply (sound_scfg_verification_condition_myWP2 (seg_vc c Hv) Post Hif Hef
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
  Definition seg_exit_at {R : LCtx} (c : @CFGVerifierContract R) (iota : Valuation R)
      (a : bv xlenbits) (L : list AnnotInstr) (cbase : bv xlenbits)
      (v : bv xlenbits) : iProp Σ :=
    ( pc ↦ᵣ SyncVal v
      ∗ (bi_exist (fun u => nextpc ↦ᵣ u))
      ∗ Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs
          (ai_instr <$> instrs_of_list cbase L)
      ∗ asn.interpret (cfg_postcondition c)
          ((iota.["a"∷ty_xlenbits ↦ SyncVal a]).["an"∷ty_xlenbits ↦ SyncVal v]) )%I.

  Lemma seg_step1 {R : LCtx} (c : @CFGVerifierContract R) (iota : Valuation R)
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
    (HPre  : Pre -∗ Fr ∗ seg_entry c iota a L cbase)
    (HPost : Fr ∗ seg_exit_at c iota a L cbase (seg_addr ia t) -∗ Post) :
    Pre -∗ myWP2_loop Post.
  Proof.
    apply (seg_step c iota a L cbase Fr Hv Hif Hef HPre).
    iIntros (an) "H".
    destruct an as [av | a1 a2].
    2:{ iDestruct "H" as "(_ & %Hf & _)". destruct Hf. }
    iDestruct "H" as "(HF & %Hex & Hpc & Hnpc & Hinstrs & Hpost)".
    rewrite Hec in Hex. apply seg_exitCond_inv1 in Hex. subst av.
    iApply HPost. unfold seg_exit_at. iFrame.
  Qed.

  (* SEQUENTIAL composition: run one segment, then continue.  This is the
     shape the STRAIGHT-LINE cuts need -- nine of muladd's fourteen segments,
     i.e. most of the remaining work -- and it is what the hand-written tail
     spelled out per link as linkN / linkFN.  Trivial on top of
     myWP2_loop_bind, but it is exactly the kind of five-line wrapper that
     otherwise gets re-derived at every call site (which is how the 21 copies
     of the register builder happened). *)
  Lemma seg_seq (Pre Mid Post : iProp Σ)
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
     seg_exits_faith's head-shifted form does not apply definitionally
     (`t - 0` and `q +b of_N 0` are both stuck on a symbolic argument). *)
  Lemma seg_exits_faith0 {R : LCtx} (place : Term R ty_xlenbits)
      (iota : Valuation R) (iq : N) (targets : list N)
      (Hp : inst (T := fun Σ => Term Σ ty_xlenbits) place iota
            = ty.SyncVal (@bv.of_N xlenbits iq)) :
    Katamaran.RiscvPmp.CFGVer.VerifierRel.etable_rel (w := wlctx R)
      (seg_exitCond iq targets) (exits_of_offs place targets) iota.
  Proof.
    apply etable_faith_exits_of_offs with (cbase := @bv.of_N xlenbits iq);
      [exact Hp |].
    (* NB: offs IS targets here -- there is no `map (.- head)` to invert, unlike
       seg_exits_faith.  Copying its `in_map_iff` line does not typecheck. *)
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
  Definition loop_inv {R : LCtx} (ls : LoopSpec R)
      (iotaf : nat -> Valuation R) (q : bv xlenbits)
      (Fr : nat -> iProp Σ) (Instrs : iProp Σ) (P : nat -> Prop) (n : nat)
      : iProp Σ :=
    ( bi_pure (P n)
      ∗ asn.interpret (gen_loop_win ls)
        ((iotaf n).["a"∷ty_xlenbits ↦ ty.SyncVal q])
      ∗ Fr n ∗ pc ↦ᵣ ty.SyncVal q
      ∗ (bi_exist (fun v => nextpc ↦ᵣ v))
      ∗ Instrs )%I.

  (* ---- ONE TRIP ---------------------------------------------------------- *)

  (* Everything generic is discharged here.  What the caller supplies is
     exactly the loop's own content:
       Hpl/Hpa : the valuation family pins the code base (reflexivity in
                 practice, since a caller's iotaf maps "q" to a literal);
       Hg      : the GUARD holds at trip S n -- one arithmetic fact;
       Htrans  : one trip's POSTcondition establishes the next trip's
                 invariant -- the counter decremented and the frame moved on.
     Htrans is where a sliding footprint lives: the contract is
     trip-independent, and iotaf moves the pointers. *)
  Lemma loop_step {R : LCtx} (ls : LoopSpec R) (pia pbound : N)
      (Fr : nat -> iProp Σ) (iotaf : nat -> Valuation R) (P : nat -> Prop)
      (n : nat)
      (HPm : P (S n) -> P n)
      (Hq : @bv.of_N xlenbits (ls_iq ls)
            = bv.add (@bv.of_N xlenbits pia)
                (@bv.of_N xlenbits (4 * N.of_nat (ls_skip ls))))
      (Hok : seg_ok (ls_prog ls) (ls_skip ls)
               (4 * N.of_nat (ls_skip ls))%N pbound [0%N] = true)
      (Hwf : seg_wf pia pbound)
      (Hv  : ValidCFGVerifierContract (loop_body ls))
      (Hpl : inst (T := fun Σ => Term Σ ty_xlenbits) (ls_q ls) (iotaf (S n))
             = ty.SyncVal (@bv.of_N xlenbits (ls_iq ls)))
      (Hpa : inst (T := fun Σ => Term Σ ty_xlenbits) (ls_q_a ls)
               ((iotaf (S n)).["a"∷ty_xlenbits
                  ↦ ty.SyncVal (@bv.of_N xlenbits (ls_iq ls))])
             = ty.SyncVal (@bv.of_N xlenbits (ls_iq ls)))
      (Hg  : P (S n) ->
             instprop (ls_guard ls (ls_step (ls_imm ls) (ls_k_a ls)))
               ((iotaf (S n)).["a"∷ty_xlenbits
                  ↦ ty.SyncVal (@bv.of_N xlenbits (ls_iq ls))]))
      (Htrans : P (S n) ->
         asn.interpret (cfg_postcondition (loop_body ls))
           (((iotaf (S n)).["a"∷ty_xlenbits
               ↦ ty.SyncVal (@bv.of_N xlenbits (ls_iq ls))])
              .["an"∷ty_xlenbits ↦ ty.SyncVal (@bv.of_N xlenbits (ls_iq ls))])
         ∗ Fr (S n)
         ⊢ asn.interpret (gen_loop_win ls)
             ((iotaf n).["a"∷ty_xlenbits
                ↦ ty.SyncVal (@bv.of_N xlenbits (ls_iq ls))])
           ∗ Fr n) :
    loop_inv ls iotaf (@bv.of_N xlenbits (ls_iq ls)) Fr
      (Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs
         (ai_instr <$> instrs_of_list (@bv.of_N xlenbits pia) (ls_prog ls)))
      P (S n)
    -∗ myWP2_loop (loop_inv ls iotaf (@bv.of_N xlenbits (ls_iq ls)) Fr
         (Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs
            (ai_instr <$> instrs_of_list (@bv.of_N xlenbits pia) (ls_prog ls)))
         P n).
  Proof.
    (* Peel the pure side condition FIRST: the two bullets are separate goals,
       so an iIntros inside HPre would not scope over HPost, and HPost is
       where P n has to be re-established. *)
    unfold loop_inv at 1.
    iIntros "(%HP & H)".
    iApply (seg_step1 (loop_body ls) (iotaf (S n))
             (@bv.of_N xlenbits (ls_iq ls)) (ls_prog ls)
             (@bv.of_N xlenbits pia) (Fr (S n)) (ls_iq ls) 0%N eq_refl Hv
             (seg_itable_faith (cfg_placement (loop_body ls)) (iotaf (S n))
                pia (ls_prog ls) (ls_skip ls) (ls_take ls)
                (4 * N.of_nat (ls_skip ls))%N pbound [0%N] Hok
                ltac:(cbn [cfg_placement loop_body gen_loop_contract];
                      rewrite Hpl; now rewrite Hq) Hwf)
             (seg_exits_faith0 (cfg_placement (loop_body ls)) (iotaf (S n))
                (ls_iq ls) [0%N] Hpl) with "H").
    - (* HPre: the invariant IS the precondition minus the branch decision, at
         the SAME valuation, so one iFrame takes it whole. *)
      unfold seg_entry, extend_to_minimal_pre, gen_loop_win.
      iIntros "(H & HF & Hpc & Hnpc & Hinstrs)".
      iSplitL "HF"; [ iFrame |].
      iSplitR "Hpc Hnpc Hinstrs"; [| iFrame].
      cbn [cfg_precondition loop_body gen_loop_contract gen_loop_pre
           asn.interpret].
      iDestruct "H" as "[Hcore Hmin]".
      iFrame "Hcore Hmin".
      unfold asn_pc_eq; cbn.
      iSplit; [iPureIntro; now rewrite Hpa |].
      iSplit; [iPureIntro; exact (Hg HP) | done].
    - (* HPost: frame the ambient half, then the caller's transfer. *)
      unfold loop_inv, seg_exit_at.
      rewrite seg_addr_0.
      iIntros "(HF & Hpc & Hnpc & Hinstrs & Hpost)".
      iSplit; [iPureIntro; exact (HPm HP) |].
      iDestruct ((Htrans HP) with "[$Hpost $HF]") as "(Hwin & HFn)".
      iFrame.
  Qed.

  (* ---- THE EXIT TRIP ------------------------------------------------------ *)

  (* Same shape, with the exit guard and the fall-through target.  `Out` is
     whatever the caller wants to hand the next segment -- this is the cut out
     of the loop, and it is genuine specification. *)
  Lemma loop_exit {R : LCtx} (ls : LoopSpec R)
      (post : Assertion (R ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
      (pia pbound : N) (Fr : nat -> iProp Σ) (Out : iProp Σ)
      (iotaf : nat -> Valuation R)
      (P : nat -> Prop) (HP0 : P 0)
      (Hq : @bv.of_N xlenbits (ls_iq ls)
            = bv.add (@bv.of_N xlenbits pia)
                (@bv.of_N xlenbits (4 * N.of_nat (ls_skip ls))))
      (Hok : seg_ok (ls_prog ls) (ls_skip ls)
               (4 * N.of_nat (ls_skip ls))%N pbound [ls_exit ls] = true)
      (Hwf : seg_wf pia pbound)
      (Hv  : ValidCFGVerifierContract (loop_final ls post))
      (Hpl : inst (T := fun Σ => Term Σ ty_xlenbits) (ls_q ls) (iotaf 0)
             = ty.SyncVal (@bv.of_N xlenbits (ls_iq ls)))
      (Hpa : inst (T := fun Σ => Term Σ ty_xlenbits) (ls_q_a ls)
               ((iotaf 0).["a"∷ty_xlenbits
                  ↦ ty.SyncVal (@bv.of_N xlenbits (ls_iq ls))])
             = ty.SyncVal (@bv.of_N xlenbits (ls_iq ls)))
      (Hg  : instprop (ls_exitg ls (ls_step (ls_imm ls) (ls_k_a ls)))
               ((iotaf 0).["a"∷ty_xlenbits
                  ↦ ty.SyncVal (@bv.of_N xlenbits (ls_iq ls))]))
      (HOut : Fr 0 ∗ seg_exit_at (loop_final ls post) (iotaf 0)
                     (@bv.of_N xlenbits (ls_iq ls)) (ls_prog ls)
                     (@bv.of_N xlenbits pia)
                     (seg_addr (ls_iq ls) (ls_exit ls))
              -∗ Out) :
    loop_inv ls iotaf (@bv.of_N xlenbits (ls_iq ls)) Fr
      (Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs
         (ai_instr <$> instrs_of_list (@bv.of_N xlenbits pia) (ls_prog ls)))
      P 0
    -∗ myWP2_loop Out.
  Proof.
    apply (seg_step1 (loop_final ls post) (iotaf 0)
             (@bv.of_N xlenbits (ls_iq ls)) (ls_prog ls)
             (@bv.of_N xlenbits pia) (Fr 0) (ls_iq ls) (ls_exit ls) eq_refl Hv
             (seg_itable_faith (cfg_placement (loop_final ls post)) (iotaf 0)
                pia (ls_prog ls) (ls_skip ls) (ls_take ls)
                (4 * N.of_nat (ls_skip ls))%N pbound [ls_exit ls] Hok
                ltac:(cbn [cfg_placement loop_final gen_loop_contract];
                      rewrite Hpl; now rewrite Hq) Hwf)
             (seg_exits_faith0 (cfg_placement (loop_final ls post)) (iotaf 0)
                (ls_iq ls) [ls_exit ls] Hpl)).
    - unfold loop_inv, seg_entry, extend_to_minimal_pre, gen_loop_win.
      iIntros "(_ & H & HF & Hpc & Hnpc & Hinstrs)".
      iSplitL "HF"; [ iFrame |].
      iSplitR "Hpc Hnpc Hinstrs"; [| iFrame].
      cbn [cfg_precondition loop_final gen_loop_contract gen_loop_pre
           asn.interpret].
      iDestruct "H" as "[Hcore Hmin]".
      iFrame "Hcore Hmin".
      unfold asn_pc_eq; cbn.
      iSplit; [iPureIntro; now rewrite Hpa |].
      iSplit; [iPureIntro; exact Hg | done].
    - exact HOut.
  Qed.

  (* ---- THE WHOLE LOOP ----------------------------------------------------- *)

  (* seg_loop, instantiated.  Given a step for every trip and an exit, the
     loop runs to its continuation. *)
  Lemma loop_counted {R : LCtx} (ls : LoopSpec R) (pia : N)
      (Fr : nat -> iProp Σ) (Out Post : iProp Σ)
      (iotaf : nat -> Valuation R) (P : nat -> Prop)
      (Hstep : forall n,
         loop_inv ls iotaf (@bv.of_N xlenbits (ls_iq ls)) Fr
           (Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs
              (ai_instr <$> instrs_of_list (@bv.of_N xlenbits pia) (ls_prog ls)))
           P (S n)
         -∗ myWP2_loop (loop_inv ls iotaf (@bv.of_N xlenbits (ls_iq ls)) Fr
              (Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs
                 (ai_instr <$> instrs_of_list (@bv.of_N xlenbits pia)
                    (ls_prog ls))) P n))
      (Hexit :
         loop_inv ls iotaf (@bv.of_N xlenbits (ls_iq ls)) Fr
           (Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs
              (ai_instr <$> instrs_of_list (@bv.of_N xlenbits pia) (ls_prog ls)))
           P 0
         -∗ myWP2_loop Out)
      (Hcont : Out -∗ myWP2_loop Post) :
    forall n,
      loop_inv ls iotaf (@bv.of_N xlenbits (ls_iq ls)) Fr
        (Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs
           (ai_instr <$> instrs_of_list (@bv.of_N xlenbits pia) (ls_prog ls)))
        P n
      -∗ myWP2_loop Post.
  Proof. apply (seg_loop _ Out Post Hstep Hexit Hcont). Qed.

  (* ---- THE TRANSFER, GENERICALLY ----------------------------------------

     `loop_step`'s `Htrans` -- one trip's postcondition establishes the next
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
     existential's witness because `ls_k_anc` sits under the post's binder;
     in practice it does not mention "c" and the caller passes `fun _ => _`. *)
  Lemma loop_trans {R : LCtx} (ls : LoopSpec R) (iS iN : Valuation R)
    (q : bv xlenbits) (kv w : N) (FS Fn : iProp Σ)
    (Hk : forall x : ty.RelVal ty_xlenbits,
            inst (T := fun Σ => Term Σ ty_xlenbits) (ls_k_anc ls)
              (((iS.["a"∷ty_xlenbits ↦ ty.SyncVal q]).["an"∷ty_xlenbits ↦ ty.SyncVal q])
                 .["c"∷ty_xlenbits ↦ x])
            = ty.SyncVal (@bv.of_N xlenbits kv))
    (Hstep : bv.add (@bv.of_N xlenbits kv) (ls_imm ls) = @bv.of_N xlenbits w)
    (Hkn : inst (T := fun Σ => Term Σ ty_xlenbits) (ls_k_a ls)
             (iN.["a"∷ty_xlenbits ↦ ty.SyncVal q])
           = ty.SyncVal (@bv.of_N xlenbits w))
    (Hframe : asn.interpret (gen_loop_frame_an ls)
                ((iS.["a"∷ty_xlenbits ↦ ty.SyncVal q]).["an"∷ty_xlenbits ↦ ty.SyncVal q])
              ∗ FS
              ⊢ asn.interpret (gen_loop_frame_a ls) (iN.["a"∷ty_xlenbits ↦ ty.SyncVal q])
                ∗ Fn) :
    asn.interpret (cfg_postcondition (loop_body ls))
      ((iS.["a"∷ty_xlenbits ↦ ty.SyncVal q]).["an"∷ty_xlenbits ↦ ty.SyncVal q])
    ∗ FS
    ⊢ asn.interpret (gen_loop_win ls) (iN.["a"∷ty_xlenbits ↦ ty.SyncVal q]) ∗ Fn.
  Proof.
    cbn [cfg_postcondition loop_body gen_loop_contract].
    unfold gen_loop_win, gen_loop_core, gen_loop_post.
    iIntros "(((Hex & Hfr) & Hmin) & HFS)".
    iDestruct "Hex" as (v) "(Hc & (%Heq & _) & (%Hsl & _))".
    destruct v as [w' | va vb]; [| destruct Hsl].
    cbn in Heq. rewrite (Hk (ty.SyncVal w')) in Heq. cbn in Heq.
    rewrite Hstep in Heq. subst w'.
    cbn [asn.interpret].
    assert (Hc2 : inst (T := fun Σ => Term Σ ty_xlenbits) (term_var "c")
                    (((iS.["a"∷ty_xlenbits ↦ ty.SyncVal q]).["an"∷ty_xlenbits ↦ ty.SyncVal q])
                       .["c"∷ty_xlenbits ↦ ty.SyncVal (@bv.of_N xlenbits w)])
                  = inst (T := fun Σ => Term Σ ty_xlenbits) (ls_k_a ls)
                      (iN.["a"∷ty_xlenbits ↦ ty.SyncVal q]))
      by (cbn; now rewrite Hkn).
    rewrite <- (asn_regidx_pts_inst (ls_ctr ls) (term_var "c") (ls_k_a ls) _ _ Hc2).
    iDestruct (Hframe with "[$Hfr $HFS]") as "(Hfr' & HFn)".
    iSplitR "HFn"; [| iExact "HFn"].
    iSplitR "Hmin"; [| iExact "Hmin"].
    iSplitL "Hc"; [iExact "Hc" |].
    iSplitR; [iPureIntro; cbn; now rewrite Hkn |].
    iExact "Hfr'".
  Qed.

  (* ---- THE RESERVOIR -----------------------------------------------------

     An ARRAY loop cannot close its own back edge with a trip-independent
     frame: the body consumes the cell at the current pointer and the next
     trip needs the cell at the next one, which was never in the frame.  The
     reservoir is where the not-yet-reached cells live, and `loop_inv`'s `Fr`
     is trip-indexed so that it can hold them.

     The definition avoids ALL binder machinery by a trick: the cells trip i
     needs are, by construction, `A` interpreted at trip i's own valuation --
     so the reservoir is just that assertion at every future trip, and peeling
     one off is `big_sepL`'s app lemma.  `A` is the CELL half of the loop's
     `ls_extra_a`; the carried half (registers, pure facts) crosses the back
     edge in the frame as usual. *)
  Definition loop_res {R : LCtx} (A : Assertion (R ▻ "a"∷ty_xlenbits))
      (iota : nat -> Valuation R) (q : bv xlenbits) (n : nat) : iProp Σ :=
    ([∗ list] i ∈ seq 0 n,
       asn.interpret A ((iota i).["a"∷ty_xlenbits ↦ ty.SyncVal q]))%I.

  Lemma loop_res_peel {R : LCtx} (A : Assertion (R ▻ "a"∷ty_xlenbits))
      (iota : nat -> Valuation R) (q : bv xlenbits) (n : nat) :
    loop_res A iota q (S n)
    ⊣⊢ loop_res A iota q n
        ∗ asn.interpret A ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q]).
  Proof.
    unfold loop_res. rewrite seq_S. rewrite big_opL_app. cbn.
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

  Lemma loop_frame_std {R : LCtx} (ls : LoopSpec R) (iS iN : Valuation R)
    (q : bv xlenbits) (FS Fn : iProp Σ)
    (Hq : inst (T := fun Σ => Term Σ ty_xlenbits) (ls_q_an ls)
            ((iS.["a"∷ty_xlenbits ↦ ty.SyncVal q]).["an"∷ty_xlenbits ↦ ty.SyncVal q])
          = inst (T := fun Σ => Term Σ ty_xlenbits) (ls_q_a ls)
              (iN.["a"∷ty_xlenbits ↦ ty.SyncVal q]))
    (Hb : List.Forall (fun b =>
            instprop (formula_relop bop.le
              (term_binop bop.plus (term_unop uop.unsigned (fst b))
                 (term_val ty.int (Z.of_N (snd b))))
              (term_val ty.int (Z.of_N lenAddr)))
              (iN.["a"∷ty_xlenbits ↦ ty.SyncVal q])) (ls_bases_a ls))
    (Hex : asn.interpret (ls_extra_an ls)
             ((iS.["a"∷ty_xlenbits ↦ ty.SyncVal q]).["an"∷ty_xlenbits ↦ ty.SyncVal q])
           ∗ FS
           ⊢ asn.interpret (ls_extra_a ls) (iN.["a"∷ty_xlenbits ↦ ty.SyncVal q]) ∗ Fn) :
    asn.interpret (gen_loop_frame_an ls)
      ((iS.["a"∷ty_xlenbits ↦ ty.SyncVal q]).["an"∷ty_xlenbits ↦ ty.SyncVal q])
    ∗ FS
    ⊢ asn.interpret (gen_loop_frame_a ls) (iN.["a"∷ty_xlenbits ↦ ty.SyncVal q]) ∗ Fn.
  Proof.
    unfold gen_loop_frame_an, gen_loop_frame_a. cbn [asn.interpret].
    iIntros "((_ & Hregs & Hex') & HFS)".
    iDestruct (Hex with "[$Hex' $HFS]") as "(Hea & HFn)".
    iSplitR "HFn"; [| iExact "HFn"].
    iSplitR; [iApply gen_loop_bounds_intro; exact Hb |].
    iSplitL "Hregs"; [| iExact "Hea"].
    iApply (bi.equiv_entails_1_1 _ _
              (gen_regs_at_inst (ls_q_an ls) (ls_q_a ls) _ _ (ls_regs ls) Hq)).
    iExact "Hregs".
  Qed.

  (* ---- THE TWO OBLIGATIONS, NAMED ---------------------------------------

     What a caller proves per loop is exactly these two, and without a name
     each one's STATEMENT is a dozen lines of re-spelled valuation.  Same
     disease, same cure, as `dvInv` for the assembly block. *)
  Definition loop_frame_obl {R : LCtx} (ls : LoopSpec R)
      (iota : nat -> Valuation R) (q : bv xlenbits) (Fr : nat -> iProp Σ)
      (n : nat) : Prop :=
    asn.interpret (gen_loop_frame_an ls)
      (((iota (S n)).["a"∷ty_xlenbits ↦ ty.SyncVal q]).["an"∷ty_xlenbits ↦ ty.SyncVal q])
    ∗ Fr (S n)
    ⊢ asn.interpret (gen_loop_frame_a ls)
        ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])
      ∗ Fr n.

  Definition loop_edge {R : LCtx} (ls : LoopSpec R)
      (iota : nat -> Valuation R) (q : bv xlenbits) (Fr : nat -> iProp Σ)
      (n : nat) : Prop :=
    asn.interpret (cfg_postcondition (loop_body ls))
      (((iota (S n)).["a"∷ty_xlenbits ↦ ty.SyncVal q]).["an"∷ty_xlenbits ↦ ty.SyncVal q])
    ∗ Fr (S n)
    ⊢ asn.interpret (gen_loop_win ls)
        ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])
      ∗ Fr n.

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
              (addr_off (@term_var _ (wr_var w) _ (ctx.in_succ (ctx.in_succ (wr_in w))))
                 (wr_off w))
              ((iS.["a"∷ty_xlenbits ↦ ty.SyncVal q]).["an"∷ty_xlenbits ↦ ty.SyncVal q])
            = ty.SyncVal (@bv.of_N xlenbits x)
         /\ inst (T := fun Σ => Term Σ ty_xlenbits)
              (@term_var _ (wr_var w) _ (ctx.in_succ (wr_in w)))
              (iN.["a"∷ty_xlenbits ↦ ty.SyncVal q])
            = ty.SyncVal (@bv.of_N xlenbits x)) ws) :
    asn.interpret (gen_walk_an ws)
      ((iS.["a"∷ty_xlenbits ↦ ty.SyncVal q]).["an"∷ty_xlenbits ↦ ty.SyncVal q])
    ⊢ asn.interpret (gen_walk_a ws) (iN.["a"∷ty_xlenbits ↦ ty.SyncVal q]).
  Proof.
    induction ws as [| w ws IH]; cbn [gen_walk_an gen_walk_a List.fold_right].
    - iIntros "_". iSplit; [iPureIntro; cbn; reflexivity | done].
    - inversion Hw as [| ?? Hh Ht]; subst.
      destruct Hh as (x & Hx & Hy).
      destruct (wr_pub w); cbn [asn.interpret].
      + iIntros "(Hr & Hsl & Hrest)".
        iSplitL "Hr";
          [ iApply (loop_reg_shift (wr_reg w) _ _ _ _ x x Hx Hy eq_refl); iExact "Hr" |].
        iSplitR;
          [ iSplit; [ iPureIntro; exact (walk_secLeak _ _ _ x Hy) | done ] |].
        iApply (IH Ht). iExact "Hrest".
      + iIntros "(Hr & Hrest)".
        iSplitL "Hr";
          [ iApply (loop_reg_shift (wr_reg w) _ _ _ _ x x Hx Hy eq_refl); iExact "Hr" |].
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

  Lemma loop_extra_step {R : LCtx} (ws : list (walk_reg R))
    (fs : list (Formula (R ▻ "a"∷ty_xlenbits))) (cs : list (cell_spec R))
    (iS iN : Valuation R) (q : bv xlenbits) (FS Fn : iProp Σ)
    (Hw : List.Forall (fun w => exists x : N,
            inst (T := fun Σ => Term Σ ty_xlenbits)
              (addr_off (@term_var _ (wr_var w) _ (ctx.in_succ (ctx.in_succ (wr_in w))))
                 (wr_off w))
              ((iS.["a"∷ty_xlenbits ↦ ty.SyncVal q]).["an"∷ty_xlenbits ↦ ty.SyncVal q])
            = ty.SyncVal (@bv.of_N xlenbits x)
         /\ inst (T := fun Σ => Term Σ ty_xlenbits)
              (@term_var _ (wr_var w) _ (ctx.in_succ (wr_in w)))
              (iN.["a"∷ty_xlenbits ↦ ty.SyncVal q])
            = ty.SyncVal (@bv.of_N xlenbits x)) ws)
    (Hf : List.Forall (fun f => instprop f (iN.["a"∷ty_xlenbits ↦ ty.SyncVal q])) fs)
    (Hc : asn.interpret (gen_cells_an cs)
            ((iS.["a"∷ty_xlenbits ↦ ty.SyncVal q]).["an"∷ty_xlenbits ↦ ty.SyncVal q])
          ∗ FS
          ⊢ asn.interpret (gen_cells_a cs) (iN.["a"∷ty_xlenbits ↦ ty.SyncVal q]) ∗ Fn) :
    asn.interpret (gen_extra_an ws cs)
      ((iS.["a"∷ty_xlenbits ↦ ty.SyncVal q]).["an"∷ty_xlenbits ↦ ty.SyncVal q])
    ∗ FS
    ⊢ asn.interpret (gen_extra_a ws fs cs) (iN.["a"∷ty_xlenbits ↦ ty.SyncVal q]) ∗ Fn.
  Proof.
    unfold gen_extra_an, gen_extra_a. cbn [asn.interpret].
    iIntros "((Hw' & Hc') & HFS)".
    iDestruct (Hc with "[$Hc' $HFS]") as "(Hca & HFn)".
    iSplitR "HFn"; [| iExact "HFn"].
    iSplitL "Hw'"; [ iApply (gen_walk_step ws iS iN q Hw); iExact "Hw'" |].
    iApply (gen_pures_interp fs (gen_cells_a cs) _ Hf). iExact "Hca".
  Qed.

  (* ---- WHERE THE RESERVOIR COMES FROM ------------------------------------

     Everything above ASSUMES the reservoir: `loop_inv` carries `Fr n`, the
     trip step trades with it, and at trip 0 it is empty.  Nothing so far said
     where a caller GETS one, which is what a real program proof has to supply
     before it can instantiate any of this.

     `loop_res_intro` is the general answer: a reservoir IS a block of per-trip
     resources, so producing one is producing `A` at each future trip's
     valuation.  `loop_res_words` is the case that actually occurs -- a loop
     walking an array of words -- where the block is n memory cells at
     addresses the caller computes, and the per-trip obligation collapses to
     one arithmetic fact about `addr i`. *)

  Lemma loop_res_intro {R : LCtx} (A : Assertion (R ▻ "a"∷ty_xlenbits))
    (iota : nat -> Valuation R) (q : bv xlenbits) (n : nat) (blk : nat -> iProp Σ)
    (H : forall i,
           blk i ⊢ asn.interpret A ((iota i).["a"∷ty_xlenbits ↦ ty.SyncVal q])) :
    ([∗ list] i ∈ seq 0 n, blk i) ⊢ loop_res A iota q n.
  Proof.
    unfold loop_res. apply big_sepL_mono. intros k i _. apply H.
  Qed.

  (* one word of memory at a PUBLIC address, contents arbitrary *)
  Definition mem_word (a : bv xlenbits) : iProp Σ :=
    asn.interpret (Σ := ["p"∷ty_xlenbits])
      (asn.exist "w" ty_xlenbits (term_var "p" ↦ₘ term_var "w"))
      ([env].["p"∷ty_xlenbits ↦ ty.SyncVal a]).

  Lemma loop_res_words {R : LCtx} (c : cell_spec R) (iota : nat -> Valuation R)
    (q : bv xlenbits) (n : nat) (addr : nat -> bv xlenbits)
    (Hpub : cs_pub c = false)
    (Haddr : forall i (v : ty.RelVal (ty.bvec (bytes_per_word * byte))),
       inst (T := fun Σ => Term Σ ty_xlenbits)
         (addr_off (@term_var _ (cs_var c) _ (ctx.in_succ (ctx.in_succ (cs_in c))))
            (cs_off c))
         ((((iota i).["a"∷ty_xlenbits ↦ ty.SyncVal q]))
            .[cs_bind c ∷ty.bvec (bytes_per_word * byte) ↦ v])
       = ty.SyncVal (addr i)) :
    ([∗ list] i ∈ seq 0 n, mem_word (addr i)) ⊢ loop_res (gen_cells_a [c]) iota q n.
  Proof.
    unfold loop_res. apply big_sepL_mono. intros k i _.
    unfold mem_word.
    cbn [gen_cells_a List.fold_right asn.interpret].
    rewrite Hpub.
    iIntros "H". iSplitL "H"; [| iSplit; [iPureIntro; cbn; reflexivity | done]].
    iApply (bi.equiv_entails_1_1 _ _
              (asn_cell_inst "w" (cs_bind c) (term_var "p")
                 (addr_off (@term_var _ (cs_var c) _ (ctx.in_succ (ctx.in_succ (cs_in c))))
                    (cs_off c))
                 ([env].["p"∷ty_xlenbits ↦ ty.SyncVal (addr i)])
                 ((iota i).["a"∷ty_xlenbits ↦ ty.SyncVal q])
                 ltac:(intros v; cbn; symmetry; exact (Haddr i v)))).
    iExact "H".
  Qed.

  (* ---- THE EDGE, FROM THE DATA ------------------------------------------

     `loop_edge` is a Prop, so it can be BUILT rather than proved by hand.
     Every counted loop whose extra is data (GenSegment §5) gets its back edge
     from exactly this composition -- loop_trans over loop_frame_std over
     loop_extra_step -- and the caller is left with the six facts that are
     genuinely its own:

       Hk/Hstep/Hkn : the counter's arithmetic across the trip;
       Hqan         : the code base is the same on both sides (eq_refl);
       Hb           : each base is in range at trip n;
       Hw/Hf/Hc     : the walk, the dropped pure facts, the reservoir trade.

     `Hea`/`Hean` are `eq_refl` whenever `ls_extra_*` was defined as the
     generator applied to the loop's own lists, which is the point of defining
     them that way. *)
  Lemma loop_edge_std {R : LCtx} (ls : LoopSpec R)
    (ws : list (walk_reg R)) (fs : list (Formula (R ▻ "a"∷ty_xlenbits)))
    (cs : list (cell_spec R))
    (iota : nat -> Valuation R) (q : bv xlenbits) (Fr : nat -> iProp Σ)
    (n : nat) (kv w : N)
    (Hea  : ls_extra_a ls = gen_extra_a ws fs cs)
    (Hean : ls_extra_an ls = gen_extra_an ws cs)
    (Hk : forall x : ty.RelVal ty_xlenbits,
            inst (T := fun Σ => Term Σ ty_xlenbits) (ls_k_anc ls)
              ((((iota (S n)).["a"∷ty_xlenbits ↦ ty.SyncVal q])
                  .["an"∷ty_xlenbits ↦ ty.SyncVal q])
                 .["c"∷ty_xlenbits ↦ x])
            = ty.SyncVal (@bv.of_N xlenbits kv))
    (Hstep : bv.add (@bv.of_N xlenbits kv) (ls_imm ls) = @bv.of_N xlenbits w)
    (Hkn : inst (T := fun Σ => Term Σ ty_xlenbits) (ls_k_a ls)
             ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])
           = ty.SyncVal (@bv.of_N xlenbits w))
    (Hqan : inst (T := fun Σ => Term Σ ty_xlenbits) (ls_q_an ls)
              (((iota (S n)).["a"∷ty_xlenbits ↦ ty.SyncVal q])
                 .["an"∷ty_xlenbits ↦ ty.SyncVal q])
            = inst (T := fun Σ => Term Σ ty_xlenbits) (ls_q_a ls)
                ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q]))
    (Hb : List.Forall (fun b =>
            instprop (formula_relop bop.le
              (term_binop bop.plus (term_unop uop.unsigned (fst b))
                 (term_val ty.int (Z.of_N (snd b))))
              (term_val ty.int (Z.of_N lenAddr)))
              ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])) (ls_bases_a ls))
    (Hw : List.Forall (fun v => exists x : N,
            inst (T := fun Σ => Term Σ ty_xlenbits)
              (addr_off (@term_var _ (wr_var v) _ (ctx.in_succ (ctx.in_succ (wr_in v))))
                 (wr_off v))
              (((iota (S n)).["a"∷ty_xlenbits ↦ ty.SyncVal q])
                 .["an"∷ty_xlenbits ↦ ty.SyncVal q])
            = ty.SyncVal (@bv.of_N xlenbits x)
         /\ inst (T := fun Σ => Term Σ ty_xlenbits)
              (@term_var _ (wr_var v) _ (ctx.in_succ (wr_in v)))
              ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])
            = ty.SyncVal (@bv.of_N xlenbits x)) ws)
    (Hf : List.Forall
            (fun f => instprop f ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])) fs)
    (Hc : asn.interpret (gen_cells_an cs)
            (((iota (S n)).["a"∷ty_xlenbits ↦ ty.SyncVal q])
               .["an"∷ty_xlenbits ↦ ty.SyncVal q])
          ∗ Fr (S n)
          ⊢ asn.interpret (gen_cells_a cs)
              ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q]) ∗ Fr n) :
    loop_edge ls iota q Fr n.
  Proof.
    unfold loop_edge.
    apply (loop_trans ls (iota (S n)) (iota n) q kv w (Fr (S n)) (Fr n)
             Hk Hstep Hkn).
    apply (loop_frame_std ls (iota (S n)) (iota n) q (Fr (S n)) (Fr n)
             Hqan Hb).
    rewrite Hea. rewrite Hean.
    exact (loop_extra_step ws fs cs (iota (S n)) (iota n) q (Fr (S n)) (Fr n)
             Hw Hf Hc).
  Qed.

  (* ---- THE WHOLE LOOP, FROM ITS OBLIGATIONS ------------------------------

     The analogue of `cfg_instrs_endToEnd`: everything generic about a counted
     loop is discharged here, and what a caller passes is a fixed list of
     example-specific arguments.  Assembling a loop used to mean writing out
     `loop_step`, `loop_exit` and `loop_counted` -- three lemmas whose
     statements are mostly re-spelled valuations -- for every example.

     The arguments group as:
       placement  Hq/Hok/HokF/Hwf -- where the segment sits in the program;
       the VCs    Hvb/Hvf         -- `solve_seg` on body and final;
       the base   Hpl/Hpa         -- eq_refl whenever iotaf maps "q" to a literal;
       the count  HP0/HPm         -- the trip predicate survives decrement;
       THE TWO    Hlatch/Hedge    -- the latch (guard + exit guard, as one
                  `loop_latch_obl`, built by `loop_latch_ptr`/`_ctr`) and the
                  back edge (built by `loop_edge_std` above).  Nothing else:
                  the frame lives inside `loop_edge`;
       the cut    HOut/Hcont      -- what the loop hands the next segment.

     Both `Hlatch`'s guard half and `Hedge` take `P (S n)`, so a loop whose
     guard needs a no-wrap bound gets it from the trip predicate rather than
     from a side hypothesis. *)
  Lemma loop_all {R : LCtx} (ls : LoopSpec R)
      (post : Assertion (R ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
      (pia pbound : N) (Fr : nat -> iProp Σ) (Out Post : iProp Σ)
      (iotaf : nat -> Valuation R) (P : nat -> Prop)
      (Hq : @bv.of_N xlenbits (ls_iq ls)
            = bv.add (@bv.of_N xlenbits pia)
                (@bv.of_N xlenbits (4 * N.of_nat (ls_skip ls))))
      (Hok : seg_ok (ls_prog ls) (ls_skip ls)
               (4 * N.of_nat (ls_skip ls))%N pbound [0%N] = true)
      (HokF : seg_ok (ls_prog ls) (ls_skip ls)
                (4 * N.of_nat (ls_skip ls))%N pbound [ls_exit ls] = true)
      (Hwf : seg_wf pia pbound)
      (Hvb : ValidCFGVerifierContract (loop_body ls))
      (Hvf : ValidCFGVerifierContract (loop_final ls post))
      (Hpl : forall n, inst (T := fun Σ => Term Σ ty_xlenbits) (ls_q ls) (iotaf n)
                       = ty.SyncVal (@bv.of_N xlenbits (ls_iq ls)))
      (Hpa : forall n, inst (T := fun Σ => Term Σ ty_xlenbits) (ls_q_a ls)
                         ((iotaf n).["a"∷ty_xlenbits
                            ↦ ty.SyncVal (@bv.of_N xlenbits (ls_iq ls))])
                       = ty.SyncVal (@bv.of_N xlenbits (ls_iq ls)))
      (HP0 : P 0) (HPm : forall n, P (S n) -> P n)
      (* guard + exit guard, as the single obligation `loop_latch_obl`
         (GenSegment): both are the same branch read two ways, and the two
         builders there produce the pair from the loop's counter alone. *)
      (Hlatch : loop_latch_obl ls iotaf (@bv.of_N xlenbits (ls_iq ls)) P)
      (Hedge : forall n, P (S n) ->
             loop_edge ls iotaf (@bv.of_N xlenbits (ls_iq ls)) Fr n)
      (HOut : Fr 0 ∗ seg_exit_at (loop_final ls post) (iotaf 0)
                     (@bv.of_N xlenbits (ls_iq ls)) (ls_prog ls)
                     (@bv.of_N xlenbits pia)
                     (seg_addr (ls_iq ls) (ls_exit ls))
              -∗ Out)
      (Hcont : Out -∗ myWP2_loop Post) :
    forall n,
      loop_inv ls iotaf (@bv.of_N xlenbits (ls_iq ls)) Fr
        (Katamaran.RiscvPmp.CFGVer.VerifierRel.ptsto_instrs
           (ai_instr <$> instrs_of_list (@bv.of_N xlenbits pia) (ls_prog ls)))
        P n
      -∗ myWP2_loop Post.
  Proof.
    apply (loop_counted ls pia Fr Out Post iotaf P
             (fun n => loop_step ls pia pbound Fr iotaf P n (HPm n) Hq Hok Hwf
                         Hvb (Hpl (S n)) (Hpa (S n)) (proj1 Hlatch n)
                         (Hedge n))
             (loop_exit ls post pia pbound Fr Out iotaf P HP0 Hq HokF Hwf Hvf
                (Hpl 0) (Hpa 0) (proj2 Hlatch) HOut)
             Hcont).
  Qed.

End SegCompose.

(* Ltac defined INSIDE a Section does not survive `End`, so these live after
   it.  They need no section variable -- a tactic is syntax. *)
(* ---- THE PER-TRIP LEMMA, as two tactics ---------------------------------
   `seg_step1` leaves HPre and HPost; these discharge everything in them
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


