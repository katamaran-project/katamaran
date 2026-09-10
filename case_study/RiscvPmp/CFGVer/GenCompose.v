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
     exactly the arithmetic the segment did. *)
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

End SegCompose.
