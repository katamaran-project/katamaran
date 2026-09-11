(******************************************************************************)
(*  GenSegment.v -- the contract generator for MID-PROGRAM SEGMENTS (cuts).   *)
(*                                                                            *)
(*  GenContract.v's `gen_contract_rel` family generates a contract for a       *)
(*  WHOLE program: entry at offset 0, exit one past the last instruction, and  *)
(*  `asn_no_post`.  A compositional proof needs something different in four    *)
(*  ways, and before this file every cut open-coded all four:                  *)
(*                                                                            *)
(*    1. Sigma has EXTRA LOGIC VARIABLES (a loop counter, data pointers), so   *)
(*       the hardwired `["p"]` context of gen_pre_rel does not fit.            *)
(*    2. Entry is at a byte offset HEAD inside the program, so the placement   *)
(*       and pc-eq terms are `p +b of_N head`, not `p`.                        *)
(*    3. Exits are EXPLICIT branch targets, not "one past the end".            *)
(*    4. There is a REAL postcondition -- the cut -- plus segment-specific     *)
(*       precondition logic (the counter, the guard, the memory window).       *)
(*                                                                            *)
(*  Measured duplication this removes (muladd family, 2026-09-09): 21 copies  *)
(*  of the register-assertion builder, 22 of its fold_right wrapper, and 31    *)
(*  byte-identical `vm_compute; solve_vc; solve_symbase_fetch` proofs.         *)
(*                                                                            *)
(*  THE ONE STRUCTURAL FIX WORTH KNOWING.  `gen_reg_asn_rel` is fixed at       *)
(*  `["p"] > "a"`, so a cut copied it -- and then copied it AGAIN for the      *)
(*  `> "an"` post-context, because an Assertion is indexed by its context and  *)
(*  does not weaken.  Two copies with identical bodies are CONVERTIBLE BUT NOT *)
(*  SYNTACTICALLY EQUAL, and iFrame matches syntactically; that is the wall    *)
(*  that produced the misleading "No applicable tactic" in both hand-written   *)
(*  loops.  `gen_regs_at` below takes the base as a TERM PARAMETER and is      *)
(*  Sigma-generic, so ONE definition serves the pre- AND the post-context:     *)
(*  same head constant, so a single `cbn [gen_reg_asn_at]` reduces both sides. *)
(*  Passing the base as a term (rather than requiring `"p" ∈ Sigma` and        *)
(*  carrying ctx.In proofs) is deliberate -- it needs no dependent plumbing    *)
(*  and the caller writes `term_var "p"`, exactly as today.                    *)
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
     RiscvPmp.CFGVer.Noninterference
     RiscvPmp.CFGVer.Tables
     RiscvPmp.CFGVer.Contracts
     RiscvPmp.CFGVer.GenContract.

From iris.proofmode Require string_ident tactics.

Import RiscvPmpProgram.

(* GenContract.v does a non-Local `Set Implicit Arguments`, which persists into
   every file that Requires it.  It is what makes `itable_faith_of_segment`'s
   pre/seg/post positional-only-and-unnameable (ZZMladTail.v records that trap)
   and it silently turned `iota` implicit on a first draft of seg_step.  Turn it
   off HERE so this file's own signatures are predictable; `Local` keeps the
   change from leaking on to consumers, and implicit-argument marks are baked in
   at definition time, so consumers see the explicit signatures regardless. *)
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
Import asn.notations.

(* ========================================================================== *)
(* 1. Sigma-GENERIC ASSERTION BUILDERS                                         *)
(* ========================================================================== *)

(* gen_reg_asn_rel, with the base as a parameter and no fixed context. *)
Definition gen_reg_asn_at {Σ : LCtx} (base : Term Σ ty_xlenbits)
    (s : reg_spec_rel) : Assertion Σ :=
  let '(r, is_pub, pv) := s in
  match pv with
  | PVExist =>
      asn.exist "v" ty_xlenbits
        (if is_pub then r ↦ᵣ term_var "v" ∗ secLeakvar "v" else r ↦ᵣ term_var "v")
  | PVConst v => r ↦ᵣ term_val ty_xlenbits v
  | PVBaseOff k =>
      r ↦ᵣ term_binop bop.bvadd base (term_val ty_xlenbits (bv.of_N k))
  end.

Definition gen_regs_at {Σ : LCtx} (base : Term Σ ty_xlenbits)
    (specs : list reg_spec_rel) : Assertion Σ :=
  List.fold_right (fun s acc => gen_reg_asn_at base s ∗ acc) ⊤ specs.

(* NO memory-block builder here, deliberately.  Writing one Sigma-generically
   needs the base term WEAKENED under the `asn.exist "mv"` binder (the fixed-
   context gen_mem_asn_rel dodges this by re-resolving `term_var "p"` inline),
   and the only weakening to hand is `subst _ sub_wk1`, which diagnostics
   record as a Theta(|Sigma|^2) cost driver and which would put a non-
   transparent wrapper around every address for iFrame to trip over.
   More to the point: NEITHER worked precedent needs it.  Segment G touches no
   memory at all, and the sliding two-cell window of muladd's br_i31_sub loop
   has addresses that are LOGIC VARIABLES, not base-plus-literal, so it states
   its cells in extra_pre.  Generalising from zero examples is how the previous
   round of this machinery went wrong; when a segment with a fixed base-
   relative memory block actually appears, add the builder then. *)

(* ========================================================================== *)
(* 2. THE SEGMENT EXIT CONDITION                                               *)
(* ========================================================================== *)

(* From ABSOLUTE byte targets, so single- and multi-exit segments are spelled
   the same way.  The hand-written segments used two different spellings for
   this -- `bv.eqb v (of_N (ia + 1128))` in most, `bv.eqb v (of_N (ia + head +
   108))` in one -- which is a latent source of exit-table mismatches. *)
Definition seg_exitCond (ia : N) (targets : list N) : bv xlenbits -> bool :=
  fun v => List.fold_right
             (fun t acc => orb (bv.eqb v (bv.of_N (ia + t)%N)) acc) false targets.

(* ========================================================================== *)
(* 2b. BOUNDS                                                                  *)
(* ========================================================================== *)

(* Every compositional lemma was threading THREE bounds by hand -- 12 + 9 + 3
   = 24 hypothesis re-declarations across ~14 lemmas:
     Hrep : bv.bin (bv.of_N ia) + 4 * |instrs| < bv.exp2 xlenbits
     Hlen : bv.unsigned (bv.of_N ia) + Z.of_N bound <= Z.of_N lenAddr
     Hmax : bv.bin (bv.of_N ia) + bound <= maxAddr
   They are NOT independent.  maxAddr = minAddr + lenAddr and minAddr = 0, so
   Hmax and Hlen are the SAME fact in N and in Z; and Hrep follows from either
   plus lenAddr_rep, as long as the segment fits inside `bound`.

   So the caller supplies ONE fact -- the natural one, on the raw ia -- and the
   three forms each lemma happens to want are projections. *)
(* The CANONICAL segment address.  Two spellings of the same thing were in use
   -- `bv.add (bv.of_N ia) (bv.of_N off)`, what `inst place iota` produces
   since a placement is `p +b of_N head`, and `bv.of_N (ia + off)`, what
   seg_exitCond compares against (30 and 24 occurrences).  Any proof meeting
   both paid a bv.of_N_add rewrite; seg_addr_add is now the ONE conversion. *)
Definition seg_addr (ia off : N) : bv xlenbits := @bv.of_N xlenbits (ia + off).

Lemma seg_addr_add (ia off : N) :
  seg_addr ia off = bv.add (@bv.of_N xlenbits ia) (@bv.of_N xlenbits off).
Proof. unfold seg_addr. now rewrite bv.of_N_add. Qed.

Definition seg_wf (ia bound : N) : Prop := (ia + bound <= lenAddr)%N.

(* ia is representable, so bv.of_N does not truncate it. *)
Lemma seg_wf_bin (ia bound : N) (H : seg_wf ia bound) :
  bv.bin (@bv.of_N xlenbits ia) = ia.
Proof. apply bv.bin_of_N_small. pose proof lenAddr_rep. unfold seg_wf in H. lia. Qed.

(* the form fetch_bound_step_Z / sep_contract_mem_read want *)
Lemma seg_wf_max (ia bound : N) (H : seg_wf ia bound) :
  (bv.bin (@bv.of_N xlenbits ia) + bound <= maxAddr)%N.
Proof.
  rewrite (seg_wf_bin ia bound H). unfold seg_wf in H.
  unfold maxAddr, minAddr. lia.
Qed.

(* the form gen_seg_contract's base-bound conjunct wants *)
Lemma seg_wf_Z (ia bound : N) (H : seg_wf ia bound) :
  (bv.unsigned (@bv.of_N xlenbits ia) + Z.of_N bound <= Z.of_N lenAddr)%Z.
Proof.
  unfold bv.unsigned. rewrite (seg_wf_bin ia bound H).
  unfold seg_wf in H. lia.
Qed.

(* the form itable_faith_at wants.  Hsz is `reflexivity`-adjacent: bound is
   chosen >= the program's byte length by construction. *)
Lemma seg_wf_rep (ia bound : N) (L : list AnnotInstr)
  (Hsz : (4 * N.of_nat (length L) <= bound)%N) (H : seg_wf ia bound) :
  (bv.bin (@bv.of_N xlenbits ia) + 4 * N.of_nat (length L) < bv.exp2 xlenbits)%N.
Proof.
  rewrite (seg_wf_bin ia bound H). pose proof lenAddr_rep.
  unfold seg_wf in H. lia.
Qed.

(* A SUB-SEGMENT of a well-formed segment is well-formed.  This is what lets a
   whole chain thread ONE `seg_wf ia bound` for the program instead of a
   separate address-space bound per segment and per cut: every segment's own
   bound, and every data block's, is a shift of the program's. *)
Lemma seg_wf_shift (ia bound h b : N)
  (Hfit : (h + b <= bound)%N) (H : seg_wf ia bound) :
  seg_wf (ia + h) b.
Proof. unfold seg_wf in *. lia. Qed.

(* ...and the tactic that uses it.  EVERY address-space bound a segment or a
   data block owes is a shift of the program's single `seg_wf`, so a whole
   chain can thread ONE well-formedness fact instead of a bound per segment and
   per cut (ZZMladTail.linkFN threads two, Hrep and Hb, and every link after it
   would thread more).

   `seg_wf_bin` is applied at bound 0 purely to get the no-truncation fact
   `bv.bin (of_N (ia+h)) = ia+h`; the real inequality is then plain lia against
   the hypothesis.  Applying `seg_wf_Z` directly does NOT work: by the time the
   goal is reduced the byte count is a Z LITERAL, and unifying `Z.of_N ?b` with
   `20` would require inverting Z.of_N. *)
Ltac seg_bound :=
  unfold bv.unsigned;
  match goal with
  | [ H : seg_wf ?i ?b |- context[bv.bin (@bv.of_N _ (?i + ?h))] ] =>
      rewrite (seg_wf_bin (i + h) 0%N (seg_wf_shift i b h 0%N ltac:(lia) H))
  | [ H : seg_wf ?i ?b |- context[bv.bin (@bv.of_N _ ?i)] ] =>
      rewrite (seg_wf_bin i b H)
  end;
  unfold seg_wf in *; lia.

(* An in-range offset does not truncate either -- this packages the
   bv.bin_of_N_small rewrites (8 occurrences) with their side condition
   already discharged. *)
Lemma seg_addr_bin (ia bound off : N)
  (Hoff : (off <= bound)%N) (H : seg_wf ia bound) :
  bv.bin (seg_addr ia off) = (ia + off)%N.
Proof.
  unfold seg_addr. apply bv.bin_of_N_small.
  pose proof lenAddr_rep. unfold seg_wf in H. lia.
Qed.

(* DISTINCT offsets give DISTINCT addresses.  This is the obligation every
   sliding-window loop body owes (two cells must not alias); the tail proved it
   inline as `bv_off_neq` with a bv.add_cancel_l/_r + bin_of_N_small + lia
   chain, once per use. *)
Lemma seg_addr_neq (ia bound o1 o2 : N)
  (H1 : (o1 <= bound)%N) (H2 : (o2 <= bound)%N) (Hne : o1 <> o2)
  (H : seg_wf ia bound) :
  seg_addr ia o1 <> seg_addr ia o2.
Proof.
  intros HH. apply (f_equal (@bv.bin xlenbits)) in HH.
  rewrite (seg_addr_bin ia bound o1 H1 H) in HH.
  rewrite (seg_addr_bin ia bound o2 H2 H) in HH.
  unfold seg_wf in H. lia.
Qed.

(* Advancing a window by d.  The tail proved this inline as `bv_shift4`,
   hardcoded at d = 4; every sliding loop needs it. *)
Lemma seg_addr_step (ia off d : N) :
  bv.add (seg_addr ia off) (@bv.of_N xlenbits d) = seg_addr ia (off + d).
Proof. unfold seg_addr. rewrite bv.of_N_add. f_equal. lia. Qed.

(* `lia` chokes on 2^32 while bv.exp2 xlenbits is folded (bv-pitfalls); this is
   the incantation, 5 copies of which were inline.

   It supplies the value as a HYPOTHESIS rather than rewriting the goal.  The
   `change (bv.exp2 xlenbits) with 4294967296%N; lia` form this replaces is a
   trap: it unfolds only the goal, so a bound that arrives as a hypothesis
   (`Hm : (m + 2 < bv.exp2 xlenbits)%N`) stays a DIFFERENT atom from the
   goal's literal and lia reports "Cannot find witness" on something it could
   have closed by treating both as the same opaque atom.  Handing lia the
   equation instead works in BOTH directions.

   Do NOT "improve" this to `rewrite ?exp2_xlenbits in *; lia`: `in *` fails
   here with the (very unhelpful) "assumptions should be named explicitly",
   measured 2026-09-10. *)
Lemma exp2_xlenbits : bv.exp2 xlenbits = 4294967296%N.
Proof. vm_compute; reflexivity. Qed.

Ltac bv_bound := pose proof exp2_xlenbits; lia.

(* ---- pc ALGEBRA -----------------------------------------------------------
   Segment addresses are written TWO ways across the hand-written proofs:
   `bv.add (bv.of_N ia) (bv.of_N off)` (what `inst place iota` produces, since
   a placement term is `p +b of_N head`) and `bv.of_N (ia + off)` (what
   seg_exitCond compares against).  30 and 24 occurrences respectively, and
   every proof that meets both pays a bv.of_N_add rewrite to reconcile them.
   `seg_addr` is the canonical form; `seg_addr_add` is the one conversion, so a
   call site never has to think about which spelling it is holding. *)

(* A declared target IS hit.  (Used by GenCompose.seg_exits_faith.) *)
Lemma seg_exitCond_hit (ia : N) (targets : list N) (t : N) :
  List.In t targets -> seg_exitCond ia targets (seg_addr ia t) = true.
Proof.
  unfold seg_addr.
  induction targets as [|t0 ts IH]; [contradiction|].
  intros [Heq | Hin]; cbn [seg_exitCond List.fold_right].
  - subst t0.
    destruct (bv.eqb_spec (@bv.of_N xlenbits (ia + t)%N)
                          (@bv.of_N xlenbits (ia + t)%N)); [reflexivity | congruence].
  - (* the cbn has already unfolded seg_exitCond into its foldr, so
       `rewrite (IH Hin)` finds no subterm; `exact` unifies up to conversion
       where `rewrite` matches syntactically. *)
    apply Bool.orb_true_iff. right. exact (IH Hin).
Qed.

(* ...and the CONVERSE, which is what every call site was open-coding as
   `destruct an as [av|..]; [|contradiction]` + `unfold <seg>_exitCond` +
   `assert (Hav : av = ...) by (destruct (bv.eqb_spec ...); congruence)`.
   Only a declared target can be reached, so knowing the exit condition holds
   PINS the pc. *)
Lemma seg_exitCond_inv (ia : N) (targets : list N) (v : bv xlenbits) :
  seg_exitCond ia targets v = true ->
  exists t, List.In t targets /\ v = seg_addr ia t.
Proof.
  unfold seg_addr.
  induction targets as [|t0 ts IH]; cbn [seg_exitCond List.fold_right].
  - discriminate.
  - intros Hor. apply Bool.orb_true_iff in Hor as [Heq | Hrest].
    + exists t0. split; [now left |].
      destruct (bv.eqb_spec v (@bv.of_N xlenbits (ia + t0)%N));
        [assumption | discriminate].
    + destruct (IH Hrest) as [t [Hin Hv]]. exists t. split; [now right | exact Hv].
Qed.

(* The overwhelmingly common case: ONE declared exit, so the pc is determined
   outright and no case analysis survives at all. *)
Lemma seg_exitCond_inv1 (ia t : N) (v : bv xlenbits) :
  seg_exitCond ia [t] v = true -> v = seg_addr ia t.
Proof.
  intros H. apply seg_exitCond_inv in H as [t' [Hin Hv]].
  destruct Hin as [-> | []]. exact Hv.
Qed.

(* ========================================================================== *)
(* 2b. THE SEGMENT'S DECIDABLE SIDE CONDITIONS, AS ONE BOOLEAN                 *)
(* ========================================================================== *)

(* Every compositional call site owes three facts about the SLICING, and all
   three are closed and decidable -- they mention only the numbers the caller
   already handed to gen_seg_contract, never the base address or the
   valuation.  Bundling them into one boolean is what lets the two
   faithfulness obligations be discharged by `eq_refl` INSIDE a seg_step1
   application, instead of by four named lemmas per segment (measured on
   segment G: 45 lines of near-byte-identical ritual for two contracts).

   `Hoff` is the head = 4 * skip invariant gen_seg_contract documents but
   cannot enforce in its type; `Hskip`/`Hsz` are the sub-table's fit. *)
Definition seg_ok (prog : list AnnotInstr) (skip : nat)
    (head bound : N) (targets : list N) : bool :=
  andb (andb (N.eqb (N.mul 4 (N.of_nat skip)) head)
             (Nat.leb skip (length prog)))
       (andb (N.leb (N.mul 4 (N.of_nat (length prog))) bound)
             (List.forallb (fun t => N.leb head t) targets)).

Lemma seg_ok_off (prog : list AnnotInstr) (skip : nat) (head bound : N)
  (targets : list N) (H : seg_ok prog skip head bound targets = true) :
  @eq N (N.mul 4 (N.of_nat skip)) head.
Proof.
  unfold seg_ok in H.
  apply Bool.andb_true_iff in H as [H _]. apply Bool.andb_true_iff in H as [H _].
  now apply N.eqb_eq.
Qed.

Lemma seg_ok_skip (prog : list AnnotInstr) (skip : nat) (head bound : N)
  (targets : list N) (H : seg_ok prog skip head bound targets = true) :
  Nat.le skip (length prog).
Proof.
  unfold seg_ok in H.
  apply Bool.andb_true_iff in H as [H _]. apply Bool.andb_true_iff in H as [_ H].
  now apply Nat.leb_le.
Qed.

Lemma seg_ok_sz (prog : list AnnotInstr) (skip : nat) (head bound : N)
  (targets : list N) (H : seg_ok prog skip head bound targets = true) :
  (N.mul 4 (N.of_nat (length prog)) <= bound)%N.
Proof.
  unfold seg_ok in H.
  apply Bool.andb_true_iff in H as [_ H]. apply Bool.andb_true_iff in H as [H _].
  now apply N.leb_le.
Qed.

Lemma seg_ok_tgts (prog : list AnnotInstr) (skip : nat) (head bound : N)
  (targets : list N) (H : seg_ok prog skip head bound targets = true) :
  List.Forall (fun t => N.le head t) targets.
Proof.
  unfold seg_ok in H.
  apply Bool.andb_true_iff in H as [_ H]. apply Bool.andb_true_iff in H as [_ H].
  apply List.Forall_forall. intros t Hin.
  rewrite List.forallb_forall in H. apply N.leb_le. now apply H.
Qed.

(* ========================================================================== *)
(* 3. THE SEGMENT CONTRACT GENERATOR                                           *)
(* ========================================================================== *)

(* `base` and `base_a` are THE SAME TERM at two contexts (`term_var "p"` in
   both).  Two arguments rather than one, because an Assertion's context is an
   index: cfg_placement lives at Sigma while the precondition lives at
   Sigma > "a", and a `Term Sigma` does not weaken into `Term (Sigma > "a")`.
   The hand-written segments already paid this cost by writing the pc-eq term
   inline; passing it twice is no worse and keeps every term syntactically
   transparent (no `subst _ sub_wk1` wrappers for iFrame to trip over).

   INVARIANT THE CALLER MUST RESPECT: `head = 4 * skip`.  It is not enforced in
   the type -- head is a byte offset and skip an instruction index -- and
   getting it wrong yields a segment placed at an address whose instructions
   are not the ones in its sub-table.  GenCompose.itable_faith_at makes the
   mismatch a PROOF OBLIGATION (`4 * skip = head`), so it cannot pass silently
   once the segment is composed. *)
Definition gen_seg_contract {Σ : LCtx}
    (base   : Term Σ ty_xlenbits)
    (base_a : Term (Σ ▻ "a"∷ty_xlenbits) ty_xlenbits)
    (ia head : N)
    (* `list AnnotInstr`, NOT `list AST`: cfg_instrs is an AnnotInstr list, so
       with `list AST` here the coercion lands OUTSIDE the slicing
       (`list_AST_AnnotInstr (firstn take (skipn skip prog))`) and can never
       unify with GenCompose.itable_faith_at's `firstn take (skipn skip L)`
       for `L : list AnnotInstr`.  Taking the AnnotInstr list makes the two
       syntactically identical; a caller with a `list AST` program still just
       writes it and lets the coercion fire at the argument. *)
    (prog : list AnnotInstr) (skip take : nat)
    (targets : list N)
    (bound : N)
    (fl : nat)
    (regs : list reg_spec_rel)
    (extra_pre : Assertion (Σ ▻ "a"∷ty_xlenbits))
    (post : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
    : @CFGVerifierContract Σ :=
  let place := term_binop bop.bvadd base (term_val ty_xlenbits (bv.of_N head)) in
  @MkCFGVerifierContract Σ (ia + head)%N
    place
    (exits_of_offs place (List.map (fun t => (t - head)%N) targets))
    ( asn_pc_eq (term_binop bop.bvadd base_a
                   (term_val ty_xlenbits (bv.of_N head)))
      ∗ asn.formula (formula_relop bop.le
           (term_binop bop.plus (term_unop uop.unsigned base_a)
              (term_val ty.int (Z.of_N bound)))
           (term_val ty.int (Z.of_N lenAddr)))
      ∗ extra_pre
      ∗ gen_regs_at base_a regs )
    (List.firstn take (List.skipn skip prog))
    (seg_exitCond ia targets)
    fl
    (* minimal_pre is appended HERE rather than left to the caller, so the
       post MIRRORS the pre: CFG_VC_triple already wraps the precondition in
       extend_to_minimal_pre, and the asymmetry was a real bug source.  A post
       that forgets to hand cur_privilege / inv_leakage back consumes them on
       every trip, so the loop body can only ever run ONCE -- which is exactly
       what happened to amBody_post, and it fails late and confusingly. *)
    (post ∗ minimal_pre)%asn.

(* The 31 byte-identical segment VC proofs, once. *)
Ltac solve_seg := intros; vm_compute; solve_vc; solve_symbase_fetch.

(* ========================================================================== *)
(* 4. THE reg_convert TABLE                                                    *)
(* ========================================================================== *)

(* `asn_regidx_pts` dispatches through `reg_convert`, which matches on
   `bv.to_bitstring`: cbn will NOT reduce it at ANY delta setting -- only
   vm_compute does.  So every Iris-side segment proof needs these equations to
   get from `T4 ↦ᵣ _` to `x29 ↦ᵣ _`, and they were being re-proved per file
   (with rc_T1 defined twice over).  Note X0 is None: x0 is hardwired zero and
   has no ghost cell, so `asn_regidx_pts X0 v` is Top. *)
Lemma rc_X0 : reg_convert X0 = None.     Proof. vm_compute; reflexivity. Qed.
Lemma rc_X1 : reg_convert X1 = Some x1.  Proof. vm_compute; reflexivity. Qed.
Lemma rc_X2 : reg_convert X2 = Some x2.  Proof. vm_compute; reflexivity. Qed.
Lemma rc_X3 : reg_convert X3 = Some x3.  Proof. vm_compute; reflexivity. Qed.
Lemma rc_X4 : reg_convert X4 = Some x4.  Proof. vm_compute; reflexivity. Qed.
Lemma rc_T0 : reg_convert T0 = Some x5.  Proof. vm_compute; reflexivity. Qed.
Lemma rc_T1 : reg_convert T1 = Some x6.  Proof. vm_compute; reflexivity. Qed.
Lemma rc_T2 : reg_convert T2 = Some x7.  Proof. vm_compute; reflexivity. Qed.
Lemma rc_A0 : reg_convert A0 = Some x10. Proof. vm_compute; reflexivity. Qed.
Lemma rc_A1 : reg_convert A1 = Some x11. Proof. vm_compute; reflexivity. Qed.
Lemma rc_A2 : reg_convert A2 = Some x12. Proof. vm_compute; reflexivity. Qed.
Lemma rc_A3 : reg_convert A3 = Some x13. Proof. vm_compute; reflexivity. Qed.
Lemma rc_A4 : reg_convert A4 = Some x14. Proof. vm_compute; reflexivity. Qed.
Lemma rc_A5 : reg_convert A5 = Some x15. Proof. vm_compute; reflexivity. Qed.
Lemma rc_A6 : reg_convert A6 = Some x16. Proof. vm_compute; reflexivity. Qed.
Lemma rc_A7 : reg_convert A7 = Some x17. Proof. vm_compute; reflexivity. Qed.
Lemma rc_T3 : reg_convert T3 = Some x28. Proof. vm_compute; reflexivity. Qed.
Lemma rc_T4 : reg_convert T4 = Some x29. Proof. vm_compute; reflexivity. Qed.
Lemma rc_T5 : reg_convert T5 = Some x30. Proof. vm_compute; reflexivity. Qed.
Lemma rc_T6 : reg_convert T6 = Some x31. Proof. vm_compute; reflexivity. Qed.
Lemma rc_S0 : reg_convert S0 = Some x8.  Proof. vm_compute; reflexivity. Qed.
Lemma rc_S1 : reg_convert S1 = Some x9.  Proof. vm_compute; reflexivity. Qed.
Lemma rc_S2 : reg_convert S2 = Some x18. Proof. vm_compute; reflexivity. Qed.
Lemma rc_S3 : reg_convert S3 = Some x19. Proof. vm_compute; reflexivity. Qed.

Ltac reg_reduce :=
  unfold asn_regidx_pts;
  rewrite ?rc_X0; rewrite ?rc_X1; rewrite ?rc_X2; rewrite ?rc_X3;
  rewrite ?rc_X4; rewrite ?rc_T0; rewrite ?rc_T1; rewrite ?rc_T2;
  rewrite ?rc_A0; rewrite ?rc_A1; rewrite ?rc_A2; rewrite ?rc_A3;
  rewrite ?rc_A4; rewrite ?rc_A5; rewrite ?rc_A6; rewrite ?rc_A7;
  rewrite ?rc_T3; rewrite ?rc_T4; rewrite ?rc_T5; rewrite ?rc_T6;
  rewrite ?rc_S0; rewrite ?rc_S1; rewrite ?rc_S2; rewrite ?rc_S3.

(* ========================================================================== *)
(* 4. COUNTED LOOPS                                                            *)
(* ========================================================================== *)

(* A loop is stated ONCE, as data, and BOTH its segment contracts plus its
   invariant are generated from that.

   THE CONTEXT IS A PARAMETER.  An earlier version fixed it at ["q";"d";"k"],
   which bought a large simplification -- `term_var "d"` resolves at whatever
   context it is written in, so no term has to be passed twice and nothing
   needs weakening under `asn.exist`.  It also made the framework fit exactly
   ONE of muladd's seven loops: six of them compare the counter against a
   REGISTER (needing a limit variable) and every one walks a POINTER (needing
   a pointer variable), and a fixed context has no room for either.  So Sigma
   is a parameter and the counter and the bases are explicit terms.

   THE PRICE is that a term must be supplied once per context it appears in --
   `gen_seg_contract` already pays this with base/base_a, and here the counter
   needs FOUR copies because the post binds a fresh variable and a
   `Term (Σ ▻ "a" ▻ "an")` does not weaken under `asn.exist "c"`.  Writing
   `term_var "k"` four times is tedious but it is resolution, not proof.

   THE CODE BASE CARRIES NO OFFSET: cfg_placement is `ls_q`, so the contract
   never mentions where the loop sits in the program.  Composition supplies
   q = programBase + head. *)

(* The counter's update, as the machine does it: RISC-V sign-extends the
   12-bit immediate and ADDS, so a decrement by one is `+ 0xFFFFFFFF`.  Do not
   "simplify" this to a bvsub -- the contract must match the term the executor
   produces or the VC will not discharge (measured 2026-09-11). *)
Definition ls_step {Σ} (imm : Val ty_xlenbits) (t : Term Σ ty_xlenbits)
    : Term Σ ty_xlenbits :=
  term_binop bop.bvadd t (term_val ty_xlenbits imm).

(* Address-space bounds, one per base the loop uses.  Generated rather than
   written, because forgetting one fails late and confusingly. *)
Definition gen_loop_bounds {Σ : LCtx}
    (bs : list (Term Σ ty_xlenbits * N)) : Assertion Σ :=
  List.fold_right
    (fun (b : Term Σ ty_xlenbits * N) (acc : Assertion Σ) =>
       (asn.formula (formula_relop bop.le
          (term_binop bop.plus (term_unop uop.unsigned (fst b))
             (term_val ty.int (Z.of_N (snd b))))
          (term_val ty.int (Z.of_N lenAddr))) ∗ acc)%asn)
    ⊤%asn bs.

Record LoopSpec {Σ : LCtx} : Type := MkLoopSpec
  { ls_iq     : N            (* ABSOLUTE address of the loop head              *)
  ; ls_prog   : list AnnotInstr
  ; ls_skip   : nat          (* first instruction of the body, as a list index *)
  ; ls_take   : nat          (* how many instructions the body is              *)
  ; ls_exit   : N            (* fall-through target, RELATIVE to the head      *)
  ; ls_fuel   : nat

    (* the loop's own CODE base, at the three contexts it appears in *)
  ; ls_q      : Term Σ ty_xlenbits
  ; ls_q_a    : Term (Σ ▻ "a"∷ty_xlenbits) ty_xlenbits
  ; ls_q_an   : Term (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) ty_xlenbits

    (* THE COUNTER: its register, its value as a term, and its per-trip
       update.  ls_at is the bridge from trips-remaining to counter value. *)
  ; ls_ctr    : RegIdx
  ; ls_k_a    : Term (Σ ▻ "a"∷ty_xlenbits) ty_xlenbits
  ; ls_k_an   : Term (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) ty_xlenbits
  ; ls_k_anc  : Term (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits ▻ "c"∷ty_xlenbits)
                     ty_xlenbits                  (* under the post's binder *)
  ; ls_imm    : Val ty_xlenbits
  ; ls_at     : nat -> N

    (* the classification: registers by spec list, every base with its bound,
       and an escape hatch for what a spec list cannot say -- a walking
       pointer's value, memory cells, anything loop-specific. *)
  ; ls_regs     : list reg_spec_rel
  ; ls_bases_a  : list (Term (Σ ▻ "a"∷ty_xlenbits) ty_xlenbits * N)
  ; ls_bases_an : list (Term (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) ty_xlenbits * N)
  ; ls_extra_a  : Assertion (Σ ▻ "a"∷ty_xlenbits)
  ; ls_extra_an : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)

    (* the branch, as a predicate on the counter's POST-decrement value.  Two
       fields rather than one plus a negation: Formula is not usefully closed
       under negation, and flipping a relop mechanically would be wrong for
       some comparison. *)
  ; ls_guard  : Term (Σ ▻ "a"∷ty_xlenbits) ty_xlenbits
                -> Formula (Σ ▻ "a"∷ty_xlenbits)
  ; ls_exitg  : Term (Σ ▻ "a"∷ty_xlenbits) ty_xlenbits
                -> Formula (Σ ▻ "a"∷ty_xlenbits)
  }.
Arguments LoopSpec : clear implicits.
Arguments MkLoopSpec {Σ}.

(* What is the same at entry and exit.  Written once per context because a
   Term does not weaken; the two must agree, and that is a real proof
   obligation at composition, not a convention. *)
Definition gen_loop_frame_a {Σ : LCtx} (ls : LoopSpec Σ)
    : Assertion (Σ ▻ "a"∷ty_xlenbits) :=
  ( gen_loop_bounds (ls_bases_a ls)
    ∗ gen_regs_at (ls_q_a ls) (ls_regs ls)
    ∗ ls_extra_a ls )%asn.

Definition gen_loop_frame_an {Σ : LCtx} (ls : LoopSpec Σ)
    : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( gen_loop_bounds (ls_bases_an ls)
    ∗ gen_regs_at (ls_q_an ls) (ls_regs ls)
    ∗ ls_extra_an ls )%asn.

(* The counter and the frame.  SHARED by the contracts' preconditions and the
   invariant, which differ only in what each adds.

   MIND THE minimal_pre.  CFG_VC_triple already wraps a precondition in
   extend_to_minimal_pre, so gen_loop_pre must NOT carry it -- a second copy
   makes the pre demand two and the post return one, i.e. the body consumes
   cur_privilege / inv_leakage every trip and can only run ONCE.  That still
   VERIFIES, so it fails late and only at composition; it is the amBody_post
   bug, and it bit this file too.  The INVARIANT does carry minimal_pre,
   because it describes the whole state at the loop head. *)
Definition gen_loop_core {Σ : LCtx} (ls : LoopSpec Σ)
    : Assertion (Σ ▻ "a"∷ty_xlenbits) :=
  ( ls_ctr ls ↦ᵣ ls_k_a ls
    ∗ asn.formula (formula_secLeak (ls_k_a ls))
    ∗ gen_loop_frame_a ls )%asn.

Definition gen_loop_win {Σ : LCtx} (ls : LoopSpec Σ)
    : Assertion (Σ ▻ "a"∷ty_xlenbits) :=
  ( gen_loop_core ls ∗ minimal_pre )%asn.

(* ...and the branch decision is the ONLY thing a contract adds.  Note it is
   applied to ls_step, never to the raw counter: the head decrements, THEN the
   branch tests, and that off-by-one is now unstateable. *)
Definition gen_loop_pre {Σ : LCtx} (ls : LoopSpec Σ)
    (g : Term (Σ ▻ "a"∷ty_xlenbits) ty_xlenbits -> Formula (Σ ▻ "a"∷ty_xlenbits))
    : Assertion (Σ ▻ "a"∷ty_xlenbits) :=
  ( gen_loop_core ls
    ∗ asn.formula (g (ls_step (ls_imm ls) (ls_k_a ls))) )%asn.

(* The body's post binds a FRESH variable and states the decrement as a PURE
   equation, rather than putting the computed term in the spatial part.  That
   is what lets the back edge frame like any other cut (measured: it removes
   the valuation-crossing rewrite entirely). *)
Definition gen_loop_post {Σ : LCtx} (ls : LoopSpec Σ)
    : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( asn.exist "c" ty_xlenbits
      ( ls_ctr ls ↦ᵣ term_var "c"
        ∗ asn.formula (formula_relop bop.eq (term_var "c")
                         (ls_step (ls_imm ls) (ls_k_anc ls)))
        ∗ asn.formula (formula_secLeak (term_var "c")) )
    ∗ gen_loop_frame_an ls )%asn.

Definition gen_loop_contract {Σ : LCtx} (ls : LoopSpec Σ)
    (g : Term (Σ ▻ "a"∷ty_xlenbits) ty_xlenbits -> Formula (Σ ▻ "a"∷ty_xlenbits))
    (target : N)
    (post : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
    : @CFGVerifierContract Σ :=
  @MkCFGVerifierContract Σ (ls_iq ls)
    (ls_q ls)
    (exits_of_offs (ls_q ls) [target])
    (asn_pc_eq (ls_q_a ls) ∗ gen_loop_pre ls g)
    (List.firstn (ls_take ls) (List.skipn (ls_skip ls) (ls_prog ls)))
    (seg_exitCond (ls_iq ls) [target])
    (ls_fuel ls)
    (post ∗ minimal_pre)%asn.

(* BODY: guard holds, back edge to the head (offset 0 -- the loop is stated
   against its own entry address). *)
Definition loop_body {Σ : LCtx} (ls : LoopSpec Σ) : @CFGVerifierContract Σ :=
  gen_loop_contract ls (ls_guard ls) 0%N (gen_loop_post ls).

(* FINAL: the guard fails, fall out to ls_exit.  Its postcondition is the
   caller's -- that is the cut into whatever follows the loop, and it is
   genuine specification. *)
Definition loop_final {Σ : LCtx} (ls : LoopSpec Σ)
    (post : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
    : @CFGVerifierContract Σ :=
  gen_loop_contract ls (ls_exitg ls) (ls_exit ls) post.


(* head 0 is not definitionally `+ 0`, so the two shapes the composition needs
   get their own one-liners. *)
Lemma seg_addr_0 (ia : N) : seg_addr ia 0 = @bv.of_N xlenbits ia.
Proof. unfold seg_addr. f_equal. lia. Qed.

Lemma seg_exitCond_hit0 (iq : N) (targets : list N) (t : N)
  (Hin : List.In t targets) :
  seg_exitCond iq targets (bv.add (@bv.of_N xlenbits iq) (@bv.of_N xlenbits t))
  = true.
Proof. rewrite <- seg_addr_add. now apply seg_exitCond_hit. Qed.
