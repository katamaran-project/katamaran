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
   and it silently turned `iota` implicit on a first draft of seg_run.  Turn it
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

Definition seg_fits_memory (ia bound : N) : Prop := (ia + bound <= lenAddr)%N.

(* ia is representable, so bv.of_N does not truncate it. *)
Lemma seg_fits_bin (ia bound : N) (H : seg_fits_memory ia bound) :
  bv.bin (@bv.of_N xlenbits ia) = ia.
Proof. apply bv.bin_of_N_small. pose proof lenAddr_rep. unfold seg_fits_memory in H. lia. Qed.

(* the form fetch_bound_step_Z / sep_contract_mem_read want *)
Lemma seg_fits_max (ia bound : N) (H : seg_fits_memory ia bound) :
  (bv.bin (@bv.of_N xlenbits ia) + bound <= maxAddr)%N.
Proof.
  rewrite (seg_fits_bin ia bound H). unfold seg_fits_memory in H.
  unfold maxAddr, minAddr. lia.
Qed.

(* the form gen_seg_contract's base-bound conjunct wants *)
Lemma seg_fits_Z (ia bound : N) (H : seg_fits_memory ia bound) :
  (bv.unsigned (@bv.of_N xlenbits ia) + Z.of_N bound <= Z.of_N lenAddr)%Z.
Proof.
  unfold bv.unsigned. rewrite (seg_fits_bin ia bound H).
  unfold seg_fits_memory in H. lia.
Qed.

(* the form instr_table_ok_at wants.  Hsz is `reflexivity`-adjacent: bound is
   chosen >= the program's byte length by construction. *)
Lemma seg_fits_rep (ia bound : N) (L : list AnnotInstr)
  (Hsz : (4 * N.of_nat (length L) <= bound)%N) (H : seg_fits_memory ia bound) :
  (bv.bin (@bv.of_N xlenbits ia) + 4 * N.of_nat (length L) < bv.exp2 xlenbits)%N.
Proof.
  rewrite (seg_fits_bin ia bound H). pose proof lenAddr_rep.
  unfold seg_fits_memory in H. lia.
Qed.

(* A SUB-SEGMENT of a well-formed segment is well-formed.  This is what lets a
   whole chain thread ONE `seg_fits_memory ia bound` for the program instead of a
   separate address-space bound per segment and per cut: every segment's own
   bound, and every data block's, is a shift of the program's. *)
Lemma seg_fits_shift (ia bound h b : N)
  (Hfit : (h + b <= bound)%N) (H : seg_fits_memory ia bound) :
  seg_fits_memory (ia + h) b.
Proof. unfold seg_fits_memory in *. lia. Qed.

(* ...and the tactic that uses it.  EVERY address-space bound a segment or a
   data block owes is a shift of the program's single `seg_fits_memory`, so a whole
   chain can thread ONE well-formedness fact instead of a bound per segment and
   per cut (ZZMladTail.linkFN threads two, Hrep and Hb, and every link after it
   would thread more).

   `seg_fits_bin` is applied at bound 0 purely to get the no-truncation fact
   `bv.bin (of_N (ia+h)) = ia+h`; the real inequality is then plain lia against
   the hypothesis.  Applying `seg_fits_Z` directly does NOT work: by the time the
   goal is reduced the byte count is a Z LITERAL, and unifying `Z.of_N ?b` with
   `20` would require inverting Z.of_N. *)
Ltac seg_bound :=
  unfold bv.unsigned;
  match goal with
  | [ H : seg_fits_memory ?i ?b |- context[bv.bin (@bv.of_N _ (?i + ?h))] ] =>
      rewrite (seg_fits_bin (i + h) 0%N (seg_fits_shift i b h 0%N ltac:(lia) H))
  | [ H : seg_fits_memory ?i ?b |- context[bv.bin (@bv.of_N _ ?i)] ] =>
      rewrite (seg_fits_bin i b H)
  end;
  unfold seg_fits_memory in *; lia.

(* An in-range offset does not truncate either -- this packages the
   bv.bin_of_N_small rewrites (8 occurrences) with their side condition
   already discharged. *)
Lemma seg_addr_bin (ia bound off : N)
  (Hoff : (off <= bound)%N) (H : seg_fits_memory ia bound) :
  bv.bin (seg_addr ia off) = (ia + off)%N.
Proof.
  unfold seg_addr. apply bv.bin_of_N_small.
  pose proof lenAddr_rep. unfold seg_fits_memory in H. lia.
Qed.

(* DISTINCT offsets give DISTINCT addresses.  This is the obligation every
   sliding-window loop body owes (two cells must not alias); the tail proved it
   inline as `bv_off_neq` with a bv.add_cancel_l/_r + bin_of_N_small + lia
   chain, once per use. *)
Lemma seg_addr_neq (ia bound o1 o2 : N)
  (H1 : (o1 <= bound)%N) (H2 : (o2 <= bound)%N) (Hne : o1 <> o2)
  (H : seg_fits_memory ia bound) :
  seg_addr ia o1 <> seg_addr ia o2.
Proof.
  intros HH. apply (f_equal (@bv.bin xlenbits)) in HH.
  rewrite (seg_addr_bin ia bound o1 H1 H) in HH.
  rewrite (seg_addr_bin ia bound o2 H2 H) in HH.
  unfold seg_fits_memory in H. lia.
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

(* A declared target IS hit.  (Used by GenCompose.seg_exit_table_ok.) *)
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
   faithfulness obligations be discharged by `eq_refl` INSIDE a seg_run_single_exit
   application, instead of by four named lemmas per segment (measured on
   segment G: 45 lines of near-byte-identical ritual for two contracts).

   `Hoff` is the head = 4 * skip invariant gen_seg_contract documents but
   cannot enforce in its type; `Hskip`/`Hsz` are the sub-table's fit. *)
Definition seg_placement_ok (prog : list AnnotInstr) (skip : nat)
    (head bound : N) (targets : list N) : bool :=
  andb (andb (N.eqb (N.mul 4 (N.of_nat skip)) head)
             (Nat.leb skip (length prog)))
       (andb (N.leb (N.mul 4 (N.of_nat (length prog))) bound)
             (List.forallb (fun t => N.leb head t) targets)).

Lemma seg_placement_off (prog : list AnnotInstr) (skip : nat) (head bound : N)
  (targets : list N) (H : seg_placement_ok prog skip head bound targets = true) :
  @eq N (N.mul 4 (N.of_nat skip)) head.
Proof.
  unfold seg_placement_ok in H.
  apply Bool.andb_true_iff in H as [H _]. apply Bool.andb_true_iff in H as [H _].
  now apply N.eqb_eq.
Qed.

Lemma seg_placement_skip (prog : list AnnotInstr) (skip : nat) (head bound : N)
  (targets : list N) (H : seg_placement_ok prog skip head bound targets = true) :
  Nat.le skip (length prog).
Proof.
  unfold seg_placement_ok in H.
  apply Bool.andb_true_iff in H as [H _]. apply Bool.andb_true_iff in H as [_ H].
  now apply Nat.leb_le.
Qed.

Lemma seg_placement_size (prog : list AnnotInstr) (skip : nat) (head bound : N)
  (targets : list N) (H : seg_placement_ok prog skip head bound targets = true) :
  (N.mul 4 (N.of_nat (length prog)) <= bound)%N.
Proof.
  unfold seg_placement_ok in H.
  apply Bool.andb_true_iff in H as [_ H]. apply Bool.andb_true_iff in H as [H _].
  now apply N.leb_le.
Qed.

Lemma seg_placement_targets (prog : list AnnotInstr) (skip : nat) (head bound : N)
  (targets : list N) (H : seg_placement_ok prog skip head bound targets = true) :
  List.Forall (fun t => N.le head t) targets.
Proof.
  unfold seg_placement_ok in H.
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
   are not the ones in its sub-table.  GenCompose.instr_table_ok_at makes the
   mismatch a PROOF OBLIGATION (`4 * skip = head`), so it cannot pass silently
   once the segment is composed. *)
(* The address-space bound on ONE base, as a precondition conjunct.  Factored
   out because gen_seg_contract emits it for the code base while the loop
   invariant has to RE-establish exactly the same conjunct at the back edge:
   two spellings of one formula is how they drift. *)
Definition gen_base_bound {Σ : LCtx} (base : Term Σ ty_xlenbits) (bound : N)
    : Assertion Σ :=
  asn.formula (formula_relop bop.le
     (term_binop bop.plus (term_unop uop.unsigned base)
        (term_val ty.int (Z.of_N bound)))
     (term_val ty.int (Z.of_N lenAddr))).

Definition gen_seg_contract {Σ : LCtx}
    (base   : Term Σ ty_xlenbits)
    (base_a : Term (Σ ▻ "a"∷ty_xlenbits) ty_xlenbits)
    (ia head : N)
    (* `list AnnotInstr`, NOT `list AST`: cfg_instrs is an AnnotInstr list, so
       with `list AST` here the coercion lands OUTSIDE the slicing
       (`list_AST_AnnotInstr (firstn take (skipn skip prog))`) and can never
       unify with GenCompose.instr_table_ok_at's `firstn take (skipn skip L)`
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
      ∗ gen_base_bound base_a bound
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

(* `solve_param_vc` lived here and is GONE: it was character-for-character the
   standard parametric-base discharge, which ~150 other sites wrote out.  One
   spelling now, `solve_param_vc`, defined in Contracts.v beside the tactics
   it calls -- a segment needs nothing a parametric-base contract does not. *)

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

   THE CODE BASE CARRIES NO OFFSET: cfg_placement is `loop_base`, so the contract
   never mentions where the loop sits in the program.  Composition supplies
   q = programBase + head. *)

(* The counter's update, as the machine does it: RISC-V sign-extends the
   12-bit immediate and ADDS, so a decrement by one is `+ 0xFFFFFFFF`.  Do not
   "simplify" this to a bvsub -- the contract must match the term the executor
   produces or the VC will not discharge (measured 2026-09-11). *)
Definition counter_after_step {Σ} (imm : Val ty_xlenbits) (t : Term Σ ty_xlenbits)
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

(* ========================================================================= *)
(*  C1 (PLAN-loop-automation.md) -- THE MECHANICAL LoopSpec FIELDS, DERIVED.  *)
(*                                                                           *)
(*  Six of a LoopSpec's fields state nothing a reader could not read off the  *)
(*  instruction list: where the body starts, how long it is, where the        *)
(*  fall-through goes, how much fuel it needs, and which way the branch       *)
(*  tests.  Written by hand they are that many separate opportunities to be   *)
(*  off by one -- and the part that actually bites is that a wrong one does   *)
(*  NOT fail where it was written.  It surfaces as a bare `False` deep in a   *)
(*  VC (cfgver-solve-vc's third entry is exactly this: a hand-authored        *)
(*  backward branch offset), or, worse, verifies a real loop that is not the  *)
(*  one in the program.                                                       *)
(*                                                                           *)
(*  NARROW form: the BACK EDGE's list index is an INPUT.  The wide form would *)
(*  find it by scanning for a branch whose target is at most its own address, *)
(*  which is the whole CFG pass; the caller always knows which loop they      *)
(*  mean, so naming its back edge costs them one number and buys the other    *)
(*  six fields.                                                               *)
(*                                                                           *)
(*  NOTHING HERE IS TRUSTED.  Every field this computes is re-checked         *)
(*  downstream -- the instruction table by seg_placement_ok, the extent and   *)
(*  both guards by the VC itself.  A wrong derivation therefore cannot make a *)
(*  false theorem; it can only fail to prove a true one.  That is what buys   *)
(*  the convenience below: `loop_shape` is TOTAL, answering with an empty     *)
(*  body (shape_num_instrs = 0) rather than threading an option through every *)
(*  LoopSpec literal, and `loop_shape_found` is the vm_compute-checkable      *)
(*  early error for the cases where that happened.                            *)
(* ========================================================================= *)
Record LoopShape : Type := MkLoopShape
  { shape_first_instr : nat    (* the head, as a list index                   *)
  ; shape_num_instrs  : nat    (* head .. back edge, INCLUSIVE                *)
  ; shape_exit_off    : N      (* fall-through, RELATIVE to the head          *)
  ; shape_fuel        : nat
  ; shape_branch_op   : BOP    (* the back edge's condition and its operands, *)
  ; shape_branch_rs1  : RegIdx (* kept so the guards can be built without     *)
  ; shape_branch_rs2  : RegIdx (* decoding the instruction a second time      *)
  }.

(* The four ways `back` can fail to be a back edge, each answered with None
   rather than with a plausible-looking shape: it must exist, be a B-type
   branch, jump BACKWARDS by a multiple of the instruction width, and not
   jump off the front of the list.  A `Some` is then a real claim that
   indices `first .. back` are a loop body entered at `first`. *)
Definition loop_shape_at (prog : list AnnotInstr) (back slack : nat)
    : option LoopShape :=
  match nth_error prog back with
  | Some ai =>
      match ai_instr ai with
      | BTYPE imm rs2 rs1 op =>
          let off      := bv.signed imm in
          let back_off := (4 * Z.of_nat back)%Z in
          if (off <? 0)%Z then
            if (Z.rem off 4 =? 0)%Z then
              if (0 <=? back_off + off)%Z then
                let first := Z.to_nat ((back_off + off) / 4) in
                let num   := S (back - first) in
                Some (MkLoopShape first num (4 * N.of_nat num)%N (num + slack)
                        op rs1 rs2)
              else None
            else None
          else None
      | _ => None
      end
  | None => None
  end.

(* An empty body is the safe junk value: it makes the loop's instruction
   table empty, so the failure is immediate and local rather than subtle. *)
Definition loop_shape_bogus : LoopShape :=
  MkLoopShape 0 0 0%N 0 RISCV_BEQ bv.zero bv.zero.

Definition loop_shape (prog : list AnnotInstr) (back slack : nat) : LoopShape :=
  match loop_shape_at prog back slack with
  | Some sh => sh
  | None    => loop_shape_bogus
  end.

(* `Proof. vm_compute. reflexivity. Qed.` -- says "index `back` is not a back
   edge" AT the LoopSpec, instead of as a False in its VC ten minutes later. *)
Definition loop_shape_found (prog : list AnnotInstr) (back slack : nat) : bool :=
  match loop_shape_at prog back slack with Some _ => true | None => false end.

(* THE BRANCH, AS THE RECORD'S TWO GUARD FIELDS.  `c` is the counter's
   POST-step value, so the caller never re-writes the head-decrements-then-
   branch-tests off-by-one; `other` is the Sigma-level name for whatever the
   branch's OTHER operand holds, which is the one thing no CFG pass can
   supply.

   THIS IS NOT the mechanical relop flip the record's comment warns against.
   It is a TABLE, one row per BOP, each row naming the exact complement --
   available for all six because RISC-V's branch conditions are equality and
   two total orders, so `not (a < b)` really is `b <= a` at the same
   signedness.  A generic `formula_not` would have been the unsound shortcut;
   six explicit rows are not.  Operand ORDER is preserved rather than
   normalised (the eq/neq rows could swap and mean the same thing) because
   the solver matches terms syntactically. *)
Definition shape_guards {Σ : LCtx} (sh : LoopShape) (ctr : RegIdx)
    (other : Term Σ ty_xlenbits)
    : (Term Σ ty_xlenbits -> Formula Σ) * (Term Σ ty_xlenbits -> Formula Σ) :=
  if bv.eqb ctr (shape_branch_rs1 sh) then
    match shape_branch_op sh with
    | RISCV_BEQ  => (fun c => formula_relop bop.eq    c other,
                     fun c => formula_relop bop.neq   c other)
    | RISCV_BNE  => (fun c => formula_relop bop.neq   c other,
                     fun c => formula_relop bop.eq    c other)
    | RISCV_BLT  => (fun c => formula_relop bop.bvslt c other,
                     fun c => formula_relop bop.bvsle other c)
    | RISCV_BGE  => (fun c => formula_relop bop.bvsle other c,
                     fun c => formula_relop bop.bvslt c other)
    | RISCV_BLTU => (fun c => formula_relop bop.bvult c other,
                     fun c => formula_relop bop.bvule other c)
    | RISCV_BGEU => (fun c => formula_relop bop.bvule other c,
                     fun c => formula_relop bop.bvult c other)
    end
  else if bv.eqb ctr (shape_branch_rs2 sh) then
    (* the counter is the branch's SECOND operand, so every row is the mirror
       of the one above -- `c` and `other` trade places, the relops do not. *)
    match shape_branch_op sh with
    | RISCV_BEQ  => (fun c => formula_relop bop.eq    other c,
                     fun c => formula_relop bop.neq   other c)
    | RISCV_BNE  => (fun c => formula_relop bop.neq   other c,
                     fun c => formula_relop bop.eq    other c)
    | RISCV_BLT  => (fun c => formula_relop bop.bvslt other c,
                     fun c => formula_relop bop.bvsle c other)
    | RISCV_BGE  => (fun c => formula_relop bop.bvsle c other,
                     fun c => formula_relop bop.bvslt other c)
    | RISCV_BLTU => (fun c => formula_relop bop.bvult other c,
                     fun c => formula_relop bop.bvule c other)
    | RISCV_BGEU => (fun c => formula_relop bop.bvule c other,
                     fun c => formula_relop bop.bvult other c)
    end
  else
    (* the named counter is neither operand: an unsatisfiable guard, so the
       body contract fails rather than quietly testing something else. *)
    (fun _ => formula_false, fun _ => formula_false).

Definition shape_guard {Σ : LCtx} (sh : LoopShape) (ctr : RegIdx)
    (other : Term Σ ty_xlenbits) : Term Σ ty_xlenbits -> Formula Σ :=
  fst (shape_guards sh ctr other).

Definition shape_exit_guard {Σ : LCtx} (sh : LoopShape) (ctr : RegIdx)
    (other : Term Σ ty_xlenbits) : Term Σ ty_xlenbits -> Formula Σ :=
  snd (shape_guards sh ctr other).

(* WHAT A `Some` MEANS.  The two facts a LoopSpec built from a shape relies on
   and cannot check for itself: the branch at `back` really does target the
   head -- which is what makes loop_body_contract's exit target `0%N` correct
   -- and the body really does run from the head through that branch, which is
   what makes shape_exit_off the fall-through. *)
Lemma loop_shape_at_spec (prog : list AnnotInstr) (back slack : nat)
    (sh : LoopShape) (H : loop_shape_at prog back slack = Some sh) :
  exists (imm : bv 13) (ai : AnnotInstr),
    nth_error prog back = Some ai
    /\ @eq AST (ai_instr ai)
          (BTYPE imm (shape_branch_rs2 sh) (shape_branch_rs1 sh)
             (shape_branch_op sh))
    (* the back edge lands on the head.  Spelled with @eq/Z.mul rather than
       infix: asn.notations' `=`/`*` are in scope here and would elaborate
       these plain Z's against Term _ ty.int (see rocq-pitfalls). *)
    /\ @eq Z (Z.add (Z.mul 4 (Z.of_nat back)) (bv.signed imm))
             (Z.mul 4 (Z.of_nat (shape_first_instr sh)))
    (* the body is head .. back inclusive, so the fall-through is one past *)
    /\ Nat.le (shape_first_instr sh) back
    /\ @eq nat (shape_num_instrs sh) (S (Nat.sub back (shape_first_instr sh)))
    /\ @eq N (shape_exit_off sh) (N.mul 4 (N.of_nat (shape_num_instrs sh))).
Proof.
  unfold loop_shape_at in H.
  destruct (nth_error prog back) as [ai|] eqn:Hai; [|discriminate].
  destruct (ai_instr ai) eqn:Hi; try discriminate.
  destruct (bv.signed imm <? 0)%Z eqn:Hneg; [|discriminate].
  destruct (Z.rem (bv.signed imm) 4 =? 0)%Z eqn:Hrem; [|discriminate].
  destruct (0 <=? 4 * Z.of_nat back + bv.signed imm)%Z eqn:Hlo; [|discriminate].
  apply Z.ltb_lt in Hneg. apply Z.eqb_eq in Hrem. apply Z.leb_le in Hlo.
  injection H as <-.
  exists imm, ai.
  cbn [shape_first_instr shape_num_instrs shape_exit_off shape_fuel
       shape_branch_op shape_branch_rs1 shape_branch_rs2].
  assert (H4 : (4 <> 0)%Z) by lia.
  (* the alignment test is stated with Z.rem, which lia does NOT connect to
     divisibility on its own -- hence the explicit Z.rem_divide step. *)
  assert (Hd : (4 | 4 * Z.of_nat back + bv.signed imm)%Z).
  { apply Z.divide_add_r.
    - apply Z.divide_factor_l.
    - exact (proj1 (Z.rem_divide (bv.signed imm) 4 H4) Hrem). }
  assert (Hpos : (0 <= (4 * Z.of_nat back + bv.signed imm) / 4)%Z).
  { apply Z.div_pos; lia. }
  (* the head index is EXACT: Z.to_nat o (/4) undoes the 4.  Spelled with
     @eq/Z.mul for the same reason as the statement -- infix `=`/`*` here
     parse against Term _ ty.int. *)
  assert (Hex : @eq Z
                  (Z.mul 4 (Z.of_nat (Z.to_nat
                     (Z.div (Z.add (Z.mul 4 (Z.of_nat back)) (bv.signed imm)) 4))))
                  (Z.add (Z.mul 4 (Z.of_nat back)) (bv.signed imm))).
  { rewrite (Z2Nat.id _ Hpos). destruct Hd as [k Hk]. rewrite Hk.
    rewrite (Z.div_mul k 4 H4). lia. }
  repeat split; try reflexivity; try exact Hi; lia.
Qed.


(* ---- C1, CONTINUED: THE COUNTER'S STEP ----------------------------------

   The last `LoopSpec` field that has to silently agree with the code.  It is
   also the one whose being wrong is hardest to see: the step feeds
   `counter_after_step`, so a wrong value does not make the loop look wrong,
   it makes it look like a DIFFERENT loop -- and C2 and C3 both read their
   strides off it, so one typo propagates into the latch and the trip bound.

   Deriving it needs the counter's REGISTER, which no CFG pass can supply (it
   is the user's choice of which register the loop is "about"), so this is a
   separate function from `loop_shape` rather than another of its fields.

   WHAT MAKES IT MORE THAN A SCAN.  Looking for an `addi ctr, ctr, k` and
   taking `k` would be wrong in a way that fails silently: if the body ALSO
   writes `ctr` some other way (`add ctr, ctr, rX`, a `lw` into it), the step
   is not constant and the whole affine model is void, but a scan that only
   looks at ADDIs would report a confident, wrong answer.  So the body is
   scanned for EVERY write to `ctr`, and the answer is `None` unless there is
   exactly one and it is a constant-immediate self-increment.  Refusing beats
   guessing here, because the guess is what C2 and C3 build on. *)
Definition instr_writes (i : AST) : option RegIdx :=
  match i with
  | RTYPE _ _ rd _         => Some rd
  | ITYPE _ _ rd _         => Some rd
  | SHIFTIOP _ _ rd _      => Some rd
  | UTYPE _ rd _           => Some rd
  | RISCV_JAL _ rd         => Some rd
  | RISCV_JALR _ _ rd      => Some rd
  | LOAD _ _ rd _ _        => Some rd
  | CSR _ _ rd _ _         => Some rd
  (* QUALIFIED: `Import Assembly` puts a smart constructor named MUL in
     scope, which shadows the AST one and cannot appear in a pattern. *)
  | Base.MUL _ _ rd _ _ _  => Some rd
  | BTYPE _ _ _ _          => None   (* branches and stores write no register *)
  | STORE _ _ _ _          => None
  | ECALL | EBREAK | MRET  => None
  end.

Definition loop_body_slice (prog : list AnnotInstr) (sh : LoopShape)
    : list AnnotInstr :=
  List.firstn (shape_num_instrs sh) (List.skipn (shape_first_instr sh) prog).

Definition writes_to (ctr : RegIdx) (ai : AnnotInstr) : bool :=
  match instr_writes (ai_instr ai) with
  | Some r => bv.eqb r ctr
  | None   => false
  end.

Definition loop_ctr_step_at (prog : list AnnotInstr) (sh : LoopShape)
    (ctr : RegIdx) : option (Val ty_xlenbits) :=
  match List.filter (writes_to ctr) (loop_body_slice prog sh) with
  | ai :: nil =>
      match ai_instr ai with
      | ITYPE imm rs1 _ RISCV_ADDI =>
          (* self-increment, not merely a write: `addi ctr, rX, k` with
             rX <> ctr sets the counter rather than advancing it. *)
          if bv.eqb rs1 ctr
          then Some (@bv.of_Z xlenbits (bv.signed imm))
          else None
      | _ => None
      end
  | _ => None
  end.

(* Total, like `loop_shape`, and for the same reason -- nothing here is
   trusted.  The junk value is a ZERO step, which is the loudest one
   available: `loop_latch_*_affine` all demand `0 < stride`, so a loop built
   on a failed derivation cannot have its latch discharged. *)
Definition loop_ctr_step (prog : list AnnotInstr) (sh : LoopShape)
    (ctr : RegIdx) : Val ty_xlenbits :=
  match loop_ctr_step_at prog sh ctr with
  | Some s => s
  | None   => bv.zero
  end.

Definition loop_ctr_step_found (prog : list AnnotInstr) (sh : LoopShape)
    (ctr : RegIdx) : bool :=
  match loop_ctr_step_at prog sh ctr with Some _ => true | None => false end.

(* WHAT A `Some` MEANS: the body writes `ctr` exactly once, that write is a
   constant self-increment, and the step is its sign-extended immediate.  The
   first conjunct is the one worth having -- it is what licenses treating the
   counter as affine at all. *)
Lemma loop_ctr_step_at_spec (prog : list AnnotInstr) (sh : LoopShape)
    (ctr : RegIdx) (s : Val ty_xlenbits)
    (H : loop_ctr_step_at prog sh ctr = Some s) :
  exists (imm : bv 12) (rd : RegIdx) (ai : AnnotInstr),
    @eq (list AnnotInstr)
      (List.filter (writes_to ctr) (loop_body_slice prog sh)) (cons ai nil)
    /\ @eq AST (ai_instr ai) (ITYPE imm ctr rd RISCV_ADDI)
    /\ @eq (Val ty_xlenbits) s (@bv.of_Z xlenbits (bv.signed imm)).
Proof.
  unfold loop_ctr_step_at in H.
  destruct (List.filter (writes_to ctr) (loop_body_slice prog sh))
    as [|ai tl] eqn:Hf; [discriminate|].
  destruct tl; [|discriminate].
  destruct (ai_instr ai) eqn:Hi; try discriminate.
  destruct op; try discriminate.
  destruct (bv.eqb rs1 ctr) eqn:Hr; [|discriminate].
  (* bv.eqb_spec is a `reflect`, not an iff, so it cannot be applied to Hr
     directly. *)
  assert (rs1 = ctr) as -> by (destruct (bv.eqb_spec rs1 ctr); congruence).
  injection H as <-.
  (* `repeat split` closes the two reflexivity conjuncts itself -- `split` is
     `constructor`, and eq_refl is one. *)
  exists imm, rd, ai. repeat split; exact Hi.
Qed.

Record LoopSpec {Σ : LCtx} : Type := MkLoopSpec
  { loop_head_addr     : N            (* ABSOLUTE address of the loop head              *)
  ; loop_prog   : list AnnotInstr
  ; loop_first_instr   : nat          (* first instruction of the body, as a list index *)
  ; loop_num_instrs   : nat          (* how many instructions the body is              *)
  ; loop_exit_off   : N            (* fall-through target, RELATIVE to the head      *)
  ; loop_fuel   : nat

    (* C4: the loop's own CODE base, as a NAME plus its membership proof.  It
       used to be three fields -- loop_base / loop_base_pre / loop_base_post -- because a Term
       does not weaken, so the same variable had to be written once per
       context.  Storing the name and the In-proof instead lets the three
       Terms be DERIVED (below), which makes them agree by construction rather
       than by a convention nothing checked, and makes the composition lemmas'
       Hpa premise follow from Hpl by reflexivity.  In a LoopSpec literal the
       proof is written `_` and resolved by ctx.resolution. *)
  ; loop_base_var   : string
  ; loop_base_in    : (loop_base_var∷ty_xlenbits ∈ Σ)%katamaran

    (* THE COUNTER: its register, its variable (same treatment as loop_base_var --
       loop_counter_pre / loop_counter_post / loop_counter_post_ex were one variable at three weakenings), and
       its per-trip update. *)
  ; loop_counter_reg    : RegIdx
  ; loop_counter_var   : string
  ; loop_counter_in    : (loop_counter_var∷ty_xlenbits ∈ Σ)%katamaran
  ; loop_counter_step    : Val ty_xlenbits

    (* the classification: registers by spec list, every base with its bound,
       and an escape hatch for what a spec list cannot say -- a walking
       pointer's value, memory cells, anything loop-specific. *)
  ; loop_regs     : list reg_spec_rel
  ; loop_data_bounds_pre  : list (Term (Σ ▻ "a"∷ty_xlenbits) ty_xlenbits * N)
  ; loop_data_bounds_post : list (Term (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) ty_xlenbits * N)
  ; loop_extra_pre  : Assertion (Σ ▻ "a"∷ty_xlenbits)
  ; loop_extra_post : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)

    (* the branch, as a predicate on the counter's POST-decrement value.  Two
       fields rather than one plus a negation: Formula is not usefully closed
       under negation, and flipping a relop mechanically would be wrong for
       some comparison. *)
  ; loop_guard  : Term (Σ ▻ "a"∷ty_xlenbits) ty_xlenbits
                -> Formula (Σ ▻ "a"∷ty_xlenbits)
  ; loop_exit_guard  : Term (Σ ▻ "a"∷ty_xlenbits) ty_xlenbits
                -> Formula (Σ ▻ "a"∷ty_xlenbits)
  }.
Arguments LoopSpec : clear implicits.
Arguments MkLoopSpec {Σ}.

(* THE SIX DERIVED TERMS (C4).  Each is `term_var <name>` at one more binder
   than the last; `loop_base` and `loop_counter_pre` are DEFINITIONALLY the `term_var "q"` /
   `term_var "p1"` the LoopSpec literals used to spell out, so collapsing the
   fields changed no contract and re-proved no VC. *)
Definition loop_base {Σ : LCtx} (ls : LoopSpec Σ) : Term Σ ty_xlenbits :=
  @term_var Σ (loop_base_var ls) ty_xlenbits (loop_base_in ls).
Definition loop_base_pre {Σ : LCtx} (ls : LoopSpec Σ)
    : Term (Σ ▻ "a"∷ty_xlenbits) ty_xlenbits :=
  @term_var _ (loop_base_var ls) ty_xlenbits (ctx.in_succ (loop_base_in ls)).
Definition loop_base_post {Σ : LCtx} (ls : LoopSpec Σ)
    : Term (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) ty_xlenbits :=
  @term_var _ (loop_base_var ls) ty_xlenbits (ctx.in_succ (ctx.in_succ (loop_base_in ls))).

Definition loop_counter_pre {Σ : LCtx} (ls : LoopSpec Σ)
    : Term (Σ ▻ "a"∷ty_xlenbits) ty_xlenbits :=
  @term_var _ (loop_counter_var ls) ty_xlenbits (ctx.in_succ (loop_counter_in ls)).
Definition loop_counter_post {Σ : LCtx} (ls : LoopSpec Σ)
    : Term (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) ty_xlenbits :=
  @term_var _ (loop_counter_var ls) ty_xlenbits (ctx.in_succ (ctx.in_succ (loop_counter_in ls))).
Definition loop_counter_post_ex {Σ : LCtx} (ls : LoopSpec Σ)
    : Term (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits ▻ "c"∷ty_xlenbits)
           ty_xlenbits :=
  @term_var _ (loop_counter_var ls) ty_xlenbits
    (ctx.in_succ (ctx.in_succ (ctx.in_succ (loop_counter_in ls)))).

(* NOT `Arguments … : simpl never`, though that is the obvious way to make
   these behave like the record PROJECTIONS they replace.  It is too blunt:
   the examples' proofs rely on `cbn` reducing `loop_counter_pre (ldSpec iq)` -- a
   projection of a CONCRETE record -- down to `term_var "p1"`, and blocking
   the definition blocks that too.  The problem is only the VARIABLE case, in
   this file's own latch lemmas, where `cbn` would unfold `loop_counter_pre ls` into
   `term_var (loop_counter_var ls) …` and strand a `rewrite Hk` written against the
   folded form.  Those few sites say `cbn -[loop_counter_pre]` instead. *)

(* What loop_base_pre's extra binder costs: nothing.  This is why the composition
   lemmas need only the BARE placement fact -- the "a"-context one follows.
   (Before C4 the two were independent fields and both had to be supplied.) *)
Lemma inst_loop_base_pre {Σ : LCtx} (ls : LoopSpec Σ) (i : Valuation Σ)
  (w : RelVal ty_xlenbits) :
  inst (T := fun Σ => Term Σ ty_xlenbits) (loop_base_pre ls) (i.["a"∷ty_xlenbits ↦ w])
  = inst (T := fun Σ => Term Σ ty_xlenbits) (loop_base ls) i.
Proof. reflexivity. Qed.

(* THE LOOP'S OWN CODE EXTENT.  The body is `loop_num_instrs` instructions starting at
   `loop_first_instr`, so it occupies 4*loop_num_instrs bytes.  This used to be written by hand
   as the LEADING entry of loop_data_bounds_pre/loop_data_bounds_post, where it had to agree with
   loop_num_instrs (and, for a bottom-tested loop, with loop_exit_off) and could silently
   drift; 7/7 loops in the tree had all three equal.  It is now derived, and
   ls_bases_* carry DATA bases only. *)
Definition loop_code_extent {Σ : LCtx} (ls : LoopSpec Σ) : N :=
  (4 * N.of_nat (loop_num_instrs ls))%N.

(* EVERY base the loop uses, code first.  The code entry used to be written by
   hand as the head of loop_data_bounds_pre/loop_data_bounds_post; deriving it is what lets
   loop_code_extent stay the single source of truth, and it keeps the frames below
   SYMMETRIC and shaped exactly as they were before A3 -- which is why
   loop_frame_transfer, loop_back_edge and loop_runs needed no restructuring. *)
Definition loop_all_bounds_pre {Σ : LCtx} (ls : LoopSpec Σ)
    : list (Term (Σ ▻ "a"∷ty_xlenbits) ty_xlenbits * N) :=
  (loop_base_pre ls, loop_code_extent ls) :: loop_data_bounds_pre ls.

Definition loop_all_bounds_post {Σ : LCtx} (ls : LoopSpec Σ)
    : list (Term (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) ty_xlenbits * N) :=
  (loop_base_post ls, loop_code_extent ls) :: loop_data_bounds_post ls.

(* What is the same at entry and exit.  Written once per context because a
   Term does not weaken; the two must agree, and that is a real proof
   obligation at composition, not a convention. *)
Definition gen_loop_frame_pre {Σ : LCtx} (ls : LoopSpec Σ)
    : Assertion (Σ ▻ "a"∷ty_xlenbits) :=
  ( gen_loop_bounds (loop_all_bounds_pre ls)
    ∗ gen_regs_at (loop_base_pre ls) (loop_regs ls)
    ∗ loop_extra_pre ls )%asn.

Definition gen_loop_frame_post {Σ : LCtx} (ls : LoopSpec Σ)
    : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( gen_loop_bounds (loop_all_bounds_post ls)
    ∗ gen_regs_at (loop_base_post ls) (loop_regs ls)
    ∗ loop_extra_post ls )%asn.

(* The counter and the frame.  SHARED by the contracts' preconditions and the
   invariant, which differ only in what each adds.

   MIND THE minimal_pre.  CFG_VC_triple already wraps a precondition in
   extend_to_minimal_pre, so gen_loop_contract_pre must NOT carry it -- a second copy
   makes the pre demand two and the post return one, i.e. the body consumes
   cur_privilege / inv_leakage every trip and can only run ONCE.  That still
   VERIFIES, so it fails late and only at composition; it is the amBody_post
   bug, and it bit this file too.  The INVARIANT does carry minimal_pre,
   because it describes the whole state at the loop head. *)
Definition gen_loop_state {Σ : LCtx} (ls : LoopSpec Σ)
    : Assertion (Σ ▻ "a"∷ty_xlenbits) :=
  ( loop_counter_reg ls ↦ᵣ loop_counter_pre ls
    ∗ asn.formula (formula_secLeak (loop_counter_pre ls))
    ∗ gen_loop_frame_pre ls )%asn.

Definition gen_loop_at_head {Σ : LCtx} (ls : LoopSpec Σ)
    : Assertion (Σ ▻ "a"∷ty_xlenbits) :=
  ( gen_loop_state ls ∗ minimal_pre )%asn.

(* ...and the branch decision is the ONLY thing a contract adds.  Note it is
   applied to counter_after_step, never to the raw counter: the head decrements, THEN the
   branch tests, and that off-by-one is now unstateable. *)
(* NOT `gen_loop_state ∗ guard`, since A3: this is what the contract hands to
   gen_seg_contract as its `extra_pre`, and gen_seg_contract emits the code
   bound and the register block ITSELF.  So this is gen_loop_state MINUS those
   two, plus the branch decision -- and gen_loop_at_head, which is the invariant's
   view, still carries all of it.  The two therefore have the same conjuncts in
   a different order, which is why loop_body_trip's HPre is an iFrame and not a
   rewrite. *)
Definition gen_loop_contract_pre {Σ : LCtx} (ls : LoopSpec Σ)
    (g : Term (Σ ▻ "a"∷ty_xlenbits) ty_xlenbits -> Formula (Σ ▻ "a"∷ty_xlenbits))
    : Assertion (Σ ▻ "a"∷ty_xlenbits) :=
  ( loop_counter_reg ls ↦ᵣ loop_counter_pre ls
    ∗ asn.formula (formula_secLeak (loop_counter_pre ls))
    ∗ gen_loop_bounds (loop_data_bounds_pre ls)
    ∗ loop_extra_pre ls
    ∗ asn.formula (g (counter_after_step (loop_counter_step ls) (loop_counter_pre ls))) )%asn.

(* The body's post binds a FRESH variable and states the decrement as a PURE
   equation, rather than putting the computed term in the spatial part.  That
   is what lets the back edge frame like any other cut (measured: it removes
   the valuation-crossing rewrite entirely). *)
Definition gen_loop_contract_post {Σ : LCtx} (ls : LoopSpec Σ)
    : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  ( asn.exist "c" ty_xlenbits
      ( loop_counter_reg ls ↦ᵣ term_var "c"
        ∗ asn.formula (formula_relop bop.eq (term_var "c")
                         (counter_after_step (loop_counter_step ls) (loop_counter_post_ex ls)))
        ∗ asn.formula (formula_secLeak (term_var "c")) )
    ∗ gen_loop_frame_post ls )%asn.

(* A3 (PLAN-loop-automation.md): a loop's contract IS an ordinary segment
   contract, entered at head 0 of its own code base.  It used to build a
   MkCFGVerifierContract by hand, which meant loop_final_contract could compose with a
   following segment but could not be STATED in segment vocabulary.

   What changed in the generated contract, and why none of it is cosmetic:
     - the precondition is now gen_seg_contract's layout (pc-eq, code bound,
       extra, registers LAST) rather than the loop generator's.  Conjunct order
       moves consume-scan positions, so this was measured, not assumed --
       ZZSpikeA3.v verifies both of loop D's contracts, the shape with two
       walking pointers, two cells and three base bounds;
     - cfg_placement is `loop_base + 0` and cfg_init_addr `loop_head_addr + 0`, neither
       definitionally the bare form, which is why the composition lemmas pick
       up a bv.add_zero_r / N.add_0_r;
     - cfg_exitCond is unchanged (`seg_exitCond (loop_head_addr ls) [target]`), because
       gen_seg_contract takes ia and head separately. *)
Definition gen_loop_contract {Σ : LCtx} (ls : LoopSpec Σ)
    (g : Term (Σ ▻ "a"∷ty_xlenbits) ty_xlenbits -> Formula (Σ ▻ "a"∷ty_xlenbits))
    (target : N)
    (post : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
    : @CFGVerifierContract Σ :=
  gen_seg_contract (loop_base ls) (loop_base_pre ls) (loop_head_addr ls) 0
    (loop_prog ls) (loop_first_instr ls) (loop_num_instrs ls) [target]
    (loop_code_extent ls) (loop_fuel ls) (loop_regs ls)
    (gen_loop_contract_pre ls g) post.

(* THE FOUR PROJECTIONS the composition lemmas use, so they never cbn through
   gen_seg_contract's `let place := …`.  Three are eq_refl.  Only the exit
   table needs a rewrite: gen_seg_contract subtracts the head offset from every
   target, and `t - 0` is STUCK for a variable t (N.sub matches on its first
   argument, so it cannot see that the second is zero). *)
Lemma gen_loop_place {Σ : LCtx} (ls : LoopSpec Σ)
    (g : Term (Σ ▻ "a"∷ty_xlenbits) ty_xlenbits -> Formula (Σ ▻ "a"∷ty_xlenbits))
    (target : N) (post : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) :
  cfg_placement (gen_loop_contract ls g target post)
  = term_binop bop.bvadd (loop_base ls) (term_val ty_xlenbits (bv.of_N 0)).
Proof. reflexivity. Qed.

Lemma gen_loop_exitCond {Σ : LCtx} (ls : LoopSpec Σ)
    (g : Term (Σ ▻ "a"∷ty_xlenbits) ty_xlenbits -> Formula (Σ ▻ "a"∷ty_xlenbits))
    (target : N) (post : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) :
  cfg_exitCond (gen_loop_contract ls g target post)
  = seg_exitCond (loop_head_addr ls) [target].
Proof. reflexivity. Qed.

Lemma gen_loop_instrs {Σ : LCtx} (ls : LoopSpec Σ)
    (g : Term (Σ ▻ "a"∷ty_xlenbits) ty_xlenbits -> Formula (Σ ▻ "a"∷ty_xlenbits))
    (target : N) (post : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) :
  cfg_instrs (gen_loop_contract ls g target post)
  = List.firstn (loop_num_instrs ls) (List.skipn (loop_first_instr ls) (loop_prog ls)).
Proof. reflexivity. Qed.

Lemma gen_loop_exits {Σ : LCtx} (ls : LoopSpec Σ)
    (g : Term (Σ ▻ "a"∷ty_xlenbits) ty_xlenbits -> Formula (Σ ▻ "a"∷ty_xlenbits))
    (target : N) (post : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)) :
  cfg_exits (gen_loop_contract ls g target post)
  = exits_of_offs (term_binop bop.bvadd (loop_base ls) (term_val ty_xlenbits (bv.of_N 0)))
      [target].
Proof.
  unfold gen_loop_contract, gen_seg_contract.
  cbn [cfg_exits List.map]. now rewrite N.sub_0_r.
Qed.

(* BODY: guard holds, back edge to the head (offset 0 -- the loop is stated
   against its own entry address). *)
Definition loop_body_contract {Σ : LCtx} (ls : LoopSpec Σ) : @CFGVerifierContract Σ :=
  gen_loop_contract ls (loop_guard ls) 0%N (gen_loop_contract_post ls).

(* FINAL: the guard fails, fall out to loop_exit_off.  Its postcondition is the
   caller's -- that is the cut into whatever follows the loop, and it is
   genuine specification. *)
Definition loop_final_contract {Σ : LCtx} (ls : LoopSpec Σ)
    (post : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
    : @CFGVerifierContract Σ :=
  gen_loop_contract ls (loop_exit_guard ls) (loop_exit_off ls) post.


(* head 0 is not definitionally `+ 0`, so the two shapes the composition needs
   get their own one-liners. *)
Lemma seg_addr_0 (ia : N) : seg_addr ia 0 = @bv.of_N xlenbits ia.
Proof. unfold seg_addr. f_equal. lia. Qed.

(* A3 made every loop's cfg_placement `loop_base + 0` rather than the bare `loop_base`,
   because gen_seg_contract always adds its head offset.  The composition
   lemmas are handed the BARE fact (`inst (loop_base ls) iota = SyncVal q`, which is
   reflexivity for a caller whose iota maps "q" to a literal), so these two
   carry it across the `+ 0`.  Stated for a general offset as well, because
   loop_enter_from_seg will want the non-zero case. *)
Lemma inst_addr_plus {R : LCtx} (t : Term R ty_xlenbits) (iota : Valuation R)
  (q : bv xlenbits) (off : N)
  (H : inst (T := fun Σ => Term Σ ty_xlenbits) t iota = ty.SyncVal q) :
  inst (T := fun Σ => Term Σ ty_xlenbits)
    (term_binop bop.bvadd t (term_val ty_xlenbits (bv.of_N off))) iota
  = ty.SyncVal (bv.add q (@bv.of_N xlenbits off)).
Proof. cbn. now rewrite H. Qed.

Lemma inst_addr_plus0 {R : LCtx} (t : Term R ty_xlenbits) (iota : Valuation R)
  (q : bv xlenbits)
  (H : inst (T := fun Σ => Term Σ ty_xlenbits) t iota = ty.SyncVal q) :
  inst (T := fun Σ => Term Σ ty_xlenbits)
    (term_binop bop.bvadd t (term_val ty_xlenbits (bv.of_N 0))) iota
  = ty.SyncVal q.
Proof.
  rewrite (inst_addr_plus t iota q 0 H). do 2 f_equal.
  apply bv.add_zero_r.
Qed.

Lemma seg_exitCond_hit0 (iq : N) (targets : list N) (t : N)
  (Hin : List.In t targets) :
  seg_exitCond iq targets (bv.add (@bv.of_N xlenbits iq) (@bv.of_N xlenbits t))
  = true.
Proof. rewrite <- seg_addr_add. now apply seg_exitCond_hit. Qed.

(* The counter step of a COUNTED loop, at the bitvector level.  `addi ctr,ctr,-s`
   assembles to an add of the wrap-around literal `2^32 - s` (RISC-V has no
   subtract-immediate), so every counted loop's trip-to-trip transfer needs
   exactly this rewrite.  Unconditional in `m`: it is the wrap that makes it
   true, not a no-overflow side condition -- the `dvP`-style bound a loop
   carries is for its GUARD, not for this step. *)
Lemma bv_of_N_wrap_dec (s m : N) (Hs : (s <= bv.exp2 xlenbits)%N) :
  bv.add (@bv.of_N xlenbits (m + s)) (@bv.of_N xlenbits (bv.exp2 xlenbits - s))
  = @bv.of_N xlenbits m.
Proof.
  rewrite bv.of_N_add.
  replace (m + s + (bv.exp2 xlenbits - s))%N with (m + bv.exp2 xlenbits)%N by lia.
  rewrite <- (bv.of_N_add (n := xlenbits) m (bv.exp2 xlenbits)).
  replace (@bv.of_N xlenbits (bv.exp2 xlenbits)) with (@bv.zero xlenbits)
    by (vm_compute; reflexivity).
  now rewrite bv.add_zero_r.
Qed.

(* ---- THE LATCH ------------------------------------------------------------

   `loop_body_trip`/`loop_final_trip` each leave one obligation about the BRANCH: the
   guard holds at trip S n, the exit guard holds at trip 0.  Both are the same
   three moves -- read the counter off the valuation, apply the machine's
   step, compare -- so they are proved ONCE here and instantiated per loop.

   There is a pair per relop family, not one relop-parametric lemma: a
   parametric version would need the two formulas' complementarity as a
   per-loop side condition, which is most of what these exist to delete.  The
   seven muladd loops use exactly two families:

     neq/eq    -- the counter (usually a walking POINTER) against a sentinel,
                  either a limit variable or a literal.  5 of 7.
     ult/ule   -- a countdown against a literal bound.  2 of 7.

   `Hstep` is the one place the machine's arithmetic enters: supply
   `bv_of_N_wrap_dec` for a decrement and `eq_sym (bv.of_N_add ..)` for an
   increment.  Everything else is bounds, stated in N so the caller never
   touches `bv.bin`. *)

Lemma loop_latch_neq {R : LCtx} (ls : LoopSpec R)
  (i : Valuation (R ▻ "a"∷ty_xlenbits))
  (e : Term (R ▻ "a"∷ty_xlenbits) ty_xlenbits) (kv w ev : N)
  (Hg : loop_guard ls = fun t => formula_relop bop.neq t e)
  (Hk : inst (T := fun Σ => Term Σ ty_xlenbits) (loop_counter_pre ls) i
        = ty.SyncVal (@bv.of_N xlenbits kv))
  (He : inst (T := fun Σ => Term Σ ty_xlenbits) e i
        = ty.SyncVal (@bv.of_N xlenbits ev))
  (Hstep : bv.add (@bv.of_N xlenbits kv) (loop_counter_step ls) = @bv.of_N xlenbits w)
  (Hw : (w < bv.exp2 xlenbits)%N) (Hev : (ev < bv.exp2 xlenbits)%N)
  (Hne : w <> ev) :
  instprop (loop_guard ls (counter_after_step (loop_counter_step ls) (loop_counter_pre ls))) i.
Proof.
  (* `cbn -[loop_counter_pre]`, not plain `cbn`: with ls a VARIABLE, cbn unfolds the
     C4 accessor into `term_var (loop_counter_var ls) …` and Hk -- stated against the
     folded form -- then matches nothing. *)
  rewrite Hg. cbn -[loop_counter_pre]. rewrite Hk. rewrite He. cbn. rewrite Hstep.
  intros Hc. apply Hne.
  apply (f_equal (@bv.bin xlenbits)) in Hc.
  rewrite (bv.bin_of_N_small Hw) in Hc.
  rewrite (bv.bin_of_N_small Hev) in Hc. exact Hc.
Qed.

Lemma loop_latch_eq {R : LCtx} (ls : LoopSpec R)
  (i : Valuation (R ▻ "a"∷ty_xlenbits))
  (e : Term (R ▻ "a"∷ty_xlenbits) ty_xlenbits) (kv w ev : N)
  (Hg : loop_exit_guard ls = fun t => formula_relop bop.eq t e)
  (Hk : inst (T := fun Σ => Term Σ ty_xlenbits) (loop_counter_pre ls) i
        = ty.SyncVal (@bv.of_N xlenbits kv))
  (He : inst (T := fun Σ => Term Σ ty_xlenbits) e i
        = ty.SyncVal (@bv.of_N xlenbits ev))
  (Hstep : bv.add (@bv.of_N xlenbits kv) (loop_counter_step ls) = @bv.of_N xlenbits w)
  (Heq : w = ev) :
  instprop (loop_exit_guard ls (counter_after_step (loop_counter_step ls) (loop_counter_pre ls))) i.
Proof.
  (* `cbn -[loop_counter_pre]`, not plain `cbn`: with ls a VARIABLE, cbn unfolds the
     C4 accessor into `term_var (loop_counter_var ls) …` and Hk -- stated against the
     folded form -- then matches nothing. *)
  rewrite Hg. cbn -[loop_counter_pre]. rewrite Hk. rewrite He. cbn. rewrite Hstep.
  now subst w.
Qed.

Lemma loop_latch_ult {R : LCtx} (ls : LoopSpec R)
  (i : Valuation (R ▻ "a"∷ty_xlenbits)) (b kv w : N)
  (Hg : loop_guard ls = fun t => formula_relop bop.bvult
                                 (term_val ty_xlenbits (@bv.of_N xlenbits b)) t)
  (Hk : inst (T := fun Σ => Term Σ ty_xlenbits) (loop_counter_pre ls) i
        = ty.SyncVal (@bv.of_N xlenbits kv))
  (Hstep : bv.add (@bv.of_N xlenbits kv) (loop_counter_step ls) = @bv.of_N xlenbits w)
  (Hb : (b < bv.exp2 xlenbits)%N) (Hw : (w < bv.exp2 xlenbits)%N)
  (Hlt : (b < w)%N) :
  instprop (loop_guard ls (counter_after_step (loop_counter_step ls) (loop_counter_pre ls))) i.
Proof.
  rewrite Hg. cbn -[loop_counter_pre]. rewrite Hk. cbn. rewrite Hstep. unfold bv.ult.
  rewrite (bv.bin_of_N_small Hb).
  rewrite (bv.bin_of_N_small Hw). exact Hlt.
Qed.

Lemma loop_latch_ule {R : LCtx} (ls : LoopSpec R)
  (i : Valuation (R ▻ "a"∷ty_xlenbits)) (b kv w : N)
  (Hg : loop_exit_guard ls = fun t => formula_relop bop.bvule t
                                 (term_val ty_xlenbits (@bv.of_N xlenbits b)))
  (Hk : inst (T := fun Σ => Term Σ ty_xlenbits) (loop_counter_pre ls) i
        = ty.SyncVal (@bv.of_N xlenbits kv))
  (Hstep : bv.add (@bv.of_N xlenbits kv) (loop_counter_step ls) = @bv.of_N xlenbits w)
  (Hb : (b < bv.exp2 xlenbits)%N) (Hw : (w < bv.exp2 xlenbits)%N)
  (Hle : (w <= b)%N) :
  instprop (loop_exit_guard ls (counter_after_step (loop_counter_step ls) (loop_counter_pre ls))) i.
Proof.
  rewrite Hg. cbn -[loop_counter_pre]. rewrite Hk. cbn. rewrite Hstep. unfold bv.ule.
  rewrite (bv.bin_of_N_small Hb).
  rewrite (bv.bin_of_N_small Hw). exact Hle.
Qed.

(* ---- THE LATCH, AS ONE OBLIGATION ---------------------------------------

   `loop_runs` asks for two things about the branch: that the GUARD holds at
   every trip that still has work, and that the EXIT guard holds at trip 0.
   They are the same branch read two ways, and every loop discharged them as
   two near-identical `refine`s whose bullets were the same six moves --
   differing only in the counter values, which are exactly the values
   `loop_back_edge_std` already takes.  `loop_latch_obligation` names the pair; the two
   builders below produce it from the counter alone, so a loop states its
   recurrence ONCE.

   `kv n` is the counter as read off trip n BEFORE the latch's own step, and
   `w n` is it after -- the value the branch actually compares.  The trip
   predicate `P` is what separates "still looping" from "done": the guard
   obligation may assume `P (S n)`, the exit obligation gets nothing. *)
Definition loop_latch_obligation {R : LCtx} (ls : LoopSpec R)
    (iota : nat -> Valuation R) (q : bv xlenbits) (P : nat -> Prop) : Prop :=
  (forall n, P (S n) ->
     instprop (loop_guard ls (counter_after_step (loop_counter_step ls) (loop_counter_pre ls)))
       ((iota (S n)).["a"∷ty_xlenbits ↦ ty.SyncVal q]))
  /\ instprop (loop_exit_guard ls (counter_after_step (loop_counter_step ls) (loop_counter_pre ls)))
       ((iota 0).["a"∷ty_xlenbits ↦ ty.SyncVal q]).

(* Both builders take their facts as `forall n, P n -> ...`.  That is not
   decoration: a COUNTDOWN's no-wrap bound is FALSE for large n, so an
   unconditional hypothesis could not be discharged at all.  The two
   obligations only ever look at trip `S n` (where the guard half has
   `P (S n)`) and trip 0 (hence `HP0`, which `loop_runs` already carries), so
   this is exactly as strong as it needs to be. *)

(* THE POINTER-COMPARE FAMILY: `bne c, e` / `beq c, e`, where the limit `e` is
   a TERM of the loop's context (B, C, D, F, Tail).  What the loop supplies is
   its counter, its limit, and the one fact that makes the loop terminate --
   the counter misses the limit while trips remain and hits it at trip 0. *)
Lemma loop_latch_ptr {R : LCtx} (ls : LoopSpec R)
  (iota : nat -> Valuation R) (q : bv xlenbits) (P : nat -> Prop)
  (e : Term (R ▻ "a"∷ty_xlenbits) ty_xlenbits) (kv w : nat -> N) (ev : N)
  (HP0 : P 0)
  (Hg  : loop_guard ls = fun t => formula_relop bop.neq t e)
  (Hxg : loop_exit_guard ls = fun t => formula_relop bop.eq t e)
  (Hk : forall n, P n ->
          inst (T := fun Σ => Term Σ ty_xlenbits) (loop_counter_pre ls)
            ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])
          = ty.SyncVal (@bv.of_N xlenbits (kv n)))
  (He : forall n, P n ->
          inst (T := fun Σ => Term Σ ty_xlenbits) e
            ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])
          = ty.SyncVal (@bv.of_N xlenbits ev))
  (Hstep : forall n, P n ->
             bv.add (@bv.of_N xlenbits (kv n)) (loop_counter_step ls)
             = @bv.of_N xlenbits (w n))
  (Hwb : forall n, P n -> (w n < bv.exp2 xlenbits)%N)
  (Hev : (ev < bv.exp2 xlenbits)%N)
  (Hne : forall n, P (S n) -> w (S n) <> ev)
  (Heq : w 0%nat = ev) :
  loop_latch_obligation ls iota q P.
Proof.
  split.
  - intros n HP.
    exact (loop_latch_neq ls _ e (kv (S n)) (w (S n)) ev Hg (Hk _ HP)
             (He _ HP) (Hstep _ HP) (Hwb _ HP) Hev (Hne n HP)).
  - exact (loop_latch_eq ls _ e (kv 0) (w 0) ev Hxg (Hk 0 HP0) (He 0 HP0)
             (Hstep 0 HP0) Heq).
Qed.

(* THE COUNTER-VS-BOUND FAMILY: `bltu b, c` / `bleu c, b` against a LITERAL
   bound (A, divrem).  Same shape; the limit is a constant rather than a term,
   so there is no `He`. *)
Lemma loop_latch_ctr {R : LCtx} (ls : LoopSpec R)
  (iota : nat -> Valuation R) (q : bv xlenbits) (P : nat -> Prop)
  (b : N) (kv w : nat -> N)
  (HP0 : P 0)
  (Hg  : loop_guard ls = fun t => formula_relop bop.bvult
                                 (term_val ty_xlenbits (@bv.of_N xlenbits b)) t)
  (Hxg : loop_exit_guard ls = fun t => formula_relop bop.bvule t
                                 (term_val ty_xlenbits (@bv.of_N xlenbits b)))
  (Hk : forall n, P n ->
          inst (T := fun Σ => Term Σ ty_xlenbits) (loop_counter_pre ls)
            ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])
          = ty.SyncVal (@bv.of_N xlenbits (kv n)))
  (Hstep : forall n, P n ->
             bv.add (@bv.of_N xlenbits (kv n)) (loop_counter_step ls)
             = @bv.of_N xlenbits (w n))
  (Hb : (b < bv.exp2 xlenbits)%N)
  (Hwb : forall n, P n -> (w n < bv.exp2 xlenbits)%N)
  (Hlt : forall n, P (S n) -> (b < w (S n))%N)
  (* `0%nat`: the %N would otherwise make `w`'s ARGUMENT parse as N. *)
  (Hle : (w 0%nat <= b)%N) :
  loop_latch_obligation ls iota q P.
Proof.
  split.
  - intros n HP.
    exact (loop_latch_ult ls _ b (kv (S n)) (w (S n)) Hg (Hk _ HP)
             (Hstep _ HP) Hb (Hwb _ HP) (Hlt n HP)).
  - exact (loop_latch_ule ls _ b (kv 0) (w 0) Hxg (Hk 0 HP0) (Hstep 0 HP0) Hb
             (Hwb 0 HP0) Hle).
Qed.


(* ---- C2: THE AFFINE LATCH, SO A LOOP STATES ITS RECURRENCE ONCE ----------

   Spike (a) found that every `iota` in the tree is `anchor + n·stride` with
   every stride already a field of the `LoopSpec`, and -- the part that
   matters -- that the counter's ANCHOR IS FORCED rather than chosen: writing
   `counter n = sentinel − (n+1)·imm` reproduces all seven hand-written
   families exactly, because that is precisely what `loop_latch_obligation`
   demands.  It is two-sided (exit at trip 0, guard above it), which is what
   pins the `+1`.

   So the `+1` is the thing worth removing from user code: it is forced, it is
   invisible in the goal, and getting it wrong fails late.  The two lemmas
   below take the closed form as DATA -- an anchor and a stride -- and
   discharge every one of `loop_latch_ptr`/`_ctr`'s seven remaining premises
   from three N-level facts.  A loop then names its recurrence once, in
   `loop_ctr_down`/`loop_ctr_up`, and never writes `kv`, `w`, `ev`, or the
   wrap-around step again.

   WHY THE LATCH AND NOT JUST `iota`.  Deriving `iota` alone would have left
   each loop's `refine (loop_latch_ptr ...)` and its seven bullets standing --
   `mulinner_latch` and `walkup_latch` are byte-identical apart from variable
   names -- and would have forced ONE arithmetic on both families, where the
   pointer family wants N-subtraction and the counter family N-addition.  At
   this level each family keeps its own form and the user never writes either.

   NOT DERIVED, deliberately: the non-counter walking pointers.  They do not
   appear in `loop_latch_obligation` at all (only the counter and the limit
   do), so asking for them here would be asking for data the obligation
   cannot use. *)

(* The counter as a function of TRIPS REMAINING.  `down` for a pointer walking
   up towards a limit (the limit is the anchor, and trip 0 is AT it); `up` for
   a countdown towards a bound (the bound is the anchor, trip 0 is AT it).
   Both carry the forced `+1`. *)
Definition loop_ctr_down (anchor stride : N) (n : nat) : N :=
  (anchor - stride * (N.of_nat n + 1))%N.

Definition loop_ctr_up (bound stride : N) (n : nat) : N :=
  (bound + stride * (N.of_nat n + 1))%N.

(* TWO AXES, NOT ONE -- worth stating because the obvious reading is wrong.
   The GUARD FAMILY (`ptr` = neq/eq against a term, `ctr` = bvult/bvule against
   a literal) and the DIRECTION (does the counter grow or shrink as trips
   REMAIN) are independent.  Of the five `ptr` loops, D, F and Tail count down
   (`loop_counter_step` positive) while B and C count up (step negative, hence
   encoded as a wrap-around `2^32 - stride`).  So `ptr` needs both directions
   below.  `ctr` gets only `_up`, because no loop in the tree counts the other
   way -- an absence, not an impossibility.

   THE POINTER-COMPARE FAMILY, COUNTING DOWN (D, F, Tail).  `anch` is both the
   counter's anchor and the limit's value -- one number, not two, and that
   identity is the spike's "the anchor is forced" restated: the loop stops
   exactly when the counter reaches the limit, so `ev` cannot be anything else.
   Passing them separately would have let a non-terminating loop typecheck. *)
Lemma loop_latch_ptr_affine_down {R : LCtx} (ls : LoopSpec R)
  (iota : nat -> Valuation R) (q : bv xlenbits) (P : nat -> Prop)
  (e : Term (R ▻ "a"∷ty_xlenbits) ty_xlenbits) (anch stride : N)
  (HP0 : P 0)
  (Hg  : loop_guard ls = fun t => formula_relop bop.neq t e)
  (Hxg : loop_exit_guard ls = fun t => formula_relop bop.eq t e)
  (Himm : loop_counter_step ls = @bv.of_N xlenbits stride)
  (Hk : forall n, P n ->
          inst (T := fun Σ => Term Σ ty_xlenbits) (loop_counter_pre ls)
            ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])
          = ty.SyncVal (@bv.of_N xlenbits (loop_ctr_down anch stride n)))
  (He : forall n, P n ->
          inst (T := fun Σ => Term Σ ty_xlenbits) e
            ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])
          = ty.SyncVal (@bv.of_N xlenbits anch))
  (Hs : (0 < stride)%N)
  (HPle : forall n, P n -> (stride * (N.of_nat n + 1) <= anch)%N)
  (Hb : (anch < bv.exp2 xlenbits)%N) :
  loop_latch_obligation ls iota q P.
Proof.
  refine (loop_latch_ptr ls iota q P e (loop_ctr_down anch stride)
            (fun n => (anch - stride * N.of_nat n)%N) anch
            HP0 Hg Hxg Hk He _ _ Hb _ _).
  - (* the latch's own step, at the bv level: one increment, no wrap *)
    intros n HP. rewrite Himm. rewrite bv.of_N_add. f_equal.
    unfold loop_ctr_down. pose proof (HPle n HP). lia.
  - (* the post-step counter fits *) intros n HP. pose proof (HPle n HP). lia.
  - (* MISSES the limit while trips remain.  This is where `0 < stride` earns
       its place: a zero stride would make the counter sit on the limit
       forever and the loop would not terminate. *)
    intros n HP. pose proof (HPle (S n) HP). cbn [N.of_nat] in *. lia.
  - (* HITS it at trip 0 *) pose proof (HPle 0%nat HP0). lia.
Qed.

(* THE POINTER-COMPARE FAMILY, COUNTING UP (B, C).  Same identity `anch = ev`,
   mirrored.  Two differences from `_down`, both forced by the direction:
   `Himm` is the wrap-around form (a negative step is not a `Val ty_xlenbits`),
   and there is no separate `Hb` -- `HPb` at trip 0 already bounds the anchor,
   so asking for it again would be asking the caller to prove it twice. *)
Lemma loop_latch_ptr_affine_up {R : LCtx} (ls : LoopSpec R)
  (iota : nat -> Valuation R) (q : bv xlenbits) (P : nat -> Prop)
  (e : Term (R ▻ "a"∷ty_xlenbits) ty_xlenbits) (anch stride : N)
  (HP0 : P 0)
  (Hg  : loop_guard ls = fun t => formula_relop bop.neq t e)
  (Hxg : loop_exit_guard ls = fun t => formula_relop bop.eq t e)
  (Himm : loop_counter_step ls
          = @bv.of_N xlenbits (bv.exp2 xlenbits - stride))
  (Hk : forall n, P n ->
          inst (T := fun Σ => Term Σ ty_xlenbits) (loop_counter_pre ls)
            ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])
          = ty.SyncVal (@bv.of_N xlenbits (loop_ctr_up anch stride n)))
  (He : forall n, P n ->
          inst (T := fun Σ => Term Σ ty_xlenbits) e
            ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])
          = ty.SyncVal (@bv.of_N xlenbits anch))
  (Hs : (0 < stride < bv.exp2 xlenbits)%N)
  (HPb : forall n, P n -> (anch + stride * N.of_nat n < bv.exp2 xlenbits)%N) :
  loop_latch_obligation ls iota q P.
Proof.
  assert (Hsb : (stride <= bv.exp2 xlenbits)%N) by lia.
  refine (loop_latch_ptr ls iota q P e (loop_ctr_up anch stride)
            (fun n => (anch + stride * N.of_nat n)%N) anch
            HP0 Hg Hxg Hk He _ _ _ _ _).
  - (* the latch's own step: a wrap-around decrement *)
    intros n HP. rewrite Himm.
    replace (loop_ctr_up anch stride n)
      with ((anch + stride * N.of_nat n) + stride)%N
      by (unfold loop_ctr_up; lia).
    apply bv_of_N_wrap_dec. exact Hsb.
  - (* the post-step counter fits *) intros n HP. exact (HPb n HP).
  - (* the limit fits -- from HPb at trip 0, not a separate premise *)
    pose proof (HPb 0%nat HP0). cbn [N.of_nat] in *. lia.
  - (* MISSES the limit while trips remain: `0 < stride` earns its place *)
    intros n HP. pose proof (HPb (S n) HP). cbn [N.of_nat] in *. lia.
  - (* HITS it at trip 0 *) cbn [N.of_nat]. lia.
Qed.

(* THE COUNTER-VS-BOUND FAMILY (A, divrem).  The limit is a literal, so there
   is no `He`; in exchange the step is a WRAP-AROUND decrement, which is why
   `Himm` is stated against `bv.exp2 xlenbits - stride` rather than against a
   negative number that `Val ty_xlenbits` cannot hold. *)
Lemma loop_latch_ctr_affine_up {R : LCtx} (ls : LoopSpec R)
  (iota : nat -> Valuation R) (q : bv xlenbits) (P : nat -> Prop)
  (b stride : N)
  (HP0 : P 0)
  (Hg  : loop_guard ls = fun t => formula_relop bop.bvult
                                 (term_val ty_xlenbits (@bv.of_N xlenbits b)) t)
  (Hxg : loop_exit_guard ls = fun t => formula_relop bop.bvule t
                                 (term_val ty_xlenbits (@bv.of_N xlenbits b)))
  (Himm : loop_counter_step ls
          = @bv.of_N xlenbits (bv.exp2 xlenbits - stride))
  (Hk : forall n, P n ->
          inst (T := fun Σ => Term Σ ty_xlenbits) (loop_counter_pre ls)
            ((iota n).["a"∷ty_xlenbits ↦ ty.SyncVal q])
          = ty.SyncVal (@bv.of_N xlenbits (loop_ctr_up b stride n)))
  (* `< bv.exp2 xlenbits` here but not in the pointer family: that is the
     wrap-around encoding's doing, not an oversight.  `Himm` writes the
     decrement as `2^32 - stride`, which only denotes a decrement while the
     stride fits in a word. *)
  (Hs : (0 < stride < bv.exp2 xlenbits)%N)
  (Hb : (b < bv.exp2 xlenbits)%N)
  (HPb : forall n, P n -> (b + stride * N.of_nat n < bv.exp2 xlenbits)%N) :
  loop_latch_obligation ls iota q P.
Proof.
  assert (Hsb : (stride <= bv.exp2 xlenbits)%N) by lia.
  refine (loop_latch_ctr ls iota q P b (loop_ctr_up b stride)
            (fun n => (b + stride * N.of_nat n)%N)
            HP0 Hg Hxg Hk _ Hb _ _ _).
  - (* the wrap-around decrement *)
    intros n HP. rewrite Himm.
    replace (loop_ctr_up b stride n) with ((b + stride * N.of_nat n) + stride)%N
      by (unfold loop_ctr_up; lia).
    apply bv_of_N_wrap_dec. exact Hsb.
  - (* the post-step counter fits *) intros n HP. exact (HPb n HP).
  - (* still ABOVE the bound while trips remain: `0 < stride` again *)
    intros n HP. cbn [N.of_nat] in *. lia.
  - (* AT the bound at trip 0 *) cbn [N.of_nat]. lia.
Qed.


(* ---- C3: THE TRIP PREDICATE ---------------------------------------------

   `P` separates "still looping" from "done", and every loop's is the same
   shape: one no-wrap bound per MOVING variable, and a cap on how many trips
   the loop was entered with.  Three were written by hand (mulinner, subword,
   divrem), each with its own `_mono` proved by hand, each re-deriving the
   same `+2`.

   WHY `+2` AND NOT THE LATCH'S `+1`.  The latch only ever reads trip `n`, so
   `loop_latch_*_affine` asks for the bound at `n+1`.  The BACK EDGE reads trip
   `S n` -- it has to know what the previous trip left -- so `P` must cover one
   trip more than the latch needs.  That off-by-one between the two consumers
   is invisible in a goal and fails late, which is why it lives here once
   rather than in each loop.

   `P` is a HYPOTHESIS the caller establishes, so every clause added here makes
   the loop's theorem WEAKER.  Hence the trip cap is `option`: divrem genuinely
   has none, and giving it one to make the shape uniform would have silently
   strengthened its premise.

   EVERYTHING REDUCES UNDER ONE `cbn`.  That is a design constraint, not an
   accident: a call site used to say `unfold X_trip_bound` and then read the
   conjunction off.  An earlier draft here made the cap a `nat -> Prop`
   parameter, which `cbn` will not unfold (its body is a lambda, not a match),
   so every site needed an extra `unfold` -- turning C3 into a NET LOSS in
   lines.  `trip_tail`'s match on `option` reduces, so one
   `cbn [loop_trip_bound List.fold_right trip_axis_bound trip_tail]` is the
   whole incantation, and `_mono` needs no side premise about the cap. *)
Variant trip_axis : Type :=
| TripDown (anchor stride : N)   (* value SHRINKS as trips remain: must not underflow *)
| TripUp   (anchor stride : N).  (* value GROWS as trips remain: must not overflow    *)

Definition trip_axis_bound (ax : trip_axis) (n : nat) : Prop :=
  match ax with
  | TripDown a s => (s * (N.of_nat n + 2) <= a)%N
  | TripUp   a s => (a + s * (N.of_nat n + 2) < bv.exp2 xlenbits)%N
  end.

Definition trip_tail (tot : option nat) (n : nat) : Prop :=
  match tot with Some t => Nat.le n t | None => True end.

(* RIGHT fold, so the result is the same RIGHT-NESTED conjunction the
   hand-written predicates were: a loop's existing `intros (H1 & H2 & H3)` and
   `repeat split; lia` keep working verbatim. *)
Definition loop_trip_bound (axes : list trip_axis) (tot : option nat)
    (n : nat) : Prop :=
  List.fold_right (fun ax acc => trip_axis_bound ax n /\ acc)
    (trip_tail tot n) axes.

(* `P_mono` for every loop at once. *)
Lemma loop_trip_bound_mono (axes : list trip_axis) (tot : option nat) (n : nat) :
  loop_trip_bound axes tot (S n) -> loop_trip_bound axes tot n.
Proof.
  unfold loop_trip_bound. induction axes as [|ax axes IH]; cbn.
  - destruct tot; cbn; [lia | exact (fun _ => I)].
  - intros [Hax Hrest]. split; [| exact (IH Hrest)].
    destruct ax; cbn in *; lia.
Qed.

(* WHAT `P` HANDS THE LATCH: the `+2`-to-`+1` weakening, written once.  Stated
   as lemmas rather than folded into a tactic so a call site can `exact` them. *)
Lemma trip_axis_down_latch (a s : N) (n : nat) :
  trip_axis_bound (TripDown a s) n -> (s * (N.of_nat n + 1) <= a)%N.
Proof. cbn. lia. Qed.

Lemma trip_axis_up_latch (a s : N) (n : nat) :
  trip_axis_bound (TripUp a s) n -> (a + s * N.of_nat n < bv.exp2 xlenbits)%N.
Proof. cbn. lia. Qed.

(* One address-space bound, from N-level facts: the caller says what the term
   evaluates to and that it fits, and never touches `bv.bin`.  Every loop's
   `gen_loop_bounds` is a list of these (see `gen_loop_bounds_intro`). *)
Lemma loop_bound_le {Σ : LCtx} (T : Term Σ ty_xlenbits) (ι : Valuation Σ)
  (x off : N)
  (HT : inst (T := fun Σ => Term Σ ty_xlenbits) T ι
        = ty.SyncVal (@bv.of_N xlenbits x))
  (Hx : (x < bv.exp2 xlenbits)%N) (H : (x + off <= lenAddr)%N) :
  instprop (formula_relop bop.le
      (term_binop bop.plus (term_unop uop.unsigned T) (term_val ty.int (Z.of_N off)))
      (term_val ty.int (Z.of_N lenAddr))) ι.
Proof.
  cbn. rewrite HT. cbn. unfold bv.unsigned.
  rewrite (bv.bin_of_N_small Hx). lia.
Qed.

(* Two facts every loop-frame proof needs, so that none of them re-derives
   them: a disequality of addresses from a disequality of N, and the fact
   that the address space fits in a word. *)
Lemma bv_of_N_neq (x y : N)
  (Hx : (x < bv.exp2 xlenbits)%N) (Hy : (y < bv.exp2 xlenbits)%N) (H : x <> y) :
  @bv.of_N xlenbits x <> @bv.of_N xlenbits y.
Proof.
  intros Hc. apply (f_equal (@bv.bin xlenbits)) in Hc.
  rewrite (bv.bin_of_N_small Hx) in Hc.
  rewrite (bv.bin_of_N_small Hy) in Hc. contradiction.
Qed.

Lemma lenAddr_lt_exp2 : (lenAddr < bv.exp2 xlenbits)%N.
Proof. vm_compute. reflexivity. Qed.

(* NO tactic for the bounds block.  `loop_bound_le` above already IS the
   lemma; the only thing a tactic added was INFERRING the per-base value from
   the goal, and `refine` does that:

     repeat constructor;
     all: refine (loop_bound_le _ _ _ _ _ _ _); [cbn; reflexivity | lia | lia].

   `reflexivity` unifies the value evar against the valuation, so nothing has
   to be written out per base, and the reasoning stays in the lemma where it
   can be read and reused. *)

(* ========================================================================== *)
(* 5. THE EXTRA, AS DATA                                                       *)
(* ========================================================================== *)

(* §4 said a Sigma-generic memory builder was NOT worth building, because the
   base has to be weakened under `asn.exist` and the only weakening to hand is
   `subst _ sub_wk1` -- a recorded Theta(|Sigma|^2) driver, and opaque to
   `iFrame`.  That is true of a builder that takes TERMS.  A builder that takes
   a variable's NAME together with its In-proof does not weaken anything: it
   re-derives the variable at the wider context with `ctx.in_succ`, which is
   structural, transparent, and CONVERTIBLE with what the hand-written
   assertion produces.  Measured 2026-09-12: a hand-written extra and the
   built one are equal by `reflexivity`.

   So the loop's `ls_extra_*` can be DATA, and the step across the back edge
   becomes one lemma (`loop_extra_transfer`, GenCompose) instead of the same
   `iSplit` walk written once per loop. *)

(* A register holding an ADDRESS: which register, which Sigma-variable holds
   its value at the loop head, what the BODY adds to it over one trip (zero
   for a register the loop does not move), and whether it is public. *)
Record walk_reg (Σ : LCtx) : Type := MkWalkReg
  { walk_register : RegIdx
  ; walk_var : string
  ; walk_var_in  : (walk_var∷ty_xlenbits ∈ Σ)%katamaran
  ; walk_step : Val ty_xlenbits
  ; walk_is_public : bool }.
Arguments MkWalkReg {Σ} walk_register walk_var {walk_var_in} walk_step walk_is_public.
Arguments walk_register {Σ}. Arguments walk_var {Σ}. Arguments walk_var_in {Σ}.
Arguments walk_step {Σ}. Arguments walk_is_public {Σ}.

(* A memory cell: the binder for its value, the Sigma-variable holding its
   base address, a constant offset from that base, and whether the VALUE is
   public (a walking pointer's target usually is not). *)
Record cell_spec (Σ : LCtx) : Type := MkCellSpec
  { cell_binder : string
  ; cell_base_var  : string
  ; cell_base_in   : (cell_base_var∷ty_xlenbits ∈ Σ)%katamaran
  ; cell_offset  : Val ty_xlenbits
  ; cell_is_public  : bool }.
Arguments MkCellSpec {Σ} cell_binder cell_base_var {cell_base_in} cell_offset cell_is_public.
Arguments cell_binder {Σ}. Arguments cell_base_var {Σ}. Arguments cell_base_in {Σ}.
Arguments cell_offset {Σ}. Arguments cell_is_public {Σ}.

(* `t + off`, except that a ZERO offset must produce the bare term: the
   contract has to match the term the executor builds, and a register the loop
   does not move is written `r |-> term_var v`, not `r |-> v + 0`. *)
Definition addr_off {Σ : LCtx} (t : Term Σ ty_xlenbits) (off : Val ty_xlenbits)
    : Term Σ ty_xlenbits :=
  if bv.eqb off bv.zero then t
  else term_binop bop.bvadd t (term_val ty_xlenbits off).

(* the walk registers at the loop head ("a") and after one trip ("an"): same
   list, and the only difference is that the "an" side has advanced. *)
Definition gen_walk_pre {Σ : LCtx} (ws : list (walk_reg Σ))
    : Assertion (Σ ▻ "a"∷ty_xlenbits) :=
  List.fold_right
    (fun w acc =>
       let t := @term_var _ (walk_var w) _ (ctx.in_succ (walk_var_in w)) in
       (walk_register w ↦ᵣ t
        ∗ (if walk_is_public w then asn.formula (formula_secLeak t) ∗ acc else acc))%asn)
    ⊤%asn ws.

Definition gen_walk_post {Σ : LCtx} (ws : list (walk_reg Σ))
    : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  List.fold_right
    (fun w acc =>
       let t := @term_var _ (walk_var w) _ (ctx.in_succ (ctx.in_succ (walk_var_in w))) in
       (walk_register w ↦ᵣ addr_off t (walk_step w)
        ∗ (if walk_is_public w then asn.formula (formula_secLeak t) ∗ acc else acc))%asn)
    ⊤%asn ws.

(* the cells.  Written twice for the same reason every Term is: the two
   contexts differ.  The BINDER's variable is always the head one, hence
   ctx.in_zero; the base needs one more in_succ than the enclosing context. *)
Definition gen_cells_pre {Σ : LCtx} (cs : list (cell_spec Σ))
    : Assertion (Σ ▻ "a"∷ty_xlenbits) :=
  List.fold_right
    (fun c acc =>
       (asn.exist (cell_binder c) ty_xlenbits
          (let a := addr_off (@term_var _ (cell_base_var c) _
                                (ctx.in_succ (ctx.in_succ (cell_base_in c)))) (cell_offset c) in
           let v := @term_var _ (cell_binder c) _ ctx.in_zero in
           if cell_is_public c then (a ↦ₘ v ∗ asn.formula (formula_secLeak v))%asn
           else (a ↦ₘ v)%asn)
        ∗ acc)%asn)
    ⊤%asn cs.

Definition gen_cells_post {Σ : LCtx} (cs : list (cell_spec Σ))
    : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  List.fold_right
    (fun c acc =>
       (asn.exist (cell_binder c) ty_xlenbits
          (let a := addr_off (@term_var _ (cell_base_var c) _
                                (ctx.in_succ (ctx.in_succ (ctx.in_succ (cell_base_in c)))))
                     (cell_offset c) in
           let v := @term_var _ (cell_binder c) _ ctx.in_zero in
           if cell_is_public c then (a ↦ₘ v ∗ asn.formula (formula_secLeak v))%asn
           else (a ↦ₘ v)%asn)
        ∗ acc)%asn)
    ⊤%asn cs.

(* the pure facts the PRECONDITION carries and the postcondition drops --
   disjointness of two pointers, a lower bound on one, and so on. *)
Definition gen_pures {Σ : LCtx} (fs : list (Formula (Σ ▻ "a"∷ty_xlenbits)))
    (tail : Assertion (Σ ▻ "a"∷ty_xlenbits)) : Assertion (Σ ▻ "a"∷ty_xlenbits) :=
  List.fold_right (fun f acc => (asn.formula f ∗ acc)%asn) tail fs.

(* THE THREE PARTS STAY SEPARATE CONJUNCTS.  Threading a tail through the
   folds instead would interleave the reservoir with the walk in every proof;
   keeping them apart is what lets the step across the back edge be the
   composition of three independent lemmas (GenCompose: gen_walk_step,
   gen_pures_interp, and the caller's cell trade). *)
Definition gen_extra_pre {Σ : LCtx} (ws : list (walk_reg Σ))
    (fs : list (Formula (Σ ▻ "a"∷ty_xlenbits))) (cs : list (cell_spec Σ))
    : Assertion (Σ ▻ "a"∷ty_xlenbits) :=
  (gen_walk_pre ws ∗ gen_pures fs (gen_cells_pre cs))%asn.

Definition gen_extra_post {Σ : LCtx} (ws : list (walk_reg Σ))
    (cs : list (cell_spec Σ))
    : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) :=
  (gen_walk_post ws ∗ gen_cells_post cs)%asn.
