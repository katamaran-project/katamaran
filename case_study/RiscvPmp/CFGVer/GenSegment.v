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
    (prog : list AST) (skip take : nat)
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
    post.

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
