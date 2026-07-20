(* TEMP Phase-1 probe: accumulator fold, isolated cost measurement.
   Simulates the executor's per-round term growth WITHOUT peval or a
   framework recompile.  The fold is modelled with a REFLECTED
   accumulator (A-shift term + list of (Y_i, C_i) summands); stepping is
   trivial list ops (this is exactly what the peval recognizer does, with
   the Term<->AccState parse deferred).  Cost is measured via Term_eqb
   self-compare (= the blowup mechanism: processing walks by syntactic
   occurrence).  Throwaway. *)
From Coq Require Import ZArith.ZArith Lists.List Strings.String.
From Katamaran Require Import
     Notations Bitvector Semantics
     RiscvPmp.CFGVer.Spec RiscvPmp.Machine RiscvPmp.Sig.
From stdpp Require Import gmap.
From Katamaran Require Import
     RiscvPmp.CFGVer.Verifier RiscvPmp.CFGVer.Contracts.

Import RiscvPmpProgram.
Set Implicit Arguments.
Import ctx.resolution ctx.notations bv.notations env.notations ListNotations.
Import RiscvPmpCFGVerifExecutor.
Import RiscvPmp.Sig.
Import TermNotations.

Definition Sig : LCtx := [ctx] ▻ ("h" ∷ ty.bvec 32).
Notation TB := (ty.bvec 32).
Notation T := (Term Sig TB).

Definition h : T := term_var "h".

Definition v_ones : Val TB := bv.of_Z (-1).
Definition v_R    : Val TB := bv.of_N 0xE1000000.
Definition v_1    : Val TB := bv.of_N 1.
Definition v_0    : Val TB := bv.zero.
Definition v_31s  : Val (ty.bvec 5) := bv.of_N 31.
Definition v_1s   : Val (ty.bvec 5) := bv.of_N 1.

Definition tv (v : Val TB) : T := term_val TB v.
Definition shiftr1 (Y : T) : T := term_binop bop.shiftr Y (term_val (ty.bvec 5) v_1s).

(* mask chain applied to (Z & 1), exactly as peval emits it *)
Definition mask_chain_tm (Z : T) : T :=
  term_binop bop.bvand
    (term_binop bop.bvadd (tv v_ones)
       (term_binop bop.shiftr
          (term_binop bop.bvand
             (term_binop bop.bvadd (tv v_ones) (term_binop bop.bvand Z (tv v_1)))
             (term_binop bop.bvxor (term_binop bop.bvand Z (tv v_1)) (tv v_ones)))
          (term_val (ty.bvec 5) v_31s)))
    (tv v_R).

(* one raw masking round = mulx applied to Z (Z occurs 3x) *)
Definition raw_round_tm (Z : T) : T :=
  term_binop bop.bvxor (mask_chain_tm Z) (shiftr1 Z).

(* sel Y c = (0 - (Y&1)) & c *)
Definition sel_tm (Y : T) (c : Val TB) : T :=
  term_binop bop.bvand
    (term_binop bop.bvsub (tv v_0) (term_binop bop.bvand Y (tv v_1)))
    (tv c).

(* concrete mulx on values, for aging constants *)
Definition mulx_val (a : Val TB) : Val TB :=
  bv.lxor (bv.land (bv.sub bv.zero (bv.land a v_1)) v_R) (bv.shiftr a v_1s).

(* ---- reflected accumulator: A-shift term + (Y_i, C_i) summands ---- *)
Record Acc := MkAcc { ashift : T ; summands : list (T * Val TB) }.

Fixpoint denote_sums (sums : list (T * Val TB)) : option T :=
  match sums with
  | nil => None
  | cons (Y,C) rest =>
      match denote_sums rest with
      | None => Some (sel_tm Y C)
      | Some r => Some (term_binop bop.bvxor (sel_tm Y C) r)
      end
  end.

Definition denote (a : Acc) : T :=
  match denote_sums (summands a) with
  | None => ashift a
  | Some s => term_binop bop.bvxor (ashift a) s
  end.

(* one round on the reflected accumulator: O(1)+map (no term duplication) *)
Definition step_acc (a : Acc) : Acc :=
  MkAcc (shiftr1 (ashift a))
        (cons (ashift a, v_R) (map (fun p => (fst p, mulx_val (snd p))) (summands a))).

Definition a0 : Acc := MkAcc h nil.

(* folded value after n rounds *)
Definition Zf (n : nat) : T := denote (Nat.iter n step_acc a0).
(* unfolded value after n rounds (the executor's current behaviour) *)
Definition Zu (n : nat) : T := Nat.iter n raw_round_tm h.

(* sanity: the round shape matches peval's real output *)
Definition round_peval := Eval vm_compute in peval (raw_round_tm h).
Set Printing Depth 200.
Print round_peval.

(* sanity: fold fires + grows linearly *)
Definition Zf2 := Eval vm_compute in Zf 2.
Print Zf2.

(* ==================================================================== *)
(* Real term-level recognizer (the actual graft target for peval_binop).
   Every match below is SHALLOW (one constructor level), mirroring
   term_get_val's idiom -- this is what sidesteps the Equations
   "unused clause" wall the deep single-pattern attempt hit. The deep
   verification (does t1 really denote the mask chain of Z?) is
   offloaded to Term_eqb, a plain decidable-equality boolean function,
   never a dependent pattern match. *)

(* CRITICAL IDIOM, discovered the hard way in this file's history: every
   raw match on a `Term Σ σ` value must keep σ a GENUINE BOUND VARIABLE
   of the enclosing function (matching term_get_val's `{Σ σ}` and this
   codebase's own peval_bvand_bvapp_val's `{m1 m2}`), never a literal
   plugged in ahead of time (like our `T := Term Sig TB` alias). With σ
   fixed to a literal, any wildcard arm implicitly covers term_var --
   whose own type is an arbitrary Ty pulled from a membership proof --
   and Coq's match-compiler then builds one motive by case-splitting
   over EVERY Ty constructor (ty.int, ty.bvec 0, ty.bvec 1, ...) instead
   of reusing the shared variable trick, and a branch returning
   anything at the fixed literal type fails to unify with that
   generic motive. Keeping the width `n` abstract throughout (only
   instantiated to 32 at the outer call sites) sidesteps this
   completely -- this, not Equations vs plain match, was the actual
   fix for the wall hit earlier in this file's history. *)

From Equations Require Import Equations.

(* Equations (not vanilla match): the codebase's own analogues
   (peval_bvand_val, peval_bvdrop_eq) use Equations for exactly this
   shape -- a shallow, single-level Term pattern generic in the bitvector
   width. Equations' equation compiler builds the dependent elimination
   via unification/noConfusion rather than vanilla Gallina's naive
   "generalize the index" step, which is what got stuck (previous
   attempt in this file) once the index became a compound expression
   `ty.bvec n` instead of a bare variable. *)
Equations try_age_leaf {n} (age_const : Val (ty.bvec n) -> Val (ty.bvec n))
  (t : Term Sig (ty.bvec n)) : option (Term Sig (ty.bvec n)) :=
  try_age_leaf age_const (term_binop bop.bvand inner (term_val _ c)) :=
    Some (term_binop bop.bvand inner (term_val _ (age_const c))) ;
  try_age_leaf age_const _ := None.

Definition age_leaf {n} (age_const : Val (ty.bvec n) -> Val (ty.bvec n))
  (t : Term Sig (ty.bvec n)) : Term Sig (ty.bvec n) :=
  match try_age_leaf age_const t with
  | Some t' => t'
  | None => t
  end.

(* age a whole summand-list term: right-nested bvxor of sel-leaves.
   Shallow at each step: only asks "is the top constructor bvxor?". *)
Equations try_age_sum_step {n} (t : Term Sig (ty.bvec n))
  : option (Term Sig (ty.bvec n) * Term Sig (ty.bvec n)) :=
  try_age_sum_step (term_binop bop.bvxor a b) := Some (a, b) ;
  try_age_sum_step _ := None.

(* Equations, recursing DIRECTLY on the matched subterm b (not through
   try_age_sum_step's opaque call) -- a plain Fixpoint via the helper
   call couldn't see the structural decrease. *)
Equations age_sum {n} (age_const : Val (ty.bvec n) -> Val (ty.bvec n))
  (t : Term Sig (ty.bvec n)) : Term Sig (ty.bvec n) :=
  age_sum age_const (term_binop bop.bvxor a b) :=
    term_binop bop.bvxor (age_leaf age_const a) (age_sum age_const b) ;
  age_sum age_const t := age_leaf age_const t.

(* top-level recognizer for the bvxor case of peval_binop: t1 = mask
   value, t2 = shift value. Fires iff t2 = shiftr Z 1 AND t1 equals the
   mask chain of that same Z (verified via Term_eqb, not by pattern
   matching its 8-level internal structure).

   bop.shiftr is polymorphic in BOTH widths {m n} (BinOps.v:74), so the
   shift-amount's own width can't be pinned to a literal (5) inside an
   Equations pattern (Equations rejects a non-variable index there:
   "This pattern must be inaccessible"). Sidestep entirely by not caring
   about the width at all: bv.bin is width-generic, so comparing the
   raw N value (bv.bin vs =? 1) verifies "this is the constant 1" for
   ANY width the shift-amount happens to carry -- no dependent cast
   needed. *)
Equations try_match_shiftr1 {n} (t2 : Term Sig (ty.bvec n)) : option (Term Sig (ty.bvec n)) :=
  try_match_shiftr1 (term_binop bop.shiftr Z (term_val _ vs)) :=
    if N.eqb (bv.bin vs) 1 then Some Z else None ;
  try_match_shiftr1 _ := None.

Equations try_split_bvxor {n} (Z : Term Sig (ty.bvec n))
  : option (Term Sig (ty.bvec n) * Term Sig (ty.bvec n)) :=
  try_split_bvxor (term_binop bop.bvxor Y Ssum) := Some (Y, Ssum) ;
  try_split_bvxor _ := None.

Definition try_fold_round (t1 t2 : T) : option T :=
  match try_match_shiftr1 t2 with
  | None => None
  | Some Z =>
      if Term_eqb t1 (mask_chain_tm Z) then
        Some (match try_split_bvxor Z with
              | Some (Y, Ssum) =>
                  term_binop bop.bvxor (shiftr1 Y)
                    (term_binop bop.bvxor (sel_tm Y v_R) (age_sum mulx_val Ssum))
              | None =>
                  term_binop bop.bvxor (shiftr1 Z) (sel_tm Z v_R)
              end)
      else None
  end.

(* peval_bvxor as it would be added to peval_binop: try the fold first,
   fall back to plain term_bvxor otherwise. *)
Definition peval_bvxor_fold (t1 t2 : T) : T :=
  match try_fold_round t1 t2 with
  | Some r => r
  | None => term_binop bop.bvxor t1 t2
  end.

(* Real per-round step using the term-level recognizer (no Acc reflection). *)
Definition step_real (Z : T) : T := peval_bvxor_fold (mask_chain_tm Z) (shiftr1 Z).
Definition Zr (n : nat) : T := Nat.iter n step_real h.

(* Cross-check: term-level recognizer agrees with the Acc-simulation. *)
Definition check_Zr_1 := Eval vm_compute in Term_eqb (Zr 1) (Zf 1).
Definition check_Zr_2 := Eval vm_compute in Term_eqb (Zr 2) (Zf 2).
Definition check_Zr_5 := Eval vm_compute in Term_eqb (Zr 5) (Zf 5).
Print check_Zr_1.
Print check_Zr_2.
Print check_Zr_5.
