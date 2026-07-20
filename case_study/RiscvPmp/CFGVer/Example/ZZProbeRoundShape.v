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
