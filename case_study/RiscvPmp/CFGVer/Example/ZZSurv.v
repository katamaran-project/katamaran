(* ========================================================================= *)
(* ZZSurv.v — THROWAWAY diagnostic probe (delete after use).                  *)
(*                                                                           *)
(* ZZNames.v dumps the two multisets (demonicv introductions, assume_vareq    *)
(* eliminations) but leaves the diff to be done by eye, and the dump is large *)
(* enough to be truncated by the tooling.  This computes the DIFFERENCE — the *)
(* names that are introduced demonically and never eliminated, i.e. the ones  *)
(* that keep |wctx| growing — and reports them directly.                     *)
(*                                                                           *)
(* Reading the result: a name that appears once per INSTRUCTION STEP is a     *)
(* per-step leak (14 per trip in this reproducer); a name appearing a fixed   *)
(* number of times regardless of n is contract-entry noise and harmless.      *)
(* Fresh-name suffixes (.1, .2, ...) are themselves the tell: a survivor must *)
(* be alpha-renamed when the next step introduces the same base name, so      *)
(* suffix accumulation marks exactly the variables that never die.           *)
(* ========================================================================= *)

(* ZZCommon first (it Exports Prelude, which is where LVar and the list/string
   notations come from); ZZNames only Imports it, so its scope does not reach
   here transitively — the Require-vs-Require-Import landmine in CFGVer/CLAUDE.md. *)
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZCommon.
From Katamaran Require Import RiscvPmp.CFGVer.Example.ZZNames.

(* Remove ONE occurrence of y (multiset semantics, not set semantics: the
   same base name is introduced once per step and eliminated once per step,
   so set difference would wrongly report it as fully eliminated). *)
Fixpoint zz_mremove (y : LVar) (xs : list LVar) : list LVar :=
  match xs with
  | nil        => nil
  | cons x xs' => if String.eqb x y then xs' else cons x (zz_mremove y xs')
  end.

Fixpoint zz_mdiff (xs ys : list LVar) : list LVar :=
  match ys with
  | nil        => xs
  | cons y ys' => zz_mdiff (zz_mremove y xs) ys'
  end.

Definition zz_surv (n : nat) : list LVar := zz_mdiff (zz_dn n) (zz_en n).

Goal True. idtac "ZZ ===== SURVIVOR COUNTS (N=1, N=2) =====". exact I. Qed.
Eval vm_compute in (List.length (zz_surv 1), List.length (zz_surv 2)).

Goal True. idtac "ZZ ===== SURVIVOR NAMES (N=1) =====". exact I. Qed.
Eval vm_compute in (zz_surv 1).

Goal True. idtac "ZZ ===== SURVIVOR NAMES (N=2) =====". exact I. Qed.
Eval vm_compute in (zz_surv 2).
