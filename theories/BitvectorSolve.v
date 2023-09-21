(******************************************************************************)
(* Copyright (c) 2020 Aïna Linn Georges, Armaël Guéneau, Thomas Van Strydonck,*)
(* Amin Timany, Alix Trieu, Dominique Devriese, Lars Birkedal                 *)
(* Copyright (c) 2023 Steven Keuchel, Dominique Devriese, Sander Huyghebaert  *)
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
(* 3. Neither the name of the copyright holder nor the names of its           *)
(*    contributors may be used to endorse or promote products derived from    *)
(*    this software without specific prior written permission.                *)
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

From Katamaran Require Import
     Prelude
     BitvectorBase.
From iris.base_logic Require Import invariants lib.iprop lib.gen_heap.
From Coq Require Import
     Arith.PeanoNat.

Import bv (bv).
Import stdpp.tactics.
Import bv.notations.

(* TODO: replace explicit argument by typeclass instance? *)
Local Lemma bv_bin_one {n}: Nat.lt 0 n → bv.bin (@bv.one n) = 1%N.
Proof. unfold bv.bin, bv.one. destruct n; lia. Qed.
Local Lemma bv_bin_zero {n}: bv.bin (@bv.zero n) = 0%N.
Proof. by simpl. Qed.

(* Faster alternative to [set (H := v) in *] *)
(* https://github.com/coq/coq/issues/13788#issuecomment-767217670 *)
Ltac fast_set H v :=
  pose v as H; change v with H;
  repeat match goal with H' : context[v] |- _ => change v with H in H' end.

(* Replace term `v` with a fresh variable everywhere *)
(* Use this tactic once a spec for `v` has been introduced as a hypothesis *)
Ltac fast_set_fresh v :=
  let fx := fresh "fx" in
  fast_set fx v;
  clearbody fx.
(* Use this version if an equality of the form `v = trm` is already present in the context after applying a spec. *)
Ltac fast_set_fresh_subst v :=
  let fx := fresh "fx" in
  fast_set fx v;
  clearbody fx; subst fx.

Ltac solve_bv_cbn :=
  cbv [bv.ult bv.ule bv.ugt bv.uge bv.unsigned];
  cbn [bv.of_Z bv.of_N bv.of_nat]. (* Lemmas operate on these; don't always unfold *)

Ltac solve_bv_cbn_in_all :=
  cbv [bv.ult bv.ule bv.ugt bv.uge bv.unsigned] in *;
  cbn [bv.of_Z bv.of_N bv.of_nat] in *.

Ltac bv_zify_op_nonbranching_step :=
    lazymatch goal with
    (* Options *)
    | |- @eq (option (bv _)) (Some _) (Some _) =>
      f_equal
    | H : @eq (option (bv _)) (Some _) (Some _) |- _ =>
      apply some_inj in H
    | |- @eq (option (bv _)) (Some _) None =>
      exfalso
    | |- @eq (option (bv _)) None (Some _) =>
      exfalso
    | H : @eq (option (bv _)) (Some _) None |- _ =>
      discriminate H
    | H : @eq (option (bv _)) None (Some _) |- _ =>
      discriminate H
    (* Non-branching specs *)
    | |- context [ bv.bin (bv.one) ] =>
      rewrite bv_bin_one ; [ | cbn; lia] (* TODO create spec Ltac for these? Currently assumes n > 0 *)
    | H : context [ bv.bin (bv.one) ] |- _ =>
      rewrite bv_bin_one in H ; [ | cbn; lia]
    | |- context [ bv.bin (bv.zero) ] =>
      rewrite bv_bin_zero
    | H : context [ bv.bin (bv.zero) ] |- _ =>
      rewrite bv_bin_zero in H
    end.

Ltac bv_zify_nonbranching_step :=
  first [ progress solve_bv_cbn_in_all
        | bv_zify_op_nonbranching_step ].

Ltac rename_or_learn H HTy :=
    lazymatch goal with
    | H' : HTy |- _ => rename H' into H
    | _ => destruct (decide HTy) as [H|H] end.

(* TODO: we could provide a more precise spec in case of overflow; either `bin(x + y) = bin x + bin y`, or they are `2^n` off *)
Ltac bin_add_spec n x y :=
  let HTy := constr:((bv.bin x + bv.bin y < bv.exp2 n)%N) in
  (* Check if `HyT` has been assumed before? *)
  let H := fresh "H" in
  rename_or_learn H HTy;
  [generalize (bv.bin_add_small H); intros ?; fast_set_fresh_subst (bv.bin (bv.add x y)) |
    apply N.nlt_ge in H; fast_set_fresh (bv.bin (bv.add x y)) ..]. (* Note: second tactic is only run if we did not yet know `HTy`  *)

(* TODO: more precise spec using `mod` possible, but might make it harder for `lia` to discharge some goals *)
Ltac bin_of_nat_spec n x :=
  let HTy := constr:((N.of_nat x < bv.exp2 n)%N) in
  (* Check if `HyT` has been assumed before? *)
  let H := fresh "H" in
  rename_or_learn H HTy;
  [generalize (bv.bin_of_nat_small H); intros ?; fast_set_fresh_subst (@bv.bin n (bv.of_nat x)) |
  apply N.nlt_ge in H; fast_set_fresh (@bv.bin n (bv.of_nat x)) ..] (* Note: second tactic is only run if we did not yet know `HTy`  *).

Ltac bv_zify_op_branching_goal_step :=
  lazymatch goal with
  | |- context [ bv.bin (@bv.add ?n ?x ?y) ] =>
      bin_add_spec n x y
  | |- context [ bv.bin (@bv.of_nat ?n ?x) ] =>
      bin_of_nat_spec n x
  end.

Ltac bv_zify_op_branching_hyps_step :=
  lazymatch goal with
  | _ : context [ bv.bin (@bv.add ?n ?x ?y) ] |- _ =>
      bin_add_spec n x y
  | _ : context [ bv.bin (@bv.of_nat ?n ?x) ] |- _ =>
      bin_of_nat_spec n x
  end.

(* Getting rid of all mentions of bv's at the end, by introducing wf-constraints explicitly for lia *)
(* TODO: probably better to (also) generate this wf-spec earlier on -> This prevents duplication of goals along the way *)
Ltac bv_zify_ty_step_on f :=
  generalize (bv.bv_is_wf f); intros ?;
  fast_set_fresh (bv.bin f);
  first [ clear f | revert dependent f ].

Ltac bv_zify_ty_step_var :=
  lazymatch goal with
  | f : bv _ |- _ => bv_zify_ty_step_on f
  end.

Ltac bv_zify_ty_step_subterm :=
  match goal with
  | H : context [ ?x ] |- _ =>
    lazymatch type of x with bv _ =>
      let X := fresh in
      set (X := x) in *;
      bv_zify_ty_step_on X
    end
  end.

Ltac bv_zify_ty_step :=
  first [ bv_zify_ty_step_var | bv_zify_ty_step_subterm ].

(* Naive, greedy procedure that converts everything to Z without simplifying bitvectors *)
Ltac bv_zify_greedy :=
  intros; solve_bv_cbn;
  repeat (first [ bv_zify_nonbranching_step
                | bv_zify_op_branching_goal_step
                | bv_zify_op_branching_hyps_step ]);
  repeat bv_zify_ty_step; intros.

(* From a high-level perspective, [bv_zify] is equivalent to [bv_zify_greedy] followed by [lia].

However, this gets very slow when there are branching steps (anything that branches on small-ness) in the context (and some of those may not be relevant to prove the goal at hand), so the implementation is a bit more clever. Instead, we try to call [lia] as soon as possible to quickly terminate sub-goals than can be proved before the whole context gets translated. *)

Ltac bv_zify_op_goal_step :=
  first [ bv_zify_nonbranching_step
        | bv_zify_op_branching_goal_step ].

Ltac bv_zify_op_deepen :=
  bv_zify_op_branching_hyps_step;
  repeat bv_zify_nonbranching_step;
  try (
    bv_zify_op_branching_hyps_step;
    repeat bv_zify_nonbranching_step
  ).

Ltac bv_zify_close_proof :=
  repeat bv_zify_ty_step; intros;
  solve [ auto | lia | congruence ].

Ltac bv_zify :=
  intros; solve_bv_cbn;
  (* Branches on the goal are always forced: do all of these at once *)
  repeat bv_zify_op_goal_step;
  (* Are we done? *)
  try bv_zify_close_proof;
  (* Take <=2 branching steps at a time and try to finish the proof *)
  repeat (
    bv_zify_op_deepen;
    try bv_zify_close_proof
  );
  bv_zify_close_proof.

Tactic Notation "solve_bv" := bv_zify.
Tactic Notation "solve_bv" "-" hyp_list(Hs) := clear Hs; bv_zify.
Tactic Notation "solve_bv" "+" hyp_list(Hs) := clear -Hs; bv_zify.
