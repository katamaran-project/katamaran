(******************************************************************************)
(* Copyright (c) 2019 Steven Keuchel                                          *)
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

From Coq Require Import Bool.Bool PeanoNat.
From Equations Require Import Equations.
From stdpp Require base decidable finite list.
From Katamaran Require Import Context Environment Prelude.

(* Extract the head of a term.
   from http://poleiro.info/posts/2018-10-15-checking-for-constructors.html
 *)
Ltac head t :=
  match t with
  | ?t' _ => head t'
  | _ => t
  end.

Ltac solve_eqb_spec' tac :=
  repeat
    (intros; cbn in *;
     match goal with
     | H: ?x <> ?x |- _ => congruence
     | |- _ <> _ => intro
     | |- ?x = ?x => reflexivity
     | |- reflect _ true => constructor
     | |- reflect _ false => constructor
     | H: ?x = ?y |- _ =>
       let hx := head x in
       let hy := head y in
       is_constructor hx; is_constructor hy;
       dependent elimination H
     | |- context[eq_dec ?x ?y] => destruct (eq_dec x y); subst
     | |- context[eq_dec_het ?x ?y] => destruct (eq_dec_het x y); subst
     | H : forall y, reflect _ (?eq ?x y) |- context[?eq ?x ?y] =>
       destruct (H y)
     | H : forall x y, reflect _ (?eq x y) |- context[?eq ?x ?y] =>
       destruct (H x y)
     | [ H : reflect _ ?b |- context[?b] ] =>
       let H1 := fresh in destruct H as [H1 |]; [dependent elimination H1 | idtac]
     | e : ?x = ?y |- context[eq_rect ?x _ _ ?y ?e] => destruct e; cbn
     | p: @ctx.nth_is ?B ?Γ ?n ?b, q: @ctx.nth_is ?B ?Γ ?n ?b |- _ =>
         pose proof (@ctx.proof_irrelevance_nth_is B _ Γ n b p q); subst
     | |- context[ctx.In_eqb ?x ?y] => destruct (ctx.In_eqb_spec x y); subst
     | |- context[Nat.eqb ?x ?y] => destruct (Nat.eqb_spec x y); subst
     | |- _ => tac; subst; cbn
     end;
     rewrite ?andb_true_r, ?andb_false_r);
  cbn in *;
  try congruence.

Ltac solve_eqb_spec := solve_eqb_spec' idtac.

Tactic Notation "solve_eqb_spec" "with" tactic(tac) :=
  solve_eqb_spec' tac.

Ltac finite_from_eqdec :=
  match goal with
  | |- base.NoDup ?xs =>
      now apply (@decidable.bool_decide_unpack _ (list.NoDup_dec xs))
  | |- forall x : ?T, base.elem_of x _ =>
      lazymatch T with
      | sigT _ => intros [? []]
      | _      => intros []
      end;
      apply (@decidable.bool_decide_unpack _ (list.elem_of_list_dec _ _));
      auto
  end.

Ltac destruct_propositional H :=
  lazymatch type of H with
  | _ /\ _ =>
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    destruct H as [H1 H2];
    destruct_propositional H1;
    destruct_propositional H2
  | _ \/ _ =>
    destruct H as [H|H];
    destruct_propositional H
  | exists _, _ =>
    let x := fresh in
    destruct H as [x H];
    destruct_propositional H
  | _ => idtac
  end.

(* Adopted from
   https://softwarefoundations.cis.upenn.edu/plf-current/LibTactics.html
 *)
Ltac check_noevar M :=
  first [ has_evar M; fail 1 | idtac ].
Ltac check_noevar_hyp H :=
  let T := type of H in check_noevar T.

(* This tactic instantiates a hypothesis with fresh unification variables,
   possibly solving some on the fly.
   Adopted from CPDT: http://adam.chlipala.net/cpdt/html/Match.html
 *)
Ltac inster_gen H tac :=
  match type of H with
  | forall x : ?T, _ =>
    match type of T with
    | Prop =>
      (let H' := fresh "H'" in
       assert (H' : T) by solve [ tac ];
       specialize (H H'); clear H';
       first [ check_noevar_hyp H | inster_gen H tac ])
      || fail 1
    | _ =>
      let x := fresh "x" in
      evar (x : T);
      let x' := eval unfold x in x in
          clear x; specialize (H x');
      first [ check_noevar_hyp H | inster_gen H tac ]
    end
  end.

Ltac inster_loop H tac :=
  repeat
    (inster_gen H tac;
     check_noevar_hyp H).

Tactic Notation "inster" constr(H) "by" tactic(tac) :=
  inster_loop H tac.
