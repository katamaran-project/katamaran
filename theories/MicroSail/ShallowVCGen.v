(******************************************************************************)
(* Copyright (c) 2020 Dominique Devriese, Georgy Lukyanov,                    *)
(*   Sander Huyghebaert, Steven Keuchel                                       *)
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

From Coq Require Import
     Arith.PeanoNat
     Bool.Bool
     Classes.Morphisms
     Classes.Morphisms_Prop
     Classes.Morphisms_Relations
     Classes.RelationClasses
     Relations.Relation_Definitions
     Lists.List
     NArith.NArith
     Program.Tactics
     Strings.String
     ZArith.BinInt.
From Coq Require
     Classes.CRelationClasses.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Prelude
     Bitvector
     Signature
     MicroSail.ShallowExecutor
     Shallow.MonadInstances
     Shallow.MonadInterface
     Shallow.Replay
     Specification
     Base.

From stdpp Require
     base.

Import ctx.notations.
Import env.notations.
Import ListNotations.

Module Type ShallowVCGenOn
  (Import B : Base)
  (Import SIG : Signature B)
  (Import PROG : Program B)
  (Import SPEC : Specification B SIG PROG)
  (Import EXEC : ShallowExecOn B SIG PROG)
  (Import MINST : ShallowMonadInstancesOn B SIG).

  Definition exec_call_foreign : @ExecCallForeign CHeapSpec :=
    fun Δ τ f args =>
      ccall_contract (CEnvEx f) args.

  #[export] Instance mon_exec_call_foreign :
    MonotonicExecCallForeign exec_call_foreign.
  Proof. intros Δ τ f args. apply mon_call_contract. Qed.

  Definition exec_lemma : @ExecLemma CHeapSpec :=
    fun Δ l args =>
      ccall_lemma (LEnv l) args.

  #[export] Instance mon_exec_lemma :
    MonotonicExecLemma exec_lemma.
  Proof. intros Δ l args. apply mon_call_lemma. Qed.

  Fixpoint exec_call (inline_fuel : nat) : ExecCall CHeapSpec :=
    fun Δ τ f args =>
      (* Let's first see if we have a contract defined for function [f]
           and then if we have enough fuel for inlining. *)
      match CEnv f , inline_fuel with
      | Some c , _ =>
          (* YES: Execute the call by interpreting the contract. *)
          ccall_contract c args
      | None   , 0 =>
          (* Out of fuel *)
          exec_call_error (M:=CHeapSpec) f args
      | None   , S n =>
          evalCStoreT
            (exec_aux exec_call_foreign exec_lemma (exec_call n) (FunDef f))
            args
      end.

  #[export] Instance rexec_call n :
    MonotonicExecCall (exec_call n).
  Proof.
    induction n; intros Δ τ f args;
      cbn - [CPureSpecM.bind evalCStoreT];
      destruct (CEnv f); try typeclasses eauto.
    - apply CHeapSpec.mon_lift_purespec'.
      apply CPureSpec.mon_error.
    - apply mon_evalCStoreT.
      change (?R ?m ?m) with (Monotonic R m).
      apply mon_exec_aux; typeclasses eauto.
  Qed.

  Section WithFuel.

    Variable inline_fuel : nat.

    Definition exec : Exec CHeapSpec :=
      exec_aux exec_call_foreign exec_lemma (exec_call inline_fuel).

    #[export] Instance rexec : MonotonicExec exec.
    Proof. typeclasses eauto. Qed.

    Definition shallow_vcgen [Δ τ] (c : SepContract Δ τ) (s : Stm Δ τ) : Prop :=
      CHeapSpec.run (exec_contract exec c s).

  End WithFuel.

  Module Shallow.
    Definition ValidContractWithFuel (fuel : nat) :
      forall [Δ τ], SepContract Δ τ -> Stm Δ τ -> Prop :=
      shallow_vcgen fuel.

    Definition ValidContract :
      forall [Δ τ], SepContract Δ τ -> Stm Δ τ -> Prop :=
      (* Use inline_fuel = 1 by default. *)
      ValidContractWithFuel 1.

    Ltac calcstats fnc :=
      let P := eval compute - [FALSE TRUE FINISH
                                 negb Z.mul Z.opp Z.compare Z.add Z.geb Z.eqb
                                 Z.leb Z.gtb Z.ltb Z.le Z.lt Z.gt Z.ge Z.of_nat
                                 List.app List.length rev rev_append
          ] in
      (match CEnv fnc with
       | Some c => Shallow.ValidContract c (FunDef fnc)
       | None => False
       end) in
        let s := eval compute in (Statistics.stats P) in s.

  End Shallow.

End ShallowVCGenOn.

Module Type ShallowVCGen (B : Base) (SIG : Signature B) (PROG : Program B)
  (SPEC : Specification B SIG PROG).
  Include ShallowMonadInstancesOn B SIG.
  Include ShallowExecOn B SIG PROG.
  Include ShallowVCGenOn B SIG PROG SPEC.
End ShallowVCGen.

Module MakeShallowVCGen (B : Base) (SIG : Signature B) (PROG : Program B)
  (SPEC : Specification B SIG PROG) <: ShallowVCGen B SIG PROG SPEC.
  Include ShallowMonadInstancesOn B SIG.
  Include ShallowExecOn B SIG PROG.
  Include ShallowVCGenOn B SIG PROG SPEC.
End MakeShallowVCGen.
