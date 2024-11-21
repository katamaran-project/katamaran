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
     MicroSail.SymbolicExecutor
     Program
     Specification
     Base.

From stdpp Require
     base.

Import ctx.notations.
Import env.notations.
Import ListNotations.

Set Implicit Arguments.

Module Type SymbolicVCGenOn
  (Import B : Base)
  (Import SIG : Signature B)
  (Import PROG : Program B)
  (Import SPEC : Specification B SIG PROG)
  (Import SYMB : SymbolicExecOn B SIG PROG).

  Import SymProp Postprocessing.

  Section VerificationConditions.

    Inductive VerificationCondition (p : 𝕊 ctx.nil) : Prop :=
    | vc (P : safe p env.nil).

    Lemma vc_debug (p : 𝕊 ctx.nil) (H : safe_debug p env.nil) : VerificationCondition p.
    Proof.
      constructor; now rewrite safe_debug_safe in H.
    Qed.

    #[export] Instance proper_vc : Proper (sequiv ctx.nil ==> iff) VerificationCondition.
    Proof. intros p q pq. split; intros []; constructor; now apply pq. Qed.

    Inductive VerificationConditionWithErasure (p : Erasure.ESymProp) : Prop :=
    | vce (P : Erasure.inst_symprop nil p).

  End VerificationConditions.

  Module Symbolic.

    Import ModalNotations.

    Definition ok {Σ} (p : 𝕊 Σ) : bool :=
      match prune p with
      | SymProp.block => true
      | _           => false
      end.

    Lemma ok_sound {Σ} (p : 𝕊 Σ) (ι : Valuation Σ) :
      is_true (ok p) -> safe p ι.
    Proof.
      rewrite <- prune_sound. unfold ok.
      generalize (prune p) as q. clear. intros q.
      destruct q; try discriminate; cbn; auto.
    Qed.

    Definition exec_call_foreign : ExecCallForeign :=
      fun Δ τ f w args =>
        SHeapSpec.scall_contract (CEnvEx f) args.

    Definition exec_lemma : ExecLemma :=
      fun Δ l w args =>
        SHeapSpec.scall_lemma (LEnv l) args.

    Fixpoint exec_call (inline_fuel : nat) : ExecCall :=
      fun Δ τ f w args =>
        (* Let's first see if we have a contract defined for function [f]. *)
        match CEnv f , inline_fuel with
        | Some c , _ =>
            (* Execute the call by interpreting the contract. *)
            SHeapSpec.scall_contract c args
        | None  , O =>
            exec_call_error f args
        | None  , S n =>
            evalStoreSpec
              (exec_aux exec_call_foreign exec_lemma (exec_call n) (FunDef f) (w:=_))
              args
        end.

    Definition runreplay : ⊢ 𝕊 -> 𝕊 :=
      fun w P => SPureSpec.run (sreplay P (sub_id w)).

    Section WithFuel.

      Variable inline_fuel : nat.

      Definition exec : Exec :=
        exec_aux exec_call_foreign exec_lemma (exec_call inline_fuel).

      Definition vcgen {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) : ⊢ 𝕊 :=
        fun w => SHeapSpec.run (exec_contract exec c s (w:=w)).

      Definition vcgenpp {Δ τ} (c : SepContract Δ τ) (s : Stm Δ τ) : ⊢ 𝕊 :=
        fun w => postprocess (runreplay (postprocess (vcgen c s w))).

      Definition ValidContractWithFuel {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
        VerificationCondition (vcgenpp c body wnil).

      Definition ValidContractReflectWithFuel {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
        is_true (ok (vcgenpp c body wnil)).

      Lemma validcontract_reflect_fuel_sound {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
        ValidContractReflectWithFuel c body ->
        ValidContractWithFuel c body.
      Proof.
        unfold ValidContractReflectWithFuel, ValidContractWithFuel. intros Hok.
        apply (ok_sound _ env.nil) in Hok. now constructor.
      Qed.

    End WithFuel.

    Definition ValidContract {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      (* Use inline_fuel = 1 by default. *)
      ValidContractWithFuel 1 c body.

    Definition ValidContractReflect {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      ValidContractReflectWithFuel 1 c body.

    Lemma validcontract_reflect_sound {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
      ValidContractReflect c body ->
      ValidContract c body.
    Proof.
      unfold ValidContract, ValidContractReflect.
      now apply validcontract_reflect_fuel_sound.
    Qed.

    Definition VcGenErasure {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Erasure.ESymProp :=
      Erasure.erase_symprop (vcgenpp 1 c body wnil).

    Definition ValidContractWithErasure {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      VerificationConditionWithErasure (VcGenErasure c body).

    Lemma verification_condition_with_erasure_sound (p : 𝕊 ctx.nil) :
      VerificationConditionWithErasure (Erasure.erase_symprop p) ->
      VerificationCondition p.
    Proof. intros [H]. constructor. now rewrite <- Erasure.erase_safe. Qed.

    Lemma validcontract_with_erasure_sound {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) :
      ValidContractWithErasure c body ->
      ValidContract c body.
    Proof. apply verification_condition_with_erasure_sound. Qed.

    Module Statistics.

      Import SymProp.Statistics.

      Definition extend_postcond_with_debug {Δ τ} (c : SepContract Δ τ) : SepContract Δ τ :=
        match c with
        | {| sep_contract_logic_variables := lvars;
             sep_contract_localstore      := store;
             sep_contract_precondition    := pre;
             sep_contract_result          := res;
             sep_contract_postcondition   := post;
          |} => {| sep_contract_logic_variables := lvars;
                   sep_contract_localstore      := store;
                   sep_contract_precondition    := pre;
                   sep_contract_result          := res;
                   sep_contract_postcondition   := asn.sep post asn.debug;
                |}
        end.

      Definition calc {Δ τ} (f : 𝑭 Δ τ) : option (Stats) :=
        match CEnv f with
        | Some contract =>
            let contract' := extend_postcond_with_debug contract in
            let body      := FunDef f in
            let vc        := vcgen 1 contract' body wnil in
            Some (count_to_stats (count_nodes vc empty))
        | None   => None
        end.

    End Statistics.

  End Symbolic.

End SymbolicVCGenOn.

Module Type SymbolicVCGen
  (Import B    : Base)
  (Import SIG  : Signature B)
  (Import PROG : Program B)
  (Import SPEC : Specification B SIG PROG).

  Include SymbolicExecOn B SIG PROG.
  Include SymbolicVCGenOn B SIG PROG SPEC.
End SymbolicVCGen.

Module MakeSymbolicVCGen (B : Base) (SIG : Signature B)
  (PROG : Program B) (SPEC : Specification B SIG PROG) <:
  SymbolicVCGen B SIG PROG SPEC.
  Include SymbolicExecOn B SIG PROG.
  Include SymbolicVCGenOn B SIG PROG SPEC.
End MakeSymbolicVCGen.
