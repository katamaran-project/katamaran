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
     Shallow.MonadInterface
     Base.

From stdpp Require
     base.

Import ctx.notations.
Import env.notations.
Import ListNotations.
Import (hints) bv.finite.

Set Implicit Arguments.

Module Type ShallowReplayOn
  (Import B : Base)
  (Import SIG : Signature B).

  Import ModalNotations.
  Import Entailment.
  Import SymProp.
  Import CPureSpecM.
  Import CPureSpecM.notations.

  Section WithMonad.

    Context {M : Type -> Type} {pureM : CPureSpecM M} {heapM : CHeapSpecM M}.

    Definition creplay :
      forall {Σ} (s : 𝕊 Σ) (ι : Valuation Σ), M unit :=
      fix replay {Σ} s ι :=
        match s with
        | SymProp.angelic_binary o1 o2 =>
            angelic_binary (replay o1 ι) (replay o2 ι)
        | SymProp.demonic_binary o1 o2 =>
            demonic_binary (replay o1 ι) (replay o2 ι)
        | SymProp.block =>
            block
        | SymProp.error msg =>
            error
        | SymProp.assertk fml msg k =>
            bind (assert_formula (instprop fml ι))
              (fun _ => replay k ι)
        | SymProp.assumek fml k =>
            bind (assume_formula (instprop fml ι))
              (fun _ => replay k ι)
        | SymProp.angelicv b k =>
            bind (angelic _)
              (fun v => replay k (env.snoc ι b v))
        | SymProp.demonicv b k =>
            bind (demonic _)
              (fun v => replay k (env.snoc ι b v ))
        | @SymProp.assert_vareq _ x σ xIn t msg k =>
            let ι' := env.remove (x ∷ σ) ι xIn in
            let x' := ι.[? x∷σ] in
            let t' := inst t ι' in
            bind (assert_formula (x' = t'))
                 (fun _ => replay k ι')
        | @SymProp.assume_vareq _ x σ xIn t k =>
            let ι' := env.remove (x ∷ σ) ι xIn in
            let x' := ι.[? x∷σ] in
            let t' := inst t ι' in
            bind (assume_formula (x' = t'))
                 (fun _ => replay k ι')
        | SymProp.pattern_match s pat rhs =>
            error
        | SymProp.pattern_match_var x pat rhs =>
            error
        | SymProp.debug b k =>
            debug (replay k ι)
        end.

  End WithMonad.

End ShallowReplayOn.
