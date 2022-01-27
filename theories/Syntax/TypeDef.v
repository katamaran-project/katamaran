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

From Katamaran Require Import
     Context
     Environment
     Syntax.TypeDecl
     Syntax.Variables.

Local Set Implicit Arguments.

Module Type UnionTypeDefKit (Import TD : TypeDecl).
  (* Union data constructor field type *)
  Parameter Inline 𝑼𝑲_Ty : forall (U : 𝑼), 𝑼𝑲 U -> Ty.
  Parameter Inline 𝑼_fold   : forall (U : 𝑼), { K : 𝑼𝑲 U & Val (𝑼𝑲_Ty K) } -> 𝑼𝑻 U.
  Parameter Inline 𝑼_unfold : forall (U : 𝑼), 𝑼𝑻 U -> { K : 𝑼𝑲 U & Val (𝑼𝑲_Ty K) }.
  Parameter Inline 𝑼_fold_unfold :
    forall (U : 𝑼) (Kv: 𝑼𝑻 U),
      𝑼_fold (𝑼_unfold Kv) = Kv.
  Parameter Inline 𝑼_unfold_fold :
    forall (U : 𝑼) (Kv: { K : 𝑼𝑲 U & Val (𝑼𝑲_Ty K) }),
      𝑼_unfold (𝑼_fold Kv) = Kv.
End UnionTypeDefKit.

Module Type RecordTypeDefKit (Import TD : TypeDecl).
  (* Record field names. *)
  Parameter Inline 𝑹𝑭  : Set.
  (* Record field types. *)
  Parameter Inline 𝑹𝑭_Ty : 𝑹 -> NCtx 𝑹𝑭 Ty.
  Parameter Inline 𝑹_fold   : forall (R : 𝑹), NamedEnv Val (𝑹𝑭_Ty R) -> 𝑹𝑻 R.
  Parameter Inline 𝑹_unfold : forall (R : 𝑹), 𝑹𝑻 R -> NamedEnv Val (𝑹𝑭_Ty R).
  Parameter Inline 𝑹_fold_unfold :
    forall (R : 𝑹) (Kv: 𝑹𝑻 R),
      𝑹_fold (𝑹_unfold Kv) = Kv.
  Parameter Inline 𝑹_unfold_fold :
    forall (R : 𝑹) (Kv: NamedEnv Val (𝑹𝑭_Ty R)),
      𝑹_unfold (𝑹_fold Kv) = Kv.
End RecordTypeDefKit.

Module Type TypeDefKit (TD : TypeDecl) :=
  UnionTypeDefKit TD <+ RecordTypeDefKit TD.

Module DefaultUnionTypeDefKit <: UnionTypeDefKit DefaultTypeDecl.
  Import DefaultTypeDecl.

  Definition 𝑼𝑲_Ty (U : 𝑼) : 𝑼𝑲 U -> Ty := match U with end.
  Definition 𝑼_fold (U : 𝑼) : { K : 𝑼𝑲 U & Val (𝑼𝑲_Ty K) } -> 𝑼𝑻 U :=
    match U with end.
  Definition 𝑼_unfold (U : 𝑼) : 𝑼𝑻 U -> { K : 𝑼𝑲 U & Val (𝑼𝑲_Ty K) } :=
    match U with end.
  Lemma 𝑼_fold_unfold (U : 𝑼) :
    forall (Kv: 𝑼𝑻 U), 𝑼_fold (𝑼_unfold Kv) = Kv.
  Proof. destruct U. Qed.
  Lemma 𝑼_unfold_fold (U : 𝑼) :
    forall (Kv: { K : 𝑼𝑲 U & Val (𝑼𝑲_Ty K) }),
      𝑼_unfold (𝑼_fold Kv) = Kv.
  Proof. destruct U. Qed.

End DefaultUnionTypeDefKit.

Module DefaultRecordTypeDefKit : RecordTypeDefKit DefaultTypeDecl.
  Import DefaultTypeDecl.

  Definition 𝑹𝑭 : Set := Empty_set.
  Definition 𝑹𝑭_Ty (R : 𝑹) : NCtx 𝑹𝑭 Ty := match R with end.
  Definition 𝑹_fold (R : 𝑹) : NamedEnv Val (𝑹𝑭_Ty R) -> 𝑹𝑻 R := match R with end.
  Definition 𝑹_unfold (R : 𝑹) : 𝑹𝑻 R -> NamedEnv Val (𝑹𝑭_Ty R) := match R with end.
  Lemma 𝑹_fold_unfold (R : 𝑹) :
    forall (Kv: 𝑹𝑻 R), 𝑹_fold R (𝑹_unfold Kv) = Kv.
  Proof. destruct R. Qed.
  Lemma 𝑹_unfold_fold (R : 𝑹) :
    forall (Kv: NamedEnv Val (𝑹𝑭_Ty R)),
      𝑹_unfold (𝑹_fold R Kv) = Kv.
  Proof. destruct R. Qed.

End DefaultRecordTypeDefKit.

Module DefaultTypeDefKit : TypeDefKit DefaultTypeDecl :=
  DefaultUnionTypeDefKit <+ DefaultRecordTypeDefKit.

Module Type Types :=
  VarKit <+ TypeDecl.TypeDecl <+ TypeDefKit.