(******************************************************************************)
(* Copyright (c) 2019 Dominique Devriese, Georgy Lukyanov,                    *)
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
     Strings.String.
From Katamaran Require Import
     Base
     Semantics.Registers
     Syntax.FunDecl
     Syntax.Statements.

Module Type FunDefKit (Import B : Base) (Import F : FunDecl B).
  Include RegStoreKit B.

  (* Memory model *)
  Parameter Memory : Type.
  (* Step relation for calling an external function. The complete function call
     is done in one step. The result of an external call is either a failure
     with an error message msg (res = inl msg) or a successful computation with
     a result value v (res = inr v).
   *)
  Parameter ForeignCall :
    forall
      {Δ σ} (f : 𝑭𝑿 Δ σ)
      (args : CStore Δ)
      (res  : string + Val σ)
      (γ γ' : RegStore)
      (μ μ' : Memory), Prop.
  Parameter ForeignProgress :
    forall {Δ σ} (f : 𝑭𝑿 Δ σ) (args : CStore Δ) γ μ,
    exists γ' μ' res, ForeignCall f args res γ γ' μ μ'.

  Parameter FunDef : forall {Δ τ} (f : 𝑭 Δ τ), Stm Δ τ.

End FunDefKit.
