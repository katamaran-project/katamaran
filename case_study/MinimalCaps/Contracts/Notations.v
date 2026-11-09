(******************************************************************************)
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

From Stdlib Require Import
  Strings.String.
From Katamaran Require Import
  MinimalCaps.Machine
  MinimalCaps.Sig.

Import ctx.notations.
Import ctx.resolution.
Import env.notations.
Import MinCapsSignature.
Open Scope string_scope.
Open Scope ctx_scope.

Module Notations.
  Import MinCapsSignature.ContractNotations.
  Import MinCapsContractNotations.

  (* Destructure a capability argument into its fields, which become logic
     variables of the contract. *)
  Notation "'(' p ',' b ',' e ',' a ')' '::' 'ty.cap'" :=
    (arg_pat ty.cap [p∷ty.perm; b∷ty.addr; e∷ty.addr; a∷ty.addr]
       (term_record capability [term_var p; term_var b; term_var e; term_var a]))
    : arg_scope.

  (* 𝒱 should only be used with terms of type word or cap, otherwise it just
     returns bottom *)
  Definition 𝒱 {Σ τ} : Term Σ τ -> Assertion Σ :=
    match τ with
    | ty.word => fun w => asn_safe w
    | ty.cap  => fun w => asn_csafe w
    | ty.int  => fun w => asn_safe (term_inl w)
    | _       => fun _ => ⊥
    end.

  Notation "'(' tp ',' tb ',' te ',' ta ')'" :=
    (term_record capability [tp%term; tb%term; te%term; ta%term]) : term_scope.
  Notation "'𝒱' '(' tp ',' tb ',' te ',' ta ')'" :=
    (𝒱 (term_record capability [tp%term; tb%term; te%term; ta%term])) : asn_scope.
  Notation "'𝒱' '(' t ')'" :=
    (𝒱 t) : asn_scope.
End Notations.
