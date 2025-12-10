(******************************************************************************)
(* Copyright (c) 2021 Steven Keuchel                                          *)
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

From Equations Require Import
     Equations.
From Katamaran Require Import
     Prelude
     Tactics
     Syntax.TypeDecl.

Local Set Implicit Arguments.

Module Type RegDeclKit (Import T : Types).
  (* Names of registers. *)
  Parameter Inline 𝑹𝑬𝑮 : Ty -> Set.
  #[export] Declare Instance 𝑹𝑬𝑮_eq_dec : EqDec (sigT 𝑹𝑬𝑮).
  #[export] Declare Instance 𝑹𝑬𝑮_finite : finite.Finite (sigT 𝑹𝑬𝑮).
End RegDeclKit.

Module DefaultRegDeclKit (Import T : Types) <: RegDeclKit T.
  Definition 𝑹𝑬𝑮 : Ty -> Set := fun _ => Empty_set.
  #[export] Instance 𝑹𝑬𝑮_eq_dec : EqDec (sigT 𝑹𝑬𝑮) := sigma_eqdec _ _.

  Local Obligation Tactic :=
    finite_from_eqdec.

  #[export] Instance 𝑹𝑬𝑮_finite : finite.Finite (sigT 𝑹𝑬𝑮).
  Proof.
    refine {| finite.enum := nil; finite.NoDup_enum := base.NoDup_nil_2; finite.elem_of_enum := fun x => _ |}.
    destruct x as (x & R). destruct R.
  Defined.

  (* denis says: stuck here, probably something to do with the equations library
     that i don't quite understand. *)

End DefaultRegDeclKit.
