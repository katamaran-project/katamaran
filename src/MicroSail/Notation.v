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

(* Really short summary on notations in Coq:
   - Coq uses precedence levels from 0 to 100.
   - Lower levels bound tighter than higher levels.
   - A /\ B is at level 80, right assoc
   - A \/ B is at level 85, right assoc
   - x = y is at level 70
 *)

(* after 8.10: Declare Scope ctx_scope. *)
Delimit Scope ctx_scope with ctx.

Reserved Notation "'ε'"            (at level 0).
Reserved Infix "▻"                 (at level 55, left associativity).
Reserved Infix "▻▻"                (at level 55, left associativity).
Reserved Notation "b ∈ Γ"          (at level 75, Γ at next level, no associativity).

(* after 8.10: Declare Scope env_scope. *)
Delimit Scope env_scope with env.

Reserved Notation "δ ► x ↦ v"      (at level 55, x at level 99, left associativity).
Reserved Notation "δ1 ►► δ2"       (at level 55, left associativity).
Reserved Notation "δ [ x ↦ v ]"    (at level 55, x at level 99, v at level 99, left associativity).
Reserved Notation "δ ! x"          (at level 56, no associativity).

Reserved Notation "⟨ δ1 , s1 ⟩ ---> ⟨ δ2 , s2 ⟩" (at level 75, no associativity).
Reserved Notation "⟨ δ1 , s1 ⟩ --->* ⟨ δ2 , s2 ⟩" (at level 75, no associativity).
