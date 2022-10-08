(******************************************************************************)
(* Copyright (c) 2019 Steven Keuchel, Dominique Devriese, Georgy Lukyanov     *)
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

Reserved Infix "▻"                 (at level 61, left associativity).
Reserved Infix "▻▻"                (at level 61, left associativity).
(* stdpp defines this at level 70 *)
Reserved Infix "∈"                 (at level 70).
(* Notation for bindings and type of bindings defined in the Context module.
   This is at level 49 because "-" is at level 50. This avoid parens when
   removing a binding an element from a context, e.g. Γ - x∷σ. *)
Reserved Notation "x ∷ t"          (at level 49, no associativity, format "'[' x ∷ t ']'").

Reserved Notation "[ ]" (format "[ ]").
Reserved Notation "[ x ]".
Reserved Notation "[ x ; y ; .. ; z ]".

(* We use the character ↦ as an infix notation for points-to predicates in the
   case-studies. This should bind tighter than ∗ which is at level 80. Hence
   x in this notation has to bind at least tighter than that. Also it should
   allow for x being a typed binding (y ∷ t) which is at level 49, so looser
   than that. *)
Reserved Notation "δ ► ( x ↦ v )"  (at level 50, x at level 50, left associativity,
 format "δ  ►  ( x  ↦  v )").
Reserved Notation "δ1 ►► δ2"       (at level 50, left associativity).
Reserved Notation "δ ⟪ x ↦ v ⟫"    (at level 90, x at level 0, v at level 0, left associativity).
Reserved Notation "δ ‼ x"          (at level 56, no associativity).

Reserved Notation "⟨ γ1 , μ1 , δ1 , s1 ⟩ ---> ⟨ γ2 , μ2 , δ2 , s2 ⟩" (at level 75, no associativity).
Reserved Notation "⟨ γ1 , μ1 , δ1 , s1 ⟩ --->* ⟨ γ2 , μ2 , δ2 , s2 ⟩" (at level 75, no associativity).
(* Notation "( x , y , .. , z )" := *)
(*   (tuplepat_snoc .. (tuplepat_snoc (tuplepat_snoc tuplepat_nil x) y) .. z). *)

Reserved Notation "s1 ;; s2" (at level 100, s2 at level 200, right associativity,
  format "'[v' s1 ;; '/' s2 ']'").

Reserved Notation "⦃ P ⦄ s ; δ ⦃ Q ⦄" (at level 75, no associativity).

(* Logic notations. These were chosen to be compatible with Coq.Unicode.Utf8, stdpp and iris. *)
Reserved Notation "P ⊢ Q" (at level 99, Q at level 200, right associativity).
Reserved Notation "P '⊢@{' L } Q" (at level 99, Q at level 200, right associativity).
Reserved Notation "P ⊢f f" (at level 99, f at level 200, no associativity).
Reserved Notation "P ⊣⊢ Q" (at level 95, no associativity).
Reserved Notation "P '⊣⊢@{' L } Q" (at level 95, no associativity).
Reserved Infix "∧" (at level 80, right associativity).
Reserved Infix "∨" (at level 85, right associativity).
Reserved Notation "x → y" (at level 99, y at level 200, right associativity).
Reserved Notation "'!!' e" (at level 25).
Reserved Notation "P ∗ Q" (at level 80, right associativity).
Reserved Notation "P -∗ Q"
  (at level 99, Q at level 200, right associativity,
   format "'[' P  '/' -∗  Q ']'").

Reserved Notation "x != y" (at level 70, no associativity).

Reserved Notation "x +ᵇ y" (at level 50, left associativity).
Reserved Notation "x -ᵇ y" (at level 50, left associativity).
Reserved Notation "x *ᵇ y" (at level 40, left associativity).

(* Signed bitvector operations *)
Reserved Notation "x >=ˢ y" (at level 70, no associativity).
Reserved Notation "x >ˢ y" (at level 70, no associativity).
Reserved Notation "x <=ˢ y" (at level 70, no associativity).
Reserved Notation "x <ˢ y" (at level 70, no associativity).

(* Unsigned bitvector operations *)
Reserved Notation "x >=ᵘ y" (at level 70, no associativity).
Reserved Notation "x >ᵘ y" (at level 70, no associativity).
Reserved Notation "x <=ᵘ y" (at level 70, no associativity).
Reserved Notation "x <ᵘ y" (at level 70, no associativity).
