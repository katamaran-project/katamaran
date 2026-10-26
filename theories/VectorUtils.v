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

From Equations Require Import Equations.
From stdpp Require Import vector.
From Stdlib Require Import ZArith.BinInt.
From Stdlib Require Import Vector.

Local Set Implicit Arguments.
Local Set Equations Transparent.

Section AddRemove.

  Context (A : Type).

  Equations vadd {n} (i : fin (S n)) (a : A) (v : vec A n) : vec A (S n) :=
  | 0%fin | a | v := cons a v
  | FS i | a | h ::: v := h ::: vadd i a v
  .

  (* Note: spurious pattern match to appease type checker *)
  Equations vremove {n} (i : fin n) (v : vec A n) : vec A (pred n) :=
  | 0%fin | h ::: v := v
  | FS 0%fin | h ::: v := h ::: vremove 0%fin v
  | FS (FS i) | h ::: v := h ::: vremove (FS i) v
  .

  (* The following would be nice as a defining equation, but alas... *)
  Lemma vremove_FS {n} (i : fin (S n)) h (v : vec A (S n)) :
    vremove (FS i) (h ::: v) = h ::: vremove i v.
  Proof.
    revert i.
    refine (fin_S_inv _ _ _); now cbn.
  Qed.

  (* Whatever would we do without Equations? *)
  Equations vadd_lookup_remove {n} (i : fin (S n)) (v : vec A (S n)) :
    v = vadd i (v !!! i) (vremove i v) :=
  | 0%fin | h ::: v := _
  | FS 0%fin | h ::: v := f_equal (cons h) (vadd_lookup_remove 0%fin v)
  | FS (FS i) | h ::: v := f_equal (cons h) (vadd_lookup_remove (FS i) v)
  .
  Next Obligation. reflexivity. Qed.

End AddRemove.

Equations vmap_vremove {n A B} (i : fin n) (v : vec A n) (f : A -> B) :
  vmap f (vremove i v) = vremove i (vmap f v) :=
| 0%fin | h ::: v | f:= eq_refl
| FS 0%fin | h ::: v | f := f_equal _ (vmap_vremove 0%fin v f)
| FS (FS i) | h ::: v | f := f_equal _ (vmap_vremove (FS i) v f)
.

Equations vzip_with_vremove {n A1 A2 B} (i : fin n) (v1 : vec A1 n) (v2 : vec A2 n) (f : A1 -> A2 -> B) :
  vzip_with f (vremove i v1) (vremove i v2) = vremove i (vzip_with f v1 v2) :=
| 0%fin | h1 ::: v1 | h2 ::: v2 | f := eq_refl
| FS 0%fin | h1 ::: v1 | h2 ::: v2 | f := f_equal _ (vzip_with_vremove 0%fin v1 v2 f)
| FS (FS i) | h1 ::: v1 | h2 ::: v2 | f := f_equal _ (vzip_with_vremove (FS i) v1 v2 f)
.

(* Dot product of two integer vectors. *)
Equations dot {n} (c xs : vec Z n) : Z :=
| [#] | [#] := 0%Z
| c ::: cs | x ::: xs := (c * x + dot cs xs)%Z.
