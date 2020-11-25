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

From Coq Require Import
     Bool.Bool
     ZArith.ZArith.

From MicroSail Require Export
     Syntax.Types.

Import CtxNotations.

Local Set Implicit Arguments.

(******************************************************************************)

Module Type ValueKit.

  Declare Module typekit : TypeKit.
  Module Export TY := Types typekit.

  (* Union data constructor field type *)
  Parameter Inline 𝑼𝑲_Ty : forall (U : 𝑼), 𝑼𝑲 U -> Ty.
  Parameter Inline 𝑼_fold   : forall (U : 𝑼), { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty K) } -> 𝑼𝑻 U.
  Parameter Inline 𝑼_unfold : forall (U : 𝑼), 𝑼𝑻 U -> { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty K) }.
  Parameter Inline 𝑼_fold_unfold :
    forall (U : 𝑼) (Kv: 𝑼𝑻 U),
      𝑼_fold (𝑼_unfold Kv) = Kv.
  Parameter Inline 𝑼_unfold_fold :
    forall (U : 𝑼) (Kv: { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty K) }),
      𝑼_unfold (𝑼_fold Kv) = Kv.

  (* Record field names. *)
  Parameter Inline 𝑹𝑭  : Set.
  (* Record field types. *)
  Parameter Inline 𝑹𝑭_Ty : 𝑹 -> NCtx 𝑹𝑭 Ty.
  Parameter Inline 𝑹_fold   : forall (R : 𝑹), NamedEnv Lit (𝑹𝑭_Ty R) -> 𝑹𝑻 R.
  Parameter Inline 𝑹_unfold : forall (R : 𝑹), 𝑹𝑻 R -> NamedEnv Lit (𝑹𝑭_Ty R).
  Parameter Inline 𝑹_fold_unfold :
    forall (R : 𝑹) (Kv: 𝑹𝑻 R),
      𝑹_fold (𝑹_unfold Kv) = Kv.
  Parameter Inline 𝑹_unfold_fold :
    forall (R : 𝑹) (Kv: NamedEnv Lit (𝑹𝑭_Ty R)),
      𝑹_unfold (𝑹_fold Kv) = Kv.

End ValueKit.

Module Values (Export valuekit : ValueKit).

  Fixpoint Lit_eqb (σ : Ty) : forall (l1 l2 : Lit σ), bool :=
    match σ with
    | ty_int      => Z.eqb
    | ty_bool     => Bool.eqb
    | ty_bit      => Bit_eqb
    | ty_string   => String.eqb
    | ty_list σ   => list_beq (Lit_eqb σ)
    | ty_prod σ τ => prod_beq (Lit_eqb σ) (Lit_eqb τ)
    | ty_sum σ τ  => sum_beq (Lit_eqb σ) (Lit_eqb τ)
    | ty_unit     => fun _ _ => true
    | ty_enum E   => fun l1 l2 => if 𝑬𝑲_eq_dec l1 l2 then true else false
    | ty_bvec n   => @Word.weqb n
    | ty_tuple σs => envrec_beq Lit_eqb
    | ty_union U  => fun l1 l2 => if 𝑼𝑻_eq_dec l1 l2 then true else false
    | ty_record R => fun l1 l2 => if 𝑹𝑻_eq_dec l1 l2 then true else false
    end.

  Lemma Lit_eqb_spec (σ : Ty) (x y : Lit σ) : reflect (x = y) (Lit_eqb σ x y).
  Proof with microsail_solve_eqb_spec.
    induction σ; cbn.
    - apply Z.eqb_spec.
    - apply Bool.eqb_spec.
    - apply Bit_eqb_spec.
    - apply String.eqb_spec.
    - apply list_beq_spec; auto.
    - destruct x as [x1 x2]; destruct y as [y1 y2]...
    - destruct x as [x1|x2]; destruct y as [y1|y2]...
    - destruct x. destruct y...
    - destruct (𝑬𝑲_eq_dec x y)...
    - apply iff_reflect. symmetry.
      apply (Word.weqb_true_iff x y).
    - induction σs; intros.
      + destruct x; destruct y...
      + cbn in *.
        destruct x as [xs x]; destruct y as [ys y]; destruct X as [pσs pb]; cbn in *.
        specialize (IHσs pσs).
        destruct (IHσs xs ys); destruct (pb x y)...
    - destruct (𝑼𝑻_eq_dec x y)...
    - destruct (𝑹𝑻_eq_dec x y)...
  Qed.

End Values.
