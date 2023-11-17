(******************************************************************************)
(* Copyright (c) 2023 Steven Keuchel                                          *)
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
  ZArith.BinInt.
From Equations Require Import
  Equations.
From Katamaran Require Import
  Bitvector
  Context
  Prelude
  Syntax.TypeDecl.

Import ctx.notations.

Local Set Implicit Arguments.
Local Set Transparent Obligations.

Module uop.

  Import ty.

  Section WithTypeDecl.
    Context {TDC : TypeDeclKit}.

    Variant UnOp : Ty -> Ty -> Set :=
    | inl {σ1 σ2 : Ty}  : UnOp σ1 (sum σ1 σ2)
    | inr {σ1 σ2 : Ty}  : UnOp σ2 (sum σ1 σ2)
    | neg               : UnOp int int
    | not               : UnOp bool bool
    | sext {m n} {p : IsTrue (m <=? n)} : UnOp (bvec m) (bvec n)
    | zext {m n} {p : IsTrue (m <=? n)} : UnOp (bvec m) (bvec n)
    | get_slice_int {n} : UnOp int (bvec n)
    | unsigned {n}      : UnOp (bvec n) int
    | truncate {n} (m : nat) {p : IsTrue (m <=? n)} : UnOp (bvec n) (bvec m)
    | vector_subrange {n} (s l : nat) {p : IsTrue (s + l <=? n)} : UnOp (bvec n) (bvec l)
    | negate {n}        : UnOp (bvec n) (bvec n)
    | hl_injl           : UnOp hl_val hl_val
    | hl_injr           : UnOp hl_val hl_val
    | hl_locv           : UnOp hl_loc hl_val
    .
    Set Transparent Obligations.
    Derive Signature for UnOp.
    Derive NoConfusion for UnOp.

  End WithTypeDecl.

  Section WithTypeDef.
    Context {TDC : TypeDeclKit}.
    Context {TDN : TypeDenoteKit TDC}.
    Context {TDF : TypeDefKit TDN}.
    Import Sigma_Notations.

    Definition Tel (τ : Ty) : Set :=
      Σ σ : Ty, UnOp σ τ.

    Obligation Tactic := cbn; intros;
      try solve
        [let e := fresh in intro e; depelim e; try easy;
         try progress cbn in * |-; congruence
        |subst; repeat f_equal; apply IsTrue.proof_irrelevance
        ].

    #[derive(equations=no)] Equations tel_eq_dec {σ1 σ2 τ : Ty}
      (op1 : UnOp σ1 τ) (op2 : UnOp σ2 τ) :
      dec_eq (A := Tel τ) (σ1,op1) (σ2,op2) :=
    | inl                              | inl => left eq_refl
    | inr                              | inr => left eq_refl
    | neg                              | neg => left eq_refl
    | not                              | not => left eq_refl
    | @sext _ m1 ?(n) p1               | @sext _ m2 n p2 with eq_dec m1 m2 => {
      | left _ => left _
      | right _ => right _
      }
    | @zext _ m1 ?(n) p1               | @zext _ m2 n p2 with eq_dec m1 m2 => {
      | left _ => left _
      | right _ => right _
      }
    | get_slice_int                    | get_slice_int => left eq_refl
    | @unsigned _ m                    | @unsigned _ n with eq_dec m n => {
      | left _ => left _
      | right _ => right _
      }
    | @truncate _ m1 ?(n) p1           | @truncate _ m2 n p2 with eq_dec m1 m2 => {
      | left _ => left _
      | right _ => right _
      }
    | @vector_subrange _ n1 s1 ?(l) p1 | @vector_subrange _ n2 s2 l p2 with eq_dec n1 n2, eq_dec s1 s2 => {
      | left _  | left _  => left _
      | left _  | right _ => right _
      | right _ | _       => right _
      }
    | negate                           | negate => left eq_refl
    | hl_injl                          | hl_injl => left eq_refl
    | hl_injr                          | hl_injr => left eq_refl
    | hl_locv                          | hl_locv => left eq_refl
    | _                                | _ => right _.

    #[local] Instance eq_dec_unop [σ1 σ2] : EqDec (UnOp σ1 σ2) :=
      fun x y =>
        match tel_eq_dec x y with
        | left e => left
                      (* Uses decidable equality of Ty. *)
                      (inj_right_sigma _ _ _ e)
        | right b => right (fun e => b (f_equal _ e))
        end.

    Definition eval {σ1 σ2 : Ty} (op : UnOp σ1 σ2) : Val σ1 -> Val σ2 :=
      match op in UnOp σ1 σ2 return Val σ1 -> Val σ2 with
      | inl                 => Datatypes.inl
      | inr                 => Datatypes.inr
      | neg                 => Z.opp
      | not                 => negb
      | sext                => fun v => bv.sext v
      | zext                => fun v => bv.zext v
      | get_slice_int       => bv.of_Z
      | unsigned            => fun v => bv.unsigned v
      | truncate m          => fun v => bv.truncate m v
      | vector_subrange s l => bv.vector_subrange s l
      | negate              => bv.negate
      | hl_injl             => lang.heap_lang.InjLV
      | hl_injr             => lang.heap_lang.InjRV
      | hl_locv             => fun l => lang.heap_lang.LitV (lang.heap_lang.LitLoc l)
      end.

  End WithTypeDef.
  #[export] Existing Instance eq_dec_unop.

End uop.
#[export] Existing Instance uop.eq_dec_unop.
Export uop (UnOp).
