(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel                                          *)
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
     Strings.String
     ZArith.ZArith.
From MicroSail Require Import
     Notation
     Syntax.Values.
From MinimalCaps Require Export
     Types.

Set Implicit Arguments.
Import CtxNotations.
Import EnvNotations.
Local Open Scope string_scope.

Module MinCapsValueKit <: ValueKit.

  Module typekit := MinCapsTypeKit.
  Module Export TY := Syntax.Types.Types typekit.

  Notation ty_hv := (ty_enum regname).
  Notation ty_lv := (ty_enum regname).
  Notation ty_rv := (ty_sum (ty_enum regname) ty_int).
  Notation ty_cap := (ty_record capability).
  Notation ty_word := (ty_sum ty_int ty_cap).
  Notation ty_memval := (ty_int).
  Notation ty_addr := (ty_int).
  Notation ty_perm := (ty_enum permission).
  Notation ty_instr := (ty_union instruction).

  (** UNIONS **)
  Definition 𝑼𝑲_Ty (U : 𝑼) : 𝑼𝑲 U -> Ty :=
    match U with
    | instruction => fun K =>
      match K with
      | kjr       => ty_lv
      | kjalr     => ty_prod ty_lv ty_lv
      | kj        => ty_int
      | kjal      => ty_prod ty_lv ty_int
      | kbnez     => ty_prod ty_lv ty_int
      | kmv       => ty_prod ty_lv ty_hv
      | kld       => ty_tuple [ty_lv, ty_hv, ty_int]
      | ksd       => ty_tuple [ty_hv, ty_lv, ty_int]
      | kaddi     => ty_tuple [ty_lv, ty_hv, ty_int]
      | kadd      => ty_tuple [ty_lv, ty_lv, ty_lv]
      (* | klt       => ty_prod ty_lv (ty_prod ty_rv ty_rv) *)
      (* | kplus     => ty_prod ty_lv (ty_prod ty_rv ty_rv) *)
      (* | kminus    => ty_prod ty_lv (ty_prod ty_rv ty_rv) *)
      (* | klea      => ty_prod ty_lv ty_rv *)
      (* | krestrict => ty_prod ty_lv ty_rv *)
      (* | ksubseg   => ty_prod ty_lv (ty_prod ty_rv ty_rv) *)
      (* | kisptr    => ty_prod ty_lv ty_rv *)
      | kgetp     => ty_prod ty_lv ty_lv
      | kgetb     => ty_prod ty_lv ty_lv
      | kgete     => ty_prod ty_lv ty_lv
      | kgeta     => ty_prod ty_lv ty_lv
      (* | kfail     => ty_unit *)
      | kret      => ty_unit
      end
    end.

  Definition 𝑼_fold (U : 𝑼) : { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty U K) } -> 𝑼𝑻 U :=
    match U with
    | instruction => fun Kv =>
      match Kv with
      | existT kjr       lv                 => jr lv
      | existT kjalr     (lv1 , lv2)        => jalr lv1 lv2
      | existT kj        offset             => j offset
      | existT kjal      (lv , offset)      => jal lv offset
      | existT kbnez     (lv , immediate)   => bnez lv immediate
      | existT kmv       (lv , hv)          => mv lv hv
      | existT kld       (tt , lv , hv , immediate) => ld lv hv immediate
      | existT ksd       (tt , hv , lv , immediate) => sd hv lv immediate
      | existT kaddi     (tt , lv , hv , immediate) => addi lv hv immediate
      | existT kadd      (tt , lv1 , lv2 , lv3)     => add lv1 lv2 lv3
      (* | existT klt       (lv , (rv1 , rv2)) => lt lv rv1 rv2 *)
      (* | existT kplus     (lv , (rv1 , rv2)) => plus lv rv1 rv2 *)
      (* | existT kminus    (lv , (rv1 , rv2)) => minus lv rv1 rv2 *)
      (* | existT klea      (lv , rv)          => lea lv rv *)
      (* | existT krestrict (lv , rv)          => restrict lv rv *)
      (* | existT ksubseg   (lv , (rv1 , rv2)) => subseg lv rv1 rv2 *)
      (* | existT kisptr    (lv , rv)          => isptr lv rv *)
      | existT kgetp     (lv , lv')         => getp lv lv'
      | existT kgetb     (lv , lv')         => getb lv lv'
      | existT kgete     (lv , lv')         => gete lv lv'
      | existT kgeta     (lv , lv')         => geta lv lv'
      (* | existT kfail     tt                 => fail *)
      | existT kret      tt                 => ret
      end
    end.
  Definition 𝑼_unfold (U : 𝑼) : 𝑼𝑻 U -> { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty U K) } :=
    match U as u return (𝑼𝑻 u -> {K : 𝑼𝑲 u & Lit (𝑼𝑲_Ty u K)}) with
    | instruction => fun Kv =>
      match Kv with
      | jr  lv             => existT kjr   lv
      | jalr lv1 lv2       => existT kjalr (lv1 , lv2)
      | j offset           => existT kj    offset
      | jal lv offset      => existT kjal  (lv , offset)
      | bnez lv immediate  => existT kbnez (lv , immediate)
      | mv lv hv           => existT kmv   (lv , hv)
      | ld lv hv immediate => existT kld   (tt , lv , hv , immediate)
      | sd hv lv immediate => existT ksd   (tt , hv , lv , immediate)
      | addi lv hv immediate => existT kaddi (tt , lv , hv , immediate)
      | add lv1 lv2 lv3      => existT kadd (tt , lv1 , lv2 , lv3)
      (* | lt lv rv1 rv2     => existT klt       (lv , (rv1 , rv2)) *)
      (* | plus lv rv1 rv2   => existT kplus     (lv , (rv1 , rv2)) *)
      (* | minus lv rv1 rv2  => existT kminus    (lv , (rv1 , rv2)) *)
      (* | lea lv rv         => existT klea      (lv , rv) *)
      (* | restrict lv rv    => existT krestrict (lv , rv) *)
      (* | subseg lv rv1 rv2 => existT ksubseg   (lv , (rv1 , rv2)) *)
      (* | isptr lv rv       => existT kisptr    (lv , rv) *)
      | getp lv lv'       => existT kgetp     (lv , lv')
      | getb lv lv'       => existT kgetb     (lv , lv')
      | gete lv lv'       => existT kgete     (lv , lv')
      | geta lv lv'       => existT kgeta     (lv , lv')
      (* | fail              => existT kfail     tt *)
      | ret                => existT kret  tt
      end
    end.
  Lemma 𝑼_fold_unfold : forall (U : 𝑼) (Kv: 𝑼𝑻 U),
      𝑼_fold U (𝑼_unfold U Kv) = Kv.
  Proof. now intros [] []. Qed.
  Lemma 𝑼_unfold_fold : forall (U : 𝑼) (Kv: { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty U K) }),
      𝑼_unfold U (𝑼_fold U Kv) = Kv.
  Proof.
    intros [] [[] x]; cbn in x;
      repeat match goal with
             | x: unit     |- _ => destruct x
             | x: prod _ _ |- _ => destruct x
             end; auto.
  Qed.

  (** RECORDS **)
  Definition 𝑹𝑭  : Set := string.

  Definition 𝑹𝑭_Ty (R : 𝑹) : NCtx 𝑹𝑭 Ty :=
    match R with
    | capability => [ "cap_permission" ∶ ty_perm,
                      "cap_begin"     ∶ ty_addr,
                      "cap_end"       ∶ ty_addr,
                      "cap_cursor"    ∶ ty_addr
                    ]
    end.

  Definition 𝑹_fold (R : 𝑹) : NamedEnv Lit (𝑹𝑭_Ty R) -> 𝑹𝑻 R :=
    match R with
    | capability =>
      fun fields =>
        MkCap
          (fields ‼ "cap_permission")
          (fields ‼ "cap_begin")
          (fields ‼ "cap_end")
          (fields ‼ "cap_cursor")
    end%exp.

  Definition 𝑹_unfold (R : 𝑹) : 𝑹𝑻 R -> NamedEnv Lit (𝑹𝑭_Ty R) :=
    match R  with
    | capability =>
      fun c=>
        env_nil
          ► ("cap_permission" ∶ ty_perm ↦ cap_permission c)
          ► ("cap_begin"      ∶ ty_addr ↦ cap_begin c)
          ► ("cap_end"        ∶ ty_addr ↦ cap_end c)
          ► ("cap_cursor"     ∶ ty_addr ↦ cap_cursor c)
    end%env.
  Lemma 𝑹_fold_unfold : forall (R : 𝑹) (Kv: 𝑹𝑻 R),
      𝑹_fold R (𝑹_unfold R Kv) = Kv.
  Proof. now intros [] []. Qed.
  Lemma 𝑹_unfold_fold : forall (R : 𝑹) (Kv: NamedEnv Lit (𝑹𝑭_Ty R)),
      𝑹_unfold R (𝑹_fold R Kv) = Kv.
  Proof. intros []; now apply Forall_forall. Qed.

End MinCapsValueKit.
