(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel, Sander Huyghebaert                      *)
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
From stdpp Require
     finite.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Base.

(*** TYPES ***)

Inductive Permission : Set :=
  O | R | RW | E.

Inductive RegName : Set :=
  R0 | R1 | R2 | R3.

Definition LV : Set := RegName.
Definition HV : Set := RegName.
Definition RV : Set := LV + Z.

Inductive Instruction : Set :=
| jr        (lv : LV)
| jalr      (lv1 : LV) (lv2 : LV)
| j         (offset : Z)
| jal       (lv : LV) (offset : Z)
| bnez      (lv : LV) (immediate : Z)
| mv        (lv : LV) (hv : HV)
| ld        (lv : LV) (hv : HV) (immediate : Z)
| sd        (hv : HV) (lv : LV) (immediate : Z)
| addi      (lv : LV) (hv : HV) (immediate : Z)
| add       (lv1 : LV) (lv2 : LV) (lv3 : LV)
| sub       (lv1 : LV) (lv2 : LV) (lv3 : LV)
| slt       (lv1 : LV) (lv2 : LV) (lv3 : LV)
| slti      (lv : LV) (hv : HV) (immediate : Z)
| sltu      (lv1 : LV) (lv2 : LV) (lv3 : LV)
| sltiu     (lv : LV) (hv : HV) (immediate : Z)
| lea       (lv : LV) (hv : HV)
| restrict  (lv : LV) (hv : HV)
| restricti (lv : LV) (immediate : Z)
| subseg    (lv : LV) (hv1 hv2 : HV)
| subsegi   (lv : LV) (hv : HV) (immediate : Z)
| isptr     (lv : LV) (lv' : HV)
| getp      (lv lv' : LV)
| getb      (lv lv' : LV)
| gete      (lv lv' : LV)
| geta      (lv lv' : LV)
| fail
| ret.

Inductive InstructionConstructor : Set :=
| kjr
| kjalr
| kj
| kjal
| kbnez
| kmv
| kld
| ksd
| kaddi
| kadd
| ksub
| kslt
| kslti
| ksltu
| ksltiu
| klea
| krestrict
| krestricti
| ksubseg
| ksubsegi
| kisptr
| kgetp
| kgetb
| kgete
| kgeta
| kfail
| kret.

Section Records.
  (* Local Set Primitive Projections. *)

  Definition Addr : Set := Z.

  Record Capability : Set :=
    MkCap
      { cap_permission : Permission;
        cap_begin      : Addr;
        cap_end        : Addr;
        cap_cursor     : Addr;
      }.

End Records.

(** Enums **)
Inductive Enums : Set :=
| permission
| regname.

(** Unions **)
Inductive Unions : Set :=
| instruction.

(** Records **)
Inductive Records : Set :=
| capability.

Section TransparentObligations.
  Local Set Transparent Obligations.

  Derive NoConfusion for Capability.
  Derive NoConfusion for Permission.
  Derive NoConfusion for RegName.
  Derive NoConfusion for Enums.
  Derive NoConfusion for Unions.
  Derive NoConfusion for Records.
  Derive NoConfusion for Instruction.
  Derive NoConfusion for InstructionConstructor.

End TransparentObligations.

Derive EqDec for Permission.
Derive EqDec for Capability.
Derive EqDec for RegName.

Derive EqDec for Enums.
Derive EqDec for Unions.
Derive EqDec for Records.
Derive EqDec for Instruction.
Derive EqDec for InstructionConstructor.

Section Finite.

  Import stdpp.finite.

  Local Obligation Tactic :=
    finite_from_eqdec.

  Global Program Instance Permission_finite : Finite Permission :=
    {| enum := [O;R;RW;E] |}.

  Global Program Instance RegName_finite : Finite RegName :=
    {| enum := [R0;R1;R2;R3] |}.

  Global Program Instance InstructionConstructor_finite :
    Finite InstructionConstructor :=
    {| enum := [kjr;kjalr;kj;kjal;kbnez;kmv;kld;ksd;klea;krestrict;krestricti;ksubseg;ksubsegi;kisptr;kaddi;kadd;ksub;kslt;kslti;ksltu;ksltiu;kgetp;kgetb;kgete;kgeta;kfail;kret] |}.

End Finite.

Module Export MinCapsBase <: Base.
  Import ctx.notations.
  Import ctx.resolution.
  Import env.notations.
  Import stdpp.finite.

  Include DefaultVarKit.

  Section TypeDeclKit.

    (** ENUMS **)
    Definition 𝑬        := Enums.
    Definition 𝑬_eq_dec := Enums_eqdec.
    Definition 𝑬𝑲 (e : 𝑬) : Set :=
      match e with
      | permission => Permission
      | regname    => RegName
      end.
    Instance 𝑬𝑲_eq_dec (E : 𝑬) : EqDec (𝑬𝑲 E) :=
      ltac:(destruct E; auto with typeclass_instances).
    Instance 𝑬𝑲_finite (E : 𝑬) : Finite (𝑬𝑲 E) :=
      ltac:(destruct E; auto with typeclass_instances).

    (** UNIONS **)
    Definition 𝑼        := Unions.
    Definition 𝑼_eq_dec := Unions_eqdec.
    Definition 𝑼𝑻 (U : 𝑼) : Set :=
      match U with
      | instruction => Instruction
      end.
    Instance 𝑼𝑻_eq_dec U : EqDec (𝑼𝑻 U) :=
      ltac:(destruct U; cbn; auto with typeclass_instances).
    Definition 𝑼𝑲 (U : 𝑼) : Set :=
      match U with
      | instruction => InstructionConstructor
      end.
    Instance 𝑼𝑲_eq_dec U : EqDec (𝑼𝑲 U) :=
      ltac:(destruct U; auto with typeclass_instances).
    Instance 𝑼𝑲_finite U : Finite (𝑼𝑲 U) :=
      ltac:(destruct U; auto with typeclass_instances).

    (** RECORDS **)
    Definition 𝑹        := Records.
    Definition 𝑹_eq_dec := Records_eqdec.
    Definition 𝑹𝑻 (R : 𝑹) : Set :=
      match R with
      | capability => Capability
      end.
    Instance 𝑹𝑻_eq_dec R : EqDec (𝑹𝑻 R) :=
      ltac:(destruct R; auto with typeclass_instances).

  End TypeDeclKit.

  Include TypeDeclMixin.

  Notation ty_hv := (ty_enum regname).
  Notation ty_lv := (ty_enum regname).
  Notation ty_rv := (ty_sum (ty_enum regname) ty_int).
  Notation ty_cap := (ty_record capability).
  Notation ty_word := (ty_sum ty_int ty_cap).
  Notation ty_memval := (ty_word).
  Notation ty_addr := (ty_int).
  Notation ty_perm := (ty_enum permission).
  Notation ty_instr := (ty_union instruction).

  Section TypeDefKit.

    Open Scope string_scope.

    (** UNIONS **)
    Definition 𝑼𝑲_Ty (U : 𝑼) : 𝑼𝑲 U -> Ty :=
      match U with
      | instruction => fun K =>
        match K with
        | kjr        => ty_lv
        | kjalr      => ty_prod ty_lv ty_lv
        | kj         => ty_int
        | kjal       => ty_prod ty_lv ty_int
        | kbnez      => ty_prod ty_lv ty_int
        | kmv        => ty_prod ty_lv ty_hv
        | kld        => ty_tuple [ty_lv; ty_hv; ty_int]
        | ksd        => ty_tuple [ty_hv; ty_lv; ty_int]
        | kaddi      => ty_tuple [ty_lv; ty_hv; ty_int]
        | kadd       => ty_tuple [ty_lv; ty_lv; ty_lv]
        | ksub       => ty_tuple [ty_lv; ty_lv; ty_lv]
        | kslt       => ty_tuple [ty_lv; ty_lv; ty_lv]
        | kslti      => ty_tuple [ty_lv; ty_hv; ty_int]
        | ksltu      => ty_tuple [ty_lv; ty_lv; ty_lv]
        | ksltiu     => ty_tuple [ty_lv; ty_hv; ty_int]
        | klea       => ty_prod ty_lv ty_hv
        | krestrict  => ty_prod ty_lv ty_hv
        | krestricti => ty_prod ty_lv ty_int
        | ksubseg    => ty_tuple [ty_lv; ty_hv; ty_hv]
        | ksubsegi   => ty_tuple [ty_lv; ty_hv; ty_int]
        | kisptr     => ty_prod ty_lv ty_lv
        | kgetp      => ty_prod ty_lv ty_lv
        | kgetb      => ty_prod ty_lv ty_lv
        | kgete      => ty_prod ty_lv ty_lv
        | kgeta      => ty_prod ty_lv ty_lv
        | kfail      => ty_unit
        | kret       => ty_unit
        end
      end.

    Definition 𝑼_fold (U : 𝑼) : { K : 𝑼𝑲 U & Val (𝑼𝑲_Ty U K) } -> 𝑼𝑻 U :=
      match U with
      | instruction => fun Kv =>
        match Kv with
        | existT kjr       lv                          => jr lv
        | existT kjalr     (lv1 , lv2)                 => jalr lv1 lv2
        | existT kj        offset                      => j offset
        | existT kjal      (lv , offset)               => jal lv offset
        | existT kbnez     (lv , immediate)            => bnez lv immediate
        | existT kmv       (lv , hv)                   => mv lv hv
        | existT kld       (tt , lv , hv , immediate)  => ld lv hv immediate
        | existT ksd       (tt , hv , lv , immediate)  => sd hv lv immediate
        | existT kaddi     (tt , lv , hv , immediate)  => addi lv hv immediate
        | existT kadd      (tt , lv1 , lv2 , lv3)      => add lv1 lv2 lv3
        | existT ksub      (tt , lv1 , lv2 , lv3)      => sub lv1 lv2 lv3
        | existT kslt      (tt , lv1 , lv2 , lv3)      => slt lv1 lv2 lv3
        | existT kslti     (tt , lv , hv , immediate)  => slti lv hv immediate
        | existT ksltu     (tt , lv1 , lv2 , lv3)      => sltu lv1 lv2 lv3
        | existT ksltiu    (tt , lv , hv , immediate)  => sltiu lv hv immediate
        | existT klea      (lv , hv)                   => lea lv hv
        | existT krestrict (lv , hv)                   => restrict lv hv
        | existT krestricti (lv , immediate)           => restricti lv immediate
        | existT ksubseg   (tt , lv , hv1 , hv2)       => subseg lv hv1 hv2
        | existT ksubsegi  (tt , lv , hv  , immediate) => subsegi lv hv immediate
        | existT kisptr    (lv , lv')                  => isptr lv lv'
        | existT kgetp     (lv , lv')                  => getp lv lv'
        | existT kgetb     (lv , lv')                  => getb lv lv'
        | existT kgete     (lv , lv')                  => gete lv lv'
        | existT kgeta     (lv , lv')                  => geta lv lv'
        | existT kfail     tt                          => fail
        | existT kret      tt                          => ret
        end
      end.
    Definition 𝑼_unfold (U : 𝑼) : 𝑼𝑻 U -> { K : 𝑼𝑲 U & Val (𝑼𝑲_Ty U K) } :=
      match U as u return (𝑼𝑻 u -> {K : 𝑼𝑲 u & Val (𝑼𝑲_Ty u K)}) with
      | instruction => fun Kv =>
        match Kv with
        | jr  lv                   => existT kjr        lv
        | jalr lv1 lv2             => existT kjalr      (lv1 , lv2)
        | j offset                 => existT kj         offset
        | jal lv offset            => existT kjal       (lv , offset)
        | bnez lv immediate        => existT kbnez      (lv , immediate)
        | mv lv hv                 => existT kmv        (lv , hv)
        | ld lv hv immediate       => existT kld        (tt , lv , hv , immediate)
        | sd hv lv immediate       => existT ksd        (tt , hv , lv , immediate)
        | addi lv hv immediate     => existT kaddi      (tt , lv , hv , immediate)
        | add lv1 lv2 lv3          => existT kadd       (tt , lv1 , lv2 , lv3)
        | sub lv1 lv2 lv3          => existT ksub       (tt , lv1 , lv2 , lv3)
        | slt lv1 lv2 lv3          => existT kslt       (tt , lv1 , lv2 , lv3)
        | slti lv hv immediate     => existT kslti      (tt , lv , hv , immediate)
        | sltu lv1 lv2 lv3         => existT ksltu      (tt , lv1 , lv2 , lv3)
        | sltiu lv hv immediate    => existT ksltiu     (tt , lv , hv , immediate)
        | lea lv hv                => existT klea       (lv , hv)
        | restrict lv hv           => existT krestrict  (lv , hv)
        | restricti lv immediate   => existT krestricti (lv , immediate)
        | subseg lv hv1 hv2        => existT ksubseg    (tt, lv , hv1 , hv2)
        | subsegi lv hv immediate  => existT ksubsegi   (tt, lv , hv , immediate)
        | isptr lv lv'             => existT kisptr     (lv , lv')
        | getp lv lv'              => existT kgetp      (lv , lv')
        | getb lv lv'              => existT kgetb      (lv , lv')
        | gete lv lv'              => existT kgete      (lv , lv')
        | geta lv lv'              => existT kgeta      (lv , lv')
        | fail                     => existT kfail      tt
        | ret                      => existT kret       tt
        end
      end.
    Lemma 𝑼_fold_unfold : forall (U : 𝑼) (Kv: 𝑼𝑻 U),
        𝑼_fold U (𝑼_unfold U Kv) = Kv.
    Proof. now intros [] []. Qed.
    Lemma 𝑼_unfold_fold : forall (U : 𝑼) (Kv: { K : 𝑼𝑲 U & Val (𝑼𝑲_Ty U K) }),
        𝑼_unfold U (𝑼_fold U Kv) = Kv.
    Proof.
      intros [] [[] x]; cbn in x;
        repeat match goal with
               | x: unit     |- _ => destruct x
               | x: prod _ _ |- _ => destruct x
               end; auto.
    Qed.

    (** RECORDS **)
    Local Open Scope string_scope.
    Definition 𝑹𝑭  : Set := string.

    Definition 𝑹𝑭_Ty (R : 𝑹) : NCtx 𝑹𝑭 Ty :=
      match R with
      | capability => [ "cap_permission" ∷ ty_perm;
                        "cap_begin"      ∷ ty_addr;
                        "cap_end"        ∷ ty_addr;
                        "cap_cursor"     ∷ ty_addr
                      ]
      end.

    Definition 𝑹_fold (R : 𝑹) : NamedEnv Val (𝑹𝑭_Ty R) -> 𝑹𝑻 R :=
      match R with
      | capability =>
        fun fields =>
          MkCap
            fields.[??"cap_permission"]
            fields.[??"cap_begin"]
            fields.[??"cap_end"]
            fields.[??"cap_cursor"]
      end%exp.

    Definition 𝑹_unfold (R : 𝑹) : 𝑹𝑻 R -> NamedEnv Val (𝑹𝑭_Ty R) :=
      match R  with
      | capability =>
        fun c=>
          env.nil
            ► ("cap_permission" ∷ ty_perm ↦ cap_permission c)
            ► ("cap_begin"      ∷ ty_addr ↦ cap_begin c)
            ► ("cap_end"        ∷ ty_addr ↦ cap_end c)
            ► ("cap_cursor"     ∷ ty_addr ↦ cap_cursor c)
      end%env.
    Lemma 𝑹_fold_unfold : forall (R : 𝑹) (Kv: 𝑹𝑻 R),
        𝑹_fold R (𝑹_unfold R Kv) = Kv.
    Proof. now intros [] []. Qed.
    Lemma 𝑹_unfold_fold : forall (R : 𝑹) (Kv: NamedEnv Val (𝑹𝑭_Ty R)),
        𝑹_unfold R (𝑹_fold R Kv) = Kv.
    Proof. intros []; now apply env.Forall_forall. Qed.

  End TypeDefKit.

  Section RegDeclKit.

    Inductive Reg : Ty -> Set :=
    | pc   : Reg ty_cap
    | reg0 : Reg ty_word
    | reg1 : Reg ty_word
    | reg2 : Reg ty_word
    | reg3 : Reg ty_word.

    Section TransparentObligations.
      Local Set Transparent Obligations.
      Derive Signature NoConfusion for Reg.
    End TransparentObligations.

    Definition 𝑹𝑬𝑮 : Ty -> Set := Reg.
    Instance 𝑹𝑬𝑮_eq_dec : EqDec (sigT Reg).
    Proof.
      intros [? []] [? []]; cbn;
        first
          [ left; now apply eq_refl
          | right; intros e; dependent elimination e
          ].
    Defined.

    Local Obligation Tactic :=
      finite_from_eqdec.

    Program Instance 𝑹𝑬𝑮_finite : Finite (sigT Reg) :=
      {| enum := [ existT _ pc; existT _ reg0; existT _ reg1; existT _ reg2; existT _ reg3 ] |}.

  End RegDeclKit.

  Include BaseMixin.

End MinCapsBase.
