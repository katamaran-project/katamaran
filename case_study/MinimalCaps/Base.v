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
Require Import Katamaran.Base.

(*** TYPES ***)

Inductive Permission : Set :=
  O | R | RW | E.

Inductive RegName : Set :=
  R0 | R1 | R2 | R3.

Definition LV : Set := RegName.
Definition HV : Set := RegName.
Definition RV : Set := LV + Z.

Inductive Instruction : Set :=
| jalr          (lv1 : LV) (lv2 : LV)
| jal           (lv : LV) (offset : Z)
| bne           (lv1 : LV) (lv2 : LV) (immediate : Z)
| cmove         (lv : LV) (hv : HV)
| ld            (lv : LV) (hv : HV) (immediate : Z)
| sd            (hv : HV) (lv : LV) (immediate : Z)
| addi          (lv : LV) (hv : HV) (immediate : Z)
| add           (lv1 : LV) (lv2 : LV) (lv3 : LV)
| sub           (lv1 : LV) (lv2 : LV) (lv3 : LV)
| slt           (lv1 : LV) (lv2 : LV) (lv3 : LV)
| slti          (lv : LV) (hv : HV) (immediate : Z)
| sltu          (lv1 : LV) (lv2 : LV) (lv3 : LV)
| sltiu         (lv : LV) (hv : HV) (immediate : Z)
| cincoffsetimm (lv : LV) (hv : HV)
| restrict      (lv : LV) (hv : HV)
| restricti     (lv : LV) (immediate : Z)
| csetbounds    (lv : LV) (hv1 hv2 : HV)
| csetboundsimm (lv : LV) (hv : HV) (immediate : Z)
| isptr         (lv : LV) (lv' : HV)
| cgetperm      (lv lv' : LV)
| cgetbase      (lv lv' : LV)
| cgetlen       (lv lv' : LV)
| cgetaddr      (lv lv' : LV)
| fail
| ret.

Inductive InstructionConstructor : Set :=
| kjalr
| kjal
| kbne
| kcmove
| kld
| ksd
| kaddi
| kadd
| ksub
| kslt
| kslti
| ksltu
| ksltiu
| kcincoffsetimm
| krestrict
| krestricti
| kcsetbounds
| kcsetboundsimm
| kisptr
| kcgetperm
| kcgetbase
| kcgetlen
| kcgetaddr
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

  #[export,program] Instance Permission_finite : Finite Permission :=
    {| enum := [O;R;RW;E] |}.

  #[export,program] Instance RegName_finite : Finite RegName :=
    {| enum := [R0;R1;R2;R3] |}.

  #[export,program] Instance InstructionConstructor_finite :
    Finite InstructionConstructor :=
    {| enum := [kjalr;kjal;kbne;kcmove;kld;ksd;kcincoffsetimm;krestrict;krestricti;kcsetbounds;kcsetboundsimm;kisptr;kaddi;kadd;ksub;kslt;kslti;ksltu;ksltiu;kcgetperm;kcgetbase;kcgetlen;kcgetaddr;kfail;kret] |}.

End Finite.

Module Export MinCapsBase <: Base.
  Import ctx.notations.
  Import ctx.resolution.
  Import env.notations.
  Import stdpp.finite.

  Local Open Scope string_scope.

  #[export] Instance typedeclkit : TypeDeclKit :=
    {| enumi := Enums;
       unioni := Unions;
       recordi := Records;
    |}.

  Notation "ty.hv" := (ty.enum regname).
  Notation "ty.lv" := (ty.enum regname).
  Notation "ty.rv" := (ty.sum (ty.enum regname) ty.int).
  Notation "ty.cap" := (ty.record capability).
  Notation "ty.word" := (ty.sum ty.int ty.cap).
  Notation "ty.memval" := (ty.word).
  Notation "ty.addr" := (ty.int).
  Notation "ty.perm" := (ty.enum permission).
  Notation "ty.instr" := (ty.union instruction).

  Definition enum_denote (e : Enums) : Set :=
    match e with
    | permission => Permission
    | regname    => RegName
    end.

  Definition union_denote (U : Unions) : Set :=
    match U with
    | instruction => Instruction
    end.

  Definition record_denote (R : Records) : Set :=
    match R with
    | capability => Capability
    end.

  #[export] Instance typedenotekit : TypeDenoteKit typedeclkit :=
    {| enumt := enum_denote;
       uniont := union_denote;
       recordt := record_denote;
    |}.

  Definition union_constructor (U : Unions) : Set :=
    match U with
    | instruction => InstructionConstructor
    end.

  Definition union_constructor_type (U : Unions) : union_constructor U -> Ty :=
    match U with
    | instruction => fun K =>
      match K with
      | kjalr          => ty.prod ty.lv ty.lv
      | kjal           => ty.prod ty.lv ty.int
      | kbne           => ty.tuple [ty.lv; ty.lv; ty.int]
      | kcmove         => ty.prod ty.lv ty.hv
      | kld            => ty.tuple [ty.lv; ty.hv; ty.int]
      | ksd            => ty.tuple [ty.hv; ty.lv; ty.int]
      | kaddi          => ty.tuple [ty.lv; ty.hv; ty.int]
      | kadd           => ty.tuple [ty.lv; ty.lv; ty.lv]
      | ksub           => ty.tuple [ty.lv; ty.lv; ty.lv]
      | kslt           => ty.tuple [ty.lv; ty.lv; ty.lv]
      | kslti          => ty.tuple [ty.lv; ty.hv; ty.int]
      | ksltu          => ty.tuple [ty.lv; ty.lv; ty.lv]
      | ksltiu         => ty.tuple [ty.lv; ty.hv; ty.int]
      | kcincoffsetimm => ty.prod ty.lv ty.hv
      | krestrict      => ty.prod ty.lv ty.hv
      | krestricti     => ty.prod ty.lv ty.int
      | kcsetbounds    => ty.tuple [ty.lv; ty.hv; ty.hv]
      | kcsetboundsimm => ty.tuple [ty.lv; ty.hv; ty.int]
      | kisptr         => ty.prod ty.lv ty.lv
      | kcgetperm      => ty.prod ty.lv ty.lv
      | kcgetbase      => ty.prod ty.lv ty.lv
      | kcgetlen       => ty.prod ty.lv ty.lv
      | kcgetaddr      => ty.prod ty.lv ty.lv
      | kfail          => ty.unit
      | kret           => ty.unit
      end
    end.

  #[export] Instance eqdec_enum_denote E : EqDec (enum_denote E) :=
    ltac:(destruct E; auto with typeclass_instances).
  #[export] Instance finite_enum_denote E : finite.Finite (enum_denote E) :=
    ltac:(destruct E; auto with typeclass_instances).
  #[export] Instance eqdec_union_denote U : EqDec (union_denote U) :=
    ltac:(destruct U; cbn; auto with typeclass_instances).
  #[export] Instance eqdec_union_constructor U : EqDec (union_constructor U) :=
    ltac:(destruct U; cbn; auto with typeclass_instances).
  #[export] Instance finite_union_constructor U : finite.Finite (union_constructor U) :=
    ltac:(destruct U; cbn; auto with typeclass_instances).
  #[export] Instance eqdec_record_denote R : EqDec (record_denote R) :=
    ltac:(destruct R; auto with typeclass_instances).

  Definition union_fold (U : unioni) : { K & Val (union_constructor_type U K) } -> uniont U :=
    match U with
    | instruction => fun Kv =>
      match Kv with
      | existT kjalr     (lv1 , lv2)                       => jalr lv1 lv2
      | existT kjal      (lv , offset)                     => jal lv offset
      | existT kbne      (tt , lv1 , lv2 , immediate)      => bne lv1 lv2 immediate
      | existT kcmove    (lv , hv)                         => cmove lv hv
      | existT kld       (tt , lv , hv , immediate)        => ld lv hv immediate
      | existT ksd       (tt , hv , lv , immediate)        => sd hv lv immediate
      | existT kaddi     (tt , lv , hv , immediate)        => addi lv hv immediate
      | existT kadd      (tt , lv1 , lv2 , lv3)            => add lv1 lv2 lv3
      | existT ksub      (tt , lv1 , lv2 , lv3)            => sub lv1 lv2 lv3
      | existT kslt      (tt , lv1 , lv2 , lv3)            => slt lv1 lv2 lv3
      | existT kslti     (tt , lv , hv , immediate)        => slti lv hv immediate
      | existT ksltu     (tt , lv1 , lv2 , lv3)            => sltu lv1 lv2 lv3
      | existT ksltiu    (tt , lv , hv , immediate)        => sltiu lv hv immediate
      | existT kcincoffsetimm (lv , hv)                    => cincoffsetimm lv hv
      | existT krestrict (lv , hv)                         => restrict lv hv
      | existT krestricti (lv , immediate)                 => restricti lv immediate
      | existT kcsetbounds (tt , lv , hv1 , hv2)           => csetbounds lv hv1 hv2
      | existT kcsetboundsimm  (tt , lv , hv , immediate)  => csetboundsimm lv hv immediate
      | existT kisptr    (lv , lv')                        => isptr lv lv'
      | existT kcgetperm (lv , lv')                        => cgetperm lv lv'
      | existT kcgetbase (lv , lv')                        => cgetbase lv lv'
      | existT kcgetlen  (lv , lv')                        => cgetlen lv lv'
      | existT kcgetaddr (lv , lv')                        => cgetaddr lv lv'
      | existT kfail     tt                                => fail
      | existT kret      tt                                => ret
      end
    end.

  Definition union_unfold (U : unioni) : uniont U -> { K & Val (union_constructor_type U K) } :=
    match U with
    | instruction => fun Kv =>
      match Kv with
      | jalr lv1 lv2                  => existT kjalr      (lv1 , lv2)
      | jal lv offset                 => existT kjal       (lv , offset)
      | bne lv1 lv2 immediate         => existT kbne       (tt , lv1 , lv2 , immediate)
      | cmove lv hv                   => existT kcmove     (lv , hv)
      | ld lv hv immediate            => existT kld        (tt , lv , hv , immediate)
      | sd hv lv immediate            => existT ksd        (tt , hv , lv , immediate)
      | addi lv hv immediate          => existT kaddi      (tt , lv , hv , immediate)
      | add lv1 lv2 lv3               => existT kadd       (tt , lv1 , lv2 , lv3)
      | sub lv1 lv2 lv3               => existT ksub       (tt , lv1 , lv2 , lv3)
      | slt lv1 lv2 lv3               => existT kslt       (tt , lv1 , lv2 , lv3)
      | slti lv hv immediate          => existT kslti      (tt , lv , hv , immediate)
      | sltu lv1 lv2 lv3              => existT ksltu      (tt , lv1 , lv2 , lv3)
      | sltiu lv hv immediate         => existT ksltiu     (tt , lv , hv , immediate)
      | cincoffsetimm lv hv           => existT kcincoffsetimm (lv , hv)
      | restrict lv hv                => existT krestrict  (lv , hv)
      | restricti lv immediate        => existT krestricti (lv , immediate)
      | csetbounds lv hv1 hv2         => existT kcsetbounds (tt, lv , hv1 , hv2)
      | csetboundsimm lv hv immediate => existT kcsetboundsimm (tt, lv , hv , immediate)
      | isptr lv lv'                  => existT kisptr     (lv , lv')
      | cgetperm lv lv'               => existT kcgetperm  (lv , lv')
      | cgetbase lv lv'               => existT kcgetbase  (lv , lv')
      | cgetlen lv lv'                => existT kcgetlen   (lv , lv')
      | cgetaddr lv lv'               => existT kcgetaddr  (lv , lv')
      | fail                          => existT kfail      tt
      | ret                           => existT kret       tt
      end
    end.

  Definition record_field_type (R : recordi) : NCtx string Ty :=
    match R with
    | capability => [ "cap_permission" ∷ ty.perm;
                      "cap_begin"      ∷ ty.addr;
                      "cap_end"        ∷ ty.addr;
                      "cap_cursor"     ∷ ty.addr
                    ]
    end.

  Definition record_fold (R : recordi) : NamedEnv Val (record_field_type R) -> recordt R :=
    match R with
    | capability =>
      fun fields =>
        MkCap
          fields.[??"cap_permission"]
          fields.[??"cap_begin"]
          fields.[??"cap_end"]
          fields.[??"cap_cursor"]
    end%exp.

  Definition record_unfold (R : recordi) : recordt R -> NamedEnv Val (record_field_type R) :=
    match R  with
    | capability =>
      fun c=>
        env.nil
          ► ("cap_permission" ∷ ty.perm ↦ cap_permission c)
          ► ("cap_begin"      ∷ ty.addr ↦ cap_begin c)
          ► ("cap_end"        ∷ ty.addr ↦ cap_end c)
          ► ("cap_cursor"     ∷ ty.addr ↦ cap_cursor c)
    end%env.

  #[export,refine] Instance typedefkit : TypeDefKit typedenotekit :=
    {| unionk           := union_constructor;
       unionk_ty        := union_constructor_type;
       recordf          := string;
       recordf_ty       := record_field_type;
       unionv_fold      := union_fold;
       unionv_unfold    := union_unfold;
       recordv_fold     := record_fold;
       recordv_unfold   := record_unfold;
    |}.
  Proof.
    - abstract (now intros [] []).
    - abstract (intros [] [[] x]; cbn in x;
                repeat
                  match goal with
                  | x: unit     |- _ => destruct x
                  | x: prod _ _ |- _ => destruct x
                  end; auto).
    - abstract (now intros [] []).
    - abstract (intros []; now apply env.Forall_forall).
  Defined.

  Canonical typedeclkit.
  Canonical typedenotekit.
  Canonical typedefkit.

  #[export] Instance varkit : VarKit := DefaultVarKit.

  Section RegDeclKit.

    Inductive Reg : Ty -> Set :=
    | pc   : Reg ty.cap
    | reg0 : Reg ty.word
    | reg1 : Reg ty.word
    | reg2 : Reg ty.word
    | reg3 : Reg ty.word.

    Section TransparentObligations.
      Local Set Transparent Obligations.
      Derive Signature NoConfusion NoConfusionHom EqDec for Reg.
    End TransparentObligations.

    Definition 𝑹𝑬𝑮 : Ty -> Set := Reg.
    #[export] Instance 𝑹𝑬𝑮_eq_dec : EqDec (sigT Reg) :=
      sigma_eqdec _ _.

    Local Obligation Tactic :=
      finite_from_eqdec.

    #[export,program] Instance 𝑹𝑬𝑮_finite : Finite (sigT Reg) :=
      {| enum := [ existT _ pc; existT _ reg0; existT _ reg1; existT _ reg2; existT _ reg3 ] |}.

  End RegDeclKit.

  Include BaseMixin.

End MinCapsBase.
