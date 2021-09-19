(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel, Dominique Devriese, Sander Huyghebaert  *)
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

From MicroSail Require Import
     Notation
     Syntax.Values.

From RiscvPmp Require Export
     Types.

Set Implicit Arguments.
Import CtxNotations.

Module RiscvPmpValueKit <: ValueKit.
  Module typekit := RiscvPmpTypeKit.
  Module Export TY := Syntax.Types.Types typekit.

  Notation ty_regidx := (ty_enum regidx).
  Notation ty_rop    := (ty_union rop).

  Definition 𝑼𝑲_Ty (U : 𝑼) : 𝑼𝑲 U -> Ty :=
    match U with
    | rop => fun K =>
               match K with
               | KRISCV_ADD => ty_unit
               end
    | ast => fun K =>
               match K with
               | KRTYPE => ty_tuple [ty_regidx, ty_regidx, ty_regidx, ty_rop]
               end
    end.

  (* TODO: something goes wrong here when using existT in different match clauses? *)
  Definition 𝑼_fold (U : 𝑼) : { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty U K) } -> 𝑼𝑻 U :=
    match U with
    | rop => fun Kv =>
               (* match Kv with
               | existT KRISCV_ADD tt => RISCV_ADD
               end *)
               RISCV_ADD
    | ast => fun Kv =>
               (* match Kv with
               | existT KRTYPE (rs2 , rs1 , rd , rop) => RTYPE rs2 rs1 rd rop
               end *)
               RTYPE X1 X1 X2 RISCV_ADD
    end.
End RiscvPmpValueKit.
