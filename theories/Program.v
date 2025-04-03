(******************************************************************************)
(* Copyright (c) 2019 Dominique Devriese, Georgy Lukyanov,                    *)
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

From Katamaran Require Export
     Syntax.FunDecl
     Syntax.FunDef
     Syntax.Statements
     Base.

Module Type FunDeclMixin (B : Base) :=
  StatementsOn B.

Module Type ProgramMixin (B : Base)
  (Import FDecl : FunDecl B)
  (Import FDK : FunDefKit B FDecl).

  Definition InvokedByFun {Δ1 τ1} {Δ2 τ2} (f1 : 𝑭 Δ1 τ1) (f2 : 𝑭 Δ2 τ2) :=
    InvokedByStm f1 (FunDef f2).
  Definition InvokedByFunPackage (f1 f2 : {Δ & {τ & 𝑭 Δ τ}}) :=
    match f1, f2 with
    | existT Δ1 (existT τ1 f1) ,  existT Δ2 (existT τ2 f2) => InvokedByFun f1 f2
    end.
End ProgramMixin.

Module Type Program (B : Base) :=
  FunDeclKit B <+ FunDeclMixin B <+ FunDefKit B <+ ProgramMixin B.
