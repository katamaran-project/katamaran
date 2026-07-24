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


(* ========================================================================= *)
(* Example/Prelude.v — the shared import preamble for CFGVer example files.  *)
(*                                                                           *)
(* Every Example/<Prog>.v opened with the SAME ~35-line Require/Import/Set   *)
(* block.  This module re-exports it, so a new example starts with just      *)
(*                                                                           *)
(*   From Katamaran Require Import RiscvPmp.CFGVer.Example.Prelude.          *)
(*                                                                           *)
(* Everything below is `Export`ed (not merely `Import`ed) so the effects     *)
(* reach the requiring example.                                              *)
(*                                                                           *)
(* NOTE on Verifier: examples deliberately Import it (unlike the Results.v   *)
(* aggregator, which keeps a bare `Require` to dodge the BlockVer name       *)
(* clash — see CFGVer/CLAUDE.md).  Example files never pull BlockVer in, so  *)
(* the Export here is safe for them.                                         *)
(* ========================================================================= *)

From Coq Require Export
     ZArith.ZArith
     Lists.List
     micromega.Lia
     Strings.String.
From Katamaran Require Export
     Notations
     Bitvector
     Semantics
     RiscvPmp.CFGVer.Spec
     RiscvPmp.Machine
     RiscvPmp.Sig.
From stdpp Require Export gmap.
From Katamaran Require Export
     RiscvPmp.CFGVer.Verifier
     RiscvPmp.CFGVer.Noninterference
     RiscvPmp.CFGVer.Tables
     RiscvPmp.CFGVer.Contracts
     RiscvPmp.CFGVer.GenContract.
From iris.proofmode Require Export string_ident tactics.

Export RiscvPmpProgram.

#[export] Set Implicit Arguments.
Export ctx.resolution.
Export ctx.notations.
Export bv.notations.
Export env.notations.
Export ListNotations.

Export RiscvPmpCFGVerifExecutor.
Export Assembly.
Export RiscvPmp.Sig.
Export iris.proofmode.tactics.
Export asn.notations.
Export TermNotations.
