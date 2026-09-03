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
(* Results.v — aggregator for the concrete end-to-end noninterference        *)
(* theorems.                                                                 *)
(*                                                                           *)
(* The theorems themselves live one per program in Example/<Prog>Result.v;   *)
(* this file only re-exports them, so the merge gate keeps a single build     *)
(* target whose closure is every result (scripts/gate.sh runs Print          *)
(* Assumptions on each theorem after requiring this file).                   *)
(*                                                                           *)
(* Why the theorems are NOT in Example/<Prog>.v: a result file requires      *)
(* EndToEnd (and so Adequacy), an 85 s chain. Keeping it out of the examples  *)
(* lets that chain build in PARALLEL with them rather than ahead of all of    *)
(* them — worth ~40 s of wall time on a -j2 gate build.                      *)
(*                                                                           *)
(* Together with Noninterference.v and the per-example instruction/spec       *)
(* definitions, these statements are the trusted surface of CFGVer: what they *)
(* assert can be audited without reading the verifier or the proofs.         *)
(* ========================================================================= *)

(* Verifier is deliberately a bare `Require` (no Import): Importing it clashes
   with BlockVer's identically-named definitions. See CFGVer/CLAUDE.md. *)
From Katamaran Require
     RiscvPmp.CFGVer.Verifier.

From Katamaran Require Export
     RiscvPmp.CFGVer.Noninterference
     RiscvPmp.CFGVer.Tables
     RiscvPmp.CFGVer.Contracts
     RiscvPmp.CFGVer.GenContract
     RiscvPmp.CFGVer.Adequacy
     RiscvPmp.CFGVer.EndToEnd.

(* The 25 end-to-end theorems, one file per program. *)
From Katamaran Require Export
     RiscvPmp.CFGVer.Example.MvSwapResult
     RiscvPmp.CFGVer.Example.JumpsResult
     RiscvPmp.CFGVer.Example.CountdownResult
     RiscvPmp.CFGVer.Example.SetX2Result
     RiscvPmp.CFGVer.Example.Cmovznz4Result
     RiscvPmp.CFGVer.Example.PrecomputeResult
     RiscvPmp.CFGVer.Example.KeyScheduleLoopResult
     RiscvPmp.CFGVer.Example.BearSSLMuladdResult
     RiscvPmp.CFGVer.Example.BearSSLModpowResult
     RiscvPmp.CFGVer.Example.BearSSLModpowFullResult
     RiscvPmp.CFGVer.Example.BearSSLCheckScalarResult
     RiscvPmp.CFGVer.Example.BearSSLCheckScalarLoop1Result
     RiscvPmp.CFGVer.Example.SwapComposedResult.
