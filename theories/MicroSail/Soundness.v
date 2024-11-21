(******************************************************************************)
(* Copyright (c) 2020 Dominique Devriese, Sander Huyghebaert, Steven Keuchel  *)
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

From Katamaran Require Import
  Signature
  Sep.Hoare
  Specification
  Prelude
  Program
  Refinement.MonadInstances
  MicroSail.ShallowVCGen
  MicroSail.SymbolicVCGen
  MicroSail.RefineExecutor
  MicroSail.RefineVCGen
  MicroSail.ShallowSoundness.

Module MakeSoundness
  (Import B : Base)
  (Import SIG : Signature B)
  (Import SOLV : SolverKit B SIG)
  (Import PROG : Program B)
  (Import SPEC : Specification B SIG PROG)
  (Import CVCG : ShallowVCGen B SIG PROG SPEC)
  (Import SVCG : SymbolicVCGen B SIG SOLV PROG SPEC).

  Include ProgramLogicOn B SIG PROG SPEC.
  Include VCGenSoundnessOn B SIG PROG SPEC CVCG.
  Include RefinementMonadInstancesOn B SIG SOLV CVCG SVCG.
  Include RefineExecutorOn B SIG PROG CVCG SVCG.
  Include RefineVCGenOn B SIG PROG SPEC CVCG SOLV SVCG.

End MakeSoundness.
