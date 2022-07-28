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

From Katamaran Require Import
     Base
     Iris.Instance
     Iris.Model
     Syntax.Predicates
     RiscvPmp.Base
     RiscvPmp.Machine
     RiscvPmp.IrisModel
     RiscvPmp.Sig.

From iris.base_logic Require Import invariants lib.iprop lib.gen_heap.
From iris.proofmode Require Import tactics.

Set Implicit Arguments.

Module RiscvPmpIrisInstance <:
  IrisInstance RiscvPmpBase RiscvPmpProgram RiscvPmpSemantics
    RiscvPmpSignature RiscvPmpIrisBase.
  Import RiscvPmpIrisBase.
  Import RiscvPmpProgram.

  Section WithSailGS.
    Context `{sailRegGS Σ} `{invGS Σ} `{mG : mcMemGS Σ}.

    Definition reg_file : gset (bv 3) := list_to_set (finite.enum (bv 3)).

    Definition interp_ptsreg `{sailRegGS Σ} (r : RegIdx) (v : Z) : iProp Σ :=
      match reg_convert r with
      | Some x => reg_pointsTo x v
      | None => True
      end.

    Definition interp_gprs : iProp Σ :=
      [∗ set] r ∈ reg_file, (∃ v, interp_ptsreg r v)%I.

    Definition PmpEntryCfg : Set := Pmpcfg_ent * Xlenbits.

    Definition interp_pmp_entries (entries : list PmpEntryCfg) : iProp Σ :=
      match entries with
      | (cfg0, addr0) :: (cfg1, addr1) :: [] =>
          reg_pointsTo pmp0cfg cfg0 ∗
                       reg_pointsTo pmpaddr0 addr0 ∗
                       reg_pointsTo pmp1cfg cfg1 ∗
                       reg_pointsTo pmpaddr1 addr1
      | _ => False
      end.

    Definition interp_ptsto (addr : Addr) (w : Word) : iProp Σ :=
      mapsto addr (DfracOwn 1) w.
    Definition ptstoSth : Addr -> iProp Σ := fun a => (∃ w, interp_ptsto a w)%I.
    Definition ptstoSthL : list Addr -> iProp Σ :=
      fun addrs => ([∗ list] k↦a ∈ addrs, ptstoSth a)%I.
    Lemma ptstoSthL_app {l1 l2} : (ptstoSthL (l1 ++ l2) ⊣⊢ ptstoSthL l1 ∗ ptstoSthL l2)%I.
    Proof. eapply big_sepL_app. Qed.

    Definition interp_pmp_addr_access (addrs : list Addr) (entries : list PmpEntryCfg) (m : Privilege) : iProp Σ :=
      [∗ list] a ∈ addrs,
        (⌜∃ p, Pmp_access a entries m p⌝ -∗ ptstoSth a)%I.

    Definition interp_pmp_addr_access_without (addr : Addr) (addrs : list Addr) (entries : list PmpEntryCfg) (m : Privilege) : iProp Σ :=
      (ptstoSth addr -∗ interp_pmp_addr_access addrs entries m)%I.

    Definition interp_ptsto_instr (addr : Z) (instr : AST) : iProp Σ :=
      (∃ v, interp_ptsto addr v ∗ ⌜ pure_decode v = inr instr ⌝)%I.

  End WithSailGS.

  Section RiscvPmpIrisPredicates.

    Definition luser_inst `{sailRegGS Σ, invGS Σ, mcMemGS Σ} (p : Predicate) : Env Val (𝑯_Ty p) -> iProp Σ :=
      match p return Env Val (𝑯_Ty p) -> iProp Σ with
      | pmp_entries                   => fun ts => interp_pmp_entries (env.head ts)
      | pmp_addr_access               => fun ts => interp_pmp_addr_access liveAddrs (env.head (env.tail ts)) (env.head ts)
      | pmp_addr_access_without       => fun ts => interp_pmp_addr_access_without (env.head (env.tail (env.tail ts))) liveAddrs (env.head (env.tail ts)) (env.head ts)
      | gprs                          => fun _  => interp_gprs
      | ptsto                         => fun ts => interp_ptsto (env.head (env.tail ts)) (env.head ts)
      | encodes_instr                 => fun _ => True%I
      | ptstomem                      => fun _ => True%I
      | ptstoinstr                    => fun ts  => interp_ptsto_instr (env.head (env.tail ts)) (env.head ts)%I
      end.

    Definition lduplicate_inst `{sailRegGS Σ, invGS Σ, mcMemGS Σ} :
      forall (p : Predicate) (ts : Env Val (𝑯_Ty p)),
        is_duplicable p = true ->
        (luser_inst p ts) ⊢ (luser_inst p ts ∗ luser_inst p ts).
    Proof.
      iIntros (p ts hdup) "H".
      destruct p; inversion hdup;
        iDestruct "H" as "#H";
        auto.
    Qed.

  End RiscvPmpIrisPredicates.

  Include IrisSignatureRules RiscvPmpBase RiscvPmpProgram RiscvPmpSemantics
    RiscvPmpSignature RiscvPmpIrisBase.

End RiscvPmpIrisInstance.
