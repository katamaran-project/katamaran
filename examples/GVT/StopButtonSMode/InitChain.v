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

From Stdlib Require Import
     ZArith.ZArith
     Lists.List
     Strings.String.
From Katamaran Require Import
     Base
     Bitvector
     SmallStep.Step
     RiscvPmp.GVT.PmpCheck
     RiscvPmp.GVT.Spec
     RiscvPmp.GVT.TotalVerifier
     RiscvPmp.GVT.IrisModel
     RiscvPmp.GVT.IrisInstance
     RiscvPmp.GVT.Machine
     RiscvPmp.GVT.Logic
     RiscvPmp.GVT.trace
     RiscvPmp.iostate
     RiscvPmp.GVT.Sig
     RiscvPmp.GVT.Target
     RiscvPmp.GVT.StopButtonSMode.Layout
     RiscvPmp.GVT.StopButtonSMode.Kernel.
From Katamaran Require
     RiscvPmp.GVT.Contracts
     RiscvPmp.GVT.LoopVerification
     RiscvPmp.GVT.Model.
From iris.base_logic Require lib.gen_heap lib.iprop invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac big_op.
From iris.program_logic Require weakestpre adequacy.
From iris.proofmode Require string_ident proofmode.
From stdpp Require namespaces.

Import RiscvPmpProgram.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import env.notations.
Import ListNotations.
Open Scope ctx_scope.

Import iris.program_logic.weakestpre.
Import iris.proofmode.proofmode.

Import MicroSail.ShallowExecutor.

Import RiscvPmp.GVT.Contracts.
Import RiscvPmpIrisPrelims RiscvPmpIrisBase.
Import RiscvPmpIrisInstancePredicates.
Import RiscvPmpIrisInstance.
Import RiscvPmpBlockVerifSpec.
Import RiscvPmpIrisInstanceWithContracts.
Import RiscvPmpShallowExec.

(* Block verification for the S-mode StopButton femtokernel: pre- and
   postconditions, verification conditions and Hoare triples per block.
   Block definitions, labels and addresses come from Kernel.v, the memory
   layout from Layout.v and Target.v.

   Done so far: the init chain (entry, init_block0, virtio_init, init_block1).
   Still to be ported from examples/GVT/StopButtonUMode.v: the handler blocks
   (Σ__csrs and CSRVals below are for those). *)

Section FemtoKernel.
  Import bv.notations.
  Import ListNotations.
  Import TermNotations.

  Open Scope hex_Z_scope.

  Local Notation "e1 ',ₜ' e2" := (term_binop bop.pair e1 e2) (at level 100).

    (* Shorthand for the pmp entries in both Katamaran and Iris *)
    Local Abbreviation asn_femto_pmpentries a :=
      ([(term_val ty_pmpcfg_ent femto_pmpcfg_ent0 ,ₜ (a +ᵇ term_val ty_xlenbits (bv.of_N adv_addr)));
        (term_val ty_pmpcfg_ent femto_pmpcfg_ent1 ,ₜ (term_val ty_xlenbits (bv.of_N adv_addr_end)));
        (term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ (term_val ty_xlenbits bv.zero));
        (term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ (term_val ty_xlenbits bv.zero));
        (term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ (term_val ty_xlenbits bv.zero));
        (term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ (term_val ty_xlenbits bv.zero));
        (term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ (term_val ty_xlenbits bv.zero));
        (term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ (term_val ty_xlenbits bv.zero));
        (term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ (term_val ty_xlenbits bv.zero));
        (term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ (term_val ty_xlenbits bv.zero));
        (term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ (term_val ty_xlenbits bv.zero));
        (term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ (term_val ty_xlenbits bv.zero));
        (term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ (term_val ty_xlenbits bv.zero));
        (term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ (term_val ty_xlenbits bv.zero));
        (term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ (term_val ty_xlenbits bv.zero));
        (term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ (term_val ty_xlenbits bv.zero))])%list.

    Definition pmp_cfg_to_term {Σ} : list PmpEntryCfg -> list (Term Σ (ty.prod ty_pmpcfg_ent ty_xlenbits)) :=
      let term_cfg cfg := term_val ty_pmpcfg_ent cfg in
      let term_addr a  := term_val ty_xlenbits a in
      map (fun '(cfg , addr) => term_binop bop.pair (term_cfg cfg) (term_addr addr)).

    Definition femto_pmpentries : list PmpEntryCfg :=
      [(femto_pmpcfg_ent0, bv.of_N adv_addr); (femto_pmpcfg_ent1, bv.of_N adv_addr_end);
       (default_pmpcfg_ent, bv.zero); (default_pmpcfg_ent, bv.zero); (default_pmpcfg_ent, bv.zero); (default_pmpcfg_ent, bv.zero);
       (default_pmpcfg_ent, bv.zero); (default_pmpcfg_ent, bv.zero); (default_pmpcfg_ent, bv.zero); (default_pmpcfg_ent, bv.zero);
       (default_pmpcfg_ent, bv.zero); (default_pmpcfg_ent, bv.zero); (default_pmpcfg_ent, bv.zero); (default_pmpcfg_ent, bv.zero);
       (default_pmpcfg_ent, bv.zero); (default_pmpcfg_ent, bv.zero)]%list.

    Definition term_femto_pmpentries {Σ} : Term Σ (ty.list (ty.prod ty_pmpcfg_ent ty_xlenbits)) :=
      term_list (pmp_cfg_to_term femto_pmpentries).

    (* PMP configuration as programmed by init_block0: the regions of
       Layout.v, all TOR, alternating RWX (0x0f) and R-X (0x0d); entries
       13..15 keep their reset value. *)
    Definition smode_cfg_rwx : Pmpcfg_ent := MkPmpcfg_ent false TOR true true true.
    Definition smode_cfg_rx  : Pmpcfg_ent := MkPmpcfg_ent false TOR true false true.
    Definition smode_pmpentries : list PmpEntryCfg :=
      [(smode_cfg_rwx, bv.of_N Layout.region0);  (smode_cfg_rx,  bv.of_N Layout.region1);
       (smode_cfg_rwx, bv.of_N Layout.region2);  (smode_cfg_rx,  bv.of_N Layout.region3);
       (smode_cfg_rwx, bv.of_N Layout.region4);  (smode_cfg_rx,  bv.of_N Layout.region5);
       (smode_cfg_rwx, bv.of_N Layout.region6);  (smode_cfg_rx,  bv.of_N Layout.region7);
       (smode_cfg_rwx, bv.of_N Layout.region8);  (smode_cfg_rx,  bv.of_N Layout.region9);
       (smode_cfg_rwx, bv.of_N Layout.region10); (smode_cfg_rx,  bv.of_N Layout.region11);
       (smode_cfg_rwx, bv.of_N Layout.region12);
       (default_pmpcfg_ent, bv.zero); (default_pmpcfg_ent, bv.zero); (default_pmpcfg_ent, bv.zero)]%list.

    Definition term_smode_pmpentries {Σ} : Term Σ (ty.list (ty.prod ty_pmpcfg_ent ty_xlenbits)) :=
      term_list (pmp_cfg_to_term smode_pmpentries).

    Import asn.notations.
    Import RiscvPmp.GVT.Sig.
    (* Fix word length at 4 for this example, as we do not perform any other writes*)
    Local Notation asn_mmio_trace_state_inv := (asn.chunk (chunk_user (mmio_state_trace bytes_per_word) [env])).
    Local Notation asn_mmio_state_pred s := (asn.chunk (chunk_user (mmio_state bytes_per_word) [s])).
    Local Notation asn_mmio_read_valid a s := (asn.formula (formula_user (mmio_read_valid bytes_per_word) [a; s])).
    Local Notation asn_mmio_event a v t s s' := (asn.formula (formula_user (mmio_event bytes_per_word) [a; v; t; s; s'])).

    Local Notation asn_pmp_addr_access l m := (asn.chunk (chunk_user pmp_addr_access [l; m])).
    Local Notation asn_pmp_entries l := (asn.chunk (chunk_user pmp_entries [l])).

    Definition post_mip_val : Val ty_Minterrupts :=
      MkMinterrupts false false false false false false false false false.
    Definition term_post_mip_val {Σ} : Term Σ ty_Minterrupts :=
      term_val ty_Minterrupts post_mip_val.

    Definition Σ__csrs : LCtx :=
      ["mtvec" :: ty_xlenbits;
       "mcause" :: ty_xlenbits;
       "mscratch" :: ty_xlenbits;
       "mepc" :: ty_xlenbits;
       "mie" :: ty_Minterrupts;
       "mip" :: ty_Minterrupts;
       "mstatus_mpie" :: ty.bool;
       "mstatus_mpp" :: ty_privilege;
       "mstatus_spp" :: ty_privilege;
       "mstatus_spie" :: ty.bool;
       "mstatus_sie" :: ty.bool;
       "mideleg" :: ty_Minterrupts;
       "medeleg" :: ty_Medeleg;
       "scause" :: ty_xlenbits;
       "sscratch" :: ty_xlenbits;
       "sepc" :: ty_xlenbits;
       "stvec" :: ty_xlenbits].

    Record CSRVals := mkCSRVals {
        vmtvec  : Val ty_xlenbits;
        vmcause : Val ty_xlenbits;
        vmscratch: Val ty_xlenbits;
        vmepc   : Val ty_xlenbits;
        vmie    : Val ty_Minterrupts;
        vmip    : Val ty_Minterrupts;
        vmstatus_mpie : Val ty.bool;
        vmstatus_mpp  : Val ty_privilege;
        vmstatus_spp  : Val ty_privilege;
        vmstatus_spie : Val ty.bool;
        vmstatus_sie  : Val ty.bool;
        vmideleg : Val ty_Minterrupts;
        vmedeleg : Val ty_Medeleg;
        vscause  : Val ty_xlenbits;
        vsscratch  : Val ty_xlenbits;
        vsepc  : Val ty_xlenbits;
        vstvec  : Val ty_xlenbits;
      }.

    Definition CSRVals_Valuation (vals : CSRVals) : Valuation Σ__csrs :=
      [env]
        .["mtvec" ∷ ty_xlenbits ↦ vmtvec vals]
        .["mcause" ∷ ty_xlenbits ↦ vmcause vals]
        .["mscratch" ∷ ty_xlenbits ↦ vmscratch vals]
        .["mepc" ∷ ty_xlenbits ↦ vmepc vals]
        .["mie" ∷ ty_Minterrupts ↦ vmie vals]
        .["mip" ∷ ty_Minterrupts ↦ vmip vals]
        .["mstatus_mpie" ∷ ty.bool ↦ vmstatus_mpie vals]
        .["mstatus_mpp" ∷ ty_privilege ↦ vmstatus_mpp vals]
        .["mstatus_spp" ∷ ty_privilege ↦ vmstatus_spp vals]
        .["mstatus_spie" ∷ ty.bool ↦ vmstatus_spie vals]
        .["mstatus_sie" ∷ ty.bool ↦ vmstatus_sie vals]
        .["mideleg" ∷ ty_Minterrupts ↦ vmideleg vals]
        .["medeleg" ∷ ty_Medeleg ↦ vmedeleg vals]
        .["scause" ∷ ty_xlenbits ↦ vscause vals]
        .["sscratch" ∷ ty_xlenbits ↦ vsscratch vals]
        .["sepc" ∷ ty_xlenbits ↦ vsepc vals]
        .["stvec" ∷ ty_xlenbits ↦ vstvec vals].

    (* ---------------------------------------------------------------------- *)
    (* Init chain                                                             *)
    (*   entry:       boot -> boot,  j init_block0                            *)
    (*   init_block0: boot -> mid,   jal virtio_init                          *)
    (*   virtio_init: mid  -> mid,   ret to init_block1                       *)
    (*   init_block1: mid  -> femtokernel_init_post (S-mode)                  *)
    (* Pre/postconditions only differ in where control is (a / an).           *)
    (* ---------------------------------------------------------------------- *)

    (* Boot state: what the hardware/loader guarantees at the entry point. *)
    Definition femtokernel_init_boot {Σ} : Assertion Σ :=
      (∃ "v", mtvec ↦ term_var "v") ∗
      (∃ "v", mcause ↦ term_var "v") ∗
      (mideleg ↦ term_val ty_Minterrupts Minterrupts_zero) ∗ (medeleg ↦ term_val ty_Medeleg Medeleg_zero) ∗
      (∃ "v", mip ↦ term_var "v") ∗ (∃ "v", mie ↦ term_var "v") ∗
      (∃ "v", mepc ↦ term_var "v") ∗
      (∃ "v", mscratch ↦ term_var "v") ∗
      (∃ "v", stvec ↦ term_var "v") ∗ (∃ "v", sepc ↦ term_var "v") ∗
      (∃ "v", scause ↦ term_var "v") ∗ (∃ "v", sscratch ↦ term_var "v") ∗
      mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_val ty_privilege User; term_val ty.bool false; term_val ty.bool false; term_val ty.bool false; term_val ty.bool false ] ∗
      cur_privilege ↦ term_val ty_privilege Machine ∗
      asn_regs_ptsto ∅ ∗
      (∃ "v", term_val ty_xlenbits (bv.of_N iostate_addr) ↦ₘ term_var "v") ∗
      (∃ "v", term_val ty_xlenbits (bv.of_N rx_used_seen_addr) ↦ₘ term_var "v") ∗
      asn_pmp_entries (term_list (repeat (term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ term_val ty_xlenbits bv.zero) 16)) ∗
      (* IO protocol: the trace invariant, and the protocol starts in SGo (0) *)
      asn_mmio_trace_state_inv ∗
      asn_mmio_state_pred (term_val ty_iostate bv.zero).

    (* Everything init_block0 establishes apart from the general-purpose
       registers and the PMP entries. Shared by the states inside the block
       and by mid. *)
    Definition femtokernel_init_csrs {Σ} : Assertion Σ :=
      (mtvec ↦ term_val ty_xlenbits (bv.of_N handler_block0_addr)) ∗
      (∃ "v", mcause ↦ term_var "v") ∗
      (mideleg ↦ term_val ty_Minterrupts Minterrupts_zero) ∗ (medeleg ↦ term_val ty_Medeleg Medeleg_zero) ∗
      (∃ "v", mip ↦ term_var "v") ∗ (∃ "v", mie ↦ term_var "v") ∗
      (∃ "v", mepc ↦ term_var "v") ∗
      (mscratch ↦ term_val ty_xlenbits (bv.of_N kernel_stack_top_addr)) ∗
      (∃ "v", stvec ↦ term_var "v") ∗ (∃ "v", sepc ↦ term_var "v") ∗
      (∃ "v", scause ↦ term_var "v") ∗ (∃ "v", sscratch ↦ term_var "v") ∗
      mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_val ty_privilege User; term_val ty.bool false; term_val ty.bool false; term_val ty.bool false; term_val ty.bool false ] ∗
      cur_privilege ↦ term_val ty_privilege Machine ∗
      term_val ty_xlenbits (bv.of_N iostate_addr) ↦ₘ term_val ty_word bv.zero ∗  (* iostate = SGo *)
      (∃ "v", term_val ty_xlenbits (bv.of_N rx_used_seen_addr) ↦ₘ term_var "v") ∗
      (* IO protocol: still in SGo, in step with the iostate word *)
      asn_mmio_trace_state_inv ∗
      asn_mmio_state_pred (term_val ty_iostate bv.zero).

    (* The PMP entries after the first k of the four pmpcfg groups; each group
       covers four entries. k = 4 is the full configuration. *)
    Definition smode_pmpentries_upto (k : nat) : list PmpEntryCfg :=
      firstn (4 * k) smode_pmpentries
      ++ skipn (4 * k) (repeat (default_pmpcfg_ent, bv.zero) 16).
    Definition term_smode_pmpentries_upto {Σ} (k : nat) :
      Term Σ (ty.list (ty.prod ty_pmpcfg_ent ty_xlenbits)) :=
      term_list (pmp_cfg_to_term (smode_pmpentries_upto k)).

    (* State inside init_block0: k pmpcfg groups written, ra not set yet (the
       jal at the end of the block does that). *)
    Definition femtokernel_init_setup {Σ} (k : nat) : Assertion Σ :=
      femtokernel_init_csrs ∗
      asn_regs_ptsto {[x2]} ∗
      x2 ↦ term_val ty_xlenbits (bv.of_N kernel_stack_top_addr) ∗     (* sp *)
      asn_pmp_entries (term_smode_pmpentries_upto k).

    (* Kernel set up: established by init_block0, preserved by virtio_init,
       completed by init_block1. *)
    Definition femtokernel_init_mid {Σ} : Assertion Σ :=
      femtokernel_init_csrs ∗
      asn_regs_ptsto {[x1; x2]} ∗
      x1 ↦ term_val ty_xlenbits (bv.of_N init_block1_addr) ∗          (* ra: return from virtio_init *)
      x2 ↦ term_val ty_xlenbits (bv.of_N kernel_stack_top_addr) ∗     (* sp *)
      asn_pmp_entries term_smode_pmpentries.

    (* ---- states inside init_block1 ------------------------------------- *)
    (* init_block1 moves three CSRs that it also reads back: mie (two csrs),
       mstatus (csrc then csrs) and the delegation registers (one csrw each).
       The model's CSR write does not normalise its result to a literal
       record, so a second read-modify-write on the same register squares the
       term and the VC explodes: vc__init1_prefix 16 is 6.5s, 17 -- the
       second csrs mie -- does not finish. Cutting after each such write and
       naming the value here forces the term back to a constant, exactly as
       femtokernel_init_setup does for the PMP entries.

       A CSR only has to be concrete in the piece that reads it. Nothing
       after the delegation writes reads mideleg or medeleg, so deleg_set
       switches them to existential instead of naming the record for
       0xfffff57f. Of mstatus only MPP changes, hence the single mpp
       parameter. *)
    Definition femtokernel_init1_csrs {Σ} (mie_val : Val ty_Minterrupts)
      (deleg_set : bool) (mpp : Val ty_privilege) : Assertion Σ :=
      (mtvec ↦ term_val ty_xlenbits (bv.of_N handler_block0_addr)) ∗
      (∃ "v", mcause ↦ term_var "v") ∗
      (if deleg_set
       then (∃ "v", mideleg ↦ term_var "v") ∗ (∃ "v", medeleg ↦ term_var "v")
       else (mideleg ↦ term_val ty_Minterrupts Minterrupts_zero) ∗ (medeleg ↦ term_val ty_Medeleg Medeleg_zero)) ∗
      (∃ "v", mip ↦ term_var "v") ∗ (mie ↦ term_val ty_Minterrupts mie_val) ∗
      (∃ "v", mepc ↦ term_var "v") ∗
      (mscratch ↦ term_val ty_xlenbits (bv.of_N kernel_stack_top_addr)) ∗
      (∃ "v", stvec ↦ term_var "v") ∗ (∃ "v", sepc ↦ term_var "v") ∗
      (∃ "v", scause ↦ term_var "v") ∗ (∃ "v", sscratch ↦ term_var "v") ∗
      mstatus ↦ term_record rmstatus [nenv term_val ty_privilege mpp; term_val ty_privilege User; term_val ty.bool false; term_val ty.bool false; term_val ty.bool false; term_val ty.bool false ] ∗
      cur_privilege ↦ term_val ty_privilege Machine ∗
      term_val ty_xlenbits (bv.of_N iostate_addr) ↦ₘ term_val ty_word bv.zero ∗
      (∃ "v", term_val ty_xlenbits (bv.of_N rx_used_seen_addr) ↦ₘ term_var "v") ∗
      asn_mmio_trace_state_inv ∗
      asn_mmio_state_pred (term_val ty_iostate bv.zero).

    Definition femtokernel_init1_state {Σ} (mie_val : Val ty_Minterrupts)
      (deleg_set : bool) (mpp : Val ty_privilege) : Assertion Σ :=
      femtokernel_init1_csrs mie_val deleg_set mpp ∗
      asn_regs_ptsto {[x1; x2]} ∗
      x1 ↦ term_val ty_xlenbits (bv.of_N init_block1_addr) ∗
      x2 ↦ term_val ty_xlenbits (bv.of_N kernel_stack_top_addr) ∗
      asn_pmp_entries term_smode_pmpentries.

    (* mie bit positions in Minterrupts: USI 0, SSI 1, MSI 3, UTI 4, STI 5,
       MTI 7, UEI 8, SEI 9, MEI 11; field order MEI SEI UEI MTI STI UTI MSI
       SSI USI. *)
    Definition mie_init_s : Val ty_Minterrupts :=      (* 0xa88: MSIE | MTIE | SEIE | MEIE *)
      MkMinterrupts true true false true false false true false false.

    Definition init_pre_at (addr : N) (P : ∀ Σ, Assertion Σ) : Assertion ["a"::ty_xlenbits] :=
      (term_var "a" = term_val ty_xlenbits (bv.of_N addr))%asn ∗ P _.
    Definition init_post_to (next : N) (P : ∀ Σ, Assertion Σ) : Assertion ["a"::ty_xlenbits; "an"::ty_xlenbits] :=
      (term_var "an" = term_val ty_xlenbits (bv.of_N next))%asn ∗ P _.

    Example femtokernel_entry_pre        := init_pre_at  entry_addr       (@femtokernel_init_boot).
    Example femtokernel_entry_post       := init_post_to init_block0_addr (@femtokernel_init_boot).
    (* init_block0 is cut before the first PMP write and after each pmpcfg
       write; see Layer 1 below. *)
    Definition init0a2_addr : N := Eval compute in (init_block0_addr + 4 * 10)%N.
    Definition init0b_addr : N := Eval compute in (init_block0_addr + 4 * 23)%N.
    Definition init0c_addr : N := Eval compute in (init_block0_addr + 4 * 37)%N.
    Definition init0d_addr : N := Eval compute in (init_block0_addr + 4 * 49)%N.

    Example femtokernel_init0a_pre       := init_pre_at  init_block0_addr (@femtokernel_init_boot).
    Example femtokernel_init0a_post      := init_post_to init0a2_addr     (fun Σ => @femtokernel_init_setup Σ 0).
    Example femtokernel_init0a2_pre      := init_pre_at  init0a2_addr     (fun Σ => @femtokernel_init_setup Σ 0).
    Example femtokernel_init0a2_post     := init_post_to init0b_addr      (fun Σ => @femtokernel_init_setup Σ 1).
    Example femtokernel_init0b_pre       := init_pre_at  init0b_addr      (fun Σ => @femtokernel_init_setup Σ 1).
    Example femtokernel_init0b_post      := init_post_to init0c_addr      (fun Σ => @femtokernel_init_setup Σ 2).
    Example femtokernel_init0c_pre       := init_pre_at  init0c_addr      (fun Σ => @femtokernel_init_setup Σ 2).
    Example femtokernel_init0c_post      := init_post_to init0d_addr      (fun Σ => @femtokernel_init_setup Σ 3).
    Example femtokernel_init0d_pre       := init_pre_at  init0d_addr      (fun Σ => @femtokernel_init_setup Σ 3).
    Example femtokernel_init0d_post      := init_post_to virtio_init_addr (@femtokernel_init_mid).
    Example femtokernel_virtio_init_pre  := init_pre_at  virtio_init_addr (@femtokernel_init_mid).
    Example femtokernel_virtio_init_post := init_post_to init_block1_addr (@femtokernel_init_mid).

    (* virtio_init is cut into four pieces purely to bound the peak memory of
       one vm_compute; see Layer 1 below. The block changes no modelled state
       apart from rx_used_seen, which femtokernel_init_mid already owns
       existentially, and the device registers, which are not modelled at
       all. So every piece has femtokernel_init_mid on both sides and only
       the address differs. Each boundary sits just before an auipc/lui that
       rebuilds the address registers, so no live register value crosses one.
         1..34  status, features, queue select/num/align/pfn
         35..50 descriptor 0 and the avail ring, then the fence
         51..58 rx_used_seen <- used.idx  (the one RAM write and the read)
         59..66 DRIVER_OK, queue notify, ret *)
    Definition virtio_v2_addr : N := Eval compute in (virtio_init_addr + 4 * 34)%N.
    Definition virtio_v3_addr : N := Eval compute in (virtio_init_addr + 4 * 50)%N.
    Definition virtio_v4_addr : N := Eval compute in (virtio_init_addr + 4 * 58)%N.

    Example femtokernel_virtio_v1_post := init_post_to virtio_v2_addr (@femtokernel_init_mid).
    Example femtokernel_virtio_v2_pre  := init_pre_at  virtio_v2_addr (@femtokernel_init_mid).
    Example femtokernel_virtio_v2_post := init_post_to virtio_v3_addr (@femtokernel_init_mid).
    Example femtokernel_virtio_v3_pre  := init_pre_at  virtio_v3_addr (@femtokernel_init_mid).
    Example femtokernel_virtio_v3_post := init_post_to virtio_v4_addr (@femtokernel_init_mid).
    Example femtokernel_virtio_v4_pre  := init_pre_at  virtio_v4_addr (@femtokernel_init_mid).
    Example femtokernel_init1_pre        := init_pre_at  init_block1_addr (@femtokernel_init_mid).

    (* init_block1 is cut after each CSR write whose register a later
       instruction reads again; see Layer 1 below.
         1..14  three PLIC stores,       csrw mie  (0xa88)
         15..21 csrw medeleg, csrw mideleg
         22..24 csrc mstatus (0x1800: clears MPP, already User, so a no-op)
         25..27 csrs mstatus (0x800:  MPP <- Supervisor)
         28..30 csrw mepc, mret *)
    Definition init1b_addr : N := Eval compute in (init_block1_addr + 4 * 14)%N.
    Definition init1c_addr : N := Eval compute in (init_block1_addr + 4 * 21)%N.
    Definition init1d_addr : N := Eval compute in (init_block1_addr + 4 * 24)%N.
    Definition init1e_addr : N := Eval compute in (init_block1_addr + 4 * 27)%N.

    Example femtokernel_init1a_post := init_post_to init1b_addr (fun Σ => @femtokernel_init1_state Σ mie_init_s false User).
    Example femtokernel_init1b_pre  := init_pre_at  init1b_addr (fun Σ => @femtokernel_init1_state Σ mie_init_s false User).
    Example femtokernel_init1b_post := init_post_to init1c_addr (fun Σ => @femtokernel_init1_state Σ mie_init_s true  User).
    Example femtokernel_init1c_pre  := init_pre_at  init1c_addr (fun Σ => @femtokernel_init1_state Σ mie_init_s true  User).
    Example femtokernel_init1c_post := init_post_to init1d_addr (fun Σ => @femtokernel_init1_state Σ mie_init_s true  User).
    Example femtokernel_init1d_pre  := init_pre_at  init1d_addr (fun Σ => @femtokernel_init1_state Σ mie_init_s true  User).
    Example femtokernel_init1d_post := init_post_to init1e_addr (fun Σ => @femtokernel_init1_state Σ mie_init_s true  Supervisor).
    Example femtokernel_init1e_pre  := init_pre_at  init1e_addr (fun Σ => @femtokernel_init1_state Σ mie_init_s true  Supervisor).

    (* Postcondition of init_block1: the kernel has dropped to S-mode at
       adv_start. mret takes the privilege from mstatus.MPP (set to S by the
       block) and resets MPP to User, MPIE to true and MIE to the old MPIE.
       TODO: mie, mideleg and medeleg are only owned here; state the values
       init_block1 writes once the handler proofs need them. *)
    Example femtokernel_init_post : Assertion ["a"::ty_xlenbits; "an"::ty_xlenbits] :=
      (term_var "an" = term_val ty_xlenbits (bv.of_N adv_addr))%asn ∗
      (mtvec ↦ term_val ty_xlenbits (bv.of_N handler_block0_addr)) ∗
      (∃ "v", mcause ↦ term_var "v") ∗
      (∃ "v", mideleg ↦ term_var "v") ∗ (∃ "v", medeleg ↦ term_var "v") ∗
      (∃ "v", mip ↦ term_var "v") ∗ (∃ "v", mie ↦ term_var "v") ∗
      (mepc ↦ term_val ty_xlenbits (bv.of_N adv_addr)) ∗
      (mscratch ↦ term_val ty_xlenbits (bv.of_N kernel_stack_top_addr)) ∗
      (∃ "v", stvec ↦ term_var "v") ∗ (∃ "v", sepc ↦ term_var "v") ∗
      (∃ "v", scause ↦ term_var "v") ∗ (∃ "v", sscratch ↦ term_var "v") ∗
      mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_val ty_privilege User; term_val ty.bool true; term_val ty.bool false; term_val ty.bool false; term_val ty.bool false ] ∗
      cur_privilege ↦ term_val ty_privilege Supervisor ∗
      asn_regs_ptsto {[x1; x2]} ∗
      x1 ↦ term_val ty_xlenbits (bv.of_N init_block1_addr) ∗
      x2 ↦ term_val ty_xlenbits (bv.of_N kernel_stack_top_addr) ∗
      term_val ty_xlenbits (bv.of_N iostate_addr) ↦ₘ term_val ty_word bv.zero ∗
      (∃ "v", term_val ty_xlenbits (bv.of_N rx_used_seen_addr) ↦ₘ term_var "v") ∗
      asn_pmp_entries term_smode_pmpentries ∗
      asn_mmio_trace_state_inv ∗
      asn_mmio_state_pred (term_val ty_iostate bv.zero).

    (* ---------------------------------------------------------------------- *)
    (* Layer 1: one VC per block                                              *)
    (* ---------------------------------------------------------------------- *)

    (* entry *)
    Definition femtokernel_entry_gen :=
      femtokernel_entry' entry_addr init_block0_addr.
    Definition vc__femtoentry : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition
                      femtokernel_entry_pre femtokernel_entry_gen femtokernel_entry_post wnil).
    Lemma sat__femtoentry : safeE vc__femtoentry.
    Proof.
      vm_compute.
      constructor; cbn.
      intuition bv_solve_Ltac.solveBvManual.
    Qed.

    (* init_block0, in five pieces: the CSR/store prefix, then one piece per
       pmpcfg group.

       One PMP CSR write is expensive (the executor opens and closes all 16
       entries, twice: once in readCSR and once in writeCSR), and the cost
       grows faster than linearly in the number of such writes in a single
       VC, because the accumulated path condition is re-checked each time.
       All 17 writes of this block at once exhaust memory. Each piece starts
       from concrete values again, so the cost stays bounded.

       Measured (vc__init0_prefix n, after the lean open lemma): n = 9 takes
       3.3s, n = 11 5.2s, n = 12 29s, n = 18 100s, n = 23 300s. Instruction
       12 is the first `csrw pmpaddr0`, so the prefix itself is cheap and the
       writes are what climbs. Cutting the prefix off (piece a) also resets
       the state the writes start from, which is why a2 is far cheaper than
       the old a: five writes from a concrete assertion, as in b and c.

       The indices are positions in the AnnotInstr list of the block, which
       here contains no annotations, so they are instruction counts:
         1..10  mtvec, iostate, mhartid, sp/mscratch  (no PMP write)
         11..23 entries 0..3,                          pmpcfg0
         24..37 entries 4..7,                          pmpcfg1
         38..49 entries 8..11,                         pmpcfg2
         50..54 entry 12, pmpcfg3, jal virtio_init *)
    Definition femtokernel_init0_gen :=
      femtokernel_init_block0' init_block0_addr handler_block0_addr iostate_addr
        kernel_stack_top_addr virtio_init_addr.

    Definition femtokernel_init0a_gen := firstn 10 femtokernel_init0_gen.
    Definition femtokernel_init0a2_gen := firstn 13 (skipn 10 femtokernel_init0_gen).
    Definition femtokernel_init0b_gen := firstn 14 (skipn 23 femtokernel_init0_gen).
    Definition femtokernel_init0c_gen := firstn 12 (skipn 37 femtokernel_init0_gen).
    Definition femtokernel_init0d_gen := skipn 49 femtokernel_init0_gen.

    (* The pieces cover the block exactly. *)
    Goal (femtokernel_init0a_gen ++ femtokernel_init0a2_gen ++ femtokernel_init0b_gen
            ++ femtokernel_init0c_gen ++ femtokernel_init0d_gen)%list = femtokernel_init0_gen.
    Proof. now vm_compute. Qed.

    Definition vc__femtoinit0a : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition
                      femtokernel_init0a_pre femtokernel_init0a_gen femtokernel_init0a_post wnil).
    Definition vc__femtoinit0a2 : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition
                      femtokernel_init0a2_pre femtokernel_init0a2_gen femtokernel_init0a2_post wnil).
    Definition vc__femtoinit0b : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition
                      femtokernel_init0b_pre femtokernel_init0b_gen femtokernel_init0b_post wnil).
    Definition vc__femtoinit0c : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition
                      femtokernel_init0c_pre femtokernel_init0c_gen femtokernel_init0c_post wnil).
    Definition vc__femtoinit0d : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition
                      femtokernel_init0d_pre femtokernel_init0d_gen femtokernel_init0d_post wnil).

    Definition vc__init0_prefix (n : nat) : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition
                      femtokernel_init0a_pre (firstn n femtokernel_init0_gen)
                      (term_var "an" = term_var "an")%asn wnil).

    Lemma sat__femtoinit0a : safeE vc__femtoinit0a.
    Proof.
      vm_compute.
      constructor; cbn.
      intuition bv_solve_Ltac.solveBvManual.
    Qed.

    Lemma sat__femtoinit0a2 : safeE vc__femtoinit0a2.
    Proof.
      vm_compute.
      constructor; cbn.
      intuition bv_solve_Ltac.solveBvManual.
    Qed.

    Lemma sat__femtoinit0b : safeE vc__femtoinit0b.
    Proof.
      vm_compute.
      constructor; cbn.
      intuition bv_solve_Ltac.solveBvManual.
    Qed.

    Lemma sat__femtoinit0c : safeE vc__femtoinit0c.
    Proof.
      vm_compute.
      constructor; cbn.
      intuition bv_solve_Ltac.solveBvManual.
    Qed.

    Lemma sat__femtoinit0d : safeE vc__femtoinit0d.
    Proof.
      vm_compute.
      constructor; cbn.
      intuition bv_solve_Ltac.solveBvManual.
    Qed.

    (* virtio_init *)
    Definition femtokernel_virtio_init_gen :=
      femtokernel_virtio_init' virtio_init_addr virtq_mem_addr rx_buf_addr rx_used_seen_addr.
    Definition femtokernel_virtio_v1_gen := firstn 34 femtokernel_virtio_init_gen.
    Definition femtokernel_virtio_v2_gen := firstn 16 (skipn 34 femtokernel_virtio_init_gen).
    Definition femtokernel_virtio_v3_gen := firstn 8 (skipn 50 femtokernel_virtio_init_gen).
    Definition femtokernel_virtio_v4_gen := skipn 58 femtokernel_virtio_init_gen.

    (* The pieces cover the block exactly. *)
    Goal (femtokernel_virtio_v1_gen ++ femtokernel_virtio_v2_gen
            ++ femtokernel_virtio_v3_gen ++ femtokernel_virtio_v4_gen)%list
         = femtokernel_virtio_init_gen.
    Proof. now vm_compute. Qed.

    Definition vc__femtovirtio_v1 : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition
                      femtokernel_virtio_init_pre femtokernel_virtio_v1_gen femtokernel_virtio_v1_post wnil).
    Definition vc__femtovirtio_v2 : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition
                      femtokernel_virtio_v2_pre femtokernel_virtio_v2_gen femtokernel_virtio_v2_post wnil).
    Definition vc__femtovirtio_v3 : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition
                      femtokernel_virtio_v3_pre femtokernel_virtio_v3_gen femtokernel_virtio_v3_post wnil).
    Definition vc__femtovirtio_v4 : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition
                      femtokernel_virtio_v4_pre femtokernel_virtio_v4_gen femtokernel_virtio_init_post wnil).

    Definition vc__virtio_prefix (n : nat) : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition
                      femtokernel_virtio_init_pre (firstn n femtokernel_virtio_init_gen)
                      (term_var "an" = term_var "an")%asn wnil).

    Definition virtio_at (n : nat) : N := Eval compute in (virtio_init_addr + 4 * N.of_nat n)%N.
    Definition vc__virtio_one (n k : nat) : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition
                      (init_pre_at (virtio_at n) (@femtokernel_init_mid))
                      (firstn k (skipn n femtokernel_virtio_init_gen))
                      (term_var "an" = term_var "an")%asn wnil).


    Ltac solve_dev_chain :=
      repeat first
        [ exact I
        | apply bounds_withinMMIO; now vm_compute
        | apply IOdev; [ now vm_compute | reflexivity ]
        | split
        | eexists ].

    (* Pieces 1, 2 and 4 are device writes only. Piece 3 holds the read of
       used.idx and the store to rx_used_seen: the read leaves an event
       hypothesis, and the store splits on MMIO versus RAM -- rx_used_seen is
       in RAM, so the MMIO branch is the false one and [right] picks the
       other. Mmio_event_prot_below_dev then turns the event hypothesis into
       "the protocol state did not change". *)
    Lemma sat__femtovirtio_v1 : safeE vc__femtovirtio_v1.
    Proof.
      vm_compute. constructor; cbn.
      solve_dev_chain.
    Qed.

    Lemma sat__femtovirtio_v2 : safeE vc__femtovirtio_v2.
    Proof.
      vm_compute. constructor; cbn.
      solve_dev_chain.
    Qed.

    Lemma sat__femtovirtio_v3 : safeE vc__femtovirtio_v3.
    Proof.
      vm_compute. constructor; cbn.
      solve_dev_chain.
      intros v0 v1 Hev. right. solve_dev_chain.
      symmetry. eapply Mmio_event_prot_below_dev; [ | exact Hev ]. now vm_compute.
    Qed.

    Lemma sat__femtovirtio_v4 : safeE vc__femtovirtio_v4.
    Proof.
      vm_compute. constructor; cbn.
      solve_dev_chain.
    Qed.

    (* init_block1 *)
    Definition femtokernel_init1_gen :=
      femtokernel_init_block1' init_block1_addr adv_addr.
    Definition vc__femtoinit1 : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition
                      femtokernel_init1_pre femtokernel_init1_gen femtokernel_init_post wnil).

    (* For measuring, as for init_block0. Measured on the earlier version of
       this block, which set mie with two csrs instead of one csrw: n = 11
       was 3.7s (the three PLIC stores), 14 was 4.9s (the first csrs), 16 was
       6.5s, and 17 -- the second csrs, reading back what the first wrote --
       did not finish. Do not leave measurement goals in the file; each one
       re-runs on every pass. *)
    Definition vc__init1_prefix (n : nat) : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition
                      femtokernel_init1_pre (firstn n femtokernel_init1_gen)
                      (term_var "an" = term_var "an")%asn wnil).

    Definition femtokernel_init1a_gen := firstn 14 femtokernel_init1_gen.
    Definition femtokernel_init1b_gen := firstn 7 (skipn 14 femtokernel_init1_gen).
    Definition femtokernel_init1c_gen := firstn 3 (skipn 21 femtokernel_init1_gen).
    Definition femtokernel_init1d_gen := firstn 3 (skipn 24 femtokernel_init1_gen).
    Definition femtokernel_init1e_gen := skipn 27 femtokernel_init1_gen.

    (* The pieces cover the block exactly. *)
    Goal (femtokernel_init1a_gen ++ femtokernel_init1b_gen ++ femtokernel_init1c_gen
            ++ femtokernel_init1d_gen ++ femtokernel_init1e_gen)%list
         = femtokernel_init1_gen.
    Proof. now vm_compute. Qed.

    Definition vc__femtoinit1a : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition
                      femtokernel_init1_pre femtokernel_init1a_gen femtokernel_init1a_post wnil).
    Definition vc__femtoinit1b : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition
                      femtokernel_init1b_pre femtokernel_init1b_gen femtokernel_init1b_post wnil).
    Definition vc__femtoinit1c : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition
                      femtokernel_init1c_pre femtokernel_init1c_gen femtokernel_init1c_post wnil).
    Definition vc__femtoinit1d : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition
                      femtokernel_init1d_pre femtokernel_init1d_gen femtokernel_init1d_post wnil).
    Definition vc__femtoinit1e : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition
                      femtokernel_init1e_pre femtokernel_init1e_gen femtokernel_init_post wnil).

    (* Piece a costs ~205s, almost all of it the csrw mie at instruction 14:
       readCSR runs even for a plain write, and reading mie out of
       femtokernel_init_mid -- where it is existential -- decodes nine
       symbolic booleans. With mie pinned to Minterrupts_zero in the
       precondition the same prefix takes 4.9s, but that value is not
       architecturally guaranteed at reset (the spec fixes mstatus.MIE, not
       mie), so the precondition stays honest and the proof pays instead. *)
    Lemma sat__femtoinit1a : safeE vc__femtoinit1a.
    Proof.
      vm_compute. constructor; cbn.
      solve_dev_chain; by vm_compute.
    Qed.

    Lemma sat__femtoinit1b : safeE vc__femtoinit1b.
    Proof.
      vm_compute.
      constructor; cbn.
      intuition bv_solve_Ltac.solveBvManual.
    Qed.

    Lemma sat__femtoinit1c : safeE vc__femtoinit1c.
    Proof.
      vm_compute.
      constructor; cbn.
      intuition bv_solve_Ltac.solveBvManual.
    Qed.

    Lemma sat__femtoinit1d : safeE vc__femtoinit1d.
    Proof.
      vm_compute.
      constructor; cbn.
      intuition bv_solve_Ltac.solveBvManual.
    Qed.

    (* mret: cur_privilege <- mstatus.MPP (Supervisor), MPP <- User,
       MPIE <- true, MIE <- the old MPIE (false), which is what
       femtokernel_init_post states. If a field does not match, the
       remaining goal names it. *)
    Lemma sat__femtoinit1e : safeE vc__femtoinit1e.
    Proof.
      vm_compute.
      constructor; cbn.
      intuition bv_solve_Ltac.solveBvManual.
    Qed.


    (* ---------------------------------------------------------------------- *)
    (* Layer 2: one Hoare triple per block                                    *)
    (* ---------------------------------------------------------------------- *)

    Definition init_iprop_pre `{sailGS Σ, iostateG IOState Σ}
      (pre : Assertion ["a"::ty_xlenbits]) (a : Val ty_xlenbits) : iProp
                                                                    Σ :=
      asn.interpret pre [env].["a" ∷ ty_xlenbits ↦ a].
    Definition init_iprop_post `{sailGS Σ, iostateG IOState Σ}
      (post : Assertion ["a"::ty_xlenbits; "an"::ty_xlenbits]) (a an : Val ty_xlenbits) : iProp Σ :=
      asn.interpret post [env].["a" ∷ ty_xlenbits ↦ a].["an" ∷ ty_xlenbits ↦ an].

    Definition contract_femtoentry `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits) : iProp Σ :=
      semTripleBlock (init_iprop_pre femtokernel_entry_pre) a
        (filter_AST femtokernel_entry_gen) (init_iprop_post femtokernel_entry_post).
    Definition contract_femtoinit0a `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits) : iProp Σ :=
      semTripleBlock (init_iprop_pre femtokernel_init0a_pre) a
        (filter_AST femtokernel_init0a_gen) (init_iprop_post femtokernel_init0a_post).
    Definition contract_femtoinit0a2 `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits) : iProp Σ :=
      semTripleBlock (init_iprop_pre femtokernel_init0a2_pre) a
        (filter_AST femtokernel_init0a2_gen) (init_iprop_post femtokernel_init0a2_post).
    Definition contract_femtoinit0b `{sailGS Σ, iostateG IOState Σ}

      (a : Val ty_xlenbits) : iProp Σ :=
      semTripleBlock (init_iprop_pre femtokernel_init0b_pre) a
        (filter_AST femtokernel_init0b_gen) (init_iprop_post femtokernel_init0b_post).
    Definition contract_femtoinit0c `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits) : iProp Σ :=
      semTripleBlock (init_iprop_pre femtokernel_init0c_pre) a
        (filter_AST femtokernel_init0c_gen) (init_iprop_post femtokernel_init0c_post).
    Definition contract_femtoinit0d `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits) : iProp Σ :=
      semTripleBlock (init_iprop_pre femtokernel_init0d_pre) a
        (filter_AST femtokernel_init0d_gen) (init_iprop_post femtokernel_init0d_post).
    Definition contract_femtovirtio_v1 `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits) : iProp Σ :=
      semTripleBlock (init_iprop_pre femtokernel_virtio_init_pre) a
        (filter_AST femtokernel_virtio_v1_gen) (init_iprop_post femtokernel_virtio_v1_post).
    Definition contract_femtovirtio_v2 `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits) : iProp Σ :=
      semTripleBlock (init_iprop_pre femtokernel_virtio_v2_pre) a
        (filter_AST femtokernel_virtio_v2_gen) (init_iprop_post femtokernel_virtio_v2_post).
    Definition contract_femtovirtio_v3 `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits) : iProp Σ :=
      semTripleBlock (init_iprop_pre femtokernel_virtio_v3_pre) a
        (filter_AST femtokernel_virtio_v3_gen) (init_iprop_post femtokernel_virtio_v3_post).
    Definition contract_femtovirtio_v4 `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits) : iProp Σ :=
      semTripleBlock (init_iprop_pre femtokernel_virtio_v4_pre) a
        (filter_AST femtokernel_virtio_v4_gen) (init_iprop_post femtokernel_virtio_init_post).
    Definition contract_femtoinit1a `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits) : iProp Σ :=
      semTripleBlock (init_iprop_pre femtokernel_init1_pre) a
        (filter_AST femtokernel_init1a_gen) (init_iprop_post femtokernel_init1a_post).
    Definition contract_femtoinit1b `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits) : iProp Σ :=
      semTripleBlock (init_iprop_pre femtokernel_init1b_pre) a
        (filter_AST femtokernel_init1b_gen) (init_iprop_post femtokernel_init1b_post).
    Definition contract_femtoinit1c `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits) : iProp Σ :=
      semTripleBlock (init_iprop_pre femtokernel_init1c_pre) a
        (filter_AST femtokernel_init1c_gen) (init_iprop_post femtokernel_init1c_post).
    Definition contract_femtoinit1d `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits) : iProp Σ :=
      semTripleBlock (init_iprop_pre femtokernel_init1d_pre) a
        (filter_AST femtokernel_init1d_gen) (init_iprop_post femtokernel_init1d_post).
    Definition contract_femtoinit1e `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits) : iProp Σ :=
      semTripleBlock (init_iprop_pre femtokernel_init1e_pre) a
        (filter_AST femtokernel_init1e_gen) (init_iprop_post femtokernel_init_post).

    (* As in U-mode: let the kernel unfold the VC names first. *)
    Local Strategy expand [vc__femtoentry vc__femtoinit0a vc__femtoinit0a2 vc__femtoinit0b
                             vc__femtoinit0c vc__femtoinit0d
                             vc__femtovirtio_v1 vc__femtovirtio_v2 vc__femtovirtio_v3 vc__femtovirtio_v4
                             vc__femtoinit1a vc__femtoinit1b vc__femtoinit1c
                             vc__femtoinit1d vc__femtoinit1e].

    Lemma contract_femtoentry_verified : ∀ `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits),
        ⊢ contract_femtoentry a.
    Proof.
      unfold contract_femtoentry, init_iprop_pre, init_iprop_post. iIntros (Σ sg ioG a).
      iApply (sound_sannotated_block_verification_condition lemSemBlockVerif).
      exact sat__femtoentry.
    Qed.

    Lemma contract_femtoinit0a_verified : ∀ `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits),
        ⊢ contract_femtoinit0a a.
    Proof.
      unfold contract_femtoinit0a, init_iprop_pre, init_iprop_post. iIntros (Σ sg ioG a).
      iApply (sound_sannotated_block_verification_condition lemSemBlockVerif).
      exact sat__femtoinit0a.
    Qed.

    Lemma contract_femtoinit0a2_verified : ∀ `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits),
        ⊢ contract_femtoinit0a2 a.
    Proof.
      unfold contract_femtoinit0a2, init_iprop_pre, init_iprop_post. iIntros (Σ sg ioG a).
      iApply (sound_sannotated_block_verification_condition lemSemBlockVerif).
      exact sat__femtoinit0a2.
    Qed.

    Lemma contract_femtoinit0b_verified : ∀ `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits),
        ⊢ contract_femtoinit0b a.
    Proof.
      unfold contract_femtoinit0b, init_iprop_pre, init_iprop_post. iIntros (Σ sg ioG a).
      iApply (sound_sannotated_block_verification_condition lemSemBlockVerif).
      exact sat__femtoinit0b.
    Qed.

    Lemma contract_femtoinit0c_verified : ∀ `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits),
        ⊢ contract_femtoinit0c a.
    Proof.
      unfold contract_femtoinit0c, init_iprop_pre, init_iprop_post. iIntros (Σ sg ioG a).
      iApply (sound_sannotated_block_verification_condition lemSemBlockVerif).
      exact sat__femtoinit0c.
    Qed.

    Lemma contract_femtoinit0d_verified : ∀ `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits),
        ⊢ contract_femtoinit0d a.
    Proof.
      unfold contract_femtoinit0d, init_iprop_pre, init_iprop_post. iIntros (Σ sg ioG a).
      iApply (sound_sannotated_block_verification_condition lemSemBlockVerif).
      exact sat__femtoinit0d.
    Qed.

    Lemma contract_femtovirtio_v1_verified : ∀ `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits),
        ⊢ contract_femtovirtio_v1 a.
    Proof.
      unfold contract_femtovirtio_v1, init_iprop_pre, init_iprop_post. iIntros (Σ sg ioG a).
      iApply (sound_sannotated_block_verification_condition lemSemBlockVerif).
      exact sat__femtovirtio_v1.
    Qed.

    Lemma contract_femtovirtio_v2_verified : ∀ `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits),
        ⊢ contract_femtovirtio_v2 a.
    Proof.
      unfold contract_femtovirtio_v2, init_iprop_pre, init_iprop_post. iIntros (Σ sg ioG a).
      iApply (sound_sannotated_block_verification_condition lemSemBlockVerif).
      exact sat__femtovirtio_v2.
    Qed.

    Lemma contract_femtovirtio_v3_verified : ∀ `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits),
        ⊢ contract_femtovirtio_v3 a.
    Proof.
      unfold contract_femtovirtio_v3, init_iprop_pre, init_iprop_post. iIntros (Σ sg ioG a).
      iApply (sound_sannotated_block_verification_condition lemSemBlockVerif).
      exact sat__femtovirtio_v3.
    Qed.

    Lemma contract_femtovirtio_v4_verified : ∀ `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits),
        ⊢ contract_femtovirtio_v4 a.
    Proof.
      unfold contract_femtovirtio_v4, init_iprop_pre, init_iprop_post. iIntros (Σ sg ioG a).
      iApply (sound_sannotated_block_verification_condition lemSemBlockVerif).
      exact sat__femtovirtio_v4.
    Qed.

    Lemma contract_femtoinit1a_verified : ∀ `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits),
        ⊢ contract_femtoinit1a a.
    Proof.
      unfold contract_femtoinit1a, init_iprop_pre, init_iprop_post. iIntros (Σ sg ioG a).
      iApply (sound_sannotated_block_verification_condition lemSemBlockVerif).
      exact sat__femtoinit1a.
    Qed.

    Lemma contract_femtoinit1b_verified : ∀ `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits),
        ⊢ contract_femtoinit1b a.
    Proof.
      unfold contract_femtoinit1b, init_iprop_pre, init_iprop_post. iIntros (Σ sg ioG a).
      iApply (sound_sannotated_block_verification_condition lemSemBlockVerif).
      exact sat__femtoinit1b.
    Qed.

    Lemma contract_femtoinit1c_verified : ∀ `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits),
        ⊢ contract_femtoinit1c a.
    Proof.
      unfold contract_femtoinit1c, init_iprop_pre, init_iprop_post. iIntros (Σ sg ioG a).
      iApply (sound_sannotated_block_verification_condition lemSemBlockVerif).
      exact sat__femtoinit1c.
    Qed.

    Lemma contract_femtoinit1d_verified : ∀ `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits),
        ⊢ contract_femtoinit1d a.
    Proof.
      unfold contract_femtoinit1d, init_iprop_pre, init_iprop_post. iIntros (Σ sg ioG a).
      iApply (sound_sannotated_block_verification_condition lemSemBlockVerif).
      exact sat__femtoinit1d.
    Qed.

    Lemma contract_femtoinit1e_verified : ∀ `{sailGS Σ, iostateG IOState Σ} (a : Val ty_xlenbits),
        ⊢ contract_femtoinit1e a.
    Proof.
      unfold contract_femtoinit1e, init_iprop_pre, init_iprop_post. iIntros (Σ sg ioG a).
      iApply (sound_sannotated_block_verification_condition lemSemBlockVerif).
      exact sat__femtoinit1e.
    Qed.


End FemtoKernel.
