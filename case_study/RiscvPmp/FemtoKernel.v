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

From Coq Require Import
     ZArith.ZArith
     Lists.List
     Strings.String.
From Katamaran Require Import
     Bitvector
     Notations
     Specification
     SmallStep.Step
     RiscvPmp.BlockVer.Spec
     RiscvPmp.BlockVer.TotalVerifier
     RiscvPmp.IrisModel
     RiscvPmp.IrisInstance
     RiscvPmp.Machine
     RiscvPmp.PmpCheck
     RiscvPmp.Sig.
From Katamaran Require
     RiscvPmp.Contracts
     RiscvPmp.LoopVerification
     RiscvPmp.Model.
From iris.base_logic Require lib.gen_heap lib.iprop invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac big_op.
From iris.program_logic Require weakestpre adequacy.
From iris.proofmode Require string_ident tactics.
From stdpp Require namespaces.

Import RiscvPmpProgram.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import env.notations.
Import ListNotations.
Open Scope ctx_scope.

Module inv := invariants.

  Import ctx.resolution.
  Import ctx.notations.
  Import env.notations.
  Import iris.program_logic.weakestpre.
  Import iris.proofmode.tactics.

  Import MicroSail.ShallowExecutor.

  Import Contracts.
  Import RiscvPmpIrisBase.
  Import RiscvPmpIrisInstancePredicates.
  Import RiscvPmpBlockVerifIrisInstance.
  Import RiscvPmpBlockVerifSpec.
  Import RiscvPmpIrisInstanceWithContracts.
  Import RiscvPmpBlockVerifShalExecutor.


  Section FemtoKernel.
    Import bv.notations.
    Import ListNotations.
    Import TermNotations.

    Open Scope hex_Z_scope.

    (* FIXED ADDRESSES *)
    (* The first address that is no longer used by the adversary, and hence the address at which the PMP entries should stop granting permission. Note that this address is currently also the first MMIO address. *)
    Definition adv_addr_end : N := maxAddr. (* Change once adversary gets access to MMIO*)
    (* Address where we will write in MMIO memory, and proof that our writes will indeed be within the MMIO region*)
    Definition mmio_write_addr : N := mmioStartAddr.
    Lemma write_word_is_MMIO: withinMMIO (bv.of_N mmio_write_addr) bytes_per_word.
    Proof.
      (* Avoid compute in case the list of MMIO addresses ever becomes longer *)
      repeat split; cbn; unfold mmioAddrs;
      eassert (mmioLenAddr = _) as -> by now compute. (* Get actual length so we can use successors *)
      all: apply bv.in_seqBv; now compute.
    Qed.

    (* Aliases for registers *)
    Definition zero : RegIdx := [bv 0].
    Definition ra : RegIdx := [bv 1].
    Definition t0 : RegIdx := [bv 5].
    Definition t1 : RegIdx := [bv 6].
    Definition t2 : RegIdx := [bv 7].

    Definition pure_privilege_to_bits {n} : Privilege -> bv n :=
      fun p => match p with | Machine => bv.of_N 3 | User => bv.zero end.

    Definition pure_pmpAddrMatchType_to_bits : PmpAddrMatchType -> bv 4 :=
      fun mt => match mt with
                | OFF => bv.zero
                | TOR => bv.one
                end.

    Definition pure_pmpcfg_ent_to_bits : Pmpcfg_ent -> Val (ty.bvec byte) :=
      fun ent =>
        match ent with
        | MkPmpcfg_ent L A X W R =>
            let l : bv 1 := bv.of_bool L in
            let a : bv 4 := pure_pmpAddrMatchType_to_bits A in
            let x : bv 1 := bv.of_bool X in
            let w : bv 1 := bv.of_bool W in
            let r : bv 1 := bv.of_bool R in
            bv.app r (bv.app w (bv.app x (bv.app a l)))
        end%Z.

    (* Definitions for configuration bits of PMP entries *)
    Definition femto_pmpcfg_ent0 : Pmpcfg_ent := MkPmpcfg_ent false OFF false false false.
    Definition femto_pmpcfg_ent0_bits : Val (ty.bvec byte) := pure_pmpcfg_ent_to_bits femto_pmpcfg_ent0.
    Definition femto_pmpcfg_ent1 : Pmpcfg_ent := MkPmpcfg_ent false TOR true true true.
    Definition femto_pmpcfg_ent1_bits : Val (ty.bvec byte) := pure_pmpcfg_ent_to_bits femto_pmpcfg_ent1.
    Definition femto_pmp0cfg_bits : Val (ty.bvec 32) := bv.zext (bv.app femto_pmpcfg_ent0_bits femto_pmpcfg_ent1_bits).

    (* Because of sign extension in the 12-bit immediate of ADDI/SW/LW, one cannot just take subranges to split immediates. Rather, the following function is used: *)
    (* See e.g.: https://stackoverflow.com/questions/50742420/risc-v-build-32-bit-constants-with-lui-and-addi *)
    Definition imm_split_bv (imm : bv 32) : (bv 12 * bv 20) :=
      let (lo , hi) := bv.appView 12 _ imm in
        if bv.eqb hi (bv.ones 20) then (lo , hi) (* Small negative numbers *)
        else if (bv.msb lo) (* Avoid incorrect sign-extension *)
             then (bv.of_Z (Z.of_N (bv.bin lo) - 4096), (hi + bv.one)%bv)
             else (lo , hi).

    (* TODO: prove this spec for `imm_split_bv`*)
    (* Lemma imm_split_bv_spec lo hi imm : *)
    (*    (lo , hi) = imm_split_bv imm -> imm = bv.add (bv.shiftl (bv.zext hi) (@bv.of_N 12 12)) (bv.sext lo). *)

    Definition femto_pmp0cfg_bits_1 : Val (ty.bvec 12) := fst (imm_split_bv femto_pmp0cfg_bits).
    Definition femto_pmp0cfg_bits_2 : Val (ty.bvec 20) := snd (imm_split_bv femto_pmp0cfg_bits).

    (* ASTs with a very limited form of labels, that allow us to refer to the address of the current instruction *)
    (* TODO: have the symbolic executor work with these types of instructions directly? *)
    Inductive ASM :=
      | Instr (a: AnnotInstr)
      | RelInstr (f : N -> AnnotInstr).
    Local Coercion AST_AnnotAST (a : AST) := AnnotAST (a).
    Local Coercion AnnotAST_ASM (a : AnnotInstr) := Instr (a).
    Local Notation "'Λ' x , a" := (RelInstr (fun x => a))
      (at level 200) : list_scope.
    Local Arguments List.cons {_} & _ _. (* Allow projecting individual ASM into AST  - TODO: wrap `cons` in another definition so this bidirectionality does not interfere with lists *)

    (* The following definitions are required for layouting in memory, because otherwise we will count other things than instructions as taking up space *)
    Definition filter_AnnotInstr_AST (l : list AnnotInstr) := base.omap extract_AST l.
    Definition ASM_extract_AST (a : ASM) :=
      extract_AST
      (match a with
      | Instr a => a
      | RelInstr f => f 0%N end).
    Definition filter_ASM_AST (l : list ASM) := base.omap ASM_extract_AST l.

    (* Address resolution *)
    Fixpoint resolve_ASM (la : list ASM) (cur_off : N) : list AnnotInstr :=
      match la with
      | nil => nil
      | cons hd tl =>
          let hd' := (match hd with
          | Instr a => a
          | RelInstr f => f cur_off end) in
          let new_off : N :=
            (* Only instructions should increase the current offset, whereas lemma and debug calls will be filtered out in the end! *)
            (match extract_AST hd' with
            | Some _ => (cur_off + N.of_nat xlenbytes)%N
            | _ => cur_off
            end) in
              cons hd' (resolve_ASM tl new_off)
       end.

    (* Init code is the same in both versions of the femtokernel, since MMIO memory is placed after the adversary code, hence not affecting initialization *)
    Example femtokernel_init_asm (handler_start : N) (adv_start : N): list ASM :=
      [
        UTYPE bv.zero ra RISCV_AUIPC
      ; Λ x, ITYPE (bv.of_N (adv_start - (x - 4))) ra ra RISCV_ADDI
      ; CSR MPMPADDR0 ra zero false CSRRW
      ; ITYPE (bv.of_N adv_addr_end) zero ra RISCV_ADDI
      ; CSR MPMPADDR1 ra zero false CSRRW
      ; UTYPE femto_pmp0cfg_bits_2 ra RISCV_LUI
      ; ITYPE femto_pmp0cfg_bits_1 ra ra RISCV_ADDI
      ; CSR MPMP0CFG ra zero false CSRRW
      ; UTYPE bv.zero ra RISCV_AUIPC
      ; Λ x, ITYPE (bv.of_N (handler_start - (x - 4))) ra ra RISCV_ADDI
      ; CSR MTvec ra zero false CSRRW
      ; ITYPE (bv.of_N (adv_start - handler_start)) ra ra RISCV_ADDI
      ; CSR MEpc ra zero false CSRRW
      ; ITYPE [bv 0x80] zero ra RISCV_ADDI
      ; CSR MStatus ra zero false CSRRW
      ; MRET
      ].

    Example femtokernel_init' (init_start : N) (handler_start : N) (adv_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_init_asm handler_start adv_start) init_start.

    Example femtokernel_handler_asm : list ASM :=
      [
          ITYPE bv.one zero t1 RISCV_ADDI (* t1 <- 1 *)
        ; RTYPE t1 t0 t2 RISCV_AND (* t2 = t0 && 1 *)
        ; Λ current_pc, BTYPE (bv.of_N (mmio_handler_start_block2 - current_pc)) t1 t2 RISCV_BEQ (* branch if t0 odd (t2 = 1) *)
      ].
    Example femtokernel_handler' (handler_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_handler_asm) handler_start.

    Example femtokernel_mmio_handler_asm_block2 : list ASM :=
      [
         MRET
      ].

    Example femtokernel_mmio_handler_block2' (handler_start : N) : list AnnotInstr :=
      resolve_ASM (femtokernel_mmio_handler_asm_block2) handler_start.

    (* SIZES *)
    Definition instruction_size : N := N.of_nat bytes_per_instr.

    Definition init_size : N := N.of_nat (List.length (filter_AnnotInstr_AST (femtokernel_init' 0 0 0))) * 4.

    Definition handler_size : N := N.of_nat (List.length (filter_AnnotInstr_AST (femtokernel_handler' 0))) * 4.

    (* ADDRESSES *)
    Definition init_addr     : N := 0.
    Definition handler_addr  : N := init_addr + init_size.
    Definition mmio_handler_addr_block0  : N := handler_addr.
    Definition mmio_handler_addr_block1 : N := mmio_handler_addr_block0 + mmio_handler_size_block0.
    Definition mmio_handler_addr_block2 : N := mmio_handler_addr_block1 + mmio_handler_size_block1.

    (* NOTE: There is no data in the MMIO case, but we just keep *)
    Definition data_addr     : N := handler_addr + handler_size.
    Definition adv_addr : N := handler_addr + handler_size.

    (* CODE AND CONFIG SHORTANDS *)
    Local Notation "e1 ',ₜ' e2" := (term_binop bop.pair e1 e2) (at level 100).
    (* Shorthand for the pmp entries in both Katamaran and Iris *)
    Local Notation asn_femto_pmpentries a :=
      ([(term_val ty_pmpcfg_ent femto_pmpcfg_ent0 ,ₜ (a +ᵇ term_val ty_xlenbits (bv.of_N adv_addr)));
        (term_val ty_pmpcfg_ent femto_pmpcfg_ent1 ,ₜ (term_val ty_xlenbits (bv.of_N adv_addr_end)))])%list.
    Definition femto_pmpentries : list PmpEntryCfg := [(femto_pmpcfg_ent0, bv.of_N adv_addr); (femto_pmpcfg_ent1, bv.of_N adv_addr_end)]%list.
    (* Definition of the femtokernel initialization procedure. *)
    (* Note that the addresses we supply assume a base address of 0. The code however uses relative addresses and could be placed elsewhere in memory. *)
    Definition femtokernel_init_gen := femtokernel_init' init_addr handler_addr adv_addr.

    (* The code is different in both cases for the handler, so we cannot derive the concrete cases from the more general one. *)
    Definition femtokernel_handler := femtokernel_handler' handler_addr.

    Import asn.notations.
    Import RiscvPmp.Sig.
    (* Fix word length at 4 for this example, as we do not perform any other writes*)
    Local Notation asn_inv_mmio := (asn.chunk (chunk_user (inv_mmio bytes_per_word) [env])).
    Local Notation asn_pmp_addr_access l m := (asn.chunk (chunk_user pmp_addr_access [l; m])).
    Local Notation asn_pmp_entries l := (asn.chunk (chunk_user pmp_entries [l])).

    Example femtokernel_init_pre : Assertion ["a"::ty_xlenbits] :=
      (term_unop uop.unsigned (term_var "a") + term_val ty.int (Z.of_N adv_addr) < term_val ty.int (Z.of_N maxAddr))%asn ∗
      (∃ "v", mtvec ↦ term_var "v") ∗
      (∃ "v", mcause ↦ term_var "v") ∗
      (∃ "v", mip ↦ term_var "v") ∗ (∃ "v", mie ↦ term_var "v") ∗
      (∃ "v", mepc ↦ term_var "v") ∗
      mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_val ty.bool false; term_val ty.bool false ] ∗
      cur_privilege ↦ term_val ty_privilege Machine ∗
      (∃ "x1", x1 ↦ term_var "x1") ∗
      (asn_pmp_entries (term_list [(term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ term_val ty_xlenbits bv.zero);
                                   (term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ term_val ty_xlenbits bv.zero)])).

    Import TermNotations.

    Example femtokernel_init_post : Assertion ["a"::ty_xlenbits; ("an"::ty_xlenbits)] :=
      (
        (term_var "an" = term_var "a" +ᵇ (term_val ty_xlenbits (bv.of_N adv_addr)))%asn ∗
          (mtvec ↦ term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N handler_addr)) ∗
          (∃ "v", mcause ↦ term_var "v") ∗
          (∃ "v", mip ↦ term_var "v") ∗ (∃ "v", mie ↦ term_var "v") ∗
          (∃ "v", mepc ↦ term_var "v") ∗
          mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_val ty.bool true; term_val ty.bool true ] ∗
          cur_privilege ↦ term_val ty_privilege User ∗
          x1 ↦ term_val ty_xlenbits [bv 0x80] ∗
          asn_pmp_entries (term_list (asn_femto_pmpentries (term_var "a")))
      ).

    (* (* note that this computation takes longer than directly proving sat__femtoinit below *) *)
    (* Time Example t_vc__femtoinit : 𝕊 Σ__femtoinit := *)
    (*   Eval vm_compute in *)
    (*   simplify (VC__addr femtokernel_init_pre femtokernel_init femtokernel_init_post). *)

    Definition vc__femtoinit : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition femtokernel_init_pre femtokernel_init_gen femtokernel_init_post wnil).
    Definition vc__femtoinit_unq : 𝕊 [] :=
      Postprocessing.unquantify vc__femtoinit.

    (* NOTE: For now this proof covers both the MMIO and non-MMIO Femtokernel variants, since the start of the adversary region is the same in both cases.
       If this were not the case, we would take a naive approach to verifying both versions of the initialization code here; we would require that `adv_start` takes one of the two values present in the two versions of the initialization code.
       A more general approach would verify the contract under a logical value for `adv_start`.
       This would require the block verifier to support taking a list of instructions that can depend on symbolic values as input (i.e. proper terms).
     *)
    Lemma sat__femtoinit : safeE vc__femtoinit.
    Proof.
      vm_compute.
      constructor; cbn.
      intuition bv_solve_Ltac.solveBvManual.
    Qed.

    Definition contract_femtoinit `{sailGS Σ} (a : Val ty_xlenbits) : iProp Σ :=
      semTripleBlock
        (λ a, asn.interpret femtokernel_init_pre [env].["a" ∷ ty_xlenbits ↦ a])
        a (filter_AST femtokernel_init_gen)
        (λ a an, asn.interpret femtokernel_init_post [env].["a" ∷ ty_xlenbits ↦ a].["an" ∷ ty_xlenbits ↦ an]).

    Lemma contract_femtoinit_verified : ∀ `{sailGS Σ} (a : Val ty_xlenbits),
        ⊢ contract_femtoinit a.
    Proof.
      unfold contract_femtoinit. iIntros (Σ sg a).
      iApply (sound_sannotated_block_verification_condition lemSemBlockVerif).
      vm_compute.
      apply sat__femtoinit.
    Qed.

    (* NOTE: in one case the handler reads (legacy) and in the other it writes (mmio). However, this does not have an impact on the shape of the contract, as we do not directly talk about the written/read value *)
    Example femtokernel_handler_pre : Assertion ["x5" :: ty_xlenbits; "mepc" :: ty_xlenbits; "a" :: ty_xlenbits] :=
      (* (term_var "a" = term_val ty_word (bv.of_N handler_addr)) ∗ *)
      (term_unop uop.unsigned (term_var "a") + term_val ty.int (Z.of_N (adv_addr - handler_addr)) < term_val ty.int (Z.of_N maxAddr))%asn ∗
      (∃ "mpie", mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_var "mpie"; term_val ty.bool false ]) ∗
      (mtvec ↦ term_val ty_word (bv.of_N handler_addr)) ∗
      (∃ "v", mcause ↦ term_var "v") ∗
      (∃ "v", mip ↦ term_var "v") ∗ (∃ "v", mie ↦ term_var "v") ∗
      (mepc ↦ term_var "mepc") ∗
      cur_privilege ↦ term_val ty_privilege Machine ∗
      (∃ "x1", x1 ↦ term_var "x1") ∗
      x5 ↦ term_var "x5" ∗
      asn_pmp_entries (term_list (asn_femto_pmpentries (term_var "a" -ᵇ term_val ty_xlenbits (bv.of_N handler_addr)))) ∗ (* Different handler sizes cause different entries *)
      asn_inv_mmio.

    Example femtokernel_handler_post :
      Assertion ["x5" :: ty_xlenbits; "mepc" :: ty_xlenbits; "a" :: ty_xlenbits; "an"::ty_xlenbits] :=
      term_var "an" = term_var "mepc" ∗
      (∃ "mie", mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_val ty.bool true; term_var "mie" ]) ∗
          (mtvec ↦ term_val ty_word (bv.of_N handler_addr)) ∗
          (∃ "v", mcause ↦ term_var "v") ∗
          (∃ "v", mip ↦ term_var "v") ∗ (∃ "v", mie ↦ term_var "v") ∗
          (mepc ↦ term_var "mepc") ∗
          cur_privilege ↦ term_val ty_privilege User ∗
          (x1 ↦ term_val ty_xlenbits bv.zero ∗
           x5 ↦ term_val ty_xlenbits (bv.of_N 42)) ∗
          asn_pmp_entries (term_list (asn_femto_pmpentries (term_var "a" -ᵇ term_val ty_xlenbits (bv.of_N handler_addr)))). (* Different handler sizes cause different entries *)

    (* Time Example t_vc__femtohandler : 𝕊 [] := *)
    (*   Eval vm_compute in *)
    (*     simplify (VC__addr femtokernel_handler_pre femtokernel_handler femtokernel_handler_post). *)

    Definition vc__femtohandler : 𝕊 [] :=
      postprocess2 (sannotated_block_verification_condition
                     femtokernel_handler_pre
                     femtokernel_handler
                     femtokernel_handler_post wnil).

      (* let vc1 := VC__addr femtokernel_handler_pre femtokernel_handler femtokernel_handler_post in *)
      (* let vc2 := Postprocessing.prune vc1 in *)
      (* let vc3 := Postprocessing.solve_evars vc2 in *)
      (* let vc4 := Postprocessing.solve_uvars vc3 in *)
      (* let vc5 := Postprocessing.prune vc4 in *)
      (* vc5. *)
    (* Import SymProp.notations. *)
    (* Set Printing Depth 200. *)
    (* Eval vm_compute in vc__femtohandler. *)


    Definition vc__femtohandler_block0 : 𝕊 [] :=
      postprocess (sannotated_block_verification_condition
                     (femtokernel_handler_pre)
                     (femtokernel_handler_gen_block0 mmio_handler_addr_block2)
                     (femtokernel_handler_post_block0) wnil).

    Definition vc__femtohandler_block1 : 𝕊 [] :=
      postprocess (sannotated_block_verification_condition
                     (femtokernel_handler_pre_block1)
                     (femtokernel_handler_gen_block1)
                     (femtokernel_handler_post_block1) wnil).

    Definition vc__femtohandler_block2 : 𝕊 [] :=
      postprocess (sannotated_block_verification_condition
                     (femtokernel_handler_pre_block2)
                     (femtokernel_handler_gen_block2)
                     (femtokernel_handler_post) wnil).

Import Erasure.notations.
Eval vm_compute in Erasure.erase_symprop vc__femtohandler_block0.
Locate erase_symprop.

    (* Lemma even_iff_land1: forall n, N.even n <-> N.land n 1 = 0%N. *)
    (* Proof. *)
    (*   split; *)
    (*     destruct n; auto; destruct p; auto; *)
    (*     intros H; inversion H. *)
    (* Qed. *)

    (* Lemma even_trunc: forall (m : nat) (n : N), N.even n -> N.even (bv.truncn m n). *)
    (* Proof. *)
    (*   intros m n Heven. destruct n; destruct m; auto; destruct p; auto. *)
    (*   - inversion Heven. *)
    (*   - simpl. destruct (bv.trunc m p); auto. *)
    (* Qed. *)

    Import Erasure.notations.
    Lemma sat__femtohandler : safeE vc__femtohandler.
    Proof.
      (* We still need to prove that our word falls within mmio *)
      vm_compute.
      constructor; cbn.
      intuition bv_solve_Ltac.solveBvManual.
      1-4: eapply bv.in_seqBv'; now vm_compute.
    Qed.

    Definition contract_femtohandler `{sailGS Σ} (a x5 mepc : Val ty_xlenbits) : iProp Σ :=
      semTripleBlock
        (λ a, asn.interpret femtokernel_handler_pre [env].["x5" ∷ ty_xlenbits ↦ x5].["mepc" ∷ ty_xlenbits ↦ mepc].["a" ∷ ty_xlenbits ↦ a])
        a (filter_AST femtokernel_handler)
        (λ a an, asn.interpret femtokernel_handler_post [env].["x5" ∷ ty_xlenbits ↦ x5].["mepc" ∷ ty_xlenbits ↦ mepc].["a" ∷ ty_xlenbits ↦ a].["an" ∷ ty_xlenbits ↦ an]).

    Lemma contract_femtohandler_verified : ∀ `{sailGS Σ} (a x5 mepc : Val ty_xlenbits),
        ⊢ contract_femtohandler a x5 mepc.
    Proof.
      unfold contract_femtohandler. iIntros (Σ sg a x5 mepc).
      iApply (sound_sannotated_block_verification_condition lemSemBlockVerif).
      pose proof sat__femtohandler as H.
      vm_compute; apply H.
    Qed.

    Definition femtoinit_stats :=
      SymProp.Statistics.count_to_stats
        (SymProp.Statistics.count_nodes
           (sannotated_block_verification_condition
              femtokernel_init_pre
              femtokernel_init_gen
              (asn.sep femtokernel_init_post asn.debug)
              wnil)
           SymProp.Statistics.empty).
    (* Eval vm_compute in femtoinit_stats. *)

    (* There is currently no difference, because the adversary addresses are shared between both cases*)
    Definition femto_init_stats := femtoinit_stats.
    (* Eval vm_compute in femto_init_stats. *)

    Definition femtohandler_stats :=
      SymProp.Statistics.count_to_stats
        (SymProp.Statistics.count_nodes
           (sannotated_block_verification_condition
              femtokernel_handler_pre
              femtokernel_handler
              (asn.sep femtokernel_handler_post asn.debug)
              wnil)
           SymProp.Statistics.empty).
    (* Eval vm_compute in femtohandler_stats. *)

  End FemtoKernel.

  Definition advAddrs : list (bv xlenbits) := bv.seqBv (bv.of_N adv_addr) (adv_addr_end - adv_addr).

  Global Instance dec_has_some_access {ents p1} : forall x, Decision (exists p2, Pmp_access x (bv.of_nat 1) ents p1 p2).
  Proof.
    intros x.
    eapply finite.exists_dec.
    intros p2.
    unfold Pmp_access, Gen_Pmp_access.
    destruct (pmp_check_aux x (bv.of_nat 1) bv.zero ents p1 p2); [left|right]; easy.
  Defined.

  Lemma adv_is_live y : (y ∈ advAddrs)%stdpp → (y ∈ liveAddrs)%stdpp.
  Proof. unfold advAddrs, liveAddrs.
         apply bv.seqBv_sub_elem_of; now compute.
  Qed.

  Ltac case_if H :=
    let go P := (destruct P eqn:H) in
      match goal with
      | |- context [if ?P then _ else _] => go P
      | K: context [if ?P then _ else _] |- _ => go P
      end.

  Lemma adv_in_pmp x : (x ∈ advAddrs)%stdpp -> (∃ p : Val ty_access_type, Pmp_access x (bv.of_nat 1) femto_pmpentries User p).
  Proof.
    intro Hin. rewrite /femto_pmpentries.
    exists Read.
    cbv [Pmp_access Gen_Pmp_access pmp_check_aux pmp_check_rec pmp_match_entry].
    apply bv.seqBv_in' in Hin as [Hlo Hhi]; [|clear Hin; now compute].
    cbn in *. eassert (adv_addr = _) as -> by now compute.
    unfold bv.uleb, bv.ule, bv.ult, bv.ultb in *.
    set (y := bv.bin x) in *. (* Avoid this being simplified later on, just sub when we need it *)
    cbv -[N.le N.lt y] in Hlo,Hhi.
    case_if H; [now compute | clear H].
    case_if H.
    { rewrite bv.bin_add_small in H.
      - apply orb_prop in H as [|]; rewrite N.leb_le -/y /= in H; lia.
      - cbn. unfold N.of_nat. cbn. lia. }
    clear H. case_if H; first easy.
    { rewrite bv.bin_add_small /= -/y in H; last lia.
      apply andb_false_iff in H as [|]; rewrite N.leb_gt in H; solve_bv. }
  Qed.

  Lemma pmp_in_adv x : (∃ p : Val ty_access_type, Pmp_access x (bv.of_nat 1) femto_pmpentries User p) → (x ∈ advAddrs)%stdpp.
  Proof.
    intros [p HPmp]. rewrite /femto_pmpentries.
    cbv [Pmp_access Gen_Pmp_access pmp_check_aux pmp_check_rec pmp_match_entry] in HPmp. cbn in HPmp.
    case_if H; first now compute. clear H.
    unfold bv.uleb in *.
    case_if H; first by exfalso.
    apply orb_false_elim in H as [_ Hhi]. rewrite N.leb_gt in Hhi.
    case_if H'; last by exfalso.
    apply andb_prop in H' as [Hlo _]. rewrite N.leb_le in Hlo.
    apply bv.in_seqBv; exact.
  Qed.

  (* Use permutation rather than membership to avoid indexes *)
  Lemma allAddr_filter_advAddr : filter
                 (λ x : Val ty_word ,
                    (∃ p : Val ty_access_type, Pmp_access x (bv.of_nat 1) femto_pmpentries User p)%type)
                 all_addrs ≡ₚ advAddrs.
  Proof. rewrite (list_filter_iff _ (fun x => x ∈ advAddrs)); last split; auto using adv_in_pmp, pmp_in_adv.
    apply NoDup_Permutation.
    - apply NoDup_filter. rewrite all_addrs_eq. refine (bv.NoDup_seqbv _).
      now cbn -[xlenbits].
    - apply bv.NoDup_seqbv. now compute.
    - intros x. rewrite elem_of_list_filter.
      split.
      + now intros [? ?].
      + split; [auto | apply addr_in_all_addrs].
  Qed.

  Lemma big_sepL_filter `{BiAffine PROP} {A : Type} {l : list A}
      {φ : A → Prop} (dec : ∀ x, Decision (φ x)) (Φ : A -> PROP) :
    ([∗ list] x ∈ filter φ l, Φ x) ⊣⊢
    ([∗ list] x ∈ l, ⌜φ x⌝ -∗ Φ x).
  Proof. induction l.
    - now cbn.
    - cbn.
      destruct (decide (φ a)) as [Hφ|Hnφ].
      + rewrite big_opL_cons.
        rewrite <-IHl.
        iSplit; iIntros "[Ha Hl]"; iFrame; try done.
        now iApply ("Ha" $! Hφ).
      + rewrite <-IHl.
        iSplit.
        * iIntros "Hl"; iFrame; iIntros "%Hφ"; intuition.
        * iIntros "[Ha Hl]"; now iFrame.
  Qed.

  Lemma memAdv_pmpPolicy `{sailGS Σ} :
    (ptstoSthL advAddrs ⊢
      interp_pmp_addr_access liveAddrs mmioAddrs femto_pmpentries User)%I.
  Proof.
    iIntros "Hadv".
    unfold interp_pmp_addr_access.
    rewrite <-(big_sepL_filter).
    unfold ptstoSthL.
    rewrite -> (big_opL_permutation _ _ _ allAddr_filter_advAddr).
    iApply (big_sepL_mono with "Hadv"). iIntros (? ? Hsom) "Hptsto".
    unfold interp_addr_access_byte.
    apply elem_of_list_lookup_2, adv_is_live in Hsom.
    repeat case_decide; auto.
    iPureIntro. eapply mmio_ram_False; eauto.
  Qed.

  Definition femto_inv_mmio `{sailGS Σ} := interp_inv_mmio bytes_per_word.

  (* Note: temporarily make femtokernel_handler_pre opaque to prevent Gallina typechecker from taking extremely long *)
  Opaque femtokernel_handler_pre.

  Import env.notations.

  Transparent femtokernel_handler_pre.

  Definition femto_handler_pre_block1 `{sailGS Σ} a : iProp Σ :=
    asn.interpret femtokernel_handler_pre_block1 [ a ].
  Eval cbn in fun a => femto_handler_pre_block1 a.

  Definition femto_handler_post_block1 `{sailGS Σ} a an : iProp Σ :=
    asn.interpret femtokernel_handler_post_block1 [].[("a"∷ty_xlenbits) ↦ a ].[("an"∷ty_xlenbits) ↦ an ].
  Eval cbn in fun a an => femto_handler_post_block1 a an.

  Definition femto_handler_block1_contract `{sailGS Σ} : iProp Σ :=
    semTripleAnnotatedBlock femto_handler_pre_block1 (femtokernel_handler_gen_block1) femto_handler_post_block1.

  (* Note: temporarily make femtokernel_handler_pre opaque to prevent Gallina typechecker from taking extremely long *)
  Opaque femtokernel_handler_pre_block1.
  Import env.notations.

  Lemma femto_handler_verified_block1: forall `{sailGS Σ}, ⊢ femto_handler_block1_contract.
  Proof.
    iIntros (Σ sG a).
    iApply (sound_sannotated_block_verification_condition lemSemBlockVerif $! a).
    exact sat__femtohandler_block1.
  Qed.

  Transparent femtokernel_handler_pre_block1.

  Definition femto_handler_pre_block2 `{sailGS Σ} a : iProp Σ :=
    asn.interpret femtokernel_handler_pre_block2 [ a ].
  Eval cbn in fun a => femto_handler_pre_block2 a.

  Definition femto_handler_post `{sailGS Σ} a an : iProp Σ :=
    asn.interpret femtokernel_handler_post [].[("a"∷ty_xlenbits) ↦ a ].[("an"∷ty_xlenbits) ↦ an ].
  Eval cbn in fun a an => femto_handler_post a an.

  Definition femto_handler_block2_contract `{sailGS Σ} : iProp Σ :=
    semTripleAnnotatedBlock femto_handler_pre_block2 (femtokernel_handler_gen_block2) (femto_handler_post).

  (* Note: temporarily make femtokernel_handler_pre opaque to prevent Gallina typechecker from taking extremely long *)
  Opaque femtokernel_handler_pre_block2.
  Import env.notations.

  Lemma femto_handler_verified_block2: forall `{sailGS Σ}, ⊢ femto_handler_block2_contract.
  Proof.
    iIntros (Σ sG a).
    iApply (sound_sannotated_block_verification_condition lemSemBlockVerif $! a).
    exact sat__femtohandler_block2.
  Qed.

  Transparent femtokernel_handler_pre_block2.
  Opaque interp_pmp_entries.

  (* Needed when introducing the below conditional *)
  Local Instance if_persistent `{sailGS Σ} (b : bool) (A B : iProp Σ) (P: Persistent A) (P' : Persistent B)  : Persistent (if b then A else B).
  Proof. destruct b; apply _. Qed.

  Ltac set_to_list s l Hl Hel :=
    remember (elements s) as l eqn:Hel;
    assert (Hl : list_to_set l = s) by (subst; apply list_to_set_elements_L).

  Ltac set_subseteq_to_list :=
    match goal with
    | |- (?s1 : gset _) ⊆ (?s2 : gset _) =>
        let l1 := fresh "l" in
        let l2 := fresh "l" in
        let Hl1 := fresh "Hl" in
        let Hl2 := fresh "Hl" in
        let Hel1 := fresh "Hel" in
        let Hel2 := fresh "Hel" in
        set_to_list s1 l1 Hl1 Hel1;
        set_to_list s2 l2 Hl2 Hel2;
        vm_compute in Hel1;
        vm_compute in Hel2;
        rewrite <- Hl1, <- Hl2;
        apply list_to_set_subseteq;
        rewrite Hel1 Hel2
    end.

  Ltac solve_elem_of :=
    repeat (try apply elem_of_list_here;
            try apply elem_of_list_further).

  Ltac solve_list_subseteq :=
    repeat
      match goal with
      | |- []%list ⊆ ?l =>
          apply list_subseteq_nil
      | |- ?l1 ⊆ ?l2 =>
          apply list_subseteq_cons_iff
      | |- ?P ∧ ?q =>
          split
      | |- ?e ∈ ?l =>
          solve_elem_of
      end.

  Ltac solve_subseteq :=
    set_subseteq_to_list;
    solve_list_subseteq.

  Ltac reduce_big_sepS_big_sepL :=
    repeat
      match goal with
      | |- context[big_opS ?op ?f ?s] =>
          let l := fresh "l" in
          let Hl := fresh "Hl" in
          let Hel := fresh "Hel" in
          set_to_list s l Hl Hel;
          rewrite <- Hl;
          assert (Hdup : NoDup l) by (subst; apply NoDup_elements);
          rewrite (big_sepS_list_to_set _ _ Hdup);
          vm_compute in Hel;
          rewrite Hel
      end.

  Lemma femtokernel_handler_safe `{sailGS Σ} (x5_val mepc : Val ty_xlenbits) :
    ⊢ exec_instructions_prologue (bv.of_N handler_addr) (filter_AST femtokernel_handler)
      ∗ asn.interpret femtokernel_handler_pre [env].["x5" ∷ ty_xlenbits ↦ x5_val].["mepc" ∷ ty_xlenbits ↦ mepc].["a" ∷ ty_xlenbits ↦ bv.of_N handler_addr] ∗
        interp_gprs {[x1; x5]} ∗
        (∃ v, mscratch ↦ᵣ v) ∗
        interp_pmp_addr_access liveAddrs mmioAddrs femto_pmpentries User (* Not needed for handler, but required for the rest of execution *)
        -∗
        WP_loop.
  Proof.
    revert x5_val mepc.
    iLöb as "Hind".
    iIntros (x5_val mepc) "(Hpro & Hpre & Hgprs & Hmscratch & HaccU)".
    iPoseProof (contract_femtohandler_verified (bv.of_N handler_addr) x5_val mepc) as "H".
    unfold contract_femtohandler; cbn - [asn_regs_ptsto].
    iDestruct "Hpre" as "([% _] & Hmstatus & Hmtvec & Hmcause & Hmip & Hmie & Hmepc & Hcurpriv & Hx1 & Hx5 & Hpmpentries & #Hmem)".
    iPoseProof (WP_loop_semTripleBlock _ _ _ _ with "Hpro [-Hgprs Hmscratch HaccU] H") as "Hk";
      first (cbn - [asn_regs_ptsto]; iFrame "Hmstatus Hmtvec Hmcause Hmip Hmie Hmepc Hcurpriv Hpmpentries Hx1 Hx5 Hmem"; try iSplitR; try (iPureIntro; auto)).
    iApply "Hk".
    iIntros (an) "(Hpost & Hepi)".
    cbn - [asn_regs_ptsto].
    iDestruct "Hpost" as "([<- _] & Hmstatus & Hmtvec & Hmcause & Hmip & Hmie & Hmepc & Hcurpriv & Hx1x5 & Hpmpentries)".
    iDestruct "Hepi" as "(Hpc & Hinstrs & Hnpc)".
    iPoseProof (LoopVerification.valid_semTriple_loop with "[Hmem $Hmstatus $Hmtvec $Hmcause $Hmip $Hmie $Hmscratch $Hmepc $Hpc $Hcurpriv Hx1x5 Hgprs $Hpmpentries $Hnpc $HaccU Hinstrs]") as "Hk".
    { iSplitL "Hx1x5 Hgprs".
      { iApply (interp_gprs_with_excluded (exclude := {[x1; x5]}));
          try solve_subseteq.
        iFrame "Hgprs".
        reduce_big_sepS_big_sepL.
        now iDestruct "Hx1x5" as "($ & $)". }
      iSplitR; last iSplitL.
      - iModIntro.
        unfold LoopVerification.CSRMod.
        iIntros "(_ & _ & _ & %eq & _)".
        inversion eq.
      - iModIntro.
        unfold LoopVerification.Trap.
        iIntros "(HaccU & Hgprs & Hpmpentries & Hmcause & Hmip & Hmie & Hmscratch & Hcurpriv & Hnextpc & Hpc & Hmtvec & Hmstatus & Hmepc)".
        iDestruct "Hmepc" as "(%mepc & Hmepc)".
        rewrite <- (interp_gprs_with_excluded (exclude := {[x1; x5]}));
          try solve_subseteq.
        iDestruct "Hgprs" as "(Hx1x5 & Hgprs)".
        cbn.
        reduce_big_sepS_big_sepL.
        repeat try iDestruct "Hx1x5" as "([% ?] & Hx1x5)".
        iApply ("Hind" $! _ mepc).
        iFrame "Hgprs Hmstatus Hmtvec Hmcause Hmip Hmie Hmscratch Hmepc Hcurpriv Hpmpentries Hpc HaccU Hnextpc Hinstrs Hmem".
        repeat try (iRename select (_ ↦ᵣ _) into "Hpts";
                    iFrame "Hpts").
        iPureIntro; auto.
      - iModIntro.
        unfold LoopVerification.Recover.
        iIntros "(_ & _ & _ & %eq & _)".
        inversion eq.
    }
    unfold WP_loop.
    iApply (semWP_mono with "Hk"); auto.
  Qed.

  Lemma femtokernel_handler_safe_block1 `{sailGS Σ} a :
    ⊢ ▷ (femtoKernelAssumptions femto_handler_pre (bv.of_N handler_addr) -∗ WP_loop) -∗
    femtoKernelAssumptions femto_handler_pre_block1 a -∗
    WP_loop.
  Proof.
    iIntros "IH (Hbase & HaccU & (Hinstrs0 & Hinstrs1 & Hinstrs2))".
    iDestruct "Hbase" as "(Hpre & Hpc & Hnextpc)".
    iDestruct "Hpre" as "( [%Ha _] & [#Haoffset _] & Hmstatus & Hmtvec & Hmcause & [%Hmepcv Hmepc] & (%v & Hx5 & [%Htake _]) & Hpts & Hcurpriv & Hpmpentries & #Hmem)".
    iApply (femto_handler_verified_block1 with "[Hmstatus Hmtvec Hmcause Hmepc Hpts Hx5 Hcurpriv Hpmpentries Hpc Hnextpc Hinstrs1]").
    - iFrame "Hmstatus Hmtvec Hmcause Hmepc Hx5 Hpts Hcurpriv Haoffset Hmem". iFrame "Hpc Hnextpc". subst.
      iSplitL "Hpmpentries".
      -- cbn; repeat iSplit; auto.
      -- cbv in Ha. subst. iFrame "Hinstrs1".
    - cbn.
      iIntros (an) "(Hpc & Hnextpc & Hinstrs1 & [%Ha2 _] & _ & Hmstatus & Hmtvec & Hmcause & Hmepc & (%Han & _) & Hpts & Hcurpriv & Hpmpentries & _)".
      iApply (femtokernel_handler_safe_block2 with "[$IH]").
      iPoseProof (Model.RiscvPmpModel2.gprs_equiv with "Hpts") as "Hgprs".
      rewrite Han. rewrite Ha2. iFrame "Hpc Hnextpc Hmstatus Hmtvec Hmcause Hmepc Hcurpriv Hmem HaccU".
      iFrame "Hpmpentries".
      iSplitL "Hgprs"; auto.
      + cbn. subst. iSplitR. iSplitR; auto. iSplitR. iSplitR; auto.
        iPoseProof (Model.RiscvPmpModel2.gprs_equiv with "Hgprs") as "Hgprs"; auto.
      + cbn. subst. iFrame "Hinstrs0 Hinstrs1 Hinstrs2".
  Qed.

  Lemma femtokernel_handler_safe_block0 `{sailGS Σ} a :
    ⊢ femtoKernelAssumptions femto_handler_pre a -∗
      WP_loop.
  Proof.
    iLöb as "Hind".
    iIntros "(Hbase & HaccU & (Hinstrs0 & Hinstrs1 & Hinstrs2))".
    iDestruct "Hbase" as "(Hpre & Hpc & Hnextpc)".
    iDestruct "Hpre" as "( [%Ha _] & [#Haoffset _] & Hmstatus & Hmtvec & Hmcause & [%Hmepcv Hmepc] & Hpts & Hcurpriv & Hpmpentries & #Hmem)". cbv in Ha.
    iApply (femto_handler_verified_block0 with "[
           Hmstatus  Hmtvec Hmcause Hmepc Hpts Hcurpriv Hpmpentries Hmem
           $Hpc $Hnextpc Hinstrs0]").
    {
      subst. iFrame "Hinstrs0". iFrame "Hmstatus  Hmtvec Hmcause Hmepc Hpts Hcurpriv Hpmpentries Hmem Haoffset".
      auto.
    }
    iIntros "%Han (Hpc & [%Hv Hnextpc] & Hinstrs0 & Hpost0)".
    cbn.
    iDestruct "Hpost0" as "(_ & _ & Hmstatus & Hmtvec & Hmcause & Hmepc & (%t0 & Hx5 & #Hand) & Hpts & Hcurpriv & Hpmpentries & _)".
    (* Tut: We destruct over the two cases even / odd number in t0 *)
    iDestruct "Hand" as "[( [%Heven _ ] & [%Hblock1 _]) | ([%Hodd _ ] & [%Hblock2 _])]".
    - (* Tut: Case even i.e. we do not jump and therefore enter block1 *)
      iApply (femtokernel_handler_safe_block1 with "[] [HaccU Hinstrs0 Hinstrs1 Hinstrs2 $Hnextpc $Hpc $Hmstatus $Hmtvec $Hmcause $Hmepc $Hx5 $Hpts $Hcurpriv Hpmpentries $Hmem]").
      + iModIntro. iIntros "IH". cbn. subst.
        iApply "Hind".
        unfold femtoKernelAssumptions.
        iDestruct "IH" as "(Hbase & HaccU & Hinstrs)". iFrame "HaccU Hinstrs".
        iDestruct "Hbase" as "(Hpre0 & Hpc0 & Hnextpc0)".
        unfold blockVerifierAssumptions. iFrame "Hpre0 Hpc0 Hnextpc0".
      + iFrame "HaccU". iSplitL "Hpmpentries". iSplitR. auto. iSplitR. subst. auto. iSplitR. auto. cbn. subst. iFrame "Hpmpentries". cbn. subst. iFrame "Hinstrs0 Hinstrs1 Hinstrs2".
    - (* Tut: Case even i.e. we do not jump and therefore enter block1 *)
      iApply (femtokernel_handler_safe_block2 with "[]").
      + iModIntro. iIntros "IH". cbn. subst.
        iApply "Hind".
        unfold femtoKernelAssumptions.
        iDestruct "IH" as "(Hbase & HaccU & Hinstrs)". iFrame "HaccU Hinstrs".
        iDestruct "Hbase" as "(Hpre0 & Hpc0 & Hnextpc0)".
        unfold blockVerifierAssumptions. iFrame "Hpre0 Hpc0 Hnextpc0".
      + iFrame "HaccU Hpc Hnextpc Hmstatus Hmtvec Hmcause Hmepc Hcurpriv". iFrame "Hx5 Hpts Hmem". iSplitL "Hpmpentries". iSplitR. auto. iSplitR. subst. auto. cbn. subst. iFrame "Hpmpentries". cbn. subst. iFrame "Hinstrs0 Hinstrs1 Hinstrs2".
Qed.



  (* TODO: this lemma feels very incremental wrt to the last one; merge? *)
  Lemma femtokernel_manualStep2 `{sailGS Σ} :
    ⊢ (∃ mpp mpie mie, mstatus ↦ᵣ {| MPP := mpp; MPIE := mpie; MIE := mie |}) ∗
      (mtvec ↦ᵣ (bv.of_N handler_addr)) ∗
      (∃ v, mcause ↦ᵣ v) ∗
      (∃ v, mip ↦ᵣ v) ∗ (∃ v, mie ↦ᵣ v) ∗
      (∃ v, mscratch ↦ᵣ v) ∗
      (∃ v, mepc ↦ᵣ v) ∗
      cur_privilege ↦ᵣ User ∗
      interp_gprs ∅ ∗
      interp_pmp_entries femto_pmpentries ∗
      femto_inv_mmio ∗
      (pc ↦ᵣ (bv.of_N adv_addr)) ∗
      (∃ v, nextpc ↦ᵣ v) ∗
      ptsto_instrs (bv.of_N handler_addr) (filter_AnnotInstr_AST femtokernel_handler) ∗
      ptstoSthL advAddrs
      ={⊤}=∗
      ∃ mpp, LoopVerification.loop_pre User (bv.of_N handler_addr) (bv.of_N adv_addr) mpp femto_pmpentries.
  Proof.
    iIntros "([%mpp Hmst] & Hmtvec & Hmcause & Hmip & Hmie & Hmscratch & Hmepc & Hcurpriv & Hgprs & Hpmpcfg & #Hmmio & Hpc & Hnpc & Hhandler & Hmemadv)".
    iExists mpp.
    unfold LoopVerification.loop_pre, LoopVerification.Step_pre, LoopVerification.Execution.
    iFrame "Hmst Hmtvec Hmcause Hmip Hmie Hmscratch Hmepc Hcurpriv Hgprs Hpmpcfg Hpc Hnpc".
    iModIntro.

    iSplitL "Hmemadv".
    now iApply memAdv_pmpPolicy.

    iSplitL "".
    iModIntro.
    unfold LoopVerification.CSRMod.
    iIntros "(_ & _ & _ & %eq & _)".
    inversion eq.

    iSplitL.
    unfold LoopVerification.Trap.
    iModIntro.
    iIntros "(Hmem & Hgprs & Hpmpents & Hmcause & Hmip & Hmie & Hmscratch & Hcurpriv & Hnpc & Hpc & Hmtvec & Hmstatus & Hmepc)".
    iDestruct "Hmepc" as "[%mepc Hmepc]".
    iPoseProof (interp_gprs_with_excluded (exclude := {[x1; x5]}) with "Hgprs") as "(Hx1x5 & Hgprs)";
      try solve_subseteq.
    reduce_big_sepS_big_sepL.
    repeat try iDestruct "Hx1x5" as "([% ?] & Hx1x5)".
    iApply (femtokernel_handler_safe _ mepc).
    cbn.
    iFrame "Hmepc Hgprs Hpmpents Hmcause Hmip Hmie Hmscratch Hcurpriv Hnpc Hpc Hmtvec Hmstatus Hmem Hhandler Hmmio".
    repeat try (iRename select (_ ↦ᵣ _) into "Hpts";
                iFrame "Hpts").
    iSplit; cbn; auto.
    iModIntro.
    unfold LoopVerification.Recover.
    iIntros "(_ & _ & _ & %eq & _)".
    inversion eq.
  Qed.

  (* Note: temporarily make femtokernel_init_pre opaque to prevent Gallina typechecker from taking extremely long *)
  Opaque femtokernel_init_pre.
  Transparent interp_pmp_entries.

  Local Opaque femtokernel_init_gen. (* TODO: figure out why not having this makes the below proof spin in two places *)

  (* see above *)
  Transparent femtokernel_init_pre.

  Lemma femtokernel_init_safe `{sailGS Σ} :
    ⊢ exec_instructions_prologue (bv.of_N init_addr) (filter_AST femtokernel_init_gen)
      ∗ ptsto_instrs (bv.of_N handler_addr) (filter_AnnotInstr_AST femtokernel_handler)
      ∗ ptstoSthL advAddrs
      ∗ asn.interpret femtokernel_init_pre [env].["a" ∷ ty_xlenbits ↦ bv.of_N init_addr]
      ∗ interp_gprs {[x1]}
      ∗ (∃ v, mscratch ↦ᵣ v)
      ∗ femto_inv_mmio (* This is not needed for the `init` code, but it is needed later on *)
        -∗
        WP_loop.
  Proof.
    iLöb as "Hind".
    iIntros "(Hpro & Hhandler & Hadv & Hpre & Hgprs & Hmscratch & #Hmem)".
    iPoseProof (contract_femtoinit_verified (bv.of_N init_addr)) as "H".
    unfold contract_femtoinit; cbn - [asn_regs_ptsto].
    iDestruct "Hpre" as "([% _] & Hmtvec & Hmcause & Hmip & Hmie & Hmepc & Hmstatus & Hcurpriv & Hx1 & Hpmpentries)".
    iPoseProof (WP_loop_semTripleBlock _ _ _ _ with "Hpro [-Hmscratch Hhandler Hadv Hgprs] H") as "Hk";
      first (cbn - [asn_regs_ptsto]; iFrame "Hmstatus Hmtvec Hmcause Hmip Hmie Hmepc Hcurpriv Hpmpentries Hx1"; iPureIntro; auto).
    iApply "Hk".
    iIntros (an) "(Hpost & Hepi)".
    iDestruct "Hpost" as "([-> _] & Hmtvec & Hmcause & Hmip & Hmie & Hmepc & Hmstatus & Hcurpriv & Hx1 & Hpmpentries)".
    iAssert (interp_gprs ∅) with "[Hgprs Hx1]" as "Hgprs".
    { iApply (interp_gprs_with_excluded (exclude := {[x1]}));
        try solve_subseteq.
      reduce_big_sepS_big_sepL.
      now iFrame "Hx1 Hgprs". }
    iDestruct "Hepi" as "(Hpc & Hinstrs & Hnpc)".
    rewrite ?bv.add_zero_l.
    iApply (fupd_semWP ⊤).
    iMod (femtokernel_manualStep2 with "[$Hmstatus $Hmtvec $Hmcause $Hmip $Hmie $Hmscratch $Hgprs $Hcurpriv $Hpmpentries $Hpc $Hnpc $Hmepc $Hmem $Hhandler $Hadv]") as "[%mpp Hlooppre]".
    iModIntro.
    iPoseProof (LoopVerification.valid_semTriple_loop with "Hlooppre") as "Hk".
    iApply (semWP_mono with "Hk"); auto.
  Qed.
  (* THIS IS WHERE EVERYTHING HAS BEEN CHECKED TO MATCH UP. *)

  Definition mem_has_word (μ : Memory) (a : Val ty_word) (w : Val ty_word) : Prop :=
    exists v0 v1 v2 v3, map (memory_ram μ) (bv.seqBv a 4) = [v0; v1; v2; v3]%list /\ bv.app v0 (bv.app v1 (bv.app v2 (bv.app v3 bv.nil))) = w.

  (* byte order correct? *)
  Definition mem_has_instr (μ : Memory) (a : Val ty_word) (instr : AST) : Prop :=
    exists w, mem_has_word μ a w /\ pure_decode w = inr instr.

  Fixpoint mem_has_instrs (μ : Memory) (a : Val ty_word) (instrs : list AST) : Prop :=
    match instrs with
    | cons inst instrs => mem_has_instr μ a inst /\ mem_has_instrs μ (bv.add (bv.of_N 4) a) instrs
    | nil => True
    end.

  Import RiscvPmpSemantics.
  Import RiscvPmpIrisAdeqParameters.
  Import SmallStepNotations.

  Import iris.bi.big_op.
  Import iris.algebra.big_op.

  (* Note that the split differs depending on whether or not we have an MMIO region! *)
  Lemma liveAddrs_split : liveAddrs = bv.seqBv (bv.of_N init_addr) init_size ++ bv.seqBv (bv.of_N handler_addr) handler_size ++ advAddrs.
  Proof.
    (* TODO: scalable proof *)
    by compute.
  Qed.

  Lemma intro_ptstomem_word `{sailGS Σ} v0 v1 v2 v3 (a : Val ty_word) :
    interp_ptsto (bv.of_Z (0 + bv.unsigned a)) v0 ∗
    interp_ptsto (bv.of_Z (1 + bv.unsigned a)) v1 ∗
    interp_ptsto (bv.of_Z (2 + bv.unsigned a)) v2 ∗
    interp_ptsto (bv.of_Z (3 + bv.unsigned a)) v3 ⊢
      interp_ptstomem (width := 4) a (bv.app v0 (bv.app v1 (bv.app v2 (bv.app v3 bv.nil)))).
  Proof.
    iIntros "(Hmema & Hmema1 & Hmema2 & Hmema3)".
    unfold interp_ptstomem.
    rewrite ?bv.appView_app.
    replace (@bv.of_Z xlenbits (0 + bv.unsigned a)%Z) with a by now rewrite bv.of_Z_unsigned.
    replace (@bv.of_Z xlenbits (1 + bv.unsigned a)%Z) with (bv.add bv.one a) by now rewrite <-bv.of_Z_add, bv.of_Z_unsigned.
    replace (@bv.of_Z xlenbits (2 + bv.unsigned a)%Z) with (bv.add bv.one (bv.add bv.one a)).
    replace (@bv.of_Z xlenbits (3 + bv.unsigned a)%Z) with (bv.add bv.one (bv.add bv.one (bv.add bv.one a))).
    now iFrame.
    rewrite ?bv.add_assoc.
    change (bv.add _ bv.one) with (@bv.of_Z xlenbits 3).
    now rewrite <-bv.of_Z_add, bv.of_Z_unsigned.
    rewrite ?bv.add_assoc.
    now rewrite <-bv.of_Z_add, bv.of_Z_unsigned.
  Qed.

  Lemma intro_ptstomem_word2 `{sailGS Σ} {μ : Memory} {a : Val ty_word} {v : Val ty_word} :
    mem_has_word μ a v ->
    ([∗ list] a' ∈ bv.seqBv a 4, interp_ptsto a' ((memory_ram μ) a')) ⊢ interp_ptstomem a v.
  Proof.
    iIntros (Hmhw) "Hmem".
    destruct Hmhw as (v0 & v1 & v2 & v3 & Heqμ & Heqv).
    unfold bv.seqBv, seqZ. change (seq 0 ?x) with [0;1;2;3].
    cbn -[bv.add interp_ptstomem word].
    iDestruct "Hmem" as "(Hmema & Hmema1 & Hmema2 & Hmema3 & _)".
    inversion Heqμ; subst.
    now iApply (intro_ptstomem_word with "[$Hmema $Hmema1 $Hmema2 $Hmema3]").
  Qed.

  Lemma intro_ptsto_instr `{sailGS Σ} {μ : Memory} {a : Val ty_word} {instr : AST} :
    (4 + bv.bin a < bv.exp2 xlenbits)%N ->
    mem_has_instr μ a instr ->
    ([∗ list] a' ∈ bv.seqBv a 4, interp_ptsto a' ((memory_ram μ) a'))
      ⊢ interp_ptsto_instr a instr.
  Proof.
    iIntros (Hrep (v & Hmhw & Heq)) "Hmem".
    iExists v.
    iSplitL; last done.
    now iApply (intro_ptstomem_word2 Hmhw).
  Qed.

  Lemma intro_ptsto_instrs `{sailGS Σ} {μ : Memory} {a : Val ty_word} {instrs : list AST} :
    (4 * N.of_nat (length instrs) + bv.bin a < bv.exp2 xlenbits)%N ->
    mem_has_instrs μ a instrs ->
    ([∗ list] a' ∈ bv.seqBv a (4 * N.of_nat (length instrs)), interp_ptsto a' ((memory_ram μ) a'))
      ⊢ ptsto_instrs a instrs.
  Proof.
    assert (word > 0) by now compute; Lia.lia.
    iIntros (Hrep Hmeminstrs) "Hmem".
    iInduction instrs as [|instr instrs] "IH" forall (a Hrep Hmeminstrs).
    - done.
    - rewrite Nat2N.inj_succ in Hrep.
      fold (length instrs) in Hrep.
      replace (4 * N.of_nat (length (instr :: instrs)))%N with (4 + 4 * N.of_nat (length instrs))%N by (cbn; lia).
      rewrite bv.seqBv_app; try (cbn -[N.of_nat N.mul] in *; Lia.lia).
      rewrite big_opL_app.
      destruct Hmeminstrs as [Hinstr Hmeminstrs].
      iDestruct "Hmem" as "[Hmema Hmema4]".
      cbv [ptsto_instrs].
      iSplitL "Hmema".
      + iApply (intro_ptsto_instr with "Hmema"); auto; Lia.lia.
      + rewrite (@bv.add_comm _ a bv_instrsize).
        iApply ("IH" with "[%] [% //] [-]").
        * rewrite bv.bin_add_small;
          cbn -[N.mul] in *;
          now Lia.lia.
        * now rewrite ?bv.add_assoc.
  Qed.

  Lemma intro_ptstoSthL `{sailGS Σ} (μ : Memory) (addrs : list Xlenbits)  :
    ([∗ list] a' ∈ addrs, interp_ptsto a' ((memory_ram μ) a')) ⊢ ptstoSthL addrs.
  Proof.
    induction addrs as [|a l]; cbn.
    - now iIntros "_".
    - iIntros "[Hmema Hmem]".
      iSplitL "Hmema".
      + now iExists ((memory_ram μ) a).
      + now iApply IHl.
  Qed.

  Lemma sub_heap_mapsto_interp_ptsto {Σ : gFunctors} {H : sailGS Σ} {s e} (μ : Memory):
    (minAddr <= bv.bin s)%N → (bv.bin s + e <= minAddr + lenAddr)%N →
    ([∗ list] y ∈ bv.seqBv s e, gen_heap.pointsto y (dfrac.DfracOwn 1) (memory_ram μ y)) ⊢ [∗ list] a' ∈ bv.seqBv s e, interp_ptsto a' (memory_ram μ a').
  Proof.
    iIntros (Hlow Hhi) "Hlist".
    iApply (big_sepL_mono with "Hlist"). intros ? ? Hsom. cbn.
    iIntros "$". iPureIntro.
    rewrite /= /not; apply mmio_ram_False.
    apply elem_of_list_lookup_2 in Hsom.
    refine (bv.seqBv_sub_elem_of _ _ Hsom).
    - solve_bv.
    - rewrite bv.bin_of_N_small; last apply minAddr_rep. lia.
  Qed.

  Lemma femtokernel_splitMemory `{sailGS Σ} {μ : Memory} :
    mem_has_instrs μ (bv.of_N init_addr) (filter_AnnotInstr_AST femtokernel_init_gen) ->
    mem_has_instrs μ (bv.of_N handler_addr) (filter_AnnotInstr_AST femtokernel_handler) ->
    mmio_pred bytes_per_word (memory_trace μ) -> (* Either demand sensible data in memory, or a sensible history of trace events. Note that the extra handler instruction in the case of mmio is already captured by the previous conjunct *)
    @mem_res _ sailGS_memGS μ ⊢ |={⊤}=>
      ptsto_instrs (bv.of_N init_addr) (filter_AnnotInstr_AST femtokernel_init_gen) ∗
      ptsto_instrs (bv.of_N handler_addr) (filter_AnnotInstr_AST femtokernel_handler) ∗
      femto_inv_mmio ∗
      ptstoSthL advAddrs.
  Proof.
    iIntros (Hinit Hhandler0 Hhandler1 Hhandler2 Hft) "Hmem".
    unfold mem_res, initMemMap.
    rewrite liveAddrs_split.
    iDestruct "Hmem" as "[(Hinit & Hhandler & Hadv) Htr]".
    iSplitL "Hinit".
    { iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
      iApply (sub_heap_mapsto_interp_ptsto with "Hinit"); now compute. }
    iSplitL "Hhandler". (* Need to solve the goal for both handlers *)
    { iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
      iApply (sub_heap_mapsto_interp_ptsto with "Hhandler"); now compute. }
    iSplitL "Htr".
    - (* Two cases; either we set up the trace invariant o memory invariant or the trace invariant. *)
      iApply (inv.inv_alloc). iExists _; now iFrame.
    - iApply (intro_ptstoSthL μ).
      iApply (sub_heap_mapsto_interp_ptsto with "Hadv"); now compute.
  Qed.

  Lemma interp_ptsto_valid `{sailGS Σ} {μ a v} :
    ⊢ mem_inv _ μ -∗ interp_ptsto a v -∗ ⌜(memory_ram μ) a = v⌝.
  Proof.
    unfold interp_ptsto, mem_inv.
    iIntros "(%memmap & Hinv & %link & Htr) [Hptsto %Hmmio]".
    iDestruct (gen_heap.gen_heap_valid with "Hinv Hptsto") as "%x".
    iPureIntro.
    now apply (map_Forall_lookup_1 _ _ _ _ link).
  Qed.

  (* TODO: move to bitvector *)
  Lemma bv0_is_nil (x : bv 0) : x = bv.nil.
  Proof.
    destruct x as [bin wf].
    destruct bin; first by apply bv.bin_inj.
    by exfalso.
  Qed.

  (* TODO: use this lemma in earlier proofs, like `read_ram_works`? *)
  Lemma interp_ptstomem_valid `{sailGS Σ} {μ a v} :
    ⊢ mem_inv _ μ -∗ interp_ptstomem a v -∗ ⌜mem_has_word μ a v⌝.
  Proof.
    iIntros "Hinv Hptstomem".

    (* Prep hypotheses first *)
    do 4 destruct (bv.appView byte _ v) as [? v].
    (* rewrite (bv0_is_nil v). *)

    repeat iExists _.
    rewrite bv.app_nil_r. (* Get rid of annoying `nil` bv *)
    iSplit; last eauto.

    rewrite !ptstomem_bv_app.
    iDestruct "Hptstomem" as "(Ha0 & Ha1 & Ha2 & Ha3 & Htail)".
    iDestruct (interp_ptsto_valid with "Hinv Ha0") as "%Hm0".
    iDestruct (interp_ptsto_valid with "Hinv Ha1") as "%Hm1".
    iDestruct (interp_ptsto_valid with "Hinv Ha2") as "%Hm2".
    iDestruct (interp_ptsto_valid with "Hinv Ha3") as "%Hm3".

    iPureIntro.
    rewrite (bv0_is_nil v) bv.app_nil_r.
    change 4%N with (N.succ (N.succ (N.succ (N.succ N.zero)))).
    rewrite !bv.seqBv_succ !map_cons.
    repeat f_equal; auto.
  Qed.

  Transparent ptsto_instrs.
  Opaque Model.RiscvPmpModel2.gprs_equiv.

  Lemma femtokernel_endToEnd {γ γ' : RegStore} {μ μ' : Memory}
        {δ δ' : CStore [ctx]} {s' : Stm [ctx] ty.unit} :
    mem_has_instrs μ (bv.of_N init_addr) (filter_AnnotInstr_AST femtokernel_init_gen) ->
    mem_has_instrs μ (bv.of_N handler_addr) (filter_AnnotInstr_AST femtokernel_handler) ->
    mmio_pred bytes_per_word (memory_trace μ) -> (* Either demand sensible data in memory, or a sensible history of trace events. Note that the extra handler instruction in the case of mmio is already captured by the previous conjunct *)
    read_register γ mstatus = {| MPP := User; MPIE := false; MIE := false |} ->
    read_register γ cur_privilege = Machine ->
    read_register γ pmp0cfg = default_pmpcfg_ent ->
    read_register γ pmpaddr0 = bv.zero ->
    read_register γ pmp1cfg = default_pmpcfg_ent ->
    read_register γ pmpaddr1 = bv.zero ->
    read_register γ pc = (bv.of_N init_addr) ->
    ⟨ γ, μ, δ, fun_loop ⟩ --->* ⟨ γ', μ', δ', s' ⟩ ->
    mmio_pred bytes_per_word (memory_trace μ') (* The initial demands hold over the final state *).
  Proof.
    intros μinit μhandler0 μhandler1 μhandler2 μft γcurpriv γpmp0cfg γpmpaddr0 γpmp1cfg γpmpaddr1 γpc steps.
    refine (adequacy_gen (Q := fun _ _ _ _ => True%I) _ steps _).
    iIntros (Σ' H).
    cbn.
    iIntros "(Hmem & Hpc & Hnpc & Hmstatus & Hmie & Hmip & Hmtvec & Hmscratch & Hmepc & Hmcause & Hcurpriv & H')".
    rewrite γmstatus γcurpriv γpmp0cfg γpmpaddr0 γpmp1cfg γpmpaddr1 γpc.
    iMod (femtokernel_splitMemory with "Hmem") as "(Hinit & Hhandler & #Hmmio & Hadv)";
      try assumption.
    iModIntro.
    iSplitL.
    - destruct (env.view δ).

      iApply (femtokernel_init_safe with "[-]").

      #[local] Opaque ptsto_instrs. (* Avoid spinning because code is unfolded *)
      iFrame "∗ #". cbn.
      rewrite <- ?bi.sep_assoc.
      iSplitR; first auto.
      rewrite <- ?bi.sep_assoc.
      unfold interp_gprs; reduce_big_sepS_big_sepL; cbn.
      now repeat iDestruct "H'" as "($ & H')".
      Unshelve. all: constructor.
    - iIntros "Hmem".
      iInv "Hmmio" as (t) ">[Hfrag %Hpred]" "_".
      iDestruct "Hmem" as "(%memmap & Hinv & %link & Htr)".
      iDestruct (trace.trace_full_frag_eq with "Htr Hfrag") as "->".
      iApply fupd_mask_intro; first apply empty_subseteq.
      now iIntros "_".
  Qed.

(* Print Assumptions femtokernel_endToEnd. *)


(* Local Variables: *)
(* proof-omit-proofs-option: t *)
(* End: *)
