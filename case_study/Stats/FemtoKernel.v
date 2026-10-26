(* Size statistics of the femtokernel block verification conditions. *)

From Stdlib Require Import
     NArith.NArith
     Strings.String
     Lists.List.
From Katamaran Require Import
     Base
     Bitvector
     RiscvPmp.Machine
     RiscvPmp.Logic
     RiscvPmp.Contracts
     RiscvPmp.BlockVer.Spec
     RiscvPmp.BlockVer.PartialVerifier
     RiscvPmp.FemtoKernel.

Import Sig.RiscvPmpSignature.
Import RiscvPmpBlockVerifSpec.
Import RiscvPmpExecutor.
Import Assembly.
Import SymProp.Statistics.
Import ListNotations.

(* Number of instructions, then [raw; postprocess; postprocess2 (the VC used in
   FemtoKernel.v)]. *)
Definition block_stats {Σ} pre b post : N * list (list N) :=
  let vc := @TotalVerifier.sannotated_block_verification_condition Σ pre b post wnil in
  (N.of_nat (length (filter_AnnotInstr_AST b)),
   [vc_count_to_list (vc_count vc vc_count_empty);
    vc_count_to_list (vc_count (postprocess vc) vc_count_empty);
    vc_count_to_list (vc_count (postprocess2 vc) vc_count_empty)]).

Ltac showb name t :=
  let r := eval vm_compute in t in idtac name r.

Goal True.
  Time showb "VCSTAT femto_init"
    (block_stats femtokernel_init_pre femtokernel_init_gen femtokernel_init_post).
  Time showb "VCSTAT femto_handler_entry"
    (block_stats femtokernel_handler_entry_pre femtokernel_handler_entry femtokernel_handler_entry_post).
  Time showb "VCSTAT femto_handler_write"
    (block_stats femtokernel_handler_write_pre femtokernel_handler_write femtokernel_handler_write_post).
  Time showb "VCSTAT femto_handler_secret_write"
    (block_stats femtokernel_handler_secret_write_pre femtokernel_handler_secret_write femtokernel_handler_secret_write_post).
  Time showb "VCSTAT femto_handler_exit"
    (block_stats femtokernel_handler_exit_pre femtokernel_handler_exit femtokernel_handler_exit_post).
Abort.
