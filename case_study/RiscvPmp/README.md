# Case Study: RISC-V with PMP 
Case study for RISC-V (RV32I) with Physical Memory Protection (PMP).


## How To Build
This case study is part of the overall Katamaran build. When Katamaran is build,
MinimalCaps will have been build as well. For instructions see: `README.md`.

## Case Study Structure
All files mentioned in this section are relative to `case_study/RiscvPmp/`.

- `Base.v`: contains type declarations and hooks these into the appropriate Katamaran
  modules.
- `Machine.v`: contains the ISA specification in μSail. All functions are declared here,
  as well as the foreign functions and signatures of the lemmas.
- `Sig.v`: contains the pure predicates, spatial predicate signatures and
  user solver.
- `Contracts.v`: contains the contract definitions and lemmas showing that
  the defined contracts are valid. We also define contracts for foreign
  functions and the lemmas of the case study (but these are proved in the `Model.v`).
- `IrisModel.v`: instantiates the Iris requirements of Katamaran.
- `IrisInstance.v`: defines the interpretation of spatial predicates.
- `Model.v`: is the Iris part of the verification, here we prove the soundness
  of the foreign functions and lemmas.
- `LoopVerification.v`: is where the universal contract is proven, this happens over
  the fdeCycle (i.e., the loop of the machine).
- `BlockVer/Verifier.v`: is the block verifier, providing definitions and lemmas
  to generate the verification conditions of blocks.
- `BlockVer/Spec.v`: contains the specification for the block verifier to verify
  the FemtoKernel.
- `FemtoKernel.v`: the FemtoKernel verification itself.

## Paper-to-Artifact Correspondence

| Paper                                 | File                                     | Definition                         |
|---------------------------------------|------------------------------------------|------------------------------------|
| Figure 7: UC Definition               | `case_study/RiscvPmp/LoopVerification.v` | Definition semTriple_loop          |
| Figure 7: UC verif.                   | `case_study/RiscvPmp/LoopVerification.v` | Lemma valid_semTriple_loop         |
| Figure 7: Normal                      | `case_study/RiscvPmp/LoopVerification.v` | Definition Step_pre                |
| Figure 7: Trap                        | `case_study/RiscvPmp/LoopVerification.v` | Definition Trap                    |
| Figure 8: PMP_addr_access             | `case_study/RiscvPmp/IrisInstance.v`     | Definition interp_pmp_addr_access  |
| Figure 12: read_ram contract          | `case_study/RiscvPmp/Contracts.v`        | Definition sep_contract_read_ram   |
| Figure 12: read_ram verif.            | `case_study/RiscvPmp/Model.v`            | Lemma read_ram_sound               |
| Figure 12: write_ram contract         | `case_study/RiscvPmp/Contracts.`         | Definition sep_contract_write_ram  |
| Figure 12: write_ram verif.           | `case_study/RiscvPmp/Model.v`            | Lemma write_ram_sound              |
| Figure 13: Step contract              | `case_study/RiscvPmp/Contracts.v`        | Definition sep_contract_step       |
| Figure 13: Step verif.                | `case_study/RiscvPmp/Contracts.v`        | Lemma valid_contract_step          |
| Figure 14: open_PMP_entries contract  | `case_study/RiscvPmp/Contracts.v`        | Definition lemma_open_pmp_entries  |
| Figure 14: open_PMP_entries verif.    | `case_study/RiscvPmp/Model.v`            | Lemma open_pmp_entries_sound       |
| Figure 14: extract_PMP_ptsto contract | `case_study/RiscvPmp/Contracts.v`        | Definition lemma_extract_pmp_ptsto |
| Figure 14: extract_PM_ptsto verif.    | `case_study/RiscvPmp/Model.v`            | Lemma extract_pmp_ptsto_sound      |
| Figure 14: return_PMP_ptsto contract  | `case_study/RiscvPmp/Contracts.v`        | Definition lemma_return_pmp_ptsto  |
| Figure 14: return_PMP_ptsto verif.    | `case_study/RiscvPmp/Model.v`            | Lemma return_pmp_ptsto_sound       |
| Figure 15: FemtoKernel kernel         | `case_study/RiscvPmp/FemtoKernel.v`      | Example femtokernel_init           |
| Figure 15: FemtoKernel ih             | `case_study/RiscvPmp/FemtoKernel.v`      | Example femtokernel_handler        |
| Figure 15: FemtoKernel end-to-end     | `case_study/RiscvPmp/FemtoKernel.v`      | Lemma femtokernel_endToEnd         |

## Remarks
Focus is on RV32I, with the PMP extension.
Remarks/Comments/Info:
- instructions with "W" suffix are not implemented (these are for RV64 and are variants that operate only on the lower 32 bits of a doubleword)
- fence instructions not implemented, our model is simple and sequential, updates to registers and memory happen instantly
- WFI (wait for interrupt) instruction not implemented, focus in this model is on exceptions, not interrupts
- keep AccessType simple (i.e. no type parameter for extensions, this is ignored in the PMP related code anyway), but still represent it as a *union* (note that we could opt to represent this as an enum, but this way is more faithful to the Sail model)
- the model does not support S-mode, so any checks/pattern matches that depend on M-mode and S-mode privileges are simplified to only consider the M-mode case
- note that the main loop (function "loop") just calls the step function, this is a lot simpler than the one in the actual sail model, which is complicated with tracing, interrupts, ...
- step function shortened, dropped extension related code, also not doing anything with the "retire" result of an execution (has to do with "minstret", doesn't seem relevant for the case study)
- the fetch function is simplified, in the sail model it reads 16 bits at a time (to support the compressed extension), in our case we read the entire instruction at once (no support for the compressed extension) (this also means our fetchresult type is simplified)
- trap vector register (mtvec) is limited to only direct mode, i.e. we don't include "mode" bit and take the address in mtvec as is
- the mcause register is limited to just contain an exception code, this suffices for our purposes
- No alignment checks
- exception_delegatee is simplified, note that we can never transition to a less-privileged mode, resulting in this function always returning M-mode (we only have M-mode and U-mode support)
- mem related function are simplified and some auxiliary functions are inlined (see riscv_mem.sail, example: mem_write_value calls mem_write_value_meta, which is inlined in our model)
- mstatus is limited to those fields we require. The fields themselves are also *NOT* bits but rather the corresponding non-bit representation (for example: MPP is normally a 2-bit field of mstatus but in our model is a field that will contain Privilege enum value), this means that we don't need the conversion functions from/to bits

## Source

This machine is based on a minimal model of the official RISC-V Sail model.

The machine that this case study represents is based on the official RISC-V code, more specifically, (parts of) the following files:
- [https://github.com/rems-project/sail-riscv/blob/master/model/riscv_insts_base.sail](Base Instructions)
- [https://github.com/rems-project/sail-riscv/blob/master/model/riscv_pmp_regs.sail](PMP Configuration)
- [https://github.com/rems-project/sail-riscv/blob/master/model/riscv_pmp_control.sail](PMP)
