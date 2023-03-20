# Case Study: RISC-V with PMP 
Case study for (base) RISC-V with Physical Memory Protection (PMP).

Focus is on RV32I, with the PMP extension.
Remarks/Comments/Info:
- instructions with "W" suffix are not implemented (these are for RV64 and are variants that operate only on the lower 32 bits of a doubleword)
- fence instructions not implemented, our model is simple and sequential, updates to registers and memory happen instantly
- WFI (wait for interrupt) instruction not implemented, focus in this model is on exceptions, not interrupts
- store & load instructions are simplified (i.e. no size, always word, no sign/zero extension, no aq or rl
- keep AccessType simple (i.e. no type parameter for extensions, this is ignored in the PMP related code anyway), but still represent it as a *union* (note that we could opt to represent this as an enum, but this way is more faithful to the (simplified) Sail model)
- the model does not support S-mode, so any checks/pattern matches that depend on M-mode and S-mode privileges are simplified to only consider the M-mode case
- some auxiliary functions that convert bits to enums are dropped, the model uses the enum immediately (example: pmpAddrRange calls a function pmpAddrMatchType_of_bits that converts a bitvector into the corresponding enum value of PmpAddrMatchType)
- note that the main loop (function "loop") just calls the step function, this is a lot simpler than the one in the actual sail model, which is complicated with tracing, interrupts, ...
- step function shortened, dropped extension related code, also not doing anything with the "retire" result of an execution (has to do with "minstret", doesn't seem relevant for our case study at this point)
  + have kept the "stm_lit ty_retire RETIRE_SUCCESS/FAIL" stmts tho, can however drop this? (TODO: consider)
- the fetch function is simplified, in the sail model it reads 16 bits at a time (to support the compressed extension), in our case we read the entire instruction at once (no support for the compressed extension) (this also means our fetchresult type is simplified)
- trap vector register (mtvec) is limited to only direct mode, i.e. we don't include "mode" bit and take the address in mtvec as is
- the mcause register is limited to just contain an exception code, this suffices for our purposes
- No alignment checks
- exception_delegatee is simplified, note that we can never transition to a less-privileged mode, resulting in this function always returning M-mode (we only have M-mode and U-mode support)
- mem related function are simplified and some auxiliary functions are inlined (see riscv_mem.sail, example: mem_write_value calls mem_write_value_meta, which is inlined in our model)
- mstatus is limited to those fields we require. The fields themselves are also *NOT* bits but rather the corresponding non-bit representation (for example: MPP is normally a 2-bit field of mstatus but in our model is a field that will contain Privilege enum value), this means that we don't need the conversion functions from/to bits

## Translation Notes
Inline function call expressions get translated into
```
# ...
# | RISCV_AUIPC => get_arch_pc() + off
# ==>
| RISCV_AUIPC => 
	let: tmp := call get_arch_pc in
	tmp + off
```

Currently omitting alignment related checks and exceptions (bitvector support needed for this).
-> OR simply check if address is divisible by 4?

Ignoring instructions that rely on bitvector operations (like shift operations), this mostly affects the support for RTYPE- and ITYPE-instructions.

## Source

This machine is based on a minimal model of the official RISC-V Sail model.

The machine that this case study represents is based on the official RISC-V code, more specifically, (parts of) the following files:
- [Base Instructions](https://github.com/rems-project/sail-riscv/blob/master/model/riscv_insts_base.sail)
- [PMP Configuration](https://github.com/rems-project/sail-riscv/blob/master/model/riscv_pmp_regs.sail)
- [PMP](https://github.com/rems-project/sail-riscv/blob/master/model/riscv_pmp_control.sail)
