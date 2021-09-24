# Case Study: RISC-V with PMP 
Case study for (base) RISC-V with Physical Memory Protection (PMP).

Focus is on RV32I, with the PMP extension.
Remarks/Comments/Info:
- instructions with "W" suffix are not implemented (these are for RV64 and are variants that operate only on the lower 32 bits of a doubleword)
- fence instructions not implemented, our model is simple and sequential, updates to registers and memory happen instantly
- WFI (wait for interrupt) instruction not implemented, focus in this model is on exceptions, not interrupts
- store & load instructions are simplified (i.e. no size, always word, no sign/zero extension, no aq or rl
- keep AccessType simple (i.e. no type parameter for extensions, this is ignored in the PMP related code anyway), but still represent it as a *union* (note that we could opt to represent this as an enum, but this way is more faithful to the (simplified) Sail model)
- MemoryOpResult is simplified and MemValue can only be a Word (no type param in definition of MemoryOpResult, this complicates EqDec...)
- Store instructions involve a function mem_write that returns a MemoryOpResult with a boolean value to indicate failure, to keep things simple (point above), I model this as a ty_word where 0 = false and 1 = true

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

Currently ommitting alignment related checks and exceptions (bitvector support needed for this).
-> OR simply check if address is divisible by 4? (currently added empty alignment check function, "address_aligned")

Ignoring instructions that rely on bitvector operations (like shift operations), this mostly affects the support for RTYPE- and ITYPE-instructions.

## Source

This machine is based on a minimal model of the official RISC-V Sail model.
The corresponding model can be found at [https://gitlab.soft.vub.ac.be/shuygheb/sail-minimal-riscv](sail-minimal-riscv).

The machine that this case study represents is based on the official RISC-V code, more specifically, (parts of) the following files:
- [https://github.com/rems-project/sail-riscv/blob/master/model/riscv_insts_base.sail](Base Instructions)
- [https://github.com/rems-project/sail-riscv/blob/master/model/riscv_pmp_regs.sail](PMP Configuration)
- [https://github.com/rems-project/sail-riscv/blob/master/model/riscv_pmp_control.sail](PMP)

## Machine Invariant
TODO
