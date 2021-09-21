# Case Study: RISC-V with PMP 
Case study for (base) RISC-V with Physical Memory Protection (PMP).

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

## Source

This machine is based on a minimal model of the official RISC-V Sail model.
The corresponding model can be found at [https://gitlab.soft.vub.ac.be/shuygheb/sail-minimal-riscv](sail-minimal-riscv).

The machine that this case study represents is based on the official RISC-V code, more specifically, (parts of) the following files:
- [https://github.com/rems-project/sail-riscv/blob/master/model/riscv_insts_base.sail](Base Instructions)
- [https://github.com/rems-project/sail-riscv/blob/master/model/riscv_pmp_regs.sail](PMP Configuration)
- [https://github.com/rems-project/sail-riscv/blob/master/model/riscv_pmp_control.sail](PMP)

## Machine Invariant
TODO
