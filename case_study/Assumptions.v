
Require
  Katamaran.MinimalCaps.LoopVerification
  Katamaran.RiscvPmp.FemtoKernel
  Katamaran.RiscvPmp.LoopVerification
  Katamaran.RiscvPmpBoundedInts.FemtoKernel
  Katamaran.RiscvPmpBoundedInts.LoopVerification.

Goal True. idtac "Assumptions of MinimalCaps universal contract:". Abort.
Print Assumptions MinimalCaps.LoopVerification.valid_semContract_loop2.

Goal True. idtac "Assumptions of Risc-V PMP universal contract (unbounded ints):". Abort.
Print Assumptions RiscvPmp.LoopVerification.valid_semTriple_loop.

Goal True. idtac "Assumptions of FemtoKernel verification (unbounded ints):". Abort.
Print Assumptions RiscvPmp.FemtoKernel.femtokernel_init_safe.

Goal True. idtac "Assumptions of femtokernel end-to-end theorem (unbounded ints):". Abort.
Print Assumptions RiscvPmp.FemtoKernel.femtokernel_endToEnd.

Goal True. idtac "Assumptions of Risc-V PMP universal contract (bounded ints, byte-addressing):". Abort.
Print Assumptions RiscvPmpBoundedInts.LoopVerification.valid_semTriple_loop.

Goal True. idtac "Assumptions of FemtoKernel verification (bounded ints, byte-addressing):". Abort.
Print Assumptions RiscvPmpBoundedInts.FemtoKernel.femtokernel_init_safe.

Goal True. idtac "Assumptions of femtokernel end-to-end theorem (bounded ints, byte-addressing):". Abort.
Print Assumptions RiscvPmpBoundedInts.FemtoKernel.femtokernel_endToEnd.
