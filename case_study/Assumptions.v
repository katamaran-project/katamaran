
Require
  Katamaran.MinimalCaps.LoopVerification
  Katamaran.RiscvPmp.FemtoKernel
  Katamaran.RiscvPmp.LoopVerification.
Import Coq.Numbers.BinNums Coq.Strings.String Bitvector.

Goal True. idtac "Assumptions of MinimalCaps universal contract:". Abort.
Print Assumptions MinimalCaps.LoopVerification.valid_semContract_loop2.

Goal True. idtac "Assumptions of Risc-V PMP universal contract:". Abort.
Print Assumptions RiscvPmp.LoopVerification.valid_semTriple_loop.

Goal True. idtac "Assumptions of FemtoKernel verification:". Abort.
Print Assumptions RiscvPmp.FemtoKernel.femtokernel_init_safe.

Goal True. idtac "Assumptions of femtokernel end-to-end theorem:". Abort.
Print Assumptions RiscvPmp.FemtoKernel.femtokernel_endToEnd.
