# Cerise Comparison

## Instructions

| Cerise   | MinimalCaps (CHERI-RISC-V)                                                   |
|----------|------------------------------------------------------------------------------|
| Fail     | Fail (“Illegal”1)                                                            |
| Halt     | Ret (“HLT”2)                                                                 |
| Jmp      | Jalr.cap(cd, cs), CJalr(cd, cs, imm), CJal(cd, imm)                          |
| Jnz      | Bne(rs1, rs2, imm)                                                           |
| Load     | Ld(rd, rs, imm)                                                              |
| Store    | Sd(rs1, rs2, imm)                                                            |
| Mov      | CMove(cd, cs) (int move = addi)                                              |
| Lea      | CIncOffset(cd, cs, rs)                                                       |
| Restrict | CAndPerm(cd, cs, rs)                                                         |
| Add      | Add(rd, rs1, rs2), Addi(rd, rs, imm)                                         |
| Sub      | Sub(rd, rs1, rs2)                                                            |
| Lt       | Slt(rd, rs1, rs2), Slti(rd, rs, imm), Sltu(rd, rs1, rs2), Sltiu(rd, rs, imm) |
| Subseg   | CSetBounds(cd, cs, rs), CSetBoundsImm(cd, cs, imm)                           |
| GetA     | CGetAddr(rd, cs)                                                             |
| GetB     | CGetBase(rd, cs)                                                             |
| GetE     | CGetLen(rd, cs)                                                              |
| GetP     | CGetPerm(rd, cs)                                                             |
| IsPtr    | CGetTag(rd, cs)                                                              |

1: No literal “fail” instruction, but the effect can be achieved with any illegal instruction encoding (for example, writing “HLT” or “FAIL” as an instruction)

2: The Ret of RISC-V will return from the subroutine, i.e., giving control back to the caller, an actual halt can be achieved similar to Fail
