# AST constructor vocabulary + register aliases (reference)

Loaded on demand from **cfgver-new-example** (step 1) — never self-triggers.
Everything needed to hand-author or read an RV32I `list AST` program without
grepping `Base.v`/`Tables.v`/`Spec.v` from scratch. Not needed when
`asm_to_ast.py` does the translation — it emits these constructors directly.

## Register aliases (`Tables.v`)

`RegIdx` is a `bv 5` (0–31). Aliases in scope after `Import Assembly.`:

| Alias | Index | Alias | Index |
|-------|------:|-------|------:|
| `X0`–`X4` | 0–4 | `T0`/`T1` | 5/6 |
| `A0`–`A7` | 10–17 | | |

`X0` is architecturally hardwired to 0 (`Machine.v`'s `rX`/`wX` special-case
it) — never usable as a general-purpose base-holding register (see
`countdown_mem`'s `X0`→`X2` rewrite in `cfgver-gen-contract`). No aliases
exist for x7–x9/x18–x31; use `bv.of_nat n` directly if one is ever needed.

## The `AST` inductive (`RiscvPmp/Base.v`)

Field order matters — every hand-authored instruction must match it exactly:

```coq
| RTYPE (rs2 rs1 rd : RegIdx) (op : ROP)
| ITYPE (imm : bv 12) (rs1 rd : RegIdx) (op : IOP)
| SHIFTIOP (shamt : bv 6) (rs1 rd : RegIdx) (op : SOP)
| UTYPE (imm : bv 20) (rd : RegIdx) (op : UOP)
| BTYPE (imm : bv 13) (rs2 rs1 : RegIdx) (op : BOP)
| RISCV_JAL (imm : bv 21) (rd : RegIdx)
| RISCV_JALR (imm : bv 12) (rs1 rd : RegIdx)
| LOAD (imm : bv 12) (rs1 rd : RegIdx) (is_unsigned : bool) (width : WordWidth)
| STORE (imm : bv 12) (rs2 rs1 : RegIdx) (width : WordWidth)
| ECALL | EBREAK | MRET
| CSR (csr : CSRIdx) (rs1 rd : RegIdx) (is_imm : bool) (csrop : CSROP)
| MUL (rs2 rs1 rd : RegIdx) (high signed1 signed2 : bool)
```

Opcode enums (`ROP`/`IOP`/`SOP`/`UOP`/`BOP`, also `Base.v`):

- `ROP` (`RTYPE`): `RISCV_ADD/SLT/SLTU/AND/OR/XOR/SLL/SRL/SUB/SRA`
- `IOP` (`ITYPE`): `RISCV_ADDI/SLTI/SLTIU/ANDI/ORI/XORI`
- `SOP` (`SHIFTIOP`): `RISCV_SLLI/SRLI/SRAI`
- `UOP` (`UTYPE`): `RISCV_LUI/AUIPC`
- `BOP` (`BTYPE`): `RISCV_BEQ/BNE/BLT/BGE/BLTU/BGEU`
- `WordWidth` (`LOAD`/`STORE`): `BYTE/HALF/WORD`

## Assembler-mnemonic notations (`Spec.v` `Module Assembly`, `Tables.v`)

These are what every `Example/*.v` actually writes; they wrap the raw
constructors above (argument order is *mnemonic* order, not necessarily
constructor-field order — note `BEQ`/`BNE`'s `rs1 rs2` vs `BTYPE`'s `rs2 rs1`):

```coq
ADD  rd rs1 rs2  := RTYPE rs2 rs1 rd RISCV_ADD
SUB  rd rs1 rs2  := RTYPE rs2 rs1 rd RISCV_SUB
BEQ  rs1 rs2 imm := BTYPE imm rs2 rs1 RISCV_BEQ
BNE  rs1 rs2 imm := BTYPE imm rs2 rs1 RISCV_BNE
ADDI rd rs1 imm  := ITYPE imm rs1 rd RISCV_ADDI
JALR rd rs1 imm  := RISCV_JALR imm rs1 rd
RET              := JALR X0 X1 0            (* return address in X1 *)
MV   rd rs1      := ADDI rd rs1 0
MUL/MULH/MULHSU rd rs1 rs2 := Base.MUL rs2 rs1 rd <flags>
JAL  rd imm      := RISCV_JAL imm rd         (* Tables.v *)
LW   rd rs imm   := LOAD imm rs rd false WORD (* Tables.v *)
SW   rs2 rs1 imm := STORE imm rs2 rs1 WORD    (* Tables.v *)
NOP              := MV X0 X0                  (* Tables.v *)
```

`RTYPE`/`LOAD`/`STORE` are also used directly (unwrapped) in most examples,
e.g. `RTYPE A2 A1 A1 RISCV_AND` (`and a1,a1,a2`) or
`STORE (bv.of_Z 0) A0 A3 WORD` (`sw a0,0(a3)`).

## Branch-immediate encoding (the hand-authoring pitfall)

`imm` in `BTYPE`/`RISCV_JAL`/`RISCV_JALR` is **relative to that instruction's
own pc**, not to the loop body's length or any other instruction's address —
`target_pc = branch_pc + imm`. For a backward branch closing an N-instruction
loop whose branch is the loop's *last* (Nth, 0-indexed instruction N-1)
instruction, jumping back to instruction 0 needs
`imm = 0 - (N-1)*4 = -((N-1)*4)`, encoded as a `bv 13` two's-complement
literal: `bv.of_N (8192 - (N-1)*4)`. Existing examples: `countdown` (N=2) uses
`bv.of_N 8188` (`-4`); `countdown_mem` (N=4) uses `bv.of_N 8180` (`-12`). Getting
this wrong (e.g. using `-(N*4)`, the total code length, instead of `-((N-1)*4)`)
does not error at `vm_compute` — it silently sends the taken branch to an
address with no mapped instruction, which surfaces many steps later as an
unprovable bare `False` deep in the VC (→ **cfgver-solve-vc**'s residual
table has the reverse pointer back here).
