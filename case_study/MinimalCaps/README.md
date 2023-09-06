# MinimalCaps

The MinimalCaps machine is a subset of CHERI-RISC-V, focusing on the capability
related instructions and with some simplifications such as unbounded integers
and no byte-addressing. The universal contract we prove is based on the Cerise
work. At the end of this file we provide a paper-to-artifact correspondence.

## How To Build

This case study is part of the overall Katamaran build. When Katamaran is build,
MinimalCaps will have been build as well. For instructions see: `README.md`.

## Case Study Structure
All files mentioned in this section are relative to `case_study/MinimalCaps/`.

- `Base.v`: contains type declarations and hooks these into the appropriate Katamaran
  modules.
- `Machine.v`: contains the ISA specification in μSail. All functions are declared here,
  as well as the foreign functions and signatures of the lemmas.
- `Contracts.v`: contains the pure predicates, spatial predicate signatures and
  user solver. Also contains the contract definitions and lemmas showing that
  the defined contracts are valid. We also define contracts for foreign
  functions and the lemmas of the case study (but these are proved in the `Model.v`).
- `Model.v`: is the Iris part of the verification, we define an interpretation for each
  spatial predicate and prove the soundness of the foreign functions and lemmas.
- `LoopVerification.v`: is where the universal contract is proven, this happens over
  the fdeCycle (i.e., the loop of the machine).

## Instructions

| Cerise   | MinimalCaps (⊆ CHERI-RISC-V)                                                 |
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

## Paper-to-Artifact Correspondence

| Paper                         | File                                        | Definition                               |
|-------------------------------|---------------------------------------------|------------------------------------------|
| Figure 4: Store instruction   | `case_study/MinimalCaps/Machine.v`          | Definition fun\_exec\_sd                 |
| Figure 5: 𝒱(z)                | `case_study/MinimalCaps/Model.v`            | Definition interp\_z                     |
| Figure 5: 𝒱(O, -, -, -)       | `case_study/MinimalCaps/Model.v`            | Definition interp\_cap\_O                |
| Figure 5: 𝒱(R, _b_, _e_, -)   | `case_study/MinimalCaps/Model.v`            | Definition interp\_cap\_R                |
| Figure 5: 𝒱(RW, _b_, _e_, -)  | `case_study/MinimalCaps/Model.v`            | Definition interp\_cap\_RW               |
| Figure 5: 𝒱(E, _b_, _e_, _a_) | `case_study/MinimalCaps/Model.v`            | Definition interp\_cap\_E                |
| Figure 5: ℰ(_w_)              | `case_study/MinimalCaps/Model.v`            | Definition interp\_expr                  |
| Figure 6: UC Definition       | `case_study/MinimalCaps/LoopVerification.v` | Definition semContract\_loop             |
| Figure 6: UC Verif.           | `case_study/MinimalCaps/LoopVerification.v` | Lemma valid\_semContract\_loop2          |
| Figure 10: Store contract     | `case_study/MinimalCaps/Contracts.v`        | Definition sep\_contract\_exec\_sd       |
| Figure 10: Store verif.       | `case_study/MinimalCaps/Contracts.v`        | Lemma valid\_contract\_exec\_sd          |
| Figure 11: read\_mem          | `case_study/MinimalCaps/Contracts.v`        | Definition sep\_contract\_read\_mem      |
| Figure 11: read\_reg          | `case_study/MinimalCaps/Contracts.v`        | Definition sep\_contract\_read\_reg      |
| Figure 11: read\_reg\_cap     | `case_study/MinimalCaps/Contracts.v`        | Definition sep\_contract\_read\_reg\_cap |
| Figure 11: write\_mem         | `case_study/MinimalCaps/Contracts.v`        | Definition sep\_contract\_write\_mem     |
| Figure 11: update\_pc         | `case_study/MinimalCaps/Contracts.v`        | Definition sep\_contract\_update\_pc     |
| Figure 11: move\_cursor       | `case_study/MinimalCaps/Contracts.v`        | Definition lemma\_safe\_move\_cursor     |
| Figure 11: subperm\_not\_E    | `case_study/MinimalCaps/Contracts.v`        | Definition lemma\_subperm\_not\_E        |
