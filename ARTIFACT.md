# CCS 2023 Artifact
Paper: Formalizing, Verifying and Applying ISA Security Guarantees as Universal Contracts

This artifact contains the Coq development providing the evidence for the paper. At the end of this
document we provide a paper-to-artifact correspondence. The code itself is documented as well.

The easiest way to get started is by downloading [katamaran-ccs23.tar.gz](https://github.com/katamaran-project/katamaran/releases/download/ccs23/katamaran-ccs23.tar.gz), the prebuilt image, and loading it into Docker:
```bash
docker load < katamaran-ccs23.tar.gz
docker run -it --rm katamaran/ccs23
```

## Overview
The supplementary material of our paper consists of Katamaran, our mechanized
separation logic verifier for the Sail language, and the MinimalCaps and RISC-V
PMP case studies.

The different parts can be found in the following directories

| Part                   | Directory                |
|------------------------|--------------------------|
| Kataraman              | `theories`               |
| MinimalCaps            | `case_study/MinimalCaps` |
| RISC-V 32-bit with PMP | `case_study/RiscvPmp`    |

The assumptions, i.e. unimplemented or unproven parts, can be printed with the
Coq command [`Print Assumptions`](https://coq.inria.fr/refman/proof-engine/vernacular-commands.html#coq:cmd.Print-Assumptions).
We have already added these commands to the code in the `case_study/Assumptions.v` file for the key theorems.

The following table contains `make` commands that can be used for this artifact:
| Command            | Description                                                                                                                       |
|--------------------|-----------------------------------------------------------------------------------------------------------------------------------|
| `make`             | Runs the default command that builds the entire project.                                                                          |
| `make assumptions` | Forces recompilation of the `case_study/Assumptions.v` file, outputting the result of the different `Print Assumptions` commands. |
| `make patch`       | Applies the patches that add a duplicate instruction (`add`) to the case studies.                                                 |
| `make unpatch`     | Removes the patches introduced by running `make patch`, i.e., it reverses the above command.                                      |

### Katamaran
The Katamaran development can be found in the `theories/` directory. As mentioned in the paper, Katamaran is implemented and
proven sound using Kripke specification monads. In this artifact we focus on universal contracts and our case studies.
Those interested in the internals of Katamaran can take a look at its dedicated artifact and documentation:
[Katamaran artifact](https://doi.org/10.5281/zenodo.6865817).

### MinimalCaps
The code for MinimalCaps can be found in the `case_study/MinimalCaps/` directory.
In the MinimalCaps case study, we verify a universal contract enforcing a
capability-safety property. The following table lists the contents of the
different files comprising this case study.

| File                             | Description                                                                                        |
|----------------------------------|----------------------------------------------------------------------------------------------------|
| `MinimalCaps/Base.v`             | Background theory for case study-specific datatypes and machine registers                          |
| `MinimalCaps/Machine.v`          | The definitional interpreter for the ISA implemented in μSail                                      |
| `MinimalCaps/Contracts.v`        | - Declaration of spatial and pure predicates                                                       |
|                                  | - Solver for pure predicates                                                                       |
|                                  | - Definition of contracts and ghost lemmas statements                                              |
|                                  | - (Semi-)automatic verification of the μSail function with Katamaran's symbolic executor           |
| `MinimalCaps/Model.v`            | - Instantiation of μSail operational semantic and the Iris-based program logic model,              |
|                                  | - Verification of ghost lemmas and foreign functions                                               |
|                                  | - Composition of all soundness theorems                                                            |
| `MinimalCaps/LoopVerification.v` | Manual verification of the contract of the fetch-decode-execute loop, i.e. the universal contract, |
|                                  | using the semi-automatically verified contract of a single fetch-decode-execute step.              |

The `Assumptions.v` file in the main `case_study` folder contains
`Print Assumptions` for the various main theorems of the case studies.
For MinimalCaps it should show the following compile output:
```
Assumptions of MinimalCaps universal contract:
Axioms:
Machine.MinCapsProgram.pure_decode : Z -> string + Base.Instruction
Model.MinCapsIrisBase.maxAddr : nat
```

For this case study we have postulated a decoder, i.e. a function that takes a
word and gives back a decoded instruction or signals an error, and specify that
this is what the decode foreign function implements. Furthermore, we have left
the maximum address of the memory unspecified. No other definitions (or proofs)
are assumed as axioms.

### RISC-V PMP
The code for RISC-V PMP can be found in the `case_study/RiscvPmp/` directory. We outline the structure of this directory below.

| File                           | Description                                                                              |
|--------------------------------|------------------------------------------------------------------------------------------|
| `RiscvPmp/Base.v`              | See the explanation of MinimalCaps above.                                                |
| `RiscvPmp/Machine.v`           | See the explanation of MinimalCaps above.                                                |
| `RiscvPmp/Sig.v`               | - Declaration of spatial and pure predicates                                             |
|                                | - Solver for pure predicates                                                             |
| `RiscvPmp/Contracts.v`         | - Definition of contracts and ghost lemmas statements                                    |
|                                | - (Semi-)automatic verification of the μSail function with Katamaran's symbolic executor |
| `RiscvPmp/Model.v`             | See the explanation of MinimalCaps above.                                                |
| `RiscvPmp/IrisModel.v`         | The instantiation of the Iris model                                                      |
| `RiscvPmp/IrisInstance.v`      | is split over two additional files.                                                      |
| `RiscvPmp/LoopVerification.v`  | See the explanation of MinimalCaps above.                                                |
| `RiscvPmp/BlockVer/Spec.v`     | A separate set of function contracts to derive a verifier for assembly code              |
| `RiscvPmp/BlockVer/Verifier.v` | The assembly code verifier and its soundness proof.                                      |
| `RiscvPmp/Femtokernel.v`       | Verification of the femtokernel initialization and handler code.                         |

The `Assumptions.v` file should produce the following compile output for RISC-V
PMP:

```
Assumptions of Risc-V PMP universal contract:
Axioms:
Machine.pure_decode : bv 32 -> string + Base.AST
Assumptions of FemtoKernel verification:
Axioms:
Machine.pure_decode : bv 32 -> string + Base.AST
Assumptions of femtokernel end-to-end theorem:
Axioms:
Machine.pure_decode : bv 32 -> string + Base.AST
```
Like the MinimalCaps case study, the instruction decoder is postulated, but no
other axioms exist. The precondition of the femtokernel init requires that
the encoded instructions in memory decode to the kernel code via this postulated
function.

### Requirements
The following Coq and Coq libraries are required:
```
coq            >= 8.16
coq-equations  >= 1.3
coq-iris       >= 4.0
coq-stdpp      >= 1.8
```

To ease building the project, we provide a `Dockerfile` and an prebuilt image of this `Dockerfile`. 
The easiest way to get started is by downloading [katamaran-ccs23.tar.gz](https://github.com/katamaran-project/katamaran/releases/download/ccs23/katamaran-ccs23.tar.gz) the prebuilt image and loading it into Docker:
```bash
docker load < katamaran-ccs23.tar.gz
docker run -it --rm katamaran/ccs23
```

The docker image can also be build locally using the following commands:
```bash
docker build . -t katamaran/ccs23
docker run -it --rm katamaran/ccs23
```
NOTE: we rely on the GitHub Docker Container Registry, please consult [this manual](https://docs.github.com/en/packages/working-with-a-github-packages-registry/working-with-the-container-registry) to setup the required access tokens for this registry in case you receive `Access Denied` errors in the output.

For further build instructions, such as the complete manual setup on your system, see [README.md](./README.md).

## Paper-to-Artifact Correspondence
| Paper                                   | File                                        | Definition                               |
|-----------------------------------------|---------------------------------------------|------------------------------------------|
| Figure 4: Store instruction             | `case_study/MinimalCaps/Machine.v`          | Definition fun\_exec\_sd                 |
| Figure 5: 𝒱(z)                          | `case_study/MinimalCaps/Model.v`            | Definition interp\_z                     |
| Figure 5: 𝒱(O, -, -, -)                 | `case_study/MinimalCaps/Model.v`            | Definition interp\_cap\_O                |
| Figure 5: 𝒱(R, _b_, _e_, -)             | `case_study/MinimalCaps/Model.v`            | Definition interp\_cap\_R                |
| Figure 5: 𝒱(RW, _b_, _e_, -)            | `case_study/MinimalCaps/Model.v`            | Definition interp\_cap\_RW               |
| Figure 5: 𝒱(E, _b_, _e_, _a_)           | `case_study/MinimalCaps/Model.v`            | Definition interp\_cap\_E                |
| Figure 5: ℰ(_w_)                        | `case_study/MinimalCaps/Model.v`            | Definition interp\_expr                  |
| Figure 6: UC Definition                 | `case_study/MinimalCaps/LoopVerification.v` | Definition semContract\_loop             |
| Figure 6: UC Verif.                     | `case_study/MinimalCaps/LoopVerification.v` | Lemma valid\_semContract\_loop2          |
| Section 5.1: Step contract              | `case_study/MinimalCaps/Contracts.v`        | Definition sep\_contract\_step           |
| Section 5.1: Step verif.                | `case_study/MinimalCaps/Contracts.v`        | Lemma valid\_contract\_step              |
| Section 5.1: IH                         | `case_study/MinimalCaps/Model.v`            | Definition IH                            |
| Figure 7: UC Definition                 | `case_study/RiscvPmp/LoopVerification.v`    | Definition semTriple\_loop               |
| Figure 7: UC verif.                     | `case_study/RiscvPmp/LoopVerification.v`    | Lemma valid\_semTriple\_loop             |
| Figure 7: Normal                        | `case_study/RiscvPmp/LoopVerification.v`    | Definition Step\_pre                     |
| Figure 7: Trap                          | `case_study/RiscvPmp/LoopVerification.v`    | Definition Trap                          |
| Figure 8: PMP\_addr\_access             | `case_study/RiscvPmp/IrisInstance.v`        | Definition interp\_pmp\_addr\_access     |
| Figure 10: Store contract               | `case_study/MinimalCaps/Contracts.v`        | Definition sep\_contract\_exec\_sd       |
| Figure 10: Store verif.                 | `case_study/MinimalCaps/Contracts.v`        | Lemma valid\_contract\_exec\_sd          |
| Figure 11: read\_mem                    | `case_study/MinimalCaps/Contracts.v`        | Definition sep\_contract\_read\_mem      |
| Figure 11: read\_reg                    | `case_study/MinimalCaps/Contracts.v`        | Definition sep\_contract\_read\_reg      |
| Figure 11: read\_reg\_cap               | `case_study/MinimalCaps/Contracts.v`        | Definition sep\_contract\_read\_reg\_cap |
| Figure 11: write\_mem                   | `case_study/MinimalCaps/Contracts.v`        | Definition sep\_contract\_write\_mem     |
| Figure 11: update\_pc                   | `case_study/MinimalCaps/Contracts.v`        | Definition sep\_contract\_update\_pc     |
| Figure 11: move\_cursor                 | `case_study/MinimalCaps/Contracts.v`        | Definition lemma\_safe\_move\_cursor     |
| Figure 11: subperm\_not\_E              | `case_study/MinimalCaps/Contracts.v`        | Definition lemma\_subperm\_not\_E        |
| Figure 12: read\_ram contract           | `case_study/RiscvPmp/Contracts.v`           | Definition sep\_contract\_read\_ram      |
| Figure 12: read\_ram verif.             | `case_study/RiscvPmp/Model.v`               | Lemma read\_ram\_sound                   |
| Figure 12: write\_ram contract          | `case_study/RiscvPmp/Contracts.`            | Definition sep\_contract\_write\_ram     |
| Figure 12: write\_ram verif.            | `case_study/RiscvPmp/Model.v`               | Lemma write\_ram\_sound                  |
| Figure 13: Step contract                | `case_study/RiscvPmp/Contracts.v`           | Definition sep\_contract\_step           |
| Figure 13: Step verif.                  | `case_study/RiscvPmp/Contracts.v`           | Lemma valid\_contract\_step              |
| Figure 14: open\_PMP\_entries contract  | `case_study/RiscvPmp/Contracts.v`           | Definition lemma\_open\_pmp\_entries     |
| Figure 14: open\_PMP\_entries verif.    | `case_study/RiscvPmp/Model.v`               | Lemma open\_pmp\_entries\_sound          |
| Figure 14: extract\_PMP\_ptsto contract | `case_study/RiscvPmp/Contracts.v`           | Definition lemma\_extract\_pmp\_ptsto    |
| Figure 14: extract\_PMP\_ptsto verif.   | `case_study/RiscvPmp/Model.v`               | Lemma extract\_pmp\_ptsto\_sound          |
| Figure 14: return\_PMP\_ptsto contract  | `case_study/RiscvPmp/Contracts.v`           | Definition lemma\_return\_pmp\_ptsto     |
| Figure 14: return\_PMP\_ptsto verif.    | `case_study/RiscvPmp/Model.v`               | Lemma return\_pmp\_ptsto\_sound          |
| Section 6: FemtoKernel invariant        | `case_study/RiscvPmp/FemtoKernel.v`         | Definition femto\_inv\_fortytwo          |
| Figure 15: FemtoKernel kernel           | `case_study/RiscvPmp/FemtoKernel.v`         | Example femtokernel\_init                |
| Figure 15: FemtoKernel ih               | `case_study/RiscvPmp/FemtoKernel.v`         | Example femtokernel\_handler             |
| Figure 15: FemtoKernel end-to-end       | `case_study/RiscvPmp/FemtoKernel.v`         | Lemma femtokernel\_endToEnd              |
