# CCS 2023 Artifact
Paper: Formalizing, Verifying and Applying ISA Security Guarantees as Universal Contracts

This artifact contains the Coq development providing the evidence for the paper. At the end of this
document we provide a paper-to-artifact correspondence. The code itself is documented as well.

## Artifact Instructions
The artifact consists of three developments: (1) Katamaran, the semi-automatic seperation logic verifier, (2) the MinimalCaps
case study and (3) the RISC-V with PMP case study. The paper focuses on the general universal contracts approach, which we
demonstrated for two instruction set architectures with different security primitives, MinimalCaps and RISC-V PMP. Our Coq
development provides evidence for our claims in the paper.

### Requirements
The following Coq and Coq libraries are required:
```
coq            >= 8.16
coq-equations  >= 1.3
coq-iris       >= 4.0
coq-stdpp      >= 1.8
```

To ease building the project, we provide a `Dockerfile`. The project can then be build locally using the following commands:
```bash
docker build . -t katamaran/ccs23
docker run katamaran/ccs23
```
 or by downloading the docker container:
 ```bash
 docker pull ghcr.io/katamaran-project/artifact:ccs2023
 docker run ghcr.io/katamaran-project/artifact:ccs2023
 ```

For further build instructions, see [README.md](./README.md).

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
| Figure 14: extract\_PMP\_ptsto verif.   | `case_study/RiscvPmp/Model.v`               | Lemma extract\_pmp\_ptsto_sound          |
| Figure 14: return\_PMP\_ptsto contract  | `case_study/RiscvPmp/Contracts.v`           | Definition lemma\_return\_pmp\_ptsto     |
| Figure 14: return\_PMP\_ptsto verif.    | `case_study/RiscvPmp/Model.v`               | Lemma return\_pmp\_ptsto\_sound          |
| Section 6: FemtoKernel invariant        | `case_study/RiscvPmp/FemtoKernel.v`         | Definition femto\_inv\_fortytwo          |
| Figure 15: FemtoKernel kernel           | `case_study/RiscvPmp/FemtoKernel.v`         | Example femtokernel\_init                |
| Figure 15: FemtoKernel ih               | `case_study/RiscvPmp/FemtoKernel.v`         | Example femtokernel\_handler             |
| Figure 15: FemtoKernel end-to-end       | `case_study/RiscvPmp/FemtoKernel.v`         | Lemma femtokernel\_endToEnd              |
