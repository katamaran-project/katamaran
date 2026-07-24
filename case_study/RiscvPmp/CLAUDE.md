# RISC-V PMP case study — shared file map

These 5 files are instantiated once and SHARED between `BlockVer/` (linear
verifier) and `CFGVer/` (active work) — each sub-verifier layers its own
executor/contracts on top. One-liner here for orientation; each file also
carries a fuller header comment (right after its copyright block).

| File | What it's for |
|---|---|
| `Machine.v` | RISC-V PMP instantiation of the generic `Program` typeclass — `Fun`/`FunX`/`Lem` signatures and their statement bodies (rX/wX, fetch, decode, execute_*, step/loop, trap/CSR, PMP encode/decode) |
| `Sig.v` | RISC-V PMP instantiation of the generic `Signature` typeclass — the pure/spatial predicate indices (`gprs`, `ptsto`, `ptstomem`, `ptstoinstr`, PMP-range formulas) |
| `IrisModel.v` | RISC-V PMP instantiation of `IrisBase` — register/RAM ghost state, no contracts/predicates wired yet |
| `IrisInstance.v` | interprets `Sig.v`'s predicate vocabulary into concrete Iris resources over `IrisModel.v`'s ghost state |
| `Contracts.v` | hand-written `SepContract`s for the primitive functions common to every verifier (rX, wX, fetch, mem_read/write, tick_pc, decode, leak, ...) — NOT `CFGVer/Contracts.v`'s unrelated `CFGVerifierContract` record |

For `case_study/RiscvPmp/CFGVer/`-specific files, see the nested
`CFGVer/CLAUDE.md`.
