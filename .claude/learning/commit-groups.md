# Katamaran CFGVer: a study map of commits `a71bc67b^..HEAD` (2026-06-17 to 2026-10-07)

> **Warning: an LLM wrote this and nobody has checked it as teaching material.** It is a reading
> aid for the author. Each "conceptual summary" was produced by a model that read commit
> messages, PLAN headers and status blocks, and spot-checked code. Where a summary says
> something about code, the named definitions and lemmas were confirmed to EXIST at HEAD
> (`command grep`, file:line given). Their *content* was not proof-read. Trusted-surface
> verdicts come from mechanical diffs (method in §E). Everything else is a paraphrase of
> commit messages and PLANs, which were also written by an LLM.

Branch: `issue/relval-pair` (HEAD `51dc0af8`). Range: 680 commits, 11 merges into
`KatamaranRel`. The commits fall into **47 groups**: 45 initiative groups plus "misc /
infrastructure" (M) and "Claude tooling" (T). Each commit is in exactly one group. The per-commit
listing (formerly the Appendix) was lost with the session scratchpad; each group section
still names its commit range and key commits, and `scripts/stmtdiff.py` re-checks any range.

Category key: **A** = changed what is proved (trusted statement surface or semantics), so
read the code. **B** = a mechanism the author *uses*, so understand the concept. **C** =
performance, scaling or solver cost, where the summary is enough. **I** = infrastructure or
build. **T** = tooling.

Paths are relative to `case_study/RiscvPmp/CFGVer/` unless they start with `theories/` or
`RiscvPmp/`.

---

## (a) Summary table

| # | group (code) | dates | #c | cat | trusted touch | plan(s) |
|---|---|---|---|---|---|---|
| 1 | CFGVer foundations: executor, end-to-end wiring, public memory (F1) | 06-17..06-24 | 14 | A+B | yes: creates the statement layer (then in Examples.v) | — |
| 2 | Termination-sensitive statement `noninterferent_strong` (F3) | 06-23..07-01 | 15 | A | **yes**: defines/changes `noninterferent_strong`; `semWP2` def in theories/Iris | — |
| 3 | `gen_contract` generator (F2) | 06-20..07-01 | 5 | B (+A) | yes: `reg_spec`, `gen_public_regs` (statement vocabulary) | — |
| 4 | Relational pattern match / LOAD-of-secret, cmovznz4 (PM) | 07-02..07-04 | 11 | A+B | **yes**: cmovznz4 data, 3 other end statements, program-logic rule in theories | (.claude/TODO.md) |
| 5 | Load address `init_addr` as parameter (IA) | 07-04..07-05 | 7 | A+B | **yes**: `noninterferent_strong` + all end theorems gain `init_addr` | — |
| 6 | gmap instruction store pivot (GM) | 07-13 | 3 | B | no | — |
| 7 | Symbolic (universal) base address (SB) | 07-13..07-18 | 18 | A+B | **yes**: new `*_param` theorems, `concretize_*`, countdown_mem program changed | PLAN-symbolic-base |
| 8 | Layering / build-cost restructuring (LAY) | 07-17..07-27 | 15 | I | moved verbatim (Examples.v split, Results split, imports) | — |
| 9 | New-example boilerplate reduction (BOIL) | 07-24 | 2 | B | Results.v touched, no statement change | merge `2918109c` |
| 10 | `bool_to_bits` branch-free: SLT* on secrets (SLT) | 07-27 | 1 | **A** | **yes: `RiscvPmp/Machine.v` model change** | — |
| 11 | Real-world examples: Botan, BearSSL, AES (EX) | 07-19..10-06 | 7 | A (additive) | yes: new data blocks + end theorems | PLAN-ksl64 (parked) |
| 12 | Address space `lenAddr` 2^10 to 2^12 (ADDR) | 09-08..09-09 | 2 | **A** | **yes: `RiscvPmp/Base.v`** | PLAN-address-space-params |
| 13 | Exit targets: one exit address (EXT) | 09-25 | 11 | **A**+B | **yes**: `noninterferent_strong`, all 17 Result statements, jump_if_zero program | PLAN-exit-targets; merge `321c42f3` |
| 14 | RelVal as a plain pair (RVP) | 10-06..10-07 | 18 | **A** (semantics) | theories semantics; trusted statements textually unchanged | PLAN-relval-pair (unmerged) |
| 15 | One end-to-end core, check_scalar at every klen, arr widths (GEN) | 10-02 | 14 | A+B | **yes**: new theorems + new statement vocabulary in GenSegment.v | PLAN-general-endtoend, PLAN-check-scalar-full §9; merges `5fb8e42a`, `9073e7c6` |
| 16 | AnnotInstr migration (ghost annotations) (AI) | 08-20..08-24 | 24 | B | proof-only in Results | PLAN-annotinstr Ph 0-3 |
| 17 | Havoc ghost lemma / `call_lemma` (HAV) | 08-24..08-27 | 10 | B+C | `Machine.v`: new ghost `Lem` (no FunDef uses it) | PLAN-annotinstr Ph 4 |
| 18 | Classed existentials (CLS) | 08-18 | 18 | B+C | proof-only | PLAN-classed-existentials |
| 19 | Unify generators (UG) | 08-18..08-19 | 12 | B | proof-only | PLAN-unify-generators |
| 20 | Byte-granular memory + check_scalar (flat) (BYTE) | 08-05..08-17 | 23 | B+C | additive (loop1 theorem) | PLAN-byte-memory, PLAN-check-scalar-full |
| 21 | Iris-level contract composition + loop rule (COMP) | 08-10..09-04 | 12 | B | new Iris-level composed Result files | PLAN-loop-invariant |
| 22 | Sub-table segments, prefix length, branch refutation (SUBT) | 09-04..09-05 | 14 | B (superseded) + C | new Iris-level PaddedLoopResult | — |
| 23 | Segment generators + muladd cuts (SEG) | 09-09..09-25 | 31 | B | no | PLAN-segment-generators, PLAN-muladd-composed; merge `a5198438` |
| 24 | LoopSpec / loop automation (LOOP) | 09-11..09-14 | 49 | B | no (but fixes a theories bug) | PLAN-loop-automation |
| 25 | Self-contained segments (SCS) | 09-25 | 1 | B | aux lemmas only | PLAN-self-contained-segments |
| 26 | Composition in the executor: blocks (EXC) | 09-15..09-22 | 13 | B | proof-only | PLAN-executor-composition |
| 27 | Contract-AST: annotations as tool input (CAST) | 09-22..09-23 | 23 | B | Iris-level composed statements changed | PLAN-contract-ast |
| 28 | Loop as self-referential block, Löb (REC) | 09-24..09-25 | 7 | B | additive (countdown_rec) | PLAN-rec-loop-block |
| 29 | Valid block annotations `AnnotInstrV` (VBA) | 09-25..09-29 | 11 | B | aux lemmas only | PLAN-valid-blk-annot; merge `b001d1a3` |
| 30 | Array invariants, parametric muladd (ARR) | 09-28..10-02 | 35 | B (+A additive) | additive (muladd_param) | PLAN-array-invariants, PLAN-chunk-facts (reverted); merge `d8ca8316` |
| 31 | KSL scaling hunt I: term sharing / havoc / solver-fold, all refuted (KSL) | 07-19..07-24 | 31 | C | no | PLAN-term-sharing, PLAN-havoc-secrets (PLAN-solver-fold deleted) |
| 32 | `|wctx|` hunt: unquantify + forward world-GC (WCTX) | 07-29 | 16 | C | no (leaves Admitted in theories) | PLAN-unquantify-gate, PLAN-unquantify-forward |
| 33 | `nextpc` param + `encoded_instr` removal (NPC) | 07-31..08-03 | 17 | C | no | PLAN-nextpc-param, PLAN-encoded-instr; merge `e20e9969` |
| 34 | Chunk GC for leaked `encodes_instr` (CGC) | 08-03 | 12 | C | no | PLAN-chunk-gc |
| 35 | Mask algebra: `uop.expand`, `bop.coalesce`, `bop.mulx` (MASK) | 08-04..08-17 | 9 | C | no (new ops in theories, unused by Machine) | PLAN-coalesce, PLAN-ksl64; merge `9d4f740f` |
| 36 | Chunk count vs `|Σ|` diagnostics (SIG) | 08-13..08-18 | 9 | C | no | — |
| 37 | Fetch-bound VCs discharged in solver (FB) | 08-17 | 4 | C | no | PLAN-fetch-bound-vcs |
| 38 | lvar lookup hypothesis (LV) | 08-19 | 2 | C | no | PLAN-lvar-lookup |
| 39 | Word slicing (WS) | 08-24 | 7 | C | no | PLAN-encoded-instr §12; merge `2001202f` |
| 40 | Dead-lvar drop: `dropk` + PExt/CExt (DROP) | 08-25..09-06 | 55 | C (big framework change) | no | PLAN-lvar-drop, -drop-build, PLAN-dropk; merge `c5ac2c5b` |
| 41 | `env.lookup` fused walk (ENV) | 09-01..09-02 | 7 | C | no | PLAN-env-trie |
| 42 | muladd flat attempt, footprint, Base(K) (MF) | 08-11..09-29 | 12 | C | no | PLAN-muladd-full |
| 43 | Table-entry cost, vm-vs-tactic split (TE) | 09-07..09-08 | 8 | C | no | — |
| 44 | bv ring normalisation in peval (BVA) | 09-29..10-01 | 6 | C | no | PLAN-bv-arith-solver |
| 45 | Small solver fixes (SOLM) | 07-28..09-22 | 5 | C | no | — |
| 46 | Misc / infrastructure (M) | 07-04..09-24 | 8 | I | `Machine.v` comment-only | — |
| 47 | Claude tooling (T) | 06-20..10-06 | 46 | T | no | — |

Total: 680.

---

## (b) Suggested study order

The order follows dependencies. A and B come before C. Brackets give the groups to read
first.

1. **F1** foundations: what `sexec_cfg_addr` / `cexec_cfg_addr` / the end-to-end lemma are.
2. **F3** `noninterferent_strong` [F1]: the theorem everything ends in.
3. **F2** `gen_contract` [F1, F3].
4. **PM** relational pattern match and cmovznz4 [F2]. The first realistic example and the
   first program-logic rule change.
5. **IA**, then **GM**, then **SB** [F2]. Placement: `init_addr`, gmap store, symbolic base,
   `param_val`, `concretize_*`, `gen_contract_param/_rel`.
6. **SLT** [relval/secret-walls skills]. A trusted model change. Read the disclaimer in
   `RiscvPmp/Machine.v` above `fun_bool_to_bits`.
7. **LAY** + **BOIL** (skim). Why the file layout is what it is, and the trusted-file list.
8. **EX** [SB, SLT]. What the real examples prove and what they do not.
9. **BYTE** [SB, MASK-skim] → **CLS** → **UG** [F2, SB]. The generator family as it is today.
10. **AI** [SB]: `AnnotInstr`, ghosts. Then **HAV** (skim).
11. **COMP** [F3] → **SUBT** (skim, superseded) → **SEG** → **LOOP** → **SCS**. Iris-level
    composition. Most of this is superseded by the next block, but `GenSegment.v` /
    `GenCompose.v` still hold the data-spec vocabulary used by GEN.
12. **ADDR** [none]. A trusted model parameter.
13. **EXC** → **CAST** → **REC** → **EXT** → **VBA** [AI, SEG]. Composition moved into the
    executor (blocks, `ai_loop` Löb), single exit, sealed validity. **This is the current
    architecture.**
14. **ARR** [VBA, REC] → **GEN** [ARR, BYTE]. Array ghost views, then the single end-to-end
    core.
15. **RVP** [everything, plus the relval-model skill]. The in-flight semantics change on this
    branch.
16. C groups, in rough causal order, if wanted: KSL → WCTX → NPC → CGC → MASK → SIG → FB → LV →
    WS → DROP → ENV → MF → TE → BVA → SOLM. `diagnostics/*.md` are the durable records.
    Several headline numbers in them were later retracted, so read each file's latest
    addendum first.

---

## (c) Per-group sections

Churn is lines added plus lines deleted, summed over the group's commits (from `--numstat`),
top entries only. `ZZ*` probe files and plan/diagnostics markdown are included when they
dominate.

### 1. F1: CFGVer foundations (executor, end-to-end wiring, public memory)
- Plan: none. Merge: none (direct commits).
- 2026-06-17..06-24, **14 commits**, `a71bc67b..e40bb24a`.
- Churn: `Examples.v` (2749), `Verifier.v` (693), `CLAUDE.md` (107), `Spec.v` (88), `EndToEnd.v`
  (55; an early file, deleted in `04a634c8` and later recreated by the LAY split).
- Trusted touch: **yes, it creates the surface.** At the time the statements lived inside
  `Examples.v`. The statement-diff script (§E) shows the first data blocks being added
  (`countdown_mem_instrs`, `jmp_fwd_exitCond`, `countdown_exitCond`), along with
  `mem_spec`, `declare_public_memory` and `gen_public_addrs` (`d0193771`).
- Category: A+B.
- Summary: this group adds an alignment check and an `exitCond` parameter to the
  symbolic/concrete CFG executors (`sexec_cfg_addr` `Verifier.v:1600`, `cexec_cfg_addr`
  `VerifierRel.v:347`). It proves the first end-to-end result (jmp_fwd), then factors out
  the generic `cfg_instrs_endToEnd` (`EndToEnd.v:1445`). It removes postconditions from
  `CFGVerifierContract`, though COMP later re-adds them. It adds public data memory:
  `cfg_instrs_endToEnd_with_memory` (`EndToEnd.v:1494`) and `instrsAndDataMemory`
  (`Adequacy.v:1233`), which splits raw memory into code plus data words. Much of the API was
  later renamed or re-parameterised (IA, GM, SB, EXT), but the shape survives.
- Depends on: nothing.

### 2. F3: termination-sensitive statement `noninterferent_strong`
- Plan: none (notes in `.claude/TODO.md`). Merge: none.
- 06-23..07-01, **15 commits**, `41514a00..31bf222b`. Includes `97c930cc` (reg_spec triple and
  `mem_full_spec`).
- Churn: `Examples.v` (2589), `.claude/TODO.md` (185), `theories/Iris/BinaryAdequacy.v` (96),
  `CLAUDE.md` (58), `theories/Iris/BinaryWeakestPre.v` (48).
- Trusted touch: **yes.** `13109698` introduces `noninterferent_strong`, `declare_init_*`,
  `reg_init_spec`. `97c930cc` changes `noninterferent_strong`, `reg_spec`, `gen_public_regs`
  and every end theorem (statement diff). `902a4e2e` changes the *definition* of `semWP2` in
  `theories/Iris/BinaryWeakestPre.v`: mixed `stm_val`/`stm_fail` outcomes now give `False`.
  That is the proof model, not the trusted statement, and adequacy was re-proved.
- Category: A.
- Summary: the trusted theorem becomes "if run 1 reaches the exit in n steps then run 2 does
  so in exactly n steps with equal leakage trace". It now reads `noninterferent_strong`
  (`Noninterference.v:261`), with the exit later changed by EXT. Getting there needed a
  strengthened adequacy (`adequacy_gen_RiscVNStepsExitCond_strong`, `Adequacy.v:606`) and a
  pc-synchronisation invariant threaded through the WP2 preservation lemma. `7e9b703a`/`5b8c2df1`
  made every end-to-end lemma termination-sensitive, and `8d92df34` **reverted** that attempt
  ("keep helpers and SyncVal form"). The final route is `noninterferent_strong` plus
  `gen_contract_noninterferent`.
- Depends on: F1.

### 3. F2: `gen_contract` generator
- Plan: none. Merge: none.
- 06-20..07-01, **5 commits**, `74575ce1..95b4193c`.
- Churn: `Examples.v` (349), `BlockVer/Spec.v` (36), `CFGVer/Spec.v` (36),
  `theories/Syntax/Assertions.v` (2).
- Trusted touch: yes, the vocabulary. `reg_spec` (`Noninterference.v:93`) and
  `gen_public_regs` (`Noninterference.v:109`) are introduced and changed (`74575ce1`,
  `8e0245e7`). Both appear inside `noninterferent_strong`.
- Category: B (with an A component).
- Summary: a contract is built from spec lists (register, is_public, optional value) instead of
  hand-written assertions. `gen_contract` (`GenContract.v:260`) produces the precondition and
  `gen_implpre` (`EndToEnd.v:417`) proves the concrete initial state implies it. The
  `secLeakvar` notation (`theories/Syntax/Assertions.v:307`) marks public values.
  `gen_contract_noninterferent` closes the loop to the trusted statement. It was later
  generalised many times (SB, CLS, UG, GEN).
- Depends on: F1, F3.

### 4. PM: relational pattern matching / LOAD-of-secret, cmovznz4
- Plan: `.claude/TODO.md` (not a PLAN file). Merge: none.
- 07-02..07-04, **11 commits**, `0bc112da..823e81fd`.
- Churn: `.claude/commands` (1442, tooling swept into `f90a607e`), `.claude/TODO.md` (1055),
  `theories/Syntax/Patterns.v` (639), `tools/asm_to_ast.py` (408), `theories/Shallow/Monads.v`
  (399), `Examples.v` (340).
- Trusted touch: **yes.**
  - `0bc112da` adds `cmovznz4_instrs/_reg_specs/_mem_specs` and *changes* the statements of
    `swap_noninterferent`, `jmp_fwd_noninterferent_cfg` and `countdown_mem_noninterferent`.
    The message does not say this.
  - `88c947bb` changes `cmovznz4_mem_specs` so that x and y become secret, which strengthens
    the theorem.
  - `f90a607e`, titled "TCB pattern-match rule weakened", changes the program-logic rule
    `rule_stm_pattern_match` (`theories/Sep/Hoare.v:197`): the premise `secLeak` becomes
    `is_Some(pattern_match_relval …)`. It was re-proved sound in Iris
    (`iris_rule_stm_pattern_match`, `theories/Iris/BinaryWeakestPre.v:1265`), so this is a
    proof-system change, not an end-statement change.
- Category: A+B.
- Summary: Breaking-Bad cmovznz4 needed LOADs of secret data. The relational pattern match
  previously demanded `secLeak` of the scrutinee. "Method Y" case-splits on unique
  reversibility. Var/unit/union patterns take a fast path with raw payloads, and the rest
  fall back to `secLeak`. `pattern_match_relval` (`theories/Syntax/Patterns.v:429`) gained
  projection lemmas. `asm_to_ast.py` (assembly to AST) arrives here. RVP §6 R2 plans to
  revisit this rule.
- Depends on: F1, F2.

### 5. IA: load address as a genuine parameter
- 07-04..07-05, **7 commits**, `0f308958..66bf60f5`. No plan or merge. A related unmerged
  branch is `wip/cfgver-base-offset-split`.
- Churn: `Examples.v` (520), `Verifier.v` (244).
- Trusted touch: **yes.** `73676c0c` changes `noninterferent_strong`, `pcOutOfInstrs_exitCond`
  and every end theorem, which all gain `init_addr`. `66bf60f5` adds
  `cmovznz4_noninterferent_at_start`.
- Category: A+B.
- Summary: the executor and contracts are parameterised on a load base, and memory lemmas
  (`instrsMemory`, `instrsAndDataMemory`) on an arbitrary start address. cmovznz4 is then
  verified at init_addr = 256. SB later makes the base symbolic, so this concrete-base
  machinery is mostly superseded. The `init_addr` argument of the trusted statement remains.
- Depends on: F1, F2.

### 6. GM: gmap instruction store pivot
- 07-13, **3 commits**, `5ea9fba4..0c44f2be`.
- Churn: `Verifier.v` (315), `Examples.v` (246). Trusted touch: no (only
  `intro_ptsto_instrs` and internal end-to-end lemmas changed).
- Category: B.
- Summary: the instruction store becomes a finite map keyed by address instead of a
  list plus base offset. `instrs_of_list` (`Tables.v:133`) builds it, and `cexec_cfg_addr`
  takes a `gmap (bv xlenbits) AnnotInstr`. Vestigial alignment and base parameters are dropped.
- Depends on: IA.

### 7. SB: symbolic (universal) base address
- Plan: `plans/PLAN-symbolic-base.md` ("probes complete, design locked"; the phases record
  completion). No merge.
- 07-13..07-18, **18 commits**, `f0cc9739..1718cd1a`.
- Churn: `Verifier.v` (1519), `Examples.v` (1362), `.claude/skills` (618), `.claude/TODO.md`
  (552), `PLAN-symbolic-base.md` (373).
- Trusted touch: **yes.**
  - `5c39fb78`/`5962a1b9` add `gen_contract_noninterferent_param/_rel`, `concretize_mem`, and
    the first `*_noninterferent_param` theorems. `concretize_reg`/`concretize_mem`
    (`GenContract.v:832/840`) appear *inside* end-theorem statements, so they are trusted.
  - `af2a1187` ("migrate all examples to parametric base") adds `*_param` theorems for every
    example. It also **changes the countdown_mem program**: LOAD/STORE now go through base
    register X2 instead of X0, and X2 is pinned to `init_addr`. Its statement changed too.
- Category: A+B.
- Summary: the executor runs with the program base as a symbolic term `term_var "p"`, so one
  VC covers every placement. Instruction dispatch is a syntactic term-table lookup
  (`table_of_list`, `Tables.v:317`). The concrete mirror is related by `itable_rel`
  (`VerifierRel.v:533`), with "guarded concrete VC" refinement in `rexec_cfg_addr`
  (`VerifierRel.v:2055`). `param_val` (`GenContract.v:328`: `PVExist`/`PVConst`/`PVBaseOff`)
  states base-relative values. A known trap: the base must be a `term_var`, because
  `term_val (bv.of_N …)` diverges `vm_compute`. The commits also cleaned up the `_tbl` naming
  and the dead non-table executor.
- Depends on: IA, GM, F2.

### 8. LAY: layering and build-cost restructuring
- 07-17..07-27, **15 commits**, `e50336e2..4617af16`.
- Churn: `Examples.v` (3682, split away), `Adequacy.v` (1282), `Verifier.v` (1053), `EndToEnd.v`
  (1011), `VerifierRel.v` (723).
- Trusted touch: files moved, statements not changed.
  - `e50336e2` splits `Examples.v` and creates `Noninterference.v` and `Results.v` verbatim.
  - `522e08d7` splits `Results.v` into `Example/*Result.v`. The statement diff shows no
    changed statement.
  - `d460a993` removes requires from `Noninterference.v`. Its message claims all 30
    definitions elaborate byte-identically; this was not re-checked.
- Category: I.
- Summary: the file layering in the CLAUDE.md files comes from here. Light branch:
  Spec → Verifier → Tables → Contracts → GenContract → Example/*. Heavy branch: SpecIris →
  VerifierRel → … → EndToEnd. Iris is split out of the light files. `_CoqProject` is pruned
  to the gate closure. The gate's `-j` is bounded by RAM.
- Depends on: SB.

### 9. BOIL: new-example boilerplate reduction
- 07-24, **2 commits** (`573f54ad` + merge `2918109c`, branch `cfgver-boilerplate-reduction`).
- Churn: `.claude/skills` (111), `EndToEnd.v` (101), `Results.v` (93), `Example/Prelude.v` (82).
- Trusted touch: Results.v edited, no statement changed. Category: B.
- Summary: introduces `Example/Prelude.v` as the shared import preamble, plus helper
  tactics and bridges, so a new example needs less copy-paste.
- Depends on: SB.

### 10. SLT: `bool_to_bits` made branch-free
- 07-27, **1 commit** `1236c880`.
- Churn: `RiscvPmp/Machine.v` (86).
- Trusted touch: **YES, the machine model.** `fun_bool_to_bits` (`RiscvPmp/Machine.v:620`)
  changes from a μSail `if:` to a `bop.bvcons` expression. The commit message and a long
  in-file disclaimer (around `Machine.v:529-610`) say that concrete `Val` semantics are
  preserved exactly (checked exhaustively on `bool`). What changes is the statement
  structure, and therefore the relational reading. This is a deliberate deviation from Sail,
  and it *loosens* the verifier: SLT/SLTU on secrets no longer forces `secLeak`. It is
  justified by the leakage model, since `bool_to_bits` emits no leak event.
- Category: **A**.
- Summary: every result about code using SLT*, including BearSSL's EQ/NEQ/GT and clang's
  seqz/snez/sltu, depends on this change. The disclaimer states what is *not* claimed: no
  bisimulation, and the assumption is invisible to `Print Assumptions`.
- Depends on: none (conceptually the relval-model / secret-data-walls skills).

### 11. EX: real-world examples (Botan, BearSSL, AES)
- 07-19..10-06, **7 commits**, `24eda45e..d026cadc`.
  - `24eda45e` precompute (Botan GHASH mask).
  - `b2a70067` key_schedule_loop2.
  - `dbc0c583` BearSSL check_scalar / modpow_win / muladd_q snippets.
  - `64bdfb1a` what the BearSSL work does not cover.
  - `389a66f1` modpow_win_full; also creates PLAN-ksl64.
  - `fe915f1d` AES InvMixColumns, Linux and Algorithm 7.
  - `d026cadc` attribution fix.
- Churn: `PLAN-ksl64.md` (421), `.claude/skills` (327), `Example/Aes/InvMixColumns.v` (198),
  `Example/KeyScheduleLoop.v` (191), `Example/BearSSLMuladd.v` (166).
- Trusted touch: **yes, additive.** New `*_instrs`/`*_reg_specs`/`*_mem_specs` blocks and new
  `*Result.v` files. No existing statement changed.
- Category: A (additive).
- Summary: each example is a translated real binary plus spec lists, verified through
  `gen_contract_*_param`, with end theorems such as `imc_linux_noninterferent_param`
  (`Example/Aes/InvMixColumnsResult.v:49`). What is proved for an example is exactly its data
  block plus its Result statement. Read those, and `64bdfb1a`'s "does NOT cover" note.
- Depends on: SB, SLT (for SLT* users).

### 12. ADDR: address space `lenAddr` from 2^10 to 2^12, de-hardcoded
- Plan: `plans/PLAN-address-space-params.md` (stage 0 DONE, minAddr deferred). The commits
  sit on the muladd-composed branch.
- 09-08..09-09, **2 commits** `b4439a8f`, `5cb8d958`. `b4439a8f` also creates
  PLAN-muladd-composed.
- Churn: `PLAN-muladd-composed.md` (403), `PLAN-address-space-params.md` (193), `Contracts.v`
  (79), `RiscvPmp/Base.v` (65), `theories/Bitvector.v` (25).
- Trusted touch: **YES, `RiscvPmp/Base.v`.** The address space quadruples. That changes every
  `… < lenAddr` premise in the end theorems (they get weaker, so the theorems get stronger)
  and `liveAddrs` in the memory model. The `JumpsResult.v` literal edits are proof-only.
  `b4439a8f` was committed "NOT YET VALIDATED" and validated by `5cb8d958`.
- Category: **A**.
- Summary: muladd (1168 bytes) did not fit in 1024 bytes. Every earlier whole-function muladd
  statement therefore had an unsatisfiable hypothesis, i.e. it was vacuous. The ZZ probes
  were affected; no gate theorem was. 24 proof sites hard-coded the value. All now name
  `lenAddr`/`maxAddr`. A quadratic `NoDup` decision in the Iris layer was replaced by
  `bv.seqBv_NoDup` (`theories/Bitvector.v:3237`).
- Depends on: none.

### 13. EXT: exit targets, one exit address per contract
- Plan: `plans/PLAN-exit-targets.md` (IMPLEMENTED; Phase 5 done via VBA). Merge: `321c42f3`
  (`issue/exit-targets`).
- 09-25, **11 commits**, `27a2fd1a..321c42f3`.
- Churn: `PLAN-valid-blk-annot.md` (476), `.claude/skills` (349), `PLAN-exit-targets.md` (265),
  `VerifierRel.v` (245), `EndToEnd.v` (239).
- Trusted touch: **YES.**
  - `9a4e303e` changes `noninterferent_strong`: `(exitCond : bv -> bool)` becomes
    `(exit_addr : N)` with `atPc` (`Noninterference.v:104`). It also deletes
    `pcOutOfInstrs_exitCond`.
  - `cfa9a762` changes the statement of all 17 Result files (statement diff lists every end
    theorem).
  - `27a2fd1a` **changes the jump_if_zero program**: it appends a NOP, and the bound goes
    from +4 to +8. The message flags this as a trusted change kept revertable.
- Category: **A**+B.
- Summary: a run "stops" only when pc equals the single exit address. A run that leaves the
  code elsewhere is no longer a stopping run. The contract field becomes
  `cfg_exit : Term Σ ty_xlenbits` (`Verifier.v:379`), and exit tables, `etable_rel` and
  `HexitsFaith` are deleted. Programs with several exits are cut at a join point.
- Depends on: F3, CAST.

### 14. RVP: RelVal as a plain pair (current branch, unmerged)
- Plan: `theories/plans/PLAN-relval-pair.md` (§11: pure port builds, full gate passed on
  `aa795710`, 24 end theorems axiom-clean). The D3 "meaning-change list" and repairs R1-R6
  are **open**. Not merged into KatamaranRel.
- 10-06..10-07, **18 commits**, `936ec9a3..51dc0af8`.
- Churn: `theories/Symbolic/Solver.v` (977), `PLAN-relval-pair.md` (506),
  `theories/Syntax/TypeDecl.v` (276), `theories/Syntax/Patterns.v` (261),
  `theories/Symbolic/Worlds.v` (249).
- Trusted touch: **semantics in theories/, yes. Trusted statements, textually no.**
  `RV` is now a record pair `NonSyncVal {projLeftRV; projRightRV}`, and `SyncVal a := NonSyncVal a a`
  (`theories/Syntax/TypeDecl.v:174-181`). `secLeak` (`theories/Syntax/Formulas.v:119`) now means
  equal projections. The statement-diff script finds no statement change in any `*Result.v`
  touched by `f6c35d8b`/`9028e9ce`/`aa795710`, and PLAN §11 says the same ("checked
  mechanically"). `noninterferent_strong` is stated over concrete `RegStore`/`Memory`, so its
  meaning does not depend on `RelVal`. The Iris-level composed Result statements
  (`swap_composed` etc., which mention `SyncVal`) *may* change meaning; that is the open D3
  item. `411d1c89` adds a solver rule `secLeak (c + t) <-> secLeak t`, logged in
  `theories/plans/relval-pair-baseline/AUDIT.md`.
- Category: **A** (semantic domain), port mostly mechanical.
- Summary: the SyncVal/NonSyncVal tag stops being visible to the semantics, following
  Binsec/Rel. "Untainting" (proving `secLeak` from value equality) becomes sound, and several
  `NonSyncVal ⇒ False` walls become repairable. The `secret-data-walls` and `relval-model`
  skills describe the *pre*-port model and will need updating after merge. Cost: 1.3-1.4×
  on some VCs, because a public relop is now two leaves.
- Depends on: all; the relval-model skill.

### 15. GEN: one end-to-end core, check_scalar at every klen, arrays of any width
- Plans: `plans/PLAN-general-endtoend.md` (in progress, A and B done), `PLAN-check-scalar-full.md`
  §9 (DONE). Merges: `5fb8e42a` (`issue/general-endtoend`), `9073e7c6` (`issue/arr-regroup`).
- 10-02, **14 commits**, `eb9a6fa0..9073e7c6`.
- Churn: `SpecIris.v` (650), `EndToEnd.v` (444), `Example/CheckScalar/CheckScalarParamResult.v`
  (268), `Adequacy.v` (264), `GenProg.v` (251).
- Trusted touch: **yes.**
  - New end theorems: `check_scalar_param_noninterferent`
    (`Example/CheckScalar/CheckScalarParamResult.v:188`) and
    `check_scalar_ptr_noninterferent` (`…/CheckScalarPtrResult.v:87`).
  - The ptr theorem's *statement* uses `concretize_reg_q` (`GenSegment.v:2017`) and
    `concretize_data` (`GenSegment.v:1925`). Both were added in `51fb58e6`. **Trusted
    statement vocabulary now lives in `GenSegment.v`, a file not on the documented
    trusted-file list.**
- Category: A+B.
- Summary: `instrsAndDataMemory` accepts data cells at arbitrary disjoint addresses.
  `cfg_instrs_endToEnd_with_memory` becomes the single core, and the 7 generator bridges are
  corollaries. `gen_prog_noninterferent` (`GenProg.v:105`) is a generic whole-program bridge
  over `data_spec` (`GenSegment.v:1851`), with `DPtr` for pointer arguments. `arr` gets an
  explicit cell width (`arr pub w s`), with split/join/bytes-of-words/regroup ghost lemmas
  such as `clem_arr_bytes_of_words` (`Verifier.v:162`).
- Depends on: ARR, BYTE, F2.

### 16. AI: AnnotInstr migration (ghost annotations on instructions)
- Plan: `plans/PLAN-annotinstr.md` Phases 0-3. Committed directly to KatamaranRel (the plan
  notes the gate ran after the fact).
- 08-20..08-24, **24 commits**, `2274a22b..127190fc`. Includes one revert-and-redo:
  `ace0c893`/`13eb91e0`.
- Churn: `PLAN-annotinstr.md` (1098), `Verifier.v` (799), `.claude/skills` (649),
  `VerifierRel.v` (271), `EndToEnd.v` (135).
- Trusted touch: Result files edited, proof-only (statement diff). Example files gained
  `strip_id_*` lemmas.
- Category: B.
- Summary: instructions carry annotations (`AnnotInstr`, `Verifier.v:441`) holding ghost
  actions that run around an instruction (`sexec_ghost`, `Verifier.v:1011`). `strip`
  (`Verifier.v:497`) recovers the plain program at the trusted boundary. CAST later removed
  annotations from the contract record entirely, but `AnnotInstr` (now with `ai_block` and
  `ai_loop`) is still the executor's input.
- Depends on: SB.

### 17. HAV: havoc ghost lemma and real `call_lemma` (AnnotInstr Phase 4)
- Plan: `PLAN-annotinstr.md` Phase 4. Was on `issue/annot-havoc-spike`, reached KatamaranRel
  via the dropk merge.
- 08-24..08-27, **10 commits**, `a9a1392d..abaab9eb`.
- Churn: `diagnostics/havoc-abstraction-payoff.md` (863), `PLAN-annotinstr.md` (185),
  `PLAN-lvar-drop.md` (162), `Verifier.v` (95).
- Trusted touch: `RiscvPmp/Machine.v` gains the ghost lemma constructor `havoc_regs`
  (`Machine.v:266`), with a trivial contract in `Contracts.v` and a `ValidLemma` in
  `ModelBinary.v`. No `FunDef` uses it, so program semantics are unchanged. It is still an
  edit to the Machine.v file.
- Category: B+C.
- Summary: a ghost `call_lemma` can forget register values (existential intro), which turns
  exponential term growth into linear growth in dead variables. That measured result is what
  motivated DROP. `havoc-abstraction-payoff.md` has two retractions and one
  retraction-of-retraction (`20722200`).
- Depends on: AI.

### 18. CLS: classed existentials (one existential per publicness class)
- Plan: `plans/PLAN-classed-existentials.md` (ALL FIVE PHASES COMPLETE). Merge: none.
- 08-18, **18 commits**, `bfdf7ec2..5afab603`.
- Churn: `PLAN-classed-existentials.md` (771), `EndToEnd.v` (554), `GenContract.v` (221),
  `key-schedule-loop2-cost-drivers.md` (116).
- Trusted touch: 4 Result files migrated, proof-only. GenContract.v edits are on the builder
  side; `concretize_*` is unchanged.
- Category: B+C.
- Summary: `gen_mem_pre_rel` minted one `asn.exist` per data cell, and `|Σ|` was the
  quadratic cost driver. `gen_contract_rel_classed` (`GenContract.v:735`) mints one wide
  existential per class. This is equivalent, not a weakening. The `ImplPre` bridge is
  `gen_mem_cells_class_intro` (`EndToEnd.v:767`) / `gen_implpre_mem_class` (`EndToEnd.v:1597`)
  / `gen_contract_noninterferent_rel_classed_simple` (`EndToEnd.v:2115`). The win depends on
  cell count (1.00× to 3.31×).
- Depends on: F2, SB, SIG.

### 19. UG: unify generators
- Plan: `plans/PLAN-unify-generators.md` (ALL STAGES DONE; the plan admits the files grew 12%).
- 08-18..08-19, **12 commits**, `c68a0890..893e5b92`.
- Churn: `EndToEnd.v` (1040), `PLAN-unify-generators.md` (508), `.claude/skills` (342),
  `GenContract.v` (289), `diagnostics/byte-classed-block-payoff.md` (245).
- Trusted touch: `JumpsResult.v` proof-only. "All 29 end-theorem statements byte-identical"
  per the plan.
- Category: B.
- Summary: there were 5 builders and 9 bridges. Now `gen_contract_u` (`GenContract.v:708`)
  is the single underlying builder, with 3 that still build their own record. 5 bridges
  containing the end-to-end ritual became 1. A byte-classed block makes 8 byte entries mint 1
  variable.
- Depends on: CLS, BYTE.

### 20. BYTE: byte-granular data memory and flat check_scalar
- Plans: `plans/PLAN-byte-memory.md`, `plans/PLAN-check-scalar-full.md` (both superseded in
  outcome by GEN §9).
- 08-05..08-17, **23 commits**, `1c69aa4b..9249811c`.
- Churn: ZZ probes (1871), `diagnostics/check-scalar-combined-cost-drivers.md` (1153),
  `PLAN-check-scalar-full.md` (753), `PLAN-byte-memory.md` (734), `EndToEnd.v` (418),
  `theories/Symbolic/Solver.v` (365).
- Trusted touch: additive (`check_scalar_loop1_noninterferent(_param)`). GenContract.v gains
  byte cells (`byte_chunks`, `GenContract.v:203`; `gen_contract_rel_bytes`,
  `GenContract.v:803`) on the builder side.
- Category: B+C.
- Summary: lets `lbu`/`sb` programs own byte cells. Diagnoses that a symbolic *pointer
  compare* in clang's loop exit is a cost driver, and fixes it with a `bvadd` cancellation
  solver rule (`try_bvadd_cancel_spec`, `theories/Symbolic/Solver.v:2717`; `14794add`). The
  whole-function N=32 flat VC was parked. Loop blocks (GEN) eventually did the whole function
  at every klen.
- Depends on: SB, F2, MASK.

### 21. COMP: Iris-level contract composition and loop rule
- Plan: `plans/PLAN-loop-invariant.md` (design 08-10). Merge: part of `c5ac2c5b`.
- 08-10..09-04, **12 commits**, `42c46499..bab76699`.
- Churn: `plans/PLAN-loop-invariant.md` (733 + 386 pre-move), `Example/CountdownComposedResult.v`
  (375), `Example/TwoLoopsComposedResult.v` (307), `diagnostics/composition-payoff.md` (275).
- Trusted touch: new Iris-level theorems (`swap_composed`, `SwapComposedResult.v:103`;
  `cd_loop`, `CountdownComposedResult.v:231`). These are `⊢ … -∗ myWP2_loop …`, not
  `noninterferent_strong`. The postcondition field is re-added to `CFGVerifierContract`
  (`1ed8c09c`).
- Category: B.
- Summary: `myWP2_loop_bind` (`Adequacy.v:185`) composes two contracts, and
  `myWP2_loop_induction` (`Adequacy.v:224`) is the loop rule (body contract in, loop
  contract out). The first payoff measurements said composition *loses* (6.4×, 7.30×). SUBT's
  branch refutation reversed that (composition-payoff.md ADDENDUM). Largely superseded by
  executor-level composition (EXC/REC).
- Depends on: F3, SB.

### 22. SUBT: sub-table segment contracts, prefix length, branch refutation
- 09-04..09-05, **14 commits**, `733011a6..a2c5d8f9`.
- Churn: `diagnostics/prefix-length-cost.md` (858), `diagnostics/branch-refutation-payoff.md`
  (264), `Example/PaddedLoopResult.v` (188), `.claude/skills` (176),
  `theories/Symbolic/Solver.v` (150).
- Trusted touch: new Iris-level `PaddedLoopResult.v`, later rewritten in ARR. No change to
  existing statements.
- Category: B (superseded) + C.
- Summary: a segment can be verified against just its slice of the instruction table. The
  key lemma `itable_faith_of_segment` was **deleted** by VBA Phase 5 and no longer exists at
  HEAD. The solver learned to *refute* a formula against the path condition, not only
  discharge it (`cfdcc92f`; `formula_refuted_by`, around `theories/Symbolic/Solver.v:3701`).
  That killed the prefix-length quadratic (measured 275× at P=64). The `3697cf41` "muladd
  mid-program cut VERIFIES" was later shown vacuous (see ADDR).
- Depends on: COMP.

### 23. SEG: segment generators and muladd cuts
- Plans: `plans/PLAN-segment-generators.md`, `plans/PLAN-muladd-composed.md` (both "superseded
  in part" by PLAN-self-contained-segments). Merge: `a5198438` (`issue/muladd-composed`, 137
  commits incl. LOOP/EXC/CAST/REC; gate skipped, passed on a descendant).
- 09-09..09-25, **31 commits**, `9c74a8b6..a5198438`.
- Churn: `PLAN-muladd-composed.md` (2009), `PLAN-segment-generators.md` (999), `GenCompose.v`
  (895), `GenSegment.v` (669), `diagnostics/segment-postcondition-cost.md` (177).
- Trusted touch: no.
- Category: B.
- Summary: `GenSegment.v` (light) and `GenCompose.v` (heavy) are a `gen_contract` for cuts:
  `gen_seg_contract` (`GenSegment.v:302`), `contract_run` (`GenCompose.v:190`), `cell_spec`
  (`GenSegment.v:1610`), `PVVar` (`GenSegment.v:1765`). They replaced 21-31 hand-copied
  boilerplate blocks. `a72dc9bc` is the "cell trade" that lets a loop keep the array it
  writes. The publicness sweep `510e159f` found 29/45 public marks unearned. The muladd
  composition chain (F;G;H) was never completed. ARR's parametric muladd is the eventual
  whole-function result.
- Depends on: COMP, SUBT, ADDR.

### 24. LOOP: LoopSpec and loop automation
- Plan: `plans/PLAN-loop-automation.md` (superseded in part). On the muladd-composed branch.
- 09-11..09-14, **49 commits**, `0def6ccd..b7b86685` (interleaved with SEG).
- Churn: `GenCompose.v` (2534), `GenSegment.v` (2106), `PLAN-loop-automation.md` (1518),
  `PLAN-segment-generators.md` (1247), `theories/Syntax/Assertions.v` (35).
- Trusted touch: no. But `5835e3da` fixed **a real framework bug** in
  `theories/Syntax/Assertions.v`: `sub_assertion` mapped `asn.or` to separating conjunction
  while `interpret` maps it to disjunction, so substituting an assertion containing `or`
  changed its meaning. New lemma: `interpret_subst` (`theories/Syntax/Assertions.v:224`).
- Category: B.
- Summary: `LoopSpec` (`GenSegment.v:736`) states a counted loop once and generates both its
  body and loop contracts (`gen_loop_contract`, `GenSegment.v:938`). The obligations are
  `loop_runs` (`GenCompose.v:2141`), `loop_back_edge_std` (`GenCompose.v:1847`),
  `loop_latch_obligation` (`GenSegment.v:1207`) and `loop_completed` (`GenCompose.v:1402`).
  Memory notes use older names (`loop_all`, `loop_edge_std`, `loop_latch_obl`,
  `loop_done`); these were renamed in `6193075f` and do not exist at HEAD.
  `loop_reservoir`/`loop_carry` handle sliding arrays. The fixed-context limitation is what
  ARR's array invariants address. REC's Löb-based loop block superseded the per-loop glue.
- Depends on: SEG.

### 25. SCS: self-contained segments
- Plan: `plans/PLAN-self-contained-segments.md`. 09-25, **1 commit** `1de8844d`.
- Churn: `GenCompose.v` (400), plan (183), `GenSegment.v` (179).
- Trusted touch: `CountdownRecResult.v` aux lemma removed only. Category: B.
- Summary: a segment or loop contract is stated as if it were the whole program (its own code,
  base and relative exits). Placement becomes a composition fact. `gen_seg_contract` loses
  `head prog skip take`.
- Depends on: SEG, LOOP.

### 26. EXC: composition in the executor (blocks)
- Plan: `plans/PLAN-executor-composition.md` (design note; steps 1-2 built).
- 09-15..09-22, **13 commits**, `c73b628b..0b721940`.
- Churn: `VerifierRel.v` (1034), `Verifier.v` (857), `Adequacy.v` (568), plan (425).
- Trusted touch: Result files edited, proof-only. Category: B.
- Summary: at a block boundary the executor *consumes* the block's precondition and
  *produces* its postcondition, exactly like `call_contract`. A cut program stays one
  contract and one VC. `BlkAnnot` (`Verifier.v:420`) is carried in `ai_block`
  (`Verifier.v:474`). Soundness is `blocksSound` (`Adequacy.v:1480`) and `blockSound_of_vc`
  (`Adequacy.v:2010`): a valid contract justifies its block.
- Depends on: AI, SEG.

### 27. CAST: contract-AST (annotations as tool input)
- Plan: `plans/PLAN-contract-ast.md` (Phases 1-5 landed; several naming decisions retracted
  in-plan).
- 09-22..09-23, **23 commits**, `91d9fdc9..11e0a562`.
- Churn: `PLAN-contract-ast.md` (2022), `EndToEnd.v` (474), `Verifier.v` (360), `Adequacy.v`
  (286), `GenCompose.v` (188).
- Trusted touch: `noninterferent_strong` theorems proof-only. **Iris-level composed statements
  changed**: `swap_composed`, `cdInv`, `tOwn` in `f95f32c0`, and `cdExit` in `11e0a562`.
- Category: B.
- Summary: `cfg_instrs` becomes `list AST`. The annotated list is an argument to the
  *verification* (`cfg_vc`, `Contracts.v:180`), not part of the specification.
  `CFGVerifierContract` moves to `Verifier.v:371`. `ValidCFGVerifierContract`
  (`Validity.v:134`) is a sealed, annotation-free validity. `blockFaithful`
  (`Adequacy.v:1983`) is proved rather than assumed. Blocks own only their span
  (`ptsto_instrs_w_split`, `VerifierRel.v:2869`).
- Depends on: EXC, AI.

### 28. REC: loop as a self-referential block (Löb)
- Plan: `plans/PLAN-rec-loop-block.md`. 09-24..09-25, **7 commits**, `d8f8da90..acc3a37c`.
- Churn: `GenCompose.v` (786), `VerifierRel.v` (607), `Adequacy.v` (339), `Verifier.v` (332),
  `Example/CountdownRecResult.v` (330).
- Trusted touch: additive (`countdown_rec_noninterferent_param`, data `cd_link_instrs`).
- Category: B.
- Summary: a loop is one block whose precondition is its invariant. The VC runs the body once
  with the head annotated `ai_loop` (`Verifier.v:484`). The back edge consumes the invariant,
  and soundness is a single Löb induction inside `blockSound_of_vc`. This gives partial
  correctness only. It replaced LoopSpec glue for new work and is the loop mechanism ARR
  uses.
- Depends on: EXC, CAST.

### 29. VBA: valid block annotations (`AnnotInstrV`)
- Plan: `plans/PLAN-valid-blk-annot.md` (COMPLETE). Merge: `b001d1a3`.
- 09-25..09-29, **11 commits**, `6a6ebfdd..a8367495`.
- Churn: `GenCompose.v` (521), `EndToEnd.v` (413), plan (333), `.claude/skills` (307),
  `Validity.v` (281).
- Trusted touch: Result aux lemmas only. End statements unchanged, including at `0d9f56e2`,
  which drops `cfg_init_addr`.
- Category: B.
- Summary: instead of a post-hoc `blocksSound` premise, an `ai_block` annotation carries a
  proof that its block is valid (`AnnotInstrV`, `Verifier.v:560`; `blkValid`,
  `Adequacy.v:2145`). The VC checks containment (`blk_code_in`, `Verifier.v:1135`; fixed for
  more than 63 instructions in `db668dae`). Sub-table and dead block lemmas are deleted, and
  so are `cfg_init_addr` and all dead load-address parameters.
- Depends on: EXT, REC.

### 30. ARR: array invariants for loop blocks, parametric muladd
- Plans: `plans/PLAN-array-invariants.md`; `plans/PLAN-chunk-facts.md` (REVERTED, patch kept).
  Merge: `d8ca8316` (`issue/array-invariants`).
- 09-28..10-02, **35 commits**, `ed639815..d8ca8316`.
- Churn: `PLAN-array-invariants.md` (1146), `Example/MuladdParamResult.v` (440),
  `plans/chunk-facts.patch` (424), `Example/MuladdParamInstrs.v` (358), `SpecIris.v` (293).
- Trusted touch: additive. `muladd_param_noninterferent`
  (`Example/Muladd/MuladdParamResult.v:343`) has its spec lists `sym_reg_specs`/`sym_mem_specs`
  defined *inside* the Result file (lines 299/301). `PaddedLoopResult.v` was rewritten to a
  `noninterferent_param` theorem. `RiscvPmp/Sig.v` gains the `arr` predicate (a signature, not
  the trusted statement).
- Category: B (+A additive).
- Summary: a loop over an array with a *symbolic* trip count owns a count-dependent number of
  cells, which a fixed-context assertion cannot state. The fix is one family `arr pub w s
  [a; n; e]` (interpreted at `RiscvPmp/IrisInstanceBinary.v:330`) plus a closed catalogue of
  ghost lemmas `CLem` (`Verifier.v:116`, e.g. `clem_arr_lockstep` `:139`), proved sound by
  `clemSem` (`SpecIris.v:1289`). The result is the flat and parametric-mlen BearSSL muladd
  noninterferent end to end. Also included: precise chunk matching on normalised inputs
  (`c32d2d6b`) and removal of a silently shadowed `solve_bv` (`bd3ff6b7`).
- Depends on: VBA, REC.

### 31. KSL: key_schedule_loop scaling hunt I (refuted)
- Plans: `plans/PLAN-term-sharing.md` (REFUTED), `plans/PLAN-havoc-secrets.md` (REFUTED).
  PLAN-solver-fold was deleted at `027d7c27`. Probe branches `e2-term-naming-probe` and
  `havoc-secrets-probe` are unmerged.
- 07-19..07-24, **31 commits**, `8df0d7c5..027d7c27`. Includes 7 reverts and the removal of
  the `select_last_k` fold, which had an added-then-reverted axiom.
- Churn: `PLAN-solver-fold.md` (1457, deleted), ZZ probes (1122), `Example/ProbeFoldAlgebra.v`
  (798, deleted), `theories/Symbolic/PartialEvaluation.v` (608).
- Trusted touch: no. Category: C.
- Summary: three successive fixes for a backward-loop scaling wall were tried and refuted:
  opaque term naming, havocking secrets, and a peval accumulator fold. The real driver was
  later found to be a leaked heap chunk (CGC). Net code left: nothing. Read only for the
  history.
- Depends on: SB.

### 32. WCTX: `|wctx|` hunt, unquantify gate, forward world-GC
- Plans: `plans/PLAN-unquantify-gate.md`, `plans/PLAN-unquantify-forward.md`. The world-GC is
  archived on tag `archive/gc-attempt-2026-07` / branch `unquantify-gate` (unmerged).
- 07-29, **16 commits**, `c94eb30b..30c9517a`.
- Churn: ZZ probes (1763), `theories/Symbolic/GenOccursCheck.v` (1261), the two plans,
  `theories/Symbolic/Propositions.v` (144).
- Trusted touch: no. **However, `c5437a16`/`929d55c6` left three `Admitted` instances in
  theories/** (`GenOccursCheckLawsFormula`, `Formulas.v:337`; `SubstSULaws_SymProp`,
  `Propositions.v:1918`; `gen_occurs_check_laws_term`, `GenOccursCheck.v:616`). They are off
  the trusted path, because the gate checks the end theorems are axiom-clean, but they are
  still in the tree.
- Category: C.
- Summary: ports upstream `unquantify` (`Propositions.v:2015`) to drop dead binders, and
  builds a forward world-GC. The GC could not be proved as a local refinement lemma
  (PLAN-nextpc-param §0 explains why). The diagnosis that the `|wctx|` growth came from
  `encodes_instr` fed directly into CGC.
- Depends on: KSL.

### 33. NPC: `nextpc` as contract parameter, `encoded_instr` removal
- Plans: `plans/PLAN-nextpc-param.md`, `plans/PLAN-encoded-instr.md` (DONE; §8 retracts its
  "curve bends" claim). Merge: `e20e9969` (`nextpc-param`, 73 commits incl. LAY tail, WCTX,
  CGC).
- 07-31..08-03, **17 commits**, `05a4ba00..e20e9969`.
- Churn: `PLAN-encoded-instr.md` (982), `VerifierRel.v` (969), ZZ probes (694), `Verifier.v`
  (397), `PLAN-nextpc-param.md` (351).
- Trusted touch: no. Category: C.
- Summary: removes two per-step demonic variables. `an` (nextpc) is threaded as a parameter,
  and the instruction word comes from a word-supply function instead of a fresh variable.
  Execution-driven variable growth went to zero, but end-to-end cost did not bend. WS later
  made the words one wide variable.
- Depends on: WCTX.

### 34. CGC: chunk GC for the leaked `encodes_instr` chunk
- Plan: `plans/PLAN-chunk-gc.md` (LANDED 08-03).
- 08-03, **12 commits**, `2d072fb8..cd79cbe0`.
- Churn: `PLAN-chunk-gc.md` (540), `.claude/skills` (374), `PLAN-encoded-instr.md` (305),
  `VerifierRel.v` (172).
- Trusted touch: no. Category: C.
- Summary: `encodes_instr` is duplicable, so it was never removed on consume. The symbolic
  heap grew one chunk per step, which made cost quadratic. A filter at each step, with
  refinement lemma `refine_chunk_gc` (`VerifierRel.v:484`), makes it linear. This was the
  actual root cause of the July scaling wall.
- Depends on: NPC.

### 35. MASK: mask algebra (`uop.expand`, `bop.coalesce`, `bop.mulx`)
- Plans: `plans/PLAN-coalesce.md` (DONE), `plans/PLAN-ksl64.md` (parked). Merge: `9d4f740f`
  (`solver-expand-mask`, 56 commits incl. BYTE, SIG, FB).
- 08-04..08-17, **9 commits**, `fcccba5e..9d4f740f`.
- Churn: `theories/Symbolic/PartialEvaluation.v` (1011), `theories/Bitvector.v` (608),
  `PLAN-coalesce.md` (391).
- Trusted touch: new operators `expand` (`theories/Syntax/UnOps.v:90`), `coalesce` and `mulx`
  (`theories/Syntax/BinOps.v:91/103`) with their `eval`. They are not used by `Machine.v`, so
  concrete semantics are unchanged. Category: C.
- Summary: peval recognises clang's branchless constant-time mask idiom and the GHASH `mulx`
  step, collapsing 2^N or 3^N term growth to linear. The rules are proved sound in the
  solver.
- Depends on: KSL.

### 36. SIG: chunk count vs `|Σ|` diagnostics
- 08-13..08-18, **9 commits**, `7b80e88e..44394449`.
- Churn: `diagnostics/key-schedule-loop2-cost-drivers.md` (1248), ZZ probes (600),
  `check-scalar-combined-cost-drivers.md` (196).
- Trusted touch: no. Category: C.
- Summary: shows the "declared-chunk" cost was mostly `|Σ|`, the logic-variable count, and
  that pinning with `PVConst` is dominated by grouping existentials. That motivated CLS.
  Several numbers in it were retracted later; see LV and `table-entry-sigma-axis.md`.
- Depends on: BYTE, CGC.

### 37. FB: fetch-bound VCs discharged in the solver
- Plan: `plans/PLAN-fetch-bound-vcs.md` (DONE). 08-17, **4 commits**, `ac23c47c..f8b42d4e`.
- Churn: plan (343), `theories/Symbolic/Solver.v` (284). Trusted: no. Category: C.
- Summary: a solver rule `try_fetch_bound` (`theories/Symbolic/Solver.v:2676`) discharges the
  per-address access bounds during execution. Residuals went 29 to 0, a 2.3-4.3× constant
  factor.
- Depends on: BYTE.

### 38. LV: logical-variable lookup hypothesis
- Plan: `plans/PLAN-lvar-lookup.md` (DONE). 08-19, **2 commits** `f6f11702`, `7de81a3c`.
- Churn: `diagnostics/lvar-lookup-cost-drivers.md` (464). Trusted: no. Category: C.
- Summary: chunks spawn no variables but multiply lookup cost by depth. Its "ctx.fresh next"
  recommendation was retracted by ENV.
- Depends on: SIG, CLS.

### 39. WS: word slicing
- Plan: `PLAN-encoded-instr.md` §12. Merge: `2001202f` (`issue/word-slicing`).
- 08-24, **7 commits**, `aa10ef16..ea125c42`.
- Churn: `PLAN-annotinstr.md` (215), `diagnostics/word-slicing-payoff.md` (171),
  `VerifierRel.v` (133), `Verifier.v` (121). Trusted: no. Category: C.
- Summary: all instruction words become slices of ONE wide demonic variable
  (`words_width`, `Verifier.v:1959`). On br_divrem, `|Σ|` went 63 to 15, for 2.8×.
- Depends on: NPC.

### 40. DROP: dead logical-variable drop (`dropk`) and the PExt/CExt extensionality framework
- Plans: `plans/PLAN-lvar-drop.md` (investigation, "DO NOT FUND" overridden),
  `plans/PLAN-lvar-drop-build.md` (record), `plans/PLAN-dropk.md` (build plan, 3676 lines).
  Merge: `c5ac2c5b` (`issue/dropk-framework`, 108 commits incl. HAV, ENV, MF, COMP, SUBT).
- 08-25..09-06, **55 commits**, `03c96b54..c5ac2c5b`.
- Churn: `PLAN-dropk.md` (4380), `VerifierRel.v` (1846), `Verifier.v` (941),
  `diagnostics/dropk-firing-payoff.md` (689), `PLAN-lvar-drop.md` (686).
- Trusted touch: no. It is a **generic framework change in theories/**: a new SymProp
  constructor `dropk` (`theories/Symbolic/Propositions.v:170`), `acc_drop`
  (`theories/Symbolic/Worlds.v:444`), and refinement cases in `theories/Refinement/Monads.v`.
  It also adds 94 continuation-extensionality lemmas (`PExt`, `theories/Symbolic/Monads.v:933`;
  `CExt`, `:1425`; `cext_sexec_cfg_addr`, `Verifier.v:1877`).
- Category: C (large and proof-heavy, but not a user-facing mechanism).
- Summary: drops dead logic variables mid-execution. `rdrop_dead` (`VerifierRel.v:1358`) is
  the refinement. `var_dead` (`Verifier.v:1275`) is the liveness test. Its `&&` not
  short-circuiting under `vm_compute` was a 22.7× cost bug, fixed in `289c0327`. The payoff
  became a net 1.87× only after that fix. The "funext wall" was broken by PExt/CExt rather
  than by an axiom.
- Depends on: HAV, plus the pred-modalities skill.

### 41. ENV: `env.lookup` fused walk
- Plan: `theories/plans/PLAN-env-trie.md` (DONE via a smaller fix; the skew-RAL design is
  DROPPED). 09-01..09-02, **7 commits**, `4de34f92..81deaf17`.
- Churn: `theories/diagnostics/env-lookup-cost-drivers.md` (582), plan (340), ZZ (277),
  `diagnostics/ctx-fresh-cost.md` (168), `theories/Environment.v` (115).
- Trusted: no. Category: C.
- Summary: the cost was `ctx.view`'s per-step allocation, not the walk. A fused walk
  (`lookup_at_fold`, `theories/Environment.v:210`) gives 2.4-2.9×. ctx.fresh was measured
  and closed.
- Depends on: LV.

### 42. MF: muladd flat attempt, footprint, Base(K)
- Plan: `plans/PLAN-muladd-full.md` (Phase 3 BLOCKED; superseded by ARR).
- 08-11..09-29, **12 commits**, `46ce6836..b229958d`.
- Churn: ZZ (816), `diagnostics/base-k-hunt.md` (765), the plan (510), `muladd-full-cost-drivers.md`
  (244).
- Trusted: no. Category: C.
- Summary: the flat muladd VC fails on footprint (peak memory), not throughput. Causes
  investigated: term duplication, `|Σ|`², and a Base(K) that no tree-level candidate
  explains. Also records (`b229958d`) that the *unhardened* muladd binary has three secret
  branches.
- Depends on: SB, DROP.

### 43. TE: table-entry cost, vm-vs-tactic split
- 09-07..09-08, **8 commits**, `329d3eb8..c9f8de44`. One headline was retracted the same day
  (`1b18ea8d`).
- Churn: `diagnostics/table-entry-cost.md` (701), `diagnostics/vm-vs-tactic-split.md` (489),
  `VerifierRel.v` (219), `table-entry-sigma-axis.md` (191). Trusted: no. Category: C.
- Summary: `7e5ceffe` makes a declared exit *stop*, removing an `angelic_binary` from
  `sexec_cfg_addr`. A `cbn` in `solve_vc` unfolding `inst_symprop` caused a spurious 48×
  multiplier. diagnostics/ now prices the pipeline split into `vm_compute` vs tactic.
- Depends on: SUBT.

### 44. BVA: bitvector ring normalisation in peval
- Plan: `plans/PLAN-bv-arith-solver.md` (PROPOSED; U5 recorded). On the array-invariants branch.
- 09-29..10-01, **6 commits**, `23f904fa..1c9cfee1`.
- Churn: `theories/Symbolic/PartialEvaluation.v` (2267), plan (364), `theories/Symbolic/Solver.v`
  (235). Trusted: no. Category: C.
- Summary: canonical ring forms for bv sums, exact over RelVal. This reinstates upstream
  `peval2` (`PartialEvaluation.v:2987ff`). `secLeakT` (`Solver.v:249`) becomes
  compositional, and the solver drops public zero atoms. RVP §6 R1 plans to simplify this
  once RelVal is a pair.
- Depends on: ARR.

### 45. SOLM: small solver fixes
- 07-28..09-22, **5 commits**: `17c18d63`, `6d69e7dc`, `55421905`, `bc4adb1d`, `3223f7a5`.
- Churn: `theories/Symbolic/Solver.v` (336), `.claude/skills` (323), `CFGVer/Spec.v` (42).
  Trusted: no. Category: C.
- Summary: covers four things. `0 <= unsigned t` is discharged as `secLeak t`. A
  fact-burning `bop.eq` case in `formula_simplifies` is fixed. The fetch contract's conjunct
  order is fixed, which removed 28 secLeak residuals and made VCs 6× smaller; the contract
  lives in `CFGVer/Spec.v`. Finally, `try_bvadd_cancel_val_propeq` and peval in
  `simplify_formula`'s propeq/secLeak arms were added (prerequisites of CAST).
- Depends on: none.

### 46. M: misc / infrastructure
- **8 commits**:
  - `e514f2ba`, `a20d61ce`: rocq-mcp cache ignore.
  - `34b0f0b0`: module headers and repo map. It touches `Machine.v`/`Sig.v`, verified
    **comment-only**.
  - `003e3035`: Monotonic Hint Extern.
  - `4a76eca3`: docs reorganised into `plans/` + `diagnostics/`.
  - `29e832f9`: untrack ZZ probes.
  - `6930d41c`: `Example/_CoqProject`.
  - `eaea8b43`: remove dune.
- Category: I.

### 47. T: Claude tooling
- **46 commits**: skills, hooks (`skill-edit-guard`, `skill-path-guard`, `coqc-guard`,
  `git-workflow-guard`), CLAUDE.md files, routing evals, `.claude/commands`. No `.v` files.
  `f90a607e` (PM) also swept in about 1.4k lines of `.claude/commands`.
- Category: T. It is useful context for *why sessions behaved as they did*. It is not about
  the proofs.

---

## (d) Local branches with commits not in HEAD

| branch | commits not in HEAD | forked from | note |
|---|---|---|---|
| `issue/mul-latency-leak` | 8 | `9073e7c6` (10-02) | **changes `RiscvPmp/Machine.v` + `Base.v`** (new `LeakMul`, ARM7TDMI step-count leak; +67/-7). Gate green 10-05 per memory; trusted model change; includes a merge of `issue/aes-inv-mix-columns` |
| `issue/aes-inv-mix-columns` | 2 | `9073e7c6` | AES example. A later version of this work landed as `fe915f1d` (EX) |
| `issue/mul-leaks-args` | 5 | `c9f8de44` (09-08) | earlier `LeakMul` variant (mul leaks both operands), gate passed 09-08; trusted model change |
| `issue/relval-cleanup` | 7 | `9073e7c6` | "PLAN-value-parametric"; checked out in another worktree (`+`) |
| `unquantify-gate` | 9 | `30c9517a` (07-29) | archived world-GC attempt; tip says "SUPERSEDED, does not compile" (tag `archive/gc-attempt-2026-07`) |
| `wip/cfgver-base-offset-split` | 2 | `66bf60f5` (07-05) | abandoned base+offset split, before the GM pivot |
| `e2-term-naming-probe` | 1 | `47e0db7c` | KSL Plan A throwaway (refuted) |
| `havoc-secrets-probe` | 2 | `47e0db7c` | KSL havoc throwaway (refuted) |
| `main` | 148 | `a163bb7a` (2025-08-01) | upstream. Read-only, by policy never a merge target |

The current branch `issue/relval-pair` (RVP) is itself not yet merged into `KatamaranRel`.

---

## (e) Method and caveats

**How groups were formed.** I took the 680 commits from `git log --reverse a71bc67b^..HEAD`
and assigned each by hand. The signals, in priority order, were:
- the PLAN file the commit creates, edits or names;
- the branch of the enclosing merge (`git log M^1..M^2`);
- subject keywords.

Pure tooling was detected first, automatically: commits touching only `.claude/`,
`CLAUDE.md` or `.gitignore`. Some of those were moved back into initiatives because their
content is research notes in `.claude/TODO.md`: PM's `e9245b74..54da6351` and `823e81fd`,
KSL's `8df0d7c5`/`318ca054`, WCTX's `c94eb30b`, and LAY's four cost-record commits. Merges
are counted in the group whose branch they close. Long-lived branches (`nextpc-param`,
`solver-expand-mask`, `dropk-framework`, `muladd-composed`) span several initiatives, so the
merge-to-group mapping is a convention and not a fact.

**How trusted-surface touches were determined.** I did not rely on commit messages.
1. `git log -- <file>` for `Noninterference.v`, `RiscvPmp/Machine.v`, `RiscvPmp/Base.v`,
   `RiscvPmp/Sig.v`, every `*Result.v`/`Results.v`, and pre-split `Examples.v`. Each hit was
   inspected with `git show`.
2. A Python script (now `scripts/stmtdiff.py`) extracted every `Lemma/Theorem/Definition/Fixpoint`
   *statement* (text up to `Proof.`, or to the first `. ` for definitions), with comments
   stripped and whitespace normalised. It did this before and after each commit and reported
   added/removed/changed names. This was run over every commit touching a Result file, and over
   non-Result Example files filtered to `*_instrs`/`*_specs`/`*_regs` names.
3. For GenContract.v, I grepped changed lines for the `param_val`/`PV*`/`concretize_*`
   vocabulary, then identified `concretize_reg/_mem` (`GenContract.v:832/840`) and
   `concretize_reg_q`/`concretize_data` (`GenSegment.v`) as the parts that occur *inside*
   end-theorem statements.
4. For theories/, I listed commits touching semantics-bearing files (`Syntax/*`,
   `Bitvector.v`, `Semantics.v`, `SmallStep`, `Iris/*`, `TypeDecl.v`) and read the messages
   and diffs of the suspicious ones (`902a4e2e`, `f90a607e`, `5835e3da`, the RVP commits).

**Limits of that method.**
- The statement extractor is heuristic. A definition containing `. ` inside a string or
  notation could be truncated, and Ltac/Notation changes are invisible to it. So "proof-only"
  means "no extracted statement text changed".
- Changes to definitions *used by* a statement in another file are caught only for the files
  listed above. A change in, for example, `Tables.v`'s `instrs_of_list` (used via
  `mem_has_instrs`) would be missed. `mem_has_instrs`, `declare_*` and `gen_init_*` live in
  `Noninterference.v` and are covered.
- `d460a993`'s "byte-identical elaboration" claim and RVP's "every diff line is inside
  Proof…Qed" claim were spot-checked, not fully re-verified.

**Classifications I am not confident about.**
- The SEG/LOOP split. They interleave on 09-11..09-14 and were split by subject keywords
  (LoopSpec, latch, reservoir, "PLAN 3u..4c" → LOOP).
- MF vs ENV for `396`-`406`.
- Placing `5835e3da` (the sub_assertion bug fix) in LOOP. It is really a theories bug fix.
- BYTE also absorbs the check_scalar cost-driver commits (`0721c750`, `02bdcdc1`,
  `14794add`..`9249811c`), which could stand alone.
- SOLM is a catch-all.

**Summaries based on PLANs and messages rather than code.** These are KSL, WCTX, NPC, CGC,
MASK, SIG, FB, LV, WS, DROP (beyond the names), ENV, MF, TE, BVA, HAV, the payoff numbers
everywhere, and all "superseded/retracted" statements, which come from PLAN status blocks.
The code-checked parts are the trusted-surface verdicts and the existence and location of
every named definition. Names quoted from memory notes that do NOT exist at HEAD are flagged
(`loop_all`/`loop_edge_std`/`loop_latch_obl`/`loop_done`, `itable_faith_of_segment`).

**Other things worth knowing.**
- The composed Result files (`SwapComposedResult`, `CountdownComposedResult`,
  `TwoLoopsComposedResult`) state Iris-level `-∗ myWP2_loop` facts, not
  `noninterferent_strong`. They ARE in the gate's axiom-clean list (`scripts/gate.sh:81-84`,
  e.g. `swap_composed`, `cd_loop`), so they count as "end theorems" even though they are
  not concrete noninterference statements. A first draft of this file said otherwise, and
  it was corrected after checking.
- `Admitted` count changes since `a71bc67b^`: +1 each in `theories/Syntax/Formulas.v`,
  `theories/Symbolic/Propositions.v` and `theories/Symbolic/GenOccursCheck.v` (WCTX). The
  pre-existing ones in `CFGVer/Spec.v`, `RiscvPmp/Contracts.v` and `ModelBinary.v` are
  unchanged. The gate's axiom check on end theorems is what keeps these off the trusted path.

## Appendix

Appendix (per-commit listing) lost with the session scratchpad on 2026-10-08; not regenerated.
