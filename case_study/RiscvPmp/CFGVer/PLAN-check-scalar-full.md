# PLAN-check-scalar-full — BearSSL `check_scalar` to a whole-function end theorem

Status: **IN PROGRESS, written 2026-08-07, updated 2026-08-10.**
**Phase 1 (§2) is DONE and committed (`0eb02b36`).**
**Phase 2 (§3) is DONE, gate green, 14th axiom-clean end theorem
`check_scalar_loop1_noninterferent_param` — see §3's Outcome.**
**Phase 3 (§4) is DONE — GATE 3 passed: loop 2 standalone at N=32 compiles
axiom-clean, 278.30 s user CPU / 10.62 GB peak RSS. See §4's Outcome, and its
memory note before re-running N=32 unattended.**
Phase 4 (§5, the whole-function decision) is next and is an OWNER decision,
not something to pick unattended — read §5 before starting.

Audience: a later session executing one phase at a time. Each phase has an
explicit GATE — reach it, report, and stop. Do not run two phases in one session.
**Model routing is in §0.5 — check it before starting a phase.**

**Read before starting, in this order:**
1. `PLAN-byte-memory.md` **§10** — the measurement record this plan builds on.
   Its "Next, in order" list is what §3/§4/§5 below expand into phases.
2. `PLAN-coalesce.md` §1 — why loop 2's term wall is already down.
3. Skills: **`cfgver-solve-vc`** (VC residuals), **`cfgver-memory`** (data-memory
   wiring), **`rocq-implementation`** (the mandatory rocq-mcp preamble workflow —
   read §1 before writing any tactic).

Every "VERIFIED" below was checked against the tree on 2026-08-07 with the
`file:line` given. Every "DESIGN" is a proposal that has not been compiled.

---

## §0. The target, and why it is reachable now

BearSSL P-256 `check_scalar` (`ec_p256_m62.c:1610`), the third of three
"Breaking Bad" targets (Schneider et al., ASIA CCS'25, arXiv:2410.13489):

```c
z = 0;
for (u = 0; u < klen; u++) z |= k[u];                          /* loop 1 */
c = 0;
for (u = 0; u < klen; u++) c |= -EQ0(c) & CMP(k[u], P256_N[u]); /* loop 2 */
```

Real `klen` is **32**. Every structural wall that has ever blocked this program
is now down — that is the whole reason this plan exists:

| Wall | Status | Evidence |
|---|---|---|
| 2^N accumulator in loop 2's mask chain | **down** | `PLAN-coalesce.md` §1: `uop.expand` / `bop.coalesce` / `srl-sra by 31` counts exactly linear over 1–4 unrolled copies, measured on the REAL body (`Example/ZZCsUnroll.v`) |
| no byte-granular memory for `lbu` | **down** | `byte_chunks` (`GenContract.v:203`); loop 1 VC green at the real N=32 (`Example/ZZByteLoop1N32.v`) |
| `\|Σ\|` growth from per-byte variables | **down** | one word variable per entry (`GenContract.v:~240`); −43% VC, −56% `Qed`, doubling-slope 1.39 → 1.02 |
| pointer-compare exponent (driver B) | **down** (2026-08-10, `0eb02b36`) | §2 "Outcome": loop-1 N=32 VC 112 s → **36.93 s** user CPU |

What is left is plumbing plus one never-attempted compile. No new mathematics is
believed necessary — if a phase turns up some, that is a STOP-and-report event,
not something to improvise around.

**Currently landed** (`Example/BearSSLCheckScalarResult.v`):
`check_scalar_noninterferent`, axiom-clean. Note what it covers —
`check_scalar_instrs` is **loop 2's 16-instruction BODY**, straight-line, with
operands already in registers and no memory at all. VERIFIED via
`Example/ZZCsUnroll.v`'s header, which imports it and describes it as "the REAL
check_scalar body". There is no loop and no memory in the landed theorem.

---

## §0.5. Model routing — which phase goes to which model

**The split is by DELIVERABLE TYPE, not by phase difficulty.**

- **A proof obligation** (the deliverable is a `Qed`) → **Sonnet**.
- **Mechanical replication from an existing template, plus recorded
  measurements** → **Haiku** is fine.
- **Anything that changes a soundness statement, the trusted surface, or core
  `theories/` machinery** → neither, unattended. Escalate.

| Phase | Model | Why |
|---|---|---|
| ~~§2 — `try_bvadd_cancel_spec`~~ | **DONE** `0eb02b36` | Was: dependent `Equations`, `Term_eqb_spec`, RelVal case analysis, `⊣⊢` both directions, preamble mode throughout. Landed on Sonnet as routed |
| §3 — §5.3 Iris wiring | **Sonnet** | Iris proof mode plus address-form reconciliation, with a documented `cbn` landmine |
| §4a — build loop 2's file set, run the compiles, record CPU/RSS | **Haiku** | `asm_to_ast.py`, replicate the `ZZByteLoop1N*` layout, run `/usr/bin/time`. Genuinely mechanical |
| §4b — diagnose whatever residual shapes appear | **Sonnet** | Loop 1 turned up two unanticipated shapes; reading a goal and inventing the right small lemma is not mechanical |
| §5 — whole-function decision | **Owner decision**, then Sonnet to execute | A judgement call on architecture from measured numbers |
| §6 — region chunks | **Neither, unattended** | Touches `try_consume_chunk_user_precise_spec` and the refinement chain. Its cheap probe (§6, last paragraph) IS Haiku-suitable; the change itself is not |

### Three failure modes recorded on THIS repo — the reason for the split above

All three are documented incidents, not hypotheticals (see the
`project-key-schedule-loop-scaling` memory note):

1. **Fabricated measurements.** "N=16: 6.1 s / N=64: 6.8 s" was never plausible
   (6.8 s at N=64 would beat the measured N=8) and came from uncommitted local
   edits, so it was unreproducible by construction. REFUTED — never requote.
   → **Rule for §4a: paste the raw `/usr/bin/time` output into the report. Never
   type a number from memory, and never report a figure from a run whose
   `Finished transaction` line you did not see.**
2. **Axiomatized the goal.** Two chunk-GC obligations were stated as `Axiom`s and
   the refinement derived from them — i.e. the result was assumed. Those commits
   are deliberately not in any branch.
   → **Rule for §2/§3: if the `Qed` cannot be reached, the correct outcome is to
   report WHY. Never weaken the statement, add a hypothesis, `Admit` a sub-goal,
   or introduce an axiom to get a green build.**
3. **A two-site consistency error.** `Adequacy.v` was left at `false false`
   while `Contracts.v` emitted `true true`, so the fast VC could not reach the
   adequacy chain at all. Cost a build.
   → **Rule generally: when a value is set in two places, grep for every site
   before reporting done.** `scripts/gate.sh` is the check that catches this.

---

## §1. Starting point

- Branch `solver-expand-mask`. `theories/Symbolic/Solver.v` is **modified and
  uncommitted** — that diff is Phase 1's subject. Do not discard it.
- Gate: `scripts/gate.sh` with `GATE_JOBS=1` (see `CFGVer/CLAUDE.md` for the
  RAM-bound reason). 13 axiom-clean end theorems today; the allowlist is exactly
  `Machine.pure_decode` and `Base.mmioenv`. Any phase that adds a third axiom has
  failed, regardless of what else it achieved.
- The `Example/ZZ*.v` files are throwaway probes, deliberately NOT in
  `_CoqProject`. Keep new probes that way, and remember `scripts/gate.sh`'s
  hole-scan is unconditional over the whole `CFGVer` tree — an `Admitted` in a
  scratch file blocks the gate even if nothing depends on it.

---

## §2. Phase 1 — discharge `try_bvadd_cancel_spec`

**Smallest item, unblocks everything downstream, and it is already in the tree.**

### What exists (VERIFIED, uncommitted)

`theories/Symbolic/Solver.v` now has, just before `simplify_relop`:

- `bvadd_cancel_pair` — an `Equations(noeqns)` matching
  `term_binop bop.bvadd (term_val _ v1) s1` against
  `term_binop bop.bvadd (term_val _ v2) s2`, returning `Some (v1, v2, s1)` when
  `Term_eqb s1 s2`.
- `try_bvadd_cancel op t1 t2` — restricted to `σ = ty.bvec n`, guarded by
  `secLeakT s`, returning `if bop.eval_relop_val op v1 v2 then empty else error`.
- Both the `bop.eq` and `bop.neq` arms of `simplify_relop` dispatch through it.
- `simplify_relop_spec` is **fully proved around it** — the eight-branch
  `destruct op` is written and the comment explains why the branches are
  destructed by name rather than by `context[match _ with _ => _ end]`.

The single hole:

```coq
Lemma try_bvadd_cancel_spec {w : World} {σ} (op : RelOp σ)
  (t1 t2 : STerm σ w) (d : DList w) :
  try_bvadd_cancel op t1 t2 = Some d ->
  instpred d ⊣⊢ instpred (formula_relop op t1 t2).
Admitted.
```

### Why it is true

`bv.add` is injective in each argument, so at the `Val` level
`c1 + a = c2 + a ↔ c1 = c2` holds **unconditionally** in ℤ/2³² — no no-wrap side
condition, unlike most bitvector rules.

### Proof route (DESIGN — expect to iterate)

1. `destruct σ`; every constructor other than `ty.bvec n` makes
   `try_bvadd_cancel` return `None`, so `discriminate`.
2. Destruct `bvadd_cancel_pair t1 t2`; the `None` arm discriminates. Because
   `bvadd_cancel_pair` is `Equations`, use `funelim` or destruct `t1`/`t2` down
   to the `term_binop bop.bvadd (term_val _ _) _` shape by hand. `Local Set
   Equations Transparent` is already on at `Solver.v:68`, so direct computation
   is available.
3. `Term_eqb s1 s2 = true → s1 = s2` comes from `Term_eqb_spec`.
4. Destruct `secLeakT s`; the `false` arm discriminates. In the `true` arm apply
   **`secLeakT_spec` (`Solver.v:230`)** to obtain `instpred (formula_secLeak s)`.
   That is what discharges the `NonSyncVal` case: `formula_relop` sends a
   `NonSyncVal` operand to `False` (`Formulas.v:147`), and `secLeak s` is exactly
   the fact that rules it out. Read **`secret-data-walls`** before touching this
   step.
5. What remains is a `Val`-level identity: for `op ∈ {eq, neq}`,
   `eval_relop_val op (bv.add v1 s) (bv.add v2 s) = eval_relop_val op v1 v2`.

**The one lemma choice a session will get wrong.** `peval_bvadd` canonicalises
to **constant-headed** form `c ⊕ t`, so `bvadd_cancel_pair` matches with the
constant on the LEFT and the shared term `s` on the RIGHT. You therefore need

- **`bv.add_cancel_r` (`Bitvector.v:1482`)**: `add x z = add y z → x = y`,
  instantiated at `z := s`.

**Not** `bv.add_cancel_l` (`Bitvector.v:1475`, `add x y = add x z → y = z`),
which cancels the LEFT operand and will not apply. The `⊣⊢` needs both
directions; the reverse is `f_equal`.

Precedent for the whole shape: `simplify_eq_binop_bvapp'` cancels via
`transparent.nat_add_cancel_l` at `Solver.v:701-713`.

### Traps

- **`rocq_compile_file` cannot build `theories/Symbolic/Solver.v`.** This is
  documented in `rocq-implementation` §1. Use preamble mode via `rocq_start`, or
  build through `make -f Makefile.coq`.
- Ordering relops do **not** cancel — bv addition wraps
  (`0 ≤u 0xFFFFFFFF` but `0+1 >u 0xFFFFFFFF+1`). That is why there is an explicit
  `bop.neq` arm rather than a fold into the catch-all. Do not "simplify" the
  definition by generalising it to all relops.

### GATE 1

`theories/Symbolic/Solver.v` compiles with **no `Admitted`**, and
`scripts/gate.sh` (`GATE_JOBS=1`) is green with the axiom allowlist unchanged at
exactly `Machine.pure_decode` + `Base.mmioenv`.

Then measure the payoff on an existing probe: `Example/ZZByteLoop1N32.v` should
move from ~112 s VC toward the counter-proxy's ~25 s (`PLAN-byte-memory.md` §10,
"CONSOLIDATED" table). Report the actual number — the proxy is a proxy, and if it
lands nowhere near, that is information Phase 3 needs.

**Commit and stop.**

### Outcome — GATE 1 PASSED, 2026-08-10, commit `0eb02b36`

`try_bvadd_cancel_spec` and its `Equations` inversion lemma
`bvadd_cancel_pair_spec` are proved (`Solver.v:2589`, `Qed`). Gate green, 13 end
theorems, allowlist unchanged.

**Measured: `Example/ZZByteLoop1N32.v` VC 112.13 s → 36.93 s user CPU, 3.0x.**

Two corrections to the plan as written, both worth carrying forward:

1. **The counter proxy over-promised by ~1.5x.** It predicted 25.13 s; the real
   solver rule delivers 36.93 s. Driver (B) is genuinely down, but the proxy was
   an optimistic bound, not an estimate. **Every §4/§5 projection below that was
   calibrated on 25 s is re-anchored on 36.93 s.**
2. **The rule as first written was UNSOUND and the plan did not catch it.**
   `try_bvadd_cancel` was restricted by *type* (`ty.bvec n`) but not by
   *operator*, so the stated spec was false for ordering relops — exactly the
   wrap-around trap the "Traps" bullet above warns about, present in the code the
   plan described as merely needing a proof. Now restricted to `eq`/`neq`.
   Lesson: a "single hole" in an uncommitted rule is not evidence the rule around
   it is right.

---

## §3. Phase 2 — §5.3 Iris wiring, loop 1 as the 14th end theorem

The only thing between the existing green loop-1 VC and an axiom-clean end
theorem. `PLAN-byte-memory.md` "Next" item 1 holds the detailed route; it is
summarised here only so this document stands alone. **Read that item, it is
authoritative.**

### The shortening insight

All of loop 1's entries are `PVExist`, and for those you do **not** need
`word_byte` at all. `get_word` (`Noninterference.v:139`) is already a nested
`bv.app` of four `memory_ram` bytes, so **`ptstomem_bv_app`
(`IrisInstanceBinary.v:315`, proved, relational)** applies three times directly
to `interp_ptstomem (width := 4) (SyncVal a) (get_word μ a)` and yields the four
`interp_ptsto` chunks with no subrange reasoning at all.

`word_byte` is needed only for PINNED (`PVConst`) entries, where `ImplPre` must
show `ram μ (a+j) = word_byte j v` from `get_word μ a = v`. Route:
`bv.take_app` (`Bitvector.v:974`) / `bv.drop_app` (`Bitvector.v:947`).

### Traps

- **Do NOT attempt the reassembly lemma with `cbn`.** It explodes into a
  multi-thousand-line `bv.view` match.
- **Address forms disagree and reconciling them is the fiddly part.**
  `interp_ptstomem` peels with `bv.one + addr`, giving `1+(1+a)`; the assertion
  says `bv.add a (bv.of_N j)`. Commuting and associating those is where the time
  goes. Budget for it; it is not a sign the design is wrong.

### GATE 2

A `check_scalar_loop1_noninterferent` end theorem in a new
`Example/BearSSLCheckScalarLoop1Result.v`, axiom-clean at the existing allowlist,
gate green, **14** end theorems. The instruction list and specs move out of the
`ZZByteLoop1*` probes into a real `Example/` file added to `_CoqProject`.

This is a publishable result on its own — the first byte-granular example in the
repo. **Commit and stop.**

### Outcome — GATE 2 PASSED, 2026-08-10

Landed in `EndToEnd.v`: `gen_mem_asn_of_ptstomem_bytes` (the per-entry Iris
bridge — the hard part, see the "Address forms disagree" note above),
`gen_implpre_mem_bytes` (list induction over it), `gen_mem_pre_rel_bytes_concretize`
(the pure `_rel`→concrete syntactic bridge), and `gen_contract_noninterferent_rel_bytes`
+ `_simple` (the top-level bridge, mirroring `gen_contract_noninterferent_rel`).

**Scope call worth recording:** the general bridge fixes the WORD-level
`mem_specs` argument of `gen_contract_rel_bytes` to `[]` rather than threading
a combined `mem_specs ++ byte_mem_specs` through `HDataAddrs`/`Hlen`/a
`big_sepL_app` split. No CFGVer program has ever needed both word- and
byte-granular data memory at once, so the general case would have been unused
complexity. Generalise if that need arises.

Promoted `ZZByteLoop1Common.v`/`ZZByteLoop1N32.v` into real
`Example/BearSSLCheckScalarLoop1.v` (klen fixed at 32, not left parametric —
the VC re-measured at 36.93 s user CPU, matching the probe exactly) +
`Example/BearSSLCheckScalarLoop1Result.v` (`check_scalar_loop1_noninterferent_param`
+ a concrete corollary at `init_addr`), wired into `_CoqProject` and
`Results.v`, `check_scalar_loop1_noninterferent_param` added to
`scripts/gate.sh`'s `AXIOM_CLEAN_THMS`. Gate green: 14 end theorems,
axiom-clean at the unchanged allowlist (`Machine.pure_decode`, `Base.mmioenv`).

**One infrastructure trap hit along the way, worth restating:**
`rocq_compile_file`/`rocq_start` reported a clean pass on a version of
`gen_mem_asn_of_ptstomem_bytes` that was actually broken (missing one
`bv.add_assoc`/`bv.of_N_add` fold on the PVConst/is_pub=true branch's 4th
address) — a stale pet-cache false positive, not a real check. Only an
independent `make -f Makefile.coq` caught it. **Trust `make`, not
`rocq_compile_file`, for the final confirmation of anything touching a file
with many accumulated interactive sessions.**

---

## §4. Phase 3 — loop 2 standalone: COMPILE AND MEASURE

Loop 2 as a real loop with memory has **never been compiled**. This phase is a
measurement, not a proof effort.

### What is new relative to loop 1

- **64 resident cells**, not 32 — both `k` (secret) and `P256_N` (public) are
  32 bytes.
- **A `P256_N` representation choice that Phase 2 lets you dodge and Phase 3 does
  not.** §3's shortening insight — "all of loop 1's entries are `PVExist`, so you
  do not need `word_byte` at all" — is what makes Phase 2 cheap. It does **not**
  carry here if `P256_N` is pinned: `PVConst` is exactly the case where `ImplPre`
  must prove `ram μ (a+j) = word_byte j v`, i.e. the `bv.take_app`/`bv.drop_app`
  subrange work, with the `cbn` landmine. So that cost is DEFERRED by Phase 2,
  not avoided.
  **But pinning may not be necessary.** `param_val`'s `PVExist`
  (`GenContract.v:361`) carries `is_pub` separately, so a public-but-unpinned
  entry is expressible, and per `PLAN-byte-memory.md`'s driver-(C) note the
  shapes then match directly (`secLeakvar "mw"` against the `SyncVal` word
  `interp_mem_with_public_memory` hands out) — no subrange lemma. The VC should
  not need `P256_N`'s concrete bytes: loop 2's chain is branch-free, so nothing
  branches on the comparison, and publicness is all noninterference needs.
  **Try public-`PVExist` FIRST; fall back to `PVConst` only if the VC actually
  demands the literals.** If it does, that is the one place the deferred
  `word_byte` work comes due.
- **~16 instructions per iteration** against loop 1's 4.
- The mask/accumulator chain, which `coalesce` has made linear on the real body
  but which has never been run *inside a loop with memory loads*.

### Method

1. Get the assembly the same way every other example did — `tools/asm_to_ast.py`;
   follow **`cfgver-new-example`** for the full recipe (exitCond, fuel,
   `extra_exit_offs`, `gen_contract`, the end lemma).
2. Build it at N = 4, 8, 16, 32 as separate files, one heavy `Eval` per `coqc`
   process. Reuse the `ZZByteLoop1N*` file layout verbatim.
3. **Re-measure; do NOT extrapolate.** `PLAN-byte-memory.md` says this explicitly
   and it has been right every previous time.

Projection for calibration only, **re-anchored 2026-08-10 on Phase 1's measured
36.93 s** (not the 25 s proxy `PLAN-byte-memory.md` §10 used): same crude
`steps × cells` model, ~3.25x the steps and 2x the cells, so
**6.5 × 36.93 ≈ 240 s** of `vm_compute` at N=32. Treat a result within 2× as
success.

Note what this does to §5's decision threshold: 240 s is ABOVE the "under ~200 s
lands comfortably" line, so on the current anchor loop 2 is expected to come in
*tight*, and the `chunk_gc` widening lever is more likely to be needed than the
original plan assumed. Do not pre-emptively build it — measure first — but do not
be surprised into thinking something broke.

### Progress so far (2026-08-10, IN PROGRESS — not GATE 3 yet)

Compiled standalone from real clang output (`loop2.c`, GT/CMP/EQ0 exactly as
`BearSSLCheckScalar.v`'s header): `Example/ZZByteLoop2Common.v` (parametric
over the byte count `n`, mirrors `ZZByteLoop1Common.v`) +
`Example/ZZByteLoop2N{4,8,16,32}.v`. Both `k[]` and `n[]` (P256_N) are tried
as **public-but-unpinned `PVExist`** per this section's own advice — n[] is
`is_pub := true`, NOT `PVConst` — deferring the `PVConst`/subrange cost this
section flagged as due here. Not yet known whether that holds at N=32; if the
VC ends up demanding `n[]`'s literal bytes, fall back to `PVConst` per this
section's fallback clause.

Loop 2's compiled comparison idiom differs from `check_scalar_step`'s 16-instr
body: standalone, clang picked a SHORTER branch-free sequence (two `sltu` +
`neg`/`or`, 13 instructions total per iteration) rather than the XOR-based `GT`
formula `check_scalar_instrs` uses when compiled as part of the larger
function. Both are branch-free; this is a codegen-context difference, not a
semantic one — noted in `ZZByteLoop2Common.v`'s header so it isn't mistaken
for a translation error later.

| N | user CPU | system | wall | peak RSS | notes |
|---|---|---|---|---|---|
| 4  | 23.08 s | 3.44 s | 26.54 s | 3.52 GB | passed first try, axiom-clean |
| 8  | 38.58 s | 3.71 s | 42.31 s | 4.24 GB | passed first try, axiom-clean |
| 16 | 85.21 s | 5.13 s | 90.44 s | 6.47 GB | passed first try, axiom-clean |
| 32 | 278.30 s | 21.07 s | 306.89 s | 10.62 GB | **GATE 3 — passed on the 4th `coqc` attempt; first 3 were killed by a memory-pressure watchdog, not a Coq error — see note below**, axiom-clean |

Doubling ratios (user CPU): N4→8 **1.67×**, N8→16 **2.21×**, N16→32 **3.27×**
(278.30/85.21). The exponent is accelerating each doubling, not settling —
confirms this file's own §8 rule against trusting an early exponent. On peak
RSS the ratios are gentler: 1.20×, 1.53×, 1.64×.

**GATE 3 memory note (new finding, 2026-08-10).** N=32 needs ~10.6 GB peak
RSS, and on this machine (15.3 GB RAM, both `systemd-oomd` and
`earlyoom -r 3600` active) that is close enough to the ceiling that it is
NOT reliably reproducible without care:

- Attempt 1 and 2: killed by `SIGTERM` (`/usr/bin/time` reports "Command
  terminated by signal 15") at ~290–302 s user CPU / ~9.4–9.8 GB RSS — i.e.
  BEFORE reaching the eventual 10.62 GB peak, with `Closed under the global
  context` never printed. Exit code was reported as the misleading `0` by the
  shell wrapper's `echo DONE_EXIT_$?` in one case — **trust the presence of
  `Closed under the global context` in the log, not the wrapper's exit code,
  when a watchdog may have intervened.**
- Between attempts, closing Thunderbird (and, by the successful attempt,
  most of Firefox) was enough to clear it. No swap growth during the two
  failed attempts pointed at a leak; system-wide `available` memory simply
  ran out because ~1.6 GB was already committed to other GUI apps that had
  nothing to do with the compile.
- This is a MACHINE-CAPACITY finding, not a Coq or proof-content finding —
  record it so a later session doesn't mistake a `SIGTERM` here for a real
  compile failure and start debugging the `.v` file. If N=32 (or the
  eventual whole-function compile, §5) needs to run unattended or on CI,
  either budget ≥12 GB free RAM for the one process, or use
  `systemd-run --scope -p MemoryHigh=... nice ...` bookkeeping is not needed —
  just close memory-hungry GUI apps first and check `free -m` shows
  ≥12 GB `available` before starting.

Each N was run, from the repo root:
```
coqc -Q case_study/RiscvPmp Katamaran.RiscvPmp -R theories Katamaran \
  case_study/RiscvPmp/CFGVer/Example/ZZByteLoop2N<N>.v
```
under `/usr/bin/time -v`, one process per N (`ZZByteLoop2Common.vo` was
already built). **Watch the shell CWD** — it drifted to
`case_study/RiscvPmp/CFGVer` twice during N=4/8 and caused two spurious
"Can't find file" failures with near-zero CPU time (a dead giveaway it's a
path problem, not a real compile failure) — always `cd` to the repo root
explicitly first, don't rely on a persistent shell.

### Expect first-use surprises

Loop 1's first compile turned up **two** residual shapes nobody predicted (a
byte access leaving an access bound with offset 1 rather than 4; a pointer
compare leaving `p+k ≠ p+k → False`). Both were small lemmas, both looked like
"the design doesn't work" to someone who had not read the goal. Budget for the
same here and read the actual residual before concluding anything.

### GATE 3

Loop 2 verifies standalone at the real N=32 with a real `Qed`, and the four-point
cost curve is recorded in this file. **Report the curve and stop** — the
whole-function decision in §5 depends on it.

### Outcome — GATE 3 PASSED, 2026-08-10

Full curve above: N=4/8/16/32 all compile with a real `Qed`, axiom-clean
(`Closed under the global context`), still as public-but-unpinned `PVExist`
for both `k[]` and `n[]` — the `PVConst`/subrange fallback was never needed.
N=32: **278.30 s user CPU, 10.62 GB peak RSS**. Against the plan's
re-anchored crude projection (~240 s), that is 1.16× — within the "2× is
success" bound, landing on the "tight" side exactly as §4's own note
anticipated (240 s is above the "under ~200 s lands comfortably" line).

**§5 read on this:** per §5's decision rule, "tight" (not "comfortably under
~200 s") means the whole-function attempt is not a free "attempt directly"
case — the `chunk_gc` widening lever is the indicated next lever if the
combined 64-cell/~640-step whole function misses. This is an owner decision
(§0.5 model-routing table), not something to pick unattended.

Nothing in `_CoqProject`/`Results.v`/`scripts/gate.sh` changed this phase —
the `ZZByteLoop2*` files stay throwaway probes exactly as §4's method
prescribed; promoting loop 2 into a real `Example/` file (mirroring Phase 2's
`BearSSLCheckScalarLoop1.v`) was not part of GATE 3's scope and was not done.

### Follow-up diagnosis (2026-08-10) — why loop 2 accelerates, loop 1 doesn't

Requested after GATE 3: loop 1 (single memory read/iteration, 4-instruction
body) barely accelerates through N=16 (1.13×, 1.41× doubling ratios on freshly
re-measured, post-Phase-1-fix numbers — `Example/ZZByteLoop1N{4,8,16}.v`, not
previously timed at these N), while loop 2 (two reads, 13-instruction body)
accelerates sharply (1.67×, 2.21×). Two ablations, both throwaway probes
(`Example/ZZByteLoop2Abl{,2}{Common,N4,N8,N16}.v`, not wired into
`_CoqProject`):

1. **Ablation 1 — accumulator `A3` read once instead of twice per iteration**
   (the `snez a5,a3` operand changed to `a4`, everything else identical).
   Prior expectation was that this self-referential read (also feeding the
   next iteration's own `A3`) might reproduce the old `key_schedule_loop`
   "k≥2 copies of a register's own value ⇒ super-linear growth" mechanism.
   **Null result**: 21.45/36.44/84.36 s at N=4/8/16 — statistically identical
   to the real body (23.08/38.58/85.21 s), same acceleration (1.70×/2.32× vs
   1.67×/2.21×). Term duplication in the accumulator is NOT the driver.
2. **Ablation 2 — one memory read instead of two** (`lbu a5,0(a1)` replaced by
   a non-memory `mv a5,a0`, `n[]` dropped from the byte specs; instruction
   count held at 13, same as the real body). Result: 19.03/29.77/60.18 s —
   a real ~30% reduction at N=16 and a mildly gentler ratio (1.56×/2.02× vs
   1.67×/2.21×), but **still far steeper than loop 1's own 1.13×/1.41×**
   despite now matching loop 1's read count exactly. The only thing ablation 2
   still shares with loop 2 (not loop 1) is the 13-instruction body.

**Conclusion: body length (steps/iteration), not chunk count or term
duplication, is the primary driver — chunk count is a secondary multiplier.**
This is the SAME cost law already characterized for this executor
(`work ≈ heap_size × (α·S + β·S²)`, S = steps = instructions/iteration × N;
see **cfgver-executor**'s "Backward-branch loops" section) — not a new bug in
the Phase-2 byte-memory machinery. Loop 2's 13-instruction body is close to
`key_schedule_loop`'s ~14-instruction body, whose documented quadratic
crossover is N≈25; loop 1's 4-instruction body pushes that crossover much
further out, which is exactly why it stays near-flat through N=16 (and only
starts to move at N=16→32: 2.11× per the existing Phase-2 number).

**Correction (same day, before §5 was acted on): `chunk_gc` widening is NOT
the right lever here, and the paragraph that used to sit here claiming it was
is wrong.** `ptstomem` chunks are `is_duplicable := false` (`Sig.v:344`) —
unlike `encodes_instr`, they are already removed by ordinary, non-leaking
`consume_chunk` the moment `lbu` reads them. There is no leak for a GC to
fix; "widening chunk_gc to drop consumed cells" cannot remove anything
earlier than immediate consumption already does. The actual mechanism is
that `gen_contract_rel_bytes` asserts **all** `2N` byte chunks in the
precondition up front (not incrementally), so even with perfectly clean
consumption the heap averages `Θ(N)` resident chunks over the `Θ(N)`-length
run, and per-step cost scales with current heap size regardless of how
promptly chunks are removed (`SHeap Σ`'s `Subst`-transport cost, per the
"indexing the heap is a SIZE problem, not a LOOKUP problem" dead-end note in
`cfgver-executor`). Two levers that DO target this correctly, in increasing
order of how much of the mechanism they fix:
- **Region chunks** (§6 below) — collapse `N` separate byte chunks per array
  into ONE, cutting the resident-chunk contribution from `O(N)` to `O(1)`.
  Real payoff, narrower/more invasive than it looks (needs a new
  `PredicateKit` offset-projection hook).
- **Per-iteration loop contracts** (`PLAN-loop-invariant.md`, new plan,
  2026-08-10) — give the loop body its own small contract so the executor
  never carries more than one iteration's footprint at a time, fixing the
  root cause (heap size DURING each step) rather than the chunk
  representation. Larger scope, but every piece it needs already exists and
  works elsewhere in this codebase (`Adequacy.v`'s `myWP2_loop`,
  `MinimalCaps/LoopVerification.v`'s composed-contract precedent) — see that
  plan's §0 for why this is judged more promising than either lever here,
  and its own phases/gates for the work involved.

---

## §5. Phase 4 — the whole-function decision

Two per-loop theorems do **not** compose into a whole-function theorem, and
`modpow_win_full` set the precedent that whole-function is the bar.

Whole-function `check_scalar` means both loops in one instruction list:
**64 resident cells × roughly 640 steps**. That is a substantially larger
cells×steps than either loop alone, and it is the one target in the entire corpus
where resident-chunk count is expected to be a first-order cost.

### Decide from Phase 3's numbers, not from this document

- **If loop 2 at N=32 lands comfortably** (say under ~200 s VC): attempt the
  whole function directly. No cost work needed.
- **If it is tight or misses**: the indicated lever, in this order —

  1. **Widen `chunk_gc` to drop consumed data cells.** `gc_heap`
     (`Verifier.v:307`) is currently `filter (fun c => negb (is_encodes_instr c))`.
     Widening the filter is a small, local change reusing infrastructure that
     already exists and is already proved sound (the ambient BI `iProp Σ` is
     affine, so dropping any chunk is sound; only COMPLETENESS is at risk).
     **Must be opt-in**: dropping a cell breaks completeness if the program reads
     it again. Correct for an ascending single-pass walk, wrong in general.
     Verify with a byte-identical census, exactly as `PLAN-chunk-gc.md` did.
  2. **Region chunks** (one `ptstomem 32` chunk per array instead of 32
     `ptstomem 1` chunks) — see §6 for why this is a LAST resort and what it
     would cost.

### GATE 4

`check_scalar_noninterferent` covering the whole function, axiom-clean, gate
green.

---

## §6. Region chunks — the idea, and why it is deliberately last

Recorded so a later session does not re-derive it, and does not start it early.

**The idea.** `ptstomem width` is already registered as
`MkPrecise [ty_xlenbits] [ty.bvec (width * byte)]` (`Sig.v:365`), so a
whole-region chunk `chunk_user (ptstomem 32) [base; v]` is already
*representable*. One chunk and one logic variable would replace 32 of each.

**The gap.** `try_consume_chunk_user_precise` (`Chunks.v:316`) matches the
predicate by `eq_dec` and the INPUT arguments by `env.eqb_hom Term_eqb` — purely
syntactic. So `ptstomem 32` at `base` cannot discharge the `ptstomem 1` at
`base+17` that `sep_contract_mem_read` (`Spec.v:439`) asks for. It needs an
offset-projection rule: compute `δ := a' − a` (must reduce to a literal, which it
does because `peval_bvadd` canonicalises to constant-headed form and CFGVer
unrolls), check `δ + w ≤ R`, emit `v' = vector_subrange (8δ) (8w) v`.

**Where it would live.** Core's `𝑯` is abstract, so this needs a new
`PredicateKit` hook — a sibling to `𝑯_precise` (`Predicates.v:82`), defaulting to
`None` exactly as `𝑯_precise` does at `Predicates.v:124`, with RiscvPmp answering
`Some` only for the `ptstomem R → ptstomem w` pair. General in mechanism, opt-in
in effect; nothing has to opt *out*. The Iris obligation is a borrow
(`interp p ⊢ interp q ∗ (interp q -∗ interp p)`), whose crux lemma
`ptstomem_bv_app` is already proved.

**Why it is last.** Blast radius is real: `try_consume_chunk_user_precise_spec`
is a list induction feeding the soundness chain, plus `heap_extractions`,
`consume_chunk`'s refinement, and `RefineCompat`. And the *evidence* for it is
indirect — see §7's first bullet.

**Before funding it, run the cheap probe.** Hold the program fixed and vary only
the number of resident chunks (K = 1 / 8 / 32), with all K cells projected from
ONE shared variable so `|Σ|` stays constant and only chunk count moves. Use the
`ZZByteCtr*` counter-exit base so driver (B) is absent. That reads off the
marginal cost per resident chunk per step directly. If it comes back like the
indexing result (≤7%), drop the idea.

---

## §7. Do NOT — refuted, do not re-derive

- **Do not index the symbolic heap** (gmap instead of the chunk list). MEASURED
  DEAD END at ≤7%, `PLAN-byte-memory.md` §10 and commit `450d1118`. The scan is
  not where the time goes: `SHeap Σ = list (Chunk Σ)` is indexed by the WORLD and
  has `Subst` via `subst_list` (`Chunks.v:237,241`), so every world extension
  transports the whole heap regardless of how it is indexed. (A) is a SIZE
  problem, not a LOOKUP problem.
- **Do not tune fuel for speed.** 4.4× the fuel = +0.04% allocation, every
  counter byte-identical.
- **Do not chase the symbolic base.** A concrete base is faster in absolute terms
  but its exponent is STEEPER (1.63 vs 1.48) — a shrinking constant-factor
  penalty, not a scaling driver.
- **Do not re-attempt the world-GC.** Structurally unprovable; `rexec_cfg_addr`
  as stated on `unquantify-gate` is FALSE, not merely unproven. See the
  `project-key-schedule-loop-scaling` memory note.
- **Do not pull `key_schedule_loop` into this plan.** It is the outlier, not the
  template — its array size IS its trip count, and it has a SECOND driver (the
  GHASH `mulx` 3^N term explosion) that `coalesce` does not cover.
  `PLAN-ksl64.md` §0 records the un-park condition; nothing here meets it.

---

## §8. Measurement hygiene — every one of these produced a wrong result once

- **Judge on user CPU and peak RSS, never wall clock.** One `PLAN-byte-memory.md`
  run recorded 70 698 s wall against 27.1 s user — a machine suspend. This box's
  ordinary run-to-run CPU spread is ~7%.
- **ONE heavy `Eval` per `coqc` process.** Several in one process contaminate
  each other badly; within-run growth ratios have flipped direction between runs.
- **A probe that fails to compile reports the imports-only `allocated_words`**,
  which reads as "this variant is free". Gate on `Finished transaction` appearing
  before believing any allocation figure.
- **`all: idtac "X"` prints exactly once regardless of goal count, including at
  zero goals.** Use `all: (let n := numgoals in idtac "count:" n)`.
- **`solve_vc. solve_symbase_fetch.` is not `solve_vc; solve_symbase_fetch`.**
  The period form runs the second tactic on the first goal only.
- **Never quote a growth exponent from one doubling, or from a series ending at
  N=8.** That error has been made twice in this project, two sessions apart.
