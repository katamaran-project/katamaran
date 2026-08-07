# PLAN-check-scalar-full — BearSSL `check_scalar` to a whole-function end theorem

Status: **DRAFT / HANDOFF, written 2026-08-07.** Nothing in this plan has been
started. Phase 1's subject exists as uncommitted work in the tree (see §2).

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
| pointer-compare exponent (driver B) | **rule written, one lemma open** | §2 below |

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
| §2 — `try_bvadd_cancel_spec` | **Sonnet**, high effort | Dependent `Equations` (`funelim`), `Term_eqb_spec`, RelVal case analysis, `⊣⊢` in both directions — and `Solver.v` cannot be built with `rocq_compile_file`, so it is preamble mode throughout. The hardest single item here |
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

---

## §4. Phase 3 — loop 2 standalone: COMPILE AND MEASURE

Loop 2 as a real loop with memory has **never been compiled**. This phase is a
measurement, not a proof effort.

### What is new relative to loop 1

- **64 resident cells**, not 32 — both `k` (secret) and `P256_N` (public, pinned)
  are 32 bytes.
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

Projection for calibration only, from `PLAN-byte-memory.md` §10: ~165 s of
`vm_compute` at N=32 assuming both driver (B) and driver (C) fixes. Treat a
result within 2× of that as success.

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
