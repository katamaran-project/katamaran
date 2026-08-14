# key_schedule_loop2 cost drivers — heap size vs. term growth

Status: **Diagnostic record. Originally 2026-08-13; fully re-measured
2026-08-14 after `bop.mulx` landed (commit `3215b219`).** Not a phased plan —
a completed causal investigation. Lives in `diagnostics/`, not `plans/`.

**Follow-on finding, same day:** the surviving chunk-count cost is a heap
**SIZE** cost, not a lookup cost — `H × S`, paid by `subst_list` transporting
the whole heap across every world extension (mechanism already identified in
`plans/PLAN-byte-memory.md` §10, 2026-08-05). Established here by the
access-count series (0/1/2 data accesses per trip move the excess by 3.2%)
and by the fact that the declared cells' predicate index (`ptstomem 4`) is
never matched by ANY consume in the zero-access arm, yet they still carry 97%
of the excess. See "§Is the chunk cost SEARCHING or CARRYING?" — including a
retraction of the first, invalid argument for the same conclusion. Only
shrinking the declared set can fix it; cheaper lookups cannot.

**One-sentence finding (2026-08-14):** of the two independent axes this
experiment was built to separate — declared-chunk **usage** (1 vs. N
genuinely-touched memory cells) and the masking step's self-referential
**term growth** (`H := (H>>1) ^ mask(H)`) — the term-growth axis is now
**gone**, measuring 0.98–0.99× (i.e. the growing variant is marginally
*cheaper* than its flat control) where it measured 3.7–4.7× before
`bop.mulx`; **declared-chunk count is the sole remaining driver** and the
only source of superlinearity, at 2.72× for N-used-vs-1-used at N=16 and
still climbing.

> **Retraction notice.** The original 2026-08-13 conclusion — that term
> growth was the *dominant* axis and that reviving `select_last_k` was the
> most promising next step — is **superseded**; see
> "§Superseded: the original 2026-08-13 reading" at the bottom, which keeps
> the old numbers on the record. Term growth was real and was fixed, but by
> a different route (`bop.mulx`, not `select_last_k`), and `select_last_k`
> would not have touched the axis that actually remains.

---

## The experiment

All variants reuse `KeyScheduleLoop.v`'s committed 14-instruction body
(masking step + table store + backward branch). **This body is a 32-bit
stand-in for the true 64-bit Botan/GHASH masking step**, reusing
`Precompute.v`'s 32-bit step. That is the architecture-**natural** choice,
not a dodge: the 64-bit version targets a 64-bit processor and we verify on
RV32. (An earlier revision of this file framed the 32-bit choice as
"deliberately sidestepping the still-open `sltu`-on-secret-borrow-chain
gap" — that framing is withdrawn.) The residual caveat is one of per-step
**density**, not of recognition: a full GF(2^128) step on RV32 needs four
words per iteration, so the masking chain fires ~4× per trip plus carry
handling, multiplying the per-step term count without introducing a new
mechanism.

Two independent knobs, and as of 2026-08-14 **all six grid cells are
built** (the sixth was added specifically as a held-out test, below):

- **Chunk-usage axis**: `1-used` (table pointer never advances, `addi
  a3,a3,0`, all N iterations hit the same address) / `N-used` (pointer
  genuinely advances, `addi a3,a3,4`, N distinct addresses) / `N-declared-
  1-used` (N addresses declared in the precondition, but the pointer never
  advances, so N−1 of them are dead weight, never read or written).
- **Term-growth axis**: `growing-term` (`H`'s two reads are `andi a1,a0,1` /
  `srli a0,a0,1` — `H` feeds into its own previous value, as written) /
  `flat-term` (those two reads are rerouted to `A3` instead of `A0` — `H` is
  recomputed from a value that does not itself accumulate across
  iterations).

| short name | chunks used | chunks declared | term | file |
|---|---|---|---|---|
| 1-used + growing-term | 1 | 1 | growing | `ZZKslChunkSharedCommon.v` |
| N-used + growing-term | N | N | growing | `ZZKslChunkDistinctCommon.v` |
| 1-used + flat-term | 1 | 1 | flat | `ZZKslChunkSharedNoFbCommon.v` |
| N-used + flat-term | N | N | flat | `ZZKslNUsedFlatCommon.v` |
| N-declared-1-used + flat-term | 1 | N | flat | `ZZKslChunkPaddedCommon.v` |
| N-declared-1-used + growing-term | 1 | N | growing | `ZZKslPaddedGrowCommon.v` |

Each was measured at N=4/8/16 via **`allocated_words`** (OCaml's own GC
allocation counter — both wall-clock and OS-reported peak RSS gave
misleading numbers earlier in this investigation and were abandoned in
favor of this metric). Every run below gated on both `Finished transaction
… (successful)` lines appearing.

Determinism spot-checks on the 2026-08-14 rerun: the imports-only baseline
reproduced to **0.002%** (593,774,593 vs. 593,763,750 measured hours
earlier), and the `1-used+growing` row reproduced a prior session's figures
to **<0.0001%** at every N. The metric is behaving.

## Results (2026-08-14, post-`bop.mulx`)

`allocated_words`, minus the imports-only baseline **593,774,593**. Note
this baseline is 37% above the pre-`bop.mulx` one (434,833,198), because
~750 lines were added to `Bitvector.v`/`PartialEvaluation.v` — **do not mix
figures across the two baselines.**

| N | 1-used, growing | N-used, growing | 1-used, flat | N-used, flat | N-decl-1-used, flat | N-decl-1-used, growing |
|---|---|---|---|---|---|---|
| 4 | 2,050,677,204 | 2,636,150,058 | 2,071,752,785 | 2,662,041,673 | 2,332,817,765 | 2,310,967,799 |
| 8 | 2,752,082,041 | 4,698,843,108 | 2,794,838,905 | 4,770,279,073 | 3,783,276,413 | 3,736,522,913 |
| 16 | 4,158,691,427 | 11,310,144,251 | 4,240,899,486 | 11,528,010,680 | 8,253,199,842 | 8,150,780,260 |

**Doubling ratios** (N4→8, then N8→16):

| variant | N4→8 | N8→16 |
|---|---|---|
| 1-used, growing | 1.342 | 1.511 |
| 1-used, flat | 1.349 | 1.517 |
| N-decl-1-used, growing | 1.617 | 2.181 |
| N-decl-1-used, flat | 1.622 | 2.182 |
| N-used, growing | 1.783 | 2.407 |
| N-used, flat | 1.792 | 2.417 |

**Held-out linearity check** — fit `a+b·N` on N=4/8 only, predict N=16,
compare against the withheld measurement:

| variant | predicted N=16 | measured N=16 | error |
|---|---|---|---|
| 1-used, flat | 4,241,011,145 | 4,240,899,486 | **−0.003%** |
| 1-used, growing | 4,154,891,715 | 4,158,691,427 | **+0.09%** |
| N-decl-1-used, flat | 6,684,193,709 | 8,253,199,842 | +23.5% |
| N-decl-1-used, growing | 6,587,633,141 | 8,150,780,260 | +23.7% |
| N-used, growing | 8,824,229,208 | 11,310,144,251 | +28.2% |
| N-used, flat | 8,986,753,873 | 11,528,010,680 | +28.3% |

Both **1-chunk** rows are linear to within measurement noise, *whether or
not the term grows*. Every row that declares N chunks misses a linear fit
by 23–28%. The split falls exactly on the chunk axis and not at all on the
term axis.

## Reading the two axes apart (same N, one knob changed)

| axis isolated | N=4 | N=8 | N=16 |
|---|---|---|---|
| **term growth**, chunks pinned at 1 (`1-used,growing` / `1-used,flat`) | 0.990 | 0.985 | **0.981** |
| **term growth**, chunks pinned at N (`N-used,growing` / `N-used,flat`) | 0.990 | 0.985 | **0.981** |
| **term growth**, at N-decl-1-used (`…,growing` / `…,flat`) | 0.991 | 0.988 | **0.988** |
| **chunk usage**, term flat (`N-used,flat` / `1-used,flat`) | 1.285 | 1.707 | **2.718** |
| **chunk usage**, term growing (`N-used,growing` / `1-used,growing`) | 1.286 | 1.707 | **2.720** |
| declared-but-unused sub-effect, term flat (`N-decl` / `1-used`) | 1.126 | 1.354 | 1.946 |
| genuinely-used vs. merely-declared (`N-used` / `N-decl-1-used`) | 1.141 | 1.261 | 1.397 |

Three things to take from this table:

1. **The term-growth axis is not merely reduced, it is absent** — and its
   residual sign is *negative*: the self-referential variant costs ~1–2%
   LESS than its flat control, consistently at all three chunk settings and
   all three N. Do not over-read the 2%: the two variants differ in which
   register two instructions read, which is not a pure no-op, and a
   couple of percent is the scale at which such structural differences
   show up. The honest statement is "no measurable term-growth cost."
2. **The chunk-usage ratio is identical to three decimals whether the term
   grows or not** (2.718 vs. 2.720 at N=16). The two axes, which the
   original experiment found compounding multiplicatively, are now fully
   decoupled — which is exactly what "one axis went to zero" predicts.
3. **Merely declaring the cells accounts for most of the chunk penalty.**
   At N=16, declaring N cells and touching one costs 1.95× over declaring
   one; genuinely touching all N adds a further 1.40×.

### Held-out confirmation of the decoupling

Points 1–2 were read off the five cells the original experiment built. The
sixth cell (`N-declared-1-used + growing-term`, previously unbuilt) was
then added as a genuine held-out test: if the axes are decoupled, the
declared-but-unused surcharge measured on the *flat* side must reappear
unchanged on the *growing* side.

| N | surcharge, flat side (`CP`/`1-used,flat`) | surcharge, growing side (`PG`/`1-used,growing`) | agreement |
|---|---|---|---|
| 4 | 1.1260 | 1.1269 | 0.08% |
| 8 | 1.3537 | 1.3577 | 0.30% |
| 16 | 1.9461 | 1.9599 | 0.71% |

Confirmed. The prediction was not fitted to this cell and holds to under
1% at every N.

## The term-level mechanism, re-measured — and a correction

`bop.mulx` (`theories/Symbolic/PartialEvaluation.v`, `bvmulx_try` /
`bvmulx_mask_arg` / `bvmulx_shiftr1`) recognizes the GF(2) multiply-by-x
step and rewrites the whole masking chain to a single `mulx` node. Verified
directly on the real executor output: the masking step now reads
`term_mulx "v" [bv 0xe1000000]`.

`ZZTermSim2.v` re-measures the recurrence at the term level, on the shape
the executor actually builds — the six-node sign-extraction idiom dumped in
`ZZMulxDump.v` and pinned by `selftest_mulx_fires_real_shape` — ablated on
**one** axis: whether the recognizer can fire. `H>>1` fires; `H>>2` fails
`bvmulx_shiftr1`'s `bin s =? 1` guard with every other node of the
recurrence byte-identical.

| n | `H`'s term size, mulx fires | `H`'s term size, recognition blocked |
|---|---|---|
| 1 | 3 | 21 |
| 2 | 5 | 81 |
| 4 | 9 | 801 |
| 8 | 17 | 65,601 |
| 16 | 33 | 430,467,201 |
| 32 | 65 | — |

With the rule firing: exactly `2n+1` — one node per trip, the same linear
law `check_scalar` loop 1's once-referenced `z` accumulator obeys (see
`check-scalar-loop1-cost-drivers.md`), and no crossover through n=32.
Blocked: exactly `30·3^(n−1) − 9`.

**Correction to the earlier mechanism section (and a vindication).** The
base of that exponential is **3, not 2**. The original section reported
`2^n` (8/22/106/1786/458,746 = `7·2^n − 6`) from `ZZTermSim.v`, and on that
basis second-guessed a July 2026 session's report of a "3^N blowup" as
"likely a difference in exactly which part of the chain was modeled." That
July figure was right and this file's was wrong. Two modelling errors in
`ZZTermSim.v` caused it, both since documented in its own header:

- it used the **simple** two-node mask `negate (bvand H 1)` — two
  references to `H`, hence base 2 — rather than the six-node idiom clang
  actually emits, which references `H` three times, hence base 3;
- it omitted the outer `bvand mask R` against the GHASH constant
  `R = 0xE1000000` (what `lui a2,921600` loads) entirely. This matters
  beyond the constant: `bvmulx_arg` reaches the mask *only* through a
  `bvand mask r` split, so `ZZTermSim.v`'s shape cannot fire the recognizer
  at all. Re-run on 2026-08-14 it returns its original numbers unchanged,
  which is the expected result, not a `bop.mulx` failure.

`ZZTermSim.v` is kept for the record; `ZZTermSim2.v` supersedes it.

## Is the chunk cost SEARCHING or CARRYING? — carrying, `H × S`

Asked 2026-08-14, immediately after the above. Two independent ablations,
both on the flat-term body so the term axis is out of the picture.

**Stage split first** (free, from the runners' own two `Time` lines).
Seconds at N=16, flat-term rows:

| variant | `vm_compute` | `solve_vc` |
|---|---|---|
| 1 chunk | 15.97 | 4.38 |
| N declared, 1 used | 33.31 | 5.13 |
| N used | 41.84 | 9.58 |

Declaring N cells costs **×2.09 in `vm_compute` but only ×1.17 in
`solve_vc`** (+17.3 s vs. +0.75 s). `solve_vc` is essentially flat in N for
both 1-chunk and N-declared-1-used (4.4 / 5.1 / 5.0 at N=4/8/16) and grows
only when the pointer genuinely advances — that growth is a separate,
smaller mechanism, matching commit `404ac0d1`'s finding that the byte loop's
driver was the symbolic pointer compare. So the dominant penalty is paid
building the VC, in a stage that never decides anything about those chunks.

**Probe (a) — position of the accessed cell** (`ZZKslPadLastCommon.v`).
Same declared set, same order; only `A3` changes, from the first declared
cell to the last. `SHeap` is a list and `try_consume_chunk_user_precise`
scans it, so a scan cost must show a best/worst-case gap (this is
`ZZByteRev*.v`'s bracketing, reused):

| N | accessed first | accessed last | ratio |
|---|---|---|---|
| 4 | 2,332,817,765 | 2,333,493,902 | 1.0003 |
| 8 | 3,783,276,413 | 3,786,715,619 | 1.0009 |
| 16 | 8,253,199,842 | 8,268,587,100 | 1.0019 |

No gap. Position is irrelevant.

**Probe (b) — zero DATA accesses** (`ZZKslNoMemCommon.v`). The `STORE` is
*replaced* by a no-op `addi a1,a1,0`, so instruction count, branch offset
and fuel are unchanged — a genuine one-knob change. Both arms (1 declared /
N declared) live in one file so the control shares the body exactly.

> **Correction — this probe does NOT by itself rule out search cost, as
> first claimed.** Removing the `STORE` removes only the DATA access. Every
> one of the S steps still FETCHES an instruction, and the symbolic heap
> holds one `ptstoinstr` chunk per instruction (`cfgver-executor`), so each
> step still performs consumes that walk the heap — now carrying N extra
> chunks. Search cost alone therefore predicts `H × S` too, and the original
> "carrying, not searching" conclusion did not follow from this probe. What
> does establish it is the predicate argument plus the access-count series,
> both below. The measurements were fine; the inference was not.

| N | surcharge WITH an access (`CP`/`1-used,flat`) | surcharge with ZERO accesses (`NMN`/`NM1`) |
|---|---|---|
| 4 | 1.1260 | 1.1281 |
| 8 | 1.3537 | 1.3608 |
| 16 | 1.9461 | **1.9681** |

Unchanged — marginally *larger* with no access at all. Removing every
memory access moves the absolute figures by only 5.3–5.8%, so the whole
access machinery is a rounding error next to the cost of carrying the
declarations. The superlinearity is in carrying too: the no-access
N-declared arm misses a linear fit by **+24.0%** (vs. +23.5% with the
access), while the no-access 1-declared arm is linear to −0.00%.

**The excess is exactly quadratic.** Subtracting the 1-declared arm from
the N-declared arm isolates the cost attributable purely to declarations:

| | N=4 | N=8 | N=16 | per-doubling |
|---|---|---|---|---|
| no access | 250,158,200 | 952,801,210 | 3,889,739,984 | 3.81, **4.08** |
| with access | 261,064,980 | 988,437,508 | 4,012,300,356 | 3.79, **4.06** |

Quadrupling per doubling of N is `H × S` with `H ∝ N` and `S = 14N + c` —
the executor threads all H chunks through all S steps. A held-out `c·N²`
fit from N=8 alone predicts N=16 to within 2% on both arms. This is the
`heap_size × (α·S + β·S²)` cost law's *first* term with `heap_size` growing
in N, not a search cost.

**Probe (c) — the access-count series, and the predicate argument.** With
probe (b)'s inference retracted, two things do settle it.

*The series.* Vary data accesses per trip 0 → 1 → 2 at fixed H and fixed S,
each arm swapping exactly one no-op ALU instruction for one `STORE`
(`ZZKslNoMemCommon.v` / `ZZKslChunkPaddedCommon.v` /
`ZZKslTwoAccCommon.v`). The declared-chunk excess (N-declared minus
1-declared) barely moves:

| accesses/trip | N=4 | N=8 | N=16 |
|---|---|---|---|
| 0 | 250,158,200 | 952,801,210 | 3,889,739,984 |
| 1 | 261,064,980 | 988,437,508 | 4,012,300,356 |
| 2 | 261,535,848 | 990,842,642 | 4,023,371,305 |

Adding the first data lookup per trip adds **3.2%** to the excess at N=16
(122.6 M of 3,890 M); the second adds 0.3%. The surcharge ratio itself is
flat across the series (1.968 / 1.946 / 1.946 at N=16). So data lookups are
not what the declared cells cost.

(The 0→1 and 1→2 increments differ ~11×, which is expected rather than
noise: `produce_chunk` conses, so the first `STORE` leaves its cell at the
FRONT of the heap and the second trip's second `STORE` finds it
immediately. Read the marginal lookup cost off 0→1, not 1→2.)

*The predicate argument — this is the decisive one.* `gen_mem_pre_rel`
emits `chunk_user (ptstomem 4)` chunks (`GenContract.v`); the fetch consumes
`ptstoinstr` and register operations use `chunk_ptsreg` — different
predicate indices, and `try_consume_chunk_user_precise` rejects on the
predicate before touching arguments (`Chunks.v:316`). So in the zero-access
arm **no consume in the entire run ever candidate-matches the N declared
cells**: they are never unified against, never generate a formula, never
reach the solver. They still account for 97% of the excess. Lookup work
cannot be what they cost.

**Mechanism — already identified 2026-08-05, and this should have been read
first.** Commit `450d1118` / `plans/PLAN-byte-memory.md` §10 names the
carrier: `SHeap` is indexed by the WORLD and has `Subst` via `subst_list`
(`Chunks.v:237,241`), so **every world extension transports the whole heap,
re-substituting every chunk's terms**, and `produce_chunk` additionally
`peval_chunks`. That is proportional to heap SIZE and independent of
indexing — world extensions happen per step, giving `H × S` exactly. Its
verdict was already the right one: *"(A) is a SIZE problem, not a LOOKUP
problem: cut the number of resident chunks, do not index them."* The probes
here re-derive that conclusion for `key_schedule_loop2` and add the
predicate argument, but they did not discover it. (This is precisely the
failure mode this skill's "Read these before measuring anything" section
exists to prevent.)

**On the ≤7% figure — scope it correctly.** That number bounds LOOKUP cost:
it was obtained by bracketing best-case against worst-case *position of the
matching chunk* (`ZZByteRev*.v`). It is not, and was never claimed to be, a
bound on the size cost measured here — the original commit says so
explicitly. Do not cite it as "indexing was tried and the heap cost is
irreducible"; cite it as "making lookup O(1) is worth ≤7%, because lookup
is not the cost." Probe (a) above independently agrees, at 1.002×.

**Consequence for fix design.** Unchanged in direction, now with a named
carrier: indices, sorting and better key matching do not touch this driver,
because the cost is paid transporting the heap across world extensions, not
finding things in it. The only lever is shrinking the **declared set** —
`plans/PLAN-loop-invariant.md`'s per-iteration contract by construction, or
region chunks. Since the cost is `H × S`, the win scales directly with how
few cells the invariant has to name.

## What this means

`KeyScheduleLoop.v` sits at `N-used + growing-term`. Post-`bop.mulx` only
one of those two words still costs anything:

- **Term growth: closed.** Not a constant-factor improvement but an
  exponent change — `3^n` → `2n+1` at the term level, and no measurable
  end-to-end cost at any N tested. This is the mechanism that made the
  file's own body expensive, and it is gone.
- **Chunk usage: the sole remaining driver, and still superlinear.** 2.72×
  at N=16 for N-used vs. 1-used, missing a linear fit by 28%, with the
  ratio still climbing (1.29 → 1.71 → 2.72). Roughly two-thirds of it
  (1.95× of the 2.72×) comes from merely *declaring* the cells, before any
  are touched — i.e. from `gen_contract_rel` asserting the whole
  `mem_specs` list up front for the entire run, per the
  declared-chunk-count mechanism catalogued in `cfgver-scaling-
  diagnostics`.

That split determines the next lever, and it is **not** `select_last_k`
(which addressed term growth — already solved, by another route). It is the
chunk axis: `plans/PLAN-loop-invariant.md`'s per-iteration contract, which
mentions only the O(1) resource one iteration touches, or region chunks.
The declared-vs-used breakdown above is a useful constraint on that design:
since ~two-thirds of the penalty is incurred by *declaration* alone, a fix
that keeps declaring N cells while touching them more cheaply captures at
most the remaining ~1.40×. The win is in not declaring them — and per the
search-vs-carry section above, that is now measured rather than inferred:
the penalty is `H × S` carrying cost, unchanged by removing every memory
access and unaffected by where the touched cell sits, so only shrinking `H`
moves it.

Amdahl caveat, per this skill's own checklist: with the term axis at 1.00×,
the chunk axis is essentially 100% of the N-dependent cost, so a complete
fix to it is not bounded by some other mechanism taking over — but nothing
here measures what the residual per-step density costs at the ~4×
instruction count a real GF(2^128) step on RV32 would need.

## Files (throwaway, not in `_CoqProject`)

`ZZKslBaseline.v` (baseline) ·
`ZZKslChunkSharedCommon.v` + `ZZKslCS_N{4,8,16}.v` (1-used+growing) ·
`ZZKslChunkDistinctCommon.v` + `ZZKslCD_N{4,8,16}.v` (N-used+growing) ·
`ZZKslChunkSharedNoFbCommon.v` + `ZZKslCSNF_N{4,8,16}.v` (1-used+flat) ·
`ZZKslNUsedFlatCommon.v` + `ZZKslNUF_N{4,8,16}.v` (N-used+flat) ·
`ZZKslChunkPaddedCommon.v` + `ZZKslCP_N{4,8,16}.v` (N-declared-1-used+flat) ·
`ZZKslPaddedGrowCommon.v` + `ZZKslPG_N{4,8,16}.v` (N-declared-1-used+growing).

Search-vs-size probes (each with 1-declared and N-declared arms in one body,
so the surcharge is read within a single instruction sequence):
`ZZKslPadLastCommon.v` + `ZZKslPL_N{4,8,16}.v` (accessed cell = LAST declared) ·
`ZZKslNoMemCommon.v` + `ZZKslNM1_N{4,8,16}.v` / `ZZKslNMN_N{4,8,16}.v`
(0 data accesses per trip) ·
`ZZKslTwoAccCommon.v` + `ZZKslTA1_N{4,8,16}.v` / `ZZKslTAN_N{4,8,16}.v`
(2 data accesses per trip; the 1-access arm is `ZZKslChunkPadded`/`CSNF`).

**Gate on `Error` as well as on `Finished transaction`.** A first run of the
2-access arm was launched with a `cd` that did not reach the backgrounded
subshell; every `coqc` failed with "Can't find file" and each reported
`allocated_words: 1447863` — i.e. a failed variant reads as *nearly free*,
exactly the trap in this skill's checklist.

```
coqc -w none -Q case_study/RiscvPmp Katamaran.RiscvPmp -R theories Katamaran <Common>.v
OCAMLRUNPARAM='v=0x400' coqc -w none -Q case_study/RiscvPmp Katamaran.RiscvPmp \
  -R theories Katamaran <Runner>.v 2>&1 | grep allocated_words
```

Subtract `ZZKslBaseline.v`'s figure from every runner before comparing, and
run them one at a time (one heavy proof per `coqc` process). Post-`mulx`
these are cheap: the most expensive cell (`N-used+growing` at N=16) is ~39 s
of `vm_compute`, where pre-`mulx` it was killed after 8 minutes without
finishing.

Also: `ZZTermSim2.v` (the real-shape term simulation backing the mechanism
section) and `ZZTermSim.v` (its superseded predecessor).

**Not done:**

1. N=32 and beyond on the chunk axis — every N-chunk row is still climbing
   at N=16 and no fit here pins its exponent. Worth having before
   `PLAN-loop-invariant.md` claims a projected win at the N that matters.
2. The same term-simulation check applied to `br_divrem`'s loop (muladd) —
   a bit-serial division algorithm plausibly updates its state from
   multiple self-references per step. Structurally similar to `H`, still
   untested, and now cheap to test with `ZZTermSim2.v` as the template.
   Note `PLAN-muladd-full.md` Phase 3 is blocked on that loop's cost.

---

## Superseded: the original 2026-08-13 reading

Kept per this project's retraction discipline — a reader who remembers
these figures needs to find out what happened to them. **The measurements
below are real and were correctly taken; it is the conclusion drawn from
them that no longer holds, and they are on a different (pre-`bop.mulx`)
baseline of 434,833,198 — never requote them alongside the current
table.**

> `allocated_words`, minus the then-current imports-only baseline
> (434,833,198):
>
> | N | 1-used, growing | N-used, growing | 1-used, flat | N-used, flat | N-decl-1-used, flat |
> |---|---|---|---|---|---|
> | 4 | 2,136,783,054 | 2,775,733,250 | 2,090,805,329 | 2,696,079,703 | 2,354,454,405 |
> | 8 | 10,480,969,207 | 23,087,289,792 | 2,837,247,223 | 4,914,660,883 | 3,839,101,444 |
> | 16 | not run | killed, >8 min, never finished | 4,330,048,822 | 12,219,708,553 | 8,402,593,577 |
>
> Axis-isolated readings at N=8: term growth 3.69× (chunks pinned at 1) and
> 4.70× (pinned at N); chunk usage 1.73× (term flat) and 2.20× (term
> growing); declared-but-unused 1.35×.
>
> Conclusion at the time: **term growth is the dominant axis**, the two
> axes compound (`2.20 × 4.70 ≈ 10.3`), and reviving `select_last_k` from
> commit `a13da1b3` was "the single highest-value next step."

**What specifically changed, and what did not.**

- *Still true:* term growth was genuinely a dominant driver at that time,
  and the mechanism (a register embedded twice into its own next value,
  duplicating its whole prior tree because Coq terms are trees, not DAGs)
  was correctly identified. It was worth fixing, and fixing it is what
  produced the current numbers.
- *Superseded:* the axis magnitudes. Term growth went 3.7–4.7× → 0.98×;
  the chunk axis, unchanged in mechanism, is now the whole story. The
  compounding observation is void because one factor is 1.
- *Superseded:* "revive `select_last_k`" as the next step. The wall it
  targeted was removed by `bop.mulx` instead — a different rule, landed
  with a closed `Qed` soundness chain and two recognizer clauses (the
  second one required precisely because, as documented above, the real
  compiled shape is not the simple one `select_last_k`-era work and
  `ZZTermSim.v` both assumed). `select_last_k` would not touch the chunk
  axis that remains, so it should not be revived for this file.
- *Corrected:* the `2^n` term-size law and the associated doubt cast on the
  July 2026 "3^N" figure. See the mechanism section above; the real shape
  is base 3.
- *Withdrawn:* the framing of the 32-bit masking step as sidestepping the
  `sltu`-on-secret-borrow gap. On RV32 a 32-bit step is the natural choice.

The old flat-term rows also should not be compared against current growing
rows: `bop.mulx` fires on the flat variants too (both masking reads are the
same register, `A3`, so the same-operand check passes), it just has no
accumulated term to collapse there. Re-measured on 2026-08-14 they moved by
only −1% to −6%, which is why they remain usable as controls — but only in
their re-measured form, in the current table.
