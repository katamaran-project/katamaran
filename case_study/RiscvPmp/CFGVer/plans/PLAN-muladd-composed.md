# PLAN-muladd-composed — `br_i31_muladd_small` whole-function, by CUTS and LOOP INVARIANTS

Status: **Phase 1 in progress.** Started 2026-09-08.

Successor to `PLAN-muladd-full.md`, whose Phase 3 is BLOCKED and stays blocked:
that plan verifies the function *flat*, and the flat arm does not fit in memory
(`diagnostics/muladd-full-cost-drivers.md`: peak RSS ~linear in prefix length,
extrapolating to ~11.5 GB on a 14 GB box; the wall is FOOTPRINT, not throughput,
so none of that plan's throughput levers can reach it). This plan does not
attempt to make the flat VC cheaper. It never builds one.

Audience: a later session executing one phase at a time. Each phase ends in an
explicit GATE — reach it, report, commit, stop.

---

## §0. The bet, in five lines

A cut resets term duplication (the 215,636-char register term of
`muladd-full-cost-drivers.md` §3.2 is built *within* one straight-line run) and
caps footprint at one segment's worth, because each segment is a separate
`Lemma`/`Qed` whose heap is reclaimed. A loop invariant additionally removes the
trip count from the executor entirely. Both mechanisms already work on this very
program (`ZZSegTrimP`, a mid-program muladd cut, 339 M words / 15 s) and on loops
(`PaddedLoopResult`, a sub-table loop cut). Nothing new is needed except the
segments themselves and the last mile (§4).

> **Written before the address-space finding below.** `ZZSegTrimP`'s goal turns
> out to be vacuous (see RESULTS), so it evidences that a cut is CHEAP, not that
> it proves anything. `PaddedLoopResult` is unaffected and remains a real
> gate-checked result.

Why now and not in the 2026-09-04 attempt: composition got **15.3× cheaper per
cut** on 2026-09-05 (`diagnostics/composition-payoff.md` ADDENDUM: 108 M → 7.1 M
marginal, break-even ~71 → ~4.65 trips per cut) when the solver learned to refute
branches against the path condition. "Cut sparingly" is retracted.

## §1. The segment map

From the C source (`bearssl.org/gitweb`, commit `79c060e`, files `i31_muladd.c`,
`i32_div32.c`, `i31_add.c`, `i31_sub.c`, `inner.h`) cross-referenced against the
282-instruction listing in `Example/ZZMuladdFullN2.v`. Live path at the pinned
public `m[0] = x[0] = 63` ⇒ `mlen = 2`, `mblr = 31`.

| # | idx | byte | C construct | kind |
|---|---|---|---|---|
| A | 0–3 | 0–12 | prologue; `if (m_bitlen==0)`, `if (m_bitlen<=31)` — both leaked by design | straight |
| B | 55–69 | 220–276 | `mlen`, `mblr`, `hi = x[mlen]`, the `if (mblr==0)` test | straight |
| C | 71–83 | 284–332 | else-branch: `a0` extraction, memmove setup | straight |
| **D** | **84–89** | **336–356** | memmove word loop | **loop** |
| E | 90–106 | 360–424 | `x[1]=z`, `a1`, `b0`, `j` to the division | straight |
| F | 123–134 | 492–536 | `br_divrem` prologue: `q=0`, `ch=EQ(hi,d)`, `hi=MUX(ch,0,hi)` | straight |
| **G** | **135–161** | **540–644** | `br_divrem` k-loop, 27 instrs, **31 trips** | **loop** |
| H | 162–189 | 648–756 | divrem epilogue; `q = MUX(EQ(a0,b0),0x7FFFFFFF,…)`; limb-loop guard | straight |
| **I** | **190–218** | **760–872** | limb multiply-accumulate, 29 instrs, `mlen` trips | **loop** |
| J | 219–236 | 876–944 | `over`/`under`; `br_i31_add` prologue (`m=(a[0]+63)>>5`) | straight |
| **K** | **237–249** | **948–996** | `br_i31_add` word loop | **loop** |
| L | 250–263 | 1000–1052 | `br_i31_sub` prologue | straight |
| **M** | **264–276** | **1056–1104** | `br_i31_sub` word loop | **loop** |
| N | 277–281 | 1108–1124 | epilogue; falls out at 1128 | straight |

Dead, never visited, provably infeasible against the pinned public bitlen:
idx 4–54 (the `m_bitlen<=31` small-modulus path, with its OWN inlined `br_divrem`
copy at head idx 16 and the shared `ret` at idx 54) and idx 107–122 (the
`mblr==0` arm of the `if`, with its own memmove loop at head idx 113).

Nine straight-line cuts, five loop invariants, fourteen segment contracts. Every
cut lands on a C function or loop boundary.

## §2. Why the loops are cuttable at all

`secret-data-walls` is the standing limit: a loop whose **trip count** is secret
cannot be cut this way, because the guard is a `formula_relop` and that is `False`
on `NonSyncVal`. Checked against the C for each of the five:

| loop | bound | public? |
|---|---|---|
| D, memmove | `mlen - 1` | yes — from `m[0]`, leaked by design |
| G, `br_divrem` | `k = 31 … 1`, a literal | yes |
| I, limb | `u = 1 … mlen` | yes |
| K, `br_i31_add` | `u < (a[0]+63)>>5` | yes — `a[0]` pinned public |
| M, `br_i31_sub` | same | yes |

All five bounds are public; every secret in this function (`x[]`, `z`, and
everything derived: `a0`, `a1`, `hi`, `lo`, `q`, `cc`, `tb`, `over`, `under`)
flows as a VALUE only. That is exactly the property the invariants must carry,
and it is why this function is cuttable where a secret-trip-count loop would not
be.

**Consequence, taken up as of this plan:** `PLAN-muladd-full.md`'s **deviation 3
is reverted**. The trip count never reaches the symbolic executor, so 31 trips
cost what 2 cost, and the two patched immediates (`li A4,3` at idx 13, `li T4,3`
at idx 132) go back to `32`. The verified instruction list is now exactly what
clang emitted. Deviations 1 (the `opaque()` hardening) and 2 (the word-copy
memmove) remain and remain disclosed.

## §3. The invariant shape, and the one lesson that must not be re-learnt

`ZZSeg2P` (2026-09-04): a cut assertion that havocs uniformly makes the VC
**`False`**, because the segment's own loads are addressed from values the caller
pinned. The rule is: **an invariant carries every public/pinned fact the segment
depends on, and nothing else.**

For the loop bodies that means, per register: `PVConst` where a *branch* or an
*address* needs the literal, public-`PVExist` where only publicness is preserved
and used, secret-`PVExist` otherwise. Worked example, loop G (registers read off
the listing, meanings from `i32_div32.c`):

| reg | C | in the invariant |
|---|---|---|
| T4 | `k`, the counter | `term_var "k"`, public, `bv.bin k = n+1` |
| T5 | the literal `1` in `bltu T5,T4` | `PVConst 1` — the guard must be decidable |
| T6 | `j = 32-k` | public `PVExist` — a shift amount; publicness is all that is used |
| T0 | `d` = `b0`, from `m[]` | public `PVExist` |
| T1 | `q` | secret `PVExist` |
| T2 | `hi` | secret `PVExist` |
| T3 | `lo` | secret `PVExist` |
| S0–S3 | `w`, `ctl`, `hi2`, `lo2` | secret `PVExist` (write-before-read) |

Note T6 does NOT need `32 - k`: nothing branches on it. Deriving the weakest
invariant from the C, rather than the strongest one the code happens to satisfy,
is what keeps each body VC small.

## §4. Phases

### Phase 1 — the `br_divrem` body (SPIKE)

Hardest single VC and the biggest payoff (31 trips). Un-patch the two
immediates; build `ZZMladCommon.v` (instruction list + specs, shared) and a body
contract for segment G at a symbolic counter with a **trimmed table** (15-entry
sub-table style of `ZZSegTrimP`).

GATE 1: a real `Qed` on the G body contract, plus its measured cost. If the
weakest invariant of §3 gives a bare `False`, report WHICH fact the segment
needed — do not strengthen by guessing.

### Phase 2 — the remaining four loop bodies + their exit contracts

D, I, K, M, same recipe. Each loop needs a body contract (head→head) and an exit
contract (head→ the instruction after the loop).

GATE 2: ten `Qed`s (5 loops × body+exit), each with its cost recorded.

### Phase 3 — the nine straight-line segments

A, B, C, E, F, H, J, L, N. B already exists as `ZZSegTrimP`.

GATE 3: nine `Qed`s. Any segment that yields `False` is a missing pinned fact,
diagnosed the `ZZSegTrimD` way (dump the goal, 11 s) — not by widening the pre.

### Phase 4 — compose

`myWP2_loop_induction` per loop, `myWP2_loop_bind`/`_join` along the chain,
`itable_faith_of_segment` per segment for the sub-tables. Result: a single
`myWP2_loop muladdExit` from the entry invariant.

GATE 4: `muladd_full_loop : muladdInv -∗ myWP2_loop muladdExit`, axiom-clean.

### Phase 5 — the last mile (NEW MACHINERY)

No composed proof in this tree has ever become a leakage theorem: `swap_composed`,
`cd_loop`, `loopA`, `pl_loop` all stop at `myWP2_loop`. But
`exitCond_WP2_loop exitCond` is *definitionally* `myWP2_loop (∃ v, pc ↦ᵣ SyncVal v
∗ ⌜exitCond v⌝)` (`Adequacy.v:1140`), which is exactly what `cfg_instrs_verified`
produces from a single contract (`EndToEnd.v:115`). So the last mile is a variant
of `cfg_instrs_verified` that takes a *composed* `myWP2_loop` fact in place of the
`ValidCFGVerifierContract` + `sound_scfg_verification_condition_myWP2` step,
keeping its register/privilege/`ImplPre` plumbing; then the existing
`_with_mem` bridge (this program has data memory) to `muladd_noninterferent_param`.

GATE 5: `muladd_noninterferent_param` axiom-clean, on the gate's list, gate green.

### Phase 6 — promote

`Example/BearSSLMuladdFull.v` + `…FullResult.v`, `_CoqProject`, `Results.v`,
allowlist. Header comment carries the two remaining deviations and the segment
map.

## §5. Do NOT

- **Do not build a flat whole-function VC to "check" a segment.** It does not
  fit in memory; that is the finding this plan starts from.
- **Do not widen an invariant to fix a `False`.** Dump the goal and find the
  missing pinned fact (§3).
- **Do not re-investigate store-address disambiguation (4.8%) or `MUL`/`MULHU`
  (8.2%)** — eliminated, `muladd-full-cost-drivers.md` §3.3.
- **Do not use dense per-instruction havoc.** It was the flat arm's workaround
  and it trades term duplication for a quadratic `|Σ|`; a cut removes the
  duplication without minting the variables.
- **Do not raise `mlen` before the mlen=2 chain closes.**

## §6. Related

- `PLAN-muladd-full.md` — Phases 0–2 (source, hardening, translation) are the
  input to this plan and are NOT redone. Its Phase 3 stays blocked by design.
- `diagnostics/muladd-full-cost-drivers.md` — why flat does not fit.
- `diagnostics/composition-payoff.md` ADDENDUM 2026-09-05 — why cuts are cheap now.
- `PLAN-loop-invariant.md` U9/U12 — the loop cut and `myWP2_loop_induction`.
- `Example/PaddedLoop.v` / `…Result.v` — sub-table loop cut, the closest template.
- `Example/ZZSegTrimP.v` — the working mid-program muladd cut (segment B).

---

# RESULTS 2026-09-08 — Phase 1 PASSES; Phase 2 blocked by TWO findings, one of them fatal to the plan as written

## Phase 1 (segment G, `br_divrem`) — GATE 1 PASSED

Three contracts, all closing on the FIRST attempt, at the **real 31 trips**
(the trip count never reaches the executor, so §2's revert of deviation 3 costs
nothing):

| probe | contract | allocated | net of baseline | wall | peak RSS |
|---|---|---|---:|---:|---:|
| `ZZMladDvBody.v` | body, `asn_no_post` | 856.390 M | 214.4 M | 14.4 s | 4.28 GB |
| `ZZMladDvFinal.v` | exit (guard negated) | 856.439 M | 214.5 M | 14.9 s | 4.28 GB |
| `ZZMladDvBodyP.v` | body, invariant-preserving post | 864.624 M | 222.7 M | 12.7 s | 4.29 GB |

Baseline `ZZMladBase.v` (imports only) = **641,953,144** words. Against the flat
whole function, which is killed at ~11.5 GB after >14 min without a `Qed`.

**Non-vacuity was tested, not assumed** (`ZZMladDvBodyBad.v`): un-pinning T5 —
the latch's literal `1` — makes the VC FAIL (`No applicable tactic`) at 10.68 G
words / 64.8 s, i.e. **12.5x the cost of the closing arm and no `Qed`**. So the
pin is load-bearing and `solve_vc` is doing real work. Reproducibility: the 1b
arm re-run after an unrelated tree rebuild gave 864,624,308 vs 864,610,421,
**+0.0016%**.

The publicness-propagation worry in §3 did NOT materialise: the post
re-establishes `secLeak` for both `k-1` and `j+1` with no extra machinery.

## Phase 2 — the four remaining loop bodies FAIL, and the sliding-footprint
## pattern is only part of the reason

`ZZMladAddBody.v` (K), `ZZMladSubBody.v` (M), `ZZMladMvBody.v` (D),
`ZZMladLimbBody.v` (I), each `No applicable tactic`:

| probe | allocated | wall | peak RSS |
|---|---:|---:|---:|
| K, `br_i31_add` | 4.823 G | 21.4 s | 4.94 GB |
| M, `br_i31_sub` | 4.815 G | 19.2 s | 4.94 GB |
| D, memmove | 1.805 G | 13.1 s | 4.35 GB |
| I, limb accumulate | 21.242 G | 90.6 s | 7.90 GB |

(Costs of FAILING runs: upper bounds only — a `solve_vc` that cannot close does
extra work.)

**Diagnosed cause, from `cfgver-solve-vc`:** `sep_contract_mem_read` (Spec.v:439)
demands TWO bounds per data access — `minAddr <= unsigned paddr` and
`unsigned paddr + bytes <= maxAddr`. The sliding-footprint invariants name the
data pointers as FREE logic variables (`ap`/`bp`/`xp`/`mp`/`dp`) with no bounds
at all, so those obligations are unprovable. The fix is to carry both bound
formulas per cell address in each invariant; `relval_fetch_upper_bare`
(Contracts.v:392) is shaped to consume exactly that plus the `secLeakvar` these
invariants already have. **Not attempted** — it is downstream of the next
finding.

## THE FATAL FINDING — the whole function does not FIT in the address space

`Base.v:79-81`: `minAddr = 0`, `lenAddr = 2^10 = 1024`, `maxAddr = 1024`.

- `gen_contract_rel` (GenContract.v) puts `unsigned p + bound <= lenAddr` in
  every precondition.
- `cfg_instrs_verified` (EndToEnd.v:115) requires
  `init_addr + 4 * length instrs < lenAddr` to wire anything end-to-end.

muladd whole-function is **282 instructions = 1128 bytes** of code, with
`x[]`/`m[]`/stack at offsets 1128..1168, so it passes **bound = 1168**. Since
`unsigned p >= 0`, the precondition `unsigned p + 1168 <= 1024` is
**UNSATISFIABLE**, and `Hleninstrs` is false for every `init_addr`. For scale,
every landed example passes a bound <= 204 (`modpow_win_full`: 176).

**Consequences, stated plainly:**

1. **Whole-function muladd cannot be wired end-to-end at `lenAddr = 2^10`, at
   any cost.** Every cost investigation stopped before the wiring, which is why
   this was never hit.
2. **Existing whole-function muladd statements are VACUOUS** — a false
   hypothesis: `Example/ZZMuladdFullN2.v`, `ZZMuladdFullN4.v`, and the
   2026-09-04 `ZZSegTrimP`/`ZZSeg2P` result that `PLAN-muladd-full.md` records
   as *"RESOLVED — the mid-program cut VERIFIES"*. **That headline needs
   correcting: the cut closed a vacuous goal.** So do Phase 1's three `Qed`s
   above. The proofs are real work (see the non-vacuity probe — the solver does
   NOT exploit the contradiction) but they prove nothing about executions.
3. Every `allocated_words` figure in `diagnostics/muladd-full-cost-drivers.md`
   is a measurement of symbolic execution under an unsatisfiable precondition.
   Since the solver demonstrably does not exploit the contradiction, they are
   probably still representative — but that is an argument, not a measurement.

## What raising `lenAddr` actually costs (checked, not assumed)

Owner decision 2026-09-08: raise it to `2^12`. Two things a one-line change does
NOT cover:

- **20 HARDCODED `1024` literals** must move with it: `CFGVer/Contracts.v` (16,
  the `relval_fetch_*` / fetch-bound lemma family that IS `solve_symbase_fetch`),
  `CFGVer/Adequacy.v` (3, incl. an explicit `change (2^10)%N with 1024%N`),
  `CFGVer/EndToEnd.v` (1). Mechanical, but they are the tactic engine.
  `theories/Symbolic/Solver.v` mentions `lenAddr`/`maxAddr` in COMMENTS ONLY, so
  `theories/` neither changes nor rebuilds.
- **`Base.v:92`: `liveAddrs := bv.seqBv (bv.of_N minAddr) lenAddr`.** Raising
  `lenAddr` QUADRUPLES the live-address list the Iris memory model iterates
  (`interp_mem`, `gen_public_addrs`, `big_sepL` over `liveAddrs`). Unmeasured;
  measure one small example at 2^10 vs 2^12 before committing the tree.

## NOT DONE, and why

The change was NOT made. This checkout is SHARED with another live session,
working on branch `issue/mul-leaks-args` (`822c33a7` "leakage model gains
LeakMul -- multiplication leaks both operands", `ea335628` "mul_public"). A
tree-wide `Base.v` edit plus full rebuild would break their build and confound
both sets of measurements.

**That branch also bears directly on this plan.** If `MUL` leaks BOTH operands,
segment I's `MUL31(mw, q)` leaks the SECRET `q`, and the limb loop is
unverifiable on that model — so `ZZMladLimbBody`'s failure above may have a
second, independent cause, and the attribution to missing address bounds is
UNCERTAIN for that one probe (K/M/D have no multiply and are unaffected).
Re-check segment I only after the LeakMul model settles.

## Files

Committed nothing. Probes (untracked, in `Example/`): `ZZMladCommon.v` (the
shared instruction list with deviation 3 reverted — the only artifact worth
keeping), `ZZMladBase.v`, `ZZMladDv{Body,Final,BodyP,BodyBad,Fit}.v`,
`ZZMlad{Add,Sub,Limb,Mv}{Body,Final}.v`.

---

# RESULTS 2026-09-09 — segment G is NON-VACUOUS; Phase 5's machinery EXISTS

## Segment G re-run at `lenAddr = 2^12` — the precondition is now satisfiable

Three `Qed`s, and this time they mean something (`bound = 1168 <= 4096`, and
`unsigned p >= 0` leaves `p` in `[0, 2928]`).

| | vacuous (2^10) | non-vacuous (2^12) | delta |
|---|---:|---:|---:|
| body (`ZZMladDvBody`) | 856,390,131 | 856,403,082 | **+0.0015%** |
| exit (`ZZMladDvFinal`) | 856,439,435 | 856,451,554 | +0.0014% |
| invariant post (`ZZMladDvBodyP`) | 864,610,421 | 864,621,715 | +0.0013% |
| control (`ZZMladDvBodyBad`, T5 un-pinned) | 10.68 G, FAILS | 10.67 G, **still FAILS** | — |

**`allocated_words` is identical to four decimal places.** So the solver never
exploited the contradictory precondition: it built and discharged exactly the
same VC, and only the truth of the hypothesis changed.

Consequences:
- The Phase 1 cost model transfers unchanged; composed 4.3 GB vs flat 11.5 GB
  stands.
- The earlier caveat that `diagnostics/muladd-full-cost-drivers.md`'s numbers
  are "probably still representative — but that is an argument, not a
  measurement" is DISCHARGED. It is now a measurement.
- Ignore the wall-clock drop (14.4 s -> 11.0 s): wall is contended on this box
  and the vacuous run competed with another session. `allocated_words` is the
  deterministic metric and it is flat.

## Phase 5 — the last mile WORKS (spike, `Example/ZZPhase5.v`, untracked)

The plan called this NEW MACHINERY and the highest-risk item. It is done, and
it was smaller than expected.

**The translation lemma is not needed.** `exitCond_WP2_loop exitCond` is
*definitionally* `myWP2_loop (∃ v, pc ↦ᵣ SyncVal v ∗ ⌜exitCond v⌝)`
(`Adequacy.v:1140`), and `swap_composed` already concludes exactly that shape
(`swapExit`). So the two are the same proposition and no bridge between them
has to be proved.

What DID have to be written is `cfg_instrs_verified_composed`: `cfg_instrs_
verified` with the one `sound_scfg_verification_condition_myWP2` step replaced
by the caller's composed fact, keeping the register destructuring, the four
`read_register` rewrites, `regPstsTo_sync_is_nonsync` and the `ImplPre`
plumbing — which is the part a composed proof otherwise has no route to, and
the actual reason `swap_composed`, `cd_loop`, `loopA` and `pl_loop` all stop at
`myWP2_loop`.

`swap_composed_endToEnd` then drives the real two-segment `swap_composed`
through it to the same conclusion `cfg_instrs_verified` produces.

Both are **axiom-clean**: `Print Assumptions` gives `pure_decode` and
`mmioenv` only — the two the gate whitelists. Zero `Admitted`.

**The one remaining gap, stated precisely:** `swap_composed_endToEnd` takes
`ImplPre` as a HYPOTHESIS, exactly as `cfg_instrs_verified` does. So it is not
yet a closed leakage theorem for swap. For GENERATED contracts `gen_implpre`
supplies that hypothesis; `swapA` is hand-written over a bespoke `swapCtx`, so
there is no generator to ask and one would have to be built by hand. This is
instantiation, not new machinery. muladd's segments would be generated, so
this gap is not expected to recur there — but that is a prediction, not a
measurement, and it should be checked before relying on it.

## Where that leaves the muladd plan

Phase 1 (segment G) and Phase 5 (the last mile) are the two that were in
doubt. Both now hold. What is left is the bulk, and it is ordinary work except
for one model question:

- Phase 2: four loop bodies still `No applicable tactic`; the diagnosed fix
  (carry `minAddr <= unsigned ap` and `unsigned ap + bytes <= maxAddr` per cell)
  is UNATTEMPTED and UNCONFIRMED — the `ZZMladAddDump` diagnostic has still
  never run.
- Segment I additionally risks being impossible under `LeakMul` (its
  `MUL31(mw, q)` has a SECRET `q`). That is a model question, not a proof one.
- Phases 3, 4, 6: nine straight-line segments, composition, promotion.

---

# RESULTS 2026-09-09 (later) — PHASE 2 COMPLETE; Phase 3 is 3/9

Gate PASSED first (build clean, no holes, 18 end theorems axiom-clean), so all
of the below sits on a validated tree.

## Phase 2 — ALL TEN loop contracts verify

The diagnosed fix was right, and it was HALF of what the earlier note said.
`sep_contract_mem_read` wants two bounds per access, but only the UPPER one was
missing: `minAddr <= unsigned paddr` is discharged unconditionally by
`relval_fetch_lower` — which works only because `minAddr = 0`, one more place
that assumption is load-bearing (see PLAN-address-space-params.md). So each
pointer needed exactly `unsigned ptr + 4 <= maxAddr`.

| loop | body | exit | body before the fix |
|---|---|---|---|
| D memmove | QED 0.705 G | QED 0.704 G | FAIL 1.805 G |
| G `br_divrem` | QED 0.856 G | QED 0.856 G | (already passing) |
| I limb accumulate | QED 0.998 G | QED 0.970 G | FAIL 21.242 G |
| K `br_i31_add` | QED 0.801 G | QED 0.788 G | FAIL 4.823 G |
| M `br_i31_sub` | QED 0.784 G | QED 0.773 G | FAIL 4.815 G |

**PROTOCOL (added 2026-09-14): every figure in this table is GROSS
`allocated_words`, not net.** Subtract the Phase-1 baseline (`ZZMladBase.v`,
641,953,144) to get the cost of the segment: D 63 M, M 142 M, K 159 M, G 214 M,
I 356 M. Read as net they say "per-segment cost is nearly size-independent",
which is false and was briefly concluded on 2026-09-14; read correctly they say
cost is roughly PROPORTIONAL to segment size at ~12.7 M words/instruction.
See `diagnostics/segment-postcondition-cost.md` §3.

**Segment I verifies.** The `LeakMul` risk does not apply: that model is on
`issue/mul-leaks-args` and not on this branch (owner, 2026-09-09). If it ever
merges, segment I must be re-checked — its `MUL31(mw, q)` has a secret `q`.

Note every fixed body got CHEAPER than its failing run (I: 21.2 G -> 1.0 G).
A `solve_vc` that cannot close does extra work, so failing-run costs are upper
bounds and must never be quoted as the cost of the segment.

Two traps hit while doing this, both already documented and both walked into
anyway:
- the four `*Final.v` files had **never compiled** — three unterminated header
  comments each, left by the session that wrote them. `wc -l` and "the file
  exists" say nothing; only a compile does.
- `asn_pc_eq`'s argument lives at `Σ ▻ "a"`, so a `Definition foo : Term Σ _`
  does not weaken into it and must be INLINED. `ZZMladAddBody.v` carries a
  comment saying exactly this, which I read and then did anyway.

## Phase 3 — nine straight-line segments written, THREE verify

> **SUPERSEDED 2026-09-14 — ALL NINE NOW `Qed`.** Re-compiled from source this
> date: B, C, E, H, N all `Qed` (L confirmed separately). The `.v` files were
> edited 09-13, four days after the table below was written, and the fix is
> visible in them: a cut-specific register spec, `mlad_reg_specs_cut`, in place
> of `mlad_reg_specs_rel`. **That CONFIRMS "the leading hypothesis, NOT yet
> confirmed" further down this section** — a cut assertion must carry
> publicness, because a mid-program segment that branches on a register
> receives it havoc'd-and-private from the cut and a `formula_relop` on private
> data is the `secret-data-walls` `False`. The hypothesis is closed; the
> "next step is per-segment" paragraph below is DONE, not pending. The
> FAIL/QED column below is kept as the historical record of the pre-fix state —
> **never read it as current status.**

`Example/ZZMladStraight.v` (also split into `ZZMladSg{A,B,C,E,F,H,J,L,N}.v` so
one failure does not mask the rest). Exit targets were read off the actual
branch instructions, NOT off §1's map — **§1's segment B range is off by one**:
idx 70 (byte 280) IS the `if (mblr==0)` test the map attributes to B, so B
spans idx 55..70 and exits at 284.

| seg | idx | instrs | head | exit | result |
|---|---|---|---|---|---|
| A | 0..3 | 4 | 0 | 220 (branch taken) | **QED** |
| B | 55..70 | 16 | 220 | 284 | FAIL |
| C | 71..83 | 13 | 284 | 336 | FAIL |
| E | 90..106 | 17 | 360 | 492 (uncond. jump) | FAIL |
| F | 123..134 | 12 | 492 | 540 | **QED** |
| H | 162..189 | 28 | 648 | 760 | FAIL |
| J | 219..236 | 18 | 876 | 948 | **QED** |
| L | 250..263 | 14 | 1000 | 1056 | FAIL |
| N | 277..281 | 5 | 1108 | 1128 | FAIL |

### What the failures are NOT

Dumped rather than guessed (`ZZMladSgBDump.v`): **`solve_vc` COMPLETES** and
leaves an unreduced `Erasure.inst_symprop` tree. So this is not a solver bug,
not a missing `solve_symbase_fetch` shape, and not the fetch-bound residual
that Phase 2 was. Fuel is not it either — the passing A/F/J run at 3.6-7.5x the
instruction count and the failures are at 3-6x.

### The leading hypothesis, NOT yet confirmed

**A cut assertion must carry PUBLICNESS, and `mlad_reg_specs_rel` does not.**
It marks nearly every register private (`false`), which is right at function
ENTRY but wrong at a cut: a mid-program segment that BRANCHES on a register
receives it havoc'd-and-private from the cut, and a `formula_relop` on private
data is the `secret-data-walls` `False`. A/F/J are consistent with this —
segment A branches on `T0`, but loads it FRESH from the PUBLIC-pinned `m[0]`
inside the segment, so the entry spec never constrains it.

Next step is per-segment: find which register each failing segment branches on
and mark exactly those public in a mid-program spec. That is invariant DESIGN,
one segment at a time, not a mechanical edit.

**Independently confirmed and separate:** segment N needs `X2 = PVBaseOff 1152`,
not 1168. The prologue's `addi X2, X2, -16` lives in segment B, so 1168 is the
entry value and every segment after B sees 1152. N reads the four spill slots at
`0/4/8/12(X2)` = p+1152..1164, which only lands in `mlad_stack_specs_rel` if X2
is 1152. B and N are the only segments that touch X2 at all.

## Still to do

- Phase 3: the six failing straight-line segments (above).
- Phase 4: compose the fourteen via `myWP2_loop_induction` / `_bind` / `_join`.
- Phase 5: MACHINERY DONE (`cfg_instrs_verified_composed`, see the earlier
  RESULTS section); what remains is instantiating `ImplPre`, which `gen_implpre`
  supplies for generated contracts.
- Phase 6: promote out of `ZZ*` into tracked files, `_CoqProject`, `Results.v`,
  gate allowlist.

## Phase 3 update — 5/9 straight-line segments verify

A, F, J (already), plus **N** and **L**. B, C, E, H still fail.

### Two confirmed causes, both found by dumping rather than guessing

**1. The stack pointer moves at segment B (fixes N).** The prologue's
`addi X2, X2, -16` lives INSIDE B, so `X2 = p+1168` holds only up to and
including B; every later segment sees `p+1152`. N's four spill reloads at
`0/4/8/12(X2)` land on `mlad_stack_specs_rel`'s 1152..1164 only with the
smaller value. `mlad_reg_specs_cut_at` in ZZMladCommon.v now takes the stack
offset as a parameter (`_cut_hi` = 1168 for B, `_cut` = 1152 after).

**2. A conditional branch has TWO successors; a one-exit contract is a `False`
(fixes L).** The taken arm lands on an address that is in neither the segment's
own sub-table nor its exit list, and the executor errors on a pc matching no
table key — which surfaces as the bare `False` `cfgver-solve-vc` documents.
Resolving each taken target says which fix applies, and they differ:

| seg | branch | taken target | what it is | fix |
|---|---|---|---|---|
| B | idx 70 `beqz T0` | 428 | the DEAD `mblr==0` arm | guard (T0 <> 0) |
| C | idx 80 `beqz T6` | 360 | segment E's head — REAL | second exit (done, still fails) |
| H | idx 163 `bgeu A6,T4` | 668 | INTERNAL to H (648..756) | not an exit at all |
| L | idx 250 `bltu T1,T2` | 1108 | segment N's head — REAL | **second exit — QED** |

C and L are the same shape: `if (trip count == 0) skip the following loop`, so
both genuinely have two successors. L verifies with both declared; C does not,
so C has a further cause not yet found.

### What the publicness hypothesis was worth

It was NOT the cause. `mlad_reg_specs_cut_at` marks T0/T1/T2/T4/T6/A6 public —
the six registers the straight-line segments branch on, each a length or counter
that is public in the C source. That change alone fixed nothing; only combined
with the stack-pointer offset did N pass. It is retained because it is correct
and will be needed once B's guard is written (a guard on a private register is
the secret-data wall), but it must not be credited with the fix.

### The `False` was invisible until inst_symprop was unfolded

`solve_vc` runs `cbn -[Erasure.inst_symprop]` — a deliberate 30x speedup landed
2026-09-08. Blocking that constant also stops the demonic binders being peeled,
so a failing VC shows as one goal that is the WHOLE erasure tree, with no hint
of the actual obligation. A full `cbn` (paying the 30x) reduced sgE's residual
to the single word `False`, which is what identified the exit problem. Worth
knowing for any future `No applicable tactic` on this rig: the informative dump
is `constructor; cbn; intros; repeat split`, NOT `solve_vc`.

### Remaining, with what is known about each

- **B** — needs a guard making the dead-arm branch infeasible (`T0 <> 0`, i.e.
  mblr != 0). Cannot be written with `gen_pre_rel`: the register values are
  existentially bound inside it and cannot be named from outside. B needs its
  branched-on register lifted into its own LCtx and pinned, the way the loop
  Body contracts do. That is invariant design, not a mechanical edit.
- **C** — has both real successors declared and still fails; cause unknown.
  Suspect a second control-flow instruction in idx 71..83 not found by the
  BTYPE grep (a JAL would have been missed).
- **E** — no conditional branch at all (ends in an unconditional `j` to 492,
  which IS declared). Residual is `False`. Cause unknown.
- **H** — its only branch is internal, so the two-exit story does not apply.
  Cause unknown.

## Phase 3 COMPLETE — all 19 segment contracts verify (2026-09-09)

Ten loop contracts (5 bodies + 5 exits) and nine straight-line segments, all
`Qed`, no `Admitted`. Phases 1, 2 and 3 are done.

### The one rule that explains every straight-line failure

**A cut assertion must pin every register that feeds a MEMORY ADDRESS or a
BRANCH CONDITION. Nothing else needs pinning.**

That is the whole story, and each of the six failures was one instance:

| seg | what was missing |
|---|---|
| N | `X2 = p+1152`, not 1168 — the prologue's `addi X2,X2,-16` is inside B, so every segment after B sees the lowered pointer |
| L | a SECOND EXIT: `bltu T1,T2` at 1000 skips the sub-loop straight to N (1108) |
| H | a second exit again, but via an unconditional `j` at 664 -> 876 that a BTYPE-only grep MISSED |
| B | `T0 = 63` — segment A loads m[0] into it; without the value the dead `mblr==0` arm at 428 has to be explored |
| C | `T0=31, T1=2, T5=0x3FFFFFFF, A3=0x7FFFFFFF` — idx 78 is `and T6,T6,T5`, so `beqz T6` is decided by (T1-1) & T5, NOT by T1 alone |
| E | `A7=&x[2], T3=&x[1], A5=8, T2=4` — E loads from four addresses built from otherwise-havoc'd registers, and an unresolvable load address IS the bare `False` |

The pinned values are not guesses: they were obtained by symbolically executing
segment B by hand from the pinned public `m[0] = 63`
(`A6 = 94`, `T1 = 94>>5 = 2 = mlen`, `A5 = 8`, `A7 = A0+8`, `T0 = 63&31 = 31 =
mblr`, `T5 = 0x40000000-1`, `A3 = 0x7FFFFFFF`), then segment C the same way.
Every value pinned is PUBLIC in the C source (lengths, counters, pointers);
every secret (`x[]`, `A4`, and everything derived) stays `PVExist`/private, so
no secret is assumed public anywhere.

### Two method lessons

- **`solve_vc` hides the diagnosis.** Its `cbn -[Erasure.inst_symprop]` (the
  2026-09-08 30x speedup) also stops the demonic binders being peeled, so every
  failure looks like one goal containing the whole erasure tree. Pay the 30x
  once — `constructor; cbn; intros; repeat split` — and the residual reduces to
  the single word `False`, which is what made all six diagnosable. This is now
  the first thing to try on a `No applicable tactic` here.
- **Grep for ALL control flow, not just `BTYPE`.** Segment H's second exit is a
  `RISCV_JAL`. One missed jump cost a full wrong hypothesis.

### Retraction

The earlier "publicness of branched-on registers" hypothesis was **wrong as
stated**. Marking T0/T1/T2/T4/T6/A6 public fixed NOTHING on its own — E has no
branch at all and still failed. Publicness is necessary for the pinned values
to be usable (a guard on a private register is the secret-data wall) but it was
never the cause. `mlad_reg_specs_cut_at` is retained on those grounds.

## What remains

- **Phase 4 — compose.** Fourteen segments via `myWP2_loop_induction` /
  `_bind` / `_join`, plus `itable_faith_of_segment` for the sub-table gaps.
  Note every contract currently carries `asn_no_post`: nothing flows from one
  segment's exit to the next's entry. Composition needs real postconditions,
  and the values above are exactly what they must carry.
- **Phase 5 — DONE as machinery** (`cfg_instrs_verified_composed`); what is
  left is instantiating `ImplPre`.
- **Phase 6 — promote** out of `ZZ*` into tracked files + `_CoqProject` +
  `Results.v` + the gate allowlist.

## Phase 4 — machinery all validated; the chaining proof itself is NOT written

Every mechanism the composition needs now has a working instance on muladd.
What is missing is the (large, mechanical) work of applying them 14 times.

### 1. Post-context generators — DONE (`ZZMladCommon.v`)

A precondition lives at `Σ ▻ "a"`, a postcondition at `Σ ▻ "a" ▻ "an"`, and an
Assertion is indexed by its context: `gen_pre_rel` / `gen_mem_pre_rel` are fixed
at the narrower one and do NOT weaken. Added `gen_post_rel` /
`gen_mem_post_rel` (same bodies, wider context), so a cut assertion can be
written as literally the next segment's precondition. Note the PVExist branch
must write the address term OUT IN FULL — `asn.exist` extends the context and an
outer `let addr := …` does not weaken into it, which is why GenContract repeats
it too.

### 2. The first real cut assertion — DONE and VERIFIED

`sgA_post := gen_post_rel sgB_regs ∗ gen_mem_post_rel mlad_mem_specs_rel ∗
minimal_pre`, i.e. A's postcondition IS B's precondition. Both segments still
`Qed` with it.

**The discipline that makes this work, and it cost a failed attempt to find:**
a cut assertion may claim only publicness the previous segment can ESTABLISH.
Assuming `secLeak` in a standalone precondition is free; PROVING it as a
postcondition is not. `sgB_regs` initially promoted A6/T1/T2/T4/T6 to public
(left over from the retracted publicness hypothesis) and sgA could not prove it
— those registers are private garbage at function entry. B only ever needed
`T0` pinned, because `beqz T0` is its one branch and it computes everything
else itself. Tightened, both pass.

### 3. Sub-table derivation — DONE (`ZZMladCompose.v`, `HifA`)

Unlike `SwapComposedResult` (both segments share one table, one `Hif` serves
both), each muladd segment carries its OWN sub-table, so each needs its
`itable_rel` derived from the whole-program list via `itable_faith_of_segment`.
`HifA` does this for segment A and is `Qed`.

Two argument-passing traps, both costing a compile each:
- **Do NOT `Set Implicit Arguments` in the composition file.** It makes
  `itable_faith_of_segment`'s `pre`/`seg`/`post` positional-only *and*
  unnameable, so the split cannot be supplied at all.
- Its implicit arguments are exactly `Σ`, `cbase`, `off` (a failed named
  application reports those three); `p`, `ι`, `pre`, `seg`, `post` are
  positional. `mlad_instrs` is a `list AST` and the tables are over
  `AnnotInstr`: `list_AST_AnnotInstr` is a Coercion but does not fire inside a
  stated goal under `firstn`/`length`, so name it once (`mlad_ai`).

### 4. The bridge to a leakage theorem — DONE (Phase 5, earlier section)

### What is actually left

- **The chaining proof.** 13 more cut assertions (each needing the publicness
  discipline above), a `HifX` per segment, and the `sound_scfg_verification_
  condition_myWP2` / `myWP2_loop_join` chain. `SwapComposedResult` is ~60 lines
  for TWO segments over ONE table; muladd is fourteen over fourteen, and the
  framing at each cut needs `iExact` rather than `iFrame` because the two sides
  are convertible but not syntactically equal.
- **Five loop inductions.** `myWP2_loop_induction` needs
  `Inv : nat -> iProp`, with the body contract's postcondition being `Inv n`.
  NOTE: `mlen = 2` is pinned, so D/I/K/M run 1-2 trips and could simply be
  unrolled via `myWP2_loop_bind` instead; only **G** (`br_divrem`, 31 trips)
  genuinely needs an induction, and its invariant must own the loop state
  across all remaining trips rather than the single sliding pair the body
  contract currently states.
- **`ImplPre`** for the composed whole.

## Phase 4 — the TAIL chain: cut assertions all VERIFIED (2026-09-09)

`sgL (1000..1052) ; amBody (trip 1) ; amFinal (trip 2) ; sgN (1108..1124)`.
Files: `Example/ZZMladTail.v` plus the four segment files.

**Trip count settled, and confirmed by the executor rather than by hand.**
Segment J loads `T1 = x[0] = 63` (idx 222), makes it 126 (idx 226), sets
`T2 = 64` (idx 228) and `A7 = (126>>5)<<2 = 12` (idx 227/229). So `bltu T1,T2`
at idx 250 is `126 <u 64` = FALSE, control falls into the sub setup, and idx
261..263 give `A4 = m+4 = p+1144`, `A0 = p+1132`, `e = m+12 = p+1152`.
**Exactly two trips** (bp = 1144 then 1148), both over declared cells; 1152 is
only the sentinel and is never dereferenced. So D/I/K/M need no induction at
all — `amBody` once, then `amFinal`. (I briefly mis-derived this as 3 trips
running off the end of `m[]` and raised a false alarm about the memory spec;
there is no such problem.)

| contract | what it now proves | |
|---|---|---|
| `sgL` | the L->M cut: ap=p+1132, bp=p+1144, e=p+1152 | Qed |
| `amBody` | the BACK EDGE: ap+4, bp+4, one trip later | Qed |
| `amFinal` | the M->N cut | Qed |
| `sgN` | tail end, minimal `mlad_reg_specs_tail` | Qed |
| `HifSub` | the shared sub-table for BOTH loop links | Qed |

### THE rule for cut assertions, learned three times over

**A postcondition can only assert what the segment OWNS or COMPUTED.** Every
failed attempt was an over-claim, and standalone verification of all 19
contracts revealed none of them — only composition does:

1. `sgA_post` promoted A6/T1/T2/T4/T6 to public; segment A cannot establish
   publicness for registers that are private garbage at function entry.
   (Assuming `secLeak` in a precondition is free; PROVING it in a
   postcondition is not.)
2. `sgL_post` claimed `A3 = 0x7FFFFFFF` while sgL's entry left A3 unknown —
   residual was the single equation `v3 = [bv 0x7fffffff]`. Fixed by pinning A3
   at sgL's entry (it IS the limb mask, set in segment B idx 60/61).
3. `amFinal_post` claimed all TWENTY registers while amFinal owns NINE. That
   over-claim is what produced a bare `False` — you cannot conjure ownership.
   Fixed by shrinking the cut to the five registers sgN actually uses (X2 plus
   S0-S3, its four spill reloads) and carrying those through the loop.

So a cut assertion should be the MINIMAL frame the next segment needs, not a
copy of a whole-program register spec.

### Method notes

- **`rocq_start` cannot replay these files** (`Valuation`/`N` unresolved in the
  pet session) — the dune/load-path problem `rocq-implementation` documents for
  `case_study/RiscvPmp/CFGVer/`. Preamble mode needs the whole definition block
  pasted. Where a diagnosis is unambiguous, one `coqc` is cheaper than setting
  that up; where it is not, the full-`cbn` dump is the tool.
- **Occurrence-numbered rewrites are fragile.** `rewrite … at 4` in `HifSub`
  was simply wrong; the obligation is only about the reassembled list's LENGTH,
  and both sides `vm_compute` to 282, so assert that equality instead.
- **An interrupted tool call may already have written its file.** A rejected
  edit left `persist p acc_snoc_right` (a world/modality-level operation, wrong
  layer for an Assertion) on disk; it sent elaboration into an unbounded search
  — 5.8 GB and climbing after 9m42s on a file of pure definitions that compiles
  in 9 s. Verify the tree after an interruption instead of assuming nothing
  happened.
- The register block CAN be context-generic (`gen_regs_any`, parameterised by
  the base term); the memory block CANNOT, because `p` is used inside the
  `asn.exist` branch that extends the context.

### Still to write

The Iris glue only: `HifL` / `HifN`, four `etable_rel` facts via
`etable_faith_exits_of_offs`, and the `sound_scfg_verification_condition_myWP2`
/ `myWP2_loop_join` chain. Then `ImplPre` and Phase 5's bridge give a leakage
theorem for the tail.

## Phase 4 — tail chain: 7 supporting facts + the first LINK are Qed (2026-09-09)

`Example/ZZMladTail.v`, all `Qed`, no holes:

| fact | what it gives |
|---|---|
| `HifL`, `HifSub`, `HifN` | each segment's sub-table from the ONE whole-program list (`HifSub` serves both loop links, which share `am_seg`) |
| `HefL`, `HefBody`, `HefFinal`, `HefN` | the four `etable_rel` facts |
| **`linkN`** | **sgN alone: its precondition -∗ `exitCond_WP2_loop (sgN_exitCond ia)`** |

`linkN` is the important one: it is the full `sound_scfg_verification_condition_
myWP2` application for a segment with its OWN sub-table, which
`SwapComposedResult` never needed (there both segments share one table). The
remaining three links are the same shape plus a cut.

### Reusable pieces found here

- **Exit-offset tactic** (`exit_hit x y`), validated in preamble mode at 46 ms:
  `rewrite !bv.of_N_add`, normalise the N-level sum with `lia`, then close via
  `bv.eqb_spec`'s reflect. **There is no `bv.eqb_refl`.** The matched disjunct
  may sit on EITHER side of an `orb` (sgL has two exits) and `X || true` does
  not reduce, so finish with `rewrite ?Bool.orb_true_r; rewrite ?Bool.orb_true_l`
  rather than `reflexivity`.
- **Sub-table obligations**: never use occurrence-numbered rewrites. The goal is
  only about the reassembled list's LENGTH, and both sides `vm_compute` to 282 —
  `assert (Hlen : … = length mlad_ai) by (vm_compute; reflexivity)`.
- `etable_faith_exits_of_offs` takes `cbase` EXPLICITLY: use
  `apply … with (cbase := …)`, not term-level naming. `itable_faith_of_segment`
  is the opposite (`Σ`/`cbase`/`off` implicit, `p`/`ι`/`pre`/`seg`/`post`
  positional).
- The exit tail is `rewrite Hexit; exact I` — the goal is `Is_true (…)`, not
  `… = true`.

### Syntax traps that cost a compile each

- **The Iris `∃` binder notation is NOT active in this import context.** Both
  `ZZMladCompose.v` and `ZZMladTail.v` reject `(∃ v, nextpc ↦ᵣ v)` with
  "reference v was not found", even though `SwapComposedResult.v` has exactly
  that line with the same imports. Write `bi_exist (fun v => …)` — the
  application form needs no notation. (`iExists` in a PROOF is fine.)
- A Coq comment inside a `[ t1 | t2 ]` tactic bracket breaks parsing; put it
  above the tactic.
- `rewrite ?A, ?B` inside a tactic bracket does not parse (the comma clashes
  with the goal-selector grammar). Sequence them: `rewrite ?A; rewrite ?B`.

### The coercion "obstacle" was NOT one — RETRACTED

I recorded that chaining `amFinal` would need a `map`/`firstn` commutation
lemma, because `HifSub`'s table is over `firstn 13 (skipn 264 mlad_ai)` while
the contract's is built from `amf_seg` (a `list AST` reaching `list AnnotInstr`
via the `list_AST_AnnotInstr` Coercion). **Wrong**: both are CONCRETE literal
lists, so they compute to the same value and conversion closes the gap with no
lemma at all. Tested rather than assumed. Do not write that lemma.

### `linkFN` framing goals — DUMPED and diagnosed (2026-09-09)

**Bullet 1 (feeding amFinal its precondition) — mechanical.** The hypothesis is
`asn.interpret (extend_to_minimal_pre (cfg_precondition (amFinal ia))) ι.[a↦…]`
and the goal is the same thing UNFOLDED (convertible, so `cbn` + `iExact`, not
`iFrame`, which matches syntactically) plus ONE EXTRA PURE CONJUNCT the goal
carries and the hypothesis does not:

    ⌜secLeak (SyncVal (bv.of_N ia + bv.of_N 1056))⌝

That is a fact to PROVE, not to frame — a `SyncVal` is public by construction.
`cfg_instrs_verified` discharges the identical obligation with
`iSplit. { done. }`. So bullet 1 is:

    cbn [cfg_precondition amFinal].
    iSplitL "Hpre"; [iExact "Hpre" | iSplit; [done | iFrame]].

**Bullet 2 (the cut into linkN) — reveals the cut assertion is STILL too weak.**
The goal is

    pc ↦ᵣ SyncVal av ∗ (∃ v, nextpc ↦ᵣ v) ∗ ptsto_instrs …
    ∗ asn.interpret amFinal_post ι.[a↦…].[an↦SyncVal av]
    ⊢ exitCond_WP2_loop (sgN_exitCond ia)

Two gaps against what `linkN` consumes:

1. `av` must be shown to BE `bv.of_N ia + bv.of_N 1108`. It follows from
   `Hexit : amf_headExitCond ia av`, exactly as `SwapComposedResult` does it:
   `assert (Hav : av = …) by (destruct (bv.eqb_spec …); congruence). subst av.`
2. **`amFinal_post` supplies only the register block; sgN's precondition also
   wants `gen_mem_pre_rel mlad_mem_specs_rel` (the WHOLE memory block), the
   pc-eq, and the base bound.** amFinal owns two cells, not ten, so it cannot
   supply that — the same over-claim that gave the earlier bare `False`, now on
   the MEMORY side rather than the register side.

**The fix, and it is the minimal-frame rule again:** sgN only reads the four
spill slots at 1152/1156/1160/1164 (`lw S0,12(X2)` … `lw S3,0(X2)`). So
introduce `mlad_mem_specs_tail` = those four cells, use it in BOTH sgN's
precondition and `amFinal_post`, and add the four cells to amFinal's
precondition so they flow through the loop. The pc-eq is delivered by the exit
(`pc ↦ᵣ`), and the base bound is a pure fact about `p` that can be carried as a
hypothesis of the link lemma rather than through the assertion.

Note this is the FOURTH instance of the same rule (registers at A->B, values at
L->M, register ownership at M->N, now memory ownership at M->N). Write cut
assertions as the minimal frame from the start.

### `linkFN` — bullet 1 CLOSED, bullet 2 needs ι PINNED (2026-09-09, latest)

**CORRECTION (same day): the claim "bullet 1 now closes" was WRONG.** It came
from misreading a dump: `iStopProof` had failed silently so no goal printed for
bullet 1, and the absence of output was read as success even though the same
output line said `B1 goals: 1`. Both bullets still have exactly one open goal.
Read the COUNTER, not the absence of a print.

The tactic below is still the right shape for bullet 1 (iExact for conversion,
`done` for the pure secLeak conjunct) but does not finish it:

    cbn [cfg_precondition amFinal].
    iSplitL "Hpre"; [iExact "Hpre" | iSplit; [done | iFrame]].

The memory-frame fix also landed: `sgN` uses `gen_mem_pre_rel
mlad_stack_specs_rel` (the four spill slots it actually reads, already defined
in ZZMladCommon.v) instead of the whole ten-cell block, and `amFinal` carries
those four cells in BOTH its precondition and `amFinal_post`. `sgN` and
`amFinal` are both Qed with that.

**Bullet 2 has ONE goal left, and it is a STATEMENT problem, not a tactic one:**

    Hpost : asn.interpret amFinal_post ι.[a↦…].[an↦SyncVal (bv.of_N (ia+1056+52))]
      ⊢ asn.interpret (… (cfg_precondition (sgN_contract ia)))
            (tailI ia).[a↦…] ∗ pc ↦ᵣ SyncVal (bv.of_N ia + bv.of_N 1108)

- minor: `bv.of_N (ia+1056+52)` vs `bv.of_N ia + bv.of_N 1108` — `bv.of_N_add`
  plus `1056+52 = 1108`, i.e. the same `exit_hit` normalisation used for the
  etable facts.
- **the real one: `Hpost` is interpreted at the ARBITRARY valuation `ι`, while
  the goal needs `tailI ia`.** `linkFN` quantifies `ι` freely and only
  constrains it through `Hp` (about `inst amf_place ι`), which pins
  `ι("p") + 1056` but not `ι("p")` itself. Nothing lets the two assertions be
  equated.

**DONE: the concrete valuation is in place** (`amI ia apo bpo eo` in
ZZMladTail.v, with `linkFN` stated at `ιF ia = amI ia 1136 1148 1152`, the
second trip). Both sides of the cut are now CLOSED terms, and bullet 2's
remaining goal is legible and reachable:

    Hpost : asn.interpret amFinal_post (ιF ia).[a↦…].[an↦SyncVal (bv.of_N (ia+1056+52))]
      ⊢ asn.interpret (… (cfg_precondition (sgN_contract ia))) (tailI ia).[a↦…]
        ∗ pc ↦ᵣ SyncVal (bv.of_N ia + bv.of_N 1108)

Next step: `replace (ia+1056+52)%N with (ia+1108)%N by lia`, then
`rewrite <- bv.of_N_add` to match the goal's `bv.of_N ia + bv.of_N 1108`, then
split `pc` off (`iSplitR "Hpc"`) and match the assertion halves by `iExact`
after `unfold amFinal_post; cbn`.

Also fixed on the way: **`HifSub` had an unused `ia` binder.** Because `ia`
does not occur in its conclusion, `apply` could not infer it and failed with a
completely misleading "Cannot find a relation to rewrite". Dropped.

The original write-up of the fix, for reference:

    Definition amI (ia apo bpo eo : N) : Valuation amfCtx :=
      [env].["p"∷ty_xlenbits  ↦ SyncVal (bv.of_N ia)]
           .["ap"∷ty_xlenbits ↦ SyncVal (bv.add (bv.of_N ia) (bv.of_N apo))]
           .["bp"∷ty_xlenbits ↦ SyncVal (bv.add (bv.of_N ia) (bv.of_N bpo))]
           .["e"∷ty_xlenbits  ↦ SyncVal (bv.add (bv.of_N ia) (bv.of_N eo))]

and state `linkFN` at `amI ia 1136 1148 1152` (the SECOND trip: ap and bp have
each advanced 4 from sgL's 1132/1144). Then `ι("p")` is `bv.of_N ia` by
construction, `Hp` becomes `reflexivity`, and the register/memory halves of the
cut denote the same iProp on both sides. `linkBFN` then uses
`amI ia 1132 1144 1152` (the first trip) and `amBody`'s back-edge postcondition
carries it to the second.

Alternative if that proves awkward: keep `ι` free and add the hypothesis
`env.lookup ι ("p"∷ty_xlenbits) = SyncVal (bv.of_N ia)` — derivable from `Hp`
by `bv.add_cancel_l`, which exists and needs no no-wrap side condition.

### `linkFN` — earlier state (superseded by the entry above)

The `assert`ed `HifF`/`HefF` facts and the
`sound_scfg_verification_condition_myWP2` application all go through; the proof
fails only with "Attempt to save an incomplete proof" — the remaining goals are
the FRAMING at the cut, which is exactly where `SwapComposedResult` needs
`iExact` rather than `iFrame` (its own comment says why: the two sides are
convertible but not syntactically equal, and `iFrame` matches syntactically).
That is the next thing to write, and it needs the goals dumped rather than
guessed.

### Argument-passing: use `assert` + `apply … with`, not term-level naming

Three different conventions were hit in one proof, so do not try to remember
them per lemma:
- `itable_faith_of_segment` reports nameable `Σ cbase off`; `p`/`ι`/`pre`/`seg`/
  `post` are positional.
- `etable_faith_exits_of_offs` takes `cbase` EXPLICITLY — term-level
  `(cbase := …)` fails, `apply … with (cbase := …)` works.
- `HefFinal` (a local lemma!) reports nameable `ia cbase` only.

**The robust pattern that works for all of them**: `assert` the fact you want
with its statement written out, prove it `by (apply L with (cbase := …); …)`,
and pass the resulting hypothesis. Term-level named application is not portable
across these.

### Remaining for the tail

`linkFN` (amFinal + the cut into linkN), `linkBFN` (amBody + the back edge),
`tailChain` (sgL), then `ImplPre` and Phase 5's bridge for a leakage theorem.


## Phase 4b — the sub-loop verified by a RANGE INVARIANT (2026-09-09)

`ZZMladTail.v` compiles clean, 188 s, 23 `Qed`, no holes. The tail is now

    sgL (1000..1052) ; amBody x k (by induction) ; amFinal ; sgN (1108..1124)

with the loop discharged by `myWP2_loop_induction`, NOT by unrolling. Owner
chose this over widening `amBody`'s frame ("we will want to use these methods
in other places as well").

### The framing fact this rests on — and a RETRACTION

I first claimed the remaining cells could not be framed around a segment,
because "CFGVer contracts drop leftover resources". **That is wrong**, and the
claim conflated two different things: the SYMBOLIC EXECUTOR drops leftover
chunks at a contract's exit (`Contracts.v`'s own comment, and true), but at the
IRIS level `sound_scfg_verification_condition_myWP2`'s `with "[...]"` selector
decides only what the CONTRACT consumes -- every unselected spatial hypothesis
stays in context for the continuation goal. Verified with a probe carrying a
spare `(P : iProp Σ)` through: it arrives in goal 2 untouched.

So `amBody`'s sliding two-cell contract is UNCHANGED. The n windows beyond the
current one ride outside it as ordinary Iris resources. Being Iris-level they
may be a Coq `Fixpoint` over the trip count, which is what makes a
symbolic-length range expressible at all -- inside an `Assertion` it is not,
because the VC is discharged by `vm_compute` and needs a concrete length.

### Shape

- `cellsPriv` / `cellsPub n base off` -- the range, indexed by an **N offset**,
  not by repeated `bv.add` (see below).
- `amWinAsn` -- the current window: `amBody`'s precondition MINUS `asn_pc_eq`
  and MINUS the guard, PLUS `minimal_pre`. The guard is what separates body
  from exit (`bp+4 <> e` vs `= e`), so each half derives its own from the trip
  arithmetic. This is why the invariant carries its own assertion rather than
  `cfg_precondition (amBody ia)` -- exactly what `cdInvAsn` does in
  `Example/PaddedLoopResult.v`, the working `myWP2_loop_induction` call site.
- `amInvN ia n` -- `bi_exist apo/bpo` + the trip relations as PURE side
  conditions (`bpo + 4*(n+1) = 1152`, `apo + 12 = bpo`), mirroring `plInvN`'s
  `bv.bin k = n+1`.
- `amTailRegs` -- X2 and S0-S3. `amf_regs` is `X2 :: am_regs ++ [S0..S3]`, so
  `amFinal` needs registers `amBody` never owns; they ride outside too.
  `gen_regs_any` already covers them (it takes the base TERM), no new builder.

### One contract change was needed: amBody_post += minimal_pre

`amBody_post` did not hand back the ambient chunks (`cur_privilege`,
`inv_leakage`), so each trip consumed them and the invariant could never be
re-established -- the body would run exactly once. `cdInvAsn` carries the same
chunks (`pl_step` destructures them as `Hpriv`/`Hinv`). The segment never
writes `cur_privilege`, so the executor still holds both at the exit and the
postcondition can claim them; re-verified in 15 s. **This invalidated
`ZZMladSgL.vo`** (it uses `am_regs`) -- rebuilt, 19 s.

### THE recurring cost: convertible but not SYNTACTICALLY equal

`iFrame` matches syntactically. Six distinct instances in this one proof, each
costing an iteration; this is the dominant cost of composing CFGVer segments
and should be the first hypothesis whenever a frame "obviously" ought to close:

1. `bv.of_N (off+4)` vs `bv.of_N off + bv.of_N 4` -- hence the N-offset
   indexing of `cellsPriv`; a recursion building `((base + of_N 1152) + of_N 4)
   + of_N 4` is equal to `base + of_N 1160` but unmatchable.
2. `subst` orienting on `apo + 12 = bpo`, leaving `amI ia 1136 (1136+12) 1152`
   against the goal's `... 1148 ...`. Fix: `clear` the trip equations first.
3. `1152 + 4` vs `1156` -- `cbn [N.add Pos.add]` does NOT collapse N literals;
   needs `change (1152+4)%N with 1156%N`, innermost first.
4. `asn_regidx_pts` (`↦ᵣ`) is `match reg_convert r with ...`, and `reg_convert`
   dispatches on `bv.to_bitstring` -- a match **cbn will not reduce at any
   delta setting**; only `vm_compute` does. Fix: eight equations
   (`reg_convert A0 = Some x10`, ...) by `vm_compute; reflexivity`, then `cbn`
   gets through. Packaged as the `reg_reduce` tactic.
5. `am_reg_asn` vs `am_post_reg_asn` -- two separate definitions with IDENTICAL
   bodies, so the pre- and post-register blocks never match. Fix:
   `cbn [am_reg_asn am_post_reg_asn]` then `reg_reduce` AGAIN for the
   `reg_convert` matches that exposes. **This one produced the misleading
   "No applicable tactic"**: the register conjuncts stayed unframed, so the
   `first [...]` handling the pure leftovers met goals it had no case for.
6. `rewrite bv_shift4` reports "found no subterm" on a goal equal to its RHS
   (elaboration difference in the implicit width), while the PRIMITIVE sequence
   `rewrite <- bv.add_assoc; rewrite bv.of_N_add; rewrite bv.add_comm` works.
   **`rewrite` matches syntactically; `apply` unifies up to conversion** -- when
   a rewrite refuses on a term you can prove equal, reach for the primitives or
   for `apply`, not for another delta flag.

### iFrame performance, which is a real constraint here

- **Split before reducing.** A `cbn` that reaches `instrs_of_list ... mlad_ai`
  tries to compute the 282-entry store and diverges. Peel pc/nextpc/instrs off
  with `iSplitR`/`iSplitL` FIRST; only the assertion half is ever reduced.
- **Isolate the big conjunct.** With `asn.interpret amWinAsn` still in the
  goal, `iFrame` tries every named hypothesis against that unreduced term and
  times out even when the rest match verbatim.
- **Name the hypotheses, in goal order.** A bare `iFrame` over ~25 atomised
  hypotheses times out; naming them runs in ~19 s.
- **`iFrame "H"` needs the WHOLE hypothesis as one syntactic block** -- on a
  `∗`-chain it fails outright. Destructure to atoms first.

### Other traps banked

- `%N` does NOT stop `exp_scope`'s `=` / `<=` from winning. Write `@eq N` /
  `N.le` explicitly in `assert`s.
- `exitCond_WP2_loop c` is `myWP2_loop (∃ v, pc ↦ᵣ SyncVal v ∗ ⌜c v⌝)` -- `⌜c v⌝`
  under the **`Is_true` coercion**, not `c v = true`. Spelling it `= true` does
  not unify. (Same distinction as `linkN`'s `rewrite Hexit; exact I`.)
- `linkFN` needed a NEW hypothesis `Hb`: `sgN`'s precondition demands the
  address-space bound and `amFinal_post` does not carry it, so it threads in
  like `Hrep`. `am_step` needs `Hmax` (maxAddr form) and `Hlen` (lenAddr form)
  for the same reason -- the old window's copies are consumed by `amBody`.
- Old-window cells (`Hp7`/`Hp8`) are deliberately dropped: that limb is summed
  and the invariant does not mention it. `iProp` is affine, so this is sound.

### INTERACTIVE MODE WORKS HERE -- previous note retracted

The standing belief that `rocq_start` cannot replay these files was a
misdiagnosis of a fixable load-path problem, not a property of the files. The
repo root holds BOTH `_CoqProject` and `dune-project`; coq-lsp prefers dune,
and no dune stanza covers `case_study/RiscvPmp`, so under the dune workspace
this subtree gets NO load path and every `From Katamaran Require` silently
no-ops. Symptoms: "The reference Valuation was not found in the current
environment" on any `rocq_start` against a file here, and a preamble that
returns `success: true` having loaded ZERO Katamaran libraries.

Fix: `Example/_CoqProject` (untracked, 2 lines, `-Q ../.. Katamaran.RiscvPmp`
and `-R ../../../../theories Katamaran`) -- coq-lsp's detection stops at the
first directory holding a project file, and there is no dune-project there.
With it, `rocq_check` against the full tail context runs in 10 ms - 19 s.

Two caveats measured the same day:
- **Preamble mode reports success on a partial load.** A cold `rocq_start` with
  the whole heavy import block returned `success: true` with only Coq/stdpp/
  Iris present. ALWAYS `Locate` a name you expect before trusting a preamble.
  Building the context up with one `Require` per `rocq_check` works.
- `rocq_check` echoes the entire session's tactic history on every call, so
  deep in a session each step costs ~7k tokens regardless of what it does. For
  a self-contained sub-question, start a FRESH light session (Prelude only)
  rather than continuing in the heavy one.

### Still open

- Wire `am_loop` into the chain at `n = 1` (`sgL` -> loop -> `sgN`), i.e. the
  `tailChain` lemma. `sgL_post` is already the loop's entry shape.
- `ImplPre` + the Phase-5 bridge for a leakage theorem on the tail.
- The other ten segments: 12 cut assertions, a `Hif`/`Hef` each.
- **G (`br_divrem`, 31 trips) is now the interesting case**: it is the loop this
  machinery was built for, and unlike M it cannot be unrolled.
- Everything but the tail four still carries `asn_no_post`.

---

## Phase 4c — segment G (`br_divrem`, 31 trips) COMPOSED (2026-09-09)

**Status: `ZZMladDvLoop.v`, 20 `Qed`, no holes, compiles clean.**  G — the loop
this whole machinery was built for, and the one that cannot be unrolled — is now
a reusable loop-elimination lemma.  The tail (Phase 4b) exercised the machinery
on M, which runs only two trips at `mlen = 2`; G runs 31 and the executor still
sees the 27 instructions exactly once.

### What was missing and what was added

Both G contracts already existed as Phase-1 spikes with `asn_no_post`
(`ZZMladDvBody.v` = latch taken, `ZZMladDvFinal.v` = latch falls through to
offset 108).  `asn_no_post` proves "this segment runs and leaks nothing"; it
hands nothing to the next trip, so neither could be chained.  Added:

- `dvBody_post` — T4 pinned to `dvdec (term_var "k")` (= k-1) with its
  `secLeak`, the other ten registers re-havoc'd at their own publicness
  (`dv_regs` serves unchanged: T0/T6 public, T5 the pinned literal 1,
  q/hi/lo/S0..S3 secret), plus `minimal_pre`.
- `dvFinal_post` — `dvf_out_regs = (T4, true, PVExist) :: dvf_regs` plus
  `minimal_pre`.  T4 is deliberately NOT pinned at the exit: idx 162
  (`li T4, 32`, the *next* loop's initialiser) overwrites it immediately, so
  the weakest useful claim is "some public value" — which is exactly the shape
  sgH's `gen_pre_rel` precondition wants.

**Both VCs verified FIRST TRY**, 2.8 s and 3.7 s, with the unchanged
`intros; vm_compute; solve_vc; solve_symbase_fetch`.  `secLeak (k-1)` and
`secLeak (j+1)` come for free from `instprop_formula_secLeak_binop` (compositional
through `bvadd`, literal on the other side) — no new solver work was needed.

### The rotated-loop indexing (get this wrong and the trip count is off by one)

    idx 132 (byte 528)  li   T4, 32          <- segment F leaves the counter
    idx 135 (byte 540)  addi T4, T4, -1      <- LOOP HEAD decrements
    ...
    idx 161 (byte 644)  bltu T5, T4, -104    <- LATCH, back-edge to 540,
                                                taken while 1 <u T4
    fall-through -> byte 648 = idx 162       <- segment H

The head value (PRE-decrement) runs 32, 31, …, 2 — **31 head visits**, of which
visits 1..30 take the back edge and visit 31 exits.  Post-decrement that is
k = 31, 30, …, 1, i.e. the C loop's `for (k = 31; k > 0; k--)` exactly.
So `dvInvN ia F n` carries T4 = n + 2, and the entry state is `dvInvN ia F 30`
(30 `dv_step`s + one `dv_exit`).  `dv_loop_31` is that instance.

### THE reusable shape — parametric in BOTH frame and continuation

    Lemma dv_loop (ia : N) (Hrep …) (Hlen …) (F Post : iProp Σ)
      (Hcont : dvOut ia F -∗ myWP2_loop Post) :
      forall n, dvInvN ia F n -∗ myWP2_loop Post.

This is the piece worth reusing verbatim for the other four loops.  Two
decisions make it drop-in:

1. **The frame `F` is an OPAQUE `iProp Σ`.**  G touches eleven registers and NO
   memory, so A0-A7 / X2 / the whole x[]/m[]/stack block are what actually ride
   in `F` — but nothing in the file knows that.  Verified in the proof: after
   the `iApply`, `HF : F` sits untouched in the continuation goal.  Contrast
   Phase 4b, where the out-of-contract resources were a concrete `cellsPriv`/
   `cellsPub` fixpoint because M's footprint genuinely slides.  **When a loop's
   footprint is fixed, use an opaque frame; the range fixpoint is only for
   sliding footprints.**
2. **The continuation `Post` is a parameter, discharged by `myWP2_loop_bind`.**
   So G does not mention segment H, and the same lemma serves the eventual full
   chain and any standalone use.  Compare `am_loop`, whose conclusion is
   hardwired to `exitCond_WP2_loop (sgN_exitCond ia)` — fine there because N is
   the last segment, useless for a mid-function loop.

`dvOut ia F` is spelled as `asn.interpret dvFinal_post` at the exit valuation,
so `dv_exit`'s continuation obligation is *literally* what the soundness bridge
hands back and closes with one `iFrame`.  Worth copying: it removes an entire
class of reduction fighting.

### Method notes that generalise

- **The counter lives as a PURE side condition, not inside the bitvector.**
  `dvInvN` existentially quantifies `kv : N` with `⌜kv = N.of_nat n + 2⌝`, the
  amInvN trick.  Baking `N.of_nat n` into `bv.of_N` directly would force
  `N.of_nat (S k)` to reduce (to `N.succ …` / `Pos.of_succ_nat`), which no `cbn`
  setting normalises usefully.  With the side condition, `assert (kv = (N.of_nat
  k + 2) + 1) by lia` puts it in exactly the `m + 1` shape the decrement lemma
  wants.
- **A no-wrap bound must be carried too**: `⌜kv + 1 < bv.exp2 xlenbits⌝`.  It is
  used in exactly ONE place — the latch's `bv.ult`, via `bv.bin_of_N_small` —
  because `kv = n + 2` alone says nothing about wrapping for an unbounded `nat`.
- **The decrement is unconditional at the bv level.**  `dv_dec (m : N) :
  bv.of_N (m+1) + bv.of_N 4294967295 = bv.of_N m` needs NO hypothesis on `m`:
  `(m+1) + (2^32-1) = m + 2^32`, and `bv.of_N 4294967296 = bv.zero` at width 32
  by `vm_compute`.  Route: `rewrite bv.of_N_add` (collapse), `replace` the
  N-level sum, `rewrite <- bv.of_N_add` (SPLIT it back the other way — the same
  lemma both directions), then `bv.add_zero_r`.  133 ms.  A first attempt via
  `bv.of_N_Proper` + `bv.eq2n` died because `bv.truncn` is not `N.modulo` (it
  matches on `N.pos` and calls `bv.trunc`), so no `N.Div0.*` lemma applies.
- **`cbn [dv_reg_asn dv_post_reg_asn]` + `reg_reduce` + `cbn`, in that order.**
  Same convertible-but-not-syntactically-equal wall as Phase 4b, same fix.  The
  eleven `rc_*` equations (T0→x5, T1→x6, T2→x7, T3→x28, T4→x29, T5→x30, T6→x31,
  S0→x8, S1→x9, S2→x18, S3→x19) are each `vm_compute; reflexivity`; `cbn` will
  not touch `reg_convert` at any delta setting.  The trailing whole-goal `cbn`
  is safe ONLY after the 282-entry instruction store has been framed away.
- **`dvWinAsn` nests the register block one level deeper** than the contract's
  precondition does (`… ∗ dv_pre_regs …` vs the flattened `… ∗ regT0 ∗ … ∗ ⊤`),
  so the `iDestruct` pattern needs an inner group:
  `"(Hw1 & Hw2 & Hw3 & (Hr1 & … & Hr11) & Hw5)"`.  Flattening it as sixteen
  atoms silently mis-binds.
- **divrem_ctx and dvfCtx are two definitions with identical bodies** (as are
  divrem_iota/dvfI, dv_pre_regs/dvf_pre_regs, dv_reg_asn/dvf_reg_asn).  `dv_exit` mixes
  them — the invariant is at divrem_ctx, dvFinal's contract at dvfCtx — so BOTH must
  be unfolded before `iFrame`.  Once reduced to `x5 ↦ᵣ …` the two sides match
  term-for-term.
- At the concrete `kv = 2` of the exit, pc-eq AND the negated guard both simply
  **compute**: `repeat iSplit; try done` closes them, no `dv_dec` needed.  Only
  the symbolic body needs the rewrite.
- Interactive mode carried the whole file: `rocq_start(theorem=…)` reached
  `dv_step`, `dv_exit`, `dv_loop` and `dv_loop_31` in this HEAVY Iris file
  without timing out, and each proof step ran in 30 ms – 7 s.  Total interactive
  cost for all four proofs was well under a minute; the confirming full compile
  was paid once.  (Phase 4b's note that file/theorem mode was unusable here no
  longer holds — that was before `Example/_CoqProject` landed.)

### What G does NOT yet give

- **No F ; G ; H chain.**  `dv_loop` is the loop-elimination step; wiring it
  needs `sgF_post` extended to establish `dvInvN ia F 30` (with `F` instantiated
  to sgH's precondition minus G's eleven registers) and `sgH`'s precondition met
  by `dvOut`.  That is the same per-cut work the other eleven segments need, not
  new machinery.
- **No leakage theorem for G alone.**  `ImplPre` + the Phase-5 bridge are still
  open, exactly as for the tail.
- The three remaining loops (D memmove 6 instrs, I limb-accumulate 29, K
  `br_i31_add` 13) should now be near-mechanical: each needs its Body/Final
  posts plus a copy of the `dv_loop` shape.  D/I/K all have SLIDING memory
  footprints, so they need Phase 4b's cell-range fixpoint rather than G's opaque
  frame — G is the only register-only loop of the five.


# ========================================================================
# THE REPEATABILITY GOAL (2026-09-14)
# ========================================================================

Everything above treats muladd as the target. This section restates the target
as the thing that actually matters — **a whole-function proof whose cost is
linear in segments, with a per-segment cost that is mostly mechanical** — and
re-orders the remaining work by that criterion rather than by segment index.
muladd is then the 14-segment instance that demonstrates it, not the goal.

## §R0. The claim we are trying to be able to make

> For a function cut into `n` segments, verifying it costs `n` × (a small
> mechanical part + one genuine specification decision per cut), and neither
> part grows with `n`.

Three things have to hold, and they are separable:

1. **Per-segment cost does not grow with program size.** This is §0's bet. It is
   the reason cutting works at all, and it is the one thing that makes a LARGER
   program tractable rather than merely longer.
2. **The mechanical part is actually generated**, not re-typed per segment.
3. **The specification part is small and local** — one statement per cut about
   what that cut hands the next segment.

## §R1. Honest stock-take

**(1) is the weakest-evidenced of the three, and the plan has been overstating
it.** §0 cites `ZZSegTrimP` (339 M words / 15 s for a mid-program cut) — but the
RESULTS section then records that `ZZSegTrimP`'s goal is VACUOUS. It evidences
that a cut is cheap to *state*, not that a real one is cheap to *prove*. The
non-vacuous data points are segment G composed at its real 31 trips, and the
tail `sgL;M;sgN`. **Neither has been priced as a per-segment cost.** Until a
non-vacuous per-segment number exists across at least two segment sizes, "cost
is linear in segments" is a hypothesis, not a result.

**(2) is largely done for LOOPS and not started for the CELL TRADE.**
`PLAN-loop-automation.md` phases C and D landed 2026-09-14:

| piece | state |
|---|---|
| six `LoopSpec` CFG fields + the counter step | derived from the instruction list (C1) |
| the latch obligation | three bullets from an anchor and a stride (C2) |
| the trip predicate and its `_mono` | generated from an axis list (C3) |
| back edge: counter at `S n`, the step, counter at `n` | derived (D2) |
| back edge: walking registers | one lemma, one call shape, all eight in the tree (Hw) |
| segment table obligations | `gen_seg_*_table_ok`, discharged once (A1') |
| back edge: **the cell trade `Hc`** | **hand-written per loop — the gap** |

**(3) has barely started.** Most straight-line segments still carry
`asn_no_post`, i.e. they prove nothing to hand on. Only the tail chain and G are
composed; there is no F;G;H chain and no leakage theorem for the whole function
or for G alone.

## §R2. Machinery vs specification — the distinction that decides the order

**Machinery (amortises across programs; worth generating):**

- **M1. The cell trade `Hc`, and the cell-range fixpoint behind it.** The last
  hand-written back-edge premise. It blocks three of muladd's five loops: D
  (memmove), I (limb-accumulate) and K (`br_i31_add`) all have SLIDING memory
  footprints and need Phase 4b's cell-range fixpoint rather than G's opaque
  frame. G is the only register-only loop of the five, which is exactly why it
  is the one that got composed first — it is the easy case, and generalising
  from it is the trap §5 warns about.
- **M2. The per-cut *plumbing*** — `ImplPre` instantiation and the Phase-5
  bridge. Machinery exists (`cfg_instrs_verified_composed`, `gen_implpre`); what
  is missing is applying it, once per program.

**Specification (per-program; NOT generatable, and should stop being treated as
a backlog item):**

- **S1. What each cut promises the next segment.** Nine straight-line cuts here.
  `gen_seg_contract` makes these cheap to *state* and (since A1') discharges
  their table obligations for free, but nothing can decide what a cut says. This
  is the irreducible cost, and it is proportional to the number of cuts — which
  is the argument for cutting on C-function and loop boundaries, as §1 does,
  rather than for cutting sparingly or often.

## §R3. Revised order

1. **M1 — the cell trade.** Highest repeatability payoff of anything left: it is
   the last generatable piece of the loop layer, and it unblocks 3 of 5 muladd
   loops. Do it against D (memmove, 6 instructions) — the smallest sliding
   footprint in the program — then check it covers I and K without special
   cases. If it needs a special case per loop it is not machinery and should be
   re-scoped.
2. **PRICE A SEGMENT, non-vacuously.** Before writing nine more cut contracts,
   measure what one real cut costs to prove, at two different segment sizes.
   This is the missing evidence for §R0(1), and it is cheap now that G and the
   tail exist. If the per-segment cost turns out to grow, the whole segment-count
   plan needs revisiting and it is much better to learn that at segment 3 than
   at segment 14.
3. **S1 — the cut postconditions, in dependency order.** F;G;H first, since G is
   already composed and its neighbours are the shortest path to a second
   composed chain. Then J;K, then the rest.
4. **M2 + promote.** `ImplPre`, the bridge, and Phase 6 (out of `ZZ*` into
   tracked files, `_CoqProject`, `Results.v`, the gate allowlist).

Steps 1 and 2 are the ones that generalise. 3 and 4 are what makes muladd
specifically finish.

## §R4. The second-program test

Repeatability cannot be claimed from one program. `check_scalar` is the existing
second data point (whole-function N=2/4/8 with a real `Qed`, see
`PLAN-check-scalar-full.md`). **The test for this whole line of work is whether a
loop in `check_scalar` can be brought up on the phase-C/D machinery without
adding a case to it.** That is a cheap experiment and it should be run once M1
lands, not after muladd finishes — a machinery gap found on a second program is
worth more than another muladd segment.

## §R5. Banked, so it is not re-derived

**Converting the four composed examples onto `gen_seg_contract` was attempted
and reverted 2026-09-14, with results worth keeping:**

- The **contract side converts cleanly**: `PaddedLoop.v`'s two contracts became
  `gen_seg_contract` applications and BOTH VCs still discharge with the
  identical `vm_compute. solve_vc.` — including with the exit condition
  strengthened from `pcOutOfInstrs_exitCond` (any pc past the code) to the exact
  return address.
- The uniformity payoff is real: `pl_itable`'s 16 hand-written lines applying
  `itable_faith_of_segment` — whose comment was entirely about `@`-argument
  order — collapse to a 3-line `gen_seg_instr_table_ok` application.
- The cost is the `*Result.v` side: the precondition gains a `gen_base_bound`
  conjunct and a trailing `⊤`, so each `ImplPre` framing chain needs rework, and
  the `Hex` destructuring changes with the exit condition. ~30 lines of brittle
  `iSplit`/`iFrame` churn per contract, ×10 contracts across 8 files.
- **`GenSegment` is safe to import into a light `Example/*.v`**: measured +1.8 MB
  peak and no extra time on `PaddedLoop.v`. CLAUDE.md's 1.2 GB light-branch
  invariant is about the Iris MODEL (`SpecIris`/`VerifierRel`/`Adequacy`), which
  `GenSegment` does not require. `GenCompose` does, so that one is genuinely
  heavy.

It was reverted because it is polish on machinery that already works, while M1
blocks three loops. Resume it when the segment path needs to be demonstrated
uniform, or fold it into step 3 as each example gets a real postcondition.


# ========================================================================
# §R6. M1 LANDED -- the cell trade (2026-09-14)
# ========================================================================

§R3 step 1 is DONE.  `GenCompose.v` gains 13 items (commit below); the
falsification test the step set itself -- "check it covers I and K without
special cases, and if it needs a special case per loop it is not machinery" --
was run and **passed for 3 of 3 sliding loops**, but only after two genuine
design changes that the D-only version would have hidden.

## What `Hc` turned out to be

A **pure permutation**, and that is the headline.  With the frame

    Fr n := loop_carry A iota q N n  ==  loop_reservoir A iota q n
                                         ∗ loop_completed A iota q n N

the back edge's cell obligation is: peel trip n's cells off the reservoir
(`loop_reservoir_peel`), push trip (S n)'s finished cells onto the done block
(`loop_completed_push`), re-index the post's `an`-shaped cells to `a`-shaped
(`gen_cells_drop_exit_pc`) -- and the two sides are then literally the same
resources.  `loop_cells_trade` is four rewrites and an `iFrame`.

It carries NO arithmetic and NO per-loop content, works for any `cs` of any
length at any publicness, and its only side condition is `n < N`, which every
back edge satisfies by construction (entry at trip N, edges at n = N-1 … 0).
That is what makes it machinery rather than a per-loop obligation.

`loop_carry_exit` is the point of the whole exercise: at trip 0 the reservoir
is empty and the done block is every trip the body ran, i.e. **the array the
loop wrote, handed back to the caller**.  Every loop before this dropped it.

## The two things D alone would NOT have found

Both were caught by actually instantiating I and K, not by inspection.

1. **A public cell is not a special case, it is a MISSING BRANCH.**  D's two
   cells are both private; I, K and M each have one PUBLIC cell (`mw`, carrying
   `secLeakvar`) alongside a private one.  The first cut required
   `cell_is_public c = false` and so covered D only.  But publicness is already
   a field of `cell_spec`, so the fix was to make the reservoir's per-cell
   resource branch on it (`mem_cell : bool -> bv -> iProp`) plus a public twin
   of `asn_cell_inst`.  `mem_cell false` IS `mem_word`, by conversion, so
   nothing existing moved.  **Rule of thumb this confirms: when a generator
   takes a record, every FIELD of that record needs a branch before the
   generator is finished -- "the examples I have don't use it" is how a missing
   branch gets mistaken for a special case.**

2. **The per-cell address had to become a PROJECTION.**  `loop_carry_cells`
   originally asked the caller for `addr : nat -> cell_spec R -> bv`.  Fine for
   D (one base), but I and K each walk TWO INDEPENDENT bases, so writing that
   function by hand means matching on which cell -- exactly the per-loop
   special-casing this layer exists to delete.  Reading the address off the
   trip valuation instead (`cell_addr_of i c`, matching `addr_off`'s own
   zero-offset convention via `cell_addr_at`) makes it a projection, and what
   is left for the caller is ONE side condition per LOOP:

       cell_base_sync : every cell's base is a public (SyncVal) address

   discharged by a single `repeat constructor; eexists; cbn; reflexivity`.
   This is the SAME move as "iota is a projection off LoopSpec fields" from the
   segment-generator spikes, arrived at independently.  Worth treating as a
   general rule for this codebase: **if a generator's caller-supplied function
   would have to match on the data, the function is a projection.**

## The uniformity evidence

`Example/ZZCellTrade.v` (untracked probe, compiles clean with the project's own
flags; 12 lemmas verified present in the `.vo`).  D, I and K each get the same
four items -- `_bases_sync`, `_entry`, `_Hc`, `_exit` -- with **byte-identical
proof scripts**.  The only per-loop text is the data: its cell list and its trip
valuation, both transcribed from the segment's own VC contract
(`ZZMladMvBody.v` / `ZZMladLimbBody.v` / `ZZMladAddBody.v`).

    D  memmove      "sw" @ dp-4 (priv), "dw" @ dp   (priv)   ONE base
    I  limb-macc    "xw" @ xp   (priv), "mw" @ mp   (PUB)    TWO bases
    K  br_i31_add   "xw" @ ap   (priv), "mw" @ bp   (PUB)    TWO bases

## What this does NOT yet show

Stated plainly, because §R1 already had to retract one "cuts are cheap" claim
that rested on a vacuous goal:

- These are the CELL half of each loop's back edge only.  None of D/I/K has its
  full `LoopSpec` / `loop_back_edge_std` instance yet -- `Hc` is now free, the
  other nine premises are not.
- Nothing here is priced.  §R3 step 2 (price a segment non-vacuously at two
  segment sizes) is unaffected and is still the next thing.
- `loop_reservoir_words` (the one-cell form) is kept rather than replaced, since
  `ZZLoopTransCheck2` uses it; `loop_reservoir_cells` is its generalisation.

## Method note that cost real time

`make ... | tail` reports **tail's** exit code, not make's.  A failed
`GenCompose.v` build was read as green that way and the stale `.vo` looked
plausible because an EARLIER successful build had left one.  Same false-green
class as the two already in `feedback_rocq_workflow`, but self-inflicted.  Check
`$?` on the make itself (or `set -o pipefail`) AND confirm the new name is in
the artifact with `strings <file>.vo | grep <newname>`.

The build failure itself is worth recording: `GenCompose.v` has **no
`Import asn.notations`** (unlike `GenSegment.v`), so `(A ∗ B)%asn` does not
parse there -- write `asn.sep A B`.  Three sites.


# ========================================================================
# §R7. STEP 2 DONE -- a cut postcondition is free to prove (2026-09-14)
# ========================================================================

Full record: `diagnostics/segment-postcondition-cost.md`.

## Step 2 was HALF ALREADY ANSWERED, and the half that was missing was the
## one that mattered

§R3 step 2 asks to price a segment "at two different segment sizes". A sweep of
`diagnostics/` and of this plan's own tables found the SIZE axis already
measured at FIVE sizes (D/M/K/G/I, Phase 2 above), post-`cfdcc92f`,
post-`7e5ceffe`, post-`cbn` — so running it again would have re-derived an
existing result. What no record contained was §R1's actual worry: **cheap to
STATE versus cheap to PROVE**. That is the postcondition-strength axis, and it
is what got measured instead.

## The finding

One token changed -- the contract's postcondition field -- in two otherwise
byte-identical files, `sed`-generated so nothing else can differ, same
`Proof. solve_param_vc. Qed.` in both arms, same-session baseline:

| pair | segment | real post | `asn_no_post` | ratio |
|---|---|---:|---:|---:|
| M | `br_i31_sub` body, 13 instrs | 162.41 M | 161.53 M | **1.0054x** |
| L | segment L, straight-line, 14 instrs | 190.75 M | 186.80 M | **1.0212x** |

**0.5-2.1%.** For scale, the `Qed`/`Admitted` protocol gap is 1.81x. A cut
postcondition is free to discharge; the cost of a segment is executing its
instructions, which is paid whether or not you cut there.

**This closes §R1's objection for the postcondition axis.** It does NOT close
§R1 entirely -- see "still open" below.

## A retraction of my own, same day

I read the Phase-2 QED table as NET and concluded "per-segment cost is almost
size-independent, 1.42x over a 4.8x size range, hence constant-dominated". Those
figures are **GROSS**; the 1.42x was the import closure. Net, the spread is
**5.6x over 4.8x** -- cost is roughly PROPORTIONAL to segment size,
`~ -14 + 12.76 M words/instruction`, and the table now carries the protocol note
it was missing. The law is LOOSE: held-out L is +13.7% and G is -35.2%, G being
the only segment with no memory cells, so part of the slope is cell inventory
rather than instruction count.

## What this changes for the plan

- **§R0(1)'s cost model, corrected: cost tracks INSTRUCTIONS, not CUTS.**
  Verifying a program in `n` segments costs about what those instructions cost
  in one piece, however `n` is chosen. So segment count is nearly free and
  should be chosen for PROOF CLARITY -- which is independently where
  `composition-payoff.md` landed post-`cfdcc92f` ("cut where it makes the proof
  clearer"), reached from the other direction.
- **Step 3 (the nine cut postconditions) is de-risked on the cost side.** Its
  cost is design effort, not machine time. That was the open question gating it,
  and it is answered; S1 remains irreducible but is no longer a cost risk.
- **STILL OPEN, and it is the other half of §R0(1):** the **Iris-level
  COMPOSITION** cost -- chaining segments in `ZZMladTail.v` and through the
  Phase-5 bridge -- is a different pipeline from the VC cost priced here, and
  nothing prices it for a chain longer than the three-segment tail. If a
  superlinearity in segment count exists anywhere, that is where it is. Price it
  when the F;G;H chain exists, i.e. during step 3, not before.


# ========================================================================
# §R8. §R2's machinery/specification LINE IS IN THE WRONG PLACE (2026-09-14)
# ========================================================================

§R2 classified **S1, the cut postconditions, as irreducible specification:**
"nothing can decide what a cut says … This is the irreducible cost, and it is
proportional to the number of cuts."

**That is wrong as stated, and `ZZSpikeEnter2.v` (2026-09-14) is the
counter-example.** Its header states the principle:

> a cut assertion is determined by its SUCCESSOR's precondition, so it should
> be GENERATED from it … `sgL_post` is not bridged to -- it is deleted.

An earlier spike (`ZZSpikeEnter.v`) did it the §R2 way -- hand-write the cut
assertion, then reconcile it against the successor's invariant resource by
resource. Fifteen cross-context `iApply`s, and it **did not finish in 4.5
minutes**. `loop_entry_by_subst` (GenCompose) replaces the whole activity: the
cut assertion IS the successor's precondition transported along one
substitution, and the entry obligation collapses to a **valuation equality**
(`subword_cut_valuation`) closed by `cbn; repeat f_equal; rewrite ?bv.of_N_add;
lia` -- no separation logic at all.

## Where the line actually falls

- **GENERATABLE**: the cut assertion's RESOURCE CONTENT. It is the successor's
  precondition, re-based. Nothing per-cut to invent.
- **IRREDUCIBLE**: the ARITHMETIC relating predecessor to successor -- which
  trip the loop starts at, how the predecessor's pointers relate to the loop's
  walking variables. In `ZZSpikeEnter2` that is the substitution plus a
  half-dozen `lia` lines, and it is FORCED by the program, not chosen: the loop
  head is p+1056, sgL hands over bp = p+1144, and `subword_iota`'s
  `bp(n) = pe - 4*(n+1)` then PINS n = 1.

So the per-cut cost is a substitution and an arithmetic reconciliation, not a
20-conjunct assertion. §R2's "proportional to the number of cuts" survives; its
"nothing can decide what a cut says" does not.

## Consequence for §R3 step 3

Step 3 should be executed as *"for each cut, write the substitution and its
valuation equality"*, following `ZZSpikeEnter2.v` as the precedent -- NOT as
"write nine postconditions", which is what §R2's framing implies and what the
4.5-minute spike actually tried.

Two things that make F;G;H the right first instance, both confirmed 2026-09-14:

- **F and H both `Qed`** (see the Phase 3 supersession note above), so the
  chain's endpoints are sound.
- **G is already on the `LoopSpec` machinery** -- `divrem_spec : LoopSpec
  divrem_ctx` (`ZZDvLoopSpec.v`) with its loop theorem in `ZZDvLoopThm.v` -- so
  F->G is structurally the SAME enter that already works for M, with
  `divrem_spec` in place of `subword_spec`.

And `subword_entry` hand-rolls at n=1 exactly what §R6's `loop_carry_entry`
now packages, so the two strands meet at the enter.


# ========================================================================
# §R9. THE F -> G CUT, stage 1 -- PROVED and FALSIFIED (2026-09-14)
# ========================================================================

`Example/ZZEnterFG.v` (untracked). First instance of §R3 step 3 executed the
§R8 way -- generate the cut assertion from the successor, do not write one.

## The cut is FOUR LINES

    Definition divrem_cut_subst : Sub (divrem_ctx ▻ "a") (["p"] ▻ "a" ▻ "an") :=
      [env].["q" ↦ PO 540]                            (* G's head, base-relative *)
           .["k" ↦ term_val ty_xlenbits (bv.of_N 32)] (* the counter at entry    *)
           .["a" ↦ term_var "an"].                    (* G's entry pc IS F's exit *)

and F's postcondition becomes
`asn.sep (subst (gen_loop_at_head (divrem_spec (ia+540))) divrem_cut_subst) sgF_rest`.
No hand-written assertion; `valid_sgF'` is `solve_param_vc`, one line.

G is the register-only loop, so this is the SIMPLEST of the five enters:
`divrem_ctx` is just `["q";"k"]` and there is no reservoir substitution at all,
where L->M needed a second one for its sliding window.

## The entry arithmetic is FORCED, which is the repeatability point

F's last three instructions are `li T4,32` / `li T5,1` / `li T6,1` (idx 132-134;
idx 135 is G's `loop_first_instr`). `divrem_iota`'s `k(n) = n+2` then PINS
**n = 30** -- independently the same 31 head visits (32,31,...,2) §1 derives
from the listing. Nothing about this cut was a free choice, which is exactly
what §R8 predicts: the resource content is generated, and the arithmetic is
dictated by the program.

## NON-VACUITY: FALSIFIED, not assumed

One token changed, `bv.of_N 32` -> `bv.of_N 31` in the substitution
(`ZZEnterFG_bad.v`):

| arm | result |
|---|---|
| `k = 32` | **Qed** |
| `k = 31` | **`No applicable tactic`** |

So the generated postcondition is genuinely checked and `valid_sgF'` is not
passing on an unsatisfiable precondition. **Do this for every cut** -- it is one
`sed` and one compile, and it is the only thing separating "the cut is proved"
from "the cut typechecks".

## One gap closed by existing work

`dvs_regs` needs **T0 public** ("d = b0, from the public modulus") and F's
original precondition used `mlad_reg_specs_rel`, which marks it private -- the
same publicness issue that broke the six segments. `mlad_reg_specs_cut` (landed
09-13) already marks T0 public, so F simply moves onto it, as the other eight
straight-line segments already have. **A cut's precondition wants the CUT
spec, not the ENTRY spec** -- worth stating as the rule.

## Stage 2, and the machinery it needs

This file sets `sgF_rest := ⊤`. Dropping resources only weakens a
postcondition, so stage 1 is exactly "does F establish G's entry state?" with
nothing else in the way -- and it does. Stage 2 must carry what G never touches
but H needs: the memory block and A0-A7/X2.

**BLOCKER, and it is a MACHINERY gap rather than per-cut work:**
`gen_mem_pre_rel` is hardwired to `Assertion (["p"] ▻ "a")` (GenContract.v:381),
so it cannot be used in a postcondition at `... ▻ "a" ▻ "an"`. The register half
has a Σ-generic builder -- `gen_regs_any` (ZZMladCommon) takes the base as a
`Term Σ` and works at any context -- but the memory half has NO analogue, which
is why `sgL_carry` spells its four cells out by hand. `mlad_mem_specs_rel` is
x ++ m ++ stack, so spelling it out per cut is both long and per-cut.

**Next machinery item: a Σ-generic `gen_mem_any`, the memory twin of
`gen_regs_any`.** Every cut that carries memory across it needs one, so it
amortises exactly like §R6's cell trade; without it, step 3's remaining cuts
each pay a hand-written cell block.


# ========================================================================
# §R10. F -> G STAGE 2 DONE, and the memory carry now GENERATES (2026-09-14)
# ========================================================================

§R9's blocker is closed and the F -> G cut is complete.

## The blocker, and why it was real

`gen_mem_pre_rel` is hardwired to `Assertion (["p"] ▻ "a")`, so it cannot appear
in a postcondition at `... ▻ "a" ▻ "an"`. The reason there was no Σ-generic twin
is structural, and worth keeping:

- `gen_reg_asn_any` takes a `Term Σ` and gets away with it because its `PVExist`
  branch **never mentions the base inside the existential** (`r ↦ᵣ term_var "v"`);
  the base appears only in `PVBaseOff`, which has no binder.
- `gen_mem_asn_rel`'s `PVExist` branch uses the base **inside** the binder
  (`p + k ↦ₘ term_var "mv"`), so a `Term`-taking version must weaken it, and the
  only weakening available is `subst _ sub_wk1` -- a recorded Θ(|Σ|²) driver and
  opaque to `iFrame`. **GenSegment §4 declined to build it for exactly this
  reason.**

§5 is the way through and `cell_spec` already used it (name + In-proof,
re-derived with `ctx.in_succ`). So the fix was to FINISH `cell_spec`, not to
write a new builder: `cell_value : option (Val ty_xlenbits)`, because two of
muladd's ten declared cells are `PVConst` and the builders could only express
existential ones. Commit `d0a84fc5`.

**A constant cell has NO BINDER**, hence one fewer `ctx.in_succ` -- which is why
this is a field rather than two record types, and why every consumer branches
rather than forwarding it. `loop_cells_trade` (§R6's `Hc`) needed no change: a
permutation is indifferent to what a cell contains.

## Acceptance, in the strong form §5 specifies

    Lemma mlad_mem_cells_faithful :
      gen_cells_pre mlad_mem_cells = gen_mem_pre_rel mlad_mem_specs_rel.
    Proof. reflexivity. Qed.

All ten cells, CONVERTIBLE with the hand-written block rather than merely
provably equal -- which is what keeps `iFrame` working downstream. The same data
then builds `gen_cells_post` at the context `gen_mem_pre_rel` cannot reach.

## Stage 2: F's postcondition is G's entry state PLUS a real carry

`sgF_rest` is now the pinned exit, the program bound,
`gen_regs_any (term_var "p") sgF_rest_regs`, and
`gen_cells_post mlad_mem_cells`. `valid_sgF'` is still ONE `solve_param_vc`.

The register split is DETERMINED, not chosen: G's `dvs_regs` consumes T0-T3,
T5, T6, S0-S3, plus T4 as counter and `"q"` as base, leaving exactly A0-A7 and
X2.

## NON-VACUITY: one arm PER HALF, and stage 1's single check was not enough

A bigger postcondition is exactly where an obligation can quietly stop being
enforced, and stage 1 could not have caught a vacuous carry because there was
none.

| arm | one token changed | result |
|---|---|---|
| `ZZEnterFG_badk` | entry counter 32 → 31 | **fails as required** |
| `ZZEnterFG_badr` | carried `A0` `PVBaseOff` 1128 → 1124 | **fails as required** |

So BOTH halves are genuinely checked. **Rule for the remaining cuts: one
falsification arm per independent half of the cut assertion, not one per cut.**

## Next

- **G -> H**, the same shape in the other direction: `dvs_out` meeting H's
  precondition. H already `Qed`s independently.
- **Then price the Iris-level composition** (§R7's open item). F;G;H is the
  first chain long enough to show segment-count superlinearity if it exists,
  and that is a different pipeline from the VC cost §R7 measured.

## Promotion risk, worth naming now

`ZZMemCells.v`, `ZZEnterFG.v` and the falsification arms are UNTRACKED probes.
`mlad_mem_cells` is now the single definition of muladd's memory layout used by
a real cut, and `mlad_mem_cells_faithful` is the ONLY thing tying it to the
tracked spec -- and it lives in an untracked file too. **When Phase 6 promotes
this, that lemma travels first.**


# ========================================================================
# §R11. D's WINDOW -- the reservoir needs DISJOINT trips, and D has not
#       (2026-09-14)
# ========================================================================

Attempted §R3-step-3's "risky items first" on **D** (memmove, 6 instructions),
chosen for being the smallest sliding loop. **Wrong axis: D is the HARDEST of
the four, not the easiest**, and the reason is worth recording because it is
invisible in every check §R6 ran.

## The unstated assumption in `loop_carry`

`loop_reservoir A iota q n` is `[∗ list] i ∈ seq 0 n, A@(iota i)`. If two trips'
cells share an address that separating conjunction is **`False`** -- so
`loop_carry_cells` still PROVES, from a premise no caller can supply. Vacuous,
not unsound, and it would have passed every test in §R6.

**Mechanical criterion, checkable from the cell list alone: two cells sharing a
base variable whose offsets differ by a multiple of the walk step overlap across
trips.**

| loop | cells | same base? | trip n vs n+1 |
|---|---|---|---|
| D memmove | `sw@dp-4`, `dw@dp`, step −4 | **yes** | **OVERLAP** |
| I limb-macc | `xw@xp`, `mw@mp`, step +4 | no | disjoint |
| K `br_i31_add` | `xw@ap`, `mw@bp`, step +4 | no | disjoint |
| M `br_i31_sub` | `xw@ap`, `mw@bp`, step +4 | no | disjoint |

**Only D**, because it is an in-place shift: source and destination are the same
array one word apart. I/K/M read and write DIFFERENT arrays, so their footprints
slide in parallel and never meet.

**Scope note on §R6:** `ZZCellTrade.v`'s `mv_*` lemmas for D are all TRUE and the
uniformity result for the TRADE stands. What they do not establish is that D's
reservoir is INHABITABLE. "The trade is uniform" and "the loop can be entered"
are different claims and §R6 only made the first.

## The design that does work, and the one piece of it that is proved

Split the loop's FOOTPRINT from the reservoir's UNIT:

- reservoir unit `A` := ONE cell (offset 0) -- what each trip newly acquires
- the loop's window := TWO cells (offsets 0 and −4)
- frame at trip `m` := `reservoir (m−1) ∗ completed (m, N)` -- one cell already
  peeled forward into the window

The back edge is then three steps:

1. **retire** the written cell -> `loop_completed_push` (existed)
2. **carry** the shared cell, described with offset −4 at trip `S n` and offset 0
   at trip `n` -- two names for one address -> **`gen_cell_shift`, PROVED and
   landed**, the cell analogue of `walk_step_ok`
3. **acquire** the next cell -> `loop_reservoir_peel` (existed)

## Why that is still not enough: the extra must be TRIP-DEPENDENT

D writes `dp(N)…dp(1)` and reads `dp(N−1)…dp(0)`: **N trips, N+1 cells.** At the
head of trip `m` the window is `{dp(m), dp(m−1)}`; at trip 0 the body never runs
and the window is `{dp(0)}` alone. A uniform width-2 extra makes the exit state
claim `dp(0)−4`, one cell below everything the loop touches -- and no
re-indexing discharges it: the last back edge (1→0) would have to ACQUIRE from
trip −1. Pre-loading that cell into the constant carry does not help either,
because then trip 0 acquires from the carry while every other trip acquires from
the reservoir, which is non-uniform again.

**`LoopSpec` cannot express a trip-dependent extra.** `loop_body_contract` and
`loop_final_contract` both go through `gen_loop_contract ls …`, and
`loop_invariant` carries the single `gen_loop_at_head ls` at EVERY trip. Making
it trip-dependent touches `gen_loop_at_head`, `loop_invariant`, both trip lemmas
and the transfer lemmas -- the core, not the periphery. **An earlier note in this
session proposing "just give the final contract its own extra" is RETRACTED: the
final contract cannot differ in isolation.**

## Decision: PARK D, do K next

- **3 of the 4 sliding loops need none of this** -- I/K/M are disjoint and the
  existing `loop_cells_trade` applies unchanged.
- K validates both genuinely untested paths (`loop_runs` on a sliding loop, and
  the reservoir at a REAL trip count) without also paying for a core change.
- D's shape -- an in-place overlapping shift -- may want a different invariant
  altogether ("the array with its first k words already shifted", as one block)
  rather than a sliding window. Decide that after seeing K and I, not before.

`gen_cell_shift` is landed regardless: any overlapping-window design needs the
carry step, and it cost one lemma.


# ========================================================================
# §R12. K's BACK EDGE -- the first sliding loop on the generated machinery
# ========================================================================

`Example/ZZAddkSpec.v` + `Example/ZZAddkLoop.v` (untracked). §R11 chose K to
validate the two untested paths. **Path 1 -- a sliding-footprint loop's back
edge -- is DONE, no holes.**

## What transferred without change

K is the `add` mirror of the tail loop M, and every `LoopSpec` field came off
the listing: `T6`(ap) and `T5`(bp) both `+= 4`, `bne T5, S0` as the latch,
`sw S1, 0(T6)` writing x[] at `ap`, `lw S2, 0(T5)` reading m[] at `bp`.
`valid_addk_body` and `valid_addk_final` are `solve_param_vc`, first attempt.

The back edge mirrors M's field for field -- the counter through
`loop_back_edge_affine_down` (anchor/stride), the range bounds, and both walking
registers through `walk_step_ok`, INCLUDING the zero-step branch for the limit
register `S0`.

## THE PAYOFF, and it is the point of §R6

M's back edge spells the cell trade out in five tactic lines
(`loop_reservoir_peel`, `loop_completed_push`, `gen_cells_drop_exit_pc`,
destructure, `iFrame`). K's is ONE:

    exact (loop_cells_trade addk_cells (addk_iota iq pe ape)
             (@bv.of_N xlenbits iq) tot n Hlt).

and the frame is `loop_carry` directly, where M hand-wrote
`subword_reservoir_frame` as literally the same definition before the
abstraction existed. So §R6's `Hc` -- built against D/I/K as ISOLATED lemmas --
works inside a real `loop_back_edge` on a loop it had never been applied to.

## The one genuinely new obligation

K's `loop_dropped_facts` is NON-EMPTY where M's is `[]`: `ap ≠ bp`, the
x[]/m[] array disjointness that the hand-written `akBody` carries. First real
use of that field, and it needed content -- the goal reduces to a BITVECTOR
disequality, which `bv.bin_of_N_small` carries back to `N` where the no-wrap
bounds make both subtractions exact.

**Trap, comment left in place:** `rewrite A, B in H` is SSReflect-hijacked here
and is a *syntax error* (`[ltac_use_default] expected after [tactic]`), not a
tactic failure. Write the two rewrites as separate sentences.

## Method note

The intermediate version of this file carried a deliberate `admit` on that
bullet plus `Admitted`, purely to make the compiler PRINT the goal instead of
guessing its shape -- the "dump rather than guess" method this plan uses
elsewhere. It was labelled a scaffold when written and is gone: the file has
zero `admit`s and the lemma ends in `Qed`.

## Still open: path 2

**The reservoir has been TRADED but never INHABITED.** `loop_cells_trade` moves
cells across the back edge; nothing yet supplies `loop_reservoir` at a real trip
count. That needs `addk_place`, the trip bound, and `addk_loop_runs` (all direct
mirrors of M's), where the entry must build N cells via
`loop_reservoir_cells` -- the lemma from §R6 that still has no caller. M's own
enter (`ZZSpikeEnter2`) does it at `tot = 1`, peeling the single copy by hand,
so the N-copy path is genuinely untested.


# ========================================================================
# §R13. PATH 2 CLOSED -- the reservoir is INHABITABLE at any trip count
# ========================================================================

`Example/ZZAddkLoop.v`, `Section AddkEntry`. §R11's second untested path, and
the one that could still have hidden a D-shaped surprise: everything before this
TRADED cells (`loop_cells_trade` moves resources it assumes exist); nothing
SUPPLIED a reservoir at a real trip count. `loop_reservoir_cells` and
`loop_carry_cells_sync` (§R6) had **no caller** -- M's own enter does it at
`tot = 1` and peels the single copy by hand.

    Lemma addk_reservoir_entry (iq pe ape : N) (tot : nat) :
      ([∗ list] i ∈ seq 0 tot, [∗ list] c ∈ addk_cells,
         mem_cell (cell_value c) (cell_is_public c)
                  (cell_addr_of (addk_iota iq pe ape i) c))
      ⊢ addk_frame iq pe ape tot tot.

`tot` copies of the two-cell window, at the addresses each trip will use,
become the entry frame -- for ARBITRARY `tot`, with the per-trip side condition
discharged by the same `repeat constructor; eexists; cbn; reflexivity` that
`ZZCellTrade` uses. `addk_reservoir_exit` is the far end: at trip 0 the caller
gets the array back, which is what every loop before §R6 had to DROP.

**Why this was the load-bearing test.** D taught that a reservoir can be
tradeable and still impossible to inhabit -- `loop_carry_cells` proves from a
`False` premise when trips overlap. K is disjoint, and now demonstrably
inhabitable rather than presumed so.

## Both §R11 paths are now closed

| path | status |
|---|---|
| a sliding loop's BACK EDGE on generated machinery | `addk_back_edge`, no holes (§R12) |
| the reservoir INHABITED at a real trip count | `addk_reservoir_entry/_exit` |

`loop_cells_trade`, `loop_carry`, `loop_carry_exit`, `loop_reservoir_cells` and
`loop_carry_cells_sync` all now have real callers on a loop they were not
developed against.

## Next, and it is MECHANICAL

`addk_place`, the trip bound and `addk_loop_runs` -- direct mirrors of M's
`subword_place` / `subword_trip_bound` / `subword_loop_runs`, tying latch +
back edge + entry into one `loop_runs` instance. Nothing in them is new
machinery; §R12/§R13 removed the parts that were.

Then: I and M on the same pattern, the remaining cuts, and only then D (§R11).

---

# §R14. The cuts were not using the FRAME RULE (2026-09-15)

Prompted by the question "do we leverage separation logic in proving our cuts —
can we use the frame rule somehow, that would make it possible to prove segments
in a self-contained way?". The answer turned out to be *the mechanism is already
in the code and the cuts were not using it*, and switching the F→G cut onto it
halves its proof cost.

## The mechanism was already there

`seg_run` (`GenCompose.v:304`) — the lemma turning one verified segment contract
into one step of the Iris proof — has always taken an explicit frame:

```coq
Lemma seg_run {R : LCtx} (c : @CFGVerifierContract R) (iota : Valuation R)
  (a : bv xlenbits) (L : list AnnotInstr) (cbase : bv xlenbits) (Fr : iProp Σ)
  (HPre  : Pre -∗ Fr ∗ seg_entry c iota a L cbase)
  (HPost : forall an, Fr ∗ seg_exit c iota a L cbase an -∗ Post) :
  Pre -∗ myWP2_loop Post.
```

`Fr` is an arbitrary `iProp Σ`, split off before the segment runs and handed back
untouched — i.e. `{P} c {Q}` ⟹ `{P ∗ Fr} c {Q ∗ Fr}` at segment granularity. Its
own comment already said why it works: `Fr` is not selected by the soundness
bridge's `with "[...]"` selector, so unselected spatial resources survive into
the continuation goal.

## What the cuts were doing instead

`sgF_rest` (§R10, stage 2) carried the data-memory block and nine registers
through F's **postcondition**, justified in a comment as "which G never touches
and H needs". But *G never touches it* is the side condition of the frame rule.
Those resources belong in `Fr` at the composition site, not in F's contract.

Stage 2 was not wrong, only unnecessary — and §R10's framing of it as "the
carry" is what hid the alternative.

## Measurement

Matched arms: same file, same import block, same `solve_param_vc`, one changed
block. `allocated_words` net of `ZZImpCarry.v`, an imports-only arm measuring
1,117,458,396.

| arm | total M | net M | ratio |
|---|---|---|---|
| `ZZEnterFGCarry` — stage 2, memory carried + 20 regs declared | 1296.5 | 179.1 | 1.00× |
| `ZZEnterFGFrame` — memory framed off | 1230.5 | 113.0 | **1.585×** |
| `ZZEnterFGFramedM` — + registers trimmed to footprint | 1208.8 | 91.3 | **1.961×** |

**About half the proof cost of this cut was specifying resources the segment
never touches.** The split matters: framing the memory is worth 1.585× on its
own, trimming the register list a further 1.241×.

The landed `ZZEnterFG.v` additionally drops the `ZZMemCells` `Require` it no
longer needs, so whole-process it totals 1170.4 M against the carry arm's
1296.5 M = **1.108×**. Quote 1.96× for proof cost and 1.11× for process cost;
they answer different questions and neither alone is the headline.

## PROTOCOL TRAP — the imports baseline is not a constant

Worth more than the ratios, and it nearly produced a wrong number here. Roughly
1.117 G of that "imports baseline" is forcing the heavy RiscvPmp instantiation,
and **which file pays depends on what first forces it**. An imports-only arm cut
from the *framed* file measures **1,447,984** — three orders of magnitude less —
because its import block no longer forces the instantiation; the same 1.117 G
then reappears inside the proof. Subtracting the carry arm's baseline from the
framed file's total would report a ~1,169 M "proof cost" that is almost entirely
instantiation, i.e. would say framing made the cut *six times worse*.

So: **a net-of-baseline figure is comparable only between arms with the same
import block.** This is `diagnostics/vm-vs-tactic-split.md`'s lesson (an
`allocated_words` figure prices a pipeline) recurring on the import axis, and
`check-scalar-loop*`'s cross-protocol retraction recurring in a new disguise.
`ZZEnterFGFramedM.v` exists solely to keep the A/B matched and should not be
deleted as a duplicate of `ZZEnterFG.v`.

## The footprint is ENFORCED, not trusted

The reason framing can be done by trial rather than by careful reasoning: the
symbolic executor rejects any access outside the declared footprint. An early
trim dropped A7 and the VC failed with `No applicable tactic` in ~28 s — A7 is
x17, the `rs1` of the SRLI/SLLI pair at idx 125/126, so F does read it. Restore
it and the proof goes green; A2, X2 and A3–A6 stay dropped because F genuinely
never names them.

**Recipe for narrowing a segment's footprint:** delete a resource, recompile,
and keep the deletion iff it still verifies. A wrong guess is caught locally by
the executor rather than distantly by a later composition failure.

One refinement learned doing it: the rule is *the footprint of the contract*,
not *the footprint of the instructions*. S0–S3 are kept although F never
mentions them, because G's precondition (reached through `divrem_cut_subst`)
demands them — what the POSTCONDITION promises counts too.

## Non-vacuity re-checked on the framed shape

A weaker contract could in principle make a false claim provable, so both
falsification arms were regenerated from the framed file and re-run:

| arm | change | result |
|---|---|---|
| `ZZEnterFG_badk` | `k = 31` instead of 32 (wrong entry counter) | **REJECTED**, `No applicable tactic` |
| `ZZEnterFG_badr` | `A0 = p+1124` instead of `p+1128` | **REJECTED**, `No applicable tactic` |

`A0` is inside F's footprint, so trimming did not defang the register arm. The
stale stage-1 arm `ZZEnterFG_bad.v` (trivial `sgF_rest`, `k=31`) was deleted as
superseded.

## Where framing does NOT reach

Three limits, and they are why `loop_carry` (§R6) is complementary rather than
redundant:

1. **Sliding-footprint loops cannot frame their array off.** K, I and D *do*
   touch the memory, at different addresses each trip. `Fr` is a single opaque
   proposition and cannot express "the part of the array we have not reached
   yet". That is exactly `loop_carry`'s reservoir/completed split.
2. **Partial memory footprints need a cell-level block.** F was the easy case —
   it touches no memory, so the choice was all-or-nothing. A segment touching
   three of twelve words must declare those three and frame the rest;
   `cell_spec`/`gen_cells_pre` (§R9) is what makes that writable, since
   `ZZMladCommon.v` records why no context-generic memory block existed before.
3. **One segment, one size, no held-out point.** And per
   `diagnostics/vm-vs-tactic-split.md` the muladd cut-segment family is
   tactic-bound (33–78% `solve_vc`), so part of the 1.96× may be `cbn` rather
   than executor work. Not split.

## Consequence for the remaining cuts

`ZZDvAlone.v` already demonstrates the endpoint: the `br_divrem` loop stated at
its OWN symbolic base `q` at offset 0, knowing nothing about its host program.
That is framing taken to its conclusion, and it verifies.

For the eight straight-line cuts still to write, the default should be
**minimal footprint plus `Fr`**, not carry-everything. This strengthens the case
for the deferred `gen_cut_contract` wrapper (§R3 step 3): it should take the
footprint as data and generate the framed contract, so a new cut starts minimal
and is widened only when the executor says so.

## Files

Landed: `Example/ZZEnterFG.v` reworked onto the framed shape (`valid_sgF'`,
`Qed`, hole-free), arms `ZZEnterFG_badk.v` / `ZZEnterFG_badr.v` regenerated.
Measurement rig kept: `ZZImpCarry.v` (imports baseline), `ZZEnterFGCarry.v`
(pre-framing arm — the ONLY copy, since these files are untracked and it is not
recoverable from git), `ZZEnterFGFrame.v` (memory-only arm),
`ZZEnterFGFramedM.v` (framed contract at carry imports),
`ZZEnterFGImportsNM.v` (the 1,447,984 arm that exposed the protocol trap).
