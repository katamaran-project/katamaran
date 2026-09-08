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
