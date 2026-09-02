# `env.lookup` — where its linear cost actually is

Status: **Diagnostic record, 2026-09-01. §1–§4 are PLAN-env-trie's GATE 0 and
overturn that plan's premise; §7 is GATE 2, measured on the real workload after
the fix landed (commit `acb0368d`).** Read §5 before funding any part of §3 of
`theories/plans/PLAN-env-trie.md`.

## One-sentence finding

`env.lookup`'s cost is **not** the linear walk — it is **allocation inside the
walk**: `ctx.view` builds a `SnocView` value *and* a fresh `MkIn` record at
every step, costing a measured **23.5 allocated words per binder walked**,
whereas the identical O(depth) traversal written without `ctx.view` allocates
**exactly zero** words per step — so the indicated fix is a ~20-line rewrite of
`Environment.v:154`, worth **5.9× on allocation / 3.1× on time at |Σ|=200**, and
the skew-binary RAL of PLAN §3 is *not* indicated: it cannot be sub-linear at
all, because `ctx.in_at` is a **unary** `nat`, so every comparison and
subtraction inside a tree descent costs O(index). **Landed and measured on the
real workload (§7): 2.41×–2.89× over `|Σ|` = 33–135, removing 58–65% of total
cost — roughly double the ~1.28× Amdahl estimate, for the reason in §7.3. A
constant factor, not an exponent change, and a THROUGHPUT win only: full-length
muladd at `mlen`=2 still does not fit in 14 GB (§7.5), because what blocks it is
peak live heap and every figure here is total allocation. On the twelve shipped
examples, whose `|Σ|` is far smaller, the same mechanism is worth
**1.11×–1.93× of their own verification work** (§8).**

## 0. Protocol

| tag | protocol |
|---|---|
| **ALLOC** | `OCAMLRUNPARAM='v=0x400' coqc`, **one** `Time Eval vm_compute` per process, `allocated_words` net of a per-`n` imports+definitions baseline (`BASE` arm, identical file with the `Eval` removed). Gated on the arm's checksum being correct and `errors=0`. |

Every arm is generated from one common body by a two-token `sed` on `NN` and
`ROUNDS`, so only `n` and the benchmarked function can differ. Total lookups is
held at **9600 in every cell** (`ROUNDS = 9600/n`), so a column is directly a
*per-lookup* cost and `n` moves only the depth, never the work count.

Wall-clock figures below are from the same runs and are **indicative only**
(shared 14 GB box); every ratio claimed in §5 is on `allocated_words`.

## 1. The axes

The plan named one axis (lookup **algorithm**: linear walk vs. random access).
This study needed a second, because the first sweep contradicted itself:

| axis | states |
|---|---|
| `algorithm` | `walk` (O(depth)) \| `ral` (skew-binary random access) |
| `per-step-allocation` | `view` (current: `ctx.view`, allocates) \| `fused` (recurse on `(Env, in_at, in_valid)` together, allocates a closure) \| `none` (non-dependent walk, allocates nothing) |
| `index-arithmetic` | `unary` (as `ctx.in_at` really is) \| `binary` (`N`) |

| arm | algorithm | per-step alloc | what it is |
|---|---|---|---|
| `SLOW` | walk | `view` | **`env.lookup` as it exists today** |
| `IDX` | walk | `fused` | fused walk, curried — closure per step |
| `IDX2` | walk | `fused` | fused walk, all args up front |
| `WALK` | walk | `none` | non-dependent spine walk, binder type recovered once by `EqDec B` |
| `BARE` | walk | `none` | `WALK` with the type recovery deleted — not a usable lookup, a floor |
| `FAST` | ral | — | PLAN §3's skew-binary RAL, `nat` (unary) sizes and indices |
| `NULL` | — | — | the same `env.tabulate` with **no lookup at all** — the floor both arms pay |

Every arm is driven by `env.tabulate (fun b bIn => <arm> E bIn)`, which is
exactly `sub_comp`'s shape (one traversal of `Σ`, one lookup per entry).

## 2. Results — allocated words **per lookup**, net of the `NULL` floor

| n = \|Γ\| | `SLOW` | `IDX` | `IDX2` | `WALK` | `BARE` | `FAST` |
|---|---|---|---|---|---|---|
| 100 | 2371.7 | 752.0 | 397.6 | 194.6 | 5.29 | 305.3 |
| 200 | 4721.9 | 1502.2 | 797.6 | 224.6 | 5.20 | 436.8 |
| 400 | 9421.9 | 3002.2 | 1597.7 | 254.4 | 5.22 | 671.1 |
| 1600 | 37621.7 | 12001.9 | 6398.5 | 314.1 | 5.17 | 1961.9 |

(`FAST` is from a sibling sweep with its own `BASE`/`NULL`; all others share one.)

Per-binder slopes, **fitted on n ∈ {100, 200} only and held out at n = 1600**,
which is 8× beyond the fit range:

| arm | fitted law (words/lookup) | predicted @1600 | actual | error |
|---|---|---|---|---|
| `SLOW` | 22.2 + **23.503**·n | 37627.0 | 37621.7 | **−0.014%** |
| `IDX` | 2.2 + **7.5017**·n | 12005.0 | 12001.9 | **−0.026%** |
| `IDX2` | −2.4 + **4.0001**·n | 6397.7 | 6398.5 | **+0.012%** |
| `WALK` | 164.6 + **29.98**·log₂n | 313.6 | 314.1 | **+0.16%** |
| `BARE` | **5.2**, no n term | 5.2 | 5.17 | −0.6% |

Five arms, five held-out points, all inside 0.2%. The laws are not in doubt.

`FAST` is **linear too** — slope ≈1.1 words/binder fitted on n ∈ {400, 800},
predicting 1991 at n=1600 against 1962 (−1.5%). It never becomes logarithmic.

Wall clock, whole 9600-lookup `Eval`, net of `NULL` (indicative):

| n | `SLOW` | `IDX` | `IDX2` | `WALK` | `BARE` |
|---|---|---|---|---|---|
| 200 | 0.123 s | 0.043 | 0.040 | 0.036 | 0.022 |
| 1600 | 1.062 s | 0.407 | 0.313 | 0.205 | 0.167 |

## 3. Reading the axes apart

### 3.1 The whole linear term of `env.lookup` is `ctx.view`'s allocation

`SLOW` and `BARE` execute the **same number of steps over the same spine**.
`SLOW` allocates 23.5 words per step; `BARE` allocates **0.000 words per step**
(5.2 words per lookup, flat over a 16× range in n). The mechanism is visible in
the source: `ctx.view = ctx.In_case _ isZero isSucc`, and `In_case`'s successor
branch is

```coq
| S n => fun p => fs _ _ _ (MkIn n p)          (* Context.v:131 *)
```

so each step allocates a fresh `MkIn` record *and* the `isSucc` constructor
wrapping it. Nothing else in the walk allocates.

**This is the finding.** "`env.lookup` is a linear walk" is true and was never
the problem; the problem is that each of those steps costs 23.5 words instead of
0.

### 3.2 Recovering the binder type is what a `fused` walk pays for

`IDX`/`IDX2` keep full dependency — they recurse on the `Env` spine and the raw
`in_at` nat together and transport `d : D b'` to `D b` **once**, at the base
case, along the *existing* `in_valid` proof. No `EqDec`, no conversion, no new
structure. They cost 7.5 and 4.0 words/step: the residual is the per-step
closure the dependent motive forces, and taking every argument up front (`IDX2`)
halves it.

`WALK` removes even that by walking non-dependently into a `sigT D` and
recovering `b' = b` once per lookup with a decidable test. Its 30 words/doubling
is that test (`N.eq_dec` on binder *values* 0..n−1, whose bit length grows with
n); with a fixed binder type — which is the real case, `B = Binding` — that term
is a constant, not a function of `|Σ|`.

### 3.3 The RAL cannot be sub-linear, and the reason is the index type

`FAST` is PLAN §3's design, and it is **linear**, at slope 1.1 instead of 23.5.
The cause is not transports (§4) and not the tree: a skew-RAL descent must
compute `i < h`, `i − h` and `h/2`, and `ctx.in_at` is a **unary `nat`**, so each
of those is O(index). Summed over a halving descent that is Θ(n) again.

PLAN §1 states this exactly backwards:

> "`ctx.In` is **already index-optimised** … the index is a machine `nat`;
> there is nothing to gain there."

A Coq `nat` is not a machine word; it is unary Peano, and the VM has no special
representation for it. **Any** random-access scheme keyed on `in_at` pays O(in_at)
in arithmetic before it looks at a single tree node. A sub-linear lookup would
require `ctx.In` to carry a *binary* index (`N`/`positive`), which is a far
larger change than the plan scoped — and §3.1 says it would buy nothing anyway,
because a linear walk that allocates nothing already has zero allocation slope.

### 3.4 GATE 0's transport question: PASSED, and it is not the risk

PLAN §2c called dependent transports "the assumption that kills the plan if it
is wrong". It is not wrong, in any arm:

- `FAST`/`WALK`: `eq_rect` on a decided `N.eq_dec` equality.
- `IDX`/`IDX2`: `eq_rect` on the **`in_valid` proof itself**, the harder case.

A lookup at **depth 196 of 200** reduces to a bare constructor (`dmk 3%N 4`)
under **both `vm_compute` and `cbv`** in every arm, and the strict variants —
which return a deliberately wrong value instead of falling back on the linear
walk, so a blocked transport cannot be masked — return the exact checksum
(20100 = Σ 1..200) at every index. No `eq_rect` survives reduction anywhere.

## 3.5 Landing it: `cbn`-refoldability is a THIRD axis, and it costs the win

Found while landing Phase 1', not predicted by anything above, and it is the
part of this change most likely to bite a future reader.

The old `lookup` was a **`Fixpoint` on `E`**, which gave downstream proofs *two*
properties, easily conflated:

1. `cbn` unfolded it **only** when `E` was in constructor form.
2. What it unfolded **to** contained a folded `lookup E' i`, because the body's
   recursive occurrence was `lookup` itself — so the next `rewrite` of any
   `lookup`-shaped lemma still matched.

Property 1 is recoverable: `Arguments lookup {Γ} !E {b} x` reproduces the old
gating exactly. **Property 2 is not**, because the fast body's recursive
occurrence must be the auxiliary `lookup_at` — carrying `(n, p)` onward instead
of rebuilding an `In` *is* the optimisation. Isolated on a three-line control
(a hypothesis `Hwk : forall b i, lk Ewk i = f b i`, goal
`lk (snoc Ewk v) (in_succ i) = f b i`, tactic `cbn; rewrite Hwk`):

| definition | goal after `cbn` | `rewrite Hwk` |
|---|---|---|
| old, `ctx.view` | `oldlk Ewk i = f b i` | **✓** |
| fused walk **+ `!E`** | `newlk_at Ewk (ctx.in_at i) b (ctx.in_valid i) = f b i` | **✗** |
| `Fixpoint`, recursive call `fixlk E' (ctx.MkIn n' p)` | `fixlk Ewk i = f b i` | **✓** |

The failure mode is nasty because the error names nothing relevant: `Terms.v`'s
`sub_up1_id` reported `Found no subterm matching "sub_wk1.[? ?x∷?σ]"`.

**Resolution (what landed): `!E` plus a refold lemma.**
`lookup_at_fold : lookup_at E (ctx.in_at x) b (ctx.in_valid x) = lookup E x`,
true by `reflexivity`, with `lookup_at_fold'` for a goal whose index is a raw
`MkIn` record. `cbn` then reduces exactly where it used to, and the repair for
any proof that notices is the single uniform line `rewrite ?lookup_at_fold`.

An earlier attempt used `Arguments lookup : simpl never` instead. It also
builds, but it blocks reduction that proofs legitimately want, so each repair
had to be reasoned out separately (`unfold sub_snoc`, `cbn -[env.lookup]`,
`rewrite env.lookup_snoc_succ`, …). Prefer the refold lemma: same cost, same
proofs touched, one rule instead of three.

**The zero-churn alternative, measured rather than assumed.** Row 3 above needs
*no* `Arguments`, *no* refold lemma and *no* proof changes anywhere — but it
rebuilds one `MkIn` per step:

| variant | words/binder | vs. old |
|---|---|---|
| old, `ctx.view` (inlined into the probe, so this arm is stable) | 22.5 | — |
| `Fixpoint`, rebuilds `MkIn` per step — **zero churn** | 9.5 | **2.4×** |
| fused walk + `!E` + refold — **what landed** | 4.0 | **5.6×** |

So refoldability is worth 2.3× of the speedup, and buying it back costs eleven
repaired proofs. The old arm reads 22.5 words/binder here against §2's 23.5 for
the real `env.lookup`; the 4% gap is the inlined copy plus a different `BASE`,
and affects no ratio in this section.

## 4. RETRACTION of this study's own first sweep (same day)

The first sweep reported `SLOW`/`FAST` net costs of 108.7 M / 65.8 M words at
n=200 and a ratio that **shrank** with n (2.75× → 1.72×). **Never requote those
numbers.** They were ~85% *my own checksum*: the harness summed the payloads
with `Nat.add (esum E') (meas d)` over unary nats, and since `Nat.add` recurses
on its first argument, summing 1..n costs Θ(n³/6) — 66.6 M words per 50 rounds at
n=200, swamping the arms being compared. Replaced by an O(1)-per-entry
accumulator; every number in §2 is from the corrected harness. The measurements
were bad, not merely the conclusion.

Cost-of-the-instrument is the same class of error this directory's records
warn about for baselines and protocols. The tell was that the *shape* was
impossible — no log-vs-linear pair can converge as n grows.

## 5. What this means

1. **PLAN-env-trie §3 (skew-binary RAL) and Phase 3 (replace `Env`'s
   representation) should be dropped.** The structure is linear anyway (§3.3),
   and the win it was reaching for is available from a local rewrite.
2. **The indicated fix is `Environment.v:154` itself**: define `lookup` by
   recursion on the `Env` spine and `ctx.in_at` simultaneously, transporting
   once along `ctx.in_valid`. No new type, no conversion, no `EqDec`
   constraint, no API change — `lookup (snoc E v) in_zero = v` and
   `lookup (snoc E v) (in_succ i) = lookup E i` both still hold
   **definitionally**. This is `IDX2`: **5.9× on allocation and 3.1× on time at
   n=200**, **5.9×/3.4× at n=1600**. It also needs `Arguments lookup !E`, a
   `lookup_at_fold` refold lemma, and eleven repaired proofs — see §3.5, none
   of which was foreseen here.
3. **Constant factor, NOT an exponent change.** `sub_comp` stays O(`|Σ|²`); the
   constant on the `|Σ|²` term drops ~5.9×. Say this in those words when
   quoting it. The `WALK` arm *is* an exponent change in allocation (flat
   vs. linear per step, 120× at n=1600) but needs `EqDec B` in
   `Environment.v`'s `WithBinding` section, which `lookup` does not currently
   assume.
4. ~~**Amdahl is NOT yet applied and this fix is NOT yet justified.**~~
   **SUPERSEDED by §7, which measured it: the real answer is 2.41×–2.89×, not
   the ~1.28× predicted here. The prediction below is left in place because the
   REASON it was wrong is the useful part — see §7.3.**
   `case_study/RiscvPmp/CFGVer/diagnostics/lvar-lookup-cost-drivers.md` §5.4
   attributes only **26.4%** of the K=64 variable surcharge to the `env.lookup`
   walk (L1); the other 73.6% is `env.tabulate` per mint, `ctx.fresh`'s name
   scan, and pc re-substitution. On that reading a 5.9× on L1 is worth
   ~1.28× end to end. **PLAN Phase 0b is still the deciding measurement** — and
   it now has a much better instrument than the one it specified: land the
   `IDX2` rewrite and re-measure the real probes, which prices L1 exactly *and*
   delivers the fix in the same build. Note the tabulate floor measured here
   (`NULL`) is itself substantial — 5.9 M words at n=200 against 45.3 M for the
   lookups — so L2 is real and will become the wall.

## 6. Files / reproduction

`theories/diagnostics/ZZEnvLookupProbe.v` is the common body. It is **not** in
`_CoqProject` (so the gate never builds it) and its `ZZ` prefix keeps it outside
`gate.sh`'s hole scan (`--exclude='ZZ*'`, `scripts/gate.sh:152`); it is
nonetheless committed rather than left untracked, because it contains no
`Admitted.` at all -- there is not a single proof in it -- and the reproduction
below is worthless without it. It defines every arm over a toy
`B := N`, `D := Dty` (a genuine `B -> Set` family) but uses **Katamaran's real
`env.Env`, `ctx.nth_is`, `ctx.in_at`, `ctx.in_valid`**, so the candidate
definitions transplant verbatim.

```bash
for n in 100 200 400 1600; do r=$((9600/n)); for arm in BASE NULL SLOW IDX IDX2 WALK BARE; do
  f=ZZU_${n}_${arm}
  sed "s/^Definition NN : nat := 200\./Definition NN : nat := $n./;
       s/^Definition ROUNDS : nat := 50\./Definition ROUNDS : nat := $r./" \
      theories/diagnostics/ZZEnvLookupProbe.v > /tmp/$f.v
  [ $arm = BASE ] || echo "Time Eval vm_compute in bench_$(echo $arm | tr A-Z a-z)." >> /tmp/$f.v
  OCAMLRUNPARAM='v=0x400' coqc -q -w none -R theories Katamaran /tmp/$f.v \
    2>&1 | grep -E 'allocated_words|Finished transaction|Error'
done; done
```

Run `coqc` from the repo root (`-R theories Katamaran` is relative).

Two harness traps, both hit here: an accumulator built with unary `Nat.add`
dominates the measurement (§4) *and* stack-overflows past n≈400; and
`allocated_words` is **blind to a pointer-chasing walk** — the `BARE` arm does
960 000 spine steps for 5.2 words per lookup. That is the finding in §3.1, but
it also means allocation alone cannot price a *time* question here; §2's wall
clock is quoted for exactly that reason.

---

# Part II — GATE 2: what it was actually worth

## 7. The fix, measured on the real workload

Two full builds of the same commit, differing **only** in `env.lookup`: the
working tree (fused walk, `acb0368d`) and a scratch copy with
`theories/Environment.v`, `Syntax/Terms.v`, `Symbolic/Instantiation.v` and
`Symbolic/GenOccursCheck.v` reverted to `7da9ce85`. Neither arm's `.vo`s can
clobber the other's, and the working tree was never edited to produce the
old arm (`cfgver-scaling-diagnostics`: "comparing two COMMITS by editing the
working tree — don't").

Probe: the muladd dense-havoc prefix `Example/ZZDS<K>.v`, `drop_fuel = 0`, raw
VC construction, **one `Eval vm_compute` per `coqc` process**, net of
`ZZDSB.v` — the identical file with its final `Eval` deleted. Protocol tag:
**ALLOC** (`allocated_words`; no `Qed`, no `solve_vc`, so this is not
comparable to any `Qed`-protocol figure in this repo — that mismatch is worth
1.81×).

**Two checks before reading anything into the numbers.** The two arms' import
baselines are 656,540,034 (old) and 656,571,975 (new) — **0.0049% apart**, so
the closures cost the same and the ratios are clean. And the old arm reproduces
`muladd-full-cost-drivers.md` §3.6's published figures (0.904 / 4.387 /
10.546 G) at 0.868 / 4.351 / 10.510 — within **0.34% at K=206** — so the
published numbers stand on this commit and this is the same rig.

### 7.1 Results

| K | peak `\|Σ\|` | OLD net G | NEW net G | **ratio** | share of cost removed |
|---|---|---|---|---|---|
| 118 | 33 | 0.8678 | 0.3608 | **2.406×** | 58.4% |
| 162 | 96 | 4.3507 | 1.5927 | **2.732×** | 63.4% |
| **184** | **108** | **6.5027** | **2.3153** | **2.809×** | **64.4%** |
| 206 | 135 | 10.5100 | 3.6358 | **2.891×** | 65.4% |

`peak |Σ|` is byte-identical between arms at every K (33/96/108/135), so both
arms verify the same VC — the change is not observable in what is proved.

Marginal cost per instruction, which strips the K-independent part out:

| segment | OLD | NEW | ratio |
|---|---|---|---|
| K 118→162 | 79.16 M/instr | 28.00 M/instr | 2.827× |
| K 162→184 | 97.82 M/instr | 32.85 M/instr | 2.978× |
| K 184→206 | 182.15 M/instr | 60.02 M/instr | 3.035× |

### 7.2 Held-out point

K=184 was **not** used to fit anything: the quadratic in K was fitted on
{118, 162, 206} (equally spaced, ΔK=44) and the prediction recorded before the
run.

| | predicted | actual | error |
|---|---|---|---|
| OLD net | 7.096 G | 6.503 G | **+9.1%** |
| NEW net | 2.513 G | 2.315 G | **+8.5%** |
| **ratio** | **2.824** | **2.809** | **+0.53%** |

Read this the right way round. The quadratic-in-K model is **not** accurate in
absolute terms — it over-predicts both arms by ~9%, so the growth is somewhat
sub-quadratic in K and no absolute figure should be extrapolated from it. But
the error is common-mode and cancels: **the ratio is predicted to 0.53%**, which
is what the claim rests on. Quote ratios from this rig, not levels.

### 7.3 Why the ~1.28× Amdahl prediction was wrong

§5's prediction came from `lvar-lookup-cost-drivers.md` §5.4, which attributes
**26.4%** of the K=64 variable surcharge to L1 (`env.lookup`'s walk) and 73.6%
to "breadth" — `env.tabulate` per mint, `ctx.fresh`'s name scan, pc
re-substitution. A 5.9× on 26.4% is 1.28×.

**That §5.4 measurement is not retracted; the inference from it was wrong.**
§5.4 partitions by *axis* — how deep the hot variables sit at fixed `|Σ|`
(depth) versus everything that scales with `|Σ|` regardless of depth (breadth).
This fix does not live on either side of that line. It removes `ctx.view`'s
**per-step allocation from every lookup everywhere**, including the lookups
performed *inside* the mechanisms §5.4 counts as breadth — `env.tabulate` calls
`lookup` per entry, and pc re-substitution does a lookup per variable
occurrence. So a fix priced against the depth axis alone was always going to be
under-predicted.

The measured share removed is **58–65%, rising with `|Σ|`**, which is the number
to use for any future Amdahl estimate on this workload.

### 7.4 Constant factor or exponent change?

**Constant factor.** Say it in those words. The marginal ratio is *saturating*
(2.83 → 2.98 → 3.04), not diverging, and the share removed is converging on
~65% — the signature of an Amdahl ceiling near 1/(1−0.67) ≈ 3×, not of an
exponent reduction. Both arms remain superlinear in `|Σ|`; `sub_comp` is still
O(`|Σ|²`), now with a ~3× smaller constant. **The wall moves; it does not go
away.** `muladd` at `mlen`=2 is not expected to complete because of this.

### 7.5 THROUGHPUT vs FOOTPRINT — this fix buys the first, and the muladd wall is the second

**Every number in this record is `allocated_words`: total allocation over a
run, a THROUGHPUT metric.** What makes muladd at `mlen`=2 infeasible is *peak
live heap*, which is a different quantity, and the two come apart badly here:
the `MkIn` + `SnocView` pairs this fix removes are **short-lived garbage**. They
inflate allocation enormously and contribute almost nothing to the high-water
mark. So a 2.9× on allocation should NOT be read as a 2.9× on footprint, and
the feasibility question is not answered by anything in §7.1–§7.4. **§9 then
measured it: footprint is unchanged EXACTLY — `top_heap_words` byte-identical
between arms at every K, peak RSS within 1.3%.**

Measured directly, 2026-09-01, on the new arm: the **full-length** dense-havoc
arm (`ZZDSFULL.v`, `ZZK = 400` so `firstn` takes all ~292 instructions — K=206
was only a 70% prefix) reached **12.0 GB peak RSS and ~34 GB VSZ on a 14 GB
box**, went into sustained swap thrashing at ~85–100 MB/s in both directions,
and was killed at 26:32 having made no useful progress. It does not fit, and
`allocated_words` was never going to predict that.

**So the motivating problem is NOT solved.** This is consistent with §7.4 — a
constant factor moves a wall rather than removing one — but the reason
full-length muladd still fails is a metric this study did not track. Anyone
extending it should use **`top_heap_words`** (also in the GC dump) or peak RSS
for the feasibility question, and should read
`cfgver-scaling-diagnostics`'s warnings about both before quoting either.

### 7.6 Not measured

Wall clock at the probe level (the probe has a bare `Eval`, not `Time Eval`, and
this box is shared — the §2 microbenchmark's 3.1× and the whole-project build's
58:04 → 47:21 are the only timing evidence here). Anything under a real `Qed` or
`solve_vc`: §7.1–§7.4 are raw VC construction only, so those figures are not
comparable to any `Qed`-protocol number in
`case_study/RiscvPmp/CFGVer/diagnostics/`. Where full-length muladd stops
fitting (a `top_heap_words` bisection over K) — not attempted.

### 7.7 Reproduction

Both arms, four K values each:

```bash
# new arm = the working tree at acb0368d; old arm:
tar -cf - --exclude=.git --exclude=_build . | (cd $OFF && tar -xf -)
for f in theories/Environment.v theories/Syntax/Terms.v \
         theories/Symbolic/Instantiation.v theories/Symbolic/GenOccursCheck.v; do
  git show 7da9ce85:"$f" > "$OFF/$f"; done
(cd $OFF && make -f Makefile.coq -j1)

# ZZDS<K>.v is ZZDS206.v with `Definition ZZK` sed'd; ZZDSB.v is it minus the
# final Eval.  One process per point, sequentially:
OCAMLRUNPARAM='v=0x400' coqc -q -w none -Q case_study/RiscvPmp Katamaran.RiscvPmp \
  -R theories Katamaran case_study/RiscvPmp/CFGVer/Example/ZZDS206.v \
  2>&1 | grep -E 'allocated_words|Error'
```

`ZZDS*.v` are gitignored throwaways derived from `Example/ZZMuladdFullN2.v`;
see `muladd-full-cost-drivers.md` §5 for how that root artifact is produced.

---

# Part III — what it did for the shipped examples

## 8. Per-example payoff (`Qed` protocol, the examples' real one)

### One-sentence finding

On the twelve verified CFGVer examples the rewrite is worth **1.11×–1.93× of
each example's OWN verification work**, monotone in example size and **every one
of them below §7's 2.41×–2.89×** — because the examples run at far smaller `|Σ|`
than the probe, so the lookup walk is a smaller share of what they do.

### 8.1 Protocol, and why "own work" is the only column that means anything

**ALLOC**, but under the examples' **real** protocol — one `coqc` per file,
whole file, `vm_compute` + `solve_vc` + a real `Qed` — not §7's raw-VC
construction. The two are not comparable to each other (§7.6); they are
comparable *within* this section, arm to arm.

`own work = aw(file) − aw(ZZExBase)`, where `Example/ZZExBase.v` contains
exactly the examples' shared import line and nothing else. That baseline is
**605,766,546** (new) / **605,756,891** (old) — **0.0016% apart**, which is what
makes the ratios below clean.

**Own work is the object of study; the whole-file figure is not.** ~0.6 G of
every example's compile is the import closure, which is a **constant** — it is
the same in both arms to four decimal places, no part of this study touches it,
and `theories/CLAUDE.md`'s compile-cost section already records that it has
resisted every attempt to reduce it. Dividing by it does nothing but dilute the
measurement by a factor that varies with example size for reasons unrelated to
the mechanism. The whole-file column is retained in 8.2 only so that nobody
re-derives it and thinks it contradicts the own-work column.

### 8.2 Results

| example | OLD own | NEW own | **own-work ratio** | (whole-file, not the metric) |
|---|---|---|---|---|
| SetX2 | 5.6 M | 5.1 M | **1.105×** | 1.001× |
| Jumps | 7.7 M | 6.7 M | **1.141×** | 1.002× |
| MvSwap | 20.6 M | 17.4 M | **1.183×** | 1.005× |
| Countdown | 42.2 M | 35.6 M | **1.184×** | 1.010× |
| Precompute | 39.9 M | 27.5 M | **1.451×** | 1.020× |
| `BearSSLMuladd` (snippet) | 48.9 M | 33.5 M | **1.460×** | 1.024× |
| BearSSLModpow | 26.7 M | 18.2 M | **1.469×** | 1.014× |
| Cmovznz4 | 477.6 M | 307.2 M | **1.555×** | 1.187× |
| BearSSLCheckScalarLoop1 | 1146.1 M | 721.2 M | **1.589×** | 1.320× |
| KeyScheduleLoop | 127.8 M | 80.2 M | **1.594×** | 1.069× |
| BearSSLCheckScalar | 117.9 M | 65.1 M | **1.810×** | 1.079× |
| **BearSSLModpowFull** | 2504.2 M | 1296.0 M | **1.932×** | 1.635× |

### 8.3 Reading it

**The payoff scales with the example, and the ordering is the point.** Sorted by
own work, the ratio rises 1.10 → 1.93 essentially monotonically. That is the
same `|Σ|` law as §7 seen from below: `lvar-lookup-cost-drivers.md` puts the
verified examples' peak `|Σ|` at ~25, *under* §7's smallest point (33), and the
lookup walk's share of cost falls with `|Σ|`. **§7's 2.41×–2.89× was never
transferable to these files**, and 1.11×–1.93× is what the same mechanism is
worth in their regime.

**Same function, opposite verdicts.** `Example/BearSSLMuladd.v` — the landed
`muladd_q` snippet — gets **1.46×** on 48.9 M of work, while the *whole
function* under dense havoc gets **2.89×** (§7.1). One mechanism, one program,
a 2× spread in payoff, decided entirely by `|Σ|`. Do not quote either number as
"muladd".

**Wall clock is not evidence here and is not tabulated.** Cmovznz4 measured
11.87 s old vs 12.50 s new — the *wrong direction* — while its allocation
improved 1.19×. At ~10 s per file on a shared box the wall figures are noise;
`BearSSLModpowFull` (23.33 → 20.39 s, 1.14×) is the only one whose wall moved
beyond it, and it under-reads its own 1.64× allocation change.

### 8.4 Reproduction

`Example/ZZExBase.v` is one line (`Require Import …Example.Prelude.`). Then, one
process per file, both arms, no `make` wrapper — `make` runs `coqdep`, which
under `OCAMLRUNPARAM='v=0x400'` prints its **own** `allocated_words` line and
silently corrupts a naive grep (hit once here; take the LAST match, or call
`coqc` directly as the script does):

```bash
OCAMLRUNPARAM='v=0x400' coqc -q -w none -Q case_study/RiscvPmp Katamaran.RiscvPmp \
  -R theories Katamaran case_study/RiscvPmp/CFGVer/Example/<Example>.v \
  2>&1 | grep -E 'allocated_words|top_heap_words'
```

---

# Part IV — the reduced rig: footprint, and why `mlen`=2 is untouched

## 9. Throughput, footprint and wall on one cheap sweep

### One-sentence finding

The rewrite removes **2.4×–2.9× of allocation, 1.14×–1.70× of wall clock, and
EXACTLY ZERO footprint** — `top_heap_words` is byte-identical between arms at
every K and peak RSS agrees within 1.3% — which is the whole explanation for why
`mlen`=2 remains infeasible, and it was obtainable from runs of 14–73 s each
without ever going near the memory ceiling.

### 9.1 Why a reduced rig, and what "reduced" means here

Running full length (K=292) cost 26 minutes of swap thrashing and produced one
number before being killed. The K-prefix knob (`zz_prefix k = firstn k`) gives
the same function at any length, is already validated (§7 reproduced the
published figures to 0.34%), and **K ≤ 206 never exceeds ~7 GB**. So the rule
is: *cap the sweep below the wall and extrapolate to it*. §9.4 shows that works.

The other half of the reduction was not size at all — it was **grepping one more
line out of a dump I was already producing**. `OCAMLRUNPARAM='v=0x400'` prints
`top_heap_words` next to `allocated_words`; §7 simply never read it.

### 9.2 Results — six K values, both arms, one process each

| K | `\|Σ\|` | alloc OLD | alloc NEW | **alloc ratio** | `top_heap_words` OLD | NEW | identical? | RSS OLD | RSS NEW | **wall ratio** |
|---|---|---|---|---|---|---|---|---|---|---|
| 140 | 42 | 1.196 G | 0.495 G | **2.415×** | 636,785,152 | 636,785,152 | **yes** | 4.30 G | 4.29 G | 1.14× |
| 162 | 96 | 4.351 G | 1.593 G | **2.732×** | 732,303,360 | 732,303,360 | **yes** | 5.18 G | 5.14 G | 1.44× |
| 184 | 108 | 6.503 G | 2.315 G | **2.809×** | 842,148,864 | 842,148,864 | **yes** | 5.79 G | 5.72 G | 1.61× |
| 206 | 135 | 10.510 G | 3.636 G | **2.891×** | 968,471,552 | 968,471,552 | **yes** | 6.84 G | 6.77 G | 1.70× |

Baseline arm (`ZZDSB`) also identical: 553,725,952 both. Five matched pairs,
byte-for-byte. The allocation ratios reproduce §7.1 to four significant figures.

### 9.3 Reading it

**Footprint: unchanged, and this is the finding.** Peak live heap is identical
at every K. This is exactly what the mechanism predicts — the `MkIn` +
`SnocView` pairs the rewrite eliminates are **short-lived garbage**: enormous in
allocation, absent from the high-water mark. So the rewrite makes tractable work
~3× cheaper and does **nothing at all** for work that fails by exhausting
memory. `mlen`=2 is the latter.

*Resolution caveat, stated because it bounds the claim:* `top_heap_words` moves
in exact **1.15× steps** here (636.8/553.7 = 732.3/636.8 = 842.1/732.3 =
968.5/842.1 = 1.150), i.e. it is counting OCaml heap-growth increments, so
"identical" means "the same number of growth steps" and could in principle hide
up to 15%. **Peak RSS is the finer check and agrees to 1.001×–1.013×** — the new
arm is a hair *lower*, never higher. Both metrics, two directions, same answer.

**Wall clock is 1.14×–1.70×, not 2.4×–2.9×.** Measured back-to-back on an
otherwise idle box (K=206: 72.53 s → 42.71 s). Time is not purely
allocation-bound, so **the allocation ratios in §7 and §8 over-state what a
person actually waits through** — quote 1.7× for "how much faster is the muladd
probe", not 2.9×. (The `K=B` wall pair is discarded: the new arm's baseline ran
first from a cold page cache, 14.10 s vs 9.90 s, in the wrong direction.)

### 9.4 The reduced rig predicts the wall it never touches

Peak RSS is **roughly linear in K** — 38.3 / 26.4 / 47.7 MB per instruction over
the three segments — unlike allocation, which is superlinear. Fitting a straight
line on the **two cheapest usable points only** (K = 140 and 162, together under
30 s of compute) and extrapolating to K=292:

> predicted 10.12 GB, **observed 11.46 GB**, error **−11.7%**

So a sub-minute pair of runs predicts the full-length memory wall to about 12%,
which is more than enough to answer "will this fit". **Nobody needs to run
full-length muladd again to know it does not fit in 14 GB.**

### 9.5 What this says about attacking `mlen`=2

The footprint curve is *identical in both arms*, so it is a property of the VC
being constructed, not of how it is walked. Any attack on `mlen`=2 has to
**shrink the live symbolic term** — fewer/smaller chunks, fewer live logic
variables, earlier `dropk` — and not the garbage rate. Every lever in
`cfgver-scaling-diagnostics`'s catalogue should be re-read with that
distinction in mind, because the catalogue is written in `allocated_words`
throughout and therefore cannot, as written, tell a throughput lever from a
footprint lever.

### 9.6 Reproduction

`ZZDS<K>.v` = `ZZDS206.v` with `Definition ZZK` sed'd; `ZZDSB.v` = it minus the
final `Eval`. One process per point, both arms:

```bash
OCAMLRUNPARAM='v=0x400' /usr/bin/time -f "RSS %M WALL %e" \
  coqc -q -w none -Q case_study/RiscvPmp Katamaran.RiscvPmp \
  -R theories Katamaran case_study/RiscvPmp/CFGVer/Example/ZZDS206.v \
  2>&1 | grep -E 'allocated_words|top_heap_words|RSS'
```

Whole sweep, 6 K values × 2 arms, is ~5 minutes. Do not raise K past 206 on a
14 GB box.
