# Program length is a QUADRATIC cost driver for a symbolic segment contract

Status: **Diagnostic record, 2026-09-04.** Prompted by the question "is having
many instructions around also a performance problem?", asked of the countdown
loop specifically. `composition-payoff.md` §2.1 had answered the prefix-length
question on a *straight-line* 3-instruction segment and found it nearly free
(1.155× over 32 filler instructions). Asked again of the **loop-body segment
contract**, the same axis behaves completely differently.

## One-sentence finding

A segment contract whose branch condition the solver cannot decide by
computation costs **93.81 + 4.05·P + 0.531·P² M words** in the number `P` of
**never-executed** instructions sharing its table — an exact quadratic
(held-out **+0.0024%**) worth **26.9× over 64 filler instructions** — while the
*same* contract with its counter pinned costs 1.42×, the flat unrolled VC of the
same loop 1.60×, and §2.1's straight-line segment 1.35×. So program length is
free for everything except the one construct a loop invariant is made of, where
it is quadratic.

## 0. Protocol

| tag | protocol |
|---|---|
| **ALLOC** | `OCAMLRUNPARAM='v=0x400'`, one heavy proof per `coqc` process, `allocated_words` net of an imports-only baseline re-measured per family, `/usr/bin/time` for peak RSS |

Proof protocol is `vm_compute. solve_vc. Qed.` in every arm — `Qed` throughout.
The unpinned arms carry three residual-closing tactics before `Qed` (priced at
~0.004% by this directory's own rule); the pinned and flat arms close on
`solve_vc` alone, which is the same asymmetry `composition-payoff.md` §4
documents.

Four baselines, one per family: 605,864,905 / 605,871,490 / 605,864,980 /
605,846,159 — a spread of **25,331 words in 6.06e8 (0.0042%)**, which is what
licenses comparing across them.

Three independent reproductions of published figures, on this commit, confirm
the rigs are measuring the same objects as the earlier records:

| arm | here | published | delta |
|---|---|---|---|
| flat unrolled, N=8 | 15.646 | 15.632 | +0.09% |
| flat unrolled, N=16 | 27.868 | 27.862 | +0.02% |
| `ZZCmpBodyPin` (re-run) | 10.660 | 10.66 | 0.00% |
| `ZZU5_K0` / `_K32` | 7.220 / 8.339 | 7.223 / 8.343 | −0.04% |

**Gate:** every arm grepped for `Error`. This caught the known stale-`.vo` trap
(`footprint-vs-throughput.md` §5) on the structural-count arms, which would
otherwise have reported as "free".

## 1. Axes

| axis | states | rig |
|---|---|---|
| **prefix length P** | 0 / 16 / 32 / 64 never-executed instructions before the loop | all rigs |
| **proof structure** | composed segment contract vs flat unrolled VC | `ZZPadB*` vs `ZZPadF*` |
| **counter knownness** | symbolic `k` vs `k` pinned to 5 | `ZZPadB*` vs `ZZPadP*` |
| **branch decidability** | undecidable branch vs straight-line | `ZZPadB*` vs `ZZU5_K*` |
| conjunct order (control) | pin before vs after the guard | `ZZPadP0` vs `ZZPadPrev0` |

Held fixed across every `P` within a rig: the executed loop
(`ADDI X1 X1 -1 ; BNE X1 X0 -4`) is byte-identical, the entry pc is set to `4·P`
so **executed steps are identical**, `|Σ|` is identical (1 for the segment rigs,
0 for the flat rig — and `P` mints nothing), the chunk inventory is identical
(X1 only), and the fuel is identical.

**Filler goes BEFORE the loop on purpose.** The loop's fall-through then still
lands exactly one past the end of the table at every `P`, so the exit/infeasible
branch has the same shape in every arm. Padding *after* would put a filler
instruction at the fall-through address and change the branch structure — a
second axis. Filler is `MV X4 X4`, the same filler `ZZU5Common` uses, so these
numbers are comparable in kind to §2.1's.

`drop_fuel` is **0** (`Verifier.v:934`), so `drop_dead` is `pure tt` and
`var_dead`'s O(K) instruction-table scan never runs. **Whatever this record
measures, it is not that scan** — a `drop_fuel > 0` sweep along this axis is a
separate (and probably much worse) story, unmeasured.

## 2. Results

### 2.1 The composed loop-body contract — exactly quadratic in P

| P | net M words | vs P=0 | marginal M/filler instr |
|---|---|---|---|
| 0 | 93.809 | 1.00× | — |
| 16 | 294.473 | 3.14× | 12.54 |
| 32 | 766.845 | 8.17× | 29.52 |
| 64 | **2526.656** | **26.93×** | 54.99 |

Exact quadratic through P ∈ {0,16,32}:

> **cost = 93.809 + 4.0506·P + 0.530681·P² M words**

Held out at P=64: predicted 2526.716 vs **actual 2526.656**, i.e. **+0.0024%**
— 24 parts per million, on a point 3.3× outside the fit range. This is the
tightest held-out fit in this directory, and it is a genuine **exponent**, not a
constant factor. The quadratic term overtakes the linear one at **P = 7.6**, so
a program of more than ~8 instructions is already in the quadratic regime.

### 2.2 …and it needs the unknown counter. Pinning removes the exponent.

Same contract, same `|Σ|`, same chunks, same table, same steps; only `k = 5`
added to the path condition:

| P | unpinned | pinned | ratio |
|---|---|---|---|
| 0 | 93.809 | 5.789 | 16.2× |
| 16 | 294.473 | 6.289 | 46.8× |
| 32 | 766.845 | 6.859 | 111.8× |
| 64 | 2526.656 | 8.227 | **307.1×** |

The pinned arm is `5.777 + 0.0334·P` (held-out linear −3.77%), **1.42× over the
whole range**. So `composition-payoff.md` §2.4's pinning effect is not a 9.19×
constant — **it is a factor that grows linearly in program length**, and 9.19×
is its value at a 2-instruction program.

### 2.3 The flat unrolled VC of the same loop is linear and nearly free

`X1` pinned concrete, so exactly `N` trips execute.

| P | net M words (N=8) | vs P=0 |
|---|---|---|
| 0 | 15.646 | 1.00× |
| 16 | 17.835 | 1.14× |
| 32 | 20.115 | 1.29× |
| 64 | 25.004 | **1.60×** |

`15.631 + 0.1397·P`, held-out linear **−1.74%**. Slightly superlinear, but a
4-point series over a 1.6× effect cannot distinguish linear from quadratic and
**no exponent should be quoted**.

The prefix does, however, tax each *trip*: refitting the trip law at both ends
(N ∈ {8,16}),

| P | flat trip law | per-trip cost |
|---|---|---|
| 0 | `3.425 + 1.5277·N` | 1.528 |
| 64 | `4.245 + 2.5948·N` | 2.595 (**+69.8%**) |

so the prefix penalty is **not** a pure intercept shift. (The P=0 law reproduces
the published `3.410 + 1.5278·N` to 0.4% on the intercept and 0.007% on the
slope.)

### 2.4 A straight-line segment with symbolic values stays linear too

§2.1's rig, extended to K=64. Three *symbolic* register values (`x`,`y`,`z`),
three MVs, no branch:

| K | net M words | vs K=0 |
|---|---|---|
| 0 | 7.220 | 1.00× |
| 32 | 8.339 | 1.16× |
| 64 | 9.759 | **1.35×** |

**So symbolic values are not the trigger.** This arm carries three of them and
pays 1.35×. What the loop body has and this does not is a **branch whose
condition the solver cannot decide by computation** — in the loop body the BNE
tests `dec k ≠ 0`, which must be matched against the path-condition guard rather
than computed; pinning `k` (§2.2) turns exactly that match into a computation
and the exponent disappears.

### 2.5 Footprint moves too — the first arm in this family where it does

`composition-payoff.md` says of itself "this record says nothing about
footprint" because `top_heap_words` was byte-identical across every arm. On this
axis it is not.

| P | PB net RSS | PP net RSS | PF net RSS |
|---|---|---|---|
| 0 | 41.4 MB | 22.1 MB | 26.6 MB |
| 16 | 85.3 | 23.3 | 30.7 |
| 32 | 297.1 | 25.0 | 36.6 |
| 64 | **1317.7** | 29.9 | 50.1 |

**31.8×** on the composed arm against 1.35× and 1.88× on the others, and
`top_heap_words` finally steps off its floor (553,738,752 → 732,320,256) at
P=64. A quadratic fit on the RSS points holds out at only −7.1% and produces a
negative linear coefficient, so **do not quote a footprint coefficient** — but
the axis is unambiguously superlinear, and it is a footprint driver, not just a
throughput one.

### 2.6 Control: conjunct order in the path condition is worth 1.74×

Not the point of the study, but it explains an apparent disagreement with the
published pinning ratio and is a reproducible effect in its own right:

| arm | pin position | net M words |
|---|---|---|
| `ZZPadP0` | before the guard | 5.789 |
| `ZZPadPrev0` | after the guard | 10.062 |
| `ZZCmpBodyPin` (published rig, re-run) | after the guard | 10.660 |

**1.74× from conjunct order alone.** So §2.4's 9.19× and this record's 16.2× are
both correct and differ only in where the pin sits. (`ZZPadPrev0` vs
`ZZCmpBodyPin` differ by 5.6%, which is my rig's `repeat … ++` table wrapper
being reduced by `vm_compute` — the two rigs are otherwise the same object.)
Compare the already-known conjunct-order cost bug in
`sep_contract_fetch_instr`; ordering effects in the path condition are a
recurring theme, not a one-off.

## 3. Mechanism: the cost is TRANSIENT — the VC does not get bigger

### 3.1 Every structural count is invariant in P

`ZZLvarInstrCommon`'s `zz_all_raw` on the RAW (pre-`postprocess`) VC, at all
four prefix lengths:

| P | nodes | asserts | assumes | binders | vareqs | maxsig | sigint | occ | lw | (ang,dem,err,blk) |
|---|---|---|---|---|---|---|---|---|---|---|
| 0 | 236 | 42 | 32 | 73 | 70 | 7 | 257 | 24 | 47 | (15,29,15,30) |
| 16 | 236 | 42 | 32 | 73 | 70 | 7 | 257 | 24 | 47 | (15,29,15,30) |
| 32 | 236 | 42 | 32 | 73 | 70 | 7 | 257 | 24 | 47 | (15,29,15,30) |
| 64 | 236 | 42 | 32 | 73 | 70 | 7 | 257 | 24 | 47 | (15,29,15,30) |

**Byte-identical at every P** — every counter, including the branch structure
and the count of proof obligations. The pinned contract is likewise invariant
(224 / 38 / 30 / 69 / 67 / 6 / 179 / 10 / 17, (14,29,14,30) at all four).

So the 26.93× is **not a bigger VC**. The executor builds the same 236-node
object with the same 42 obligations and the same 15 error leaves, and pays 27×
more to do it. The K² is **entirely transient construction state**.

This is the second independent sighting of the phenomenon `base-k-hunt.md`
established for `Base(K)` ("the ENTIRE finished VC is ≤2.6% of peak heap, so
`Base(K)` is not tree-reachable at all — it is transient construction state").
That record had a *bound*; this one has an **exact invariance**, on a rig where
the driving parameter is a dial.

### 3.2 What is excluded

| candidate | why not |
|---|---|
| a larger VC / more obligations / more branches | §3.1 — every count identical |
| `var_dead`'s O(K) table scan | `drop_fuel = 0`; the drop is `pure tt` |
| `\|Σ\|` (quadratic per this directory's catalog) | `maxsig` = 7 and `sigint` = 257 at every `P`; `P` mints nothing |
| chunk count | identical at every `P` |
| executed steps | identical at every `P` (entry pc set past the filler) |
| lookup depth / occurrence count | `lw` = 47, `occ` = 24 at every `P` |
| symbolic values as such | §2.4 carries three and stays linear |
| program length alone | §2.3 / §2.4 / §2.5's pinned column all stay linear |

What is required is an **undecidable branch condition** *and* a **K-sized
instruction table**, together, and the product is spent and discarded during
construction. Note the instrument's own scope limit
(`footprint-vs-throughput.md` §2.5): it weighs formula and `vareq` payloads,
**not `AMessage` contents and not the symbolic heap** — so the unexplained mass
is, by construction, in the part it cannot see. `base-k-hunt.md` did ablate
`AMessage` snapshots and priced them at 1.7–2.1% of allocation, on the muladd
rig; if that transfers, the candidate list is thin and the remaining mass is in
per-step transport of the table through world extensions
(`persist`/`occurs_check`/`sub_comp`) rather than in anything retained.

### 3.3 Why this rig matters beyond this question

`base-k-hunt.md` closed with "`Base(K)` needs OCaml heap profiling", having
eliminated four candidates and found no cheap Coq-level handle. **This rig is
that handle.** It is a 2-instruction executed segment, a 236-node VC, and a
single integer dial that moves cost by 27× with *every* structural counter held
exactly constant; arms compile in 10–17 s. Any hypothesis about transient
construction cost can be tested here in minutes instead of on a 282-instruction
muladd prefix, and a fix's effect is unambiguous because there is nothing else
moving.

## 4. Consistency check: the muladd mid-program cuts

`plans/PLAN-muladd-full.md` records that mid-program cuts on the 282-instruction
whole-function muladd collapsed to a bare `False` at **~43.8 G words**, with the
cause listed as unidentified after four refuted hypotheses.

Extrapolating §2.1's law to K=282 gives **43.4 G words** — 0.9% from the
observed figure.

**Treat this as a hint, not a result.** A coefficient fitted on a 2-instruction
loop with `|Σ|`=1 and a two-register inventory has no business predicting a
282-instruction program with a symbolic base and ten memory cells, and agreement
this tight over a 4.4× extrapolation in K is more likely coincidence than not.
What it does justify is *promoting the K² mechanism to the leading hypothesis*
for that blowup, and the controlled test is direct: run one muladd segment
contract with its table trimmed to the segment's own instructions and see
whether the cost falls by ~(282/k)².

## 5. What this means

- **§2.1's "prefix length is nearly free" is CORRECT BUT NOT GENERAL.** It is a
  measurement of a straight-line segment, and it does not transfer to a segment
  contract with an undecidable branch — which is what every loop-invariant body
  contract is. Scoped, not retracted; annotated in place in
  `composition-payoff.md`.
- **The ADDENDUM's cost law needs the same scoping.** "A symbolic segment
  contract costs ~83–99 M words almost regardless of what it contains" is the
  value at K≈2. It is 2.5 G at K=66. The law is flat in the segment's *own*
  content and quadratic in the *surrounding program*, and every contract behind
  that ~90 M figure lived in a 2–4 instruction table.
- **Composition's break-even grows quadratically with program length.** The
  body contract alone breaks even against the flat VC at **59 trips** at P=0 and
  **972 trips** at P=64 (a full cut, body + exit contract, is ~2× both, which
  recovers the published 114 at P=0). So the technique degrades fastest exactly
  where it was meant to help — long programs.
- **The actionable fix is per-segment table trimming, and it is now worth
  (K/k)² rather than the 1.155× §2.1 implied.** A segment contract currently
  carries `cfg_instrs` = the *whole* program; it only ever fetches from its own
  segment. Letting a contract declare a sub-table needs a **sub-table
  faithfulness lemma** — if the contract's table agrees with the program's gmap
  on every address the segment can fetch, the existing `itable_rel` bridge
  should still go through. That is the highest-value item this measurement
  produces, and §4 suggests it is worth ~200× on the muladd cut.
- **It is also a footprint lever** (§2.5), which none of the other levers in
  `composition-payoff.md` are, so it plausibly bears on the `mlen`=2 memory wall
  and on `footprint-vs-throughput.md`'s `Base(K)` block. Note the two are
  measured on different rigs and their exponents differ (that record's muladd
  prefixes imply steeper than quadratic); **do not equate the coefficients.**
- **The cost is transient, so this is a lever on the class of driver nothing
  else in this directory can reach.** §3.1's exact invariance means no amount of
  pruning, classing or postprocessing the *result* can help; the win has to come
  from not doing the construction work, i.e. from a smaller K. That is the same
  conclusion `base-k-hunt.md` reached for `Base(K)`, arrived at independently.
- **Amdahl, per this directory's rule:** at P=64 the K² term is 2433 M of the
  2527 M total (96.3%). On this axis there is nothing else worth attacking.

## 6. Files / reproduction

Throwaway, gitignored, none in `_CoqProject`:

| purpose | files |
|---|---|
| shared definitions | `Example/ZZPadCommon.v`, baseline `ZZPadBase.v` |
| composed body, prefix axis | `Example/ZZPadB{0,16,32,64}.v` |
| pinned body, prefix axis | `Example/ZZPadP{0,16,32,64}.v` |
| flat unrolled, prefix axis | `Example/ZZPadF{0,16,32,64}.v`, `ZZPadFN16_{0,64}.v` |
| conjunct-order control | `Example/ZZPadPrev0.v` |
| straight-line comparison | `Example/ZZU5_K64.v` (new point on §2.1's rig) |
| structural counts | `Example/ZZPadI{0,16,32,64}.v` + `ZZLvarInstrCommon.v` |

```bash
OCAMLRUNPARAM='v=0x400' /usr/bin/time -f "RSS %M KB WALL %e s" \
  coqc -q -w none -Q case_study/RiscvPmp Katamaran.RiscvPmp -R theories Katamaran \
  case_study/RiscvPmp/CFGVer/Example/<probe>.v 2>&1 \
  | grep -E 'allocated_words|top_heap_words|RSS|Error'
```

Traps hit here:

- **`ZZLvarInstrCommon.vo` goes stale** against a rebuilt `Prelude.vo` and fails
  with *"makes inconsistent assumptions over library"* — exactly the trap
  `footprint-vs-throughput.md` §5 records. Rebuild it before the count arms.
  Without the `Error` grep these arms read as *free*.
- **Pad BEFORE, not after.** Padding after the loop puts a filler instruction at
  the fall-through address, so the branch that is infeasible at P=0 becomes a
  further executed step — a second axis silently added to the one under test.
