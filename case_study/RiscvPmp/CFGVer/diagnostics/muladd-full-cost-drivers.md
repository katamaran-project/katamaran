# muladd whole-function at mlen=2: the wall is TERM DUPLICATION, and dense havoc trades it for `|Σ|`

**Finding, one sentence.** `br_i31_muladd_small` at `mlen`=2 does not verify: the
wall is **symbolic tree CONSTRUCTION** (never reaching `solve_vc`), caused by
symbolic terms being *copied* rather than shared — one register was dumped
holding a **215,636-character** term in which a single havoc-minted variable
appears **460 times** — and havocing after every instruction removes it, at the
price of converting the problem into a quadratic `|Σ|` cost that the existing
variable drop makes **4.3× worse**, not better.

Date 2026-09-01. Supersedes `PLAN-muladd-full.md` Phase 3's "BLOCKED, cause
unidentified" (2026-08-11), which predates chunk-GC, word slicing, classed
existentials, `bop.mulx` and the fetch-bound solver rule.

## 1. Status of the target

| attempt | result |
|---|---|
| whole function, as it stood (`ZZMuladdFullN2.v`, `vm_compute; solve_vc; Qed`) | killed at 14.5 min, empty log |
| raw VC only (no `Qed`, no `solve_vc`) | killed at 16 min |
| whole function + loop-head havoc, raw VC | killed at 17 min |
| whole function + 111-site dense havoc, raw VC | killed at 9 min and at 19 min (two budgets) |

**The raw-VC kill is the load-bearing one: it localises the wall to CONSTRUCTION.**
`solve_vc` and the `Qed` are never reached, so nothing about VC discharge is
implicated. Cause of each kill is *not established* — `journalctl`/`dmesg` are
restricted on this box (same limitation as `havoc-abstraction-payoff.md` §8.5);
memory exhaustion is the obvious candidate given RSS 7.2 GB at 96 s and rising
~4.5 GB/min on a 14 GB box. **Do not record these as confirmed OOMs.**

## 2. The axes

| axis | states |
|---|---|
| `prefix` | K = first K instructions of 282 (`List.firstn`), i.e. how many of the 7 loops are included |
| `havoc-granularity` | none / loop-head only (5 sites) / dense per-instruction (25 limb-only, or 111 all-blocks) |
| `drop_fuel` | 0 / 8 |

Program: 282 instructions, 7 loops, `br_divrem` inlined **twice** (dead
small-modulus path head idx 16, live main path head idx 135), the `mlen`-sized
limb multiply-accumulate at 190–218, two word loops at 237–249 / 264–276.
**`br_divrem`'s trip count is patched to 2** in this probe (header deviation 3),
so today's `dropk-firing-payoff.md` Part 3 result — which is about that loop at
**32** trips — contributes almost nothing here. Said explicitly because it is the
natural wrong inference to draw.

## 3. Results

### 3.1 Prefix sweep, no dense havoc — WALL CLOCK, indicative only

| K | ends after | tree size | peak `\|Σ\|` | wall |
|---|---|---|---|---|
| 41 | dead divrem copy | 371 | 33 | 14 s |
| 90 | memmove loop | 4 511 | 33 | 20 s |
| 118 | 2nd short loop | 6 960 | 33 | 19 s |
| 162 | **live divrem** | 16 180 | 33 | 39 s |
| 164 | +`bgeu` | 16 436 | 33 | 52 s |
| 176 | mid q-block | 18 010 | 33 | 84 s |
| 190 | **q-block done** | 19 484 | 33 | **295 s** |
| 219 | +limb loop | — | — | **died >600 s** |

**Peak `|Σ|` is FLAT at 33 throughout.** From K=162→190 time grows **7.5×** while
node count grows **1.2×**. Cost per node is exploding: that is term size, and it
rules out both the declared-`|Σ|` driver and any tree/path-count explanation.

### 3.2 The direct evidence: a dumped term

`AnnotDebugBreak` planted at idx 205 (inside the limb loop, havoc active),
postprocessed tree, `Set Printing Depth 1000000`. 33 debug nodes; largest
register term per node rises 52 → 129 → 216 → 42 776 → 129 206 → **215 636 chars**.

At the final node:

| reg | | term chars |
|---|---|---|
| x16 | **A6 — the carry** | **215 636** |
| x28 | T3 | 43 042 |
| x29 | T4 | 42 989 |
| x5 | T0 (`q`) | 42 776 |

Inside that one A6 term, `hv.11` appears **460** times and `hv.12` **500** times.
These are *single havoc-minted variables* (~14 chars each). **Nothing was computed
460 times; the same leaf was transcribed 460 times**, because the term
representation is a TREE with no sharing: reading a register inlines its entire
term rather than referencing it.

Mechanism, from the body (A6 is read at 194, 198, 200, then its copies are re-read
at 201 and 203): roughly one doubling every two instructions. 2⁹ = 512 ≈ the 460–500
observed over ~15 instructions.

### 3.3 Two hypotheses ELIMINATED — do not re-investigate

**Protocol for both: raw VC, no `Qed`, one heavy `Eval` per process,
`OCAMLRUNPARAM=v=0x400`, imports baseline 620,664,005 subtracted. Arms differ in
ONE token.**

| prefix | adds | net G | ratio |
|---|---|---|---|
| 191 | loop head + `lw` | 4.169 | — |
| 193 | **`MULHU` + `MUL`** | 4.510 | **1.082×** |
| 205 | 12-instr carry/mask chain | 11.552 | 2.562× |
| 206 | **the `sw`** | 12.104 | **1.048×** |

- **Symbolic store-address disambiguation: 4.8%. NOT the driver.** This also
  means an `asn_havoc_mem` (no memory havoc exists — `asn_havoc_reg`,
  `Spec.v:764`, emits `chunk_ptsreg` only) is **not** indicated by this evidence.
- **The M-extension `MUL`/`MULHU`: 8.2%. NOT the driver.** The project's only
  use of these opcodes; they are fine.
- What remains is the **12-instruction carry/mask chain**, at 2.562× — i.e.
  ~1.08× per instruction, diffuse, with no single culprit.

### 3.4 Havoc granularity — the result that matters

| K=219 (through the limb loop) | outcome |
|---|---|
| loop-head havoc only (5 sites) | **died** >270 s |
| dense per-instruction havoc (25 sites in the limb body) | **155 s, 19.408 G net, size 28948** |

Dense havoc is what makes the block complete at all. At the matched K=190 point,
loop-head havoc alone is 34.4 s vs 294.7 s without (**8.6×** — *wall clock, and
the no-havoc arm's u/s split was not captured; treat as indicative, not
measured*), with tree size unchanged (+0.2%) and `|Σ|` up by exactly the fresh
variables. Loop-head havoc kills **cross-trip** duplication; only dense havoc
kills **within-trip** duplication.

**This inverts `Spec.v:773`'s standing advice** ("HAVOC THE MINIMUM SET"). That
was measured at loop-head granularity, where a temp havoc buys nothing and costs
a binder. At per-instruction granularity the same annotation is what stops the
doubling. Second inversion of that advice in a week — see
`havoc-abstraction-payoff.md` §9.5 for the first.

### 3.5 What dense havoc costs: it TRADES the problem

Same file, same metric, **only `drop_fuel` differs** (K=206, 111 dense sites):

| `drop_fuel` | peak `\|Σ\|` | net G | protocol |
|---|---|---|---|
| 0 | **135** | **10.546** | raw VC, no Qed, one Eval |
| 8 | **33** | **45.355** | ″ |

The drop works **perfectly** — it retires all ~102 dense-havoc variables, landing
exactly on the no-havoc baseline of 33 — and costs **4.30× more**. `var_dead`
occurs-checks every candidate against path condition, heap, `trans`, `apc`,
`anp`, table and exits at every step; with a 30-chunk heap that scan exceeds what
the variables cost. **The opposite of `dropk-firing-payoff.md` Part 3**, where
`|Σ|` grew 7/trip over 32 trips and the saving was quadratic. Same code, opposite
verdict, decided by (variables × laps), not by variables alone.

*Caveat: the fuel-8 arm reuses the fuel-0 import baseline. On the br_divrem rig the
two baselines differed by 0.0003%, immaterial to a 4.3× ratio, but it was not
re-measured here.*

### 3.6 The residual driver: `|Σ|`, quadratic

Dense havoc (fuel 0), net of baseline:

| K | peak `\|Σ\|` | net G | marginal cost/instruction |
|---|---|---|---|
| 118 | 33 | 0.904 | 7.7 M |
| 162 | 96 | 4.387 | 79 M |
| 206 | 135 | 10.546 | 140 M |

Per-instruction cost tracks **`|Σ|²`**: predicted (96/33)² = 8.5 and (135/33)² =
16.7; observed 10.3× and 18.3×. Within ~20%, consistent with
`lvar-lookup-cost-drivers.md`'s quadratic law. **This is corroboration, not a
fit** — `|Σ|` varies inside each segment, and no held-out point was withheld.

The anchoring datum is the first row: **at `|Σ|` = 33, muladd costs 7.7 M
words/instruction — essentially br_divrem's own 6.8 M/instruction** under
havoc+drop (`dropk-firing-payoff.md` Part 3: 183.0 M/trip ÷ 27 instructions).
When `|Σ|` is small this function is already as cheap per instruction as the loop
that was made linear the same day. Everything above that is the `|Σ|` penalty
that dense havoc itself creates.

## 4. What this means

- **The exponential is gone; a quadratic replaced it.** Dense havoc converts term
  duplication (2^k) into logic-variable count (`|Σ|²`). A large improvement in
  kind, but the constant is bad and `mlen`=2 still does not complete.
- **`asn_havoc_mem` is NOT the indicated build** (§3.3). Register havoc plus
  memory havoc would not have helped; the store is 4.8%.
- **The drop cannot collect what dense havoc mints, economically, at this shape.**
  Two untried levers: (a) `drop_fuel` is UNTUNED — 8 is a probe value, only a
  couple of variables die per step here, so 1–2 may capture most of the
  retirement at a quarter of the scan; (b) **packing** — slice each block's
  per-trip havoc values out of ONE wide binder
  (`havoc-abstraction-payoff.md` §8.5), taking `|Σ|` growth from k/trip to 1/trip
  with no scan at all.
- **Deeper lever, planned but unstarted:** `theories/plans/PLAN-env-trie.md` —
  `env.lookup` is a linear walk, which is why `|Σ|` cost is quadratic. Its §0
  states honestly that the upside is unquantified, and its Phase 0b is the
  measurement that would also explain §3.5's 4.3×.
- **Not established:** everything here is raw-VC CONSTRUCTION cost. No `Qed`, no
  `solve_vc`. And 111 havoc sites make a great deal of data possibly-secret (a
  havoced value carries no `secLeakvar`), so the risk shifts from cost to
  COMPLETENESS: the VC may turn to `False` at `solve_vc` rather than merely be
  slow. Untested.

## 5. Files / reproduction

**`Example/ZZMuladdFullN2.v` is the root artifact** — the hardened, `-flto`-
inlined, AST-translated whole function from PLAN-muladd-full Phases 0–2. Every
probe below is generated from it. It is NOT regenerable without redoing those
phases (fetch BearSSL, apply `opaque()` barriers, clang `-flto`, `asm_to_ast.py`).

Derived throwaway probes (gitignored, not in `_CoqProject`), all produced from it
by single-token `sed`/python edits so only the intended axis can differ:

| file | what |
|---|---|
| `ZZMuladdPrefix.v` | prefix sweep, no havoc (§3.1) |
| `ZZMuladdPrefixHavoc.v` / `…HavocAll.v` | loop-head havoc, 1 site / 5 sites |
| `ZZDisc_BASE.v`, `ZZDisc{191,193,205,206}.v` | the elimination pairs (§3.3) |
| `ZZMuladdDense.v` | 25 dense sites, limb body (§3.4) |
| `ZZMuladdDenseAll.v`, `ZZDS206.v` | 111 dense sites, all blocks (§3.5–3.6) |
| `ZZMuladdDump.v` | `AnnotDebugBreak` at idx 205, postprocessed (§3.2) |

```bash
OCAMLRUNPARAM='v=0x400' coqc -q -w none \
  -Q case_study/RiscvPmp Katamaran.RiscvPmp -R theories Katamaran \
  case_study/RiscvPmp/CFGVer/Example/ZZDS206.v 2>&1 | grep allocated_words
```

Run `coqc` from the REPO ROOT — the `-Q` paths are relative, and a stray `cd`
into `Example/` makes it fail in 0.1 s while looking like a fast result (hit
once during this study). `Example/Prelude.vo` must be rebuilt between `drop_fuel`
arms. Dense-havoc site lists are generated mechanically: per block, protect
load/store **bases** (not stored values), branch operands, and ±4 pointer bumps;
havoc every other destination register.

**Box caveat.** These runs shared a 14 GB box, partly with an unrelated 4.4 GB
process, and several exceeded RAM into swap. `allocated_words` figures are
deterministic and unaffected; **every wall-clock figure here is indicative
only**, and two timings in this study came back visibly corrupted (82 min against
a 270 s timeout) from a suspended shell.
