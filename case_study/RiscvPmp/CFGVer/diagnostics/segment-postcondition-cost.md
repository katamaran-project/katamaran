# A real cut postcondition is FREE to prove — 0.5–2.1% over `asn_no_post`

Status: **Diagnostic record, 2026-09-14.** This is `plans/PLAN-muladd-composed.md`
§R3 step 2 ("price a segment non-vacuously"), narrowed after a record sweep to
the one axis that was actually unmeasured.

## One-sentence finding

Replacing a segment's real cut postcondition with `asn_no_post` — one token, in
two otherwise byte-identical files — changes the cost by **1.0054×** on a loop
body and **1.0212×** on a straight-line segment, so **what a cut PROMISES is
essentially free to discharge**; the per-segment cost is the symbolic execution
of its instructions, at roughly **12.7 M words per instruction** with near-zero
fixed cost.

## Why only this axis

§R3 step 2 as written asks for a segment priced "at two different segment
sizes". A sweep of this directory and of the plan's own tables found the SIZE
axis already measured, post-fix, at five sizes (below), so re-running it would
have re-derived an existing result. What no record contained was the axis §R1
actually worried about — *cheap to state* versus *cheap to prove*. That is the
postcondition-strength axis, and it is what this record measures.

## 0. Protocol

| tag | protocol |
|---|---|
| **ALLOC** | `OCAMLRUNPARAM='v=0x400'`, one heavy proof per `coqc` process, `allocated_words` net of an imports-only baseline **re-measured in the same session**, `/usr/bin/time` for RSS |

**Proof protocol is `Proof. solve_param_vc. Qed.` in BOTH arms of both pairs** —
identical, because each `nopost` arm was generated from its `real` arm by `sed`
on the single postcondition token, so no other token can differ. Verified by
`diff`: exactly one line, in both pairs.

Both pairs produced a `.vo`, i.e. both arms genuinely closed. (A `solve_vc` that
cannot close does extra work and its cost is an upper bound only — that trap is
already recorded in the plan's Phase 2.)

Baselines are per-pair, because the L arms `Require` one extra file:
`ZZPostM_base` = 642,054,273; `ZZPostL_base` = 678,472,325. The M baseline
agrees with the plan's Phase-1 `ZZMladBase` (641,953,144) to **0.016%**, which is
what licenses comparing today's numbers against that table.

`top_heap_words` is byte-identical (553,848,832) across every M arm and peak RSS
moves ≤2.2%, matching `composition-payoff.md`: this rig says nothing about
footprint.

## 1. Axes

| axis | states | how it is moved |
|---|---|---|
| `post-strength` | `real` \| `no_post` | the contract's final field: `amBody_post`/`sgL_post` vs `asn_no_post` |
| `segment-kind` | `loop-body` \| `straight-line` | which segment the pair is built from (M vs L) |

`segment-kind` is a second axis and is NOT read as a one-knob comparison here —
it is present only to check whether the `post-strength` result transfers.

## 2. Results — the postcondition axis

| pair | segment | instrs | real | `asn_no_post` | ratio |
|---|---|---:|---:|---:|---:|
| M | `br_i31_sub` body | 13 | 162.41 M | 161.53 M | **1.0054×** |
| L | segment L, straight-line | 14 | 190.75 M | 186.80 M | **1.0212×** |

Both arms of each pair differ by exactly one token. The postcondition M carries
is ten conjuncts (two walking registers with their `secLeak` facts, the end
pointer, two memory cells, the post register block, `minimal_pre`); L's is
comparable. `asn_no_post` is `asn.formula (formula_bool (term_val ty.bool true))`
— trivially true, so the `real` arm is strictly the stronger goal.

**0.5–2.1%.** For comparison, the `Qed`-vs-`Admitted` protocol gap is 1.81× and
the largest genuine effect in this directory is ~1.8×.

## 3. The size axis, recomputed — and a retraction

**RETRACTED 2026-09-14, mine, same day:** I read the plan's Phase-2 QED table
(`D 0.705 G`, `K 0.801 G`, `M 0.784 G`, `G 0.856 G`, `I 0.998 G`) as NET and
concluded "per-segment cost is almost size-independent — 1.42× over a 4.8× size
range — hence constant-dominated". **Those are GROSS figures.** The plan's own
Phase-1 table states the protocol explicitly (`856.390 M allocated | 214.4 M net
| baseline 641,953,144`), and `0.856 G` is that row's gross column. Never quote
1.42× or "size-independent"; the 1.42× was the import closure.

Net of the 642.0 M baseline:

| segment | instrs | gross | net | kind |
|---|---:|---:|---:|---|
| D memmove | 6 | 0.705 G | 63 M | loop body, 2 cells |
| M `br_i31_sub` | 13 | 0.784 G | 142 M | loop body, 2 cells |
| K `br_i31_add` | 13 | 0.801 G | 159 M | loop body, 2 cells |
| G `br_divrem` | 27 | 0.856 G | 214 M | loop body, **0 cells** |
| I limb-accumulate | 29 | 0.998 G | 356 M | loop body, 2 cells |

**5.6× over a 4.8× size range** — cost is close to PROPORTIONAL to segment size,
not constant-dominated. Least squares on the three two-cell loop-body sizes
(D, K/M mean, I) gives

    net ≈ -14.3 + 12.76 M words per instruction

**Held-out checks, and the law is LOOSE:**

| point | predicted | measured | error |
|---|---:|---:|---:|
| L (14 instrs, straight-line, `no_post`) | 164.3 M | 186.8 M | **+13.7%** |
| G (27 instrs, register-only) | 330.2 M | 214 M | **−35.2%** |

So `12.7 M/instruction` is a ±15% rule of thumb for a two-cell loop body and
nothing stronger. G's −35% is the informative one: it is the only segment with
**no memory cells**, so the per-instruction slope is partly a cell-inventory
cost, not instruction count alone. Do not use this law to predict a segment of
an unfamiliar shape.

One independent confirmation worth recording: today's M measurement (162.4 M)
lands within **2%** of the fit's prediction for 13 instructions (152 M is the
fit; 150.5 M was the five-day-old mean of K and M) — a point measured in a
different session on a later tree, agreeing with the old table.

## 4. Reading the axes apart

- **`post-strength` is isolated**: one token, `diff`-verified, same proof script,
  same baseline, same session. 1.0054× / 1.0212×.
- **`segment-kind` is NOT isolated** and is not claimed as a measurement — M and
  L differ in instruction count, register inventory and control flow. It is used
  only to show the `post-strength` result is not an artifact of one segment.
- **A tempting reading to avoid:** the plan's table shows M (real post, 142 M)
  cheaper than K (`asn_no_post`, 159 M), which looks like "a real post is
  cheaper". It is not evidence — M and K are different loops (`sub` vs `add`,
  arithmetic vs logical shift). Today's matched pair is what settles the sign,
  and it is +0.54%, not −11%.

## 5. What this means

- **§R1's "cheap to state ≠ cheap to prove" is CLOSED for the postcondition
  axis.** A cut postcondition costs ~1% to discharge. The cost of a cut is the
  cost of executing its instructions, which you pay whether you cut there or
  not.
- **Consequence for §R0's linearity claim**: cost tracks INSTRUCTIONS, not CUTS.
  Verifying a program in `n` segments costs about what the same instructions
  cost in one piece, however `n` is chosen — so the segment count is nearly free
  and can be chosen for proof clarity, matching `composition-payoff.md`'s
  post-`cfdcc92f` verdict ("cut where it makes the proof clearer") from a
  different direction.
- **What is still NOT measured**: the Iris-level COMPOSITION cost (chaining
  segments in `ZZMladTail.v` / the Phase-5 bridge) is a separate pipeline from
  the VC cost priced here, and no record prices it for a chain longer than the
  three-segment tail. That is the remaining half of §R0(1).
- **Not a fix candidate.** Nothing here is worth optimising: at ~1% the
  postcondition is not a driver, and the per-instruction cost is the executor
  doing the work it exists to do.

## 6. Files / reproduction

Throwaway probes, not in `_CoqProject`, generated by `sed` from the tracked
originals so only the intended token differs:

    ZZPostM_base.v / ZZPostM_real.v / ZZPostM_nopost.v   (from ZZMladSubBody.v)
    ZZPostL_base.v / ZZPostL_real.v / ZZPostL_nopost.v   (from ZZMladSgL.v)

```bash
cp ZZMladSubBody.v ZZPostM_real.v
sed 's/^    amBody_post\.$/    asn_no_post./' ZZMladSubBody.v > ZZPostM_nopost.v
diff ZZPostM_real.v ZZPostM_nopost.v        # MUST be exactly one line

OCAMLRUNPARAM='v=0x400' /usr/bin/time -f "@@rss=%MkB wall=%e user=%U" \
  coqc -w none -Q case_study/RiscvPmp Katamaran.RiscvPmp -R theories Katamaran \
  case_study/RiscvPmp/CFGVer/Example/ZZPostM_real.v
```

Run the arms SEQUENTIALLY — each peaks at ~4.2 GB and this box has 14 GB.

**Method note.** `make … | tail` and `coqc … | grep` both report the PIPE's exit
code, not the compiler's. A failed `GenCompose.v` build was read as green that
way earlier the same day. Check the compiler's own status, and confirm the
artifact exists (`ls *.vo`) before trusting a number — a run that fails to
compile reports only baseline-level allocation, which reads as "this variant is
free."
