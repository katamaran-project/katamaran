# PLAN-solver-fold — fold two masking rounds into one closed form

Status: DRAFT (2026-07-19). Third attempt at the `key_schedule_loop` scaling
wall, after Plan A (opaque naming, refuted) and havoc-the-secret (refuted) —
see `PLAN-term-sharing.md` and `PLAN-havoc-secrets.md` status headers, and
memory note `project-key-schedule-loop-scaling` for the full prior record.
User framing for this attempt: the triggering pattern (a secret rebuilt from
k≥1 copies of itself, here via a doubling/masking operation) is narrow and
uncommon enough that a general executor-level mechanism is disproportionate
— prefer a small, targeted rule recognizing this SPECIFIC operation and
folding two applications into one.

**Terminology correction (please confirm or redirect):** the request named
`Solver.v`, but that file (`combined_solver`, `solveruseronly_to_solver`,
RiscvPmp's `simplify_user` in `Sig.v`) operates purely on **path-condition
formulas** — asserted/assumed propositions — and structurally cannot see the
register **value** being computed during instruction execution (confirmed:
RiscvPmp's `simplify_user` is currently a no-op with every clause commented
out, and even a live one only ever fires on `formula_user` propositions).
The masking computation is a plain expression evaluated via `eval_exp`
(`theories/MicroSail/SymbolicExecutor.v:401-403`), which calls **`peval`**
(`theories/Symbolic/PartialEvaluation.v`) immediately on every register
write. `peval` already has a precedent of hand-written domain-specific
bitvector simplification rules (`peval_bvand_val`, `peval_bvdrop_eq`, etc.,
dispatched from `peval_binop` at `PartialEvaluation.v:750-764`) — that is
the natural and, per investigation, the *only* viable hook for this idea.
This plan targets `PartialEvaluation.v`, not `Solver.v`; flag now if a
different mechanism was actually intended.

## The math (recap, re-derived to ground the plan)

The masking round (`key_schedule_loop2_instrs`, `Example/KeyScheduleLoop.v`)
implements constant-time "multiply by x mod R" in GF(2^32):

```
f(A) = (A >> 1) XOR (bit0(A) ? R : 0)
```

`bit0(A)` (the LSB) is extracted and used to select `R` or `0` via a
branchless all-1s/all-0s mask (the ANDI/XORI/ADDI/AND/SRLI/ADDI/LUI/AND
chain), then XORed into the shifted value. `f` is GF(2)-**linear** in `A`:
shifting is linear, and "select `R` or `0` based on one bit, XOR it in" is
`bit0(A) * R` — a scalar multiple by a linear functional, hence also
linear; the sum of two linear maps is linear.

Because `f` is linear, so is `f ∘ f`. Splitting `A` as
`(A with low 2 bits zeroed) XOR (A mod 4)` and using linearity:

- `f(f(A - (A mod 4)))` = `A >> 2` exactly (zeroing the low 2 bits means
  neither round's bit-select ever triggers; two plain shifts by 1 compose
  to a shift by 2).
- `f(f(A mod 4))` is one of exactly 4 precomputable constants (`A mod 4` ∈
  {0,1,2,3}).

So: **`f(f(A)) = (A >> 2) XOR CORR[A & 3]`**, `CORR` a fixed 4-entry table.
This is the identity to fold. It generalizes to `mulxᵏ(A) = (A>>k) XOR
CORR_k[A & (2^k-1)]`, but `CORR_k` has `2^k` entries — doubling k=1→2→4
only costs a 4-entry table; going further (k=8, 16, ...) grows the table
exponentially in k, so **this plan scopes to the single pairwise fold
(k=2) only** — recursive doubling is a stretch goal, not a target.

## What this buys, and what it doesn't

Folding pairs changes the reference pattern: instead of every 2 loop
iterations rebuilding the term via 2 full 9-node masking chains (each
referencing the running value ~2-3 times, compounding to the documented
~2.5-3×/trip), one folded step references the input **twice** (once for
the shift, once for the 2-bit selector) to produce **one round's worth of
output size** for **two logical iterations of work**. Expected effect: the
per-iteration growth *exponent* roughly halves (~3×/trip → ~√3×/trip ≈
1.73×/trip for folded pairs) — a real, meaningful constant-factor win, but
**still exponential**, not a full fix. Concretely: if the original curve
made N≈6 already expensive (tens of seconds, per the documented baseline),
halving the exponent roughly *doubles* how far N can practically reach
(ballpark N≈12-ish), not open-ended scaling to N=64. Set this expectation
explicitly before starting — it matches the user's framing of "fold two
operations," not "solve arbitrary N."

This is evaluated against the **original, non-havoc executor** (`peval` as
it exists today) — havoc is fully abandoned, not combined with this idea.

## Phase 0 — nail the algebra in isolation (cheap, do first)

Before touching the executor: state and prove the identity above as a
**standalone bitvector lemma**, decoupled from any executor machinery,
using the concrete bitwidth and exact operations the instruction sequence
uses (check `RISCV_SRLI` is a *logical* shift, confirm the exact encoding
of the mask-from-bit0 idiom against `bv.of_Z (-1)`/`ADDI`/`AND` semantics,
and watch for the width-32-vs-signed-immediate gotchas `bv-pitfalls`
documents). This is the load-bearing step — if the identity doesn't hold
exactly as derived (off-by-one shift, a sign/truncation surprise), the
rest of the plan is moot, and it's far cheaper to find that out against a
standalone `bv` lemma than inside a `peval` soundness proof.
- Write `f` as a plain Gallina function over `bv 32` (not `Term`).
- Prove `f (f a) = bv.shiftr 2 a `bv.xor` CORR (bv.land a 3)` for a
  concretely-defined 4-entry `CORR`, by `bv_comp`/`lia`-style case
  analysis on `a`'s low 2 bits (likely `bv.append`/`bv.extract` lemmas,
  or a brute-force `vm_compute`-checked enumeration if `bv 32` case
  splits awkwardly — check what `bv-pitfalls` recommends for this shape).
- **Decision gate**: if this doesn't go through cleanly (or reveals the
  real instruction sequence isn't quite the idealized `f` above — e.g. an
  off-by-one in which bit is tested), stop and reassess before Phase 1.

## Phase 1 — recognize the pattern in `peval` (experiment, throwaway-able)

- Print/inspect the ACTUAL `peval`'d term shape for one round applied to a
  fresh symbolic register (`Eval cbn in` or a `Set Printing Depth` probe on
  a tiny standalone example) to get the real, exact nested-constructor
  shape to match against — do not hand-derive this blind from the RISC-V
  mnemonics; peval's own simplification (constant-folding the concrete
  immediates like `bv.of_Z 1`, `921600`, etc.) will already collapse parts
  of the chain, and the match needs to target what peval ACTUALLY produces
  post-simplification, not the raw unfolded instruction sequence.
- Add a recognizer function (analogous in style to `peval_bvdrop_eq`'s
  multi-constructor traversal, but deeper: ~8-9 nested constructors) that,
  given a term, returns `Some X` if the term matches "one masking round
  applied to `X`", else `None`.
- In `peval_binop`, add a case for the round's outer combining op (the
  final XOR) that: recognizes round 2 (giving inner term `B`), checks
  whether `B` ALSO matches round 1 (giving `X`), and if so returns the
  folded closed form on `X`; otherwise falls through to today's behavior
  (`peval_binop'` or the existing dispatch) unchanged. Bottom-up recursion
  (`peval'` at `PartialEvaluation.v:1686-1696`) guarantees operands are
  already normalized by the time this case runs — confirmed architecturally
  sound for this kind of deep, rigid match.
- **Throwaway timing check**: before writing any soundness proof, verify
  the fold actually fires and actually helps — reuse the isolated
  single-Goal probe methodology from the havoc experiments (`Time
  vm_compute` on `ValidCFGVerifierContract`, sweeping N) against the
  *unpatched* executor plus this new `peval` case, comparing against the
  documented baseline curve. **Decision gate**: if the exponent doesn't
  visibly improve (or the pattern doesn't fire because peval's real term
  shape differs from what Phase 1 assumed), fix the recognizer or stop
  before investing in the proof.

## Phase 2 — soundness proof (the real cost)

- Extend `peval_binop_sound`/`peval'_sound` (`PartialEvaluation.v:~1704-
  1729`) to cover the new case: the new rule must produce a term
  denoting the same value as the un-folded 2-round expression, for
  *every* instantiation — this is exactly Phase 0's lemma, lifted from
  plain `bv 32` values to symbolic `Term`s under an arbitrary valuation.
  Reuse Phase 0's lemma as the semantic core of this proof; the `Term`-
  level proof adds the substitution/evaluation-commutes bookkeeping.
- This is very likely the single biggest time cost in the whole plan
  (matches this codebase's general pattern: foundational proofs cost more
  than the mechanism they justify) — budget for it explicitly, and don't
  treat Phase 1's throwaway timing win as "done" until this lands.
- **Soundness risk to watch, not just performance**: an under-constrained
  recognizer could misfire on a term that superficially resembles the
  round shape but isn't semantically that operation (e.g. same op
  sequence with a different constant) — the recognizer must check the
  actual embedded constants (the specific `R`, the specific shift amounts)
  match exactly, not just the constructor skeleton, or the "fold" would
  be silently unsound.

## Phase 3 — measure against the acceptance target

- Re-run the full `key_schedule_loop2` N-sweep (not just the reduced
  ALU-only bisection probes) with the real, proven rule in place.
  Record the new curve and compare honestly against the ~3×/trip baseline
  and the ~√3×/trip prediction.
- Decide against the ORIGINAL goal (`key_schedule_loop` at N=64, stretch
  N=128, from `PLAN-term-sharing.md`): is a halved exponent enough, or
  does this only push the practical wall out by a constant factor (most
  likely outcome, per the "what this buys" section above)? If the latter,
  that's not a failure of this plan — it was scoped as a targeted,
  non-general fix from the outset — but it means N=64 needs either the
  stretch (Phase 4) or a different idea for the remaining gap.

## Phase 4 — stretch: recursive doubling (only if Phase 3 falls short)

- Fold groups of 4 rounds using `CORR_4` (16 entries), built from `CORR_2`
  by the same linearity argument applied one level up, then 8 rounds
  (`CORR_8`, 256 entries) if still needed. Table size doubles per
  doubling of k — likely impractical past k≈8-16 unless `R`'s sparse bit
  structure keeps most table entries trivially derivable rather than
  independent. Not attempted unless Phase 3's numbers make it clearly
  worthwhile.

## Regression + acceptance

- All existing examples unaffected (the new `peval` case should be a
  no-op wherever this exact round shape doesn't appear — verify, don't
  assume, same discipline as every prior plan's regression phase).
- Update **cfgver-executor**/**core-executor-internals** skills with the
  new `peval` rule in the same commit as the code change.

## Risks

- Phase 0's identity doesn't hold exactly as derived (shift-amount or
  sign gotcha) → stop before any executor work; cheapest possible failure
  point.
- `peval`'s actual post-simplification term shape differs from the
  hand-traced instruction sequence → Phase 1's inspection step exists
  precisely to catch this before the recognizer is written blind.
- The fold is idiom-specific and fragile by construction (syntactic, not
  semantic, matching) — acceptable per the user's own framing, but means
  any future rewording of the masking idiom (different instruction order,
  different constant-time trick) silently stops benefiting from this rule
  with no error, just no speedup. Worth a one-line note in
  **cfgver-executor** so a future session isn't puzzled why a
  superficially-similar loop doesn't get the same speedup.
- Even with the fold, N=64 is not guaranteed reachable (see Phase 3) —
  set this expectation now, not after Phase 2's proof cost is sunk.
