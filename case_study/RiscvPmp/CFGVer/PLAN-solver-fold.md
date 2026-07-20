# PLAN-solver-fold — fold two masking rounds into one closed form

## Design decisions this session (2026-07-20) — supersede parts of the sections below

These were settled with the user after the DRAFT below was written; where they
conflict with a later section, these win. A full rewrite of the Phase sections
around them is pending (representation still being pinned down with proofs).

- **LOCKED — recognition is factored into reusable ct-idiom rules, not one
  monolithic `mask_of` recognizer.** The single idiom-specific unit is the
  **constant-time is-zero test** `((x-1) & ~x) >> (n-1)` — ubiquitous in crypto
  (comparisons, ct-select, ct-swap), so recognizing it once pays off across the
  corpus. `mask_of` then emerges as: is-zero ∘ (subtract-1 broadcast) ∘
  (and-with-constant select). The generic GF(2) rules (shift-over-xor,
  shift-composition, const-fold, select distribution, xor AC-normalize) do the
  rest.
- **LOCKED — the is-zero rule is polymorphic in the bitvector width `n`** (shift
  amount `n-1`, `ones` = `bv.ones n`). One soundness lemma, generic in `n`.
- **LOCKED — all canonical forms stay in pure `bv` arithmetic; NO `relop`/
  `term_eq`, NO `bool`-typed sub-terms.** Reason: this loop's values are all
  secret (`NonSyncVal`), and any `bool` that reaches a `formula_bool`/
  `formula_relop`/`secLeak` position collapses to `False`. A pure-`bv` form never
  produces a `bool`, so it is *structurally immune* to that trap. `term_eq` on a
  secret is safe only as a value and thin-margin fragile — we avoid it entirely.
  See the **`relval-semantics`** skill for the full model (SyncVal/NonSyncVal,
  the three `NonSyncVal ⇒ False` walls, and why pure-`bv` identities are
  auto-sound over secrets). This means the is-zero output is a `bv` "0/1" form
  (e.g. via `bvcons`/`bvand`), NOT `bvcons (term_eq x 0) …`.
- **DIRECTION (not yet proof-locked) — representation is the per-bit incremental
  form** `V_n = (A >> n) ^ XOR_{i<n} (bit_i(A) ? C_i : 0)`, one summand appended
  per round, `C_i = mulx^{(n-1-i)}(R)` — NOT the 2^k doubling ladder (Phase 0's
  "doubling" sub-lemmas below). O(n) term size, no tables, capped at ~33 terms
  since `A>>n = 0` for `n ≥ 32`. The `? C : 0` selects are pure-`bv` sugar per the
  all-bvec decision, not `bool` selects.

---

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

Crucially, the folded step `g_k(A) = (A >> k) XOR T_k[A & (2^k-1)]` is
ITSELF GF(2)-linear — so folds compose. `g_k ∘ g_k = g_2k` with a
concretely computable table:

```
T_2k[(y,x)] = (T_k[x] >> k) XOR T_k[y XOR low_k(T_k[x])]
```

where `x` = low k bits, `y` = next k bits of the selector. And while the
table entries have ≥ k low zero bits, `low_k(T_k[x]) = 0` and this
simplifies to `T_2k[(y,x)] = (T_k[x] >> k) XOR T_k[y]`. `R = 0xE1000000`
has 24 low zero bits, and each doubling erodes that by k, so the simple
regime holds comfortably through k=8 (entries retain ≥17 low zeros).

Hand-derived concrete values to check Phase 0 against (from the actual
instruction sequence: `LUI 921600` = `0xE1000 << 12` = `0xE1000000` = R;
`RISCV_SRLI` logical; the ANDI/XORI/ADDI/AND/SRLI/ADDI chain = all-ones
mask iff bit0=1 — traced by hand, Phase 0 re-verifies mechanically):

- `T_1 = [0; 0xE1000000]` (this is `f` itself, bit0-indexed)
- `T_2 = [0; 0x70800000; 0xE1000000; 0x91800000]` (indexed by bits (1,0))
- `T_4` (16 entries), `T_8` (256 entries): computed by the doubling
  formula, each doubling provable by finite enumeration (16 / 256 / 65536
  case `vm_compute` checks — the last only if k=16 is ever wanted, which
  also exits the simple regime; k=8 is the planned ceiling).

**The ladder** (occurrences of A0 in the final term at N=64):

| Level | Table | A0-occurrences at N=64 | Reach |
|---|---|---|---|
| k=2 fold only | 4 entries | 2^32 | N≈12 — NOT the target |
| doubling to k=8 | 256 entries | 2^8 = 256 | N=64 comfortably; N=128 (2^16 occs) borderline |
| GF(2) matrix normal form | 32×32 concrete matrix | ~constant | unbounded, any linear code |

This plan targets **the k=8 row** — the k=2 fold alone (the original
scoping) does NOT reach N=64 and is only the first rung. The matrix
normal form is the documented endpoint (a linear map's canonical 128-byte
representation; CORR tables are an encoding that wastes 2^k entries) —
NOT planned work, but written down so a future need for more linear-
masking examples knows where this road ends.

## What this buys, and why the havoc failure does NOT condemn it

Each folded step references its input exactly twice (shift + selector),
so k-fold steps give 2^(N/k) A0-occurrences: the exponent divides by k.
k=2 alone halves it (insufficient, see ladder); climbing to k=8 brings
N=64 down to ~256 occurrences — comfortably in vm_compute range. The
stored table entries along the way (iteration i's value written to
memory) carry fold-depth ~i/k, so total VC size ≈ Σ 2^(i/k) ≈ 2·2^(N/k)
— same bound, still fine at k=8/N=64.

Why trust a term-size fix after havoc — the ultimate term-size fix,
size 1 — failed? Because the two prior failures bracket this approach
rather than condemning it: havoc's residual cost tracked the number of
FRESH DEMONIC VARIABLES introduced (per the bisection), a cost the fold
never incurs (zero new binders — it shrinks terms in place over the same
A0). And the original mimic probes showed that WITHOUT added binders,
traversal cost genuinely tracks syntactic term size — which is exactly
the quantity the fold reduces. Still, predictions in this saga have a
poor track record: the Phase 1 probe gate below is mandatory before any
proof investment.

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
Structure it **compositionally from day one** so the ladder is nearly free:
- Write `f` as a plain Gallina function over `bv 32` (not `Term`),
  mirroring the exact ALU ops of the instruction sequence (including the
  `x-1` mask idiom — note `ADDI -1` is NOT GF(2)-linear in general, only
  on the bit-valued domain the idiom restricts it to; the lemma absorbs
  this, the linearity story is motivation not proof structure).
- Define the general folded form `g T k a = (a >> k) ^ T[a & (2^k-1)]`
  (table as a function/vector over `bv k` indices).
- Prove TWO lemmas: (i) **base**: `f (f a) = g T_2 2 a` with `T_2` as
  derived above; (ii) **doubling**: `g T k (g T k a) = g (dbl T k) (2*k) a`
  where `dbl` is the concrete table-doubling formula — proven either
  generically (shift/xor/extract algebra) or per-instance at k=2→4 and
  k=4→8 by finite enumeration of the selector bits (16 / 256 cases,
  `vm_compute`-checkable) with the high bits handled by one generic
  split lemma. Enumeration-per-instance is fine; only k=2,4 instances
  are needed.
- Sanity-check the derived `T_2` against the hand-derived values recorded
  above; disagreement means the hand trace was wrong somewhere — find out
  which before proceeding.
- **Decision gate**: if the base identity doesn't go through cleanly (or
  reveals the real instruction sequence isn't quite the idealized `f` —
  e.g. an off-by-one in which bit is tested), stop and reassess before
  Phase 1.

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
  given a term, returns `Some (k, X)` if the term matches "`g_k` applied
  to `X`" — where the recognized shapes are (a) one RAW masking round
  (k=1) and (b) **an already-folded step** `(X >> k) ^ T_k[X & mask]`
  with a recognized table constant. (b) is NOT optional: without it the
  ladder never climbs — fold-of-folds is where all the leverage is.
- In `peval_binop`, add a case for the outer combining op (the final XOR)
  that: recognizes the outer application as `g_j` of some inner term `B`,
  checks whether `B` is `g_k(X)` with `j = k` (equal-k folds only — that
  is what the doubling lemma covers), and if so emits `g_2k(X)` with the
  doubled table (up to the k=8 ceiling; beyond that, leave the term
  alone); otherwise falls through to today's behavior unchanged.
  Bottom-up recursion (`peval'` at `PartialEvaluation.v:1686-1696`)
  guarantees operands are already normalized — including already-folded —
  by the time this case runs.
  - Wrinkle to design around: rounds arrive one at a time (one
    instruction each), so the term after round 3 is `f(g_2(X))` —
    unequal levels. The k=1 raw round only pairs with another k=1. This
    still works out: rounds fold in a binary-counter pattern (1+1→2,
    then 1 pending, 1+1→2, 2+2→4, ...), keeping ≤ log k pending
    unequal-level wrappers at any time — sizes stay bounded, the ladder
    climbs every power-of-two boundary. No unequal-k doubling lemma is
    needed. Verify this dynamic actually materializes in Phase 1's probe
    rather than trusting the paper argument.
- **Throwaway timing check**: before writing any soundness proof, verify
  the fold actually fires and actually helps — reuse the isolated
  single-Goal probe methodology from the havoc experiments (`Time
  vm_compute` on `ValidCFGVerifierContract`, sweeping N) against the
  *unpatched* executor plus this new `peval` case, comparing against the
  documented baseline curve. Then push N directly: 8, 16, 32, 64 — with
  the ladder live there is no reason to stop at small N. **Decision
  gate**: N=64 discharging in minutes-or-less is the bar for proceeding
  to the soundness proof; if the pattern doesn't fire (peval's real term
  shape differs from the assumed one) fix the recognizer; if it fires
  but the curve doesn't collapse, stop and re-diagnose — that would mean
  a THIRD cost driver beyond term size and binder count, and more
  probing beats more building at that point.

## Phase 2 — soundness proof (the real cost)

- Extend `peval_binop_sound`/`peval'_sound` (`PartialEvaluation.v:~1704-
  1729`) to cover the new case: the rule must produce a term denoting
  the same value as the un-folded expression, for *every* instantiation
  — exactly Phase 0's two lemmas (base + doubling), lifted from plain
  `bv 32` values to symbolic `Term`s under an arbitrary valuation. The
  recognizer's correctness ("returns `Some (k, X)` only if the term
  really denotes `g_k` of `X`'s denotation") is the bridge lemma; the
  `Term`-level proof adds substitution/evaluation-commutes bookkeeping.
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
  Record the final curve; acceptance is the ORIGINAL goal from
  `PLAN-term-sharing.md`: end-to-end noninterference at **N=64**
  (Phase 1's probe gate should have already demonstrated the raw VC
  discharge there; this phase confirms nothing regressed under the
  proven rule and wires the real `Example/KeyScheduleLoop.v` contract
  rather than probe copies). Stretch: N=128 (2^16 A0-occurrences —
  measure, don't promise).

## Documented endpoint (NOT planned work): GF(2)-linear normal form

If more linear-masking examples accumulate, or N=128+ is ever required,
the principled generalization is to normalize every A0-linear register
value to a concrete 32×32 GF(2) matrix (+ affine constant) applied to
A0 — constant-size values regardless of depth, composition by concrete
matrix multiply, any linear code covered without per-idiom recognizers.
The CORR-table ladder is that idea specialized to powers of one fixed
map with a 2^k-entry encoding; the matrix form is where this road ends.
Recorded here so the next scaling wall starts from this paragraph, not
from scratch.

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
- The binary-counter folding dynamic (unequal pending levels between
  power-of-two boundaries) is a paper argument until Phase 1's probe
  confirms it — if peval's interleaving breaks it, sizes between
  boundaries could grow more than expected.
- Phase 1's gate now REQUIRES demonstrating N=64 on the throwaway rule
  before the soundness proof is funded — the proof cost is only sunk
  against a measured win, per the lesson of the two refuted plans.
