---
name: core-executor-internals
description: >
  Katamaran's CORE generic symbolic-execution monad (SPureSpec/SHeapSpec) and its
  refinement/soundness proof — the framework-wide layer underneath every case
  study's own executor (CFGVer's sexec_cfg_addr, MinimalCaps' equivalents, etc.),
  not specific to any one of them. Use when reading or modifying the generic
  choice combinators (demonic_finite, demonic_pattern_match, angelic_finite,
  angelic_pattern_match — theories/Symbolic/Monads.v), the generic statement-level
  executor `sexec`'s dispatch over Stm constructors (theories/MicroSail/
  SymbolicExecutor.v), or their refinement lemmas (refine_<combinator>,
  theories/Refinement/Monads.v, stated via the ℛ⟦⟧ logical relation and usually
  proved with Iris). ALSO use when investigating WHY a proof involving repeated
  branches or pattern-matches is unexpectedly slow or looks exponential — these
  combinators fork unconditionally with no peval/decidability short-circuit
  before building a branch, in ANY case study, not just CFGVer (see "Where the
  CFGVer loop blowup lives" below for a concrete worked trace). NOT for CFGVer's
  own executor layer built on top of this (cfgver-executor), and NOT for the
  rsolve tactic that closes CFGVer's own relational goals (cfgver-rsolve) — this
  skill is about the shared core monad's own refinement lemmas, one layer
  further down than either of those.
---

# Core symbolic-execution monad internals

The layer every case study's own executor is built on. If you're working purely
inside `case_study/RiscvPmp/CFGVer/`, you usually want **cfgver-executor**
instead (CFGVer's `sexec_cfg_addr`, built ON this layer) or **cfgver-refinement**
(the `sexec_cfg_addr`/`cexec_cfg_addr` relational pair, also built on this).
Reach for THIS skill when the question is about the generic machinery itself —
reading it, changing it, or explaining a symptom that traces back to it.

## The two sides of the monad

- **`CPureSpec`/`CHeapSpec`** — the CONCRETE side: plain, deterministic Coq
  computation, no symbolic terms.
- **`SPureSpec`/`SHeapSpec`** — the SYMBOLIC side: world-indexed
  (`⊢ ... : World -> Type`), what every case study's symbolic executor runs on.

Both sides expose the SAME named combinators (choice, pattern-matching, assume/
assert). Every symbolic combinator has a matching `refine_<name>` lemma in
`theories/Refinement/Monads.v` proving it agrees with its concrete counterpart.

## Choice combinators (`theories/Symbolic/Monads.v`)

- `demonic_finite F := demonic_list (finite.enum F)` (~line 431) —
  **unconditionally enumerates every value of the finite type `F`**, with no
  check of whether the real answer is already known/decidable. Universal
  ("demonic") choice: used wherever the executor must consider every
  possibility (e.g. picking a pattern-match case).
- `angelic_finite`/`angelic_list` — same shape, EXISTENTIAL ("angelic") choice:
  used where the executor gets to pick (e.g. CFGVer's exit-vs-continue choice
  in `sexec_cfg_addr`).
- `demonic_pattern_match'`/`demonic_pattern_match` (~line 574-618) — the
  pattern-match dispatcher: `demonic_finite (PatternCase pat)` picks a case,
  THEN `assume_formula` records — but does not check up front — that the
  reconstructed value equals the real scrutinee. This is what `if`/`match` on
  ANY type desugars through (`stm_if` is sugar over a boolean
  `stm_pattern_match`).
- `angelic_pattern_match'`/`angelic_pattern_match` — same shape, angelic choice
  + `assert_formula` (the proof-*obligation*-generating counterpart, used on
  the concrete/refinement side).

**Nothing here calls `peval`/`term_get_val` on the scrutinee before choosing.**
Even when the scrutinee is already a concrete `term_val`, `demonic_finite`
builds a case for every possibility; `assume_formula` only records which one
is "real" as a fact for LATER (`solve_vc`-time) simplification — it does not
stop the dead cases from being constructed as terms in the first place.

## Generic statement executor (`theories/MicroSail/SymbolicExecutor.v`)

`sexec (inline_fuel : nat) : Exec` (~line 609) is the top-level `Fixpoint`
every case study calls to symbolically execute a `Stm`. Its dispatch
(~line 426-490) is a plain match over statement constructors — `stm_val`,
`stm_let`, `stm_call`, `stm_pattern_match` (→ `demonic_pattern_match`, above),
`stm_seq`, `stm_read_register`, etc.

## Refinement lemmas (`theories/Refinement/Monads.v`)

Every combinator above has a `refine_<name>` lemma (e.g.
`refine_demonic_pattern_match'`, ~line 574-595) proving
`ℛ⟦R...⟧ (CPureSpec.<name>) (SPureSpec.<name>)` — the symbolic combinator
agrees with its concrete counterpart under the `ℛ⟦⟧` logical relation.
Proofs are Iris-based (`iIntros`/`iApply (refine_bind ...)`/`rsolve`
patterns). This is the layer that has to keep working if you touch a core
combinator: changing `demonic_pattern_match'`, for instance, means
re-proving `refine_demonic_pattern_match'`, not just editing the function —
and since every case study goes through these same combinators, "no
regression" realistically means recompiling more than just one case study.

## Where the CFGVer loop blowup lives

A concrete, worked trace of why "unconditional forking" matters in practice:
CFGVer's `sexec_cfg_addr` (`case_study/RiscvPmp/CFGVer/Verifier.v`) revisits
the SAME `BNE` instruction once per loop iteration; each visit goes through
`demonic_pattern_match` above, and since neither it nor `demonic_finite`
prunes based on the (already concrete) loop counter, every iteration doubles
the term the executor builds — confirmed empirically (~2–2.5× per +1 trip
count) and traced to exactly this mechanism. Full write-up: **cfgver-executor**'s
"Backward-branch loops" section. If you're chasing a similar slow or
exponential symbolic-execution proof in a DIFFERENT case study (not CFGVer),
the same root cause almost certainly applies — it's a property of these
shared combinators, not anything CFGVer-specific.

## The fix (not yet attempted)

The principled fix is a decidability/`peval` short-circuit inside
`demonic_finite`/`demonic_pattern_match'` (and the angelic equivalents)
BEFORE constructing a branch — skip enumerating a case when the scrutinee
already decides the answer. Not a quick patch: any change here needs the
matching `refine_*` lemma re-proved (a new case, not just a new function
body), and needs testing broader than one case study. Tracked in `TODO.md`'s
`GHASH::key_schedule` section; not attempted as of 2026-07-19.
