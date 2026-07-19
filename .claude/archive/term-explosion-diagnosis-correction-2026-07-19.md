# Term-explosion diagnosis correction — 2026-07-19

Removed/superseded content, archived verbatim per the CLAUDE.md hygiene rule.
The fork-blowup diagnosis below was DISPROVED by the probe chain recorded in
memory note project-key-schedule-loop-scaling (real cause: secret-register
term duplication, no sharing in the symbolic register store).

## From .claude/TODO.md (lines 300-363 at removal time)

  **Now confirmed WHY the concrete-trip-count pattern can't just be scaled up
  instead (2026-07-19):** tried bumping the `key_schedule_loop2` (N=2) spike
  to N=64 via `gen_contract_rel`, unchanged otherwise. `vm_compute` alone
  (before `solve_vc`) didn't finish in 590s; a timing probe (trip counts
  1..8, `vm_compute` only) showed a clean ~2–2.5× blowup per +1 trip
  (4→5→6→7 trips: 25.5s→52.2s→112.4s→285.5s) — genuine O(2^trip-count), and
  an isolating probe ruled out the memory-table size (`gen_mem_pre_rel`) as a
  factor (an 8-entry table with only a 2-trip loop was just as fast as the
  N=2 baseline). Root cause is in Katamaran's CORE generic executor, not
  CFGVer: `BNE`'s `if`-semantics desugars to `demonic_pattern_match`
  (`theories/Symbolic/Monads.v`), whose fallback calls `demonic_finite F :=
  demonic_list (finite.enum F)` — this unconditionally enumerates every
  pattern case with no `peval`/decidability short-circuit on the scrutinee,
  and since `sexec_cfg_addr` continues the full remaining fuel budget from
  BOTH forks independently, every branch the loop revisits doubles the term.
  Full trace: **`cfgver-executor`** skill's "Backward-branch loops" section;
  session detail in memory `project-key-schedule-loop-scaling`. This means
  the *symbolic iteration count* redesign above isn't just a nicer API — it's
  the only way to avoid inline unrolling's exponential cost, short of a
  core-executor change to `demonic_finite`/`demonic_pattern_match` (which
  would be framework-wide, not CFGVer-local).
- **TODO: tell Dominique (Devriese) and Steven (Keuchel) about the
  `demonic_finite`/`demonic_pattern_match` exponential-blowup finding above.**
  This is a core-framework issue (`theories/Symbolic/Monads.v`), not a CFGVer
  bug: NONE of the generic forking combinators (`demonic_finite`,
  `angelic_binary`, `angelic_finite`, and anywhere else a disjunction gets
  built) check the accumulated path condition before constructing a branch —
  every fork is built blind, and pruning only happens afterward, on tactics'
  own time, once the (already exponentially large) term already exists. This
  is a well-known symbolic-execution pattern ("eager"/"on-the-fly" path
  pruning, smart constructors on the choice combinators) that's currently
  missing across the board, not just for CFGVer's loops — worth their
  attention as a possible systematic fix, since it would need re-verifying
  the refinement/soundness lemmas for whichever combinators are touched, and
  affects every case study (MinimalCaps etc.), not just RiscvPmp. A narrower,
  single-combinator version of the same idea was scoped out (next bullet) but
  NOT attempted this session — worth mentioning to them too, as a possible
  smaller first step.
- **Proposed limited/local fix (2026-07-19, write-up only — NOT attempted):**
  add a decidability fast path to `demonic_pattern_match'`
  (`theories/Symbolic/Monads.v`, ~line 574-590) specifically — that's the one
  call site that actually has the scrutinee term in scope (`demonic_finite`
  itself doesn't; it just enumerates a finite type with no notion of "which
  value is real"). Concretely: before the existing `demonic_finite
  (PatternCase pat) ;; demonic_ctx ... ;; assume_formula ...` sequence, check
  `term_get_val (peval t)` on the scrutinee `t` — the same `peval`-then-
  `term_get_val` idiom `lookup_instr`/`is_exit` already use for table
  dispatch (`Verifier.v`). If that's `Some v` (already concrete), skip the
  whole demonic-choice/assume machinery entirely and call the CONCRETE
  `pattern_match_val pat v` (`theories/Syntax/Patterns.v:251`) directly to
  get `(pc, δpc)`, then `pure (existT pc (term_val <$> δpc))` — no fork ever
  gets built in that case. Falls back to today's fully general behavior when
  `t` isn't concrete (nothing changes for genuinely symbolic conditions).
  **Why this turned out not to be a quick patch, on inspection:**
  `demonic_pattern_match'` already has a refinement/soundness lemma
  (`refine_demonic_pattern_match'`, `theories/Refinement/Monads.v:574-595`)
  tying it to `CPureSpec.demonic_pattern_match` (the concrete-side semantics)
  via Iris `ℛ⟦⟧`. Adding a new code path means that lemma needs a new case
  *proved*, not just the function edited — and since this is the SAME
  generic combinator every case study's `stm_pattern_match` goes through
  (not just RiscvPmp/CFGVer — MinimalCaps too), a real "no regression" check
  means recompiling more than just CFGVer. Scoped out but deliberately not
  attempted this session; left for a dedicated pass, either by us or by
  Dominique/Steven directly given it's their combinator.

## From .claude/skills/cfgver-executor/SKILL.md (description excerpt)

  (how the VC is built and called). ALSO use when vm_compute on a backward-branch
  loop example genuinely never terminates (not just slow — no residual ever appears
  to even inspect) after its trip count was raised, especially if a SMALLER trip count
  on the same loop shape compiled fine — a known exponential (O(2^trip-count)) blowup
  from the core executor's demonic_finite/demonic_pattern_match unconditionally forking
  on every branch, not a fuel/timeout/spec-size problem to tune around. Contrast: a

## From .claude/skills/cfgver-executor/SKILL.md (lines 64-111)

## Backward-branch loops: exponential blowup, not a fuel/spec-tuning problem

A concrete-pinned-trip-count loop (`countdown`, `countdown_mem`,
`key_schedule_loop2`) does **not** scale past a small trip count by just raising
`fuel`/timeout — confirmed (2026-07-19) by trying to bump `key_schedule_loop2`
(N=2) to N=64: `vm_compute` alone (before `solve_vc` even runs) didn't finish in
590s. A finer timing probe (trip counts 1..8, `vm_compute` only, `Abort` before
`solve_vc`) showed a clean ~2–2.5× blowup per +1 trip (4→5→6→7 trips:
25.5s→52.2s→112.4s→285.5s — doubling, not polynomial), and a follow-up probe
ruled out `gen_mem_pre_rel`'s memory-precondition size as a factor (an 8-entry
table with a 2-trip loop was just as fast as the N=2 baseline; only the trip
count matters).

**Root cause is in Katamaran's CORE generic executor, not CFGVer.** A backward
branch like `BNE` has ordinary `if: taken then … else …` semantics
(`RiscvPmp/Machine.v`'s `fun_execute_BTYPE`), which desugars to
`stm_pattern_match` on a bool. The generic executor's handler for that
(`theories/MicroSail/SymbolicExecutor.v`'s `stm_pattern_match` case) calls
`demonic_pattern_match` (`theories/Symbolic/Monads.v`), whose fallback case
(`demonic_pattern_match'`) calls `demonic_finite (PatternCase pat)`, and
`demonic_finite F := demonic_list (finite.enum F)` — this **unconditionally
enumerates every pattern case** (both `true`/`false`), with no `peval`/
decidability check on the scrutinee first, even when it is already a concrete
`term_val`. The `assume_formula` that later constrains which fork is actually
consistent runs *after* the fork, so it prunes the resulting *proof
obligation*, not the *term being built*. Since `sexec_cfg_addr` continues the
full remaining fuel budget from **both** forks independently (its
`sexec_instruction i apc ;; sexec_cfg_addr n' ...` bind), every backward branch
the loop revisits doubles the term: O(2^(branch instructions within the fuel
budget)), i.e. O(2^trip-count) for a loop. For the underlying core-framework
mechanism itself (`demonic_finite`/`demonic_pattern_match`, their refinement
lemmas, why this affects any case study, not just CFGVer) see
**core-executor-internals**; for the general "my compile/proof is way slower
than expected" triage workflow that led here, see **rocq-timeout-triage**.

This is a property of the generic executor (any `if`/pattern-match on a
not-yet-reduced-but-decidable condition forks unconditionally) — `countdown`/
`countdown_mem` simply were never pushed past a tiny trip count before to
expose it. Two real (nontrivial) ways forward if a bigger concrete-trip-count
loop is ever needed: (a) teach `demonic_finite`/`demonic_pattern_match` (or a
specialized call site) to `peval` the scrutinee first and skip dead cases when
already concrete — a change to core `theories/Symbolic/Monads.v`, framework-
wide, needs real scrutiny before touching it; or (b) a genuinely different VC
shape for concrete-trip-count loops (induction/loop-invariant style, not
inline step-by-step unrolling) — the not-yet-designed *symbolic iteration
count* approach `TODO.md`'s `GHASH::key_schedule` entry already flags as open.
Session detail (the two isolating probes, exact timings): memory
`project-key-schedule-loop-scaling`.

## From .claude/skills/core-executor-internals/SKILL.md (description excerpt + lines 64-68, 91-113)

  proved with Iris). ALSO use when investigating WHY a proof involving repeated
  branches or pattern-matches is unexpectedly slow or looks exponential — these
  combinators fork unconditionally with no peval/decidability short-circuit
  before building a branch, in ANY case study, not just CFGVer (see "Where the
  CFGVer loop blowup lives" below for a concrete worked trace). NOT for CFGVer's

**Nothing here calls `peval`/`term_get_val` on the scrutinee before choosing.**
Even when the scrutinee is already a concrete `term_val`, `demonic_finite`
builds a case for every possibility; `assume_formula` only records which one
is "real" as a fact for LATER (`solve_vc`-time) simplification — it does not
stop the dead cases from being constructed as terms in the first place.

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
