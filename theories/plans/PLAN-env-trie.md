# PLAN-env-trie — sub-linear `env.lookup` for `theories/Environment.v`

**Status: GATE 0 REACHED AND FAILED-OVER, 2026-09-01. §3 (skew-binary RAL) and
Phase 3 are DROPPED; a much smaller fix replaces them. Read
`theories/diagnostics/env-lookup-cost-drivers.md` first, then §5's revised
Phase 1'. The transport risk that this plan was built around did NOT
materialise; a different assumption (§1's "the index is already a machine
`nat`") did, and it was wrong.**

**Status (original): UNSTARTED. Written 2026-09-01.**

Audience: a later session executing one phase at a time, same convention as
`case_study/RiscvPmp/CFGVer/plans/PLAN-loop-invariant.md` — each phase ends in an
explicit GATE; reach it, report, commit, stop.

---

## §0. Why, and what is NOT known

`env.lookup` (`Environment.v:154`) walks the environment one binder at a time, so
it costs O(depth). Every world extension re-substitutes the whole heap, and each
substitution pays that walk per variable occurrence. Declared-variable count is
measured **quadratic** (`diagnostics/lvar-lookup-cost-drivers.md`, held-out
+0.17%), and on 2026-09-01 the muladd probe reproduced it: per-instruction cost
went 7.7 M → 79 M → 140 M words as peak `|Σ|` went 33 → 96 → 135, tracking `|Σ|²`
to within ~20%.

**The upside of fixing it is NOT established, and the owner has accepted that.**
Two readings disagree and both are in the record:

- `lvar-lookup-cost-drivers.md` §5.4 measures pure lookup **depth** at fixed
  `|Σ|` as only **1.16–1.47×**, with ~74% of the variable cost being "breadth"
  (`env.tabulate` per mint, `ctx.fresh`'s name scan, pc re-substitution) —
  none of which a faster lookup touches. On that reading Amdahl caps this at
  ~1.3–1.5×.
- The code-level suspect for the quadratic is `sub_comp`: mapping a substitution
  over `|Σ|` entries, each doing an O(`|Σ|`) lookup. Making lookup logarithmic
  turns that into O(`|Σ| log |Σ|`) — an **exponent** change.

That candidate is **named but never isolated** in the existing diagnostics. §2's
Phase 0b resolves it for one day of work and is the cheapest thing in this plan.
Do it before funding anything else.

---

## §1. What the code actually is (verified 2026-09-01, with line refs)

- `Env : Ctx B -> Set` is a snoc-list — `nil : Env []`,
  `snoc {Γ} (E : Env Γ) {b} (db : D b) : Env (Γ ▻ b)` (`Environment.v:65`).
- `lookup` (`Environment.v:154`) recurses **structurally on the Env**, matching
  `ctx.view` at each step. It walks from the most recent end.
- ~~`ctx.In` is **already index-optimised**: a primitive-projection class
  `MkIn { in_at : nat; in_valid : nth_is Γ in_at b }` (`Context.v:195`), with a
  comment saying the naive inductive "is not very efficient". So the index is a
  machine `nat`; there is nothing to gain there.~~ **RETRACTED 2026-09-01**: the
  record is real, but a Coq `nat` is **unary Peano, not a machine word**, and
  `vm_compute` has no special representation for it. Every `<`, `-` and `/2` on
  `in_at` therefore costs O(`in_at`). This single sentence is what made §3 look
  viable; measured, the skew RAL stays LINEAR because of it
  (`diagnostics/env-lookup-cost-drivers.md` §3.3). Never requote it.
- `nth_is` (`Context.v:127`) is a `Prop`. **`in_valid` therefore cannot be
  eliminated into `Set`**, so no lookup implementation can branch on it — a
  constraint, but also a guarantee that proofs never block reduction.
- **`in_at` counts from the RIGHT (newest = 0)** and `in_succ` is
  `S (in_at bIn)` (`Context.v:205`): extending the context **renumbers every
  existing variable**. This single fact drives §3's design choice.
- Precedent for a second representation already exists in-file: `EnvRec`
  (`Environment.v:816`) with `to_env`/`of_env` (`827`/`833`). Phase 1 mirrors it.

API surface to preserve: 34 definitions and 54 lemmas in `Environment.v`.

---

## §2. Three traps, and why the obvious designs fail

**(a) Indices are not stable under extension.** A trie keyed on "position from
the left" would need every key rewritten on each `snoc`, and `snoc` fires on
every mint. Fatal. The fix is to pick a structure whose natural index is
*distance from the newest*, which is exactly `in_at`.

**(b) `snoc` is the hot operation, not just lookup.** Any structure needing
rebalancing on insert trades lookup cost for insert cost in an insert-heavy
workload. A plain balanced tree is therefore the wrong choice.

**(c) THE RISK: dependent shape changes produce transports, and `eq_rect` can
block `vm_compute`.** `Env Γ` is heterogeneous — slot *i*'s type depends on
Γ's *i*-th entry — so any structure whose shape is not literally Γ's shape must
carry equalities relating the two, and those transports sit in the middle of the
hottest reduction path in the project. **This is the assumption that kills the
plan if it is wrong, so Phase 0 tests it before anything else is built.**

Rejected outright (do not re-derive):
- **function representation** (`forall b, b ∈ Γ -> D b`) — O(1) to write, builds
  closures, reduces badly under `vm_compute`. Almost certainly worse.
- **balanced search tree** — trap (b).
- **changing `ctx.In`'s index convention** — touches every file in the project
  and buys nothing (§1: the index is already a `nat`).

---

## §3. The design: a skew-binary random-access list

Okasaki's skew-binary RAL: a list of **complete binary trees** whose sizes are
successive skew-binary digits. `cons` is **O(1)**, index is **O(log n)**.

Why this one and not a trie proper:

- Its natural index is **0 = most recently consed**, which *is* `in_at`. So
  `snoc` never rekeys anything (trap (a) dissolved), and `in_zero`/`in_succ`
  keep their current meanings.
- `cons` is O(1) with no rebalancing (trap (b) dissolved).
- The tree shapes depend only on `length Γ`, and the skew-binary carry rule
  means a `cons` either prepends a singleton or merges the two leading trees —
  a *local* shape change, which is the best possible case for trap (c).

Dependent formulation: `Tree : Ctx B -> Set` for complete trees over a context
*segment*, and `Env Γ` a list of trees whose segments concatenate to Γ. Define
the decomposition **by recursion on a skeleton computed from Γ**, so segment
boundaries are computed rather than asserted — this is what keeps transports out
of the lookup path. Whether that is achievable is precisely Phase 0's gate.

---

## §4. The cheaper alternative that Phase 0b may make unnecessary

If the quadratic really is `sub_comp`'s nested lookups, there is a **local** fix
requiring no change to `Env` at all:

> `sub_comp`/`inst_subst_env` do `|Σ|` lookups **into the same environment**.
> Convert that environment to a fast structure **once** per call — O(n) by a
> single traversal, not n lookups — then serve every lookup from it.
> O(`|Σ|²`) becomes O(`|Σ|`) + occurrences × O(log n).

Same asymptotic win, ~54 lemmas untouched, and it composes with `EnvRec`'s
existing `to_env`/`of_env` pattern. **If Phase 0b says the quadratic is in
`sub_comp`, do this and stop — Phase 3 is then not worth its risk.**

---

## §5. Phases

### Phase 0 — SPIKE — **DONE 2026-09-01. Transports PASS, design FAILS.**

Result in `theories/diagnostics/env-lookup-cost-drivers.md`; probe body
`theories/diagnostics/ZZEnvLookupProbe.v`. Three things it established:

- **No `eq_rect` survives reduction** — a lookup at depth 196/200 reduces to a
  bare constructor under both `vm_compute` and `cbv`, including the hardest
  case (transporting along `ctx.in_valid` itself). §2c's "assumption that kills
  the plan" is simply not a problem.
- **The skew RAL does not win**: linear at 1.1 words/binder instead of 23.5,
  and it *cannot* be sub-linear while `in_at` is a unary `nat` (§1, retracted).
- **`env.lookup`'s entire linear cost is `ctx.view`'s per-step allocation** —
  a fresh `MkIn` plus a `SnocView` at every step (`Context.v:131`), 23.5
  allocated words per binder walked, against **0.000** for the identical
  traversal written without `ctx.view`.

### Phase 0 (original text, superseded) — does a dependent RAL survive `vm_compute`?
Throwaway file, no framework changes, nothing in `_CoqProject`. Build a
heterogeneous skew-binary RAL over a toy `Ctx`, plus the list version, and
`vm_compute` the same lookup workload on both.

**GATE 0:** at 200 entries and ~10 000 lookups, the RAL beats the list on
`allocated_words`, and inspection shows **no `eq_rect` left in the reduced
lookup path**. If transports survive reduction, **STOP and report** — §3 is not
viable and only §4 remains.

### Phase 0b — where is the quadratic, actually? (BLOCKING, ~1 day)
Instrument `sub_comp`/`inst_subst_env` (`Symbolic/Instantiation.v:196`) to count
calls and lookups. Move `|Σ|` at fixed depth and fixed chunk count, per
`lvar-lookup-cost-drivers.md` §4–5's method.

**GATE 0b:** a statement of what fraction of the quadratic is nested lookups.
Cheap, and it decides §4-only vs. full replacement. **Also settles a live
question from 2026-09-01:** why `drop_fuel = 8` cost 4.3× on muladd — the drop's
`var_dead` scan pays the same lookup cost it is trying to reduce.

### Phase 1' — REPLACES Phases 1 and 3: rewrite `lookup` in place

Define `lookup` by simultaneous recursion on the `Env` spine and `ctx.in_at`,
transporting once at the base case along the **existing** `ctx.in_valid` proof
(`ZZEnvLookupProbe.v`'s `lookup5`/`lookupJ`, the `IDX2` arm). No new type, no
`to_fast`/`of_fast` conversion, no `EqDec B` constraint, no API change. Both
defining equations still hold **definitionally**:
`lookup (snoc E v) in_zero = v` and `lookup (snoc E v) (in_succ i) = lookup E i`.

Measured **5.9× on allocated words and 3.1× on wall clock at |Σ| = 200**. It is
a **constant factor, not an exponent change** — `sub_comp` stays O(`|Σ|²`).

Real cost of the phase: the 54 lemmas. Their *statements* are unchanged, but
proofs that `cbn` through `ctx.view` need a `lookup_snoc` rewrite lemma instead;
budget that, not the definition.

**GATE 1':** `Environment.v` builds; every existing lemma re-proved with no
statement change; whole project builds; `scripts/gate.sh` green with the same
14 axiom-clean end theorems.

### Phase 1 (original, SUPERSEDED by Phase 1') — `FastEnv` alongside `Env`
Add the structure, `to_fast`/`of_fast`, and the agreement lemma
`lookup_fast (to_fast E) i = lookup E i`. Mirrors `EnvRec`/`to_env`/`of_env`
exactly. Nothing else in the tree changes.

**GATE 1:** `Environment.v` builds; agreement lemma `Qed`; full project build
unaffected (it is additive).

### Phase 2 — measure the real probes (this is also Phase 0b)

With Phase 1' landed, the K=206 muladd probe re-measured against its baseline
**is** the L1 attribution PLAN §5's Phase 0b was asking for, and it delivers the
fix in the same build instead of throwing instrumentation away. Amdahl bound to
beat: `lvar-lookup-cost-drivers.md` §5.4 puts only **26.4%** of the variable
surcharge on L1, so the predicted end-to-end win is ~**1.28×**, and `NULL`-arm
data says the `env.tabulate` floor (L2) becomes the wall next.

### Phase 2 (original, superseded) — route the hot paths through it (the §4 fix)
`inst_subst_env`, `sub_comp`, `persist`. Convert once per call, serve many.

**GATE 2:** the muladd K=206 probe (`ZZDS206.v`, peak `|Σ|` = 135) improves on
its measured **10.55 G net**, with `allocated_words` and a re-measured baseline.
No trusted-surface change, so the merge gate must stay green with the same 14
axiom-clean end theorems.

### Phase 3 — **DROPPED 2026-09-01.** Phase 1' obtains the win with a local
rewrite, and the structure this phase would install is linear anyway (§3.3 of
the diagnostic). Original text kept below for the record only.

### Phase 3 (DROPPED) — replace `Env`'s representation
Swap the internals, keeping `nil`/`snoc`/`lookup`/`view` and all 54 lemma
*statements* identical. Client code that only constructs (~379 of the 421
`env.snoc`/`env.nil` mentions) is unaffected; only the ~19 pattern positions and
8 `dependent elimination`s need work.

**GATE 3:** whole project builds, no proof holes, 14 end theorems still
axiom-clean (`scripts/gate.sh`), and the Phase 2 measurement improves again.

### Phase 4 — docs
Update `theories/CLAUDE.md`'s `Environment.v` row and this plan's Status, in the
**same commit** as the code (repo rule: docs travel with code).

---

## §6. Files that would change

| File | Why | Size of change |
|---|---|---|
| `theories/Environment.v` | the structure itself: 34 defs + 54 lemmas | **the bulk of the work** |
| `theories/Symbolic/Instantiation.v` | `inst_subst_env` (:196) — the suspected quadratic; the §4 fix lands here | moderate, and it is Phase 2's whole scope |
| `theories/Symbolic/Worlds.v` | `Sub`/`persist`/`Persistent` (:575) | moderate |
| `theories/Context.v` | **expected UNCHANGED** — index already a `nat`; listed only to say so | none |
| `theories/CLAUDE.md` | file-map row for `Environment.v` | 1 line |

Pattern positions needing manual work in Phase 3 (~19 sites, 11 files):
`Syntax/TypeDecl.v` (4), `Symbolic/Solver.v` (3), `Syntax/Formulas.v` (3),
`Symbolic/OccursCheck.v` (2), and one each in `Base.v`, `Symbolic/Worlds.v`,
`Symbolic/GenOccursCheck.v`, `Symbolic/PartialEvaluation.v`,
`Symbolic/Propositions.v`, `Staging/BinaryExecutor/ShallowExecutorRel.v`.
Note `Symbolic/Solver.v` cannot be built by `rocq_compile_file` (see
`rocq-implementation` §1) — use `make -f Makefile.coq` there.

**Not in the trusted surface.** `Valuation` is a `Notation` for `Env`
(`Base.v:79`) and `CFGVer/Noninterference.v` never mentions `Env`, so no end
theorem's *statement* changes. The gate still governs, because proof terms do.

---

## §7. Do NOT

- **Do not start Phase 3 before GATE 0.** The transport risk (§2c) is the one
  that invalidates the whole design, and it costs a throwaway file to test.
- **Do not skip Phase 0b because the trie is more interesting.** If the win is
  1.3× (the §0 first reading), §4 gets it for a fraction of the risk.
- **Do not change `ctx.In`'s index convention.** §3 was chosen specifically so
  it does not have to.
- **Do not use wall-clock.** `allocated_words` with a re-measured imports
  baseline, one heavy `Eval` per process — see
  `rocq-timeout-triage`'s `references/allocation-probes.md`.
- **Do not judge Phase 2 on the muladd whole-function probe.** It does not
  currently complete at all; use the K=206 prefix, which does.
