---
name: prove
description: Guided cycle-by-cycle theorem proving with explicit checkpoints
user_invocable: true
---

# Rocq Prove

Guided, cycle-by-cycle theorem proving. Asks before each cycle, supports deep escalation, and checkpoints your progress.

## Usage

```
/rocq:prove                         # Start guided session
/rocq:prove File.v                  # Focus on specific file
/rocq:prove --repair-only           # Fix build errors without filling Admitted
/rocq:prove --deep=stuck            # Enable deep escalation when stuck
```

## Inputs

| Arg | Required | Default | Description |
|-----|----------|---------|-------------|
| scope | No | all | Specific file or theorem to focus on |
| --repair-only | No | false | Fix build errors only, skip Admitted-filling |
| --planning | No | ask | `ask` (prompt at startup), `on`, or `off` |
| --review-source | No | internal | `internal`, `external`, `both`, or `none` |
| --review-every | No | checkpoint | `N` (Admitted), `checkpoint`, or `never` |
| --checkpoint | No | true | Create checkpoint commits after each cycle |
| --deep | No | never | `never`, `ask`, `stuck`, or `always` |
| --deep-sorry-budget | No | 1 | Max Admitted per deep invocation |
| --deep-time-budget | No | 10m | Max time per deep invocation |
| --max-deep-per-cycle | No | 1 | Max deep invocations per cycle |
| --deep-snapshot | No | stash | V1: `stash` only |
| --deep-rollback | No | on-regression | `on-regression`, `on-no-improvement`, `always`, or `never` |
| --deep-scope | No | target | `target` or `cross-file` |
| --deep-max-files | No | 1 | Max files per deep invocation |
| --deep-max-lines | No | 120 | Max added+deleted lines per deep invocation |
| --deep-regression-gate | No | strict | `strict` (auto-abort on regression) or `off` |
| --batch-size | No | 1 | Admitted to attempt per cycle |
| --commit | No | ask | `ask` (prompt before each commit), `auto`, or `never` |
| --golf | No | prompt | `prompt`, `auto`, or `never` |

## Startup Behavior

If key preferences are not passed via flags, ask once at startup:

**Planning preference:**
> Start with a planning phase? (Recommended for new sessions)
> 1) Yes — discover state, set scope, show plan (recommended)
> 2) No — skip planning, start immediately

**Review source:**
> How should reviews be conducted?
> 1) Internal — planner mode reviews and can apply fixes (recommended)
> 2) External — interactive handoff for advice only
> 3) Both — internal first, then external advice
> 4) None — no automatic reviews

If `--planning=off`, skip initial planning but stuck-triggered replan is still mandatory.

## Actions

Each cycle has 6 phases — see [cycle-engine.md](../skills/rocq/references/cycle-engine.md) for shared mechanics.

### Phase 1: Plan

Discover Admitted via MCP. Start proof sessions (`rocq_start`), search with `rocq_query` (up to 3 queries, ~30s), show plan and get confirmation.

### Phase 2: Work (Per Admitted)

See [admitted-filling.md](../skills/rocq/references/admitted-filling.md).

1. Open session with `rocq_start(file, theorem)` → see goals
2. Search via `rocq_query("Search ...")` → generate 2-3 candidates
3. Test via `rocq_step_multi(tactics=[...])` (up to 20 tactics)
4. Commit winning tactic via `rocq_check(body)`
5. Validate via `rocq_compile(source)` — verify full file compiles
6. Stage & commit (see below)

**Staging rule:** If `--commit=never`, skip staging and committing entirely. Otherwise, stage only the files touched by this fill (`git add <edited files>`) — never `git add -A` or broad patterns.

**Commit behavior** (unique to prove):
Show diff and ask before each commit when `--commit=ask` (default):
```
Commit this? [yes / yes-all / no / never]
```
- **yes** — commit, prompt again next time
- **yes-all** — switch to `auto` for rest of session
- **no** — unstage (`git reset HEAD <files>`), skip this commit
- **never** — unstage, skip all remaining commits for session

**Constraints:** Max 3 candidates per Admitted, ≤80 lines diff, NO statement changes, NO cross-file refactoring (fast path). Declaration headers are immutable — if deep mode suggests a header change, it must stop and recommend `/rocq:formalize`.

### Phase 3: Checkpoint

Stage only files from **accepted** fills; exclude declined fills and rolled-back deep invocations.

### Phase 4: Review

Runs at configured `--review-every` intervals.

### Phase 5: Replan

Planner mode updates the action plan based on review findings.

### Phase 6: Continue / Stop

Prompt the user after each full cycle:
```
Cycle complete. Filled N/M Admitted this cycle.
- [continue] — run next cycle
- [stop] — save progress and exit
- [adjust] — change flags for next cycle
```
Never auto-start the next cycle. Always ask.

## Deep Mode

Bounded subroutine for stubborn Admitted. Enabled via `--deep`. Default: `never`.

Modes: `never` | `ask` (prompt first) | `stuck` (auto on stuck) | `always` (auto on any failure).

Statement changes are NOT permitted. Declaration headers are immutable (header fence). If deep concludes the statement is wrong, it emits `next_action = redraft` but does not rewrite. Suggest `/rocq:formalize` for statement work. Deep allows multi-file refactoring and helper extraction within the header fence.

**Safety:** Deep creates a path-scoped pre-deep snapshot (`--deep-snapshot`), enforces scope/diff budgets, and auto-rolls back on regression.

### Header Fence

Declaration headers (everything from `Theorem`/`Definition`/`Lemma` through `Proof.`) are snapshotted at deep entry. At each checkpoint, the engine compares headers against the snapshot. Any header change triggers immediate rollback and marks the Admitted as stuck.

## Stuck Definition

An Admitted is **stuck** when: same failure 2-3x, same build error 2x, no progress 10+ min, or empty search 2x.

**When stuck:** review → fresh plan → present for approval ([yes / no / skip]). Handoff must include search queries attempted, top candidates, and `rocq_step_multi` outcomes.

## Completion

Report filled/remaining Admitted, then prompt:

```
## Session Complete

Filled: 5/8 Admitted
Commits: 7 new

Create checkpoint? (per-file + project build, axiom check, commit)
- [yes] — run /rocq:checkpoint
- [no] — keep commits as-is
```

**Golf prompt** (if `--golf=prompt` or default):
```
Run /rocq:golf on touched files?
- [yes] — golf each file
- [no] — skip golfing
```

## Repair Mode

Compiler-guided repair is **escalation-only** — not the default response to a first failure. Auto-invoke only when compiler errors are the active blocker: same blocker 2x, same build error 2x, or 3+ errors in scope. Budgets: max 2 per error signature, max 6 total per cycle.

See [cycle-engine.md](../skills/rocq/references/cycle-engine.md#repair-mode) for full policy and [compilation-errors.md](../skills/rocq/references/compilation-errors.md) for error-specific fixes.

## Safety

Guardrailed git commands are blocked. See [cycle-engine.md](../skills/rocq/references/cycle-engine.md#safety) for the full list.
- **Line width.** Follow Rocq 80-char line width convention.

## See Also

- `/rocq:draft` - Draft Rocq declaration skeletons
- `/rocq:autoformalize` - Autonomous end-to-end formalization
- `/rocq:autoprove` - Autonomous multi-cycle proving
- `/rocq:checkpoint` - Manual save point
- `/rocq:review` - Quality check (read-only)
- `/rocq:refactor` - Strategy-level proof simplification
- `/rocq:golf` - Optimize proofs
- [Cycle Engine](../skills/rocq/references/cycle-engine.md) - Shared prove/autoprove mechanics
