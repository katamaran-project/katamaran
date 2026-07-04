---
name: autoprove
description: Autonomous multi-cycle theorem proving with hard stop rules
user_invocable: true
---

# Rocq Autoprove

Autonomous multi-cycle theorem proving. Runs cycles automatically with hard stop conditions and structured summaries.

## Usage

```
/rocq:autoprove                        # Start autonomous session
/rocq:autoprove File.v                 # Focus on specific file
/rocq:autoprove --repair-only          # Fix build errors without filling Admitted
/rocq:autoprove --max-cycles=10        # Limit total cycles
```

## Inputs

| Arg | Required | Default | Description |
|-----|----------|---------|-------------|
| scope | No | all | Specific file or theorem to focus on |
| --repair-only | No | false | Fix build errors only, skip Admitted-filling |
| --planning | No | on | `on` or `off` |
| --review-source | No | internal | `internal`, `external`, `both`, or `none` (see coercion below) |
| --review-every | No | checkpoint | `N` (Admitted), `checkpoint`, or `never` |
| --checkpoint | No | true | Create checkpoint commits after each cycle |
| --deep | No | stuck | `never`, `stuck`, or `always` (`ask` coerced to `stuck`) |
| --deep-sorry-budget | No | 2 | Max Admitted per deep invocation |
| --deep-time-budget | No | 20m | Max time per deep invocation |
| --max-deep-per-cycle | No | 1 | Max deep invocations per cycle |
| --max-consecutive-deep-cycles | No | 2 | Hard cap on consecutive cycles using deep mode |
| --deep-snapshot | No | stash | V1: `stash` only |
| --deep-rollback | No | on-regression | `on-regression`, `on-no-improvement`, `always`, or `never` |
| --deep-scope | No | target | `target` or `cross-file` |
| --deep-max-files | No | 2 | Max files per deep invocation |
| --deep-max-lines | No | 200 | Max added+deleted lines per deep invocation |
| --deep-regression-gate | No | strict | `strict` or `off` |
| --batch-size | No | 2 | Admitted to attempt per cycle |
| --commit | No | auto | `auto` or `never` (`ask` coerced to `auto`) |
| --golf | No | never | `prompt`, `auto`, or `never` |
| --max-cycles | No | 20 | Hard stop: max total cycles |
| --max-total-runtime | No | 120m | Hard stop: max total runtime |
| --max-stuck-cycles | No | 3 | Hard stop: max consecutive stuck cycles |

### Review Source Coercion

Autoprove **never blocks waiting for interactive input**. If the value is `external` or `both`, autoprove coerces to `internal` at startup.

## Startup Behavior

No questionnaire. Discover state and start immediately.

1. **Discover state** (MCP-first):
   - `rocq_toc(file)` for file structure
   - `rocq_start(file, theorem)` at each Admitted to see goals
   - Up to 3 `rocq_query` search calls (~30s); record top candidates per Admitted
2. If `--planning=on` (default): run planning phase — list Admitted with candidates, set order, then start
3. If `--planning=off`: skip planning, start immediately

## Actions

Each cycle has 6 phases — see [cycle-engine.md](../skills/rocq/references/cycle-engine.md) for shared mechanics.

### Phase 2: Work (Per Admitted)

1. Open session → search → generate 2-3 candidates → test via `rocq_step_multi`
2. Tactic cascade if no candidate passed
3. Validate via `rocq_compile(source)`; run `rocq_verify` for correctness
4. Stage & commit

**Commit behavior:** Default `--commit=auto` — commits without prompting.

### Phase 6: Continue / Stop

**Autonomous loop:** Auto-runs cycles without per-cycle user prompts. Checkpoint + review + replan at each cycle boundary.

## Stop Conditions

Autoprove stops when the **first** of these is satisfied:

1. **Completion** — all Admitted in scope are filled
2. **Max stuck cycles** — `--max-stuck-cycles` consecutive stuck cycles (default: 3)
3. **Max cycles** — `--max-cycles` total cycles reached (default: 20)
4. **Max runtime** — `--max-total-runtime` elapsed (default: 120m)
5. **Manual user stop** — user interrupts

## Structured Summary on Stop

```
## Autoprove Summary

**Reason stopped:** [completion | max-stuck | max-cycles | max-runtime | user-stop]

| Metric | Value |
|--------|-------|
| Admitted before | N |
| Admitted after | M |
| Cycles run | C |
| Stuck cycles | S |
| Deep invocations | D |
| Time elapsed | T |

**Handoff recommendations:**
- [If incomplete: "Run /rocq:prove for guided work on remaining N Admitted"]
- [If stuck: "Review stuck blockers: file:line, file:line"]
- [If clean: "All Admitted filled. Run /rocq:checkpoint to save."]
```

## Deep Mode

Bounded subroutine for stubborn Admitted. Default: `stuck` (auto-escalate when stuck).

Statement changes are NOT permitted. Declaration headers are immutable (header fence). If deep concludes the statement is wrong, emit `next_action = redraft`, auto-revert any header changes, and mark stuck.

**Deep safety coercions** (validated at startup):
- `--deep-rollback=never` → coerced to `on-regression`
- `--deep-regression-gate=off` → coerced to `strict`

## Stuck Definition

An Admitted is **stuck** when: same failure 2-3x, same build error 2x, no progress 10+ min, or empty search 2x.

**When stuck:** auto-review → planner mode → revised plan → next cycle executes plan.

## Repair Mode

Compiler-guided repair is **escalation-only**. Auto-invoke only when compiler errors are the active blocker. Budgets: max 2 per error signature, max 8 total per cycle.

## Safety

Guardrailed git commands are blocked. See [cycle-engine.md](../skills/rocq/references/cycle-engine.md#safety).
- **Line width.** Follow Rocq 80-char line width convention.

## See Also

- `/rocq:autoformalize` - Autonomous end-to-end formalization
- `/rocq:prove` - Guided cycle-by-cycle proving
- `/rocq:checkpoint` - Manual save point
- `/rocq:review` - Quality check (read-only)
- `/rocq:golf` - Optimize proofs
- [Cycle Engine](../skills/rocq/references/cycle-engine.md)
