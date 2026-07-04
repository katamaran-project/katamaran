---
name: autoformalize
description: Autonomous end-to-end formalization from informal sources
user_invocable: true
---

# Rocq Autoformalize

Autonomous end-to-end formalization: extracts claims from a source, drafts Rocq skeletons, and proves them — all unattended. Combines `/rocq:draft` and `/rocq:autoprove` in a single command.

## Usage

```
/rocq:autoformalize --source ./paper.pdf --claim-select=first --out=Paper.v
/rocq:autoformalize --source ./paper.pdf --claim-select=regex:"Theorem.*" --out=Paper.v --rigor=checked
/rocq:autoformalize --source ./notes.md --claim-select=named:"Main Lemma" --out=Lemma.v
```

## Inputs

| Arg | Required | Default | Description |
|-----|----------|---------|-------------|
| --source | **yes** | — | File path, URL, or PDF for claim extraction. |
| --claim-select | **yes** | — | `first` \| `named:"..."` \| `regex:"..."`. |
| --out | **yes** | — | Target file for formalized claims. |
| --rigor | no | `sketch` | `sketch` \| `checked`. |
| --draft-mode | no | `skeleton` | `skeleton` \| `attempt`. |
| --max-cycles | no | 20 | Hard stop: max total cycles per claim |
| --max-total-runtime | no | 120m | Hard stop: max total runtime |
| --max-stuck-cycles | no | 3 | Hard stop: max consecutive stuck cycles per claim |
| --deep | no | stuck | `never`, `stuck`, or `always` |
| --deep-sorry-budget | no | 2 | Max Admitted per deep invocation |
| --deep-time-budget | no | 20m | Max time per deep invocation |
| --commit | no | auto | `auto` \| `never` |

## Actions

1. Extract claim queue from `--source` (filtered by `--claim-select`) at startup
2. For each claim: draft skeleton → run inner 6-phase prove cycle → on stuck, consult review router
3. On `next_action=redraft`: re-draft; commit if allowed
4. Advance to next claim when Admitted-free or stop rule fires

## Stop Conditions

1. **Queue empty** — all claims attempted
2. **Max stuck cycles** — consecutive stuck cycles on current claim
3. **Max cycles** — total cycles reached on current claim
4. **Max runtime** — elapsed time
5. **Manual user stop**

## Structured Summary on Stop

```
## Autoformalize Summary

**Reason stopped:** [queue-empty | max-stuck | max-cycles | max-runtime | user-stop]

| Metric | Value |
|--------|-------|
| Claims attempted | N/M |
| Admitted after | S |
| Cycles run | C |
| Time elapsed | T |

**Handoff recommendations:**
- [If incomplete: "Run /rocq:formalize for guided work on remaining claims"]
- [If stuck: "Review stuck blockers: file:line, file:line"]
- [If clean: "All Admitted filled. Run /rocq:checkpoint to save."]
```

## Safety

- **Autonomous operation.** Never blocks waiting for interactive input.
- **Header fence.** Proof engines never modify declaration headers.
- **All `guardrails.sh` rules apply.**
- **Line width.** Follow Rocq 80-char line width convention.

## See Also

- `/rocq:draft` — Skeleton-only drafting
- `/rocq:formalize` — Interactive synthesis
- `/rocq:autoprove` — Autonomous proving (no drafting)
- [Cycle Engine](../skills/rocq/references/cycle-engine.md)
