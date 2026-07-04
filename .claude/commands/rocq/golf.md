---
name: golf
description: Improve Rocq proofs for directness, clarity, performance, and brevity
user_invocable: true
---

# Rocq Golf

Improve Rocq proofs that already compile. Score candidates by: correctness → directness → clarity/inference burden → performance/determinism → length.

**Prerequisite:** Code must compile. Verify via `rocq_compile` or `coqc` first.

## Usage

```
/rocq:golf                     # Golf entire project
/rocq:golf File.v              # Golf specific file
/rocq:golf File.v:42           # Golf proof at specific line
/rocq:golf --dry-run           # Show opportunities without applying
/rocq:golf --search=full       # Include lemma replacement pass
```

## Inputs

| Arg | Required | Description |
|-----|----------|-------------|
| target | No | File or file:line to golf |
| --dry-run | No | Preview only, no changes |
| --search | No | `off`, `quick` (default), or `full` — MCP lemma replacement pass |
| --max-delegates | No | `2` — max concurrent golfer subagents |

## Actions

1. **Verify Build** - Ensure code compiles before optimizing
2. **Find Patterns** - Detect golfable patterns (directness → structural → conditional):
   ```bash
   ${ROCQ_PYTHON_BIN:-python3} "$ROCQ_SCRIPTS/find_golfable.py" [file]
   ```
3. **Tactic Collapse Pass** — For tactic chains, construct collapsed alternatives → test via `rocq_step_multi` + `rocq_compile` check
4. **Lemma Replacement** (if `--search=quick` or `full`):
   - Search via `rocq_query("Search ...")` → test with `rocq_step_multi`
   - Accept best passing replacement by scoring order
5. **Apply** - Make changes with `rocq_compile` verification after each; revert on failure
6. **Report** - Show savings and saturation status

## Golfing Patterns

### Instant Wins (Always Apply)

| Before | After | Notes |
|--------|-------|-------|
| `intros. reflexivity.` | `reflexivity.` | When no intros needed |
| `apply H. exact H'.` | `exact (H H').` | Merge apply+exact |
| `split. exact H1. exact H2.` | `exact (conj H1 H2).` | |
| `simpl. trivial.` | `trivial.` | When trivial subsumes |

### Safe with Verification

| Pattern | Condition |
|---------|-----------|
| Inline `assert` | Used once, simple term |
| Merge sequential rewrites | `rewrite H1. rewrite H2.` → `rewrite H1, H2.` |
| Replace `destruct` chain | With `decide` or `auto` when applicable |

### Skip (False Positive Risk)

- Complex `assert` blocks used multiple times
- Named hypotheses referenced in error messages
- Tactics that change proof term opacity (`Qed` vs `Defined`)

### Golfing Policy

**Scoring order:** directness → inference burden → performance → length. Length is a tiebreaker among acceptable proofs.

**Tactic complexity ladder:** `reflexivity`/`exact` < `apply`/`rewrite` < `simpl`/`auto` < `eauto`/`intuition` < broad `lia`/`omega`/`ring`/`decide`.

**Hard reject if:** moves UP the complexity ladder for only a 1-line win, removes meaningful names, changes `Qed` to `Defined` or vice versa.

## Output

```markdown
## Golf Results

**Meaningful simplifications:** 3 (directness improvements)
**Performance cleanups:** 1
**Syntax cleanups:** 1
**Skipped:** 2 (safety / marginal)
**Build status:** passing
**Total savings:** 8 lines (~12%)

Optional next step: run `/rocq:checkpoint` to save progress.
```

## Saturation

Stop when success rate < 20% or last 3 attempts failed.

## Safety

- Requires passing build to start
- Reverts immediately on build failure
- Does not create commits (use `/rocq:checkpoint`)
- Follow Rocq 80-char line width convention

## See Also

- `/rocq:review` - See opportunities (read-only)
- `/rocq:refactor` - Strategy-level simplification
- `/rocq:checkpoint` - Save after golfing
- [proof-golfing.md](../skills/rocq/references/proof-golfing.md)
