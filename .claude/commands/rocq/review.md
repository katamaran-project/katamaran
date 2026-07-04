---
name: review
description: Read-only code review of Rocq proofs
user_invocable: true
---

# Rocq Review

Read-only review of Rocq proofs for quality, style, and optimization opportunities.

**Non-destructive:** Files are restored after analysis.

## Usage

```
/rocq:review                              # Review changed files (default)
/rocq:review File.v                       # Review specific file
/rocq:review File.v --line=89             # Review single Admitted
/rocq:review --scope=project              # Review entire project (prompts)
```

## Inputs

| Arg | Required | Description |
|-----|----------|-------------|
| target | No | File or directory to review |
| --scope | No | `sorry`, `deps`, `file`, `changed`, or `project` |
| --line | No | Line number for single-Admitted scope |
| --json | No | Output structured JSON for external tools |
| --mode | No | `batch` (default) or `stuck` (triage) |

## Scope Behavior

| Scope | Description |
|-------|-------------|
| `sorry` | Single Admitted at --line |
| `deps` | Admitted + same-file helpers and directly referenced lemmas |
| `file` | All Admitted in target file |
| `changed` | Files modified since last commit (git diff) |
| `project` | Entire project (requires confirmation) |

**Defaults:**
- No args → `--scope=changed`
- Target file → `--scope=file`
- Target + `--line` → `--scope=sorry`

## Review Modes

**Batch mode (default):** Full review report with all sections.

**Stuck mode:** Top 3 blockers with actionable next steps. Lightweight: skips golf analysis.

**Stuck mode output:**
```markdown
## Stuck Review — File.v:89

**Top 3 blockers:**
1. Missing lemma about convergence → Search Reals library
2. Instance missing for Decidable → add Decidable instance
3. Proof too long (38 lines) → extract helper lemma first

**next_action:** continue
```

**next_action classification:** `continue` | `deep` | `repair` | `redraft` | `golf` | `stop`.

## Actions

1. **Build Status** - `rocq_compile` or project build
2. **Admitted Audit** - `${ROCQ_PYTHON_BIN:-python3} "$ROCQ_SCRIPTS/admitted_analyzer.py" <target> --format=json --report-only`
3. **Axiom Check** - `bash "$ROCQ_SCRIPTS/check_axioms.sh" <target> --report-only` or `rocq_query("Print Assumptions ...")`
4. **Style Review** - Check conventions (naming, structure, tactics, 80-char line width)
5. **Golfing Opportunities** - `${ROCQ_PYTHON_BIN:-python3} "$ROCQ_SCRIPTS/find_golfable.py" <target>`
6. **Complexity Metrics** - Proof sizes, longest proofs, tactic patterns

## Output

```markdown
## Rocq Review Report
**Scope:** File.v:89 (single Admitted)

### Build Status
Project compiles

### Admitted Audit (N remaining)
| File | Line | Theorem | Suggestion |
|------|------|---------|------------|

### Axiom Status
Standard axioms only

### Style Notes
- [file:line] - [suggestion]

### Golfing Opportunities
- [pattern] → [optimization]

### Recommendations
1. [action item]
```

## Post-Review Actions

After review completes, prompt:
```
## Review Complete

Would you like me to create an action plan from the review findings?
- [yes] — Enter plan mode
- [no] — End review
```

## Safety

- Read-only (does not modify files permanently)
- Does not create commits
- Does not apply fixes

## See Also

- `/rocq:prove` - Guided proving
- `/rocq:golf` - Apply golfing optimizations
