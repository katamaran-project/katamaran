---
name: refactor
description: Leverage stdlib/MathComp, extract helpers, simplify proof strategies
user_invocable: true
---

# Rocq Refactor

Strategy-level proof simplification: find better proof approaches, leverage stdlib/MathComp, and extract reusable helpers. Complements `/rocq:golf` (tactic-level optimization) and `/rocq:review` (read-only audit).

**Mutating command:** Edits files with user approval. Does not change theorem statements, introduce axioms, or create commits.

## Usage

```
/rocq:refactor File.v                  # Refactor all proofs in file
/rocq:refactor File.v:149              # Refactor proof at line 149
/rocq:refactor --scope=changed         # Refactor files modified since last commit
/rocq:refactor --scope=changed --dry-run  # Report opportunities without editing
```

## Inputs

| Arg | Required | Description |
|-----|----------|-------------|
| target | No | File or `File.v:line` |
| --scope | No | `file` (default with target), `changed` (default without target) |
| --dry-run | No | Report only, do not edit |
| --search | No | `quick` (default) or `full` (exhaustive library search) |
| --extract-helpers | No | `on` (default) or `off` |

## Preconditions

- Target proofs must compile (no Admitted, no build errors in scope)
- Run `/rocq:prove` or `/rocq:autoprove` first if there are open Admitted

## Actions

1. **Audit** — Read target proofs, identify repeated patterns, long proofs (>30 lines), hand-rolled arguments
2. **Search** — For each opportunity, search library via MCP-first protocol. `--search=quick`: up to 2 `rocq_query` calls. `--search=full`: up to 5 queries.
3. **Plan** — Present findings with estimated impact
4. **Approval** — Ask before each batch. `--dry-run` stops here.
5. **Apply** — Edit files, verify with `rocq_compile` after each batch; revert batch on new diagnostic
6. **Verify** — Project build if multi-file. If final gate fails, revert all batches.
7. **Report** — Summarize changes applied, helpers extracted, line count delta

## Safety

- Does not change theorem/lemma statements
- Does not introduce axioms
- Does not create commits
- Asks before each batch of edits
- Reverts batch on verification failure
- Compiled proofs only (refuses files with Admitted or build errors)
- Follow Rocq 80-char line width convention

## See Also

- `/rocq:review` - Read-only quality audit
- `/rocq:golf` - Tactic-level optimization
- `/rocq:prove` - Guided theorem proving
