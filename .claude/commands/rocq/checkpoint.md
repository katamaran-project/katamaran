---
name: checkpoint
description: Save progress with a safe commit checkpoint
user_invocable: true
---

# Rocq Checkpoint

Creates a checkpoint with per-file and project-wide build verification, axiom check, and commit.

## Usage

```
/rocq:checkpoint
/rocq:checkpoint "optional custom message"
```

## Inputs

| Arg | Required | Description |
|-----|----------|-------------|
| message | No | Custom commit message suffix |

## Actions

1. **Verify Touched Files** - For each existing added/modified `.v` file in the staged set, compile individually via `rocq_compile(source)` or `coqc`:
   ```bash
   coqc -Q . ProjectName <path/to/File.v>   # or use rocq_compile
   ```
   If any file fails, stop and report the error before proceeding.
2. **Verify Build** - Run project-wide build gate:
   ```bash
   make -f CoqMakefile   # or coq_makefile generated Makefile
   ```
3. **Check Axioms** - Verify no unwanted custom axioms:
   ```bash
   bash "$ROCQ_SCRIPTS/check_axioms.sh" .
   ```
   Or via MCP: `rocq_query("Print Assumptions theorem_name.")` for each theorem.
4. **Count Admitted** - Report current Admitted count:
   ```bash
   ${ROCQ_PYTHON_BIN:-python3} "$ROCQ_SCRIPTS/admitted_analyzer.py" . --format=summary
   ```
5. **Stage and Commit** - Stage only files touched during this session, then commit:
   ```bash
   git add <files touched during this session>
   git diff --cached --name-only   # print exact staged set
   git commit -m "checkpoint(rocq): [summary]"
   ```
   Never use `git add -A` or broad glob patterns.
6. **Report Status** - Show what was saved

## Output

```markdown
## Checkpoint Created

**Commit:** [hash] - [message]
**Touched files compiled:** N files
**Project build:** passing
**Admitted:** [N] remaining
**Axioms:** [status]

**Next steps:**
- Continue with `/rocq:prove`
- Push manually when ready: `git push`
```

## Safety

- Does NOT push to remote (manual only)
- Does NOT create PRs (manual only)
- Does NOT amend commits (each checkpoint = new commit)
- Will NOT create checkpoint if build fails

## Rollback

```bash
git reset --soft HEAD~1   # Undo last, keep staged
git reset HEAD~1          # Undo last, keep unstaged
git reset HEAD~N          # Undo last N commits
```

**Warning:** Only use reset before pushing.

## See Also

- `/rocq:prove` - Guided cycle-by-cycle proving
- `/rocq:review` - Read-only code review
- `/rocq:refactor` - Strategy-level proof simplification
