---
name: rocq-golf
description: >
  Runs the rocq plugin's proof-golfing workflow on Rocq/Coq proofs that ALREADY
  compile. Use when the user wants a proof shortened, cleaned up, or made more
  direct — "golf this down", "this proof is 40 lines of spaghetti", "simplify this
  Qed" — or right after a large proof lands green and tightening it is the natural
  next step. NOT for proofs that don't compile yet (repair first) and NOT for
  strategy-level restructuring (that's rocq-refactor).
---

# Wrapper: /rocq:golf

This is a thin auto-trigger wrapper. The actual workflow lives in the rocq plugin:
read and follow `~/.claude/plugins/cache/rocq-skills/rocq/*/commands/golf.md`
(glob the version directory — don't hardcode `0.1.0`).

Key facts before you start:
- **Prerequisite: the code must compile.** Verify with `rocq_compile_file` first.
- Scoping: whole project / one file / one proof at a line (`File.v:42`);
  `--dry-run` reports opportunities without editing; `--search=full` adds a
  lemma-replacement pass.
- Scoring order: correctness → directness → clarity/inference burden →
  performance/determinism → length.
- In this repo, prefer golfing via `rocq_compile_file` iteration; pet OOMs on the
  full `Examples.v` (see CLAUDE.md).
