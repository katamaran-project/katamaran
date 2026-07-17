---
name: rocq-review
description: >
  Runs the rocq plugin's READ-ONLY proof review on Rocq/Coq files — quality, style,
  and optimization opportunities, no edits. Use when the user asks for a review,
  audit, or second opinion on proofs ("review my changes", "anything smelly in this
  file before I commit?"), or as the pre-commit look-over before a checkpoint. NOT
  when the user wants the improvements actually applied (rocq-golf / rocq-refactor)
  and NOT for reviewing non-Rocq code.
---

# Wrapper: /rocq:review

Thin auto-trigger wrapper. The workflow lives in the rocq plugin: read and follow
`~/.claude/plugins/cache/rocq-skills/rocq/*/commands/review.md` (glob the version
directory).

Key facts:
- **Non-destructive** — analysis only; any files touched during probing are
  restored afterwards.
- Default scope is files changed since the last commit; `File.v`, `--line=N`
  (single Admitted), or `--scope=project` narrow/widen it.
- Natural pairing: run this before `rocq-checkpoint`, and hand its findings to
  `rocq-golf` (tactic-level) or `rocq-refactor` (strategy-level) if the user wants
  them applied.
