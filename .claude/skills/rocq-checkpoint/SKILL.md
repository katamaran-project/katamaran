---
name: rocq-checkpoint
description: >
  Runs the rocq plugin's checkpoint: verify the build (per-file + project), check
  axiom hygiene, then git-commit the progress. Use at natural milestones — a lemma
  or example just went green end-to-end, a work session is wrapping up, or the user
  says "save this", "checkpoint", "let's lock this in". Committing without being
  asked is allowed in this project (nothing riskier than a commit). NOT when the
  build is red (fix first) and NOT for pushing or history rewriting — commits only.
---

# Wrapper: /rocq:checkpoint

Thin auto-trigger wrapper. The workflow lives in the rocq plugin: read and follow
`~/.claude/plugins/cache/rocq-skills/rocq/*/commands/checkpoint.md` (glob the
version directory).

Project-specific overrides (these WIN over the plugin's defaults):
- Commit message: `WIP (LLM):` prefix, trailer
  `Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>` (or the actual model).
- Axiom check standard here: `Print Assumptions` on the end-to-end lemmas must
  show only `pure_decode` and `mmioenv`.
- Branch: work happens on `KatamaranRel`; never commit to `main`.
- Leave the user's untracked personal files out of the commit
  (`REFACTORING_NOTES.md`, `case_study/RiscvPmp/CFGVer/Remarks6juli2026`).
- Full-project verification is expensive here (the example VCs vm_compute);
  per-file verification of the files actually touched is the sensible default.
