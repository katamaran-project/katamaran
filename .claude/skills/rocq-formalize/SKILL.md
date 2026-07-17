---
name: rocq-formalize
description: >
  Runs the rocq plugin's interactive formalization: turn an INFORMAL mathematical
  claim (English statement, paper, PDF) into Rocq definitions/theorem skeletons and
  prove them with guided cycles. Use when the user pastes an informal theorem or
  points at a paper — "formalize this claim", "turn Theorem 3.2 of this paper into
  Rocq". NOT for verifying RISC-V programs in the CFGVer case study (that's
  cfgver-new-example) and NOT for the fully-autonomous variant (/rocq:autoformalize
  — only on explicit user request; it is an unbounded token-burning loop).
---

# Wrapper: /rocq:formalize

Thin auto-trigger wrapper. The workflow lives in the rocq plugin: read and follow
`~/.claude/plugins/cache/rocq-skills/rocq/*/commands/formalize.md` (glob the
version directory). For skeletons-only (no proving), the lighter
`commands/draft.md` variant exists — offer it when the user only wants statements.

Key facts:
- Human-in-the-loop: drafts skeletons, then guided prove cycles with explicit
  checkpoints; `--rigor=checked|sketch|axiomatic`; `--source ./paper.pdf`.
- Custom axioms require explicit user approval (plugin rule; also this project's
  rule — axiom-clean matters here).
- Do NOT silently escalate to `/rocq:autoformalize` or `/rocq:autoprove`; those
  run unattended multi-cycle loops and need an explicit user go-ahead with a scope
  bound.
