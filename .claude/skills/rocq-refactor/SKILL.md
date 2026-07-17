---
name: rocq-refactor
description: >
  Runs the rocq plugin's strategy-level proof simplification: find a better proof
  approach, leverage stdlib/MathComp lemmas instead of hand-rolled ones, extract
  reusable helper lemmas. Use for "there must be a stdlib lemma for this whole
  block", "factor these three similar proofs into a helper", "this proof strategy
  feels wrong". Edits files (with approval) but never changes theorem statements,
  adds axioms, or commits. NOT for tactic-level shortening of an already-fine proof
  (rocq-golf) and NOT read-only audits (rocq-review).
---

# Wrapper: /rocq:refactor

Thin auto-trigger wrapper. The workflow lives in the rocq plugin: read and follow
`~/.claude/plugins/cache/rocq-skills/rocq/*/commands/refactor.md` (glob the
version directory).

Key facts:
- **Mutating, bounded**: edits proof bodies with user approval; theorem statements,
  axioms, and commits are off-limits by the command's own rules.
- Scoping: `File.v`, `File.v:149`, `--scope=changed`, `--dry-run` to report only.
- Complements: `rocq-golf` = tactic-level, this = strategy-level,
  `rocq-review` = read-only.
- Repo caveat: in CFGVer, refactoring shared lemmas means recompiling downstream
  (`Verifier.v` keep_vo → `Examples.v`); axiom hygiene must stay pure_decode +
  mmioenv only.
