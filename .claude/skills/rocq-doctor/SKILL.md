---
name: rocq-doctor
description: >
  Runs the rocq plugin's diagnostics: environment checks, stale-artifact cleanup,
  plugin health. Use when the Rocq TOOLING (not a proof) misbehaves — stale .vo/.vos
  files causing phantom errors, "compiled fine yesterday, broken today" with no code
  change, rocq-mcp acting strangely, opam/coqc version confusion, or the user asks
  to clean the build tree. NOT for errors inside a proof body (those are proof
  bugs, not environment bugs).
---

# Wrapper: /rocq:doctor

Thin auto-trigger wrapper. The workflow lives in the rocq plugin: read and follow
`~/.claude/plugins/cache/rocq-skills/rocq/*/commands/doctor.md` (glob the version
directory).

Key facts:
- Modes: full diagnostic (default), `env` (environment only), `cleanup` (show
  stale files; add `--apply` to actually remove them — ask before `--apply`).
- Typical trigger in this repo: `Cannot find a physical path bound to
  …CFGVer.Verifier`-style errors that persist after a `keep_vo` compile — often a
  stale-artifact problem doctor's cleanup finds.
