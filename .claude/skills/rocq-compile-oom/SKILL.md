---
name: rocq-compile-oom
description: >
  A heavy Rocq/Coq compile (vm_compute-heavy VC proofs — e.g. a fuel-30+
  solve_vc in CFGVer) gets silently KILLED (`Terminated` / `Error 143`, no Coq
  error at all) or hangs well past how long it normally takes, with nothing in
  the output to explain why. Use ONLY once a compile has actually died
  unexplained or is confirmed stuck far longer than its own history — before
  concluding it's a real proof or code regression, check system memory/swap
  pressure and leftover orphaned MCP-server node processes (removing an MCP
  server from Claude Code's config does not kill its already-running
  process). Do NOT use this for a compile that is simply still in progress —
  a tool reporting "still running after Ns, moved to background" is normal,
  routine async behavior, not a failure, and is not this skill's concern
  unless/until it comes back dead or the user reports it's been stuck far
  longer than expected. NOT for actual Coq compile errors or stale .vo/.vos
  artifacts (rocq-doctor), and NOT for tactic-level failures that DO produce a
  Coq error message (rocq-pitfalls).
---

# Rocq compile OOM / silent-kill diagnosis

**Symptom:** a heavy `coqc`/`vm_compute` compile (large `solve_vc` calls, deep
`vm_compute` normalization, anything with a big fuel parameter) gets killed
partway through — `Terminated` / `Error 143` (SIGTERM) — with ZERO Coq-level
diagnostic: no error position, no failing tactic, nothing. Or it just hangs
past any timeout. This is easy to misread as a real regression in whatever
code you just touched, especially when the file itself has no diff and
compiled clean minutes earlier.

**Root cause to check FIRST, before touching the proof:** the machine is
memory-starved, most often because an MCP server was removed from Claude
Code's config but its already-running process was never killed. Removing an
MCP entry only stops NEW sessions from spawning it — it does not touch
instances already running from before the removal. These orphans can linger
for days; each one is modest alone, but dozens of them add up to gigabytes of
RSS and swap.

## Diagnose

```bash
free -h                                     # swap usage near the ceiling? that's the lead
ps -eo pid,ppid,rss,etime,cmd | grep <mcp-server-name-or-node>
```

A process is a safe-to-kill orphan if its `ppid` is `systemd --user`'s pid —
i.e. no live `claude`/`claude --resume` session is its parent anymore. Get
that pid with `ps -p $(pgrep -u "$USER" -x systemd) -o pid,cmd` (or just
`pgrep -f 'systemd --user'`). Processes whose `ppid` IS a live claude session
are still in use by that session — leave those alone.

## Fix

```bash
kill $(ps -eo pid,ppid,cmd | grep '<name>' | grep -v grep | awk -v p=<systemd-user-pid> '$2==p {print $1}')
```

Re-check `free -h` — swap should drop substantially. Retry the compile with no
other changes; if it now succeeds, the original failure was pure memory
pressure, not a code regression.

For the specific incident this generalizes (`token-optimizer-mcp`,
2026-07-17/18), see the `reference-removed-config` memory note.

## Hang that reproduces IDENTICALLY regardless of timeout: probably NOT this skill

If a compile hangs at the exact same spot whether given 120s or 580s — check
`rocq_compile_file(..., timing=True)`'s `last_completed` field across two
attempts at different timeouts — that is genuine non-termination, not "needs
more patience." Check process health first (as above) to rule out contention,
but if memory/CPU come back clean AND the hang reproduces bit-for-bit, look for
a real bug in the PROOF TERM itself before assuming environment/OOM.

Concrete instance (CFGVer, 2026-07-18): `eapply gen_contract_noninterferent_param`
followed by its side-premise bullets in natural order (instead of discharging
the LAST premise — `valid_contract` — first) produced a `Qed` that hung
indefinitely with the project's full Iris/Equations import set in scope, but
failed FAST and cleanly (a normal "no subterm found" error) without those
imports — the transitively-imported SSReflect `rewrite`'s more powerful/
backtracking matching engine apparently gets stuck exactly where plain Coq's
`rewrite` fails fast on the same malformed proof term. See
**cfgver-gen-contract**'s "discharge `valid_contract` FIRST" section for the
actual fix — this diagnostic dead-end is exactly why that section exists.

## Isolating a suspected hang: minimal standalone scratch file

To tell apart "this lemma is broken" from "something about the whole file's
accumulated state", write a throwaway `.v` file INSIDE the repo (not `/tmp` —
`Require` needs `_CoqProject`/`_RocqProject` resolution), with only the
`Require`s the ONE suspect lemma needs, and that lemma copy-pasted in. Batch-
`coqc` it in isolation:
- Hangs the same way standalone → the lemma + import combination is the bug,
  independent of everything else in the original file.
- Fails fast (even with a different, "wrong" error) → rules out a genuine
  infinite loop entirely; go looking elsewhere.

Narrow further by replacing the tail of the proof with `Show. Admitted.` right
before the suspect tactic — `Show.`'s printed goal (captured in the compile's
`output` on success, since `Admitted.` lets the file "compile") tells you
exactly what's left unproved, without needing a slow interactive `pet` session.
Prefer batch `rocq_compile_file` + `Show.`/`Admitted.` cycles over interactive
`rocq_start`/`rocq_check` for iterating on a heavy file — `pet`'s full IDE-style
elaboration is often far slower to even LOAD such a file than a batch `coqc`
run is to fully check it. Delete the scratch file once done; it is not meant to
be committed.
