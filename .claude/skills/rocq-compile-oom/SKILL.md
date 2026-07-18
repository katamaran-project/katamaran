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
