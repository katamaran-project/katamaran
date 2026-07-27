---
name: rocq-compile-oom
description: >
  A heavy Rocq/Coq compile (vm_compute-heavy VC proofs — e.g. a fuel-30+
  solve_vc in CFGVer) gets silently KILLED — `Terminated` / `Error 143`, no Coq
  error at all. This is the OUT-OF-MEMORY / orphaned-process diagnosis
  specifically (system memory/swap pressure, leftover orphaned MCP-server node
  processes — removing an MCP server from Claude Code's config does not kill
  its already-running process), not a general "my compile is slow" symptom.
  Use when a compile has actually died with no diagnostic, or once
  **rocq-timeout-triage** (the general entry point for "way slower than
  expected"/timeout symptoms) has already pointed here because the hang looks
  memory-related. Do NOT use this for a compile that is simply still in
  progress — a tool reporting "still running after Ns, moved to background" is
  normal, routine async behavior, not a failure. NOT for actual Coq compile
  errors or stale .vo/.vos artifacts (rocq-doctor), and NOT for tactic-level
  failures that DO produce a Coq error message (rocq-pitfalls). NOT for a hang
  that reproduces at the IDENTICAL position regardless of timeout (e.g. same
  last_completed sentence at 120s and 580s) once process/memory health is
  ALREADY confirmed clean — that signature points to a genuine proof-term bug,
  not resource exhaustion (in CFGVer specifically:
  gen_contract_noninterferent(_param/_rel)'s discharge-order gotcha, see
  cfgver-gen-contract). NOT for a hang that scales with a specific parameter
  you just changed (N, fuel, table size) — that's a capacity/complexity
  question, triage it via **rocq-timeout-triage** first (it may turn out to be
  the known CFGVer backward-branch-loop exponential blowup — see
  cfgver-executor/core-executor-internals — which this skill's memory checks
  won't explain or fix).
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

## Other OOM cause: a PARALLEL build (`make -jN`) on a term-heavy closure

Same `Terminated` / `Error 143` signature, but the machine has NO orphans and a
SERIAL build succeeds — it dies ONLY under `make -jN`. Cause: every `coqc`
process loading the CFGVer/µSail closure carries a large INHERENT memory floor
(~3.6 GB — the RISC-V model's transparent `fun_*`/`FunDef` terms dominate;
full breakdown in the `project-compile-cost` memory), so `-jN` demands
`N × ~3.6 GB` of baseline at once. On a 14 GiB box `make -j$(nproc)` (= -j16) is
tens of GB → the kernel OOM-kills the heaviest file mid-build (e.g. Cmovznz4,
which peaks ~5.7 GB). Classic trigger: a `git checkout`/merge bumps `.vo`
mtimes, forcing a full rebuild that had been quietly incremental — so it strikes
right after a branch switch or merge, not during normal editing.

**Tell it apart from the orphan cause:** it dies under `-jN` but a `-j1`/`-j2`
rebuild of the SAME target is clean, and `free -h` shows no pre-existing
pressure → it's parallelism, not orphans and not a code regression.

**Fix — bound `-j` by RAM, not cores.** Budget ~6 GB per job against total RAM
(`jobs = mem_gb / 6`, clamped to `[1, nproc]`); `scripts/gate.sh` computes this
and honours a `GATE_JOBS=N` override. The floor is NOT reducible: it is
transparent µSail terms that `solve_vc`'s `vm_compute` must keep reducible, and
`vos`-load == `vo`-load (so it is not opaque-proof bloat that a lighter load
could drop). Don't chase it in the model — cap parallelism instead.

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
