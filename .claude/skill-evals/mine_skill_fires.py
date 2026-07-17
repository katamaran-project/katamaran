#!/usr/bin/env python3
"""List (user message -> skill fired) pairs from Claude Code session transcripts.

Purpose: post-hoc review of skill auto-invocation. Skim the output for
over-triggers (a skill fired on a query it shouldn't own) and feed any misfire
into .claude/skill-evals/cfgver-routing/eval_set.json as a new query with the
correct expected winner, then re-run the Haiku-judge matrix.

Silent NON-fires (a skill that should have fired but didn't) are invisible to
this script — those still need a human noticing in the moment.

Token cost: the script makes NO API calls — mining is free. The only token
cost is its OUTPUT entering a Claude context when Claude runs it, so before
printing it shows an order-of-magnitude output-token estimate and asks for
confirmation (pass --yes to skip, e.g. when run non-interactively).

Usage:
  python3 mine_skill_fires.py            # sessions touched in the last 7 days
  python3 mine_skill_fires.py --days 30
  python3 mine_skill_fires.py --all
  python3 mine_skill_fires.py --session <path/to/session.jsonl>
  python3 mine_skill_fires.py --skill cfgver-rsolve   # filter by skill name
  python3 mine_skill_fires.py --yes      # skip the confirmation prompt
"""

import argparse
import json
import sys
import time
from pathlib import Path

BUILTIN_COMMANDS = {
    "model", "compact", "clear", "exit", "quit", "help", "login", "logout",
    "resume", "status", "cost", "context", "init", "memory", "hooks", "mcp",
    "agents", "ide", "config", "permissions", "export", "bug", "todos",
    "release-notes", "add-dir", "bashes", "statusline", "terminal-setup",
    "upgrade", "usage", "install-github-app", "privacy-settings",
    "output-style", "vim", "fast", "rewind", "workflows", "doctor", "plugin",
    "loop", "remember", "review",
}

NOISE_PREFIXES = (
    "<local-command",
    "[SYSTEM NOTIFICATION",
    "<task-notification",
    "<system-reminder",
    "Caveat: The messages below",
)


def transcript_dir() -> Path:
    """Claude Code encodes the project cwd into the transcript dir name."""
    enc = str(Path.cwd().resolve()).replace("/", "-")
    d = Path.home() / ".claude" / "projects" / enc
    if not d.is_dir():
        sys.exit(f"transcript dir not found: {d} (run from the project root)")
    return d


def text_of(content) -> str:
    """Flatten a user message's content to its typed text, dropping tool results."""
    if isinstance(content, str):
        return content
    parts = []
    for b in content if isinstance(content, list) else []:
        if isinstance(b, dict) and b.get("type") == "text":
            parts.append(b.get("text", ""))
    return "\n".join(parts)


def is_noise(text: str) -> bool:
    t = text.lstrip()
    return not t or any(t.startswith(p) for p in NOISE_PREFIXES)


def clip(s: str, n: int) -> str:
    s = " ".join(s.split())
    return s if len(s) <= n else s[: n - 1] + "…"


def mine_file(path: Path, skill_filter: str | None):
    last_user = ""
    records = []
    with open(path, encoding="utf-8") as f:
        for line in f:
            try:
                e = json.loads(line)
            except json.JSONDecodeError:
                continue
            if e.get("isSidechain"):
                continue  # subagent transcripts have their own trigger context
            msg = e.get("message") or {}
            if e.get("type") == "user":
                # user-typed /command invocations are worth listing too
                raw = msg.get("content")
                raw_s = raw if isinstance(raw, str) else ""
                if "<command-name>" in raw_s:
                    cmd = raw_s.split("<command-name>")[1].split("</command-name>")[0]
                    cmd = cmd.strip().lstrip("/")
                    if cmd not in BUILTIN_COMMANDS and \
                            (not skill_filter or skill_filter in cmd):
                        records.append((e.get("timestamp", ""), "user-invoked",
                                        cmd, "", last_user))
                    continue
                t = text_of(raw)
                if not is_noise(t):
                    last_user = t
            elif e.get("type") == "assistant":
                for b in msg.get("content") or []:
                    if isinstance(b, dict) and b.get("type") == "tool_use" \
                            and b.get("name") == "Skill":
                        skill = (b.get("input") or {}).get("skill", "?")
                        if skill_filter and skill_filter not in skill:
                            continue
                        args = (b.get("input") or {}).get("args", "") or ""
                        records.append((e.get("timestamp", ""), "model-invoked",
                                        skill, args, last_user))
    return records


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--days", type=float, default=7)
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--session", type=Path)
    ap.add_argument("--skill", help="substring filter on the skill name")
    ap.add_argument("--yes", action="store_true",
                    help="print without the confirmation prompt")
    a = ap.parse_args()

    files = [a.session] if a.session else sorted(
        transcript_dir().glob("*.jsonl"), key=lambda p: p.stat().st_mtime)
    if not a.all and not a.session:
        cutoff = time.time() - a.days * 86400
        files = [p for p in files if p.stat().st_mtime >= cutoff]

    # continued sessions copy history into the new file, and API retries
    # duplicate turns — dedupe globally on (minute, skill, user snippet)
    seen, all_recs = set(), []
    for p in files:
        for ts, how, skill, args, user in mine_file(p, a.skill):
            key = (ts[:16], skill, clip(user, 80))
            if key not in seen:
                seen.add(key)
                all_recs.append((ts, how, skill, args, user))
    all_recs.sort()
    lines = []
    for ts, how, skill, args, user in all_recs:
        lines.append(f"[{ts[:16]}] {skill}  ({how})")
        if user:
            lines.append(f"    user: {clip(user, 220)}")
        if args:
            lines.append(f"    args: {clip(args, 120)}")
    output = "\n".join(lines)
    total = len(all_recs)

    # pre-flight: the script itself costs 0 API tokens; the output costs
    # roughly chars/4 input tokens if it lands in a Claude context
    scanned_mb = sum(p.stat().st_size for p in files) / 1e6
    est = max(1, len(output) // 4)
    mag = f"~{est}" if est < 1000 else f"~{round(est / 1000)}k"
    print(f"[mine_skill_fires] scanned {len(files)} session file(s) "
          f"({scanned_mb:.0f} MB, free — no API calls); {total} invocation(s) "
          f"found; printing them ≈ {mag} tokens if read by Claude.",
          file=sys.stderr)
    if not a.yes:
        if sys.stdin.isatty():
            if input("Print? [y/N] ").strip().lower() not in ("y", "yes"):
                sys.exit("aborted — nothing printed.")
        else:
            sys.exit("non-interactive run: pass --yes to print the results.")
    print(output)
    if total == 0:
        print("(model-invoked Skill calls only appear in sessions run with a "
              "harness that routes skills through the Skill tool)", file=sys.stderr)


if __name__ == "__main__":
    main()
