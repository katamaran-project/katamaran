#!/usr/bin/env bash
# Test harness for .claude/hooks/git-workflow-guard.sh mechanism 1 (main deny).
# Lives in a file, NOT in a Bash tool command string, because the harness text
# itself contains command-word-position git pushes that the guard rightly denies.
cd /home/emiel/Documents/katamaran || exit 1
H=.claude/hooks/git-workflow-guard.sh
export CLAUDE_GIT_GUARD_OFF=1   # isolate mechanism 1 from the skill nag
SEP='&''&'                      # assembled, so this file has no literal `&& git`
pass=0; fail=0

t () { # $1 expect DENY|ALLOW, $2 command, $3 optional cwd
  local wd="${3:-/home/emiel/Documents/katamaran}"
  local json out got r
  json=$(jq -n --arg c "$2" '{tool_input:{command:$c},session_id:"t"}')
  out=$(cd "$wd" && printf '%s' "$json" | bash /home/emiel/Documents/katamaran/$H 2>/dev/null)
  if printf '%s' "$out" | grep -q '"deny"'; then got=DENY; else got=ALLOW; fi
  if [ "$got" = "$1" ]; then r="ok  "; pass=$((pass+1)); else r="FAIL"; fail=$((fail+1)); fi
  printf '%s %-6s %s\n' "$r" "$got" "$2"
}

echo "=== must DENY (HEAD = issue/dropk-framework) ==="
t DENY  "git push origin main"
t DENY  "git push -u origin main"
t DENY  "git push origin HEAD:main"
t DENY  "git push origin +main"
t DENY  "git push --all origin"
t DENY  "git push --mirror origin"
t DENY  "git push origin --delete main"
t DENY  "git push origin refs/heads/main"
t DENY  "cd /tmp $SEP git push origin main"

echo "=== must ALLOW ==="
t ALLOW "git push -u origin issue/dropk-framework"
t ALLOW "git push origin domain/thing"
t ALLOW "git push origin main-fix"
t ALLOW "git push origin mainline"
t ALLOW "git merge main"
t ALLOW "git merge --no-ff issue/foo"
t ALLOW "git status"
t ALLOW "git log --oneline origin/main..HEAD"
t ALLOW "git fetch origin main"
t ALLOW 'echo "remember to git push main later"'

# --- a repo whose HEAD really is main, for the bare-push / merge-into cases ---
R=/home/emiel/.claude/jobs/df9bc0fb/tmp/fakemain
rm -rf "$R"; mkdir -p "$R"
( cd "$R" && git init -q -b main . && git commit -q --allow-empty -m x ) >/dev/null 2>&1
echo "=== must DENY (HEAD = main, in a scratch repo) ==="
t DENY  "git push" "$R"
t DENY  "git merge --no-ff issue/foo" "$R"
echo "=== must ALLOW (HEAD = main: reading is fine) ==="
t ALLOW "git status" "$R"
t ALLOW "git log" "$R"
rm -rf "$R"

echo
echo "pass=$pass fail=$fail"
[ "$fail" -eq 0 ]
