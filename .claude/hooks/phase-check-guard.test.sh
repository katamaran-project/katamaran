#!/usr/bin/env bash
# Test harness for .claude/hooks/phase-check-guard.sh. Lives in a file, not in a
# Bash tool command string, because its text contains the very builds the guard
# denies.
H=/home/emiel/Documents/katamaran/.claude/hooks/phase-check-guard.sh
export TMPDIR=$(mktemp -d)
unset CLAUDE_PHASE_GUARD_OFF
R=case_study/RiscvPmp/CFGVer/Results.vo
pass=0; fail=0

t () { # $1 expect DENY|ALLOW, $2 command, $3 session id (default t)
  local json out got r
  json=$(jq -n --arg c "$2" --arg s "${3:-t}" '{tool_input:{command:$c},session_id:$s}')
  out=$(printf '%s' "$json" | bash "$H" 2>/dev/null)
  if printf '%s' "$out" | grep -q '"deny"'; then got=DENY; else got=ALLOW; fi
  if [ "$got" = "$1" ]; then r="ok  "; pass=$((pass+1)); else r="FAIL"; fail=$((fail+1)); fi
  printf '%s %-6s %s\n' "$r" "$got" "$2"
}

echo "=== must DENY (skill not loaded) ==="
t DENY  "make -f Makefile.coq $R"
t DENY  "make -f Makefile.coq TIMED=1 -k -j1 $R"
t DENY  "cd /home/emiel/Documents/katamaran-relval-rsa && make -f Makefile.coq -j1 $R > log 2>&1; echo EXIT \$?"
t DENY  "make -f Makefile.coq -j1 $R case_study/RiscvPmp/CFGVer/Example/Rsa/RsaMemcpy.vo"
t DENY  "(time make -f Makefile.coq $R) > log 2>&1"
t DENY  "nohup make -f Makefile.coq $R &"
t DENY  "GATE_JOBS=1 make -f Makefile.coq $R"
t DENY  "make -f Makefile.coq"
t DENY  "make -f Makefile.coq -j1"
t DENY  "make -f Makefile.coq vok"
t DENY  "./scripts/gate.sh"
t DENY  "scripts/gate.sh"
t DENY  "COQC=rocq ./scripts/gate.sh"
t DENY  "bash scripts/gate.sh"
t DENY  "/home/emiel/Documents/katamaran/scripts/gate.sh"
t DENY  "make Results.vo"

echo "=== must ALLOW ==="
t ALLOW "make -f Makefile.coq theories/Symbolic/Solver.vo"
t ALLOW "make -f Makefile.coq TIMED=1 -k -j1 case_study/RiscvPmp/CFGVer/Example/Rsa/RsaCcopy.vo case_study/RiscvPmp/CFGVer/Verifier.vo"
t ALLOW "make -f Makefile.coq vos"
t ALLOW "make -f Makefile.coq case_study/RiscvPmp/CFGVer/Results.vos"
t ALLOW "make -f Makefile.coq -n $R"
t ALLOW "make -f Makefile.coq clean"
t ALLOW "cat scripts/gate.sh"
t ALLOW "command grep -n BUILD_TARGETS scripts/gate.sh"
t ALLOW "echo 'later: make -f Makefile.coq $R'"
t ALLOW "less /home/emiel/Documents/katamaran/scripts/gate.sh"
t ALLOW "ls case_study/RiscvPmp/CFGVer/Results.vo"
t ALLOW "git log --oneline -3"

echo "=== loaded marker satisfies it, per session ==="
: > "$TMPDIR/claude-skillload-phase-check-s1"
t ALLOW "make -f Makefile.coq $R" s1
t ALLOW "./scripts/gate.sh" s1
t DENY  "make -f Makefile.coq $R" s2

echo "=== override ==="
export CLAUDE_PHASE_GUARD_OFF=1
t ALLOW "make -f Makefile.coq $R"
unset CLAUDE_PHASE_GUARD_OFF

rm -rf "$TMPDIR"
echo "pass=$pass fail=$fail"
[ "$fail" -eq 0 ]
