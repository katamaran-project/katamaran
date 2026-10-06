#!/usr/bin/env bash
# Test suite for skill-bash-write-guard.sh (2026-09-11).
#
# The whole difficulty is the read/write split: a guard that denies `cat
# SKILL.md` is worse than no guard, because it trains people to reach for the
# override. Half these cases exist to prove it stays silent.
#
# Denial is signalled by JSON (permissionDecision), NOT an exit code.
cd "$(dirname "$0")/../.." || exit 1
pass=0; fail=0
NEW=".claude/skills/zz-does-not-exist/SKILL.md"      # absent -> authoring
OLD=".claude/skills/cfgver/SKILL.md"                  # present -> rewrite
t() {
  got=$(printf '%s' "{\"session_id\":\"bashguardtest\",\"tool_input\":{\"command\":$2}}" \
        | .claude/hooks/skill-bash-write-guard.sh 2>/dev/null \
        | jq -r 'if (.hookSpecificOutput.permissionDecision // "") == "deny" then "deny" else "allow" end' 2>/dev/null)
  [ -z "$got" ] && got=allow
  if [ "$got" = "$3" ]; then pass=$((pass+1)); echo "  PASS  $1"; \
  else fail=$((fail+1)); echo "  FAIL  $1  got=$got want=$3"; fi
}
echo "== must DENY: real writes to a SKILL.md =="
t "heredoc authoring a new skill"   "\"cat > $NEW <<'EOF'\\nhi\\nEOF\""                 deny
t "echo append"                     "\"echo hi >> $NEW\""                                deny
t "tee"                             "\"echo hi | tee $NEW\""                             deny
t "tee -a with flag"                "\"echo hi | tee -a $NEW\""                          deny
t "sed -i in place"                 "\"sed -i 's/a/b/' $NEW\""                           deny
t "cp onto a skill"                 "\"cp /tmp/draft.md $NEW\""                          deny
t "mv onto a skill"                 "\"mv /tmp/draft.md $NEW\""                          deny
t "dd of="                          "\"dd if=/tmp/x of=$NEW\""                           deny
t "python open(...,'w')"            "\"python3 -c \\\"open('$NEW','w').write('x')\\\"\"" deny
t "rewrite w/ description (exists)" "\"cat > $OLD <<'EOF'\\ndescription: new\\nEOF\""     deny
echo "== must ALLOW: reads and near-misses =="
t "cat a SKILL.md"                  "\"cat $OLD\""                                       allow
t "grep across skills"              "\"grep -rn foo .claude/skills/*/SKILL.md\""         allow
t "sed -n (read only)"              "\"sed -n '1,20p' $OLD\""                            allow
t "ls the skills dir"               "\"ls .claude/skills/\""                             allow
t "read SKILL.md, write elsewhere"  "\"grep description $OLD > /tmp/out.txt\""           allow
t "wc over skills"                  "\"wc -l .claude/skills/*/SKILL.md\""                allow
t "write a NON-skill md"            "\"cat > notes/SKILL.md.bak <<'EOF'\\nx\\nEOF\""     allow
t "python READING a SKILL.md"       "\"python3 -c \\\"print(open('$OLD').read())\\\"\""   allow
t "unrelated command"               "\"make -f Makefile.coq all\""                       allow
t "body-only rewrite of existing"   "\"cat > $OLD <<'EOF'\\n# just body text\\nEOF\""     allow
echo; echo "  $pass passed, $fail failed"; [ "$fail" -eq 0 ]
