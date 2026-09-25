#!/bin/bash
# 21-case suite for coqc-guard.sh AND rocq-interactive-marker.sh.  Run it after
# ANY edit to either hook: it is load-bearing in both directions -- a false
# ALLOW silently disables the guard, a false DENY blocks all builds.
#
# The last section drives the MARKER HOOK itself rather than writing a marker
# by hand.  That is deliberate: until 2026-09-24 every case here hand-computed
# the key, so the suite tested the guard against its own idea of the key and
# never against the key the marker actually writes -- which is exactly where
# the absolute-vs-relative false-deny bug lived, 15/15 green throughout.
J='{"session_id":"regr","tool_input":{"command":"%s"}}'
WRAP=$(mktemp /tmp/zzwrap-XXXX.sh); HARMLESS=$(mktemp /tmp/zzharm-XXXX.sh)
printf '#!/bin/bash\ncoqc -q "case_study/RiscvPmp/CFGVer/Example/$1.v"\n' > "$WRAP"
printf '#!/bin/bash\necho hi\n' > "$HARMLESS"
chmod +x "$WRAP" "$HARMLESS"
trap 'rm -f "$WRAP" "$HARMLESS"' EXIT
cd "$(dirname "$0")/../.." || exit 1
# ISOLATE THE RATE-LIMIT STATE.  The guard records every build it ALLOWS into
# $XDG_RUNTIME_DIR, and this suite's ALLOW cases are indistinguishable from real
# builds -- so running it spent the LIVE session's budget and blocked the next
# genuine `make` (2026-09-24).
XDG_RUNTIME_DIR=$(mktemp -d); export XDG_RUNTIME_DIR
trap 'rm -f "$WRAP" "$HARMLESS"; rm -rf "$XDG_RUNTIME_DIR"' EXIT
v() { printf "$J" "$1" | .claude/hooks/coqc-guard.sh 2>/dev/null | grep -q deny && echo DENY || echo ALLOW; }
rm -f /tmp/claude-rocq-interactive-regr-*
T=case_study/RiscvPmp/CFGVer/Example/ZZMladTail.v
TABS=$(realpath "$T")
# keys are over the CANONICAL path (see canon_path in both hooks)
K=$(printf '%s' "$TABS" | cksum | cut -d' ' -f1)
# write a marker the way the real tool call does: through the marker hook
mark() { printf '{"session_id":"regr","cwd":"%s","tool_input":{"file":"%s"}}' "$2" "$1" \
           | .claude/hooks/rocq-interactive-marker.sh; }
fails=0; total=0
p() { got=$(v "$3"); total=$((total+1))
      if [ "$got" = "$2" ]; then st="ok  "; else st="FAIL"; fails=$((fails+1)); fi
      printf "  [%s] %-44s want %-5s got %s\n" "$st" "$1" "$2" "$got"; }
echo "--- must ALLOW (no regressions) ---"
p "inspection: ps|grep"        ALLOW 'ps -ef | grep coqc'
p "grep in a file"             ALLOW "grep -n 'coqc' notes.txt"
p "make -n"                    ALLOW 'make -f Makefile.coq -n'
p "make clean"                 ALLOW 'make -f Makefile.coq clean'
p "echo mentioning make"       ALLOW 'echo remember to make -f Makefile.coq'
p "unrelated make"             ALLOW 'make -C /tmp/other all'
p "names a hook file"          ALLOW 'cat .claude/hooks/coqc-guard.sh'
p "harmless script"            ALLOW "bash $HARMLESS"
echo "--- same-target rule (source newer than .vo) ---"
touch "$T"
p "ZZ probe, no check"         DENY  "coqc $T"
date +%s%N > /tmp/claude-rocq-interactive-regr-$K
p "ZZ probe, checked"          ALLOW "coqc $T"
rm -f /tmp/claude-rocq-interactive-regr-*
KO=$(printf '%s' "$(realpath case_study/RiscvPmp/Base.v)" | cksum | cut -d' ' -f1)
date +%s%N > /tmp/claude-rocq-interactive-regr-$KO
p "checked a DIFFERENT file"   DENY  "coqc $T"
rm -f /tmp/claude-rocq-interactive-regr-*
date +%s%N > /tmp/claude-rocq-interactive-regr-any
p "preamble marker, 1st"       ALLOW "coqc $T"
p "preamble marker, 2nd"       DENY  "coqc $T"
echo "--- builds hidden in scripts ---"
rm -f /tmp/claude-rocq-interactive-regr-*
p "wrapper script, no check"   DENY  "nohup $WRAP ZZMladTail"
date +%s%N > /tmp/claude-rocq-interactive-regr-$K
p "wrapper script, checked"    ALLOW "nohup $WRAP ZZMladTail"
echo "--- marker hook + guard agree on the PATH, not its spelling ---"
CFG=$PWD/case_study/RiscvPmp/CFGVer
rm -f /tmp/claude-rocq-interactive-regr-*
mark "$TABS" "$PWD"
p "check ABS, build REL"       ALLOW "coqc $T"
rm -f /tmp/claude-rocq-interactive-regr-*
mark "$T" "$PWD"
p "check REL, build ABS"       ALLOW "coqc $TABS"
rm -f /tmp/claude-rocq-interactive-regr-*
mark "Example/ZZMladTail.v" "$CFG"
p "check REL-to-other-cwd"     ALLOW "coqc $T"
rm -f /tmp/claude-rocq-interactive-regr-*
p "cd DIR && rel, no check"    DENY  "cd $CFG && coqc Example/ZZMladTail.v"
mark "$TABS" "$PWD"
p "cd DIR && rel, checked"     ALLOW "cd $CFG && coqc Example/ZZMladTail.v"
rm -f /tmp/claude-rocq-interactive-regr-*
mark "$(realpath case_study/RiscvPmp/Base.v)" "$PWD"
p "abs check of OTHER file"    DENY  "coqc $TABS"
echo "--- a probe spelled relative to its cd is still a probe (rate limit) ---"
rm -f /tmp/claude-rocq-interactive-regr-*
# Put the source just BELOW its .vo, so the same-target rule is silent and only
# the rate limit is under test.  NOT `touch -d '1 hour ago'`: the .vo may be
# days old, and a source newer than it trips the other rule -- which is what
# the first draft of this case did, reading as a hook bug.
touch -d "@$(( $(stat -c %Y "${T}o") - 60 ))" "$T"
export CLAUDE_COQC_GUARD_MAX=1
p "cd-rel ZZ probe, 1st"       ALLOW "cd $CFG && coqc Example/ZZMladTail.v"
p "cd-rel ZZ probe, 2nd"       ALLOW "cd $CFG && coqc Example/ZZMladTail.v"
p "non-probe, 1st"             ALLOW "coqc case_study/RiscvPmp/Base.v"
p "non-probe, 2nd (limited)"   DENY  "coqc case_study/RiscvPmp/Base.v"
unset CLAUDE_COQC_GUARD_MAX
touch "$T"

echo
if [ "$fails" -eq 0 ]; then echo "PASS: $total/$total"; else echo "FAIL: $fails of $total cases"; fi
exit $((fails > 0))
