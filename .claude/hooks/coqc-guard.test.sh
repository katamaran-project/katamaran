#!/bin/bash
# 15-case suite for coqc-guard.sh.  Run it after ANY edit to that hook: it is
# load-bearing in both directions -- a false ALLOW silently disables the guard,
# a false DENY blocks all builds.
J='{"session_id":"regr","tool_input":{"command":"%s"}}'
WRAP=$(mktemp /tmp/zzwrap-XXXX.sh); HARMLESS=$(mktemp /tmp/zzharm-XXXX.sh)
printf '#!/bin/bash\ncoqc -q "case_study/RiscvPmp/CFGVer/Example/$1.v"\n' > "$WRAP"
printf '#!/bin/bash\necho hi\n' > "$HARMLESS"
chmod +x "$WRAP" "$HARMLESS"
trap 'rm -f "$WRAP" "$HARMLESS"' EXIT
cd "$(dirname "$0")/../.." || exit 1
v() { printf "$J" "$1" | .claude/hooks/coqc-guard.sh 2>/dev/null | grep -q deny && echo DENY || echo ALLOW; }
rm -f /tmp/claude-rocq-interactive-regr-*
T=case_study/RiscvPmp/CFGVer/Example/ZZMladTail.v
K=$(printf '%s' "$T" | cksum | cut -d' ' -f1)
p() { printf "  %-46s want %-5s got %s\n" "$1" "$2" "$(v "$3")"; }
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
KO=$(printf '%s' case_study/RiscvPmp/Base.v | cksum | cut -d' ' -f1)
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
