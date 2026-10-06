#!/usr/bin/env bash
# Test suite for skill-path-guard.sh's leakage-model rule (added 2026-09-11).
#
# The rule is CONTENT-gated: Base.v/Machine.v are mostly not about leakage, so
# it must fire on a leak token in the edit payload and stay silent otherwise.
# Both halves matter -- an over-firing guard trains people to use the override.
#
# NOTE the trap this suite exists to avoid: the hook signals denial with JSON
# (permissionDecision), NOT an exit code. A first version of this test read $?
# and reported every deny as "allow", i.e. "my hook is broken" when it was fine.
# Parse the JSON.
cd "$(dirname "$0")/../.." || exit 1
pass=0; fail=0
t() {
  got=$(printf '%s' "$2" | .claude/hooks/skill-path-guard.sh 2>/dev/null \
        | jq -r 'if (.hookSpecificOutput.permissionDecisionReason // "") | test("leakage-model-change") then "deny" else "allow" end' 2>/dev/null)
  [ -z "$got" ] && got=allow
  if [ "$got" = "$3" ]; then pass=$((pass+1)); echo "  PASS  $1"; \
  else fail=$((fail+1)); echo "  FAIL  $1  got=$got want=$3"; fi
}
S='"session_id":"leakguardtest"'
echo "== fires on a leakage-model change =="
t "Base.v: add LeakEvent constructor" "{$S,\"tool_input\":{\"file_path\":\"/x/case_study/RiscvPmp/Base.v\",\"new_string\":\"| LeakDiv : bv xlenbits -> LeakEvent\"}}" deny
t "Base.v: add KLeak tag"             "{$S,\"tool_input\":{\"file_path\":\"/x/case_study/RiscvPmp/Base.v\",\"new_string\":\"| KLeakDiv\"}}" deny
t "Base.v: unionk_ty leak_event arm"  "{$S,\"tool_input\":{\"file_path\":\"/x/case_study/RiscvPmp/Base.v\",\"new_string\":\"| leak_event => fun K => ...\"}}" deny
t "Machine.v: add an emit"            "{$S,\"tool_input\":{\"file_path\":\"/x/case_study/RiscvPmp/Machine.v\",\"new_string\":\"stm_foreign leak [exp_union leak_event KLeakDiv v];;\"}}" deny
t "Machine.v: REMOVE an emit"         "{$S,\"tool_input\":{\"file_path\":\"/x/case_study/RiscvPmp/Machine.v\",\"old_string\":\"stm_foreign leak [exp_union leak_event KLeakPc tmp];;\",\"new_string\":\"\"}}" deny
t "Base.v: full-file Write"           "{$S,\"tool_input\":{\"file_path\":\"/x/case_study/RiscvPmp/Base.v\",\"content\":\"Inductive LeakEvent : Set := | LeakPc : Addr -> LeakEvent.\"}}" deny
echo "== stays silent otherwise =="
t "Machine.v: unrelated instruction"  "{$S,\"tool_input\":{\"file_path\":\"/x/case_study/RiscvPmp/Machine.v\",\"new_string\":\"let: r := rs1_val +ᵇ rs2_val in\"}}" allow
t "Base.v: unrelated register decl"   "{$S,\"tool_input\":{\"file_path\":\"/x/case_study/RiscvPmp/Base.v\",\"new_string\":\"| x31 : Reg ty_xlenbits\"}}" allow
t "another .v merely mentioning it"   "{$S,\"tool_input\":{\"file_path\":\"/x/case_study/RiscvPmp/CFGVer/Results.v\",\"new_string\":\"(* see LeakEvent *)\"}}" allow
t "Solver.v mentioning secLeak"       "{$S,\"tool_input\":{\"file_path\":\"/x/theories/Symbolic/Solver.v\",\"new_string\":\"simplify_secLeak t\"}}" allow
t "non-.v file with every token"      "{$S,\"tool_input\":{\"file_path\":\"/x/notes.md\",\"new_string\":\"LeakEvent stm_foreign leak fun_leak\"}}" allow
echo; echo "  $pass passed, $fail failed"; [ "$fail" -eq 0 ]
