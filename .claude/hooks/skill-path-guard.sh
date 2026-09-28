#!/usr/bin/env bash
# PreToolUse(Write|Edit): BLOCKING gate requiring the right skill(s) to be loaded
# before a file whose subject a skill already documents is written.
#
# Was v-write-guard.sh (2026-08-17, .v only); generalised the same day when the
# rule set grew past a handful. Table-driven now, because the previous shape --
# one `case` block per rule -- does not scale and the whole point is that adding
# rule N+1 stays trivial.
#
# WHY THIS EXISTS. Advisory nudging does not work. `skill-nudge.sh` fired early
# in the 2026-08-17 session, was read, and the session still hand-derived
# material that `core-executor-internals` documents -- while editing the very
# file that skill covers, with the skill named in a routing table it had just
# read. Two data points (2026-07-28 zero-Skill-calls; 2026-08-17) say the same
# thing: only DENY changes behaviour.
#
# THE PATH -> SKILL MAPPING IS NOT INVENTED HERE. For CFGVer it is transcribed
# from `case_study/RiscvPmp/CFGVer/CLAUDE.md`'s own file table, which is the
# project's documented answer to "which skill covers this file". If that table
# changes, change this to match -- they are supposed to agree.
#
# Design notes:
#   - ALL missing skills are collected and reported in ONE denial, so a file
#     needing two skills costs one round-trip, not two.
#   - Session-scoped via skill-load-marker.sh, so each requirement fires at most
#     once per session and long editing runs are not nagged.
#   - Throwaway `ZZ*.v` probes are exempt from the CFGVer-specific rules but NOT
#     from the blanket `rocq-implementation` rule.
#   - Only Write/Edit. Reading is `skill-nudge.sh`'s business (advisory).
#
# Override is deliberately NOT something the assistant can arrange: set
# CLAUDE_V_GUARD_OFF=1 in the environment Claude Code itself was launched with,
# or toggle the hook off in /hooks. A Bash call from inside a session cannot
# change the parent process's environment. (Name kept from v-write-guard.sh so
# an existing launcher env does not silently stop working.)
set -u

input=$(cat)

if [ "${CLAUDE_V_GUARD_OFF:-}" = "1" ]; then
  exit 0
fi

path=$(printf '%s' "$input" | jq -r '.tool_input.file_path // ""' 2>/dev/null) || exit 0
[ -n "$path" ] || exit 0

# Only files a skill actually covers. Bail early on everything else.
case $path in
  *.v) ;;
  */CFGVer/diagnostics/*.md) ;;
  # NOTE: plans/*.md is deliberately NOT here. A plan is "what we are going to
  # build"; no skill governs that. diagnostics/*.md is "what we concluded", which
  # cfgver-scaling-diagnostics does govern (the ablation discipline, the
  # retraction rules). Keeping plans/ out avoids a requirement with no content
  # behind it.
  *) exit 0 ;;
esac

sid=$(printf '%s' "$input" | jq -r '.session_id // "nosession"' 2>/dev/null) || sid=nosession
sid=${sid//[^A-Za-z0-9_-]/}
[ -n "$sid" ] || sid=nosession
dir="${TMPDIR:-/tmp}"

loaded() { [ -e "${dir}/claude-skillload-${1}-${sid}" ]; }

need=""    # newline-separated "skill<TAB>why"
req() {
  loaded "$1" && return 0
  case $need in
    *"$1	"*) return 0 ;;   # already listed
  esac
  need="${need}$1	$2
"
}

base=${path##*/}

# ---- blanket rule: any Rocq source ------------------------------------------
case $path in
  *.v) req rocq-implementation \
    "tier-1 entry point for writing/repairing a proof here; carries the rocq-mcp preamble-mode workflow (no longer hook-enforced: coqc-guard.sh was unwired 2026-09-25), and is the ONLY route to the tier-2 library skills (bv-pitfalls, rocq-pitfalls, iris-proofmode, core-executor-internals, relval-model, pred-modalities, cfgver-rsolve, cfgver-wp2, the two -internals), which are listed WITHOUT descriptions so nothing else surfaces them" ;;
esac

# ---- core framework ----------------------------------------------------------
case $path in
  */theories/Symbolic/Solver.v|*/theories/Symbolic/Monads.v|*/theories/MicroSail/SymbolicExecutor.v)
    req core-executor-internals \
      "how an \`assert\` is discharged against the path condition (solver_generic's stages, the wco walk, the wpathcondition world-extension) AND the \"Adding a NEW solver rule\" recipe -- where to hook, why returning \`error\` for \"cannot decide\" is unsoundness that does NOT fail the build, the Equations two-type-index refusal, and the iteration order that keeps you off ~6-minute rebuilds. On 2026-08-17 this file was edited without it and two builds were burned on a trap the recipe now documents" ;;
esac

# ---- the leakage model -------------------------------------------------------
# CONTENT-gated, not path-gated, and deliberately so. Base.v and Machine.v are
# large files that are overwhelmingly NOT about leakage (register decls, the
# semantics of every instruction), so a path-only rule would deny unrelated
# edits all day and train people to reach for the override. Fire only when the
# edit actually writes or deletes a leakage token.
#
# Matched against .tool_input's own string fields, never the whole JSON payload
# -- CLAUDE.md records four separate incidents of a guard that matched text
# merely MENTIONING its trigger. old_string is included on purpose: REMOVING a
# constructor or an emit site is the more dangerous direction (it silently
# weakens every noninterference theorem, and still compiles green), and that
# edit only mentions the token on the way out.
case $path in
  */RiscvPmp/Base.v|*/RiscvPmp/Machine.v)
    leakpayload=$(printf '%s' "$input" | jq -r '[.tool_input.new_string // "", .tool_input.old_string // "", .tool_input.content // ""] | join("\n")' 2>/dev/null) || leakpayload=""
    case $leakpayload in
      *LeakEvent*|*KLeak*|*"stm_foreign leak"*|*leak_event*|*LeakageTrace*|*fun_leak*)
        req leakage-model-change \
          "you are changing WHAT THE ATTACKER CAN SEE -- the one edit in this tree that changes the MEANING of every noninterference theorem at once, without restating any of them (noninterferent_strong concludes leakage_trace equality over \`list LeakEvent\` quantified abstractly). The skill carries the six mechanical Base.v arms, the emit-placement rules, why ty.prod beats ty.tuple for a multi-value payload (simplify_secLeak splits binops but has a standing TODO on tuples), and the three-cell check that distinguishes a real strengthening from a constructor nobody emits -- which compiles green and looks identical to success" ;;
    esac ;;
esac

# ---- the Pred/world/modality layer -------------------------------------------
case $path in
  */theories/Symbolic/Worlds.v|*/theories/Symbolic/UnifLogic.v)
    req pred-modalities \
      "this file DEFINES the Pred/world/modality layer -- Acc/sub_acc, Pred with its POINTWISE entails, and assuming/knowing/forgetting, which are the standard adjoint triple (f* / exists_f / forall_f) with knowing -| forgetting -| assuming proved right here. Two things are easy to break from inside and invisible from a goal: a backward modality goes VACUOUS whenever the step's substitution pins a variable (empty fibre => assuming is True and useless, knowing is False), and assuming is DERIVED from sub_acc, so every accessibility you add or change silently fixes what its modalities can express. A 2026-08-27 session spent a whole Phase A rediscovering both" ;;
esac

# ---- CFGVer: transcribed from CFGVer/CLAUDE.md's file table -------------------
case $path in
  */CFGVer/Spec.v)         req cfgver-contracts "CFGVer's own leakage-aware Specification instance lives here (secLeakvar / inv_leakage contracts), distinct from ../Contracts.v" ;;
  */CFGVer/SpecIris.v)     req cfgver-soundness "the shallow executor + Iris wiring; also DON'T re-add an Iris require to a light file (~1.2 GB onto every example)" ;;
  */CFGVer/Verifier.v)     req cfgver-executor "sexec_cfg_addr / scfg_verification_condition -- the symbolic decision layer"
                           req cfgver-contracts "since 2026-09-22 this file ALSO holds the CFGVerifierContract record + cfg_map, moved down from Contracts.v because ai_block carries a contract (PLAN-contract-ast Phase 4). Data only -- the VC over it is still cfg_vc in Contracts.v" ;;
  */CFGVer/VerifierRel.v)  req cfgver-refinement "cexec_cfg_addr, RefineCompat instances, itable_rel/etable_rel. If rsolve itself fails/hangs/eats GB, that is cfgver-rsolve instead" ;;
  */CFGVer/Tables.v)       req cfgver-executor "table builders; note the mandatory \`Open Scope list_scope.\` trap after the imports" ;;
  */CFGVer/TablesRel.v)    req cfgver-executor "the itable_rel/etable_rel faith lemmas" ;;
  */CFGVer/Contracts.v)    req cfgver-contracts "cfg_vc (the VC -- renamed from ValidCFGVerifierContract 2026-09-22), CFG_VC_triple, minimal_pre, solve_vc and the relval_fetch_* family. The RECORD itself moved to Verifier.v" ;;
  */CFGVer/GenContract.v)  req cfgver-gen-contract-internals "you are modifying the GENERATOR itself (gen_reg_asn/gen_pre/gen_implpre). Merely USING gen_contract is cfgver-gen-contract" ;;
  */CFGVer/GenSegment.v)   req cfgver-gen-contract-internals "the MID-PROGRAM SEGMENT generator (gen_seg_contract, gen_regs_at, solve_seg, the rc_* table). Sibling of GenContract.v; same skill" ;;
  */CFGVer/Adequacy.v)     req cfgver-soundness "myWP2_loop, create_resources, the semWP2_* / sound_*_myWP2 chain" ;;
  */CFGVer/GenCompose.v)   req cfgver-soundness "the composition combinators (seg_step/seg_loop) wrap sound_scfg_verification_condition_myWP2 -- same chain as Adequacy.v. NOTE: a dedicated skill for compositional segment proofs is the right follow-up (see plans/PLAN-segment-generators.md)" ;;
  */CFGVer/Validity.v)     req cfgver-endtoend-internals "the SEALED contract validity every bridge takes (ValidCFGVerifierContract; PLAN-valid-blk-annot Phase 4)" ;;
  */CFGVer/EndToEnd.v)     req cfgver-endtoend-internals "you are modifying the WIRING lemmas themselves (cfg_instrs_endToEnd, cfg_instrs_verified/_safe, the _with_mem variants)" ;;
  */CFGVer/Noninterference.v) req cfgver-endtoend "this is the TRUSTED STATEMENT surface -- changing it changes what is being proved" ;;
esac

# ---- CFGVer examples ---------------------------------------------------------
case $path in
  */CFGVer/Example/ZZ*.v) : ;;                       # throwaway probes: blanket rule only
  */CFGVer/Example/Prelude.v)
    req cfgver-new-example "the shared example preamble; it must stay free of EndToEnd or the 85 s Adequacy->EndToEnd chain serialises ahead of every example" ;;
  */CFGVer/Example/*Result.v)
    req cfgver-endtoend "the per-program end-to-end theorems -- gate-checked TRUSTED statement surface" ;;
  */CFGVer/Example/*.v)
    req cfgver-new-example "the 6-step recipe for an example: instrs/specs, exitCond/fuel/extra_exit_offs, gen_contract, discharging the VC, the end lemma. The *_instrs / *_specs blocks are TRUSTED statement surface" ;;
esac

# ---- CFGVer prose ------------------------------------------------------------
case $path in
  */CFGVer/diagnostics/*.md)
    req cfgver-scaling-diagnostics "the diagnostics/ convention and -- the step most often skipped -- how to design an ablation that isolates ONE candidate driver, plus the retraction discipline for overturning an earlier figure" ;;
esac

[ -n "$need" ] || exit 0

msg="BLOCKED by skill-path-guard: this file's subject is already documented, and the skill was not loaded.

${path}

Load these first (Skill tool), then retry:
"
while IFS=$'\t' read -r sk why; do
  [ -n "$sk" ] || continue
  msg="${msg}
  * ${sk}
      ${why}
"
done <<EOF
$need
EOF

msg="${msg}
Each requirement fires at most ONCE per session -- after the Skill call(s), later writes to this file pass. If you believe a requirement is wrong for this edit, say so rather than working around it; the mapping is meant to track CFGVer/CLAUDE.md's file table."

jq -n --arg r "$msg" '{
  hookSpecificOutput: {
    hookEventName: "PreToolUse",
    permissionDecision: "deny",
    permissionDecisionReason: $r
  }
}'
exit 0
