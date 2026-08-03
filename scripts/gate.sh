#!/usr/bin/env bash
# scripts/gate.sh — Katamaran merge gate.
#
# Enforces the invariant that mainline is always:
#   (1) full-compiling  — proof bodies, not just .vos
#   (2) hole-free       — no Admitted / Axiom / Conjecture / Parameter in scope
#   (3) axiom-clean     — the CFGVer end theorems are "Closed under the global
#                         context" (Print Assumptions shows no axioms)
#
# coqc's exit status only guarantees (1) partially; (2) and (3) are exactly what a
# green compile does NOT catch (a vacuous or axiom-polluted proof compiles fine).
#
# Usage:
#   ./scripts/gate.sh            run the full gate; exit 0 = safe to merge
#   COQC=rocq ./scripts/gate.sh  override the compiler binary (default: coqc)
#
# Installed as the pre-merge-commit hook by scripts/install-hooks.sh, where it runs
# automatically before a merge commit into a protected branch is created.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

# ---- config (edit these) ---------------------------------------------------

# Build targets: the .vo whose dependency closure the gate compiles. Building the
# end example's .vo pulls in everything the results rest on, while skipping
# unrelated experiments (e.g. theories/Staging/) that are active in _CoqProject.
BUILD_TARGETS=("case_study/RiscvPmp/CFGVer/Results.vo")

# Directories scanned for proof holes.
SCOPE_DIRS=("case_study/RiscvPmp/CFGVer")

# End theorems that must stay axiom-clean. All live at top level in
# case_study/RiscvPmp/CFGVer/Results.v. Run the gate once to establish the
# baseline; if a theorem here legitimately depends on an axiom, remove it from
# this list (and note why) rather than weakening the check.
#
# ONLY THE `_param` THEOREMS ARE LISTED, deliberately. Each program also has a
# concrete-base corollary (`X_noninterferent`, plus `jmp_fwd_noninterferent_cfg`
# and `cmovznz4_noninterferent_at_start`) whose entire proof is
# `apply X_noninterferent_param; unfold init_addr, lenAddr; lia` — its axiom set
# is the `_param`'s plus whatever `lia` uses, and `lia` is axiom-free. So the
# `_param` theorems carry all the content, and checking 12 instead of 25 halves
# a probe that is genuinely expensive (see the batching note in step 3).
#
# What this stops catching: a concrete corollary that someone later RE-PROVES
# directly (with an axiom or an Admitted lemma) instead of via its `_param`. If
# you do that, add it back to this list.
AXIOM_CLEAN_THMS=(
  "swap_noninterferent_param"
  "jumpIfZero_noninterferent_param"
  "jmp_fwd_noninterferent_param"
  "countdown_noninterferent_param"
  "countdown_mem_noninterferent_param"
  "set_X2_to_42_noninterferent_param"
  "cmovznz4_noninterferent_param"
  "precompute_noninterferent_param"
  "key_schedule_loop2_noninterferent_param"
  "muladd_q_noninterferent_param"
  "modpow_win_noninterferent_param"
  "modpow_win_full_noninterferent_param"
  "check_scalar_noninterferent_param"
)

COQC="${COQC:-coqc}"

# ---- helpers ---------------------------------------------------------------

red()  { printf '\033[31m%s\033[0m\n' "$*"; }
grn()  { printf '\033[32m%s\033[0m\n' "$*"; }
ylw()  { printf '\033[33m%s\033[0m\n' "$*"; }
fail() { red "✗ GATE FAILED: $*"; exit 1; }

# ---- (1) full build --------------------------------------------------------

grn "▶ [1/3] Build (target closure, incremental)…"
make Makefile.coq >/dev/null || fail "coq_makefile could not regenerate Makefile.coq"

# Parallelism is bounded by MEMORY, not cores: every coqc process loads its full
# Require closure, so a naive `-j$(nproc)` (e.g. -j16 on a 15 GiB box) demands
# tens of GB of baseline and OOM-kills mid-build (SIGTERM / make Error 143 —
# looks like a compile failure but is a kill). Budget per job against total RAM,
# clamp to [1, nproc]. Override explicitly with GATE_JOBS.
#
# Retuned 2026-07-27 after the Iris split of Spec/Verifier/Tables (00ac87a3) cut
# the peaks. Measured peak RSS per file now:
#
#   SpecIris 4.06, Adequacy 3.91, EndToEnd 3.84, VerifierRel 3.75,
#   TablesRel 3.63  -- these five are a SERIAL chain, so at most one is ever
#                      resident at a time
#   Cmovznz4 3.52 (was 5.72), KeyScheduleLoop 2.91, everything else ~2.5
#
# The old formula divided TOTAL RAM, which is wrong: this box idles at ~6.5 GB
# used (desktop, editors, agent sessions), so only ~8.8 GB is actually available
# to the build. Budgeting against total is how you get a number that looks safe
# and then runs at 98% — a measured full rebuild at -j3 peaked at 15085 MB of
# 15312 MB, i.e. ~227 MB of real headroom. So: subtract a reserve for whatever
# else is running, THEN divide.
#
# Measured full CFGVer rebuilds on this 15.3 GB box:
#   -j3  448 s, peak 15085 MB (98.5%)
#   -j2  480 s, peak 14582 MB (95.2%)
# -j3 is only ~7% faster and both run hot, because the baseline dominates. If
# you have a browser open or the box has less free RAM, force GATE_JOBS=2 (or 1).
#
# Tune this budget on the peak-RSS numbers, NOT the wall times. Multi-GB coqc
# processes evict each other's .vo page cache, so a file's wall time depends on
# what ran before it: TablesRel.v (unchanged) measured 22 s / 43 s / 32 s on
# three consecutive runs, the 43 s one being immediately after SpecIris (4.0 GB)
# and VerifierRel (3.75 GB). Differences under ~2x in the timings above are not
# resolvable on this box; peak RSS is deterministic and is what bounds -j anyway.
#
# NOTE: PER_JOB_MB assumes the light/heavy layering in CFGVer/CLAUDE.md holds.
# Re-adding an Iris/ShallowExecutor require to a light file puts ~1.2 GB back on
# all seven examples and invalidates this budget.
if [ -n "${GATE_JOBS:-}" ]; then
  jobs="$GATE_JOBS"
else
  RESERVE_MB="${GATE_RESERVE_MB:-6000}"   # measured idle baseline on this box
  PER_JOB_MB="${GATE_PER_JOB_MB:-3000}"   # median post-split peak (~2.5-3.5 GB)
  mem_mb="$(free -m | awk '/^Mem:/ {print $2}')"
  jobs=$(( (mem_mb - RESERVE_MB) / PER_JOB_MB ))
  [ "$jobs" -lt 1 ] && jobs=1
  cores="$(nproc)"
  [ "$jobs" -gt "$cores" ] && jobs="$cores"
fi
grn "  (building with -j$jobs; override with GATE_JOBS=N)"
make -j"$jobs" -f Makefile.coq "${BUILD_TARGETS[@]}" \
  || fail "target closure does not compile: ${BUILD_TARGETS[*]}"

# ---- (2) proof holes -------------------------------------------------------

grn "▶ [2/3] Scanning for proof holes…"
# Fast heuristic; the Print Assumptions pass below is authoritative for reachable
# holes. Drop matches where the keyword sits inside a single-line (* … *) comment.
holes="$(grep -rnE 'Admitted\.|^[[:space:]]*(Axiom|Conjecture|Parameter)[[:space:]]' \
           "${SCOPE_DIRS[@]}" --include='*.v' \
         | grep -vE '\(\*.*(Admitted|Axiom|Conjecture|Parameter)' || true)"
if [ -n "$holes" ]; then
  red "$holes"
  fail "proof holes / axiom declarations found in scope"
fi

# ---- (3) axiom hygiene -----------------------------------------------------

grn "▶ [3/3] Axiom hygiene (Print Assumptions)…"

# Assemble coqc load-path flags from _CoqProject (-Q / -R, plus -arg values).
COQFLAGS=()
while IFS= read -r line; do
  case "$line" in
    -Q*|-R*) COQFLAGS+=($line) ;;                       # intentional word-split
    -arg*)   v="${line#-arg }"; v="${v%\"}"; v="${v#\"}"; COQFLAGS+=($v) ;;
  esac
done < <(grep -E '^[[:space:]]*(-Q|-R|-arg)' _CoqProject)

# The probe basename must be a valid Coq module name (no dots), so mktemp's
# tmp.XXXXXX pattern is unusable directly — use a fresh directory instead.
probedir="$(mktemp -d)"
trap 'rm -rf "$probedir"' EXIT

# The probe is BATCHED, and must stay that way.
#
# `Print Assumptions` fetches opaque proof bodies out of the .vo files and does
# NOT release them, so one process checking the whole list grows without bound
# and gets OOM-killed. The kill arrives as SIGTERM (exit 143) with NO Coq error
# text at all, which the previous single-process version mis-reported as "a
# listed theorem may be renamed/removed" — a misdiagnosis that cost a session's
# debugging. See the exit-code handling below.
#
# Measured on this box 2026-07-27 (peak RSS — deterministic, tune on this and
# NOT on wall time, same caveat as the -j budget above):
#   Require Import Results, 0 theorems : 3.40 GB  <- fixed baseline, PER PROCESS
#   + 1 Print Assumptions              : 3.79 GB  (+0.39, one-off opaque warm-up)
#   + each further theorem             : +0.255 GB, never released
# i.e. peak(N) ≈ 3790 + (N-1)*255 MB, and ~9 s per theorem after the first.
# At N=12 that predicts 6.6 GB — and it did die at 11/12 on a box with ~6.4 GB
# available. N=25 would need ~9.9 GB. Batching trades a repeated 3.4 GB / ~9 s
# `Require` for a bounded peak.
PROBE_BASE_MB="${GATE_PROBE_BASE_MB:-3790}"
PROBE_PER_THM_MB="${GATE_PROBE_PER_THM_MB:-255}"
PROBE_HEADROOM_MB="${GATE_PROBE_HEADROOM_MB:-1000}"

if [ -n "${GATE_PROBE_BATCH:-}" ]; then
  batch="$GATE_PROBE_BATCH"
else
  # AVAILABLE, not total: the probe runs after the build, on whatever is left.
  avail_mb="$(free -m | awk '/^Mem:/ {print $7}')"
  batch=$(( (avail_mb - PROBE_HEADROOM_MB - PROBE_BASE_MB) / PROBE_PER_THM_MB + 1 ))
  [ "$batch" -lt 1 ] && batch=1
  # Cap: beyond ~8 the linear model above is extrapolation, not measurement.
  [ "$batch" -gt 8 ] && batch=8
fi
grn "  (${#AXIOM_CLEAN_THMS[@]} theorems in batches of $batch; override with GATE_PROBE_BATCH=N)"

out=""
i=0
b=0
while [ "$i" -lt "${#AXIOM_CLEAN_THMS[@]}" ]; do
  b=$((b + 1))
  probe="$probedir/AxiomProbe$b.v"
  {
    echo "From Katamaran.RiscvPmp.CFGVer Require Import Results."
    for t in "${AXIOM_CLEAN_THMS[@]:$i:$batch}"; do echo "Print Assumptions $t."; done
  } > "$probe"

  set +e
  bout="$("$COQC" "${COQFLAGS[@]}" "$probe" 2>&1)"
  rc=$?
  set -e

  if [ "$rc" -ne 0 ]; then
    ylw "$bout"
    case "$rc" in
      137|143)
        red "batch $b (${AXIOM_CLEAN_THMS[*]:$i:$batch}) was KILLED — exit $rc, no Coq error."
        fail "axiom probe ran OUT OF MEMORY, this is not a proof failure: retry with GATE_PROBE_BATCH=$(( batch > 1 ? batch - 1 : 1 )), or free memory (see the peak-RSS model above)" ;;
      *)
        fail "axiom probe batch $b failed to compile (a listed theorem may be renamed/removed)" ;;
    esac
  fi
  out="$out$bout"$'\n'
  i=$((i + batch))
done

# Baseline: every end theorem depends on exactly the two standard axioms
# (the axiomatized instruction decoder and the MMIO environment) and nothing
# else. "Axiom-clean" here = no axioms BEYOND this whitelist — in particular
# no functional_extensionality, no classical axioms, and no Admitted lemmas
# (those show up in Print Assumptions output too).
ALLOWED_AXIOMS=("Machine.pure_decode" "Base.mmioenv")

expected=${#AXIOM_CLEAN_THMS[@]}
closed="$(printf '%s\n' "$out" | grep -c 'Closed under the global context' || true)"
sections="$(printf '%s\n' "$out" | grep -c '^Axioms:' || true)"
if [ "$((closed + sections))" -ne "$expected" ]; then
  ylw "$out"
  fail "axiom hygiene: expected $expected Print Assumptions reports, got $((closed + sections))"
fi

# Axiom declarations start at column 0 as "Qualified.name : type" (type
# continuation lines are indented). Collect the names, drop the whitelist.
grepv_args=()
for a in "${ALLOWED_AXIOMS[@]}"; do grepv_args+=(-e "$a"); done
bad="$(printf '%s\n' "$out" \
       | grep -E '^[A-Za-z_][A-Za-z0-9_.'\'']* :' | awk '{print $1}' | sort -u \
       | grep -vxF "${grepv_args[@]}" || true)"
if [ -n "$bad" ]; then
  ylw "$out"
  red "non-whitelisted assumptions: $bad"
  fail "axiom hygiene: end theorems depend on axioms beyond ${ALLOWED_AXIOMS[*]}"
fi

grn "✓ GATE PASSED — build clean, no holes, $expected end theorems axiom-clean (only: ${ALLOWED_AXIOMS[*]})."
