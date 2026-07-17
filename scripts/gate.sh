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
AXIOM_CLEAN_THMS=(
  "swap_noninterferent"
  "jumpIfZero_noninterferent"
  "jmp_fwd_noninterferent_cfg"
  "countdown_noninterferent"
  "countdown_mem_noninterferent"
  "set_X2_to_42_noninterferent_param"
  "cmovznz4_noninterferent_param"
  "cmovznz4_noninterferent"
  "cmovznz4_noninterferent_at_start"
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
make -j"$(nproc)" -f Makefile.coq "${BUILD_TARGETS[@]}" \
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
probe="$probedir/AxiomProbe.v"
trap 'rm -rf "$probedir"' EXIT
{
  echo "From Katamaran.RiscvPmp.CFGVer Require Import Results."
  for t in "${AXIOM_CLEAN_THMS[@]}"; do echo "Print Assumptions $t."; done
} > "$probe"

if ! out="$("$COQC" "${COQFLAGS[@]}" "$probe" 2>&1)"; then
  ylw "$out"
  fail "axiom probe failed to compile (a listed theorem may be renamed/removed)"
fi

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
