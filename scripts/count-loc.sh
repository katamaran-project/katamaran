#!/bin/bash

katamaran=${1:-"./"}
scripts="$katamaran/scripts"
mincaps="$katamaran/case_study/MinimalCaps"
riscv="$katamaran/case_study/RiscvPmp"

_coqsec() {
  $scripts/coqsec.sh "$@"
}

_coqsec_wc() {
  _coqsec "$@" | coqwc
}

_coqsec_inductive_wc() {
  _coqsec "$@" | grep '|' | wc -l
}

# line count, ignores empty lines
_lc() {
  awk 'NF' "$@" | wc -l
}

_ghost_stmts_wc() {
  grep -i 'use lemma' $@ | wc -l
}

coqwc_spec() {
    coqwc -s "$@" | tail -1 | awk '{print $1}'
}

coqwc_proof() {
    coqwc -p "$@" | tail -1 | awk '{print $2}'
}

coqwc_total() {
    coqwc "$@" | tail -1 | awk '{print ($1 + $2)}'
}

_print() {
  category=$(printf '%-28s' "$1")
  local mincaps=$(printf '%-5s' "$2")
  local riscv=$(printf '%-5s' ${3:-""})
  local cerise=$(printf '%-5s' ${4:-"-"})
  echo "$category & $mincaps & $riscv & $cerise \\\\"
}

echo "\textbf{Category} & \textbf{\MinimalCaps{}} & \textbf{RISC-V PMP} & \textbf{Cerise} \\\\"
echo "\hline"

katamaran=$(mktemp -d /tmp/count-loc.XXXX.katamaran)
cp -r "$mincaps/../../theories/" $katamaran
rm -rf "$katamaran/theories/Staging"
rm -rf "$katamaran/theories/SmallStep/Inversion.v"

echo "\hline"
echo "\textbf{Generatable} & & & \\\\"

_print "\muSail{} LoC" "$(coqwc_spec "$mincaps/Base.v" "$mincaps/Machine.v")" "$(coqwc_spec "$riscv/Base.v" "$riscv/Machine.v")"

echo "\hline"
echo "\textbf{Case Study} & & & \\\\"

_print "Operational Semantics" "-" "-" "1190"
# The following only works because we have one constructor per line (starting with |)
_print "Nr. of \muSail{} Fns" "$(_coqsec_inductive_wc "$mincaps/Machine.v" "Fun" "Inductive" ' \.')" "$(_coqsec_inductive_wc "$riscv/Machine.v" "Fun" "Inductive" ' \.')"
_print "Nr. of Foreign Fns" "$(_coqsec_inductive_wc "$mincaps/Machine.v" "FunX" "Inductive" ' \.')" "$(_coqsec_inductive_wc "$riscv/Machine.v" "FunX" "Inductive" ' \.')"
_print "Nr. of Lemmas" "$(_coqsec_inductive_wc "$mincaps/Machine.v" "Lem" "Inductive" ' \.')" "$(_coqsec_inductive_wc "$riscv/Machine.v" "Lem" "Inductive" ' \.')" "142"
_print "Nr. of Lemma Invoc." "$(_ghost_stmts_wc $mincaps/Machine.v)" "$(_ghost_stmts_wc $riscv/Machine.v)"

tmp=$(mktemp /tmp/mincaps-stat.XXXX.v)
_coqsec "$mincaps/Contracts.v" "MinCapsSignature" "Module Import" > "$tmp"
contracthelper="$(_coqsec "$tmp" "ContractDefKit")"
contracts="$(_coqsec "$mincaps/Contracts.v" 'ContractDef\.')"
contractspec="$(echo -e "$contracthelper" "\n" "$contracts" | coqwc_spec)"
_print "Contract spec \muSail{} LoC" "$contractspec" "$(_coqsec $riscv/Contracts.v 'ContractDef\.' | coqwc_spec)"
_print "Contract spec Foreign LoC" "$(_coqsec $mincaps/Contracts.v ForeignDef | coqwc_spec)" "$(_coqsec $riscv/Contracts.v ForeignDef | coqwc_spec)"
_print "Contract spec Lemma LoC" "$(_coqsec $mincaps/Contracts.v LemDef | coqwc_spec)" "$(_coqsec $riscv/Contracts.v LemDef | coqwc_spec)" "2318"

contractproof="$(_coqsec "$mincaps/Contracts.v" "MinCapsValidContracts" "Module" | coqwc_proof)"
_print "Contract proof \muSail{} LoC" "$(_coqsec $mincaps/Contracts.v MinCapsValidContracts Module | coqwc_proof)" "$(_coqsec $riscv/Contracts.v RiscvPmpValidContracts Module | coqwc_proof)"
foreignproof="$(_coqsec "$mincaps/Model.v" "ForeignProofs" | coqwc_proof)"
_print "Contract proof Foreign LoC" "$(_coqsec $mincaps/Model.v ForeignProofs | coqwc_proof)" "$(_coqsec $riscv/Model.v ForeignProofs | coqwc_proof)"
_print "Contract proof Lemma LoC" "$(_coqsec $mincaps/Model.v LemProofs | coqwc_proof)" "$(_coqsec $riscv/Model.v LemProofs | coqwc_proof)" "2918"

irismodelmincaps=$(mktemp /tmp/mincaps-stat.XXXX.v)
_coqsec "$mincaps/Model.v" "MinCapsIrisBase" "Module Import" > "$irismodelmincaps"
_coqsec "$mincaps/Model.v" "MinCapsIrisInstance" "Module Import" >> "$irismodelmincaps"
irismodelriscv=$(mktemp /tmp/mincaps-stat.XXXX.v)
_coqsec "$riscv/IrisModel.v" "RiscvPmpIrisBase" "Module" > "$irismodelriscv"
_coqsec "$riscv/IrisInstance.v" "RiscvPmpIrisInstance" "Module" >> "$irismodelriscv"
_print "Iris Model LoC" "$(coqwc_total $irismodelmincaps)" "$(coqwc_total $irismodelriscv)" "1351"

_print "Nr. of Pure Predicates" "$(_coqsec_inductive_wc "$mincaps/Contracts.v" "PurePredicate" "Inductive" '\.')" "$(_coqsec_inductive_wc "$riscv/Sig.v" "PurePredicate" "Inductive" '\.')"

solverkit=$(mktemp /tmp/mincaps-stat.XXXX.v)
_coqsec "$mincaps/Contracts.v" "MinCapsSolverKit" "Module" > "$solverkit"
solverkitriscv=$(mktemp /tmp/mincaps-stat.XXXX.v)
_coqsec "$riscv/Sig.v" "RiscvPmpSolverKit" "Module" > "$solverkitriscv"
_print "User Solver LoC" "$(coqwc_total $solverkit)" "$(coqwc_total $solverkitriscv)"

_print "Universal Contract LoC" "$(coqwc_total "$mincaps/LoopVerification.v")" "$(coqwc_total "$riscv/LoopVerification.v")"
