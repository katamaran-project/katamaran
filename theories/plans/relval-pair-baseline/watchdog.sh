#!/bin/bash
# kill a coqc in WT whose USER cpu exceeds 2*baseline+10 s (baseline: KR per-file.tsv)
WT=$1; TSV=$2; LOG=$3; TCK=$(getconf CLK_TCK)
while true; do
  for pid in $(pgrep -x coqc); do
    cwd=$(readlink /proc/$pid/cwd 2>/dev/null); [ "$cwd" = "$WT" ] || continue
    src=$(tr '\0' '\n' < /proc/$pid/cmdline 2>/dev/null | grep '\.v$' | tail -1); [ -n "$src" ] || continue
    vo=${src%.v}.vo; base=$(awk -F'\t' -v f="$vo" '$1==f{print $2}' "$TSV")
    ut=$(awk -v t=$TCK '{print $14/t}' /proc/$pid/stat 2>/dev/null); [ -n "$ut" ] || continue
    if [ -n "$base" ] && awk -v u=$ut -v b=$base 'BEGIN{exit !(u > 2*b+10)}'; then
      echo "$(date +%T) KILL $src user=${ut}s base=${base}s" >> $LOG; kill $pid
    fi
  done
  sleep 5
done
