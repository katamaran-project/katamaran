#!/usr/bin/env bash
set -e

declare -A before
declare -A after

REBEFORE='([0-9.]+) Timing before: (.+)'
REAFTER='([0-9.]+) Timing after: (.+)'

while read line
do
   # echo $line
   if [[ "$line" =~ $REBEFORE ]]; then
     func="${BASH_REMATCH[2]}"
     time="${BASH_REMATCH[1]}"
     before[$func]="$time"
   fi

   if [[ "$line" =~ $REAFTER ]]; then
     func="${BASH_REMATCH[2]}"
     time="${BASH_REMATCH[1]}"
     awk "BEGIN {printf(\"$func %.4f\n\", $time - ${before[$func]})}"
   fi
done
