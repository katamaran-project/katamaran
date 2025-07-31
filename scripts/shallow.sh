#!/usr/bin/env bash
set -e

FINISH=0
PRUNED=0

while read line
do
    if [[ "$line" =~ FALSE ]]; then
        ((++PRUNED))
    fi
    if [[ "$line" =~ TRUE ]]; then
        ((++PRUNED))
    fi
    if [[ "$line" =~ FINISH ]]; then
        ((++FINISH))
    fi
done

echo "Shallow branching statistics:"
echo "{| branches := $((FINISH+PRUNED)); pruned := $PRUNED} |}"
