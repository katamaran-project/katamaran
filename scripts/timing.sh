#!/usr/bin/env bash
set -e

if ! command -v ts &> /dev/null; then
  echo "The ts command could not be found. Please install the moreutils package."
  exit 1
fi

if [ ! -f "$1" ]; then
  echo "Usage: $0 <input file>"
  exit 1
fi

egrep "[0-9.]+ Timing before:" "$1" | while read -r before col2 col3 func col5
do 
   egrep "Timing after: ${func}" "$1" | while read -r after col2
   do
     awk "BEGIN {printf(\"$func %.4f\n\", $after - $before)}"
   done
done
