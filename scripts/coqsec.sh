#!/bin/bash

file=$1
id=$2
cmd=${3:-"Section"}

# A fourth argument can be used for non-"End $id" use cases
# Example: ./coqsec.sh $minimalcaps/Machine.v Fun Inductive ' \.' will
# output the inductive definition of Fun and nothing else (it ends with a ".")
# Note the backslash (regex!) and the space as the first part of the "ending",
# this is need because we can have qualified names (ty.word)!
if [ "$#" -ne 4 ]; then
	cat $file | awk "/$cmd $id/,EOF" | awk "1;/End $id/ {exit}"
else
	cat $file | awk "/$cmd $id/,EOF" | awk "1;/$4/ {exit}"
fi
