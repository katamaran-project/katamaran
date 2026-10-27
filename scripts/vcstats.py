#!/usr/bin/env python3
"""Turn the output of a VC statistics file into CSV.

Usage: scripts/vcstats.py case_study/Stats/NAME.log   (CSV on stdout)

Run via `make vcstats`, which compiles each case_study/Stats/NAME.v into
NAME.log and NAME.csv. One row per function/block and VC stage, plus a TOTAL
row per stage.
"""

import os
import re
import sys

# Stage names per stats file; FemtoKernel also prints instruction counts.
STAGES = {"FemtoKernel": ["raw", "postprocess", "postprocess2"]}
DEFAULT_STAGES = ["raw", "postprocess", "replay"]
COUNTS = ["nodes", "leaves", "errors", "debugs", "forks",
          "asserts", "assumes", "quants"]
HEADER = ["name", "fuel", "instructions", "stage"] + COUNTS + ["secs"]

# A VCSTAT label, the printed term, then the timing line of [Time].
ENTRY = re.compile(
    r"VCSTAT ([^\s\"]+)(?: fuel=(\d+))?(.*?)Finished transaction in ([0-9.]+) secs",
    re.S)


def rows(femto, stages, output):
    for name, fuel, term, secs in ENTRY.findall(output):
        nums = [int(n) for n in re.findall(r"\d+", term)]
        instrs = ""
        if femto:
            instrs, nums = nums[0], nums[1:]
        if len(nums) != len(stages) * len(COUNTS):
            sys.exit(f"unexpected output for {name}: {term.strip()}")
        for i, stage in enumerate(stages):
            counts = nums[i * len(COUNTS):(i + 1) * len(COUNTS)]
            yield [name, fuel, instrs, stage] + counts + [secs]


def main():
    log = sys.argv[1]
    case_study = os.path.splitext(os.path.basename(log))[0]
    stages = STAGES.get(case_study, DEFAULT_STAGES)
    with open(log) as f:
        output = f.read()
    print(",".join(HEADER))
    total = {stage: [0] * (len(COUNTS) + 1) for stage in stages}
    found = False
    for row in rows(case_study == "FemtoKernel", stages, output):
        found = True
        print(",".join(map(str, row)))
        sums = total[row[3]]
        for i, v in enumerate(row[4:-1] + [float(row[-1])]):
            sums[i] += v
    if not found:
        sys.exit(f"no VCSTAT output in {log}")
    for stage, sums in total.items():
        print(",".join(map(str, ["TOTAL", "", "", stage] + sums[:-1] + [f"{sums[-1]:.3f}"])))


if __name__ == "__main__":
    main()
