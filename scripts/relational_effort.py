#!/usr/bin/env python3
"""Size of the relational extension of Katamaran, compared with the unary
development it builds on (evaluation section of the PLDI'27 paper).

LOC are the specification plus proof lines that `rocq wc` reports; blank
and comment lines are not counted.  Every row pairs a part of the unary
development with its relational counterpart.  Most rows count whole files;
`only(f, A, ...)` counts just the Sections/Modules named A, ... in file f,
and `but(f, A, ...)` the rest of f.

Usage:  scripts/relational_effort.py [--latex]
"""

import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
IRIS = "theories/Iris"
CS = "case_study/RiscvPmp"
FK = f"{CS}/FemtoKernel"


def only(path, *names):
    return (path, names, True)


def but(path, *names):
    return (path, names, False)


def built_files():
    with open(os.path.join(ROOT, "_CoqProject"), encoding="utf-8") as f:
        return [l.strip() for l in f if l.strip().endswith(".v") and not l.startswith("#")]


# Generic Katamaran outside the Iris model; Staging is experimental.
CORE = [f for f in built_files()
        if f.startswith("theories/") and not f.startswith((f"{IRIS}/", "theories/Staging/"))]

# (group, [(row, unary entries, relational entries)])
TABLE = [
    ("Framework", [
        ("Syntax, semantics, symbolic executor", CORE, []),
        # Resources, weakest precondition, proof rules, adequacy; relational: also
        # focusing and double vision triples.
        ("Iris model of the program logic",
         [f"{IRIS}/Base.v", f"{IRIS}/Resources.v", f"{IRIS}/WeakestPre.v", but(f"{IRIS}/Instance.v", "TotalTriple")],
         [f"{IRIS}/{f}.v" for f in "BinaryResources BinaryWeakestPre BinaryAdequacy BinaryInstance".split()]),
        ("Total weakest precondition",
         [f"{IRIS}/TotalWeakestPre.v", only(f"{IRIS}/Instance.v", "TotalTriple")], []),
    ]),
    ("RISC-V universal contract", [
        ("Machine model, function contracts",
         [f"{CS}/{f}.v" for f in "Base Machine PmpCheck Sig Logic Contracts Reification".split()], []),
        ("Iris model, universal contract",
         [f"{CS}/{f}.v" for f in "IrisModel IrisInstance trace iostate Model LoopVerification".split()],
         [f"{CS}/{f}Binary.v" for f in "IrisModel IrisInstance Model LoopVerification".split()]),
    ]),
    ("FemtoKernel", [
        ("Block verifier", [f"{CS}/BlockVer/Spec.v", f"{CS}/BlockVer/TotalVerifier.v"],
         [f"{CS}/BlockVer/BinaryVerifier.v"]),
        ("Kernel, block verification", [f"{FK}/Kernel.v", f"{FK}/BlockVerification.v"], []),
        ("End-to-end theorem", [f"{FK}/Integrity.v", f"{CS}/UnaryAdequacy.v"], [f"{FK}/Confidentiality.v"]),
    ]),
]


def source(entry):
    """The text of an entry: a whole file, or only/but some of its blocks."""
    path, names, keep = (entry, (), False) if isinstance(entry, str) else entry
    with open(os.path.join(ROOT, path), encoding="utf-8") as f:
        lines = f.readlines()
    out, end = [], None
    for line in lines:
        if end is None:
            m = re.match(r"\s*(?:Module|Section)\s+(?:Type\s+)?([\w']+)", line)
            if m and m.group(1) in names:
                end = f"End {m.group(1)}."
        if (end is not None) == keep:
            out.append(line)
        if end is not None and line.strip() == end:
            end = None
    return "".join(out)


def loc(entries):
    """Spec plus proof lines of the entries, according to `rocq wc`."""
    total = 0
    for e in entries:
        res = subprocess.run(["rocq", "wc"], input=source(e), capture_output=True, text=True, check=True)
        spec, proof, _ = res.stdout.splitlines()[1].split()
        total += int(spec) + int(proof)
    return total


def main():
    latex = "--latex" in sys.argv[1:]
    num = lambda n: f"{n:,}" if n else "--" if latex else "-"

    groups = []
    tu = tr = 0
    for group, rows in TABLE:
        counts = [(label, loc(unary), loc(relational)) for label, unary, relational in rows]
        gu, gr = sum(u for _, u, _ in counts), sum(r for _, _, r in counts)
        tu, tr = tu + gu, tr + gr
        groups.append((group, gu, gr, counts))

    if latex:
        # Two side-by-side tables, sized to their own content so they stay
        # top-aligned with a minimal gap between them: Framework and the
        # grand total on the left, the two case studies on the right.
        def rows_of(group, gu, gr, counts):
            out = [f"\\textit{{{group}}} & {num(gu)} & {num(gr)} \\\\"]
            out += [f"\\quad {label} & {num(u)} & {num(r)} \\\\" for label, u, r in counts]
            return out

        header = [" & Unary & Relational \\\\"]
        (fw_group, fw_gu, fw_gr, fw_counts), *case_studies = groups
        boxA = header + ["\\midrule"] + rows_of(fw_group, fw_gu, fw_gr, fw_counts)
        boxA += ["\\addlinespace[2.5em]", "\\midrule", f"Total & {num(tu)} & {num(tr)} \\\\"]
        boxB = header + ["\\midrule"]
        for i, (group, gu, gr, counts) in enumerate(case_studies):
            if i:
                boxB.append("\\midrule")
            boxB += rows_of(group, gu, gr, counts)

        def box(name, rows):
            print(f"\\sbox{{\\{name}}}{{%\n\\begin{{tabular}}[t]{{@{{}}lrr@{{}}}}\n\\toprule")
            for row in rows:
                print(row)
            print("\\bottomrule\n\\end{tabular}}")

        print("\\begingroup")
        print("\\setlength{\\tabcolsep}{4pt}")
        print("\\newsavebox{\\effortboxA}")
        print("\\newsavebox{\\effortboxB}")
        box("effortboxA", boxA)
        box("effortboxB", boxB)
        print("\\begin{minipage}[t]{\\wd\\effortboxA}\\usebox{\\effortboxA}\\end{minipage}\\hfill")
        print("\\begin{minipage}[t]{\\wd\\effortboxB}\\usebox{\\effortboxB}\\end{minipage}")
        print("\\endgroup")
    else:
        line = lambda l, u="", r="": print(f"{l:<52} {u:>8} {r:>11}")
        line("", "Unary", "Relational")
        for group, gu, gr, counts in groups:
            line(group, num(gu), num(gr))
            for label, u, r in counts:
                line("  " + label, num(u), num(r))
        line("Total", num(tu), num(tr))

    counted = {e if isinstance(e, str) else e[0] for _, rows in TABLE for _, u, r in rows for e in u + r}
    skipped = [f for f in built_files() if f.startswith((f"{IRIS}/", f"{CS}/")) and f not in counted]
    print(("% " if latex else "\n") + "Not counted: " + ", ".join(skipped))


if __name__ == "__main__":
    main()
