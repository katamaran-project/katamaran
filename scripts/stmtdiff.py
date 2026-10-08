"""Statement-level diff of commits: which theorem/definition STATEMENTS a commit
added (+), removed (-) or changed (~), ignoring proof bodies and comments.

    python3 scripts/stmtdiff.py <path-regex> <commit>...
    e.g. python3 scripts/stmtdiff.py 'Result\\.v$|Noninterference\\.v$' 0bc112da

Written 2026-10-08 to find trusted-surface changes in the commit history
(.claude/learning/commit-groups.md); meant for PLAN-spec-layer's Phase 6
statement review. HEURISTIC: a statement ends at `Proof.` (lemmas) or at the
first top-level `.` (definitions); Ltac, notation and `Section`-variable
changes are invisible to it.
"""
import os, subprocess, re, sys
REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

def git(*a):
    r = subprocess.run(["git", "-C", REPO] + list(a), capture_output=True, text=True)
    return r.stdout

def strip_comments(s):
    out = []; depth = 0; i = 0
    while i < len(s):
        if s.startswith("(*", i):
            depth += 1; i += 2; continue
        if depth and s.startswith("*)", i):
            depth -= 1; i += 2; continue
        if not depth:
            out.append(s[i])
        i += 1
    return "".join(out)

KW = r"(Theorem|Lemma|Corollary|Definition|Fixpoint|Example)"
def statements(text):
    t = strip_comments(text)
    res = {}
    for m in re.finditer(r"\b" + KW + r"\s+([A-Za-z0-9_']+)", t):
        name = m.group(2)
        kind = m.group(1)
        rest = t[m.start():]
        if kind in ("Theorem", "Lemma", "Corollary", "Example"):
            e = rest.find("Proof.")
            if e < 0: e = rest.find(".\n")
        else:
            # definition: up to first '.' followed by whitespace at top level
            mm = re.search(r"\.(\s|$)", rest)
            e = mm.start() if mm else len(rest)
        body = re.sub(r"\s+", " ", rest[:e]).strip()
        res[name] = body
    return res

def stmt_diff(commit, pathfilter):
    files = git("show", "--format=", "--name-status", commit).split("\n")
    out = []
    for line in files:
        if not line.strip(): continue
        parts = line.split("\t")
        st, path = parts[0], parts[-1]
        oldpath = parts[1] if st.startswith("R") else path
        if not re.search(pathfilter, path) and not re.search(pathfilter, oldpath): continue
        old = git("show", f"{commit}^:{oldpath}") if not st.startswith("A") else ""
        new = git("show", f"{commit}:{path}") if not st.startswith("D") else ""
        so, sn = statements(old), statements(new)
        added = [k for k in sn if k not in so]
        removed = [k for k in so if k not in sn]
        changed = [k for k in sn if k in so and sn[k] != so[k]]
        out.append((st, path, added, removed, changed))
    return out

if __name__ == "__main__":
    pf = sys.argv[1]
    for c in sys.argv[2:]:
        subj = git("log", "-1", "--format=%h %s", c).strip()[:90]
        print("####", subj)
        for st, path, a, r, ch in stmt_diff(c, pf):
            short = path.split("CFGVer/")[-1]
            print(f"  {st} {short}: +{a[:8]}{'...' if len(a)>8 else ''} -{r[:8]}{'...' if len(r)>8 else ''} ~{ch[:10]}{'...' if len(ch)>10 else ''}")
