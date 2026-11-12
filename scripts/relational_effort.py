#!/usr/bin/env python3
"""Measure the extra effort of the relational (binary) extension of the RISC-V
PMP case study, taking the unary verification as given.

Every Coq file of interest is split into sentences (comments stripped), the
sentences are grouped into items (one per vernacular command: Lemma,
Definition, Ltac, Import, ...), and every non-blank, non-comment line is
attributed to exactly one item, either as a spec line or as a proof line
(between Proof/Next Obligation and Qed/Defined/Admitted/Abort, like coqwc).

Items are then classified along two orthogonal axes using the rule tables
below:
  - component: which part of the development (universal contract, block
    verifier, program logic, focusing, FemtoKernel, ...);
  - kind: what sort of work (definitions, foreign function proofs, ghost lemma
    proofs, other lemmas, tactics, boilerplate, axioms).

The same machinery is run on the unary counterparts to give a baseline.

Usage:  scripts/relational_effort.py [--items items.csv] [--json out.json]
Run from anywhere; paths are resolved relative to the repository root.
"""

import argparse
import collections
import csv
import json
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CS = "case_study/RiscvPmp"

# ---------------------------------------------------------------------------
# Coq lexing

def strip_comments(text):
    """Return (code, comments): code has comments blanked out (newlines kept so
    line numbers survive), comments is a list of (start_line, end_line, text)."""
    out = []
    comments = []
    i, n = 0, len(text)
    depth = 0
    in_str = False          # string outside comments
    in_cstr = False         # string inside a comment
    line = 1
    cstart = None
    cbuf = []
    while i < n:
        c = text[i]
        two = text[i:i + 2]
        if depth == 0:
            if in_str:
                out.append(c)
                if c == '"':
                    if text[i + 1:i + 2] == '"':
                        out.append('"'); i += 1
                    else:
                        in_str = False
            elif two == "(*":
                depth = 1; cstart = line; cbuf = []
                out.append("  "); i += 2; continue
            else:
                out.append(c)
                if c == '"':
                    in_str = True
        else:
            if in_cstr:
                if c == '"':
                    in_cstr = False
            elif two == "(*":
                depth += 1; cbuf.append("(*"); out.append("  "); i += 2; continue
            elif two == "*)":
                depth -= 1
                out.append("  "); i += 2
                if depth == 0:
                    comments.append((cstart, line, "".join(cbuf)))
                else:
                    cbuf.append("*)")
                continue
            elif c == '"':
                in_cstr = True
            cbuf.append(c)
            out.append("\n" if c == "\n" else " ")
        if c == "\n":
            line += 1
        i += 1
    return "".join(out), comments


def sentences(code):
    """Split comment-free code into sentences: (start_line, end_line, text).
    A sentence ends at a '.' followed by whitespace/EOF (not '..'), outside
    strings."""
    res = []
    i, n = 0, len(code)
    line = 1
    start = None
    start_line = None
    in_str = False
    while i < n:
        c = code[i]
        if start is None and not c.isspace():
            start, start_line = i, line
        if in_str:
            if c == '"':
                in_str = False
        elif c == '"':
            in_str = True
        elif (c == "." and start is not None
              and (i + 1 == n or code[i + 1].isspace())
              and (i == 0 or code[i - 1] != ".")):
            res.append((start_line, line, code[start:i + 1]))
            start = None
        if c == "\n":
            line += 1
        i += 1
    if start is not None and code[start:].strip():
        res.append((start_line, line, code[start:]))
    return res


ATTR_RE = re.compile(r"^(#\[[^\]]*\]\s*|(Local|Global|Polymorphic|Monomorphic|Program|Private|Export)\s+(?=[A-Z]))*")
HEAD_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
NAME_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")
GOAL_HEADS = {"Lemma", "Theorem", "Corollary", "Fact", "Remark", "Proposition", "Property"}
PROOF_START = {"Proof", "Next"}
PROOF_END = {"Qed", "Defined", "Admitted", "Abort", "Save"}


def head_and_name(sent):
    s = ATTR_RE.sub("", sent.strip())
    m = HEAD_RE.match(s)
    if not m:
        return s[:1], ""
    head = m.group(0)
    rest = s[m.end():].lstrip()
    if head == "Module" and rest.startswith("Type"):
        rest = rest[4:].lstrip()
    if head == "Module" and rest.startswith("Import"):
        rest = rest[6:].lstrip()
    if head == "Equations":
        rest = re.sub(r"^\([^)]*\)\s*", "", rest)
    m2 = NAME_RE.match(rest)
    return head, (m2.group(0).rstrip(".") if m2 else "")


class Item:
    __slots__ = ("file", "start", "end", "head", "name", "path", "spec", "proof",
                 "comment", "component", "kind", "tags")

    def __init__(self, file, start, head, name, path, comment):
        self.file, self.start, self.end = file, start, start
        self.head, self.name, self.path = head, name, path
        self.spec = self.proof = 0
        self.comment = comment
        self.component = self.kind = None
        self.tags = []


def parse_file(rel):
    with open(os.path.join(ROOT, rel), encoding="utf-8") as f:
        text = f.read()
    code, comments = strip_comments(text)
    code_lines = code.split("\n")
    comment_by_end = collections.defaultdict(list)
    for (_, e, t) in comments:
        comment_by_end[e].append(t)

    items = []
    stack = []
    cur = None
    in_proof = False
    pending_goal = False
    owner = {}       # line -> item
    proofline = set()
    for (sl, el, s) in sentences(code):
        head, name = head_and_name(s)
        bare = s.strip().lstrip("-+*{} \t\n")
        bhead = HEAD_RE.match(bare).group(0) if HEAD_RE.match(bare) else ""
        is_proof = False
        if in_proof:
            is_proof = True
            if bhead in PROOF_END:
                in_proof = False
        elif head in PROOF_START or pending_goal:
            is_proof = True
            pending_goal = False
            in_proof = not (bhead in PROOF_END or re.search(r"\b(Qed|Defined|Admitted)\.\s*$", s))
        else:
            near = []
            for ln in range(sl - 3, sl + 1):
                near += comment_by_end.get(ln, [])
            cur = Item(rel, sl, head, name, tuple(stack), " ".join(near))
            items.append(cur)
            pending_goal = head in GOAL_HEADS
            # inline proof on the same sentence list? handled by next sentences
            if head in ("Section",) or (head == "Module" and ":=" not in s):
                stack.append(name)
            elif head == "End" and stack and stack[-1] == name:
                stack.pop()
        if cur is None:
            continue
        for ln in range(sl, el + 1):
            if not code_lines[ln - 1].strip():
                continue
            if ln not in owner:
                owner[ln] = cur
            if is_proof:
                proofline.add(ln)
        cur.end = max(cur.end, el)
    for ln, it in owner.items():
        if ln in proofline:
            it.proof += 1
        else:
            it.spec += 1
    return items


# ---------------------------------------------------------------------------
# Classification rules.  Each rule: (file, predicate on item, component).
# First matching rule wins; files listed must be fully covered.

def in_path(*names):
    return lambda it: any(n in it.path or it.name == n for n in names)

def named(rx):
    r = re.compile(rx)
    return lambda it: bool(r.search(it.name))

def both(*ps):
    return lambda it: all(p(it) for p in ps)

ANY = lambda it: True

C_GHOST = "Iris model: ghost state & adequacy parameters"
C_PRED = "Iris instance: predicate interpretation & lemmas"
C_MODEL = "Model: foreign function & ghost lemma contracts"
C_UC = "Universal Contract (LoopVerification)"
C_BV = "Block verifier (Iris soundness)"
C_FK_SPEC = "FemtoKernel: specs & definitions"
C_FK_SPLIT = "FemtoKernel: split/combine lemmas (focusing glue)"
C_FK_BLOCKS = "FemtoKernel: handler block proofs"
C_FK_INIT = "FemtoKernel: init block & trap step"
C_FK_E2E = "FemtoKernel: memory setup & end-to-end"
C_SHARED = "Hooks in shared (unary) files"

F_RES = "Program logic: resources"
F_WPDEF = "Program logic: WP definition"
F_WPRULES = "Program logic: WP structural rules"
F_FOCUS = "Program logic: focusing lemmas"
F_TRIPLES = "Program logic: triples & rules"
F_ADEQ = "Program logic: adequacy"
F_SOUND = "Program logic: contract soundness"

E_TWP = "Total WP"
E_TTRIPLE = "Total triples & contract soundness"

REL_FEMTO = "RelationalVerification"

RELATIONAL_CASE_STUDY = [
    (f"{CS}/IrisModelBinary.v", ANY, C_GHOST),
    (f"{CS}/IrisInstanceBinary.v", in_path("RiscvPmpIrisAdeqParams2"), C_GHOST),
    (f"{CS}/IrisInstanceBinary.v", ANY, C_PRED),
    (f"{CS}/ModelBinary.v", ANY, C_MODEL),
    (f"{CS}/LoopVerificationBinary.v", ANY, C_UC),
    (f"{CS}/BlockVer/BinaryVerifier.v", ANY, C_BV),
    (f"{CS}/FemtoKernel.v", both(in_path(REL_FEMTO),
        lambda it: it.head == "Ltac" or bool(re.search(
            r"_binary_(split|combine)$|_persistent_preds$|^femto_inv_mmio_split$|^sep_sep_swap$", it.name))), C_FK_SPLIT),
    (f"{CS}/FemtoKernel.v", both(in_path(REL_FEMTO), named(r"^femtokernel_handler_.*_safe_rel$")), C_FK_BLOCKS),
    (f"{CS}/FemtoKernel.v", both(in_path(REL_FEMTO),
        named(r"^(femtokernel_init_safe_rel|femtokernel_manualStep2_rel|memAdv_pmpPolicy_binary)$")), C_FK_INIT),
    (f"{CS}/FemtoKernel.v", both(in_path(REL_FEMTO),
        named(r"^(intro_ptstoSthL_binary|mem_has_instrs2|femtokernel_splitMemory_rel|femtokernel_rel_endToEnd)$")), C_FK_E2E),
    (f"{CS}/FemtoKernel.v", in_path(REL_FEMTO), C_FK_SPEC),
]

# Lines added to files shared with the unary development (counted per line).
SHARED_LINE_RULES = [
    (f"{CS}/Sig.v", re.compile(r"\bExec\b|\bLeft\b|\bRight\b|ptsto_one|↦₁|↦₂")),
    (f"{CS}/IrisInstance.v", re.compile(r"ptsto_one")),
]

RELATIONAL_FRAMEWORK = [
    ("theories/Iris/BinaryResources.v", ANY, F_RES),
    ("theories/Iris/BinaryWeakestPre.v", in_path("IrisSignatureRules2"), F_TRIPLES),
    ("theories/Iris/BinaryWeakestPre.v", named(r"^semWP2_(focus|focus_seq|anaglyph)$"), F_FOCUS),
    ("theories/Iris/BinaryWeakestPre.v",
     lambda it: it.head != "Lemma" or it.name in ("Post2", "Wp2", "semWP2"), F_WPDEF),
    ("theories/Iris/BinaryWeakestPre.v", ANY, F_WPRULES),
    ("theories/Iris/BinaryAdequacy.v", ANY, F_ADEQ),
    ("theories/Iris/BinaryInstance.v", ANY, F_SOUND),
]

# Unary total-correctness program logic.  The focusing lemmas rely on it, but
# it is counted separately and NOT as part of the relational effort.
ENABLING = [
    ("theories/Iris/TotalWeakestPre.v", ANY, E_TWP),
    ("theories/Iris/Base.v", in_path("IrisTotalPartialWeakestPre"), E_TWP),
    ("theories/Iris/Instance.v", in_path("TotalTriple"), E_TTRIPLE),
]
ENABLING_PARTIAL_FILES = {"theories/Iris/Base.v", "theories/Iris/Instance.v"}

U_CONTRACTS = "UC: function contracts & symbolic verification"
U_BV_SPEC = "BV: instruction specs & their verification"
U_BV_EXEC = "BV: symbolic/shallow block executor & refinement"
U_FK_CODE = "FK: code, specs & symbolic VCs"
U_FK_AUX = "FK: auxiliary definitions, lemmas & tactics"
U_FK_BLOCKS, U_FK_INIT, U_FK_E2E = "FK: handler blocks", "FK: init & trap", "FK: memory & end-to-end"

UNARY_CASE_STUDY = [
    (f"{CS}/Contracts.v", ANY, U_CONTRACTS),
    (f"{CS}/IrisModel.v", ANY, C_GHOST),
    (f"{CS}/IrisInstance.v", in_path("RiscvPmpIrisAdeqParameters"), C_GHOST),
    (f"{CS}/IrisInstance.v", ANY, C_PRED),
    (f"{CS}/Model.v", ANY, C_MODEL),
    (f"{CS}/LoopVerification.v", ANY, C_UC),
    (f"{CS}/BlockVer/Spec.v", ANY, U_BV_SPEC),
    (f"{CS}/BlockVer/TotalVerifier.v", in_path("Soundness"), C_BV),
    (f"{CS}/BlockVer/TotalVerifier.v", ANY, U_BV_EXEC),
    (f"{CS}/FemtoKernel.v", in_path("FemtoKernel"), U_FK_CODE),
    (f"{CS}/FemtoKernel.v", in_path(REL_FEMTO), None),
    (f"{CS}/FemtoKernel.v", named(r"^femtokernel_handler_.*_safe$"), U_FK_BLOCKS),
    (f"{CS}/FemtoKernel.v", named(r"^(femtokernel_init_safe|femtokernel_manualStep2|memAdv_pmpPolicy)$"), U_FK_INIT),
    (f"{CS}/FemtoKernel.v", named(r"^(femtokernel_splitMemory|femtokernel_endToEnd)$"), U_FK_E2E),
    (f"{CS}/FemtoKernel.v", ANY, U_FK_AUX),
]
UNARY_PARTIAL_FILES = set()

# Generic (non-case-study) Katamaran machinery, unary side.  Only files that
# are built (_CoqProject); theories/Staging is left out as experimental.
G_UTIL = "Gen: libraries & utilities"
G_SYNTAX = "Gen: μSail syntax & program signatures"
G_OPSEM = "Gen: μSail operational semantics"
G_SEP = "Gen: separation logic & shallow Hoare logic"
G_EXEC = "Gen: symbolic & shallow executors"
G_EXSOUND = "Gen: executor soundness"
G_WP = "Gen: WP definition & rules"

def _files(names, comp):
    return [(f"theories/{f}.v", ANY, comp) for f in names.split()]

UNARY_FRAMEWORK = (
    _files("Base Prelude Context Environment Bitvector BitvectorSolve VectorUtils Tactics Notations", G_UTIL)
    + _files("Program Signature Syntax/Assertions Syntax/BinOps Syntax/Chunks Syntax/Expressions "
             "Syntax/Formulas Syntax/FunDecl Syntax/FunDef Syntax/Messages Syntax/Patterns "
             "Syntax/Predicates Syntax/Registers Syntax/Statements Syntax/Terms Syntax/TypeDecl "
             "Syntax/UnOps Syntax/Variables", G_SYNTAX)
    + _files("Semantics Semantics/Registers SmallStep/Step SmallStep/Inversion SmallStep/Progress", G_OPSEM)
    + _files("Sep/Logic Sep/Hoare", G_SEP)
    + _files("MicroSail/SymbolicExecutor MicroSail/ShallowExecutor Symbolic/Worlds Symbolic/Propositions "
             "Symbolic/Solver Symbolic/PartialEvaluation Symbolic/Instantiation Symbolic/OccursCheck "
             "Symbolic/GenOccursCheck Symbolic/Monads Shallow/Monads", G_EXEC)
    + _files("MicroSail/Soundness MicroSail/ShallowSoundness MicroSail/RefineExecutor Refinement/Monads "
             "Symbolic/UnifLogic", G_EXSOUND)
    + [("theories/Iris/Resources.v", ANY, F_RES),
       ("theories/Iris/Base.v", in_path("IrisTotalPartialWeakestPre"), None),
       ("theories/Iris/Base.v", ANY, F_RES),
       ("theories/Iris/WeakestPre.v", ANY, G_WP),
       ("theories/Iris/Instance.v", in_path("TotalTriple"), None),
       ("theories/Iris/Instance.v", in_path("IrisAdequacy"), F_ADEQ),
       ("theories/Iris/Instance.v", in_path("IrisInstanceWithContracts"), F_SOUND),
       ("theories/Iris/Instance.v", ANY, F_TRIPLES)])

# Side-by-side comparison: (group, [(row, unary components, relational components)]).
SIDE_BY_SIDE = [
    ("Katamaran (generic)", [
        ("Libraries & utilities", [G_UTIL], []),
        ("μSail syntax & program signatures", [G_SYNTAX], []),
        ("μSail operational semantics", [G_OPSEM], []),
        ("Separation logic & shallow Hoare logic", [G_SEP], []),
        ("Symbolic & shallow executors", [G_EXEC], []),
        ("Executor soundness (refinement, shallow soundness)", [G_EXSOUND], []),
        ("Iris model: resources", [F_RES], [F_RES]),
        ("Iris model: WP definition & rules", [G_WP], [F_WPDEF, F_WPRULES]),
        ("Iris model: focusing lemmas", [], [F_FOCUS]),
        ("Double vision Hoare triples", [F_TRIPLES], [F_TRIPLES]),
        ("Iris model: adequacy", [F_ADEQ], [F_ADEQ]),
        ("Iris model: contract soundness", [F_SOUND], [F_SOUND]),
        ("Total correctness: total WP", [E_TWP], []),
        ("Total correctness: triples & contract soundness", [E_TTRIPLE], []),
    ]),
    ("Universal Contract", [
        ("Function contracts & symbolic verification (Contracts.v)", [U_CONTRACTS], []),
        ("Iris model & instance: ghost state, predicates", [C_GHOST, C_PRED], [C_GHOST, C_PRED]),
        ("Foreign function & ghost lemma contracts (Model)", [C_MODEL], [C_MODEL]),
        ("Universal Contract (LoopVerification)", [C_UC], [C_UC]),
    ]),
    ("Block verifier", [
        ("Instruction specs & their verification (Spec.v)", [U_BV_SPEC], []),
        ("Symbolic/shallow block executor & refinement", [U_BV_EXEC], []),
        ("Iris soundness", [C_BV], [C_BV]),
    ]),
    ("FemtoKernel", [
        ("Code, block specs & symbolic VCs", [U_FK_CODE], [C_FK_SPEC]),
        ("Auxiliary definitions, lemmas & tactics", [U_FK_AUX], []),
        ("Split/combine lemmas (focusing glue)", [], [C_FK_SPLIT]),
        ("Handler block proofs", [U_FK_BLOCKS], [C_FK_BLOCKS]),
        ("Init block & trap step", [U_FK_INIT], [C_FK_INIT]),
        ("Memory setup & end-to-end", [U_FK_E2E], [C_FK_E2E]),
    ]),
    ("Other", [
        ("Hooks in shared (unary) files", [], [C_SHARED]),
    ]),
]
# Things that look relational but are deliberately not counted.
EXCLUDED = [
    ("theories/Iris/LaterBinaryWp.v", "alternative binary WP; not in _CoqProject and not imported anywhere"),
    (f"{CS}/BlockVer/RunningExample.v", "relational running example; commented out in _CoqProject"),
    ("theories/Staging/BinaryExecutor/ShallowExecutorRel.v", "staging experiment; commented out in _CoqProject"),
]

FOCUS_NAMES = re.compile(r"^(semWP2_focus|semWP2_focus_seq|semWP2_anaglyph|step_n_focus)$")

# ---------------------------------------------------------------------------

K_DEF, K_FOREIGN, K_GHOST, K_LEMMA, K_TAC, K_AX, K_BOIL = (
    "Definitions", "Foreign function proofs", "Ghost lemma proofs",
    "Other lemmas", "Tactics", "Axioms & module parameters", "Boilerplate")
KINDS = [K_DEF, K_FOREIGN, K_GHOST, K_LEMMA, K_TAC, K_AX, K_BOIL]

BOILERPLATE = {"From", "Require", "Import", "Export", "Set", "Unset", "Opaque",
               "Transparent", "Arguments", "Module", "Section", "End", "Include",
               "Context", "Variable", "Variables", "Existing", "Derive", "Hint",
               "Open", "Close", "Implicit", "Generalizable", "Obligation", "Typeclasses",
               "Declare", "Create", "Strategy"}
DEF_HEADS = {"Definition", "Fixpoint", "CoFixpoint", "Example", "Let", "Class", "Record",
             "Structure", "Inductive", "CoInductive", "Variant", "Equations", "Instance",
             "Notation", "Infix", "Canonical", "Coercion", "Function"}


def kind_of(it):
    if it.head in ("Ltac", "Ltac2", "Tactic"):
        return K_TAC
    if it.head in ("Axiom", "Axioms", "Parameter", "Hypothesis", "Conjecture"):
        return K_AX
    if it.head in BOILERPLATE or not it.head[:1].isalpha():
        return K_BOIL
    is_lemma = it.head in GOAL_HEADS or (it.head in DEF_HEADS and it.proof > 0)
    if is_lemma:
        if "ForeignProofs" in it.path and re.search(r"(_sound|^T?foreignSem)$", it.name):
            return K_FOREIGN
        if "LemProofs" in it.path and re.search(r"(_sound|^lemSem)$", it.name):
            return K_GHOST
        return K_LEMMA
    if it.head in DEF_HEADS:
        return K_DEF
    return K_BOIL


def classify(rules, partial_files=()):
    """Apply rules; returns list of classified items (component None = skip)."""
    files = []
    for f, _, _ in rules:
        if f not in files:
            files.append(f)
    out = []
    for f in files:
        frules = [(p, c) for (ff, p, c) in rules if ff == f]
        for it in parse_file(f):
            comp = "__unmatched__"
            for p, c in frules:
                if p(it):
                    comp = c
                    break
            if comp == "__unmatched__":
                if f in partial_files:
                    continue
                raise SystemExit(f"unclassified item {f}:{it.start} {it.head} {it.name}")
            if comp is None:
                continue
            it.component = comp
            it.kind = kind_of(it)
            if FOCUS_NAMES.match(it.name) or comp == C_FK_SPLIT:
                it.tags.append("focusing")
            if re.search(r"duplicate", it.comment, re.I):
                it.tags.append("duplicate-of-unary")
            out.append(it)
    return out


def shared_line_items():
    out = []
    for f, rx in SHARED_LINE_RULES:
        with open(os.path.join(ROOT, f), encoding="utf-8") as fh:
            code, _ = strip_comments(fh.read())
        for ln, line in enumerate(code.split("\n"), 1):
            if line.strip() and rx.search(line):
                it = Item(f, ln, "line", line.strip()[:40], (), "")
                it.spec = 1
                it.component = C_SHARED
                it.kind = K_DEF
                out.append(it)
    return out


# ---------------------------------------------------------------------------
# Reporting

def agg(items, key):
    d = collections.OrderedDict()
    for it in items:
        k = key(it)
        a = d.setdefault(k, {"items": 0, "lemmas": 0, "spec": 0, "proof": 0})
        if it.kind != K_BOIL:
            a["items"] += 1
        if it.kind in (K_FOREIGN, K_GHOST, K_LEMMA):
            a["lemmas"] += 1
        a["spec"] += it.spec
        a["proof"] += it.proof
    return d


def total(d):
    t = {"items": 0, "lemmas": 0, "spec": 0, "proof": 0}
    for v in d.values():
        for k in t:
            t[k] += v[k]
    return t


def table(title, d, order=None, label="Category", note=None):
    rows = []
    keys = order if order else list(d.keys())
    rows.append(f"### {title}\n")
    if note:
        rows.append(note + "\n")
    rows.append(f"| {label} | items | lemmas | spec LOC | proof LOC | total LOC |")
    rows.append("|---|---:|---:|---:|---:|---:|")
    for k in keys:
        if k not in d:
            continue
        v = d[k]
        rows.append(f"| {k} | {v['items']} | {v['lemmas']} | {v['spec']} | {v['proof']} | {v['spec'] + v['proof']} |")
    t = total({k: d[k] for k in keys if k in d})
    rows.append(f"| **Total** | **{t['items']}** | **{t['lemmas']}** | **{t['spec']}** | **{t['proof']}** | **{t['spec'] + t['proof']}** |")
    return "\n".join(rows) + "\n"


def cross(title, items, comps):
    rows = [f"### {title}\n", "Total LOC (spec + proof) per component and kind.\n",
            "| Component | " + " | ".join(KINDS) + " | Total |",
            "|---|" + "---:|" * (len(KINDS) + 1)]
    colt = collections.Counter()
    for c in comps:
        cnt = collections.Counter()
        for it in items:
            if it.component == c:
                cnt[it.kind] += it.spec + it.proof
        if not cnt:
            continue
        colt.update(cnt)
        rows.append(f"| {c} | " + " | ".join(str(cnt[k]) for k in KINDS) + f" | {sum(cnt.values())} |")
    rows.append("| **Total** | " + " | ".join(f"**{colt[k]}**" for k in KINDS) + f" | **{sum(colt.values())}** |")
    return "\n".join(rows) + "\n"


def ordered(rules, extra=()):
    seen = []
    for _, _, c in rules:
        if c and c not in seen:
            seen.append(c)
    return seen + [e for e in extra if e not in seen]


def git_stats(files):
    rows = ["### Git history of the relational files\n",
            "| File | commits | first commit | last commit | authors |", "|---|---:|---|---|---|"]
    for f in files:
        try:
            log = subprocess.run(["git", "-C", ROOT, "log", "--format=%ad|%an",
                                  "--date=short", "--", f], capture_output=True, text=True, check=True).stdout
        except (OSError, subprocess.CalledProcessError):
            return ""
        entries = [l.split("|", 1) for l in log.splitlines() if l]
        if not entries:
            continue
        authors = collections.Counter(a for _, a in entries)
        rows.append(f"| {f} | {len(entries)} | {entries[-1][0]} | {entries[0][0]} | "
                    + ", ".join(f"{a} ({n})" for a, n in authors.most_common()) + " |")
    return "\n".join(rows) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--items", help="write per-item classification to this CSV file")
    ap.add_argument("--json", help="write aggregated numbers to this JSON file")
    args = ap.parse_args()

    rel_cs = classify(RELATIONAL_CASE_STUDY, {f"{CS}/FemtoKernel.v"}) + shared_line_items()
    rel_fw = classify(RELATIONAL_FRAMEWORK)
    enab = classify(ENABLING, ENABLING_PARTIAL_FILES)
    un_cs = classify(UNARY_CASE_STUDY, UNARY_PARTIAL_FILES)
    un_fw = classify(UNARY_FRAMEWORK)

    cs_order = ordered(RELATIONAL_CASE_STUDY, [C_SHARED])
    fw_order = ordered(RELATIONAL_FRAMEWORK)
    out = []
    head = subprocess.run(["git", "-C", ROOT, "rev-parse", "--short", "HEAD"],
                          capture_output=True, text=True).stdout.strip()
    out.append(f"# Relational extension of the RISC-V PMP case study: effort\n\n"
               f"Generated by `scripts/relational_effort.py` at commit `{head or '?'}`. "
               "LOC = non-blank, non-comment lines; a line is a proof line if it lies between "
               "`Proof`/`Next Obligation` and `Qed`/`Defined`/`Admitted`. "
               "\"items\" counts non-boilerplate vernacular commands; \"lemmas\" counts proved statements.\n")

    out.append("## A. Case-study specific relational work\n")
    out.append(table("A1. By kind of work", agg(rel_cs, lambda i: i.kind), KINDS, "Kind"))
    out.append(table("A2. By component", agg(rel_cs, lambda i: i.component), cs_order, "Component"))
    out.append(cross("A3. Component × kind", rel_cs, cs_order))

    out.append("## B. Generic relational program logic (theories/Iris/Binary*.v)\n")
    out.append(table("B1. By kind of work", agg(rel_fw, lambda i: i.kind), KINDS, "Kind"))
    out.append(table("B2. By component", agg(rel_fw, lambda i: i.component), fw_order, "Component"))

    out.append("## C. Total-correctness program logic (separate; not counted as relational)\n")
    out.append(table("C1. Total-correctness WP and triples", agg(enab, lambda i: i.component),
                     ordered(ENABLING), "Component",
                     note="Unary total-correctness program logic. The focusing lemmas use it, but it is "
                          "reported separately and is not included in the relational totals in E."))

    focus = [i for i in rel_cs + rel_fw if "focusing" in i.tags]
    dup = [i for i in rel_cs + rel_fw if "duplicate-of-unary" in i.tags]
    out.append("## D. Cross-cutting views\n")
    out.append(table("D1. Focusing (generic lemmas + block-level lemma + FemtoKernel split/combine glue)",
                     agg(focus, lambda i: i.component), cs_order + fw_order, "Component"))
    out.append(table("D2. Items marked as duplicates of unary lemmas (subset of A)",
                     agg(dup, lambda i: f"{i.name} ({os.path.basename(i.file)})"), None, "Item"))

    out.append("## E. Aggregate\n")
    a, b, c = total(agg(rel_cs, lambda i: 0)), total(agg(rel_fw, lambda i: 0)), total(agg(enab, lambda i: 0))
    nb = lambda items: sum(i.spec + i.proof for i in items if i.kind != K_BOIL)
    rows = ["| Part | spec LOC | proof LOC | total LOC | total excl. boilerplate |", "|---|---:|---:|---:|---:|"]
    for name, t, its in [("A. Case-study relational work", a, rel_cs),
                         ("B. Generic relational program logic", b, rel_fw)]:
        rows.append(f"| {name} | {t['spec']} | {t['proof']} | {t['spec'] + t['proof']} | {nb(its)} |")
    s = {k: a[k] + b[k] for k in a}
    rows.append(f"| **Relational total (A + B)** | **{s['spec']}** | **{s['proof']}** | **{s['spec'] + s['proof']}** | "
                f"**{nb(rel_cs) + nb(rel_fw)}** |")
    rows.append(f"| *Separately: C. Total-correctness program logic* | *{c['spec']}* | *{c['proof']}* | "
                f"*{c['spec'] + c['proof']}* | *{nb(enab)}* |")
    out.append("\n".join(rows) + "\n")

    out.append("## F. Relational vs. pre-existing unary work\n")
    ucs = agg(un_cs + un_fw + enab, lambda i: i.component)
    rcs = agg(rel_cs + rel_fw, lambda i: i.component)
    zero = {"items": 0, "lemmas": 0, "spec": 0, "proof": 0}
    pick = lambda d, ks: total({k: d.get(k, zero) for k in ks})
    fmt = lambda t: (f"{t['spec']} | {t['proof']} | {t['spec'] + t['proof']}"
                     if t["spec"] + t["proof"] else "– | – | –")
    ratio = lambda r, u: f"{(r['spec'] + r['proof']) / (u['spec'] + u['proof']):.2f}" \
        if (u["spec"] + u["proof"]) and (r["spec"] + r["proof"]) else "–"
    rows = ["Unary rows with no relational counterpart are reused as-is by the relational proofs. "
            "The unary Iris model/instance and Model also serve the block verifier and FemtoKernel. "
            "Generic rows cover the built files under theories/ (excluding theories/Staging). "
            "The total-correctness program logic is unary work that the focusing lemmas rely on.\n",
            "| Component | Part | unary spec | unary proof | unary total | rel. spec | rel. proof | rel. total | rel./unary |",
            "|---|---|---:|---:|---:|---:|---:|---:|---:|"]
    gu, gr = [], []
    for group, parts in SIDE_BY_SIDE:
        su, sr = [], []
        for name, uk, rk in parts:
            u, r = pick(ucs, uk), pick(rcs, rk)
            su.append(u); sr.append(r)
            rows.append(f"| {group} | {name} | {fmt(u)} | {fmt(r)} | {ratio(r, u)} |")
        u, r = total(dict(enumerate(su))), total(dict(enumerate(sr)))
        gu.append(u); gr.append(r)
        rows.append(f"| **{group}** | **subtotal** | **{u['spec']}** | **{u['proof']}** | **{u['spec'] + u['proof']}** | "
                    f"**{r['spec']}** | **{r['proof']}** | **{r['spec'] + r['proof']}** | **{ratio(r, u)}** |")
    u, r = total(dict(enumerate(gu))), total(dict(enumerate(gr)))
    rows.append(f"| **Total** | | **{u['spec']}** | **{u['proof']}** | **{u['spec'] + u['proof']}** | "
                f"**{r['spec']}** | **{r['proof']}** | **{r['spec'] + r['proof']}** | **{ratio(r, u)}** |")
    out.append("\n".join(rows) + "\n")
    assert r["spec"] + r["proof"] == a["spec"] + a["proof"] + b["spec"] + b["proof"], \
        "side-by-side table misses relational components"
    assert u["spec"] + u["proof"] == sum(v["spec"] + v["proof"] for v in ucs.values()), "side-by-side misses unary"
    ufw = agg(un_fw, lambda i: i.component)

    out.append("## G. Excluded from the counts\n")
    rows = ["| File | LOC | reason |", "|---|---:|---|"]
    for f, why in EXCLUDED:
        if os.path.exists(os.path.join(ROOT, f)):
            t = sum(i.spec + i.proof for i in parse_file(f))
            rows.append(f"| {f} | {t} | {why} |")
    out.append("\n".join(rows) + "\n")

    # No --follow: the *Binary.v files started as copies of their unary counterparts.
    out.append(git_stats(list(dict.fromkeys(
        [f for f, _, _ in RELATIONAL_CASE_STUDY if "Binary" in f]
        + [f for f, _, _ in RELATIONAL_FRAMEWORK]))))

    sys.stdout.write("\n".join(out))

    if args.items:
        with open(args.items, "w", newline="", encoding="utf-8") as fh:
            w = csv.writer(fh)
            w.writerow(["part", "file", "start", "end", "head", "name", "component", "kind",
                        "spec", "proof", "tags"])
            for part, its in [("A", rel_cs), ("B", rel_fw), ("C", enab), ("unary-cs", un_cs), ("unary-fw", un_fw)]:
                for i in its:
                    w.writerow([part, i.file, i.start, i.end, i.head, i.name, i.component, i.kind,
                                i.spec, i.proof, ";".join(i.tags)])
    if args.json:
        res = {"A_by_kind": agg(rel_cs, lambda i: i.kind), "A_by_component": rcs,
               "B_by_kind": agg(rel_fw, lambda i: i.kind),
               "B_by_component": agg(rel_fw, lambda i: i.component),
               "C_by_component": agg(enab, lambda i: i.component),
               "unary_case_study": ucs, "unary_framework": ufw,
               "totals": {"A": a, "B": b, "C": c}}
        with open(args.json, "w", encoding="utf-8") as fh:
            json.dump(res, fh, indent=2)


if __name__ == "__main__":
    main()
