---
name: branch-workflow
description: >
  The branch + merge-gate workflow for this repo: work each issue on a short-lived
  topic branch, then merge into a protected branch (main / KatamaranRel) through the
  scripts/gate.sh merge gate, which is wired as the pre-merge-commit git hook. Use
  when the user asks how to start a new piece of work, how to merge/land a branch,
  what the merge gate checks, why a merge was blocked, how to run the gate manually,
  how to (re)install the hook after a clone, or how to add a new end theorem to the
  axiom-clean list. The gate enforces the three things a green `coqc` does NOT: full
  build, no proof holes, and axiom-clean end theorems. NOT for the semantics of a
  single proof (use the cfgver-* / rocq skills) and NOT for committing at milestones
  on a branch (that is rocq-checkpoint).
---

# Branch + merge-gate workflow

The invariant: **mainline (`main` / `KatamaranRel`) is always full-compiling,
hole-free, and axiom-clean.** You thrash freely on a topic branch; only a clean
state is allowed to become the baseline. A green `coqc` guarantees proof *validity*
but not statement non-vacuity or axiom hygiene — the gate covers exactly that gap.

## One-time setup (and after every fresh clone)

`.git/hooks` is not tracked by git, so the hook does not travel with the repo:

```bash
./scripts/install-hooks.sh
```

This installs `.git/hooks/pre-merge-commit`, a thin wrapper that runs
`scripts/gate.sh` **only when the current branch is protected**
(`main` / `KatamaranRel`). Merges into feature branches are not gated, so they
stay fast.

## Per-issue loop

```bash
git switch -c issue/<short-name>     # branch off the protected branch
# … work: edit, prove, commit WIP freely (rocq-checkpoint is fine here) …
git switch KatamaranRel
git merge --no-ff issue/<short-name> # --no-ff forces a merge commit → hook fires
```

**`--no-ff` is required.** A fast-forward merge creates no commit, so
`pre-merge-commit` does not run and the gate is silently skipped. Always merge with
`--no-ff` into a protected branch.

The hook runs the gate against the *merged* working tree. If it exits non-zero the
merge commit is aborted (the merge stays staged-but-uncommitted); recover with
`git merge --abort`, fix on the topic branch, and merge again.

## What the gate checks (`scripts/gate.sh`)

1. **Build (target closure)** — regenerates `Makefile.coq`, then
   `make -f Makefile.coq` on `BUILD_TARGETS` (default
   `case_study/RiscvPmp/CFGVer/Results.vo`). This compiles the end theorems and
   its full transitive dependency closure — proof bodies, not `.vos` — while
   skipping unrelated files active in `_CoqProject` (e.g. `theories/Staging/`).
2. **Proof holes** — greps `SCOPE_DIRS` (default `case_study/RiscvPmp/CFGVer`) for
   `Admitted.` / `Axiom` / `Conjecture` / `Parameter`, ignoring single-line
   `(* … *)` comments.
3. **Axiom hygiene** — compiles a throwaway probe that runs `Print Assumptions` on
   each theorem in `AXIOM_CLEAN_THMS`; fails if any assumption appears beyond the
   `ALLOWED_AXIOMS` whitelist (`Machine.pure_decode`, `Base.mmioenv` — the two
   standard axioms every end theorem legitimately carries). Admitted lemmas and
   stray axioms show up in `Print Assumptions`, so this is the authoritative
   hole+axiom check (it follows the full dependency graph); step 2 is just a
   fast pre-filter.

Run it by hand any time (e.g. before merging, or to check a work-in-progress):

```bash
./scripts/gate.sh
COQC=rocq ./scripts/gate.sh    # override the compiler binary if needed
```

## Maintaining the gate

- **New end theorem** → add its `Examples.`-qualified name to `AXIOM_CLEAN_THMS`
  in `scripts/gate.sh` (names are qualified by the inner `Module Examples`).
  Establish the baseline by running the gate once; if a theorem legitimately
  depends on an axiom, drop it from the list with a note rather than weakening the
  closed-under-global-context check.
- **New build target / scope dir** → edit `BUILD_TARGETS` (the `.vo` closures to
  compile) and `SCOPE_DIRS` (the hole-scan dirs) in `gate.sh`.
- **New protected branch** → edit `PROTECTED` in the hook wrapper and regenerate
  via `install-hooks.sh`.

## Escape hatch

`git merge --no-verify --no-ff …` skips the hook. Use only for a deliberate,
known-clean administrative merge — bypassing defeats the whole invariant.
