---
name: draft
description: Draft Rocq declaration skeletons from informal claims
user_invocable: true
---

# Rocq Draft

Draft Rocq declaration skeletons from informal mathematical claims. Produces `Admitted`-stubbed statements ready for `/rocq:prove` or `/rocq:autoprove`.

## Usage

```
/rocq:draft "Every continuous function on a compact set is bounded"
/rocq:draft --mode=attempt "Zorn's lemma implies AC"
/rocq:draft --source ./paper.pdf          # Ingest, pick claims, draft skeletons
/rocq:draft --source ./paper.pdf "Theorem 3.2"  # Source as context, topic as claim
/rocq:draft --output=file --out=MyTheorem.v "..."
```

## Inputs

| Arg | Required | Default | Description |
|-----|----------|---------|-------------|
| topic | no | — | Informal claim to draft. Optional when `--source` provides it (source-led flow). At least one of `topic` or `--source` must be given; omitting both is a hard error. |
| --mode | no | `skeleton` | `skeleton` \| `attempt`. `skeleton` produces `Admitted`-stubbed declarations only. `attempt` adds a proof-attempt loop (`rocq_step_multi`) before finalizing. |
| --elab-check | no | `best-effort` | `best-effort` \| `strict`. Compilation check strictness for drafted skeletons. |
| --level | no | `intermediate` | `beginner` \| `intermediate` \| `expert` |
| --output | no | `chat` | `chat` \| `scratch` \| `file` |
| --out | no | — | Output path. Required when `--output=file`; hard error if missing. |
| --overwrite | no | `false` | Allow overwriting existing files with `--output=file`. Without flag, existing target → hard error. |
| --source | no | — | File path, URL, or PDF to seed drafting. |
| --claim-select | no | — | `first` \| `named:"..."` \| `regex:"..."`. Noninteractive claim selection from `--source`. |

### Output validation

- `--output=file` without `--out` → hard error
- `--output=scratch` → `.scratch/rocq/draft-<timestamp>.v` (workspace-local). Auto-create `.scratch/rocq/` if missing; warn if `.scratch/` is not in `.gitignore`.
- `--output=file` with existing target and no `--overwrite` → hard error

### Noninteractive Claim Selection

| Policy | Behavior |
|--------|----------|
| `first` | Select the first extractable claim from `--source` |
| `named:"..."` | Match claims by title/label substring (e.g. `named:"Theorem 3.2"`) |
| `regex:"..."` | Match claims by regex on extracted claim text |

## Actions

### 1. Claim Acquisition

Two entry points:

- **Direct:** `topic` given → parse the informal claim directly.
- **Source-led:** `--source` given, no `topic` → ingest source (`.v` → `Read`; PDF → `Read`; `.md`/`.txt` → `Read`; URL → web fetch; other → warn + ask for excerpt). Extract candidate claims. If `--claim-select` is present, select noninteractively per policy; otherwise present to user, user picks which to draft.
- **Both:** `topic` and `--source` given → use topic as the claim and source as supporting context.

### 2. Draft Theorem Skeleton

Parse natural-language claim → draft theorem skeleton with appropriate types, hypotheses, and conclusion. Use standard library naming conventions and types where possible (`rocq_query("Search ...")`, `rocq_query("Check ...")` to find canonical types).

```coq
Theorem continuous_bounded :
  forall (f : R -> R) (S : R -> Prop),
    compact S -> continuous_on f S -> bounded (image f S).
Proof.
Admitted.
```

### 3. Compilation Check

Run `rocq_compile` on the drafted skeleton. Under `--elab-check=strict`, all diagnostics must be clean (excluding the expected `Admitted`). Under `--elab-check=best-effort`, attempt to fix diagnostics but continue if unfixable.

### 4. Proof Attempt (--mode=attempt only)

When `--mode=attempt`: `rocq_start` + `rocq_step_multi` loop. Search library for existing proofs or applicable lemmas before writing tactics from scratch. If proof succeeds, include it. If proof fails, leave `Admitted` and note the attempt.

### 5. Depth Check

Offer the depth-check menu:

- show source / show proof state
- alternative formalization (e.g., different types or encoding)
- save to scratch / write to file

## Output

Output format follows `--presentation`: `informal` → prose with math notation; `supporting` → prose with selective Rocq snippets; `formal` → Rocq code blocks as primary content. In `scratch` or `file` mode, additionally write a `.v` file regardless of presentation.

## Safety

- **Read-only in chat mode.** Does not write files unless `--output` requests it.
- **No silent mutations.** Prefer MCP tools (`rocq_start`) over file writes for compilation checks.
- **No commits.** `/draft` never commits. `--output=file` writes but does not stage or commit.
- **Path restriction.** User-requested outputs restricted to workspace root (scratch uses `.scratch/rocq/`). Reject path traversal (`../`) or absolute paths outside workspace.
- **Overwrite protection.** `--output=file` with existing target requires `--overwrite`; otherwise hard error.
- **All `guardrails.sh` rules apply.**
- **Line width.** Follow Rocq 80-char line width convention.

## See Also

- `/rocq:formalize` — interactive synthesis (draft + prove)
- `/rocq:autoformalize` — autonomous synthesis (draft + autoprove)
