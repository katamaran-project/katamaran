---
name: learn
description: Interactive teaching and library exploration
user_invocable: true
---

# Rocq Learn

Interactive teaching and library exploration. Adapts to beginner, intermediate, and expert audiences.

## Usage

```
/rocq:learn                                 # Start conversational discovery
/rocq:learn Nat.add_comm                    # Auto-detect mode from topic
/rocq:learn --mode=repo                     # Explore current project
/rocq:learn --mode=library nat              # Navigate stdlib/MathComp for a topic
/rocq:learn --style=socratic --interactive  # True Socratic method
/rocq:learn --source ./paper.pdf            # Learn from a paper/PDF
/rocq:learn --output=scratch                # Write results to scratch file
```

## Inputs

| Arg | Required | Default | Description |
|-----|----------|---------|-------------|
| topic | no | — | Free-text topic, theorem name, file path, or natural-language claim |
| --mode | no | `auto` | `auto` \| `repo` \| `library` |
| --level | no | `intermediate` | `beginner` \| `intermediate` \| `expert` |
| --scope | no | `auto` | `auto` \| `file` \| `changed` \| `project` \| `topic` |
| --style | no | `tour` | `tour` \| `socratic` \| `exercise` \| `game` |
| --output | no | `chat` | `chat` \| `scratch` \| `file` |
| --out | no | — | Output path. Required when `--output=file`. |
| --interactive | no | `false` | True Socratic method (withhold answers). Valid only with `--style=socratic`. |
| --source | no | — | File path, URL, or PDF to seed learning. |

## Actions

### 1. Mode Resolution

When `--mode=auto`, resolve by tie-breaking order:

1. If topic resolves to an existing `.v` file path → `repo`
2. Resolve topic against project-local declarations (via `Grep`/`rocq_toc`) → `repo`
3. Check library names via `rocq_query("Search ...")`, `rocq_query("About ...")` → `library`
4. If topic is a natural-language mathematical statement → suggest `/rocq:formalize`
5. If ambiguous → ask the user

### 2. Discovery (per mode)

**repo:** `Glob`/`Grep` (file survey) → `Read` (targeted content) → `rocq_toc(file)` (structure). Build a map: key files, declarations, dependency flow, where proofs live.

**library:** `rocq_query("Search ...")` → `rocq_query("Check ...")` → `rocq_query("Print ...")`. Present canonical lemmas, type signatures, minimal usage examples.

### 3. Explanation

Present findings at the user's `--level` in the user's `--style`:

- **tour:** Narrated walkthrough, explains as it goes.
- **socratic:** Guided discovery with prompts. If `--interactive`, withhold answers first.
- **exercise:** Present a challenge, let user attempt, then explain. Always end with a Rocq-verified reference solution.
- **game:** Structured progression. Verification via `rocq_start` + `rocq_step_multi` + `rocq_compile`.

### 4. Depth Check

Offer the depth-check menu:

- show source / show proof state / show alternative approach
- go deeper / switch mode / broaden scope
- **draft a skeleton** → suggest `/rocq:draft`
- **formalize a specific result** → suggest `/rocq:formalize`
- **save to scratch** / **write to file**

### 5. Iterate

Return to step 4 for the next turn. Continue until the user is satisfied or switches mode.

## Output

Output format follows `--presentation`: `informal` → prose with math notation; `supporting` → prose with selective Rocq snippets; `formal` → Rocq code blocks as primary content.

## Safety

- **Read-only by default.** Never writes files unless `--output` requests it.
- **No commits.** `/learn` never commits.
- **Path restriction.** Outputs restricted to workspace root.
- **Overwrite protection.** `--output=file` with existing target requires `--overwrite`.
- **All `guardrails.sh` rules apply.**

## See Also

- `/rocq:draft` — Draft skeletons from informal claims
- `/rocq:formalize` — Interactive formalization
