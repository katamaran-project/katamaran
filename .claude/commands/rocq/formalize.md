---
name: formalize
description: Interactive formalization — drafting plus guided proving
user_invocable: true
---

# Rocq Formalize

Interactive formalization: draft Rocq skeletons from informal claims, then prove them with guided cycles. Combines `/rocq:draft` and `/rocq:prove` in a single human-in-the-loop workflow.

## Usage

```
/rocq:formalize "Every continuous function on a compact set is bounded"
/rocq:formalize --rigor=axiomatic "Zorn's lemma implies AC"
/rocq:formalize --source ./paper.pdf          # Ingest, pick claims, formalize
/rocq:formalize --output=file --out=MyTheorem.v "..."
```

## Inputs

| Arg | Required | Default | Description |
|-----|----------|---------|-------------|
| topic | no | — | Informal claim to formalize. At least one of `topic` or `--source` must be given. |
| --rigor | no | `checked` | `checked` \| `sketch` \| `axiomatic` |
| --verify | no | `best-effort` | `best-effort` \| `strict`. Verification strictness. |
| --level | no | `intermediate` | `beginner` \| `intermediate` \| `expert` |
| --output | no | `chat` | `chat` \| `scratch` \| `file` |
| --out | no | — | Output path. Required when `--output=file`. |
| --overwrite | no | `false` | Allow overwriting existing files. |
| --source | no | — | File path, URL, or PDF to seed formalization. |
| --claim-select | no | — | `first` \| `named:"..."` \| `regex:"..."`. |
| --draft-mode | no | `attempt` | `skeleton` \| `attempt`. Mode for the draft phase. |
| --deep | no | never | `never` \| `ask` \| `stuck` \| `always`. |
| --commit | no | ask | `ask` \| `auto` \| `never` |
| --golf | no | prompt | `prompt` \| `auto` \| `never` |

## Actions

### Phase 1: Draft

Invoke draft logic (same algorithm as `/rocq:draft`):

1. **Claim Acquisition** — parse topic or ingest `--source`.
2. **Draft Theorem Skeleton** — translate claim to `Admitted`-stubbed Rocq declaration.
3. **Compilation Check** — `rocq_compile` on skeleton.
4. **Proof Attempt** (when `--draft-mode=attempt`, default) — `rocq_start` + `rocq_step_multi` loop.

### Phase 2: Prove

Invoke prove logic (same algorithm as `/rocq:prove`):

1. Run guided prove cycle on the drafted declaration.
2. Rigor checks per `--rigor`.
3. User confirms or adjusts between cycles.

**Rigor completion criteria:**

| Rigor | Admitted | Diagnostics | Non-standard axiom | Silent global axiom |
|-------|---------|-------------|-------------------|-------------------|
| `checked` | **FAIL** | **FAIL** | **FAIL** | **FAIL** |
| `axiomatic` | **FAIL** | **FAIL** | allowed if in ledger | **FAIL** |
| `sketch` | allowed | allowed | allowed | **FAIL** |

### Phase 3: Statement Mismatch Handling

If the prove phase concludes the statement is wrong (`next_action = redraft`), present to user:

1. **Redraft** — return to Phase 1 with revised claim
2. **Salvage sibling** — create weaker statement variant
3. **Preserve + stop** — keep current statement, mark Admitted, stop
4. **Continue** — keep trying with current statement

**Permission boundary:** Formalize owns the right to change declaration headers. The prove phase itself cannot.

### Phase 4: Depth Check

Offer the depth-check menu: show source / show proof state / alternative formalization / generalize / strengthen / save to scratch / write to file.

## Output

Output format follows `--presentation`: `informal` → prose with math notation; `supporting` → prose with selective Rocq snippets; `formal` → Rocq code blocks as primary content.

### Standard Axiom Whitelist

`classic`, `functional_extensionality`, `propositional_extensionality`, `proof_irrelevance` — not flagged. All others reported as non-standard.

Always run `bash "$ROCQ_SCRIPTS/check_axioms.sh" <target> --report-only` or `rocq_query("Print Assumptions ...")` before presenting final results.

## Safety

- **Read-only in chat mode.** Does not write files unless `--output` requests it.
- **No commits in standalone mode.**
- **Never add global axioms silently.** Assumptions go as explicit theorem parameters.
- **All `guardrails.sh` rules apply.**
- **Line width.** Follow Rocq 80-char line width convention.

## See Also

- `/rocq:draft` — skeleton-only drafting (no prove phase)
- `/rocq:autoformalize` — autonomous synthesis (unattended)
