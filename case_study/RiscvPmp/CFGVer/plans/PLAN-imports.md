# PLAN — import, don't qualify (TODO I6, 2026-10-15)

Status: **DONE 2026-10-15** on `issue/imports` (not merged): `make -j1
Results.vo` green (50m37s), hole scan 0, zero `Katamaran.RiscvPmp.CFGVer.<File>.`
left in CFGVer. Branch `issue/imports`, off
`KatamaranRel` once `issue/loop-rule` is merged.

## 0. Goal (Emiel's words)

"for readibility, we should avoid using things like this an instead import
them properly. This holds for the whole codebase actually." — and: "import the
same way as whatever was used before Claude started helping or whatever
pattern is used on main."

Done means (Emiel, 2026-10-15):
1. no non-ZZ `.v` file in CFGVer writes a `Katamaran.RiscvPmp.CFGVer.<File>.`
   prefix in code;
2. the `CFGVer/CLAUDE.md` note "Importing CFGVer.Verifier downstream" and
   any skill copies of it are deleted;
3. `Results.vo` builds.

## 1. Vocabulary

- **qualified use** — a name written with its full path,
  `Katamaran.RiscvPmp.CFGVer.Verifier.cfg_precondition`.
- **short name** — the same name written bare, `cfg_precondition`.
- **shadowing** — two definitions with the same short name both in scope,
  so the short name may resolve to the wrong one.

## 2. The pattern on `main` (what we copy)

Read off `main:case_study/RiscvPmp/BlockVer/*.v` and `case_study/MinimalCaps/`:

1. ONE `From Katamaran Require Import …` block at the top, listing the
   sibling files the file uses (`RiscvPmp.BlockVer.Spec`,
   `RiscvPmp.BlockVer.PartialVerifier`, …).
2. Top-level `Import <instance>.` lines for the module instances the file
   works inside (`Import RiscvPmpProgram.`, `Import RiscvPmpBlockVerifExecutor.`).
3. Notation modules imported LOCALLY, inside the `Section`/`Module` that needs
   them (`Section WithAsnNotations. Import asn.notations.`).
4. A bare `Require` (no `Import`) only for a module used for a handful of
   names (`From Katamaran Require RiscvPmp.ModelBinary.`).

`main` has zero fully qualified `Katamaran.X.Y.name` uses, and so does
`theories/` on this branch (surveyed 2026-10-15). Fallback where an `Import`
genuinely clashes: a SHORT partial path (`Contracts.loop_post`), which Coq
resolves when the suffix is unique.

## 3. Census (2026-10-15, lines with a qualified use, non-ZZ)

| File | Lines | Qualifies |
|---|---|---|
| `Adequacy.v` | 176 | Verifier 119, VerifierRel 79, Tables 13, Contracts 9 |
| `SpecIris.v` | 51 | Verifier |
| `GenCompose.v` | 22 | VerifierRel 20, Verifier 2 |
| `VerifierRel.v` | 12 | Verifier |
| `EndToEnd.v` | 10 | VerifierRel |
| `Example/TwoLoopsComposedResult.v` | 8 | VerifierRel |
| `TablesRel.v` | 6 | VerifierRel 5, Verifier 1 |
| `Example/{Swap,Countdown}ComposedResult.v` | 4 each | VerifierRel |
| `Contracts.v` | 2 | Verifier |

Total 295 lines. Comments that name `Verifier.is_head` and the like are
navigation, not code, and stay.

Why the prefixes exist: `CFGVer/CLAUDE.md` says to qualify `Verifier` names
to avoid a clash with BlockVer. BlockVer is out of the build (`_CoqProject`,
zero active BlockVer lines), and the note itself says to switch to
`Require Import` once BlockVer is gone.

## 4. Risks

- **R1 Shadowing.** A name may be qualified because a same-named definition
  is also in scope; stripping the prefix could then resolve to the other one.
  Usually a type error, but not guaranteed. Mitigation: before stripping a
  file, list every qualified identifier and grep CFGVer + `theories/` for a
  second definition with that short name; strip only the unique ones by
  script, handle collisions by hand and list them in §6.
- **R2 Notation clashes.** `Adequacy.v` requires `Contracts` bare ("only
  cfg_postprocess"), and `Contracts` defines assertion notations (`↦ᵣ`,
  `↦ₘ`) that `Adequacy.v` also uses as Iris notations. Importing it may
  break parsing. Mitigation: pattern rule 4 — keep the bare `Require` and
  use the short path `Contracts.x` there.
- **R3 Cost.** Every file from `SpecIris.v` on is rebuilt; `Adequacy.v`
  takes ~5 min. Build per phase with `make -j1`, no gate until Phase 5.

## 5. Phases (dependency order, one commit each)

1. `Contracts.v` (light; already imports `Verifier`): strip the 2.
2. `SpecIris.v`, `VerifierRel.v`, `TablesRel.v`: add `Verifier` /
   `VerifierRel` to the import block where missing, strip; build
   `TablesRel.vo`.
3. `Adequacy.v`: import `Verifier`, `VerifierRel`, `Tables`; R2 for
   `Contracts`; strip; build `Adequacy.vo`.
4. `GenCompose.v`, `EndToEnd.v`, the three `*ComposedResult.v`: strip;
   build.
5. Docs + check: delete the CLAUDE.md note and skill copies (grep
   "qualified names"); then `make -j1 Results.vo`, the hole scan, and a
   `grep` showing zero `Katamaran.RiscvPmp.CFGVer.<File>.` in non-ZZ code.
   Trusted surface: the Result statements are not touched (stmtdiff).

## 6. Decisions taken during implementation

- **R1 resolved by census, no hand cases.** Every qualified short name is
  defined once in the build. The only second definitions found
  (`cexec_triple_addr`, `ptsto_instrs`, `sound_exec_instruction`) are in
  `BinaryBlockVer/Verifier.v`, which is out of `_CoqProject` and required
  by no CFGVer file. Record fields and constructors (`blk_contract`,
  `cfg_exit`, `clem_arr_*`, ...) exist only in CFGVer.
- **Phases 1-4 done in one scripted pass** (348 occurrences, 10 files),
  since all but two files already `Require Import` what they qualified.
  Exceptions: `SpecIris.v` switched its bare `Require` of `Verifier` to
  `Require Import`; `Adequacy.v` keeps `Contracts` bare (R2) and writes
  `Contracts.x`.
- Edited in the worktree `../katamaran-imports` while `issue/loop-rule`'s
  Results build ran; compiled only afterwards (RAM).
- Removed doc text archived verbatim: `.claude/archive/imports-2026-10-15.md`.
