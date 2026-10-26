# arrv loop cost drivers (2026-10-26)

**Finding.** `arrv`'s extra cost on a loop is caused by ANGELIC AMBIGUITY
between arrays of the same shape (`arrv w s` has no index to tell them apart,
where `arr` had `pub`): ×2.27 by itself, and it is ALSO the whole reason the
arrays' values cost anything (×1.63 more) — the value variables' defining
equations sit inside the angelic choice, so `solve_evars` cannot instantiate
them and they survive as existentials for the closer. With unambiguous arrays
values are free (×1.00). Warm, LoopN costs ≈3.7× `arr`, not the 2.4–2.8×
recorded before (see §4).

## 1. Axes and variants

Axes: **ambiguity** (two same-shape arrays share a predicate: no | yes),
**values** (array carries a named value list: no | yes), and a nuisance axis
**warm-up** (first heavy VC in a coqc process: cold | warm).

| name | ambiguity | values | what it is | file |
|---|---|---|---|---|
| `unamb+novals` (Old) | no | no | LoopN on `arr`, m `pub=true`, x `pub=false` | `Example/Rsa/ZZArrvAmbig.v`, `ZZArrvSplit.v` |
| `amb+novals` (Amb) | yes | no | Old with m's two arrays flipped to `pub=false` (4 tokens) | same |
| `amb+vals` (NV) | yes | yes | LoopN on `arrv`, values ∃ (VM equation off) | `ZZArrvCost.v` (`NV`), `ZZArrvSplit.v` |
| `amb+vals+tracked` | yes | yes | shipped LoopN, `VM = rev dM ++ rM` | `Example/Rsa/RsaSpikeSub.v` |
| Loop1 old/new | no (strides 1, −1) | no / yes | check_scalar loop 1, `arr` vs `arrv` | `Example/CheckScalar/ZZArrvInteract.v` |
| Loop2 old/new | yes (both `1 1`) | no / yes | check_scalar loop 2, `arr` vs `arrv` | same |

Old → Amb moves ONLY ambiguity (Amb verifies: the loop never branches on m).
Amb → NV moves ONLY values (both ambiguous). Loop1/Loop2 move ONLY values, at
fixed ambiguity no/yes respectively — the interaction test.

## 2. Results

Metric: `Time` user CPU of `solve_mb_vc` (VC only, no `Qed`), within one coqc
process per file, NOT `allocated_words`. The ordering effect below is why
this matters.

**Warm-up (ZZArrvAmbig vs ZZArrvAmbigSwap, same two VCs, order swapped):**

| file | 1st | 2nd |
|---|---|---|
| ZZArrvAmbig | Old 13.13 s | Amb 19.53 s |
| ZZArrvAmbigSwap | Amb 23.59 s | Old 8.58 s |

The first heavy VC in a process pays **≈4.3 s** extra (4.55 from Old's pair,
4.06 from Amb's — consistent, so a constant, not noise).

**Warm costs (LoopN):** Old 8.6 s → Amb 19.5 s (**×2.27**) → NV 31.7 s
(**×1.63**) → tracked ≈32.6 s (36.9 s cold − 4.3) (×1.03). Total `arrv`/`arr`
**≈3.7×**.

**Where it goes (ZZArrvSplit.v, all warm, after a throwaway warm-up VC):**

| | Old | Amb | NV |
|---|---|---|---|
| raw tree: nodes / angelic_binary / assertk / angelicv | 3281 / 629 / 20 / 244 | 8622 / 1606 / 145 / 752 | 8852 / 1606 / 145 / 819 |
| after `cfg_postprocess`: same counts | 50 / 2 / 12 / **0** | 268 / 29 / 114 / **8** | 413 / 29 / 114 / **72** |
| construction raw / with postprocess | 0.95 / 0.97 s | 2.9 / 3.1 s | 3.5 / 3.9 s |
| `vm_compute` + `solve_vc` | 1.9 s | 3.9 s | 4.9 s |
| closer: hyp `cbn` + `mb_search` | 0.8 + 5.9 s | 2.3 + 13.0 s | 4.7 + 20.4 s |
| `Qed` | 2.0 s | 6.3 s | 9.3 s |

**Interaction (ZZArrvInteract.v, postprocessed counts, nodes / angelic_binary /
assertk / angelicv):** Loop1 old 41/2/12/**0**, new 43/2/12/**0** (matched
time 9.83 → 9.83 s, ×1.00); Loop2 old 72/8/21/**0**, new 98/8/21/**8**
(14.05 → 17.25 s, ×1.23 cold, ≈×1.33 warm).

## 3. Reading the axes apart

- **Ambiguity** triples the tree (raw nodes ×2.6, angelic branches ×2.55) and
  leaves ~10× the residual asserts after postprocess (12 → 114); the closer
  pays for the surviving branches.
- **Values** add NO branches and NO asserts (raw 1606/145 and postprocessed
  29/114 identical Amb vs NV); their entire cost is **64 extra surviving
  existentials** (8 → 72) the closer must `eexists`/unify: `mb_search`
  13.0 → 20.4 s, `Qed` 6.3 → 9.3 s.
- **Interaction:** with unambiguous arrays (Loop1) the value existentials
  are all instantiated by `solve_evars` (0 survive) and cost nothing; with
  ambiguous ones they survive (Loop2: 8, LoopN: 64). So the two factors are
  not independent multipliers — removing the ambiguity should remove both.

## 4. Retracted figures

RETRACTED 2026-10-26: "arrv LoopN is 2.4× (36.6 s vs 13.0 s), its callee 7×"
(PLAN-arrv HANDOFF, Phase C) and "2.8× loop / 8.1× callee" (2026-10-25). The
measurements are real but the ratio compares a COLD `arr` baseline (first VC
in `ZZArrvCost.v`) against WARM `arrv` VCs; warm-vs-warm the loop is ≈3.7×.
Never requote 2.4×/2.8×. The check_scalar loop ratios (×1.00, ×1.23) are
cold-vs-cold (each the only VC in its file), so they stand as ratios of cold
times.

## 5. What this means

The fix is to remove the ambiguity, which by §3 should take both factors
(predicted: LoopN back to ≈`arr` cost, 8.6 s warm, a constant factor of
≈3.7× on every loop with same-shape arrays — muladd's loops are all of that
shape). Decided 2026-10-26 (Emiel): a Coq-level `string` TAG index on `arrv`
(D14), a top-level array's tag = its value name (D15), templates take tags as
Coq parameters (D16) — see PLAN-arrv. Alternative not chosen: distribute ∃
over angelic choice in postprocess (removes only the ×1.63). Re-measure this
record's rigs after the fix; the prediction is falsifiable by the surviving
∃ count (should be 0) and Amb-level cost.

## 6. Reproduction

Probes (untracked-by-build, `ZZ*.v`), compiled with
`rocq_compile_file(file, timing=True)` against a light chain built at
0f27b507..a4d3d8d2: `Example/Rsa/ZZArrvAmbig.v`, `ZZArrvAmbigSwap.v`,
`ZZArrvSplit.v` (needs `RsaSpikeSub.vo`), `Example/CheckScalar/ZZArrvInteract.v`
(needs the ported `CheckScalarParamLoop{1,2}.vo`; embeds the pre-port loops
from `a4d3d8d2~1`).
