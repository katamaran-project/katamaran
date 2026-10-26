# Removed 2026-10-26 (PLAN-arrv Phase E: `arr` deleted) — verbatim from .claude/skills/cfgver-contracts/SKILL.md

## Arrays: the `arr` chunk and the CFGVer ghost-lemma catalogue

`arr pub w s [a; n; e]` (`Sig.v`): n cells of **w bytes** at a, a+s, …,
a+s(n-1), existential values (SyncVal when `pub`), and e = a + s·n.
w = |s| tiles (words `4 4`/`4 (-4)`, bytes `1 1`); |s| > w is an array of
structs. a, n, e must be public (interp is False on NonSyncVal) — state
`secLeakvar` of the count in a loop invariant; the executor does not infer it.

Ghost lemmas (`Verifier.CLem`, used as `AnnotCLemma (...)` in
`ai_ghost_before/after`; soundness `SpecIris.clemSem`): `take_first`,
`take_last`, `add_first`, `add_last`, `nonempty` (a≠e ⊢ n≠0), `empty`,
`empty_elim`, `lockstep`, `drop`, `flip` (walk the other way), `split k`
(constant index), `join` (adjacent arrays), `bytes_of_words` (word array read
bytewise, n <u 2^30), and the regroups for any power-of-two width
`u : RgWidth` (`RgW2`/`RgW4`/`RgW8`, k = 2/4/8): `to_bytes pub u`
(`arr k k [a;n;e]`, n <u 2^32/k ⊢ `arr 1 1 [a; k·n; e]`) and `of_bytes pub u`
(`arr 1 1 [a;m;e]` ⊢ `arr k k [a; m>>sh; e'] ∗ arr 1 1 [e'; m & (k−1); e]`,
e' = a + k·(m>>sh) — no side condition, leftover bytes kept, empty for a
literal multiple of k). Halfword data = `DBytes` + `of_bytes _ RgW2`;
bytes→words = `of_bytes _ RgW4`. Worked probe: `Example/ZZArrRegroupProbe.v`
(untracked). Every other constructor takes `pub w s` (lockstep `p1 p2 w s`;
bytes_of_words only `pub`). The array argument is matched ANGELICALLY, so two
live arrays with the same `arr pub w s` predicate are ambiguous — place each
`take_first` right before its own load, or use distinct strides.
Loop template: `Example/Muladd/MuladdParamLoopN.v` (remaining count n the only
varying variable, addresses END − s·n). The general proofs (a k-byte cell
is k byte cells for any RelVal value, and back) are `SpecIris.rg_*`.
