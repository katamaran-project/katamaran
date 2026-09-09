# Making the address space a parameter, not a set of literals

Status: **stage 0 (lenAddr/maxAddr) DONE. minAddr DEFERRED by decision -- stays 0,
with the required work recorded below.**
Started 2026-09-08.

## Why

Raising `lenAddr` from `2^10` to `2^12` (commit `b4439a8f`) should have been a
one-line change. It was not: **24 proof sites spelled the numeric value**, and
the raise silently missed two of them. The two misses are the interesting part
of the story:

- they were in `Example/JumpsResult.v`, not in the verifier — an *example*, a
  file nobody thinks to grep when changing a model parameter;
- they were `1024` and `1028`, the second being `lenAddr + 4`, a *derived*
  value that a grep for the constant itself would not have found even in the
  right file;
- and one more, `Tables.v`'s, was written `2 ^ 10`, invisible to a `1024` grep.

The failure was found only because the build broke. Nothing else would have
caught it: a wrong-but-provable bound just makes theorems weaker, silently.

## Stage 0 — lenAddr / maxAddr (DONE)

Every former literal now names the constant it actually means. The two are
**deliberately not merged**: they differ exactly when `minAddr != 0`, and
keeping them distinct is what makes the minAddr-dependent sites greppable.

| file | now says | because |
|---|---|---|
| `Contracts.v` (17) | `maxAddr` | `sep_contract_mem_read`'s bound is literally `unsigned paddr + bytes <= Z.of_N maxAddr` (`Spec.v:448`). Correct for any `minAddr`. |
| `Tables.v`, `Adequacy.v`, `EndToEnd.v`, `Example/JumpsResult.v` (7) | `lenAddr` | the incoming premise from `cfg_instrs_verified` is `init_addr + 4*|instrs| < lenAddr`. |

`< bv.exp2 xlenbits` side conditions go through `Base.v`'s pre-existing
`maxAddr_rep` / `lenAddr_rep` rather than `vm_compute; reflexivity` on a
literal.

### The one trap, hit twice

`lia` needs every constant to arrive as a **consistent atom**, and a bare
`cbn in *` guarantees the opposite: it reduces a constant where it occurs in an
*existing* hypothesis but not in one you state *afterwards*. Both failures
looked identical (`Tactic failure: Cannot find witness`) and both were in
`relval_fetch_upper_add`:

1. `maxAddr` reduced in `Hb` but not in a later-posed `Hexp`;
2. after fixing that by posing `maxAddr_rep` first, `cbn` reduced
   **`bv.exp2 xlenbits` to `bv.exp2 32`** in `Hexp` — `xlenbits` is only
   `Opaque` inside `ModelBinary.v` — while the freshly-stated `Hlt` said
   `bv.exp2 xlenbits`.

Fix: `cbn -[maxAddr bv.exp2 xlenbits] in *`, i.e. block delta on every constant
that appears on both sides of a `lia`. Diagnosing it took one goal dump
(`lazymatch type of H with ?T => idtac "ZZ:" T end`) and no guessing; two
rounds of guessing preceded it and both were wrong.

## The raise had a QUADRATIC cost, now removed (2026-09-09)

Raising `lenAddr` did not just cost proportionally more -- it made
`case_study/RiscvPmp/IrisInstance.v` **uncompilable on this machine**. The file
ran 48+ minutes at 14.6 GB (6.2 resident + 8.2 swapped), footprint still
growing, and was killed without finishing.

Cause, and it is worth internalising because nothing about it is bitvector- or
Katamaran-specific:

```coq
Lemma NoDup_liveAddrs : NoDup liveAddrs.
Proof. now eapply Prelude.nodup_fixed. Qed.   (* <- decides it by COMPUTATION *)
```

`Prelude.nodup_fixed` (`theories/Prelude.v:238`) has premise
`nodup eq_dec l = l`, discharged by computation. `nodup` is O(|l|^2) in
equality tests, and `liveAddrs` is `lenAddr` elements long -- so **the size of
the address space entered the Iris layer quadratically**. `2^10 -> 2^12` is 4x
the list and ~16x the comparisons: ~0.5M -> ~8.4M, each building proof terms.

Fixed by proving it structurally instead. New in `theories/Bitvector.v`, next
to the `seqBv_*` family:

```coq
Lemma seqBv_NoDup {n} (min : bv n) (len : N) :
  (bv.unsigned min + Z.of_N len <= 2 ^ Z.of_nat n)%Z ->
  base.NoDup (seqBv min len).
```

`seqZ` is `NoDup` and `bv.of_Z` is injective on the no-wrap range, so the cost
is **independent of `len`** -- verified at `len = 2^20`, same 20 ms.

**Measured: `IrisInstance.v` went from >48 min / 14.6 GB / did-not-finish to
109 seconds.**

Two notes for whoever raises `lenAddr` again:

- The address space is no longer quadratic anywhere known, so it can be sized
  on its merits. But *re-measure* rather than assume: `liveAddrs` is still
  iterated (`interp_mem`, `big_sepL`) and that part is linear-but-real.
- A `Definition`-sized list plus a decision procedure is the general shape of
  this bug. `nodup_fixed` is still the right tool for a FIXED small list (the
  `Example/*Result.v` reg-spec lists use it correctly); it is the wrong tool
  the moment the list length is a model parameter.

## minAddr — DEFERRED (decision 2026-09-08)

**`minAddr` stays `0`. It is NOT symbolic, and nothing below is implemented.**
This section is the record of what it would take, written while the ground was
fresh, so a future session does not have to re-derive it.

`Spec.v` is already honest -- it writes `Z.of_N minAddr` symbolically. The
*discharge* is not. `minAddr = 0` is assumed structurally in two places, and
neither is a literal, so the grep that found the 24 `lenAddr` sites would never
have found them.

### The two structural assumptions

1. **`Contracts.v` `relval_fetch_lower` / `instprop_fetch_bound_lower`.**
   They prove `0 <= unsigned X` **from nothing** -- that is just
   unsigned-nonnegativity. They close the real goal
   `Z.of_N minAddr <= unsigned paddr` only because it `vm_compute`s to `0`.
2. **`Adequacy.v:946` `instrsMemory` and `:1092` `instrsAndDataMemory`.**
   Both split `liveAddrs` as `seqBv (of_N minAddr) start ++ ...` and close the
   split with `Heq : bv.of_N minAddr + bv.of_N start = bv.of_N start` --
   `minAddr = 0` outright.

### What would be needed

| # | where | work |
|---|---|---|
| 1 | `Base.v` | `fits_in_ram base bound := minAddr <= base /\ base + bound < maxAddr`, so the 16 trusted statements gain ONE named premise rather than two anonymous ones |
| 2 | `Contracts.v` | the two lemmas above become real; `solve_symbase_fetch` gains the `_add` alternative |
| 3 | `GenContract.v:680,730` | precondition gains `minAddr <= unsigned p`; `lenAddr` -> `maxAddr`. **Order-fragile** -- see `project_solver_secleak_residuals`, a conjunct-ORDER bug in `sep_contract_fetch_instr` cost real time. Check VC residuals, do not assume. |
| 4 | `Adequacy.v` | first segment length becomes `start - minAddr`, last `maxAddr - start - 4*len` |
| 5 | `Tables.v`, `EndToEnd.v` | `table_bound_of_lenAddr` + ~12 bridge premises restated over `fits_in_ram` |
| 6 | 14 statements in 12 `Example/*Result.v` | `(init_addr + N < lenAddr)%N ->` becomes `fits_in_ram init_addr N ->`. Smaller than it looks: the bodies are `intros Hb. ... - exact Hb.`, so once the *bridge* premise changes the bodies do not. |

### Three proofs already validated (rocq-mcp preamble mode)

Not written to any file -- reproduce from here if the work is picked up.

```coq
(* stage 2 core, 169 ms *)
Lemma fetch_bound_step_lower (a : bv 32) (c X : N) :
  (minAddr <= bv.bin a)%N -> (bv.bin a + X <= maxAddr)%N -> (c + 4 <= X)%N ->
  (minAddr <= bv.bin (bv.add (bv.of_N c) a))%N.
Proof.
  intros Hlow Hbound Hc.
  pose proof maxAddr_rep as Hexp.
  assert (HcE : (c < bv.exp2 32)%N).
  { set (E := bv.exp2 32) in *; clearbody E. lia. }
  pose proof (bv.bin_of_N_small HcE) as Heq.
  assert (Hlt : (bv.bin (@bv.of_N 32 c) + bv.bin a < bv.exp2 32)%N).
  { rewrite Heq. set (E := bv.exp2 32) in *; clearbody E. lia. }
  rewrite (bv.bin_add_small Hlt). rewrite Heq. lia.
Qed.

(* stage 4 core, 57 ms for both *)
Lemma seq_split_base (start : N) (Hlow : (minAddr <= start)%N) :
  bv.add (@bv.of_N 32 minAddr) (@bv.of_N 32 (start - minAddr)) = @bv.of_N 32 start.
Proof. rewrite bv.of_N_add. f_equal. lia. Qed.

Lemma seq_split_len (start len : N)
  (Hlow : (minAddr <= start)%N) (Hhi : (start + len < maxAddr)%N) :
  ((start - minAddr) + len + (maxAddr - start - len) = lenAddr)%N.
Proof. unfold maxAddr in *. lia. Qed.
```

### The part that makes this more than a refactor

**Doing stages 1-6 while `minAddr` is still `0` would produce a parametric-
looking DEAD branch.** `vm_compute` folds `Z.of_N minAddr` to `0` in every VC,
so every new hypothesis discharges trivially and the general path is never
taken -- the same rot as the hard-coded `1024`, one level up and harder to see.

So the work is only finished when a build passes at `minAddr := 256`. And that
needs one more thing: **`Noninterference.v:88` sets `init_addr := 0`**, so at
`minAddr = 256` every concrete corollary's `fits_in_ram 0 bound` premise is
FALSE and they become unprovable. `project_init_addr_param` already made the
machinery work at a nonzero base -- each `*_noninterferent_param (init_addr : N)`
is universally quantified and the corollary merely instantiates at 0 -- so the
validation run is `minAddr := 256`, `init_addr := 256`, `./scripts/gate.sh` at
`GATE_JOBS=1`, then revert. Without it, do not declare the work done.

## Do NOT

- **Do not merge `lenAddr` and `maxAddr` into one constant.** They coincide
  only because `minAddr = 0`; merging bakes that in permanently and destroys
  the grep that tells you which sites depend on it.
- **Do not write the numeric value in a proof**, ever, including derived ones
  (`maxAddr - 4`, `lenAddr + 4`). Phrase the bound to avoid the subtraction
  (`c + bin a + 4 <= maxAddr`) rather than pre-computing it.
- **Do not state a constant fact after a normalising tactic** and expect `lia`
  to connect it -- block delta instead (see the trap under stage 0).
