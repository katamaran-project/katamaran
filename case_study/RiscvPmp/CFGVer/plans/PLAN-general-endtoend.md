# PLAN-general-endtoend — one end-to-end theorem, every array layout

Status: **IN PROGRESS, started 2026-10-02**, branch `issue/general-endtoend`
(off `issue/check-scalar-param`).

Goal (owner, 2026-10-02): new examples should not need new machinery; ideally
ONE most-general end-to-end theorem that implies all the others.

Decisions (owner, 2026-10-02):
- the 7 existing generator bridges STAY, re-derived as corollaries of the core
  (the old generators carry perf work — classed existentials — data_spec lacks);
- cell width becomes an EXPLICIT argument, separate from the stride
  (`arr pub w s`), reversing the derived-width choice of PLAN-check-scalar-full §9;
- order: A then B; value-carrying arrays deferred.

## Where things stand (survey, 2026-10-02)

13 lemmas in `EndToEnd.v`: Iris core `cfg_instrs_{verified,safe}{,_with_mem}`;
end-to-end `cfg_instrs_endToEnd` (regs) and `cfg_instrs_endToEnd_with_memory`
(the most general, separately proved); generator bridges
`gen_contract_noninterferent_{u,u_simple,rel,param,param_simple,
rel_classed_simple,rel_bytes_simple}`.

**The contiguous-data restriction is NOT in the trusted statement.**
`noninterferent_strong` takes `mem_specs` at arbitrary addresses; contiguity
is only `Adequacy.instrsAndDataMemory`'s `HDataAddrs` premise.

## A. One end-to-end theorem

- **A1** `instrsAndDataMemory` for data cells at ARBITRARY addresses:
  pairwise disjoint, disjoint from the code, in range (interval form on N).
  Proof: code bytes ++ data bytes is NoDup and ⊆ liveAddrs, so it is a
  submseteq; big_sepL_submseteq peels it off (affine).  The contiguous
  premise becomes a lemma implying the interval form.
- **A2** `cfg_instrs_endToEnd_with_memory` over that premise is THE core.
  `cfg_instrs_endToEnd`, `cfg_instrs_{verified,safe}` become corollaries at
  data = [] (delete the duplicate proofs).
- **A3** one generator bridge for `gen_seg_contract` + `data_spec`:
  `DAt x` lays the following cells out AT x (pointer arguments), `data_ok`
  carries disjointness, HDataAddrs/ImplPre by construction.
- **A4** the 7 old bridges re-derived from the core.

## B. Every array layout

- **B1** `DBytes` → `DElems w` (any element width).
- **B2** explicit cell width: `arr pub w s` (gapped / struct arrays).
- **B3** random access: generic split/join-at-index ghost lemmas.
- **B4** access width ≠ cell width: ghost conversions word-array ⇄
  byte-array (and 8 ⇄ 4), sound by `ptstomem_bv_app` (existential values).
- each with a small probe proving the form works.

## Log

### 2026-10-02 — A done, B2 + B3 done; B1 + B4 open

- **A1/A2** (`fcc9b428`): `Adequacy.instrsAndDataMemory_at` (data anywhere
  `data_layout_ok` allows: in range, clear of the code, pairwise disjoint;
  proof by `big_sepL_submseteq`, not by slicing `liveAddrs`); the contiguous
  version is a corollary (`contig_data_layout`).  `EndToEnd.cfg_instrs_endToEnd_gen`
  is THE core; `cfg_instrs_endToEnd` (no data) and `_with_memory` (contiguous)
  are corollaries; the non-memory `cfg_instrs_verified/_safe` were dead and
  went.  Every generator bridge reaches the core through `_with_memory`.
- **A3** (`51fb58e6`, `98779311`): `GenSegment.DPtr` (data behind a pointer
  argument), `gen_prog_contract` (reg_spec_q registers incl. `PVVar`, facts,
  `gen_data_at`); `GenProg.v` (new): `gen_prog_noninterferent` (ImplPre once)
  and `data_layout_runs` (layout from interval arithmetic).  Probe:
  `Example/CheckScalar/CheckScalarPtr*` — check_scalar with k at ANY address,
  end theorem = one apply of the bridge.  Closer: `mb_search` now fixes all
  evars from all equations before searching; `mb_eq_evar` solves `a = t + ?v`.
- **B2** (`440f05c4`): `arr pub w s` — explicit cell width.
- **B3** (`197b7143`): `clem_arr_split` (constant index), `clem_arr_join`.
- **B4, common case** (`31630db5`): `clem_arr_bytes_of_words pub` —
  `arr pub 4 4 [a;n;e]`, n <u 2^30, is `arr pub 1 1 [a;4n;e]` (any RelVal
  word value: split by `bv.appView`, ownership by `ptstomem_bv_app`).  Probe
  `Example/ZZArrB4Probe.v` (untracked): a word behind pointer k read at byte
  offset 1 via bytes_of_words + split + take_first — VC green.  Full Results
  closure green after it (2496 s user, 7.4 GB).
- **Still open** — B1 (`DElems w` for w ∉ {1,4}: halfwords), the reverse
  bytes→words conversion, 8⇄4: all need a general `ptstomem (k·w)` ⇄ k × `ptstomem w`
  split at the VALUE level (`bvec ((k·w)·8)` sliced into k pieces), which
  needs dependent-type casts (`(S k·w)·8` is not definitionally
  `w·8 + (k·w)·8`).  Existing: only 4 → 1 bytes (`ptstomem4_split_bytes`).
