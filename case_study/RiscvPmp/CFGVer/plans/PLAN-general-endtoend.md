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
