# Scouting: `lem:ld-sandwich-line-one-point`

Date: 2026-04-24
Issue: #299

## Scope read

Paper:

- `references/ldt-paper/ld-pasting.tex:931-1036`

Lean:

- `MIPStarRE/LDT/Pasting/BridgeLemmas/LdSandwichLineOnePoint.lean`
- `MIPStarRE/LDT/Pasting/BridgeLemmas/CommuteGHalfSandwich.lean`
- `MIPStarRE/LDT/Pasting/BridgeLemmas/CommuteGHalfSandwich/Setup.lean`
- `MIPStarRE/LDT/Pasting/Sandwich/GHatSandwich.lean`
- `MIPStarRE/LDT/Pasting/Sandwich/Switcheroo.lean`
- `MIPStarRE/LDT/Pasting/Core.lean`
- `MIPStarRE/LDT/Preliminaries/CauchySchwarz.lean`
- `MIPStarRE/LDT/Test/Defs.lean`

## Executive summary

I did **not** close the final proof obligation. I did, however, refactor
`ldSandwichLineOnePoint_core` so the top-level theorem no longer ends in a raw
`sorry`. The remaining gap is now isolated to a single helper lemma:

```lean
private lemma ldSandwichLineOnePoint_matchMass_lower_bound ...
```

This helper is the exact scalar lower bound that the paper proves after
rewriting the consistency defect as
$1 - \mathbb{E}[\text{match mass}]$ for two honest measurements.

So the remaining work is now paper-faithful and local:

1. convert the left/right families into measurements,
2. rewrite `ConsRel` as an averaged match-mass lower bound,
3. prove that lower bound by the paper's delete-coordinates $+$ two
   Cauchy–Schwarz transports $+$ prefix collapse $+$ `ldGbcon` chain.

## What was landed in Lean

The file now contains three proved structural helpers:

1. `ldSandwichLineOnePointLeftMeasurement`
   - packages the left family as a genuine measurement
   - uses `gHatSandwichFamily` total $= I$

2. `ldSandwichLineOnePointRightMeasurementLocal`
   - local measurement packaging for the right family
   - intentionally named with `_Local` to avoid colliding with the public helper
     already defined in `LineInterpolation.lean`

3. `qBipartiteConsDefect_of_measurements_local`
   - rewrites questionwise consistency defect for two measurements as
     $$
     q\mathrm{Cons}(A,B) = \langle \psi, I \psi \rangle - \mathrm{match}(A,B)
     $$
   - specialized in
     `ldSandwichLineOnePoint_defect_eq_one_sub_matchMass`

Using those lemmas, `ldSandwichLineOnePoint_core` is now a short reduction:

- define the averaged match mass,
- call `ldSandwichLineOnePoint_matchMass_lower_bound`,
- rewrite the averaged defect as $1 - \mathbb{E}[\text{match mass}]$,
- finish by linear arithmetic.

## Remaining obligation: dependency map

The still-open helper
`ldSandwichLineOnePoint_matchMass_lower_bound` should follow the paper in the
following four substeps.

### A. Delete coordinates to the right of `i`

Target shape:

- reduce the averaged match mass on
  `SandwichedLineQuestion params k`
- to the same expression using only the prefix of length `i + 1`

Paper reference: `eq:delete-extraneous-coordinates`.

Likely ingredients:

- `gHatSandwichFamily`
- `gHatHalfProductTotalOperator_eq_one`
- projectivity of `gHatIdxMeas` outcomes
- finite-sum reindexing over tuple outcomes

### B. First Cauchy–Schwarz transport

Paper reference: `eq:gonna-need-a-bigger-cauchy-schwarz`.

Needed Lean ingredients:

- `closenessOfIP`
- `CommuteGHalfSandwichStatement.repeatedCommutation`
- the `hC` side condition from prefix/tail contraction lemmas in
  `CommuteGHalfSandwich/Setup.lean`, especially:
  - `gHatHalfProduct_sum_adjoint_mul_le_one`
  - `gHatReverseHalfProduct_sum_adjoint_mul_le_one`
  - `leftTensor_rightTensor_sum_adjoint_mul_le_one`

### C. Second Cauchy–Schwarz transport

Paper reference: `eq:even-bigger-CS`.

Needed Lean ingredients:

- `closenessOfIPAdjoint`
- the same commutation witness as in step B
- the adjoint-side contraction bound, again built from the Setup lemmas above

### D. Collapse the middle prefix and finish with `ldGbcon`

Paper reference: lines 1011-1027.

Target shape:

- show the middle prefix factor
  $$
  \sum_{g_{<i}} \widehat G^{x_{<i}}_{g_{<i}} (\widehat G^{x_{<i}}_{g_{<i}})^\dagger = I
  $$
- identify the surviving scalar with the one-point `ldGbcon` term

Likely ingredients:

- repeated measurement-completeness collapse for the prefix sandwich
- `ldSandwichLineOnePoint_endpoint_ldGbcon`
- `ldSandwichLineOnePoint_oneQuestion_ldGbcon`
- `ldGbcon`

## Suggested follow-up lemma split

If someone wants to finish the proof incrementally, the cleanest split seems to
be:

1. `ldSandwichLineOnePoint_delete_extraneous_matchMass`
   - handles step A only
2. `ldSandwichLineOnePoint_matchMass_after_commuting`
   - packages steps B--D into the final lower bound

That would keep each missing proof aligned with a contiguous paper chunk.

## Why this refactor is still useful

Before this session, the file ended in a monolithic top-level `sorry` with the
whole paper proof implicit.

After the refactor, the theorem statement and public wrapper are stable, the
questionwise defect has been reduced to the right scalar quantity, and the only
remaining gap is a single helper whose statement matches the paper's real work.
That should make the eventual closure substantially easier to review and debug.
