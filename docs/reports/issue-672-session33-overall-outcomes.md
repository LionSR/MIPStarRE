# Issue #672: over-all-outcomes interpolation status after #850

## Verdict

Issue #672 is now stale as a local `OverAllOutcomes.lean` / `LineInterpolation.lean`
proof gap on current `main` (`4b9b48ba`).  The interpolation-correctness and
over-all-outcomes aggregation chain introduced by the #756 → #777 → #786 → #797
→ #817 sequence is already proved in the intended local files:

- `MIPStarRE/LDT/Pasting/BridgeLemmas/HBConsistency.lean` contains no `sorry` and
  `#print axioms MIPStarRE.LDT.Pasting.hBConsistency` reports no `sorryAx`.
- `MIPStarRE/LDT/Pasting/BridgeLemmas/OverAllOutcomes.lean` contains no
  `sorry`, `axiom`, or `unsafe` matches.
- The `md/q` line-consistent Schwartz--Zippel aggregation from
  `references/ldt-paper/ld-pasting.tex:1235-1275` is already discharged by
  `overAllOutcomes_distinct_lineConsistent_indicator_mass_le_mdq` and its helper
  `lineConsistentIndicatorLocal_avg_le_mdq`.

There is therefore no safe proof edit left in `OverAllOutcomes.lean` or
`LineInterpolation.lean` that would strictly reduce an active named residual.  A
cleanup-only edit in those files would not advance the proof dependency graph.

The remaining `sorryAx` seen by `overAllOutcomes` is inherited from the upstream
one-point line-sandwich lemma, not from the interpolation/aggregation layer:

```text
#print axioms MIPStarRE.LDT.Pasting.overAllOutcomes
-- [propext, sorryAx, Classical.choice, Quot.sound]
#print axioms MIPStarRE.LDT.Pasting.hBConsistency
-- [propext, Classical.choice, Quot.sound]
#print axioms MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint
-- [propext, sorryAx, Classical.choice, Quot.sound]
```

Within `MIPStarRE/LDT/Pasting/BridgeLemmas`, the only live proof `sorry` on this
branch is

```text
MIPStarRE/LDT/Pasting/BridgeLemmas/LdSandwichLineOnePoint.lean:2212
```

in the private lemma
`ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_route`.

## Paper anchors checked

The relevant paper route is `references/ldt-paper/ld-pasting.tex`:

| Paper lines | Step | Current Lean status |
| --- | --- | --- |
| 1041-1091 | `lem:h-b-consistency`: expand the bad mass, swap from uniform to distinct tuples, union-bound over coordinates, and pay `k * ν₅ + k²/q`. | Proved in `HBConsistency.lean` via `hBConsistency_ofLinePointBounds_of_axis_self` and `avgOver_distinct_badMass_le_hBConsistencyError`; no `sorryAx`. |
| 1140-1173 | Start of `lem:over-all-outcomes`: compare pasted/global mass with the all-outcomes expansion. | Proved by the mass-splitting and distinctness lemmas in `OverAllOutcomes.lean`. |
| 1174-1232 | Insert the vertical-line measurement `B`, split the nonglobal mass into bad-line and line-consistent parts, then sum out `B`. | Proved by `nonglobal_mass_eq_inserted_vertical_measurement`, `overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_lineConsistent`, and `lineConsistentNonglobalMass_le_indicatorMass`. |
| 1235-1275 | Choose the interpolant `h*`, use nonglobality to find a disagreeing slice, and apply Schwartz--Zippel for the `md/q` term. | Proved by `lineConsistentIndicator_probability_le_mdq`, `lineConsistentIndicatorLocal_avg_le_mdq`, and `overAllOutcomes_distinct_lineConsistent_indicator_mass_le_mdq`. |
| 1280-1286 | Absorb `2k²/q + md/q + kν₅` into `ν₇`. | Proved by `hBConsistencyError_add_mdq_add_dnoteq_le_overAllOutcomesError`. |

## Interpolation API currently used

The local interpolation API that issue #672 originally requested is present in
`MIPStarRE/LDT/Pasting/BridgeLemmas/LineInterpolation.lean` and is already wired
into `OverAllOutcomes.lean`:

- `interpolateCompletedSlicesFromSupport_restrictAtHeight_poly_eq_get_of_mem`
  and `interpolateCompletedSlices_restrictAtHeight_eq_get_of_mem_supportSubset`
  identify the chosen interpolant with every supported completed slice.
- `tupleInterpolatedVerticalLine` packages the vertical-line restriction of the
  chosen interpolant.
- `tupleInterpolatedVerticalLine_eq_of_not_badLineEvent` and
  `tupleInterpolatedVerticalLine_ne_gives_exists_some_eval_mismatch` provide the
  line-answer uniqueness / mismatch interface used by the bad-line aggregation.
- `nonglobal_gives_slice_mismatch_against_interpolant` is the exact Lean form of
  the paper's line 1256-1258 nonglobal-witness step.

## Actual next proof target

The next proof target that would remove the `sorryAx` inherited by
`overAllOutcomes` is the one-point Cauchy--Schwarz residual (tracked by #835):

```lean
private lemma ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_route
    ... :
    LdSandwichLineOnePointOutcomeSumCSRoute params strategy family gamma zeta hi
```

at `MIPStarRE/LDT/Pasting/BridgeLemmas/LdSandwichLineOnePoint.lean:2196-2212`,
corresponding to `ld-pasting.tex:964-1010`.

That residual is already below the over-all-outcomes layer.  It asks for the two
fields of `LdSandwichLineOnePointOutcomeSumCSRoute`:

1. `firstCauchySchwarz`: move the selected `G` through the left half, paying
   `sqrt (commuteGHalfSandwichError params gamma zeta (i + 1))`.
2. `secondCauchySchwarz`: move the selected `G` through the adjoint/right half,
   paying the same square-root term.

The available inputs are packaged in
`LdSandwichLineOnePointResidualFacts`:

- `rawCore`, the averaged `qSDDCore` bound supplied by
  `lem:commute-g-half-sandwich`;
- `rawLeftEndpoint` and `rawRightEndpoint`, identifying the raw endpoint families
  with the two half-products;
- `prefixOriginalSome` and `movedSome`, the exact option-outcome expansions;
- `matchExpand`, the already-proved match-mass expansion.

A future proof pass should instantiate `Preliminaries.closenessOfIPAdjoint` for
`firstCauchySchwarz` and `Preliminaries.closenessOfIP` for
`secondCauchySchwarz`, with the unit-side bound coming from the submeasurement
inequality for `1 - ((ldSandwichLineOnePointRightFamily ...) q).outcome (some a)`.
That is the remaining mathematical blocker for the `overAllOutcomes` theorem's
axiom audit, not a missing interpolation-correctness lemma.

## Recommended issue action

Retitle #672 as a status/umbrella issue or close it in favor of the sharper
one-point leaf #835.  The local interpolation and over-all-outcomes aggregation
work requested in #672 is complete; the only remaining `sorryAx` in the route is
the upstream `ldSandwichLineOnePoint` Cauchy--Schwarz residual.
