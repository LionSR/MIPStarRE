# Issue #763: full-slice Schwartz--Zippel marginalization audit

Audit date: 2026-04-27

## Verdict

Issue #763 is stale as a proof gap on current `main` (`ad79dac3`).  The two
public declarations named in the issue body are now proved in
`MIPStarRE/LDT/Commutativity/Main/Auxiliary.lean`:

- `fullSlice_scalar_marginalize_x` is proved at lines 350--413 by the
  switch-sandwich center route from the paper's first-term discussion
  (`commutativity-G.tex` lines 295--305), with bound `4 * Real.sqrt zeta`.
- `fullSlice_scalar_marginalize_y` is proved at lines 460--500 by composing the
  tensor-form Schwartz--Zippel marginalization lemmas and the two
  `closenessOfIP` bridges from `commutativity-G.tex` lines 339--385, with bound
  `2 * (m * d / q) + 4 * Real.sqrt zeta`.

A focused grep over `MIPStarRE/LDT/Commutativity/Main/Auxiliary.lean` and
`MIPStarRE/LDT/Commutativity/Transport/FullSlice.lean` finds no executable
`sorry`, `axiom`, `admit`, `unsafe`, or `native_decide`.  The remaining
occurrences of the word "residual" in `FullSlice.lean` are descriptive names for
proved, private collision sums, not open proof obligations.

## Paper-to-Lean route for lines 339--385

The current Lean code follows the paper's tensor route, preserving the Option 3
hybrid decision from #713: public endpoints remain scalar, while the
Schwartz--Zippel estimates are proved internally on manifestly PSD tensor
averages.

| Paper lines | Paper step | Current Lean evidence |
| --- | --- | --- |
| 339--354 | `eq:gcom4-diff`: evaluate the `x` polynomial outcome and bound the collision contribution by `dm/q`. | `fullSliceBABAxCollisionFactored_le_mdq` (`FullSlice.lean:652--663`), averaged by `fullSliceBABA_tensor_marginalize_x_collision_bound` (`705--722`) and assembled as `fullSliceBABA_tensor_marginalize_x` (`1255--1280`). |
| 356--365 | First `closenessOfIP` move, from the x-evaluated `BAB \otimes A` tensor endpoint to the scalar endpoint. | `xEvaluatedSliceBABAtensor_to_xEvaluatedFullSliceABABAvg` (`FullSlice.lean:2712--2816`), consumed by `FullSliceScalarMarginalizeYFirstCloseness` / `fullSliceScalarMarginalizeYFirstCloseness` (`Auxiliary.lean:427--449`). |
| 356--360, 366--368 | Second `closenessOfIP` move, from the scalar endpoint to the x-evaluated `ABA \otimes B` tensor endpoint. | `xEvaluatedFullSliceABABAvg_to_xEvaluatedFullSliceABABtensorAvg` (`FullSlice.lean:2386--2522`), consumed in `fullSlice_scalar_marginalize_y` (`Auxiliary.lean:478--490`). |
| 369--385 | `eq:evaluate-gcom-at-points-part-dos`: evaluate the `y` polynomial outcome and bound the collision contribution by `dm/q`. | `fullSliceABAByCollisionFactored_le_mdq` (`FullSlice.lean:689--701`), averaged by `fullSliceABAB_tensor_marginalize_y_collision_bound` (`727--744`) and assembled as `fullSliceABAB_tensor_marginalize_y` (`1530--1555`). |
| 369--385 plus the evaluated line-360 analogue | Return from the final tensor endpoint to `evaluatedSliceABABAvg`. | `xEvaluatedFullSliceABABtensor_to_evaluatedSliceABABAvg` (`FullSlice.lean:3123--3145`). |

The public y-side theorem then composes these pieces exactly at
`Auxiliary.lean:469--500`:

1. `fullSliceABAB_to_xEvaluatedSliceBABAtensorAvg` gives the x-prefix
   `md/q + sqrt zeta`.
2. `xEvaluatedSliceBABAtensor_to_xEvaluatedFullSliceABABAvg` and
   `xEvaluatedFullSliceABABAvg_to_xEvaluatedFullSliceABABtensorAvg` give the two
   line-359/line-360 `sqrt zeta` bridges.
3. `xEvaluatedFullSliceABABtensor_to_evaluatedSliceABABAvg` gives the y-tail
   `md/q + sqrt zeta`.

The resulting bound is therefore

```lean
|fullSliceABABAvg params strategy family -
    evaluatedSliceABABAvg params strategy family| ≤
  2 * ((↑params.m : Error) * ↑params.d / ↑params.q) + 4 * Real.sqrt zeta
```

which matches the paper-faithful route recorded in #713 and the closeout notes
for #601/#813/#814.

## Tracker status

- #813 is already closed: the x-side target named there no longer exists and the
  public x theorem is proved.
- #814 is already closed: the former line-359 y closeness residual is now a
  proved package using `xEvaluatedSliceBABAtensor_to_xEvaluatedFullSliceABABAvg`.
- #601 is already closed after `comMain` was marked blueprint `\leanok` and its
  axiom closure was checked.

Thus #763 no longer has a distinct proof target.  The remaining Chapter 10 proof
work is outside the full-slice Schwartz--Zippel marginalization scope and is
tracked under the evaluated-side scalar-chain issues such as #600/#714/#715/#716
and the separate #732 audit.

## Validation for this audit

This PR is docs-only.  Local validation should be limited to:

```text
git diff --check -- docs/reports/issue-763-session34-fullslice-sz-audit.md
rg -n "\b(sorry|axiom|admit|unsafe|native_decide)\b" \
  MIPStarRE/LDT/Commutativity/Main/Auxiliary.lean \
  MIPStarRE/LDT/Commutativity/Transport/FullSlice.lean
```

No Lean files are changed in this audit; it intentionally avoids the future
#488 mechanical `FullSlice.lean` split and does not touch the #600
`ProcessedG.lean` / scalar-chain files.

## Recommended issue action

Close #763 as completed/stale after this audit PR lands.  If a future issue is
needed for `FullSlice.lean`, it should be a separate #488 modularization cleanup
or an explicitly new proof target, not the already-proved Schwartz--Zippel
marginalization lemmas named by #763.
