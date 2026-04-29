# Issues #600 / #628 / #715: evaluated-slice scalar-chain audit after PR #858

## Verdict

On current `main` after PR #858, the evaluated-slice scalar chain is no longer a
live proof residual.  The private lemma `evaluatedSlice_scalar_chain_bound` in
`ScalarApproximation/ProcessedG.lean` is proved, and the public theorem
`MIPStarRE.LDT.Commutativity.commDataProcessedG` consumes it without introducing
a new placeholder.

This audit retargets the issue state as follows:

- **#600**: resolved for the evaluated-side scalar chain.  The final assembly in
  `ProcessedG.lean` follows `references/ldt-paper/commutativity-G.tex:72-130`
  and proves the paper budget
  `2 * (12√ζ + 12√(γ(m+1))) ≤ 48m(√γ + √ζ)`.
- **#715**: resolved for phase five.  The live assembly uses the paper-faithful
  route `phase4PaperSwapped → phase5PaperRemoved`, paying
  `√ζ + 6√(γ(m+1))` via the ordered/swapped raw-defect route rather than the old
  collapsed local scaffold.
- **#628**: resolved as a signature/coordinate audit.  The active phase-five
  reindexing lemma decomposes the first coordinate, matching the term that reads
  `pointHeight params q.1` and `evaluatedSlicePointMeas params strategy q.1`, and
  it carries no unused `gamma` parameter.

No new theorem statement, constant, or bound is introduced in this report.

## Paper route in the current Lean file

The paper passage is `commutativity-G.tex:72-130`.  The current Lean route is:

| Paper lines | Paper step | Current Lean counterpart |
| --- | --- | --- |
| 75-83 | first reverse/insert step and `clm:g-comm-stability`, cost `2√ζ + √ζ` | `hphase1` and `hphase2` in `ProcessedG.lean` |
| 86 | insert the first-coordinate point measurement, cost `2√ζ` | `hphase3paper` |
| 87 | swap the right-register point measurements, cost `6√(γ(m+1))` | `hphase4paper`, via `evaluatedSlice_phaseFour_pointSwap_right_bound` |
| 90-96 | remove the trailing `G^x`, cost `√ζ + 6√(γ(m+1))` | `hphase5paper` |
| 99-104 | two reverse `eq:add-an-a` steps, cost `4√ζ` | `evaluatedSlice_phaseSixSeven_reverse_bound` from `PaperChainReverse.lean` |
| 117-119 | two postprocessed self-consistency moves, cost `√ζ + √ζ` | `htail8` and `htail9` |
| 124-130 | sum and relax the error | `hassemble` |

The total is exactly the displayed paper budget

```text
2 * (2√ζ + √ζ + 2√ζ + 6√(γ(m+1))
       + √ζ + 6√(γ(m+1)) + 4√ζ + √ζ + √ζ)
= 24 * (√ζ + √(γ(m+1)))
≤ 48m * (√γ + √ζ).
```

## #628 phase-five coordinate/signature check

The phase-five concern in #628 was that a reindexing descendant of the old
`evaluatedSlice_phaseFive_removeGx_bound` might have decomposed the wrong
coordinate, and that an unused `gamma` parameter might have survived the file
split.

The current active lemma is

```lean
MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseFivePaper_reindex_to_raw_defect
```

in `ScalarApproximation/PaperChainPhaseFive.lean`.  It starts from the swapped
paper defect

```lean
evaluatedSlicePhaseFivePaperSwappedDefect params strategy family G q
```

whose body uses `pointHeight params q.1` and the first-coordinate point outcome
`evaluatedSlicePointMeas params strategy q.1`.  The proof therefore decomposes
`q.1` as `appendPoint params u x`:

```lean
avgOver (uniformDistribution (Point params.next)) (fun ux =>
  avgOver (uniformDistribution (Point params.next)) (fun vy => ... (ux, vy)))
=
avgOver (uniformDistribution (Fq params)) (fun x =>
  avgOver (uniformDistribution (Point params)) (fun u =>
    avgOver (uniformDistribution (Point params.next)) (fun vy =>
      ... (appendPoint params u x, vy))))
```

This matches the scalar integrand's coordinate order.  The lemma signature is

```lean
(params) [FieldModel params.q] (strategy) (family) (G) (hG) : ...
```

and has no `gamma` argument.  The only phase-five `gamma` cost is the separate
right-register point-measurement swap in `ProcessedG.lean`'s `hphase5paper`
block.

## Historical leftovers that are not #600 blockers

Two pieces of source remain intentionally historical/cleanup-only:

1. `Phase67Residual.lean` records the stricter BAB-side/tensor-first endpoint
   from the #732 audit.  The current scalar-chain assembly instead uses the
   paper endpoint packaged by `evaluatedSlice_phaseSixSeven_reverse_bound`.
2. `ProcessedG.lean` still contains private, proved phase-five local-scaffold
   lemmas around `evaluatedSlicePhaseFiveStabilityDefect`.  They are not used by
   the final `hphase5paper` assembly, which follows the raw-defect route in
   `PaperChainPhaseFive.lean`.

These are simplifier-pass cleanup candidates, not proof debt for
`commDataProcessedG`.

## Recommended issue action

- Close #600 as completed for the evaluated-slice scalar chain.
- Close #715 as completed; the phase-five bridge used by the final chain is
  proved, and the older local scaffold is no longer the live route.
- Close #628 as completed unless maintainers want to keep it open solely for
  optional deletion of historical private scaffolding.
- Update #109's live-subissue list: the evaluated-side scalar chain has no live
  executable placeholders after #858 and this audit.
