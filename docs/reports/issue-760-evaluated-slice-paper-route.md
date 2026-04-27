# Issue #760: evaluated-slice scalar chain vs. paper route

## Verdict

Issue #760 is stale as a correctness/faithfulness blocker on current `main`
(`0d804c9c`).  The current `evaluatedSlice_scalar_chain_bound` no longer uses the
old exact-swap/BABA shortcut described in the issue body.  Its final assembly
follows the paper route through the point-measurement commutation step and pays
both `6 * sqrt (gamma * (m + 1))` losses explicitly.

The remaining live item is cleanup-only: `ProcessedG.lean` still contains some
private phase-five scaffolding from the older collapsed route, and
`Phase67Residual.lean` documents that older endpoint.  Those declarations are not
used by the final paper-chain assembly, so they can be audited by a future
simplifier pass, but they do not affect `commDataProcessedG`.

## Paper anchors

The relevant paper passage is
`references/ldt-paper/commutativity-G.tex:86-130`.

| Paper lines | Paper step | Current Lean counterpart |
| --- | --- | --- |
| 86 | Insert the first-coordinate point measurement after `eq:gcom9`, costing `2√ζ`. | `hphase3paper` in `ProcessedG.lean:1528-1586`. |
| 87 | Commute the two point measurements on the right, costing `6√(γ(m+1))`. | `hphase4paper` in `ProcessedG.lean:1587-1686`, via `evaluatedSlice_phaseFour_pointSwap_right_bound`. |
| 90-96 | Remove the trailing `G^x`, with claim cost `√ζ + 6√(γ(m+1))`. | `hphase5paper` in `ProcessedG.lean:1687-1842`. |
| 99-104 | Reverse the two `eq:add-an-a` insertions, costing `2√ζ + 2√ζ`. | `hphase6first` and `hphase7second` in `ProcessedG.lean:1843-1856`. |
| 117-119 | Apply postprocessed self-consistency twice, costing `√ζ + √ζ`. | `htail8` and `htail9` in `ProcessedG.lean:1857-1868`. |
| 124-130 | Sum the ten losses and relax to `48m(√γ + √ζ)`. | `hassemble` in `ProcessedG.lean:1869-1987`. |

## Current Lean route

The scalar-chain docstring in `ProcessedG.lean:1194-1213` lists exactly the ten
paper losses, with the paper's phase-five claim split into its point-commutation
and boundedness components:

```text
2√ζ, √ζ, 2√ζ, 6√(γ(m+1)), 6√(γ(m+1)), √ζ,
2√ζ, 2√ζ, √ζ, √ζ.
```

The code then defines the paper endpoints explicitly:

- `phase3PaperInserted` (`ProcessedG.lean:1351-1364`), the paper line-86 endpoint.
- `phase4PaperSwapped` (`ProcessedG.lean:1365-1375`), the paper line-87 endpoint
  after the point-measurement swap.
- `phase5PaperRemoved` (`ProcessedG.lean:1376-1378`), re-exported from
  `PaperChainPhaseFive.lean:22-38`, the paper `eq:gcom10` endpoint.

The key issue-#760 concern was whether phase five skipped the paper's internal
point-commutation transport.  It no longer does:

1. `evaluatedSlice_phaseFivePaper_avg_diff_eq_neg_orderedDefect`
   (`PaperChainPhaseFive.lean:219-320`) rewrites the line-87 removal as the
   ordered missing-mass defect.
2. `hswap_defect` (`ProcessedG.lean:1721-1822`) applies
   `evaluatedSlice_phaseFour_pointSwap_right_bound` a second time to swap this
   defect, paying the second `6 * sqrt (gamma * (m + 1))` loss.
3. `evaluatedSlice_phaseFivePaper_reindex_to_raw_defect`
   (`PaperChainPhaseFive.lean:454-540`) reindexes the swapped defect to
   `gCommStabilityTwoRawScalarDefect`.
4. `gCommStabilityTwo_raw_scalar` is then applied at
   `ProcessedG.lean:1704-1720` to obtain the `√ζ` boundedness part.

Thus the paper's line-87 and claim-`g-comm-stability2` point-commutation losses
are both present in the formal chain.

## Final assembly check

The final `hassemble` block no longer proves a `10√ζ` estimate and only later
uses `gamma` arithmetically.  Instead, `hγζ_chain` proves

```lean
avgOver 𝒟 avgBAB - avgOver 𝒟 avgABAB ≤
  12 * Real.sqrt zeta +
    12 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error))
```

at `ProcessedG.lean:1877-1880`.  Doubling this gives the paper's displayed
`24 * (sqrt (gamma * (m + 1)) + sqrt zeta)` budget before the final relaxation to
`commDataProcessedGError params gamma zeta` at `ProcessedG.lean:1928-1986`.

The exact identity
`evaluatedSliceCommutation_avg_swap_terms` is still used at
`ProcessedG.lean:1875-1876`, but only after the paper chain has already reached
`avgBAB`.  It rewrites the final orientation from `avgBAB` to `avgABA`; it does
not replace the two point-measurement commutation estimates above and does not
save any `gamma` budget.

## Cleanup observations

These observations are not correctness blockers for #760:

- `ProcessedG.lean:582-1191` still contains private lemmas for the older
  collapsed phase-five stability defect (`evaluatedSlicePhaseFiveStabilityDefect`
  and its question-level reindexing).  The final `hphase5paper` block uses the
  newer `PaperChainPhaseFive` raw-defect route instead.
- `Phase67Residual.lean` documents the older BAB-side endpoint residual.  Some of
  its prose says the endpoint is used by `evaluatedSlice_scalar_chain_bound`,
  which is no longer true for the final paper-faithful assembly.
- `avgBABA` is still bound in `ProcessedG.lean:1266-1268` but is not used in the
  final chain.

A follow-up simplifier pass could remove or reclassify these leftovers after
checking import dependencies.  I did not change Lean code in this audit to avoid
mixing proof-code cleanup with the faithfulness verdict.

## Recommended issue action

Close #760 as settled by the current `PaperChainPhaseFive` route, or retitle it
as a cleanup task for the stale private phase-five/phase-67 scaffolding.  The
faithfulness concern itself is resolved.
