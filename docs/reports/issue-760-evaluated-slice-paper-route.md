# Issue #760: evaluated-slice scalar chain vs. paper route

## Verdict

Issue #760 is stale as a correctness/faithfulness blocker on current `main`
after PR #858 (`refactor(LDT/Commutativity): package phase67 reverse bridge`).
The current `evaluatedSlice_scalar_chain_bound` no longer uses the
old exact-swap/BABA shortcut described in the issue body.  Its final assembly
follows the paper route through the point-measurement commutation step and pays
both `6 * sqrt (gamma * (m + 1))` losses explicitly.

The former cleanup-only items have been removed after import checks:
`ProcessedG/PhaseFive.lean` contained phase-five scaffolding from the older
collapsed route, and `Phase67Residual.lean` documented the corresponding
BAB-side endpoint.  Neither file was used by the final paper-chain assembly, and
their deletion does not affect `commDataProcessedG`.

## Paper anchors

The relevant paper passage is
`references/ldt-paper/commutativity-G.tex:86-130`.

| Paper lines | Paper step | Current Lean counterpart |
| --- | --- | --- |
| 86 | Insert the first-coordinate point measurement after `eq:gcom9`, costing `2√ζ`. | `hphase3paper` in `ProcessedG.lean:1528-1586`. |
| 87 | Commute the two point measurements on the right, costing `6√(γ(m+1))`. | `hphase4paper` in `ProcessedG.lean:1587-1686`, via `evaluatedSlice_phaseFour_pointSwap_right_bound`. |
| 90-96 | Remove the trailing `G^x`, with claim cost `√ζ + 6√(γ(m+1))`. | `hphase5paper` in `ProcessedG.lean:1687-1842`. |
| 99-104 | Reverse the two `eq:add-an-a` insertions, costing `2√ζ + 2√ζ`. | `hphase67paper` in `ProcessedG.lean`, via `evaluatedSlice_phaseSixSeven_reverse_bound`. |
| 117-119 | Apply postprocessed self-consistency twice, costing `√ζ + √ζ`. | `htail8` and `htail9` in `ProcessedG.lean`. |
| 124-130 | Sum the ten losses and relax to `48m(√γ + √ζ)`. | `hassemble` in `ProcessedG.lean`. |

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

- The former `ProcessedG/PhaseFive.lean` lemmas for the older collapsed
  phase-five stability defect (`evaluatedSlicePhaseFiveStabilityDefect` and its
  question-level reindexing) have been deleted after import checks.  The final
  `hphase5paper` block uses the newer `PaperChainPhaseFive` raw-defect route.
- The former `Phase67Residual.lean` BAB-side endpoint residual has also been
  deleted.  The final paper-faithful assembly uses
  `evaluatedSlicePhaseFivePaperRemoved` and
  `evaluatedSlice_phaseSixSeven_reverse_bound`.
- The unused `avgBABA` binding noted in the original audit has been removed.

No phase-five or phase-67 scaffold remains in the checked scalar-chain
interface.

## Recommended issue action

Close #760 as settled by the current `PaperChainPhaseFive` route.  The
faithfulness concern and the associated cleanup-only remnants are resolved.
