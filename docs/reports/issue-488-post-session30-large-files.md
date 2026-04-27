# Issue 488 Post-Session30 Large-File Refresh

Audit date: 2026-04-27

Scope: docs-only refresh for #488.  This report recomputes the largest Lean files on
`origin/main` after the session30 split wave and identifies low-conflict seams for future
second-pass modularization PRs.  No Lean files were edited in this sweep.

## Non-overlap constraints for this sweep

The current cleanup wave intentionally avoided code motion because several nearby proof areas are
active or externally owned:

- Open PR #833 by `jizhengfeng` owns the current `fromHToG` / Pasting-Bernoulli thread and
  touches `Pasting/Bernoulli/*`, `Pasting/ContextWrappers.lean`,
  `Pasting/Sandwich/PastedFamilies.lean`, `Pasting/Statements.lean`, and the chapter-9
  blueprint file.
- Active agents were reported on `Test/MainTheorem.lean`,
  `Pasting/BridgeLemmas/LdSandwichLineOnePoint.lean`, Test strategy / BiProjStrat files,
  Basic files, `Commutativity/ScalarApproximation/ProcessedG.lean`, and a scouting upgrade
  report.
- Because #488 is a maintainability issue, the safe outcome here is a fresh dated table and
  recommendations rather than moving declarations in proof-heavy files.

## Current largest Lean files

Line counts were recomputed with `wc -l` over every `MIPStarRE/**/*.lean` file, so they count newline terminators.  Some GitHub views may display one extra physical row for files without a final newline; this report keeps the script-friendly `wc -l` convention used by the audit command.
The table below is a current snapshot, not a promise that every row should be split immediately.
Rows marked "skip now" overlap current ownership constraints or active proof work.

| LOC | File | Status for #488 follow-up |
|---:|---|---|
| 3419 | `MIPStarRE/LDT/MainInductionStep/Theorems.lean` | Candidate, but proof-heavy main-induction file. |
| 3209 | `MIPStarRE/LDT/Commutativity/Transport/FullSlice.lean` | Candidate; large private-helper transport chain. |
| 2838 | `MIPStarRE/LDT/Pasting/BridgeLemmas/LineInterpolation.lean` | Candidate after Pasting agents calm down. |
| 2408 | `MIPStarRE/LDT/Pasting/BridgeLemmas/LdSandwichLineOnePoint.lean` | Skip now: active proof file. |
| 2254 | `MIPStarRE/LDT/Pasting/BridgeLemmas/CommuteGHalfSandwich/MoveChain.lean` | Candidate with `Setup.lean`. |
| 2151 | `MIPStarRE/LDT/Commutativity/ScalarApproximation/ProcessedG.lean` | Skip now: active / external-owned area. |
| 1840 | `MIPStarRE/LDT/Pasting/BridgeLemmas/CommuteGHalfSandwich/Setup.lean` | Candidate with `MoveChain.lean`. |
| 1702 | `MIPStarRE/LDT/Test/MainTheorem.lean` | Skip now: active proof file. |
| 1670 | `MIPStarRE/LDT/Pasting/SwitcherooCompletion.lean` | Candidate, but defer near Pasting activity. |
| 1632 | `MIPStarRE/LDT/GlobalVariance/Theorems/Results.lean` | Candidate if no GlobalVariance PR is active. |
| 1552 | `MIPStarRE/LDT/Pasting/BridgeLemmas/OverAllOutcomes.lean` | Candidate, but Pasting bridge proof-heavy. |
| 1499 | `MIPStarRE/LDT/Commutativity/GCommStability/Scalar.lean` | Good low-conflict code-split candidate. |
| 1473 | `MIPStarRE/LDT/Test/ErrorCascade.lean` | Defer while Test-area agents are active. |
| 1207 | `MIPStarRE/LDT/Pasting/Core.lean` | Candidate, but mostly large theorem bodies. |
| 1202 | `MIPStarRE/LDT/Pasting/Bernoulli/Recurrence.lean` | Skip now: PR #833 / Pasting-Bernoulli. |
| 1138 | `MIPStarRE/LDT/Commutativity/Main/Auxiliary.lean` | Defer: active commutativity residual area. |
| 924 | `MIPStarRE/LDT/Test/StrategyRole.lean` | Defer: Test strategy area is active. |
| 903 | `MIPStarRE/LDT/Basic/SubMeasurementFamilies.lean` | Defer: Basic files are active. |
| 901 | `MIPStarRE/LDT/Commutativity/ScalarApproximation/PaperChainBasic.lean` | Medium candidate; check scalar-chain owners first. |
| 874 | `MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/RankReduction.lean` | Candidate; below urgent threshold. |
| 857 | `MIPStarRE/LDT/Pasting/SwitcherooContraction.lean` | Candidate; old #488 row remains substantial. |
| 829 | `MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities.lean` | Candidate; below urgent threshold. |
| 673 | `MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization.lean` | Candidate only if it grows further. |
| 658 | `MIPStarRE/LDT/ExpansionHypercubeGraph/Defs/Fourier.lean` | Already split; below urgent threshold. |
| 609 | `MIPStarRE/LDT/Pasting/SwitcherooCompletion/Expansion.lean` | Already factored; below urgent threshold. |

## Comparison with the original #488 table

The table in the #488 issue body should now be treated as historical.  Most rows from that
snapshot are thin barrels after session22--session30 splits; the current large-file pressure has
moved to later proof-development files.

| Old LOC | Current LOC | Original file | Current note |
|---:|---:|---|---|
| 994 | 9 | `ExpansionHypercubeGraph/Theorems.lean` | Thin barrel; content moved under `Theorems/`. |
| 972 | 9 | `Commutativity/Scaffold.lean` | Thin barrel; content moved under `Scaffold/`. |
| 968 | 10 | `MakingMeasurementsProjective/QXPLayerData.lean` | Thin barrel; content moved under `QXPLayer/`. |
| 949 | 9 | `Test/StrategySymmetrized.lean` | Thin barrel from PR #621. |
| 939 | 9 | `Pasting/Sandwich.lean` | Thin barrel; content moved under `Sandwich/`. |
| 937 | 9 | `MakingMeasurementsProjective/Naimark.lean` | Thin barrel; one-measurement file remains moderate. |
| 932 | 11 | `Basic/ParametersCore.lean` | Thin barrel; Basic area is active this wave. |
| 913 | 1670 | `Pasting/SwitcherooCompletion.lean` | Still large and grew with completion helpers. |
| 881 | 9 | `Preliminaries/SelfConsistency.lean` | Thin barrel; content moved under `SelfConsistency/`. |
| 870 | 9 | `Commutativity/ScalarApproximation.lean` | Thin barrel; avoid `ProcessedG` owners. |
| 868 | 9 | `ExpansionHypercubeGraph/Defs.lean` | Thin barrel; `Defs/Fourier.lean` is 658 LOC. |
| 854 | 857 | `Pasting/SwitcherooContraction.lean` | Still a medium-sized candidate. |
| 812 | 9 | `Commutativity/GCommStability.lean` | Thin barrel; `GCommStability/Scalar.lean` is now large. |
| 783 | 924 | `Test/StrategyRole.lean` | Still sizable, but Test strategy area is active. |
| 778 | 9 | `Commutativity/EvaluatedSliceCommutation.lean` | Thin barrel. |
| 741 | 9 | `Preliminaries/SwitchSandwichMain.lean` | Thin barrel. |
| 715 | 9 | `Preliminaries/SwitchSandwichPrep.lean` | Thin barrel. |
| 711 | 1207 | `Pasting/Core.lean` | Grew beyond the old snapshot. |
| 696 | 9 | `Pasting/SwitcherooSetup.lean` | Thin barrel. |
| 683 | 9 | `Preliminaries/BipartiteSelfConsistency.lean` | Thin barrel. |

## Recommended next split seams

These are future PR candidates, ordered by expected conflict risk and clarity of mechanical seam.
Each should still be rechecked against open PRs before editing.

1. `Commutativity/GCommStability/Scalar.lean` is the best low-conflict Lean split candidate
   once this docs report lands.  It already separates into three visible blocks: the first scalar
   theorem (`gCommStability_scalar`), the second scalar theorem (`gCommStabilityTwo_scalar`), and
   the raw second-scalar theorem (`gCommStabilityTwo_raw_scalar`).  A future PR could keep
   `GCommStability/Scalar.lean` as a barrel and move those blocks to
   `GCommStability/Scalar/First.lean`, `Second.lean`, and `RawSecond.lean`.
2. `GlobalVariance/Theorems/Results.lean` has a natural split between point-conditioned
   expansion transfer, `generalizeB` collision-expansion residuals, local/global variance
   transport, and final matrix wrappers.  This should wait until no GlobalVariance follow-up PRs
   are open, because recent session30 work touched the same proof chain.
3. `Commutativity/Transport/FullSlice.lean` is high payoff but higher risk.  The visible seams are
   full-slice definitions, collision-factorized tensor averages, x/y tensor marginalization,
   self-consistency bounds, scalar-to-tensor bridge lemmas, and the final
   `fullSliceCommutation_qSDDOp_avg_eq` theorem.
4. `MainInductionStep/Theorems.lean` is now the largest file.  It has possible seams around
   induction-section package wrappers, the `m = 1` base-case bookkeeping, restricted probability
   bounds, average slice-error estimates, pasting-package assembly, and public wrappers.  Because
   this file sits near the main theorem pipeline, it should be split only in a dedicated PR with a
   full targeted build.
5. Pasting bridge files (`LineInterpolation.lean`, `OverAllOutcomes.lean`, and
   `CommuteGHalfSandwich/{Setup,MoveChain}.lean`) are clear modularization targets, but should be
   deferred until PR #833 and active Pasting bridge agents finish.  The likely seams are
   interpolation support / bad-line mass, nonglobal-line consistency, setup equivalences, move-step
   family definitions, and final chain bounds.

## Validation expectation for future code-split PRs

For every future non-doc split, keep the old file path as a barrel when downstream imports benefit,
preserve declaration names and namespaces, and validate at least:

1. `git diff --check`.
2. `lake env lean` on every new file and the barrel file it feeds.
3. A targeted `lake build` for the nearest parent module when the split moves declarations across
   files with private helpers or generated `.olean` dependencies.

This report itself is docs-only, so no Lean validation is required beyond the diff check.
