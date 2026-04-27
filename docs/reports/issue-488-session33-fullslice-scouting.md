# Issue 488 Session33 FullSlice Modularization Scout

Audit date: 2026-04-27

Scope: docs-only follow-up for #488 after the `GCommStability/Scalar.lean` split from
PR #850.  This sweep recomputes the large-file table, inspects the remaining
`Commutativity/Transport/FullSlice.lean` seams, and avoids the active proof areas owned by
PR #833, PR #851, and the Session33 agents for #835, #672, #732, and #744.
No Lean files were edited.

## Current largest Lean files

Line counts were recomputed with a Python line count over `MIPStarRE/**/*.lean` on the
session33 branch based at `4b9b48ba`.  As in the other #488 reports, note that
`wc -l` counts trailing newline characters, so its output can differ by one from
editor or script counts that count logical lines.  Rows marked "skip now" overlap active
proof work or externally owned Pasting files.

| LOC | File | Status for a #488 follow-up |
|---:|---|---|
| 3419 | `MIPStarRE/LDT/MainInductionStep/Theorems.lean` | Candidate, but proof-heavy. |
| 3209 | `MIPStarRE/LDT/Commutativity/Transport/FullSlice.lean` | Best next scouting target. |
| 2838 | `MIPStarRE/LDT/Pasting/BridgeLemmas/LineInterpolation.lean` | Skip now: active #672. |
| 2695 | `MIPStarRE/LDT/Pasting/BridgeLemmas/LdSandwichLineOnePoint.lean` | Skip now: active #835. |
| 2254 | `MIPStarRE/LDT/Pasting/BridgeLemmas/CommuteGHalfSandwich/MoveChain.lean` | Defer near Pasting work. |
| 2138 | `MIPStarRE/LDT/Test/MainTheorem.lean` | Skip now: PR #851 / Test-owned. |
| 2024 | `MIPStarRE/LDT/Commutativity/ScalarApproximation/ProcessedG.lean` | Skip now: active #732 area. |
| 1840 | `MIPStarRE/LDT/Pasting/BridgeLemmas/CommuteGHalfSandwich/Setup.lean` | Defer near Pasting work. |
| 1670 | `MIPStarRE/LDT/Pasting/SwitcherooCompletion.lean` | Defer near Pasting work. |
| 1632 | `MIPStarRE/LDT/GlobalVariance/Theorems/Results.lean` | Skip now: active #744. |
| 1552 | `MIPStarRE/LDT/Pasting/BridgeLemmas/OverAllOutcomes.lean` | Skip now: active #672. |
| 1473 | `MIPStarRE/LDT/Test/ErrorCascade.lean` | Defer while Test area is active. |
| 1207 | `MIPStarRE/LDT/Pasting/Core.lean` | Defer near PR #833 / Pasting work. |
| 1202 | `MIPStarRE/LDT/Pasting/Bernoulli/Recurrence.lean` | Skip now: PR #833-owned. |
| 1138 | `MIPStarRE/LDT/Commutativity/Main/Auxiliary.lean` | Candidate after FullSlice. |
| 924 | `MIPStarRE/LDT/Test/StrategyRole.lean` | Defer while Test area is active. |
| 903 | `MIPStarRE/LDT/Basic/SubMeasurementFamilies.lean` | Moderate; below urgent threshold. |
| 901 | `MIPStarRE/LDT/Commutativity/ScalarApproximation/PaperChainBasic.lean` | Skip now: active #732 area. |
| 874 | `MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/RankReduction.lean` | Moderate candidate. |
| 857 | `MIPStarRE/LDT/Pasting/SwitcherooContraction.lean` | Defer near Pasting work. |
| 829 | `MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities.lean` | Moderate candidate. |
| 673 | `MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization.lean` | Low priority. |
| 658 | `MIPStarRE/LDT/ExpansionHypercubeGraph/Defs/Fourier.lean` | Low priority. |
| 648 | `MIPStarRE/LDT/Commutativity/GCommStability/Scalar/RawSecond.lean` | Newly split; leave alone. |
| 609 | `MIPStarRE/LDT/Pasting/SwitcherooCompletion/Expansion.lean` | Low priority / Pasting-adjacent. |

The old #488 table is now historical.  After PR #850, the former monolithic
`Commutativity/GCommStability/Scalar.lean` is a barrel and no longer appears among the
large files.  `FullSlice.lean` is therefore the clearest non-Pasting follow-up target.

## FullSlice import and reverse-import surface

`FullSlice.lean` currently imports exactly four local modules:

```lean
import MIPStarRE.LDT.Commutativity.Transport.Pullback
import MIPStarRE.LDT.Commutativity.Scaffold.Products
import MIPStarRE.LDT.Commutativity.EvaluatedSliceCommutation.Averages
import MIPStarRE.LDT.Preliminaries.PolynomialAgreement
```

The direct reverse imports are small:

- `MIPStarRE/LDT.lean` imports it as part of the project barrel.
- `MIPStarRE/LDT/Commutativity/Transport.lean` imports it as the transport barrel.
- `MIPStarRE/LDT/Commutativity/Theorems.lean` imports it from the theorem bundle.
- `MIPStarRE/LDT/Commutativity/Main/Auxiliary.lean` imports it for the final scalar route.

The non-barrel downstream consumers are concentrated in
`Commutativity/Main/EvaluatedQuestions.lean` and `Commutativity/Main/Auxiliary.lean`.  This
makes an incremental child-module extraction feasible: keep the public declaration names in
the `MIPStarRE.LDT.Commutativity` namespace and preserve `Transport.FullSlice` as the
compatibility import.

## Public API that a split must preserve

The public surface is mostly scalar endpoints plus a few bridge lemmas.

- Zero family and trivial bounds, consumed by `Main/EvaluatedQuestions.lean`:
  `zeroFullSliceOpFamily`, `fullSliceProductLeft_to_zero_le_one`, and
  `zero_to_fullSliceProductRight_le_one`.
- Scalar averages, consumed by `Main/EvaluatedQuestions.lean` and
  `Main/Auxiliary.lean`: `fullSliceABAAvg`, `fullSliceABABAvg`,
  `evaluatedSliceABAAvg`, and `evaluatedSliceABABAvg`.
- Tensor endpoints, consumed by `Main/Auxiliary.lean`:
  `evaluatedSliceABABtensorAvg`, `xEvaluatedSliceBABAtensorAvg`,
  `xEvaluatedFullSliceABABAvg`, and `xEvaluatedFullSliceABABtensorAvg`.
- The paper-facing normalization lemma `normalizationCondition_sandwich_bound` has
  no outside references today, but should remain public.
- Bridge lemmas, mostly consumed by `Main/Auxiliary.lean`:
  `xEvaluatedFullSliceABABAvg_to_xEvaluatedFullSliceABABtensorAvg`,
  `xEvaluatedSliceBABAtensor_to_xEvaluatedFullSliceABABAvg`,
  `fullSliceABAB_to_xEvaluatedFullSliceABABtensorAvg`,
  `fullSliceABAB_to_xEvaluatedSliceBABAtensorAvg`, and
  `xEvaluatedFullSliceABABtensor_to_evaluatedSliceABABAvg`.
- The commutation expansion `fullSliceCommutation_qSDDOp_avg_eq`, consumed by
  `Main/EvaluatedQuestions.lean`.

Because several large helper declarations are currently `private`, a one-shot barrel split
would either have to keep helper/consumer blocks together or deliberately introduce a small
internal API.  The latter should be reviewed carefully to avoid the broad-helper-visibility
nit that PR #850 already encountered.

## Natural line-range seams inside FullSlice

The declaration outline suggests the following paper-aligned blocks.

- Lines 26--287, about 260 LOC: zero full-slice family and the `≤ 1`
  zero-distance bounds.  This is independent and safe to extract first.
- Lines 288--530, about 240 LOC: scalar and tensor average endpoint
  definitions.  This block is mostly definitions, but some private tensor defs feed
  later bridge proofs.
- Lines 531--1555, about 1025 LOC: reindexing, postprocessing, and x/y
  collision marginalization.  This private-heavy block matches paper
  `eq:gcom4-diff` and its y-side analogue.
- Lines 1557--1987, about 430 LOC: normalization and self-consistency
  pullbacks, including `lem:normalization-condition` and the `√ζ` inputs.
- Lines 1988--2180 plus 3153--3209, about 250 LOC: expansion of the
  full-slice qSDD average into `eq:gcomterms`.  This uses public scalar averages
  and can be separated with little helper leakage.
- Lines 2181--3152, about 970 LOC: scalar-to-tensor bridge chain for
  `eq:gcom4` and paper lines 356--360.  This is high-value but coupled to the
  previous private marginalization and self-consistency helpers.

The Lean file tracks `references/ldt-paper/commutativity-G.tex` lines 278--417: first the
`eq:gcomterms` expansion, then `lem:normalization-condition`, then the `eq:gcom4` /
evaluation-at-points chain.  A future code split should preserve this paper order in module
names and docstrings.

## Recommended staged split

A low-risk code follow-up should not make `FullSlice.lean` a pure barrel immediately.  A
safer sequence is:

1. Extract `Transport/FullSlice/ZeroBounds.lean` and let the existing
   `Transport/FullSlice.lean` import it before continuing with the remaining declarations.
   This removes about 260 lines and does not require exposing private helpers.
2. Extract the public scalar endpoint definitions to `Transport/FullSlice/Averages.lean`.
   Leave private tensor helpers in the parent until their consumers move, or move them only
   with the bridge block that uses them.
3. Extract `Transport/FullSlice/CommutationExpansion.lean` for
   `fullSliceCommutation_qSDDOp_avg_eq` and its two local private helpers.  This block uses
   `fullSliceABAAvg` and `fullSliceABABAvg` but does not depend on the marginalization
   bridge chain.
4. Only then split the larger bridge route.  Either keep the private marginalization,
   self-consistency, and scalar-to-tensor lemmas in one `ScalarTensor.lean` child, or create
   a deliberately named internal namespace such as
   `MIPStarRE.LDT.Commutativity.FullSlice.Internal` for shared helper declarations.
5. After all substantive blocks have moved, convert `Transport/FullSlice.lean` into a thin
   barrel importing the child modules in dependency order.

This staged path gives useful reviewable PRs without changing theorem statements or forcing
large visibility changes in the first step.

## Validation expectation for a future code PR

For any non-doc split, preserve declaration names and namespaces for all public API above,
keep `Transport.FullSlice` as the compatibility import, and validate at least:

1. `lake env lean` on every new child module and on
   `MIPStarRE/LDT/Commutativity/Transport/FullSlice.lean`.
2. `lake build MIPStarRE.LDT.Commutativity.Transport.FullSlice` if private helpers cross a
   file boundary or generated oleans look stale.
3. `lake env lean MIPStarRE/LDT/Commutativity/Main/Auxiliary.lean` and
   `lake env lean MIPStarRE/LDT/Commutativity/Main/EvaluatedQuestions.lean` for downstream
   consumers.
4. `git diff --check` and a touched-file `rg -n '\b(sorry|axiom)\b'` check.

This report is docs-only, so the local validation is limited to formatting and diff checks.
