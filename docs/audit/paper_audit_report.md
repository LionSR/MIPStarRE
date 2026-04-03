# Paper vs Formalization Audit Report

Generated from 6 parallel audits comparing all Lean definitions and theorem
statements against the original paper source (`references/ldt-paper/*.tex`).

## Executive Summary

The audit identified **5 systemic issues** that affect multiple sections:

### ROOT CAUSE 1: Left-Left Tensor Placement (affects ~15 statements)
**Every cross-prover relation should compare `A ⊗ I` vs `I ⊗ B` (liftLeft vs liftRight), but many use liftLeft vs liftLeft.**

Affected files:
- `Test/Strategy.lean`: `axisParallelFailureProbability`, `selfConsistencyFailureProbability`, `diagonalFailureProbability` → all use liftLeft for both sides
- `Test/Strategy.lean`: `IsGood`, `PassesLowIndividualDegreeTest` → inherit wrong predicates
- `Pasting/Statements.lean`: `LdPastingConclusion`, `LdSandwichLineOnePointStatement`, `HBConsistencyStatement`
- `CommutativityPoints/Theorem.lean`: `sampledDiagonalLineConsistency`, `sampledDiagonalLineApproximation`
- `Commutativity/Theorems.lean`: `CommDataProcessedGConclusion.postprocessedPointConsistency`

### ROOT CAUSE 2: Local SSC vs Bipartite SSC (affects ~8 statements)
**The formalization's `qSSCDefect`/`SSCRel` measures local non-projectivity `∑ ev(A²)`, but the paper's SSC measures cross-register overlap `∑ ev(A⊗A)`. We added `BipartiteSSCRel` but haven't propagated it everywhere.**

Affected:
- `Test/Strategy.lean`: `selfConsistencyFailureProbability` uses wrong `sscError`
- `MakingMeasurementsProjective/Theorems.lean`: `orthonormalization` uses `SSCRel`
- `SelfImprovement`: `SelfImprovementHelperConclusion.strongSelfConsistency`
- `MainInductionStep`: `SelfImprovementInInductionSectionConclusion.strongSelfConsistency`
- `Preliminaries/Theorems.lean`: `completingToMeasurement` uses same-side SSC

### ROOT CAUSE 3: GlobalVariance Placeholder Operators (affects ~12 definitions)
**`polynomialWeightSqrtOperator` is hard-coded to `1` instead of `(G_g)^{1/2}`, and `weightedPolynomialState` returns the raw state instead of `(I ⊗ √G_g)|ψ⟩`.**

Affected:
- `GlobalVariance/Defs.lean`: All `weighted*` and `pointConditioned*Variance*` definitions
- `GlobalVariance/Theorems.lean`: `generalizeB`, `localVarianceOfPoints`, `globalVarianceOfPoints`

### ROOT CAUSE 4: Pasting Interpolation Layer (affects ~6 definitions)
**The pasted-measurement interpolation replaces the paper's `h_w`/`|w|≥d+1`/global-consistency filtering with a single fallback polynomial.**

Affected:
- `Pasting/Defs.lean`: `fallbackInterpolatedPolynomial`, `interpolateCompletedSlices`
- `Pasting/Sandwich.lean`: `pastedInterpolationFamily`, `constructedPastedSubMeas`
- `Pasting/Sandwich.lean`: `allOutcomesExpansionFamily`, `fromHToGRecurrence*Family`

### ROOT CAUSE 5: Strategy Structure Limitations
- `SymStrat`/`ProjStrat` force `ι × ι` (equal local spaces) instead of `H_A ⊗ H_B`
- `PermInvState` only has `swap_ev`, not full permutation invariance
- `DiagonalTestSample` uses wrong sample space

## Per-Section Mismatches

### Section 3 — Test Definition (`test_definition.tex`)
| Item | Status | Issue |
|------|--------|-------|
| `mainFormalError` | ✅ MATCH | Constants correct |
| `mainFormal` conclusion | ✅ MATCH | Tensor placement fixed (#137) |
| `mainFormal` hypothesis | ❌ MISMATCH | Uses wrong `PassesLowIndividualDegreeTest` |
| `axisParallelFailureProbability` | ❌ MISMATCH | liftLeft vs liftLeft |
| `selfConsistencyFailureProbability` | ❌ MISMATCH | Local SSC, not bipartite |
| `diagonalFailureProbability` | ❌ MISMATCH | liftLeft + wrong sample space |
| `DiagonalTestSample` | ❌ MISMATCH | Wrong diagonal-line distribution |
| `ProjStrat` | ⚠️ PARTIAL | Forces equal local spaces |

### Section 4 — Preliminaries (`preliminaries.tex`)
| Item | Status | Issue |
|------|--------|-------|
| `consSubMeas` | ✅ MATCH | Correct placement |
| `switchSandwich` | ✅ MATCH | Correct (with added hψ, h𝒟) |
| `twoNotionsOfSelfConsistency` | ✅ MATCH | Uses correct BipartiteSSCRel |
| `completenessTransferProjectiveP` | ✅ MATCH | With added hψ, h𝒟 |
| `simeqToApprox` | ⚠️ PARTIAL | Missing converse "iff" |
| `simeqDataProcessing` | ✅ MATCH | |
| `completingToMeasurement` | ❌ MISMATCH | Uses same-side SSCRel, not bipartite |
| `completeAtOutcome` | ⚠️ PARTIAL | Not paper's standalone completion |

### Section 7 — Expansion (`expansion.tex`)
| Item | Status | Issue |
|------|--------|-------|
| Edge distribution | ✅ MATCH | `rerandomizeCoord` correct |
| `localToGlobal` | ✅ MATCH | Factor m correct |
| `localRewrite` | ⚠️ EQUIV | normalizedTrace vs Tr |
| `globalRewrite` | ❌ MISMATCH | Decomposition not used |
| `combinedOperator` | ❌ MISMATCH | Stores A† not A |
| `GlobalVarianceDecomposition` | ❌ MISMATCH | No orthogonality condition |
| Fourier basis | ⚠️ PARTIAL | Only prime field |

### Section 8 — GlobalVariance (`expansion.tex` continued)
| Item | Status | Issue |
|------|--------|-------|
| `polynomialWeightSqrtOperator` | ❌ MISMATCH | Hard-coded to 1 |
| `weightedPolynomialState` | ❌ MISMATCH | Returns raw state |
| `axisParallelLineQuestionDistribution` | ❌ MISMATCH | Wrong sampling |
| Error constants (24(ε+δ+md/q), etc.) | ✅ MATCH | |
| All downstream variance defs | ❌ MISMATCH | Inherit placeholder |

### Section 6 — Pasting (`ld-pasting.tex`)
| Item | Status | Issue |
|------|--------|-------|
| Sandwich operators | ✅ MATCH | Correct order |
| Error constants | ✅ MATCH | All match |
| `looksEasyButTookMeAWhile` | ✅ MATCH | Proved |
| `LdPastingConclusion` | ❌ MISMATCH | liftLeft for H |
| `LdPastingSubMeasConclusion` | ❌ MISMATCH | σ vs ν error |
| Interpolation layer | ❌ MISMATCH | Not paper's construction |
| `fromHToG` recurrence | ❌ MISMATCH | Collapsed to Unit |
| `overAllOutcomes` | ❌ MISMATCH | Not restricted sum |

### Sections 9-10 — Commutativity (`commutativity-G/points.tex`)
| Item | Status | Issue |
|------|--------|-------|
| `normalizationCondition` | ✅ MATCH | Proved |
| Error constants | ✅ MATCH | |
| Stability families | ❌ MISMATCH | Missing right-side factors |
| Point consistency | ❌ MISMATCH | Same-side placement |
| `diagonalLineProduct{Ordered,Reversed}` | ❌ MISMATCH | Names swapped |

### Section 11 — Self-Improvement (`self_improvement.tex`)
| Item | Status | Issue |
|------|--------|-------|
| SDP primal objective | ❌ MISMATCH | Averaged vs summed |
| `addInU` operators | ❌ MISMATCH | Singleton vs sum over S_u |
| Helper boundedness | ❌ MISMATCH | Placeholder 0 |
| Error constants | ✅ MATCH | |
| `orthonormalization` | ❌ MISMATCH | Wrong SSC hypothesis |

### Section 5 — Naimark (`orthonormalization.tex`)
| Item | Status | Issue |
|------|--------|-------|
| `oneMeasNaimark` scaffold | ⚠️ PARTIAL | 5 sorry, tracked |
| `naimark` | ⚠️ REFORM | Shared algebra, not tensor product |
| `orthonormalization` | ❌ MISMATCH | Wrong SSC hypothesis |

## Priority Fix Plan

### P0 — Correctness Blockers (break the main theorem chain)
1. **Fix test failure predicates** in `Strategy.lean`: change to liftLeft vs liftRight
2. **Fix `completingToMeasurement`**: use `BipartiteSSCRel` instead of `SSCRel`
3. **Implement `polynomialWeightSqrtOperator`**: needs `CFC.sqrt` on PSD operators
4. **Implement `weightedPolynomialState`**: `(I ⊗ √G_g)|ψ⟩`

### P1 — Statement Mismatches (affect downstream proofs)
5. **Fix Pasting tensor placement**: liftLeft → liftRight for H
6. **Fix CommutativityPoints placement**: liftLeft vs liftRight
7. **Fix `addInU` operators**: sum over all of S_u, not singleton
8. **Fix SDP primal**: sum not average
9. **Fix `LdPastingSubMeasConclusion`**: σ → ν for pointConsistency

### P2 — Design Improvements
10. **Fix `DiagonalTestSample`** sample space
11. **Fix `diagonalLineProduct{Ordered,Reversed}`** naming
12. **Fix pasting interpolation layer**
13. **Allow different local spaces** in `ProjStrat`
14. **Strengthen `PermInvState`** beyond `swap_ev`
