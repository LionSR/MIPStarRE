# LDT Sorry Elimination — Master Plan

## Wave 1 Results: 5 sorrys eliminated, 3 infrastructure fixes

### Completed
- [x] `QXPLayer.lean:qaRestated` — PROVED (added QXPLayerData fields)
- [x] `QXPLayer.lean:xSquared` — PROVED  
- [x] `QXPLayer.lean:xExpressionToQExpression` — PROVED
- [x] `QXPLayer.lean:xHatSquared` — PROVED
- [x] `MMP/Theorems.lean:orthonormalizationMainLemma_error_bound` — PROVED (added ζ ≤ 1 hyp)
- [x] `Pasting/Theorems.lean:commutingWithGComplete` — FIXED type mismatch
- [x] `SelfImprovement/Theorems.lean` — Updated blocker docs

### Sorry Count: 66 → 61

## Remaining Sorrys (61)

### MakingMeasurementsProjective/QXPLayer.lean (10 remaining)
- [ ] `aLooksProjective` — needs bipartite formulation
- [ ] `projectiveNonMeasurement` — #197 construction
- [ ] `projectiveLowRankSum` — #197 construction
- [ ] `qCompleteness` — #197
- [ ] `sqrtQCompleteness` — #197  
- [ ] `qAlmostProjective` — #197
- [ ] `xTimesXHat` — SVD identity
- [ ] `squaredDifference` — operator inequality
- [ ] `pProjectivity` — projective submeasurement construction
- [ ] `pQApprox` — final approximation

### MakingMeasurementsProjective/Theorems.lean (10 remaining)
- [ ] `oneMeasNaimark` (5 subgoals) — #118 unitary extension
- [ ] `naimark` — blocked on oneMeasNaimark
- [ ] `orthonormalization` — blocked on completion bridge
- [ ] `consistencyToAlmostProjective` — ConsRel bridge
- [ ] `spectralTruncateAlmostProjective` — spectral cutoff
- [ ] `adjustTruncatedProjections` — rounding

### Pasting/Theorems.lean (14)
- [ ] `ldPasting`, `ldPastingSubMeas` — top-level
- [ ] `gCompleteSelfConsistency` — slice SSC conversion
- [ ] `commutativitySwitcheroo` — aggregate commutation
- [ ] `commutingWithGComplete` — has sorry (type fixed)
- [ ] `gHatFacts` (2 subgoals) — Option splitting
- [ ] `commuteGHalfSandwich` — iterated commutation
- [ ] `ldSandwichLineOnePoint` — one-point comparison
- [ ] `hBConsistency` — aggregation
- [ ] `overAllOutcomes` — total mass
- [ ] `fromHToG` — Bernoulli-tail
- [ ] `chernoffBernoulliMatrix` — matrix Chernoff
- [ ] `ldPastingNCompleteness` — combines above

### GlobalVariance/Theorems.lean (10)
- [ ] `matrixGeneralizeB`, `matrixLocalVarianceOfPoints`, `matrixGlobalVarianceOfPoints` — matrix transfer
- [ ] `generalizeB` (2 subgoals) — pointwise + aggregate
- [ ] `localVarianceOfPoints` (3 subgoals) — local variance
- [ ] `globalVarianceOfPoints` (2 subgoals) — global variance

### Commutativity/Theorems.lean (5)
- [ ] `commDataProcessedG` (4 subgoals) — SDDOpRel bridges
- [ ] `comMain:fullSliceCommutation` — lift to full-slice

### SelfImprovement/Theorems.lean (4) — BLOCKED
- [ ] `selfImprovementHelper` — blocked on sdp + addInU
- [ ] `sdp` — needs SDP infrastructure
- [ ] `addInU` — statement issue (quantifies over arbitrary H)
- [ ] `selfImprovement` — blocked on helper + orthonormalization

### MainInductionStep/Theorems.lean (4) — BLOCKED
- [ ] `mainInduction` — blocked on everything
- [ ] `selfImprovementInInductionSection` — needs measurement witness
- [ ] `ldPastingInInductionSection` — cyclic import
- [ ] `restrictedProbabilities` — modeling mismatch

### ExpansionHypercubeGraph/Theorems.lean (3)
- [ ] `matrixLocalToGlobal` — expansion inequality
- [ ] `matrixLocalRewrite` — trace identity
- [ ] `matrixGlobalRewrite` — trace identity

### Test/MainTheorem.lean (1) — BLOCKED
- [ ] `mainFormal` — depends on everything

## PR Groups
- **PR 1 (CREATED)**: MMP + Pasting + SelfImprovement fixes
- **PR 2 (NEXT)**: GlobalVariance averaging lemma + proofs  
- **PR 3 (NEXT)**: ExpansionHypercubeGraph matrix proofs
- **PR 4 (FUTURE)**: Commutativity SDDOpRel bridges
- **PR 5 (FUTURE)**: Deep math proofs (Naimark, orthonormalization, pasting)
