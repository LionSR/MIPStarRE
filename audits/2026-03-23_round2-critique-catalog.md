---
title: Round 2 critique catalog
date: 2026-03-23
author: AI research assistant
purpose: >
  Catalogs the second round of LDT formalization critiques and records which
  findings require follow-up in Lean, blueprint, or documentation.
status: snapshot
track: paper2009ldt
kind: critique-catalog
---

# Round 2 Critique Catalog

## Batch 1 — Blueprint chapters (e8b1cc138133)
### S0 (verified correct): 6 comments
- thm:main-formal: all constants match ✅
- lem:global-variance-of-points: coefficient 24m ✅
- thm:com-main: Schwartz–Zippel removals ✅
- lem:truncated-type-sum-recurrence: recurrence ✅
- thm:self-improvement-in-induction-section: completion reduction ✅
- thm:main-formal proof cascade: ζ₁…ζ₄ and prefactor ✅

### S3 (compresses real work): 1 comment
1. **ch09_pasting / lem:over-all-outcomes**: Key source argument hidden — linewise consistency event, unique interpolant h*, Schwartz–Zippel at index i* not outlined.

### S4: 0 comments

---

## Batch 2 — Lean §3/4/6 (184bafce9fd7)
### S0: 3 comments
- mainFormalError and k≥md matched the printed source at the time; superseded by
  issue #906, which records that the proof needs the stronger k≥400md condition.
- simeqDataProcessing restored to IndexedSubMeasurement ✅
- CompletingToMeasurementStatement error bound correct ✅
- mainInductionNu/Error arithmetic was verified; the k-bound audit is superseded
  by issue #906.

### S4 (wrong or missing key hypothesis): 7 comments
1. **Section3Test / Fq carrier**: Still `Fin q` not actual GaloisField; `PrimePowerFieldSpec` not threaded into definitions.
2. **Section3Test / QuantumState**: Single-register, no bipartite tensor, Measurement/ProjectiveMeasurement carry no semantic axioms.
3. **Section3Test / comparison layer**: `questionConsistencyDefect`, failure probabilities all hard-coded to 0 — theorems vacuously true.
4. **Section3Test / postprocess**: Creates placeholder operator instead of summing matching outcomes; `evaluateAt` doesn't encode G_{[g(u)=a]}.
5. **Section4 / BipartiteStateDependentDistanceRel**: No tensor-placement content; uses one-sided defect.
6. **Section4 / OperatorBetweenZeroAndOne**: Compares against global `identityOperator` of dim 1 instead of `identityLike B`.
7. **Section6 / averagedPointEvaluationOperator**: Still placeholder; boundedness clauses don't express actual operator inequalities.
8. **Section6 / SelfImprovementConclusion**: `BoundedByOperator` and `selfCloseness` don't encode the source relations.

---

## Batch 3 — Lean §5/7/8/9 (c49cb21dc226)
### S0: 3 comments
- eigenvectors eigenvalue and gap verified ✅
- orthonormalization constant 100ζ^{1/4} verified ✅
- Section 8 error coefficients match ✅

### S3: 2 comments
1. **Section5 / orthonormalization proof**: Black-boxes R_a→Q_a→X,X̂/SVD chain.
2. **Section7 / exported theorems**: Formal statements in placeholder terms, no bridge to matrix realizations.

### S4: 5 comments
1. **Section5 / Naimark witness**: Single ambient matrix space, not explicit bipartite tensor-product model.
2. **Section7 / A_comb normalization**: Lean uses average instead of unnormalized sum; changes trace identities.
3. **Section7 / combined operator**: Matrix witness uses ⟨u|⟨u| ⊗ A^u instead of column operator; wrong quadratic forms.
4. **Section8 / weighted state**: matrixPolynomialWeightSqrtOperator = G_g (no square root); tensor-factor placement missing.
5. **Section8 / answer space**: Line/polynomial answers are arbitrary functions, not degree-bounded; enlarges Schwartz–Zippel domain.

---

## Batch 4 — Lean §10/11/12 (58ddf9e13843)
### S0: 5 comments
- pointMeasurementProductRight ordering fix verified ✅
- CommutativityPointsStatement five-step bridge verified ✅
- CommDataProcessedGConclusion internal stability outputs verified ✅
- ldDnoteq TV bound k²/q verified ✅
- gHatSandwichFamily matches source ✅
- ldPastingCompletenessLowerBound uses raw ν ✅

### S3: 1 comment
1. **Section10 / distributions**: pointWithDiagonalLineDistribution and pointPairSharedDiagonalLineDistribution are named placeholders; non-trivial marginal calculation not encoded.

### S4: 9 comments
1. **Section11 / normalizationConditionSandwichedTotalOperator**: Placeholder, not ∑_b Q_b P_a Q_b.
2. **Section11 / normalizationCondition**: Statement about placeholder operators, not actual sandwiched sums.
3. **Section12 / distinctTupleDistribution**: Named placeholder, not uniform on distinct tuples.
4. **Section12 / averageIndexedSubMeasurement**: Forgets distribution and family; core semantic gap.
5. **Section12 / verticalLineMeasurementFamily**: Ignores strategy and base point; breaks line connection.
6. **Section12 / interpolateCompletedSlices**: Picks first non-none slice, not paper's type-weight-filtered sum.
7. **Section12 / constructedPastedMeasurement**: Total overwritten to I; not paper's completion.
8. **Section12 / suffixBernoulliWeightOperator**: Placeholder can't support recurrence identities.
9. **Section12 / bernoulliTailOperator**: Name only; spectral reduction not formalized.
10. **Section12 / overAllOutcomes**: Missing good-strategy/consistency/boundedness hypotheses.
11. **Section12 / fromHToG + ldPastingNCompleteness**: Arbitrary ν; stronger than source.

---

## Summary by severity
| Severity | Batch 1 | Batch 2 | Batch 3 | Batch 4 | Total |
|----------|---------|---------|---------|---------|-------|
| S0 ✅    | 6       | 4       | 3       | 6       | 19    |
| S3 ⚠️    | 1       | 0       | 2       | 1       | 4     |
| S4 ❌    | 0       | 8       | 5       | 11      | 24    |

**Total actionable (S3+S4): 28 items**
