---
title: Chapter-by-chapter audit, session 8
date: 2026-04-10
author: AI research assistant
purpose: >
  Records the session-8 chapter-by-chapter LDT audit and preserves the status
  of each chapter's Lean, blueprint, and proof-obligation surface.
status: snapshot
track: paper2009ldt
kind: chapter-audit
---

# MIPStarRE Chapter-by-Chapter Audit — Session 8 (2026-04-10)

## Executive Summary

**Overall status**: 39 sorry sites across 8 files, 0 axioms, 0 sorry-free regressions.
9 files are fully proved (0 sorry). Build passes on main.

| Chapter | Paper File | Lean Directory | Sorry | Paper Match | Grade |
|---------|-----------|---------------|-------|-------------|-------|
| Basic/Infra | introduction.tex + preliminaries.tex | Basic/ | 0 | ~70% | B- |
| Ch3: Preliminaries | preliminaries.tex | Preliminaries/ | 0 | ~80% | B+ |
| Ch4: Self-Improvement | self_improvement.tex | SelfImprovement/ | 0 | ~50% | C |
| Ch5: Orthonormalization | orthonormalization.tex | MakingMeasurementsProjective/ | 12 | ~60% | D+ |
| Ch7: Expansion | expansion.tex §7.1-7.2 | ExpansionHypercubeGraph/ | 0 | ~70% | B- |
| Ch6+7.3: Global Variance | expansion.tex §7.3 + multilinearity.tex | GlobalVariance/ | 4 | ~40% | D |
| Ch8: Commutativity | commutativity-G.tex + commutativity-points.tex | Commutativity/ + CommutativityPoints/ | 5 | ~65% | C+ |
| Ch9: Pasting | ld-pasting.tex | Pasting/ | 13 | ~45% | D |
| Ch10: Inductive Step | inductive_step.tex | MainInductionStep/ | 3 | ~60% | C |
| Ch11: Test/Main Thm | test_definition.tex | Test/ | 3 | ~35% | D- |

**Paper match scoring** considers: statements present, hypotheses correct, proof complete, no extra scaffolding assumptions.

---

## Chapter-by-Chapter Details

### Basic Infrastructure (0 sorry)
**Files**: Basic/{Distribution,Operator,OpFamily,Parameters,SubMeasurement}.lean

| Concept | Status | Issue |
|---------|--------|-------|
| SubMeas / Measurement / ProjMeas / ProjSubMeas | ✅ correct | — |
| Distribution | ⚠️ mismatch | Not normalized (subdistribution) |
| QuantumState | ⚠️ mismatch | PSD matrix + normalized trace, not trace-1 density |
| ConsRel / SDDRel / BipartiteSSCRel | ✅ correct | Defined in Test/Defs.lean, not Basic/ |
| SSCRel | ⚠️ mismatch | Local defect, not paper's bipartite SSC |
| BoundedByOperator | ⚠️ mismatch | Expectation-level, not operator domination |
| Parameters q | ⚠️ mismatch | Only positive, not prime power |

**Action Items**:
1. Document Distribution as subdistribution or add normalization
2. Document QuantumState normalized-trace convention
3. Strengthen BoundedByOperator if downstream proofs need operator-level bound

---

### Chapter 3: Preliminaries (0 sorry) ✅
**Files**: Preliminaries/{Defs,Theorems,CauchySchwarz,Triangles,SelfConsistency,FiniteFields,Polynomials}.lean

**Coverage**: 34 paper items mapped; all proved.

| Issue | Severity |
|-------|----------|
| Missing: low-degree polynomial measurements (polysub/polymeas) | Medium |
| `completeAtOutcome` adds to existing outcome, not fresh ⊥ | Low (cosmetic) |
| `simeqToApprox` forward-only, missing projective converse | Low |
| `otherTwoNotionsOfSelfConsistency` forward-only | Low |
| `twoNotionsOfSelfConsistency` forward-only | Low |
| k-step triangle only has 2-step case | Low |

**Action Items**:
1. Add polynomial measurement definitions if needed by downstream
2. Missing converses are low priority (forward direction is what's used)

---

### Chapter 4: Self-Improvement (0 sorry) ⚠️ Statement Drift
**Files**: SelfImprovement/{Defs,Theorems,MatrixRealization}.lean

| Paper Item | Lean Name | Issue |
|------------|-----------|-------|
| `lem:sdp` | `sdp` | Trivial witness (T=δ_{g0}, Z=1), not actual SDP duality |
| `lem:add-in-u` | `addInU` | Global variance bound only, not full transfer theorem |
| `lem:self-improvement-helper` | `selfImprovementHelper` | Omits ν and G-consistency hypothesis; ignores G |
| `thm:self-improvement` | `selfImprovement` | Extra non-paper `SelfImprovementBridgePackage` assumption |

**Action Items**:
1. **P2**: Document that `sdp`/`addInU` are simplified but sufficient for downstream
2. **P3**: Remove or justify `SelfImprovementBridgePackage` scaffolding
3. Decide if simplified formulations are adequate for the proof chain

---

### Chapter 5: Orthonormalization (12 sorry) 🔴
**Files**: MakingMeasurementsProjective/{Defs,Statements,Theorems,QXPLayer}.lean

| Paper Item | Lean Name | Sorry | Blocker |
|------------|-----------|-------|---------|
| `lem:naimark-helper` | `oneMeasNaimark` | 5 | Unitary extension U construction (#118) |
| `thm:naimark` | `naimark` | 1 | Depends on oneMeasNaimark |
| `thm:orthonormalization` | `orthonormalization` | 1 | Depends on spectralTruncateAlmostProjective |
| `lem:projective-non-measurement` | `projectiveNonMeasurement` | 1 | Projector construction (#197) |
| `lem:projective-low-rank-sum` | `projectiveLowRankSum` | 1 | Rank reduction (#197) |
| `lem:Q-completeness` | `qCompleteness` | 1 | Depends on projectiveLowRankSum |
| `lem:sqrt-Q-completeness` | `sqrtQCompleteness` | 1 | CFC sqrt bridge |
| spectralTruncateAlmostProjective | — | 1 | ProjSubMeas bridge (#279) |

**Action Items**:
1. **P1**: `spectralTruncateAlmostProjective` → unblocks orthonormalization → selfImprovement chain
2. **P2**: Naimark chain (oneMeasNaimark → naimark): 6 sorry, XL effort
3. **P1**: QXP chain (projectiveNonMeasurement → projectiveLowRankSum → qCompleteness → sqrtQCompleteness): 4 sorry

---

### Chapter 7: Expansion of Hypercube (0 sorry in ExpansionHypercubeGraph/) ✅
**Files**: ExpansionHypercubeGraph/{Defs,Theorems,MatrixRealization}.lean

| Issue | Severity |
|-------|----------|
| `laplacianRewrite` is vacuous `rfl` (circular definition) | Medium |
| `laplacianSpectralGap` reformulated, not ordered-eigenvalue | Low |
| `localRewrite`/`globalRewrite` opaque wrapper packaging | Low |
| Stale TODO comments claiming things are still TODO | Low |

**Action Items**:
1. Fix `laplacianRewrite` to be non-vacuous (expose actual edge-difference formula)
2. Clean stale TODOs

---

### Chapter 6/7.3: Global Variance (4 sorry) 🔴
**Files**: GlobalVariance/{Defs,Theorems,MatrixRealization}.lean

| Paper Item | Lean Name | Sorry | Blocker |
|------------|-----------|-------|---------|
| `lem:generalize-b` | `generalizeB` | 1 | **Line-parameter API mismatch** (XL) |
| `lem:local-variance-of-points` | `localVarianceOfPoints` | 2 | Matrix transfer + deviation estimate |
| `lem:global-variance-of-points` | `globalVarianceOfPoints` | 1 | Depends on localVarianceOfPoints |

**Root cause**: Line-parameter normalization mismatch — Lean evaluates at `u(ℓ.direction)` but test API uses affine parameter `t` with `u = ℓ.pointAt t`. Also normalized polynomial averaging vs paper's family sum.

**Action Items**:
1. **P1**: Fix line-parameter API: carry affine `t` explicitly or add conversion lemma
2. **P1**: Fix polynomial averaging: replace normalized `avgOver` with family-sum formulation
3. Then fill the 4 sorry sites

---

### Chapter 8: Commutativity (5 sorry in Commutativity/, 0 in CommutativityPoints/) 🟡
**Files**: Commutativity/{Defs,Theorems}.lean, CommutativityPoints/{Defs,Theorem}.lean

| Paper Item | Lean Name | Sorry | Blocker |
|------------|-----------|-------|---------|
| `lem:comm-data-processed-g` | `commDataProcessedG` | 4 | SDDRel postprocessing bridge + stability claims |
| `thm:com-main` | `comMain` | 1 | Schwartz-Zippel evaluated→full-slice averaging |
| `thm:commutativity-points` | `commutativityPoints` | 0 | ✅ Fully proved |
| `lem:normalization-condition` | `normalizationCondition` | 0 | ✅ Fully proved |

**Action Items**:
1. **P0**: Prove SDDRel postprocessing bridge (unblocks entire pasting chain!)
2. **P0**: Prove stabilityOne/stabilityTwo SDDOpRel bridges
3. **P0**: Schwartz-Zippel averaging for comMain fullSliceCommutation
4. These 5 sorry are on the **critical path** to mainFormal

---

### Chapter 9: Pasting (13 sorry) 🔴🔴
**Files**: Pasting/{Defs,Statements,Sandwich,Theorems}.lean

The most sorry-heavy chapter. All 13 sorry are in Theorems.lean.

| Paper Item | Lean Name | Sorry | Blocker |
|------------|-----------|-------|---------|
| `commutativitySwitcheroo` | — | 1 | Root: aggregate commutation |
| `commutingWithGComplete` | — | 1 | Depends on comMain |
| `gHatFacts` (completedCommutation) | — | 1 | Option×Option quadrant split (heartbeat) |
| `commuteGHalfSandwich` | — | 1 | Depends on gHatFacts |
| `ldSandwichLineOnePoint` | — | 1 | Depends on gHatFacts + sandwich |
| `hBConsistency` | — | 1 | Depends on sandwich chain |
| `hAConsistency` | — | 1 | Depends on hBConsistency |
| `overAllOutcomes` | — | 1 | Root: all-outcomes expansion |
| `fromHToG` | — | 1 | Bernoulli-tail recurrence |
| `chernoffBernoulliMatrix` | — | 1 | Root: matrix Chernoff (XL) |
| `ldPastingNCompleteness` | — | 1 | Depends on above three |
| `ldPastingSubMeas` | — | 1 | Assembly |
| `ldPasting` | — | 1 | Assembly |

**Also**: ~~Placeholder interpolation (Lagrange coeff = 1) in Defs.lean:227.~~ **Resolved**: `interpolateCompletedSlices` now uses Mathlib's `Lagrange.basis` on a `(d+1)`-sized subset and the `lowIndividualDegree` proof is complete (PR #313 fixed the coefficient; the sorry was discharged subsequently). See `audits/2026-04-05_lean-formalization-problems.md` §5 for the remaining downstream correctness obligation.

**Action Items**:
1. **P0**: Fix completedCommutation quadrant split (heartbeat optimization)
2. **P0**: Prove commutativitySwitcheroo (aggregate commutation from slice commutation)
3. **P1**: Sandwich chain (commuteGHalfSandwich → ldSandwichLineOnePoint → hBConsistency → hAConsistency)
4. **P1**: Completeness chain (overAllOutcomes → fromHToG → chernoffBernoulliMatrix → ldPastingNCompleteness)
5. ~~**P2**: Fix placeholder interpolation~~ **Done** (definition faithful, degree bound proven; remaining work is downstream correctness, not the definition)
6. Assembly (ldPastingSubMeas, ldPasting) falls out once chains are done

---

### Chapter 10: Inductive Step (3 sorry) 🟡
**Files**: MainInductionStep/{Defs,Statements,Theorems}.lean

| Paper Item | Lean Name | Sorry | Blocker |
|------------|-----------|-------|---------|
| `thm:main-induction` | `mainInduction` | 1 | Depends on everything else |
| `thm:self-improvement-in-induction-section` | `selfImprovementInInductionSection` | 1 | SubMeas→Measurement completion |
| `lem:restricted-probabilities` | `restrictedProbabilities` | 1 | Diagonal encoding mismatch (#195) |
| `thm:ld-pasting-in-induction-section` | `ldPastingInInductionSection` | 0 | ✅ Proved |

**Action Items**:
1. **P1**: Fix diagonal branch encoding for restrictedProbabilities (#195)
2. **P1**: Thread measurement witness through selfImprovementInInductionSection
3. mainInduction is the final assembly — falls out once others are done

---

### Chapter 11: Test / Main Theorem (3 sorry) 🟡
**Files**: Test/{Defs,Strategy,MainTheorem}.lean

| Paper Item | Lean Name | Sorry | Blocker |
|------------|-----------|-------|---------|
| `thm:main-formal` | `mainFormal` | 1 | Depends on everything |
| leftAsSymmetric | — | 1 | PermInvState witness (S difficulty) |
| rightAsSymmetric | — | 1 | PermInvState witness (S difficulty) |

**Critical issues**:
- Test definition **does not match paper's Figure fig:test** — uses random point on line instead of paper's sampling
- `ProjStrat` forces same local space for both provers
- `IsGood` built from surrogate branch definitions
- Missing: `rem:good-strat-characterization`, j-restricted diagonal test

**Action Items**:
1. **P2**: Fix test definition to match paper sampling procedure
2. **P3**: Prove leftAsSymmetric/rightAsSymmetric (easy once PermInvState is threaded)
3. mainFormal is the final target — depends on all other chapters

---

## Critical Path Analysis

The **longest dependency chain** to `mainFormal`:

```
commDataProcessedG (Ch8, 4 sorry)
  → comMain (Ch8, 1 sorry)  
    → commutingWithGComplete (Ch9, 1 sorry)
      → gHatFacts (Ch9, 1 sorry)
        → commuteGHalfSandwich (Ch9, 1 sorry)
          → ldSandwichLineOnePoint (Ch9, 1 sorry)
            → hBConsistency (Ch9, 1 sorry)
              → hAConsistency (Ch9, 1 sorry)
                → ldPastingSubMeas (Ch9, 1 sorry)
                  → ldPasting (Ch9, 1 sorry)
                    → mainInduction (Ch10, 1 sorry)
                      → mainFormal (Ch11, 1 sorry)
```

**12 sorry on the critical path**. Fixing Ch8 commutativity (5 sorry) unblocks the entire pasting chain.

### Parallel chains that also need completion:
- **Completeness chain** (Ch9): overAllOutcomes → fromHToG → chernoffBernoulliMatrix → ldPastingNCompleteness (4 sorry)
- **Spectral chain** (Ch5): spectralTruncateAlmostProjective → orthonormalization → selfImprovement chain (2 sorry)
- **GlobalVariance chain** (Ch6): generalizeB → localVarianceOfPoints → globalVarianceOfPoints (4 sorry, API fix needed first)
- **Naimark chain** (Ch5): oneMeasNaimark → naimark (6 sorry, independent)
- **QXP chain** (Ch5): projectiveNonMeasurement → projectiveLowRankSum → qCompleteness → sqrtQCompleteness (4 sorry)
- **Restricted probabilities** (Ch10): 1 sorry, needs diagonal encoding fix

---

## Priority Matrix

### P0: Critical Path (must fix to reach mainFormal)
| # | Action | Chapter | Sorry Impact | Difficulty |
|---|--------|---------|-------------|------------|
| 1 | Prove SDDRel postprocessing bridge for commDataProcessedG | Ch8 | -4 | L |
| 2 | Prove Schwartz-Zippel averaging for comMain | Ch8 | -1 | L |
| 3 | Fix completedCommutation quadrant split | Ch9 | -1 | M (heartbeat) |
| 4 | Prove commutativitySwitcheroo | Ch9 | -1 | L |
| 5 | Prove sandwich chain (4 lemmas) | Ch9 | -4 | M |
| 6 | Prove completeness chain (4 lemmas) | Ch9 | -4 | L-XL |

### P1: Required for Full Proof
| # | Action | Chapter | Sorry Impact | Difficulty |
|---|--------|---------|-------------|------------|
| 7 | spectralTruncateAlmostProjective bridge | Ch5 | -1→-2 | L |
| 8 | Fix line-parameter API + fill GlobalVariance | Ch6 | -4 | XL |
| 9 | Fix diagonal encoding + restrictedProbabilities | Ch10 | -1 | L |
| 10 | selfImprovementInInductionSection | Ch10 | -1 | M |
| 11 | QXP chain (4 sorry) | Ch5 | -4 | L-M |

### P2: Important but Independent
| # | Action | Chapter | Sorry Impact | Difficulty |
|---|--------|---------|-------------|------------|
| 12 | Naimark chain (6 sorry) | Ch5 | -6 | XL |
| 13 | Fix test definition to match paper | Ch11 | 0 (statement fix) | M |
| 14 | leftAsSymmetric/rightAsSymmetric | Ch11 | -2 | S |

### P3: Documentation / Cosmetic
| # | Action | Chapter |
|---|--------|---------|
| 15 | Document Self-Improvement simplifications | Ch4 |
| 16 | Fix laplacianRewrite to be non-vacuous | Ch7 |
| 17 | Clean stale TODOs across all files | All |
| 18 | Fix placeholder interpolation in Pasting | Ch9 |
