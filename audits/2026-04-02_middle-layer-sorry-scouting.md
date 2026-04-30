---
title: "Middle-layer sorry-site scouting"
date: 2026-04-02
purpose: >
  Scouting report for middle-layer sorry sites and independent proof starting points.
status: snapshot
track: paper2009ldt
kind: scouting-report
---

# Scout Report: Middle-Layer `sorry` Sites

Workspace: repo root (`.`)  
Date: 2026-04-02

## Executive Summary

There are 19 `sorry` sites across the five requested files.

The cleanest independent starters are:

1. `MainInductionStep.restrictedProbabilities`
2. `Commutativity.normalizationCondition`
3. `CommutativityPoints.commutativityPoints`
4. `GlobalVariance.matrixGeneralizeB`

The main dependency chain across the middle layers is:

1. `matrixGeneralizeB`
2. `matrixLocalVarianceOfPoints`
3. `matrixGlobalVarianceOfPoints` once `ExpansionHypercubeGraph.matrixLocalToGlobal` exists
4. `generalizeB`
5. `localVarianceOfPoints`
6. `globalVarianceOfPoints` once `ExpansionHypercubeGraph.localToGlobal` exists
7. `addInU`
8. `selfImprovementHelper`
9. `selfImprovement`
10. `selfImprovementFromSubMeas`
11. `selfImprovementInInductionSection`

A second mostly independent branch is:

1. `commutativityPoints`
2. `normalizationCondition`
3. `commDataProcessedG`
4. `comMain`

The two top-level induction theorems are not ready to be attacked directly:

- `ldPastingInInductionSection` is blocked on later-layer `Pasting.ldPasting`
- `mainInduction` is blocked on `restrictedProbabilities`, `selfImprovementInInductionSection`, `ldPastingInInductionSection`, and the recursive induction hypothesis

## External Blockers

- `GlobalVariance.matrixGlobalVarianceOfPoints` is blocked by `ExpansionHypercubeGraph.matrixLocalToGlobal` at `MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems.lean:30-34`.
- `GlobalVariance.globalVarianceOfPoints` is blocked by `ExpansionHypercubeGraph.localToGlobal` at `MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems.lean:54-59`.
- `SelfImprovement.selfImprovement` is blocked by `MakingMeasurementsProjective.orthonormalization` at `MIPStarRE/LDT/MakingMeasurementsProjective/Theorems.lean:111-123`.
- `MainInductionStep.ldPastingInInductionSection` is blocked by `Pasting.ldPasting` at `MIPStarRE/LDT/Pasting/Theorems.lean:18-33`.

## Statement Issues Worth Fixing First

### 1. `GlobalVariance` abstract theorems are over-generalized

`generalizeB`, `localVarianceOfPoints`, and `globalVarianceOfPoints` all quantify over an arbitrary
`ψbi : QuantumState (ι × ι)` in `MIPStarRE/LDT/GlobalVariance/Theorems.lean:108-137`.

But the paper proofs in `references/ldt-paper/expansion.tex` Section 7.2 are about the strategy state `ψ`.
As written, these Lean statements look too strong: `hgood : strategy.IsGood ...` constrains `strategy.state`,
not an arbitrary `ψbi`.

Recommendation: either replace `ψbi` with `strategy.state`, or add an explicit hypothesis tying `ψbi` to the strategy.

### 2. `SelfImprovement.addInU` currently looks impossible as stated

`AddInUStatement` requires

`H = averagedSandwichedPolynomialSubMeas params strategy T`

at `MIPStarRE/LDT/SelfImprovement/Theorems.lean:164-185`,
but `addInU` takes an arbitrary parameter `H` at `:305-314`.

Unless `H` is definitionally fixed to the averaged sandwiched construction, the theorem cannot be proved.

Recommendation: either

- remove `H` as an explicit argument and define it internally, or
- keep `H` but add `hH : H = averagedSandwichedPolynomialSubMeas ...` as an assumption.

### 3. `helperAgreementOperatorAtPoint` is still a placeholder

`MIPStarRE/LDT/SelfImprovement/Theorems.lean:106-110` defines

`helperAgreementOperatorAtPoint ... := 0`

with a comment that it should be `Σ_a A^u_a ⊗ H_[h(u)=a]`.

That will directly affect the helper boundedness part of `selfImprovementHelper`.

## Per-Site Scouting

## 1. `MIPStarRE/LDT/GlobalVariance/Theorems.lean` (6)

### 1. `matrixGeneralizeB`

- Lean statement: `MIPStarRE/LDT/GlobalVariance/Theorems.lean:85-89`
- Paper reference: `references/ldt-paper/expansion.tex`, `\label{lem:generalize-b}` in Section 7.2
- What it says: matrix-level version of the Schwartz–Zippel argument comparing `[f(u)=g(u)]` with `[f=g|_ℓ]`.
- Difficulty: Medium
- Dependencies:
  - mostly finite-sum/operator bookkeeping
  - Schwartz–Zippel style bound already used elsewhere in the project
  - no dependence on the other five requested files
- Independence: good first target inside this file

### 2. `matrixLocalVarianceOfPoints`

- Lean statement: `MIPStarRE/LDT/GlobalVariance/Theorems.lean:91-97`
- Paper reference: `references/ldt-paper/expansion.tex`, `\label{lem:local-variance-of-points}`
- What it says: matrix-level six-step approximation chain producing the local variance bound.
- Difficulty: Medium
- Dependencies:
  - `matrixGeneralizeB`
  - good-strategy approximation lemmas from earlier layers
  - triangle inequality / `simeq` to `approx` infrastructure
- Independence: blocked only by `matrixGeneralizeB`, not by later middle layers

### 3. `matrixGlobalVarianceOfPoints`

- Lean statement: `MIPStarRE/LDT/GlobalVariance/Theorems.lean:99-105`
- Paper reference: `references/ldt-paper/expansion.tex`, `\label{lem:global-variance-of-points}`
- What it says: convert the local bound into a global bound by the hypercube expansion lemma.
- Difficulty: Medium once prerequisites exist; currently blocked
- Dependencies:
  - `matrixLocalVarianceOfPoints`
  - `ExpansionHypercubeGraph.matrixLocalToGlobal`
- Independence: not independent; currently externally blocked by earlier Section 7 theorem

### 4. `generalizeB`

- Lean statement: `MIPStarRE/LDT/GlobalVariance/Theorems.lean:107-116`
- Paper reference: `references/ldt-paper/expansion.tex`, `\label{lem:generalize-b}`
- What it says: abstract strategy-level packaging of the same comparison as `matrixGeneralizeB`.
- Difficulty: High
- Dependencies:
  - likely a matrix-to-abstract realization bridge, or a direct SDD proof
  - good-strategy facts for axis-parallel lines
- Independence: not blocked by other middle-layer files, but the current statement should probably be repaired to use `strategy.state`

### 5. `localVarianceOfPoints`

- Lean statement: `MIPStarRE/LDT/GlobalVariance/Theorems.lean:118-127`
- Paper reference: `references/ldt-paper/expansion.tex`, `\label{lem:local-variance-of-points}`
- What it says: abstract local variance bound for the points measurements.
- Difficulty: High
- Dependencies:
  - `generalizeB`
  - earlier approximation lemmas from the low-degree test setup
- Independence: blocked by `generalizeB`; also affected by the same `ψbi` over-generalization issue

### 6. `globalVarianceOfPoints`

- Lean statement: `MIPStarRE/LDT/GlobalVariance/Theorems.lean:129-138`
- Paper reference: `references/ldt-paper/expansion.tex`, `\label{lem:global-variance-of-points}`
- What it says: abstract global variance bound via local-to-global expansion.
- Difficulty: High once setup exists; currently blocked
- Dependencies:
  - `localVarianceOfPoints`
  - `ExpansionHypercubeGraph.localToGlobal`
- Independence: not independent; blocked by both the local theorem and the earlier expansion file

## 2. `MIPStarRE/LDT/SelfImprovement/Theorems.lean` (5)

### 7. `selfImprovementHelper`

- Lean statement: `MIPStarRE/LDT/SelfImprovement/Theorems.lean:282-295`
- Paper reference: `references/ldt-paper/self_improvement.tex`, `\label{lem:self-improvement-helper}`
- What it says: build a non-projective submeasurement `H` and witness `Z` from an input measurement `G`.
- Difficulty: Very high
- Dependencies:
  - `sdp`
  - `addInU`
  - `globalVarianceOfPoints`
  - helper boundedness constructions, including the currently placeholder `helperAgreementOperatorAtPoint`
- Independence: central bottleneck in this file; not a good first target

### 8. `sdp`

- Lean statement: `MIPStarRE/LDT/SelfImprovement/Theorems.lean:297-302`
- Paper reference: `references/ldt-paper/self_improvement.tex`, `\label{lem:sdp}`
- What it says: existence of an optimal primal/dual pair with strong duality and complementary slackness.
- Difficulty: Very high
- Dependencies:
  - finite-dimensional SDP duality / Slater condition / complementary slackness formalization
  - the file comment already notes the proof really wants a weaker `SubMeas` primal internally
- Independence: logically independent of the other middle-layer theorems, but hard enough that it should be treated as a parallel deep task, not a warm-up

### 9. `addInU`

- Lean statement: `MIPStarRE/LDT/SelfImprovement/Theorems.lean:304-314`
- Paper reference: `references/ldt-paper/self_improvement.tex`, `\label{lem:add-in-u}`
- What it says: compare the averaged left quantity using `H` with the sandwiched right quantity using `T`.
- Difficulty: High after statement repair
- Dependencies:
  - `globalVarianceOfPoints`
  - Cauchy-Schwarz and submeasurement domination lemmas
  - the statement issue around arbitrary `H`
- Independence: blocked by `GlobalVariance.globalVarianceOfPoints` and by the current theorem statement

### 10. `selfImprovement`

- Lean statement: `MIPStarRE/LDT/SelfImprovement/Theorems.lean:316-328`
- Paper reference: `references/ldt-paper/self_improvement.tex`, `\label{thm:self-improvement}` in the projective-output subsection
- What it says: projectivize the helper output using orthonormalization.
- Difficulty: Medium if prerequisites exist; currently blocked
- Dependencies:
  - `selfImprovementHelper`
  - `MakingMeasurementsProjective.orthonormalization`
- Independence: mostly a wrapper theorem; not worth attempting before those prerequisites

### 11. `selfImprovementFromSubMeas`

- Lean statement: `MIPStarRE/LDT/SelfImprovement/Theorems.lean:334-348`
- Paper reference: no direct paper theorem; this is a formal bridge for `inductive_step.tex`
- What it says: convert the measurement-input theorem into the submeasurement-input form used by the induction section.
- Difficulty: Low to Medium
- Dependencies:
  - `selfImprovement`
  - straightforward rewriting along `hbridge : Gmeas.toSubMeas = G`
- Independence: good cleanup theorem, but only after `selfImprovement`

## 3. `MIPStarRE/LDT/Commutativity/Theorems.lean` (3)

### 12. `commDataProcessedG`

- Lean statement: `MIPStarRE/LDT/Commutativity/Theorems.lean:118-129`
- Paper reference: `references/ldt-paper/commutativity-G.tex`, `\label{lem:comm-data-processed-g}`
- What it says: approximate commutativity for the evaluated slice family `G^x_[g(u)=a]`.
- Difficulty: High
- Dependencies:
  - `CommutativityPoints.commutativityPoints`
  - `normalizationCondition`
  - two internal stability subarguments mirrored by the `stabilityOne` and `stabilityTwo` fields
- Independence: not independent; depends on the pointwise commutativity branch

### 13. `comMain`

- Lean statement: `MIPStarRE/LDT/Commutativity/Theorems.lean:131-142`
- Paper reference: `references/ldt-paper/commutativity-G.tex`, `\label{thm:com-main}`
- What it says: upgrade evaluated commutativity to commutativity of full slice measurements.
- Difficulty: High
- Dependencies:
  - `commDataProcessedG`
  - additional Schwartz–Zippel bookkeeping
  - `normalizationCondition` still appears in the proof of the second term
- Independence: direct successor to `commDataProcessedG`

### 14. `normalizationCondition`

- Lean statement: `MIPStarRE/LDT/Commutativity/Theorems.lean:144-150`
- Paper reference: `references/ldt-paper/commutativity-G.tex`, `\label{lem:normalization-condition}`
- What it says: for `C_{a,b} = Q_b P_a Q_b`, the two square forms agree and are bounded by identity.
- Difficulty: Low
- Dependencies:
  - only local operator algebra from `Commutativity/Defs.lean`
  - projectivity of `Q`
- Independence: excellent first target in this file

## 4. `MIPStarRE/LDT/CommutativityPoints/Theorem.lean` (1)

### 15. `commutativityPoints`

- Lean statement: `MIPStarRE/LDT/CommutativityPoints/Theorem.lean:73-80`
- Paper reference: `references/ldt-paper/commutativity-points.tex`, `\label{thm:commutativity-points}`
- What it says: the point measurements approximately commute on average.
- Difficulty: Medium
- Dependencies:
  - diagonal-lines consistency from `hgood`
  - projectivity of line measurements
  - triangle inequality for the approximation relation
- Independence: conceptually independent of `SelfImprovement` despite the import chain; a good early standalone theorem

## 5. `MIPStarRE/LDT/MainInductionStep/Theorems.lean` (4)

### 16. `mainInduction`

- Lean statement: `MIPStarRE/LDT/MainInductionStep/Theorems.lean:13-26`
- Paper reference: `references/ldt-paper/inductive_step.tex`, `\label{thm:main-induction}`
- What it says: inductively produce a measurement consistent with point answers at dimension `m`.
- Difficulty: Very high
- Dependencies:
  - recursive use of `mainInduction` on restricted slices
  - `restrictedProbabilities`
  - `selfImprovementInInductionSection`
  - `ldPastingInInductionSection`
- Independence: final theorem in this cluster; should be left until the wrappers are in place

### 17. `selfImprovementInInductionSection`

- Lean statement: `MIPStarRE/LDT/MainInductionStep/Theorems.lean:28-40`
- Paper reference: `references/ldt-paper/inductive_step.tex`, `\label{thm:self-improvement-in-induction-section}`
- What it says: induction-section packaging of self-improvement for a submeasurement input.
- Difficulty: Medium
- Dependencies:
  - `SelfImprovement.selfImprovementFromSubMeas`
  - mostly error translation and field repackaging
- Independence: wrapper theorem; blocked by the Section 9 chain

### 18. `ldPastingInInductionSection`

- Lean statement: `MIPStarRE/LDT/MainInductionStep/Theorems.lean:42-58`
- Paper reference: `references/ldt-paper/inductive_step.tex`, `\label{thm:ld-pasting-in-induction-section}`
- What it says: induction-section wrapper around the pasting theorem.
- Difficulty: Low to Medium if pasting exists; currently blocked
- Dependencies:
  - later-layer `Pasting.ldPasting`
  - light repackaging from full Section 12 output to the local induction statement
- Independence: not an immediate target because the later Pasting file is still largely unfinished

### 19. `restrictedProbabilities`

- Lean statement: `MIPStarRE/LDT/MainInductionStep/Theorems.lean:60-67`
- Paper reference: `references/ldt-paper/inductive_step.tex`, `\label{lem:restricted-probabilities}`
- What it says: average failure rates of slice-restricted strategies are controlled by the ambient failure rates.
- Difficulty: Low to Medium
- Dependencies:
  - only the restriction definitions in `MainInductionStep/Defs.lean`
  - straightforward probability/distribution bookkeeping
- Independence: best first target in this file

## Recommended Proof Order

If the goal is fastest progress on unblockers, I would do:

1. Fix the two statement problems:
   - `GlobalVariance` abstract state parameter `ψbi`
   - `SelfImprovement.addInU` arbitrary-`H` issue
2. Prove the easy independent lemmas:
   - `restrictedProbabilities`
   - `normalizationCondition`
   - `commutativityPoints`
   - `matrixGeneralizeB`
3. Finish the rest of the local variance chain:
   - `matrixLocalVarianceOfPoints`
   - then either finish `ExpansionHypercubeGraph.matrixLocalToGlobal` or defer `matrixGlobalVarianceOfPoints`
4. Tackle the abstract variance layer:
   - `generalizeB`
   - `localVarianceOfPoints`
   - `globalVarianceOfPoints`
5. Run the commutativity branch:
   - `commDataProcessedG`
   - `comMain`
6. Run the self-improvement branch:
   - `sdp`
   - `addInU`
   - `selfImprovementHelper`
   - `selfImprovement`
   - `selfImprovementFromSubMeas`
7. Only then revisit the induction wrappers:
   - `selfImprovementInInductionSection`
   - `ldPastingInInductionSection`
   - `mainInduction`

## Best Parallelizable Work

- `restrictedProbabilities`, `normalizationCondition`, `commutativityPoints`, and `matrixGeneralizeB` can all be scouted/proved independently.
- `sdp` is also independent of the variance/commutativity branches, but it is much harder and should be treated as a separate deep task.

## Bottom Line

The most actionable near-term theorem order is:

- `restrictedProbabilities`
- `normalizationCondition`
- `commutativityPoints`
- `matrixGeneralizeB`
- `matrixLocalVarianceOfPoints`

The biggest proof bottlenecks are:

- `sdp`
- `selfImprovementHelper`
- `commDataProcessedG`
- `mainInduction`

The biggest non-proof blockers are:

- the over-generalized `ψbi` parameter in the abstract `GlobalVariance` theorems
- the arbitrary-`H` formulation of `addInU`
- unresolved earlier/later external files: `ExpansionHypercubeGraph`, `MakingMeasurementsProjective`, and `Pasting`
