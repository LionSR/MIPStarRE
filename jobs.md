# LDT Sorry Elimination — Status Report

Last updated: 2026-05-07

## Progress Summary

- **Started**: 66 sorrys across 9 files in `MIPStarRE/LDT/`
- **Current**: 1 executable sorry — `Test/MainTheorem/MainFormal.lean:mainFormal`
- **Eliminated**: 65 executable sorrys
- **Infrastructure fixes landed on this branch**:
  - `SymStrat.IsGood` and `RestrictedSymStrat.IsGood` now carry `PermInvState`
  - shared `SliceBoundednessInput` for Section 11/12 theorem interfaces
  - averaged point-operator defs moved out of induction-local scope
  - removed all `BridgePackage` wrappers; missing obligations are now explicit
    theorem hypotheses on the Section 5/8/10 wrappers

---

## Current Sorry Inventory

| Module | Declaration | Blocker |
|--------|-------------|---------|
| `Test/MainTheorem/MainFormal.lean` | `mainFormal` | Missing Section 3 assembly (the pipeline from `strategy.PassesLowIndividualDegreeTest eps` through symmetrization, self-improvement, spectral truncation, orthonormalization, commutativity, and pasting to produce the final projectivized witness) |

---

## Active Wave: Test

- **Owner**: OpenCode
- **Scope**: `MIPStarRE/LDT/Test/*.lean`
- **Live executable sorrys**: 1 (`Test/MainTheorem/MainFormal.lean:mainFormal`)
- **Status**: BLOCKED ON UPSTREAM SECTION 3/5/8/12 GAPS
- **State of surrounding theorems**:
  - `Test/Strategy.lean` is paper-faithful: point agreement is the
    self-consistency branch; the role-register symmetrized strategy is proved
    `(3 * eps, 3 * eps, 3 * eps)`-good.
  - `d = 0` / `k = 0` corner is excluded in Lean and blueprint.
  - `Test.classicalTestSoundness` closes through `polishchukSpielmanClassicalSoundness`.
  - `Test.razSafra` closes against the current `SurfaceVsPointPassCondition` /
    `PointAnswerSoundnessConclusion` interface.
- **Concrete blockers**:
  1. No theorem on the current proof path derives the Section 5/8/10 wrapper
     hypotheses directly from `strategy.PassesLowIndividualDegreeTest eps`.
     The `BridgePackage` wrappers are gone; the missing obligations now surface
     as explicit hypotheses, but no constructor for them exists yet.
  2. The geometric-line canonicalization is not on the live proof path; the
     commutativity bridge is proved only for the older raw
     `PointDiagonalLineQuestion = DiagonalLine × Fq` model.  A paper-faithful
     fix requires canonicalizing the commutativity line-question model together
     with the Test-side line model.
  3. `SpectralTruncationStatement` and `spectralTruncateAlmostProjective` overshoot
     the paper: the paper's spectral truncation step only yields a projective
     family `R_a` with `∑_a R_a ≤ (1 + 2 * sqrt ζ) I`, not a genuine `ProjSubMeas`.
     A paper-faithful Section 5 repair needs to refactor this statement back to
     the raw projective-family / total-bound form and rebuild the later adjustment
     step honestly.
- **Checklist**:
  - [x] Survey all `sorry`s in `MIPStarRE/LDT/Test`
  - [x] Confirm the only live `sorry` in scope is `mainFormal`
  - [x] Resolve the Test-level failure-surrogate mismatch
  - [x] Replace stale left/right surrogate goals with paper-faithful symmetrized goodness transfer
  - [x] Exclude the degenerate `d = 0` / `k = 0` corner from `mainFormal` / `mainInformal`
  - [x] Eliminate `mainInformal`
  - [x] Close placeholder `razSafra` wrapper
  - [x] Remove `BridgePackage` wrappers on the `mainFormal` dependency path
  - [ ] Repair the top-level Test model so sampled line questions use unique
    geometric representatives
  - [ ] Eliminate `mainFormal`
  - [ ] Sync blueprint `\leanok` tags once `mainFormal` is proved
- **Best next step**:
  - Prove the Section 5/8/10 wrapper hypotheses directly, or replace those wrapper
    surfaces with the real theorems, without adding new assumptions to `mainFormal`.
  - A natural first sub-target: refactor `SpectralTruncationStatement` back to the
    raw projective-family / total-bound form, then rebuild the late-stage repair.

---

## Active Strategy

- `Test.mainFormal` is the sole remaining sorry.  `Test/Strategy.lean` is
  paper-faithful and complete.
- The active global target is completing the Section 3 assembly: bridge from
  `strategy.PassesLowIndividualDegreeTest eps` through the self-improvement /
  projectivization / commutativity / pasting pipeline.
- The highest-leverage upstream work is any repair or replacement of the
  still-explicit bridge-package hypotheses on the Section 5/8/10 wrappers.

---

## Completed Waves

### MakingMeasurementsProjective Wave — COMPLETED (for this pass)

- Bridge packages (`SpectralTruncationBridgePackage`, `ProjectivizationRepairPackage`,
  `OrthonormalizationBridgePackage`) now stand in for the unformalized spectral
  construction and late repair stages.
- `spectralTruncateAlmostProjective` and `orthonormalization` have no local `sorry`s
  on the current branch; their remaining mathematical debt is isolated in the bridge
  packages.
- **Outstanding concern**: `SpectralTruncationStatement` still overshoots the paper
  (see Active Wave blockers above).

### Pasting Wave — COMPLETED

- All pasting sorrys are eliminated.
- `commutativitySwitcheroo`, `ldGbcon`, `commuteGHalfSandwich`, `hBConsistency`,
  `hAConsistency`, `truncatedTypeSumRecurrence`, `gCompleteSelfConsistency`,
  `commutingWithGComplete`, `gHatFacts`, `ldPastingNCompleteness` are all proved.
- `BridgeLemmas.lean` carries the paper-faithful one-point sandwich, all-outcomes,
  and half-sandwich flat-chain commutation proofs.
- The Section 12 consistency chain explicitly threads `0 < params.d`.
- See `proof-guide-bridge-lemmas-sorry-elim.md` for the Chapter 9 paper fragment
  and Lean proof spine.

### Commutativity Wave — COMPLETED

- All executable placeholders in `MIPStarRE/LDT/Commutativity` are eliminated.
- `normalizationCondition_sandwich_bound`, `fullSliceCommutation_qSDDOp_avg_eq`,
  `evaluatedSlice_scalar_chain_bound`, `fullSlice_scalar_marginalize_x`,
  `fullSlice_scalar_marginalize_y`, `fullSlice_closenessOfIP_CAB_hEval` are all proved.
- Blueprint tags in `ch08_commutativity.tex` still need syncing (`\leanok`).

### CommutativityPoints Wave — COMPLETED

- `sampledDiagonalLineApproximation_pointWithDiagonalLine` proved by reindexing
  `RestrictedDiagonalSample(last) × Fq` onto `PointDiagonalLineQuestion` via a
  rebased-line equivalence and transporting with `DiagonalEvaluationReparamInvariant`.
- No executable `sorry`s remain under `MIPStarRE/LDT/CommutativityPoints`.

### Preliminaries Wave — COMPLETED

- `completionMissingMassBound` proved with the paper-faithful `hψ : ψ.IsNormalized`
  hypothesis.
- `\leanok` added for `lem:completion-missing-mass-bound` in
  `blueprint/src/chapter/ch03_preliminaries.tex`.
- No `sorry`s remain anywhere under `MIPStarRE/LDT/Preliminaries`.

### MainInductionStep Wave — COMPLETED

- `restrictedProbabilities` proved via a direct reindexing proof over
  `Point params.next ≃ Point params × Fq params`.
- `mainInduction` proved; the `MainInductionBridgePackage` used in earlier passes
  was removed by PR #640.
- No `sorry`s remain anywhere under `MIPStarRE/LDT/MainInductionStep`.

### GlobalVariance Wave — COMPLETED

- `generalizeB`, `localVarianceOfPoints`, and `globalVarianceOfPoints` aggregate
  SDDRel subgoals proved.
- Matrix-realization transfer theorems (`matrixGeneralizeB`, `matrixLocalVarianceOfPoints`,
  `matrixGlobalVarianceOfPoints`) proved.
- No `sorry`s remain anywhere under `MIPStarRE/LDT/GlobalVariance`.

### ExpansionHypercubeGraph Wave — COMPLETED

- `matrixLocalToGlobal`, `matrixLocalRewrite`, and `matrixGlobalRewrite` proved.
- No `sorry`s remain anywhere under `MIPStarRE/LDT/ExpansionHypercubeGraph`.

### SelfImprovement Wave — COMPLETED

- `selfImprovementHelper`, `sdp`, `addInU`, and `selfImprovement` proved.
- No `sorry`s remain anywhere under `MIPStarRE/LDT/SelfImprovement`.

---

## Files Now Clean

All `MIPStarRE/LDT/` files are now sorry-free except
`Test/MainTheorem/MainFormal.lean`.  Key cleaned modules include:

- `MakingMeasurementsProjective/Projectivization.lean`
- `MakingMeasurementsProjective/QXPLayer.lean`
- `MakingMeasurementsProjective/Theorems.lean`
- `SelfImprovement/Theorems.lean`
- `ExpansionHypercubeGraph/Theorems.lean`
- `MainInductionStep/Theorems.lean`
- `Commutativity/` (entire directory)
- `CommutativityPoints/` (entire directory)
- `Preliminaries/` (entire directory)
- `Pasting/` (entire directory)
- `GlobalVariance/` (entire directory)

---

## Known Remaining Mathematical Debt

1. **`Test/MainTheorem/MainFormal.lean:mainFormal`** — the top-level theorem.
   Requires completing the entire Section 3 assembly (see Active Wave above).

2. **Bridge packages in `MakingMeasurementsProjective/`** —
   `SpectralTruncationBridgePackage`, `ProjectivizationRepairPackage`, and
   `OrthonormalizationBridgePackage` are still mathematical placeholders standing
   in for unformalized spectral construction and late-stage repair steps.

3. **Blueprint `\leanok` gaps** — Tags in `ch08_commutativity.tex` and
   `ch09_pasting.tex` are still incomplete.

---

## PRs Created

| PR | Branch | Scope | Sorrys eliminated |
|----|--------|-------|-------------------|
| #240 | `feat/ldt-sorry-elimination-wave1` | `QXPLayer.lean`, `MMP/Theorems.lean` | 5 (`qaRestated`, `xSquared`, `xExpressionToQExpression`, `xHatSquared`, `orthonormalizationMainLemma_error_bound`) |
| #241 | `feat/ldt-sorry-elimination-wave2` | `QXPLayer.lean`, `GlobalVariance/` | 4 (`aLooksProjective`, three aggregate SDDRel subgoals) |
| #327 | `fix/LDT/MainInductionStep` | `MainInductionStep/Theorems.lean` | 2 (`restrictedProbabilities`, `mainInduction`) |
| #331 | `fix/LDT/Test` | `Test/MainTheorem.lean` | 0 (updated after review; no longer claims to eliminate `mainFormal`) |
| #333 | `fix/pasting-consistency-transport` | `Pasting/`, `Preliminaries/` | Pasting transport scaffold and first pasting sorrys |

