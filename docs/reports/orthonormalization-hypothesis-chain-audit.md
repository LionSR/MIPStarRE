# Historical OrthonormalizationInput Extra-Hypothesis Chain Audit

**Issue:** #1359  
**Date:** 2026-05-07  
**Scope:** Read-only trace from `MakingMeasurementsProjective/Orthonormalization.lean` through `SelfImprovement`, `MainInductionStep`, to final assembly in `Test/MainTheorem/MainFormal.lean`.

> **Status note, 2026-05-11.**  This report predates the source-faithful
> `mainFormal` repair.  References to an external `hbaseBridge` hypothesis at
> the final theorem should now be understood as references to the conditional
> helper that existed at the time of the report, not to the paper-facing theorem
> `mainFormal`.  The subsequent MainFormal cleanup removes the live repaired
> bridge route; the current cleanup direction is to prove the internal
> obligations for the match-mass base bridge and successor residual, not to add
> these inputs to
> source-labelled theorem statements.

## Executive Summary

The `thm:orthonormalization` theorem at `MakingMeasurementsProjective/Orthonormalization.lean:394` takes `OrthonormalizationInput ψ A ζ` as an extra hypothesis beyond the paper statement (which only requires `BipartiteSSCRel`). The spectral-truncation slice of this input is **fully proved**; the repair slice (locality-preserving QXP repair) is **still a hypothesis** at all levels up to the final `mainFormal` assembly.

At the final assembly (`MainFormal.lean:507`), the base case (m=1) is discharged through the external `hbaseBridge` hypothesis, while the successor case (m>1) has a single `sorry` (line 611). This `sorry` represents the lack of a predecessor per-slice induction package and per-slice self-improvement bridge inputs.

---

## 1. Definitions at Each Level

### Level 1: MakingMeasurementsProjective (`Statements.lean`)

**`OrthonormalizationInput`** (line 216-229):
```lean
structure OrthonormalizationInput {Outcome : Type*} {ι : Type*}
    (ψ : QuantumState (ι × ι)) (A : SubMeas Outcome ι) (ζ : Error) where
  spectral : 
    let Ahat := optionCompletion A
    SpectralTruncationInput ψ (leftLiftedMeasurement Ahat)
      (consistencyToAlmostProjectiveError (2 * ζ))
  repair : 
    let Ahat := optionCompletion A
    LeftLiftedProjectivizationRepairInput ψ Ahat
      (consistencyToAlmostProjectiveError (2 * ζ))
```

This wraps two sub-hypotheses on the **option-completed** measurement at doubled error:

- **`SpectralTruncationInput`** (line 120-126) = `ψ.IsNormalized → (∑ ev ψ(A_a - A_a²) ≤ ζ) → SpectralTruncationStatement`
- **`LeftLiftedProjectivizationRepairInput`** (line 156-163) = takes `SpectralTruncationStatement` → returns `ProjSubMeas Outcome ι` with rounding via `ProjSubMeas.liftLeft P`

The paper statement (`thm:orthonormalization`, `references/ldt-paper/orthonormalization.tex`, line 67) only requires `BipartiteSSCRel` on the submeasurement.

### Level 2: SelfImprovement (`Theorems/Statements.lean`)

**`SelfImprovement.OrthonormalizationInput`** (line 436-443):
```lean
abbrev OrthonormalizationInput (params) (strategy) (eps delta) :=
  ∀ {Hhat}, BipartiteSSCRel ... Hhat (selfImprovementHelperError ...) →
    MakingMeasurementsProjective.OrthonormalizationInput
      strategy.state Hhat (selfImprovementHelperError ...)
```

This lifts the per-submeasurement `OrthonormalizationInput` to a `∀`-quantified input for each helper family `Hhat`.

**Bridge obligations** (`OrthonormalizationBridge.lean`):
- **`orthonormalizationInput_of_obligations`** (line 684): combines `OrthonormalizationSpectralObligation` + `OrthonormalizationRepairObligation` → full `OrthonormalizationInput`
- **Spectral obligation**: `orthonormalizationSpectralObligation_of_sourceAlmostProjective` (line 851) — **FULLY PROVED** via `spectralTruncationInput_of_sourceAlmostProjective`
- **Repair obligation**: `OrthonormalizationRepairObligation` (line 129-139) — **STILL HYPOTHESIS**: calls `LeftLiftedProjectivizationRepairInput` on `optionCompletion Hhat`

### Level 3: MainInductionStep (`SelfImprovementBridge/Core.lean`)

**`selfImprovementInInductionSection`** (line 65) takes `SelfImprovement.OrthonormalizationInput` as hypothesis and calls `selfImprovementFromSubMeas`.

**`SelfImprovementPackage.SliceBridgeInputs.ofOrthonormalizationRepair`** (line 456-505) builds per-slice bridge from:
- `HelperStrongSelfConsistencyInput` — hypothesis
- `OrthonormalizationRepairObligation` — hypothesis (= `repair x`)
- `FinalFieldsInput` — hypothesis

### Level 4: Test/MainTheorem (MainFormal)

**`MainFormalPostRolePackageDiagonalOrthonormalizationInput`** (`OrthonormalizationData.lean:99-126`) — used at final assembly:
```lean
structure MainFormalPostRolePackageDiagonalOrthonormalizationInput ... where
  leftSpectral  : SpectralTruncationInput ... (leftLiftedMeasurement ... unsymmetrizedLeftPOVM ...) ...
  leftRepair    : LeftLiftedProjectivizationRepairInput ... unsymmetrizedLeftPOVM ...
  rightSpectral : SpectralTruncationInput ... (leftLiftedMeasurement ... unsymmetrizedRightPOVM ...) ...
  rightRepair   : LeftLiftedProjectivizationRepairInput ... unsymmetrizedRightPOVM ...
```

**Key difference from Level 1**: This is on the **uncompleted** POVMs (measurements, not submeasurements), so no option-completion is needed. The error is `consistencyToAlmostProjectiveError scalars.zeta1` (not doubled). The spectral fields are filled by `spectralTruncationInput_of_sourceAlmostProjective` (proved). The repair fields are `LeftLiftedProjectivizationRepairInput` directly — the same underlying QXP repair.

---

## 2. Hypothesis Status Map

### Spectral Truncation

| Level | Definition | Status |
|---|---|---|
| MakingMeasurementsProjective | `SpectralTruncationInput` | **Proved** via `spectralTruncationInput_of_sourceAlmostProjective` (`ProjectiveNonMeasurement.lean:749`) |
| SelfImprovement | `OrthonormalizationSpectralObligation` | **Proved** via `orthonormalizationSpectralObligation_of_sourceAlmostProjective` (`OrthonormalizationBridge.lean:851`) |
| MainTheorem | `leftSpectral / rightSpectral` | **Proved** via `spectralTruncationInput_of_sourceAlmostProjective` applied to unsymmetrized POVMs (`OrthonormalizationData.lean:156-169`) |

### Locality-Preserving Repair (QXP Repair)

| Level | Definition | Status |
|---|---|---|
| MakingMeasurementsProjective | `LeftLiftedProjectivizationRepairInput` | **HYPOTHESIS** — takes `SpectralTruncationStatement` → returns `ProjSubMeas` with `RoundedProjMeasStatement` on `ProjSubMeas.liftLeft P` |
| SelfImprovement | `OrthonormalizationRepairObligation` | **HYPOTHESIS** — `∀ Hhat, BipartiteSSCRel ... → LeftLiftedProjectivizationRepairInput ... (optionCompletion Hhat)` |
| MainInductionStep | `SelfImprovement.OrthonormalizationInput` | **HYPOTHESIS** — flows through `selfImprovementInInductionSection` → `selfImprovement` → `orthonormalization` |
| MainTheorem | `leftRepair / rightRepair` | **HYPOTHESIS** — bundled in `MainFormalPostRolePackageDiagonalOrthonormalizationInput` |

### Match-Mass Preservation

| Level | Definition | Status |
|---|---|---|
| MainTheorem | `OrthonormalizationMatchMassPreservation` | **OBLIGATION** — bundled in `MainFormalBaseProjectiveCompletionObligations` / `MainFormalBaseCompletionObligations` |

---

## 3. The Single `sorry` (MainFormal.lean:611)

```lean
have hprojectiveCompletionResidual :
    Nonempty (MainFormalCascadeRolePackageResidualProjectiveCompletionResidual
      ... params strategy eps hpass k scalars) := by
  -- Successor case (m > 1): the answer-valued recursive-slice adapter is
  -- available, but this theorem still has no predecessor per-slice induction
  -- package or answer-side self-improvement bridge inputs in scope.
  -- TODO(#931, #834, #422): supply those successor inputs and assemble the
  -- resulting role residual into a Step 6 witness residual.
  sorry
```

### What the `sorry` Must Produce

`Nonempty (MainFormalCascadeRolePackageResidualProjectiveCompletionResidual ...)`, which contains:

1. **`roleResidual : MainFormalRolePackageResidual`** — the Section 6 residual:
   - Contains `roleMeasurement : Measurement (Polynomial params) (Role × ι)`
   - Contains `section6Consistency : ConsRel ...` at `mainInductionError params k (3*eps) (3*eps) (3*eps)`
   - For base case: constructed from `strategySymmetrization_mainInductionBaseCase` (proved)
   - For successor case: needs `mainFormalSuccessorMainInductionPublicWrapper` which requires:
     - `MainFormalSuccessorBoundary` containing:
       - `MainFormalSuccessorRecursiveSlices` — per-slice induction packages
       - `MainFormalSuccessorSelfImprovementObligation` — per-slice self-improvement inputs

2. **`postRoleDiagonalCompletion : MainFormalPostRolePackageDiagonalCompletionResidual`** — the completion residual:
   - Built from `MainFormalPostRolePackageDiagonalOrthonormalizationInput` (contains the QXP repair hypotheses)
   - Plus `OrthonormalizationMatchMassPreservation` for both sides

### Concrete Missing Pieces

To fill the `sorry`, the successor branch needs:

| Missing Input | Type | Description |
|---|---|---|
| Per-slice induction package | `MainInductionStep.PerSliceInductionPackage params strategy (3*eps) (3*eps) (3*eps) restriction k` | The recursive induction data for each Fq-slice of the restricted strategy |
| Per-slice self-improvement bridge | `MainInductionStep.SelfImprovementPackage params ...` or equivalently `SelfImprovementPackage.SliceBridgeInputs params ...` | Honest slice strategies, measurement transport, and Section 9 bridge inputs (helper SSC + orthonormalization + finalFields) |
| Orthonormalization repair inputs | `LeftLiftedProjectivizationRepairInput` × 2 | Locality-preserving QXP repair for both unsymmetrized POVMs (one per side) |
| Match-mass preservation | `OrthonormalizationMatchMassPreservation` × 2 | For both Alice and Bob sides |

Equivalent higher-level packaging: `MainFormalSuccessorBoundary` which bundles:
- `MainFormalSuccessorRecursiveSlices` (per-slice induction packages)
- `MainFormalSuccessorSelfImprovementObligation` (per-slice self-improvement bridge data)

Plus the former `MainFormalRepairedBridgeHypotheses` route, now replaced by
`MainFormalBaseCompletionObligations`, which bundles the orthonormalization and
match-mass inputs.

---

## 4. Call Chain Diagram

```
MainFormal.lean (line 611 → sorry)
  │
  ├─ Needs: MainFormalCascadeRolePackageResidualProjectiveCompletionResidual
  │   │
  │   ├─ roleResidual: MainFormalRolePackageResidual
  │   │   │
  │   │   └─ ofSuccessorBoundary / mainFormalSuccessorMainInductionPublicWrapper
  │   │       └─ MainFormalSuccessorBoundary
  │   │           ├─ MainFormalSuccessorRecursiveSlices ← MISSING
  │   │           └─ MainFormalSuccessorSelfImprovementObligation ← MISSING
  │   │               └─ ∀ perSliceInduction,
  │   │                   SelfImprovementPackage.SliceBridgeInputs
  │   │                   └─ helper SSC + OrthonormalizationInput + finalFields
  │   │                       └─ OrthonormalizationInput
  │   │                           ├─ SpectralTruncationInput ← PROVED
  │   │                           └─ LeftLiftedProjectivizationRepairInput ← HYPOTHESIS
  │   │
  │   └─ postRoleDiagonalCompletion
  │       └─ MainFormalPostRolePackageDiagonalOrthonormalizationInput
  │           ├─ leftSpectral/rightSpectral ← PROVED
  │           └─ leftRepair/rightRepair ← HYPOTHESIS (LeftLiftedProjectivizationRepairInput)
  │       └─ OrthonormalizationMatchMassPreservation × 2 ← HYPOTHESIS
  │
  └─ Alternative: MainFormalRepairedBridgeHypotheses
      └─ MainFormalPostRolePackageDiagonalOrthonormalizationInput (as above)
      └─ DiagonalConsistencyInput
```

---

## 5. Where the Chain Breaks

### What IS Proved

1. **Spectral truncation** at all levels — `spectralTruncationInput_of_sourceAlmostProjective` provides the `SpectralTruncationInput` for any measurement
2. **Consistency-to-almost-projective** — `consistencyToAlmostProjective` lemma is proved
3. **Option-completion reduction** — `optionCompletion_bipartiteSSCRel` transports the SSC hypothesis through completion
4. **orthonormalizationMainLemma_local** — the main orchestration proof is proved, taking the explicit spectral+repair inputs
5. **Base case (m=1)** — the base case is discharged through the external `hbaseBridge` hypothesis; the base role residual is proved via `strategySymmetrization_mainInductionBaseCase`
6. **Downstream cascade** (post-orthonormalization): completion, line-169 repair, line-156 handoff, point-consistency — all proved

### What Is NOT Proved (the gap)

1. **QXP repair witness** (`LeftLiftedProjectivizationRepairInput` at all levels) — this requires producing a canonical local projective family `qxpProjSubMeas` whose left lift is rounding-close to the source measurement. This corresponds to unformalized content in Section 5 of the paper (Lemmas 5.8–5.10, the QXP construction).
2. **Per-slice induction packages** for the successor case — the recursive per-Fq-slice induction data (corresponding to the Section 6 slice recursion)
3. **Per-slice self-improvement bridge inputs** — honest slice strategies, their Section 9 bridge inputs (helper SSC, orthonormalization repair, final fields)
4. **Orthonormalization match-mass preservation** — the P_A/P_B match-mass invariant used by `completingToMeasurement`

### The Bridge Structures That Accept These Inputs

Several "bridge hypothesis" structures exist as named targets:
- `MainFormalBaseProjectiveCompletionObligations` — full package for `baseProjectiveCompletionResidual`
- `MainFormalBaseCompletionObligations` — narrowed, omits a_A/a_B
- `MainFormalRepairedBridgeHypotheses` (MainFormal.lean:240) — alias for the base repaired bridge
- `SelfImprovement.SelfImprovementBridgeInputs` — packages the three Section 9 inputs
- `SelfImprovementPackage.SliceBridgeInputs` — per-slice bridge for Section 6
- `MainFormalSuccessorBoundary` — successor-case boundary data

---

## 6. Recommended Path to Closing the Gap

### For the Successor Case `sorry` (MainFormal.lean:611)

1. **Construct per-slice induction packages** — For each Fq slice, build `MainInductionStep.PerSliceInductionPackage`. This is the recursive call to `mainInduction` at the predecessor parameter set.

2. **Build slice-bridge inputs** — For each slice, construct `SelfImprovementPackage.SliceBridgeInputs`:
   - Honest slice strategies matching the restricted interfaces
   - `HelperStrongSelfConsistencyInput` — the helper SSC
   - `OrthonormalizationInput` — containing the QXP repair witness
   - `FinalFieldsInput` — for completeness/point-consistency/self-closeness

3. **Construct `MainFormalSuccessorSelfImprovementObligation`** — from the slice-bridge inputs

4. **Construct `MainFormalSuccessorBoundary`** — via `mainFormalSuccessorBoundary_ofRecursiveSelfImprovement`

5. **Get role residual** — via `MainFormalRolePackageResidual.ofSuccessorBoundary`

6. **Build `MainFormalPostRolePackageDiagonalOrthonormalizationInput`** — from the QXP repair witnesses for both unsymmetrized POVMs. Use `ofRepairInputs` or `ofQXPLayerRepairWitnesses` or `ofLiftedQXPApproximations`.

7. **Build match-mass preservation** — the `OrthonormalizationMatchMassPreservation` for both sides

8. **Assemble** — via `MainFormalCascadeRolePackageResidualProjectiveCompletionResidual.nonempty_ofRoleResidualAndDiagonalInputsAndMatchMassPreservation`

### For the QXP Repair Itself

The QXP repair witness (`LeftLiftedProjectivizationRepairInput`) requires:
- A `QXPLayerData` structure (Q, X, XHat, T matrices)
- Proof that the source measurement equals the Q-layer
- `SDDOpRel` showing the P-family is rounding-close to the Q-family
- Optional coisometry/residual-domination conditions for the monotone-total route

The `leftLiftedProjectivizationRepairInput_of_lifted_qxp_sddOpRel` and related constructors in `OrthonormalizationBridge.lean` accept these QXP data and produce the `LeftLiftedProjectivizationRepairInput`.

---

## 7. Files Involved

| File | Role |
|---|---|
| `MIPStarRE/LDT/MakingMeasurementsProjective/Statements.lean` | Defines `OrthonormalizationInput`, `SpectralTruncationInput`, `LeftLiftedProjectivizationRepairInput` |
| `MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization.lean` | Theorem `orthonormalization` consuming `OrthonormalizationInput` |
| `MIPStarRE/LDT/MakingMeasurementsProjective/SpectralTruncation/ProjectiveNonMeasurement.lean` | Proved: `spectralTruncationInput_of_sourceAlmostProjective` |
| `MIPStarRE/LDT/SelfImprovement/Theorems/Statements.lean` | Defines `SelfImprovement.OrthonormalizationInput`, `OrthonormalizationRepairObligation` |
| `MIPStarRE/LDT/SelfImprovement/Theorems/OrthonormalizationBridge.lean` | Bridge: spectral/repair obligations, QXP repair witness constructors |
| `MIPStarRE/LDT/SelfImprovement/Theorems/Results/SelfImprovementTop/Core.lean` | `selfImprovement` theorem (uses `orthonormalization` from MMProj) |
| `MIPStarRE/LDT/MainInductionStep/Theorems/SelfImprovementBridge/Core.lean` | `selfImprovementInInductionSection`, `SelfImprovementPackage` |
| `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean` | Final assembly with 1 `sorry` (line 611) |
| `MIPStarRE/LDT/Test/MainTheorem/OrthonormalizationData.lean` | `MainFormalPostRolePackageDiagonalOrthonormalizationInput` and residual |
| `MIPStarRE/LDT/Test/MainTheorem/NativeTargets.lean` | `MainFormalCascadeRolePackageResidualProjectiveCompletionResidual` |
| `MIPStarRE/LDT/Test/MainTheorem/OrdinaryRestriction/Basic.lean` | `MainFormalSuccessorBoundary` and successor self-improvement obligations |
| `MIPStarRE/LDT/Test/MainTheorem/RoleRegister/Core.lean` | `MainFormalRolePackageResidual` (base and successor constructors) |

---

*End of audit report. No Lean code was modified.*
