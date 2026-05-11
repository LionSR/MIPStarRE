# Historical Issue #1367 — SelfImprovement Bridge Audit: Input-Consistency Orphans

**Date:** 2026-05-08
**Scope:** `MIPStarRE/LDT/SelfImprovement/` → `MainInductionStep/` → `Test/MainTheorem/`
**Active PRs:** #1373 (orthonormalization-input producer), #1374 (successor bridge hypotheses)
**Related issues:** #1385 (SDP slackness), #1375/#1376/#1377 (#1036 sub-gaps), #1043 (hbaseBridge), #1035 (recursive mainFormal)

> **Status note, 2026-05-11.**  This report records the pre-#1458 and pre-#1482
> state of the final theorem.  Its statements about making `mainFormal`
> sorry-free by adding new hypotheses are historical, not current project
> guidance.  The current policy is that `mainFormal` remains the paper-facing
> theorem statement; bridge, residual, repair, input, package, or producer
> assumptions belong only in separately named conditional helpers or in producer
> obligations tracked by #1458.

---

## Executive Summary

The `SelfImprovementBridgeInputs` package (the three Section 9 hypotheses) and its downstream wiring in `MainInductionStep` and `MainTheorem` are structurally sound. All individual lemmas in `SelfImprovement/` are proved conditional on their explicit hypotheses. The MainInductionStep bridge (`SelfImprovementBridge/Core.lean`) wires SelfImprovement → Pasting correctly. The *only* remaining `sorry` in the entire LDT directory is at `MainFormal.lean:611` (the successor case branch).

At the time of this report, PR #1374 proposed adding two new hypotheses to
`mainFormal` and replacing the `sorry` with a call to existing constructors in
`RoleRegister.lean`.  Under the current #1458 policy, that route is historical:
the source-facing theorem should instead keep the paper statement and discharge
the missing analytic content through producer theorems or separately named
conditional helpers.

**This audit report confirms that #1367 can be closed** once #1374 and #1373 land (or this report is merged), because:
- The remaining gaps are individually tracked by open issues (#1375, #1376, #1377, #1043, #1035, #1385)
- The active PRs complete the immediate bridge architecture
- No new undiscovered gaps exist

---

## 1. SelfImprovementBridgeInputs Decomposition

### 1.1 Definition

**File:** `MIPStarRE/LDT/SelfImprovement/Theorems/Statements.lean:485-500`

```lean
structure SelfImprovementBridgeInputs (params) (strategy) (eps delta nu) where
  helperStrongSelfConsistency : HelperStrongSelfConsistencyInput params strategy eps delta
  orthonormalization         : OrthonormalizationInput params strategy eps delta
  finalFields                : FinalFieldsInput params strategy eps delta nu
```

Three `Prop`-valued fields packaging the remaining Section 9 unformalized hypotheses:

| Field | Type | Meaning | Paper Reference |
|-------|------|---------|-----------------|
| `helperStrongSelfConsistency` | `∀ T Hhat Z, SelfImprovementHelperConclusion → BipartiteSSCRel ...` | Averaged `Hhat` is strongly self-consistent at `selfImprovementHelperError` | Section 8 helper SSC |
| `orthonormalization` | `∀ Hhat, BipartiteSSCRel ... → MakingMeasurementsProjective.OrthonormalizationInput ...` | Spectral-truncation + repair witnesses exist for `optionCompletion Hhat` | Section 9 orthonormalization |
| `finalFields` | `∀ T Hhat H Z, ... → SelfImprovementFinalFields ...` | Completeness, point-consistency, self-closeness, projective-residual bound | Sections 9.2–9.4 |

### 1.2 Sub-hypothesis types

- **`HelperStrongSelfConsistencyInput`** (line 420-428): A `∀` wrapper over `SelfImprovementHelperConclusion` that asserts `BipartiteSSCRel` at the helper error level
- **`OrthonormalizationInput`** (line 440-447): An `abbrev` converting `BipartiteSSCRel` on `Hhat` into `MakingMeasurementsProjective.OrthonormalizationInput` at helper error
- **`FinalFieldsInput`** (line 455-470): A `∀` wrapper that, given `SelfImprovementHelperConclusion`, orthonormalization closeness, and data-processing closeness, produces `SelfImprovementFinalFields`

---

## 2. Producer Chain: SelfImprovement Module

### 2.1 Main theorems

**File:** `MIPStarRE/LDT/SelfImprovement/Theorems/Results/SelfImprovementTop/Core.lean`

| Theorem | Line | Takes | Produces | Status |
|---------|------|-------|----------|--------|
| `selfImprovementHelper` | 84 | `sdp` (SDP unsolved), `addInU` (type variable) | `SelfImprovementHelperConclusion` (T, Hhat, Z) | **PROVED** (conditional on `sdp`/`addInU` as explicit hypotheses) |
| `selfImprovement` | 158 | 3 explicit bridge hypotheses + `IsGood` + `G` | `SelfImprovementConclusion` (H, Z) | **PROVED** (conditional) |
| `selfImprovementFromBridgeInputs` | 285 | `SelfImprovementBridgeInputs` + `IsGood` + `G` | `SelfImprovementConclusion` | **PROVED** (pure wiring) |
| `selfImprovementFromSubMeas` | 259 | Same as above | SubMeas version | **PROVED** (pure wiring) |

### 2.2 Internal lemma producers for each bridge field

#### `helperStrongSelfConsistency` — PROVED (conditional)

**File:** `MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperSSC.lean`

- **`helper_strong_self_consistency_input_of_producer`** (line 663): Takes `HelperStrongSelfConsistencyProducerInputs` (a `∀` requiring local-variance and residual bounds for each `SelfImprovementHelperConclusion` output) → produces `HelperStrongSelfConsistencyInput`
- **The actual derivation** (`helper_strong_self_consistency_producer_inputs_of_selfConsistency_localVariance`, line 611): From a `BipartiteSSCRel` hypothesis on the helper output + local-variance/residual bounds → `HelperStrongSelfConsistencyProducerInputs`
- **End-to-end wrapper** (`ofBipartiteSSC_and_localVariance`, line 669): From `hssc : BipartiteSSCRel ...` + `hlocal` + `hresidual` → `HelperStrongSelfConsistencyInput`

**Status:** The conditional lemma is proved. The unconditional gap is: the `BipartiteSSCRel` hypothesis itself must be discharged at each call site. This is exactly the helper-SSC step that Section 8 of the paper characterizes.

#### `orthonormalization` — PARTIAL (spectral proved, repair unproven)

**File:** `MIPStarRE/LDT/SelfImprovement/Theorems/OrthonormalizationBridge.lean`

The `OrthonormalizationInput` is an `abbrev` that maps `BipartiteSSCRel` → `MakingMeasurementsProjective.OrthonormalizationInput`. The latter has two sub-fields:

1. **`spectral`** (`SpectralTruncationInput`): **PROVED** via `spectralTruncationInput_of_sourceAlmostProjective` in `ProjectiveNonMeasurement.lean:749`
2. **`repair`** (`LeftLiftedProjectivizationRepairInput`): **HYPOTHESIS** — requires QXP-layer data (`QXPLayerData` with a projective `P` family rounding-close to the source submeasurement)

Bridge constructors:
- `orthonormalizationSpectralProducer_of_sourceAlmostProjective` (line 851): **PROVED**
- `OrthonormalizationRepairProducer` (line 129-139): **HYPOTHESIS** — defined as a type `∀ Hhat, BipartiteSSCRel ... → LeftLiftedProjectivizationRepairInput ... (optionCompletion Hhat)`
- `orthonormalizationInput_of_producers` (line 684): Combines spectral + repair → full input

**Status:** Spectral ✓, repair ✗. The repair gap is the QXP construction (Sections 5.8–5.10 of the paper). Tracked by #1032.

#### `finalFields` — PROVED (conditional)

**File:** `MIPStarRE/LDT/SelfImprovement/Theorems/Results/SelfImprovementTop/FinalFields.lean`

- **`final_fields_of_helper_outputs_of_total_expectation_le`** (line 44): Takes `SelfImprovementHelperConclusion`, helper completeness, helper SSC, point SSC, orthonormalization closeness, data-processing closeness, and right-total monotonicity → produces `SelfImprovementFinalFields`
- This is a conditional lemma: all sub-hypotheses are available in the `selfImprovement` theorem's context (produced by helper SSC, orthonormalization, and data-processing steps)
- The `FinalFieldsInput` `abbrev` wraps this conditional lemma into the `∀`-quantified form consumed by `selfImprovement`

**Status:** The conditional lemma is fully proved. The SDP-related hypotheses (helper completeness, right-total monotonicity) derive from the `selfImprovementHelper` output. This field is effectively discharged within the `selfImprovement` theorem's context.

---

## 3. Consumer Chain: MainInductionStep

### 3.1 `SelfImprovementPackage.SliceBridgeInputs`

**File:** `MIPStarRE/LDT/MainInductionStep/Theorems/SelfImprovementBridge/Core.lean:242-279`

Per-slice bridge requiring:
- `sliceStrategy : Fq params → SymStrat params ι` — **honest** symmetric strategies per slice
- `state_eq`, `pointMeasurement_eq`, `averagedPoint_eq` — structural transports
- `good` — IsGood at restricted failure profile
- `bridgeInputs : ∀ x, SelfImprovement.SelfImprovementBridgeInputs params (sliceStrategy x) ...`

**Key design choice:** The `sliceStrategy`s are **honest** `SymStrat params ι` (not `AnswerSymStrat`, not restricted). This means the honest slice strategies must be constructible from the restricted `AnswerSymStrat` — which is the gap tracked by #1375.

### 3.2 `AnswerSelfImprovementPackage.SliceBridgeInputs`

**File:** `MIPStarRE/LDT/MainInductionStep/Theorems/SelfImprovementBridge/AnswerSlice.lean:32-69`

Same pattern but with `diagonalZeroCoord_eq` instead of `diagonalMeasurement_eq` (since answer types differ: `DiagonalLinePolynomial` vs `DiagonalLineAnswer`).

### 3.3 Constructors

| Constructor | File:line | What it takes | What it produces |
|-------------|-----------|---------------|-----------------|
| `SliceBridgeInputs.ofMeasurementEq` | Core.lean:411 | Honest strategies + measurement transport + bridge inputs | `SliceBridgeInputs` |
| `SliceBridgeInputs.ofOrthonormalizationRepair` | Core.lean:456 | Above + separate `helperStrongSelfConsistency` + `OrthonormalizationRepairProducer` + `FinalFieldsInput` | `SliceBridgeInputs` (fills orthonormalization via `orthonormalizationInput_of_producers`) |
| `AnswerSliceBridgeInputs.ofMeasurementEq` | AnswerSlice.lean:… | Same pattern, answer-valued | Answer counterpart |
| `SelfImprovementPackage.ofSliceBridgeInputs` | Core.lean:514 | `SliceBridgeInputs` | Full `SelfImprovementPackage` |

### 3.4 Downstream assembly

**File:** `MIPStarRE/LDT/MainInductionStep/Theorems/MainTheorems.lean`

- `mainInductionByRecursionOnM` (line 200): Takes `hselfProducer` (a function `PerSliceInductionPackage → SelfImprovementPackage`) as hypothesis, then assembles `AveragedPastingInput` → `mainInductionFromPackages`
- `mainInductionPublicWrapper` (line 311): Passes `hselfProducer` through to callers

**Status:** The MainInductionStep wiring is complete (no `sorry`s). The gap is at the `mainFormal` level: nobody calls `mainInductionByRecursionOnM` with a concrete `hselfProducer`.

---

## 4. MainTheorem Assembly

### 4.1 RoleRegister wiring

**File:** `MIPStarRE/LDT/Test/MainTheorem/RoleRegister.lean`

Complete wiring functions exist (all proved):
- `successorOfBridgeInputs` (line 547): Takes `hrec` + `hbridge` → branch residual
- `answerSuccessorOfBridgeInputs` (line 582): Answer-valued counterpart
- `answerSuccessorOfInductionPackageAndBridgeInputs` (line 628): Takes `PerSliceInductionPackage` + bridge → branch residual
- `rolePackageResidual_ofAnswerSuccessorBridgeInputs` (line 602): Wraps → `Nonempty (MainFormalRolePackageResidual)`

These functions were not called from the older final assembly because the
successor induction and bridge data had not been produced.  Under the current
policy, that data should be supplied by producer theorems or isolated in a
conditional helper, not added as new hypotheses to the paper-facing theorem.

### 4.2 Historical MainFormal successor-case hypotheses (PR #1374 additions)

**Historical PR #1374** (`issue1036-successor-slice-bridge`) proposed the
following two additional hypotheses for `mainFormal`; the current #1458 policy
does not permit this as the paper-facing theorem shape:

```lean
(hanswerSliceWitness : ∀ (hm_ne_one : params.m ≠ 1),
   MainFormalSuccessorAnswerSliceWitness params strategy eps hpass k hm_ne_one)
(hanswerSliceBridge : ∀ (hm_ne_one : params.m ≠ 1),
   MainFormalSuccessorAnswerSliceBridge params strategy eps hpass k hm_ne_one)
```

Where:
- **`MainFormalSuccessorAnswerSliceWitness`** (new `abbrev`, line ~23): Expands `answerSuccessorRecursiveSlicesInput` from `RoleRegister.lean` — a `Prop` asserting per-slice induction conclusions for the transported predecessor
- **`MainFormalSuccessorAnswerSliceBridge`** (new `abbrev`, line ~41): Expands `answerSuccessorSelfImprovementBridgeInput` from `RoleRegister.lean` — a `Type` packaging per-slice self-improvement bridge data

The successor branch then becomes:
```lean
rcases MainFormalRolePackageBranchResidual
    .rolePackageResidual_ofAnswerSuccessorInductionPackageAndBridgeInputs
    hpass hm1 hd hk0 hk
    (hanswerSliceWitness hm1) (hanswerSliceBridge hm1) with
  ⟨roleResidual⟩
exact mainFormal_ofRoleResidualAndRepairedBridge herr roleResidual
  (hbaseBridge scalars roleResidual)
```

**Impact:** After #1374, `mainFormal` is sorry-free. The unformalized analytic content is pushed into the two new "extra" hypotheses.

### 4.3 Orthonormalization-input producer (PR #1373 additions)

**PR #1373** (`issue1359-orthonormalization-input-producer`) adds:
- New file `OrthonormalizationInputProducer.lean`:
  - `MainFormalPostRolePackageDiagonalOrthonormalizationInput.of_roleResidual` — builds the line-130 orthonormalization input from a role residual + two `LeftLiftedProjectivizationRepairInput` witnesses
- In `MainFormal.lean`:
  - `repairedBridgeHypotheses_of_roleResidual` — builds `MainFormalBaseRepairedBridgeHypotheses` from role residual + leftRepair + rightRepair + diagonalConsistency

**Impact:** The `hbaseBridge` constructor is now explicit: callers need `leftRepair`, `rightRepair` (QXP repair witnesses) and `diagonalConsistency` (diagonal self-consistency). This is exactly the target for #1043.

---

## 5. Active PR Coverage Matrix

| Component | What's proved right now | After #1373 | After #1374 | Issue tracking final gap |
|-----------|------------------------|-------------|-------------|--------------------------|
| `selfImprovementHelper` (SDP + addInU) | Conditional on `sdp` witness | No change | No change | #1385 (SDP slackness), #1230 |
| `helperStrongSelfConsistency` (helper SSC) | Conditional lemma proved | No change | No change | #1376 (per-slice producer) |
| `orthonormalization.spec` (spectral) | **PROVED** unconditionally | No change | No change | — |
| `orthonormalization.repair` (QXP repair) | Hypothesis | New: `of_roleResidual` wraps it | No change | #1032 (QXP construction) |
| `finalFields` (completeness etc.) | Conditional lemma proved | No change | No change | #1376 (per-slice producer) |
| `SliceBridgeInputs` wiring | **PROVED** (constructors exist) | No change | No change | #1375 (honest SymStrat) |
| `MainFormal` successor case | **`sorry`** (line 611) | No change | New: replaced by `hanswerSlice*` hypotheses | #1376 + #1377 + #1035 |
| `hbaseBridge` construction | Hypothesis | New: `repairedBridgeHypotheses_of_roleResidual` | No change | #1043 |

---

## 6. Remaining Blocker Inventory

### 6.1 Blockers for `mainFormal` closure (after #1373/#1374)

These are the producers for the two new `mainFormal` hypotheses:

| # | Gap | What it produces | Tracked by | Dependency chain |
|---|-----|-----------------|------------|-----------------|
| A | Honest `SymStrat` slice strategies from `AnswerSymStrat` | `sliceStrategy : Fq params → SymStrat params (Role × ι)` | #1375 | Needed by #1376 |
| B | `SelfImprovementBridgeInputs` per honest slice | Per-slice helperSSC + orthonormalization + finalFields | #1376 | Depends on A |
| C | Universe mismatch `AnswerMainInductionHypothesis` at `Role × ι` | Fix type-level application | #1377 | Blocks per-slice induction |
| D | Recursive `mainFormal` for successor restricted slices | `MainFormalSuccessorAnswerRecursiveSlices` (= per-slice induction conclusion) | #1035 | Needs C fixed |
| E | `hbaseBridge` for base/successor cases | `MainFormalRepairedBridgeHypotheses` (leftRepair + rightRepair + diagonalConsistency) | #1043 | Needs QXP repair (#1032) |

### 6.2 Blockers for SelfImprovement internal closure

| # | Gap | Tracked by |
|---|-----|------------|
| F | `SdpStatementWithSlackness` unconditional producer (strong duality) | #1385, #1230 |
| G | `LeftLiftedProjectivizationRepairInput` unconditional producer (QXP construction) | #1032 |
| H | `OrthonormalizationRepairProducer` for the helper families | #1032 (via QXP) |

### 6.3 Dependency relationships

```
#1032 (QXP repair) ──────────────────────────┐
                                               ├─→ #1043 (hbaseBridge)
#1385/#1230 (SDP slackness) ───→               │
                                    #1376 (per-slice bridge inputs) ──→ mainFormal closure
#1375 (honest SymStrat) ─────────→              │
                                               ├─→ #1374 hypotheses
#1377 (universe mismatch) ───────→ #1035 (recursive mainFormal) ─────→
```

### 6.4 Non-blockers (handled by active PRs)

| Item | Status |
|------|--------|
| `slackness-carrying helpers` (orphan lemmas, `ResidualDomination.lean`, `SdpMatrixHelperBridge.lean`) | Orphan — tracked by #1230, not blocking |
| `MatrixAddInUTransferStatement` | Dead scaffolding — tracked by statement-smuggle reaudit |
| `self_improvement_helper_with_slackness` variants | Orphan — tracked by #1385, not blocking |
| Internal SelfImprovement sub-lemmas (HelperCompleteness, PointConsistency, etc.) | All proved (conditional) |
| Pasting theorem (`ldPasting`) | Fully proved, fully wired |
| MainInductionStep bridge (`mainInductionByRecursionOnM`) | Fully proved (conditional on `hselfProducer`) |

---

## 7. Orphan Status Assessment

### 7.1 Slackness-carrying lemmas (from prior audit)

| Declaration | File | Callers in MainTest | Verdict |
|------------|------|---------------------|---------|
| `self_improvement_helper_with_slackness` | `SelfImprovementTop/Core.lean:119` | None | Orphan — useful for SDP duality path (#1385) |
| `selfImprovementWithSlacknessAndResidualDominationInput` | `ResidualDomination.lean:81` | None | Orphan — same |
| ~10 matrix-level SDP bridge lemmas | `SdpMatrixHelperBridge.lean` | None | Orphan — same |
| `MatrixAddInUTransferStatement` | `MatrixRealization.lean:148` | None (0 consumers) | **DEAD** — should be deleted or documented |

### 7.2 OrthonormalizationInputConstructors

**File:** `SelfImprovement/Theorems/OrthonormalizationInputConstructors/`

Imported by barrel `Theorems.lean` but **never by MainInductionStep or MainTheorem**. These are internal helper lemmas used within SelfImprovement's own submodules. Not orphan — they serve the internal pipeline.

---

## 8. Issue Tracking Completeness

The following open issues directly address the remaining gaps identified in this audit:

| Issue | Description | Covers Gap(s) | Status |
|-------|-------------|---------------|--------|
| #1375 | Construct honest `SymStrat` slice strategies from answer-valued restriction | A | Open, untouched |
| #1376 | Prove `SelfImprovementBridgeInputs` unconditionally for answer-valued restricted slices | B | Open, untouched |
| #1377 | `Role × ι` universe mismatch in `AnswerMainInductionHypothesis` | C | Open, diagnosed |
| #1035 | Prove recursive `mainFormal` for successor restricted slices | D | Open, blocked by #1377 |
| #1043 | Construct `hbaseBridge` for base/successor cases | E | Open, blocked by #1032 |
| #1032 | QXP repair / spectral-truncation + locality-preserving repair lemmas | G, H | Open, core gap |
| #1385 | `SdpStatementWithSlackness` producer | F | Open, epic tracking |
| #1369 | Construct answer-valued successor inputs for MainFormal | A–D (umbrella) | Open |

**Completeness check:** Every sub-gap identified in Section 6 has a corresponding open issue. No new gaps need new issues.

---

## 9. Actively Duplicated / Overlapping Work

### 9.1 PR conflict surface

Both #1373 and #1374 touch:
- `MIPStarRE/LDT/SelfImprovement/Theorems/Thresholds/Final.lean` (same `hdata_sqrt` fix)
- `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean` (different additions)

The fix in `Final.lean` is identical (adding a missing parenthesis in a `gcongr` block). The `MainFormal.lean` additions are additive (both add new material after the existing preamble). They can be merged in either order with trivial conflict resolution.

### 9.2 #1369 vs #1374

Issue #1369 ("Construct answer-valued successor inputs for MainFormal") is an umbrella that covers the same work as #1374's new hypotheses. #1374 moves the gap into `mainFormal`'s hypothesis list; #1375/#1376/#1035 are the actual sub-gaps.

**Recommendation:** Close #1369 as superseded by the combination of #1374 + #1375 + #1376 + #1035.

---

## 10. Recommendations

### 10.1 Immediate (this audit cycle)

1. **Merge #1373 and #1374** (after resolving the trivial `Final.lean` conflict). These complete the bridge architecture and make `mainFormal` sorry-free.

2. **Close #1367** — this audit confirms the chain is structurally sound. Remaining gaps are individually tracked.

3. **Close #1363** and **#1369** as superseded by the sub-issues opened by #1374 (#1375, #1376, #1377, #1035, #1043).

4. **Delete or justify `MatrixAddInUTransferStatement`** — the only dead `*Statement` structure (0 consumers, 0 producers). Either open a sub-issue under #1385 or delete.

### 10.2 Next proof cycle

5. **Fix #1377** (universe mismatch) — prerequisite for #1035, likely a small type-level fix.

6. **Prove #1375** (honest `SymStrat` construction) — the constructive bridge from answer-valued restricted strategies to honest symmetric strategies. This is the most load-bearing missing piece for the `hanswerSliceBridge` hypothesis.

7. **Prove #1376** (per-slice `SelfImprovementBridgeInputs`) — requires #1375 + SDP witness + QXP repair witness for each slice. This is the meat of the paper's Section 9 applied at the restricted-profile level.

8. **Prove #1035** (recursive `mainFormal`) — the fixed-point that ties the induction together.

9. **Prove #1043** (`hbaseBridge`) — the base-case orthonormalization + diagonal-consistency bridge.

10. **Prove #1385** (`SdpStatementWithSlackness`) — the strong-duality SDP bridge.

---

## 11. File Reference (for proof agents)

| File | Role |
|------|------|
| `MIPStarRE/LDT/SelfImprovement/Theorems/Statements.lean` | `SelfImprovementBridgeInputs`, `HelperStrongSelfConsistencyInput`, `OrthonormalizationInput`, `FinalFieldsInput` definitions |
| `MIPStarRE/LDT/SelfImprovement/Theorems/Results/SelfImprovementTop/Core.lean` | `selfImprovementHelper`, `selfImprovement`, `selfImprovementFromBridgeInputs` |
| `MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperSSC.lean` | `helperStrongSelfConsistency` conditional producer |
| `MIPStarRE/LDT/SelfImprovement/Theorems/OrthonormalizationBridge.lean` | Spectral producer (proved), repair producer (hypothesis) |
| `MIPStarRE/LDT/SelfImprovement/Theorems/Results/SelfImprovementTop/FinalFields.lean` | `finalFields` conditional producer |
| `MIPStarRE/LDT/MakingMeasurementsProjective/Statements.lean` | `MMProj.OrthonormalizationInput`, `SpectralTruncationInput`, `LeftLiftedProjectivizationRepairInput` |
| `MIPStarRE/LDT/MakingMeasurementsProjective/SpectralTruncation/ProjectiveNonMeasurement.lean` | `spectralTruncationInput_of_sourceAlmostProjective` (PROVED) |
| `MIPStarRE/LDT/MainInductionStep/Theorems/SelfImprovementBridge/Core.lean` | `SelfImprovementPackage.SliceBridgeInputs`, `ofSliceBridgeInputs`, `selfImprovementInInductionSection` |
| `MIPStarRE/LDT/MainInductionStep/Theorems/SelfImprovementBridge/AnswerSlice.lean` | `AnswerSelfImprovementPackage.SliceBridgeInputs` |
| `MIPStarRE/LDT/MainInductionStep/Theorems/MainTheorems.lean` | `mainInductionByRecursionOnM`, `mainInductionPublicWrapper` |
| `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean` | `mainFormal` (1 `sorry` at line 611; closed by #1374) |
| `MIPStarRE/LDT/Test/MainTheorem/RoleRegister.lean` | `successorOfBridgeInputs`, `answerSuccessorOfBridgeInputs`, `rolePackageResidual_ofAnswerSuccessorBridgeInputs` |
| `MIPStarRE/LDT/Test/MainTheorem/OrdinaryRestriction/Basic.lean` | `MainFormalSuccessorSelfImprovementBridgeInputs` type + constructors |
| `MIPStarRE/LDT/Test/MainTheorem/AnswerValuedRestriction.lean` | Answer-valued counterpart types + constructors |
| `MIPStarRE/LDT/Test/MainTheorem/OrthonormalizationInputProducer.lean` | **New in #1373** — `of_roleResidual` lemma |
| `MIPStarRE/LDT/Test/MainTheorem/OrthonormalizationData.lean` | `MainFormalPostRolePackageDiagonalOrthonormalizationInput` |

---

*End of audit report. No Lean code was modified.*
