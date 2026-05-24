# Historical Issue #1367 — SelfImprovement Bridge Audit: Input-Consistency Orphans

**Date:** 2026-05-08
**Scope:** `MIPStarRE/LDT/SelfImprovement/` → `MainInductionStep/` → `Test/MainTheorem/`
**Active PRs:** #1373 (orthonormalization-input obligation), #1374 (successor bridge hypotheses)
**Related issues:** #1385 (SDP slackness), #1375/#1376/#1377 (#1036 sub-gaps), #1043 (base completion), #1035 (recursive mainFormal)

> **Status note, 2026-05-11.**  This report records the pre-#1458 and pre-#1482
> state of the final theorem.  Its statements about making `mainFormal`
> sorry-free by adding new hypotheses are historical, not current project
> guidance.  The current policy is that the source-labelled `mainFormal`
> blueprint statement remains paper-facing, while the Lean declaration is linked
> from the separate current-interface entry until the same-space restriction is
> removed.  Bridge, residual, repair, input, or obligation-structure assumptions
> belong only in separately named conditional helpers or in named obligations
> tracked by #1458.
>
> **Status note, 2026-05-12.**  This report also predates #1525.  Its local
> table entries saying that `selfImprovement` itself takes the three explicit
> Section 9 bridge hypotheses, and that `selfImprovementFromSubMeas` is a live
> bridge wrapper, are historical.  The current paper-facing theorem
> `selfImprovement` has the paper-shaped consistency hypothesis and a tracked
> proof gap #1515.  The old submeasurement wrappers
> `selfImprovementFromSubMeas` and `selfImprovementFromObligationsSubMeas` have
> been removed; the remaining conditional Section 6 helper is
> `selfImprovementInInductionSection_ofObligations`.
>
> **Status note, 2026-05-20.**  The preceding 2026-05-12 note is now itself
> historical.  The Section 9 theorem `selfImprovement` and the
> induction-section theorem `selfImprovementInInductionSection` are checked
> without `sorry` or `axiom`.  The former #1515 and #1503
> self-improvement gaps have been discharged in the current Lean code.  The
> remaining live proof obstruction on the `mainFormal` route is the Section 6
> small-error successor construction
> `mainInductionSuccessorNext_ofSmallErrorConstruction` (#1507), together with
> the already documented source-interface restrictions for the same-space
> current formal theorem.
>
> **Status note, 2026-05-13.**  This report also predates PR #1539.  The
> `SelfImprovementObligations` record, the top-level
> `selfImprovementFromObligations` theorem, the matrix-SDP
> residual-domination assembly theorems, and the Section 3/6 successor-boundary
> conditional API have been removed.  The later 2026-05-13 PR update also
> removes `mainInductionPublicWrapper` and `answerMainInductionPublicWrapper`,
> and later work replaced the old recursion wrapper by the successor
> construction theorem
> `mainInductionSuccessorNext_ofSmallErrorConstruction`.  As of the 2026-05-20
> blueprint split, `mainInduction` is linked from the corrected large-`k`
> current-interface entry, while the printed paper theorem remains a separate
> source-labelled statement.  The current repair direction is to keep the paper
> theorem statements visible and to represent the remaining Section 6 analytic
> derivation by the tracked `sorry` site until it is proved.
>
> **Status note, 2026-05-22.**  The Section 6 corrected large-\(k\) successor
> construction has since been proved.  Later table rows that describe the
> former answer-valued small-error successor theorem as a remaining proof
> obligation are historical.  At that snapshot, the remaining direct proof
> holes were the printed source-range obligation
> `MainInductionStep.mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation`
> and the final two-space source-boundary obligation
> `Test.mainFormal_sourceSmallErrorConclusion`.
>
> The same day, the orthonormalization-input cleanup removed the former
> `SelfImprovement.HelperStrongSelfConsistencyInput`,
> `SelfImprovement.OrthonormalizationInput`, `SelfImprovement.FinalFieldsInput`,
> and `MakingMeasurementsProjective.OrthonormalizationInput` bundles.  It later
> narrowed `SelfImprovement/Theorems/OrthonormalizationBridge.lean` to a
> spectral-only module, which has now also been retired.  Later mentions of the
> removed input bundles or the old bridge module in this report should be read
> only as historical diagnostics, not as live API guidance.
>
> The Section 5 projectivization cleanup also removed the former
> `ProjectivizationRepairInput` and `LeftLiftedProjectivizationRepairInput`
> abbreviations.  Mentions of those names below are historical descriptions of
> the old formalization boundary; the current construction uses
> `leftLiftedProjectivizationRepair` directly.
>
> **Status note, 2026-05-23.**  The 2026-05-22 proof-frontier description is
> now historical.  With the confirmed correction `k >= 400md` and the explicit
> nonzero-sampling boundary `0 < k`, the Section 6 source route and the final
> two-space source-boundary theorem are proof-complete in Lean.  Later mentions
> of source-range or final-theorem obligation declarations below refer to
> retired interfaces, not to current theorem hypotheses.

---

## Executive Summary

This executive summary is historical.  The
`SelfImprovementObligations` record, its top-level conditional theorem, and the
old downstream Section 3/6 wiring have been removed.  The current invariant is
that paper-facing theorem statements retain the paper hypotheses.  The Section
9 and induction-section self-improvement derivations are now checked in Lean;
the corrected large-\(k\) Section 6 small-error successor construction is also
now checked.  Under the corrected source hypotheses, the former source-range
and final two-space obligation declarations have also been retired.

In the audited snapshot, the `SelfImprovementObligations` record (the three
Section 9 hypotheses) and its downstream wiring in `MainInductionStep` and
`MainTheorem` were structurally sound as conditional declarations.  All
individual lemmas in `SelfImprovement/` were proved conditional on their
explicit hypotheses. The MainInductionStep bridge
(`SelfImprovementBridge/Core.lean`) wires SelfImprovement to Pasting correctly.
As of 2026-05-08, this report identified the successor-case branch at
`MainFormal.lean:611` as the remaining final-theorem `sorry` site.

At the time of this report, PR #1374 proposed adding two new hypotheses to
`mainFormal` and replacing the `sorry` with a call to existing constructors in
`RoleRegister.lean`.  Under the current #1458 policy, that route is historical:
the paper-facing theorem should instead keep the paper statement and discharge
the missing analytic content through named obligation theorems or separately named
conditional helpers.

**This audit report confirms that #1367 can be closed** once #1374 and #1373 land (or this report is merged), because:
- The remaining gaps are individually tracked by open issues (#1375, #1376, #1377, #1043, #1035, #1385)
- The active PRs complete the immediate bridge architecture
- No new undiscovered gaps exist

---

## 1. SelfImprovementObligations Decomposition

### 1.1 Historical Definition

**File:** `MIPStarRE/LDT/SelfImprovement/Theorems/Statements.lean:485-500`

```lean
structure SelfImprovementObligations (params) (strategy) (eps delta nu) where
  helperStrongSelfConsistency : HelperStrongSelfConsistencyInput params strategy eps delta
  orthonormalization         : OrthonormalizationInput params strategy eps delta
  finalFields                : FinalFieldsInput params strategy eps delta nu
```

This structure has been removed.  In the audited snapshot, three
`Prop`-valued fields recorded the remaining Section 9 unformalized hypotheses:

| Field | Type | Meaning | Paper Reference |
|-------|------|---------|-----------------|
| `helperStrongSelfConsistency` | `∀ T Hhat Z, SelfImprovementHelperConclusion → BipartiteSSCRel ...` | Averaged `Hhat` is strongly self-consistent at `selfImprovementHelperError` | Section 8 helper SSC |
| `orthonormalization` | `∀ Hhat, BipartiteSSCRel ... → MakingMeasurementsProjective.OrthonormalizationInput ...` | Spectral-truncation + repair witnesses exist for `optionCompletion Hhat` | Section 9 orthonormalization |
| `finalFields` | `∀ T Hhat H Z, ... → SelfImprovementFinalFields ...` | Completeness, point-consistency, self-closeness, projective-residual bound | Sections 9.2–9.4 |

### 1.2 Historical Sub-hypothesis Types

- **`HelperStrongSelfConsistencyInput`** (line 420-428 in the audited
  snapshot): a `∀` wrapper over `SelfImprovementHelperConclusion` asserting
  `BipartiteSSCRel` at the helper error level.  This wrapper has been removed.
- **`OrthonormalizationInput`** (line 440-447 in the audited snapshot): an
  `abbrev` converting `BipartiteSSCRel` on `Hhat` into
  `MakingMeasurementsProjective.OrthonormalizationInput` at helper error.  This
  input bundle has been removed.
- **`FinalFieldsInput`** (line 455-470 in the audited snapshot): a `∀` wrapper
  that, given `SelfImprovementHelperConclusion`, orthonormalization closeness,
  and data-processing closeness, produced `SelfImprovementFinalFields`.  This
  wrapper has been removed.

---

## 2. Obligation Chain: SelfImprovement Module

### 2.1 Main theorems

**File:** `MIPStarRE/LDT/SelfImprovement/Theorems/Results/SelfImprovementTop/Core.lean`

| Theorem | Line | Takes | Produces | Status |
|---------|------|-------|----------|--------|
| `selfImprovementHelper` | 84 | `sdp` (SDP unsolved), `addInU` (type variable) | `SelfImprovementHelperConclusion` (T, Hhat, Z) | **PROVED** (conditional on `sdp`/`addInU` as explicit hypotheses) |
| `selfImprovement` | current `SelfImprovementTop/Core.lean` | paper hypotheses `IsGood`, `G`, and input consistency | `SelfImprovementConclusion` (H, Z) | checked paper-facing statement |
| Historical `selfImprovementFromObligations` | removed | `SelfImprovementObligations` + `IsGood` + `G` | `SelfImprovementConclusion` | removed by PR #1539 |

### 2.2 Historical Internal Obligations for Each Bridge Field

The following three subsections describe the old bridge-field decomposition.
They should not be read as current API: the input wrappers named here have
been removed, and the remaining derivations are now either direct construction
theorems or tracked `sorry` sites on source-facing statements.

#### `helperStrongSelfConsistency` — historical conditional route

**File:** `MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperSSC.lean`

- **`helper_strong_self_consistency_input_of_obligations`** (line 663): Takes `HelperStrongSelfConsistencyBounds` (a `∀` requiring local-variance and residual bounds for each `SelfImprovementHelperConclusion` output) → produces `HelperStrongSelfConsistencyInput`
- **The actual derivation** (`helper_strong_self_consistency_bounds_of_selfConsistency_localVariance`, line 611): From a `BipartiteSSCRel` hypothesis on the helper output + local-variance/residual bounds → `HelperStrongSelfConsistencyBounds`
- **End-to-end wrapper** (`ofBipartiteSSC_and_localVariance`, line 669): From `hssc : BipartiteSSCRel ...` + `hlocal` + `hresidual` → `HelperStrongSelfConsistencyInput`

**Historical status:** the conditional lemma was proved in the audited
snapshot.  The wrapper has since been removed; the helper strong
self-consistency conclusion is now stated directly from named scalar
obligations, and any missing derivation remains a proof gap rather than an
input bundle.

#### `orthonormalization` — historical spectral/repair split

**Historical file:** `MIPStarRE/LDT/SelfImprovement/Theorems/OrthonormalizationBridge.lean`

In the audited snapshot, `OrthonormalizationInput` was an `abbrev` that mapped
`BipartiteSSCRel` to `MakingMeasurementsProjective.OrthonormalizationInput`.
The latter had two sub-fields:

1. **`spectral`** (`SpectralTruncationStatement`): **PROVED** via `spectralTruncationStatement_of_sourceAlmostProjective` in `ProjectiveNonMeasurement.lean`
2. **`repair`** (`LeftLiftedProjectivizationRepairInput`): **HYPOTHESIS** — requires QXP-layer data (`QXPLayerData` with a projective `P` family rounding-close to the source submeasurement)

Bridge constructors:
- Former `orthonormalizationSpectralObligation_of_sourceAlmostProjective`: **RETIRED**; its
  proof content is the direct construction `spectralTruncationStatement_of_sourceAlmostProjective`.
- `OrthonormalizationRepairObligation` (line 129-139): **HYPOTHESIS** — defined as a type `∀ Hhat, BipartiteSSCRel ... → LeftLiftedProjectivizationRepairInput ... (optionCompletion Hhat)`
- `orthonormalizationInput_of_obligations` (line 684): Combines spectral + repair → full input

**Current status:** the full input bundle and the old bridge module have been
removed.  The spectral conversion is retained directly as
`spectralTruncationStatement_of_sourceAlmostProjective`.  The locality-preserving
QXP repair construction from Sections 5.8-5.10 remains tracked by #1032 and
should be proved directly, not supplied as a theorem hypothesis.

#### `finalFields` — historical conditional route

**File:** `MIPStarRE/LDT/SelfImprovement/Theorems/Results/SelfImprovementTop/FinalFields.lean`

- **`final_fields_of_helper_outputs_of_total_expectation_le`** (line 44): Takes `SelfImprovementHelperConclusion`, helper completeness, helper SSC, point SSC, orthonormalization closeness, data-processing closeness, and right-total monotonicity → produces `SelfImprovementFinalFields`
- In the audited snapshot this was used as a conditional lemma: all
  sub-hypotheses were expected to be available in the `selfImprovement`
  theorem's context.
- The former `FinalFieldsInput` `abbrev` wrapped this conditional lemma into
  the `∀`-quantified form consumed by `selfImprovement`; that wrapper has been
  removed.

**Current status:** the useful final-fields lemma remains proof content, but
there is no longer a `FinalFieldsInput` theorem hypothesis.  Any missing
transport from the helper and orthonormalization outputs belongs inside the
proof of `selfImprovement`.

---

## 3. Consumer Chain: MainInductionStep

### 3.1 Historical `SelfImprovementData.SliceObligations`

**Former file:** `MIPStarRE/LDT/MainInductionStep/Theorems/SelfImprovementBridge/Core.lean:242-279`

This section describes removed interfaces.  The later ordinary slice-transport
construction in
`MIPStarRE/LDT/MainInductionStep/Theorems/SelfImprovementAssembly/Core.lean`
has also been retired from the checked interface.  The active successor proof
uses the answer-valued carrier route and then forgets the answer-valued data
through `SelfImprovementData.ofAnswer`.

Per-slice bridge requiring:
- `sliceStrategy : Fq params → SymStrat params ι` — concrete symmetric strategies per slice
- `state_eq`, `pointMeasurement_eq`, `averagedPoint_eq` — structural transports
- `good` — IsGood at restricted failure profile
- `obligations : ∀ x, SelfImprovement.SelfImprovementObligations params (sliceStrategy x) ...`

**Key design choice:** The `sliceStrategy`s are concrete `SymStrat params ι` (not `AnswerSymStrat`, not restricted). This means the slice strategies must be constructible from the restricted `AnswerSymStrat` — which is the gap tracked by #1375.

### 3.2 Historical `AnswerSelfImprovementData.SliceObligations`

**Former file:** `MIPStarRE/LDT/MainInductionStep/Theorems/SelfImprovementBridge/AnswerSlice.lean:32-69`

This answer-valued obligation bundle has likewise been replaced.  The current
answer-valued construction is in
`MIPStarRE/LDT/MainInductionStep/Theorems/SelfImprovementAssembly/AnswerSlice.lean`
and uses `AnswerSelfImprovementData.ofSelfImprovementInInductionSection` together
with `AnswerSelfImprovementData.ofAnswerCarrier`.  The carrier construction is
the active route: it avoids assuming ordinary polynomial diagonal measurements
that realize the answer-valued slice interface.

### 3.3 Constructors

| Constructor | File:line | What it takes | What it produces |
|-------------|-----------|---------------|-----------------|
| `SliceObligations.ofMeasurementEq` | Core.lean:411 | Concrete strategies + measurement transport + obligations | `SliceObligations` |
| `SliceObligations.ofOrthonormalizationRepair` | Core.lean:456 | Above + separate `helperStrongSelfConsistency` + `OrthonormalizationRepairObligation` + `FinalFieldsInput` | `SliceObligations` (fills orthonormalization via `orthonormalizationInput_of_obligations`) |
| `AnswerSliceObligations.ofMeasurementEq` | AnswerSlice.lean:… | Same pattern, answer-valued | Answer counterpart |
| `SelfImprovementData.ofSliceObligations` | Core.lean:514 | `SliceObligations` | Full `SelfImprovementData` |

### 3.4 Downstream assembly

**File:** `MIPStarRE/LDT/MainInductionStep/Theorems/MainTheorems.lean`

- Historical `mainInductionByRecursionOnM`: took `hselfObligation` as an
  internal proof-stage input, then assembled averaged pasting data.  The
  current frontier is instead
  `mainInductionSuccessorNext_ofSmallErrorConstruction`, which must construct
  the answer-valued and ordinary slice data from the paper hypotheses in the
  small-error successor case.
- Historical `mainInductionPublicWrapper`: removed in the 2026-05-13 PR #1539 update, so this proof-stage input is no longer exposed as a theorem adjacent to the source theorem.

**Status:** This paragraph is historical.  The conditional assembly proof was
useful proof content while the corrected large-`k` Lean interface carried the
successor proof gap directly.  In the current tree, `thm:main-induction` links
to the corrected large-`k` source statement, the former source-range obligation
has been retired under the confirmed factor-\(400\) correction, and the
successor construction is proved without exposing restricted-slice data,
recursive witnesses, or self-improvement packages as source-theorem
assumptions.

---

## 4. MainTheorem Assembly

### 4.1 Historical RoleRegister wiring

**File:** `MIPStarRE/LDT/Test/MainTheorem/RoleRegister.lean`

The older branch-residual route used the following proved wiring functions:
- `successorOfObligations` (line 547): takes `hrec` and the corresponding
  self-improvement obligations to produce the branch residual
- `answerSuccessorOfObligations` (line 582): Answer-valued counterpart
- `answerSuccessorOfInductionPackageAndObligations` (line 628): takes a
  `PerSliceInductionData` and the corresponding obligations to produce the
  branch residual
- `roleWitnessResidual_ofAnswerSuccessorObligations` (line 602): wraps into
  `Nonempty (MainFormalRoleInductionWitness)`

These functions have since been removed.  The current role-register route uses
`MainFormalRoleInductionWitness.ofMainInduction`, so the missing successor
construction is the `sorry` in the corrected large-`k` Section 6 interface
`MainInductionStep.mainInduction`, not a separate obligation API in Section 3.

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
- **`MainFormalSuccessorAnswerSliceBridge`** (new `abbrev`, line ~41): Expands `answerSuccessorSelfImprovementObligations` from `RoleRegister.lean` — a type recording per-slice self-improvement obligations

The historical branch then used these two new parameters to construct a role
residual and call the old conditional assembly route.

**Impact:** Under the historical #1374 route, `mainFormal` became sorry-free by
pushing unformalized analytic content into two new hypotheses.  This is now
rejected for the paper-facing theorem.

### 4.3 Orthonormalization-input obligation (PR #1373 additions)

**PR #1373** (`issue1359-orthonormalization-input-obligation`) adds:
- New file `OrthonormalizationInputObligation.lean`:
  - a historical constructor for the former line-130 orthonormalization input
    from a role residual and two `LeftLiftedProjectivizationRepairInput`
    witnesses
- In `MainFormal.lean`:
  - a historical bridge constructor from role residual, left/right repair
    witnesses, and diagonal consistency

**Historical impact:** the proposed bridge-style constructor made the missing
left/right repair witnesses and diagonal consistency explicit.  The current
cleanup does not add this data to `mainFormal`; #1043 tracks the corresponding
base-case completion obligation.

---

## 5. Active PR Coverage Matrix

| Component | What's proved right now | After #1373 | After #1374 | Issue tracking final gap |
|-----------|------------------------|-------------|-------------|--------------------------|
| `selfImprovementHelper` (SDP + addInU) | Conditional on `sdp` witness | No change | No change | #1385 (SDP slackness), #1230 |
| `helperStrongSelfConsistency` (helper SSC) | Conditional lemma proved | No change | No change | #1376 (per-slice obligation) |
| `orthonormalization.spec` (spectral) | **PROVED** unconditionally | No change | No change | — |
| `orthonormalization.repair` (QXP repair) | Hypothesis | New: `of_roleInductionWitness` wraps it | No change | #1032 (QXP construction) |
| `finalFields` (completeness etc.) | Conditional lemma proved | No change | No change | #1376 (per-slice obligation) |
| `SliceObligations` wiring | **PROVED** (constructors exist) | No change | No change | #1375 (concrete SymStrat) |
| `MainFormal` successor case | **Historical, as of 2026-05-08:** `sorry` at line 611 | No change | New: replaced by `hanswerSlice*` hypotheses | #1376 + #1377 + #1035 |
| Historical bridge-style base/successor construction | Hypothesis | New conditional constructor | No change | #1043 |

---

## 6. Remaining Blocker Inventory

### 6.1 Blockers for `mainFormal` closure (after #1373/#1374)

These were the obligation constructors for the two historical proposed
`mainFormal` hypotheses:

| # | Gap | What it produces | Tracked by | Dependency chain |
|---|-----|-----------------|------------|-----------------|
| A | Concrete `SymStrat` slice strategies from `AnswerSymStrat` | `sliceStrategy : Fq params → SymStrat params (Role × ι)` | #1375 | Needed by the answer-valued slice interface |
| B | Historical `SelfImprovementObligations` per concrete slice | Per-slice helperSSC + orthonormalization + finalFields | #1376 | Replaced by checked Section 9 and induction-section self-improvement theorems |
| C | Universe mismatch `AnswerMainInductionHypothesis` at `Role × ι` | Fix type-level application | #1377 | Blocks per-slice induction |
| D | Recursive `mainFormal` for successor restricted slices | `MainFormalSuccessorAnswerRecursiveSlices` (= per-slice induction conclusion) | #1035 | Needs C fixed |
| E | Historical bridge-style base/successor input | left/right repair witnesses + diagonal consistency | #1043 | Needs QXP repair (#1032) |

### 6.2 Blockers for SelfImprovement internal closure

| # | Gap | Tracked by |
|---|-----|------------|
| F | `SdpStatementWithSlackness` unconditional obligation (strong duality) | #1385, #1230 |
| G | `LeftLiftedProjectivizationRepairInput` unconditional obligation (QXP construction) | #1032 |
| H | `OrthonormalizationRepairObligation` for the helper families | #1032 (via QXP) |

### 6.3 Dependency relationships

```
#1032 (QXP repair) ──────────────────────────┐
                                               ├─→ #1043 (base completion)
#1385/#1230 (SDP slackness) ───→               │
                                    #1376 (per-slice obligations) ──→ mainFormal closure
#1375 (genuine SymStrat) ────────→              │
                                               ├─→ #1374 hypotheses
#1377 (universe mismatch) ───────→ #1035 (recursive mainFormal) ─────→
```

### 6.4 Non-blockers (handled by active PRs)

| Item | Status |
|------|--------|
| Remaining slackness-carrying helper route (`self_improvement_helper_with_slackness`) | Internal SelfImprovement dependency; tracked by #1230 and #1385 |
| Former `MatrixAddInUTransferStatement` | Removed; no live Lean declaration remains |
| `self_improvement_helper_with_slackness` variants | Internal SelfImprovement route; not a public substitute for `selfImprovement` |
| Internal SelfImprovement sub-lemmas (HelperCompleteness, PointConsistency, etc.) | All proved (conditional) |
| Pasting theorem (`ldPasting`) | Fully proved, fully wired |
| MainInductionStep assembly (`answerMainInduction`) | Historical Section 6 answer-valued successor obligation; now proved in the corrected large-\(k\) route |

---

## 7. Orphan Status Assessment

### 7.1 Slackness-carrying lemmas (from prior audit)

| Declaration | File | Callers in MainTest | Verdict |
|------------|------|---------------------|---------|
| `self_improvement_helper_with_slackness` | `SelfImprovementTop/Core.lean:119` | `selfImprovementHelper` | Internal route resting on SDP slackness (#1230, #1385) |
| Former full-conclusion residual-domination variants | `ResidualDomination.lean` | None | Removed by PR #1539; no longer a live theorem-level route |
| Matrix-to-helper SDP lemmas | `SdpMatrixHelperBridge.lean` | None | Removed orphan module; revive only as source-derived proof content if the SDP duality path is completed |
| Former `MatrixAddInUTransferStatement` | `MatrixRealization.lean` | None | Removed; no live Lean declaration remains |

### 7.2 OrthonormalizationInputConstructors

**File:** `SelfImprovement/Theorems/OrthonormalizationInputConstructors/`

Formerly imported by the barrel `Theorems.lean` but never by MainInductionStep
or MainTheorem.  The module has been removed; the remaining orthonormalization
bridge layer stops at named source obligations rather than re-exporting unused
constructors from those obligations to larger input packages.

---

## 8. Issue Tracking Completeness

The following open issues directly address the remaining gaps identified in this audit:

| Issue | Description | Covers Gap(s) | Status |
|-------|-------------|---------------|--------|
| #1375 | Construct concrete `SymStrat` slice strategies from answer-valued restriction | A | Open, untouched |
| #1376 | Historical per-slice self-improvement obligation route for answer-valued restricted slices | B | Superseded by the checked Section 9 and induction-section construction route |
| #1377 | `Role × ι` universe mismatch in `AnswerMainInductionHypothesis` | C | Open, diagnosed |
| #1035 | Prove recursive `mainFormal` for successor restricted slices | D | Open, blocked by #1377 |
| #1043 | Construct base/successor completion data | E | Open, blocked by #1032 |
| #1032 | QXP repair / spectral-truncation + locality-preserving repair lemmas | G, H | Open, core gap |
| #1385 | `SdpStatementWithSlackness` obligation | F | Open, epic tracking |
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

Issue #1369 ("Construct answer-valued successor inputs for MainFormal") is an
umbrella for the same mathematical work that #1374 tried to expose through new
hypotheses.  Under the current policy, that work belongs in named construction
theorems inside the corrected Section 6 interface, while the source-labelled
paper theorems remain separate and source-faithful.  Construction lemmas should
be introduced only when their assumptions are derived from the paper
hypotheses.

**Recommendation:** Close #1369 as superseded by the combination of #1374 + #1375 + #1376 + #1035.

---

## 10. Recommendations

### 10.1 Immediate (this audit cycle)

1. **Do not merge the historical #1374 hypothesis route.**  Its theorem-level
   extra hypotheses have been replaced by paper-facing `sorry` sites.

2. **Close or retarget #1367** only after the tracking issue records that the
   former obligation route has been removed.  The remaining live work on this
   route is #1507, the final completion construction, and the documented
   source-interface restrictions for the current same-space formal theorem.

3. **Close or retarget #1363 and #1369** as historical bridge-route issues if
   they no longer describe live Lean declarations.

4. **Do not reintroduce `MatrixAddInUTransferStatement`** as a standalone
   proof-debt structure.  If the add-in-\(u\) transfer is needed again, state it
   as a source-derived theorem with a paper citation and a proof obligation.

### 10.2 Next proof cycle

5. **Fix #1377** (universe mismatch) — prerequisite for #1035, likely a small type-level fix.

6. **Answer-valued slice self-improvement interface** — discharged by the
   carrier route `AnswerSelfImprovementData.ofAnswerCarrier`.  A low-degree
   support theorem would still be needed for the stronger ordinary-realization
   route, but it is not needed for the active successor reduction.

7. **Continue the Section 6 successor construction** (#1507), including the
   predecessor induction input.  The
   former #1515 and #1503 self-improvement gaps should not be reopened as live
   bridge obligations, and the former degree-zero family branch has been retired
   by the recursive-slice reduction.

8. **Prove #1035** (recursive `mainFormal`) — the fixed-point that ties the induction together.

9. **Prove #1043** — the base-case completion construction.

10. **Prove #1385** (`SdpStatementWithSlackness`) — the strong-duality SDP bridge.

---

## 11. File Reference (for proof agents)

| File | Role |
|------|------|
| `MIPStarRE/LDT/SelfImprovement/Theorems/Statements.lean` | `SelfImprovementHelperConclusion`, `SelfImprovementConclusion`, and remaining statement types; the former `SelfImprovementObligations` bundle has been removed |
| `MIPStarRE/LDT/SelfImprovement/Theorems/Results/SelfImprovementTop/Core.lean` | `selfImprovementHelper`, `selfImprovement`; the former `selfImprovementFromObligations` theorem has been removed |
| `MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperSSC.lean` | `helperStrongSelfConsistency` construction used by Section 9 |
| `MIPStarRE/LDT/SelfImprovement/Theorems/Results/SelfImprovementTop/FinalFields.lean` | Final-field transport used in the checked `selfImprovement` proof |
| `MIPStarRE/LDT/MakingMeasurementsProjective/Statements.lean` | Current projectivization statements; the former orthonormalization and repair-input bundles are historical |
| `MIPStarRE/LDT/MakingMeasurementsProjective/SpectralTruncation/ProjectiveNonMeasurement.lean` | `spectralTruncationStatement_of_sourceAlmostProjective` (PROVED) |
| `MIPStarRE/LDT/MainInductionStep/Theorems/SelfImprovementAssembly/Core.lean` | `selfImprovementInInductionSection`, ordinary slice transport, and ordinary self-improvement data constructors |
| `MIPStarRE/LDT/MainInductionStep/Theorems/SelfImprovementAssembly/AnswerSlice.lean` | Answer-valued slice transport and answer-valued self-improvement data constructors |
| `MIPStarRE/LDT/MainInductionStep/Theorems/StageDataConstructors.lean` | Stage-data constructors, including conversion from answer-valued to ordinary self-improvement data |
| `MIPStarRE/LDT/MainInductionStep/Theorems/MainTheorems.lean` | `mainInduction`, `mainInductionBaseCase`, `answerMainInduction`, and the checked successor construction |
| `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean` | Source-final statement and obligation, current same-space interface, and proved final transport |
| `MIPStarRE/LDT/Test/MainTheorem/RoleRegister.lean` | Role-register witness constructors routed through Section 6 `mainInduction` |
| `MIPStarRE/LDT/Test/MainTheorem/AnswerValuedRestriction.lean` | Answer-valued restricted-slice weighted bounds and recursive-slice targets |
| `MIPStarRE/LDT/Test/MainTheorem/OrthonormalizationData.lean` | Current line-130 orthonormalization residual construction |

---

*End of audit report. No Lean code was modified.*
