# SelfImprovement Proof-Obligation Integrity Audit

Date: 2026-05-07
Updated: 2026-05-12, after the source-faithful `mainFormal` repair and
internal-obligation renaming.

Status note, 2026-05-13: this report predates PR #1539.  The
`SelfImprovementObligations` record, the top-level
`selfImprovementFromObligations` theorem, the matrix-SDP residual-domination
assembly theorems, and the Section 3/6 successor-boundary conditional API have
been removed.  The later 2026-05-13 PR update also removes
`mainInductionPublicWrapper` and `answerMainInductionPublicWrapper`, leaving
`mainInductionByRecursionOnM` as internal proof content and `mainInduction` as
the theorem with the paper statement.  The present paper-alignment policy is to
preserve the theorem statements from the paper and to leave the remaining
derivations as tracked `sorry` sites until they are proved.

Status note, 2026-05-13 after PR #1547 and the follow-up orthonormalization
cleanup: the residual-domination orthonormalization route and the bundled
`OrthonormalizationInput` records have also been removed.  The retained Section
9 orthonormalization proof content is the spectral-truncation conversion in
`SelfImprovement/Theorems/OrthonormalizationSpectral.lean`; the
locality-preserving repair argument remains a proof gap on the source-facing
self-improvement theorem, not an extra theorem input.

Auditor: Research specialist (read-only analysis)
Scope: `MIPStarRE/LDT/SelfImprovement/` → `MIPStarRE/LDT/Pasting/` →
       `MIPStarRE/LDT/MainInductionStep/` → `MIPStarRE/LDT/Test/MainTheorem/`

---

## Executive Summary

The proof-debt concern is valid.  Several formal interfaces still record
intermediate mathematical obligations as explicit inputs to conditional helper
theorems.  Such helpers may preserve useful downstream proof content, but they
must not be presented as theorems from the paper.

The SelfImprovement module compiles with all its lemmas, the Pasting module
compiles independently, and the MainInductionStep module wires them together in
principle.  The remaining gap is now represented in the correct place:
`mainFormal` is again the paper-facing theorem statement, and its proof contains
the tracked construction gap directly.  The proved final-transport theorem
`mainFormal_ofProjectiveCompletionTransportWitness` is retained as useful proof content,
but no public theorem supplies completion data as an additional hypothesis.

The architecture is therefore incomplete, but the theorem boundary is no longer
misstated.  The remaining work is to derive the Section 6 role residual and the
post-role projective-completion residual inside the proof, and then apply the
already-proved final transport.

---

## 1. Architecture Map

### 1.1. SelfImprovement (Section 9)

**Module:** `MIPStarRE/LDT/SelfImprovement/`

Main theorems:

| Theorem | Location | Produces | Hypotheses |
|---------|----------|----------|------------|
| `selfImprovementHelper` | `SelfImprovementTop/Core.lean` | `SelfImprovementHelperConclusion` (T, Hhat, Z) | `IsGood`, input consistency, tracked helper obligations |
| `selfImprovement` | `SelfImprovementTop/Core.lean` | `SelfImprovementConclusion` (full output) | paper-shaped hypotheses: `IsGood`, `G`, input consistency |

Historically, the deleted `SelfImprovementObligations` bundle recorded three
proof-stage inputs:

1. **`helperStrongSelfConsistency`**: the former
   `HelperStrongSelfConsistencyInput` has been removed.  The helper SSC
   conclusion is now produced by
   `helper_strong_self_consistency_of_helper_conclusion` from the named scalar
   obligations, and any remaining derivation is a direct proof gap rather than
   an input bundle.
2. **`orthonormalization`**: the former `OrthonormalizationInput` bundle has
   been removed.  The retained Section 9 API records only the proved
   spectral-truncation conversion; the locality-preserving repair construction
   remains a proof obligation on the source-facing theorem, not a supplied
   theorem hypothesis.
3. **`finalFields`**: the former `FinalFieldsInput` bundle has been removed.
   The completeness, point-consistency, self-closeness, and
   projective-residual estimates must be derived in the proof of
   `selfImprovement`, or left as the tracked proof gap there until proved.

These three inputs are no longer hypotheses of the paper-facing theorem
`selfImprovement`.  The former conditional helper
`selfImprovementFromObligations` has been removed; the derivation from the paper
hypotheses is the tracked proof obligation #1515 in `selfImprovement` itself.

### 1.2. Pasting (Section 9/10 bridge)

**Module:** `MIPStarRE/LDT/Pasting/`

**Key fact: Pasting does NOT import or reference SelfImprovement at all.**
This is intentional — `ldPasting` operates on families produced by the induction
step, not on SelfImprovement's internal structures.

Pasting provides `Pasting.ldPasting` — the theorem that consumes an
`IdxPolyFamily` with completeness, consistency, self-consistency, and boundedness
properties, and produces a next-level `Measurement`.

### 1.3. MainInductionStep (Section 6) — where they meet

**Module:** `MIPStarRE/LDT/MainInductionStep/`

This is where SelfImprovement and Pasting are wired together.  The bridge module
is `Theorems/SelfImprovementBridge/Core.lean`.

**Wiring chain:**

```
selfImprovementInInductionSection    (Core.lean)
  └─ paper-facing statement with tracked proof obligation #1503
```

```
SelfImprovementData.ofSliceObligations   (Core.lean)
  └─ calls selfImprovementInInductionSection per slice
       └─ uses SliceObligations only for concrete slice strategies
          and measurement transport
```

```
ldPastingInInductionSection   (Core.lean)
  └─ calls Pasting.ldPasting  (INDEPENDENT of SelfImprovement call)
```

```
mainInductionByRecursionOnM   (MainTheorems.lean)
  └─ Calls PerSliceInductionData.ofRecursion (induction)
  └─ Calls hselfObligation : PerSliceInductionData → SelfImprovementData
  └─ Calls assembleAveragedPastingData (builds AveragedPastingData from SelfImprovementData)
  └─ Calls mainInductionFromPackages
       └─ Calls AveragedPastingData.output
            └─ Calls ldPastingInInductionSection
                 └─ Calls Pasting.ldPasting
```

**The key observation:** `mainInductionByRecursionOnM` takes `hselfObligation`
as an internal proof-stage input.  This `hselfObligation` must produce a
`SelfImprovementData` from a `PerSliceInductionData`.  It is not a
hypothesis of the paper-facing `mainInduction` theorem; that theorem retains
the paper-shaped statement and the non-base branch is tracked by #1507.

### 1.4. MainFormal (Final Assembly)

**Module:** `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean`

The current paper-facing theorem `mainFormal` takes the paper hypotheses,
together with the large-`k` and positivity boundary hypotheses tracked elsewhere
in the project.  It does **not** take bridge-style data, role residual data, or final
projective-completion inputs.

The current proof gap is direct: `mainFormal` must construct the Section 6 role
residual and the post-role projective-completion residual from the paper
hypotheses.  The Section 6 role residual is routed through
`MainFormalRoleInductionWitness.ofMainInduction`, whose successor branch is
the tracked `sorry` in `MainInductionStep.mainInduction`.  Once the role
residual and post-role completion residual are available, the proved theorem
`mainFormal_ofProjectiveCompletionTransportWitness` supplies the final three consistency
conclusions.

---

## 2. Internal and Orphan Helper Lemmas

These are proved within SelfImprovement but are not public substitutes for the
paper-facing `selfImprovement`, `mainInduction`, or `mainFormal` statements:

### 2.1. Slackness-carrying helpers

| Declaration | File | Status |
|------------|------|--------|
| `self_improvement_helper_with_slackness` | `SelfImprovementTop/Core.lean:119` | Internal dependency of `selfImprovementHelper`; rests on `sdp_statement_with_slackness` |

The former full-conclusion residual-domination variants
`selfImprovementWithSlacknessAndResidualDominationInput` and
`selfImprovementFromSlacknessResidualDominationObligations` were removed by PR
#1539.  The remaining slackness-carrying helper is not a theorem-level
substitute for `selfImprovement`.

These variants assume the SDP carries complementary slackness
(`SdpStatementWithSlackness`).  They are useful proof content only insofar as
the Section 9 SDP slackness theorem is eventually proved from the paper
hypotheses.

### 2.2. Removed orphan helper-bridge modules

The former module
`SelfImprovement/Theorems/Results/SdpMatrixHelperBridge.lean` contained direct
adapters from matrix-level SDP slackness data to the slackness-carrying
self-improvement helper conclusion.  These declarations were never imported or
called from MainInductionStep or MainTheorem.  They have been removed; the
retained proof content stops at the abstract SDP comparison lemmas in
`SdpMatrixBridge.lean`, and the paper-facing helper consumes the abstract
`SdpStatementWithSlackness` interface directly.

The former module
`SelfImprovement/Theorems/OrthonormalizationInputConstructors.lean` contained
thin constructors that combined QXP repair obligations and residual-domination
obligations into larger orthonormalization input packages.  These constructors
were not used outside their own module and have been removed so that the
Section 9 API does not normalize unused proof-debt packages.

### 2.3. Remaining orthonormalization spectral layer

The former `SelfImprovement/Theorems/OrthonormalizationBridge.lean` module has
been narrowed and renamed to
`SelfImprovement/Theorems/OrthonormalizationSpectral.lean`.  It no longer
exports repair-obligation or full-orthonormalization-input constructors.  Its
only retained role is to record the spectral-truncation conversion for the
option-completed helper measurement.

### 2.4. Used (NOT orphan)

| Module | Used by |
|--------|---------|
| `SelfImprovement/Theorems/OrthonormalizationSpectral` | Re-exported by `SelfImprovement/Theorems.lean`; linked from the Section 9 auxiliary blueprint remark |
| `SelfImprovement/Theorems/Results/HelperSSC` | `SelfImprovementTop/Core.lean` (via `selfImprovement`) |
| `SelfImprovement/Theorems/Results/BoundednessTransport` | `SelfImprovementTop/Core.lean` (via `selfImprovement`) |
| `SelfImprovement/Theorems/Results/SelfImprovementTop/Core.lean` | `MainInductionStep/SelfImprovementBridge/Core.lean` |
| `Pasting/Core.lean` → `ldPasting` | `MainInductionStep/SelfImprovementBridge/Core.lean:599` |

---

## 3. Bridge Points — Complete vs. Incomplete

### 3.1. selfImprovementHelper → selfImprovement: Incomplete source proof

`selfImprovementHelper` produces `SelfImprovementHelperConclusion`, which
the conditional assembly uses as the first stage of the Section 9 proof.  The
remaining missing step is to derive the helper strong self-consistency,
orthonormalization, and final-fields inputs from the hypotheses of the paper
theorem.  The paper-facing theorem `selfImprovement` now leaves this as the
tracked proof obligation #1515, rather than taking those three inputs as
hypotheses.  The helper-stage strong self-consistency derivation is separately
tracked by #1514.

### 3.2. selfImprovement → selfImprovementInInductionSection: Proof gap

The paper-facing theorem `selfImprovementInInductionSection` has the expected
submeasurement input and leaves the induction-section proof as #1503.  It does
not take a measurement-completion package or Section 9 obligation bundle as an
extra hypothesis.

### 3.3. selfImprovementInInductionSection → SelfImprovementData: Internal assembly

`SelfImprovementData.ofSliceObligations` calls
`selfImprovementInInductionSection` per slice, using
`SelfImprovementData.SliceObligations` only for the concrete restricted-slice
strategies and measurement transports.  The theorem-level Section 9 proof debt
remains in `selfImprovementInInductionSection`, not in an additional package
hypothesis.

### 3.4. SelfImprovementData → AveragedPastingData: ✅ Complete

`assembleAveragedPastingData` (in `PastingAssembly.lean:420`) converts the
per-slice `SelfImprovementData` fields into averaged inputs for the pasting
theorem.

### 3.5. AveragedPastingData → ldPastingInInductionSection: ✅ Complete

`AveragedPastingData.output` (in `PackageConstructors.lean:357`) calls
`ldPastingInInductionSection`, which calls `Pasting.ldPasting`.

### 3.6. mainInductionByRecursionOnM → mainFormal completion obligations: INCOMPLETE

The theorem `mainFormal` carries the remaining construction gap directly.  It
does not expose recursive-slice data, self-improvement obligations, or a role
residual as hypotheses.

The missing successor construction needs:

- the Section 6 role residual, via `MainFormalRoleInductionWitness.ofMainInduction`;
- the post-role projective-completion residual, from the line-130
  orthonormalization and completion estimates.

---

## 4. Quantifying the "Sorry-Free but Not Complete" Pattern

| Layer | Declarations with proofs | Declarations that wire to downstream | Gap |
|-------|------------------------|--------------------------------------|-----|
| SelfImprovement | ~50 theorems/lemmas | 2 paper theorem statements (`selfImprovementHelper`, `selfImprovement`) | The paper statements are visible; their remaining derivations are tracked proof gaps |
| SelfImprovement sub-lemmas (slackness, matrix bridge) | ~15 proved lemmas | 0 called from MI or MT | Entirely orphan |
| MainInductionStep | `selfImprovementInInductionSection`, `SelfImprovementData.ofSliceObligations`, `ldPastingInInductionSection`, `mainInductionByRecursionOnM` | Internal assembly remains in `MainTheorems.lean` | `mainInductionByRecursionOnM` takes `hselfObligation` as an internal input; the public wrapper has been removed |
| MainTheorem | `mainFormal`, `mainFormal_ofProjectiveCompletionTransportWitness` | Paper-facing theorem plus proved final transport from a constructed completion residual | Role-residual and post-role completion constructions remain tracked proof gaps |

---

## 5. Assessment

### Is the concern real?

**Yes.** The earlier formalization pattern really did risk replacing proof work
by additional hypotheses:

1. **Lean compiles** — all individual lemmas in SelfImprovement, Pasting, and
   MainInductionStep compile successfully, while the final theorem still has
   tracked proof obligations in `MainFormal.lean`.

2. The former top-level obligation bundle has been removed.  Some components
   such as helper strong self-consistency, orthonormalization, and final-fields
   assembly are still proved or stated in isolation, but the paper-facing
   theorems keep their missing derivations as tracked proof gaps.

3. The successor gap is the concrete manifestation: the Section 6 theorem must
   derive the restricted-slice recursion and self-improvement outputs from the
   paper hypotheses, rather than receiving them through a public wrapper.

### Is the architecture broken?

The architecture is usable but incomplete.  The assembly functions from
`RoleRegister.lean` describe the intended construction.  A conditional helper is
acceptable only as an explicitly named proof-frontier object with a discharge
plan; it must not be advertised as the paper theorem.  The source theorem itself
must not acquire non-paper bridge hypotheses.  What remains missing is an
internal proof that supplies these inputs from the paper hypotheses.

### What would close the gap?

The correct closure route is to prove the missing recursive induction data,
self-improvement obligations, and repaired completion data from the paper
hypotheses, then call those internal obligations from `mainFormal`.  Adding these
objects as new hypotheses to `mainFormal` would reintroduce the statement drift
which this audit is meant to prevent.

---

## 6. Recommendations

1. **Track the internal obligations explicitly.**  The tracking issue should
   distinguish the paper-facing theorem from the conditional helper, and should
   record that the remaining work is to produce the completion data and
   successor residuals from the paper hypotheses.

2. **Keep only source-relevant helper content in the public Section 9 API.**
   The direct matrix-to-helper wrappers from the former
   `SdpMatrixHelperBridge.lean` module and the unused orthonormalization input
   constructor wrappers have been deleted.  The remaining slackness-carrying
   helper route should be extended only by proving source-derived construction
   theorems, not by reintroducing unused proof-debt packages.

3. **Coordinate with the proof-debt tracking issue.**  New repair work should
   be linked from #1458 and should state whether it discharges an internal
   obligation, restores a paper-facing theorem statement, or only records a
   conditional helper.

4. **Keep blueprint tags paper-facing.**  A theorem block with a paper label
   should point to the paper-facing declaration.  Conditional helpers belong in
   remarks or implementation notes, and should not be used to justify a
   `\leanok` claim for the paper theorem.

---

## 7. File Reference

| File | Role |
|------|------|
| `MIPStarRE/LDT/SelfImprovement/Defs.lean` | SDP witnesses, error functions, `averagedSandwichedPolynomialSubMeas` |
| `MIPStarRE/LDT/SelfImprovement/Theorems/Statements.lean` | `SelfImprovementHelperConclusion`, `SelfImprovementConclusion`, etc.; the former `SelfImprovementObligations` bundle has been removed |
| `MIPStarRE/LDT/SelfImprovement/Theorems/Results/SelfImprovementTop/Core.lean` | `selfImprovementHelper`, `selfImprovement`; the former `selfImprovementFromObligations` theorem has been removed |
| `MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperSSC/` | Proof of `helperStrongSelfConsistency` (internal) |
| `MIPStarRE/LDT/SelfImprovement/Theorems/Results/BoundednessTransport.lean` | Proof of `finalFields` (internal) |
| `MIPStarRE/LDT/SelfImprovement/Theorems/Results/SdpMatrixHelperBridge.lean` | Removed orphan module; direct SDP-to-helper wrappers no longer exist |
| `MIPStarRE/LDT/SelfImprovement/Theorems/Results/SelfImprovementTop/ResidualDomination.lean` | Removed compatibility module; top-level residual-domination variants no longer exist |
| `MIPStarRE/LDT/SelfImprovement/Theorems/OrthonormalizationInputConstructors.lean` | Removed orphan module; unused obligation-package constructors no longer exist |
| `MIPStarRE/LDT/SelfImprovement/MatrixRealization.lean` | Matrix-level SDP realization (used by orphan SDP bridges only) |
| `MIPStarRE/LDT/Pasting/Core.lean` | `ldPasting` — consumed by `ldPastingInInductionSection` |
| `MIPStarRE/LDT/MainInductionStep/Theorems/SelfImprovementBridge/Core.lean` | `selfImprovementInInductionSection`, `SelfImprovementData.ofSliceObligations`, `ldPastingInInductionSection` |
| `MIPStarRE/LDT/MainInductionStep/Theorems/MainTheorems.lean` | `mainInduction`, `mainInductionBaseCase`, `mainInductionByRecursionOnM` |
| `MIPStarRE/LDT/MainInductionStep/Theorems/PackageConstructors.lean` | `AveragedPastingData.output`, `mainInductionFromPackages` |
| `MIPStarRE/LDT/MainInductionStep/Theorems/PastingAssembly.lean` | `assembleAveragedPastingData` |
| `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean` | `mainFormal` and `mainFormal_ofProjectiveCompletionTransportWitness`; paper theorem plus proved final transport |
| `MIPStarRE/LDT/Test/MainTheorem/RoleRegister.lean` | Role-register residual constructors routed through Section 6 `mainInduction` |
| `MIPStarRE/LDT/Test/MainTheorem/OrdinaryRestriction/Basic.lean` | Ordinary restricted-slice weighted bounds and recursive-slice targets |
| `MIPStarRE/LDT/Test/MainTheorem/AnswerValuedRestriction.lean` | Answer-valued restricted-slice weighted bounds and recursive-slice targets |
