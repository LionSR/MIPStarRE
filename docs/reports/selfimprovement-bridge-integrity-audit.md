# SelfImprovement Proof-Obligation Integrity Audit

Date: 2026-05-07
Updated: 2026-05-12, after the source-faithful `mainFormal` repair and
internal-obligation renaming.

Status note, 2026-05-13: this report predates PR #1539.  The
`SelfImprovementObligations` record, the top-level
`selfImprovementFromObligations` theorem, the matrix-SDP residual-domination
assembly theorems, and the Section 3/6 successor-boundary conditional API have
been removed.  The later 2026-05-13 PR update also removes
`mainInductionPublicWrapper` and `answerMainInductionPublicWrapper`.  Subsequent
repairs split the printed induction theorem from the corrected large-\(k\) Lean
interface.  The later status notes below supersede the successor-frontier
description in the body of this historical report.  The present
paper-alignment policy is to preserve the theorem statements from the paper and
to leave missing source derivations as tracked `sorry` sites until they are
proved.

Status note, 2026-05-13 after PR #1547 and the follow-up orthonormalization
cleanup: the residual-domination orthonormalization route and the bundled
`OrthonormalizationInput` records have also been removed.  The retained Section
9 orthonormalization proof content is the direct spectral-truncation statement
`spectralTruncationStatement_of_sourceAlmostProjective`.  The temporary
`SelfImprovement/Theorems/OrthonormalizationSpectral.lean` module has also been
retired.  Subsequent repairs
discharged the locality-preserving projectivization route inside the
source-facing self-improvement theorem; it is no longer a live Section 9 proof
gap.

Historical status note, 2026-05-20: the blueprint separated the printed source
theorems from the then-current Lean interfaces for `mainFormal` and
`mainInduction`.  At that snapshot the source-labelled statements linked to
source-shaped Lean statements with named proof obligations, including a
temporary source-range chain for `md ≤ k < 400md`.  The later 2026-05-23 status
note supersedes that classification: the factor-\(400\) condition is now a
confirmed statement correction, not a live source-range proof obligation.

Historical status note, 2026-05-20 after the Section 9 repair: the source-facing
`selfImprovement` theorem and the induction-section reformulation
`selfImprovementInInductionSection` are now axiom-clean in
`MIPStarRE/LDT/Test/AxiomAudit.lean`.  The former #1515 and #1503
self-improvement proof gaps should therefore be read as historical entries in
this report.  At that snapshot the live transitive proof frontier was the
Section 6 small-error successor construction; this has since been discharged
for the corrected large-\(k\) interface.

Status note, 2026-05-22 after the answer-valued successor repair: the Section 6
small-error successor construction is now checked for the corrected large-`k`
interface.

Status note, 2026-05-23 after the source-boundary cleanup: the project has
adopted the factor-\(400\) correction as a confirmed statement correction and
has added the final-theorem nonzero sampling boundary \(0<k\).  Under these
corrected statements, the main induction source theorem and the final
two-space source theorem are proof-complete; the remaining differences from the
printed paper are these documented boundary corrections, not hidden proof
obligations.

Auditor: Research specialist (read-only analysis)
Scope: `MIPStarRE/LDT/SelfImprovement/` → `MIPStarRE/LDT/Pasting/` →
       `MIPStarRE/LDT/MainInductionStep/` → `MIPStarRE/LDT/Test/MainTheorem/`

---

## Executive Summary

This executive summary is historical.  At the audited snapshot, several formal
interfaces still recorded intermediate mathematical obligations as explicit
inputs to conditional helper theorems.  Those interfaces have since been
removed or replaced by checked construction theorems under the corrected source
statements.

The SelfImprovement module compiles with all its lemmas, the Pasting module
compiles independently, and the MainInductionStep module wires them together in
principle.  The remaining gap is now represented in the current Lean interfaces
rather than as extra hypotheses on the source-labelled blueprint theorems.  The
proved final-transport theorem
`mainFormal_ofProjectiveCompletionTransportWitness` is retained as useful proof content,
but no public theorem supplies completion data as an additional hypothesis.

Under the current corrected theorem statements, the architecture described
above is no longer incomplete.  The theorem boundary differs from the literal
paper only by the documented factor-\(400\) large-\(k\) correction and the
nonzero-sampling boundary \(0<k\).

---

## 1. Architecture Map

### 1.1. SelfImprovement (Section 9)

**Module:** `MIPStarRE/LDT/SelfImprovement/`

Main theorems:

| Theorem | Location | Produces | Hypotheses |
|---------|----------|----------|------------|
| `selfImprovementHelper` | `SelfImprovementTop/Core.lean` | `SelfImprovementHelperConclusion` (T, Hhat, Z) | `IsGood`, input consistency; helper-stage estimates are assembled internally |
| `selfImprovement` | `SelfImprovementTop/Core.lean` | `SelfImprovementConclusion` (full output) | paper hypotheses: `IsGood`, `G`, input consistency |

Historically, the deleted `SelfImprovementObligations` bundle recorded three
proof-stage inputs:

1. **`helperStrongSelfConsistency`**: the former
   `HelperStrongSelfConsistencyInput` has been removed.  The helper SSC
   conclusion is now produced by
   `helper_strong_self_consistency_of_helper_conclusion` from the checked
   package of intermediate estimates
   `HelperStrongSelfConsistencyBounds`; this package is assembled
   internally from the self-consistency, local-variance, and residual estimates.
2. **`orthonormalization`**: the former `OrthonormalizationInput` bundle has
   been removed.  The retained Section 9 API records the spectral-truncation
   conversion and uses the checked locality-preserving orthonormalization route
   inside the proof of `selfImprovement`, not as a supplied theorem hypothesis.
3. **`finalFields`**: the former `FinalFieldsInput` bundle has been removed.
   The completeness, point-consistency, self-closeness, and
   projective-residual estimates are derived in the proof of `selfImprovement`
   by the final-field assembly lemmas.

These three inputs are no longer hypotheses of the paper-facing theorem
`selfImprovement`.  The former conditional helper
`selfImprovementFromObligations` has been removed, and the current theorem is
axiom-clean in `MIPStarRE/LDT/Test/AxiomAudit.lean`.

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

This is where SelfImprovement and Pasting are wired together.  The current
self-improvement assembly lives in
`Theorems/SelfImprovementAssembly/Core.lean`, with the answer-valued slice route
in `Theorems/SelfImprovementAssembly/AnswerSlice.lean`.

**Wiring chain:**

```
selfImprovementInInductionSection    (SelfImprovementAssembly/Core.lean)
  └─ checked induction-section reformulation of selfImprovement
```

```
AnswerSelfImprovementData.ofSelfImprovementInInductionSection
AnswerSelfImprovementData.ofAnswerCarrier
SelfImprovementData.ofAnswer
  └─ call the induction-section self-improvement theorem per answer-valued slice
     and then forget the answer-valued data to the ordinary pasting interface
```

```
ldPastingInInductionSection   (Core.lean)
  └─ calls Pasting.ldPasting  (INDEPENDENT of SelfImprovement call)
```

```
mainInductionSuccessorNext_ofSmallErrorConstruction   (MainTheorems.lean)
  └─ named source-faithful successor construction obligation
     ├─ recursive predecessor induction argument
     ├─ answer-valued self-improvement, or a prior low-degree support theorem
     │  giving ordinary slice realization
     └─ checked assembly through selfImprovementInInductionSection and ldPasting
```

**The key observation:** the current corrected large-\(k\) Lean interface for
`mainInduction` does not take a self-improvement package as a public hypothesis.
The remaining non-base work is isolated in
`mainInductionSuccessorNext_ofSmallErrorConstruction`.  The source-labelled
`thm:main-induction` remains separate in the printed paper form, while the
corrected large-\(k\) interface records the successor proof frontier tracked by
#1507.

### 1.4. MainFormal (Final Assembly)

**Module:** `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean`

The current Lean interface `mainFormal` takes the same-space strategy input,
together with the large-`k` and positivity boundary hypotheses tracked elsewhere
in the project.  It does **not** take bridge-style data, role residual data, or final
projective-completion inputs.  The printed source theorem is kept as a separate
blueprint statement until the heterogeneous strategy interface is supplied.

The current same-space interface follows the checked branch structure: the
vacuous branch is closed by `mainFormal_trivial_witness`, the non-vacuous branch
invokes the Section 6 role-register witness, the post-role
projective-completion construction target, and the final transport.  The
remaining proof gap is transitive through Section 6, namely
`mainInductionSuccessorNext_ofSmallErrorConstruction`; it is not an additional
hypothesis of `mainFormal`.

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

### 2.3. Retired orthonormalization spectral layer

The former `SelfImprovement/Theorems/OrthonormalizationBridge.lean` module has
since been retired after it was narrowed to a spectral-only module.  Its only
substantive role was to repackage the already proved
`spectralTruncationStatement_of_sourceAlmostProjective` construction for the
option-completed helper measurement.

### 2.4. Used (NOT orphan)

| Module | Used by |
|--------|---------|
| `SelfImprovement/Theorems/Results/HelperSSC` | `SelfImprovementTop/Core.lean` (via `selfImprovement`) |
| `SelfImprovement/Theorems/Results/BoundednessTransport` | `SelfImprovementTop/Core.lean` (via `selfImprovement`) |
| `SelfImprovement/Theorems/Results/SelfImprovementTop/Core.lean` | `MainInductionStep/SelfImprovementAssembly/Core.lean` |
| `Pasting/Core.lean` → `ldPasting` | `MainInductionStep/Theorems/SelfImprovementAssembly/Core.lean` through `ldPastingInInductionSection`, then the successor-stage assembly |

---

## 3. Bridge Points — Complete vs. Incomplete

### 3.1. selfImprovementHelper → selfImprovement: Complete source route

`selfImprovementHelper` produces `SelfImprovementHelperConclusion`, which
the Section 9 proof uses as its first stage.  The helper strong
self-consistency package, the orthonormalization step, and the final-field
estimates are now assembled inside `selfImprovement`.  The former #1515 and
#1514 proof gaps are historical; the current paper-facing theorem
`selfImprovement` is axiom-clean in `AxiomAudit.lean`.

### 3.2. selfImprovement → selfImprovementInInductionSection: Complete

The theorem `selfImprovementInInductionSection` has the expected
submeasurement input and is proved by applying `SelfImprovement.selfImprovement`
and transporting the resulting fields to the induction-section statement.  It
does not take a measurement-completion package or Section 9 obligation bundle as
an extra hypothesis, and it is axiom-clean in `AxiomAudit.lean`.

### 3.3. selfImprovementInInductionSection → SelfImprovementData: Internal assembly

`AnswerSelfImprovementData.ofAnswerCarrier` calls the induction-section
self-improvement theorem per answer-valued slice.  The successor proof then uses
`SelfImprovementData.ofAnswer` to forget the answer-valued data to the ordinary
pasting interface.  Any remaining obstruction is the Section 6 construction of
the appropriate slice profile, not a Section 9 proof debt.

### 3.4. SelfImprovementData → AveragedPastingData: ✅ Complete

`assembleAveragedPastingData` (in `PastingAssembly.lean:420`) converts the
per-slice `SelfImprovementData` fields into averaged inputs for the pasting
theorem.

### 3.5. AveragedPastingData → ldPastingInInductionSection: ✅ Complete

`AveragedPastingData.output` (in `PackageConstructors.lean:357`) calls
`ldPastingInInductionSection`, which calls `Pasting.ldPasting`.

### 3.6. mainInduction source boundary → mainFormal completion targets: historical

At the audited snapshot, the theorem `mainFormal` carried the remaining
construction gap directly.  It did not expose recursive-slice data,
self-improvement obligations, or a role residual as hypotheses.

The following list is historical.  Later repairs discharged the corrected
two-space source-boundary route and reclassified the printed \(k\ge md\) range
as the confirmed \(k\ge400md\) statement correction:

- the printed source range for the Section 6 induction theorem;
- the two-space role-register reduction for the final theorem;
- the post-role projective-completion residual, from the line-130
  orthonormalization and completion estimates.

---

## 4. Quantifying the "Sorry-Free but Not Complete" Pattern

| Layer | Declarations with proofs | Declarations that wire to downstream | Gap |
|-------|------------------------|--------------------------------------|-----|
| SelfImprovement | ~50 theorems/lemmas | 2 paper theorem statements (`selfImprovementHelper`, `selfImprovement`) | Section 9 route is checked and axiom-clean |
| SelfImprovement sub-lemmas (slackness, matrix bridge) | ~15 proved lemmas | Used internally by `selfImprovement` where needed; some historical adapters have been removed | No public substitute for the source theorem |
| MainInductionStep | `selfImprovementInInductionSection`, self-improvement output constructors, `ldPastingInInductionSection`, checked successor assembly lemmas | Internal assembly remains in `MainTheorems.lean`; the broad slice-transport obstruction has been removed, while the narrow `SliceStrategyTransport` constructors remain as Lean-only transport interfaces | Corrected large-\(k\) successor route is proved; the printed range has been superseded by the confirmed \(k\ge400md\) correction |
| MainTheorem | `mainFormal`, `mainFormal_ofProjectiveCompletionTransportWitness` | Corrected two-space source theorem plus proved final transport from a constructed completion witness | Proof-complete under the documented \(k\ge400md\) and \(0<k\) boundary corrections |

---

## 5. Assessment

### Is the concern real?

**Yes.** The earlier formalization pattern really did risk replacing proof work
by additional hypotheses:

1. **Lean compiles** — the SelfImprovement and Pasting routes are now checked,
   while the final theorem route still has the tracked Section 6 successor
   proof obligation in `MainTheorems.lean`.

2. The former top-level obligation bundle has been removed.  Some components
   such as helper strong self-consistency, orthonormalization, and final-fields
   assembly are now proved and used internally by the paper-facing
   self-improvement theorem.

3. The successor gap is now the concrete manifestation: the Section 6 theorem
   must derive the restricted-slice recursion, slice-realization data, and
   pasting inputs from the paper hypotheses, rather than receiving them through
   a public wrapper.

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
| `MIPStarRE/LDT/MainInductionStep/Theorems/SelfImprovementAssembly/Core.lean` | `selfImprovementInInductionSection` |
| `MIPStarRE/LDT/MainInductionStep/Theorems/SelfImprovementAssembly/AnswerSlice.lean` | answer-valued carrier self-improvement construction |
| `MIPStarRE/LDT/MainInductionStep/Theorems/MainTheorems.lean` | `mainInduction`, `mainInductionBaseCase`, `mainInductionSuccessorNext_ofSmallErrorConstruction` |
| `MIPStarRE/LDT/MainInductionStep/Theorems/StageDataConstructors.lean` | ordinary and answer-valued stage-data conversions |
| `MIPStarRE/LDT/MainInductionStep/Theorems/PastingAssembly.lean` | `assembleAveragedPastingData` |
| `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean` | source-final statement and obligation, current same-space interface, and proved final transport |
| `MIPStarRE/LDT/Test/MainTheorem/RoleRegister.lean` | role-register witness constructors routed through Section 6 `mainInduction` |
| `MIPStarRE/LDT/Test/MainTheorem/AnswerValuedRestriction.lean` | Answer-valued restricted-slice weighted bounds and recursive-slice targets |
