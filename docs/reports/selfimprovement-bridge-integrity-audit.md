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
`mainFormal_ofProjectiveCompletionResidual` is retained as useful proof content,
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

1. **`helperStrongSelfConsistency`**: `HelperStrongSelfConsistencyInput` — the
   averaged `Hhat` is stably self-consistent (`BipartiteSSCRel` at level
   `selfImprovementHelperError`).
2. **`orthonormalization`**: `OrthonormalizationInput` — converts
   `BipartiteSSCRel` into `OrthonormalizationInput` (spectral-truncation +
   locality-preserving repair witnesses).
3. **`finalFields`**: `FinalFieldsInput` — the remaining completeness,
   point-consistency, self-closeness, and projective-residual conclusions are
   derivable from the helper+orthonormalization+data-processing outputs.

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
SelfImprovementPackage.ofSliceObligations   (Core.lean)
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
  └─ Calls PerSliceInductionPackage.ofRecursion (induction)
  └─ Calls hselfObligation : PerSliceInductionPackage → SelfImprovementPackage
  └─ Calls assembleAveragedPastingInput (builds AveragedPastingInput from SelfImprovementPackage)
  └─ Calls mainInductionFromPackages
       └─ Calls AveragedPastingInput.output
            └─ Calls ldPastingInInductionSection
                 └─ Calls Pasting.ldPasting
```

**The key observation:** `mainInductionByRecursionOnM` takes `hselfObligation`
as an internal proof-stage input.  This `hselfObligation` must produce a
`SelfImprovementPackage` from a `PerSliceInductionPackage`.  It is not a
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
`MainFormalRolePackageResidual.ofMainInductionLargeK`, whose successor branch is
the tracked `sorry` in `MainInductionStep.mainInduction`.  Once the role
residual and post-role completion residual are available, the proved theorem
`mainFormal_ofProjectiveCompletionResidual` supplies the final three consistency
conclusions.

---

## 2. Orphan Lemmas

These are proved within SelfImprovement but **never called** by anything in
MainInductionStep or MainTheorem:

### 2.1. Slackness-carrying helpers

| Declaration | File | Status |
|------------|------|--------|
| `self_improvement_helper_with_slackness` | `SelfImprovementTop/Core.lean:119` | Proved, orphan |

The former full-conclusion residual-domination variants
`selfImprovementWithSlacknessAndResidualDominationInput` and
`selfImprovementFromSlacknessResidualDominationObligations` were removed by PR
#1539.  The remaining slackness-carrying helper is not a theorem-level
substitute for `selfImprovement`.

These are variants that assume the SDP carries complementary slackness
(`SdpStatementWithSlackness`).  The main pipeline uses
`selfImprovementHelper` (without slackness) because the current SDP wrapper
(`sdp`) does not yet prove strong duality.

### 2.2. SDP matrix helper bridge

The entire module `SelfImprovement/Theorems/Results/SdpMatrixHelperBridge.lean`
contains the following lemmas that are **never imported or called** from
MainInductionStep or MainTheorem:

| Declaration | Line |
|------------|------|
| `selfImprovementHelperWithMatrixSdpSlacknessAndDominance` | 42 |
| `selfImprovementHelperWithCanonicalMatrixSdpSlacknessAndDominance` | 70 |
| `selfImprovementHelperWithCanonicalOptimalPairSdpSlacknessAndDominance` | 110 |
| `selfImprovementHelperWithCanonicalOptimalPairSdpSlackness_of_dualDominatesIdentity` | 134 |

These bridge the matrix-level SDP (in `MatrixRealization/`) with the
slackness-carrying helper conclusion.  PR #1539 removed the former
full-conclusion matrix-SDP residual-domination variants, so this module no
longer produces `selfImprovement` from additional residual, repair, or QXP
hypotheses.

### 2.3. OrthonormalizationInputConstructors

The submodule `SelfImprovement/Theorems/OrthonormalizationInputConstructors/` is
imported by the barrel `Theorems.lean` but **never imported by MainInductionStep
or MainTheorem**.  Its declarations are used only within SelfImprovement's own
submodules.

### 2.4. Used (NOT orphan)

| Module | Used by |
|--------|---------|
| `SelfImprovement/Theorems/OrthonormalizationBridge` | `MainInductionStep/SelfImprovementBridge/Core.lean`, `Test/MainTheorem/OrthonormalizationData.lean` |
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

### 3.3. selfImprovementInInductionSection → SelfImprovementPackage: Internal assembly

`SelfImprovementPackage.ofSliceObligations` calls
`selfImprovementInInductionSection` per slice, using
`SelfImprovementPackage.SliceObligations` only for the concrete restricted-slice
strategies and measurement transports.  The theorem-level Section 9 proof debt
remains in `selfImprovementInInductionSection`, not in an additional package
hypothesis.

### 3.4. SelfImprovementPackage → AveragedPastingInput: ✅ Complete

`assembleAveragedPastingInput` (in `PastingAssembly.lean:420`) converts the
per-slice `SelfImprovementPackage` fields into averaged inputs for the pasting
theorem.

### 3.5. AveragedPastingInput → ldPastingInInductionSection: ✅ Complete

`AveragedPastingInput.output` (in `PackageConstructors.lean:357`) calls
`ldPastingInInductionSection`, which calls `Pasting.ldPasting`.

### 3.6. mainInductionByRecursionOnM → mainFormal completion obligations: INCOMPLETE

The theorem `mainFormal` carries the remaining construction gap directly.  It
does not expose recursive-slice data, self-improvement obligations, or a role
residual as hypotheses.

The missing successor construction needs:

- the Section 6 role residual, via `MainFormalRolePackageResidual.ofMainInductionLargeK`;
- the post-role projective-completion residual, from the line-130
  orthonormalization and completion estimates.

---

## 4. Quantifying the "Sorry-Free but Not Complete" Pattern

| Layer | Declarations with proofs | Declarations that wire to downstream | Gap |
|-------|------------------------|--------------------------------------|-----|
| SelfImprovement | ~50 theorems/lemmas | 2 paper theorem statements (`selfImprovementHelper`, `selfImprovement`) | The paper statements are visible; their remaining derivations are tracked proof gaps |
| SelfImprovement sub-lemmas (slackness, matrix bridge) | ~15 proved lemmas | 0 called from MI or MT | Entirely orphan |
| MainInductionStep | `selfImprovementInInductionSection`, `SelfImprovementPackage.ofSliceObligations`, `ldPastingInInductionSection`, `mainInductionByRecursionOnM` | Internal assembly remains in `MainTheorems.lean` | `mainInductionByRecursionOnM` takes `hselfObligation` as an internal input; the public wrapper has been removed |
| MainTheorem | `mainFormal`, `mainFormal_ofProjectiveCompletionResidual` | Paper-facing theorem plus proved final transport from a constructed completion residual | Role-residual and post-role completion constructions remain tracked proof gaps |

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

2. **Decide fate of the remaining orphan helper lemmas.**  The
   slackness-carrying helper and the matrix-to-helper lemmas in
   `SdpMatrixHelperBridge.lean` are fully proved but not yet used by the
   main induction.  The top-level residual-domination variants have already
   been deleted.  Options for the remaining helper route are: (a) keep it as
   future proof content for strong duality, (b) mark it with `@[deprecated]`
   or move it to a future-work namespace, (c) delete it if the paper proof
   will not use this route.

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
| `MIPStarRE/LDT/SelfImprovement/Theorems/Results/SdpMatrixHelperBridge.lean` | **ORPHAN** — matrix-level SDP bridges |
| `MIPStarRE/LDT/SelfImprovement/Theorems/Results/SelfImprovementTop/ResidualDomination.lean` | Removed compatibility module; top-level residual-domination variants no longer exist |
| `MIPStarRE/LDT/SelfImprovement/Theorems/OrthonormalizationInputConstructors/` | **ORPHAN** — unused outside barrel import |
| `MIPStarRE/LDT/SelfImprovement/MatrixRealization.lean` | Matrix-level SDP realization (used by orphan SDP bridges only) |
| `MIPStarRE/LDT/Pasting/Core.lean` | `ldPasting` — consumed by `ldPastingInInductionSection` |
| `MIPStarRE/LDT/MainInductionStep/Theorems/SelfImprovementBridge/Core.lean` | `selfImprovementInInductionSection`, `SelfImprovementPackage.ofSliceObligations`, `ldPastingInInductionSection` |
| `MIPStarRE/LDT/MainInductionStep/Theorems/MainTheorems.lean` | `mainInduction`, `mainInductionBaseCase`, `mainInductionByRecursionOnM` |
| `MIPStarRE/LDT/MainInductionStep/Theorems/PackageConstructors.lean` | `AveragedPastingInput.output`, `mainInductionFromPackages` |
| `MIPStarRE/LDT/MainInductionStep/Theorems/PastingAssembly.lean` | `assembleAveragedPastingInput` |
| `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean` | `mainFormal` and `mainFormal_ofProjectiveCompletionResidual`; paper theorem plus proved final transport |
| `MIPStarRE/LDT/Test/MainTheorem/RoleRegister.lean` | Role-register residual constructors routed through Section 6 `mainInduction` |
| `MIPStarRE/LDT/Test/MainTheorem/OrdinaryRestriction/Basic.lean` | Ordinary restricted-slice weighted bounds and recursive-slice targets |
| `MIPStarRE/LDT/Test/MainTheorem/AnswerValuedRestriction.lean` | Answer-valued restricted-slice weighted bounds and recursive-slice targets |
