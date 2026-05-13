# SelfImprovement Proof-Obligation Integrity Audit

Date: 2026-05-07
Updated: 2026-05-12, after the source-faithful `mainFormal` repair and
internal-obligation renaming.

Status note, 2026-05-13: this report predates PR #1539.  The
`SelfImprovementObligations` record, the top-level
`selfImprovementFromObligations` theorem, the matrix-SDP residual-domination
assembly theorems, and the Section 3/6 successor-boundary conditional API have
been removed.  The present paper-alignment policy is to preserve the theorem
statements from the paper and to leave the remaining derivations as tracked
`sorry` sites until they are proved.

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
`mainFormal` is again the paper-facing theorem statement, while
`mainFormal_ofInternalObligations` is the internal-obligation assembly theorem.
The public `mainFormal` theorem does not take completion data as an additional
hypothesis; instead it contains tracked proof obligations to produce that data
from the paper hypotheses.

The architecture is therefore incomplete, but the theorem boundary is no longer
misstated.  The remaining work is to derive the obligations and residual records
inside the proof, and then discharge those obligations from the paper-facing
theorem.

---

## 1. Architecture Map

### 1.1. SelfImprovement (Section 9)

**Module:** `MIPStarRE/LDT/SelfImprovement/`

Main theorems:

| Theorem | Location | Produces | Hypotheses |
|---------|----------|----------|------------|
| `selfImprovementHelper` | `SelfImprovementTop/Core.lean` | `SelfImprovementHelperConclusion` (T, Hhat, Z) | `IsGood`, input consistency, tracked helper obligations |
| `selfImprovement` | `SelfImprovementTop/Core.lean` | `SelfImprovementConclusion` (full output) | paper-shaped hypotheses: `IsGood`, `G`, input consistency |
| `selfImprovementFromObligations` | `SelfImprovementTop/Core.lean` | `SelfImprovementConclusion` | conditional helper: `SelfImprovementObligations` + `IsGood` + `G` |

The three hypotheses recorded by `SelfImprovementObligations` (defined in
`Theorems/Statements.lean:481`):

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
`selfImprovement`.  They are the fields of the conditional helper
`selfImprovementFromObligations`, and the source-facing theorem currently leaves
the derivation from the paper hypotheses as the tracked proof obligation #1515.

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
  └─ calls selfImprovementInInductionSection_ofObligations per slice
       └─ internally completes the input submeasurement
       └─ uses SelfImprovement.SelfImprovementObligations per slice
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
as an internal wrapper input.  This `hselfObligation` must produce a
`SelfImprovementPackage` from a `PerSliceInductionPackage`.  It is not a
hypothesis of the source-facing `mainInduction` theorem; that theorem retains
the paper-shaped statement and the non-base branch is tracked by #1507.

### 1.4. MainFormal (Final Assembly)

**Module:** `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean`

The current source-facing theorem `mainFormal` takes the paper hypotheses,
together with the large-`k` and positivity boundary hypotheses tracked elsewhere
in the project.  It does **not** take bridge-style data, role residual data, or final
projective-completion inputs.

The internal-obligation helper `mainFormal_ofInternalObligations` is closed
except for two tracked proof obligations: the base-branch completion data and
the successor projective-completion residual.

**Base case (m=1):** Works inside the internal-obligation helper.  The base
role residual is produced by the checked handoff; the remaining completion data
is isolated as `MainFormalBaseBranchCompletionObligations`.

**Successor case (m>1):** incomplete.  The comment in `MainFormal.lean`
identifies the missing work as supplying the ordinary or answer-valued recursive
induction witnesses, the per-slice self-improvement obligations, and the
resulting Step 6 witness residual.

#### What's needed in the successor case:

1. Recursive per-slice induction data for the predecessor —
   `MainFormalSuccessorRecursiveSlices` (typed by
   `successorRecursiveSlicesInput` in `RoleRegister.lean`).
2. Self-improvement obligations for the predecessor —
   `MainFormalSuccessorSelfImprovementObligations` (typed by
   `successorSelfImprovementObligations` in `RoleRegister.lean`).

Both are type aliases for `Prop`-valued functions asking for:
- Per-slice induction conclusions (`ConsRel` with bounded error) for the
  predecessor's restricted strategies
- Per-slice `SelfImprovementObligations` for the honest slice strategies

#### What exists but is not yet connected:

The assembly functions in `RoleRegister.lean` are all ready:

- `successorOfObligations` (line 538) — takes `hrec` + `obligations` →
  `MainFormalRolePackageBranchResidual.successor`
- `answerSuccessorOfInductionPackageAndObligations` (line 628) — takes
  `hinduction` + `obligations` → `MainFormalRolePackageBranchResidual.answerSuccessor`
- Their corresponding `rolePackageResidual_of*` wrappers produce
  `MainFormalRolePackageResidual`

The gap is now a construction gap rather than a statement-signature gap.  The
successor branch in `mainFormal_ofInternalObligations` still has a tracked
proof obligation because the proof has not yet derived the successor induction
data and self-improvement obligations from the paper hypotheses.

---

## 2. Orphan Lemmas

These are proved within SelfImprovement but **never called** by anything in
MainInductionStep or MainTheorem:

### 2.1. Slackness-carrying helpers

| Declaration | File | Status |
|------------|------|--------|
| `self_improvement_helper_with_slackness` | `SelfImprovementTop/Core.lean:119` | Proved, orphan |
| `selfImprovementWithSlacknessAndResidualDominationInput` | `SelfImprovementTop/ResidualDomination.lean:81` | Proved, orphan |
| `selfImprovementFromSlacknessResidualDominationObligations` | `SelfImprovementTop/ResidualDomination.lean:166` | Proved, orphan |

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
| `selfImprovementWithCanonicalMatrixSdpSlacknessAndResidualDomination` | 167 |
| `selfImprovementWithCanonicalMatrixSdpSlacknessAndResidualDominationInput` | 287 |
| `selfImprovementWithCanonicalOptimalPairSdpSlacknessAndResidualDomination` | 353 |
| `selfImprovementWithCanonicalOptimalPairSdpSlacknessAndResidualDominationInput` | 407 |
| `selfImprovementWithCanonicalOptimalPairAndQXPResidualDomination` | 460 |
| `selfImprovementWithCanonicalOptimalPairAndQXPRepairAndResidualDomination` | 511 |

These bridge the matrix-level SDP (in `MatrixRealization/`) with the abstract
`selfImprovement` theorem.  They are **designed for a matrix-based proof path**
that is not yet wired into the main induction.

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
theorem.  The source-facing theorem `selfImprovement` now leaves this as the
tracked proof obligation #1515, rather than taking those three inputs as
hypotheses.  The helper-stage strong self-consistency derivation is separately
tracked by #1514.

### 3.2. selfImprovement → selfImprovementInInductionSection: Conditional only

The paper-facing theorem `selfImprovementInInductionSection` has the expected
submeasurement input and leaves the induction-section proof as #1503.  The
conditional helper `selfImprovementInInductionSection_ofObligations` performs
the current checked assembly: it internally completes the submeasurement to a
measurement and then calls `SelfImprovement.selfImprovementFromObligations`.

### 3.3. selfImprovementInInductionSection → SelfImprovementPackage: Conditional only

`SelfImprovementPackage.ofSliceObligations` calls
`selfImprovementInInductionSection_ofObligations` per slice, using the
slice-level obligations from `SelfImprovementPackage.SliceObligations`.  This
keeps the proof-stage assumptions inside the conditional package constructor;
they should not be reintroduced into the paper-facing theorem.

### 3.4. SelfImprovementPackage → AveragedPastingInput: ✅ Complete

`assembleAveragedPastingInput` (in `PastingAssembly.lean:420`) converts the
per-slice `SelfImprovementPackage` fields into averaged inputs for the pasting
theorem.

### 3.5. AveragedPastingInput → ldPastingInInductionSection: ✅ Complete

`AveragedPastingInput.output` (in `PackageConstructors.lean:357`) calls
`ldPastingInInductionSection`, which calls `Pasting.ldPasting`.

### 3.6. mainInductionByRecursionOnM → mainFormal completion obligations: INCOMPLETE

The internal helper `mainFormal_ofInternalObligations` still has tracked proof
obligations in the successor and base-completion branches.  The source-facing
theorem `mainFormal` keeps those obligations inside the proof.  They are not new
assumptions on the paper theorem.

The missing successor construction needs:

- Recursive per-slice induction data for the predecessor
- Self-improvement obligations for the predecessor slices
- The ordinary or answer-valued role residual used by the final Step 6 assembly

The wiring functions (`successorOfObligations`, `answerSuccessorOfObligations`,
and their residual constructors) exist in `RoleRegister.lean`, but the
source-facing theorem still lacks the obligation discharger that constructs
their inputs from the paper hypotheses.

---

## 4. Quantifying the "Sorry-Free but Not Complete" Pattern

| Layer | Declarations with proofs | Declarations that wire to downstream | Gap |
|-------|------------------------|--------------------------------------|-----|
| SelfImprovement | ~50 theorems/lemmas | 3 public theorems (`selfImprovementHelper`, `selfImprovement`, `selfImprovementFromObligations`) | All three take explicit hypotheses; internal sub-lemmas are proved but the obligations are not discharged internally |
| SelfImprovement sub-lemmas (slackness, matrix bridge) | ~15 proved lemmas | 0 called from MI or MT | Entirely orphan |
| MainInductionStep | `selfImprovementInInductionSection`, `SelfImprovementPackage.ofSliceObligations`, `ldPastingInInductionSection`, `mainInductionByRecursionOnM` | All wired together in `MainTheorems.lean` | `mainInductionByRecursionOnM` takes `hselfObligation` as an internal wrapper input; `mainInductionPublicWrapper` passes this through |
| MainTheorem | `mainFormal`, `mainFormal_ofInternalObligations` | Paper-facing theorem separated from internal-obligation assembly | Completion obligations and the successor residual remain tracked proof obligations |

---

## 5. Assessment

### Is the concern real?

**Yes.** The earlier formalization pattern really did risk replacing proof work
by additional hypotheses:

1. **Lean compiles** — all individual lemmas in SelfImprovement, Pasting, and
   MainInductionStep compile successfully, while the final theorem still has
   tracked proof obligations in `MainFormal.lean`.

2. The three obligations
   (`helperStrongSelfConsistency`, `orthonormalization`, `finalFields`) are
   separately stated as hypotheses for conditional interfaces.  Some components
   are proved in isolation within SelfImprovement's submodules, but the
   assertion that the full `SelfImprovementObligations` record is derived from
   every good strategy is not yet available at the source-facing call site.

3. The successor gap is the concrete manifestation: the final assembly needs
   `SelfImprovementObligations` for each predecessor slice, together with the
   corresponding predecessor induction data.

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

2. **Decide fate of orphan lemmas.**  The ~15 slackness-carrying and
   matrix-bridge lemmas in `SdpMatrixHelperBridge.lean` and
   `SelfImprovementTop/ResidualDomination.lean` are fully proved but never
   called.  Options: (a) keep them as future-proofing for the strong-duality
   proof, (b) mark them with `@[deprecated]` or move them to a
   `FutureWork/` directory, (c) delete them.

3. **Coordinate with the proof-debt tracking issue.**  New repair work should
   be linked from #1458 and should state whether it discharges an internal
   obligation, restores a paper-facing theorem statement, or only records a
   conditional helper.

4. **Keep blueprint tags source-facing.**  A theorem block with a paper label
   should point to the paper-facing declaration.  Conditional helpers belong in
   remarks or implementation notes, and should not be used to justify a
   `\leanok` claim for the paper theorem.

---

## 7. File Reference

| File | Role |
|------|------|
| `MIPStarRE/LDT/SelfImprovement/Defs.lean` | SDP witnesses, error functions, `averagedSandwichedPolynomialSubMeas` |
| `MIPStarRE/LDT/SelfImprovement/Theorems/Statements.lean` | `SelfImprovementObligations`, `SelfImprovementHelperConclusion`, `SelfImprovementConclusion`, etc. |
| `MIPStarRE/LDT/SelfImprovement/Theorems/Results/SelfImprovementTop/Core.lean` | `selfImprovementHelper`, `selfImprovement`, `selfImprovementFromObligations` |
| `MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperSSC/` | Proof of `helperStrongSelfConsistency` (internal) |
| `MIPStarRE/LDT/SelfImprovement/Theorems/Results/BoundednessTransport.lean` | Proof of `finalFields` (internal) |
| `MIPStarRE/LDT/SelfImprovement/Theorems/Results/SdpMatrixHelperBridge.lean` | **ORPHAN** — matrix-level SDP bridges |
| `MIPStarRE/LDT/SelfImprovement/Theorems/Results/SelfImprovementTop/ResidualDomination.lean` | **ORPHAN** — slackness-carrying self-improvement variants |
| `MIPStarRE/LDT/SelfImprovement/Theorems/OrthonormalizationInputConstructors/` | **ORPHAN** — unused outside barrel import |
| `MIPStarRE/LDT/SelfImprovement/MatrixRealization.lean` | Matrix-level SDP realization (used by orphan SDP bridges only) |
| `MIPStarRE/LDT/Pasting/Core.lean` | `ldPasting` — consumed by `ldPastingInInductionSection` |
| `MIPStarRE/LDT/MainInductionStep/Theorems/SelfImprovementBridge/Core.lean` | `selfImprovementInInductionSection`, `SelfImprovementPackage.ofSliceObligations`, `ldPastingInInductionSection` |
| `MIPStarRE/LDT/MainInductionStep/Theorems/MainTheorems.lean` | `mainInductionByRecursionOnM`, `mainInductionPublicWrapper` |
| `MIPStarRE/LDT/MainInductionStep/Theorems/PackageConstructors.lean` | `AveragedPastingInput.output`, `mainInductionFromPackages` |
| `MIPStarRE/LDT/MainInductionStep/Theorems/PastingAssembly.lean` | `assembleAveragedPastingInput` |
| `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean` | `mainFormal` and `mainFormal_ofInternalObligations`; paper-facing theorem plus internal-obligation assembly |
| `MIPStarRE/LDT/Test/MainTheorem/RoleRegister.lean` | Assembly functions `successorOfObligations`, etc., awaiting source-level obligation dischargers |
| `MIPStarRE/LDT/Test/MainTheorem/OrdinaryRestriction/Basic.lean` | `MainFormalSuccessorSelfImprovementObligations` type definition and constructors |
| `MIPStarRE/LDT/Test/MainTheorem/AnswerValuedRestriction.lean` | Answer-valued counterpart |
