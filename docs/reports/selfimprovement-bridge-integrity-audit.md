# SelfImprovement Bridge Integrity Audit

Date: 2026-05-07
Updated: 2026-05-11, after the source-faithful `mainFormal` repair.

> **Status note, 2026-05-11.**  This report predates the removal of the live
> `MainFormal*RepairedBridge*` route.  References below to
> `mainFormal_ofRepairedBridge` and `MainFormalRepairedBridgeHypotheses` are
> historical descriptions of the earlier conditional assembly.  The current
> MainFormal route uses producer obligations and the match-mass
> `MainFormalBaseBranchBridgeHypotheses` target instead.
Auditor: Research specialist (read-only analysis)
Scope: `MIPStarRE/LDT/SelfImprovement/` → `MIPStarRE/LDT/Pasting/` →
       `MIPStarRE/LDT/MainInductionStep/` → `MIPStarRE/LDT/Test/MainTheorem/`

---

## Executive Summary

The bridge-debt concern is valid.  Several formal interfaces still record
intermediate mathematical obligations as explicit inputs to conditional helper
theorems.  Such helpers may preserve useful downstream proof content, but they
must not be presented as theorems from the paper.

The SelfImprovement module compiles with all its lemmas, the Pasting module
compiles independently, and the MainInductionStep module wires them together in
principle.  The remaining gap is now represented in the correct place:
`mainFormal` is again the paper-facing theorem statement, while
`mainFormal_ofRepairedBridge` is the conditional assembly theorem.  The public
`mainFormal` theorem does not take the repaired bridge as an additional
hypothesis; instead it contains a tracked proof obligation to produce that
bridge from the paper hypotheses.

The architecture is therefore incomplete, but the theorem boundary is no longer
misstated.  The remaining work is to turn the bridge inputs and residual
packages into producer theorems, and then call those producers from the
paper-facing theorem.

---

## 1. Architecture Map

### 1.1. SelfImprovement (Section 9)

**Module:** `MIPStarRE/LDT/SelfImprovement/`

Main theorems:

| Theorem | Location | Produces | Hypotheses |
|---------|----------|----------|------------|
| `selfImprovementHelper` | `SelfImprovementTop/Core.lean:84` | `SelfImprovementHelperConclusion` (T, H, Z) | `IsGood`, SDP |
| `selfImprovement` | `SelfImprovementTop/Core.lean:158` | `SelfImprovementConclusion` (full output) | `helperStrongSelfConsistency`, `orthonormalization`, `finalFields`, `IsGood`, `G` |
| `selfImprovementFromBridgeInputs` | `SelfImprovementTop/Core.lean:285` | `SelfImprovementConclusion` | `SelfImprovementBridgeInputs` + `IsGood` + `G` |

The three hypotheses packaged by `SelfImprovementBridgeInputs` (defined in
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

These three inputs are proved individually within SelfImprovement's leaf
submodules (e.g., `HelperSSC`, `BoundednessTransport`), but they are **not
unconditionally provided** — each is a `Prop` that must be discharged by the
caller of `selfImprovement`.

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
selfImprovementInInductionSection    (Core.lean:65)
  └─ calls SelfImprovement.selfImprovementFromSubMeas
       └─ calls selfImprovement with the three bridge input hypotheses
```

```
SelfImprovementPackage.ofSliceBridgeInputs   (Core.lean:514)
  └─ calls selfImprovementInInductionSection per slice
       └─ using SelfImprovement.SelfImprovementBridgeInputs per slice
```

```
ldPastingInInductionSection   (Core.lean:577)
  └─ calls Pasting.ldPasting  (INDEPENDENT of SelfImprovement call)
```

```
mainInductionByRecursionOnM   (MainTheorems.lean:200)
  └─ Calls PerSliceInductionPackage.ofRecursion (induction)
  └─ Calls hselfProducer : PerSliceInductionPackage → SelfImprovementPackage
  └─ Calls assembleAveragedPastingInput (builds AveragedPastingInput from SelfImprovementPackage)
  └─ Calls mainInductionFromPackages
       └─ Calls AveragedPastingInput.output
            └─ Calls ldPastingInInductionSection
                 └─ Calls Pasting.ldPasting
```

**The key observation:** `mainInductionByRecursionOnM` takes `hselfProducer` as
a hypothesis — it does NOT produce it internally.  This `hselfProducer` must
produce a `SelfImprovementPackage` from a `PerSliceInductionPackage`.  The
published wrapper `mainInductionPublicWrapper` (MainTheorems.lean:311) passes
this hypothesis through to its callers.

### 1.4. MainFormal (Final Assembly)

**Module:** `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean`

The current source-facing theorem `mainFormal` takes the paper hypotheses,
together with the large-`k` and positivity boundary hypotheses tracked elsewhere
in the project.  It does **not** take `hbaseBridge`, role residual data, or final
projective-completion inputs.

The conditional helper `mainFormal_ofRepairedBridge` takes:

- `hbaseBridge`: a producer-shaped assumption for
  `MainFormalRepairedBridgeHypotheses`;
- a successor branch whose residual construction is still a tracked `sorry`.

**Base case (m=1):** Works inside the conditional helper.  The base role
residual is produced by the checked handoff, and `hbaseBridge` supplies the
orthonormalization and diagonal-consistency inputs needed by
`mainFormal_ofRoleResidualAndRepairedBridge`.

**Successor case (m>1):** incomplete.  The comment in `MainFormal.lean`
identifies the missing work as supplying the ordinary or answer-valued recursive
induction witnesses, the per-slice self-improvement package producers, and the
resulting Step 6 witness residual.

#### What's needed in the successor case:

1. A recursive per-slice induction package for the predecessor —
   `MainFormalSuccessorRecursiveSlices` (typed by
   `successorRecursiveSlicesInput` in `RoleRegister.lean`).
2. Self-improvement bridge inputs for the predecessor —
   `MainFormalSuccessorSelfImprovementBridgeInputs` (typed by
   `successorSelfImprovementBridgeInput` in `RoleRegister.lean`).

Both are type aliases for `Prop`-valued functions asking for:
- Per-slice induction conclusions (`ConsRel` with bounded error) for the
  predecessor's restricted strategies
- Per-slice `SelfImprovementBridgeInputs` for the honest slice strategies

#### What exists but is not yet connected:

The assembly functions in `RoleRegister.lean` are all ready:

- `successorOfBridgeInputs` (line 538) — takes `hrec` + `hbridge` →
  `MainFormalRolePackageBranchResidual.successor`
- `answerSuccessorOfInductionPackageAndBridgeInputs` (line 628) — takes
  `hinduction` + `hbridge` → `MainFormalRolePackageBranchResidual.answerSuccessor`
- Their corresponding `rolePackageResidual_of*` wrappers produce
  `MainFormalRolePackageResidual`

The gap is now a producer gap rather than a statement-signature gap.  The
successor branch in `mainFormal_ofRepairedBridge` still has
`hprojectiveCompletionResidual := sorry` because the proof has not yet produced
the successor induction package and self-improvement bridge inputs from the
paper hypotheses.

---

## 2. Orphan Lemmas

These are proved within SelfImprovement but **never called** by anything in
MainInductionStep or MainTheorem:

### 2.1. Slackness-carrying helpers

| Declaration | File | Status |
|------------|------|--------|
| `self_improvement_helper_with_slackness` | `SelfImprovementTop/Core.lean:119` | Proved, orphan |
| `selfImprovementWithSlacknessAndResidualDominationInput` | `SelfImprovementTop/ResidualDomination.lean:81` | Proved, orphan |
| `selfImprovementFromSlacknessResidualDominationBridgeInputs` | `SelfImprovementTop/ResidualDomination.lean:166` | Proved, orphan |

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

### 3.1. selfImprovementHelper → selfImprovement: ✅ Complete

`selfImprovementHelper` produces `SelfImprovementHelperConclusion`, which
`selfImprovement` consumes via:
```lean
rcases selfImprovementHelper params strategy eps delta gamma hgood nu G with
  ⟨T, Hhat, Z, hhelper⟩
```
Then `hhelper` feeds into the three explicit hypotheses.

### 3.2. selfImprovement → selfImprovementInInductionSection: ✅ Complete

`selfImprovementInInductionSection` calls `SelfImprovement.selfImprovementFromSubMeas`
directly, which calls `selfImprovement` with the bridge input hypotheses.

### 3.3. selfImprovementInInductionSection → SelfImprovementPackage: ✅ Complete

`SelfImprovementPackage.ofSliceBridgeInputs` calls
`selfImprovementInInductionSection` per slice, using the slice-level bridge inputs
from `SelfImprovementPackage.SliceBridgeInputs`.

### 3.4. SelfImprovementPackage → AveragedPastingInput: ✅ Complete

`assembleAveragedPastingInput` (in `PastingAssembly.lean:420`) converts the
per-slice `SelfImprovementPackage` fields into averaged inputs for the pasting
theorem.

### 3.5. AveragedPastingInput → ldPastingInInductionSection: ✅ Complete

`AveragedPastingInput.output` (in `PackageConstructors.lean:357`) calls
`ldPastingInInductionSection`, which calls `Pasting.ldPasting`.

### 3.6. mainInductionByRecursionOnM → mainFormal bridge producer: INCOMPLETE

The conditional helper `mainFormal_ofRepairedBridge` still has a tracked `sorry`
in the successor branch.  The source-facing theorem `mainFormal` also has a
tracked proof obligation whose purpose is to derive the repaired bridge consumed
by that helper.  These are not new assumptions on the paper theorem.

The missing successor construction needs:

- A recursive per-slice induction package for the predecessor
- Self-improvement bridge inputs for the predecessor slices
- The ordinary or answer-valued role residual used by the final Step 6 assembly

The wiring functions (`successorOfBridgeInputs`, `answerSuccessorOfBridgeInputs`,
and their residual constructors) exist in `RoleRegister.lean`, but the
source-facing theorem still lacks the producer theorem that constructs their
inputs from the paper hypotheses.

---

## 4. Quantifying the "Sorry-Free but Not Complete" Pattern

| Layer | Declarations with proofs | Declarations that wire to downstream | Gap |
|-------|------------------------|--------------------------------------|-----|
| SelfImprovement | ~50 theorems/lemmas | 3 public theorems (`selfImprovementHelper`, `selfImprovement`, `selfImprovementFromBridgeInputs`) | All three take explicit hypotheses; internal sub-lemmas are proved but the bridge inputs are not discharged internally |
| SelfImprovement sub-lemmas (slackness, matrix bridge) | ~15 proved lemmas | 0 called from MI or MT | Entirely orphan |
| MainInductionStep | `selfImprovementInInductionSection`, `SelfImprovementPackage.ofSliceBridgeInputs`, `ldPastingInInductionSection`, `mainInductionByRecursionOnM` | All wired together in `MainTheorems.lean` | `mainInductionByRecursionOnM` takes `hselfProducer` as hypothesis; `mainInductionPublicWrapper` passes this through |
| MainTheorem | `mainFormal`, `mainFormal_ofRepairedBridge` | Paper-facing theorem separated from conditional bridge assembly | Repaired bridge producer and successor residual remain tracked proof obligations |

---

## 5. Assessment

### Is the concern real?

**Yes.** The earlier formalization pattern really did risk replacing proof work
by additional hypotheses:

1. **Lean compiles** — all individual lemmas in SelfImprovement, Pasting, and
   MainInductionStep compile successfully, while the final theorem still has
   tracked proof obligations in `MainFormal.lean`.

2. The three bridge inputs
   (`helperStrongSelfConsistency`, `orthonormalization`, `finalFields`) are
   separately stated as hypotheses for conditional interfaces.  Some components
   are proved in isolation within SelfImprovement's submodules, but the
   assertion that the full bridge input package is produced from every good
   strategy is not yet available at the source-facing call site.

3. The successor gap is the concrete manifestation: the final assembly needs
   `SelfImprovementBridgeInputs` for each predecessor slice, together with the
   corresponding predecessor induction package.

### Is the architecture broken?

The architecture is usable but incomplete.  The wiring functions from
`RoleRegister.lean` describe the intended assembly, and conditional helpers are
legitimate local proof-frontier objects.  The source theorem itself, however,
must not acquire non-paper bridge hypotheses.  What remains missing is a
producer theorem that supplies the conditional inputs from the paper hypotheses.

### What would close the gap?

The correct closure route is to prove producer theorems for the missing
recursive induction package, self-improvement bridge inputs, and repaired
completion bridge, then call those producers from `mainFormal`.  Adding these
objects as new hypotheses to `mainFormal` would reintroduce the statement drift
which this audit is meant to prevent.

---

## 6. Recommendations

1. **Track the producer obligations explicitly.**  The tracking issue should
   distinguish the paper-facing theorem from the conditional helper, and should
   record that the remaining work is to produce the repaired bridge and
   successor residuals from the paper hypotheses.

2. **Decide fate of orphan lemmas.**  The ~15 slackness-carrying and
   matrix-bridge lemmas in `SdpMatrixHelperBridge.lean` and
   `SelfImprovementTop/ResidualDomination.lean` are fully proved but never
   called.  Options: (a) keep them as future-proofing for the strong-duality
   proof, (b) mark them with `@[deprecated]` or move them to a
   `FutureWork/` directory, (c) delete them.

3. **Coordinate with the bridge-debt tracking issue.**  New repair work should
   be linked from #1458 and should state whether it discharges a producer
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
| `MIPStarRE/LDT/SelfImprovement/Theorems/Statements.lean` | `SelfImprovementBridgeInputs`, `SelfImprovementHelperConclusion`, `SelfImprovementConclusion`, etc. |
| `MIPStarRE/LDT/SelfImprovement/Theorems/Results/SelfImprovementTop/Core.lean` | `selfImprovementHelper`, `selfImprovement`, `selfImprovementFromBridgeInputs` |
| `MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperSSC/` | Proof of `helperStrongSelfConsistency` (internal) |
| `MIPStarRE/LDT/SelfImprovement/Theorems/Results/BoundednessTransport.lean` | Proof of `finalFields` (internal) |
| `MIPStarRE/LDT/SelfImprovement/Theorems/Results/SdpMatrixHelperBridge.lean` | **ORPHAN** — matrix-level SDP bridges |
| `MIPStarRE/LDT/SelfImprovement/Theorems/Results/SelfImprovementTop/ResidualDomination.lean` | **ORPHAN** — slackness-carrying self-improvement variants |
| `MIPStarRE/LDT/SelfImprovement/Theorems/OrthonormalizationInputConstructors/` | **ORPHAN** — unused outside barrel import |
| `MIPStarRE/LDT/SelfImprovement/MatrixRealization.lean` | Matrix-level SDP realization (used by orphan SDP bridges only) |
| `MIPStarRE/LDT/Pasting/Core.lean` | `ldPasting` — consumed by `ldPastingInInductionSection` |
| `MIPStarRE/LDT/MainInductionStep/Theorems/SelfImprovementBridge/Core.lean` | `selfImprovementInInductionSection`, `SelfImprovementPackage.ofSliceBridgeInputs`, `ldPastingInInductionSection` |
| `MIPStarRE/LDT/MainInductionStep/Theorems/MainTheorems.lean` | `mainInductionByRecursionOnM`, `mainInductionPublicWrapper` |
| `MIPStarRE/LDT/MainInductionStep/Theorems/PackageConstructors.lean` | `AveragedPastingInput.output`, `mainInductionFromPackages` |
| `MIPStarRE/LDT/MainInductionStep/Theorems/PastingAssembly.lean` | `assembleAveragedPastingInput` |
| `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean` | `mainFormal` and `mainFormal_ofRepairedBridge`; paper-facing theorem plus conditional bridge assembly |
| `MIPStarRE/LDT/Test/MainTheorem/RoleRegister.lean` | Assembly functions `successorOfBridgeInputs`, etc., awaiting source-level producers |
| `MIPStarRE/LDT/Test/MainTheorem/OrdinaryRestriction/Basic.lean` | `MainFormalSuccessorSelfImprovementBridgeInputs` type definition and constructors |
| `MIPStarRE/LDT/Test/MainTheorem/AnswerValuedRestriction.lean` | Answer-valued counterpart |
