# SelfImprovement Bridge Integrity Audit

Date: 2026-05-07
Auditor: Research specialist (read-only analysis)
Scope: `MIPStarRE/LDT/SelfImprovement/` → `MIPStarRE/LDT/Pasting/` →
       `MIPStarRE/LDT/MainInductionStep/` → `MIPStarRE/LDT/Test/MainTheorem/`

---

## Executive Summary

**The user's concern is valid.**  "东西没连起来…一开始lean，然后分别放了假设" (things
aren't connected … initially Lean, then they put assumptions separately).

The SelfImprovement module compiles with all its lemmas, the Pasting module
compiles independently, and the MainInductionStep module wires them together in
principle — but the **final assembly at `mainFormal` has one `sorry` in the
successor branch** (line 611 of `MainFormal.lean`).  The individual pieces are
proved, but the "last mile" of the dependency chain — producing the
self-improvement bridge inputs for the successor case — is not yet written.

The architecture is _not_ broken: the wiring functions exist.  The gap is that
`mainFormal` does not take the hypotheses those wiring functions need, and nobody
calls the wiring functions from within `mainFormal`.

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

`mainFormal` (line 507) takes:

- `hbaseBridge`: provides `MainFormalRepairedBridgeHypotheses` for the base case
- A successor branch that is `sorry` (line 611)

**Base case (m=1):** Works.  `hbaseBridge` provides orthonormalization +
diagonal consistency inputs, and `mainFormal_ofRoleResidualAndRepairedBridge`
completes the proof.

**Successor case (m>1):** `sorry`.  The comment says:

> TODO(#931, #834, #422): supply those successor inputs and assemble the
> resulting role residual into a Step 6 witness residual.

#### What's needed in the successor case:

1. A recursive per-slice induction package for the predecessor —
   `MainFormalSuccessorRecursiveSlices` (typed by
   `successorRecursiveSlicesInput` in `RoleRegister.lean`).
2. Self-improvement bridge inputs for the predecessor —
   `MainFormalSuccessorSelfImprovementBridgeInputs` (typed by
   `successorSelfImprovementBridgeInput` in `RoleRegister.lean`).

Both are "just" type aliases for `Prop`-valued functions asking for:
- Per-slice induction conclusions (`ConsRel` with bounded error) for the
  predecessor's restricted strategies
- Per-slice `SelfImprovementBridgeInputs` for the honest slice strategies

#### What exists but isn't called:

The assembly functions in `RoleRegister.lean` are all ready:

- `successorOfBridgeInputs` (line 538) — takes `hrec` + `hbridge` →
  `MainFormalRolePackageBranchResidual.successor`
- `answerSuccessorOfInductionPackageAndBridgeInputs` (line 628) — takes
  `hinduction` + `hbridge` → `MainFormalRolePackageBranchResidual.answerSuccessor`
- Their corresponding `rolePackageResidual_of*` wrappers produce
  `MainFormalRolePackageResidual`

**The gap is in `mainFormal`:** it doesn't take these hypotheses.  The successor
branch says "`hprojectiveCompletionResidual := sorry`" because it has no
successor induction package or self-improvement bridge inputs in scope.

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

### 3.6. mainInductionByRecursionOnM → mainFormal successor bridge: ❌ INCOMPLETE

This is the `sorry` at `MainFormal.lean:611`.  The gap is that `mainFormal`
needs:
- A recursive per-slice induction package for the predecessor
- Self-improvement bridge inputs for the predecessor slices

Neither of these is provided to `mainFormal` as a hypothesis, nor produced
internally.

The wiring functions (`successorOfBridgeInputs`, etc.) exist in `RoleRegister.lean`
but are not called from `mainFormal`.

---

## 4. Quantifying the "Sorry-Free but Not Complete" Pattern

| Layer | Declarations with proofs | Declarations that wire to downstream | Gap |
|-------|------------------------|--------------------------------------|-----|
| SelfImprovement | ~50 theorems/lemmas | 3 public theorems (`selfImprovementHelper`, `selfImprovement`, `selfImprovementFromBridgeInputs`) | All three take explicit hypotheses; internal sub-lemmas are proved but the bridge inputs are not discharged internally |
| SelfImprovement sub-lemmas (slackness, matrix bridge) | ~15 proved lemmas | 0 called from MI or MT | Entirely orphan |
| MainInductionStep | `selfImprovementInInductionSection`, `SelfImprovementPackage.ofSliceBridgeInputs`, `ldPastingInInductionSection`, `mainInductionByRecursionOnM` | All wired together in `MainTheorems.lean` | `mainInductionByRecursionOnM` takes `hselfProducer` as hypothesis; `mainInductionPublicWrapper` passes this through |
| MainTheorem | `mainFormal` | Base case wired via `hbaseBridge` | Successor case: 1 `sorry` at `MainFormal.lean:611` |

---

## 5. Assessment

### Is the concern real?

**Yes.** The user's characterization "一开始lean，然后分别放了假设" is accurate:

1. **Lean compiles** — all individual lemmas in SelfImprovement, Pasting, and
   MainInductionStep compile successfully.  There is only 1 `sorry` in the
   entire LDT directory (`MainFormal.lean:611`).

2. **"然后分别放了假设"** — the three bridge inputs
   (`helperStrongSelfConsistency`, `orthonormalization`, `finalFields`) are
   separately stated as hypotheses.  They are proved in isolation within
   SelfImprovement's submodules (the internal lemmas are all proved), but
   these are `Type`-valued structures that produce the hypotheses as
   conditional implications.  The *assertion* that the bridge inputs are
   unconditionally satisfied for every good strategy is not proved.

3. **The successor gap** is the concrete manifestation: `mainFormal` needs
   `SelfImprovementBridgeInputs` for each predecessor slice, but it doesn't
   have a predecessor induction package to feed them with.

### Is the architecture broken?

**No.** The architecture is sound.  The wiring functions from
`RoleRegister.lean` are complete and would close the gap if called.  The
pattern (take extra hypotheses as parameters, discharge them at the top-level
assembly point) is a legitimate mathematical design, documented in session 49's
blueprint audit.  What's missing is the actual call site in `mainFormal`.

### What would close the gap?

One of:
1. Add `mainFormal` hypotheses for the successor case (recursive induction
   package + self-improvement bridge inputs) and call
   `rolePackageResidual_ofSuccessorBridgeInputs` / the answer-valued variant.
2. Restructure `mainFormal` as an induction that calls itself recursively on
   the predecessor, providing its own `hrec` and `hbridge` inputs.

---

## 6. Recommendations

1. **Track the successor gap explicitly.**  Create an issue reporting that
   `mainFormal.lean:611` is a `sorry` blocking the successor branch.  The
   wiring functions exist; the gap is producing the hypotheses.

2. **Decide fate of orphan lemmas.**  The ~15 slackness-carrying and
   matrix-bridge lemmas in `SdpMatrixHelperBridge.lean` and
   `SelfImprovementTop/ResidualDomination.lean` are fully proved but never
   called.  Options: (a) keep them as future-proofing for the strong-duality
   proof, (b) mark them with `@[deprecated]` or move them to a
   `FutureWork/` directory, (c) delete them.

3. **Do NOT overlap with active PRs.**  PRs #1355, #1353, #1352 are
   actively changing SelfImprovement files.  Any bridge surgery should wait
   until those land.

4. **Update blueprint tags.**  The `\leanok` tag on `thm:self-improvement`
   should note that the theorem takes explicit hypotheses.  The blueprint
   dep graph (session 49 findings) is stale and needs regeneration.

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
| `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean` | `mainFormal` — **1 `sorry` at line 611** |
| `MIPStarRE/LDT/Test/MainTheorem/RoleRegister.lean` | Assembly functions `successorOfBridgeInputs`, etc. (not called from `mainFormal`) |
| `MIPStarRE/LDT/Test/MainTheorem/OrdinaryRestriction/Basic.lean` | `MainFormalSuccessorSelfImprovementBridgeInputs` type definition and constructors |
| `MIPStarRE/LDT/Test/MainTheorem/AnswerValuedRestriction.lean` | Answer-valued counterpart |
