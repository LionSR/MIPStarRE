# MainFormal Remaining `sorry` — Gap Analysis

Date: 2026-05-07

## 1. Exact sorry site

**File:** `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean:611`

**Goal type at the sorry:**
```lean
Nonempty (MainFormalCascadeRolePackageResidualProjectiveCompletionResidual
  (params := params) (strategy := strategy) (eps := eps)
  (hpass := hpass) (k := k) (scalars := scalars))
```

**The structure `MainFormalCascadeRolePackageResidualProjectiveCompletionResidual` has two fields** (defined in `NativeTargets.lean:23-34`):

| Field | Type | Paper Reference |
|-------|------|-----------------|
| `roleResidual` | `MainFormalRolePackageResidual params strategy eps hpass k` | Section 6 witness |
| `postRoleDiagonalCompletion` | `MainFormalPostRolePackageDiagonalCompletionResidual params strategy eps k scalars (roleResidual.rolePackage scalars)` | Post-role line-130 completion |

## 2. Context at the sorry site

### Branch conditions
- `herr : ¬ 1 ≤ mainFormalError params k eps` — error is non-trivial
- `hm1 : params.m ≠ 1` — **successor case** (the base case `params.m = 1` is handled on lines 595-601)
- `hd : 0 < params.d` — degree positive
- `hk0 : 0 < k` — dimension positive
- `hk : 400 * params.m * params.d ≤ k` — large-k hypothesis

### Available hypotheses
- `scalars : MainFormalCascadeScalars params eps k` — constructed from `hepsNN`, `hk0`, `herr`
- `hbaseBridge : (scalars : MainFormalCascadeScalars params eps k) → ∀ (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k), MainFormalRepairedBridgeHypotheses params strategy eps k hpass scalars roleResidual`

The `hbaseBridge` provides, for any concrete role residual:
- `MainFormalPostRolePackageDiagonalOrthonormalizationInput` — line-130 spectral truncation + repair witnesses
- `MainFormalPostRolePackageDiagonalConsistencyInput` — diagonal consistency for the two unsymmetrized POVMs

These two are exactly the inputs needed to construct Field 2 (the `postRoleDiagonalCompletion`).

### What's NOT in scope

The comment on line 606-610 states explicitly:

> "the answer-valued recursive-slice adapter is available, but this theorem still has no predecessor per-slice induction package or answer-side self-improvement bridge inputs in scope."

The missing inputs are:
1. **Predecessor per-slice induction package** — providing a Section 6 witness for each restricted slice of the predecessor parameter
2. **Answer-side self-improvement bridge inputs** — providing the Section 9 self-improvement data for the predecessor

These are NOT hypotheses of `mainFormal`. The base case avoids them entirely by using `MainFormalRolePackageResidual.ofBaseCase` (which calls the already-checked `strategySymmetrization_mainInductionBaseCase`).

## 3. Field analysis

### Field 1: `roleResidual : MainFormalRolePackageResidual`

This is a Section 6 witness:
```lean
structure MainFormalRolePackageResidual ... where
  roleMeasurement : Measurement (Polynomial params) (Role × ι)
  section6Consistency :
    ConsRel (strategy.strategySymmetrization).state
      (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas (strategy.strategySymmetrization).pointMeasurement)
      (polynomialEvaluationFamily params roleMeasurement.toSubMeas)
      (MainInductionStep.mainInductionError params k (3 * eps) (3 * eps) (3 * eps))
```

**Existing producer for base case:** `MainFormalRolePackageResidual.ofBaseCase` (RoleRegister/Core.lean:187-196)
- Calls `strategySymmetrization_mainInductionBaseCase` — already checked ✅

**Existing producer for successor case:** `MainFormalRolePackageResidual.ofSuccessorBoundary` (RoleRegister/Core.lean:205-216)
- Requires `params.next`, `MainFormalSuccessorBoundary`, etc.
- The successor boundary is NOT available in `mainFormal`'s context.

**Alternative successor producers** (all in RoleRegister.lean):

| Constructor | Required inputs | Status |
|------------|----------------|--------|
| `MainFormalRolePackageBranchResidual.rolePackageResidual_ofSuccessorBridgeInputs` | `successorRecursiveSlicesInput` + `successorSelfImprovementBridgeInput` | Neither in scope |
| `MainFormalRolePackageBranchResidual.rolePackageResidual_ofAnswerSuccessorBridgeInputs` | `answerSuccessorRecursiveSlicesInput` + `answerSuccessorSelfImprovementBridgeInput` | Neither in scope |
| `MainFormalRolePackageBranchResidual.rolePackageResidual_ofAnswerSuccessorRecursiveSelfImprovement` | `answerSuccessorRecursiveSlicesInput` + `answerSuccessorSelfImprovementInput` | Neither in scope |
| `MainFormalRolePackageBranchResidual.rolePackageResidual_ofAnswerSuccessorInductionPackageAndBridgeInputs` | `answerSuccessorPerSliceInductionPackageInput` + `answerSuccessorSelfImprovementBridgeInput` | Neither in scope |

**Status:** ❌ NO producer available in scope. This is the primary gap.

### Field 2: `postRoleDiagonalCompletion : MainFormalPostRolePackageDiagonalCompletionResidual`

This structure contains the line-130 orthonormalization residual plus completion data:
```lean
structure MainFormalPostRolePackageDiagonalCompletionResidual ... where
  orthResidual : MainFormalPostRolePackageDiagonalOrthonormalizationResidual ...
  a_A a_B : Polynomial params
  leftCompletedCloseness : SDDRel ...
  rightCompletedCloseness : SDDRel ...
  leftMatchMass : qBipartiteMatchMass ...
  rightMatchMass : qBipartiteMatchMass ...
```

**Existing producers** (all in NativeTargets.lean):

| Constructor | Required inputs | Status |
|------------|----------------|--------|
| `nonempty_ofRoleResidualAndCompletion` | `roleResidual` + `Nonempty MainFormalPostRolePackageDiagonalCompletionResidual` | Circular (needs itself) |
| `nonempty_ofRoleResidualAndDiagonalInputs` | `roleResidual` + `OrthonormalizationInput` + `completionProducer : OrthResidual → CompletionResidual` | CompletionProducer missing |
| `nonempty_ofRoleResidualAndDiagonalInputsAndMatchMassPreservation` | `roleResidual` + `OrthonormalizationInput` + `a_A a_B` + match-mass for both sides | Match-mass unproven |
| `nonempty_ofRoleResidualAndDiagonalInputsAndCompletingToMeasurementInputs` | `roleResidual` + `OrthonormalizationInput` + `a_A a_B` + `BipartiteSSCRel` (left + right) + match-mass | All four missing |

**Given `hbaseBridge`:** Once Field 1 (`roleResidual`) is produced, `hbaseBridge scalars roleResidual` provides:
- `orthonormalizationInput` ✅
- `diagonalConsistency` ✅

The `diagonalConsistency` already packages:
- A diagonal consistency input (`MainFormalPostRolePackageDiagonalConsistencyInput`)
- Which can be used to produce the `orthResidual` via `MainFormalPostRolePackageDiagonalOrthonormalizationResidual.nonempty_ofDiagonalInputs`

The remaining pieces for a `MainFormalPostRolePackageDiagonalCompletionResidual` are:
- `a_A a_B` — distinguished outcomes (can use zero polynomial)
- `leftCompletedCloseness`, `rightCompletedCloseness` — completion closeness (can derive from `completingToMeasurement`)
- `leftMatchMass`, `rightMatchMass` — match-mass preservation (needs `OrthonormalizationMatchMassPreservation`)

There are also the `BipartiteSSCRel` strong self-consistency packages. The `diagonalConsistency` provides `ConsRel` (cross correlation), not `BipartiteSSCRel` (self-consistency). But some theorems derive `BipartiteSSCRel` from `ConsRel` under `PermInvState` (see `lines 297-308` of MainFormal.lean).

**Status:** ⚠️ Partially producible once Field 1 is obtained, but may require additional auxiliary lemmas (match-mass, self-consistency derivation). However, note that the alternative `baseMainFormal_ofRepairedBaseBridge` theorem builds the final result directly from the bridge without constructing a separate `CompletionResidual` — see Section 4.

## 4. Two possible resolution routes

### Route A: Simple (mirror the base case)

Replace the entire successor branch (lines 602-656) with the same pattern as the base case:
```lean
-- Produce role residual for successor case
rcases produceRoleResidualForSuccessor ... with ⟨roleResidual⟩
-- Use same mainFormal_ofRoleResidualAndRepairedBridge as base case
exact mainFormal_ofRoleResidualAndRepairedBridge herr roleResidual
  (hbaseBridge scalars roleResidual)
```

This avoids the complicated `MainFormalCascadeRolePackageResidualProjectiveCompletionResidual` → `toLeftCompletionTransportResidual` → ... → `MainFormalNativeTargets.toMainFormal` cascade (lines 612-656), replacing it with the already-proven `mainFormal_ofRoleResidualAndRepairedBridge`.

**What's needed:** Only Field 1 (`MainFormalRolePackageResidual` for successor case).

### Route B: Keep the native-targets cascade

Keep lines 612-656 and fill the `sorry` at line 611 to produce:
```lean
Nonempty (MainFormalCascadeRolePackageResidualProjectiveCompletionResidual ...)
```

This requires BOTH Field 1 and Field 2.

**Comparison:** Route A is simpler and more faithful to the base case structure. Route B requires more construction but preserves existing downstream code. Either route ultimately needs Field 1.

## 5. What needs to be added to `mainFormal`'s hypotheses

The successor case needs inputs that are currently absent from `mainFormal`'s parameter list:

### Option: Add successor-bridge hypotheses

Add parameters providing the predecessor induction data:

```lean
(hanswerBridgeInputs : answerSuccessorSelfImprovementBridgeInput (k := k) hpass hm_one_ne)
(hinductionPackage : answerSuccessorPerSliceInductionPackageInput (k := k) hpass hm_one_ne)
```

Where:
- `answerSuccessorSelfImprovementBridgeInput` — per-slice Section 9 bridge data (Type-valued, wraps each slice's self-improvement inputs)
- `answerSuccessorPerSliceInductionPackageInput` — per-slice induction package (Type-valued, wraps predecessor `mainFormal` result per restricted slice)

Then use:
```lean
rcases MainFormalRolePackageBranchResidual
  .rolePackageResidual_ofAnswerSuccessorInductionPackageAndBridgeInputs
    hpass hm1 hd hk0 hk hinductionPackage hanswerBridgeInputs
  with ⟨roleResidual⟩
exact mainFormal_ofRoleResidualAndRepairedBridge herr roleResidual
  (hbaseBridge scalars roleResidual)
```

### Alternative: Use ordinary (non-answer) successor route

The ordinary route needs:
- `successorRecursiveSlicesInput`
- `successorSelfImprovementBridgeInput`

With producers:
```lean
MainFormalRolePackageBranchResidual.rolePackageResidual_ofSuccessorBridgeInputs
  hpass hm1 hd hk0 hk hrec hbridge
```

### Which route is paper-faithful?

The paper uses the answer-restricted induction (Section 6 of the LDT paper goes through the answer alphabet restriction). The answer-valued route is the paper-faithful one. However, both routes are mathematically equivalent — the ordinary restriction and answer-valued restriction are both formalized.

## 6. Relationship to active PRs

| PR | Description | Overlap with this gap? |
|----|-------------|----------------------|
| #1355 | Absorb small-alphabet data-processing gap in SelfImprovement | ❌ Orthogonal (self-improvement pipeline — needed to eventually prove the bridge inputs but doesn't provide them directly) |
| #1353 | Residual-domination wrappers for SelfImprovement orthonormalization | ❌ Orthogonal (helps discharge orthonormalization bridge inputs but doesn't provide the bridge inputs themselves) |
| #1352 | Slackness bridge for strong-duality producer | ❌ Orthogonal (SDP infrastructure for self-improvement) |

None of the active PRs directly fills the gap. They are building the self-improvement infrastructure that would eventually be consumed by `answerSuccessorSelfImprovementBridgeInput` / `successorSelfImprovementBridgeInput` producers, but these producers are not yet constructed.

## 7. Summary of actionable sub-gaps

### Gap 1 (CRITICAL): Successor role residual construction

**What:** Need to produce `MainFormalRolePackageResidual` for the `params.m ≠ 1` branch.

**Why blocked:** `mainFormal` lacks the successor induction hypotheses needed to invoke any of the existing successor role-residual constructors.

**Resolution options:**
- **(a)** Add `answerSuccessorPerSliceInductionPackageInput` and `answerSuccessorSelfImprovementBridgeInput` as additional hypotheses to `mainFormal`
- **(b)** Embed `mainFormal` in a recursive induction that provides these from an outer induction hypothesis
- **(c)** Add `successorRecursiveSlicesInput` and `successorSelfImprovementBridgeInput` as hypotheses and use the ordinary successor route

**Tracked by:** #931 (successor-bridge inputs), #834 (remaining witness residual), #422 (main-formal completion epic)

### Gap 2 (MINOR, follows from Gap 1): Post-role diagonal completion

**What:** Need to derive `MainFormalPostRolePackageDiagonalCompletionResidual` from the bridge hypothesis `hbaseBridge` and the role residual.

**Why blocked:** Depends on Gap 1. Once the role residual is available, `hbaseBridge` provides the orthonormalization input. Remaining pieces (match-mass, self-consistency) may need new lemmas.

**Resolution options:**
- Use Route A (simple): skip `CompletionResidual` entirely and call `mainFormal_ofRoleResidualAndRepairedBridge` (no separate completion residual needed)
- Use Route B (native targets): build the completion residual from the bridge using existing theorems in `NativeTargets.lean`, possibly requiring new lemmas for match-mass and bipartite SSC derivation

### Gap 3 (INFRA): Base-case bridge construction

**What:** `mainFormal` takes `hbaseBridge` as an unproven hypothesis. #1043 tracks constructing this hypothesis.

**Status:** `hbaseBridge` is used by both base and successor cases. It's an orthogonal gap to the successor case — it needs to be discharged regardless of which successor route is chosen.

**Tracked by:** #1043

## 8. Which approach makes the single `sorry` disappear?

**Minimum closure:** Add the missing hypotheses to `mainFormal` (Gap 1) and use Route A (simple). This replaces the `sorry` with a call to the existing constructors, making `mainFormal` "sorry-free" — but now with additional hypotheses that track the remaining unformalized analytic content (the successor bridge inputs and per-slice induction package).

**Complete closure:** Discharge `hbaseBridge` (#1043), then prove the successor bridge inputs (#931), then prove the per-slice induction package (which itself would need a recursive application of `mainFormal`). This closes `mainFormal` completely without extra hypotheses but requires a well-founded recursion setup.

The "extra-hypothesis" pattern (documented in the memory) is the expected approach: prove the main theorem with explicit hypotheses, then separately prove that those hypotheses are satisfiable.

## 9. Existing tracking issues

Several issues already cover the sub-gaps identified above:

| Issue | Description | Covers Gap |
|-------|-------------|------------|
| #1363 | Close the sole remaining `sorry` in MainFormal (successor-case projective completion) | Primary tracker |
| #1035 | Prove recursive mainFormal for successor restricted slices | `MainFormalSuccessorRecursiveSlices` |
| #1036 | Construct successor-case self-improvement bridge inputs | `MainFormalSuccessorSelfImprovementBridgeInputs` |
| #1041 | Assemble successor-case mainFormal branch | Final wiring of #1035 + #1036 |
| #1043 | Construct `hbaseBridge` for base case | Base-case bridge |
| #1103 | SelfImprovement: assemble closed bridge inputs from producers | Self-improvement closure |
| #1104 | LDT/Test: assemble successor Step-6 witness from proved producers | Step-6 assembly |
| #931 | Close self-improvement inputs for Section 6 | Self-improvement → main induction bridge |
| #1367 | SelfImprovement bridge: audit and close input-consistency orphans blocking mainFormal | Self-improvement audit |
| #1359 | Trace OrthonormalizationInput extra-hypothesis chain | Orthonormalization hypothesis chain |

One **missing piece**: the **answer-valued** successor route (`MainFormalSuccessorAnswerRecursiveSlices` + `MainFormalSuccessorAnswerSelfImprovementBridgeInputs`, or `AnswerPerSliceInductionPackage` + answer bridge inputs) is not yet tracked by a dedicated issue. This is the paper-faithful route (using answer alphabet restriction). Tracked in #1369.
