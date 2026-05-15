# Historical MainFormal Remaining `sorry` — Gap Analysis

Date: 2026-05-07

> **Status note, 2026-05-12.**  This report describes the older conditional
> `mainFormal` shape.  It should be read as historical analysis of the missing
> constructions, not as a recommendation to add hypotheses to the paper-facing
> theorem.  The current repair keeps `mainFormal` aligned with
> `thm:main-formal`.  The subsequent MainFormal cleanup removes the live
> repaired-bridge route and keeps the remaining base and successor work as
> internal proof obligations tracked by #1458.  The later projective-layer
> cleanup also removed
> `MainFormalCascadeRolePackageResidualProjectiveCompletionResidual`; the active
> construction target is now
> `MainFormalProjectiveCompletionTransportWitness`.
>
> **Status note, 2026-05-13.**  The post-role diagonal completion theorem now
> reduces to two named match-mass preservation obligations,
> `leftMatchMassPreservation_ofDiagonalConsistency` and
> `rightMatchMassPreservation_ofDiagonalConsistency`, tracked by #1566.  The
> broader completion construction is tracked by #1565.
>
> **Status note, 2026-05-14.**  The two downstream match-mass theorems are now
> projections from the line-130 orthonormalization witness.  The active proof
> gap has been lowered to
> `orthonormalizationMeasurement_of_consistency_from_projectivizationRepair_with_matchMass`,
> which must prove the exact construction-level match-mass monotonicity needed
> for line 169, or be replaced by the checked repaired line-169 route with its
> explicit loss; this is tracked by #1610 under #1566.
>
> **Status note, 2026-05-15.**  The Step 3 factor-two unsymmetrization record
> has been renamed from `UnsymmetrizationBridgePackage` to
> `UnsymmetrizationConsistency`.  This is not a change of mathematical content:
> the record is a proved consistency statement derived from the role-register
> estimate, not an additional bridge hypothesis.

## 1. Exact sorry site

**File:** `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean:611`

**Historical goal type at the sorry:**
```lean
Nonempty (MainFormalCascadeRolePackageResidualProjectiveCompletionResidual
  (params := params) (strategy := strategy) (eps := eps)
  (hpass := hpass) (k := k) (scalars := scalars))
```

This intermediate structure has since been removed.  The corresponding active
internal target is now a direct construction of
`MainFormalProjectiveCompletionTransportWitness` from the role-register witness
and the post-role diagonal completion theorem.

**The removed structure had two fields**:

| Field | Type | Paper Reference |
|-------|------|-----------------|
| `roleInductionWitness` | `MainFormalRoleInductionWitness params strategy eps hpass k` | Section 6 witness |
| `postRoleDiagonalCompletion` | `MainFormalDiagonalCompletionWitness params strategy eps k scalars (roleInductionWitness.roleWitness scalars)` | Post-role line-130 completion |

## 2. Context at the sorry site

### Branch conditions
- `herr : ¬ 1 ≤ mainFormalError params k eps` — error is non-trivial
- `hm1 : params.m ≠ 1` — **successor case** (the base case `params.m = 1` is handled on lines 595-601)
- `hd : 0 < params.d` — degree positive
- `hk0 : 0 < k` — dimension positive
- `hk : 400 * params.m * params.d ≤ k` — large-k hypothesis

### Available hypotheses
- `scalars : MainFormalCascadeScalars params eps k` — constructed from
  `hepsNN`, `hk0`, `herr`.
- The current theorem statement has no bridge-style hypothesis.  The
  role-register witness, line-130 orthonormalization witness, and completion data are
  internal proof obligations.

The line-130 orthonormalization witness is now obtained from cross consistency
through the Section 5 repair construction.  The remaining completion work is
match-mass preservation and the successor role-register construction.

### What's NOT in scope

The comment at the historical `sorry` site states that the answer-valued
recursive-slice adapter is available, but the predecessor per-slice induction
data and answer-side self-improvement obligations are not in scope.

The missing inputs are:
1. **Predecessor per-slice induction data** — providing a Section 6 witness for each restricted slice of the predecessor parameter
2. **Answer-side self-improvement obligations** — providing the Section 9 self-improvement data for the predecessor

These are NOT hypotheses of `mainFormal`. The base case avoids them entirely by using `MainFormalRoleInductionWitness.ofBaseCase` (which calls the already-checked `strategySymmetrization_mainInductionBaseCase`).

## 3. Field analysis

### Field 1: `roleInductionWitness : MainFormalRoleInductionWitness`

This is a Section 6 witness:
```lean
structure MainFormalRoleInductionWitness ... where
  roleMeasurement : Measurement (Polynomial params) (Role × ι)
  section6Consistency :
    ConsRel (strategy.strategySymmetrization).state
      (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas (strategy.strategySymmetrization).pointMeasurement)
      (polynomialEvaluationFamily params roleMeasurement.toSubMeas)
      (MainInductionStep.mainInductionError params k (3 * eps) (3 * eps) (3 * eps))
```

**Existing construction theorem for base case:** `MainFormalRoleInductionWitness.ofBaseCase` (RoleRegister/Core.lean:187-196)
- Calls `strategySymmetrization_mainInductionBaseCase` — already checked ✅

**Existing construction theorem for successor case:** `MainFormalRoleInductionWitness.ofSuccessorBoundary` (RoleRegister/Core.lean:205-216)
- Requires `params.next`, `MainFormalSuccessorBoundary`, etc.
- The successor boundary is NOT available in `mainFormal`'s context.

**Alternative successor construction theorems** (all in RoleRegister.lean):

| Constructor | Required inputs | Status |
|------------|----------------|--------|
| `MainFormalRolePackageBranchResidual.roleWitnessResidual_ofSuccessorObligations` | `successorRecursiveSlicesInput` + `successorSelfImprovementObligations` | Neither in scope |
| `MainFormalRolePackageBranchResidual.roleWitnessResidual_ofAnswerSuccessorObligations` | `answerSuccessorRecursiveSlicesInput` + `answerSuccessorSelfImprovementObligations` | Neither in scope |
| `MainFormalRolePackageBranchResidual.roleWitnessResidual_ofAnswerSuccessorRecursiveSelfImprovement` | `answerSuccessorRecursiveSlicesInput` + `answerSuccessorSelfImprovementInput` | Neither in scope |
| `MainFormalRolePackageBranchResidual.roleWitnessResidual_ofAnswerSuccessorInductionPackageAndObligations` | `answerSuccessorPerSliceInductionDataInput` + `answerSuccessorSelfImprovementObligations` | Neither in scope |

**Status:** no construction theorem is available in scope. This is the primary
gap.

### Field 2: `postRoleDiagonalCompletion : MainFormalDiagonalCompletionWitness`

This structure contains the line-130 orthonormalization witness plus completion data:
```lean
structure MainFormalDiagonalCompletionWitness ... where
  orthWitness : MainFormalDiagonalOrthonormalizationWitness ...
  a_A a_B : Polynomial params
  leftCompletedCloseness : SDDRel ...
  rightCompletedCloseness : SDDRel ...
```
The match-mass preservation proofs now live in
`MainFormalDiagonalOrthonormalizationWitness`, together with the
projective submeasurements they concern.

**Existing construction theorems**:

| Constructor | Required inputs | Status |
|------------|----------------|--------|
| `MainFormalProjectiveCompletionTransportWitness.nonempty_ofRoleWitness` | `roleInductionWitness` only | Source-shaped internal construction target; delegates the completion step to `MainFormalDiagonalCompletionWitness.nonempty_ofDiagonalConsistency` |
| `MainFormalDiagonalCompletionWitness.nonempty_ofDiagonalConsistency` | line-130 orthonormalization witness + cross consistency | Constructs the completion witness from the retained match-mass preservation proofs |
| `leftMatchMassPreservation_ofDiagonalConsistency` / `rightMatchMassPreservation_ofDiagonalConsistency` | line-130 orthonormalization witness + cross consistency | Projection theorems exposing the retained match-mass proofs |
| `orthonormalizationMeasurement_of_consistency_from_projectivizationRepair_with_matchMass` | exact line-169 orthonormalization route | Current `sorry`; must prove construction-level match-mass monotonicity from the paper hypotheses, or be replaced by the checked repaired line-169 route with its explicit loss |

**Current route:** Once Field 1 (`roleInductionWitness`) is produced, the proof must
derive the line-130 orthonormalization witness from cross consistency and then
prove the two match-mass preservation obligations.  These are internal
obligations, not public inputs to `mainFormal`.

The line-130 consistency data supplies the orthonormalization witness via
`MainFormalDiagonalOrthonormalizationWitness.nonempty_ofDiagonalConsistency`.

The completion theorem now fixes the distinguished completion outcome to the
zero polynomial and derives the completion-closeness fields from the checked
analytic completion argument.  The only remaining line-130 completion content
is the exact construction-level match-mass preservation used at line 169.  The
former QXP outcome-expectation formulation was stronger than the present
Section 5 API and should not be treated as the proof target.

**Status:** partially derivable once Field 1 is obtained.  The active local
target is
`orthonormalizationMeasurement_of_consistency_from_projectivizationRepair_with_matchMass`,
unless the final theorem is rerouted through the repaired line-169 estimate.

## 4. Historical resolution routes

### Historical Route A: Mirror the base case

The older proposed route was to replace the successor branch with the same
shape as the base case: first construct a role-register witness, then call a conditional
assembly theorem that also consumed bridge-style completion data.

This was the historical simple route.  It is rejected for the paper-facing
theorem because it relies on additional non-paper inputs.

**What's needed:** Only Field 1 (`MainFormalRoleInductionWitness` for successor case).

### Historical Route B: Keep the native-targets cascade

The older cascade filled the `sorry` by producing:
```lean
Nonempty (MainFormalCascadeRolePackageResidualProjectiveCompletionResidual ...)
```

This required both Field 1 and Field 2.  The current cleanup eliminates this
intermediate record and constructs the active
`MainFormalProjectiveCompletionTransportWitness` directly.

**Comparison:** Route A was simpler and more faithful to the base-case
structure.  Route B required more construction and preserved downstream code
that has since been simplified.  Either route ultimately needs Field 1.

## 5. What must be proved internally

The successor case needs data that must be constructed inside the proof of
`mainFormal`, not added to its parameter list.

### Historical rejected option: Add successor hypotheses

Historical rejected route: add parameters providing the predecessor induction
data:

```lean
(hanswerObligations : answerSuccessorSelfImprovementObligations (k := k) hpass hm_one_ne)
(hinductionPackage : answerSuccessorPerSliceInductionDataInput (k := k) hpass hm_one_ne)
```

Where:
- `answerSuccessorSelfImprovementObligations` — per-slice Section 9 obligations
- `answerSuccessorPerSliceInductionDataInput` — per-slice induction data

This is useful only as a description of the missing internal obligations.  It
should not be the public statement of `mainFormal`.

### Alternative: Use ordinary (non-answer) successor route

The ordinary route needs:
- `successorRecursiveSlicesInput`
- `successorSelfImprovementObligations`

With construction theorems:
```lean
MainFormalRolePackageBranchResidual.roleWitnessResidual_ofSuccessorObligations
  hpass hm1 hd hk0 hk hrec obligations
```

### Which route is paper-faithful?

The paper uses the answer-restricted induction (Section 6 of the LDT paper goes through the answer alphabet restriction). The answer-valued route is the paper-faithful one. However, both routes are mathematically equivalent — the ordinary restriction and answer-valued restriction are both formalized.

## 6. Relationship to active PRs

| PR | Description | Overlap with this gap? |
|----|-------------|----------------------|
| #1355 | Absorb small-alphabet data-processing gap in SelfImprovement | ❌ Orthogonal (self-improvement pipeline — needed to eventually prove the obligations but doesn't provide them directly) |
| #1353 | Residual-domination lemmas for SelfImprovement orthonormalization | ❌ Orthogonal (helps discharge orthonormalization obligations but doesn't provide the obligations themselves) |
| #1352 | Slackness bridge for strong duality | Orthogonal (SDP infrastructure for self-improvement) |

None of the active PRs directly fills the gap. They are building the
self-improvement infrastructure that would eventually be consumed by
`answerSuccessorSelfImprovementObligations` /
`successorSelfImprovementObligations`, but the source-level obligation
dischargers are not yet constructed.

## 7. Summary of actionable sub-gaps

### Gap 1 (CRITICAL): Successor role-register construction

**What:** Need to produce `MainFormalRoleInductionWitness` for the `params.m ≠ 1` branch.

**Why blocked:** `mainFormal` lacks the successor induction hypotheses needed to invoke any of the existing successor role-register constructors.

**Resolution:** prove the recursive induction data and the corresponding
self-improvement obligations inside the `mainFormal` proof, for example by
embedding the final theorem in a recursion that supplies them from the
predecessor induction hypothesis.  Adding
`answerSuccessorPerSliceInductionDataInput`,
`answerSuccessorSelfImprovementObligations`, `successorRecursiveSlicesInput`, or
`successorSelfImprovementObligations` to the public `mainFormal` statement is
the rejected historical route, not an acceptable repair.

**Tracked by:** #931 (successor obligations), #834 (remaining witness construction), #422 (main-formal completion epic)

### Gap 2 (follows from Gap 1): Post-role diagonal completion

**What:** Need to derive `MainFormalDiagonalCompletionWitness`
from the role-register witness and the paper's line-130 consistency data.

**Why blocked:** Depends on Gap 1. Once the role-register witness is available, the
current route derives the orthonormalization witness from cross consistency.
The remaining pieces are the two match-mass preservation obligations.  The
completion outcome and completion-closeness estimates are now produced by
`MainFormalDiagonalCompletionWitness.nonempty_ofDiagonalConsistency`
from those obligations.

**Resolution options:**
- Build the completion witness directly from the role-register witness, the
  line-130 orthonormalization witness, and match-mass preservation.
- Keep the missing match-mass argument as an internal obligation until it is
  proved from the paper hypotheses.

### Gap 3 (INFRA): Base-case completion construction

**Historical what:** the older conditional theorem shape took a bridge-style
hypothesis as an unproved input.  In the current repair, no such input belongs
to `mainFormal`; #1043 tracks the remaining base-case completion obligation.

**Status:** the base completion construction is orthogonal to the successor
case.  It must be produced from the paper hypotheses regardless of which
successor route is chosen.

**Tracked by:** #1043

## 8. Which approach discharges the remaining obligations?

**Historical minimum closure:** Add the missing hypotheses to `mainFormal`
(Gap 1) and use Route A.  This would replace the proof holes with a call to the
existing constructors, but it would also strengthen the source-facing theorem by
adding non-paper assumptions.  The current repair policy rejects this route.

**Complete closure:** Prove the base completion obligation (#1043), then prove
the successor obligations (#931), then prove the per-slice induction data
(which itself would need a recursive application of `mainFormal`). This closes
`mainFormal` completely without extra hypotheses but requires a well-founded
recursion setup.

The old "extra-hypothesis" route is rejected for the paper-facing theorem.
Missing work should appear as internal proof obligations, not as new assumptions
of `mainFormal`.

## 9. Existing tracking issues

Several issues already cover the sub-gaps identified above:

| Issue | Description | Covers Gap |
|-------|-------------|------------|
| #1363 | Historical tracker for closing the MainFormal successor-case projective completion gap | Primary tracker |
| #1565 | Discharge the line-130 diagonal completion construction for `mainFormal` | Current post-role completion tracker |
| #1566 | Prove line-169 match-mass preservation for the chosen `mainFormal` witnesses | Current lowest match-mass obligations |
| #1035 | Prove recursive mainFormal for successor restricted slices | `MainFormalSuccessorRecursiveSlices` |
| #1036 | Construct successor-case self-improvement obligations | `MainFormalSuccessorSelfImprovementObligations` |
| #1041 | Assemble successor-case mainFormal branch | Final wiring of #1035 + #1036 |
| #1043 | Construct base-case completion data | Base-case completion |
| #1103 | SelfImprovement: assemble closed obligations | Self-improvement closure |
| #1104 | LDT/Test: assemble successor Step-6 witness from proved obligations | Step-6 assembly |
| #931 | Close self-improvement inputs for Section 6 | Self-improvement → main induction bridge |
| #1367 | SelfImprovement bridge: audit and close input-consistency orphans blocking mainFormal | Self-improvement audit |
| #1359 | Trace OrthonormalizationInput extra-hypothesis chain | Orthonormalization hypothesis chain |

One **missing piece**: the **answer-valued** successor route (`MainFormalSuccessorAnswerRecursiveSlices` + `MainFormalSuccessorAnswerSelfImprovementObligations`, or `AnswerPerSliceInductionData` + answer obligations) is not yet tracked by a dedicated issue. This is the paper-faithful route (using answer alphabet restriction). Tracked in #1369.
