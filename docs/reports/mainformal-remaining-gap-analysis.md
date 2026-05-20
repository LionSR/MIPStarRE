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
> **Status note, 2026-05-15.**  The exact line-169 match-mass branch has been
> removed from the active `mainFormal` path.  The post-role diagonal completion
> theorem now derives its witness directly from line-130 cross consistency and
> orthonormalization closeness, while the completion transport uses the checked
> repaired line-169 estimate with its explicit loss.
>
> **Status note, 2026-05-15.**  The Step 3 factor-two unsymmetrization record
> has been renamed from `UnsymmetrizationBridgePackage` to
> `UnsymmetrizationConsistency`.  This is not a change of mathematical content:
> the record is a proved consistency statement derived from the role-register
> estimate, not an additional bridge hypothesis.
>
> **Status note, 2026-05-20.**  The analysis below is now a historical record
> of the final-theorem repair.  The current source statement
> `thm:main-formal` is no longer linked to a conditional Lean theorem; the
> same-space Lean interface is recorded separately as
> `thm:main-formal-current-interface`.  The same-space theorem
> `MIPStarRE.LDT.Test.mainFormal` has no bridge, residual, package, or
> obligation hypotheses.  Its only remaining `sorryAx` dependency is
> transitive through `MIPStarRE.LDT.MainInductionStep.mainInduction`, and the
> only construction proof hole on that same-space route is
> `MIPStarRE.LDT.MainInductionStep.mainInductionSuccessorNext_ofSmallErrorConstruction`.
> The source-labelled blueprint entry `thm:main-formal` is now recorded as
> `MIPStarRE.LDT.Test.mainFormal_sourceStatement`, which calls the named
> wrapper `MIPStarRE.LDT.Test.mainFormal_sourceObligation` for the printed
> two-space, `k >= md` statement.  This wrapper proves the saturated-error
> branch and leaves
> `MIPStarRE.LDT.Test.mainFormal_sourceSmallErrorObligation` as the direct
> final-theorem source-boundary proof hole.
> The former `MainFormalRolePackageBranchResidual`,
> `successorSelfImprovementObligations`,
> `answerSuccessorSelfImprovementObligations`, and recursive-slice input
> records should therefore be read as removed intermediate interfaces, not as
> current proof targets.

## 1. Exact sorry site

**Current direct file:** `MIPStarRE/LDT/MainInductionStep/Theorems/MainTheorems.lean:680`

**Current direct theorem:**
`MIPStarRE.LDT.MainInductionStep.mainInductionSuccessorNext_ofSmallErrorConstruction`

The active goal is the small-error branch of the native successor step in
`thm:main-induction`:

```lean
∃ G : Measurement (Polynomial params.next) ι,
  ConsRel strategy.state (uniformDistribution (Point params.next))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
    (polynomialEvaluationFamily params.next G.toSubMeas)
    (mainInductionError params.next k eps delta gamma)
```

This theorem assumes precisely the successor branch hypotheses, including
`strategy.IsGood eps delta gamma`,
`400 * params.next.m * params.next.d ≤ k`, and
`mainInductionError params.next k eps delta gamma < 1`.  It does not assume
restricted-probability records, slice-induction data, self-improvement data,
pasting data, residual packages, or arbitrary implication hypotheses.

The older conditional direct `sorry` in `MainFormal.lean` has been removed.  A
direct `sorry` remains in `mainFormal_sourceSmallErrorObligation`, but it is a
named non-vacuous source-boundary obligation rather than the removed conditional
bridge package.  The wrapper `mainFormal_sourceObligation` proves the
saturated-error branch by a two-space trivial measurement construction.
The historical goal displayed below records the earlier state of this report.

## 1.1. Statement integrity audit

Paper assumptions for `thm:main-formal`: a general projective strategy
`(\psi, A^A, B^A, L^A, A^B, B^B, L^B)` for the `(m,q,d)` low individual degree
test, passing probability at least `1 - eps`, and an integer `k >= md`.

Lean assumptions in `MIPStarRE.LDT.Test.mainFormal`: a same-space projective
strategy `strategy : SameSpaceProjStrat params ι`, the pass hypothesis
`strategy.PassesLowIndividualDegreeTest eps`, an integer `k`, the corrected
large-`k` bound `400 * params.m * params.d <= k`, and the scalar boundary
`0 < k`.

Paper conclusion: projective polynomial measurements `G^A` and `G^B` whose
evaluations are consistent with the two point measurements, and which are
mutually self-consistent, with error `nu`.

Lean conclusion: projective measurements
`G_A G_B : ProjMeas (Polynomial params) ι` satisfying the two point-consistency
relations and the final self-consistency relation at `mainFormalError params k
eps`.

Verdict: the source theorem `thm:main-formal` is exact in the blueprint and is
now linked to the source-faithful Lean statement
`MIPStarRE.LDT.Test.mainFormal_sourceStatement`, which calls the named
source-boundary wrapper `MIPStarRE.LDT.Test.mainFormal_sourceObligation`.
This wrapper proves the saturated-error branch and calls
`MIPStarRE.LDT.Test.mainFormal_sourceSmallErrorObligation` in the remaining
small-error branch.
The Lean theorem `mainFormal` is a separate current interface with
faithful boundary hypotheses for the present formal container and the
documented large-`k` correction.  It has no bridge, residual, package, repair,
producer, input, or obligation hypothesis.  Its only remaining proof debt is
transitive through the Section 6 theorem `MainInductionStep.mainInduction`.

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

## 2. Historical context at the removed `MainFormal.lean` sorry site

### Branch conditions
- `herr : ¬ 1 ≤ mainFormalError params k eps` — error is non-trivial
- `hm1 : params.m ≠ 1` — **successor case** (the base case `params.m = 1` is handled on lines 595-601)
- `hd : 0 < params.d` — degree positive
- `hk0 : 0 < k` — dimension positive
- `hk : 400 * params.m * params.d ≤ k` — large-k hypothesis

### Available hypotheses
- `scalars : MainFormalCascadeScalars params eps k` — constructed from
  `hepsNN`, `hk0`, `herr`.
- The theorem statement had no bridge-style hypothesis.  The role-register
  witness, line-130 orthonormalization witness, and completion data were
  internal proof obligations.

The line-130 orthonormalization witness is now obtained from cross consistency
through the Section 5 repair construction.  In the current code, this is no
longer an open `MainFormal.lean` completion problem; the remaining dependency
is the Section 6 successor construction described above.

### What's NOT in scope

The current successor theorem makes the missing constructions explicit in
mathematical form, rather than as extra fields on `mainFormal`.  The remaining
proof must construct the answer-valued restricted slice profile, apply the
recursive predecessor induction conclusion to each slice, realize the
induction-section self-improvement interface, assemble the pasting input, and
prove the scalar absorption estimates.

The checked assembly theorems have reduced this to three concrete components:

1. the degree-zero family-and-scalar construction;
2. the predecessor induction argument for the answer-valued restricted slices;
3. the positive-degree answer-valued slice realization.

These are not hypotheses of `mainFormal`, nor of the paper-facing successor
step.  They are the remaining internal proof obligations in Section 6.

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

The historical successor constructors in `RoleRegister.lean` have been removed
from the active final-theorem route.  Their names recorded the missing
predecessor-slice and self-improvement data as records.  The current repair
does not present those records as acceptable public inputs.  Instead,
`mainInductionSuccessorNext_ofSmallErrorConstruction` is the single named
construction obligation: it must derive the required successor witness from the
paper hypotheses by the induction argument of Section 6.

**Status:** the role-register construction is no longer a separate
`mainFormal` gap.  It is part of the remaining native successor proof for
`thm:main-induction`.

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
| `MainFormalDiagonalCompletionWitness.nonempty_ofDiagonalConsistency` | line-130 orthonormalization witness + cross consistency | Constructs the completion witness directly from the checked completion-closeness argument |
| `mainFormalProjectiveCompletionTransportWitnessOfCompleteAtOutcomeStatements` | role witness + line-130 cross consistency + orthonormalize-and-complete statements | Uses the checked repaired line-169 transport with its explicit loss |

**Current route:** Once Field 1 (`roleInductionWitness`) is produced, the proof
derives the line-130 orthonormalization witness from cross consistency, builds
the completion witness directly from the checked completion argument, and then
uses the repaired line-169 transport in the final projective completion step.

The line-130 consistency data supplies the orthonormalization witness via
`MainFormalDiagonalOrthonormalizationWitness.nonempty_ofDiagonalConsistency`.

The completion theorem now fixes the distinguished completion outcome to the
zero polynomial and derives the completion-closeness fields from the checked
analytic completion argument.  The former exact match-mass branch and its QXP
outcome-expectation formulation have both been removed from the active route.

**Status:** partially derivable once Field 1 is obtained.  The active route is
the repaired line-169 estimate, and the remaining work sits in the successor /
induction side rather than in a separate exact line-169 sub-obligation.

## 4. Historical resolution routes

### Historical Route A: Mirror the base case

The older proposed route was to replace the successor branch with the same
shape as the base case: first construct a role-register witness, then call an
assembly theorem that also consumed bridge-style completion data as explicit
inputs.

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

## 5. What must be proved internally now

The remaining work is no longer a `mainFormal` parameter problem.  It is the
small-error successor construction for `thm:main-induction`.

The paper uses answer-restricted slices in the induction step.  In Lean this
means the proof of
`mainInductionSuccessorNext_ofSmallErrorConstruction` should construct, from
the successor strategy and the good-strategy hypotheses, the restricted slice
data needed by the checked answer-stage assembly.  The recursive predecessor
induction should enter as the local induction hypothesis in the proof of
`mainInduction`, not as an assumption of the final theorem.

The current internal proof obligations are:

| Component | Mathematical role | Present status |
|-----------|-------------------|----------------|
| Degree-zero branch | Produce the family and scalar estimates when `params.d = 0` | Isolated by the checked degree-split assembly |
| Predecessor induction | Apply `thm:main-induction` to each answer-valued restricted predecessor slice | Still the genuine recursive part |
| Positive-degree slice realization | Build the answer-valued slice transport and self-improvement data when `0 < params.d` | Reduced to the checked stage interfaces |
| Scalar absorption | Verify that the accumulated losses are bounded by `mainInductionError params.next k eps delta gamma` | Partly assembled; remaining estimates belong to #1507 |

The rejected historical route was to add records encoding these objects to
`mainFormal`, or to a paper-facing successor theorem.  That route would
strengthen the source statement.  The present route keeps the objects internal
to the Section 6 proof.

## 6. Relationship to earlier trackers

Several older issues named the missing data as final-theorem obligations.  They
are useful for provenance, but they no longer describe the active public
interface.

| Issue | Current reading |
|-------|-----------------|
| #1507 | Live tracker for the native small-error successor construction |
| #1458 | Source-statement boundary tracker for the final theorem route |
| #1363 | Historical final-theorem successor-completion tracker |
| #1565 | Historical line-130 diagonal completion tracker; the active route now derives this through checked completion lemmas |
| #1566 | Historical line-169 exact match-mass tracker; superseded by the repaired line-169 transport estimate |
| #1558 | Cleanup tracker for removing residual and package layers from the final theorem route |
| #1035, #1036, #1041 | Historical names for recursive-slice and self-improvement obligations before the route was moved into Section 6 |
| #1043 | Historical base-completion tracker; the current base branch is checked |
| #1103, #1367 | Historical Section 9 closure and audit trackers; the self-improvement interface is now checked |
| #1359 | Historical orthonormalization-input audit; the Section 5 route is now checked |

Thus the active mathematical frontier is a single theorem:

```lean
MIPStarRE.LDT.MainInductionStep.mainInductionSuccessorNext_ofSmallErrorConstruction
```

Closing that theorem removes the remaining direct `sorry` and eliminates the
transitive `sorryAx` dependency of `mainInduction` and `mainFormal`.
