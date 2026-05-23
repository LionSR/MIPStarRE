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
> obligation hypotheses.  At this date its remaining `sorryAx` dependency was
> transitive through `MIPStarRE.LDT.MainInductionStep.mainInduction`; the
> later 2026-05-22 update below records that the corrected large-\(k\)
> successor construction has since been proved.
> The source-labelled blueprint entry `thm:main-formal` is now recorded as
> `MIPStarRE.LDT.Test.mainFormal_sourceStatement`, which calls the named
> wrapper `MIPStarRE.LDT.Test.mainFormal_sourceConclusion` for the printed
> two-space, `k >= md` statement.  This wrapper proves the saturated-error
> branch and leaves
> `MIPStarRE.LDT.Test.mainFormal_sourceSmallErrorConclusion` as the direct
> final-theorem source-boundary proof hole.
> The former `MainFormalRolePackageBranchResidual`,
> `successorSelfImprovementObligations`,
> `answerSuccessorSelfImprovementObligations`, and recursive-slice input
> records should therefore be read as removed intermediate interfaces, not as
> current proof targets.
>
> **Status note, 2026-05-21.**  The remaining source-final proof hole is not a
> generic container for old bridge hypotheses.  It is the non-vacuous branch of
> the printed two-space theorem.  Its mathematical content is the conjunction of
> three documented tasks: the two-space role-register reduction from
> `ProjStrat`, the source \(k\)-range and scalar-boundary issue from
> `docs/paper-gaps/issue-906-main-formal-k-bound.tex`, and, at that snapshot,
> the native Section 6 small-error successor construction.  The rebuilt
> blueprint then displayed these as
> `prop:main-formal-source-two-space-role-register`,
> `prop:main-formal-source-k-range-boundary`, and
> `prop:main-formal-source-successor-construction`.  The successor item is now
> historical: the corrected large-\(k\) Section 6 successor branch has since
> been proved, and the live final-theorem frontier has the two pieces listed in
> the next status note.  The saturated branch is already proved by
> `mainFormal_source_trivial_witness`, and the small-error branch is not
> vacuous: the \(md\le k<400md\) interval can still have
> `mainFormalError params k eps < 1`.
>
> **Status note, 2026-05-22.**  The native Section 6 successor construction is
> now proved for the corrected large-\(k\) interface.  The current final-theorem
> source frontier has two displayed pieces, not three:
> `prop:main-formal-source-two-space-role-register` and
> `prop:main-formal-source-k-range-boundary`.  The direct Lean proof holes are
> `MainInductionStep.mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation`
> and `Test.mainFormal_sourceSmallErrorConclusion`.
>
> **Status note, 2026-05-23.**  That final-theorem frontier is now historical.
> The factor \(400\) in the large-\(k\) hypothesis is treated as a confirmed
> correction to the printed statement, and the final theorem explicitly assumes
> the nonzero-sampling boundary \(0<k\).  Under these corrected source
> hypotheses, the two-space source-boundary route is checked; the older
> `mainInduction_sourceRange*` and `mainFormal_source*Obligation` names below
> refer to retired wrappers rather than live proof holes.
>
> **Update, 2026-05-21.**  The first state and measurement pieces of the
> heterogeneous role-register construction are now present in Lean.
> `MIPStarRE.LDT.ProjStrat.roleRegisterSymmState` constructs the positive
> direct-sum role-register state on `Role × (ιA ⊕ ιB)`, and
> `MIPStarRE.LDT.ProjStrat.roleRegisterSymmState_density_fixed` proves the
> exchange symmetry stated immediately after the definition of
> \(\psi_{\mathrm{sym}}\) in the paper.  The theorem
> `MIPStarRE.LDT.ProjStrat.roleRegisterSymmState_isNormalized` proves its
> normalized-trace condition from the normalization of the original two-space
> state.  The proof is the explicit finite-dimensional trace calculation for
> the two occupied direct-sum sectors.  The theorem
> `MIPStarRE.LDT.ProjStrat.roleRegisterProjMeas` constructs the corresponding
> projective measurements, with point, axis-parallel, and diagonal measurement
> families, and `MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy` packages the
> state and these covariant measurements as a `SymStrat`.  The occupied-sector
> expectation identities
> `MIPStarRE.LDT.ProjStrat.ev_roleRegisterSymmState_rolePair_AB_localPairABBlock`
> and
> `MIPStarRE.LDT.ProjStrat.ev_roleRegisterSymmState_rolePair_BA_localPairBABlock_swap`
> now prove the two half-weight trace calculations from which the branch
> averages follow.  The branch-probability comparison has also been assembled:
> `MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_axisParallel_eq_roleAverage`,
> `MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_selfConsistency_eq_pointAgreement`,
> and
> `MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_diagonal_eq_roleAverage`
> identify the three tested branches of the heterogeneous role-register
> strategy with the corresponding two-space role averages, and
> `MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_is_good_three_mul` proves
> the `(3ε,3ε,3ε)` goodness comparison.  These declarations are axiom-clean.
> The principal-block extraction used in the reverse passage is also now
> present in Lean.  The file
> `MIPStarRE.LDT.Test.StrategyBiProjUnsymmetrization` defines the Alice and Bob
> block extractions from a POVM on `Role × (ιA ⊕ ιB)`, proves positivity,
> monotonicity, completeness preservation, compatibility with postprocessing
> and polynomial evaluation, and proves that extracting from
> `roleRegisterProjMeas` recovers the original point measurements.  These
> declarations are axiom-clean.  The remaining two-space role-register work for
> `thm:main-formal` is therefore not the existence of the block extraction.
> Lean now also records
> `MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_sourceMainInduction`, which
> applies the source-shaped main-induction theorem to the heterogeneous
> role-register symmetrization under the paper hypothesis \(k\ge md\).  This
> handoff inherits the source-range `sorryAx` from
> `MainInductionStep.mainInduction_sourceStatement`; it is not a completed
> final-theorem proof.  Lean also records
> `MIPStarRE.LDT.ProjStrat.sourceRoleRegisterUnsymmetrizedPointConsistency`,
> which combines this handoff with the factor-two trace-compression theorem and
> produces the two complete polynomial measurements with the two point-consistency
> estimates for the original two-space strategy.  The remaining source-boundary
> work is no longer this point-unsymmetrization step.  The point-agreement
> branch is also available for the two-space strategy, and the Step 5
> Schwartz--Zippel loss has been generalized to a bipartite state on
> \(H_A\otimes H_B\).  The heterogeneous triangle/SDD comparison theorem has
> also been proved, so Lean reaches the complete-measurement
> full-polynomial consistency statement at the end of the paper's Step 5
> calculation.  The heterogeneous orthonormalization steps on both tensor
> factors have also been formalized: from this complete-measurement consistency
> they produce projective submeasurements on \(H_A\) and \(H_B\), together with
> the corresponding SDD estimates.  The completion step has also been proved:
> the projective submeasurements are completed to projective measurements and
> the corresponding estimates are widened to the orthonormalize-and-complete
> error.  The repaired polynomial line-169 relations have also been derived
> from the pre-completion orthonormalization estimates.  The final
> point-evaluation triangle has also been derived from these polynomial
> relations by ordinary evaluation data processing and the heterogeneous
> triangle inequality.  The scalar absorption from these explicit
> pre-absorption errors to `mainFormalError` is now checked under the nonzero
> scalar-cascade boundary.  This passage predates the corrected final-theorem
> statement: the source-range and zero-sampling boundaries are now documented
> statement corrections, with \(k\ge400md\) and \(0<k\) assumed in the checked
> final theorem.
>
> **Update, 2026-05-21.**  The next missing assertion has now been proved as a
> trace-level calculation.  For an arbitrary role-register observable \(Y\), the factor-two
> unsymmetrization estimate cannot be proved from an operator identity of the
> form
> \[
>   P_{AB}(\rho)\,Y = P_{AB}(\rho\,Y_{AB}).
> \]
> Such an identity is false because \(Y\) may have off-role or off-direct-sum
> blocks.  What the paper uses is the corresponding trace-compression identity:
> after pairing with the \(AB\)-supported component of the symmetrized density,
> only the \((\mathrm A,\mathrm{inl})\)-left and
> \((\mathrm B,\mathrm{inr})\)-right principal block of \(Y\) contributes.  The
> theorem
> `MIPStarRE.LDT.ProjStrat.qBipartiteConsDefect_roleRegisterProjMeas_arbitrary_eq_average`
> formalizes the resulting average-of-two-defects identity for arbitrary
> role-register measurements.  The factor-two consequences are
> `MIPStarRE.LDT.ProjStrat.qBipartiteConsDefect_extractRoleRegisterBob_le_two_symm`
> and
> `MIPStarRE.LDT.ProjStrat.qBipartiteConsDefect_extractRoleRegisterAlice_le_two_symm`.
> These are direct analogues of the same-space theorem
> `MIPStarRE.LDT.qBipartiteConsDefect_roleSymmetrizedMeasurement_left`, now for
> the heterogeneous carrier `Role × (ιA ⊕ ιB)`.

## 1. Historical sorry site

**Historical direct file:** `MIPStarRE/LDT/MainInductionStep/Theorems/MainTheorems.lean:760`

**Historical direct theorem:**
`MIPStarRE.LDT.MainInductionStep.mainInductionSuccessorNext_ofSmallErrorConstruction`

At the time of the earlier report, the active goal was the small-error branch
of the native successor step in `thm:main-induction`:

```lean
∃ G : Measurement (Polynomial params.next) ι,
  ConsRel strategy.state (uniformDistribution (Point params.next))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
    (polynomialEvaluationFamily params.next G.toSubMeas)
    (mainInductionError params.next k eps delta gamma)
```

This theorem assumed precisely the successor branch hypotheses, including
`strategy.IsGood eps delta gamma`,
`400 * params.next.m * params.next.d ≤ k`, and
`mainInductionError params.next k eps delta gamma < 1`.  It does not assume
restricted-probability records, slice-induction data, self-improvement data,
pasting data, residual packages, or arbitrary implication hypotheses.
It is now proved in the corrected large-\(k\) interface.

The older conditional direct `sorry` in `MainFormal.lean` has been removed.  The
later source-boundary wrapper `mainFormal_sourceSmallErrorConclusion` is now
checked under the corrected hypotheses `k >= 400md` and `0 < k`.  The wrapper
`mainFormal_sourceConclusion` proves the saturated-error branch by a two-space
trivial measurement construction.
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

Verdict: the source theorem `thm:main-formal` is recorded in its corrected form
in the blueprint and is linked to the Lean statement
`MIPStarRE.LDT.Test.mainFormal_sourceStatement`, which calls the named
source-boundary construction `MIPStarRE.LDT.Test.mainFormal_sourceConclusion`.
This wrapper proves the saturated-error branch and calls
`MIPStarRE.LDT.Test.mainFormal_sourceSmallErrorConclusion` in the non-vacuous
small-error branch.
The Lean theorem `mainFormal` is a separate current interface with
faithful boundary hypotheses for the present formal container and the
documented large-`k` correction.  It has no bridge, residual, package, repair,
producer, input, or obligation hypothesis.  The corrected large-`k` Section 6
theorem and the corrected final two-space source theorem are now proved.  The
literal printed theorem is not formalized verbatim because of the confirmed
factor-\(400\) correction and the explicit boundary \(0<k\).

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

### Historical branch conditions
- `herr : ¬ 1 ≤ mainFormalError params k eps` — error is non-trivial
- `hm1 : params.m ≠ 1` — **successor case** (the base case `params.m = 1` is handled on lines 595-601)
- `hd : 0 < params.d` — historical positive-degree branch condition; the
  current recursive successor route no longer requires it as an active frontier
  assumption
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
recursive predecessor induction conclusion to each slice, assemble the pasting
input, and prove the scalar absorption estimates.

The checked assembly theorems have reduced this to one concrete component:

1. the predecessor induction argument for the answer-valued restricted slices.

This is not a hypothesis of `mainFormal`, nor of the paper-facing successor
step.  It is the remaining internal proof obligation in Section 6.

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
does not present those records as acceptable public inputs.  The later
successor repair proves `mainInductionSuccessorNext_ofSmallErrorConstruction`
for the corrected large-\(k\) interface.

**Status:** the role-register construction is no longer a separate
`mainFormal` gap.  Under the corrected final-theorem statement, the two-space
source-boundary assembly and the \(k\)-range correction are checked.

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
| Predecessor induction | Apply `thm:main-induction` to each answer-valued restricted predecessor slice | Still the genuine recursive part |
| Answer-valued slice realization | Build the slice self-improvement data for the answer-valued restricted interface | Discharged by `AnswerSelfImprovementData.ofAnswerCarrier` |
| Scalar absorption | Verify that the accumulated losses are bounded by `mainInductionError params.next k eps delta gamma` | Partly assembled; remaining estimates belong to #1507 |

The rejected historical route was to add records encoding these objects to
`mainFormal`, or to a paper-facing successor theorem.  That route would
strengthen the source statement.  The present route keeps the objects internal
to the Section 6 proof.  The former degree-zero family route is now only a
retained checked reduction; the active recursive-slice route applies also when
`params.d = 0`.

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
