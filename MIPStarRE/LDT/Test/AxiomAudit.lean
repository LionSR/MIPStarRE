import Lean
import MIPStarRE.LDT.ExpansionHypercubeGraph.MatrixRealization
import MIPStarRE.LDT.GlobalVariance.Theorems.MainTheorems
import MIPStarRE.LDT.MainInductionStep.Theorems.MainTheorems
import MIPStarRE.LDT.MainInductionStep.Theorems.SourceTheorems
import MIPStarRE.LDT.MakingMeasurementsProjective.NaimarkFull
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization
import MIPStarRE.LDT.MakingMeasurementsProjective.Producers
import MIPStarRE.LDT.Pasting.Bernoulli.Final
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.HelperCompleteness.Bracketed
import MIPStarRE.LDT.Test.Classical
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.SelfImprovementTop.Core
import MIPStarRE.LDT.Test.MainTheorem
import MIPStarRE.LDT.Test.StrategyBiProj

/-!
# Axiom audits for classical low-individual-degree soundness

Regression checks for the issue-#408 replacement of the former ambient
Polishchuk--Spielman axiom by the explicit hypothesis
`PolishchukSpielmanClassicalSoundnessStatement`.

The audits for
`MakingMeasurementsProjective.orthonormalizationCompletionRoute` and
`MakingMeasurementsProjective.orthonormalization` require the standard Lean
axioms only: the locality-preserving repair obligation in
`MakingMeasurementsProjective/Producers.lean` has been discharged for both the
documented completion-route construction and the paper-facing
`100\zeta^{1/4}` theorem.

The audit for `MakingMeasurementsProjective.orthonormalizationMainLemma`
requires the standard Lean axioms only: the source-facing
`84\zeta^{1/4}` measurement orthogonalization lemma is proved from the
left-lifted projectivization repair and no longer has any hidden repair input.
The source rounding-to-projectors proposition `projectiveNonMeasurement` and
its constructive theorem
`projectiveNonMeasurement_of_sourceAlmostProjective_full` are also checked
not to import `sorryAx`; the latter is the formal construction linked from
`\label{lem:projective-non-measurement}`, not an additional hypothesis of that
source lemma.

The audit for `SelfImprovement.selfImprovement` requires the standard Lean axioms
only: the issue-#1230 SDP slackness dependency has been discharged by the
canonical finite-dimensional SDP strong-duality argument.

The audit also checks the full selection-dependent `lem:add-in-u`
formalization.  The structure `SelfImprovement.AddInUFullStatement` records the
paper's universally quantified transfer inequality, while
`SelfImprovement.addInUFullStatement_of_isGood` constructs it from the standing
good-strategy hypotheses by using the selected Cauchy--Schwarz chain and the
global-variance estimate.  The reduced `addInU` lemma remains only a downstream
specialization.

The audit for `Test.mainFormal` records the current tracked proof gap
transitively: the current same-space, corrected large-`k`
interface has no connection, residual, repair, data, or obligation hypotheses,
and its proof is assembled from named construction targets.  The same-space
restriction is documented in
`docs/paper-gaps/issue-930-main-formal-interface-restrictions.tex`; the
large-`k` and `k > 0` scalar-cascade boundary is documented in
`docs/paper-gaps/issue-906-main-formal-k-bound.tex`.  After the
projective-completion refactor, the active `mainFormal` cascade routes through
`MainInductionStep.mainInduction` via `strategySymmetrization_mainInduction`.
The base case is proved by `mainInductionBaseCase`, while the arbitrary
non-base branch merely decomposes the parameters and invokes the native
successor-step theorem `mainInductionSuccessorNext`, whose nontrivial branch
is the named construction obligation
`mainInductionSuccessorNext_ofSmallErrorConstruction`.  Thus the only remaining
transitive `sorryAx` dependency on the current `mainFormal` path is this
small-error successor construction, tracked by issue #1507 (with #1458 as the
umbrella tracking issue).

The source statements `Test.mainFormal_sourceStatement` and
`MainInductionStep.mainInduction_sourceStatement` are audited separately as
source-boundary gaps.  They record the printed paper hypotheses (`k ≥ md`, and
in the final theorem a general two-space projective strategy) without linking
the source blueprint entries to the restricted corrected interfaces.  The
remaining source interval for `thm:main-induction` is isolated as
`MainInductionStep.mainInduction_sourceRangeObligation`, whose large-error
branch is now proved by `mainInductionOfOneLeError` and whose small-error branch
is the named obligation
`MainInductionStep.mainInduction_sourceRangeSmallErrorObligation`.  That theorem
also proves the base case by `mainInductionBaseCase`; the remaining direct
source-range proof hole is
`MainInductionStep.mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation`,
after `MainInductionStep.mainInduction_sourceRangeSmallErrorNonBaseObligation`
removes the impossible degree-zero branch and
`MainInductionStep.mainInduction_sourceRangeSmallErrorPositiveNonBaseObligation`
derives `1 ≤ k`.  The final
theorem source boundary is wrapped by `Test.mainFormal_sourceObligation`, whose
saturated-error branch is proved and whose remaining branch is the named
obligation `Test.mainFormal_sourceSmallErrorObligation`.  These are named proof
obligations, not bridge or residual assumptions.

The same-space corrected-range subcase of the final source conclusion is
recorded separately as `Test.mainFormal_sourceConclusion_ofSameSpaceLargeK`.
It is audited with the current `mainFormal` route: it proves the source-shaped
conclusion for the forgetful image of a `SameSpaceProjStrat`, under
`400md ≤ k` and `0 < k`, and therefore has exactly the same transitive Section
6 successor dependency as `mainFormal`.

The audit for `GlobalVariance.globalVarianceOfPoints` now requires the standard
Lean axioms only: the issue-#1456 six-step local transport estimate is supplied
by `GlobalVariance.localVarianceTransportChainBound`, so the paper-facing theorem
no longer carries a `sorryAx` dependency.

The audit for `MainInductionStep.selfImprovementInInductionSection` records
standard Lean axioms only: the measurement-valued realization of
`thm:self-improvement-in-induction-section` no longer inherits the issue-#1230
SDP slackness obligation.

The audit for `MainInductionStep.mainInduction` records the current proof
obligation for the separate corrected large-`k` Lean interface to
`thm:main-induction`.  The source-labelled blueprint theorem keeps the printed
`k ≥ m d` hypothesis, while the Lean interface assumes the documented
correction `k ≥ 400 m d`.  The scalar side-condition discrepancy is recorded in
`docs/paper-gaps/issue-906-main-formal-k-bound.tex`.  The remaining work is to
derive the internal successor-stage inputs from these corrected theorem
hypotheses.  This is tracked by issue #1507.

The audit for
`MainInductionStep.mainInductionSuccessorNext_ofSmallErrorConstruction` records
the current direct `sorryAx` site: this theorem is the named small-error
successor construction obligation for the native Section 6 step.  The public
successor theorem `MainInductionStep.mainInductionSuccessorNext` calls it only
after splitting off the already proved large-error branch.  The theorem is a
closure obligation for the eventual induction proof: the predecessor induction
argument must be supplied by induction on the dimension and then consumed by
the checked degree-split reductions below, not added as a theorem hypothesis of
`mainInduction` or `mainFormal`.
The transitive audit also records the exact downstream Section 6 and Section 3
handoff: `mainInductionSuccessor`, `mainInduction`,
`strategySymmetrization_mainInduction`, and
`MainFormalRoleInductionWitness.ofMainInduction` inherit precisely this same
frontier and no additional proof hole.
The Lean docstrings on this route carry explicit unfaithful-dependency markers for
the tracked `sorryAx` dependency; these markers describe proof status and do not
add hypotheses to the source statements.

The audit for
`MainInductionStep.mainInductionSuccessorNext_ofAnswerStageObligations` and
`MainInductionStep.mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBound`
requires the standard Lean axioms only.  These internal helpers are not the
paper theorem; they prove the positive-degree nontrivial successor conclusion
once the predecessor answer-valued induction hypothesis and concrete
answer-valued slice-transport data have been supplied internally.  The latter
helper also derives the predecessor large-`k` and `k ≥ 1` side conditions from
the successor large-`k` hypothesis.  The split helper
`MainInductionStep.mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBoundSplit`
also discharges the complementary large-error branch, so the remaining
positive-degree frontier is the small-error answer-valued slice construction
and the predecessor induction argument.  The further checked assembly theorem
`MainInductionStep.mainInductionSuccessorNext_ofDegreeSplitObligations` splits
the small-error successor frontier into the positive-degree answer-valued route
and a separate degree-zero successor construction.  The checked helper
`MainInductionStep.mainInductionSuccessorNext_degreeZero_ofPastingFamily` shows
that the degree-zero branch follows from the existing degree-zero pasting
construction once a complete, point-consistent slice family and the scalar
absorption into `mainInductionError` have been supplied internally.  The further
checked composition theorem
`MainInductionStep.mainInductionSuccessorNext_ofDegreeSplitPastingObligations`
therefore states the remaining degree-zero input in terms of exactly that
family-and-scalar construction, rather than as an abstract successor conclusion.
The theorem
`MainInductionStep.mainInductionSuccessorNext_ofSmallErrorConstruction_ofInternalConstructions`
then records the exact small-error closure from these internal constructions
and the predecessor induction hypothesis; it is checked and does not import the
remaining `sorryAx`.
The named stage-data constructors used by these reductions are also checked not
to import `sorryAx`; they are bookkeeping and transport constructions, not
hidden proof assumptions for the paper theorem.

The Section 3 final-theorem witness constructors have the same separation.
Base-case role witnesses and projective-completion transport are standard-axiom
clean.  The successor-dependent role witness inherits the single tracked
`sorryAx` only through `MainInductionStep.mainInduction`, not through an added
final-theorem witness hypothesis.

The audit for `Pasting.ldPasting` now requires the standard Lean axioms only:
the unrestricted paper-facing theorem no longer depends on a dedicated
degree-zero `sorryAx`, because issue #1622 has been discharged by the direct
degree-zero construction in `Pasting/Bernoulli/Final.lean`.

The audits for `CommutativityPoints.commutativityPoints`,
`Commutativity.commDataProcessedG`, and `Commutativity.comMain` require the
standard Lean axioms only.  The boundedness data consumed by the latter two
is the formal record for the boundedness witnesses `Z^x` appearing explicitly
in `references/ldt-paper/commutativity-G.tex`; it is not an additional bridge
or residual hypothesis.

The audit for `ExpansionHypercubeGraph.laplacianSpectralGapOrdered` now
requires the standard Lean axioms only: the ordered-eigenvalue statement of
`cor:laplacian-spectral-gap` is proved by connecting the Fourier
diagonalization to the ordered roots of the characteristic polynomial, so the
former issue-#1497 `sorryAx` dependency is gone.

The axiom expectation is attached to each declaration separately. A declaration
using one of the `assert_*_axioms` commands with `sorryAx` in its expected set
has a named proof obligation still to be discharged; fulfilling one such
obligation should not change the audit status of the others.

The audit for the helper strong self-consistency assembly now requires the
standard Lean axioms only: the issue-#1514 local estimate is proved by the
`HelperSSC` chain.  The audit for `SelfImprovement.selfImprovementHelper` also
requires the standard Lean axioms only: the issue-#1230 SDP slackness dependency
has been discharged.

The audit for `SelfImprovement.sdp_statement_with_slackness` requires the
standard Lean axioms only.  The theorem states and proves the SDP strong-duality
and complementary-slackness conclusion of `lem:sdp` from the canonical
finite-dimensional semidefinite-programming argument.  The same audit covers
the abstract slackness structures, the matrix-level slackness statement, the
canonical-to-abstract extraction theorem, and the displayed measurement witness
used by the helper proof.

The audit for
`Test.TwoProverClassicalLIDStrategy.lowIndividualDegreeAcceptanceProbability_eq_branchAverage`
requires the standard Lean axioms only.  It is the definitional branch-average
calculation for the displayed low-individual-degree test figure.

The blueprint-linked auxiliary declarations whose names contain words such as
`Input`, `Repair`, `Residual`, `Package`, `Hypotheses`, `Obligations`, `Bridge`,
or `Producer` are all covered by explicit assertions in this file.  These names
are not by themselves proof defects: some are direct encodings of paper
hypotheses, some are construction theorems, and some are internal proof
frontiers.  The audit records whether each checked declaration uses only the
standard Lean axioms, has exactly the expected Section 6 `sorryAx` dependency,
or does not itself import the remaining `sorryAx` frontier.

This module is built explicitly in CI rather than imported from the umbrella
library modules, so the axiom audits stay out of normal downstream imports
while still acting as regression tests.
-/

open Lean Elab Command

private def expectedStandardAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound].qsort Name.lt

private def expectedStandardAxiomsWithSorry : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound, ``sorryAx].qsort Name.lt

/-- Standard kernel axioms plus `sorryAx`; tracks the transitive
`mainFormal` construction gap, currently localized to
`mainInductionSuccessorNext_ofSmallErrorConstruction` via
`MainInductionStep.mainInduction` (issue #1507; umbrella #1458). -/
private def expectedMainFormalAxioms : Array Name :=
  expectedStandardAxiomsWithSorry

/-- Standard kernel axioms only: the issue-#1032 scalar discrepancy for
`thm:orthonormalization` has been repaired without making the theorem depend on
the still-unproved heterogeneous `orthonormalizationMainLemma`. -/
private def expectedOrthonormalizationAxioms : Array Name :=
  expectedStandardAxioms

/-- Standard kernel axioms only: the issue #1230 SDP slackness dependency used
by `selfImprovement` has been discharged. -/
private def expectedSelfImprovementAxioms : Array Name :=
  expectedStandardAxioms

/-- Standard kernel axioms only: the issue #1230 SDP slackness dependency used
by `selfImprovementInInductionSection` has been discharged. -/
private def expectedInductionSelfImprovementAxioms : Array Name :=
  expectedStandardAxioms

/-- Standard kernel axioms plus `sorryAx`; tracks the issue #1507 derivation
needed for `mainInduction`. -/
private def expectedMainInductionAxioms : Array Name :=
  expectedStandardAxiomsWithSorry

/-- Standard kernel axioms only: the issue #1622 degree-zero branch for
unrestricted `ldPasting` has been discharged. -/
private def expectedLdPastingAxioms : Array Name :=
  expectedStandardAxioms

/-- Standard kernel axioms only: the issue #1497 derivation for
`laplacianSpectralGapOrdered` has been discharged. -/
private def expectedOrderedLaplacianGapAxioms : Array Name :=
  expectedStandardAxioms

/-- Standard kernel axioms only: the issue #1230 SDP slackness derivation used
by `selfImprovementHelper` has been discharged. -/
private def expectedSelfImprovementHelperAxioms : Array Name :=
  expectedStandardAxioms

/-- Standard kernel axioms only: the issue #1230 derivation needed for the SDP
complementary-slackness statement (`lem:sdp`) has been discharged. -/
private def expectedSdpSlacknessAxioms : Array Name :=
  expectedStandardAxioms

private def assertUsesExactlyAxioms (declName : Name) (expected : Array Name) :
    CommandElabM Unit := do
  let axioms := (← Lean.collectAxioms declName).qsort Name.lt
  unless axioms == expected do
    throwError
      m!"'{declName}' depends on axioms {axioms.toList}, expected exactly " ++
        m!"{expected.toList}"

private def assertUsesOnlyStandardAxioms (declName : Name) : CommandElabM Unit := do
  assertUsesExactlyAxioms declName expectedStandardAxioms

private def assertDoesNotUseSorryAxiom (declName : Name) : CommandElabM Unit := do
  let axioms := (← Lean.collectAxioms declName).qsort Name.lt
  if axioms.contains ``sorryAx then
    throwError m!"'{declName}' unexpectedly depends on `sorryAx`; axioms: {axioms.toList}"

private def assertUsesOnlyStandardOrSorryAxiomsWithSorry (declName : Name) :
    CommandElabM Unit := do
  let axioms := (← Lean.collectAxioms declName).qsort Name.lt
  unless axioms.contains ``sorryAx do
    throwError m!"'{declName}' was expected to carry the tracked source-statement gap"
  for ax in axioms do
    unless expectedStandardAxiomsWithSorry.contains ax do
      throwError
        m!"'{declName}' depends on nonstandard axiom {ax}; axioms: {axioms.toList}"

private def resolveDeclIdent (id : TSyntax `ident) : CommandElabM Name := do
  liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo id

elab "assert_standard_axioms " id:ident : command => do
  assertUsesOnlyStandardAxioms (← resolveDeclIdent id)

elab "assert_no_sorry_axiom " id:ident : command => do
  assertDoesNotUseSorryAxiom (← resolveDeclIdent id)

elab "assert_source_statement_gap_axioms " id:ident : command => do
  assertUsesOnlyStandardOrSorryAxiomsWithSorry (← resolveDeclIdent id)

elab "assert_main_formal_axioms " id:ident : command => do
  assertUsesExactlyAxioms (← resolveDeclIdent id) expectedMainFormalAxioms

elab "assert_orthonormalization_axioms " id:ident : command => do
  assertUsesExactlyAxioms (← resolveDeclIdent id) expectedOrthonormalizationAxioms

elab "assert_self_improvement_axioms " id:ident : command => do
  assertUsesExactlyAxioms (← resolveDeclIdent id) expectedSelfImprovementAxioms

elab "assert_induction_self_improvement_axioms " id:ident : command => do
  assertUsesExactlyAxioms (← resolveDeclIdent id) expectedInductionSelfImprovementAxioms

elab "assert_main_induction_axioms " id:ident : command => do
  assertUsesExactlyAxioms (← resolveDeclIdent id) expectedMainInductionAxioms

elab "assert_ld_pasting_axioms " id:ident : command => do
  assertUsesExactlyAxioms (← resolveDeclIdent id) expectedLdPastingAxioms

elab "assert_ordered_laplacian_gap_axioms " id:ident : command => do
  assertUsesExactlyAxioms (← resolveDeclIdent id) expectedOrderedLaplacianGapAxioms

elab "assert_self_improvement_helper_axioms " id:ident : command => do
  assertUsesExactlyAxioms (← resolveDeclIdent id) expectedSelfImprovementHelperAxioms

elab "assert_sdp_slackness_axioms " id:ident : command => do
  assertUsesExactlyAxioms (← resolveDeclIdent id) expectedSdpSlacknessAxioms

assert_standard_axioms MIPStarRE.LDT.Test.razSafra
assert_standard_axioms MIPStarRE.LDT.Test.PolishchukSpielmanClassicalSoundnessStatement
assert_standard_axioms MIPStarRE.LDT.Test.classicalTestSoundness
assert_standard_axioms MIPStarRE.LDT.MakingMeasurementsProjective.questionwiseNaimark
assert_source_statement_gap_axioms
  MIPStarRE.LDT.MainInductionStep.mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation
assert_source_statement_gap_axioms
  MIPStarRE.LDT.MainInductionStep.mainInduction_sourceRangeSmallErrorPositiveNonBaseObligation
assert_source_statement_gap_axioms
  MIPStarRE.LDT.MainInductionStep.mainInduction_sourceRangeSmallErrorNonBaseObligation
assert_source_statement_gap_axioms
  MIPStarRE.LDT.MainInductionStep.mainInduction_sourceRangeSmallErrorObligation
assert_source_statement_gap_axioms
  MIPStarRE.LDT.MainInductionStep.mainInduction_sourceRangeObligation
assert_source_statement_gap_axioms
  MIPStarRE.LDT.MainInductionStep.mainInduction_sourceStatement
assert_source_statement_gap_axioms MIPStarRE.LDT.Test.mainFormal_sourceSmallErrorObligation
assert_source_statement_gap_axioms MIPStarRE.LDT.Test.mainFormal_sourceObligation
assert_source_statement_gap_axioms MIPStarRE.LDT.Test.mainFormal_sourceStatement

/-! Chapter 2 interfaces used by the final-theorem route.  These are
foundational definitions and elementary API statements; the regression check is
that none of them hides a proof-hole dependency. -/
assert_no_sorry_axiom MIPStarRE.LDT.Role
assert_no_sorry_axiom MIPStarRE.LDT.Role.other
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.lowIndividualDegreeFailureProbability
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.PassesLowIndividualDegreeTest
assert_no_sorry_axiom MIPStarRE.LDT.SameSpaceProjStrat
assert_no_sorry_axiom MIPStarRE.LDT.SameSpaceProjStrat.lowIndividualDegreeFailureProbability
assert_no_sorry_axiom MIPStarRE.LDT.SameSpaceProjStrat.PassesLowIndividualDegreeTest
assert_no_sorry_axiom MIPStarRE.LDT.SameSpaceProjStrat.toGeneralProjStrat
assert_no_sorry_axiom MIPStarRE.LDT.SymStrat
assert_no_sorry_axiom MIPStarRE.LDT.SymStrat.IsGood
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.localDirectSumBlock_nonneg
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.roleBlock_mul
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.roleBlock_nonneg
assert_no_sorry_axiom MIPStarRE.LDT.lastDirectionLine
assert_no_sorry_axiom MIPStarRE.LDT.lastDirectionMeasurementFamily
assert_no_sorry_axiom MIPStarRE.LDT.RestrictedDiagonalSample
assert_no_sorry_axiom MIPStarRE.LDT.Test.mainFormal_source_trivial_witness
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.RestrictedSymStrat.diagonalFailureProbability

namespace MIPStarRE.LDT.Test.TwoProverClassicalLIDStrategy

assert_standard_axioms lowIndividualDegreeAcceptanceProbability_eq_branchAverage

end MIPStarRE.LDT.Test.TwoProverClassicalLIDStrategy

assert_standard_axioms
  MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationCompletionRoute
assert_standard_axioms MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationMainLemma
assert_no_sorry_axiom MIPStarRE.LDT.MakingMeasurementsProjective.projectiveNonMeasurement
assert_no_sorry_axiom
  MIPStarRE.LDT.MakingMeasurementsProjective.projectiveNonMeasurement_of_sourceAlmostProjective_full
assert_standard_axioms
  MIPStarRE.LDT.MakingMeasurementsProjective.projectiveLowRankSum_of_spectralTruncationStatement
assert_orthonormalization_axioms
  MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalization
assert_no_sorry_axiom MIPStarRE.LDT.SelfImprovement.AddInUFullStatement
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.addInUFullStatement_of_isGood
assert_main_formal_axioms MIPStarRE.LDT.Test.mainFormal
assert_main_formal_axioms MIPStarRE.LDT.Test.mainFormal_sourceConclusion_ofSameSpaceLargeK
assert_standard_axioms
  MIPStarRE.LDT.Test.MainFormalDiagonalCompletionWitness.nonempty_ofDiagonalConsistency
assert_standard_axioms
  MIPStarRE.LDT.Test.MainFormalDiagonalOrthonormalizationWitness.nonempty_ofDiagonalConsistency
assert_self_improvement_axioms MIPStarRE.LDT.SelfImprovement.selfImprovement
assert_standard_axioms MIPStarRE.LDT.GlobalVariance.globalVarianceOfPoints
assert_induction_self_improvement_axioms
  MIPStarRE.LDT.MainInductionStep.selfImprovementInInductionSection
assert_main_induction_axioms
  MIPStarRE.LDT.MainInductionStep.mainInductionSuccessorNext_ofSmallErrorConstruction
assert_main_induction_axioms
  MIPStarRE.LDT.MainInductionStep.mainInductionSuccessorNext
assert_main_induction_axioms
  MIPStarRE.LDT.MainInductionStep.mainInductionSuccessor
assert_standard_axioms
  MIPStarRE.LDT.MainInductionStep.mainInductionSuccessorNext_ofAnswerStageObligations
assert_standard_axioms
  MIPStarRE.LDT.MainInductionStep.mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBound
assert_standard_axioms
  MIPStarRE.LDT.MainInductionStep.mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBoundSplit
assert_standard_axioms
  MIPStarRE.LDT.MainInductionStep.mainInductionSuccessorNext_ofDegreeSplitObligations
assert_standard_axioms
  MIPStarRE.LDT.MainInductionStep.mainInductionSuccessorNext_degreeZero_ofPastingFamily
assert_standard_axioms
  MIPStarRE.LDT.MainInductionStep.mainInductionSuccessorNext_ofDegreeSplitPastingObligations
assert_standard_axioms
  MIPStarRE.LDT.MainInductionStep.mainInductionSuccessorNext_ofSmallErrorConstruction_ofInternalConstructions
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.SliceRestrictionData
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.AnswerSliceRestrictionData
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.PerSliceInductionData
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.AnswerPerSliceInductionData
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.SelfImprovementData
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.SelfImprovementData.SliceStrategyTransport
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.AnswerSelfImprovementData
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.AnswerSelfImprovementData.SliceStrategyTransport
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.AveragedPastingData
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.RestrictedSymStrat
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.xRestrictedStrategy
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.AnswerMainInductionConclusion
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.AnswerMainInductionHypothesis
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.averageRestrictedAxisParallelError
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.averageRestrictedSelfConsistencyError
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.averageRestrictedDiagonalError
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.RestrictedProbabilitiesStatement.ofWeightedBounds
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.weighted_axisParallel_bound
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.weighted_diagonal_bound
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.restrictedProbabilities
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.mainInductionBaseCase
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.mainInductionOfOneLeError
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.selfImprovementInInductionSectionConclusion_ofSelfImprovementConclusion
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.selfImprovementInInductionError_le_one_of_mainInductionError_lt_one
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.AnswerSliceRestrictionData.ofRestrictedProbabilities
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.AnswerPerSliceInductionData.ofLegacy
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.AnswerPerSliceInductionData.ofMainInductionHypothesis
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.PerSliceInductionData.ofAnswer
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.SelfImprovementData.SliceStrategyTransport.averagedPoint_eq_of_pointMeasurement_eq
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.SelfImprovementData.SliceStrategyTransport.ofPointMeasurementEq
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.SelfImprovementData.SliceStrategyTransport.good_of_restrictedGood
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.SelfImprovementData.SliceStrategyTransport.ofMeasurementEq
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.SelfImprovementData.ofSelfImprovementInInductionSection
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.SelfImprovementData.ofSliceStrategyTransport
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.SelfImprovementData.ofAnswerForLegacy
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.SelfImprovementData.ofAnswer
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.AnswerSelfImprovementData.SliceStrategyTransport.averagedPoint_eq_of_pointMeasurement_eq
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.AnswerSelfImprovementData.SliceStrategyTransport.ofPointMeasurementEq
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.AnswerSelfImprovementData.SliceStrategyTransport.good_of_restrictedGood
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.AnswerSelfImprovementData.SliceStrategyTransport.ofMeasurementEq
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.AnswerSelfImprovementData.ofSelfImprovementInInductionSection
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.AnswerSelfImprovementData.ofSliceStrategyTransport
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.AveragedPastingData.invokeLdPasting
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.assembleAveragedPastingData
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.assembleAveragedPastingDataOfSmallError
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.ldPastingInInductionSection
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.mainInductionFromStageData
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.mainInductionFromAnswerStageDataOfSmallError
assert_main_induction_axioms MIPStarRE.LDT.MainInductionStep.mainInduction
assert_main_induction_axioms
  MIPStarRE.LDT.Test.strategySymmetrization_mainInduction
assert_standard_axioms
  MIPStarRE.LDT.Test.MainFormalRoleInductionWitness.ofMainInductionWitness
assert_standard_axioms
  MIPStarRE.LDT.Test.MainFormalRoleInductionWitness.ofBaseCase
assert_standard_axioms
  MIPStarRE.LDT.Test.MainFormalRoleInductionWitness.toRoleMeasurementWitness
assert_standard_axioms
  MIPStarRE.LDT.Test.MainFormalRoleInductionWitness.roleWitness
assert_standard_axioms MIPStarRE.LDT.Test.mainFormalBaseRoleInductionWitness
assert_main_induction_axioms
  MIPStarRE.LDT.Test.MainFormalRoleInductionWitness.ofMainInduction
assert_standard_axioms
  MIPStarRE.LDT.Test.MainFormalProjectiveCompletionTransportWitness.nonempty_ofRoleWitness
assert_standard_axioms
  MIPStarRE.LDT.Test.mainFormal_ofProjectiveCompletionTransportWitness
assert_standard_axioms MIPStarRE.LDT.Pasting.ldPastingDegreeZeroBranch
assert_standard_axioms MIPStarRE.LDT.Pasting.ldPastingNontrivialPublicBranch
assert_ld_pasting_axioms MIPStarRE.LDT.Pasting.ldPasting
assert_standard_axioms MIPStarRE.LDT.CommutativityPoints.commutativityPoints
assert_standard_axioms MIPStarRE.LDT.Commutativity.commDataProcessedG
assert_standard_axioms MIPStarRE.LDT.Commutativity.comMain
assert_ordered_laplacian_gap_axioms
  MIPStarRE.LDT.ExpansionHypercubeGraph.laplacianSpectralGapOrdered
assert_standard_axioms
  MIPStarRE.LDT.SelfImprovement.helper_strong_self_consistency_of_helper_conclusion
assert_self_improvement_helper_axioms MIPStarRE.LDT.SelfImprovement.selfImprovementHelper
assert_no_sorry_axiom MIPStarRE.LDT.SelfImprovement.SdpOptimalPairWithSlackness
assert_no_sorry_axiom MIPStarRE.LDT.SelfImprovement.SdpOptimalPairWithSlackness.primalMeasurement
assert_no_sorry_axiom MIPStarRE.LDT.SelfImprovement.SdpStatementWithSlackness
assert_no_sorry_axiom MIPStarRE.LDT.SelfImprovement.sdpStrictDualWitness
assert_no_sorry_axiom MIPStarRE.LDT.SelfImprovement.sdpStrictDualWitness_nonneg
assert_no_sorry_axiom MIPStarRE.LDT.SelfImprovement.one_le_sdpStrictDualWitness
assert_no_sorry_axiom MIPStarRE.LDT.SelfImprovement.matrixSdpStrictDualWitness
assert_no_sorry_axiom MIPStarRE.LDT.SelfImprovement.matrixSdpStrictDualWitness_nonneg
assert_no_sorry_axiom MIPStarRE.LDT.SelfImprovement.one_le_matrixSdpStrictDualWitness
assert_no_sorry_axiom MIPStarRE.LDT.SelfImprovement.matrixSdpStrictDualWitness_dualFeasible
assert_no_sorry_axiom MIPStarRE.LDT.SelfImprovement.one_le_matrixSdpStrictDualWitness_dualSlack
assert_no_sorry_axiom MIPStarRE.LDT.SelfImprovement.MatrixSdpStatementWithSlackness
assert_no_sorry_axiom MIPStarRE.LDT.SelfImprovement.MatrixSdpOptimalWitnessWithDominance
assert_no_sorry_axiom MIPStarRE.LDT.SelfImprovement.MatrixSdpStatementWithSlacknessAndDominance
assert_no_sorry_axiom MIPStarRE.LDT.SelfImprovement.MatrixSdpCanonicalOptimalPairWithDominance
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.matrixSdpOptimalWitness_of_canonicalSaturatedComplementarySlackness
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.matrixSdpOptimalWitness_of_canonicalFeasibleSaturatedComplementarySlackness
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.matrixSdpStatementWithSlackness_of_canonicalSaturatedComplementarySlackness
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.matrixSdpStatementWithSlackness_of_canonicalFeasibleSaturatedComplementarySlackness
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.MatrixSdpCanonicalOptimalPair.toMatrixSdpStatementWithSlackness
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.MatrixSdpCanonicalOptimalPair.withDominance
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.MatrixSdpCanonicalOptimalPairWithDominance.toMatrixSdpStatementWithSlacknessAndDominance
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.MatrixSdpCanonicalOptimalPairWithDominance.toCanonicalOptimalPair
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.MatrixSdpCanonicalOptimalPairWithDominance.toMatrixSdpStatementWithSlackness
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.matrixSdpComplementarySlacknessEquation
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.matrixSdpMeasurementWitness_of_canonicalFeasibleComplementarySlackness
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.sdpStatementWithSlackness_of_canonicalFeasibleComplementarySlackness
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.sdpStatementWithSlackness_of_canonicalOptimalPair
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.sdpStatementWithSlackness_of_exists_canonicalOptimalPair
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.sdpStatementWithSlackness_of_canonicalOptimalPairWithDominance
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.sdpStatementWithSlackness_of_canonicalOptimalPair_of_dualDominatesIdentity
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.sdpMeasurementWitness_of_canonicalOptimalPair
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.sdpMeasurementWitness_of_exists_canonicalOptimalPair
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.sdpMeasurementWitness_of_canonicalFeasibleComplementarySlackness
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.sdpMeasurementWitness_of_canonicalOptimalPairWithDominance
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.sdpMeasurementWitness_of_canonicalOptimalPair_of_dualDominatesIdentity
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.matrixSdpPointRealization_statementWithSlackness
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.matrixSdpCanonicalComplementarySlackness_of_strongDuality
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.matrixSdpComplementarySlacknessDefect_of_canonical
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.matrixSdpComplementarySlacknessDefect_extracted_of_canonical
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.matrixSdpCanonicalSlack_mul_dual_of_complementarySlackness
assert_sdp_slackness_axioms MIPStarRE.LDT.SelfImprovement.sdp_statement_with_slackness
assert_standard_axioms MIPStarRE.LDT.SelfImprovement.sdp_slackness_measurement

assert_no_sorry_axiom
  MIPStarRE.LDT.MakingMeasurementsProjective.leftLiftedProjectivizationRepair
assert_no_sorry_axiom
  MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationMeasurement_of_consistency_from_projectivizationRepair
assert_no_sorry_axiom
  MIPStarRE.LDT.MakingMeasurementsProjective.projectiveLowRankSum_of_spectralTruncationStatement
assert_no_sorry_axiom
  MIPStarRE.LDT.IdxPolyFamily.SliceBoundednessInput.storedBoundedResidualBound
assert_no_sorry_axiom
  MIPStarRE.LDT.IdxPolyFamily.SliceBoundednessInput.averagedPoint_le_witness
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.HelperStrongSelfConsistencyObligations
assert_no_sorry_axiom MIPStarRE.LDT.Test.CascadeHypotheses
