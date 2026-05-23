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
import MIPStarRE.LDT.Test.StrategyBiProjRoleAverage
import MIPStarRE.LDT.Test.StrategyBiProjUnsymmetrization

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

The audit for the full Naimark theorem separates the Lean statement of the
paper's projective-submeasurement tensor correlation theorem from the checked
questionwise interface.  The theorem
`MakingMeasurementsProjective.oneMeasNaimark` and
`MakingMeasurementsProjective.naimarkTensorProductCorrelation` are now
axiom-clean: the one-measurement theorem is proved by the finite-dimensional
isometry-extension construction, and the four-register trace identity
`OneMeasNaimarkData.twoSidedCorrelationPreservation` has been discharged from
the checked one-measurement compression identity.  The theorem
`MakingMeasurementsProjective.questionwiseNaimark` remains a separate
axiom-clean Lean-only interface entry.

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

The audit for `Test.mainFormal` records that the current same-space, corrected
large-`k` interface has no connection, residual, repair, data, or obligation hypotheses,
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
is the named construction theorem
`mainInductionSuccessorNext_ofSmallErrorConstruction`.  That ordinary successor
theorem now has no direct `sorry`; it calls the internal simultaneous
answer-valued induction theorem `MainInductionStep.answerMainInduction`.  The
answer-valued pasting theorem
`MainInductionStep.answerLdPastingInInductionSectionOfSmallError` is now a
checked reduction through discharged answer-valued estimates:
`answerComMainForCarrier_ofAnswerGood`, the proved
`answerLdPastingInInductionSectionDegreeZeroOfSmallError`, and the proved
`answerLdPastingInInductionError_le_mainInductionError_of_smallError`.  The
predecessor answer-valued induction argument is supplied inside
`MainInductionStep.answerMainInduction`, not asserted as a standalone theorem
hypothesis.  The former degree-zero family branch has been removed from the
active frontier because the predecessor induction hypothesis no longer assumes
`0 < d`; in the nontrivial branch, `1 ≤ k` is derived from
`mainInductionError < 1`.  The
answer-valued self-improvement data are constructed by the
standard-axiom-clean carrier route.  The answer-valued base case
`MainInductionStep.answerMainInductionBaseCase` is standard-axiom clean, using
the same one-dimensional axis-parallel-line construction as the ordinary base
case.  The answer-valued large-error branch
`MainInductionStep.answerMainInductionOfOneLeError` is also standard-axiom
clean, using the same distinguished trivial polynomial measurement as the
ordinary large-error branch.  The answer-valued successor slice theorem
`MainInductionStep.answerSuccessorRestrictedSliceConclusions` now performs the
local recursive application to every restricted slice once the predecessor
answer-valued induction hypothesis is in scope.  Thus the former transitive
`sorryAx` dependency has been removed from the current `mainFormal` path.  The
source-boundary declarations audited below are now standard-axiom clean under the
corrected large-`k` and nonzero sampling hypotheses.

The corrected source statement `MainInductionStep.mainInduction_sourceStatement`
is audited with standard kernel axioms only.  The paper prints the weaker
hypothesis `k ≥ md`, but the project records the missing factor `400` as a
confirmed theorem-level correction rather than as a remaining proof obligation.
The final theorem source-boundary declaration proves the saturated-error branch,
while its small-error branch calls the checked role-register scalar-boundary
theorem under the corrected nonzero sampling hypothesis.  The zero-sampling
boundary tracked by #422 is now removed from the source theorem statement by the
explicit hypothesis `0 < k`.

The same-space corrected-range subcase of the final source conclusion is
recorded separately as `Test.mainFormal_sourceConclusion_ofSameSpaceLargeK`.
It is audited with the current `mainFormal` route: it proves the paper
conclusion for the forgetful image of a `SameSpaceProjStrat`, under
`400md ≤ k` and `0 < k`, and is standard-axiom clean.

The audit for `GlobalVariance.globalVarianceOfPoints` now requires the standard
Lean axioms only: the issue-#1456 six-step local transport estimate is supplied
by `GlobalVariance.localVarianceTransportChainBound`, so the paper-facing theorem
no longer carries a `sorryAx` dependency.

The audit for `MainInductionStep.selfImprovementInInductionSection` records
standard Lean axioms only: the measurement-valued realization of
`thm:self-improvement-in-induction-section` no longer inherits the issue-#1230
SDP slackness obligation.

The audit for `MainInductionStep.mainInduction` records that the corrected
large-`k` Lean interface to `thm:main-induction` is now proved.  The
source-labelled blueprint theorem uses the same corrected hypothesis
`k ≥ 400 m d`.  The scalar side-condition discrepancy is recorded in
`docs/paper-gaps/issue-906-main-formal-k-bound.tex` as a confirmed statement
gap in the printed theorem statement.

The audit for
`MainInductionStep.mainInductionSuccessorNext_ofSmallErrorConstruction` records
that the small-error successor construction for the native Section 6 step is
now standard-axiom clean.  The
public successor theorem `MainInductionStep.mainInductionSuccessorNext` calls it
only after splitting off the already proved large-error branch.  This theorem
is now proved from the internal answer-valued induction theorem
`MainInductionStep.answerMainInduction` and the checked answer-carrier
successor reduction.  The direct `sorryAx` site is no longer the ordinary
successor theorem, nor the answer-valued successor corollary; the answer-valued
pasting theorem is also proved by the answer-valued commutativity route.  The
degree-zero branch and scalar absorption have been discharged.
The predecessor induction argument is supplied by the strong-induction proof
of `MainInductionStep.answerMainInduction`.  The checked reduction
`MainInductionStep.answerMainInductionSuccessorNext_ofRecursiveHypothesisAndAnswerPasting`
reduces the successor branch to the answer-valued pasting theorem
`MainInductionStep.answerLdPastingInInductionSectionOfSmallError`, which is now
standard-axiom clean.
The transitive audit also records the exact downstream Section 6 and Section 3
handoff: `mainInductionSuccessor`, `mainInduction`,
`strategySymmetrization_mainInduction`, and
`MainFormalRoleInductionWitness.ofMainInduction` are standard-axiom clean.

The answer-carrier reductions
`MainInductionStep.mainInductionSuccessorNext_ofAnswerCarrier` and
`MainInductionStep.mainInductionSuccessorNext_ofAnswerCarrierFromSuccessorBound`
are standard-axiom clean.  They are not paper theorems; they are internal
successor reductions from the predecessor answer-valued induction hypothesis.
They remove the answer-valued slice-transport input from the active successor
route: the needed self-improvement data are constructed directly from
`AnswerSelfImprovementData.ofAnswerCarrier`, and the successor-bound form derives
the predecessor large-`k` side condition from the successor large-`k` hypothesis.
The answer-valued recursive slice restriction
`MainInductionStep.xRestrictedAnswerSymStratOfAnswer` and its
restricted-probability theorem
`MainInductionStep.answerSuccessorRestrictedProbabilities` are also
standard-axiom clean; they are constructions toward the simultaneous
answer-valued induction argument, not added hypotheses of the paper theorem.
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
`Producer`, `Statement`, `Slackness`, or `Dominance` are all covered by explicit
assertions in this file.  These names are not by themselves proof defects: some
are direct encodings of paper hypotheses, some are construction theorems, and
some are internal proof frontiers.  The audit records whether each checked
declaration uses only the standard Lean axioms, has exactly the expected Section
6 `sorryAx` dependency where historically relevant, or does not itself import
`sorryAx`.

This module is built explicitly in CI rather than imported from the umbrella
library modules, so the axiom audits stay out of normal downstream imports
while still acting as regression tests.
-/

open Lean Elab Command

private def expectedStandardAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound].qsort Name.lt

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

private def resolveDeclIdent (id : TSyntax `ident) : CommandElabM Name := do
  liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo id

elab "assert_standard_axioms " id:ident : command => do
  assertUsesOnlyStandardAxioms (← resolveDeclIdent id)

elab "assert_no_sorry_axiom " id:ident : command => do
  assertDoesNotUseSorryAxiom (← resolveDeclIdent id)

elab "assert_orthonormalization_axioms " id:ident : command => do
  assertUsesExactlyAxioms (← resolveDeclIdent id) expectedOrthonormalizationAxioms

elab "assert_self_improvement_axioms " id:ident : command => do
  assertUsesExactlyAxioms (← resolveDeclIdent id) expectedSelfImprovementAxioms

elab "assert_induction_self_improvement_axioms " id:ident : command => do
  assertUsesExactlyAxioms (← resolveDeclIdent id) expectedInductionSelfImprovementAxioms

elab "assert_ld_pasting_axioms " id:ident : command => do
  assertUsesExactlyAxioms (← resolveDeclIdent id) expectedLdPastingAxioms

elab "assert_ordered_laplacian_gap_axioms " id:ident : command => do
  assertUsesExactlyAxioms (← resolveDeclIdent id) expectedOrderedLaplacianGapAxioms

elab "assert_self_improvement_helper_axioms " id:ident : command => do
  assertUsesExactlyAxioms (← resolveDeclIdent id) expectedSelfImprovementHelperAxioms

elab "assert_sdp_slackness_axioms " id:ident : command => do
  assertUsesExactlyAxioms (← resolveDeclIdent id) expectedSdpSlacknessAxioms

assert_standard_axioms MIPStarRE.LDT.Test.razSafra
assert_no_sorry_axiom MIPStarRE.LDT.Test.RazSafraSoundnessStatement
assert_standard_axioms MIPStarRE.LDT.Test.PolishchukSpielmanClassicalSoundnessStatement
assert_standard_axioms MIPStarRE.LDT.Test.classicalTestSoundness
assert_no_sorry_axiom
  MIPStarRE.LDT.MakingMeasurementsProjective.NaimarkTensorProductCorrelationStatement
assert_no_sorry_axiom MIPStarRE.LDT.MakingMeasurementsProjective.NaimarkStatement
assert_standard_axioms MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimark
assert_standard_axioms MIPStarRE.LDT.MakingMeasurementsProjective.questionwiseNaimark
assert_standard_axioms
  MIPStarRE.LDT.MakingMeasurementsProjective.OneMeasNaimarkData.twoSidedCorrelationPreservation
assert_standard_axioms
  MIPStarRE.LDT.MakingMeasurementsProjective.naimarkTensorProductCorrelation
assert_standard_axioms
  MIPStarRE.LDT.MainInductionStep.mainInduction_sourceStatement
assert_standard_axioms
  MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_sourceMainInduction
assert_standard_axioms
  MIPStarRE.LDT.ProjStrat.sourceRoleRegisterPointConsistency_ofSymConsistency
assert_standard_axioms
  MIPStarRE.LDT.ProjStrat.pointAgreementFailureProbability_le_three_mul
assert_standard_axioms
  MIPStarRE.LDT.Preliminaries.simeqToApprox_heterogeneous
assert_standard_axioms
  MIPStarRE.LDT.Preliminaries.approxToSimeq_heterogeneous
assert_standard_axioms
  MIPStarRE.LDT.Preliminaries.triangleSub_right_heterogeneous
assert_standard_axioms
  MIPStarRE.LDT.Preliminaries.triangleSub_heterogeneous
assert_standard_axioms
  MIPStarRE.LDT.Preliminaries.simeqTriangleInequality_heterogeneous
assert_standard_axioms
  MIPStarRE.LDT.Preliminaries.polynomialCollisionMass_le_mdq
assert_standard_axioms
  MIPStarRE.LDT.Test.mainFormalStep5_selfConsistency_ofExpansionBound
assert_standard_axioms
  MIPStarRE.LDT.ProjStrat.sourceRoleRegisterFullPolynomialSelfConsistency_ofPointConsistency
assert_standard_axioms
  MIPStarRE.LDT.ProjStrat.sourceRoleRegisterLeftProjectiveSubmeasurement_ofFullConsistency
assert_standard_axioms
  MIPStarRE.LDT.ProjStrat.sourceRoleRegisterRightProjectiveSubmeasurement_ofFullConsistency
assert_standard_axioms
  MIPStarRE.LDT.ProjStrat.completedProjectiveMeasurements_ofTwoSidedSubmeasurements
assert_standard_axioms
  MIPStarRE.LDT.ProjStrat.completedProjectiveMeasurementsAndLine169_ofTwoSidedSubmeasurements
assert_standard_axioms
  MIPStarRE.LDT.ProjStrat.completedProjectiveConsistency_ofFullConsistency
assert_standard_axioms
  MIPStarRE.LDT.Test.consRel_constPolynomialEvaluation_heterogeneous
assert_standard_axioms
  MIPStarRE.LDT.Test.projectiveEvaluationConsistency_ofFullPolynomialConsistency_heterogeneous
assert_standard_axioms
  MIPStarRE.LDT.Test.mainFormalError_zero_k
assert_standard_axioms
  MIPStarRE.LDT.ProjStrat.sourceRoleRegisterUnsymmetrizedPointConsistency
assert_standard_axioms
  MIPStarRE.LDT.ProjStrat.sourceRoleRegisterCompletePolynomialSelfConsistency
assert_standard_axioms
  MIPStarRE.LDT.ProjStrat.sourceRoleRegisterLeftProjectiveSubmeasurement
assert_standard_axioms
  MIPStarRE.LDT.ProjStrat.sourceRoleRegisterTwoSidedProjectiveSubmeasurements
assert_standard_axioms
  MIPStarRE.LDT.ProjStrat.sourceRoleRegisterCompletedProjectiveMeasurements
assert_standard_axioms
  MIPStarRE.LDT.ProjStrat.sourceRoleRegisterFinalPointConsistency
assert_standard_axioms
  MIPStarRE.LDT.Test.mainFormal_sourceConclusion_ofRoleRegisterScalarBoundary
assert_standard_axioms MIPStarRE.LDT.Test.mainFormal_sourceSmallErrorObligation
assert_standard_axioms MIPStarRE.LDT.Test.mainFormal_sourceObligation
assert_standard_axioms MIPStarRE.LDT.Test.mainFormal_sourceStatement

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
assert_no_sorry_axiom MIPStarRE.LDT.answer_diagonalFailureProbability_nonneg
assert_no_sorry_axiom MIPStarRE.LDT.answer_eps_nonneg_of_isGood
assert_no_sorry_axiom MIPStarRE.LDT.answer_delta_nonneg_of_isGood
assert_no_sorry_axiom MIPStarRE.LDT.answer_gamma_nonneg_of_isGood
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.localDirectSumBlock_nonneg
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.roleBlock_mul
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.roleBlock_nonneg
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.localPairABBlock_nonneg
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.localPairBABlock_nonneg
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.heterogeneousSwapDensity_nonneg
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.heterogeneousSwapDensity_mul
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.rolePairDirectSumCond_nonneg
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.rolePairDirectSumCond_mul_same
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.rolePairDirectSumCond_AB_mul_BA
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.rolePairDirectSumCond_BA_mul_AB
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.roleRegisterSymmState
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.roleRegisterSymmState_density_fixed
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.roleRegisterSymmState_permInvState
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.roleRegisterSymmState_isNormalized
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.ev_roleRegisterSymmState_rolePair_AB_localPairABBlock
assert_no_sorry_axiom
  MIPStarRE.LDT.ProjStrat.ev_roleRegisterSymmState_rolePair_BA_localPairBABlock_swap
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.ev_roleRegisterSymmState_rolePairDirectSumCond_AA
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.ev_roleRegisterSymmState_rolePairDirectSumCond_BB
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.roleRegisterProjMeas
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.roleRegisterPointMeasurement
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.roleRegisterAxisParallelMeasurement
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.roleRegisterDiagonalMeasurement
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.roleRegisterAxisParallelTransportInvariant
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.roleRegisterDiagonalTransportInvariant
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy
assert_no_sorry_axiom
  MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_selfConsistency_eq_pointAgreement
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_axisParallel_eq_roleAverage
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_diagonal_eq_roleAverage
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.axisParallelRoleAverage_nonneg
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.pointAgreementFailureProbability_nonneg
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.diagonalRoleAverage_nonneg
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_is_good_three_mul
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.extractRoleRegisterAliceBlock_nonneg
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.extractRoleRegisterBobBlock_nonneg
assert_no_sorry_axiom MIPStarRE.LDT.SubMeas.extractRoleRegisterAlice
assert_no_sorry_axiom MIPStarRE.LDT.SubMeas.extractRoleRegisterBob
assert_no_sorry_axiom MIPStarRE.LDT.Measurement.extractRoleRegisterAlice
assert_no_sorry_axiom MIPStarRE.LDT.Measurement.extractRoleRegisterBob
assert_no_sorry_axiom
  MIPStarRE.LDT.ProjStrat.qBipartiteMatchMass_roleRegisterProjMeas_arbitrary_eq_average
assert_no_sorry_axiom
  MIPStarRE.LDT.ProjStrat.qBipartiteConsDefect_roleRegisterProjMeas_arbitrary_eq_average
assert_no_sorry_axiom
  MIPStarRE.LDT.ProjStrat.qBipartiteConsDefect_extractRoleRegisterBob_le_two_symm
assert_no_sorry_axiom
  MIPStarRE.LDT.ProjStrat.qBipartiteConsDefect_extractRoleRegisterAlice_le_two_symm
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.roleRegisterProjMeas_extractAlice
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.roleRegisterProjMeas_extractBob
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_point_extractAlice
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_point_extractBob
assert_no_sorry_axiom
  MIPStarRE.LDT.ProjStrat.polynomialEvaluationFamily_extractRoleRegisterAlice
assert_no_sorry_axiom MIPStarRE.LDT.ProjStrat.polynomialEvaluationFamily_extractRoleRegisterBob
assert_no_sorry_axiom
  MIPStarRE.LDT.ProjStrat.polynomialEvaluationFamily_measurement_extractRoleRegisterAlice
assert_no_sorry_axiom
  MIPStarRE.LDT.ProjStrat.polynomialEvaluationFamily_measurement_extractRoleRegisterBob
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
  MIPStarRE.LDT.MakingMeasurementsProjective.projectiveNonMeasurement_of_almostProjMeasStatement
assert_no_sorry_axiom
  MIPStarRE.LDT.MakingMeasurementsProjective.projectiveNonMeasurement_of_almostProjMeasStatement_full
assert_no_sorry_axiom
  MIPStarRE.LDT.MakingMeasurementsProjective.projectiveNonMeasurement_of_sourceAlmostProjective_full
assert_no_sorry_axiom
  MIPStarRE.LDT.MakingMeasurementsProjective.spectralTruncationStatement_of_projectiveNonMeasurement
assert_no_sorry_axiom
  MIPStarRE.LDT.MakingMeasurementsProjective.spectralTruncationStatement_of_sourceAlmostProjective
assert_standard_axioms
  MIPStarRE.LDT.MakingMeasurementsProjective.projectiveLowRankSum_of_spectralTruncationStatement
assert_orthonormalization_axioms
  MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalization
assert_no_sorry_axiom MIPStarRE.LDT.SelfImprovement.AddInUFullStatement
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.addInUFullStatement_of_isGood
assert_standard_axioms MIPStarRE.LDT.Test.mainFormal
assert_standard_axioms MIPStarRE.LDT.Test.mainFormal_sourceConclusion_ofSameSpaceLargeK
assert_standard_axioms
  MIPStarRE.LDT.Test.MainFormalDiagonalCompletionWitness.nonempty_ofDiagonalConsistency
assert_standard_axioms
  MIPStarRE.LDT.Test.MainFormalDiagonalOrthonormalizationWitness.nonempty_ofDiagonalConsistency
assert_self_improvement_axioms MIPStarRE.LDT.SelfImprovement.selfImprovement
assert_standard_axioms MIPStarRE.LDT.GlobalVariance.globalVarianceOfPoints
assert_induction_self_improvement_axioms
  MIPStarRE.LDT.MainInductionStep.selfImprovementInInductionSection
assert_standard_axioms
  MIPStarRE.LDT.SelfImprovement.selfImprovement_of_axisParallel_selfConsistency
assert_standard_axioms
  MIPStarRE.LDT.MainInductionStep.selfImprovementInInductionSection_of_axisParallel_selfConsistency
assert_standard_axioms
  MIPStarRE.LDT.MainInductionStep.answerLdPastingInInductionSectionOfSmallError
assert_no_sorry_axiom
  MIPStarRE.LDT.CommutativityPoints.answerCommutativityPoints
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.answerComMainForCarrier_ofAnswerGood
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.answerLdPastingInInductionSectionDegreeZeroOfSmallError
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.answerLdPastingInInductionError_le_mainInductionError_of_smallError
assert_standard_axioms
  MIPStarRE.LDT.MainInductionStep.answerMainInductionSuccessorNext_ofRecursiveHypothesisAndAnswerPasting
assert_standard_axioms
  MIPStarRE.LDT.MainInductionStep.answerMainInduction
assert_standard_axioms
  MIPStarRE.LDT.MainInductionStep.mainInductionSuccessorNext_ofSmallErrorConstruction
assert_standard_axioms
  MIPStarRE.LDT.MainInductionStep.mainInductionSuccessorNext
assert_standard_axioms
  MIPStarRE.LDT.MainInductionStep.mainInductionSuccessor
assert_standard_axioms
  MIPStarRE.LDT.MainInductionStep.mainInductionSuccessorNext_ofAnswerCarrier
assert_standard_axioms
  MIPStarRE.LDT.MainInductionStep.mainInductionSuccessorNext_ofAnswerCarrierFromSuccessorBound
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
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.dummyDiagonalCovariantMeasurement
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.answerSelfImprovementCarrier
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
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.AnswerSuccessorRestrictedProbabilitiesStatement
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.answerSuccessor_weighted_axisParallel_bound
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.answerSuccessor_weighted_diagonal_bound
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.answerSuccessorRestrictedProbabilities
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.answerSuccessorRestrictedSliceConclusions
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.mainInductionBaseCase
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.answerMainInductionBaseCase
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.mainInductionOfOneLeError
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.answerMainInductionOfOneLeError
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.selfImprovementInInductionSectionConclusion_ofSelfImprovementConclusion
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.selfImprovementInInductionError_le_one_of_mainInductionError_lt_one
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.answer_eps_le_one_of_mainInductionError_lt_one
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.answer_delta_le_one_of_mainInductionError_lt_one
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.answer_gamma_le_one_of_mainInductionError_lt_one
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.answer_dq_le_q_of_mainInductionError_lt_one
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.answer_three_le_k_sq_mul_next_m_of_hsmall
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.answer_selfImprovementInInductionError_le_mainInductionNu
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.answer_selfImprovementInInductionError_le_one_of_mainInductionError_lt_one
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.average_answerSuccessorSliceSelfImprovementError_le
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.average_answerSuccessorSliceMainInductionNu_le
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.average_answerSuccessorSliceMainInductionError_le
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.answerSuccessorRecursiveSliceMeasurements_ofMainInductionHypothesis
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.answerSuccessorSelfImprovementOutputs_ofMainInductionHypothesis
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
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.AnswerSelfImprovementData.ofLegacy
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.AnswerSelfImprovementData.SliceStrategyTransport.averagedPoint_eq_of_pointMeasurement_eq
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.AnswerSelfImprovementData.SliceStrategyTransport.ofPointMeasurementEq
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.AnswerSelfImprovementData.SliceStrategyTransport.good_of_restrictedGood
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.AnswerSelfImprovementData.SliceStrategyTransport.ofMeasurementEq
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.restrictAnswerDiagonalAnswerMeasurement
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.xRestrictedAnswerSymStratOfAnswer
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.AnswerSelfImprovementData.ofSelfImprovementInInductionSection
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.AnswerSelfImprovementData.ofSliceStrategyTransport
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.AnswerSelfImprovementData.slice_outputs_ofAnswerCarrier
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.AnswerSelfImprovementData.ofAnswerCarrier
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.answer_family_pointConsistencyError_eq_avg
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.answer_family_consistency_of_slice_bounds
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.family_answerRestrictedPointConsistencyError_eq_avg
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.idxPolyFamily_averagedMass_eq_avg
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.idxPolyFamily_complete_of_slice_bounds
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.idxPolyFamily_stronglySelfConsistent_of_slice_bounds
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.idxPolyFamily_sliceBoundednessInput_of_slice_bounds
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.answerSuccessorAveragedFamilyFields_ofMainInductionHypothesis
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.answerLdPastingInInductionSectionOfComMainAndErrorBound
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.average_answerSliceSelfImprovementError_le
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.average_answerSliceError_le
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.AnswerSelfImprovementData.complete_of_slice_bounds
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.AnswerSelfImprovementData.consistentWithPoints_of_slice_bounds
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.AnswerSelfImprovementData.stronglySelfConsistent_of_slice_bounds
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.AnswerSelfImprovementData.sliceBoundednessInput_of_slice_bounds
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.mainInductionFromAnswerStageDataOfSmallErrorDirect
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.AveragedPastingData.invokeLdPasting
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.assembleAveragedPastingData
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.assembleAveragedPastingDataOfSmallError
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.ldPastingInInductionSection
assert_no_sorry_axiom MIPStarRE.LDT.MainInductionStep.mainInductionFromStageData
assert_no_sorry_axiom
  MIPStarRE.LDT.MainInductionStep.mainInductionFromAnswerStageDataOfSmallError
assert_standard_axioms MIPStarRE.LDT.MainInductionStep.mainInduction
assert_standard_axioms
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
assert_standard_axioms
  MIPStarRE.LDT.Test.MainFormalRoleInductionWitness.ofMainInduction
assert_standard_axioms
  MIPStarRE.LDT.Test.MainFormalProjectiveCompletionTransportWitness.nonempty_ofRoleWitness
assert_standard_axioms
  MIPStarRE.LDT.Test.mainFormal_ofProjectiveCompletionTransportWitness
assert_standard_axioms MIPStarRE.LDT.Pasting.ldPastingDegreeZeroBranch
assert_no_sorry_axiom MIPStarRE.LDT.Pasting.pointVerticalLineSdd_of_axis_self
assert_no_sorry_axiom MIPStarRE.LDT.Pasting.ldGbcon_of_axis_self
assert_no_sorry_axiom MIPStarRE.LDT.Pasting.ldGbcon_liftedVerticalLine_of_axis_self
assert_no_sorry_axiom
  MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_endpoint_ldGbcon_of_axis_self
assert_no_sorry_axiom
  MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_endpoint_ldGbcon_lift_of_axis_self
assert_no_sorry_axiom
  MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_core_of_axis_self
assert_no_sorry_axiom
  MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_ofGHatFacts_of_axis_self
assert_no_sorry_axiom
  MIPStarRE.LDT.Pasting.hBConsistency_ofLinePointBounds_of_axis_self
assert_no_sorry_axiom
  MIPStarRE.LDT.Pasting.hAConsistency_submeas_from_lineConsistency_of_axis_self
assert_no_sorry_axiom
  MIPStarRE.LDT.Pasting.hAConsistency_submeas_ofLinePointBounds_of_axis_self
assert_no_sorry_axiom
  MIPStarRE.LDT.Pasting.hAConsistency_submeas_ofGHatFacts_of_axis_self
assert_no_sorry_axiom
  MIPStarRE.LDT.Pasting.gHatFacts_ofComMainAndSelfConsistency
assert_no_sorry_axiom
  MIPStarRE.LDT.Pasting.hAConsistency_submeas_ofComMain_of_axis_self
assert_no_sorry_axiom MIPStarRE.LDT.Pasting.overAllOutcomes_ofLinePointBounds
assert_no_sorry_axiom MIPStarRE.LDT.Pasting.overAllOutcomes_ofGHatFacts_of_axis_self
assert_no_sorry_axiom MIPStarRE.LDT.Pasting.overAllOutcomes_ofComMain_of_axis_self
assert_no_sorry_axiom MIPStarRE.LDT.Pasting.fromHToG_ofGHatFacts
assert_no_sorry_axiom MIPStarRE.LDT.Pasting.fromHToG_ofComMain
assert_no_sorry_axiom
  MIPStarRE.LDT.Pasting.ldPastingNCompleteness_of_overAllOutcomes_fromHToG_tail
assert_no_sorry_axiom
  MIPStarRE.LDT.Pasting.ldPastingNCompleteness_ofComMain_of_axis_self
assert_no_sorry_axiom MIPStarRE.LDT.Pasting.degreeZeroPastedPointConsistency_of_axis_self
assert_standard_axioms MIPStarRE.LDT.Pasting.ldPastingNontrivialPublicBranch
assert_ld_pasting_axioms MIPStarRE.LDT.Pasting.ldPasting
assert_standard_axioms MIPStarRE.LDT.CommutativityPoints.commutativityPoints
assert_standard_axioms MIPStarRE.LDT.CommutativityPoints.answerCommutativityPoints
assert_standard_axioms MIPStarRE.LDT.Commutativity.commDataProcessedG_of_commutativityPoints
assert_standard_axioms MIPStarRE.LDT.Commutativity.commDataProcessedG
assert_standard_axioms MIPStarRE.LDT.Commutativity.comMain_of_commutativityPoints
assert_standard_axioms MIPStarRE.LDT.Commutativity.comMain
assert_ordered_laplacian_gap_axioms
  MIPStarRE.LDT.ExpansionHypercubeGraph.laplacianSpectralGapOrdered
assert_standard_axioms
  MIPStarRE.LDT.SelfImprovement.helper_strong_self_consistency_of_helper_conclusion
assert_self_improvement_helper_axioms MIPStarRE.LDT.SelfImprovement.selfImprovementHelper
assert_no_sorry_axiom MIPStarRE.LDT.SelfImprovement.SdpOptimalPairWithSlackness
assert_no_sorry_axiom MIPStarRE.LDT.SelfImprovement.SdpOptimalPairWithSlackness.primalMeasurement
assert_no_sorry_axiom MIPStarRE.LDT.SelfImprovement.SdpStatement
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
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.matrixSdpPrimalTotalEqOne_of_canonicalComplementarySlackness_of_one_le
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.matrixSdpPrimalTotalEqOne_extracted_of_canonicalComplementarySlackness_of_one_le
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.matrixSdpStatementWithSlacknessAndDominance_of_canonicalComplementarySlackness
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.matrixSdpStatementWithSlacknessAndDominance_of_canonicalFeasibleComplementarySlackness
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.MatrixSdpStatementWithSlacknessAndDominance.exists_measurement_witness
assert_sdp_slackness_axioms MIPStarRE.LDT.SelfImprovement.sdp_statement_with_slackness
assert_standard_axioms MIPStarRE.LDT.SelfImprovement.sdp_slackness_measurement

assert_no_sorry_axiom
  MIPStarRE.LDT.MakingMeasurementsProjective.leftLiftedProjectivizationRepair
assert_no_sorry_axiom
  MIPStarRE.LDT.MakingMeasurementsProjective.leftLiftedProjectivizationRepairProducer
assert_no_sorry_axiom
  MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationMeasurement_of_consistency_from_projectivizationRepair
assert_no_sorry_axiom
  MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationMeasurement_of_consistency_from_projectivizationRepair_heterogeneous
assert_no_sorry_axiom
  MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationMeasurement_right_of_consistency_from_projectivizationRepair_heterogeneous
assert_no_sorry_axiom
  MIPStarRE.LDT.MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement.completedCloseness_liftRight
assert_no_sorry_axiom
  MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationSelfConsistencyHandoff.ofOrthonormalizeAndCompleteStatements
assert_no_sorry_axiom
  MIPStarRE.LDT.MakingMeasurementsProjective.projectiveLowRankSum_of_spectralTruncationStatement
assert_no_sorry_axiom
  MIPStarRE.LDT.MakingMeasurementsProjective.SpectralTruncationStatement.toRoundingToProjectorsWitness
assert_no_sorry_axiom
  MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationLine169Repair.leftConsistency_of_completion_and_sdd
assert_no_sorry_axiom
  MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationLine169Repair.rightConsistency_of_completion_and_sdd
assert_no_sorry_axiom
  MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationLine169Repair.leftConsistency_with_orthonormalization_loss
assert_no_sorry_axiom
  MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationLine169Repair.rightConsistency_with_orthonormalization_loss
assert_no_sorry_axiom
  MIPStarRE.LDT.IdxPolyFamily.SliceBoundednessInput.storedBoundedResidualBound
assert_no_sorry_axiom
  MIPStarRE.LDT.IdxPolyFamily.SliceBoundednessInput.averagedPoint_le_witness
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.HelperStrongSelfConsistencyObligations
assert_no_sorry_axiom MIPStarRE.LDT.Test.CascadeHypotheses
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.matrixSdpOptimalWitnessWithDominance_of_canonicalComplementarySlackness
assert_no_sorry_axiom
  MIPStarRE.LDT.SelfImprovement.matrixSdpOptimalWitnessWithDominance_of_canonicalFeasibleComplementarySlackness
