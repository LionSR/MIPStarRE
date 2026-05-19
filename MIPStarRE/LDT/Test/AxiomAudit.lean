import Lean
import MIPStarRE.LDT.ExpansionHypercubeGraph.MatrixRealization
import MIPStarRE.LDT.GlobalVariance.Theorems.MainTheorems
import MIPStarRE.LDT.MainInductionStep.Theorems.MainTheorems
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization
import MIPStarRE.LDT.Pasting.Bernoulli.Final
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.HelperCompleteness.Bracketed
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.SelfImprovementTop.Core
import MIPStarRE.LDT.Test.MainTheorem

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

The audit for `SelfImprovement.selfImprovement` requires the standard Lean axioms
only: the issue-#1230 SDP slackness dependency has been discharged by the
canonical finite-dimensional SDP strong-duality argument.

The audit for `Test.mainFormal` records the current tracked proof gap
transitively: the paper-facing statement has no connection, residual, repair,
data, or obligation hypotheses, and its proof is assembled from named
construction targets.  After the projective-completion refactor, the active
`mainFormal` cascade routes through `MainInductionStep.mainInduction` via
`strategySymmetrization_mainInduction`.  The base case is proved by
`mainInductionBaseCase`, so the only remaining transitive `sorryAx` dependency
on the `mainFormal` path is the successor branch `mainInductionSuccessor`,
tracked by issue #1507 (with #1458 as the umbrella tracking issue).

The audit for `GlobalVariance.globalVarianceOfPoints` now requires the standard
Lean axioms only: the issue-#1456 six-step local transport estimate is supplied
by `GlobalVariance.localVarianceTransportChainBound`, so the paper-facing theorem
no longer carries a `sorryAx` dependency.

The audit for `MainInductionStep.selfImprovementInInductionSection` records
standard Lean axioms only: the measurement-valued realization of
`thm:self-improvement-in-induction-section` no longer inherits the issue-#1230
SDP slackness obligation.

The audit for `MainInductionStep.mainInduction` records the current proof
obligation for `thm:main-induction`: the theorem statement matches the paper
statement, and the remaining work is to derive the internal successor-stage
inputs from the paper hypotheses.  This is tracked by issue #1507.

The audit for `Pasting.ldPasting` now requires the standard Lean axioms only:
the unrestricted paper-facing theorem no longer depends on a dedicated
degree-zero `sorryAx`, because issue #1622 has been discharged by the direct
degree-zero construction in `Pasting/Bernoulli/Final.lean`.

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
finite-dimensional semidefinite-programming argument.

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
`mainFormal` construction gap, currently localized to `mainInductionSuccessor`
via `MainInductionStep.mainInduction` (issue #1507; umbrella #1458). -/
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

elab "assert_standard_axioms " id:ident : command => do
  assertUsesOnlyStandardAxioms id.getId

elab "assert_main_formal_axioms " id:ident : command => do
  assertUsesExactlyAxioms id.getId expectedMainFormalAxioms

elab "assert_orthonormalization_axioms " id:ident : command => do
  assertUsesExactlyAxioms id.getId expectedOrthonormalizationAxioms

elab "assert_self_improvement_axioms " id:ident : command => do
  assertUsesExactlyAxioms id.getId expectedSelfImprovementAxioms

elab "assert_induction_self_improvement_axioms " id:ident : command => do
  assertUsesExactlyAxioms id.getId expectedInductionSelfImprovementAxioms

elab "assert_main_induction_axioms " id:ident : command => do
  assertUsesExactlyAxioms id.getId expectedMainInductionAxioms

elab "assert_ld_pasting_axioms " id:ident : command => do
  assertUsesExactlyAxioms id.getId expectedLdPastingAxioms

elab "assert_ordered_laplacian_gap_axioms " id:ident : command => do
  assertUsesExactlyAxioms id.getId expectedOrderedLaplacianGapAxioms

elab "assert_self_improvement_helper_axioms " id:ident : command => do
  assertUsesExactlyAxioms id.getId expectedSelfImprovementHelperAxioms

elab "assert_sdp_slackness_axioms " id:ident : command => do
  assertUsesExactlyAxioms id.getId expectedSdpSlacknessAxioms

assert_standard_axioms MIPStarRE.LDT.Test.razSafra
assert_standard_axioms MIPStarRE.LDT.Test.PolishchukSpielmanClassicalSoundnessStatement
assert_standard_axioms MIPStarRE.LDT.Test.classicalTestSoundness
assert_standard_axioms
  MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationCompletionRoute
assert_orthonormalization_axioms
  MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalization
assert_main_formal_axioms MIPStarRE.LDT.Test.mainFormal
assert_self_improvement_axioms MIPStarRE.LDT.SelfImprovement.selfImprovement
assert_standard_axioms MIPStarRE.LDT.GlobalVariance.globalVarianceOfPoints
assert_induction_self_improvement_axioms
  MIPStarRE.LDT.MainInductionStep.selfImprovementInInductionSection
assert_main_induction_axioms MIPStarRE.LDT.MainInductionStep.mainInduction
assert_ld_pasting_axioms MIPStarRE.LDT.Pasting.ldPasting
assert_ordered_laplacian_gap_axioms
  MIPStarRE.LDT.ExpansionHypercubeGraph.laplacianSpectralGapOrdered
assert_standard_axioms
  MIPStarRE.LDT.SelfImprovement.helper_strong_self_consistency_of_helper_conclusion
assert_self_improvement_helper_axioms MIPStarRE.LDT.SelfImprovement.selfImprovementHelper
assert_sdp_slackness_axioms MIPStarRE.LDT.SelfImprovement.sdp_statement_with_slackness
