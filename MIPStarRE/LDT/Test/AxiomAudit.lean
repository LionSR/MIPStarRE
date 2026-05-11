import Lean
import MIPStarRE.LDT.GlobalVariance.Theorems.MainTheorems
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.SelfImprovementTop.Core
import MIPStarRE.LDT.Test.MainTheorem

/-!
# Axiom audits for classical low-individual-degree soundness

Regression checks for the issue-#408 replacement of the former ambient
Polishchuk--Spielman axiom by the explicit hypothesis
`PolishchukSpielmanClassicalSoundnessStatement`.

The audit for `MakingMeasurementsProjective.orthonormalization` now requires
the standard Lean axioms only: the locality-preserving repair obligation in
`MakingMeasurementsProjective/Producers.lean` has been discharged, so the
former `sorryAx` dependency is gone.

The audit for `SelfImprovement.selfImprovement` records the current open
derivation for `thm:self-improvement`: the statement corresponding to the
blueprint theorem is present, and the missing derivation from the incoming
consistency hypothesis is tracked by issue #1453.

The audits for the `Test.mainFormal` proof frontier record the current tracked
gaps from issue #1458: the successor projective-completion residual has not yet
been produced from the Section 6 induction data, and the repaired bridge used by
`mainFormal_ofRepairedBridge` has not yet been derived from the hypotheses of
the paper theorem.

The audit for `GlobalVariance.globalVarianceOfPoints` records the issue-#1456
proof obligation: the paper theorem has been restored without the former
conclusion-shaped supplied bounds, and the remaining local transport estimate
is visible as an unresolved proof obligation rather than as an extra
hypothesis.

This module is built explicitly in CI rather than imported from the umbrella
library modules, so the axiom audits stay out of normal downstream imports
while still acting as regression tests.
-/

open Lean Elab Command

private def expectedStandardAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound].qsort Name.lt

private def expectedStandardAxiomsWithSorry : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound, ``sorryAx].qsort Name.lt

/-- Standard kernel axioms plus `sorryAx`; tracks the issue #1458 gaps in the
paper-facing `mainFormal` proof frontier. -/
private def expectedTrackedSorryAxioms : Array Name :=
  expectedStandardAxiomsWithSorry

/-- Standard kernel axioms plus `sorryAx`; tracks the issue #1453 derivation
needed for `selfImprovement`. -/
private def expectedSelfImprovementAxioms : Array Name :=
  expectedStandardAxiomsWithSorry

/-- Standard kernel axioms plus `sorryAx`; tracks the issue #1456 derivation
needed for `globalVarianceOfPoints`. -/
private def expectedGlobalVarianceAxioms : Array Name :=
  expectedStandardAxiomsWithSorry

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

elab "assert_tracked_sorry_axioms " id:ident : command => do
  assertUsesExactlyAxioms id.getId expectedTrackedSorryAxioms

elab "assert_self_improvement_axioms " id:ident : command => do
  assertUsesExactlyAxioms id.getId expectedSelfImprovementAxioms

elab "assert_global_variance_axioms " id:ident : command => do
  assertUsesExactlyAxioms id.getId expectedGlobalVarianceAxioms

assert_standard_axioms MIPStarRE.LDT.Test.razSafra
assert_standard_axioms MIPStarRE.LDT.Test.PolishchukSpielmanClassicalSoundnessStatement
assert_standard_axioms MIPStarRE.LDT.Test.classicalTestSoundness
assert_standard_axioms MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalization
assert_tracked_sorry_axioms
  MIPStarRE.LDT.Test.mainFormalSuccessorProjectiveCompletionResidualProducer
assert_tracked_sorry_axioms MIPStarRE.LDT.Test.mainFormal
assert_self_improvement_axioms MIPStarRE.LDT.SelfImprovement.selfImprovement
assert_global_variance_axioms MIPStarRE.LDT.GlobalVariance.globalVarianceOfPoints
