import Lean
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization
import MIPStarRE.LDT.Test.MainTheorem

/-!
# Axiom audits for classical low-individual-degree soundness

Regression checks for the issue-#408 replacement of the former ambient
Polishchuk--Spielman axiom by the explicit hypothesis
`PolishchukSpielmanClassicalSoundnessStatement`.

The audits for open analytic obligations record the current residual dependency
on `sorryAx`.  For `MakingMeasurementsProjective.orthonormalization`, this
comes from the locality-preserving repair obligation in
`MakingMeasurementsProjective/Producers.lean`.  For `Test.mainFormal`, this
comes from the base-case repaired-input construction and the successor-case
assembly.  When these obligations are discharged, the allowed axiom set below
should be reduced to the standard Lean axioms.

This module is built explicitly in CI rather than imported from the umbrella
library modules, so the axiom audits stay out of normal downstream imports
while still acting as regression tests.
-/

open Lean Elab Command

private def expectedStandardAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound].qsort Name.lt

private def expectedOpenObligationAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound, ``sorryAx].qsort Name.lt

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

elab "assert_orthonormalization_axioms " id:ident : command => do
  assertUsesExactlyAxioms id.getId expectedOpenObligationAxioms

elab "assert_open_obligation_axioms " id:ident : command => do
  assertUsesExactlyAxioms id.getId expectedOpenObligationAxioms

assert_standard_axioms MIPStarRE.LDT.Test.razSafra
assert_standard_axioms MIPStarRE.LDT.Test.PolishchukSpielmanClassicalSoundnessStatement
assert_standard_axioms MIPStarRE.LDT.Test.classicalTestSoundness
assert_orthonormalization_axioms MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalization
assert_open_obligation_axioms MIPStarRE.LDT.Test.mainFormal
