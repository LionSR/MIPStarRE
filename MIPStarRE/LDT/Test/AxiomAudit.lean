import Lean
import MIPStarRE.LDT.Test.MainTheorem

/-!
# Axiom audits for classical low-individual-degree soundness

Regression checks for the issue-#408 replacement of the former ambient
Polishchuk--Spielman axiom by the explicit hypothesis
`PolishchukSpielmanClassicalSoundnessStatement`.

This module is built explicitly in CI rather than imported from the umbrella
library modules, so the axiom audits stay out of normal downstream imports
while still acting as regression tests.
-/

open Lean Elab Command

private def expectedStandardAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound].qsort Name.lt

private def assertUsesOnlyStandardAxioms (declName : Name) : CommandElabM Unit := do
  let axioms := (← Lean.collectAxioms declName).qsort Name.lt
  unless axioms == expectedStandardAxioms do
    throwError
      m!"'{declName}' depends on axioms {axioms.toList}, expected only " ++
        m!"{expectedStandardAxioms.toList}"

elab "assert_standard_axioms " id:ident : command => do
  assertUsesOnlyStandardAxioms id.getId

assert_standard_axioms MIPStarRE.LDT.Test.razSafra
assert_standard_axioms MIPStarRE.LDT.Test.PolishchukSpielmanClassicalSoundnessStatement
assert_standard_axioms MIPStarRE.LDT.Test.classicalTestSoundness
assert_standard_axioms MIPStarRE.LDT.Test.classicalTestSoundnessWithPlaceholderBound
