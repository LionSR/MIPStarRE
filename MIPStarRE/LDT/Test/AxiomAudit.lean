import MIPStarRE.LDT.Test.MainTheorem

/-!
# Axiom audits for classical low-individual-degree soundness

Regression checks for the issue-#408 replacement of the former ambient
Polishchuk--Spielman axiom by the explicit hypothesis
`PolishchukSpielmanClassicalSoundnessStatement`.
-/

/-- info: 'MIPStarRE.LDT.Test.PolishchukSpielmanClassicalSoundnessStatement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MIPStarRE.LDT.Test.PolishchukSpielmanClassicalSoundnessStatement

/-- info: 'MIPStarRE.LDT.Test.classicalTestSoundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MIPStarRE.LDT.Test.classicalTestSoundness
