import MIPStarRE.LDT.Section5MakingMeasurementsProjective.Defs
import MIPStarRE.LDT.Section5MakingMeasurementsProjective.Statements
import MIPStarRE.LDT.Section5MakingMeasurementsProjective.Theorems

/-!
Matching scaffold for Section 5 of the low individual degree paper in
`references/ldt-paper/orthonormalization.tex`.

The declarations here preserve the paper's theorem names and now expose more of
its intermediate theorem shape: Naimark data include explicit auxiliary factors,
and the orthogonalization helpers separate the almost-projective and rounding
steps. This second pass also adds a finite-dimensional matrix realization layer
based on `MIPStarRE/Quantum/FiniteMatrix.lean`, so the Section 5 statements are
not only tagged by placeholder operator names but also admit honest
`Matrix d d ℂ` witnesses for their probability and overlap formulas.

This file re-exports the split submodules:
- `Defs` — foundational definitions and helpers
- `Statements` — theorem statement structures
- `Theorems` — theorem and lemma declarations
-/
