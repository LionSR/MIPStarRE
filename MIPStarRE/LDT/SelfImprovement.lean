import MIPStarRE.LDT.SelfImprovement.Defs
import MIPStarRE.LDT.SelfImprovement.MatrixRealization
import MIPStarRE.LDT.SelfImprovement.Theorems

/-!
Matching scaffold for Section 9 of the low individual degree paper in
`references/ldt-paper/self_improvement.tex`.

This file exposes the paper's SDP witnesses, the `add-in-u` transfer identity,
and the non-projective/projective self-improvement outputs through explicit named
constructions and error terms.

The content is split across submodules:
- `SelfImprovement.Defs`: core SDP/operator definitions and error terms
- `SelfImprovement.MatrixRealization`: finite-dimensional matrix realizations
- `SelfImprovement.Theorems`: lemma/theorem statement structures and stubs
-/
