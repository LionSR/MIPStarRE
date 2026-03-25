import MIPStarRE.LDT.GlobalVariance.Defs
import MIPStarRE.LDT.GlobalVariance.MatrixRealization
import MIPStarRE.LDT.GlobalVariance.Theorems

/-!
Matching scaffold for Section 8 of the low individual degree paper in
`references/ldt-paper/expansion.tex`.

This file records the named lemmas controlling the global variance of the points
measurements. The declarations now expose the conditioned operators
$A(g)^u = A^u_{g(u)}$, the weighted states $|ψ_g⟩ = (I ⊗ G_g^{1/2})|ψ⟩$, and the
variance-transfer quantities that the paper bounds.
-/
