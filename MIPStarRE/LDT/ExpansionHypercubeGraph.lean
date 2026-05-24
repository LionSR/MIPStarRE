import MIPStarRE.LDT.ExpansionHypercubeGraph.Defs
import MIPStarRE.LDT.ExpansionHypercubeGraph.MatrixRealization
import MIPStarRE.LDT.ExpansionHypercubeGraph.Theorems

/-!
# LDT/ExpansionHypercubeGraph — imports

This module re-exports the ExpansionHypercubeGraph development:
- `Defs/Core` for the hypercube parameters, operators, and statement structures
- `Defs/Fourier` for the Fourier basis, additive-character identities, and
  `GlobalVarianceDecomposition`
- `MatrixRealization` for the concrete adjacency and Laplacian matrices
- `Theorems/Foundations` for foundation-level trace and decomposition lemmas
- `Theorems/Matrix` for the matrix-realization statements
- `Theorems/Results` for the public Chapter 5 theorems, including `eigenvectors`,
  `laplacianSpectralGap`, `globalRewrite`, and `localToGlobal`

## References

- paper `expansion.tex` (Chapter 5 / Section 7 of MIP*=RE)
- Blueprint: `blueprint/src/chapter/ch05_expansion.tex`
-/
