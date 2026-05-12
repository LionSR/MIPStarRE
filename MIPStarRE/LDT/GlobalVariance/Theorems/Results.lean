import MIPStarRE.LDT.GlobalVariance.Theorems.AlgebraicIdentity
import MIPStarRE.LDT.GlobalVariance.Theorems.CollisionExpansion
import MIPStarRE.LDT.GlobalVariance.Theorems.SelfConsistencyTransport
import MIPStarRE.LDT.GlobalVariance.Theorems.SelfConsistencyTransportSum
import MIPStarRE.LDT.GlobalVariance.Theorems.TransportChain
import MIPStarRE.LDT.GlobalVariance.Theorems.MainTheorems
import MIPStarRE.LDT.GlobalVariance.Theorems.PolynomialSumBounds

/-!
# GlobalVariance Theorems — Results imports

This module re-exports all GlobalVariance theorem results from the
sub-modules:

- `AlgebraicIdentity`: matrix-transfer bounds, algebraic norm/variance reductions,
  generalize-B projective identities
- `CollisionExpansion`: generalize-B theorem wrappers, finite reparametrization,
  Schwartz-Zippel collision expansion
- `SelfConsistencyTransport`: good-strategy self-consistency transport (`2δ` and
  `2ε` approximation steps)
- `SelfConsistencyTransportSum`: polynomial-sum (cardinality-free) `2ε`
  axis-parallel consistency endpoints, the sum-form analogues of the per-`g`
  transport steps in `SelfConsistencyTransport`
- `TransportChain`: six-step local-variance transport assembly on the line-pair
  presentation
- `MainTheorems`: top-level `lem:local-variance-of-points`,
  `lem:global-variance-of-points`, and matrix-level counterparts
- `PolynomialSumBounds`: cardinality-free polynomial-sum bounds for the
  Schwartz-Zippel transport step underlying `eq:equivalent-local-variance`

Backward-compatibility: all theorems previously in `Results.lean` remain
available through this re-export import.
-/
