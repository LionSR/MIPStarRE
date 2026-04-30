import MIPStarRE.LDT.GlobalVariance.Theorems.AlgebraicIdentity
import MIPStarRE.LDT.GlobalVariance.Theorems.CollisionExpansion
import MIPStarRE.LDT.GlobalVariance.Theorems.SelfConsistencyTransport
import MIPStarRE.LDT.GlobalVariance.Theorems.TransportChain
import MIPStarRE.LDT.GlobalVariance.Theorems.MainTheorems

/-!
# GlobalVariance Theorems — Results barrel

This module re-exports all GlobalVariance theorem results from the
sub-modules:

- `AlgebraicIdentity`: matrix-transfer bounds, algebraic norm/variance reductions,
  generalize-B projective identities
- `CollisionExpansion`: generalize-B theorem wrappers, finite reparametrization,
  Schwartz-Zippel collision expansion
- `SelfConsistencyTransport`: good-strategy self-consistency transport (`2δ` and
  `2ε` approximation steps)
- `TransportChain`: six-step local-variance transport assembly on the line-pair
  presentation
- `MainTheorems`: top-level `lem:local-variance-of-points`,
  `lem:global-variance-of-points`, and matrix-level counterparts

Backward-compatibility: all theorems previously in `Results.lean` remain
available through this barrel import.
-/
