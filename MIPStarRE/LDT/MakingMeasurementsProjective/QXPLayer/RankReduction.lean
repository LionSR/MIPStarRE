import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer.RankReduction.LowRank

/-!
# Section 5 — Q/X/XHat/P rank reduction

Compatibility module for the rank-reduction layer of the paper's
`Q/X/XHat/P` construction.

The implementation is split into:

- `RankReduction.Sigma`, containing the almost-projective estimate, scalar
  truncation inequality, sigma-space projective measurement, and the canonical
  sigma-space `Q/X/Xhat/P` construction;
- `RankReduction.LowRank`, containing the auxiliary-space producers and the
  low-rank truncation branch of `lem:projective-low-rank-sum`.
-/
