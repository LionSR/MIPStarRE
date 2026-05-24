import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer.RankReduction.LowRank

/-!
# Section 5 — Q/X/XHat/P rank reduction

Compatibility module for the rank-reduction layer of the paper's
`Q/X/XHat/P` construction.

The implementation is split into:

- `QXPLayer.Core`, containing the scalar truncation estimates, the
  rounding-to-projectors witness, and the core `Q/X/Xhat/P` data structures;
- `RankReduction.Sigma`, containing the sigma-space projective measurement and
  the canonical sigma-space `Q/X/Xhat/P` construction;
- `RankReduction.LowRank`, containing the auxiliary-space producers and the
  low-rank truncation branch of `lem:projective-low-rank-sum`.
-/
