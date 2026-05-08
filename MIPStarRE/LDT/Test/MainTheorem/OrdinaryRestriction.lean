import MIPStarRE.LDT.Test.MainTheorem.OrdinaryRestriction.PublicWrapper

/-!
# Ordinary restricted-slice recursion

Compatibility barrel for the ordinary `x`-restricted successor route in the
`mainFormal` assembly.  This module re-exports declarations from three
sub-leaves:

* `OrdinaryRestriction.Basic` — successor weighted bounds
  (`MainFormalSuccessorAxisWeightedBound`, `MainFormalSuccessorDiagonalWeightedBound`),
  recursive slice producers (`MainFormalSuccessorRecursiveSlices`),
  self-improvement bridge inputs (`MainFormalSuccessorSelfImprovementBridgeInputs`),
  and the successor boundary structure (`MainFormalSuccessorBoundary`).

* `OrdinaryRestriction.SliceData` — per-slice recursive data
  (`MainFormalSuccessorRecursiveSliceData`) and the probabilistic bounds on
  the restricted success probabilities from `\Cref{lem:restricted-probabilities}`
  (`mainFormalSuccessorRestrictedPointAgreement_le_ofSliceData`,
  `mainFormalSuccessorRestrictedAxisParallel_le_ofSliceData`,
  `mainFormalSuccessorRestrictedDiagonal_le_ofSliceData`).

* `OrdinaryRestriction.PublicWrapper` — the public theorem
  `mainFormalSuccessorMainInductionPublicWrapper` that converts a bundle of
  predecessor Section 6 inputs into a role-register measurement.

## References

* Paper: `references/ldt-paper/inductive_step.tex`,
  `\Cref{def:restricted-strategy}` and
  `\Cref{lem:restricted-probabilities}` (lines 68–75).
* Blueprint: `blueprint/src/chapter/ch10_induction.tex`,
  `\label{def:main-formal-successor-boundary}`.
-/
