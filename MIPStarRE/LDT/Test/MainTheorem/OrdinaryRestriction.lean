import MIPStarRE.LDT.Test.MainTheorem.OrdinaryRestriction.SliceData

/-!
# Ordinary restricted-slice recursion

Compatibility module for the ordinary `x`-restricted successor route in the
`mainFormal` construction.  This module re-exports declarations from two
submodules:

* `OrdinaryRestriction.Basic` — successor weighted bounds
  (`MainFormalSuccessorAxisWeightedBound`, `MainFormalSuccessorDiagonalWeightedBound`),
  the restricted-probability package, and recursive slice witnesses
  (`MainFormalSuccessorRecursiveSlices`).

* `OrdinaryRestriction.SliceData` — per-slice recursive data
  (`MainFormalSuccessorRecursiveSliceData`) and the probabilistic bounds on
  the restricted success probabilities from `\Cref{lem:restricted-probabilities}`
  (`mainFormalSuccessorRestrictedPointAgreement_le_ofSliceData`,
  `mainFormalSuccessorRestrictedAxisParallel_le_ofSliceData`,
  `mainFormalSuccessorRestrictedDiagonal_le_ofSliceData`).

## References

* Paper: `references/ldt-paper/inductive_step.tex`,
  `x`-restricted strategy definition and
  `\Cref{lem:restricted-probabilities}` (lines 363–412).
* Blueprint: `blueprint/src/chapter/ch10_induction.tex`,
  `\label{def:restricted-strategy}`,
  `\label{lem:restricted-probabilities}`, and
  `\label{def:main-formal-successor-boundary}`.
-/
