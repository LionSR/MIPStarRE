import MIPStarRE.LDT.Test.MainTheorem.OrdinaryRestriction.PublicWrapper

/-!
# Ordinary restricted-slice recursion

Compatibility module for the ordinary `x`-restricted successor route in the
`mainFormal` assembly.  This module re-exports declarations from three
sub-leaves:

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

* `OrdinaryRestriction.PublicWrapper` — a compatibility import.  Its former
  conditional handoff has been removed because it took non-paper successor data
  as hypotheses; the remaining Section 6 proof obligation is now the
  `mainInduction` theorem with the paper statement.

## References

* Paper: `references/ldt-paper/inductive_step.tex`,
  `x`-restricted strategy definition and
  `\Cref{lem:restricted-probabilities}` (lines 363–412).
* Blueprint: `blueprint/src/chapter/ch10_induction.tex`,
  `\label{def:restricted-strategy}`,
  `\label{lem:restricted-probabilities}`, and
  `\label{def:main-formal-successor-boundary}`.
-/
