import MIPStarRE.LDT.Test.MainTheorem.OrdinaryRestriction.Basic

/-!
# Ordinary restricted-slice recursion

Compatibility module for the ordinary `x`-restricted successor route in the
`mainFormal` construction.  It re-exports the successor weighted bounds,
the restricted-probability package, and the recursive-slice target
(`MainFormalSuccessorRecursiveSlices`).

The former slice-data witness package, which supplied concrete restricted
same-space strategies as an additional input, has been removed.  Constructing
those witnesses from the paper hypotheses is part of the successor proof gap in
`MainInductionStep.mainInduction` and the final proof gap in `mainFormal`, not a
separate hypothesis of a source-facing theorem.

## References

* Paper: `references/ldt-paper/inductive_step.tex`,
  `x`-restricted strategy definition and
  `\Cref{lem:restricted-probabilities}` (lines 363–412).
* Blueprint: `blueprint/src/chapter/ch10_induction.tex`,
  `\label{def:restricted-strategy}`,
  `\label{lem:restricted-probabilities}`, and
  `\label{def:main-formal-successor-boundary}`.
-/
