import MIPStarRE.LDT.Test.MainTheorem.OrdinaryRestriction.Basic

/-!
# Ordinary restricted-slice recursion

Compatibility module for the ordinary `x`-restricted successor route in the
`mainFormal` construction.  It re-exports the successor weighted bounds,
the restricted-probability package, and the recursive-slice target
(`MainFormalSuccessorRecursiveSlices`).

The former slice-data witness package, which supplied concrete restricted
same-space strategies as an additional input, has been removed.  In the active
successor route the corresponding restricted-slice data are constructed inside
`MainInductionStep.mainInduction`, not supplied as a separate hypothesis of a
source-facing theorem.

## References

* Paper: `references/ldt-paper/inductive_step.tex`,
  `x`-restricted strategy definition and
  `\Cref{lem:restricted-probabilities}` (lines 363–412).
* Blueprint: `blueprint/src/chapter/ch10_induction.tex`,
  `\label{def:restricted-strategy}`,
  `\label{lem:restricted-probabilities}`, and the unnumbered paragraph
  "Lean successor restricted-recursion targets for the Section 3 proof".
-/
