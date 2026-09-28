import MIPStarRE.LDT.Test.MainTheorem.Simplified.SmallError
import MIPStarRE.LDT.Test.MainTheorem.Simplified.Saturated

/-!
# Simplified final low individual degree soundness theorem

The two-space projective strategy and all three consistency conclusions are
the same as in the original final theorem. The simplified proof removes the
public pasting-length parameter and replaces the exponential error envelope
with the displayed `1/64` power bound.

## References

- `blueprint/src/low_degree_simplified.tex`, `thm:main-formal`.
- `references/ldt-paper/test_definition.tex:180-202`, original theorem.
-/

namespace MIPStarRE.LDT.Test

/-- The final theorem of the simplified proof. The theorem retains the
original heterogeneous strategy and projective polynomial conclusions.

**Local fix:** The error parameter and absence of a public pasting length
follow `blueprint/src/low_degree_simplified.tex`, `thm:main-formal`, rather
than the original sampling parameter in
`references/ldt-paper/test_definition.tex:180-202`. -/
theorem mainFormalSimplified
    (params : Parameters) [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.lowIndividualDegreeFailureProbability ≤ eps) :
    SimplifiedMainFormalConclusion params strategy eps := by
  by_cases hlarge : 1 ≤ simplifiedMainFormalError params eps
  · exact simplifiedMainFormal_saturated params strategy eps hlarge
  · exact simplifiedMainFormal_smallError params strategy eps ⟨hpass⟩ hlarge

end MIPStarRE.LDT.Test
