import MIPStarRE.LDT.Test.MainTheorem.Simplified.Statements

/-!
# Saturated-error branch of simplified soundness

When the final error is at least one, complete projective polynomial
measurements supported on a fixed polynomial satisfy all three conclusions.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-formal`,
  first paragraph.
-/

namespace MIPStarRE.LDT.Test

/-- The final theorem's three conclusions in the saturated-error branch. -/
theorem simplifiedMainFormal_saturated
    (params : Parameters) [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hlarge : 1 ≤ simplifiedMainFormalError params eps) :
    SimplifiedMainFormalConclusion params strategy eps := by
  classical
  haveI : Inhabited (Polynomial params) :=
    ⟨⟨0, by intro i; simp [MvPolynomial.degreeOf_zero]⟩⟩
  let trivialA : ProjMeas (Polynomial params) ιA :=
    ProjMeas.trivialDistinguishedOutcome (default : Polynomial params)
  let trivialB : ProjMeas (Polynomial params) ιB :=
    ProjMeas.trivialDistinguishedOutcome (default : Polynomial params)
  refine ⟨trivialA, trivialB, ?_, ?_, ?_⟩
  all_goals exact ⟨le_trans
    (bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized _ _) hlarge⟩

end MIPStarRE.LDT.Test
