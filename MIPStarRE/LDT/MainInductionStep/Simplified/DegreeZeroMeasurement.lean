import MIPStarRE.LDT.MainInductionStep.Simplified.DimensionOne
import MIPStarRE.LDT.ExpansionHypercubeGraph.Theorems.Results

/-!
# Averaged point measurement in degree zero

The degree-zero proof begins by assigning the average point effect
`E_v Aᵛ_a` to the constant polynomial with value `a`. This file
constructs the resulting complete measurement. Its consistency estimate
uses the hypercube local-to-global variance theorem.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-induction`,
  degree-zero case.
- `references/ldt-paper/inductive_step.tex:441-551`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- Average the point measurement over the hypercube and label each
outcome by its constant polynomial. Every polynomial outcome outside
that image has zero effect. -/
noncomputable def degreeZeroPointAveragedMeasurement
    (params : Parameters) [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    Measurement (Polynomial params) ι := by
  classical
  let 𝒟 := uniformDistribution (Point params)
  let S : SubMeas (Polynomial params) ι :=
    averageIdxSubMeas 𝒟
      (fun u => postprocess (strategy.pointMeasurement u).toSubMeas
        (Polynomial.const params))
      (uniformDistribution_weight_sum_le_one (Point params))
  refine ⟨S, ?_⟩
  change averageOperatorOverDistribution 𝒟
      (fun u => (strategy.pointMeasurement u).total) = 1
  have htotal : (fun u : Point params => (strategy.pointMeasurement u).total) =
      fun _ => (1 : MIPStarRE.Quantum.Op ι) := by
    funext u
    exact (strategy.pointMeasurement u).total_eq_one
  rw [htotal]
  exact averageOperatorOverDistribution_const_of_isProbability 𝒟
    (uniformDistribution_isProbability (Point params)) 1

end MIPStarRE.LDT.MainInductionStep
