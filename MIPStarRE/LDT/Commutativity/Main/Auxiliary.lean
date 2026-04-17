import MIPStarRE.LDT.Commutativity.Transport.FullSlice

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Paper `eq:evaluate-gcom-at-points` / `eq:gcom4-diff`
(`commutativity-G.tex` lines 339-354).

Schwartz-Zippel marginalization on the `x` variable: replacing the full
polynomial sum `∑_g G^x_g` by the point-evaluated sum `E_u ∑_a G^x_[g(u)=a]`
inside the ABA term costs at most `params.m · params.d / params.q`.

TODO(#361): apply `schwartzZippel_individualDegree` from
`MIPStarRE/LDT/Preliminaries/Polynomials.lean` to the polynomial-agreement
collision term `1[g(u) = g'(u)]`, then bound the off-diagonal fiber sum using
the sub-measurement property of `G^x`. -/
lemma fullSlice_scalar_marginalize_x
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    |fullSliceABAAvg params strategy family -
        evaluatedSliceABAAvg params strategy family| ≤
      (↑params.m : Error) * ↑params.d / ↑params.q := by
  sorry

/-- Paper `eq:evaluate-gcom-at-points-part-dos`
(`commutativity-G.tex` lines 369-385).

Schwartz-Zippel marginalization on the `y` variable: replacing the full
polynomial sum `∑_h G^y_h` by the point-evaluated sum `E_v ∑_b G^y_[h(v)=b]`
inside the ABAB term costs at most `params.m · params.d / params.q`.  Symmetric
in structure to `fullSlice_scalar_marginalize_x`; the paper's difference-
expression label at line 379 is idiosyncratic, so we cite the enclosing
approximation statement. -/
lemma fullSlice_scalar_marginalize_y
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    |fullSliceABABAvg params strategy family -
        evaluatedSliceABABAvg params strategy family| ≤
      (↑params.m : Error) * ↑params.d / ↑params.q := by
  sorry

/-- Combined `closenessOfIP` chain on the evaluated side
(`commutativity-G.tex` lines 301, 334, 359-360, 394, 396).

Using `hEval` together with the six `closenessOfIP` steps in the paper:
two on the ABA side (line 301: `2√ζ`) and four on the ABAB side
(line 334: `√ζ`, lines 359-360: `2√ζ`, line 396: `√ζ`), plus the final
`closenessOfIP` with `hEval` as the `A≈B` input (line 394: `√ν_evaluation`),
the evaluated-slice scalar commutator is bounded by
`6√ζ + √(commDataProcessedGError)`.

The `hEval` hypothesis is bound into the fourth step via
`fullSlice_closenessOfIP_CAB_hEval` inputs; the first six steps use
`item:commuting-self-consistency` from `_hself`.

TODO(#361): invoke `closenessOfIP` (`Preliminaries/CauchySchwarz.lean:342`) six
times, each with `normalizationCondition_sandwich_bound` discharging the `C`
normalization condition, and chain the `√ζ` / `√ν` contributions. -/
lemma fullSlice_closenessOfIP_CAB_hEval
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (_hgamma_nonneg : 0 ≤ gamma) (_hzeta_nonneg : 0 ≤ zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hEval :
      SDDOpRel strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedFromFullSliceProductLeft params strategy family)
        (evaluatedFromFullSliceProductRight params strategy family)
        (commDataProcessedGError params gamma zeta)) :
    |evaluatedSliceABAAvg params strategy family -
        evaluatedSliceABABAvg params strategy family| ≤
      6 * Real.sqrt zeta +
        Real.sqrt (commDataProcessedGError params gamma zeta) := by
  sorry


end MIPStarRE.LDT.Commutativity
