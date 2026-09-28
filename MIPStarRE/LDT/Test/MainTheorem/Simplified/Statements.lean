import MIPStarRE.LDT.Test.MainTheorem.Simplified.Rounding

/-!
# Error parameter of the simplified final theorem

The final error has no public pasting length and no exponential term. The
three consistency conclusions retain the original two-space strategy and
projective polynomial-measurement types.

## References

- `blueprint/src/low_degree_simplified.tex`, `thm:main-formal`.
- `references/ldt-paper/test_definition.tex:180-202`, original conclusion.
-/

namespace MIPStarRE.LDT.Test

/-- `K_{m,d}` in the simplified final theorem. -/
def simplifiedFinalScale (params : Parameters) : Error :=
  if params.d = 0 then
    (params.m : Error) ^ (4 : ℕ)
  else
    (params.d : Error) ^ (2 : ℕ) * (params.m : Error) ^ (4 : ℕ)

/-- The simplified final error `21000 K_{m,d}
(ε^(1/64) + (d/q)^(1/64))`. -/
noncomputable def simplifiedMainFormalError
    (params : Parameters) (eps : Error) : Error :=
  21000 * simplifiedFinalScale params *
    (Real.rpow eps (1 / (64 : Error)) +
      Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (64 : Error)))

/-- The three paper conclusions with the simplified error, preserving the
heterogeneous local spaces of `ProjStrat`. -/
def SimplifiedMainFormalConclusion
    (params : Parameters) [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB) (eps : Error) : Prop :=
  ∃ G_A : ProjMeas (Polynomial params) ιA,
    ∃ G_B : ProjMeas (Polynomial params) ιB,
      ConsRel strategy.state (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
          (polynomialEvaluationFamily params G_B.toSubMeas)
          (simplifiedMainFormalError params eps) ∧
        ConsRel strategy.state (uniformDistribution (Point params))
          (polynomialEvaluationFamily params G_A.toSubMeas)
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
          (simplifiedMainFormalError params eps) ∧
        ConsRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily G_A.toSubMeas)
          (constSubMeasFamily G_B.toSubMeas)
          (simplifiedMainFormalError params eps)

end MIPStarRE.LDT.Test
