import MIPStarRE.LDT.Test.MainTheorem.Simplified.RoleRegister
import MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization

/-!
# Linear projective rounding in the simplified final theorem

The complete polynomial measurements extracted from the role register are
rounded independently on the two original local spaces. Both projective
measurements are complete, and each state-dependent distance is at most
`18 ζ` for the polynomial consistency error `ζ`.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-formal`,
  equations `short-polynomial-consistency` and `short-rounding-error`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.ProjStrat

open MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization

/-- Complete projective polynomial measurements obtained by linear rounding
of both extracted role-register blocks. -/
theorem simplifiedRoleRegisterProjectiveMeasurements
    (params : Parameters) [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    let σ : Error := 2 * MainInductionStep.simplifiedMainInductionError params
      (3 * eps) (3 * eps) (3 * eps)
    let ζ : Error := σ + 2 * Real.sqrt (3 * eps + σ) +
      (params.m * params.d : Error) / params.q
    ∃ G_A : Measurement (Polynomial params) ιA,
      ∃ G_B : Measurement (Polynomial params) ιB,
        ∃ Q_A : ProjMeas (Polynomial params) ιA,
          ∃ Q_B : ProjMeas (Polynomial params) ιB,
            ConsRel strategy.state (uniformDistribution (Point params))
                (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
                (polynomialEvaluationFamily params G_B.toSubMeas) σ ∧
              ConsRel strategy.state (uniformDistribution (Point params))
                (polynomialEvaluationFamily params G_A.toSubMeas)
                (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) σ ∧
              ConsRel strategy.state (uniformDistribution Unit)
                (constSubMeasFamily G_A.toSubMeas)
                (constSubMeasFamily G_B.toSubMeas) ζ ∧
              SDDRel strategy.state (uniformDistribution Unit)
                (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
                (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas))
                (18 * ζ) ∧
              SDDRel strategy.state (uniformDistribution Unit)
                (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas))
                (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas))
                (18 * ζ) := by
  dsimp
  obtain ⟨G_A, G_B, hA, hB, hfull⟩ :=
    simplifiedRoleRegisterPolynomialConsistency params strategy eps hpass
  let ζ : Error :=
    2 * MainInductionStep.simplifiedMainInductionError params
        (3 * eps) (3 * eps) (3 * eps) +
      2 * Real.sqrt (3 * eps +
        2 * MainInductionStep.simplifiedMainInductionError params
          (3 * eps) (3 * eps) (3 * eps)) +
      (params.m * params.d : Error) / params.q
  have hζ : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ζ := by
    simpa [ζ] using hfull
  obtain ⟨Q_A, hQ_A⟩ :=
    consistent_measurement_linear_bound strategy.state strategy.isNormalized
      G_A G_B ζ hζ
  obtain ⟨Q_B, hQ_B⟩ :=
    right_consistent_measurement_linear_bound strategy.state strategy.isNormalized
      G_A G_B ζ hζ
  exact ⟨G_A, G_B, Q_A, Q_B, hA, hB, hζ, hQ_A, hQ_B⟩

end MIPStarRE.LDT.ProjStrat
