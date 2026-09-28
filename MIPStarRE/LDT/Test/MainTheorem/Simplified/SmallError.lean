import MIPStarRE.LDT.Test.MainTheorem.Simplified.PointRoundingLeft
import MIPStarRE.LDT.Test.MainTheorem.Simplified.ProjectiveConsistency
import MIPStarRE.LDT.Test.MainTheorem.Simplified.ScalarsFinal

/-!
# Nontrivial branch of simplified soundness

The role-register induction, heterogeneous Schwartz--Zippel step, complete
linear rounding, and point-filter inequalities produce the original three
consistency conclusions at the simplified final error.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-formal`.
- `references/ldt-paper/test_definition.tex:180-202`, theorem conclusion.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Test

/-- The three final consistency conclusions in the nontrivial error branch.
The proof uses no public pasting-length parameter. -/
theorem simplifiedMainFormal_smallError
    (params : Parameters) [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hsmall : ¬ 1 ≤ simplifiedMainFormalError params eps) :
    SimplifiedMainFormalConclusion params strategy eps := by
  let σ : Error := 2 * MainInductionStep.simplifiedMainInductionError params
    (3 * eps) (3 * eps) (3 * eps)
  let ζ : Error := σ + 2 * Real.sqrt (3 * eps + σ) +
    (params.m * params.d : Error) / params.q
  obtain ⟨G_A, G_B, Q_A, Q_B, hpointA, hpointB, hfull, hroundA, hroundB⟩ :=
    ProjStrat.simplifiedRoleRegisterProjectiveMeasurements
      params strategy eps hpass
  have hA : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (polynomialEvaluationFamily params Q_B.toSubMeas)
      (2 * (σ + 18 * ζ)) := by
    have h := point_consistency_of_right_rounding
      strategy.state strategy.pointMeasurementA G_B Q_B
      (fun u g => g u) σ (18 * ζ)
      (by
        change ConsRel strategy.state (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
          (fun u => postprocess G_B.toSubMeas (fun g => g u)) σ at hpointA
        exact hpointA)
      (by simpa [ζ] using hroundB)
    change ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (fun u => postprocess Q_B.toSubMeas (fun g => g u))
      (2 * (σ + 18 * ζ))
    exact h
  have hB : ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params Q_A.toSubMeas)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
      (2 * (σ + 18 * ζ)) := by
    have h := point_consistency_of_left_rounding
      strategy.state strategy.pointMeasurementB G_A Q_A
      (fun u g => g u) σ (18 * ζ)
      (by
        change ConsRel strategy.state (uniformDistribution (Point params))
          (fun u => postprocess G_A.toSubMeas (fun g => g u))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) σ at hpointB
        exact hpointB)
      (by simpa [ζ] using hroundA)
    change ConsRel strategy.state (uniformDistribution (Point params))
      (fun u => postprocess Q_A.toSubMeas (fun g => g u))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
      (2 * (σ + 18 * ζ))
    exact h
  have hQQ : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily Q_A.toSubMeas)
      (constSubMeasFamily Q_B.toSubMeas) (57 * ζ) :=
    ProjStrat.simplifiedRoundedPolynomialConsistency
      params strategy G_A G_B Q_A Q_B ζ hfull hroundA hroundB
  obtain ⟨hpointBound, hselfBound⟩ :=
    simplifiedFinal_scalar_absorption params eps
      (ProjStrat.eps_nonneg_of_passes hpass) hsmall
  refine ⟨Q_A, Q_B, ?_, ?_, ?_⟩
  · exact ConsRel.mono (by simpa [σ, ζ] using hpointBound) hA
  · exact ConsRel.mono (by simpa [σ, ζ] using hpointBound) hB
  · exact ConsRel.mono (by simpa [σ, ζ] using hselfBound) hQQ

end MIPStarRE.LDT.Test
