import MIPStarRE.LDT.SelfImprovement.Theorems.Results.BoundednessTransport.PointConsistency

/-!
# Boundedness transport literal point-consistency estimates

This file contains the literal-threshold point-consistency transports obtained
from the natural-error estimates in `BoundednessTransport/PointConsistency.lean`.

## References

- `references/ldt-paper/self_improvement.tex` lines 747--755
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.Quantum
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Literal-threshold point-consistency transport from the helper output to the
projective output.

This theorem isolates the numerical absorption needed to turn the natural
error
`selfImprovementHelperError + sqrt selfImprovementDataProcessingError + η`
into the final `selfImprovementError` threshold.  The analytic content is
contained in `final_fields_point_consistency_totalGap_natural`. -/
theorem final_fields_point_consistency_totalGap
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta η : Error)
    {Hhat : SubMeas (Polynomial params) ι}
    {H : ProjSubMeas (Polynomial params) ι}
    (hhelperPoint :
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params Hhat)
        (selfImprovementHelperError params eps delta))
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta))
    (hTotal :
      avgOver (uniformDistribution (Point params)) (fun u =>
        |ev strategy.state
            (leftTensor (ι₂ := ι)
              (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
              rightTensor (ι₁ := ι)
                (((polynomialEvaluationFamily params H.toSubMeas) u).total)) -
          ev strategy.state
            (leftTensor (ι₂ := ι)
              (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
              rightTensor (ι₁ := ι)
                (((polynomialEvaluationFamily params Hhat) u).total))|) ≤ η)
    (habsorb :
      selfImprovementHelperError params eps delta +
          Real.sqrt (selfImprovementDataProcessingError params eps delta) + η ≤
        selfImprovementError params eps delta) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementError params eps delta) :=
  MIPStarRE.LDT.ConsRel.mono habsorb
    (final_fields_point_consistency_totalGap_natural params strategy eps delta η
      hhelperPoint hdata hTotal)

/-- Literal-threshold point-consistency transport from a right-register total
difference bound.

This is the `selfImprovementError`-absorbed companion to
`final_fields_point_consistency_totalGap_natural_of_total_difference`. -/
theorem final_fields_point_consistency_totalGap_of_total_difference
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta η : Error)
    {Hhat : SubMeas (Polynomial params) ι}
    {H : ProjSubMeas (Polynomial params) ι}
    (hhelperPoint :
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params Hhat)
        (selfImprovementHelperError params eps delta))
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta))
    (hTotal :
      |ev strategy.state (rightTensor (ι₁ := ι) H.toSubMeas.total) -
        ev strategy.state (rightTensor (ι₁ := ι) Hhat.total)| ≤ η)
    (habsorb :
      selfImprovementHelperError params eps delta +
          Real.sqrt (selfImprovementDataProcessingError params eps delta) + η ≤
        selfImprovementError params eps delta) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementError params eps delta) :=
  MIPStarRE.LDT.ConsRel.mono habsorb
    (final_fields_point_consistency_totalGap_natural_of_total_difference
      params strategy eps delta η hhelperPoint hdata hTotal)

/-- Natural-error point-consistency transport under monotone total overlap.

If the projective replacement has no larger right-register total overlap with
the point measurement than the helper submeasurement, then the submeasurement
triangle argument is at the paper-natural error threshold
`selfImprovementHelperError + sqrt selfImprovementDataProcessingError`. -/
theorem final_fields_point_consistency_natural_of_total_le
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {Hhat : SubMeas (Polynomial params) ι}
    {H : ProjSubMeas (Polynomial params) ι}
    (hhelperPoint :
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params Hhat)
        (selfImprovementHelperError params eps delta))
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta))
    (hTotalLe :
      ∀ u : Point params,
        ev strategy.state
            (leftTensor (ι₂ := ι)
              (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
              rightTensor (ι₁ := ι)
                (((polynomialEvaluationFamily params H.toSubMeas) u).total)) ≤
          ev strategy.state
            (leftTensor (ι₂ := ι)
              (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
              rightTensor (ι₁ := ι)
                (((polynomialEvaluationFamily params Hhat) u).total))) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta)) := by
  have hdata_right :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftRight)
        ((polynomialEvaluationFamily params H.toSubMeas).liftRight)
        (selfImprovementDataProcessingError params eps delta) := by
    simpa [IdxSubMeas.liftLeft, IdxSubMeas.liftRight]
      using
        sddRel_liftRight_of_liftLeft_permInv
          strategy.permInvState (uniformDistribution (Point params))
          (polynomialEvaluationFamily params Hhat)
          (polynomialEvaluationFamily params H.toSubMeas)
          (selfImprovementDataProcessingError params eps delta) hdata
  exact
    Preliminaries.triangleSub_right_subMeas_total_le
      strategy.state (uniformDistribution (Point params)) strategy.isNormalized
      (uniformDistribution_weight_sum_le_one (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params Hhat)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementHelperError params eps delta)
      (selfImprovementDataProcessingError params eps delta) hhelperPoint
      hdata_right hTotalLe

/-- Natural-error point-consistency transport from a scalar right-total
monotonicity hypothesis.

Since the point measurement is complete and postprocessing preserves total
operators, this monotonicity condition is equivalent to a single scalar
comparison of right-register expectations. -/
theorem final_fields_point_consistency_natural_of_total_expectation_le
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {Hhat : SubMeas (Polynomial params) ι}
    {H : ProjSubMeas (Polynomial params) ι}
    (hhelperPoint :
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params Hhat)
        (selfImprovementHelperError params eps delta))
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta))
    (hTotalLe :
      ev strategy.state (rightTensor (ι₁ := ι) H.toSubMeas.total) ≤
        ev strategy.state (rightTensor (ι₁ := ι) Hhat.total)) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta)) := by
  refine
    final_fields_point_consistency_natural_of_total_le
      params strategy eps delta hhelperPoint hdata ?_
  intro u
  rw [pointMeasurement_total_evalFamily_total_ev_eq_rightTensor
      params strategy H.toSubMeas u,
    pointMeasurement_total_evalFamily_total_ev_eq_rightTensor
      params strategy Hhat u]
  exact hTotalLe

/-- Literal-threshold point-consistency transport from scalar right-total
monotonicity and the standard small-error hypotheses. -/
theorem final_fields_point_consistency_of_total_expectation_le_of_small_errors
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    {Hhat : SubMeas (Polynomial params) ι}
    {H : ProjSubMeas (Polynomial params) ι}
    (hhelperPoint :
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params Hhat)
        (selfImprovementHelperError params eps delta))
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta))
    (hTotalLe :
      ev strategy.state (rightTensor (ι₁ := ι) H.toSubMeas.total) ≤
        ev strategy.state (rightTensor (ι₁ := ι) Hhat.total)) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementError params eps delta) :=
  MIPStarRE.LDT.ConsRel.mono
    (final_fields_projective_residual_error_le_selfImprovementError
      params eps delta heps heps_le_one hdelta hdelta_le_one hd_le_q)
    (final_fields_point_consistency_natural_of_total_expectation_le
      params strategy eps delta hhelperPoint hdata hTotalLe)

/-- Natural-error point-consistency transport from operator right-total
monotonicity.

The operator inequality `H.total ≤ Hhat.total` implies the scalar right-total
comparison after placing both operators on the right tensor factor and taking
expectation in the shared state. -/
theorem final_fields_point_consistency_natural_of_total_operator_le
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {Hhat : SubMeas (Polynomial params) ι}
    {H : ProjSubMeas (Polynomial params) ι}
    (hhelperPoint :
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params Hhat)
        (selfImprovementHelperError params eps delta))
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta))
    (hTotalLe : H.toSubMeas.total ≤ Hhat.total) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta)) := by
  have hTotalExpectationLe :
      ev strategy.state (rightTensor (ι₁ := ι) H.toSubMeas.total) ≤
        ev strategy.state (rightTensor (ι₁ := ι) Hhat.total) := by
    exact ev_mono strategy.state _ _ (MIPStarRE.LDT.rightTensor_mono hTotalLe)
  exact
    final_fields_point_consistency_natural_of_total_expectation_le
      params strategy eps delta hhelperPoint hdata hTotalExpectationLe

/-- Literal-threshold point-consistency transport from operator right-total
monotonicity and the standard small-error hypotheses.

This is the operator-order version of
`final_fields_point_consistency_of_total_expectation_le_of_small_errors`. -/
theorem final_fields_point_consistency_of_total_operator_le_of_small_errors
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    {Hhat : SubMeas (Polynomial params) ι}
    {H : ProjSubMeas (Polynomial params) ι}
    (hhelperPoint :
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params Hhat)
        (selfImprovementHelperError params eps delta))
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta))
    (hTotalLe : H.toSubMeas.total ≤ Hhat.total) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementError params eps delta) :=
  MIPStarRE.LDT.ConsRel.mono
    (final_fields_projective_residual_error_le_selfImprovementError
      params eps delta heps heps_le_one hdelta hdelta_le_one hd_le_q)
    (final_fields_point_consistency_natural_of_total_operator_le
      params strategy eps delta hhelperPoint hdata hTotalLe)

/-- Literal-threshold point-consistency transport with the data-processing
estimate.

This is the theorem required by #1240.  The remaining analytical
route is carried by `final_fields_point_consistency_natural_of_total_le`
and the standard small-error absorption bound; no additional
`sqrt (#F_q * selfImprovementDataProcessingError)` term is absorbed here. -/
theorem final_fields_point_consistency_totalGap_of_data_processing
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    {Hhat : SubMeas (Polynomial params) ι}
    {H : ProjSubMeas (Polynomial params) ι}
    (hhelperPoint :
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params Hhat)
        (selfImprovementHelperError params eps delta))
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta))
    (hTotalLe :
      ev strategy.state (rightTensor (ι₁ := ι) H.toSubMeas.total) ≤
        ev strategy.state (rightTensor (ι₁ := ι) Hhat.total)) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementError params eps delta) :=
  final_fields_point_consistency_of_total_expectation_le_of_small_errors
    params strategy eps delta heps heps_le_one hdelta hdelta_le_one hd_le_q
    hhelperPoint hdata hTotalLe

end MIPStarRE.LDT.SelfImprovement
