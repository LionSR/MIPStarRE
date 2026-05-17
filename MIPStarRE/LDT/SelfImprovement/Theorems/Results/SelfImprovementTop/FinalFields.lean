import MIPStarRE.LDT.SelfImprovement.Theorems.Results.BoundednessTransport
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.SelfImprovementTop.Completeness
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.SelfImprovementTop.SelfCloseness

/-!
# Final-fields assembly routes

This module contains the final-fields assemblers used in the projective
self-improvement theorem.  It combines the already isolated completeness,
point-consistency, self-closeness, and projective-residual constructions into
`SelfImprovementFinalFields`, with both a monotone-total route and a fallback
total-difference route for the point-consistency field.
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 800000 in
-- This final-fields route assembles completeness, point consistency,
-- self-closeness, and boundedness from the helper-output constructors.
/-- Final-fields construction using the monotone-total point-consistency route.

This theorem assembles the four fields of `SelfImprovementFinalFields` from the
already isolated helper-output constructions.  The point-consistency field is
obtained from
`final_fields_point_consistency_of_total_expectation_le_of_small_errors`, rather
than from the total-gap data-processing wrapper; consequently the proof uses the
paper's `ζ̂ + √ζ̂_dataprocess` point-consistency error and does not introduce
the Cauchy--Schwarz alphabet-size term
`√(#F_q · ζ̂_dataprocess)`.

The remaining explicit hypothesis is the scalar right-total monotonicity
comparison

`⟨ψ, I ⊗ H.total⟩ ≤ ⟨ψ, I ⊗ Hhat.total⟩`.

Here `rightTensor` is the codebase convention for placing the helper or
projective total operator on the second tensor factor, namely as `I ⊗ (-)`.
This is the exact invariant needed to replace the current alphabet-size
transport by the paper's measurement-valued `triangleSub` step. -/
theorem final_fields_of_helper_outputs_of_total_expectation_le
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta nu : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {H : ProjSubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hhelperCompleteness :
      CompletenessAtLeast strategy.state Hhat.liftLeft
        ((1 - nu) - selfImprovementHelperError params eps delta))
    (hhelperSSC :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta))
    (hpointSSC :
      BipartiteSSCRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hslack :
      ∀ h : Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z)
    (htransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          Hhat
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T.toSubMeas
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta)
    (horth :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat.liftLeft)
        (constSubMeasFamily H.toSubMeas.liftLeft)
        (selfImprovementOrthogonalizationError params eps delta))
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta))
    (hTotalLe :
      ev strategy.state (rightTensor (ι₁ := ι) H.toSubMeas.total) ≤
        ev strategy.state (rightTensor (ι₁ := ι) Hhat.total)) :
    SelfImprovementFinalFields params strategy H Z eps delta nu := by
  have hhelperPoint :
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params Hhat)
        (selfImprovementHelperError params eps delta) :=
    helper_point_consistency_of_pointConsistencyAddInU_transfer
      params strategy eps delta heps hdelta htransfer
  refine
    { completeness := ?_
      pointConsistency := ?_
      selfCloseness := ?_
      projectiveResidualBound := ?_ }
  · exact
      final_fields_completeness_of_helper_completeness_of_small_errors
        params strategy eps delta nu heps heps_le_one hdelta hdelta_le_one hd_le_q
        Hhat H hhelperCompleteness hhelperSSC horth
  · exact
      final_fields_point_consistency_of_total_expectation_le_of_small_errors
        params strategy eps delta heps heps_le_one hdelta hdelta_le_one hd_le_q
        hhelperPoint hdata hTotalLe
  · exact
      final_fields_self_closeness_of_small_errors
        params strategy eps delta heps heps_le_one hdelta hdelta_le_one hd_le_q
        Hhat H hhelperSSC horth
  · exact
      final_fields_projective_residual_bound_of_helper_outputs
        params strategy eps delta heps heps_le_one hdelta hdelta_le_one hd_le_q
        hhelper hpointSSC hslack htransfer hdata

set_option maxHeartbeats 800000 in
-- This alternative final-fields route uses the total-difference point-consistency
-- constructor and therefore elaborates the same four output fields.
/-- Final-fields construction using an explicit right-total-difference bound.

This is the submeasurement-total fallback for the point-consistency field.  When
the proof supplies only a scalar bound on

`|⟨ψ, I ⊗ H.total⟩ - ⟨ψ, I ⊗ Hhat.total⟩|`,

rather than monotonicity `⟨ψ, I ⊗ H.total⟩ ≤ ⟨ψ, I ⊗ Hhat.total⟩`, the
point-consistency field is assembled through
`final_fields_point_consistency_totalGap_of_total_difference`.  The remaining
fields are unchanged. -/
theorem final_fields_of_helper_outputs_of_total_difference
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta nu η : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {H : ProjSubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hhelperCompleteness :
      CompletenessAtLeast strategy.state Hhat.liftLeft
        ((1 - nu) - selfImprovementHelperError params eps delta))
    (hhelperSSC :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta))
    (hpointSSC :
      BipartiteSSCRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hslack :
      ∀ h : Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z)
    (htransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          Hhat
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T.toSubMeas
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta)
    (horth :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat.liftLeft)
        (constSubMeasFamily H.toSubMeas.liftLeft)
        (selfImprovementOrthogonalizationError params eps delta))
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
    SelfImprovementFinalFields params strategy H Z eps delta nu := by
  have hhelperPoint :
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params Hhat)
        (selfImprovementHelperError params eps delta) :=
    helper_point_consistency_of_pointConsistencyAddInU_transfer
      params strategy eps delta heps hdelta htransfer
  refine
    { completeness := ?_
      pointConsistency := ?_
      selfCloseness := ?_
      projectiveResidualBound := ?_ }
  · exact
      final_fields_completeness_of_helper_completeness_of_small_errors
        params strategy eps delta nu heps heps_le_one hdelta hdelta_le_one hd_le_q
        Hhat H hhelperCompleteness hhelperSSC horth
  · exact
      final_fields_point_consistency_totalGap_of_total_difference
        params strategy eps delta η hhelperPoint hdata hTotal habsorb
  · exact
      final_fields_self_closeness_of_small_errors
        params strategy eps delta heps heps_le_one hdelta hdelta_le_one hd_le_q
        Hhat H hhelperSSC horth
  · exact
      final_fields_projective_residual_bound_of_helper_outputs
        params strategy eps delta heps heps_le_one hdelta hdelta_le_one hd_le_q
        hhelper hpointSSC hslack htransfer hdata

/-- Final-fields construction using operator monotonicity of the projective total.

This is the operator-order form of
`final_fields_of_helper_outputs_of_total_expectation_le`.  The hypothesis
`H.toSubMeas.total ≤ Hhat.total` is independent of the particular state, and
therefore matches the construction-level invariant naturally produced by
orthonormalization.  The required right-register scalar comparison follows
from monotonicity of right tensor placement and of expectation in the strategy
state. -/
theorem final_fields_of_helper_outputs_of_total_operator_le
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta nu : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {H : ProjSubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hhelperCompleteness :
      CompletenessAtLeast strategy.state Hhat.liftLeft
        ((1 - nu) - selfImprovementHelperError params eps delta))
    (hhelperSSC :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta))
    (hpointSSC :
      BipartiteSSCRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hslack :
      ∀ h : Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z)
    (htransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          Hhat
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T.toSubMeas
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta)
    (horth :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat.liftLeft)
        (constSubMeasFamily H.toSubMeas.liftLeft)
        (selfImprovementOrthogonalizationError params eps delta))
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta))
    (hTotalLe : H.toSubMeas.total ≤ Hhat.total) :
    SelfImprovementFinalFields params strategy H Z eps delta nu := by
  exact
    final_fields_of_helper_outputs_of_total_expectation_le
      params strategy eps delta nu heps heps_le_one hdelta hdelta_le_one hd_le_q
      hhelper hhelperCompleteness hhelperSSC hpointSSC hslack htransfer
      horth hdata
      (ev_mono strategy.state _ _ (MIPStarRE.LDT.rightTensor_mono hTotalLe))

end MIPStarRE.LDT.SelfImprovement
