import MIPStarRE.LDT.SelfImprovement.Theorems.Results.BoundednessTransport
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.SelfImprovementTop.Completeness
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.SelfImprovementTop.SelfCloseness

/-!
# Final-fields assembly with monotone total transport

This module contains the final-fields assembler which uses the monotone
right-total point-consistency route.  It combines the already isolated
completeness, point-consistency, self-closeness, and projective-residual
producers into `SelfImprovementFinalFields`.
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Final-fields producer using the monotone-total point-consistency route.

This theorem assembles the four fields of `SelfImprovementFinalFields` from the
already isolated helper-output producers.  The point-consistency field is
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

/-- Final-fields producer using operator monotonicity of the projective total.

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

/-- Final-fields producer from helper outputs and residual-dominating
orthonormalization.

This theorem composes the strengthened orthonormalization theorem with the
monotone-total final-fields assembler.  The residual-domination input supplies
the projective submeasurement `H`, its orthonormalization SDD estimate, and the
scalar right-total comparison
`⟨ψ, I ⊗ H.total⟩ ≤ ⟨ψ, I ⊗ Hhat.total⟩`.  The data-processing SDD estimate for
polynomial evaluation families is then derived from helper strong
self-consistency and the orthonormalization estimate, exactly as in the main
self-improvement wrapper. -/
theorem final_fields_exists_of_helper_outputs_of_residual_domination
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta nu : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
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
    (horthBridge :
      OrthonormalizationInputWithResidualDomination
        strategy.state Hhat (selfImprovementHelperError params eps delta)) :
    ∃ H : ProjSubMeas (Polynomial params) ι,
      SelfImprovementFinalFields params strategy H Z eps delta nu ∧
      H.toSubMeas.total ≤ Hhat.total ∧
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat.liftLeft)
        (constSubMeasFamily H.toSubMeas.liftLeft)
        (selfImprovementOrthogonalizationError params eps delta) ∧
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta) := by
  obtain ⟨H, horth, hTotalLe, _hTotalExpectationLe⟩ :=
    orthonormalization_with_total_le_of_residual_domination
      strategy.state strategy.permInvState strategy.isNormalized Hhat
      (selfImprovementHelperError params eps delta) hhelperSSC horthBridge
  have hsscPoint :
      BipartiteSSCRel strategy.state
        (uniformDistribution (Point params))
        (fun _ : Point params => Hhat)
        (selfImprovementHelperError params eps delta) :=
    bipartiteSSCRel_uniform_const strategy.state Hhat
      (selfImprovementHelperError params eps delta) hhelperSSC
  have horthPoint :
      SDDRel strategy.state
        (uniformDistribution (Point params))
        (fun _ : Point params => H.toSubMeas.liftLeft)
        (fun _ : Point params => Hhat.liftLeft)
        (selfImprovementOrthogonalizationError params eps delta) := by
    apply sddRel_uniform_const (ψ := strategy.state)
    exact Preliminaries.sddRel_symm strategy.state (uniformDistribution Unit)
      (constSubMeasFamily Hhat.liftLeft)
      (constSubMeasFamily H.toSubMeas.liftLeft)
      (selfImprovementOrthogonalizationError params eps delta) horth
  have hdata' :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        (selfImprovementDataProcessingError params eps delta) := by
    change SDDRel strategy.state (uniformDistribution (Point params))
      (IdxSubMeas.liftLeft (fun q => postprocess H.toSubMeas (fun h => h q)))
      (IdxSubMeas.liftLeft (fun q => postprocess Hhat (fun h => h q)))
      (8 * selfImprovementHelperError params eps delta +
        8 * Real.rpow (selfImprovementOrthogonalizationError params eps delta)
          (1 / (2 : Error)))
    simpa [Real.sqrt_eq_rpow] using
      Preliminaries.selfConsistencyImpliesDataProcessing
        strategy.state strategy.permInvState strategy.isNormalized
        (uniformDistribution (Point params))
        (uniformDistribution_weight_sum_le_one (Point params))
        (fun _ : Point params => Hhat)
        (fun _ : Point params => H)
        (selfImprovementHelperError params eps delta)
        (selfImprovementOrthogonalizationError params eps delta)
        (fun (u : Point params) (h : Polynomial params) => h u)
        hsscPoint horthPoint
  have hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta) :=
    Preliminaries.sddRel_symm strategy.state (uniformDistribution (Point params))
      ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
      ((polynomialEvaluationFamily params Hhat).liftLeft)
      (selfImprovementDataProcessingError params eps delta) hdata'
  refine ⟨H, ?_, hTotalLe, horth, hdata⟩
  exact
    final_fields_of_helper_outputs_of_total_operator_le
      params strategy eps delta nu heps heps_le_one hdelta hdelta_le_one hd_le_q
      hhelper hhelperCompleteness hhelperSSC hpointSSC hslack htransfer
      horth hdata hTotalLe

end MIPStarRE.LDT.SelfImprovement
