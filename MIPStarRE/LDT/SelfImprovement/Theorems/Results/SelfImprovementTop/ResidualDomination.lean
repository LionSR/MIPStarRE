import MIPStarRE.LDT.SelfImprovement.Theorems.Results.SelfImprovementTop.Core
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.SelfImprovementTop.FinalFields

/-!
# Self-improvement with residual-dominating orthonormalization

This module records the abstract self-improvement wrapper for the
monotone-total route.  It gets complementary slackness from the visible Section
9 producer `sdpStatementWithSlackness`, assumes the orthonormalization stage
supplies residual domination, and then assembles the final projective
self-improvement conclusion without using the alphabet-size total-gap absorption
route.

## References

- `references/ldt-paper/self_improvement.tex`
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Bridge data for the slackness and residual-domination route through
self-improvement.

The package contains exactly the non-SDP inputs needed after the helper stage
has produced a slackness-carrying conclusion: helper strong self-consistency,
helper completeness, the selected point-consistency `add-in-u` transfer, and
the residual-dominating orthonormalization input.  The final-fields producer
then uses the monotone-total comparison supplied by residual domination, rather
than the alphabet-size total-gap estimate. -/
structure SelfImprovementSlacknessResidualDominationBridgeInputs
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) (eps delta nu : Error) where
  /-- Helper-stage strong self-consistency for the averaged helper family. -/
  helperStrongSelfConsistency :
    HelperStrongSelfConsistencyInput params strategy eps delta
  /-- Helper-stage completeness for a slackness-carrying helper conclusion. -/
  helperCompleteness :
    ∀ {T : Measurement (Polynomial params) ι}
      {Hhat : SubMeas (Polynomial params) ι}
      {Z : MIPStarRE.Quantum.Op ι},
      SelfImprovementHelperConclusionWithSlackness params strategy T Hhat Z eps delta →
        CompletenessAtLeast strategy.state Hhat.liftLeft
          ((1 - nu) - selfImprovementHelperError params eps delta)
  /-- The selected `add-in-u` transfer used for helper point consistency. -/
  pointConsistencyTransfer :
    ∀ {T : Measurement (Polynomial params) ι}
      {Hhat : SubMeas (Polynomial params) ι}
      {Z : MIPStarRE.Quantum.Op ι},
      SelfImprovementHelperConclusionWithSlackness params strategy T Hhat Z eps delta →
        |addInULeftQuantity params strategy
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
            Hhat
            (pointConsistencyAddInUSelection params) -
          addInURightQuantity params strategy
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
            T.toSubMeas
            (pointConsistencyAddInUSelection params)| ≤
          addInUError params eps delta
  /-- Residual-dominating orthonormalization input for every helper family. -/
  orthonormalization :
    OrthonormalizationResidualDominationInput params strategy eps delta

/-- The Section 9 SDP producer with complementary slackness and
residual-dominating orthonormalization assemble a full self-improvement
conclusion.

This is the abstract version of the matrix-specific residual-domination bridge:
the SDP stage is supplied by the visible `sdpStatementWithSlackness` producer,
while the construction-level orthonormalization hypothesis is stated through
`OrthonormalizationResidualDominationInput`.  The point-consistency field is
obtained through `final_fields_exists_of_helper_outputs_of_residual_domination`,
so the proof does not invoke the total-gap term
`sqrt (#F_q * selfImprovementDataProcessingError)`. -/
lemma selfImprovementWithSlacknessAndResidualDominationInput
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (heps_le_one : eps ≤ 1)
    (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    (hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (Polynomial params) ι)
    (hhelperCompleteness :
      ∀ {T : Measurement (Polynomial params) ι}
        {Hhat : SubMeas (Polynomial params) ι}
        {Z : MIPStarRE.Quantum.Op ι},
        SelfImprovementHelperConclusionWithSlackness params strategy T Hhat Z eps delta →
          CompletenessAtLeast strategy.state Hhat.liftLeft
            ((1 - nu) - selfImprovementHelperError params eps delta))
    (hhelperSSCInput : HelperStrongSelfConsistencyInput params strategy eps delta)
    (htransfer :
      ∀ {T : Measurement (Polynomial params) ι}
        {Hhat : SubMeas (Polynomial params) ι}
        {Z : MIPStarRE.Quantum.Op ι},
        SelfImprovementHelperConclusionWithSlackness params strategy T Hhat Z eps delta →
          |addInULeftQuantity params strategy
              (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
              Hhat
              (pointConsistencyAddInUSelection params) -
            addInURightQuantity params strategy
              (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
              T.toSubMeas
              (pointConsistencyAddInUSelection params)| ≤
            addInUError params eps delta)
    (horthonormalization :
      OrthonormalizationResidualDominationInput params strategy eps delta) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu := by
  obtain ⟨T, Hhat, Zout, hhelperWithSlackness⟩ :=
    selfImprovementHelperWithSlackness params strategy eps delta gamma
      hgood nu G
  let hhelper : SelfImprovementHelperConclusion params strategy T Hhat Zout eps delta :=
    hhelperWithSlackness.toHelperConclusion
  have heps : 0 ≤ eps := eps_nonneg_of_isGood params strategy hgood
  have hdelta : 0 ≤ delta := delta_nonneg_of_isGood params strategy hgood
  have hpointSSC :
      BipartiteSSCRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta := by
    exact ⟨by
      simpa [SymStrat.selfConsistencyFailureProbability] using
        hgood.selfConsistencyTest⟩
  have hhelperSSCRel :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta) :=
    hhelperSSCInput hhelper
  obtain ⟨H, hfinal, _hTotalLe, horth, hdata⟩ :=
    final_fields_exists_of_helper_outputs_of_residual_domination
      params strategy eps delta nu heps heps_le_one hdelta hdelta_le_one hd_le_q
      hhelper
      (hhelperCompleteness hhelperWithSlackness)
      hhelperSSCRel
      hpointSSC
      (helper_slackness_eq_of_helper_with_slackness
        params strategy eps delta hhelperWithSlackness)
      (htransfer hhelperWithSlackness)
      (horthonormalization hhelperSSCRel)
  have hselfImprovementError_nonneg :
      0 ≤ selfImprovementError params eps delta :=
    MIPStarRE.LDT.SelfImprovement.selfImprovementError_nonneg_of_isGood
      params strategy hgood
  refine ⟨H, Zout, ?_⟩
  exact
    { witness := ⟨T, Hhat, hhelper, horth, hdata⟩
      completeness := hfinal.completeness
      pointConsistency := hfinal.pointConsistency
      selfCloseness := hfinal.selfCloseness
      positiveSemidefiniteWitness := hhelper.sdpWitness.dualPositive
      dualDominatesAveragedPoint := hhelper.sdpWitness.dualFeasible
      projectiveResidualBound := hfinal.projectiveResidualBound
      bounded :=
        final_fields_bounded strategy.state H.toSubMeas
          hhelper.sdpWitness.dualDominatesIdentity hselfImprovementError_nonneg }

/-- Packaged bridge-input form of
`selfImprovementWithSlacknessAndResidualDominationInput`. -/
lemma selfImprovementFromSlacknessResidualDominationBridgeInputs
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (heps_le_one : eps ≤ 1)
    (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    (hbridge :
      SelfImprovementSlacknessResidualDominationBridgeInputs
        params strategy eps delta nu)
    (hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (Polynomial params) ι) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu :=
  selfImprovementWithSlacknessAndResidualDominationInput
    params strategy eps delta gamma nu heps_le_one hdelta_le_one hd_le_q
    hgood G hbridge.helperCompleteness hbridge.helperStrongSelfConsistency
    hbridge.pointConsistencyTransfer hbridge.orthonormalization

/-- Slackness-carrying self-improvement from an ordinary QXP repair producer whose
fresh outcome is controlled by coisometry.

This is the assembly point for the monotone right-total route identified in issue
`#1300`: the constructive spectral slice is discharged by
`orthonormalizationSpectralProducer_of_sourceAlmostProjective`, while
`residualDominatingRepairProducer_of_qxpLayer_and_coisometry` turns the QXP
repair plus the construction-level coisometry identity `X X† = I` into the
residual-domination input consumed by
`selfImprovementWithSlacknessAndResidualDominationInput`.  Consequently the final
point-consistency field uses the paper-tight right-register total comparison
rather than the alphabet-size total-gap route. -/
lemma selfImprovementWithSlacknessAndQXPRepairAndCoisometry
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (heps_le_one : eps ≤ 1)
    (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    (hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (Polynomial params) ι)
    (hhelperCompleteness :
      ∀ {T : Measurement (Polynomial params) ι}
        {Hhat : SubMeas (Polynomial params) ι}
        {Z : MIPStarRE.Quantum.Op ι},
        SelfImprovementHelperConclusionWithSlackness params strategy T Hhat Z eps delta →
          CompletenessAtLeast strategy.state Hhat.liftLeft
            ((1 - nu) - selfImprovementHelperError params eps delta))
    (hhelperSSCInput : HelperStrongSelfConsistencyInput params strategy eps delta)
    (htransfer :
      ∀ {T : Measurement (Polynomial params) ι}
        {Hhat : SubMeas (Polynomial params) ι}
        {Z : MIPStarRE.Quantum.Op ι},
        SelfImprovementHelperConclusionWithSlackness params strategy T Hhat Z eps delta →
          |addInULeftQuantity params strategy
              (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
              Hhat
              (pointConsistencyAddInUSelection params) -
            addInURightQuantity params strategy
              (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
              T.toSubMeas
              (pointConsistencyAddInUSelection params)| ≤
            addInUError params eps delta)
    (hqxp : OrthonormalizationQXPLayerRepairProducer params strategy eps delta)
    (hsource : ∀ {Hhat : SubMeas (Polynomial params) ι}
      (hssc : BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta))
      (hSpectral : SpectralTruncationStatement strategy.state
        (leftLiftedMeasurement (ιB := ι) (optionCompletion Hhat))
        (consistencyToAlmostProjectiveError
          (2 * selfImprovementHelperError params eps delta))),
        (hqxp hssc hSpectral).data.qLayer.q.outcome none =
          (optionCompletion Hhat).outcome none)
    (hcoisometry : ∀ {Hhat : SubMeas (Polynomial params) ι}
      (hssc : BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta))
      (hSpectral : SpectralTruncationStatement strategy.state
        (leftLiftedMeasurement (ιB := ι) (optionCompletion Hhat))
        (consistencyToAlmostProjectiveError
          (2 * selfImprovementHelperError params eps delta))),
        (hqxp hssc hSpectral).data.x * (hqxp hssc hSpectral).data.xᴴ =
          (1 : MIPStarRE.Quantum.Op
            (hqxp hssc hSpectral).data.qLayer.auxSpace.carrier)) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu :=
  selfImprovementWithSlacknessAndResidualDominationInput
    params strategy eps delta gamma nu heps_le_one hdelta_le_one hd_le_q
    hgood G hhelperCompleteness hhelperSSCInput htransfer
    (orthonormalizationResidualDominationInput_of_spectral_qxpLayer_and_coisometry
      (params := params) (strategy := strategy) (eps := eps) (delta := delta)
      orthonormalizationSpectralProducer_of_sourceAlmostProjective
      hqxp hsource hcoisometry)

end MIPStarRE.LDT.SelfImprovement
