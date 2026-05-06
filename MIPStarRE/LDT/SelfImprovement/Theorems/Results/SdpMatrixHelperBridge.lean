import MIPStarRE.LDT.SelfImprovement.Theorems.Results.SdpMatrixBridge
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.SelfImprovementTop
import MIPStarRE.LDT.SelfImprovement.Theorems.OrthonormalizationBridge

/-!
# Matrix SDP helper bridge

This file connects the matrix-level SDP slackness interface to the
self-improvement helper theorem.  It is deliberately a bridge statement: it
does not prove semidefinite-programming strong duality, but it records the exact
matrix-level input from which the helper conclusion with complementary
slackness follows.

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

/-- Matrix-level SDP data, together with the helper hypotheses, feed the
slackness-carrying self-improvement helper.

The theorem is the downstream use of
`MatrixSdpStatementWithSlacknessAndDominance`: once the matrix SDP argument
supplies an optimal pair satisfying complementary slackness and \(I \le Z\), it
may be combined with the helper-side assumptions `strategy.IsGood eps delta
gamma`, the error parameter `nu`, and the comparison measurement `G`.  Under
these additional hypotheses, the existing helper construction produces \(T\),
\(\widehat H\), and \(Z\) together with the complementary-slackness equations
used in the helper-completeness chain. -/
lemma selfImprovementHelperWithMatrixSdpSlacknessAndDominance
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hsdp : MatrixSdpStatementWithSlacknessAndDominance params
      (matrixSdpPointRealizationOfStrategy params strategy))
    (hgood : strategy.IsGood eps delta gamma)
    (nu : Error)
    (G : Measurement (Polynomial params) ι) :
    ∃ T : Measurement (Polynomial params) ι,
      ∃ H : SubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
        SelfImprovementHelperConclusionWithSlackness params strategy T H Z eps delta :=
  selfImprovementHelperWithSlackness params strategy eps delta gamma
    (MatrixSdpStatementWithSlacknessAndDominance.toSdpStatementWithSlackness
      params strategy hsdp)
    hgood nu G

/-- Canonical block-SDP data feed the slackness-carrying self-improvement
helper.

This is the paper-facing consumer of
`sdpStatementWithSlackness_of_canonicalFeasibleComplementarySlackness`.
Once a canonical
primal matrix `X` is feasible, the canonical dual `Z` is feasible, the canonical
objective equals the dual objective, canonical complementary slackness holds,
and the selected dual satisfies \(I \le Z\), the existing matrix SDP bridge
produces the helper output with complementary slackness. -/
lemma selfImprovementHelperWithCanonicalMatrixSdpSlacknessAndDominance
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params
      (matrixSdpPointRealizationOfStrategy params strategy)))
    (hX : MatrixSdpCanonicalPrimalFeasible params
      (matrixSdpPointRealizationOfStrategy params strategy) X)
    (Z : MIPStarRE.Quantum.Op ι)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params
          (matrixSdpPointRealizationOfStrategy params strategy) Z g)
    (hstrong :
      Complex.re (Matrix.trace
          (matrixSdpCanonicalObjectiveOperator params
            (matrixSdpPointRealizationOfStrategy params strategy) * X)) =
        matrixSdpDualObjective
          (matrixSdpPointRealizationOfStrategy params strategy) Z)
    (hcanonical :
      X * (matrixSdpCanonicalDualOperator params
          (matrixSdpPointRealizationOfStrategy params strategy) Z -
            matrixSdpCanonicalObjectiveOperator params
              (matrixSdpPointRealizationOfStrategy params strategy)) =
        0)
    (hOneLe : (1 : MIPStarRE.Quantum.Op ι) ≤ Z)
    (hgood : strategy.IsGood eps delta gamma)
    (nu : Error)
    (G : Measurement (Polynomial params) ι) :
    ∃ T : Measurement (Polynomial params) ι,
      ∃ H : SubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
        SelfImprovementHelperConclusionWithSlackness params strategy T H Z eps delta :=
  selfImprovementHelperWithSlackness params strategy eps delta gamma
    (sdpStatementWithSlackness_of_canonicalFeasibleComplementarySlackness
      params strategy X hX Z hdual hstrong hcanonical hOneLe)
    hgood nu G

/-- A canonical optimal pair with dominance feeds the slackness-carrying
self-improvement helper. -/
lemma selfImprovementHelperWithCanonicalOptimalPairSdpSlacknessAndDominance
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params
      (matrixSdpPointRealizationOfStrategy params strategy)))
    (Z : MIPStarRE.Quantum.Op ι)
    (hsdp : MatrixSdpCanonicalOptimalPairWithDominance params
      (matrixSdpPointRealizationOfStrategy params strategy) X Z)
    (hgood : strategy.IsGood eps delta gamma)
    (nu : Error)
    (G : Measurement (Polynomial params) ι) :
    ∃ T : Measurement (Polynomial params) ι,
      ∃ H : SubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
        SelfImprovementHelperConclusionWithSlackness params strategy T H Z eps delta :=
  selfImprovementHelperWithSlackness params strategy eps delta gamma
    (sdpStatementWithSlackness_of_canonicalOptimalPairWithDominance
      params strategy X Z hsdp)
    hgood nu G

/-- Canonical block-SDP slackness and residual-dominating orthonormalization
assemble a full self-improvement conclusion.

This is the slackness-aware counterpart of the reduced `selfImprovement`
wrapper.  The canonical SDP data produce the helper witnesses together with
the complementary-slackness equations.  The residual-dominating
orthonormalization input then supplies the projective measurement and the
monotone-total comparison.  The projective residual bound is not assumed as a
final field: it is derived from `final_fields_exists_of_helper_outputs_of_residual_domination`
using the helper-output boundedness producer and the complementary-slackness
equations. -/
lemma selfImprovementWithCanonicalMatrixSdpSlacknessAndResidualDomination
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (heps_le_one : eps ≤ 1)
    (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params
      (matrixSdpPointRealizationOfStrategy params strategy)))
    (hX : MatrixSdpCanonicalPrimalFeasible params
      (matrixSdpPointRealizationOfStrategy params strategy) X)
    (Z : MIPStarRE.Quantum.Op ι)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params
          (matrixSdpPointRealizationOfStrategy params strategy) Z g)
    (hstrong :
      Complex.re (Matrix.trace
          (matrixSdpCanonicalObjectiveOperator params
            (matrixSdpPointRealizationOfStrategy params strategy) * X)) =
        matrixSdpDualObjective
          (matrixSdpPointRealizationOfStrategy params strategy) Z)
    (hcanonical :
      X * (matrixSdpCanonicalDualOperator params
          (matrixSdpPointRealizationOfStrategy params strategy) Z -
            matrixSdpCanonicalObjectiveOperator params
              (matrixSdpPointRealizationOfStrategy params strategy)) =
        0)
    (hOneLe : (1 : MIPStarRE.Quantum.Op ι) ≤ Z)
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
      ∀ {T : Measurement (Polynomial params) ι}
        {Hhat : SubMeas (Polynomial params) ι}
        {Z : MIPStarRE.Quantum.Op ι},
        SelfImprovementHelperConclusionWithSlackness params strategy T Hhat Z eps delta →
          OrthonormalizationInputWithResidualDomination
            strategy.state Hhat (selfImprovementHelperError params eps delta)) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu := by
  obtain ⟨T, Hhat, Zout, hhelperWithSlackness⟩ :=
    selfImprovementHelperWithCanonicalMatrixSdpSlacknessAndDominance
      params strategy eps delta gamma X hX Z hdual hstrong hcanonical hOneLe
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
      (horthonormalization hhelperWithSlackness)
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

/-- Canonical block-SDP slackness and a bundled residual-domination input
assemble a full self-improvement conclusion.

This is the same assembly theorem as
`selfImprovementWithCanonicalMatrixSdpSlacknessAndResidualDomination`, but with
the orthonormalization hypothesis stated in the SelfImprovement-level form
`OrthonormalizationResidualDominationInput`.  The helper strong
self-consistency input selects the helper submeasurement \(\widehat H\), and
the bundled input then gives the residual-dominating orthonormalization datum
for that particular \(\widehat H\). -/
lemma selfImprovementWithCanonicalMatrixSdpSlacknessAndResidualDominationInput
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (heps_le_one : eps ≤ 1)
    (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params
      (matrixSdpPointRealizationOfStrategy params strategy)))
    (hX : MatrixSdpCanonicalPrimalFeasible params
      (matrixSdpPointRealizationOfStrategy params strategy) X)
    (Z : MIPStarRE.Quantum.Op ι)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params
          (matrixSdpPointRealizationOfStrategy params strategy) Z g)
    (hstrong :
      Complex.re (Matrix.trace
          (matrixSdpCanonicalObjectiveOperator params
            (matrixSdpPointRealizationOfStrategy params strategy) * X)) =
        matrixSdpDualObjective
          (matrixSdpPointRealizationOfStrategy params strategy) Z)
    (hcanonical :
      X * (matrixSdpCanonicalDualOperator params
          (matrixSdpPointRealizationOfStrategy params strategy) Z -
            matrixSdpCanonicalObjectiveOperator params
              (matrixSdpPointRealizationOfStrategy params strategy)) =
        0)
    (hOneLe : (1 : MIPStarRE.Quantum.Op ι) ≤ Z)
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
    (horthInput : OrthonormalizationResidualDominationInput params strategy eps delta) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu :=
  selfImprovementWithCanonicalMatrixSdpSlacknessAndResidualDomination
    params strategy eps delta gamma nu heps_le_one hdelta_le_one hd_le_q
    X hX Z hdual hstrong hcanonical hOneLe hgood G
    hhelperCompleteness hhelperSSCInput htransfer
    (fun hhelperWithSlackness =>
      horthInput (hhelperSSCInput hhelperWithSlackness.toHelperConclusion))

/-- A canonical optimal pair with dominance and residual-dominating
orthonormalization assemble a full self-improvement conclusion. -/
lemma selfImprovementWithCanonicalOptimalPairSdpSlacknessAndResidualDomination
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (heps_le_one : eps ≤ 1)
    (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params
      (matrixSdpPointRealizationOfStrategy params strategy)))
    (Z : MIPStarRE.Quantum.Op ι)
    (hsdp : MatrixSdpCanonicalOptimalPairWithDominance params
      (matrixSdpPointRealizationOfStrategy params strategy) X Z)
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
      ∀ {T : Measurement (Polynomial params) ι}
        {Hhat : SubMeas (Polynomial params) ι}
        {Z : MIPStarRE.Quantum.Op ι},
        SelfImprovementHelperConclusionWithSlackness params strategy T Hhat Z eps delta →
          OrthonormalizationInputWithResidualDomination
            strategy.state Hhat (selfImprovementHelperError params eps delta)) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu :=
  selfImprovementWithCanonicalMatrixSdpSlacknessAndResidualDomination
    params strategy eps delta gamma nu heps_le_one hdelta_le_one hd_le_q
    X hsdp.feasible Z hsdp.dualFeasible hsdp.strongDuality
    hsdp.complementarySlackness hsdp.dualDominatesIdentity hgood G
    hhelperCompleteness hhelperSSCInput htransfer horthonormalization

/-- A canonical optimal pair with dominance and a bundled residual-domination
input assemble a full self-improvement conclusion. -/
lemma selfImprovementWithCanonicalOptimalPairSdpSlacknessAndResidualDominationInput
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (heps_le_one : eps ≤ 1)
    (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params
      (matrixSdpPointRealizationOfStrategy params strategy)))
    (Z : MIPStarRE.Quantum.Op ι)
    (hsdp : MatrixSdpCanonicalOptimalPairWithDominance params
      (matrixSdpPointRealizationOfStrategy params strategy) X Z)
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
    (horthInput : OrthonormalizationResidualDominationInput params strategy eps delta) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu :=
  selfImprovementWithCanonicalMatrixSdpSlacknessAndResidualDominationInput
    params strategy eps delta gamma nu heps_le_one hdelta_le_one hd_le_q
    X hsdp.feasible Z hsdp.dualFeasible hsdp.strongDuality
    hsdp.complementarySlackness hsdp.dualDominatesIdentity hgood G
    hhelperCompleteness hhelperSSCInput htransfer horthInput
    hhelperCompleteness hhelperSSCInput htransfer horthInput

/-- A canonical optimal pair with dominance and a residual-dominating QXP repair
producer assemble a full self-improvement conclusion.

The spectral-truncation slice is discharged by
`orthonormalizationSpectralProducer_of_sourceAlmostProjective`; hence the
remaining orthonormalization hypothesis is exactly the QXP repair producer with
fresh-outcome residual domination. -/
lemma selfImprovementWithCanonicalOptimalPairAndQXPResidualDomination
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (heps_le_one : eps ≤ 1)
    (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params
      (matrixSdpPointRealizationOfStrategy params strategy)))
    (Z : MIPStarRE.Quantum.Op ι)
    (hsdp : MatrixSdpCanonicalOptimalPairWithDominance params
      (matrixSdpPointRealizationOfStrategy params strategy) X Z)
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
    (hqxp :
      OrthonormalizationQXPLayerRepairProducerWithResidualDomination
        params strategy eps delta) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu :=
  selfImprovementWithCanonicalOptimalPairSdpSlacknessAndResidualDominationInput
    params strategy eps delta gamma nu heps_le_one hdelta_le_one hd_le_q
    X Z hsdp hgood G hhelperCompleteness hhelperSSCInput htransfer
    (orthonormalizationResidualDominationInput_of_sourceAlmostProjectiveAndQXPLayerRepair
      hqxp)

/-- A canonical optimal pair, an ordinary QXP repair producer, and a separate
fresh-outcome residual-domination proof assemble a full self-improvement
conclusion. -/
lemma selfImprovementWithCanonicalOptimalPairAndQXPRepairAndResidualDomination
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (heps_le_one : eps ≤ 1)
    (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params
      (matrixSdpPointRealizationOfStrategy params strategy)))
    (Z : MIPStarRE.Quantum.Op ι)
    (hsdp : MatrixSdpCanonicalOptimalPairWithDominance params
      (matrixSdpPointRealizationOfStrategy params strategy) X Z)
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
    (hdom : ∀ {Hhat : SubMeas (Polynomial params) ι}
      (hssc : BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta))
      (hSpectral : SpectralTruncationStatement strategy.state
        (leftLiftedMeasurement (ιB := ι) (optionCompletion Hhat))
        (consistencyToAlmostProjectiveError
          (2 * selfImprovementHelperError params eps delta))),
        QXPLayerResidualDomination (hqxp hssc hSpectral).data Hhat) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu :=
  selfImprovementWithCanonicalOptimalPairAndQXPResidualDomination
    params strategy eps delta gamma nu heps_le_one hdelta_le_one hd_le_q
    X Z hsdp hgood G hhelperCompleteness hhelperSSCInput htransfer
    (residualDominatingRepairProducer_of_qxpLayer_and_residualDomination hqxp hdom)

end MIPStarRE.LDT.SelfImprovement
