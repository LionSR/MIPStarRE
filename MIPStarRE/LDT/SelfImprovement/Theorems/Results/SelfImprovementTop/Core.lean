import MIPStarRE.LDT.Basic.SubMeasurementFamilies
import MIPStarRE.LDT.GlobalVariance.Theorems.Results
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain
import MIPStarRE.LDT.Preliminaries.SelfConsistency.DataProcessing
import MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds
import MIPStarRE.LDT.SelfImprovement.Theorems.Statements
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.CommonHelpers
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.HelperCompleteness
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.BoundednessTransport

/-!
# Self-improvement theorem wrappers

The main `selfImprovementHelper` and `selfImprovement` theorems,
and the bridge-input variants used to enter the self-improvement theorem.

## Contents

- **selfImprovementHelper** — reduced helper producing `T`, `Ĥ`, `Z` and
  `SelfImprovementHelperConclusion` from `sdp` + `addInU`.
- **selfImprovementHelperWithSlackness** — companion helper producing the
  slackness-carrying helper conclusion from an SDP statement whose witnesses
  already include complementary slackness.
- **selfImprovement** — `thm:self-improvement`: assembles the full
  pipeline (helper SSC → orthonormalization → data processing →
  final fields) to produce `SelfImprovementConclusion`.
- **selfImprovementFromSubMeas / selfImprovementFromBridgeInputs /
  selfImprovementFromBridgeInputsSubMeas** — bridge-input variants for
  submeasurement and packaged-bridge interfaces.

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

/-- A good strategy has a nonnegative final self-improvement error threshold. -/
lemma selfImprovementError_nonneg_of_isGood
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    {eps delta gamma : Error}
    (hgood : strategy.IsGood eps delta gamma) :
    0 ≤ selfImprovementError params eps delta := by
  have heps : 0 ≤ eps := eps_nonneg_of_isGood params strategy hgood
  have hdelta : 0 ≤ delta := delta_nonneg_of_isGood params strategy hgood
  have hm_nonneg : (0 : Error) ≤ (params.m : Error) := by
    exact_mod_cast Nat.zero_le params.m
  have hd_nonneg : (0 : Error) ≤ (params.d : Error) := by
    exact_mod_cast Nat.zero_le params.d
  have hq_nonneg : (0 : Error) ≤ (params.q : Error) := le_of_lt params.q_cast_pos
  have hdq_nonneg : (0 : Error) ≤ (params.d : Error) / (params.q : Error) :=
    div_nonneg hd_nonneg hq_nonneg
  have hsum_nonneg :
      0 ≤ Real.rpow eps (1 / (32 : Error)) +
          Real.rpow delta (1 / (32 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (32 : Error)) := by
    exact add_nonneg
      (add_nonneg (Real.rpow_nonneg heps _) (Real.rpow_nonneg hdelta _))
      (Real.rpow_nonneg hdq_nonneg _)
  unfold selfImprovementError MainInductionStep.selfImprovementInInductionError
  exact mul_nonneg (mul_nonneg (by norm_num) hm_nonneg) hsum_nonneg

/-- Reduced version of `lem:self-improvement-helper`.

Unlike the paper helper lemma, this theorem does not yet take the consistency
error `nu` or a hypothesis `hcons`. The current
`SelfImprovementHelperConclusion` only packages the outputs produced directly by
the reduced `sdp` + `addInU` pipeline, and those facts do not depend on the
consistency hypothesis. The `nu`-dependent consistency information will be
threaded back in when the full pipeline is assembled in `selfImprovement`. -/
lemma selfImprovementHelper
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (_nu : Error)
    -- Kept for API compatibility with the full helper statement, where future
    -- proof obligations will depend on the incoming polynomial measurement.
    (_G : Measurement (Polynomial params) ι) :
    ∃ T : Measurement (Polynomial params) ι,
      ∃ H : SubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
        SelfImprovementHelperConclusion params strategy T H Z eps delta := by
  obtain ⟨Tsub, Z, hsdp⟩ := (sdp params strategy).witness
  let T : Measurement (Polynomial params) ι :=
    { toSubMeas := Tsub
      total_eq_one := hsdp.primalTotalOperator }
  let Hhat : SubMeas (Polynomial params) ι :=
    averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas
  refine ⟨T, Hhat, Z, ?_⟩
  refine
    { sdpWitness := ?_
      averagedConstruction := rfl
      addInUVarianceBound := ?_ }
  · simpa [T] using hsdp
  · exact addInU params strategy eps delta gamma hgood T

/-- Helper lemma driven by an SDP statement carrying complementary slackness.

This is the paper-facing companion to `selfImprovementHelper`: if the SDP
stage supplies the strong-duality conclusion recorded in
`SdpStatementWithSlackness`, then the helper output also carries the
complementary-slackness equations needed by the helper-completeness chain. The
reduced theorem `selfImprovementHelper` remains separate, because its current
`sdp` input has not yet formalized the strong-duality argument. -/
lemma selfImprovementHelperWithSlackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hsdp : SdpStatementWithSlackness params strategy)
    (hgood : strategy.IsGood eps delta gamma)
    (_nu : Error)
    -- Kept for API compatibility with the full helper statement, where future
    -- proof obligations will depend on the incoming polynomial measurement.
    (_G : Measurement (Polynomial params) ι) :
    ∃ T : Measurement (Polynomial params) ι,
      ∃ H : SubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
        SelfImprovementHelperConclusionWithSlackness params strategy T H Z eps delta := by
  obtain ⟨Tsub, Z, hsdpPair⟩ := hsdp.witness
  let T : Measurement (Polynomial params) ι :=
    { toSubMeas := Tsub
      total_eq_one := hsdpPair.toSdpOptimalPair.primalTotalOperator }
  let Hhat : SubMeas (Polynomial params) ι :=
    averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas
  refine ⟨T, Hhat, Z, ?_⟩
  refine
    { toHelperConclusion := ?_
      complementarySlackness := ?_ }
  · refine
      { sdpWitness := ?_
        averagedConstruction := rfl
        addInUVarianceBound := ?_ }
    · simpa [T] using hsdpPair.toSdpOptimalPair
    · exact addInU params strategy eps delta gamma hgood T
  · intro g
    simpa [T] using hsdpPair.complementarySlackness g

/-- `thm:self-improvement`.

The remaining Section 5/8/9 obligations are exposed as explicit theorem
hypotheses, rather than bundled behind a dedicated bridge-package structure. The
evaluation-map data-processing step is now discharged internally using the
question-dependent preliminaries theorem. -/
theorem selfImprovement
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (hhelperStrongSelfConsistency :
      HelperStrongSelfConsistencyInput params strategy eps delta)
    (horthonormalization : OrthonormalizationInput params strategy eps delta)
    (hfinalFields : FinalFieldsInput params strategy eps delta nu)
    (hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (Polynomial params) ι) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu := by
  rcases selfImprovementHelper params strategy eps delta gamma hgood nu
      G with
    ⟨T, Hhat, Z, hhelper⟩
  have hssc :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta) :=
    hhelperStrongSelfConsistency hhelper
  have horthBridge :
      MakingMeasurementsProjective.OrthonormalizationInput strategy.state Hhat
        (selfImprovementHelperError params eps delta) :=
    horthonormalization hssc
  rcases orthonormalization strategy.state strategy.permInvState strategy.isNormalized
      Hhat
      (selfImprovementHelperError params eps delta)
      hssc horthBridge with ⟨H, horth⟩
  have hsscPoint :
      BipartiteSSCRel strategy.state
        (uniformDistribution (Point params))
        (fun _ : Point params => Hhat)
        (selfImprovementHelperError params eps delta) :=
    bipartiteSSCRel_uniform_const strategy.state Hhat
      (selfImprovementHelperError params eps delta) hssc
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
  have hfinal :
      SelfImprovementFinalFields params strategy H Z eps delta nu :=
    hfinalFields hhelper horth hdata
  have hselfImprovementError_nonneg :
      0 ≤ selfImprovementError params eps delta :=
    selfImprovementError_nonneg_of_isGood params strategy hgood
  refine ⟨H, Z, ?_⟩
  exact
    { witness := ⟨T, Hhat, hhelper, horth, hdata⟩
      completeness := hfinal.completeness
      pointConsistency := hfinal.pointConsistency
      selfCloseness := hfinal.selfCloseness
      positiveSemidefiniteWitness := hhelper.sdpWitness.dualPositive
      dualDominatesAveragedPoint := hhelper.sdpWitness.dualFeasible
      projectiveResidualBound := hfinal.projectiveResidualBound
      bounded :=
        final_fields_bounded strategy.state H.toSubMeas hhelper.sdpWitness.dualDominatesIdentity
          hselfImprovementError_nonneg }

/--
Bridge from the measurement-input version in `self_improvement.tex` to the
submeasurement-input version used in `inductive_step.tex`.
-/
theorem selfImprovementFromSubMeas
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (hhelperStrongSelfConsistency :
      HelperStrongSelfConsistencyInput params strategy eps delta)
    (horthonormalization : OrthonormalizationInput params strategy eps delta)
    (hfinalFields : FinalFieldsInput params strategy eps delta nu)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (Gmeas : Measurement (Polynomial params) ι)
    (hbridge : Gmeas.toSubMeas = G) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementSubMeasConclusion params strategy G H Z
        eps delta gamma nu := by
  rcases selfImprovement params strategy eps delta gamma nu
      hhelperStrongSelfConsistency
      horthonormalization hfinalFields hgood Gmeas
      with ⟨H, Z, hH⟩
  refine ⟨H, Z, ?_⟩
  exact
    { measurementBridge := ⟨Gmeas, hbridge, hH⟩ }

/-- `SelfImprovementBridgeInputs` + `IsGood` is sufficient to call
`selfImprovement` and obtain the full `SelfImprovementConclusion`. -/
theorem selfImprovementFromBridgeInputs
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (hbridge : SelfImprovementBridgeInputs params strategy eps delta nu)
    (hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (Polynomial params) ι) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu :=
  selfImprovement params strategy eps delta gamma nu
    hbridge.helperStrongSelfConsistency
    hbridge.orthonormalization hbridge.finalFields hgood G

/-- `SelfImprovementBridgeInputs` + `IsGood` also suffice for the
submeasurement-input interface used by Section 6, once a measurement completion
of the input submeasurement is supplied explicitly. -/
theorem selfImprovementFromBridgeInputsSubMeas
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (hinputs : SelfImprovementBridgeInputs params strategy eps delta nu)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (Gmeas : Measurement (Polynomial params) ι)
    (hbridge : Gmeas.toSubMeas = G) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementSubMeasConclusion params strategy G H Z
        eps delta gamma nu :=
  selfImprovementFromSubMeas params strategy eps delta gamma nu
    hinputs.helperStrongSelfConsistency
    hinputs.orthonormalization hinputs.finalFields hgood G Gmeas hbridge


end MIPStarRE.LDT.SelfImprovement
