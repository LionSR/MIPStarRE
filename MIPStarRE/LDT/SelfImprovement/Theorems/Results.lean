import MIPStarRE.LDT.GlobalVariance.Theorems.Results
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization
import MIPStarRE.LDT.Preliminaries.SelfConsistency.DataProcessing
import MIPStarRE.LDT.SelfImprovement.Theorems.Statements

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.maxHeartbeats false

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Reduced theorem wrappers -/

private lemma averagedPointOperator_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params) :
    averagedPointOperator params strategy g ≤ 1 := by
  let A : SubMeas Unit ι :=
    averageUnitSubMeas (ι := ι)
      (pointConditionedOutcomeOperatorAtPolynomial params strategy g)
      (fun u => by
        simpa [pointConditionedOutcomeOperatorAtPolynomial] using
          (strategy.pointMeasurement u).outcome_pos (g u))
      (fun u => by
        simpa [pointConditionedOutcomeOperatorAtPolynomial] using
          Measurement.outcome_le_one (strategy.pointMeasurement u).toMeasurement (g u))
  simpa [A, averagedPointOperator, averageUnitSubMeas_outcome] using A.outcome_le_one ()

private lemma bipartiteSSCRel_uniform_const
    {Question Outcome : Type*}
    [Fintype Question] [DecidableEq Question] [Nonempty Question]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (A : SubMeas Outcome ι) (δ : Error) :
    BipartiteSSCRel ψ (uniformDistribution Unit) (constSubMeasFamily A) δ →
      BipartiteSSCRel ψ (uniformDistribution Question) (fun _ : Question => A) δ := by
  intro hssc
  rcases hssc with ⟨hssc⟩
  constructor
  simpa [bipartiteSSCError, avgOver, uniformDistribution, constSubMeasFamily] using hssc

private lemma sddRel_uniform_const
    {κ Question Outcome : Type*}
    [Fintype κ] [DecidableEq κ]
    [Fintype Question] [DecidableEq Question] [Nonempty Question]
    [Fintype Outcome]
    (ψ : QuantumState κ)
    (A B : SubMeas Outcome κ) (δ : Error) :
    SDDRel ψ (uniformDistribution Unit) (constSubMeasFamily A) (constSubMeasFamily B) δ →
      SDDRel ψ (uniformDistribution Question) (fun _ : Question => A) (fun _ : Question => B) δ := by
  intro hsdd
  rcases hsdd with ⟨hsdd⟩
  constructor
  simpa [sddError, avgOver, uniformDistribution, constSubMeasFamily] using hsdd

/-- Reduced version of `lem:sdp`.

This reduced wrapper now instantiates the paper's explicit Slater witnesses: the
primal uses the uniform strict-feasible submeasurement
`T_g = (2 |\polyfunc{m}{q}{d}|)^{-1} I`, canonically completed at the zero
polynomial to fit the downstream `Measurement` interface, and the dual uses
`Z = 2I`. The paper's strong-duality and complementary-slackness conclusions are
still omitted from the current Lean statement. -/
lemma sdp
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) :
    SdpStatement params strategy := by
  let T : Measurement (Polynomial params) ι := sdpPrimalWitness (ι := ι) params
  let Z : MIPStarRE.Quantum.Op ι := sdpStrictDualWitness (ι := ι)
  refine ⟨T.toSubMeas, Z, ?_⟩
  refine
    { primalTotalOperator := T.total_eq_one
      dualPositive := by
        simp [Z]
      dualFeasible := ?_ }
  intro g
  simpa [Z, sdpDualSlackOperator] using
    sub_nonneg.mpr
      (le_trans (averagedPointOperator_le_one params strategy g)
        (one_le_sdpStrictDualWitness (ι := ι)))

/-- Reduced version of `lem:add-in-u`.

This currently keeps only the global-variance consequence used downstream. It
now derives that consequence from the post-triangle six-step edge-transport
chain bound via `globalVarianceOfPointsFromTransportChainBound`. The `gamma` and
`hgood` arguments are intentionally retained so this reduced wrapper still
matches the surrounding self-improvement API and can be strengthened back to the
full paper statement without another caller-wide signature change. The
selection-dependent transfer inequality from the paper, together with its
dependence on an auxiliary family `M` and the averaged family `H`, is not yet
formalized here. -/
lemma addInU
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (T : Measurement (Polynomial params) ι)
    (hlocalChain :
      ∀ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T.toSubMeas g ≤
          localVarianceTransportChainError params eps delta) :
    AddInUStatement params strategy T eps delta := by
  refine
    { varianceBound := ?_ }
  let hglobalVariance :=
    globalVarianceOfPointsFromTransportChainBound params strategy eps delta gamma hgood
      T.toSubMeas hlocalChain
  simpa [selfImprovementVarianceError] using
    hglobalVariance.averagedGlobalVarianceBound

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
    (hglobalVarianceProofInputs : GlobalVarianceProofInputs params strategy eps delta)
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
      addInUVarianceBound := ?_
      positiveSemidefiniteWitness := hsdp.dualPositive
      dualDominatesAveragedPoint := hsdp.dualFeasible }
  · simpa [T] using hsdp
  · have hlocalChain := hglobalVarianceProofInputs T
    -- This is the remaining surfaced GlobalVariance analytic obligation. The
    -- algebraic local-to-global reduction is now formalized in
    -- `globalVarianceOfPointsFromTransportChainBound`.
    exact addInU params strategy eps delta gamma hgood T hlocalChain

set_option maxHeartbeats 800000 in
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
    (hglobalVarianceProofInputs : GlobalVarianceProofInputs params strategy eps delta)
    (hhelperStrongSelfConsistency :
      HelperStrongSelfConsistencyInput params strategy eps delta)
    (horthonormalization : OrthonormalizationInput params strategy eps delta)
    (hfinalFields : FinalFieldsInput params strategy eps delta nu)
    (hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (Polynomial params) ι) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu := by
  rcases selfImprovementHelper params strategy eps delta gamma hgood nu
      hglobalVarianceProofInputs G with
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
  refine ⟨H, Z, ?_⟩
  exact
    { witness := ⟨T, Hhat, hhelper, horth, hdata⟩
      completeness := hfinal.completeness
      pointConsistency := hfinal.pointConsistency
      selfCloseness := hfinal.selfCloseness
      positiveSemidefiniteWitness := hhelper.positiveSemidefiniteWitness
      dualDominatesAveragedPoint := hhelper.dualDominatesAveragedPoint
      projectiveResidualBound := hfinal.projectiveResidualBound
      bounded := hfinal.bounded }

set_option maxHeartbeats 800000 in
/--
Bridge from the measurement-input version in `self_improvement.tex` to the
submeasurement-input version used in `inductive_step.tex`.
-/
theorem selfImprovementFromSubMeas
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (hglobalVarianceProofInputs : GlobalVarianceProofInputs params strategy eps delta)
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
      hglobalVarianceProofInputs hhelperStrongSelfConsistency
      horthonormalization hfinalFields hgood Gmeas
      with ⟨H, Z, hH⟩
  refine ⟨H, Z, ?_⟩
  exact
    { measurementBridge := ⟨Gmeas, hbridge, hH⟩ }

end MIPStarRE.LDT.SelfImprovement
