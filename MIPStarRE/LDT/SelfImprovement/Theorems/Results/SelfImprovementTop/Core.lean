import MIPStarRE.LDT.Basic.SubMeasurementFamilies
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization
import MIPStarRE.LDT.Preliminaries.SelfConsistency.DataProcessing
import MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds
import MIPStarRE.LDT.SelfImprovement.Theorems.Statements
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.CommonHelpers
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.HelperCompleteness
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.BoundednessTransport
import MIPStarRE.LDT.SelfImprovement.Theorems.AddInUFullStatement

/-!
# Self-improvement theorem variants

The main `selfImprovementHelper`, the `selfImprovement` theorem corresponding
to `thm:self-improvement` in the blueprint, and variants with the
orthonormalization and final-fields conditions taken as explicit hypotheses.

## Contents

- **selfImprovementHelperConstruction** — construction lemma producing `T`, `Ĥ`,
  `Z` and `SelfImprovementHelperConclusion` from `sdp` + `addInU`.
- **selfImprovementHelper** — `lem:self-improvement-helper`, with the paper's
  input consistency hypothesis and four helper conclusions.
- **self_improvement_helper_with_slackness** — companion helper producing the
  slackness-carrying helper conclusion from the Section 9 SDP statement.
- **selfImprovement_assumingFinalFields** — form of `thm:self-improvement` with
  helper strong self-consistency, orthonormalization, and final-fields
  conditions taken as explicit hypotheses.
- **selfImprovement** — the statement corresponding to `thm:self-improvement`.
- **selfImprovementFromObligations** — measurement-level conditional helper
  with the remaining Section 9 proof obligations supplied explicitly.

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

/-- Construction lemma for the SDP and add-in-`u` stage of
`lem:self-improvement-helper`.

This lemma records the construction of the SDP measurement `T`, the averaged
sandwiched submeasurement `H`, and the dual witness `Z`. The paper's consistency
hypothesis for the input measurement is not needed for these three constructed
objects; it is used by `selfImprovementHelper` to prove the four helper
conclusions. -/
lemma selfImprovementHelperConstruction
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (_nu : Error)
    -- These arguments keep this construction lemma aligned with the helper
    -- theorem; the constructed SDP measurement is independent of `G`.
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

/-- Conditional form of the helper lemma from a slackness-carrying SDP
conclusion.

This is the companion to `selfImprovementHelper` when the Section 9
strong-duality conclusion has already been supplied as
`SdpStatementWithSlackness`.  The helper output therefore carries the
complementary-slackness equations needed by the helper-completeness chain. -/
lemma self_improvement_helper_with_slackness_of_sdp_statement_with_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hsdp : SdpStatementWithSlackness params strategy)
    (hgood : strategy.IsGood eps delta gamma)
    (_nu : Error)
    -- These arguments keep the slackness-carrying conclusion aligned with the
    -- helper theorem; the constructed SDP measurement is independent of `G`.
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

/-- Helper lemma driven by the Section 9 SDP statement with complementary
slackness.

This is the slackness-carrying companion to `selfImprovementHelperConstruction`:
it applies the Section 9 statement `sdp_statement_with_slackness`, which records
the strong-duality conclusion with complementary slackness.  The construction
lemma remains separate, because its current `sdp` input has not yet formalized
the strong-duality argument. -/
lemma self_improvement_helper_with_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (nu : Error)
    (G : Measurement (Polynomial params) ι) :
    ∃ T : Measurement (Polynomial params) ι,
      ∃ H : SubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
        SelfImprovementHelperConclusionWithSlackness params strategy T H Z eps delta :=
  self_improvement_helper_with_slackness_of_sdp_statement_with_slackness
    params strategy eps delta gamma (sdp_statement_with_slackness params strategy)
    hgood nu G

/-- Paper origin: `references/ldt-paper/self_improvement.tex:24-60`
(`\label{lem:self-improvement-helper}`).

Self-improvement helper lemma for a polynomial measurement `G` consistent with
the point measurement. It produces a polynomial submeasurement `H` and a
positive semidefinite witness `Z` satisfying the four conclusions of the paper:
completeness, consistency with `A`, strong self-consistency, and boundedness.
The boundedness conclusion is split into positivity of `Z`, pointwise domination
of the averaged point measurement, and the state-dependent gap estimate. -/
lemma selfImprovementHelper
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (nu : Error)
    (G : Measurement (Polynomial params) ι)
    (hcons :
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas) nu) :
    ∃ H : SubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementHelperStatement params strategy H Z eps delta nu := by
  rcases self_improvement_helper_with_slackness params strategy eps delta gamma
      hgood nu G with
    ⟨T, Hhat, Z, hhelperWithSlackness⟩
  let hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta :=
    hhelperWithSlackness.toHelperConclusion
  have heps : 0 ≤ eps := eps_nonneg_of_isGood params strategy hgood
  have hdelta : 0 ≤ delta := delta_nonneg_of_isGood params strategy hgood
  have hpointSSC :
      BipartiteSSCRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta := by
    exact ⟨by
      simpa [SymStrat.selfConsistencyFailureProbability] using
        hgood.selfConsistencyTest⟩
  have haddInUFull : AddInUFullStatement params strategy T eps delta :=
    addInUFullStatement_of_isGood params strategy eps delta gamma hgood T
  have hpointTransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          Hhat
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T.toSubMeas
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta := by
    have htransfer :=
      haddInUFull.selectionDependentTransfer
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (pointConsistencyAddInUSelection params)
    simpa [hhelper.averagedConstruction] using htransfer
  refine ⟨Hhat, Z, ?_⟩
  refine
    { completeness := ?_
      pointConsistency := ?_
      strongSelfConsistency := ?_
      positiveSemidefiniteWitness := hhelper.sdpWitness.dualPositive
      dualDominatesAveragedPoint := hhelper.sdpWitness.dualFeasible
      boundednessGap := ?_ }
  · exact
      helper_completeness_of_self_consistency_helper_slackness_input_consistency
        params strategy G eps delta nu heps hdelta hhelperWithSlackness hpointSSC hcons
  · exact
      helper_point_consistency_of_pointConsistencyAddInU_transfer
        params strategy eps delta heps hdelta hpointTransfer
  · /- TODO(#1514): Derive `HelperStrongSelfConsistencyObligations` for the
      helper output from the Section 9 scalar transport estimates, then prove this
      condition with `helper_strong_self_consistency_of_helper_conclusion` or
      `helper_strong_self_consistency_input_of_obligations`.

      This route currently uses the five estimates required by
      the scalar-transport constructor for
      `HelperStrongSelfConsistencyObligations`:
      the two off-diagonal variance swaps, the two post-`delete-an-A` transports,
      and the final lower bound on the `move-over-v` endpoint.  Its final
      absorption also uses the small-error condition `(params.d : Error) ≤
      (params.q : Error)`.  This boundary must be justified from the paper
      hypotheses or handled by a separate saturated-error branch; it should not be
      added as an extra hypothesis to `selfImprovementHelper`. -/
    sorry
  · exact
      helper_boundedness_gap_le_selfImprovementHelperError_of_helper_outputs
        params strategy eps delta heps hdelta hhelper hpointSSC
        (fun h => (hhelperWithSlackness.complementarySlackness h).symm)
        hpointTransfer

/-- Form of `thm:self-improvement` with helper strong self-consistency,
orthonormalization, and final-fields conditions taken as explicit hypotheses.

This is not the statement corresponding to `thm:self-improvement` in the
blueprint. It assumes the helper strong self-consistency input, the
orthonormalization input, and the final-fields input explicitly. The
evaluation-map data-processing step follows from the question-dependent
preliminaries theorem.

**Unfaithful:** this helper is conditional on proof-stage inputs that the paper
does not assume.  The source-facing theorem `selfImprovement` must derive these
inputs from the paper hypotheses; that proof obligation is tracked by #1515. -/
theorem selfImprovement_assumingFinalFields
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
  rcases selfImprovementHelperConstruction params strategy eps delta gamma hgood nu
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
  rcases orthonormalization_ofInput
      strategy.state strategy.permInvState strategy.isNormalized
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
Formal statement corresponding to the blueprint theorem `thm:self-improvement`,
with the input consistency hypothesis from the LDT paper.

The theorem assumes a measurement `G` whose polynomial evaluation family is
consistent with the point measurement at error `nu`. It must produce a
projective polynomial submeasurement satisfying the four self-improvement
conclusions. The paper and blueprint impose the `(eps, delta, gamma)`-good
strategy condition as a standing hypothesis for the self-improvement section
(`blueprint/src/chapter/ch07_self_improvement.tex`, line 4); Lean records it
here as the explicit hypothesis `hgood`. The theorem
`selfImprovement_assumingFinalFields` records the conditional form currently
proved in Lean, in which helper strong self-consistency, orthonormalization, and
final-fields conditions are explicit hypotheses. These conditions are missing
derivations, not hypotheses of the blueprint theorem.
-/
theorem selfImprovement
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (Polynomial params) ι)
    (hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu := by
  -- TODO(#1515): derive the helper strong self-consistency,
  -- orthonormalization, and final-fields inputs from the paper hypotheses,
  -- including the incoming consistency hypothesis `hcons`, then invoke
  -- `selfImprovement_assumingFinalFields`.
  sorry

/-- `SelfImprovementObligations` + `IsGood` is sufficient to call the form of
`thm:self-improvement` with explicit orthonormalization and final-fields
hypotheses and obtain the full `SelfImprovementConclusion`.

**Unfaithful:** this helper assumes `SelfImprovementObligations`, whose helper
strong self-consistency, orthonormalization, and final-fields components are not
yet derived from the hypotheses of `thm:self-improvement`.  This proof debt is
tracked by #1515.  Elimination: prove the source-facing `selfImprovement`
theorem from the paper hypotheses. -/
theorem selfImprovementFromObligations
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (obligations : SelfImprovementObligations params strategy eps delta nu)
    (hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (Polynomial params) ι) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu :=
  selfImprovement_assumingFinalFields params strategy eps delta gamma nu
    obligations.helperStrongSelfConsistency
    obligations.orthonormalization obligations.finalFields hgood G


end MIPStarRE.LDT.SelfImprovement
