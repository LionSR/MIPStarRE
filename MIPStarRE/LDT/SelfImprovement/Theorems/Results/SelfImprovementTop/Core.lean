import MIPStarRE.LDT.Basic.SubMeasurementFamilies
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization
import MIPStarRE.LDT.Preliminaries.SelfConsistency.DataProcessing
import MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds
import MIPStarRE.LDT.SelfImprovement.Theorems.Statements
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.CommonHelpers
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.HelperCompleteness
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.HelperSSC
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.BoundednessTransport
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.SelfImprovementTop.FinalFields
import MIPStarRE.LDT.SelfImprovement.Theorems.AddInUFullStatement

/-!
# Self-improvement theorem variants

The main `selfImprovementHelper` and the `selfImprovement` theorem corresponding
to `thm:self-improvement` in the blueprint.

## Contents

- **selfImprovementHelperConstruction** — construction lemma producing `T`, `Ĥ`,
  `Z` and `SelfImprovementHelperConclusion` from `sdp` + `addInU`.
- **selfImprovementHelper** — `lem:self-improvement-helper`, with the paper's
  input consistency hypothesis and four helper conclusions.
- **self_improvement_helper_with_slackness** — companion helper producing the
  slackness-carrying helper conclusion from the Section 9 SDP statement.
- **selfImprovement** — the statement corresponding to `thm:self-improvement`.

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
  obtain ⟨Tsub, Z, hsdp⟩ := (sdp (ι := ι) params strategy).witness
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
  · exact addInU (ι := ι) params strategy eps delta gamma hgood T

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
    · exact addInU (ι := ι) params strategy eps delta gamma hgood T
  · intro g
    simpa [T] using hsdpPair.complementarySlackness g

/-- Helper lemma driven by the Section 9 SDP statement with complementary
slackness.

This is the slackness-carrying companion to `selfImprovementHelperConstruction`:
it applies the Section 9 statement `sdp_statement_with_slackness`, which records
the strong-duality conclusion with complementary slackness.  The construction
lemma remains separate from `selfImprovementHelperConstruction`, whose reduced
`sdp` input records only the feasibility fragment. -/
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
    params strategy eps delta gamma
    (sdp_statement_with_slackness (ι := ι) params strategy)
    hgood nu G

/-- Paper origin: `references/ldt-paper/self_improvement.tex:24-60`
(`\label{lem:self-improvement-helper}`).

Self-improvement helper lemma for a polynomial measurement `G` consistent with
the point measurement. It produces a polynomial submeasurement `H` and a
positive semidefinite witness `Z` satisfying the four conclusions of the paper:
completeness, consistency with `A`, strong self-consistency, and boundedness.
The boundedness conclusion is split into positivity of `Z`, pointwise domination
of the averaged point measurement, and the state-dependent gap estimate.  The
strong-self-consistency branch is proved in this file and is not exposed as an
additional public hypothesis. -/
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
    addInUFullStatement_of_isGood (ι := ι) params strategy eps delta gamma hgood T
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
  · by_cases hd_le_q : (params.d : Error) ≤ (params.q : Error)
    · have hlocal :
          (∑ g : Polynomial params,
            localVarianceDeviationAtPolynomial params strategy strategy.state T.toSubMeas g) ≤
            localVarianceOfPointsError params eps delta :=
        localVarianceDeviation_sum_le_localVarianceOfPointsError
          params strategy eps delta gamma hgood T.toSubMeas
      have hclone :
          |helperDeleteAQuantity params strategy T.toSubMeas -
            helperDeleteAClonedQuantity params strategy T.toSubMeas| ≤
              Real.sqrt (selfImprovementVarianceError params eps delta) :=
        helperDeleteAQuantity_abs_sub_clonedQuantity_le_sqrt
          params strategy eps delta T.toSubMeas hlocal
      have hmove :
          |helperDeleteAClonedQuantity params strategy T.toSubMeas -
            helperMoveOverVQuantity params strategy T.toSubMeas| ≤
              Real.sqrt (2 * delta) :=
        helperDeleteAClonedQuantity_abs_sub_moveOverVQuantity_le_sqrt_two_delta
          params strategy delta T.toSubMeas hpointSSC
      have hsscObligations :
          HelperStrongSelfConsistencyObligations params strategy T Hhat eps delta :=
        helper_ssc_obligations_of_scalarTransports_pointTransfer
          params strategy eps delta hhelper hpointSSC hlocal hclone hmove
          (fun h => helper_slackness_eq_of_helper_with_slackness
            params strategy eps delta hhelperWithSlackness h)
          hpointTransfer
      exact
        helper_strong_self_consistency_of_helper_conclusion
          params strategy eps delta heps hdelta hd_le_q hhelper hsscObligations
    · have hhelperError_ge_one : 1 ≤ selfImprovementHelperError params eps delta := by
        have hdq_ge_one : 1 ≤ ((params.d : Error) / (params.q : Error)) := by
          exact (one_le_div₀ params.q_cast_pos).2 (le_of_lt (lt_of_not_ge hd_le_q))
        have hsqrt_dq_ge_one : 1 ≤ Real.sqrt ((params.d : Error) / (params.q : Error)) := by
          have hdq_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) :=
            d_q_ratio_nonneg params
          have hsqrt_nonneg : 0 ≤ Real.sqrt ((params.d : Error) / (params.q : Error)) :=
            Real.sqrt_nonneg _
          have hsq :
              Real.sqrt ((params.d : Error) / (params.q : Error)) *
                Real.sqrt ((params.d : Error) / (params.q : Error)) =
                ((params.d : Error) / (params.q : Error)) := by
            simpa [sq] using Real.sq_sqrt hdq_nonneg
          nlinarith
        have hsqrt_eps_nn : 0 ≤ Real.sqrt eps := Real.sqrt_nonneg _
        have hsqrt_delta_nn : 0 ≤ Real.sqrt delta := Real.sqrt_nonneg _
        rw [selfImprovementHelperError_eq]
        nlinarith [one_le_m_cast params, hsqrt_dq_ge_one, hsqrt_eps_nn, hsqrt_delta_nn]
      have hmatch_nonneg : 0 ≤ qBipartiteMatchMass strategy.state Hhat Hhat := by
        unfold qBipartiteMatchMass
        exact Finset.sum_nonneg fun h _ =>
          ev_nonneg_of_psd strategy.state _ <|
            opTensor_nonneg (Hhat.outcome_pos h) (Hhat.outcome_pos h)
      have hmass_le_one : subMeasMass strategy.state Hhat.liftLeft ≤ 1 := by
        unfold subMeasMass SubMeas.liftLeft
        have hle : leftTensor (ι₂ := ι) Hhat.total ≤
            (1 : MIPStarRE.Quantum.Op (ι × ι)) :=
          leftTensor_le_one (ι₂ := ι) Hhat.total_le_one
        simpa [ev_one_of_isNormalized strategy.state strategy.isNormalized] using
          ev_mono strategy.state _ _ hle
      have hssc_defect_le_one : qBipartiteSSCDefect strategy.state Hhat ≤ 1 := by
        unfold qBipartiteSSCDefect
        have hinner :
            subMeasMass strategy.state Hhat.liftLeft -
                qBipartiteMatchMass strategy.state Hhat Hhat ≤ 1 := by
          linarith
        exact max_le_iff.mpr ⟨by positivity, hinner⟩
      have hssc_le_one :
          bipartiteSSCError strategy.state (uniformDistribution Unit)
            (constSubMeasFamily Hhat) ≤ 1 := by
        simpa [bipartiteSSCError, avgOver, uniformDistribution, constSubMeasFamily] using
          hssc_defect_le_one
      exact ⟨le_trans hssc_le_one hhelperError_ge_one⟩
  · exact
      helper_boundedness_gap_le_selfImprovementHelperError_of_helper_outputs
        params strategy eps delta heps hdelta hhelper hpointSSC
        (fun h => (hhelperWithSlackness.complementarySlackness h).symm)
        hpointTransfer

/-- Internal large-error fallback for `selfImprovement`.

When the literal threshold `selfImprovementError` is at least `1`, the paper
conclusion is trivial: take the zero projective submeasurement and the identity
dual witness. -/
lemma selfImprovement_of_error_ge_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (_hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (Polynomial params) ι)
    (herror_ge_one : 1 ≤ selfImprovementError params eps delta)
    (hnu_nonneg : 0 ≤ nu) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu := by
  let H : ProjSubMeas (Polynomial params) ι := zeroProjSubMeas
  let Z : MIPStarRE.Quantum.Op ι := 1
  have herror_nonneg : 0 ≤ selfImprovementError params eps delta := by
    linarith
  refine ⟨H, Z, ?_⟩
  refine
    { completeness := ?_
      pointConsistency := ?_
      selfCloseness := ?_
      positiveSemidefiniteWitness := ?_
      dualDominatesAveragedPoint := ?_
      projectiveResidualBound := ?_ }
  · refine ⟨?_⟩
    have hbound : (1 - nu) - selfImprovementError params eps delta ≤ 0 := by
      linarith
    have hmass_zero : subMeasMass strategy.state H.toSubMeas.liftLeft = 0 := by
      simp [H, subMeasMass, zeroProjSubMeas, SubMeas.liftLeft, leftTensor,
        ev_zero]
    rw [hmass_zero]
    linarith
  · exact
      ConsRel.mono herror_ge_one
        ⟨bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          (polynomialEvaluationFamily params H.toSubMeas)⟩
  · refine ⟨?_⟩
    have hsdd_zero :
        sddError strategy.state (uniformDistribution Unit)
          (constSubMeasFamily (leftPlacedSubMeas (ιB := ι) H.toSubMeas))
          (constSubMeasFamily (rightPlacedSubMeas (ιA := ι) H.toSubMeas)) = 0 := by
      simp [H, zeroProjSubMeas, constSubMeasFamily, leftPlacedSubMeas,
        rightPlacedSubMeas, sddError, avgOver, uniformDistribution, qSDD,
        qSDDCore, leftTensor, rightTensor, ev_zero]
    rw [hsdd_zero]
    exact herror_nonneg
  · simp [Z]
  · intro g
    simpa [Z, sdpDualSlackOperator] using
      (sub_nonneg.mpr (averagedPointOperator_le_one params strategy g))
  · have hgap_one : projectiveBoundednessGap params strategy H Z = 1 := by
      simp [H, Z, projectiveBoundednessGap, projectiveResidualOperator,
        zeroProjSubMeas, leftTensor, rightTensor,
        ev_one_of_isNormalized strategy.state strategy.isNormalized]
    rw [hgap_one]
    exact herror_ge_one

/-- Helper-output-specific residual-preserving projective repair construction
for the paper-faithful Section 9 route.

This theorem isolates the missing construction step behind the operator-total
route: after completing the helper output by a fresh `none` outcome, one needs
an option-indexed projective repair whose fresh outcome still dominates the
original residual operator.  The existing locality-preserving repair producer
supplies the rounded projective family; the residual domination itself remains
the hard helper-output-specific step.

This is the remaining source-faithful Section 9 construction gap tracked by
issue #1642. -/
private theorem helper_output_residual_preserving_projectivization
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelperWithSlackness :
      SelfImprovementHelperConclusionWithSlackness params strategy T Hhat Z eps delta)
    (hhelperSSC :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta)) :
    ∃ P : ProjSubMeas (Option (Polynomial params)) ι,
      RoundedProjMeasStatement strategy.state
        (leftLiftedMeasurement (ιB := ι) (optionCompletion Hhat))
        (ProjSubMeas.liftLeft P)
        (orthonormalizationMainLemmaError
          (2 * selfImprovementHelperError params eps delta)) ∧
      (optionCompletion Hhat).outcome none ≤ P.outcome none := by
  sorry

/-- Helper-output orthonormalization route with operator total monotonicity.

This records the paper-faithful Section 9 route in the form needed by
`selfImprovement`: it returns the restricted projective family `H`, the usual
orthonormalization closeness statement, and the operator comparison
`H.toSubMeas.total ≤ Hhat.total`.  The proof is reduced to the residual
domination theorem `helper_output_residual_preserving_projectivization` above. -/
private theorem helper_output_projectivization_with_total_le
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelperWithSlackness :
      SelfImprovementHelperConclusionWithSlackness params strategy T Hhat Z eps delta)
    (hhelperSSC :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta)) :
    ∃ H : ProjSubMeas (Polynomial params) ι,
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat.liftLeft)
        (constSubMeasFamily H.toSubMeas.liftLeft)
        (selfImprovementOrthogonalizationError params eps delta) ∧
      H.toSubMeas.total ≤ Hhat.total := by
  let ζhelper : Error := selfImprovementHelperError params eps delta
  have hζ_nonneg : 0 ≤ ζhelper :=
    selfImprovementHelperError_nonneg params eps delta
  obtain ⟨P, hRounded, hresidual⟩ :=
    helper_output_residual_preserving_projectivization
      params strategy eps delta hhelperWithSlackness hhelperSSC
  have hP_local :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily ((optionCompletion Hhat).toSubMeas.liftLeft))
        (constSubMeasFamily P.toSubMeas.liftLeft)
        (orthonormalizationMainLemmaError (2 * ζhelper)) := by
    simpa [leftLiftedMeasurement, leftPlacedSubMeas, SubMeas.liftLeft,
      ProjSubMeas.liftLeft] using hRounded.closeness
  have hPq :
      qSDD strategy.state (optionCompletion Hhat).toSubMeas.liftLeft
        P.toSubMeas.liftLeft ≤
        orthonormalizationMainLemmaError (2 * ζhelper) := by
    simpa [ldt_simp] using hP_local.squaredDistanceBound
  let H : ProjSubMeas (Polynomial params) ι := restrictSomeProjSubMeas P
  have hHq :
      qSDD strategy.state Hhat.liftLeft H.toSubMeas.liftLeft ≤
        orthonormalizationMainLemmaError (2 * ζhelper) := by
    exact le_trans
      (Orthonormalization.Completion.qSDD_liftLeft_restrictSomeProjSubMeas_le
          (ψ := strategy.state) (A := Hhat) (P := P))
      hPq
  have hcoeff :
      orthonormalizationMainLemmaError (2 * ζhelper) ≤
        selfImprovementOrthogonalizationError params eps delta := by
    change orthonormalizationMainLemmaError (2 * ζhelper) ≤
      orthonormalizationError ζhelper
    open Orthonormalization.ErrorBounds in
    exact
      orthonormalizationMainLemmaError_two_mul_le_orthonormalizationError
        ζhelper hζ_nonneg
  have horth :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat.liftLeft)
        (constSubMeasFamily H.toSubMeas.liftLeft)
        (selfImprovementOrthogonalizationError params eps delta) := by
    constructor
    simpa [sddError, avgOver, uniformDistribution, constSubMeasFamily, H] using
      (le_trans hHq hcoeff)
  have hTotalLe : H.toSubMeas.total ≤ Hhat.total := by
    simpa [H] using
      restrictSomeProjSubMeas_total_le_of_optionCompletion_residual_le
        Hhat P hresidual
  exact ⟨H, horth, hTotalLe⟩

/--
Formal statement corresponding to the blueprint theorem `thm:self-improvement`,
with the input consistency hypothesis from the LDT paper.

The theorem assumes a measurement `G` whose polynomial evaluation family is
consistent with the point measurement at error `nu`. It must produce a
projective polynomial submeasurement satisfying the four self-improvement
conclusions. The paper and blueprint impose the `(eps, delta, gamma)`-good
strategy condition as a standing hypothesis for the self-improvement section
(`blueprint/src/chapter/ch07_self_improvement.tex`, line 4); Lean records it
here as the explicit hypothesis `hgood`. The source-facing theorem remains
visible with the paper statement; any remaining missing derivation is lowered to
internal obligations rather than hidden in a conditional theorem with extra
obligation hypotheses.

**Unfaithful:** The proof of `thm:self-improvement` in
`references/ldt-paper/self_improvement.tex` is currently represented by the
paper-faithful operator-total route, which depends on the helper-output-specific
residual-preserving projective repair theorem
`helper_output_residual_preserving_projectivization`.  This is the remaining
Section 9 construction gap tracked by issue #1642.  Elimination: prove the
residual domination for the projective repair constructed from the completed
helper output. -/
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
  have heps : 0 ≤ eps := eps_nonneg_of_isGood params strategy hgood
  have hdelta : 0 ≤ delta := delta_nonneg_of_isGood params strategy hgood
  have hnu_nonneg : 0 ≤ nu := by
    exact le_trans
      (bipartiteConsError_nonneg strategy.state
        (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas))
      hcons.offDiagonalBound
  by_cases heps_le_one : eps ≤ 1
  · by_cases hdelta_le_one : delta ≤ 1
    · by_cases hd_le_q : (params.d : Error) ≤ (params.q : Error)
      · rcases self_improvement_helper_with_slackness params strategy eps delta gamma
            hgood nu G with
          ⟨T, Hhat, Z, hhelperWithSlackness⟩
        let hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta :=
          hhelperWithSlackness.toHelperConclusion
        have hpointSSC :
            BipartiteSSCRel strategy.state (uniformDistribution (Point params))
              (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta := by
          exact ⟨by
            simpa [SymStrat.selfConsistencyFailureProbability] using
              hgood.selfConsistencyTest⟩
        have haddInUFull : AddInUFullStatement params strategy T eps delta :=
          addInUFullStatement_of_isGood (ι := ι) params strategy eps delta gamma hgood T
        have htransfer :
            |addInULeftQuantity params strategy
                (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
                Hhat
                (pointConsistencyAddInUSelection params) -
              addInURightQuantity params strategy
                (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
                T.toSubMeas
                (pointConsistencyAddInUSelection params)| ≤
              addInUError params eps delta := by
          have htransfer :=
            haddInUFull.selectionDependentTransfer
              (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
              (pointConsistencyAddInUSelection params)
          simpa [hhelper.averagedConstruction] using htransfer
        have hhelperCompleteness :
            CompletenessAtLeast strategy.state Hhat.liftLeft
              ((1 - nu) - selfImprovementHelperError params eps delta) :=
          helper_completeness_of_self_consistency_helper_slackness_input_consistency
            params strategy G eps delta nu heps hdelta hhelperWithSlackness hpointSSC hcons
        have hlocal :
            (∑ g : Polynomial params,
              localVarianceDeviationAtPolynomial params strategy strategy.state
                T.toSubMeas g) ≤
              localVarianceOfPointsError params eps delta :=
          localVarianceDeviation_sum_le_localVarianceOfPointsError
            params strategy eps delta gamma hgood T.toSubMeas
        have hclone :
            |helperDeleteAQuantity params strategy T.toSubMeas -
              helperDeleteAClonedQuantity params strategy T.toSubMeas| ≤
                Real.sqrt (selfImprovementVarianceError params eps delta) :=
          helperDeleteAQuantity_abs_sub_clonedQuantity_le_sqrt
            params strategy eps delta T.toSubMeas hlocal
        have hmove :
            |helperDeleteAClonedQuantity params strategy T.toSubMeas -
              helperMoveOverVQuantity params strategy T.toSubMeas| ≤
                Real.sqrt (2 * delta) :=
          helperDeleteAClonedQuantity_abs_sub_moveOverVQuantity_le_sqrt_two_delta
            params strategy delta T.toSubMeas hpointSSC
        have hslack :
            ∀ h : Polynomial params,
              T.toSubMeas.outcome h * averagedPointOperator params strategy h =
                T.toSubMeas.outcome h * Z :=
          fun h =>
            helper_slackness_eq_of_helper_with_slackness
              params strategy eps delta hhelperWithSlackness h
        have hsscObligations :
            HelperStrongSelfConsistencyObligations params strategy T Hhat eps delta :=
          helper_ssc_obligations_of_scalarTransports_pointTransfer
            params strategy eps delta hhelper hpointSSC hlocal hclone hmove
            hslack htransfer
        have hhelperSSC :
            BipartiteSSCRel strategy.state (uniformDistribution Unit)
              (constSubMeasFamily Hhat)
              (selfImprovementHelperError params eps delta) :=
          helper_strong_self_consistency_of_helper_conclusion
            params strategy eps delta heps hdelta hd_le_q hhelper hsscObligations
        obtain ⟨H, horth, hTotalLe⟩ :=
          helper_output_projectivization_with_total_le
            params strategy eps delta hhelperWithSlackness hhelperSSC
        have hhelperSSCPoint :
            BipartiteSSCRel strategy.state (uniformDistribution (Point params))
              (fun _ : Point params => Hhat)
              (selfImprovementHelperError params eps delta) :=
          bipartiteSSCRel_uniform_const strategy.state Hhat
            (selfImprovementHelperError params eps delta) hhelperSSC
        have horthPoint :
            SDDRel strategy.state (uniformDistribution (Point params))
              (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas (fun _ : Point params => H)))
              (IdxSubMeas.liftLeft (fun _ : Point params => Hhat))
              (selfImprovementOrthogonalizationError params eps delta) := by
          simpa [IdxProjSubMeas.toIdxSubMeas] using
            sddRel_uniform_const strategy.state H.toSubMeas.liftLeft Hhat.liftLeft
              (selfImprovementOrthogonalizationError params eps delta)
              (MIPStarRE.LDT.Preliminaries.sddRel_symm strategy.state
                (uniformDistribution Unit)
                (constSubMeasFamily Hhat.liftLeft)
                (constSubMeasFamily H.toSubMeas.liftLeft)
                (selfImprovementOrthogonalizationError params eps delta) horth)
        have hdataRev :
            SDDRel strategy.state (uniformDistribution (Point params))
              ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
              ((polynomialEvaluationFamily params Hhat).liftLeft)
              (selfImprovementDataProcessingError params eps delta) := by
          simpa [polynomialEvaluationFamily, evaluateAt,
            selfImprovementDataProcessingError_eq params eps delta] using
            Preliminaries.selfConsistencyImpliesDataProcessing
              strategy.state strategy.permInvState strategy.isNormalized
              (uniformDistribution (Point params))
              (uniformDistribution_weight_sum_le_one (Point params))
              (fun _ : Point params => Hhat)
              (fun _ : Point params => H)
              (selfImprovementHelperError params eps delta)
              (selfImprovementOrthogonalizationError params eps delta)
              (fun u g => g u)
              hhelperSSCPoint horthPoint
        have hdata :
            SDDRel strategy.state (uniformDistribution (Point params))
              ((polynomialEvaluationFamily params Hhat).liftLeft)
              ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
              (selfImprovementDataProcessingError params eps delta) :=
          MIPStarRE.LDT.Preliminaries.sddRel_symm strategy.state
            (uniformDistribution (Point params))
            ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
            ((polynomialEvaluationFamily params Hhat).liftLeft)
            (selfImprovementDataProcessingError params eps delta) hdataRev
        have hfinal : SelfImprovementFinalFields params strategy H Z eps delta nu :=
          final_fields_of_helper_outputs_of_total_operator_le
            params strategy eps delta nu
            heps heps_le_one hdelta hdelta_le_one hd_le_q
            hhelper hhelperCompleteness hhelperSSC hpointSSC hslack htransfer
            horth hdata hTotalLe
        exact ⟨H, Z,
          { completeness := hfinal.completeness
            pointConsistency := hfinal.pointConsistency
            selfCloseness := hfinal.selfCloseness
            positiveSemidefiniteWitness := hhelper.sdpWitness.dualPositive
            dualDominatesAveragedPoint := hhelper.sdpWitness.dualFeasible
            projectiveResidualBound := hfinal.projectiveResidualBound }⟩
      · have hdq_ge_one : 1 ≤ ((params.d : Error) / (params.q : Error)) := by
          exact (one_le_div₀ params.q_cast_pos).2 (le_of_lt (lt_of_not_ge hd_le_q))
        have hdq_pow_ge_one :
            1 ≤ Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (32 : Error)) := by
          have hpow :=
            Real.rpow_le_rpow (show (0 : Error) ≤ 1 by positivity) hdq_ge_one
              (by positivity : 0 ≤ (1 / (32 : Error)))
          simpa using hpow
        have hsum_ge_one :
            1 ≤ finalStagePowerSum params eps delta (1 / (32 : Error)) := by
          unfold finalStagePowerSum
          have heps_pow_nonneg : 0 ≤ Real.rpow eps (1 / (32 : Error)) :=
            Real.rpow_nonneg heps _
          have hdelta_pow_nonneg : 0 ≤ Real.rpow delta (1 / (32 : Error)) :=
            Real.rpow_nonneg hdelta _
          nlinarith
        have herror_ge_one : 1 ≤ selfImprovementError params eps delta := by
          rw [selfImprovementError_eq_finalStagePowerSum]
          nlinarith [one_le_m_cast params, hsum_ge_one]
        exact selfImprovement_of_error_ge_one
          params strategy eps delta gamma nu hgood G herror_ge_one hnu_nonneg
    · have hdelta_ge_one : 1 ≤ delta := le_of_lt (lt_of_not_ge hdelta_le_one)
      have hdelta_pow_ge_one : 1 ≤ Real.rpow delta (1 / (32 : Error)) := by
        have hpow :=
          Real.rpow_le_rpow (show (0 : Error) ≤ 1 by positivity) hdelta_ge_one
            (by positivity : 0 ≤ (1 / (32 : Error)))
        simpa using hpow
      have hsum_ge_one : 1 ≤ finalStagePowerSum params eps delta (1 / (32 : Error)) := by
        unfold finalStagePowerSum
        have heps_pow_nonneg : 0 ≤ Real.rpow eps (1 / (32 : Error)) :=
          Real.rpow_nonneg heps _
        have hdq_pow_nonneg :
            0 ≤ Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (32 : Error)) :=
          Real.rpow_nonneg (d_q_ratio_nonneg params) _
        nlinarith
      have herror_ge_one : 1 ≤ selfImprovementError params eps delta := by
        rw [selfImprovementError_eq_finalStagePowerSum]
        nlinarith [one_le_m_cast params, hsum_ge_one]
      exact selfImprovement_of_error_ge_one
        params strategy eps delta gamma nu hgood G herror_ge_one hnu_nonneg
  · have heps_ge_one : 1 ≤ eps := le_of_lt (lt_of_not_ge heps_le_one)
    have heps_pow_ge_one : 1 ≤ Real.rpow eps (1 / (32 : Error)) := by
      have hpow :=
        Real.rpow_le_rpow (show (0 : Error) ≤ 1 by positivity) heps_ge_one
          (by positivity : 0 ≤ (1 / (32 : Error)))
      simpa using hpow
    have hsum_ge_one : 1 ≤ finalStagePowerSum params eps delta (1 / (32 : Error)) := by
      unfold finalStagePowerSum
      have hdelta_pow_nonneg : 0 ≤ Real.rpow delta (1 / (32 : Error)) :=
        Real.rpow_nonneg hdelta _
      have hdq_pow_nonneg :
          0 ≤ Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (32 : Error)) := by
        exact Real.rpow_nonneg (d_q_ratio_nonneg params) _
      nlinarith
    have herror_ge_one : 1 ≤ selfImprovementError params eps delta := by
      rw [selfImprovementError_eq_finalStagePowerSum]
      nlinarith [one_le_m_cast params, hsum_ge_one]
    exact selfImprovement_of_error_ge_one
      params strategy eps delta gamma nu hgood G herror_ge_one hnu_nonneg

end MIPStarRE.LDT.SelfImprovement
