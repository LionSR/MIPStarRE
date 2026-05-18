import MIPStarRE.LDT.SelfImprovement.Theorems.Results.BoundednessTransport.PointConsistencyLiteral

/-!
# Boundedness transport boundedness-gap estimates

This file contains the helper boundedness-gap decomposition, its
data-processing transport, and the final projective-residual boundedness
constructors used in the self-improvement assembly.

## References

- `references/ldt-paper/self_improvement.tex` lines 612--613 and 742--755
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

/-- Algebraic decomposition of the helper boundedness gap.

The scalar gap
`⟨Z ⊗ I - helperAgreementAverageOperator⟩` is the sum of
`⟨Z ⊗ I⟩ - ⟨I ⊗ H.total⟩` and the off-diagonal average produced by
`helper_boundedness_slack_average_ev_eq_off_diagonal_avg`.  This is the
formal algebraic bridge between the reindexing calculation and the final
boundedness estimate in the proof of self-improvement. -/
theorem helper_boundedness_gap_eq_upper_gap_add_off_diagonal_avg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) :
    helperBoundednessGap params strategy H Z =
      (ev strategy.state (helperUpperOperator params Z) -
          ev strategy.state (rightTensor (ι₁ := ι) H.total)) +
        avgOver (uniformDistribution (Point params)) (fun u =>
          ∑ h : Polynomial params,
            ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
              ev strategy.state
                (opTensor ((strategy.pointMeasurement u).outcome a)
                  (H.outcome h))) := by
  have hslack :=
    helper_boundedness_slack_average_ev_eq_off_diagonal_avg params strategy H
  have hgap_decomp :
      helperBoundednessGap params strategy H Z =
        (ev strategy.state (helperUpperOperator params Z) -
            ev strategy.state (rightTensor (ι₁ := ι) H.total)) +
          (ev strategy.state (rightTensor (ι₁ := ι) H.total) -
            ev strategy.state (helperAgreementAverageOperator params strategy H)) := by
    unfold helperBoundednessGap helperBoundednessOperator
    rw [ev_sub]
    ring
  rw [hgap_decomp, hslack]

/-- Helper-stage boundedness from the scalar comparison and the off-diagonal
estimate.

The helper boundedness gap decomposes as
`⟨Z ⊗ I⟩ - ⟨I ⊗ Hhat.total⟩` plus the off-diagonal average from
`helper_boundedness_slack_average_ev_eq_off_diagonal_avg`.  Thus the comparison
`⟨Z ⊗ I⟩ - ⟨I ⊗ Hhat.total⟩ ≤ 3 √δ`, together with the off-diagonal estimate
`≤ 4 √ζ_variance`, gives the helper threshold after applying
`helper_boundedness_error_le_selfImprovementHelperError`. -/
theorem helper_boundedness_gap_le_selfImprovementHelperError
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hZ_vs_H :
      ev strategy.state (helperUpperOperator params Z) -
          ev strategy.state (rightTensor (ι₁ := ι) Hhat.total) ≤
        3 * Real.sqrt delta)
    (hoffdiag :
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                (Hhat.outcome h))) ≤
        4 * Real.sqrt (selfImprovementVarianceError params eps delta)) :
    helperBoundednessGap params strategy Hhat Z ≤
      selfImprovementHelperError params eps delta := by
  calc
    helperBoundednessGap params strategy Hhat Z =
        (ev strategy.state (helperUpperOperator params Z) -
            ev strategy.state (rightTensor (ι₁ := ι) Hhat.total)) +
          avgOver (uniformDistribution (Point params)) (fun u =>
            ∑ h : Polynomial params,
              ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
                ev strategy.state
                  (opTensor ((strategy.pointMeasurement u).outcome a)
                    (Hhat.outcome h))) :=
      helper_boundedness_gap_eq_upper_gap_add_off_diagonal_avg params strategy Hhat Z
    _ ≤ 3 * Real.sqrt delta +
        4 * Real.sqrt (selfImprovementVarianceError params eps delta) :=
      add_le_add hZ_vs_H hoffdiag
    _ ≤ selfImprovementHelperError params eps delta :=
      helper_boundedness_error_le_selfImprovementHelperError params eps delta heps hdelta

-- This bound combines the off-diagonal add-in-u transfer with the boundedness
-- gap decomposition.
/-- Helper-stage boundedness from the scalar comparison and the
point-consistency `add-in-u` transfer.

This theorem composes the off-diagonal estimate supplied by
`pointConsistencyAddInUSelection` with
`helper_boundedness_gap_le_selfImprovementHelperError`.  It is the theorem-side
form of the sentence "combined with the explicit `A`-consistency bound" in the
boundedness paragraph of the self-improvement proof. -/
theorem helper_boundedness_gap_le_selfImprovementHelperError_of_pointConsistencyAddInU_transfer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {T Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hZ_vs_H :
      ev strategy.state (helperUpperOperator params Z) -
          ev strategy.state (rightTensor (ι₁ := ι) Hhat.total) ≤
        3 * Real.sqrt delta)
    (htransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          Hhat
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta) :
    helperBoundednessGap params strategy Hhat Z ≤
      selfImprovementHelperError params eps delta := by
  have hoffdiag_addInU :
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                (Hhat.outcome h))) ≤ addInUError params eps delta :=
    pointConsistencyAddInU_off_diagonal_avg_le_of_transfer
      params strategy eps delta T Hhat htransfer
  have hoffdiag :
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                (Hhat.outcome h))) ≤
        4 * Real.sqrt (selfImprovementVarianceError params eps delta) := by
    simpa [addInUError, Real.sqrt_eq_rpow] using hoffdiag_addInU
  exact
    helper_boundedness_gap_le_selfImprovementHelperError
      params strategy eps delta heps hdelta hZ_vs_H hoffdiag

-- This comparison transports the helper-completeness scalar through the
-- left/right tensor swap on the permutation-invariant state.
/-- Convert the helper-completeness `Hhat`-versus-`Z` comparison to the
right-placed total comparison used in the boundedness gap.

The helper-completeness paragraph naturally proves
`⟨ψ, Z ⊗ I⟩ - 3√δ ≤ subMeasMass ψ Hhat.liftLeft`. The boundedness decomposition,
however, uses the right-placed total `⟨ψ, I ⊗ Hhat.total⟩`. On the
permutation-invariant strategy state these scalars agree, so the comparison
becomes `⟨ψ, Z ⊗ I⟩ - ⟨ψ, I ⊗ Hhat.total⟩ ≤ 3√δ`. -/
theorem helper_upper_gap_rightTensor_le_three_sqrt_delta_of_helper_outputs
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hslack :
      ∀ h : Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z) :
    ev strategy.state (helperUpperOperator params Z) -
        ev strategy.state (rightTensor (ι₁ := ι) Hhat.total) ≤
      3 * Real.sqrt delta := by
  have hleft :
      ev strategy.state (leftTensor (ι₂ := ι) Z) - 3 * Real.sqrt delta ≤
        subMeasMass strategy.state Hhat.liftLeft :=
    helper_hhat_vs_z_of_self_consistency_and_complementary_slackness
      params strategy eps delta hhelper hssc hslack
  have hmass :
      subMeasMass strategy.state Hhat.liftLeft =
        ev strategy.state (leftTensor (ι₂ := ι) Hhat.total) := rfl
  have hswap :
      ev strategy.state (leftTensor (ι₂ := ι) Hhat.total) =
        ev strategy.state (rightTensor (ι₁ := ι) Hhat.total) :=
    strategy.permInvState.swap_ev Hhat.total
  unfold helperUpperOperator
  rw [hmass, hswap] at hleft
  linarith

/-- Helper-stage boundedness from the actual helper comparison and the
point-consistency `add-in-u` transfer.

This theorem composes the helper-completeness comparison `Hhat`-versus-`Z`
with the boundedness off-diagonal estimate. Complementary slackness remains an
explicit hypothesis because the reduced `SelfImprovementHelperConclusion`
records only the presently formalized SDP facts. The off-diagonal transfer is
likewise explicit: it is the theorem-side form of the `add-in-u` application
with `S_u = {(a,h) : h(u) ≠ a}`. -/
theorem helper_boundedness_gap_le_selfImprovementHelperError_of_helper_outputs
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
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
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta) :
    helperBoundednessGap params strategy Hhat Z ≤
      selfImprovementHelperError params eps delta := by
  have hZ_vs_H :
      ev strategy.state (helperUpperOperator params Z) -
          ev strategy.state (rightTensor (ι₁ := ι) Hhat.total) ≤
        3 * Real.sqrt delta :=
    helper_upper_gap_rightTensor_le_three_sqrt_delta_of_helper_outputs
      params strategy eps delta hhelper hssc hslack
  exact
    helper_boundedness_gap_le_selfImprovementHelperError_of_pointConsistencyAddInU_transfer
      params strategy eps delta heps hdelta hZ_vs_H htransfer

/-- Transport the helper boundedness gap through the data-processing
approximation between `Hhat` and `H`.

The input `hdata` is exactly the data-processing SDD bound already produced
inside `selfImprovement`. The conclusion says that replacing the helper
polynomial family in the point-agreement average by the projective family costs
at most `sqrt ε`, matching Proposition `easy-approx-from-approx-delta` in the
boundedness paragraph of the paper. -/
theorem helper_boundedness_gap_transport_through_data_processing
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (Hhat : SubMeas (Polynomial params) ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι)
    (ε : Error)
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        ε) :
    helperBoundednessGap params strategy H.toSubMeas Z ≤
      helperBoundednessGap params strategy Hhat Z + Real.sqrt ε := by
  have hdata_right :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftRight)
        ((polynomialEvaluationFamily params H.toSubMeas).liftRight)
        ε := by
    simpa [IdxSubMeas.liftLeft, IdxSubMeas.liftRight]
      using
        sddRel_liftRight_of_liftLeft_permInv
          strategy.permInvState (uniformDistribution (Point params))
          (polynomialEvaluationFamily params Hhat)
          (polynomialEvaluationFamily params H.toSubMeas) ε hdata
  have happrox :=
    Preliminaries.easyApproxFromApproxDelta
      strategy.state strategy.isNormalized
      (uniformDistribution (Point params))
      (uniformDistribution_weight_sum_le_one (Point params))
      ((polynomialEvaluationFamily params Hhat).liftRight)
      ((polynomialEvaluationFamily params H.toSubMeas).liftRight)
      (IdxSubMeas.liftLeft (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      ε hdata_right
  have hscalar :
      |ev strategy.state (helperAgreementAverageOperator params strategy Hhat) -
        ev strategy.state (helperAgreementAverageOperator params strategy H.toSubMeas)| ≤
        Real.sqrt ε := by
    rw [helper_agreement_average_ev_eq_avg params strategy Hhat,
      helper_agreement_average_ev_eq_avg params strategy H.toSubMeas]
    simpa [polynomialEvaluationFamily, evaluateAt, IdxSubMeas.liftRight,
      IdxSubMeas.liftLeft, IdxProjMeas.toIdxSubMeas,
      rightTensor_mul_leftTensor_eq_opTensor] using happrox
  unfold helperBoundednessGap helperBoundednessOperator
  rw [ev_sub, ev_sub]
  have hle := le_abs_self
    (ev strategy.state (helperAgreementAverageOperator params strategy Hhat) -
      ev strategy.state (helperAgreementAverageOperator params strategy H.toSubMeas))
  linarith


/-- Compare the final projective residual with the helper boundedness gap for the
same projective family.

This is the SDP dual-slack step in the projective boundedness paragraph of
`thm:self-improvement` (`references/ldt-paper/self_improvement.tex`, lines
742--749): the term `Z ⊗ H_h` in the projective residual dominates
`(E_u A^u_{h(u)}) ⊗ H_h` for each polynomial `h`, and summing these inequalities
turns `Z ⊗ (I - H)` into the helper-stage defect
`Z ⊗ I - E_u Σ_a A^u_a ⊗ H_[h(u)=a]`. -/
theorem projective_boundedness_gap_le_helper_boundedness_gap
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι)
    (hdual :
      ∀ h : Polynomial params,
        0 ≤ sdpDualSlackOperator params strategy Z h) :
    projectiveBoundednessGap params strategy H Z ≤
      helperBoundednessGap params strategy H.toSubMeas Z := by
  classical
  have hprojective_eq :
      projectiveBoundednessGap params strategy H Z =
        ev strategy.state (leftTensor (ι₂ := ι) Z) -
          ∑ h : Polynomial params,
            ev strategy.state (opTensor Z (H.toSubMeas.outcome h)) := by
    have hsub_tensor :
        opTensor Z (1 - H.toSubMeas.total) =
          opTensor Z (1 : MIPStarRE.Quantum.Op ι) -
            opTensor Z H.toSubMeas.total := by
      ext x y
      simp [opTensor, sub_eq_add_neg, mul_add]
    have htotal_tensor :
        opTensor Z H.toSubMeas.total =
          ∑ h : Polynomial params, opTensor Z (H.toSubMeas.outcome h) := by
      rw [← H.toSubMeas.sum_eq_total, opTensor_sum_right_univ]
    unfold projectiveBoundednessGap projectiveResidualOperator
    calc
      ev strategy.state (leftTensor (ι₂ := ι) Z *
          rightTensor (ι₁ := ι) (1 - H.toSubMeas.total))
          = ev strategy.state (opTensor Z (1 - H.toSubMeas.total)) := by
            rw [leftTensor_mul_rightTensor_eq_opTensor]
      _ = ev strategy.state
            (opTensor Z (1 : MIPStarRE.Quantum.Op ι) -
              opTensor Z H.toSubMeas.total) := by
            rw [hsub_tensor]
      _ = ev strategy.state (opTensor Z (1 : MIPStarRE.Quantum.Op ι)) -
            ev strategy.state (opTensor Z H.toSubMeas.total) := by
            rw [ev_sub]
      _ = ev strategy.state (leftTensor (ι₂ := ι) Z) -
            ev strategy.state (opTensor Z H.toSubMeas.total) := rfl
      _ = ev strategy.state (leftTensor (ι₂ := ι) Z) -
            ∑ h : Polynomial params,
              ev strategy.state (opTensor Z (H.toSubMeas.outcome h)) := by
            rw [htotal_tensor, ev_sum]
  have hhelper_agreement_eq :
      ev strategy.state (helperAgreementAverageOperator params strategy H.toSubMeas) =
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor (averagedPointOperator params strategy h)
              (H.toSubMeas.outcome h)) := by
    rw [helper_agreement_average_ev_eq_polynomial_sum]
    rw [avgOver_sum]
    refine Finset.sum_congr rfl ?_
    intro h _
    exact (ev_opTensor_averageOperatorOverDistribution_left strategy.state
      (uniformDistribution (Point params))
      (pointConditionedOutcomeOperatorAtPolynomial params strategy h)
      (H.toSubMeas.outcome h)).symm
  have hhelper_eq :
      helperBoundednessGap params strategy H.toSubMeas Z =
        ev strategy.state (leftTensor (ι₂ := ι) Z) -
          ∑ h : Polynomial params,
            ev strategy.state
              (opTensor (averagedPointOperator params strategy h)
                (H.toSubMeas.outcome h)) := by
    unfold helperBoundednessGap helperBoundednessOperator helperUpperOperator
    rw [ev_sub, hhelper_agreement_eq]
  have hsum_le :
      (∑ h : Polynomial params,
          ev strategy.state
            (opTensor (averagedPointOperator params strategy h) (H.toSubMeas.outcome h))) ≤
        ∑ h : Polynomial params,
          ev strategy.state (opTensor Z (H.toSubMeas.outcome h)) := by
    refine Finset.sum_le_sum ?_
    intro h _
    apply ev_mono
    exact opTensor_mono_left
      (sub_nonneg.mp (by simpa [sdpDualSlackOperator] using hdual h))
      (H.toSubMeas.outcome_pos h)
  rw [hprojective_eq, hhelper_eq]
  linarith

/-- Natural-error projective-residual construction.

Given the helper-stage boundedness estimate for `Hhat`, the dual-slack
comparator above and the existing data-processing transport produce the final
projective residual at the paper's natural error
`selfImprovementHelperError + sqrt selfImprovementDataProcessingError`. The
separate numerical absorption into the literal `selfImprovementError` threshold
is intentionally not hidden in this theorem.

**Paper source:** `references/ldt-paper/self_improvement.tex` lines 742--755.
This is a source-faithful construction step for the final-fields boundedness
conclusion. -/
theorem final_fields_projective_residual_bound_natural
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {H : ProjSubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hhelperBounded :
      helperBoundednessGap params strategy Hhat Z ≤
        selfImprovementHelperError params eps delta)
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta)) :
    projectiveBoundednessGap params strategy H Z ≤
      selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta) := by
  have hcompare :=
    projective_boundedness_gap_le_helper_boundedness_gap params strategy H Z
      hhelper.sdpWitness.dualFeasible
  have htransport :=
    helper_boundedness_gap_transport_through_data_processing params strategy Hhat H Z
      (selfImprovementDataProcessingError params eps delta) hdata
  linarith

/-- Literal-threshold projective-residual construction.

This theorem combines `final_fields_projective_residual_bound_natural` with a separately
named numerical absorption lemma. The analytic inputs are only the helper-stage
boundedness estimate, dual feasibility from `SelfImprovementHelperConclusion`,
and the data-processing SDD output already produced inside `selfImprovement`.

**Paper source:** `references/ldt-paper/self_improvement.tex` lines 742--755.
This is a source-faithful construction step for the final-fields boundedness
conclusion. -/
theorem final_fields_projective_residual_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {H : ProjSubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hhelperBounded :
      helperBoundednessGap params strategy Hhat Z ≤
        selfImprovementHelperError params eps delta)
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta))
    (habsorb :
      selfImprovementHelperError params eps delta +
          Real.sqrt (selfImprovementDataProcessingError params eps delta) ≤
        selfImprovementError params eps delta) :
    projectiveBoundednessGap params strategy H Z ≤
      selfImprovementError params eps delta :=
  le_trans
    (final_fields_projective_residual_bound_natural params strategy eps delta
      hhelper hhelperBounded hdata)
    habsorb

/-- Literal-threshold projective-residual construction under the standard
unit-interval smallness hypotheses.

This is the convenience theorem following from
`final_fields_projective_residual_bound`: the numerical absorption input is
provided by
`final_fields_projective_residual_error_le_selfImprovementError`, so callers
only need the helper-stage boundedness estimate, data-processing output, and
the usual smallness assumptions on `eps`, `delta`, and `d/q`.

**Paper source:** `references/ldt-paper/self_improvement.tex` lines 742--755.
This is a source-faithful construction step for the final-fields boundedness
conclusion. -/
theorem final_fields_projective_residual_bound_of_small_errors
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {H : ProjSubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hhelperBounded :
      helperBoundednessGap params strategy Hhat Z ≤
        selfImprovementHelperError params eps delta)
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta)) :
    projectiveBoundednessGap params strategy H Z ≤
      selfImprovementError params eps delta :=
  final_fields_projective_residual_bound params strategy eps delta hhelper hhelperBounded hdata
    (final_fields_projective_residual_error_le_selfImprovementError params eps delta
      heps heps_le_one hdelta hdelta_le_one hd_le_q)

/-- Final projective-residual construction from helper outputs and the
point-consistency `add-in-u` transfer.

The theorem performs the boundedness part of the final-fields assembly once the
orthonormalization data-processing estimate is available. It supplies the
helper-stage boundedness estimate from the helper comparison, complementary
slackness, point self-consistency, and the off-diagonal `add-in-u` transfer,
then applies the standard data-processing transport and numerical absorption
into `selfImprovementError`.

**Paper source:** `references/ldt-paper/self_improvement.tex` lines 742--755.
This is a source-faithful construction step for the final-fields boundedness
conclusion. -/
theorem final_fields_projective_residual_bound_of_helper_outputs
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {H : ProjSubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
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
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta)) :
    projectiveBoundednessGap params strategy H Z ≤
      selfImprovementError params eps delta := by
  have hhelperBounded :
      helperBoundednessGap params strategy Hhat Z ≤
        selfImprovementHelperError params eps delta :=
    helper_boundedness_gap_le_selfImprovementHelperError_of_helper_outputs
      params strategy eps delta heps hdelta hhelper hssc hslack htransfer
  exact
    final_fields_projective_residual_bound_of_small_errors
      params strategy eps delta heps heps_le_one hdelta hdelta_le_one hd_le_q
      hhelper hhelperBounded hdata

/-- Final-fields constructor for the `BoundedByOperator` conclusion.

If the SDP dual witness dominates the identity, then the left-placed mass of any
submeasurement is dominated by `Z ⊗ I`: the total bound `A.total ≤ 1 ≤ Z` lifts
by monotonicity to `leftTensor A.total ≤ leftTensor Z`, and evaluation against
the state preserves this order. Consequently `bndError ψ A.liftLeft (Z ⊗ I) = 0`,
so the boundedness statement holds at any nonnegative tolerance. The
`selfImprovement` assembly uses this constructor instead of requiring a combined
boundedness-field hypothesis. -/
theorem final_fields_bounded
    {α : Type*} [Fintype α]
    (ψ : QuantumState (ι × ι))
    (A : SubMeas α ι)
    {Z : MIPStarRE.Quantum.Op ι}
    (hOne : (1 : MIPStarRE.Quantum.Op ι) ≤ Z)
    {ε : Error}
    (hε : 0 ≤ ε) :
    BoundedByOperator ψ A.liftLeft (leftTensor (ι₂ := ι) Z) ε := by
  refine
    { witnessOpPSD := ?_
      upperBound := ?_ }
  · have : leftTensor (ι₂ := ι) Z = opTensor Z (1 : MIPStarRE.Quantum.Op ι) := rfl
    rw [this]
    have hPSD : 0 ≤ Z :=
      le_trans (Matrix.PosSemidef.one.nonneg : 0 ≤ (1 : MIPStarRE.Quantum.Op ι)) hOne
    exact opTensor_nonneg hPSD
      (Matrix.PosSemidef.one.nonneg : 0 ≤ (1 : MIPStarRE.Quantum.Op ι))
  · have hAle : A.total ≤ Z :=
      le_trans A.total_le_one hOne
    have hLTle :
        leftTensor (ι₂ := ι) A.total ≤ leftTensor (ι₂ := ι) Z := by
      have hopMono :
          opTensor A.total (1 : MIPStarRE.Quantum.Op ι) ≤
            opTensor Z (1 : MIPStarRE.Quantum.Op ι) :=
        opTensor_mono_left hAle
          (Matrix.PosSemidef.one.nonneg : 0 ≤ (1 : MIPStarRE.Quantum.Op ι))
      simpa [leftTensor, opTensor] using hopMono
    have hsubmass :
        subMeasMass ψ A.liftLeft = ev ψ (leftTensor (ι₂ := ι) A.total) := rfl
    have hev_le :
        ev ψ (leftTensor (ι₂ := ι) A.total) ≤ ev ψ (leftTensor (ι₂ := ι) Z) :=
      ev_mono ψ _ _ hLTle
    have hbnd_zero :
        bndError ψ A.liftLeft (leftTensor (ι₂ := ι) Z) = 0 := by
      unfold bndError
      rw [hsubmass]
      have :
          ev ψ (leftTensor (ι₂ := ι) A.total) -
              ev ψ (leftTensor (ι₂ := ι) Z) ≤ 0 := by
        linarith
      exact max_eq_left this
    rw [hbnd_zero]
    exact hε


end MIPStarRE.LDT.SelfImprovement
