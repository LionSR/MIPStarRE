import MIPStarRE.LDT.SelfImprovement.Theorems.Results.BoundednessTransport.Agreement
import MIPStarRE.LDT.Basic.QuantumState
import MIPStarRE.LDT.Basic.SubMeasurementFamilies
import MIPStarRE.LDT.GlobalVariance.Defs.Families
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Basic
import MIPStarRE.LDT.Preliminaries.SelfConsistency.DataProcessing
import MIPStarRE.LDT.Preliminaries.Triangles
import MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds
import MIPStarRE.LDT.SelfImprovement.Theorems.Statements
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.CommonHelpers
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.HelperCompleteness
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUPointConsistency

/-!
# Final-fields point-consistency transport

This file transports helper-stage point consistency to the final projective
family.  It keeps the total-overlap displacement explicit, records the monotone
right-total variants, and gives the data-processing bound for the displacement.

## References

- `references/ldt-paper/self_improvement.tex` lines 747--755
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/


namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma opTensor_one_left_eq_rightTensor
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (B : MIPStarRE.Quantum.Op ι₂) :
    opTensor (ι₁ := ι₁) (1 : MIPStarRE.Quantum.Op ι₁) B =
      rightTensor (ι₁ := ι₁) B := by
  rfl

lemma pointMeasurement_total_evalFamily_total_opTensor_ev_eq_rightTensor
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (S : SubMeas (Polynomial params) ι)
    (u : Point params) :
    ev strategy.state
        (opTensor
          (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total)
          (((polynomialEvaluationFamily params S) u).total)) =
      ev strategy.state (rightTensor (ι₁ := ι) S.total) := by
  have hA_total :
      (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) =
        (1 : MIPStarRE.Quantum.Op ι) := by
    exact (strategy.pointMeasurement u).total_eq_one
  have hS_total : (((polynomialEvaluationFamily params S) u).total) = S.total := by
    simpa [polynomialEvaluationFamily, evaluateAt] using
      postprocess_total S (fun g : Polynomial params => g u)
  rw [hA_total, hS_total, opTensor_one_left_eq_rightTensor]

lemma pointMeasurement_total_evalFamily_total_ev_eq_rightTensor
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (S : SubMeas (Polynomial params) ι)
    (u : Point params) :
    ev strategy.state
        (leftTensor (ι₂ := ι)
            (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
          rightTensor (ι₁ := ι)
            (((polynomialEvaluationFamily params S) u).total)) =
      ev strategy.state (rightTensor (ι₁ := ι) S.total) := by
  rw [leftTensor_mul_rightTensor_eq_opTensor]
  exact pointMeasurement_total_evalFamily_total_opTensor_ev_eq_rightTensor
    params strategy S u

/-- The helper-stage consistency defect is exactly the averaged off-diagonal
mass appearing in the point-consistency `add-in-u` calculation.

This is the same algebraic identity as
`helper_boundedness_slack_average_ev_eq_off_diagonal_avg`, read as a
`ConsRel` defect for the point measurement against the polynomial-evaluation
family of `H`. -/
theorem helper_point_consistency_error_eq_off_diagonal_avg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι) :
    bipartiteConsError strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                (H.outcome h))) := by
  classical
  unfold bipartiteConsError
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro u
  have hdiff_eq :
      ev strategy.state (rightTensor (ι₁ := ι) H.total) -
          ev strategy.state (helperAgreementOperatorAtPoint params strategy H u) =
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                (H.outcome h)) := by
    exact helperAgreementOperatorAtPoint_ev_slack_eq_off_diagonal_sum params strategy H u
  have hdiff_nonneg :
      0 ≤ ev strategy.state (rightTensor (ι₁ := ι) H.total) -
          ev strategy.state (helperAgreementOperatorAtPoint params strategy H u) := by
    rw [hdiff_eq]
    exact Finset.sum_nonneg fun h _ =>
      Finset.sum_nonneg fun a _ =>
        ev_nonneg_of_psd strategy.state _
          (opTensor_nonneg ((strategy.pointMeasurement u).toMeasurement.outcome_pos a)
            (H.outcome_pos h))
  have htotal :
      ev strategy.state
          (opTensor
            (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total)
            (((polynomialEvaluationFamily params H) u).total)) =
        ev strategy.state (rightTensor (ι₁ := ι) H.total) := by
    exact pointMeasurement_total_evalFamily_total_opTensor_ev_eq_rightTensor
      params strategy H u
  have hmatch :
      qBipartiteMatchMass strategy.state
          ((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u)
          ((polynomialEvaluationFamily params H) u) =
        ev strategy.state (helperAgreementOperatorAtPoint params strategy H u) := by
    simp [qBipartiteMatchMass, helperAgreementOperatorAtPoint,
      polynomialEvaluationFamily, evaluateAt, ev_sum, IdxProjMeas.toIdxSubMeas]
  unfold qBipartiteConsDefect
  rw [htotal, hmatch]
  rw [max_eq_right hdiff_nonneg, hdiff_eq]

/-- Helper-stage point consistency from the point-consistency `add-in-u`
transfer hypothesis.

The transfer bound controls the off-diagonal mass
`E_u ∑_h ∑_{a ≠ h(u)} ⟨ψ, A^u_a ⊗ Hhat_h ψ⟩`.  The preceding algebraic
identity identifies this mass with the `ConsRel` defect for the point
measurement and the polynomial-evaluation family of `Hhat`. -/
theorem helper_point_consistency_of_pointConsistencyAddInU_transfer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {T Hhat : SubMeas (Polynomial params) ι}
    (htransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          Hhat
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params Hhat)
      (selfImprovementHelperError params eps delta) := by
  refine ⟨?_⟩
  rw [helper_point_consistency_error_eq_off_diagonal_avg]
  exact
    pointConsistencyAddInU_off_diagonal_avg_le_helper_error_of_transfer
      params strategy eps delta heps hdelta T Hhat htransfer

/-- Helper-stage point consistency obtained directly from the selected
add-in-`u` chain.

The hypotheses are the two analytic inputs used by the selected four-step
chain: bipartite self-consistency for the point measurement, and the
global-variance sum bound for the polynomial submeasurement `T`.  The helper
submeasurement is the averaged sandwiched polynomial submeasurement built from
`T`, exactly as in the helper-stage application. -/
theorem helper_point_consistency_of_selected_chain_selfConsistency_globalVariance
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    (T : SubMeas (Polynomial params) ι)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hglobal :
      (∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤
          selfImprovementVarianceError params eps delta) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params
        (averagedSandwichedPolynomialSubMeas params strategy T))
      (selfImprovementHelperError params eps delta) := by
  exact
    helper_point_consistency_of_pointConsistencyAddInU_transfer
      (params := params)
      (strategy := strategy)
      (eps := eps)
      (delta := delta)
      (heps := heps)
      (hdelta := hdelta)
      (T := T)
      (Hhat := averagedSandwichedPolynomialSubMeas params strategy T)
      (pointConsistencyAddInU_transfer_of_selected_chain_selfConsistency_globalVariance
        params strategy eps delta heps hdelta T hssc hglobal)

/-- Natural-error transport of point consistency from the helper output to the
projective output, with the submeasurement total-overlap displacement stated
explicitly.

The measurement-valued right-register triangle lemma has no total-overlap term:
both right-register totals are the identity.  In the present application
`polynomialEvaluationFamily params Hhat` and
`polynomialEvaluationFamily params H.toSubMeas` are only submeasurements, so
the total-overlap term
`⟨ψ, A^u_{\mathrm{tot}} ⊗ H^u_{\mathrm{tot}} ψ⟩` must also be transported.
This theorem separates that displacement as the parameter `η`; the remaining
contribution is exactly the square root of the data-processing SDD error.  The
note `docs/paper-gaps/issue-1093-submeasurement-triangle-total-overlap.tex`
records the corresponding discrepancy with the measurement-valued paper step. -/
theorem final_fields_point_consistency_totalGap_natural
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
                (((polynomialEvaluationFamily params Hhat) u).total))|) ≤ η) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta) + η) := by
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
    Preliminaries.triangleSub_right_subMeas_totalGap
      strategy.state (uniformDistribution (Point params)) strategy.isNormalized
      (uniformDistribution_weight_sum_le_one (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params Hhat)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementHelperError params eps delta)
      (selfImprovementDataProcessingError params eps delta) η hhelperPoint
      hdata_right hTotal

/-- Natural-error point-consistency transport when the total-overlap
displacement is supplied as a single right-register total difference.

Since the point measurement is complete and
`polynomialEvaluationFamily params H` has the same total as `H`, the averaged
total-overlap term in `final_fields_point_consistency_totalGap_natural` is
independent of the point `u`.  This theorem records the corresponding reduction
of the issue #1226 obstruction to the scalar difference between the totals of
the two right-register submeasurements. -/
theorem final_fields_point_consistency_totalGap_natural_of_total_difference
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
        ev strategy.state (rightTensor (ι₁ := ι) Hhat.total)| ≤ η) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta) + η) := by
  have hTotalAvg :
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
                (((polynomialEvaluationFamily params Hhat) u).total))|) ≤ η := by
    have hpoint : ∀ u : Point params,
        |ev strategy.state
            (leftTensor (ι₂ := ι)
              (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
              rightTensor (ι₁ := ι)
                (((polynomialEvaluationFamily params H.toSubMeas) u).total)) -
          ev strategy.state
            (leftTensor (ι₂ := ι)
              (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
              rightTensor (ι₁ := ι)
                (((polynomialEvaluationFamily params Hhat) u).total))| =
        |ev strategy.state (rightTensor (ι₁ := ι) H.toSubMeas.total) -
          ev strategy.state (rightTensor (ι₁ := ι) Hhat.total)| := by
      intro u
      rw [pointMeasurement_total_evalFamily_total_ev_eq_rightTensor
          params strategy H.toSubMeas u,
        pointMeasurement_total_evalFamily_total_ev_eq_rightTensor
          params strategy Hhat u]
    have hconst :
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
                  (((polynomialEvaluationFamily params Hhat) u).total))|) =
          avgOver (uniformDistribution (Point params)) (fun _ =>
            |ev strategy.state (rightTensor (ι₁ := ι) H.toSubMeas.total) -
              ev strategy.state (rightTensor (ι₁ := ι) Hhat.total)|) := by
      refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
      intro u
      exact hpoint u
    rw [hconst, avgOver_uniform_const]
    exact hTotal
  exact
    final_fields_point_consistency_totalGap_natural
      params strategy eps delta η hhelperPoint hdata hTotalAvg

/-- Natural-error point-consistency transport under monotone total overlap.

If the projective replacement has no larger right-register total overlap with
the point measurement than the helper submeasurement, the submeasurement
triangle argument has the same natural error as the measurement-valued paper
step:
`selfImprovementHelperError + sqrt selfImprovementDataProcessingError`.  This
is the structural route which avoids introducing the alphabet-size term
`sqrt (#F_q * selfImprovementDataProcessingError)`. -/
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
operators, the pointwise monotone-total hypothesis reduces to the single scalar
comparison between the expectations of `H.total` and `Hhat.total` on the right
register. -/
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
monotonicity and the standard small-error hypotheses.

This is the absorbable form of the projective point-consistency transport:
the monotone-total hypothesis removes the alphabet-size total-overlap term, and
the existing final-stage numerical estimate absorbs
`selfImprovementHelperError + sqrt selfImprovementDataProcessingError` into
`selfImprovementError`. -/
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
expectation in the shared state.  This lemma records the operator-order form of
the monotone-total route, leaving the production of that operator inequality to
the projectivization stage. -/
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

/-- The data-processing SDD comparison controls the total-overlap displacement
which appears in the submeasurement form of the point-consistency triangle.

For each point `u`, the right-register total difference is the sum of the
field-answer differences in the two postprocessed polynomial families.  The
finite-outcome Cauchy--Schwarz estimate
`subMeas_total_ev_gap_abs_le_sqrt_card_qSDD`, averaged over `u`, bounds this
single scalar by
`sqrt (#F_q * ε)`.  The factor `#F_q` records the cost of passing from the
outcomewise state-dependent distance to the total operator. -/
theorem final_fields_total_difference_le_sqrt_card_data
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ε : Error)
    {Hhat : SubMeas (Polynomial params) ι}
    {H : ProjSubMeas (Polynomial params) ι}
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        ε) :
    |ev strategy.state (rightTensor (ι₁ := ι) H.toSubMeas.total) -
      ev strategy.state (rightTensor (ι₁ := ι) Hhat.total)| ≤
      Real.sqrt ((Fintype.card (Fq params) : Error) * ε) := by
  let totalGap : Error :=
    |ev strategy.state (rightTensor (ι₁ := ι) H.toSubMeas.total) -
      ev strategy.state (rightTensor (ι₁ := ι) Hhat.total)|
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
  have hpoint :
      ∀ u : Point params,
        |totalGap| ≤
          Real.sqrt ((Fintype.card (Fq params) : Error) *
            qSDD strategy.state
              (((polynomialEvaluationFamily params Hhat).liftRight) u)
              (((polynomialEvaluationFamily params H.toSubMeas).liftRight) u)) := by
    intro u
    have htot_H :
        (((polynomialEvaluationFamily params H.toSubMeas).liftRight) u).total =
          rightTensor (ι₁ := ι) H.toSubMeas.total := by
      simp [IdxSubMeas.liftRight, polynomialEvaluationFamily, evaluateAt, postprocess_total]
    have htot_Hhat :
        (((polynomialEvaluationFamily params Hhat).liftRight) u).total =
          rightTensor (ι₁ := ι) Hhat.total := by
      simp [IdxSubMeas.liftRight, polynomialEvaluationFamily, evaluateAt, postprocess_total]
    have hgap :=
      Preliminaries.subMeas_total_ev_gap_abs_le_sqrt_card_qSDD
        strategy.state strategy.isNormalized
        (((polynomialEvaluationFamily params Hhat).liftRight) u)
        (((polynomialEvaluationFamily params H.toSubMeas).liftRight) u)
    have hgap' :
        totalGap ≤
          Real.sqrt (Fintype.card (Fq params) : Error) *
            Real.sqrt
              (qSDD strategy.state
                (((polynomialEvaluationFamily params Hhat).liftRight) u)
                (((polynomialEvaluationFamily params H.toSubMeas).liftRight) u)) := by
      simpa [totalGap, htot_H, htot_Hhat, abs_sub_comm] using hgap
    have hcard_nonneg : 0 ≤ (Fintype.card (Fq params) : Error) := by positivity
    have hgap_sqrt :
        totalGap ≤
          Real.sqrt ((Fintype.card (Fq params) : Error) *
            qSDD strategy.state
              (((polynomialEvaluationFamily params Hhat).liftRight) u)
              (((polynomialEvaluationFamily params H.toSubMeas).liftRight) u)) := by
      simpa [Real.sqrt_mul hcard_nonneg] using hgap'
    simpa [totalGap, abs_of_nonneg (abs_nonneg _)] using hgap_sqrt
  have hq_nonneg :
      ∀ u : Point params,
        0 ≤ (Fintype.card (Fq params) : Error) *
          qSDD strategy.state
            (((polynomialEvaluationFamily params Hhat).liftRight) u)
            (((polynomialEvaluationFamily params H.toSubMeas).liftRight) u) := by
    intro u
    exact mul_nonneg (by positivity) (qSDD_nonneg strategy.state _ _)
  have havg :=
    Preliminaries.avgOver_abs_le_sqrt_of_pointwise
      (uniformDistribution (Point params))
      (fun _ : Point params => totalGap)
      (fun u : Point params =>
        (Fintype.card (Fq params) : Error) *
          qSDD strategy.state
            (((polynomialEvaluationFamily params Hhat).liftRight) u)
            (((polynomialEvaluationFamily params H.toSubMeas).liftRight) u))
      hpoint hq_nonneg
      (uniformDistribution_weight_sum_le_one (Point params))
  have hconst :
      avgOver (uniformDistribution (Point params)) (fun _ : Point params => totalGap) =
        totalGap := by
    rw [avgOver_uniform_const]
  have havg_sdd :
      avgOver (uniformDistribution (Point params))
          (fun u : Point params =>
            (Fintype.card (Fq params) : Error) *
              qSDD strategy.state
                (((polynomialEvaluationFamily params Hhat).liftRight) u)
                (((polynomialEvaluationFamily params H.toSubMeas).liftRight) u))
        ≤ (Fintype.card (Fq params) : Error) * ε := by
    rw [avgOver_const_mul]
    exact mul_le_mul_of_nonneg_left hdata_right.squaredDistanceBound (by positivity)
  calc
    |ev strategy.state (rightTensor (ι₁ := ι) H.toSubMeas.total) -
      ev strategy.state (rightTensor (ι₁ := ι) Hhat.total)|
        = totalGap := rfl
    _ = |avgOver (uniformDistribution (Point params))
          (fun _ : Point params => totalGap)| := by
          rw [hconst, abs_of_nonneg (abs_nonneg _)]
    _ ≤ Real.sqrt
        (avgOver (uniformDistribution (Point params))
          (fun u : Point params =>
            (Fintype.card (Fq params) : Error) *
              qSDD strategy.state
                (((polynomialEvaluationFamily params Hhat).liftRight) u)
                (((polynomialEvaluationFamily params H.toSubMeas).liftRight) u))) := havg
    _ ≤ Real.sqrt ((Fintype.card (Fq params) : Error) * ε) :=
        Real.sqrt_le_sqrt havg_sdd

/-- Natural-error point-consistency transport with the total-overlap
displacement bounded internally from the data-processing SDD estimate.

The price of eliminating the explicit total-difference hypothesis is the
additional term `sqrt (#F_q * selfImprovementDataProcessingError)`. -/
theorem final_fields_point_consistency_totalGap_natural_of_data_processing
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
        (selfImprovementDataProcessingError params eps delta)) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta) +
        Real.sqrt ((Fintype.card (Fq params) : Error) *
          selfImprovementDataProcessingError params eps delta)) := by
  exact
    final_fields_point_consistency_totalGap_natural_of_total_difference
      params strategy eps delta
      (Real.sqrt ((Fintype.card (Fq params) : Error) *
        selfImprovementDataProcessingError params eps delta))
      hhelperPoint hdata
      (final_fields_total_difference_le_sqrt_card_data
        params strategy (selfImprovementDataProcessingError params eps delta) hdata)

/-- Literal-threshold point-consistency transport from the helper output to the
projective output.

This wrapper isolates the numerical absorption needed to turn the natural
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

/-- Literal-threshold point-consistency transport with the total-overlap
displacement bounded from the data-processing estimate.

This theorem removes the external total-difference hypothesis.  It keeps the
numerical absorption as an explicit hypothesis, because the Cauchy--Schwarz
argument produces the additional factor `sqrt #F_q`; deciding whether this term
is absorbed by the present threshold or whether the paper-side constants must be
adjusted is a separate numerical question. -/
theorem final_fields_point_consistency_totalGap_of_data_processing
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
    (habsorb :
      selfImprovementHelperError params eps delta +
          Real.sqrt (selfImprovementDataProcessingError params eps delta) +
          Real.sqrt ((Fintype.card (Fq params) : Error) *
            selfImprovementDataProcessingError params eps delta) ≤
        selfImprovementError params eps delta) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementError params eps delta) :=
  MIPStarRE.LDT.ConsRel.mono habsorb
    (final_fields_point_consistency_totalGap_natural_of_data_processing
      params strategy eps delta hhelperPoint hdata)

/-- Literal-threshold point-consistency transport from data-processing with an
explicit finite-field branch.

Under `|F_q| ≤ 8464`, the additional term
`√(#F_q * selfImprovementDataProcessingError)` is absorbed into
`selfImprovementError` by the explicit coefficient estimate in
`final_fields_projective_residual_error_le_selfImprovementError_of_small_alphabet`.

The hypothesis is a concrete branch condition and can be discharged where the
global parameters satisfy the finite-field size constraint. -/
theorem final_fields_point_consistency_totalGap_of_data_processing_of_small_alphabet
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
    (hq_le : Fintype.card (Fq params) ≤ 8464) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementError params eps delta) :=
  MIPStarRE.LDT.ConsRel.mono
    (final_fields_projective_residual_error_le_selfImprovementError_of_small_alphabet
      params eps delta heps heps_le_one hdelta hdelta_le_one hd_le_q hq_le)
    (final_fields_point_consistency_totalGap_natural_of_data_processing
      params strategy eps delta hhelperPoint hdata)


end MIPStarRE.LDT.SelfImprovement
