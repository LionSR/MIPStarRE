import MIPStarRE.LDT.Commutativity.EvaluatedSliceBounds.PhaseTwo

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Phase-4 swap helper: transport any normalized inserted scalar term across the
point-measurement commutation relation.

This is the abstract `commutativityPoints` corollary needed in the middle of
`evaluatedSlice_scalar_chain_bound`: once the inserted factor is packaged as a
family `C q ab` with `∑_{ab} C_{q,ab} C_{q,ab}† ≤ I`, the ordered and reversed
point-measurement products can be swapped at loss `O(√(γ (m+1)))`. -/
private lemma evaluatedSlice_phaseFour_pointSwap_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hnorm : strategy.state.IsNormalized)
    (hgood : strategy.IsGood eps delta gamma)
    (C : EvaluatedSliceQuestion params →
      EvaluatedSliceOutcome params → MIPStarRE.Quantum.Op (ι × ι))
    (hC : ∀ q, ∑ ab : EvaluatedSliceOutcome params, C q ab * (C q ab)ᴴ ≤ 1) :
    let 𝒟 := uniformDistribution (EvaluatedSliceQuestion params)
    let inserted : EvaluatedSliceQuestion params → Error := fun q =>
      ∑ ab : EvaluatedSliceOutcome params,
        ev strategy.state
          (C q ab * (pointMeasurementProductLeft params.next strategy q).outcome ab)
    let swapped : EvaluatedSliceQuestion params → Error := fun q =>
      ∑ ab : EvaluatedSliceOutcome params,
        ev strategy.state
          (C q ab * (pointMeasurementProductRight params.next strategy q).outcome ab)
    |avgOver 𝒟 inserted - avgOver 𝒟 swapped| ≤
      6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
  let 𝒟 : Distribution (EvaluatedSliceQuestion params) :=
    uniformDistribution (EvaluatedSliceQuestion params)
  let A : EvaluatedSliceQuestion params →
      EvaluatedSliceOutcome params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q ab => (pointMeasurementProductLeft params.next strategy q).outcome ab
  let B : EvaluatedSliceQuestion params →
      EvaluatedSliceOutcome params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q ab => (pointMeasurementProductRight params.next strategy q).outcome ab
  let C' : EvaluatedSliceQuestion params → EvaluatedSliceOutcome params → Unit →
      MIPStarRE.Quantum.Op (ι × ι) := fun q ab _ => C q ab
  have h𝒟 :
      ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using
      uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)
  have hgamma_nonneg : 0 ≤ gamma := by
    have : 0 ≤ strategy.diagonalFailureProbability := by
      unfold SymStrat.diagonalFailureProbability
      exact mul_nonneg (by positivity)
        (Finset.sum_nonneg fun j _ =>
          bipartiteConsError_nonneg strategy.state _ _ _)
    exact le_trans this hgood.diagonalLineTest
  have hAB :
      avgOver 𝒟 (fun q => qSDDCore strategy.state (A q) (B q)) ≤
        commutativityPointsError params.next gamma := by
    simpa [𝒟, A, B, qSDDOp] using
      (commutativityPoints
        (params := params.next) strategy eps delta gamma hgood).squaredDistanceBound
  have hC' :
      ∀ q,
        ∑ ab : EvaluatedSliceOutcome params,
            (∑ _ : Unit, C' q ab ()) * (∑ _ : Unit, C' q ab ())ᴴ ≤ 1 := by
    intro q
    simpa [C'] using hC q
  have hclose :=
    MIPStarRE.LDT.Preliminaries.closenessOfIP
      strategy.state hnorm 𝒟 h𝒟 A B C' (commutativityPointsError params.next gamma) hAB hC'
  have hsqrt32_le_six : Real.sqrt (32 : Error) ≤ 6 := by
    have hsqrt32_nonneg : 0 ≤ Real.sqrt (32 : Error) := Real.sqrt_nonneg _
    nlinarith [Real.sq_sqrt (show 0 ≤ (32 : Error) by positivity)]
  have hmul_nonneg :
      0 ≤ gamma * (((params.m + 1 : ℕ)) : Error) := by
    positivity
  calc
    |avgOver 𝒟
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          ev strategy.state
            (C q ab * (pointMeasurementProductLeft params.next strategy q).outcome ab)) -
      avgOver 𝒟
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          ev strategy.state
            (C q ab * (pointMeasurementProductRight params.next strategy q).outcome ab))|
      ≤ Real.sqrt (commutativityPointsError params.next gamma) := by
          simpa [𝒟, A, B, C'] using hclose
    _ = Real.sqrt (32 : Error) * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
          rw [commutativityPointsError, Parameters.next]
          have hring :
              32 * gamma * (((params.m + 1 : ℕ)) : Error) =
                (32 : Error) * (gamma * (((params.m + 1 : ℕ)) : Error)) := by
            ring
          rw [hring, Real.sqrt_mul (show 0 ≤ (32 : Error) by positivity)]
    _ ≤ 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
          exact mul_le_mul_of_nonneg_right hsqrt32_le_six (Real.sqrt_nonneg _)

/-- Fixed-outcome expansion for the phase-5 `G^x` insertion summand.

This is the local scalar bridge that lines the explicit swapped term up with the
left family in `gCommStabilityTwo_overlap`. -/
private lemma evaluatedSlice_phaseFive_left_weighted_outcome
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (q : EvaluatedSliceQuestion params)
    (gb : StabilityTwoOutcome params) :
    (commDataProcessedGStabilityTwoLeft params strategy family G q).outcome gb *
        rightTensor (ι₁ := ι)
          (CFC.sqrt ((G (pointHeight params q.1)).outcome gb.1)) =
      leftTensor (ι₂ := ι)
          (((evaluatedSliceFirstFactor params family q).outcome
              (gb.1 (truncatePoint params q.1))) *
            ((evaluatedSliceSecondFactor params family q).outcome gb.2) *
            ((G (pointHeight params q.1)).total)) *
        rightTensor (ι₁ := ι) ((G (pointHeight params q.1)).outcome gb.1) := by
  have hsqrt :
      CFC.sqrt ((G (pointHeight params q.1)).outcome gb.1) *
          CFC.sqrt ((G (pointHeight params q.1)).outcome gb.1) =
        (G (pointHeight params q.1)).outcome gb.1 := by
    simpa using
      sqrt_subMeas_outcome_mul_self (G (pointHeight params q.1)) gb.1
  have hsqrt' :
      CFC.sqrt ((family.meas (pointHeight params q.1)).outcome gb.1) *
          CFC.sqrt ((family.meas (pointHeight params q.1)).outcome gb.1) =
        (family.meas (pointHeight params q.1)).outcome gb.1 := by
    simpa [hG] using hsqrt
  rw [commDataProcessedGStabilityTwoLeft_outcome]
  simp [evaluatedSliceProductLeft, leftOrderedProductOpFamily, OpFamily.leftPlacedOpFamily,
    orderedProductOpFamily, fullSliceFirstFactor, fullSliceQuestionOfEvaluatedSlice, hG,
    leftTensor_mul_leftTensor, rightTensor_mul_rightTensor, mul_assoc, hsqrt']

/-- Fixed-outcome expansion for the phase-5 `G^x` removal summand. -/
private lemma evaluatedSlice_phaseFive_right_weighted_outcome
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (q : EvaluatedSliceQuestion params)
    (gb : StabilityTwoOutcome params) :
    (commDataProcessedGStabilityTwoRight params strategy family G q).outcome gb *
        rightTensor (ι₁ := ι)
          (CFC.sqrt ((G (pointHeight params q.1)).outcome gb.1)) =
      leftTensor (ι₂ := ι)
          (((evaluatedSliceFirstFactor params family q).outcome
              (gb.1 (truncatePoint params q.1))) *
            ((evaluatedSliceSecondFactor params family q).outcome gb.2)) *
        rightTensor (ι₁ := ι) ((G (pointHeight params q.1)).outcome gb.1) := by
  have hsqrt :
      CFC.sqrt ((G (pointHeight params q.1)).outcome gb.1) *
          CFC.sqrt ((G (pointHeight params q.1)).outcome gb.1) =
        (G (pointHeight params q.1)).outcome gb.1 := by
    simpa using
      sqrt_subMeas_outcome_mul_self (G (pointHeight params q.1)) gb.1
  rw [commDataProcessedGStabilityTwoRight_outcome]
  simp [orderedProductOpFamily, rightTensor_mul_rightTensor, mul_assoc, hsqrt]

/-- Rewrite the phase-5 scalar comparison into the weighted stability-two form.

This is the bookkeeping bridge between the explicit swapped term and the
`commDataProcessedGStabilityTwoLeft` / `commDataProcessedGStabilityTwoRight`
families used by `gCommStabilityTwo_overlap`. -/
private lemma evaluatedSlice_phaseFive_scalar_rewrite
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas) :
    let 𝒟 := uniformDistribution (EvaluatedSliceQuestion params)
    let inserted : EvaluatedSliceQuestion params → Error := fun q =>
      ∑ gb : StabilityTwoOutcome params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              (((evaluatedSliceFirstFactor params family q).outcome
                  (gb.1 (truncatePoint params q.1))) *
                ((evaluatedSliceSecondFactor params family q).outcome gb.2) *
                ((G (pointHeight params q.1)).total)) *
            rightTensor (ι₁ := ι) ((G (pointHeight params q.1)).outcome gb.1))
    let removed : EvaluatedSliceQuestion params → Error := fun q =>
      ∑ gb : StabilityTwoOutcome params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              (((evaluatedSliceFirstFactor params family q).outcome
                  (gb.1 (truncatePoint params q.1))) *
                ((evaluatedSliceSecondFactor params family q).outcome gb.2)) *
            rightTensor (ι₁ := ι) ((G (pointHeight params q.1)).outcome gb.1))
    avgOver 𝒟 inserted - avgOver 𝒟 removed =
      avgOver 𝒟 (fun q =>
        ∑ gb : StabilityTwoOutcome params,
          ((ev strategy.state <|
              (commDataProcessedGStabilityTwoLeft params strategy family G q).outcome gb *
                rightTensor (ι₁ := ι)
                  (CFC.sqrt ((G (pointHeight params q.1)).outcome gb.1))) -
            (ev strategy.state <|
              (commDataProcessedGStabilityTwoRight params strategy family G q).outcome gb *
                rightTensor (ι₁ := ι)
                  (CFC.sqrt ((G (pointHeight params q.1)).outcome gb.1))))) := by
  dsimp
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          ∑ gb : StabilityTwoOutcome params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  (((evaluatedSliceFirstFactor params family q).outcome
                      (gb.1 (truncatePoint params q.1))) *
                    ((evaluatedSliceSecondFactor params family q).outcome gb.2) *
                    ((G (pointHeight params q.1)).total)) *
                rightTensor (ι₁ := ι) ((G (pointHeight params q.1)).outcome gb.1))) -
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          ∑ gb : StabilityTwoOutcome params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  (((evaluatedSliceFirstFactor params family q).outcome
                      (gb.1 (truncatePoint params q.1))) *
                    ((evaluatedSliceSecondFactor params family q).outcome gb.2)) *
                rightTensor (ι₁ := ι) ((G (pointHeight params q.1)).outcome gb.1)))
      = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q =>
            ∑ gb : StabilityTwoOutcome params,
              ev strategy.state
                (leftTensor (ι₂ := ι)
                    (((evaluatedSliceFirstFactor params family q).outcome
                        (gb.1 (truncatePoint params q.1))) *
                      ((evaluatedSliceSecondFactor params family q).outcome gb.2) *
                      ((G (pointHeight params q.1)).total)) *
                  rightTensor (ι₁ := ι) ((G (pointHeight params q.1)).outcome gb.1)) -
            ∑ gb : StabilityTwoOutcome params,
              ev strategy.state
                (leftTensor (ι₂ := ι)
                    (((evaluatedSliceFirstFactor params family q).outcome
                        (gb.1 (truncatePoint params q.1))) *
                      ((evaluatedSliceSecondFactor params family q).outcome gb.2)) *
                  rightTensor (ι₁ := ι) ((G (pointHeight params q.1)).outcome gb.1))) := by
            simp [avgOver, Finset.sum_sub_distrib, mul_sub]
    _ = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q =>
            ∑ gb : StabilityTwoOutcome params,
              (ev strategy.state
                (leftTensor (ι₂ := ι)
                    (((evaluatedSliceFirstFactor params family q).outcome
                        (gb.1 (truncatePoint params q.1))) *
                      ((evaluatedSliceSecondFactor params family q).outcome gb.2) *
                      ((G (pointHeight params q.1)).total)) *
                  rightTensor (ι₁ := ι) ((G (pointHeight params q.1)).outcome gb.1)) -
              ev strategy.state
                (leftTensor (ι₂ := ι)
                    (((evaluatedSliceFirstFactor params family q).outcome
                        (gb.1 (truncatePoint params q.1))) *
                      ((evaluatedSliceSecondFactor params family q).outcome gb.2)) *
                  rightTensor (ι₁ := ι) ((G (pointHeight params q.1)).outcome gb.1)))) := by
            apply avgOver_congr
            intro q
            rw [← Finset.sum_sub_distrib]
    _ = avgOver (uniformDistribution (EvaluatedSliceQuestion params)) (fun q =>
          ∑ gb : StabilityTwoOutcome params,
            ((ev strategy.state <|
                (commDataProcessedGStabilityTwoLeft params strategy family G q).outcome gb *
                  rightTensor (ι₁ := ι)
                    (CFC.sqrt ((G (pointHeight params q.1)).outcome gb.1))) -
              (ev strategy.state <|
                (commDataProcessedGStabilityTwoRight params strategy family G q).outcome gb *
                  rightTensor (ι₁ := ι)
                    (CFC.sqrt ((G (pointHeight params q.1)).outcome gb.1))))) := by
            apply avgOver_congr
            intro q
            refine Finset.sum_congr rfl ?_
            intro gb _
            rw [evaluatedSlice_phaseFive_left_weighted_outcome params strategy family G hG q gb,
              evaluatedSlice_phaseFive_right_weighted_outcome params strategy family G q gb]



end MIPStarRE.LDT.Commutativity
