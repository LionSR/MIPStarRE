import MIPStarRE.LDT.Commutativity.EvaluatedSliceBounds.PhaseOneThree

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Fixed-outcome expansion for the phase-2 `G^y` insertion summand.

This is the local scalar bridge used to line up the explicit inserted term with
the `commDataProcessedGStabilityOneLeft` family before applying
`gCommStability_overlap`. -/
private lemma evaluatedSlice_phaseTwo_left_weighted_outcome
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (q : EvaluatedSliceQuestion params)
    (ah : StabilityOneOutcome params) :
    (commDataProcessedGStabilityOneLeft params strategy family G q).outcome ah *
        rightTensor (ι₁ := ι)
          (CFC.sqrt ((G (pointHeight params q.2)).outcome ah.2)) =
      leftTensor (ι₂ := ι)
          (((evaluatedSliceFirstFactor params family q).outcome ah.1) *
            ((evaluatedSliceSecondFactor params family q).outcome
              (ah.2 (truncatePoint params q.2))) *
            ((evaluatedSliceFirstFactor params family q).outcome ah.1) *
            ((G (pointHeight params q.2)).total)) *
        rightTensor (ι₁ := ι) ((G (pointHeight params q.2)).outcome ah.2) := by
  have hsqrt :
      CFC.sqrt ((G (pointHeight params q.2)).outcome ah.2) *
          CFC.sqrt ((G (pointHeight params q.2)).outcome ah.2) =
        (G (pointHeight params q.2)).outcome ah.2 := by
    simpa using
      sqrt_subMeas_outcome_mul_self (G (pointHeight params q.2)) ah.2
  rw [commDataProcessedGStabilityOneLeft_outcome]
  have hleft_raw :
      (leftPlacedSubMeas (ιB := ι)
          (evaluatedSliceSandwichRaw params strategy family q)).outcome
          (ah.1, ah.2 (truncatePoint params q.2)) *
        leftTensor (ι₂ := ι)
          ((fullSliceSecondFactor params family
            (fullSliceQuestionOfEvaluatedSlice params q)).total) =
      leftTensor (ι₂ := ι)
        (((evaluatedSliceSandwichRaw params strategy family q).outcome
            (ah.1, ah.2 (truncatePoint params q.2))) *
          ((fullSliceSecondFactor params family
            (fullSliceQuestionOfEvaluatedSlice params q)).total)) := by
    calc
      (leftPlacedSubMeas (ιB := ι)
            (evaluatedSliceSandwichRaw params strategy family q)).outcome
            (ah.1, ah.2 (truncatePoint params q.2)) *
          leftTensor (ι₂ := ι)
            ((fullSliceSecondFactor params family
              (fullSliceQuestionOfEvaluatedSlice params q)).total)
        = leftTensor (ι₂ := ι)
            ((evaluatedSliceSandwichRaw params strategy family q).outcome
              (ah.1, ah.2 (truncatePoint params q.2))) *
          leftTensor (ι₂ := ι)
            ((fullSliceSecondFactor params family
              (fullSliceQuestionOfEvaluatedSlice params q)).total) := by
              rfl
      _ = leftTensor (ι₂ := ι)
            (((evaluatedSliceSandwichRaw params strategy family q).outcome
                (ah.1, ah.2 (truncatePoint params q.2))) *
              ((fullSliceSecondFactor params family
                (fullSliceQuestionOfEvaluatedSlice params q)).total)) := by
              rw [leftTensor_mul_leftTensor]
  have hsandwich :
      ((evaluatedSliceSandwichRaw params strategy family q).outcome
          (ah.1, ah.2 (truncatePoint params q.2))) *
        ((fullSliceSecondFactor params family
          (fullSliceQuestionOfEvaluatedSlice params q)).total) =
      ((evaluatedSliceFirstFactor params family q).outcome ah.1) *
        ((evaluatedSliceSecondFactor params family q).outcome
          (ah.2 (truncatePoint params q.2))) *
        ((evaluatedSliceFirstFactor params family q).outcome ah.1) *
        ((G (pointHeight params q.2)).total) := by
    simp [evaluatedSliceSandwichRaw, sandwichByOuterSubMeas,
      fullSliceSecondFactor, fullSliceQuestionOfEvaluatedSlice, hG, mul_assoc]
  have hleft :
      (leftPlacedSubMeas (ιB := ι)
          (evaluatedSliceSandwichRaw params strategy family q)).outcome
          (ah.1, ah.2 (truncatePoint params q.2)) *
        leftTensor (ι₂ := ι)
          ((fullSliceSecondFactor params family
            (fullSliceQuestionOfEvaluatedSlice params q)).total) =
      leftTensor (ι₂ := ι)
        (((evaluatedSliceFirstFactor params family q).outcome ah.1) *
          ((evaluatedSliceSecondFactor params family q).outcome
            (ah.2 (truncatePoint params q.2))) *
          ((evaluatedSliceFirstFactor params family q).outcome ah.1) *
          ((G (pointHeight params q.2)).total)) := by
    rw [hleft_raw, hsandwich]
  calc
    (leftPlacedSubMeas (ιB := ι)
          (evaluatedSliceSandwichRaw params strategy family q)).outcome
          (ah.1, ah.2 (truncatePoint params q.2)) *
        leftTensor (ι₂ := ι)
          ((fullSliceSecondFactor params family
            (fullSliceQuestionOfEvaluatedSlice params q)).total) *
        rightTensor (ι₁ := ι) (CFC.sqrt ((G (pointHeight params q.2)).outcome ah.2)) *
        rightTensor (ι₁ := ι) (CFC.sqrt ((G (pointHeight params q.2)).outcome ah.2))
      = ((leftPlacedSubMeas (ιB := ι)
            (evaluatedSliceSandwichRaw params strategy family q)).outcome
            (ah.1, ah.2 (truncatePoint params q.2)) *
          leftTensor (ι₂ := ι)
            ((fullSliceSecondFactor params family
              (fullSliceQuestionOfEvaluatedSlice params q)).total)) *
          (rightTensor (ι₁ := ι) (CFC.sqrt ((G (pointHeight params q.2)).outcome ah.2)) *
            rightTensor (ι₁ := ι) (CFC.sqrt ((G (pointHeight params q.2)).outcome ah.2))) := by
          simp [mul_assoc]
    _ = ((leftPlacedSubMeas (ιB := ι)
            (evaluatedSliceSandwichRaw params strategy family q)).outcome
            (ah.1, ah.2 (truncatePoint params q.2)) *
          leftTensor (ι₂ := ι)
            ((fullSliceSecondFactor params family
              (fullSliceQuestionOfEvaluatedSlice params q)).total)) *
          rightTensor (ι₁ := ι) ((G (pointHeight params q.2)).outcome ah.2) := by
          rw [rightTensor_mul_rightTensor, hsqrt]
    _ = leftTensor (ι₂ := ι)
          (((evaluatedSliceFirstFactor params family q).outcome ah.1) *
            ((evaluatedSliceSecondFactor params family q).outcome
              (ah.2 (truncatePoint params q.2))) *
            ((evaluatedSliceFirstFactor params family q).outcome ah.1) *
            ((G (pointHeight params q.2)).total)) *
          rightTensor (ι₁ := ι) ((G (pointHeight params q.2)).outcome ah.2) := by
          rw [hleft]

/-- Fixed-outcome expansion for the phase-2 `G^y` removal summand. -/
private lemma evaluatedSlice_phaseTwo_right_weighted_outcome
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (q : EvaluatedSliceQuestion params)
    (ah : StabilityOneOutcome params) :
    (commDataProcessedGStabilityOneRight params strategy family G q).outcome ah *
        rightTensor (ι₁ := ι)
          (CFC.sqrt ((G (pointHeight params q.2)).outcome ah.2)) =
      leftTensor (ι₂ := ι)
          (((evaluatedSliceFirstFactor params family q).outcome ah.1) *
            ((evaluatedSliceSecondFactor params family q).outcome
              (ah.2 (truncatePoint params q.2))) *
            ((evaluatedSliceFirstFactor params family q).outcome ah.1)) *
        rightTensor (ι₁ := ι) ((G (pointHeight params q.2)).outcome ah.2) := by
  have hsqrt :
      CFC.sqrt ((G (pointHeight params q.2)).outcome ah.2) *
          CFC.sqrt ((G (pointHeight params q.2)).outcome ah.2) =
        (G (pointHeight params q.2)).outcome ah.2 := by
    simpa using
      sqrt_subMeas_outcome_mul_self (G (pointHeight params q.2)) ah.2
  rw [commDataProcessedGStabilityOneRight_outcome]
  simp [evaluatedSliceSandwichRaw, sandwichByOuterSubMeas,
    rightTensor_mul_rightTensor, mul_assoc, hsqrt]

/-- Rewrite the phase-2 scalar comparison into the weighted stability-one form.

This is the bookkeeping bridge between the explicit `G^y`-inserted / `G^y`-removed
summands and the stability-one operator families used by
`gCommStability_overlap`. -/
private lemma evaluatedSlice_phaseTwo_scalar_rewrite
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas) :
    let 𝒟 := uniformDistribution (EvaluatedSliceQuestion params)
    let inserted : EvaluatedSliceQuestion params → Error := fun q =>
      ∑ ah : StabilityOneOutcome params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              (((evaluatedSliceFirstFactor params family q).outcome ah.1) *
                ((evaluatedSliceSecondFactor params family q).outcome
                  (ah.2 (truncatePoint params q.2))) *
                ((evaluatedSliceFirstFactor params family q).outcome ah.1) *
                ((G (pointHeight params q.2)).total)) *
            rightTensor (ι₁ := ι) ((G (pointHeight params q.2)).outcome ah.2))
    let removed : EvaluatedSliceQuestion params → Error := fun q =>
      ∑ ah : StabilityOneOutcome params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              (((evaluatedSliceFirstFactor params family q).outcome ah.1) *
                ((evaluatedSliceSecondFactor params family q).outcome
                  (ah.2 (truncatePoint params q.2))) *
                ((evaluatedSliceFirstFactor params family q).outcome ah.1)) *
            rightTensor (ι₁ := ι) ((G (pointHeight params q.2)).outcome ah.2))
    avgOver 𝒟 inserted - avgOver 𝒟 removed =
      avgOver 𝒟 (fun q =>
        ∑ ah : StabilityOneOutcome params,
          ((ev strategy.state <|
              (commDataProcessedGStabilityOneLeft params strategy family G q).outcome ah *
                rightTensor (ι₁ := ι)
                  (CFC.sqrt ((G (pointHeight params q.2)).outcome ah.2))) -
            (ev strategy.state <|
              (commDataProcessedGStabilityOneRight params strategy family G q).outcome ah *
                rightTensor (ι₁ := ι)
                  (CFC.sqrt ((G (pointHeight params q.2)).outcome ah.2))))) := by
  dsimp
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          ∑ ah : StabilityOneOutcome params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  (((evaluatedSliceFirstFactor params family q).outcome ah.1) *
                    ((evaluatedSliceSecondFactor params family q).outcome
                      (ah.2 (truncatePoint params q.2))) *
                    ((evaluatedSliceFirstFactor params family q).outcome ah.1) *
                    ((G (pointHeight params q.2)).total)) *
                rightTensor (ι₁ := ι) ((G (pointHeight params q.2)).outcome ah.2))) -
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          ∑ ah : StabilityOneOutcome params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  (((evaluatedSliceFirstFactor params family q).outcome ah.1) *
                    ((evaluatedSliceSecondFactor params family q).outcome
                      (ah.2 (truncatePoint params q.2))) *
                    ((evaluatedSliceFirstFactor params family q).outcome ah.1)) *
                rightTensor (ι₁ := ι) ((G (pointHeight params q.2)).outcome ah.2)))
      = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q =>
            ∑ ah : StabilityOneOutcome params,
              ev strategy.state
                (leftTensor (ι₂ := ι)
                    (((evaluatedSliceFirstFactor params family q).outcome ah.1) *
                      ((evaluatedSliceSecondFactor params family q).outcome
                        (ah.2 (truncatePoint params q.2))) *
                      ((evaluatedSliceFirstFactor params family q).outcome ah.1) *
                      ((G (pointHeight params q.2)).total)) *
                  rightTensor (ι₁ := ι) ((G (pointHeight params q.2)).outcome ah.2)) -
              ∑ ah : StabilityOneOutcome params,
                ev strategy.state
                  (leftTensor (ι₂ := ι)
                      (((evaluatedSliceFirstFactor params family q).outcome ah.1) *
                        ((evaluatedSliceSecondFactor params family q).outcome
                          (ah.2 (truncatePoint params q.2))) *
                        ((evaluatedSliceFirstFactor params family q).outcome ah.1)) *
                    rightTensor (ι₁ := ι) ((G (pointHeight params q.2)).outcome ah.2))) := by
            simp [avgOver, Finset.sum_sub_distrib, mul_sub]
    _ = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q =>
            ∑ ah : StabilityOneOutcome params,
              ((ev strategy.state
                  (leftTensor (ι₂ := ι)
                      (((evaluatedSliceFirstFactor params family q).outcome ah.1) *
                        ((evaluatedSliceSecondFactor params family q).outcome
                          (ah.2 (truncatePoint params q.2))) *
                        ((evaluatedSliceFirstFactor params family q).outcome ah.1) *
                        ((G (pointHeight params q.2)).total)) *
                    rightTensor (ι₁ := ι) ((G (pointHeight params q.2)).outcome ah.2))) -
                ev strategy.state
                  (leftTensor (ι₂ := ι)
                      (((evaluatedSliceFirstFactor params family q).outcome ah.1) *
                        ((evaluatedSliceSecondFactor params family q).outcome
                          (ah.2 (truncatePoint params q.2))) *
                        ((evaluatedSliceFirstFactor params family q).outcome ah.1)) *
                    rightTensor (ι₁ := ι) ((G (pointHeight params q.2)).outcome ah.2)))) := by
            apply avgOver_congr
            intro q
            rw [← Finset.sum_sub_distrib]
    _ = avgOver (uniformDistribution (EvaluatedSliceQuestion params)) (fun q =>
          ∑ ah : StabilityOneOutcome params,
            ((ev strategy.state <|
                (commDataProcessedGStabilityOneLeft params strategy family G q).outcome ah *
                  rightTensor (ι₁ := ι)
                    (CFC.sqrt ((G (pointHeight params q.2)).outcome ah.2))) -
              (ev strategy.state <|
                (commDataProcessedGStabilityOneRight params strategy family G q).outcome ah *
                  rightTensor (ι₁ := ι)
                    (CFC.sqrt ((G (pointHeight params q.2)).outcome ah.2))))) := by
            apply avgOver_congr
            intro q
            refine Finset.sum_congr rfl ?_
            intro ah _
            rw [evaluatedSlice_phaseTwo_left_weighted_outcome params strategy family G hG q ah,
              evaluatedSlice_phaseTwo_right_weighted_outcome params strategy family G q ah]



end MIPStarRE.LDT.Commutativity
