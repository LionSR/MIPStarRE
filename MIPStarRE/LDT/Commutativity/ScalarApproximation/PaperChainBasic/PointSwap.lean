import MIPStarRE.LDT.Commutativity.ScalarApproximation.Core
import MIPStarRE.LDT.Commutativity.EvaluatedSliceCommutation.Consequences

/-!
# Point-swap bound for the evaluated-slice paper chain

This file contains the right-register point-swap estimate used in the
paper-faithful scalar chain for `lem:comm-data-processed-g`.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma qSDDOp_rightPlaced_eq_leftPlaced
    {Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (A B : OpFamily Outcome ι) :
    qSDDOp ψ
      (OpFamily.rightPlacedOpFamily (ιA := ι) A)
      (OpFamily.rightPlacedOpFamily (ιA := ι) B) =
    qSDDOp ψ
      (OpFamily.leftPlacedOpFamily (ιB := ι) A)
      (OpFamily.leftPlacedOpFamily (ιB := ι) B) := by
  unfold qSDDOp qSDDCore
  refine Finset.sum_congr rfl ?_
  intro a _
  let D : MIPStarRE.Quantum.Op ι := A.outcome a - B.outcome a
  have hright_diff :
      (OpFamily.rightPlacedOpFamily (ιA := ι) A).outcome a -
        (OpFamily.rightPlacedOpFamily (ιA := ι) B).outcome a =
      rightTensor (ι₁ := ι) D := by
    simpa [OpFamily.rightPlacedOpFamily, rightTensor, opTensor, D] using
      (MIPStarRE.Quantum.kronecker_sub_right
        (A := (1 : MIPStarRE.Quantum.Op ι))
        (B₁ := A.outcome a) (B₂ := B.outcome a))
  have hleft_diff :
      (OpFamily.leftPlacedOpFamily (ιB := ι) A).outcome a -
        (OpFamily.leftPlacedOpFamily (ιB := ι) B).outcome a =
      leftTensor (ι₂ := ι) D := by
    simpa [OpFamily.leftPlacedOpFamily, D] using
      leftTensor_sub (ι₁ := ι) (ι₂ := ι) (A.outcome a) (B.outcome a)
  rw [hright_diff, hleft_diff]
  calc
    ev ψ ((rightTensor (ι₁ := ι) D)ᴴ * rightTensor (ι₁ := ι) D)
        = ev ψ (rightTensor (ι₁ := ι) (Dᴴ * D)) := by
          rw [show (rightTensor (ι₁ := ι) D)ᴴ = rightTensor (ι₁ := ι) Dᴴ by
            simpa [rightTensor, opTensor] using
              (conjTranspose_opTensor (ι₁ := ι) (ι₂ := ι) (1 : MIPStarRE.Quantum.Op ι) D)]
          rw [rightTensor_mul_rightTensor]
    _ = ev ψ (leftTensor (ι₂ := ι) (Dᴴ * D)) := by
          rw [← hperm.swap_ev (Dᴴ * D)]
    _ = ev ψ ((leftTensor (ι₂ := ι) D)ᴴ * leftTensor (ι₂ := ι) D) := by
          rw [show (leftTensor (ι₂ := ι) D)ᴴ = leftTensor (ι₂ := ι) Dᴴ by
            simpa [leftTensor, opTensor] using
              (conjTranspose_opTensor (ι₁ := ι) (ι₂ := ι) D (1 : MIPStarRE.Quantum.Op ι))]
          rw [leftTensor_mul_leftTensor]

lemma evaluatedSlice_phaseFour_pointSwap_right_bound_of_commutativityPoints
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (gamma : Error)
    (hnorm : strategy.state.IsNormalized)
    (hcomm :
      SDDOpRel strategy.state
        (uniformDistribution (PointPairQuestion params.next))
        (pointMeasurementProductLeft params.next strategy)
        (pointMeasurementProductRight params.next strategy)
        (commutativityPointsError params.next gamma))
    (C : EvaluatedSliceQuestion params →
      EvaluatedSliceOutcome params → MIPStarRE.Quantum.Op (ι × ι))
    (hC : ∀ q, ∑ ab : EvaluatedSliceOutcome params, C q ab * (C q ab)ᴴ ≤ 1) :
    let 𝒟 := uniformDistribution (EvaluatedSliceQuestion params)
    let inserted : EvaluatedSliceQuestion params → Error := fun q =>
      ∑ ab : EvaluatedSliceOutcome params,
        ev strategy.state
          (C q ab *
            rightTensor (ι₁ := ι)
              (((evaluatedSlicePointMeas params strategy q.2).outcome ab.2) *
               ((evaluatedSlicePointMeas params strategy q.1).outcome ab.1)))
    let swapped : EvaluatedSliceQuestion params → Error := fun q =>
      ∑ ab : EvaluatedSliceOutcome params,
        ev strategy.state
          (C q ab *
            rightTensor (ι₁ := ι)
              (((evaluatedSlicePointMeas params strategy q.1).outcome ab.1) *
               ((evaluatedSlicePointMeas params strategy q.2).outcome ab.2)))
    |avgOver 𝒟 inserted - avgOver 𝒟 swapped| ≤
      6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
  let 𝒟 : Distribution (EvaluatedSliceQuestion params) :=
    uniformDistribution (EvaluatedSliceQuestion params)
  let Rrev : EvaluatedSliceQuestion params →
      EvaluatedSliceOutcome params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q ab => rightTensor (ι₁ := ι)
      (((evaluatedSlicePointMeas params strategy q.2).outcome ab.2) *
        ((evaluatedSlicePointMeas params strategy q.1).outcome ab.1))
  let Rord : EvaluatedSliceQuestion params →
      EvaluatedSliceOutcome params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q ab => rightTensor (ι₁ := ι)
      (((evaluatedSlicePointMeas params strategy q.1).outcome ab.1) *
        ((evaluatedSlicePointMeas params strategy q.2).outcome ab.2))
  let C' : EvaluatedSliceQuestion params → EvaluatedSliceOutcome params → Unit →
      MIPStarRE.Quantum.Op (ι × ι) := fun q ab _ => C q ab
  have h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)
  let Lrev : EvaluatedSliceQuestion params → OpFamily (EvaluatedSliceOutcome params) (ι × ι) :=
    fun q => OpFamily.leftPlacedOpFamily (ιB := ι) <|
      reversedProductOpFamily
        ((strategy.pointMeasurement q.1).toSubMeas : SubMeas (Fq params.next) ι)
        ((strategy.pointMeasurement q.2).toSubMeas : SubMeas (Fq params.next) ι)
  let Lord : EvaluatedSliceQuestion params → OpFamily (EvaluatedSliceOutcome params) (ι × ι) :=
    fun q => OpFamily.leftPlacedOpFamily (ιB := ι) <|
      orderedProductOpFamily
        ((strategy.pointMeasurement q.1).toSubMeas : SubMeas (Fq params.next) ι)
        ((strategy.pointMeasurement q.2).toSubMeas : SubMeas (Fq params.next) ι)
  have hleft :
      SDDOpRel strategy.state 𝒟 Lord Lrev (commutativityPointsError params.next gamma) := by
    simpa [𝒟, Lord, Lrev, pointMeasurementProductLeft, pointMeasurementProductRight,
      EvaluatedSliceQuestion, EvaluatedSliceOutcome, Parameters.next] using hcomm
  have hleft_symm :
      SDDOpRel strategy.state 𝒟 Lrev Lord (commutativityPointsError params.next gamma) := by
    exact sddOpRel_symm strategy.state 𝒟 Lord Lrev
      (commutativityPointsError params.next gamma) hleft
  have hAB : avgOver 𝒟 (fun q => qSDDCore strategy.state (Rrev q) (Rord q)) ≤
      commutativityPointsError params.next gamma := by
    rcases hleft_symm with ⟨h⟩
    calc
      avgOver 𝒟 (fun q => qSDDCore strategy.state (Rrev q) (Rord q))
          = avgOver 𝒟 (fun q => qSDDOp strategy.state (Lrev q) (Lord q)) := by
            apply avgOver_congr
            intro q
            simpa [qSDDOp, Lrev, Lord, Rrev, Rord, evaluatedSlicePointMeas,
              OpFamily.leftPlacedOpFamily, OpFamily.rightPlacedOpFamily,
              reversedProductOpFamily, orderedProductOpFamily, Parameters.next] using
              (qSDDOp_rightPlaced_eq_leftPlaced (ι := ι) strategy.state strategy.permInvState
                (reversedProductOpFamily
                  ((strategy.pointMeasurement q.1).toSubMeas : SubMeas (Fq params.next) ι)
                  ((strategy.pointMeasurement q.2).toSubMeas : SubMeas (Fq params.next) ι))
                (orderedProductOpFamily
                  ((strategy.pointMeasurement q.1).toSubMeas : SubMeas (Fq params.next) ι)
                  ((strategy.pointMeasurement q.2).toSubMeas : SubMeas (Fq params.next) ι)))
      _ ≤ commutativityPointsError params.next gamma := by
            simpa [sddErrorOp] using h
  have hC' :
      ∀ q,
        ∑ ab : EvaluatedSliceOutcome params,
            (∑ _ : Unit, C' q ab ()) * (∑ _ : Unit, C' q ab ())ᴴ ≤ 1 := by
    intro q
    simpa [C'] using hC q
  have hclose :=
    MIPStarRE.LDT.Preliminaries.closenessOfIP
      strategy.state hnorm 𝒟 h𝒟 Rrev Rord C' (commutativityPointsError params.next gamma) hAB hC'
  have hsqrt32_le_six : Real.sqrt (32 : Error) ≤ 6 := by
    have hsqrt32_nonneg : 0 ≤ Real.sqrt (32 : Error) := Real.sqrt_nonneg _
    nlinarith [Real.sq_sqrt (show 0 ≤ (32 : Error) by positivity)]
  calc
    |avgOver 𝒟
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          ev strategy.state (C q ab * Rrev q ab)) -
      avgOver 𝒟
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          ev strategy.state (C q ab * Rord q ab))|
      ≤ Real.sqrt (commutativityPointsError params.next gamma) := by
          simpa [𝒟, Rrev, Rord, C'] using hclose
    _ = Real.sqrt (32 : Error) * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
          rw [commutativityPointsError, Parameters.next]
          have hring :
              32 * gamma * (((params.m + 1 : ℕ)) : Error) =
                (32 : Error) * (gamma * (((params.m + 1 : ℕ)) : Error)) := by
            ring
          rw [hring, Real.sqrt_mul (show 0 ≤ (32 : Error) by positivity)]
    _ ≤ 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
          exact mul_le_mul_of_nonneg_right hsqrt32_le_six (Real.sqrt_nonneg _)

lemma evaluatedSlice_phaseFour_pointSwap_right_bound
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
          (C q ab *
            rightTensor (ι₁ := ι)
              (((evaluatedSlicePointMeas params strategy q.2).outcome ab.2) *
               ((evaluatedSlicePointMeas params strategy q.1).outcome ab.1)))
    let swapped : EvaluatedSliceQuestion params → Error := fun q =>
      ∑ ab : EvaluatedSliceOutcome params,
        ev strategy.state
          (C q ab *
            rightTensor (ι₁ := ι)
              (((evaluatedSlicePointMeas params strategy q.1).outcome ab.1) *
               ((evaluatedSlicePointMeas params strategy q.2).outcome ab.2)))
    |avgOver 𝒟 inserted - avgOver 𝒟 swapped| ≤
      6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
  exact
    evaluatedSlice_phaseFour_pointSwap_right_bound_of_commutativityPoints
      params strategy gamma hnorm
      (commutativityPoints (params := params.next) strategy eps delta gamma hgood)
      C hC

end MIPStarRE.LDT.Commutativity
