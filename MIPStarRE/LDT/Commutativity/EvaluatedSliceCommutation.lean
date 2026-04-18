import MIPStarRE.LDT.Commutativity.EvaluatedSliceBounds

/-!
# Section 11 commutativity: evaluated-slice commutation

Evaluated-slice commutation identities and tail bounds.
-/

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


/-- Expand the averaged evaluated-slice `qSDDOp` into the four projector terms
`BAB + ABA - BABA - ABAB`. -/
private lemma evaluatedSliceCommutation_qSDDOp_avg_expand
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          qSDDOp strategy.state
            (evaluatedSliceProductLeft params strategy family q)
            (evaluatedSliceProductRight params strategy family q)) =
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          ∑ ab : EvaluatedSliceOutcome params,
            (evaluatedSliceBABTerm params strategy family q ab +
              evaluatedSliceABATerm params strategy family q ab -
              evaluatedSliceBABATerm params strategy family q ab -
              evaluatedSliceABABTerm params strategy family q ab)) := by
  apply avgOver_congr
  intro q
  unfold qSDDOp qSDDCore
  refine Finset.sum_congr rfl ?_
  intro ab _
  rcases ab with ⟨a, b⟩
  let A : MIPStarRE.Quantum.Op ι := (evaluatedPointFamily params family q.1).outcome a
  let B : MIPStarRE.Quantum.Op ι := (evaluatedPointFamily params family q.2).outcome b
  let LA : MIPStarRE.Quantum.Op (ι × ι) := leftTensor (ι₂ := ι) A
  let LB : MIPStarRE.Quantum.Op (ι × ι) := leftTensor (ι₂ := ι) B
  have hA_herm : Aᴴ = A := by
    simpa [A] using (evaluatedPointFamily params family q.1).outcome_hermitian a
  have hB_herm : Bᴴ = B := by
    simpa [B] using (evaluatedPointFamily params family q.2).outcome_hermitian b
  have hA_proj : A * A = A := by
    simpa [A] using evaluatedPointFamily_outcome_proj params family q.1 a
  have hB_proj : B * B = B := by
    simpa [B] using evaluatedPointFamily_outcome_proj params family q.2 b
  have hLA_herm : LAᴴ = LA := by
    let hLA_nonneg :=
      Matrix.nonneg_iff_posSemidef.mp
        (leftTensor_nonneg (ι₂ := ι) ((evaluatedPointFamily params family q.1).outcome_pos a))
    exact hLA_nonneg.isHermitian.eq
  have hLB_herm : LBᴴ = LB := by
    let hLB_nonneg :=
      Matrix.nonneg_iff_posSemidef.mp
        (leftTensor_nonneg (ι₂ := ι) ((evaluatedPointFamily params family q.2).outcome_pos b))
    exact hLB_nonneg.isHermitian.eq
  have hLA_proj : LA * LA = LA := by
    simpa [LA, leftTensor_mul_leftTensor] using congrArg (leftTensor (ι₂ := ι)) hA_proj
  have hLB_proj : LB * LB = LB := by
    simpa [LB, leftTensor_mul_leftTensor] using congrArg (leftTensor (ι₂ := ι)) hB_proj
  have hmain :
      (((LA * LB - LB * LA)ᴴ) * (LA * LB - LB * LA)) =
        LB * LA * LB + LA * LB * LA - LB * LA * LB * LA - LA * LB * LA * LB := by
    rw [show (LA * LB - LB * LA)ᴴ = LB * LA - LA * LB by
      simp [Matrix.conjTranspose_mul, hLA_herm, hLB_herm]]
    calc
      (LB * LA - LA * LB) * (LA * LB - LB * LA)
          = LB * LA * LA * LB - LB * LA * LB * LA - LA * LB * LA * LB + LA * LB * LB * LA := by
              noncomm_ring
      _ = LB * LA * LB - LB * LA * LB * LA - LA * LB * LA * LB + LA * LB * LA := by
            simpa [mul_assoc, hLA_proj, hLB_proj]
      _ = LB * LA * LB + LA * LB * LA - LB * LA * LB * LA - LA * LB * LA * LB := by
            abel
  calc
    ev strategy.state
        (((evaluatedSliceProductLeft params strategy family q).outcome (a, b) -
            (evaluatedSliceProductRight params strategy family q).outcome (a, b))ᴴ *
          ((evaluatedSliceProductLeft params strategy family q).outcome (a, b) -
            (evaluatedSliceProductRight params strategy family q).outcome (a, b)))
      = ev strategy.state (((LA * LB - LB * LA)ᴴ) * (LA * LB - LB * LA)) := by
          simp [A, B, LA, LB, evaluatedSliceProductLeft, evaluatedSliceProductRight,
            evaluatedSliceFirstFactor, evaluatedSliceSecondFactor, evaluatedPointFamily,
            leftOrderedProductOpFamily, OpFamily.leftPlacedOpFamily,
            orderedProductOpFamily, reversedProductOpFamily, leftTensor_mul_leftTensor]
    _ = ev strategy.state
          (LB * LA * LB + LA * LB * LA - LB * LA * LB * LA - LA * LB * LA * LB) := by
            rw [hmain]
    _ = ev strategy.state (LB * LA * LB) + ev strategy.state (LA * LB * LA) -
          ev strategy.state (LB * LA * LB * LA) -
            ev strategy.state (LA * LB * LA * LB) := by
          rw [ev_sub, ev_sub, ev_add]
    _ = ev strategy.state (leftTensor (ι₂ := ι) (B * A * B)) +
          ev strategy.state (leftTensor (ι₂ := ι) (A * B * A)) -
          ev strategy.state (leftTensor (ι₂ := ι) (B * A * B * A)) -
            ev strategy.state (leftTensor (ι₂ := ι) (A * B * A * B)) := by
          simp [LA, LB, leftTensor_mul_leftTensor, mul_assoc]
    _ = evaluatedSliceBABTerm params strategy family q (a, b) +
          evaluatedSliceABATerm params strategy family q (a, b) -
          evaluatedSliceBABATerm params strategy family q (a, b) -
            evaluatedSliceABABTerm params strategy family q (a, b) := by
          simp [evaluatedSliceBABTerm, evaluatedSliceABATerm,
            evaluatedSliceBABATerm, evaluatedSliceABABTerm, A, B]

/-- Expand the pulled-back full-slice `qSDDOp` into the four projector terms
`BAB + ABA - BABA - ABAB`. -/
lemma fullSliceCommutation_qSDDOp_avg_expand
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          qSDDOp strategy.state
            (fullSliceProductLeft params strategy family
              (fullSliceQuestionOfEvaluatedSlice params q))
            (fullSliceProductRight params strategy family
              (fullSliceQuestionOfEvaluatedSlice params q))) =
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          ∑ gh : FullSliceOutcome params,
            (fullSliceBABTerm params strategy family
                (fullSliceQuestionOfEvaluatedSlice params q) gh +
              fullSliceABATerm params strategy family
                (fullSliceQuestionOfEvaluatedSlice params q) gh -
              fullSliceBABATerm params strategy family
                (fullSliceQuestionOfEvaluatedSlice params q) gh -
              fullSliceABABTerm params strategy family
                (fullSliceQuestionOfEvaluatedSlice params q) gh)) := by
  apply avgOver_congr
  intro q
  unfold qSDDOp qSDDCore
  refine Finset.sum_congr rfl ?_
  intro gh _
  rcases gh with ⟨g, h⟩
  let q' : FullSliceQuestion params := fullSliceQuestionOfEvaluatedSlice params q
  let A : MIPStarRE.Quantum.Op ι := (fullSliceFirstFactor params family q').outcome g
  let B : MIPStarRE.Quantum.Op ι := (fullSliceSecondFactor params family q').outcome h
  let LA : MIPStarRE.Quantum.Op (ι × ι) := leftTensor (ι₂ := ι) A
  let LB : MIPStarRE.Quantum.Op (ι × ι) := leftTensor (ι₂ := ι) B
  have hA_herm : Aᴴ = A := by
    simpa [A, q', fullSliceFirstFactor] using (family.meas q'.1).outcome_hermitian g
  have hB_herm : Bᴴ = B := by
    simpa [B, q', fullSliceSecondFactor] using (family.meas q'.2).outcome_hermitian h
  have hA_proj : A * A = A := by
    simpa [A, q', fullSliceFirstFactor] using (family.meas q'.1).proj g
  have hB_proj : B * B = B := by
    simpa [B, q', fullSliceSecondFactor] using (family.meas q'.2).proj h
  have hLA_herm : LAᴴ = LA := by
    let hLA_nonneg :=
      Matrix.nonneg_iff_posSemidef.mp
        (leftTensor_nonneg (ι₂ := ι) ((family.meas q'.1).outcome_pos g))
    exact hLA_nonneg.isHermitian.eq
  have hLB_herm : LBᴴ = LB := by
    let hLB_nonneg :=
      Matrix.nonneg_iff_posSemidef.mp
        (leftTensor_nonneg (ι₂ := ι) ((family.meas q'.2).outcome_pos h))
    exact hLB_nonneg.isHermitian.eq
  have hLA_proj : LA * LA = LA := by
    simpa [LA, leftTensor_mul_leftTensor] using congrArg (leftTensor (ι₂ := ι)) hA_proj
  have hLB_proj : LB * LB = LB := by
    simpa [LB, leftTensor_mul_leftTensor] using congrArg (leftTensor (ι₂ := ι)) hB_proj
  have hmain :
      (((LA * LB - LB * LA)ᴴ) * (LA * LB - LB * LA)) =
        LB * LA * LB + LA * LB * LA - LB * LA * LB * LA - LA * LB * LA * LB := by
    rw [show (LA * LB - LB * LA)ᴴ = LB * LA - LA * LB by
      simp [Matrix.conjTranspose_mul, hLA_herm, hLB_herm]]
    calc
      (LB * LA - LA * LB) * (LA * LB - LB * LA)
          = LB * LA * LA * LB - LB * LA * LB * LA - LA * LB * LA * LB +
              LA * LB * LB * LA := by
              noncomm_ring
      _ = LB * LA * LB - LB * LA * LB * LA - LA * LB * LA * LB + LA * LB * LA := by
            simpa [mul_assoc, hLA_proj, hLB_proj]
      _ = LB * LA * LB + LA * LB * LA - LB * LA * LB * LA - LA * LB * LA * LB := by
            abel
  calc
    ev strategy.state
        (((fullSliceProductLeft params strategy family q').outcome (g, h) -
            (fullSliceProductRight params strategy family q').outcome (g, h))ᴴ *
          ((fullSliceProductLeft params strategy family q').outcome (g, h) -
            (fullSliceProductRight params strategy family q').outcome (g, h)))
      = ev strategy.state (((LA * LB - LB * LA)ᴴ) * (LA * LB - LB * LA)) := by
          simp [A, B, LA, LB, q', fullSliceProductLeft, fullSliceProductRight,
            fullSliceFirstFactor, fullSliceSecondFactor, leftOrderedProductOpFamily,
            OpFamily.leftPlacedOpFamily, orderedProductOpFamily, reversedProductOpFamily,
            leftTensor_mul_leftTensor]
    _ = ev strategy.state
          (LB * LA * LB + LA * LB * LA - LB * LA * LB * LA - LA * LB * LA * LB) := by
            rw [hmain]
    _ = ev strategy.state (LB * LA * LB) + ev strategy.state (LA * LB * LA) -
          ev strategy.state (LB * LA * LB * LA) -
            ev strategy.state (LA * LB * LA * LB) := by
          rw [ev_sub, ev_sub, ev_add]
    _ = ev strategy.state (leftTensor (ι₂ := ι) (B * A * B)) +
          ev strategy.state (leftTensor (ι₂ := ι) (A * B * A)) -
          ev strategy.state (leftTensor (ι₂ := ι) (B * A * B * A)) -
            ev strategy.state (leftTensor (ι₂ := ι) (A * B * A * B)) := by
          simp [LA, LB, leftTensor_mul_leftTensor, mul_assoc]
    _ = fullSliceBABTerm params strategy family q' (g, h) +
          fullSliceABATerm params strategy family q' (g, h) -
          fullSliceBABATerm params strategy family q' (g, h) -
            fullSliceABABTerm params strategy family q' (g, h) := by
          simp [fullSliceBABTerm, fullSliceABATerm,
            fullSliceBABATerm, fullSliceABABTerm, A, B, q']

/-- Swapping the evaluated question and outcome identifies the averaged
`BAB`/`ABA` terms and the averaged `BABA`/`ABAB` terms. -/
private lemma evaluatedSliceCommutation_avg_swap_terms
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          evaluatedSliceBABTerm params strategy family q ab) =
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          evaluatedSliceABATerm params strategy family q ab) ∧
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          evaluatedSliceBABATerm params strategy family q ab) =
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          evaluatedSliceABABTerm params strategy family q ab) := by
  let eQ : EvaluatedSliceQuestion params ≃ EvaluatedSliceQuestion params :=
    { toFun := Prod.swap
      invFun := Prod.swap
      left_inv := by intro q; cases q; rfl
      right_inv := by intro q; cases q; rfl }
  let eA : EvaluatedSliceOutcome params ≃ EvaluatedSliceOutcome params :=
    { toFun := Prod.swap
      invFun := Prod.swap
      left_inv := by intro ab; cases ab; rfl
      right_inv := by intro ab; cases ab; rfl }
  constructor
  · calc
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceBABTerm params strategy family q ab)
        = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
            (fun q => ∑ ab : EvaluatedSliceOutcome params,
              evaluatedSliceABATerm params strategy family (eQ q) ab) := by
              apply avgOver_congr
              intro q
              calc
                ∑ ab : EvaluatedSliceOutcome params,
                    evaluatedSliceBABTerm params strategy family q ab
                  = ∑ ab' : EvaluatedSliceOutcome params,
                      evaluatedSliceBABTerm params strategy family q (eA.symm ab') := by
                      exact Fintype.sum_equiv eA
                        (fun ab => evaluatedSliceBABTerm params strategy family q ab)
                        (fun ab' => evaluatedSliceBABTerm params strategy family q (eA.symm ab'))
                        (by intro ab; simp [eA])
                _ = ∑ ab : EvaluatedSliceOutcome params,
                      evaluatedSliceABATerm params strategy family (eQ q) ab := by
                      refine Finset.sum_congr rfl ?_
                      intro ab _
                      rcases q with ⟨u, v⟩
                      rcases ab with ⟨a, b⟩
                      simpa [eQ, eA, evaluatedSliceBABTerm, evaluatedSliceABATerm]
      _ = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
            (fun q => ∑ ab : EvaluatedSliceOutcome params,
              evaluatedSliceABATerm params strategy family q ab) := by
              simpa [eQ] using
                (avgOver_uniform_equiv eQ
                  (fun q => ∑ ab : EvaluatedSliceOutcome params,
                    evaluatedSliceABATerm params strategy family q ab)).symm
  · calc
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceBABATerm params strategy family q ab)
        = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
            (fun q => ∑ ab : EvaluatedSliceOutcome params,
              evaluatedSliceABABTerm params strategy family (eQ q) ab) := by
              apply avgOver_congr
              intro q
              calc
                ∑ ab : EvaluatedSliceOutcome params,
                    evaluatedSliceBABATerm params strategy family q ab
                  = ∑ ab' : EvaluatedSliceOutcome params,
                      evaluatedSliceBABATerm params strategy family q (eA.symm ab') := by
                      exact Fintype.sum_equiv eA
                        (fun ab => evaluatedSliceBABATerm params strategy family q ab)
                        (fun ab' =>
                          evaluatedSliceBABATerm params strategy family q (eA.symm ab'))
                        (by intro ab; simp [eA])
                _ = ∑ ab : EvaluatedSliceOutcome params,
                      evaluatedSliceABABTerm params strategy family (eQ q) ab := by
                      refine Finset.sum_congr rfl ?_
                      intro ab _
                      rcases q with ⟨u, v⟩
                      rcases ab with ⟨a, b⟩
                      simpa [eQ, eA, evaluatedSliceBABATerm, evaluatedSliceABABTerm]
      _ = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
            (fun q => ∑ ab : EvaluatedSliceOutcome params,
              evaluatedSliceABABTerm params strategy family q ab) := by
              simpa [eQ] using
                (avgOver_uniform_equiv eQ
                  (fun q => ∑ ab : EvaluatedSliceOutcome params,
                    evaluatedSliceABABTerm params strategy family q ab)).symm

/-- Averaged evaluated-slice `qSDDOp` collapses to the paper's two scalar terms
after swapping the sampled questions and outcomes. -/
lemma evaluatedSliceCommutation_qSDDOp_avg_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    sddErrorOp strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedSliceProductLeft params strategy family)
      (evaluatedSliceProductRight params strategy family) =
      2 *
        (avgOver (uniformDistribution (EvaluatedSliceQuestion params))
            (fun q => ∑ ab : EvaluatedSliceOutcome params,
              evaluatedSliceABATerm params strategy family q ab) -
          avgOver (uniformDistribution (EvaluatedSliceQuestion params))
            (fun q => ∑ ab : EvaluatedSliceOutcome params,
              evaluatedSliceABABTerm params strategy family q ab)) := by
  have hswap :=
    evaluatedSliceCommutation_avg_swap_terms params strategy family
  unfold sddErrorOp
  rw [evaluatedSliceCommutation_qSDDOp_avg_expand]
  rcases hswap with ⟨hBAB, hBABA⟩
  let sf : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ ab : EvaluatedSliceOutcome params, evaluatedSliceBABTerm params strategy family q ab
  let sg : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ ab : EvaluatedSliceOutcome params, evaluatedSliceABATerm params strategy family q ab
  let sh : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ ab : EvaluatedSliceOutcome params, evaluatedSliceBABATerm params strategy family q ab
  let sk : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ ab : EvaluatedSliceOutcome params, evaluatedSliceABABTerm params strategy family q ab
  have hpoint :
      ∀ q,
        (∑ ab : EvaluatedSliceOutcome params,
            (evaluatedSliceBABTerm params strategy family q ab +
              evaluatedSliceABATerm params strategy family q ab -
              evaluatedSliceBABATerm params strategy family q ab -
              evaluatedSliceABABTerm params strategy family q ab)) =
          sf q + sg q - sh q - sk q := by
    intro q
    dsimp [sf, sg, sh, sk]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hsplit :
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => sf q + sg q - sh q - sk q) =
        avgOver (uniformDistribution (EvaluatedSliceQuestion params)) sf +
          avgOver (uniformDistribution (EvaluatedSliceQuestion params)) sg -
          avgOver (uniformDistribution (EvaluatedSliceQuestion params)) sh -
          avgOver (uniformDistribution (EvaluatedSliceQuestion params)) sk := by
    unfold avgOver
    have hmul :
        ∀ q,
          (uniformDistribution (EvaluatedSliceQuestion params)).weight q *
              (sf q + sg q - sh q - sk q) =
            (uniformDistribution (EvaluatedSliceQuestion params)).weight q * sf q +
              (uniformDistribution (EvaluatedSliceQuestion params)).weight q * sg q -
              (uniformDistribution (EvaluatedSliceQuestion params)).weight q * sh q -
              (uniformDistribution (EvaluatedSliceQuestion params)).weight q * sk q := by
      intro q
      ring
    simp_rw [hmul, sub_eq_add_neg]
    repeat rw [Finset.sum_add_distrib]
    simp_rw [Finset.sum_neg_distrib]
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          ∑ ab : EvaluatedSliceOutcome params,
            (evaluatedSliceBABTerm params strategy family q ab +
              evaluatedSliceABATerm params strategy family q ab -
              evaluatedSliceBABATerm params strategy family q ab -
              evaluatedSliceABABTerm params strategy family q ab))
      = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceBABTerm params strategy family q ab) +
        avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceABATerm params strategy family q ab) -
        avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceBABATerm params strategy family q ab) -
        avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceABABTerm params strategy family q ab) := by
            calc
              avgOver (uniformDistribution (EvaluatedSliceQuestion params))
                  (fun q =>
                    ∑ ab : EvaluatedSliceOutcome params,
                      (evaluatedSliceBABTerm params strategy family q ab +
                        evaluatedSliceABATerm params strategy family q ab -
                        evaluatedSliceBABATerm params strategy family q ab -
                        evaluatedSliceABABTerm params strategy family q ab))
                = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
                    (fun q => sf q + sg q - sh q - sk q) := by
                      apply avgOver_congr
                      intro q
                      exact hpoint q
              _ = avgOver (uniformDistribution (EvaluatedSliceQuestion params)) sf +
                  avgOver (uniformDistribution (EvaluatedSliceQuestion params)) sg -
                  avgOver (uniformDistribution (EvaluatedSliceQuestion params)) sh -
                  avgOver (uniformDistribution (EvaluatedSliceQuestion params)) sk := hsplit
    _ = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceABATerm params strategy family q ab) +
        avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceABATerm params strategy family q ab) -
        avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceABABTerm params strategy family q ab) -
        avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceABABTerm params strategy family q ab) := by
            rw [hBAB, hBABA]
    _ = 2 *
          (avgOver (uniformDistribution (EvaluatedSliceQuestion params))
              (fun q => ∑ ab : EvaluatedSliceOutcome params,
                evaluatedSliceABATerm params strategy family q ab) -
            avgOver (uniformDistribution (EvaluatedSliceQuestion params))
              (fun q => ∑ ab : EvaluatedSliceOutcome params,
                evaluatedSliceABABTerm params strategy family q ab)) := by
            ring

/-- Pull a single-point evaluated-family self-consistency bound up to the first
coordinate of an evaluated-slice question. -/
lemma evaluatedPointSelfConsistency_fst
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hssc : SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamilyLeft params family)
      (evaluatedPointFamilyRight params family)
      zeta) :
    SDDRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => evaluatedPointFamilyLeft params family q.1)
      (fun q => evaluatedPointFamilyRight params family q.1)
      zeta := by
  rcases hssc with ⟨h⟩
  constructor
  simpa [sddError] using
    (avgOver_uniform_fst (α := Point params.next) (β := Point params.next)
      (f := fun u =>
        qSDD strategy.state
          (evaluatedPointFamilyLeft params family u)
          (evaluatedPointFamilyRight params family u))).trans_le h

/-- Pull a single-point evaluated-family self-consistency bound up to the second
coordinate of an evaluated-slice question. -/
lemma evaluatedPointSelfConsistency_snd
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hssc : SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamilyLeft params family)
      (evaluatedPointFamilyRight params family)
      zeta) :
    SDDRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => evaluatedPointFamilyLeft params family q.2)
      (fun q => evaluatedPointFamilyRight params family q.2)
      zeta := by
  rcases hssc with ⟨h⟩
  constructor
  simpa [sddError] using
    (avgOver_uniform_snd (α := Point params.next) (β := Point params.next)
      (f := fun u =>
        qSDD strategy.state
          (evaluatedPointFamilyLeft params family u)
          (evaluatedPointFamilyRight params family u))).trans_le h

/-- Phase-8/9 tail helper for `evaluatedSlice_scalar_chain_bound`.

This packages the target comparison between the averaged `BAB` and `ABA`
scalar terms while keeping the new switch-sandwich bridge lemmas adjacent to
the proof site.  The current proof closes using the earlier swap symmetry,
and leaves the switch-sandwich ingredients available for the remaining scalar
chain fill-in. -/
lemma evaluatedSlice_phaseEightNine_tail_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (_hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (_hpostSSC : SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamilyLeft params family)
      (evaluatedPointFamilyRight params family)
      zeta) :
    |avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          evaluatedSliceBABTerm params strategy family q ab) -
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          evaluatedSliceABATerm params strategy family q ab)| ≤
      2 * Real.sqrt zeta := by
  have hswap := (evaluatedSliceCommutation_avg_swap_terms params strategy family).1
  calc
    |avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          evaluatedSliceBABTerm params strategy family q ab) -
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          evaluatedSliceABATerm params strategy family q ab)|
      = 0 := by rw [hswap]; simp
    _ ≤ 2 * Real.sqrt zeta := by positivity

end MIPStarRE.LDT.Commutativity
