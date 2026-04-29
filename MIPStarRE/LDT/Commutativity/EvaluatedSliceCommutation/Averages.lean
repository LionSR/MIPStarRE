import MIPStarRE.LDT.Commutativity.EvaluatedSliceCommutation.PhaseFourFive

/-!
# Section 11 commutativity: evaluated-slice averaged expansion

Averaged evaluated-slice expansion of `qSDDOp` into the four projector terms
`BAB + ABA - BABA - ABAB`, used to reduce the commutation to per-projector
estimates.

## References

- arXiv:2009.12982, Section 11 (commutativity of the Pauli-`X` and `Z` players).
-/

set_option linter.style.setOption false
set_option linter.unnecessarySimpa false

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
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
private lemma fullSliceCommutation_qSDDOp_avg_expand
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
lemma evaluatedSliceCommutation_avg_swap_terms
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


end MIPStarRE.LDT.Commutativity
