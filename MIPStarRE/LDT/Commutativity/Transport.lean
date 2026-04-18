import MIPStarRE.LDT.Commutativity.GCommStability

/-!
# Section 11 commutativity: transport to full slices

Transport lemmas from evaluated-slice commutation to full-slice commutation.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Postprocessing a `leftPlacedOpFamily` of a bilinear product equals
the `leftPlacedOpFamily` of the product of postprocessed submeasurements,
for any binary operation `g` that factors over finite sums. -/
private lemma postprocess_leftPlacedOpFamily_product_outcome
    {α₁ α₂ β₁ β₂ : Type*}
    [Fintype α₁] [Fintype α₂] [Fintype β₁] [Fintype β₂]
    (A : SubMeas α₁ ι) (B : SubMeas α₂ ι)
    (f₁ : α₁ → β₁) (f₂ : α₂ → β₂) (b₁ : β₁) (b₂ : β₂)
    (g : MIPStarRE.Quantum.Op ι → MIPStarRE.Quantum.Op ι →
      MIPStarRE.Quantum.Op ι)
    (hg_factor : ∀ (S : Finset α₁) (T : Finset α₂)
      (fA : α₁ → MIPStarRE.Quantum.Op ι)
      (fB : α₂ → MIPStarRE.Quantum.Op ι),
      ∑ a ∈ S ×ˢ T, g (fA a.1) (fB a.2) =
        g (∑ a ∈ S, fA a) (∑ b ∈ T, fB b)) :
    (OpFamily.postprocess
      (OpFamily.leftPlacedOpFamily (ιB := ι)
        (⟨fun ab => g (A.outcome ab.1) (B.outcome ab.2),
          g A.total B.total⟩ : OpFamily (α₁ × α₂) ι))
      (fun ab => (f₁ ab.1, f₂ ab.2))).outcome (b₁, b₂) =
    (OpFamily.leftPlacedOpFamily (ιB := ι)
      (⟨fun ab => g ((postprocess A f₁).outcome ab.1)
          ((postprocess B f₂).outcome ab.2),
        g (postprocess A f₁).total
          (postprocess B f₂).total⟩ :
          OpFamily (β₁ × β₂) ι)).outcome (b₁, b₂) := by
  classical
  simp only [OpFamily.postprocess, OpFamily.leftPlacedOpFamily,
    postprocess]
  rw [leftTensor_finset_sum (ι₂ := ι)]
  congr 1
  set S := Finset.univ.filter (fun a₁ => f₁ a₁ = b₁)
  set T := Finset.univ.filter (fun a₂ => f₂ a₂ = b₂)
  trans ∑ a ∈ S ×ˢ T, g (A.outcome a.1) (B.outcome a.2)
  · apply Finset.sum_congr
    · ext ⟨x, y⟩; simp [S, T, Prod.mk.injEq]
    · intros; rfl
  · exact hg_factor S T A.outcome B.outcome

private lemma postprocess_leftPlacedOpFamily_orderedProduct_outcome
    {α₁ α₂ β₁ β₂ : Type*}
    [Fintype α₁] [Fintype α₂] [Fintype β₁] [Fintype β₂]
    (A : SubMeas α₁ ι) (B : SubMeas α₂ ι)
    (f₁ : α₁ → β₁) (f₂ : α₂ → β₂) (b₁ : β₁) (b₂ : β₂) :
    (OpFamily.postprocess
      (OpFamily.leftPlacedOpFamily (ιB := ι)
        (orderedProductOpFamily A B))
      (fun ab => (f₁ ab.1, f₂ ab.2))).outcome (b₁, b₂) =
    (OpFamily.leftPlacedOpFamily (ιB := ι)
      (orderedProductOpFamily
        (postprocess A f₁)
        (postprocess B f₂))).outcome (b₁, b₂) := by
  unfold orderedProductOpFamily
  exact postprocess_leftPlacedOpFamily_product_outcome
    A B f₁ f₂ b₁ b₂ (· * ·) fun S T fA fB => by
    rw [Finset.sum_product]; simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]

private lemma postprocess_leftPlacedOpFamily_reversedProduct_outcome
    {α₁ α₂ β₁ β₂ : Type*}
    [Fintype α₁] [Fintype α₂] [Fintype β₁] [Fintype β₂]
    (A : SubMeas α₁ ι) (B : SubMeas α₂ ι)
    (f₁ : α₁ → β₁) (f₂ : α₂ → β₂) (b₁ : β₁) (b₂ : β₂) :
    (OpFamily.postprocess
      (OpFamily.leftPlacedOpFamily (ιB := ι)
        (reversedProductOpFamily A B))
      (fun ab => (f₁ ab.1, f₂ ab.2))).outcome (b₁, b₂) =
    (OpFamily.leftPlacedOpFamily (ιB := ι)
      (reversedProductOpFamily
        (postprocess A f₁)
        (postprocess B f₂))).outcome (b₁, b₂) := by
  unfold reversedProductOpFamily
  exact postprocess_leftPlacedOpFamily_product_outcome
    A B f₁ f₂ b₁ b₂ (fun x y => y * x) fun S T fA fB => by
    rw [Finset.sum_product]; simp_rw [← Finset.sum_mul]
    rw [← Finset.mul_sum]

/-- The evaluated-from-full-slice ordered product equals the
evaluated-slice ordered product at each question-outcome pair. -/
private lemma evaluatedFromFullSliceProductLeft_outcome_eq
    (params : Parameters) [FieldModel params.q] (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params)
    (ab : EvaluatedSliceOutcome params) :
    (evaluatedFromFullSliceProductLeft
      params strategy family q).outcome ab =
    (evaluatedSliceProductLeft
      params strategy family q).outcome ab := by
  obtain ⟨a, b⟩ := ab
  unfold evaluatedFromFullSliceProductLeft evaluatedSliceProductLeft
    fullSliceProductLeft leftOrderedProductOpFamily
    evaluateFullSliceOutcomeAtQuestion
    fullSliceQuestionOfEvaluatedSlice
  exact
    postprocess_leftPlacedOpFamily_orderedProduct_outcome
      (fullSliceFirstFactor params family
        (pointHeight params q.1, pointHeight params q.2))
      (fullSliceSecondFactor params family
        (pointHeight params q.1, pointHeight params q.2))
      (fun g => g (truncatePoint params q.1))
      (fun h => h (truncatePoint params q.2)) a b

/-- The evaluated-from-full-slice reversed product equals the
evaluated-slice reversed product at each question-outcome pair. -/
private lemma evaluatedFromFullSliceProductRight_outcome_eq
    (params : Parameters) [FieldModel params.q] (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params)
    (ab : EvaluatedSliceOutcome params) :
    (evaluatedFromFullSliceProductRight
      params strategy family q).outcome ab =
    (evaluatedSliceProductRight
      params strategy family q).outcome ab := by
  obtain ⟨a, b⟩ := ab
  unfold evaluatedFromFullSliceProductRight
    evaluatedSliceProductRight fullSliceProductRight
    evaluateFullSliceOutcomeAtQuestion
    fullSliceQuestionOfEvaluatedSlice
  exact
    postprocess_leftPlacedOpFamily_reversedProduct_outcome
      (fullSliceFirstFactor params family
        (pointHeight params q.1, pointHeight params q.2))
      (fullSliceSecondFactor params family
        (pointHeight params q.1, pointHeight params q.2))
      (fun g => g (truncatePoint params q.1))
      (fun h => h (truncatePoint params q.2)) a b

/-- The evaluated-from-full-slice SDD error equals the evaluated-slice
SDD error, because the postprocessed product equals the product of
postprocessed submeasurements at every question-outcome pair. -/
lemma evaluationSpecialization_sddErrorOp_eq
    (params : Parameters) [FieldModel params.q] (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) :
    sddErrorOp strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedFromFullSliceProductLeft
        params strategy family)
      (evaluatedFromFullSliceProductRight
        params strategy family) =
    sddErrorOp strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedSliceProductLeft params strategy family)
      (evaluatedSliceProductRight
        params strategy family) := by
  simp only [sddErrorOp, qSDDOp, qSDDCore]
  simp_rw [evaluatedFromFullSliceProductLeft_outcome_eq,
      evaluatedFromFullSliceProductRight_outcome_eq]

/-- Repackage the evaluated-from-full-slice commutation bound as a bound for the
evaluated-slice product families, using the pointwise postprocessing identities. -/
private lemma evaluatedSliceCommutation_of_evaluationSpecialization
    (params : Parameters) [FieldModel params.q] (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (δ : Error)
    (hEval :
      SDDOpRel strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedFromFullSliceProductLeft params strategy family)
        (evaluatedFromFullSliceProductRight params strategy family)
        δ) :
    SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedSliceProductLeft params strategy family)
      (evaluatedSliceProductRight params strategy family)
      δ := by
  exact
    CommutativityPoints.sddOpRel_congr_outcome strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedFromFullSliceProductLeft params strategy family)
      (evaluatedFromFullSliceProductRight params strategy family)
      (evaluatedSliceProductLeft params strategy family)
      (evaluatedSliceProductRight params strategy family)
      δ
      (fun q ab =>
        evaluatedFromFullSliceProductLeft_outcome_eq params strategy family q ab)
      (fun q ab =>
        evaluatedFromFullSliceProductRight_outcome_eq params strategy family q ab)
      hEval

/-- Reindex an evaluated-slice question into its truncated points and
underlying full-slice question. -/
private def evaluatedSliceQuestionEquiv (params : Parameters) [FieldModel params.q] :
    EvaluatedSliceQuestion params ≃
      (Point params × Point params) × FullSliceQuestion params where
  toFun := fun q =>
    ((truncatePoint params q.1, truncatePoint params q.2),
      fullSliceQuestionOfEvaluatedSlice params q)
  invFun := fun r =>
    ((appendPoint params r.1.1 r.2.1), (appendPoint params r.1.2 r.2.2))
  left_inv := by
    rintro ⟨u, v⟩
    change
      (appendPoint params (truncatePoint params u) (pointHeight params u),
        appendPoint params (truncatePoint params v) (pointHeight params v)) =
        (u, v)
    exact Prod.ext
      ((CommutativityPoints.pointNextEquiv params).left_inv u)
      ((CommutativityPoints.pointNextEquiv params).left_inv v)
  right_inv := by
    rintro ⟨⟨u, v⟩, x, y⟩
    simp [fullSliceQuestionOfEvaluatedSlice]

/-- Pulling a family on `FullSliceQuestion` back along
`fullSliceQuestionOfEvaluatedSlice` preserves the averaged `sddErrorOp`. -/
private lemma sddErrorOp_pullback_fullSliceQuestion_eq
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    {Outcome : Type*} [Fintype Outcome]
    (A B : IdxOpFamily (FullSliceQuestion params) Outcome (ι × ι)) :
    sddErrorOp ψ
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => A (fullSliceQuestionOfEvaluatedSlice params q))
      (fun q => B (fullSliceQuestionOfEvaluatedSlice params q)) =
    sddErrorOp ψ
      (uniformDistribution (FullSliceQuestion params))
      A B := by
  let e := evaluatedSliceQuestionEquiv params
  unfold sddErrorOp
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          qSDDOp ψ
            (A (fullSliceQuestionOfEvaluatedSlice params q))
            (B (fullSliceQuestionOfEvaluatedSlice params q)))
      =
        avgOver
          (uniformDistribution
            ((Point params × Point params) × FullSliceQuestion params))
          (fun r => qSDDOp ψ (A r.2) (B r.2)) := by
            calc
              avgOver (uniformDistribution (EvaluatedSliceQuestion params))
                  (fun q =>
                    qSDDOp ψ
                      (A (fullSliceQuestionOfEvaluatedSlice params q))
                      (B (fullSliceQuestionOfEvaluatedSlice params q)))
                =
                  avgOver
                    (uniformDistribution
                      ((Point params × Point params) × FullSliceQuestion params))
                    (fun r =>
                      qSDDOp ψ
                        (A (fullSliceQuestionOfEvaluatedSlice params (e.symm r)))
                        (B (fullSliceQuestionOfEvaluatedSlice params (e.symm r)))) :=
                    avgOver_uniform_equiv e
                      (fun q =>
                        qSDDOp ψ
                          (A (fullSliceQuestionOfEvaluatedSlice params q))
                          (B (fullSliceQuestionOfEvaluatedSlice params q)))
              _ =
                  avgOver
                    (uniformDistribution
                      ((Point params × Point params) × FullSliceQuestion params))
                    (fun r => qSDDOp ψ (A r.2) (B r.2)) := by
                      apply avgOver_congr
                      rintro ⟨⟨u, v⟩, x, y⟩
                      simp [e, evaluatedSliceQuestionEquiv,
                        fullSliceQuestionOfEvaluatedSlice]
    _ =
        avgOver (uniformDistribution (FullSliceQuestion params))
          (fun xy => qSDDOp ψ (A xy) (B xy)) := by
            simpa using
              (avgOver_uniform_snd
                (α := Point params × Point params)
                (β := FullSliceQuestion params)
                (f := fun xy => qSDDOp ψ (A xy) (B xy)))

/-- Any `SDDOpRel` bound proved after pulling back along
`fullSliceQuestionOfEvaluatedSlice` descends to `FullSliceQuestion`. -/
lemma sddOpRel_of_pullback_fullSliceQuestion
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    {Outcome : Type*} [Fintype Outcome]
    (A B : IdxOpFamily (FullSliceQuestion params) Outcome (ι × ι))
    (δ : Error) :
    SDDOpRel ψ
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => A (fullSliceQuestionOfEvaluatedSlice params q))
      (fun q => B (fullSliceQuestionOfEvaluatedSlice params q))
      δ →
    SDDOpRel ψ
      (uniformDistribution (FullSliceQuestion params))
      A B
      δ := by
  intro ⟨h⟩
  constructor
  rw [← sddErrorOp_pullback_fullSliceQuestion_eq params ψ A B]
  exact h

/-- The zero raw family on the full-slice outcome space. -/
noncomputable def zeroFullSliceOpFamily
    (params : Parameters) [FieldModel params.q] :
    OpFamily (FullSliceOutcome params) (ι × ι) where
  outcome := fun _ => 0
  total := 0

/-- Questionwise, the ordered full-slice product has squared distance at most `1`
from the zero family. -/
private lemma fullSliceProductLeft_qSDDOp_zero_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized)
    (q : FullSliceQuestion params) :
    qSDDOp strategy.state
      (fullSliceProductLeft params strategy family q)
      (zeroFullSliceOpFamily (ι := ι) params) ≤ 1 := by
  let A : SubMeas (Polynomial params) ι := fullSliceFirstFactor params family q
  let B : SubMeas (Polynomial params) ι := fullSliceSecondFactor params family q
  let S := sandwichByOuterSubMeas B A
  unfold qSDDOp qSDDCore fullSliceProductLeft leftOrderedProductOpFamily
  calc
    ∑ gh : Polynomial params × Polynomial params,
        ev strategy.state
          (((leftTensor (ι₂ := ι) (A.outcome gh.1 * B.outcome gh.2) - 0)ᴴ) *
            (leftTensor (ι₂ := ι) (A.outcome gh.1 * B.outcome gh.2) - 0))
      = ∑ gh : Polynomial params × Polynomial params,
          ev strategy.state
            (leftTensor (ι₂ := ι)
              (B.outcome gh.2 * A.outcome gh.1 * B.outcome gh.2)) := by
          refine Finset.sum_congr rfl ?_
          intro gh _
          have hAherm : (A.outcome gh.1)ᴴ = A.outcome gh.1 := A.outcome_hermitian gh.1
          have hBherm : (B.outcome gh.2)ᴴ = B.outcome gh.2 := B.outcome_hermitian gh.2
          have hAproj : A.outcome gh.1 * A.outcome gh.1 = A.outcome gh.1 := by
            simpa [A, fullSliceFirstFactor] using (family.meas q.1).proj gh.1
          have hleftH :
              (leftTensor (ι₂ := ι) (A.outcome gh.1 * B.outcome gh.2))ᴴ =
                leftTensor (ι₂ := ι) ((A.outcome gh.1 * B.outcome gh.2)ᴴ) := by
            simpa [leftTensor] using
              (Matrix.conjTranspose_kronecker
                (A.outcome gh.1 * B.outcome gh.2)
                (1 : MIPStarRE.Quantum.Op ι))
          have hmul :
              (((A.outcome gh.1 * B.outcome gh.2)ᴴ) *
                (A.outcome gh.1 * B.outcome gh.2)) =
              B.outcome gh.2 * A.outcome gh.1 * B.outcome gh.2 := by
            calc
              (((A.outcome gh.1 * B.outcome gh.2)ᴴ) *
                  (A.outcome gh.1 * B.outcome gh.2))
                = (((B.outcome gh.2)ᴴ * (A.outcome gh.1)ᴴ) *
                    (A.outcome gh.1 * B.outcome gh.2)) := by
                    simp [Matrix.conjTranspose_mul]
              _ = B.outcome gh.2 * (A.outcome gh.1 * A.outcome gh.1) * B.outcome gh.2 := by
                    simp [hAherm, hBherm, mul_assoc]
              _ = B.outcome gh.2 * A.outcome gh.1 * B.outcome gh.2 := by
                    simp [hAproj, mul_assoc]
          calc
            ev strategy.state
                (((leftTensor (ι₂ := ι) (A.outcome gh.1 * B.outcome gh.2) - 0)ᴴ) *
                  (leftTensor (ι₂ := ι) (A.outcome gh.1 * B.outcome gh.2) - 0))
              = ev strategy.state
                  (((leftTensor (ι₂ := ι) (A.outcome gh.1 * B.outcome gh.2))ᴴ) *
                    leftTensor (ι₂ := ι) (A.outcome gh.1 * B.outcome gh.2)) := by simp
            _ = ev strategy.state
                  (leftTensor (ι₂ := ι)
                    (((A.outcome gh.1 * B.outcome gh.2)ᴴ) *
                      (A.outcome gh.1 * B.outcome gh.2))) := by
                    rw [hleftH, leftTensor_mul_leftTensor]
            _ = ev strategy.state
                  (leftTensor (ι₂ := ι)
                    (B.outcome gh.2 * A.outcome gh.1 * B.outcome gh.2)) := by rw [hmul]
    _ = ev strategy.state (leftTensor (ι₂ := ι) S.total) := by
          rw [← ev_sum strategy.state
            (fun gh : Polynomial params × Polynomial params =>
              leftTensor (ι₂ := ι) (B.outcome gh.2 * A.outcome gh.1 * B.outcome gh.2))]
          congr 1
          calc
            ∑ gh : Polynomial params × Polynomial params,
                leftTensor (ι₂ := ι) (B.outcome gh.2 * A.outcome gh.1 * B.outcome gh.2)
              = leftTensor (ι₂ := ι)
                  (∑ gh : Polynomial params × Polynomial params,
                    B.outcome gh.2 * A.outcome gh.1 * B.outcome gh.2) := by
                    exact leftTensor_finset_sum (ι₂ := ι) Finset.univ
                      (fun gh : Polynomial params × Polynomial params =>
                        B.outcome gh.2 * A.outcome gh.1 * B.outcome gh.2)
            _ = leftTensor (ι₂ := ι) S.total := by
                    congr 1
                    calc
                      ∑ gh : Polynomial params × Polynomial params,
                          B.outcome gh.2 * A.outcome gh.1 * B.outcome gh.2
                        = ∑ hg : Polynomial params × Polynomial params,
                            B.outcome hg.1 * A.outcome hg.2 * B.outcome hg.1 := by
                              exact Fintype.sum_equiv
                                (Equiv.prodComm (Polynomial params) (Polynomial params))
                                (fun gh : Polynomial params × Polynomial params =>
                                  B.outcome gh.2 * A.outcome gh.1 * B.outcome gh.2)
                                (fun hg : Polynomial params × Polynomial params =>
                                  B.outcome hg.1 * A.outcome hg.2 * B.outcome hg.1)
                                (by intro gh; simp)
                      _ = S.total := by
                            simpa [S, sandwichByOuterSubMeas] using S.sum_eq_total
    _ ≤ ev strategy.state (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
          exact ev_mono strategy.state _ _ <|
            leftTensor_le_one (ι₂ := ι) S.total_le_one
    _ = 1 := ev_one_of_isNormalized strategy.state hnorm

/-- Questionwise, the reversed full-slice product has squared distance at most `1`
from the zero family. -/
private lemma zero_qSDDOp_fullSliceProductRight_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized)
    (q : FullSliceQuestion params) :
    qSDDOp strategy.state
      (zeroFullSliceOpFamily (ι := ι) params)
      (fullSliceProductRight params strategy family q) ≤ 1 := by
  let A : SubMeas (Polynomial params) ι := fullSliceFirstFactor params family q
  let B : SubMeas (Polynomial params) ι := fullSliceSecondFactor params family q
  let S := sandwichByOuterSubMeas A B
  unfold qSDDOp qSDDCore fullSliceProductRight
  calc
    ∑ gh : Polynomial params × Polynomial params,
        ev strategy.state
          (((0 - leftTensor (ι₂ := ι) (B.outcome gh.2 * A.outcome gh.1))ᴴ) *
            (0 - leftTensor (ι₂ := ι) (B.outcome gh.2 * A.outcome gh.1)))
      = ∑ gh : Polynomial params × Polynomial params,
          ev strategy.state
            (leftTensor (ι₂ := ι)
              (A.outcome gh.1 * B.outcome gh.2 * A.outcome gh.1)) := by
          refine Finset.sum_congr rfl ?_
          intro gh _
          have hAherm : (A.outcome gh.1)ᴴ = A.outcome gh.1 := A.outcome_hermitian gh.1
          have hBherm : (B.outcome gh.2)ᴴ = B.outcome gh.2 := B.outcome_hermitian gh.2
          have hBproj : B.outcome gh.2 * B.outcome gh.2 = B.outcome gh.2 := by
            simpa [B, fullSliceSecondFactor] using (family.meas q.2).proj gh.2
          have hleftH :
              (leftTensor (ι₂ := ι) (B.outcome gh.2 * A.outcome gh.1))ᴴ =
                leftTensor (ι₂ := ι) ((B.outcome gh.2 * A.outcome gh.1)ᴴ) := by
            simpa [leftTensor] using
              (Matrix.conjTranspose_kronecker
                (B.outcome gh.2 * A.outcome gh.1)
                (1 : MIPStarRE.Quantum.Op ι))
          have hmul :
              (((B.outcome gh.2 * A.outcome gh.1)ᴴ) *
                (B.outcome gh.2 * A.outcome gh.1)) =
              A.outcome gh.1 * B.outcome gh.2 * A.outcome gh.1 := by
            calc
              (((B.outcome gh.2 * A.outcome gh.1)ᴴ) *
                  (B.outcome gh.2 * A.outcome gh.1))
                = (((A.outcome gh.1)ᴴ * (B.outcome gh.2)ᴴ) *
                    (B.outcome gh.2 * A.outcome gh.1)) := by
                    simp [Matrix.conjTranspose_mul]
              _ = A.outcome gh.1 * (B.outcome gh.2 * B.outcome gh.2) * A.outcome gh.1 := by
                    simp [hAherm, hBherm, mul_assoc]
              _ = A.outcome gh.1 * B.outcome gh.2 * A.outcome gh.1 := by
                    simp [hBproj, mul_assoc]
          calc
            ev strategy.state
                (((0 - leftTensor (ι₂ := ι) (B.outcome gh.2 * A.outcome gh.1))ᴴ) *
                  (0 - leftTensor (ι₂ := ι) (B.outcome gh.2 * A.outcome gh.1)))
              = ev strategy.state
                  (((leftTensor (ι₂ := ι) (B.outcome gh.2 * A.outcome gh.1))ᴴ) *
                    leftTensor (ι₂ := ι) (B.outcome gh.2 * A.outcome gh.1)) := by simp
            _ = ev strategy.state
                  (leftTensor (ι₂ := ι)
                    (((B.outcome gh.2 * A.outcome gh.1)ᴴ) *
                      (B.outcome gh.2 * A.outcome gh.1))) := by
                    rw [hleftH, leftTensor_mul_leftTensor]
            _ = ev strategy.state
                  (leftTensor (ι₂ := ι)
                    (A.outcome gh.1 * B.outcome gh.2 * A.outcome gh.1)) := by rw [hmul]
    _ = ev strategy.state (leftTensor (ι₂ := ι) S.total) := by
          rw [← ev_sum strategy.state
            (fun gh : Polynomial params × Polynomial params =>
              leftTensor (ι₂ := ι) (A.outcome gh.1 * B.outcome gh.2 * A.outcome gh.1))]
          congr 1
          calc
            ∑ gh : Polynomial params × Polynomial params,
                leftTensor (ι₂ := ι) (A.outcome gh.1 * B.outcome gh.2 * A.outcome gh.1)
              = leftTensor (ι₂ := ι)
                  (∑ gh : Polynomial params × Polynomial params,
                    A.outcome gh.1 * B.outcome gh.2 * A.outcome gh.1) := by
                    exact leftTensor_finset_sum (ι₂ := ι) Finset.univ
                      (fun gh : Polynomial params × Polynomial params =>
                        A.outcome gh.1 * B.outcome gh.2 * A.outcome gh.1)
            _ = leftTensor (ι₂ := ι) S.total := by
                    congr 1
                    simpa [S, sandwichByOuterSubMeas] using S.sum_eq_total
    _ ≤ ev strategy.state (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
          exact ev_mono strategy.state _ _ <|
            leftTensor_le_one (ι₂ := ι) S.total_le_one
    _ = 1 := ev_one_of_isNormalized strategy.state hnorm

/-- Averaging the ordered full-slice product against zero costs at most `1`. -/
lemma fullSliceProductLeft_to_zero_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized) :
    SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => fullSliceProductLeft params strategy family
        (fullSliceQuestionOfEvaluatedSlice params q))
      (fun _ => zeroFullSliceOpFamily (ι := ι) params)
      1 := by
  constructor
  unfold sddErrorOp
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          qSDDOp strategy.state
            (fullSliceProductLeft params strategy family
              (fullSliceQuestionOfEvaluatedSlice params q))
            (zeroFullSliceOpFamily (ι := ι) params))
      ≤ avgOver (uniformDistribution (EvaluatedSliceQuestion params)) (fun _ => (1 : Error)) := by
          apply avgOver_mono
          intro q
          exact fullSliceProductLeft_qSDDOp_zero_le_one params strategy family hnorm
            (fullSliceQuestionOfEvaluatedSlice params q)
    _ = ∑ q ∈ (uniformDistribution (EvaluatedSliceQuestion params)).support,
          (uniformDistribution (EvaluatedSliceQuestion params)).weight q := by
            simp [avgOver]
    _ ≤ 1 := uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)

/-- Averaging zero against the reversed full-slice product costs at most `1`. -/
lemma zero_to_fullSliceProductRight_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized) :
    SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun _ => zeroFullSliceOpFamily (ι := ι) params)
      (fun q => fullSliceProductRight params strategy family
        (fullSliceQuestionOfEvaluatedSlice params q))
      1 := by
  constructor
  unfold sddErrorOp
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          qSDDOp strategy.state
            (zeroFullSliceOpFamily (ι := ι) params)
            (fullSliceProductRight params strategy family
              (fullSliceQuestionOfEvaluatedSlice params q)))
      ≤ avgOver (uniformDistribution (EvaluatedSliceQuestion params)) (fun _ => (1 : Error)) := by
          apply avgOver_mono
          intro q
          exact zero_qSDDOp_fullSliceProductRight_le_one params strategy family hnorm
            (fullSliceQuestionOfEvaluatedSlice params q)
    _ = ∑ q ∈ (uniformDistribution (EvaluatedSliceQuestion params)).support,
          (uniformDistribution (EvaluatedSliceQuestion params)).weight q := by
            simp [avgOver]
    _ ≤ 1 := uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)

/-- Full-slice ABA scalar average: `E_{x,y} ∑_{g,h} ⟨ψ| G^x_g G^y_h G^x_g ⊗ I |ψ⟩`.

Full-polynomial analog of the evaluated `evaluatedSliceABATerm` (line 664);
obtained from it by replacing the evaluated outcomes `a,b` with polynomial
outcomes `g,h` summed over `FullSliceOutcome`. -/
noncomputable def fullSliceABAAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) : Error :=
  avgOver (uniformDistribution (FullSliceQuestion params))
    (fun xy =>
      ∑ gh : FullSliceOutcome params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
            ((family.meas xy.1).toSubMeas.outcome gh.1 *
              (family.meas xy.2).toSubMeas.outcome gh.2 *
              (family.meas xy.1).toSubMeas.outcome gh.1)))

/-- Full-slice ABAB scalar average:
`E_{x,y} ∑_{g,h} ⟨ψ| G^x_g G^y_h G^x_g G^y_h ⊗ I |ψ⟩`. -/
noncomputable def fullSliceABABAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) : Error :=
  avgOver (uniformDistribution (FullSliceQuestion params))
    (fun xy =>
      ∑ gh : FullSliceOutcome params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
            ((family.meas xy.1).toSubMeas.outcome gh.1 *
              (family.meas xy.2).toSubMeas.outcome gh.2 *
              (family.meas xy.1).toSubMeas.outcome gh.1 *
              (family.meas xy.2).toSubMeas.outcome gh.2)))

/-- Evaluated-slice ABA scalar average:
`E_{u,v,x,y} ∑_{a,b} ⟨ψ| G^x_[g(u)=a] G^y_[h(v)=b] G^x_[g(u)=a] ⊗ I |ψ⟩`.

Averaged analog of `evaluatedSliceABATerm` (line 664) over the full slice
question. -/
noncomputable def evaluatedSliceABAAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) : Error :=
  avgOver (uniformDistribution (EvaluatedSliceQuestion params))
    (fun q =>
      ∑ ab : EvaluatedSliceOutcome params,
        evaluatedSliceABATerm params strategy family q ab)

/-- Evaluated-slice ABAB scalar average:
`E_{u,v,x,y} ∑_{a,b} ⟨ψ| G^x_[g(u)=a] G^y_[h(v)=b] G^x_[g(u)=a] G^y_[h(v)=b] ⊗ I |ψ⟩`. -/
noncomputable def evaluatedSliceABABAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) : Error :=
  avgOver (uniformDistribution (EvaluatedSliceQuestion params))
    (fun q =>
      ∑ ab : EvaluatedSliceOutcome params,
        evaluatedSliceABABTerm params strategy family q ab)

/-- Paper `lem:normalization-condition` (`commutativity-G.tex` line 309).

For a sub-measurement `P` and projective sub-measurement `Q`, the sandwiched
family `C_{a,b} = Q_b · P_a · Q_b` satisfies the `closenessOfIP` normalization
condition `∑_a (∑_b C_{a,b}) (∑_b C_{a,b})ᴴ ≤ I`.

TODO(#361): the paper proof (lines 319-328) expands the outer product, uses
projectivity of `Q` to collapse `b ≠ b'` off-diagonals, then `Q_b ≤ I` and the
sub-measurement property of `P` and `Q`. -/
lemma normalizationCondition_sandwich_bound
    {α β : Type*} [Fintype α] [Fintype β]
    (P : SubMeas α ι) (Q : ProjSubMeas β ι) :
    ∑ a : α,
        (∑ b : β, Q.outcome b * P.outcome a * Q.outcome b) *
          (∑ b : β, Q.outcome b * P.outcome a * Q.outcome b)ᴴ ≤ 1 := by
  simpa [normalizationConditionSquareOperator,
    normalizationConditionSquareFamily,
    normalizationConditionSandwichedTotalOperator,
    normalizationConditionSandwichedTotalFamily,
    normalizationConditionSandwichedFamily,
    normalizationConditionSandwichedOperator,
    postprocess] using
      (normalizationConditionSquareFamily P Q).total_le_one

/-- Paper `eq:gcomterms` (`commutativity-G.tex` lines 286-290).

Full-slice analog of `evaluatedSliceCommutation_qSDDOp_avg_eq` (line 878): the
pulled-back `sddErrorOp` on the full-slice product equals `2·(ABAAvg − ABABAvg)`
after using projectivity and the `(x,g) ↔ (y,h)` symmetry to collapse
`BAB + ABA − BABA − ABAB` into the two surviving scalar quartic terms.

TODO(#361): mirror the proof of `evaluatedSliceCommutation_qSDDOp_avg_eq` at
the full-polynomial level.  Relies on `sddErrorOp_pullback_fullSliceQuestion_eq`
to descend from `EvaluatedSliceQuestion` to `FullSliceQuestion`. -/
lemma fullSliceCommutation_qSDDOp_avg_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    sddErrorOp strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => fullSliceProductLeft params strategy family
          (fullSliceQuestionOfEvaluatedSlice params q))
        (fun q => fullSliceProductRight params strategy family
          (fullSliceQuestionOfEvaluatedSlice params q)) =
      2 * (fullSliceABAAvg params strategy family -
        fullSliceABABAvg params strategy family) := by
  have hswap :
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ gh : FullSliceOutcome params,
            fullSliceBABTerm params strategy family
              (fullSliceQuestionOfEvaluatedSlice params q) gh) =
        avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ gh : FullSliceOutcome params,
            fullSliceABATerm params strategy family
              (fullSliceQuestionOfEvaluatedSlice params q) gh) ∧
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ gh : FullSliceOutcome params,
            fullSliceBABATerm params strategy family
              (fullSliceQuestionOfEvaluatedSlice params q) gh) =
        avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ gh : FullSliceOutcome params,
            fullSliceABABTerm params strategy family
              (fullSliceQuestionOfEvaluatedSlice params q) gh) := by
    let eQ : EvaluatedSliceQuestion params ≃ EvaluatedSliceQuestion params :=
      { toFun := Prod.swap
        invFun := Prod.swap
        left_inv := by intro q; cases q; rfl
        right_inv := by intro q; cases q; rfl }
    let eA : FullSliceOutcome params ≃ FullSliceOutcome params :=
      { toFun := Prod.swap
        invFun := Prod.swap
        left_inv := by intro gh; cases gh; rfl
        right_inv := by intro gh; cases gh; rfl }
    constructor
    · calc
        avgOver (uniformDistribution (EvaluatedSliceQuestion params))
            (fun q => ∑ gh : FullSliceOutcome params,
              fullSliceBABTerm params strategy family
                (fullSliceQuestionOfEvaluatedSlice params q) gh)
          = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
              (fun q => ∑ gh : FullSliceOutcome params,
                fullSliceABATerm params strategy family
                  (fullSliceQuestionOfEvaluatedSlice params (eQ q)) gh) := by
                apply avgOver_congr
                intro q
                calc
                  ∑ gh : FullSliceOutcome params,
                      fullSliceBABTerm params strategy family
                        (fullSliceQuestionOfEvaluatedSlice params q) gh
                    = ∑ gh' : FullSliceOutcome params,
                        fullSliceBABTerm params strategy family
                          (fullSliceQuestionOfEvaluatedSlice params q) (eA.symm gh') := by
                            exact Fintype.sum_equiv eA
                              (fun gh =>
                                fullSliceBABTerm params strategy family
                                  (fullSliceQuestionOfEvaluatedSlice params q) gh)
                              (fun gh' =>
                                fullSliceBABTerm params strategy family
                                  (fullSliceQuestionOfEvaluatedSlice params q) (eA.symm gh'))
                              (by intro gh; simp [eA])
                  _ = ∑ gh : FullSliceOutcome params,
                        fullSliceABATerm params strategy family
                          (fullSliceQuestionOfEvaluatedSlice params (eQ q)) gh := by
                            refine Finset.sum_congr rfl ?_
                            intro gh _
                            rcases q with ⟨u, v⟩
                            rcases gh with ⟨g, h⟩
                            simp [eQ, eA, fullSliceQuestionOfEvaluatedSlice,
                              fullSliceBABTerm, fullSliceABATerm,
                              fullSliceFirstFactor, fullSliceSecondFactor]
        _ = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
              (fun q => ∑ gh : FullSliceOutcome params,
                fullSliceABATerm params strategy family
                  (fullSliceQuestionOfEvaluatedSlice params q) gh) := by
                simpa [eQ] using
                  (avgOver_uniform_equiv eQ
                    (fun q => ∑ gh : FullSliceOutcome params,
                      fullSliceABATerm params strategy family
                        (fullSliceQuestionOfEvaluatedSlice params q) gh)).symm
    · calc
        avgOver (uniformDistribution (EvaluatedSliceQuestion params))
            (fun q => ∑ gh : FullSliceOutcome params,
              fullSliceBABATerm params strategy family
                (fullSliceQuestionOfEvaluatedSlice params q) gh)
          = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
              (fun q => ∑ gh : FullSliceOutcome params,
                fullSliceABABTerm params strategy family
                  (fullSliceQuestionOfEvaluatedSlice params (eQ q)) gh) := by
                apply avgOver_congr
                intro q
                calc
                  ∑ gh : FullSliceOutcome params,
                      fullSliceBABATerm params strategy family
                        (fullSliceQuestionOfEvaluatedSlice params q) gh
                    = ∑ gh' : FullSliceOutcome params,
                        fullSliceBABATerm params strategy family
                          (fullSliceQuestionOfEvaluatedSlice params q) (eA.symm gh') := by
                            exact Fintype.sum_equiv eA
                              (fun gh =>
                                fullSliceBABATerm params strategy family
                                  (fullSliceQuestionOfEvaluatedSlice params q) gh)
                              (fun gh' =>
                                fullSliceBABATerm params strategy family
                                  (fullSliceQuestionOfEvaluatedSlice params q) (eA.symm gh'))
                              (by intro gh; simp [eA])
                  _ = ∑ gh : FullSliceOutcome params,
                        fullSliceABABTerm params strategy family
                          (fullSliceQuestionOfEvaluatedSlice params (eQ q)) gh := by
                            refine Finset.sum_congr rfl ?_
                            intro gh _
                            rcases q with ⟨u, v⟩
                            rcases gh with ⟨g, h⟩
                            simp [eQ, eA, fullSliceQuestionOfEvaluatedSlice,
                              fullSliceBABATerm, fullSliceABABTerm,
                              fullSliceFirstFactor, fullSliceSecondFactor]
        _ = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
              (fun q => ∑ gh : FullSliceOutcome params,
                fullSliceABABTerm params strategy family
                  (fullSliceQuestionOfEvaluatedSlice params q) gh) := by
                simpa [eQ] using
                  (avgOver_uniform_equiv eQ
                    (fun q => ∑ gh : FullSliceOutcome params,
                      fullSliceABABTerm params strategy family
                        (fullSliceQuestionOfEvaluatedSlice params q) gh)).symm
  unfold sddErrorOp
  rw [fullSliceCommutation_qSDDOp_avg_expand params strategy family]
  rcases hswap with ⟨hBAB, hBABA⟩
  let sf : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ gh : FullSliceOutcome params,
      fullSliceBABTerm params strategy family
        (fullSliceQuestionOfEvaluatedSlice params q) gh
  let sg : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ gh : FullSliceOutcome params,
      fullSliceABATerm params strategy family
        (fullSliceQuestionOfEvaluatedSlice params q) gh
  let sh : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ gh : FullSliceOutcome params,
      fullSliceBABATerm params strategy family
        (fullSliceQuestionOfEvaluatedSlice params q) gh
  let sk : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ gh : FullSliceOutcome params,
      fullSliceABABTerm params strategy family
        (fullSliceQuestionOfEvaluatedSlice params q) gh
  have hpoint :
      ∀ q,
        (∑ gh : FullSliceOutcome params,
            (fullSliceBABTerm params strategy family
                (fullSliceQuestionOfEvaluatedSlice params q) gh +
              fullSliceABATerm params strategy family
                (fullSliceQuestionOfEvaluatedSlice params q) gh -
              fullSliceBABATerm params strategy family
                (fullSliceQuestionOfEvaluatedSlice params q) gh -
              fullSliceABABTerm params strategy family
                (fullSliceQuestionOfEvaluatedSlice params q) gh)) =
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
  have hABA_pullback :
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => ∑ gh : FullSliceOutcome params,
          fullSliceABATerm params strategy family
            (fullSliceQuestionOfEvaluatedSlice params q) gh) =
      fullSliceABAAvg params strategy family := by
    let e := evaluatedSliceQuestionEquiv params
    calc
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ gh : FullSliceOutcome params,
            fullSliceABATerm params strategy family
              (fullSliceQuestionOfEvaluatedSlice params q) gh)
        = avgOver
            (uniformDistribution ((Point params × Point params) × FullSliceQuestion params))
            (fun r => ∑ gh : FullSliceOutcome params,
              fullSliceABATerm params strategy family r.2 gh) := by
                calc
                  avgOver (uniformDistribution (EvaluatedSliceQuestion params))
                      (fun q => ∑ gh : FullSliceOutcome params,
                        fullSliceABATerm params strategy family
                          (fullSliceQuestionOfEvaluatedSlice params q) gh)
                    = avgOver
                        (uniformDistribution ((Point params × Point params) × FullSliceQuestion params))
                        (fun r =>
                          ∑ gh : FullSliceOutcome params,
                            fullSliceABATerm params strategy family
                              (fullSliceQuestionOfEvaluatedSlice params (e.symm r)) gh) :=
                        avgOver_uniform_equiv e _
                  _ = avgOver
                        (uniformDistribution ((Point params × Point params) × FullSliceQuestion params))
                        (fun r => ∑ gh : FullSliceOutcome params,
                          fullSliceABATerm params strategy family r.2 gh) := by
                          apply avgOver_congr
                          rintro ⟨⟨u, v⟩, x, y⟩
                          simp [e, evaluatedSliceQuestionEquiv, fullSliceQuestionOfEvaluatedSlice]
      _ = avgOver (uniformDistribution (FullSliceQuestion params))
            (fun xy => ∑ gh : FullSliceOutcome params,
              fullSliceABATerm params strategy family xy gh) := by
              simpa using
                (avgOver_uniform_snd
                  (α := Point params × Point params)
                  (β := FullSliceQuestion params)
                  (f := fun xy => ∑ gh : FullSliceOutcome params,
                    fullSliceABATerm params strategy family xy gh))
      _ = fullSliceABAAvg params strategy family := by
            rfl
  have hABAB_pullback :
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => ∑ gh : FullSliceOutcome params,
          fullSliceABABTerm params strategy family
            (fullSliceQuestionOfEvaluatedSlice params q) gh) =
      fullSliceABABAvg params strategy family := by
    let e := evaluatedSliceQuestionEquiv params
    calc
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ gh : FullSliceOutcome params,
            fullSliceABABTerm params strategy family
              (fullSliceQuestionOfEvaluatedSlice params q) gh)
        = avgOver
            (uniformDistribution ((Point params × Point params) × FullSliceQuestion params))
            (fun r => ∑ gh : FullSliceOutcome params,
              fullSliceABABTerm params strategy family r.2 gh) := by
                calc
                  avgOver (uniformDistribution (EvaluatedSliceQuestion params))
                      (fun q => ∑ gh : FullSliceOutcome params,
                        fullSliceABABTerm params strategy family
                          (fullSliceQuestionOfEvaluatedSlice params q) gh)
                    = avgOver
                        (uniformDistribution ((Point params × Point params) × FullSliceQuestion params))
                        (fun r =>
                          ∑ gh : FullSliceOutcome params,
                            fullSliceABABTerm params strategy family
                              (fullSliceQuestionOfEvaluatedSlice params (e.symm r)) gh) :=
                        avgOver_uniform_equiv e _
                  _ = avgOver
                        (uniformDistribution ((Point params × Point params) × FullSliceQuestion params))
                        (fun r => ∑ gh : FullSliceOutcome params,
                          fullSliceABABTerm params strategy family r.2 gh) := by
                          apply avgOver_congr
                          rintro ⟨⟨u, v⟩, x, y⟩
                          simp [e, evaluatedSliceQuestionEquiv, fullSliceQuestionOfEvaluatedSlice]
      _ = avgOver (uniformDistribution (FullSliceQuestion params))
            (fun xy => ∑ gh : FullSliceOutcome params,
              fullSliceABABTerm params strategy family xy gh) := by
              simpa using
                (avgOver_uniform_snd
                  (α := Point params × Point params)
                  (β := FullSliceQuestion params)
                  (f := fun xy => ∑ gh : FullSliceOutcome params,
                    fullSliceABABTerm params strategy family xy gh))
      _ = fullSliceABABAvg params strategy family := by
            rfl
  calc
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
                (fullSliceQuestionOfEvaluatedSlice params q) gh))
      = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ gh : FullSliceOutcome params,
            fullSliceBABTerm params strategy family
              (fullSliceQuestionOfEvaluatedSlice params q) gh) +
        avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ gh : FullSliceOutcome params,
            fullSliceABATerm params strategy family
              (fullSliceQuestionOfEvaluatedSlice params q) gh) -
        avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ gh : FullSliceOutcome params,
            fullSliceBABATerm params strategy family
              (fullSliceQuestionOfEvaluatedSlice params q) gh) -
        avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ gh : FullSliceOutcome params,
            fullSliceABABTerm params strategy family
              (fullSliceQuestionOfEvaluatedSlice params q) gh) := by
            calc
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
                          (fullSliceQuestionOfEvaluatedSlice params q) gh))
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
          (fun q => ∑ gh : FullSliceOutcome params,
            fullSliceABATerm params strategy family
              (fullSliceQuestionOfEvaluatedSlice params q) gh) +
        avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ gh : FullSliceOutcome params,
            fullSliceABATerm params strategy family
              (fullSliceQuestionOfEvaluatedSlice params q) gh) -
        avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ gh : FullSliceOutcome params,
            fullSliceABABTerm params strategy family
              (fullSliceQuestionOfEvaluatedSlice params q) gh) -
        avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ gh : FullSliceOutcome params,
            fullSliceABABTerm params strategy family
              (fullSliceQuestionOfEvaluatedSlice params q) gh) := by
            rw [hBAB, hBABA]
    _ = 2 * (fullSliceABAAvg params strategy family -
          fullSliceABABAvg params strategy family) := by
            rw [hABA_pullback, hABAB_pullback]
            ring


end MIPStarRE.LDT.Commutativity
