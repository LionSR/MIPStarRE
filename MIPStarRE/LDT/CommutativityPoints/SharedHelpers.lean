import MIPStarRE.LDT.CommutativityPoints.Approximation

/-!
# Section 10 — shared-line reindexing helpers

Reindexing and tensor-placement helper lemmas for the commutativity-at-points argument.
-/

namespace MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Matrix MatrixOrder ComplexOrder BigOperators

/-! ## Shared reindexing and tensor-placement helpers -/

private lemma qSDDOp_symm
    {Outcome : Type*}
    (ψ : QuantumState ι) [Fintype Outcome]
    (A B : OpFamily Outcome ι) :
    qSDDOp ψ A B = qSDDOp ψ B A := by
  let F : Outcome → MIPStarRE.Quantum.Op ι := fun a => A.outcome a - B.outcome a
  let G : Outcome → MIPStarRE.Quantum.Op ι := fun a => B.outcome a - A.outcome a
  have hFG : F = fun a => -G a := by
    funext a
    dsimp [F, G]
    abel
  unfold qSDDOp qSDDCore
  change ∑ a : Outcome, ev ψ ((F a)ᴴ * F a) = ∑ a : Outcome, ev ψ ((G a)ᴴ * G a)
  rw [hFG]
  refine Finset.sum_congr rfl ?_
  intro a _
  change ev ψ ((-G a)ᴴ * (-G a)) = ev ψ ((G a)ᴴ * G a)
  simp

lemma sddOpRel_symm
    {Question Outcome : Type*}
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome ι) (δ : Error) :
    SDDOpRel ψ 𝒟 A B δ →
      SDDOpRel ψ 𝒟 B A δ := by
  intro ⟨h⟩
  constructor
  simpa [sddErrorOp, qSDDOp_symm] using h

/-- Reindexing the outcome type of both operator families preserves `qSDDOp`. -/
lemma qSDDOp_reindex
    {Outcome Outcome' : Type*}
    [Fintype Outcome] [Fintype Outcome']
    (e : Outcome ≃ Outcome')
    (ψ : QuantumState ι)
    (A B : OpFamily Outcome ι) :
    qSDDOp ψ A B =
      qSDDOp ψ
        ({ outcome := fun a' => A.outcome (e.symm a')
           total := A.total } : OpFamily Outcome' ι)
        ({ outcome := fun a' => B.outcome (e.symm a')
           total := B.total } : OpFamily Outcome' ι) := by
  unfold qSDDOp qSDDCore
  calc
    ∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a))
      = ∑ a' : Outcome',
          ev ψ
            ((A.outcome (e.symm a') - B.outcome (e.symm a'))ᴴ *
              (A.outcome (e.symm a') - B.outcome (e.symm a'))) := by
          exact Fintype.sum_equiv e
            (fun a =>
              ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a)))
            (fun a' =>
              ev ψ
                ((A.outcome (e.symm a') - B.outcome (e.symm a'))ᴴ *
                  (A.outcome (e.symm a') - B.outcome (e.symm a'))))
            (by
              intro a
              simp)
    _ = qSDDOp ψ
          ({ outcome := fun a' => A.outcome (e.symm a')
             total := A.total } : OpFamily Outcome' ι)
          ({ outcome := fun a' => B.outcome (e.symm a')
             total := B.total } : OpFamily Outcome' ι) := by
          rfl

/-- Reindexing the outcome type of both indexed families preserves `SDDOpRel`. -/
lemma sddOpRel_reindex
    {Question Outcome Outcome' : Type*}
    [Fintype Outcome] [Fintype Outcome']
    (e : Outcome ≃ Outcome')
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome ι) (δ : Error) :
    SDDOpRel ψ 𝒟 A B δ →
      SDDOpRel ψ 𝒟
        (fun q =>
          ({ outcome := fun a' => (A q).outcome (e.symm a')
             total := (A q).total } : OpFamily Outcome' ι))
        (fun q =>
          ({ outcome := fun a' => (B q).outcome (e.symm a')
             total := (B q).total } : OpFamily Outcome' ι))
        δ := by
  intro ⟨h⟩
  constructor
  unfold sddErrorOp at *
  calc
    avgOver 𝒟
        (fun q =>
          qSDDOp ψ
            ({ outcome := fun a' => (A q).outcome (e.symm a')
               total := (A q).total } : OpFamily Outcome' ι)
            ({ outcome := fun a' => (B q).outcome (e.symm a')
               total := (B q).total } : OpFamily Outcome' ι))
      = avgOver 𝒟 (fun q => qSDDOp ψ (A q) (B q)) := by
          apply avgOver_congr
          intro q
          rw [qSDDOp_reindex e ψ (A q) (B q)]
    _ ≤ δ := h

/-- Pointwise equality of outcomes preserves `SDDOpRel`. -/
lemma sddOpRel_congr_outcome
    {Question Outcome : Type*}
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B A' B' : IdxOpFamily Question Outcome ι) (δ : Error)
    (hA : ∀ q a, (A q).outcome a = (A' q).outcome a)
    (hB : ∀ q a, (B q).outcome a = (B' q).outcome a) :
    SDDOpRel ψ 𝒟 A B δ →
      SDDOpRel ψ 𝒟 A' B' δ := by
  intro ⟨h⟩
  constructor
  unfold sddErrorOp at *
  calc
    avgOver 𝒟 (fun q => qSDDOp ψ (A' q) (B' q))
      = avgOver 𝒟 (fun q => qSDDOp ψ (A q) (B q)) := by
          apply avgOver_congr
          intro q
          unfold qSDDOp qSDDCore
          apply Finset.sum_congr rfl
          intro a _
          rw [hA q a, hB q a]
    _ ≤ δ := h

lemma subMeas_sum_adjoint_mul_le_one
    {Outcome : Type*}
    [Fintype Outcome]
    (A : SubMeas Outcome ι) :
    ∑ a : Outcome, (A.outcome a)ᴴ * A.outcome a ≤ 1 := by
  calc
    ∑ a : Outcome, (A.outcome a)ᴴ * A.outcome a
      = ∑ a : Outcome, A.outcome a * A.outcome a := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [SubMeas.outcome_hermitian]
    _ ≤ ∑ a : Outcome, A.outcome a := by
          refine Finset.sum_le_sum ?_
          intro a _
          exact MIPStarRE.Quantum.sq_le_self (A.outcome_pos a) (A.outcome_le_one a)
    _ = A.total := A.sum_eq_total
    _ ≤ 1 := A.total_le_one

/-- Multiplying a left lift with a left-placed family stays on the left tensor factor. -/
lemma liftLeft_mul_leftPlaced_outcome
    {α β : Type*}
    [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι)
    (a : α) (b : β) :
    (A.liftLeft).outcome a * (OpFamily.leftPlacedOpFamily B.toOpFamily).outcome b =
      leftTensor (A.outcome a * B.outcome b) := by
  calc
    (A.liftLeft).outcome a * (OpFamily.leftPlacedOpFamily B.toOpFamily).outcome b
      = leftTensor (A.outcome a) * leftTensor (B.outcome b) := by
          rfl
    _ = leftTensor (A.outcome a * B.outcome b) := by
          rw [leftTensor_mul_leftTensor]

/-- Multiplying a left lift with a right-placed family gives the tensor product. -/
lemma liftLeft_mul_rightPlaced_outcome
    {α β : Type*}
    [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι)
    (a : α) (b : β) :
    (A.liftLeft).outcome a * (OpFamily.rightPlacedOpFamily B.toOpFamily).outcome b =
      opTensor (A.outcome a) (B.outcome b) := by
  calc
    (A.liftLeft).outcome a * (OpFamily.rightPlacedOpFamily B.toOpFamily).outcome b
      = leftTensor (A.outcome a) * rightTensor (B.outcome b) := by
          rfl
    _ = opTensor (A.outcome a) (B.outcome b) := by
          rw [leftTensor_mul_rightTensor_eq_opTensor]

/-- Multiplying a right lift with a left-placed family gives the tensor product. -/
lemma liftRight_mul_leftPlaced_outcome
    {α β : Type*}
    [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι)
    (a : α) (b : β) :
    (A.liftRight).outcome a * (OpFamily.leftPlacedOpFamily B.toOpFamily).outcome b =
      opTensor (B.outcome b) (A.outcome a) := by
  calc
    (A.liftRight).outcome a * (OpFamily.leftPlacedOpFamily B.toOpFamily).outcome b
      = rightTensor (A.outcome a) * leftTensor (B.outcome b) := by
          rfl
    _ = opTensor (B.outcome b) (A.outcome a) := by
          rw [rightTensor_mul_leftTensor_eq_opTensor]

/-- Multiplying a right lift with a right-placed family stays on the right tensor factor. -/
lemma liftRight_mul_rightPlaced_outcome
    {α β : Type*}
    [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι)
    (a : α) (b : β) :
    (A.liftRight).outcome a * (OpFamily.rightPlacedOpFamily B.toOpFamily).outcome b =
      rightTensor (A.outcome a * B.outcome b) := by
  calc
    (A.liftRight).outcome a * (OpFamily.rightPlacedOpFamily B.toOpFamily).outcome b
      = rightTensor (A.outcome a) * rightTensor (B.outcome b) := by
          rfl
    _ = rightTensor (A.outcome a * B.outcome b) := by
          rw [rightTensor_mul_rightTensor]

private theorem sharedDiagonalLineQuestionOfPointPair_sampledPointPair
    (params : Parameters)
    [FieldModel params.q]
    (s : PointPairQuestion params × Fq params) :
    sampledPointPairFromSharedDiagonalQuestion params
      (sharedDiagonalLineQuestionOfPointPair params s) = s.1 := by
  rcases s with ⟨⟨u, v⟩, t⟩
  refine Prod.ext ?_ ?_
  · funext i
    simp [sampledPointPairFromSharedDiagonalQuestion, sharedDiagonalLineQuestionOfPointPair,
      DiagonalLine.pointAt, addPoint, smulPoint, addCoord, subCoord, mulCoord]
  · funext i
    simp [sampledPointPairFromSharedDiagonalQuestion, sharedDiagonalLineQuestionOfPointPair,
      DiagonalLine.pointAt, addPoint, smulPoint, addCoord, subCoord, mulCoord]
    rw [← encode_decodeScalar (v i)]
    congr 1
    ring_nf
    simpa using (decode_encodeScalar (params := params) (decodeScalar (v i)))

private theorem sharedDiagonalLineQuestionOfPointPair_of_line
    (params : Parameters)
    [FieldModel params.q]
    (ℓ : DiagonalLine params)
    (t : Fq params) :
    sharedDiagonalLineQuestionOfPointPair params
      (((ℓ.pointAt t, ℓ.pointAt (addCoord t (encodeScalar 1))), t)) =
      (ℓ, (t, addCoord t (encodeScalar 1))) := by
  cases ℓ with
  | mk base direction =>
      change
        (({ base := fun i => _, direction := fun i => _ } : DiagonalLine params),
          (t, addCoord t (encodeScalar 1))) =
        ({ base := base, direction := direction }, (t, addCoord t (encodeScalar 1)))
      congr
      · funext i
        simp [DiagonalLine.pointAt,
          addPoint, smulPoint, addCoord, subCoord, mulCoord]
        rw [← encode_decodeScalar (base i)]
        congr 1
        ring_nf
        simpa using (decode_encodeScalar (params := params) (decodeScalar (base i)))
      · funext i
        simp [DiagonalLine.pointAt,
          addPoint, smulPoint, addCoord, subCoord, mulCoord]
        rw [← encode_decodeScalar (direction i)]
        congr 1
        ring_nf
        simpa using (decode_encodeScalar (params := params) (decodeScalar (direction i)))

private theorem sharedDiagonalLineQuestionOfPointPair_injective
    (params : Parameters)
    [FieldModel params.q] :
    Function.Injective (sharedDiagonalLineQuestionOfPointPair params) := by
  intro s₁ s₂ hs
  have hs' := congrArg
    (fun q => (sampledPointPairFromSharedDiagonalQuestion params q, q.2.1)) hs
  rcases Prod.mk.inj (by
    simpa [sharedDiagonalLineQuestionOfPointPair_sampledPointPair] using hs') with ⟨hpair, ht⟩
  exact Prod.ext hpair ht

private lemma avgOver_pointPairSharedDiagonalLine_eq_uniform_seed
    (params : Parameters)
    [FieldModel params.q]
    (f : PointPairDiagonalLineQuestion params → Error) :
    avgOver (pointPairSharedDiagonalLineDistribution params) f =
      avgOver (uniformDistribution (PointPairQuestion params × Fq params))
        (fun s => f (sharedDiagonalLineQuestionOfPointPair params s)) := by
  let e : PointPairQuestion params × Fq params → PointPairDiagonalLineQuestion params :=
    sharedDiagonalLineQuestionOfPointPair params
  have hinj : Function.Injective e := sharedDiagonalLineQuestionOfPointPair_injective params
  unfold avgOver pointPairSharedDiagonalLineDistribution uniformDistribution
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro s _
    have hs : e s ∈ Finset.univ.image e := by
      exact Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩
    simp [e, hs]
  · intro s₁ _ s₂ _ hs
    exact hinj hs

private noncomputable def pointPairSharedDiagonalLine_ignore_first_equiv
    (params : Parameters)
    [FieldModel params.q] :
    (PointPairQuestion params × Fq params) ≃ PointDiagonalLineQuestion params where
  toFun := fun s =>
    let q := sharedDiagonalLineQuestionOfPointPair params s
    (q.1, q.2.2)
  invFun := fun r =>
    let ℓ := r.1
    let tv := r.2
    (((ℓ.pointAt (subCoord tv (encodeScalar 1)), ℓ.pointAt tv)),
      subCoord tv (encodeScalar 1))
  left_inv := by
    rintro ⟨⟨u, v⟩, t⟩
    refine Prod.ext ?_ ?_
    · simpa [Prod.ext_iff, sharedDiagonalLineQuestionOfPointPair, addCoord, subCoord] using
        sharedDiagonalLineQuestionOfPointPair_sampledPointPair params ((u, v), t)
    · simp [sharedDiagonalLineQuestionOfPointPair, addCoord, subCoord]
  right_inv := by
    rintro ⟨ℓ, tv⟩
    simpa [addCoord, subCoord] using
      congrArg (fun q => (q.1, q.2.2))
        (sharedDiagonalLineQuestionOfPointPair_of_line params ℓ
          (subCoord tv (encodeScalar 1)))

private noncomputable def pointPairSharedDiagonalLine_ignore_second_equiv
    (params : Parameters)
    [FieldModel params.q] :
    (PointPairQuestion params × Fq params) ≃ PointDiagonalLineQuestion params where
  toFun := fun s =>
    let q := sharedDiagonalLineQuestionOfPointPair params s
    (q.1, q.2.1)
  invFun := fun r =>
    let ℓ := r.1
    let t := r.2
    (((ℓ.pointAt t, ℓ.pointAt (addCoord t (encodeScalar 1))), t))
  left_inv := by
    rintro ⟨⟨u, v⟩, t⟩
    refine Prod.ext ?_ ?_
    · simpa [Prod.ext_iff, sharedDiagonalLineQuestionOfPointPair] using
        sharedDiagonalLineQuestionOfPointPair_sampledPointPair params ((u, v), t)
    · simp [sharedDiagonalLineQuestionOfPointPair]
  right_inv := by
    rintro ⟨ℓ, t⟩
    simpa using
      congrArg (fun q => (q.1, q.2.1))
        (sharedDiagonalLineQuestionOfPointPair_of_line params ℓ t)

private lemma avgOver_pointPairSharedDiagonalLine_ignore_first
    (params : Parameters)
    [FieldModel params.q]
    (f : PointDiagonalLineQuestion params → Error) :
    avgOver (pointPairSharedDiagonalLineDistribution params)
      (fun q => f (q.1, q.2.2)) =
      avgOver (pointWithDiagonalLineDistribution params) f := by
  calc
    avgOver (pointPairSharedDiagonalLineDistribution params)
        (fun q => f (q.1, q.2.2))
      = avgOver (uniformDistribution (PointPairQuestion params × Fq params))
          (fun s => f ((pointPairSharedDiagonalLine_ignore_first_equiv params) s)) := by
            simpa [pointPairSharedDiagonalLine_ignore_first_equiv] using
              avgOver_pointPairSharedDiagonalLine_eq_uniform_seed params
                (fun q => f (q.1, q.2.2))
    _ = avgOver (uniformDistribution (PointDiagonalLineQuestion params)) f := by
          simpa using
            (avgOver_uniform_equiv (pointPairSharedDiagonalLine_ignore_first_equiv params)
              (fun s => f ((pointPairSharedDiagonalLine_ignore_first_equiv params) s)))
    _ = avgOver (pointWithDiagonalLineDistribution params) f := by
          simp [pointWithDiagonalLineDistribution]

private lemma avgOver_pointPairSharedDiagonalLine_ignore_second
    (params : Parameters)
    [FieldModel params.q]
    (f : PointDiagonalLineQuestion params → Error) :
    avgOver (pointPairSharedDiagonalLineDistribution params)
      (fun q => f (q.1, q.2.1)) =
      avgOver (pointWithDiagonalLineDistribution params) f := by
  calc
    avgOver (pointPairSharedDiagonalLineDistribution params)
        (fun q => f (q.1, q.2.1))
      = avgOver (uniformDistribution (PointPairQuestion params × Fq params))
          (fun s => f ((pointPairSharedDiagonalLine_ignore_second_equiv params) s)) := by
            simpa [pointPairSharedDiagonalLine_ignore_second_equiv] using
              avgOver_pointPairSharedDiagonalLine_eq_uniform_seed params
                (fun q => f (q.1, q.2.1))
    _ = avgOver (uniformDistribution (PointDiagonalLineQuestion params)) f := by
          simpa using
            (avgOver_uniform_equiv (pointPairSharedDiagonalLine_ignore_second_equiv params)
              (fun s => f ((pointPairSharedDiagonalLine_ignore_second_equiv params) s)))
    _ = avgOver (pointWithDiagonalLineDistribution params) f := by
          simp [pointWithDiagonalLineDistribution]

lemma avgOver_pointPairSharedDiagonalLine_sampled_pair
    (params : Parameters)
    [FieldModel params.q]
    (f : PointPairQuestion params → Error) :
    avgOver (pointPairSharedDiagonalLineDistribution params)
      (fun q => f (sampledPointPairFromSharedDiagonalQuestion params q)) =
      avgOver (uniformDistribution (PointPairQuestion params)) f := by
  calc
    avgOver (pointPairSharedDiagonalLineDistribution params)
        (fun q => f (sampledPointPairFromSharedDiagonalQuestion params q))
      = avgOver (uniformDistribution (PointPairQuestion params × Fq params))
          (fun s => f s.1) := by
            simpa [sharedDiagonalLineQuestionOfPointPair_sampledPointPair] using
              avgOver_pointPairSharedDiagonalLine_eq_uniform_seed params
                (fun q => f (sampledPointPairFromSharedDiagonalQuestion params q))
    _ = avgOver (uniformDistribution (PointPairQuestion params)) f := by
          exact avgOver_uniform_fst f

lemma pointMeasurementProductAlongSharedLine_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    (pointMeasurementProductAlongSharedLine params strategy q).outcome (a, b) =
      leftTensor
        ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a *
          (strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b) := by
  simp [pointMeasurementProductAlongSharedLine, pointMeasurementProductLeft,
    orderedProductOpFamily, sampledPointPairFromSharedDiagonalQuestion,
    OpFamily.leftPlacedOpFamily]

lemma pointMeasurementProductAlongSharedLineReversed_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    (pointMeasurementProductAlongSharedLineReversed params strategy q).outcome (a, b) =
      leftTensor
        ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b *
          (strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a) := by
  simp [pointMeasurementProductAlongSharedLineReversed, pointMeasurementProductRight,
    reversedProductOpFamily, sampledPointPairFromSharedDiagonalQuestion,
    OpFamily.leftPlacedOpFamily]

lemma pointDiagonalLineMixedProductLeft_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    ((IdxSubMeas.toIdxOpFamily
        (pointDiagonalLineMixedProductLeft params strategy) q).outcome (a, b)) =
      opTensor
        ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a)
        ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) := by
  simp [pointDiagonalLineMixedProductLeft, tensorProductSubMeas,
    sampledDiagonalLineEvaluation, IdxSubMeas.toIdxOpFamily, SubMeas.toOpFamily,
    leftTensor_mul_rightTensor_eq_opTensor]

lemma pointDiagonalLineMixedProductRight_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    ((IdxSubMeas.toIdxOpFamily
        (pointDiagonalLineMixedProductRight params strategy) q).outcome (a, b)) =
      opTensor
        ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b)
        ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) := by
  classical
  simp [pointDiagonalLineMixedProductRight, tensorProductSubMeas, sampledDiagonalLineEvaluation,
    postprocess, Prod.swap, IdxSubMeas.toIdxOpFamily, SubMeas.toOpFamily,
    leftTensor_mul_rightTensor_eq_opTensor]
  have hfilter :
      (Finset.univ.filter (fun ab : Fq params × Fq params => ab.2 = a ∧ ab.1 = b)) =
        {(b, a)} := by
    ext ab
    rcases ab with ⟨a', b'⟩
    simp [and_comm]
  rw [hfilter]
  simp

lemma diagonalLineProductOrdered_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    (diagonalLineProductOrdered params strategy q).outcome (a, b) =
      rightTensor
        ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b *
          (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) := by
  simp [diagonalLineProductOrdered, sampledDiagonalLineEvaluation,
    OpFamily.rightPlacedOpFamily, reversedProductOpFamily]

lemma diagonalLineProductReversed_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    (diagonalLineProductReversed params strategy q).outcome (a, b) =
      rightTensor
        ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a *
          (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) := by
  simp [diagonalLineProductReversed, sampledDiagonalLineEvaluation,
    OpFamily.rightPlacedOpFamily, orderedProductOpFamily]

lemma sampledDiagonalLineApproximation_ignore_first
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
      (pointDiagonalLineApproxError params gamma) := by
  rcases sampledDiagonalLineApproximation_pointWithDiagonalLine
    params strategy eps delta gamma hgood with ⟨happrox⟩
  constructor
  calc
    sddErrorOp strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (fun q =>
          OpFamily.leftPlacedOpFamily (ιB := ι)
            ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas))
        (fun q =>
          OpFamily.rightPlacedOpFamily (ιA := ι)
            (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
      = avgOver (pointPairSharedDiagonalLineDistribution params)
          (fun q =>
            qSDD strategy.state
              ((IdxSubMeas.liftLeft (sampledPointMeasurement params strategy)) (q.1, q.2.2))
              ((IdxSubMeas.liftRight (sampledDiagonalLineEvaluation params strategy))
                (q.1, q.2.2))) := by
            unfold sddErrorOp
            apply avgOver_congr
            intro q
            unfold qSDDOp qSDD qSDDCore IdxSubMeas.liftLeft IdxSubMeas.liftRight
              OpFamily.leftPlacedOpFamily OpFamily.rightPlacedOpFamily
              sampledPointMeasurement sampledPointFromDiagonalQuestion SubMeas.toOpFamily
            rfl
    _ = avgOver (pointWithDiagonalLineDistribution params)
          (fun q =>
            qSDD strategy.state
              ((IdxSubMeas.liftLeft (sampledPointMeasurement params strategy)) q)
              ((IdxSubMeas.liftRight (sampledDiagonalLineEvaluation params strategy)) q)) := by
            exact avgOver_pointPairSharedDiagonalLine_ignore_first params
              (fun q =>
                qSDD strategy.state
                  ((IdxSubMeas.liftLeft (sampledPointMeasurement params strategy)) q)
                  ((IdxSubMeas.liftRight (sampledDiagonalLineEvaluation params strategy)) q))
    _ = sddError strategy.state
          (pointWithDiagonalLineDistribution params)
          (IdxSubMeas.liftLeft (sampledPointMeasurement params strategy))
          (IdxSubMeas.liftRight (sampledDiagonalLineEvaluation params strategy)) := by
            rfl
    _ ≤ pointDiagonalLineApproxError params gamma := happrox

lemma sampledDiagonalLineApproximation_ignore_second
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      (pointDiagonalLineApproxError params gamma) := by
  rcases sampledDiagonalLineApproximation_pointWithDiagonalLine
    params strategy eps delta gamma hgood with ⟨happrox⟩
  constructor
  calc
    sddErrorOp strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (fun q =>
          OpFamily.leftPlacedOpFamily (ιB := ι)
            ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
        (fun q =>
          OpFamily.rightPlacedOpFamily (ιA := ι)
            (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      = avgOver (pointPairSharedDiagonalLineDistribution params)
          (fun q =>
            qSDD strategy.state
              ((IdxSubMeas.liftLeft (sampledPointMeasurement params strategy)) (q.1, q.2.1))
              ((IdxSubMeas.liftRight (sampledDiagonalLineEvaluation params strategy))
                (q.1, q.2.1))) := by
            unfold sddErrorOp
            apply avgOver_congr
            intro q
            unfold qSDDOp qSDD qSDDCore IdxSubMeas.liftLeft IdxSubMeas.liftRight
              OpFamily.leftPlacedOpFamily OpFamily.rightPlacedOpFamily
              sampledPointMeasurement sampledPointFromDiagonalQuestion SubMeas.toOpFamily
            rfl
    _ = avgOver (pointWithDiagonalLineDistribution params)
          (fun q =>
            qSDD strategy.state
              ((IdxSubMeas.liftLeft (sampledPointMeasurement params strategy)) q)
              ((IdxSubMeas.liftRight (sampledDiagonalLineEvaluation params strategy)) q)) := by
            exact avgOver_pointPairSharedDiagonalLine_ignore_second params
              (fun q =>
                qSDD strategy.state
                  ((IdxSubMeas.liftLeft (sampledPointMeasurement params strategy)) q)
                  ((IdxSubMeas.liftRight (sampledDiagonalLineEvaluation params strategy)) q))
    _ = sddError strategy.state
          (pointWithDiagonalLineDistribution params)
          (IdxSubMeas.liftLeft (sampledPointMeasurement params strategy))
          (IdxSubMeas.liftRight (sampledDiagonalLineEvaluation params strategy)) := by
            rfl
    _ ≤ pointDiagonalLineApproxError params gamma := happrox


end MIPStarRE.LDT.CommutativityPoints
