import MIPStarRE.LDT.CommutativityPoints.SharedHelpers.Core

/-!
# Section 10 commutativity points: shared-line helpers

Compatibility lemmas between sampled point pairs and shared-diagonal line
questions, used by both the lift and drop bridges.

## References

- arXiv:2009.12982, Section 10 (commutativity of the point measurements).
-/

namespace MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Matrix MatrixOrder ComplexOrder BigOperators
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
