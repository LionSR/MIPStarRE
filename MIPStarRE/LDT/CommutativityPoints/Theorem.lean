import MIPStarRE.LDT.CommutativityPoints.Defs

/-!
# Section 10 — Theorems

Output structures and theorem statements for commutativity at points.
The strategy state is bipartite (`QuantumState (ι × ι)`), so all fields
use `strategy.state` directly.
-/

namespace MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Matrix MatrixOrder ComplexOrder BigOperators

private def pointDiagonalLineQuestionEquiv (params : Parameters) :
    PointDiagonalLineQuestion params ≃ DiagonalTestSample params where
  toFun := fun q => (q.1.base, (q.1.direction, q.2))
  invFun := fun s =>
    ({ base := s.1, direction := s.2.1 }, s.2.2)
  left_inv := by
    intro q
    rcases q with ⟨⟨base, direction⟩, t⟩
    rfl
  right_inv := by
    intro s
    rcases s with ⟨base, direction, t⟩
    rfl

private lemma avgOver_uniform_equiv
    {α β : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (e : α ≃ β) (f : α → Error) :
    avgOver (uniformDistribution α) f =
      avgOver (uniformDistribution β) (fun b => f (e.symm b)) := by
  calc
    avgOver (uniformDistribution α) f
      = (1 / (Fintype.card α : Error)) * ∑ a : α, f a := by
          simp [avgOver, uniformDistribution, Finset.mul_sum]
    _ = (1 / (Fintype.card β : Error)) * ∑ a : α, f a := by
          rw [Fintype.card_congr e]
    _ = (1 / (Fintype.card β : Error)) * ∑ b : β, f (e.symm b) := by
          congr 1
          exact Fintype.sum_equiv e f (fun b => f (e.symm b)) (by
            intro a
            simp)
    _ = avgOver (uniformDistribution β) (fun b => f (e.symm b)) := by
          simp [avgOver, uniformDistribution, Finset.mul_sum]

private lemma sampledDiagonalLineConsistency
    (params : Parameters)
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    ConsRel strategy.state
      (pointWithDiagonalLineDistribution params)
      (IdxSubMeas.liftLeft (sampledPointMeasurement params strategy))
      (IdxSubMeas.liftRight (sampledDiagonalLineEvaluation params strategy))
      (restrictedDiagonalLinesConsistencyError params gamma) := by
  /-
  This is the diagonal-lines test, rewritten in the
  `PointDiagonalLineQuestion` indexing used in this section.
  Alice's point measurement is on the left factor, Bob's diagonal-line
  measurement is on the right factor.
  -/
  let e := pointDiagonalLineQuestionEquiv params
  have hrewrite :
      consError strategy.state
        (pointWithDiagonalLineDistribution params)
        (IdxSubMeas.liftLeft (sampledPointMeasurement params strategy))
        (IdxSubMeas.liftRight (sampledDiagonalLineEvaluation params strategy)) =
      consError strategy.state
        (uniformDistribution (DiagonalTestSample params))
        (IdxSubMeas.liftLeft (diagonalPointAnswerFamily strategy))
        (IdxSubMeas.liftRight (diagonalLineAnswerFamily strategy)) := by
    unfold consError
    simpa [e, pointWithDiagonalLineDistribution, sampledPointMeasurement,
      sampledDiagonalLineEvaluation, sampledPointFromDiagonalQuestion,
      diagonalPointAnswerFamily, diagonalLineAnswerFamily] using
        avgOver_uniform_equiv e
          (fun q =>
            qConsDefect strategy.state
              ((IdxSubMeas.liftLeft (sampledPointMeasurement params strategy)) q)
              ((IdxSubMeas.liftRight (sampledDiagonalLineEvaluation params strategy)) q))
  constructor
  rw [hrewrite]
  have hγ : 0 ≤ gamma := by
    exact le_trans (consError_nonneg strategy.state
      (uniformDistribution (DiagonalTestSample params))
      (IdxSubMeas.liftLeft (diagonalPointAnswerFamily strategy))
      (IdxSubMeas.liftRight (diagonalLineAnswerFamily strategy)))
      hgood.diagonalLineTest
  have hm : (1 : Error) ≤ params.m := by
    exact_mod_cast params.hm
  calc
    consError strategy.state
        (uniformDistribution (DiagonalTestSample params))
        (IdxSubMeas.liftLeft (diagonalPointAnswerFamily strategy))
        (IdxSubMeas.liftRight (diagonalLineAnswerFamily strategy))
      ≤ gamma := hgood.diagonalLineTest
    _ ≤ gamma * (params.m : Error) := by nlinarith

private lemma sampledDiagonalLineApproximation
    (params : Parameters)
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDRel strategy.state
      (pointWithDiagonalLineDistribution params)
      (IdxSubMeas.liftLeft (sampledPointMeasurement params strategy))
      (IdxSubMeas.liftRight (sampledDiagonalLineEvaluation params strategy))
      (pointDiagonalLineApproxError params gamma) := by
  /-
  Apply `prop:simeq-to-approx` to the previous consistency statement.
  -/
  have hsampledCons :=
    sampledDiagonalLineConsistency params strategy eps delta gamma hgood
  let A : IdxMeas (PointDiagonalLineQuestion params) (Fq params) ι :=
    fun q => (strategy.pointMeasurement
      (sampledPointFromDiagonalQuestion
        params q)).toMeasurement
  let B : IdxMeas (PointDiagonalLineQuestion params) (Fq params) ι :=
    fun q =>
      { toSubMeas := postprocess
          ((strategy.diagonalMeasurement
            q.1).toSubMeas) (fun f => f q.2)
        total_eq_one := by
          simpa [postprocess_total] using
            (strategy.diagonalMeasurement q.1).toMeasurement.total_eq_one }
  have hcons :
      ConsRel strategy.state
        (pointWithDiagonalLineDistribution params)
        (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas A))
        (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B))
        (restrictedDiagonalLinesConsistencyError params gamma) := by
    simpa [A, B, sampledPointMeasurement, sampledDiagonalLineEvaluation] using hsampledCons
  have happrox :=
    MIPStarRE.LDT.Preliminaries.simeqToApprox strategy.state
      (pointWithDiagonalLineDistribution params)
      A B (restrictedDiagonalLinesConsistencyError params gamma) hcons
  rcases happrox with ⟨happrox⟩
  exact ⟨by
    simpa [A, B, sampledPointMeasurement, sampledDiagonalLineEvaluation,
      pointDiagonalLineApproxError, restrictedDiagonalLinesConsistencyError] using happrox⟩

private lemma orderedLiftToMixedBridge
    (params : Parameters)
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (pointMeasurementProductAlongSharedLine params strategy)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductLeft params strategy))
      (pointDiagonalLineApproxError params gamma) := by
  /-
  First replacement step in the paper:
  `(A^u_a A^v_b) ⊗ I ≈ A^u_a ⊗ L^ℓ_[f(v)=b]`.
  -/
  sorry

private lemma orderedLiftToLineBridge
    (params : Parameters)
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductLeft params strategy))
      (diagonalLineProductOrdered params strategy)
      (pointDiagonalLineApproxError params gamma) := by
  /-
  Second replacement step:
  `A^u_a ⊗ L^ℓ_[f(v)=b] ≈ I ⊗ (L^ℓ_[f(v)=b] L^ℓ_[f(u)=a])`.
  -/
  sorry

private lemma diagonalLineProjectiveSwap
    (params : Parameters)
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (_hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (diagonalLineProductOrdered params strategy)
      (diagonalLineProductReversed params strategy)
      0 := by
  /-
  The middle exact equality uses projectivity of
  the diagonal-line measurement on the common
  sampled line: postprocessed outcomes from the
  same ProjMeas commute.
  -/
  constructor
  show sddErrorOp _ _ _ _ ≤ 0
  have heq : ∀ q ab,
      (diagonalLineProductOrdered params
        strategy q).outcome ab =
      (diagonalLineProductReversed params
        strategy q).outcome ab := by
    intro q ⟨a, b⟩
    simp only [diagonalLineProductOrdered,
      diagonalLineProductReversed,
      OpFamily.rightPlacedOpFamily,
      reversedProductOpFamily,
      orderedProductOpFamily,
      sampledDiagonalLineEvaluation]
    congr 1
    exact (strategy.diagonalMeasurement
      q.1).postprocess_outcome_commute
      (fun f => f q.2.2)
      (fun f => f q.2.1) b a
  have hzero : ∀ q, qSDDOp strategy.state
      (diagonalLineProductOrdered params
        strategy q)
      (diagonalLineProductReversed params
        strategy q) = 0 := by
    intro q
    unfold qSDDOp qSDDCore
    apply Finset.sum_eq_zero
    intro ab _
    rw [heq q ab, sub_self,
      Matrix.conjTranspose_zero, Matrix.zero_mul,
      ev_zero]
  simp only [sddErrorOp, hzero]
  rw [MIPStarRE.LDT.avgOver_zero]

private lemma reversedDropFromLineBridge
    (params : Parameters)
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (diagonalLineProductReversed params strategy)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
      (pointDiagonalLineApproxError params gamma) := by
  /-
  Third replacement step:
  `I ⊗ (L^ℓ_[f(u)=a] L^ℓ_[f(v)=b]) ≈ A^v_b ⊗ L^ℓ_[f(u)=a]`.
  -/
  sorry

private lemma reversedDropToPointsBridge
    (params : Parameters)
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
      (pointMeasurementProductAlongSharedLineReversed params strategy)
      (pointDiagonalLineApproxError params gamma) := by
  /-
  Final replacement step:
  `A^v_b ⊗ L^ℓ_[f(u)=a] ≈ (A^v_b A^u_a) ⊗ I`.
  -/
  sorry

/-- `thm:commutativity-points`. -/
theorem commutativityPoints
    (params : Parameters)
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (uniformDistribution (PointPairQuestion params))
      (pointMeasurementProductLeft params strategy)
      (pointMeasurementProductRight params strategy)
      (commutativityPointsError params gamma) := by
  have hsampledCons :=
    sampledDiagonalLineConsistency params strategy eps delta gamma hgood
  have hsampledApprox :=
    sampledDiagonalLineApproximation params strategy eps delta gamma hgood
  have horderedMixed :=
    orderedLiftToMixedBridge params strategy eps delta gamma hgood
  have horderedLine :=
    orderedLiftToLineBridge params strategy eps delta gamma hgood
  have hswap :=
    diagonalLineProjectiveSwap params strategy eps delta gamma hgood
  have hreversedLine :=
    reversedDropFromLineBridge params strategy eps delta gamma hgood
  have hreversedPoints :=
    reversedDropToPointsBridge params strategy eps delta gamma hgood
  /-
  This is the final triangle-inequality assembly of the four
  `≈_{2γm}` steps plus the exact projective swap.
  -/
  sorry

end MIPStarRE.LDT.CommutativityPoints
