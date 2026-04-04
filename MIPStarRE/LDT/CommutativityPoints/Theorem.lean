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

/-! ### Infrastructure: ProjMeas orthogonality and commutativity -/

/-- Distinct outcomes of a projective measurement are orthogonal. -/
private lemma projMeas_outcome_orthogonal
    {α : Type*} [Fintype α]
    (P : ProjMeas α ι) (a b : α) (hab : a ≠ b) :
    P.outcome a * P.outcome b = 0 := by
  classical
  set Pa := P.outcome a
  set Pb := P.outcome b
  have hPa_herm : Paᴴ = Pa := P.outcome_hermitian a
  have hPb_herm : Pbᴴ = Pb := P.outcome_hermitian b
  have hPb_le : Pb ≤ 1 - Pa := by
    have hsum : Pa + Pb ≤ ∑ i, P.outcome i := by
      calc Pa + Pb
          = ∑ i ∈ ({a, b} : Finset α),
              P.outcome i := by
              simp [Pa, Pb, hab]
        _ ≤ ∑ i, P.outcome i :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.subset_univ _)
                (fun i _ _ =>
                  P.toMeasurement.outcome_pos i)
    rw [P.toMeasurement.sum_eq_total,
      P.total_eq_one] at hsum
    calc Pb = Pa + Pb - Pa := by abel
      _ ≤ 1 - Pa := by
          exact sub_le_sub_right hsum Pa
  have hPaPbPa_nonneg : 0 ≤ Pa * Pb * Pa :=
    MIPStarRE.Quantum.sandwich_nonneg
      (P.toMeasurement.outcome_pos b) hPa_herm
  have hPa_idem : Pa * (1 - Pa) * Pa = 0 := by
    calc Pa * (1 - Pa) * Pa
        = (Pa * 1 - Pa * Pa) * Pa := by
          rw [mul_sub]
      _ = 0 := by simp [Pa, P.proj a]
  have hPaPbPa_eq_zero : Pa * Pb * Pa = 0 := by
    apply le_antisymm
    · calc Pa * Pb * Pa
          ≤ Pa * (1 - Pa) * Pa :=
            MIPStarRE.Quantum.sandwich_mono
              hPa_herm hPb_le
        _ = 0 := hPa_idem
    · exact hPaPbPa_nonneg
  have hPbPa_eq_zero : Pb * Pa = 0 := by
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    calc (Pb * Pa)ᴴ * (Pb * Pa)
        = (Paᴴ * Pbᴴ) * (Pb * Pa) := by
          simp [Matrix.conjTranspose_mul]
      _ = Pa * (Pb * Pb) * Pa := by
          simp [hPa_herm, hPb_herm, mul_assoc]
      _ = Pa * Pb * Pa := by
          simp [Pb, P.proj b]
      _ = 0 := hPaPbPa_eq_zero
  calc Pa * Pb
      = (Pb * Pa)ᴴ := by
        simp [Matrix.conjTranspose_mul,
          hPa_herm, hPb_herm]
    _ = 0 := by rw [hPbPa_eq_zero]; simp

/-- Any two outcomes of a ProjMeas commute. -/
private lemma projMeas_outcome_commute
    {α : Type*} [Fintype α]
    (P : ProjMeas α ι) (a b : α) :
    P.outcome a * P.outcome b =
      P.outcome b * P.outcome a := by
  classical
  by_cases hab : a = b
  · subst hab; rfl
  · rw [projMeas_outcome_orthogonal P a b hab,
        projMeas_outcome_orthogonal P b a
          (Ne.symm hab)]

/-- Postprocessed outcomes from the same ProjMeas commute. -/
private lemma postprocess_projMeas_commute
    {α β γ : Type*} [Fintype α]
    [Fintype β]
    [Fintype γ]
    (P : ProjMeas α ι) (f : α → β) (g : α → γ)
    (b : β) (c : γ) :
    (postprocess P.toSubMeas f).outcome b *
      (postprocess P.toSubMeas g).outcome c =
    (postprocess P.toSubMeas g).outcome c *
      (postprocess P.toSubMeas f).outcome b := by
  classical
  simp only [postprocess]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun y _ => ?_
  exact projMeas_outcome_commute P y x

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

/-- Output package for `thm:commutativity-points`.

The strategy state is bipartite (`QuantumState (ι × ι)`).  Alice's local
measurements are lifted to the left tensor factor (`liftLeft`), while
Bob's diagonal-line evaluations are lifted to the right tensor factor
(`liftRight`). -/
structure CommutativityPointsStatement (params : Parameters)
    (strategy : SymStrat params ι)
    (_eps _delta gamma : Error) : Prop where
  sampledDiagonalLineConsistency :
    ConsRel strategy.state
      (pointWithDiagonalLineDistribution params)
      (IdxSubMeas.liftLeft (sampledPointMeasurement params strategy))
      (IdxSubMeas.liftRight (sampledDiagonalLineEvaluation params strategy))
      (restrictedDiagonalLinesConsistencyError params gamma)
  sampledDiagonalLineApproximation :
    SDDRel strategy.state
      (pointWithDiagonalLineDistribution params)
      (IdxSubMeas.liftLeft (sampledPointMeasurement params strategy))
      (IdxSubMeas.liftRight (sampledDiagonalLineEvaluation params strategy))
      (pointDiagonalLineApproxError params gamma)
  orderedLiftToMixedBridge :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (pointMeasurementProductAlongSharedLine params strategy)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductLeft params strategy))
      (pointDiagonalLineApproxError params gamma)
  orderedLiftToLineBridge :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductLeft params strategy))
      (diagonalLineProductOrdered params strategy)
      (pointDiagonalLineApproxError params gamma)
  diagonalLineProjectiveSwap :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (diagonalLineProductOrdered params strategy)
      (diagonalLineProductReversed params strategy)
      0
  reversedDropFromLineBridge :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (diagonalLineProductReversed params strategy)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
      (pointDiagonalLineApproxError params gamma)
  reversedDropToPointsBridge :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
      (pointMeasurementProductAlongSharedLineReversed params strategy)
      (pointDiagonalLineApproxError params gamma)
  pointwiseCommutation :
    SDDOpRel strategy.state
      (uniformDistribution (PointPairQuestion params))
      (pointMeasurementProductLeft params strategy)
      (pointMeasurementProductRight params strategy)
      (commutativityPointsError params gamma)

/-- `thm:commutativity-points`. -/
theorem commutativityPoints
    (params : Parameters)
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    CommutativityPointsStatement params strategy eps delta gamma := by
  have hsampledCons :
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
  refine
    { sampledDiagonalLineConsistency := hsampledCons
      sampledDiagonalLineApproximation := by
        /-
        Apply `prop:simeq-to-approx` to the previous consistency statement.
        -/
        let A : IdxMeas (PointDiagonalLineQuestion params) (Fq params) ι :=
          fun q => (strategy.pointMeasurement -- nolint: longLine
            (sampledPointFromDiagonalQuestion params q)).toMeasurement
        let B : IdxMeas (PointDiagonalLineQuestion params) (Fq params) ι :=
          fun q =>
            { toSubMeas := postprocess -- nolint: longLine
                ((strategy.diagonalMeasurement q.1).toSubMeas) (fun f => f q.2)
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
      orderedLiftToMixedBridge := by
        /-
        First replacement step in the paper:
        `(A^u_a A^v_b) ⊗ I ≈ A^u_a ⊗ L^ℓ_[f(v)=b]`.
        -/
        sorry
      orderedLiftToLineBridge := by
        /-
        Second replacement step:
        `A^u_a ⊗ L^ℓ_[f(v)=b] ≈ I ⊗ (L^ℓ_[f(v)=b] L^ℓ_[f(u)=a])`.
        -/
        sorry
      diagonalLineProjectiveSwap := by
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
          exact postprocess_projMeas_commute
            (strategy.diagonalMeasurement q.1)
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
      reversedDropFromLineBridge := by
        /-
        Third replacement step:
        `I ⊗ (L^ℓ_[f(u)=a] L^ℓ_[f(v)=b]) ≈ A^v_b ⊗ L^ℓ_[f(u)=a]`.
        -/
        sorry
      reversedDropToPointsBridge := by
        /-
        Final replacement step:
        `A^v_b ⊗ L^ℓ_[f(u)=a] ≈ (A^v_b A^u_a) ⊗ I`.
        -/
        sorry
      pointwiseCommutation := by
        /-
        This is the final triangle-inequality assembly of the four
        `≈_{2γm}` steps plus the exact projective swap.
        -/
        sorry }

end MIPStarRE.LDT.CommutativityPoints
