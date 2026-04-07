import MIPStarRE.LDT.CommutativityPoints.Defs
import MIPStarRE.LDT.Preliminaries.Theorems

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

private def pointDiagonalLineQuestionEquiv (params : Parameters)
    [FieldModel params.q] :
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
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    ConsRel strategy.state
      (pointWithDiagonalLineDistribution params)
      (sampledPointMeasurement params strategy)
      (sampledDiagonalLineEvaluation params strategy)
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
  have hrewritePlaced :
      consError strategy.state
        (pointWithDiagonalLineDistribution params)
        (fun q => leftPlacedSubMeas (sampledPointMeasurement params strategy q))
        (fun q => rightPlacedSubMeas (sampledDiagonalLineEvaluation params strategy q)) =
      consError strategy.state
        (uniformDistribution (DiagonalTestSample params))
        (IdxSubMeas.liftLeft (diagonalPointAnswerFamily strategy))
        (IdxSubMeas.liftRight (diagonalLineAnswerFamily strategy)) := by
    simpa [IdxSubMeas.liftLeft, IdxSubMeas.liftRight] using hrewrite
  have hdiagonalLineTest :
      consError strategy.state
        (uniformDistribution (DiagonalTestSample params))
        (IdxSubMeas.liftLeft (diagonalPointAnswerFamily strategy))
        (IdxSubMeas.liftRight (diagonalLineAnswerFamily strategy)) ≤ gamma := by
    simpa [SymStrat.diagonalFailureProbability, bipartiteConsError_eq_consError_placed,
      IdxSubMeas.liftLeft, IdxSubMeas.liftRight] using hgood.diagonalLineTest
  constructor
  rw [bipartiteConsError_eq_consError_placed]
  rw [hrewritePlaced]
  have hγ : 0 ≤ gamma := by
    exact le_trans
      (consError_nonneg strategy.state
        (uniformDistribution (DiagonalTestSample params))
        (IdxSubMeas.liftLeft (diagonalPointAnswerFamily strategy))
        (IdxSubMeas.liftRight (diagonalLineAnswerFamily strategy)))
      hdiagonalLineTest
  have hm : (1 : Error) ≤ params.m := by
    exact_mod_cast params.hm
  calc
    consError strategy.state
        (uniformDistribution (DiagonalTestSample params))
        (IdxSubMeas.liftLeft (diagonalPointAnswerFamily strategy))
        (IdxSubMeas.liftRight (diagonalLineAnswerFamily strategy))
      ≤ gamma := hdiagonalLineTest
    _ ≤ gamma * (params.m : Error) := by nlinarith

private lemma sampledDiagonalLineApproximation
    (params : Parameters)
    [FieldModel params.q]
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
        (IdxMeas.toIdxSubMeas A)
        (IdxMeas.toIdxSubMeas B)
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

private lemma sddOpRel_symm
    {Question Outcome : Type*}
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome ι) (δ : Error) :
    SDDOpRel ψ 𝒟 A B δ →
      SDDOpRel ψ 𝒟 B A δ := by
  intro ⟨h⟩
  constructor
  simpa [sddErrorOp, qSDDOp_symm] using h

private lemma qSDDOp_reindex
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

private lemma sddOpRel_reindex
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

private lemma sddOpRel_congr_outcome
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

private lemma subMeas_sum_adjoint_mul_le_one
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

private lemma liftLeft_mul_leftPlaced_outcome
    {α β : Type*}
    [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι)
    (a : α) (b : β) :
    (A.liftLeft).outcome a * (OpFamily.leftPlacedOpFamily B.toOpFamily).outcome b =
      leftTensor (A.outcome a * B.outcome b) := by
  simp [SubMeas.liftLeft, OpFamily.leftPlacedOpFamily, SubMeas.toOpFamily,
    leftTensor_mul_leftTensor]

private lemma liftLeft_mul_rightPlaced_outcome
    {α β : Type*}
    [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι)
    (a : α) (b : β) :
    (A.liftLeft).outcome a * (OpFamily.rightPlacedOpFamily B.toOpFamily).outcome b =
      opTensor (A.outcome a) (B.outcome b) := by
  simp [SubMeas.liftLeft, OpFamily.rightPlacedOpFamily, SubMeas.toOpFamily,
    leftTensor_mul_rightTensor_eq_opTensor]

private lemma liftRight_mul_leftPlaced_outcome
    {α β : Type*}
    [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι)
    (a : α) (b : β) :
    (A.liftRight).outcome a * (OpFamily.leftPlacedOpFamily B.toOpFamily).outcome b =
      opTensor (B.outcome b) (A.outcome a) := by
  simp [SubMeas.liftRight, OpFamily.leftPlacedOpFamily, SubMeas.toOpFamily,
    rightTensor_mul_leftTensor_eq_opTensor]

private lemma liftRight_mul_rightPlaced_outcome
    {α β : Type*}
    [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι)
    (a : α) (b : β) :
    (A.liftRight).outcome a * (OpFamily.rightPlacedOpFamily B.toOpFamily).outcome b =
      rightTensor (A.outcome a * B.outcome b) := by
  simp [SubMeas.liftRight, OpFamily.rightPlacedOpFamily, SubMeas.toOpFamily,
    rightTensor_mul_rightTensor]

private lemma avgOver_uniform_prod_ignore_left
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (f : β → Error) :
    avgOver (uniformDistribution (α × β)) (fun ab => f ab.2) =
      avgOver (uniformDistribution β) f := by
  have hα : ((Fintype.card α : ℕ) : Error) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hβ : ((Fintype.card β : ℕ) : Error) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc
    avgOver (uniformDistribution (α × β)) (fun ab => f ab.2)
      = (1 / (Fintype.card (α × β) : Error)) * ∑ ab : α × β, f ab.2 := by
          simp [avgOver, uniformDistribution, Finset.mul_sum]
    _ = (1 / ((Fintype.card α : Error) * (Fintype.card β : Error))) *
          ∑ a : α, ∑ b : β, f b := by
          rw [Fintype.card_prod]
          simpa using
            (Fintype.sum_prod_type' (f := fun (_a : α) (b : β) => f b))
    _ = (1 / ((Fintype.card α : Error) * (Fintype.card β : Error))) *
          ((Fintype.card α : Error) * ∑ b : β, f b) := by
          congr 1
          simp
    _ = (1 / (Fintype.card β : Error)) * ∑ b : β, f b := by
          field_simp [hα, hβ]
    _ = avgOver (uniformDistribution β) f := by
          simp [avgOver, uniformDistribution, Finset.mul_sum]

private lemma avgOver_uniform_prod_ignore_right
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (f : α → Error) :
    avgOver (uniformDistribution (α × β)) (fun ab => f ab.1) =
      avgOver (uniformDistribution α) f := by
  have hα : ((Fintype.card α : ℕ) : Error) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hβ : ((Fintype.card β : ℕ) : Error) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc
    avgOver (uniformDistribution (α × β)) (fun ab => f ab.1)
      = (1 / (Fintype.card (α × β) : Error)) * ∑ ab : α × β, f ab.1 := by
          simp [avgOver, uniformDistribution, Finset.mul_sum]
    _ = (1 / ((Fintype.card α : Error) * (Fintype.card β : Error))) *
          ∑ a : α, ∑ b : β, f a := by
          rw [Fintype.card_prod]
          simpa using
            (Fintype.sum_prod_type' (f := fun (a : α) (_b : β) => f a))
    _ = (1 / ((Fintype.card α : Error) * (Fintype.card β : Error))) *
          ((Fintype.card β : Error) * ∑ a : α, f a) := by
          congr 1
          simpa [Finset.mul_sum]
    _ = (1 / (Fintype.card α : Error)) * ∑ a : α, f a := by
          field_simp [hα, hβ]
     _ = avgOver (uniformDistribution α) f := by
           simp [avgOver, uniformDistribution, Finset.mul_sum]

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
        simp [sharedDiagonalLineQuestionOfPointPair, DiagonalLine.pointAt,
          addPoint, smulPoint, addCoord, subCoord, mulCoord]
        rw [← encode_decodeScalar (base i)]
        congr 1
        ring_nf
        simpa using (decode_encodeScalar (params := params) (decodeScalar (base i)))
      · funext i
        simp [sharedDiagonalLineQuestionOfPointPair, DiagonalLine.pointAt,
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

private lemma avgOver_pointPairSharedDiagonalLine_sampled_pair
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
          exact avgOver_uniform_prod_ignore_right f

private lemma pointMeasurementProductAlongSharedLine_outcome
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
    OpFamily.leftPlacedOpFamily, SubMeas.toOpFamily, leftTensor_mul_leftTensor]

private lemma pointMeasurementProductAlongSharedLineReversed_outcome
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
    OpFamily.leftPlacedOpFamily, SubMeas.toOpFamily, leftTensor_mul_leftTensor]

private lemma pointDiagonalLineMixedProductLeft_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductLeft params strategy) q).outcome (a, b) =
      opTensor
        ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a)
        ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) := by
  simp [pointDiagonalLineMixedProductLeft, tensorProductSubMeas,
    sampledDiagonalLineEvaluation, IdxSubMeas.toIdxOpFamily, SubMeas.toOpFamily,
    leftTensor_mul_rightTensor_eq_opTensor]

private lemma pointDiagonalLineMixedProductRight_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy) q).outcome (a, b) =
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
    simpa [and_comm]
  rw [hfilter]
  simp

private lemma diagonalLineProductOrdered_outcome
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
    OpFamily.rightPlacedOpFamily, reversedProductOpFamily, SubMeas.toOpFamily,
    rightTensor_mul_rightTensor]

private lemma diagonalLineProductReversed_outcome
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
    OpFamily.rightPlacedOpFamily, orderedProductOpFamily, SubMeas.toOpFamily,
    rightTensor_mul_rightTensor]

private lemma sampledDiagonalLineApproximation_ignore_first
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
  rcases sampledDiagonalLineApproximation params strategy eps delta gamma hgood with ⟨happrox⟩
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
            simp [qSDDOp, qSDD, qSDDCore, IdxSubMeas.liftLeft, IdxSubMeas.liftRight,
              OpFamily.leftPlacedOpFamily, OpFamily.rightPlacedOpFamily, sampledPointMeasurement,
              sampledPointFromDiagonalQuestion, SubMeas.liftLeft, SubMeas.liftRight,
              SubMeas.toOpFamily]
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

private lemma sampledDiagonalLineApproximation_ignore_second
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
  rcases sampledDiagonalLineApproximation params strategy eps delta gamma hgood with ⟨happrox⟩
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
            simp [qSDDOp, qSDD, qSDDCore, IdxSubMeas.liftLeft, IdxSubMeas.liftRight,
              OpFamily.leftPlacedOpFamily, OpFamily.rightPlacedOpFamily, sampledPointMeasurement,
              sampledPointFromDiagonalQuestion, SubMeas.liftLeft, SubMeas.liftRight,
              SubMeas.toOpFamily]
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

private lemma orderedLiftToMixedBridge
    (params : Parameters)
    [FieldModel params.q]
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
  let e : (Fq params × Fq params) ≃ (Fq params × Fq params) :=
    { toFun := Prod.swap
      invFun := Prod.swap
      left_inv := by intro ab; cases ab; rfl
      right_inv := by intro ab; cases ab; rfl }
  let Araw : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params) (ι × ι) :=
    fun q =>
      ({ outcome := fun ab : Fq params × Fq params =>
           (((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas).liftLeft).outcome ab.2 *
             (OpFamily.leftPlacedOpFamily (ιB := ι)
               ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas)).outcome ab.1
         total := ∑ ab : Fq params × Fq params,
           (((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas).liftLeft).outcome ab.2 *
             (OpFamily.leftPlacedOpFamily (ιB := ι)
               ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas)).outcome ab.1
       } : OpFamily (Fq params × Fq params) (ι × ι))
  let Braw : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params) (ι × ι) :=
    fun q =>
      ({ outcome := fun ab : Fq params × Fq params =>
           (((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas).liftLeft).outcome ab.2 *
             (OpFamily.rightPlacedOpFamily (ιA := ι)
               (SubMeas.toOpFamily
                 (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)))).outcome ab.1
         total := ∑ ab : Fq params × Fq params,
           (((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas).liftLeft).outcome ab.2 *
             (OpFamily.rightPlacedOpFamily (ιA := ι)
               (SubMeas.toOpFamily
                 (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)))).outcome ab.1
       } : OpFamily (Fq params × Fq params) (ι × ι))
  let hbase :=
    sampledDiagonalLineApproximation_ignore_first params strategy eps delta gamma hgood
  let hcab :=
    MIPStarRE.LDT.Preliminaries.cabApproxDelta_raw
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
      (fun q _b a =>
        (((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas).liftLeft).outcome a)
      (pointDiagonalLineApproxError params gamma)
      hbase
      (by
        intro q b
        exact subMeas_sum_adjoint_mul_le_one
          (((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas).liftLeft))
  have hreindexed :=
    sddOpRel_reindex e strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      Araw
      Braw
      (pointDiagonalLineApproxError params gamma)
      hcab
  let Astep : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params) (ι × ι) :=
    fun q =>
      ({ outcome := fun ab : Fq params × Fq params => (Araw q).outcome (e.symm ab)
         total := (Araw q).total
       } : OpFamily (Fq params × Fq params) (ι × ι))
  let Bstep : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params) (ι × ι) :=
    fun q =>
      ({ outcome := fun ab : Fq params × Fq params => (Braw q).outcome (e.symm ab)
         total := (Braw q).total
       } : OpFamily (Fq params × Fq params) (ι × ι))
  exact sddOpRel_congr_outcome strategy.state
    (pointPairSharedDiagonalLineDistribution params)
    Astep Bstep
    (pointMeasurementProductAlongSharedLine params strategy)
    (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductLeft params strategy))
    (pointDiagonalLineApproxError params gamma)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Astep q).outcome (a, b)
          = leftTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a *
                (strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b) := by
                  simpa [Astep, Araw, e] using
                    liftLeft_mul_leftPlaced_outcome
                      ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas)
                      ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas)
                      a b
        _ = (pointMeasurementProductAlongSharedLine params strategy q).outcome (a, b) := by
              symm
              exact pointMeasurementProductAlongSharedLine_outcome params strategy q a b)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Bstep q).outcome (a, b)
          = opTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a)
              ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) := by
                  simpa [Bstep, Braw, e] using
                    liftLeft_mul_rightPlaced_outcome
                      ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas)
                      (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))
                      a b
        _ = ((IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductLeft params strategy)) q).outcome
              (a, b) := by
              symm
              exact pointDiagonalLineMixedProductLeft_outcome params strategy q a b)
    hreindexed

private lemma orderedLiftToLineBridge
    (params : Parameters)
    [FieldModel params.q]
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
  let Araw : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params) (ι × ι) :=
    fun q =>
      ({ outcome := fun ab : Fq params × Fq params =>
           opTensor ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome ab.1)
             ((postprocess (strategy.diagonalMeasurement q.1).toSubMeas fun f => f q.2.2).outcome ab.2)
         total := ∑ ab : Fq params × Fq params,
           opTensor ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome ab.1)
             ((postprocess (strategy.diagonalMeasurement q.1).toSubMeas fun f => f q.2.2).outcome ab.2)
       } : OpFamily (Fq params × Fq params) (ι × ι))
  let Braw : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params) (ι × ι) :=
    fun q =>
      ({ outcome := fun ab : Fq params × Fq params =>
           rightTensor
             ((postprocess (strategy.diagonalMeasurement q.1).toSubMeas fun f => f q.2.2).outcome ab.2 *
               (postprocess (strategy.diagonalMeasurement q.1).toSubMeas fun f => f q.2.1).outcome ab.1)
         total := ∑ ab : Fq params × Fq params,
           rightTensor
             ((postprocess (strategy.diagonalMeasurement q.1).toSubMeas fun f => f q.2.2).outcome ab.2 *
               (postprocess (strategy.diagonalMeasurement q.1).toSubMeas fun f => f q.2.1).outcome ab.1)
       } : OpFamily (Fq params × Fq params) (ι × ι))
  let hbase :=
    sampledDiagonalLineApproximation_ignore_second params strategy eps delta gamma hgood
  have hcab :=
    MIPStarRE.LDT.Preliminaries.cabApproxDelta_raw
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      (fun q _a b =>
        ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).liftRight).outcome b)
      (pointDiagonalLineApproxError params gamma)
      hbase
      (by
        intro q a
        exact subMeas_sum_adjoint_mul_le_one
          ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).liftRight))
  let Astep : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params) (ι × ι) :=
    fun q =>
      ({ outcome := fun ab : Fq params × Fq params =>
           ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).liftRight).outcome ab.2 *
             (OpFamily.leftPlacedOpFamily (ιB := ι)
               ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas)).outcome ab.1
         total := ∑ ab : Fq params × Fq params,
           ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).liftRight).outcome ab.2 *
             (OpFamily.leftPlacedOpFamily (ιB := ι)
               ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas)).outcome ab.1
       } : OpFamily (Fq params × Fq params) (ι × ι))
  let Bstep : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params) (ι × ι) :=
    fun q =>
      ({ outcome := fun ab : Fq params × Fq params =>
           ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).liftRight).outcome ab.2 *
             (OpFamily.rightPlacedOpFamily (ιA := ι)
               (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)))).outcome ab.1
         total := ∑ ab : Fq params × Fq params,
           ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).liftRight).outcome ab.2 *
             (OpFamily.rightPlacedOpFamily (ιA := ι)
               (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)))).outcome ab.1
       } : OpFamily (Fq params × Fq params) (ι × ι))
  exact sddOpRel_congr_outcome strategy.state
    (pointPairSharedDiagonalLineDistribution params)
    Astep Bstep
    (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductLeft params strategy))
    (diagonalLineProductOrdered params strategy)
    (pointDiagonalLineApproxError params gamma)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Astep q).outcome (a, b)
          = opTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a)
              ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) := by
                  simpa [Astep] using
                    liftRight_mul_leftPlaced_outcome
                      (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))
                      ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas)
                      b a
        _ = ((IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductLeft params strategy)) q).outcome
              (a, b) := by
              symm
              exact pointDiagonalLineMixedProductLeft_outcome params strategy q a b)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Bstep q).outcome (a, b)
          = rightTensor
              ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b *
                (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) := by
                  simpa [Bstep] using
                    liftRight_mul_rightPlaced_outcome
                      (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))
                      (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                      b a
        _ = (diagonalLineProductOrdered params strategy q).outcome (a, b) := by
              symm
              exact diagonalLineProductOrdered_outcome params strategy q a b)
    hcab

private lemma diagonalLineProjectiveSwap
    (params : Parameters)
    [FieldModel params.q]
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

private lemma diagonalLineProduct_outcome_swap
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) :
    ∀ q ab,
      (diagonalLineProductOrdered params strategy q).outcome ab =
        (diagonalLineProductReversed params strategy q).outcome ab := by
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

set_option maxHeartbeats 1000000 in
-- Reindexing and outcome-congruence for this bridge create a large elaboration problem.
private lemma reversedDropFromLineBridge
    (params : Parameters)
    [FieldModel params.q]
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
  let e : (Fq params × Fq params) ≃ (Fq params × Fq params) :=
    { toFun := Prod.swap
      invFun := Prod.swap
      left_inv := by intro ab; cases ab; rfl
      right_inv := by intro ab; cases ab; rfl }
  let Araw : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params) (ι × ι) :=
    fun q =>
      ({ outcome := fun ab : Fq params × Fq params =>
           ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).liftRight).outcome ab.2 *
             (OpFamily.rightPlacedOpFamily (ιA := ι)
               (SubMeas.toOpFamily
                 (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)))).outcome ab.1
         total := ∑ ab : Fq params × Fq params,
           ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).liftRight).outcome ab.2 *
             (OpFamily.rightPlacedOpFamily (ιA := ι)
               (SubMeas.toOpFamily
                 (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)))).outcome ab.1
       } : OpFamily (Fq params × Fq params) (ι × ι))
  let Braw : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params) (ι × ι) :=
    fun q =>
      ({ outcome := fun ab : Fq params × Fq params =>
           ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).liftRight).outcome ab.2 *
             (OpFamily.leftPlacedOpFamily (ιB := ι)
               ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas)).outcome ab.1
         total := ∑ ab : Fq params × Fq params,
           ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).liftRight).outcome ab.2 *
             (OpFamily.leftPlacedOpFamily (ιB := ι)
               ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas)).outcome ab.1
       } : OpFamily (Fq params × Fq params) (ι × ι))
  let hbase :=
    sddOpRel_symm strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
      (pointDiagonalLineApproxError params gamma)
      (sampledDiagonalLineApproximation_ignore_first params strategy eps delta gamma hgood)
  let hcab :=
    MIPStarRE.LDT.Preliminaries.cabApproxDelta_raw
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily
            (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas))
      (fun q _b a =>
        ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).liftRight).outcome a)
      (pointDiagonalLineApproxError params gamma)
      hbase
      (by
        intro q b
        exact subMeas_sum_adjoint_mul_le_one
          ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).liftRight))
  have hreindexed :=
    sddOpRel_reindex e strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      Araw
      Braw
      (pointDiagonalLineApproxError params gamma)
      hcab
  let Astep : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params) (ι × ι) :=
    fun q =>
      ({ outcome := fun ab : Fq params × Fq params => (Araw q).outcome (e.symm ab)
         total := (Araw q).total
       } : OpFamily (Fq params × Fq params) (ι × ι))
  let Bstep : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params) (ι × ι) :=
    fun q =>
      ({ outcome := fun ab : Fq params × Fq params => (Braw q).outcome (e.symm ab)
         total := (Braw q).total
       } : OpFamily (Fq params × Fq params) (ι × ι))
  exact sddOpRel_congr_outcome strategy.state
    (pointPairSharedDiagonalLineDistribution params)
    Astep Bstep
    (diagonalLineProductReversed params strategy)
    (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
    (pointDiagonalLineApproxError params gamma)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Astep q).outcome (a, b)
          = rightTensor
              ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a *
                (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) := by
                  simpa [Astep, Araw, e] using
                    liftRight_mul_rightPlaced_outcome
                      (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                      (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))
                      a b
        _ = (diagonalLineProductReversed params strategy q).outcome (a, b) := by
              symm
              exact diagonalLineProductReversed_outcome params strategy q a b)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Bstep q).outcome (a, b)
          = opTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b)
              ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) := by
                  simpa [Bstep, Braw, e] using
                    liftRight_mul_leftPlaced_outcome
                      (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                      ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas)
                      a b
        _ = ((IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy)) q).outcome
              (a, b) := by
              symm
              exact pointDiagonalLineMixedProductRight_outcome params strategy q a b)
    hreindexed

private lemma orderedDropFromLineBridge
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (diagonalLineProductOrdered params strategy)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
      (pointDiagonalLineApproxError params gamma) := by
  exact sddOpRel_congr_outcome strategy.state
    (pointPairSharedDiagonalLineDistribution params)
    (diagonalLineProductReversed params strategy)
    (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
    (diagonalLineProductOrdered params strategy)
    (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
    (pointDiagonalLineApproxError params gamma)
    (by
      intro q ab
      symm
      exact diagonalLineProduct_outcome_swap params strategy q ab)
    (by intro q ab; rfl)
    (reversedDropFromLineBridge params strategy eps delta gamma hgood)

private lemma reversedDropToPointsBridge
    (params : Parameters)
    [FieldModel params.q]
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
  let Astep : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params) (ι × ι) :=
    fun q =>
      ({ outcome := fun ab : Fq params × Fq params =>
           (((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas).liftLeft).outcome ab.2 *
             (OpFamily.rightPlacedOpFamily (ιA := ι)
               (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)))).outcome ab.1
         ,
          total := ∑ ab : Fq params × Fq params,
            (((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas).liftLeft).outcome ab.2 *
              (OpFamily.rightPlacedOpFamily (ιA := ι)
                (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)))).outcome ab.1
        } : OpFamily (Fq params × Fq params) (ι × ι))
  let Bstep : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params) (ι × ι) :=
    fun q =>
      ({ outcome := fun ab : Fq params × Fq params =>
           (((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas).liftLeft).outcome ab.2 *
             (OpFamily.leftPlacedOpFamily (ιB := ι)
               ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas)).outcome ab.1
         ,
          total := ∑ ab : Fq params × Fq params,
            (((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas).liftLeft).outcome ab.2 *
              (OpFamily.leftPlacedOpFamily (ιB := ι)
                ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas)).outcome ab.1
        } : OpFamily (Fq params × Fq params) (ι × ι))
  let hbase :=
    sddOpRel_symm strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      (pointDiagonalLineApproxError params gamma)
      (sampledDiagonalLineApproximation_ignore_second params strategy eps delta gamma hgood)
  have hcab :=
    MIPStarRE.LDT.Preliminaries.cabApproxDelta_raw
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
      (fun q _a b =>
        (((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas).liftLeft).outcome b)
      (pointDiagonalLineApproxError params gamma)
      hbase
      (by
        intro q a
        exact subMeas_sum_adjoint_mul_le_one
          (((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas).liftLeft))
  exact sddOpRel_congr_outcome strategy.state
    (pointPairSharedDiagonalLineDistribution params)
    Astep Bstep
    (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
    (pointMeasurementProductAlongSharedLineReversed params strategy)
    (pointDiagonalLineApproxError params gamma)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Astep q).outcome (a, b)
          = opTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b)
              ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) := by
                  simpa [Astep] using
                    liftLeft_mul_rightPlaced_outcome
                      ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas)
                      (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                      b a
        _ = ((IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy)) q).outcome
              (a, b) := by
              symm
              exact pointDiagonalLineMixedProductRight_outcome params strategy q a b)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Bstep q).outcome (a, b)
          = leftTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b *
                (strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a) := by
                  simpa [Bstep] using
                    liftLeft_mul_leftPlaced_outcome
                      ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas)
                      ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas)
                      b a
        _ = (pointMeasurementProductAlongSharedLineReversed params strategy q).outcome (a, b) := by
              symm
              exact pointMeasurementProductAlongSharedLineReversed_outcome params strategy q a b)
    hcab

/-- `thm:commutativity-points`. -/
theorem commutativityPoints
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (uniformDistribution (PointPairQuestion params))
      (pointMeasurementProductLeft params strategy)
      (pointMeasurementProductRight params strategy)
      (commutativityPointsError params gamma) := by
<<<<<<< feat/sddoprel-infrastructure
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
  have hγ : 0 ≤ gamma := by
    exact le_trans
      (consError_nonneg strategy.state
        (uniformDistribution (DiagonalTestSample params))
        (IdxSubMeas.liftLeft (diagonalPointAnswerFamily strategy))
        (IdxSubMeas.liftRight (diagonalLineAnswerFamily strategy)))
      hgood.diagonalLineTest
  have h45 :
      SDDOpRel strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (diagonalLineProductReversed params strategy)
        (pointMeasurementProductAlongSharedLineReversed params strategy)
        (2 * (pointDiagonalLineApproxError params gamma +
          pointDiagonalLineApproxError params gamma)) := by
    exact MIPStarRE.LDT.Preliminaries.sddOpRel_triangle
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (diagonalLineProductReversed params strategy)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
      (pointMeasurementProductAlongSharedLineReversed params strategy)
      (pointDiagonalLineApproxError params gamma)
      (pointDiagonalLineApproxError params gamma)
      hreversedLine
      hreversedPoints
  have h345 :
      SDDOpRel strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (diagonalLineProductOrdered params strategy)
        (pointMeasurementProductAlongSharedLineReversed params strategy)
        (2 * (0 + 2 * (pointDiagonalLineApproxError params gamma +
          pointDiagonalLineApproxError params gamma))) := by
    exact MIPStarRE.LDT.Preliminaries.sddOpRel_triangle
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (diagonalLineProductOrdered params strategy)
      (diagonalLineProductReversed params strategy)
      (pointMeasurementProductAlongSharedLineReversed params strategy)
      0
      (2 * (pointDiagonalLineApproxError params gamma +
        pointDiagonalLineApproxError params gamma))
      hswap
      h45
  have h2345 :
      SDDOpRel strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductLeft params strategy))
        (pointMeasurementProductAlongSharedLineReversed params strategy)
        (2 * (pointDiagonalLineApproxError params gamma +
          2 * (0 + 2 * (pointDiagonalLineApproxError params gamma +
            pointDiagonalLineApproxError params gamma)))) := by
    exact MIPStarRE.LDT.Preliminaries.sddOpRel_triangle
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductLeft params strategy))
      (diagonalLineProductOrdered params strategy)
      (pointMeasurementProductAlongSharedLineReversed params strategy)
      (pointDiagonalLineApproxError params gamma)
      (2 * (0 + 2 * (pointDiagonalLineApproxError params gamma +
        pointDiagonalLineApproxError params gamma)))
      horderedLine
      h345
  have h12345 :
=======
  let δ := pointDiagonalLineApproxError params gamma
  have hleft :
      SDDOpRel strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (pointMeasurementProductAlongSharedLine params strategy)
        (diagonalLineProductOrdered params strategy)
        (2 * (δ + δ)) := by
    exact MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_triangle
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (pointMeasurementProductAlongSharedLine params strategy)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductLeft params strategy))
      (diagonalLineProductOrdered params strategy)
      δ δ
      (orderedLiftToMixedBridge params strategy eps delta gamma hgood)
      (orderedLiftToLineBridge params strategy eps delta gamma hgood)
  have hright :
      SDDOpRel strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (diagonalLineProductOrdered params strategy)
        (pointMeasurementProductAlongSharedLineReversed params strategy)
        (2 * (δ + δ)) := by
    exact MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_triangle
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (diagonalLineProductOrdered params strategy)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
      (pointMeasurementProductAlongSharedLineReversed params strategy)
      δ δ
      (orderedDropFromLineBridge params strategy eps delta gamma hgood)
      (reversedDropToPointsBridge params strategy eps delta gamma hgood)
  have hshared :
>>>>>>> main
      SDDOpRel strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (pointMeasurementProductAlongSharedLine params strategy)
        (pointMeasurementProductAlongSharedLineReversed params strategy)
<<<<<<< feat/sddoprel-infrastructure
        (2 * (pointDiagonalLineApproxError params gamma +
          2 * (pointDiagonalLineApproxError params gamma +
            2 * (0 + 2 * (pointDiagonalLineApproxError params gamma +
              pointDiagonalLineApproxError params gamma))))) := by
    exact MIPStarRE.LDT.Preliminaries.sddOpRel_triangle
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (pointMeasurementProductAlongSharedLine params strategy)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductLeft params strategy))
      (pointMeasurementProductAlongSharedLineReversed params strategy)
      (pointDiagonalLineApproxError params gamma)
      (2 * (pointDiagonalLineApproxError params gamma +
        2 * (0 + 2 * (pointDiagonalLineApproxError params gamma +
          pointDiagonalLineApproxError params gamma))))
      horderedMixed
      h2345
  have hm_nonneg : 0 ≤ (params.m : Error) := by
    positivity
  have hsharedLarge :
=======
        (2 * (2 * (δ + δ) + 2 * (δ + δ))) := by
    exact MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_triangle
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (pointMeasurementProductAlongSharedLine params strategy)
      (diagonalLineProductOrdered params strategy)
      (pointMeasurementProductAlongSharedLineReversed params strategy)
      (2 * (δ + δ)) (2 * (δ + δ))
      hleft hright
  have hshared' :
>>>>>>> main
      SDDOpRel strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (pointMeasurementProductAlongSharedLine params strategy)
        (pointMeasurementProductAlongSharedLineReversed params strategy)
<<<<<<< feat/sddoprel-infrastructure
        (76 * gamma * (params.m : Error)) := by
    have hbound :
        2 * (pointDiagonalLineApproxError params gamma +
          2 * (pointDiagonalLineApproxError params gamma +
            2 * (0 + 2 * (pointDiagonalLineApproxError params gamma +
              pointDiagonalLineApproxError params gamma))))
          ≤ 76 * gamma * (params.m : Error) := by
      simp [pointDiagonalLineApproxError, restrictedDiagonalLinesConsistencyError]
      nlinarith
    exact MIPStarRE.LDT.Preliminaries.sddOpRel_mono
=======
        (commutativityPointsError params gamma) := by
    refine MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_mono
>>>>>>> main
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (pointMeasurementProductAlongSharedLine params strategy)
      (pointMeasurementProductAlongSharedLineReversed params strategy)
<<<<<<< feat/sddoprel-infrastructure
      _
      _
      h12345
      hbound
  /-
  Two gaps remain here.

  1. The paper averages over uniform point pairs together with a uniformly
     random diagonal line containing both points, while the current
     `pointPairSharedDiagonalLineDistribution` is the uniform distribution on
     raw `(ℓ, t₁, t₂)` samples. A pushforward/marginal comparison is still
     needed to transfer `hsharedLarge` to the target point-pair average.
  2. With the current raw triangle lemma
     `δ₁, δ₂ ↦ 2 * (δ₁ + δ₂)`, the five-step chaining above yields the explicit
     bound `76 * γ * m`. Recovering the blueprint's `32 * γ * m` needs either a
     sharper composition lemma or a different bookkeeping argument.
  -/
  sorry
=======
      (2 * (2 * (δ + δ) + 2 * (δ + δ)))
      (commutativityPointsError params gamma)
      ?_ hshared
    dsimp [δ, pointDiagonalLineApproxError, restrictedDiagonalLinesConsistencyError,
      commutativityPointsError]
    ring_nf
    linarith
  rcases hshared' with ⟨hshared'⟩
  constructor
  calc
    sddErrorOp strategy.state
        (uniformDistribution (PointPairQuestion params))
        (pointMeasurementProductLeft params strategy)
        (pointMeasurementProductRight params strategy)
      = avgOver (pointPairSharedDiagonalLineDistribution params)
          (fun q =>
            qSDDOp strategy.state
              (pointMeasurementProductAlongSharedLine params strategy q)
              (pointMeasurementProductAlongSharedLineReversed params strategy q)) := by
            symm
            simpa [sddErrorOp, pointMeasurementProductAlongSharedLine,
              pointMeasurementProductAlongSharedLineReversed] using
              avgOver_pointPairSharedDiagonalLine_sampled_pair params
                (fun uv =>
                  qSDDOp strategy.state
                    (pointMeasurementProductLeft params strategy uv)
                    (pointMeasurementProductRight params strategy uv))
    _ = sddErrorOp strategy.state
          (pointPairSharedDiagonalLineDistribution params)
          (pointMeasurementProductAlongSharedLine params strategy)
          (pointMeasurementProductAlongSharedLineReversed params strategy) := by
            rfl
    _ ≤ commutativityPointsError params gamma := hshared'
>>>>>>> main

end MIPStarRE.LDT.CommutativityPoints
