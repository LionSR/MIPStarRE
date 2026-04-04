import MIPStarRE.LDT.Commutativity.Defs

/-!
Statement packaging and scaffold theorems for Section 11 commutativity.

The strategy state is bipartite (`QuantumState (ι × ι)`).  All fields use
`strategy.state` directly.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Error terms and packaged conclusions -/

/-- Operator domination, written in source order as `X ≤ Y`. -/
abbrev OperatorDominatedBy (X Y : MIPStarRE.Quantum.Op ι) : Prop :=
  X ≤ Y

/-- Displayed error term for `lem:comm-data-processed-g`. -/
noncomputable def commDataProcessedGError (params : Parameters) (gamma zeta : Error) : Error :=
  48 * (params.m : Error) *
    (Real.rpow gamma (1 / (2 : Error)) + Real.rpow zeta (1 / (2 : Error)))

/-- The first internal stability error from `lem:comm-data-processed-g`. -/
noncomputable def commDataProcessedGStabilityOneError (zeta : Error) : Error :=
  Real.rpow zeta (1 / (2 : Error))

/-- The second internal stability error from `lem:comm-data-processed-g`. -/
noncomputable def commDataProcessedGStabilityTwoError
    (params : Parameters) (gamma zeta : Error) : Error :=
  Real.rpow zeta (1 / (2 : Error)) +
    6 * Real.rpow (gamma * (((params.m + 1 : ℕ) : Error))) (1 / (2 : Error))

/-- Displayed error term for `thm:com-main`. -/
noncomputable def comMainError (params : Parameters) (gamma zeta : Error) : Error :=
  30 * (params.m : Error) *
    (Real.rpow gamma (1 / (4 : Error)) +
      Real.rpow zeta (1 / (4 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (4 : Error)))

/-- Output package for `lem:comm-data-processed-g`.

The strategy state is bipartite.  Alice-side measurements are lifted to
the left tensor factor, while Bob-side postprocessed point measurements
are lifted to the right tensor factor. -/
structure CommDataProcessedGConclusion (params : Parameters)
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) : Prop where
  postprocessedPointConsistency :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeasLeft strategy.pointMeasurement)
      (IdxSubMeas.liftRight (evaluatedPointFamily params family))
      zeta
  postprocessedSelfConsistency :
    SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamilyLeft params family)
      (evaluatedPointFamilyRight params family)
      zeta
  stabilityOne :
    SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (commDataProcessedGStabilityOneLeft params strategy family)
      (commDataProcessedGStabilityOneRight params strategy family)
      (commDataProcessedGStabilityOneError zeta)
  stabilityTwo :
    SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (commDataProcessedGStabilityTwoLeft params strategy family)
      (commDataProcessedGStabilityTwoRight params strategy family)
      (commDataProcessedGStabilityTwoError params gamma zeta)
  evaluatedSliceCommutation :
    SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedSliceProductLeft params strategy family)
      (evaluatedSliceProductRight params strategy family)
      (commDataProcessedGError params gamma zeta)

/-- Output package for `thm:com-main`. -/
structure ComMainConclusion (params : Parameters)
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) : Prop where
  evaluatedCommutation :
    CommDataProcessedGConclusion params strategy family gamma zeta
  evaluationSpecialization :
    SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedFromFullSliceProductLeft params strategy family)
      (evaluatedFromFullSliceProductRight params strategy family)
      (commDataProcessedGError params gamma zeta)
  fullSliceCommutation :
    SDDOpRel strategy.state
      (uniformDistribution (FullSliceQuestion params))
      (fullSliceProductLeft params strategy family)
      (fullSliceProductRight params strategy family)
      (comMainError params gamma zeta)

/-- Output package for `lem:normalization-condition`. -/
structure NormalizationConditionStatement {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι)
    (Q : ProjSubMeas OutcomeB ι) : Prop where
  sandwichedHermitianSquare :
    normalizationConditionAdjointSquareOperator P Q =
      normalizationConditionSquareOperator P Q
  sandwichedBoundedByIdentity :
    OperatorDominatedBy
      (normalizationConditionSquareOperator P Q)
      (normalizationConditionIdentityBound P Q)

/-! ## Scaffold theorem statements -/

/-- `lem:comm-data-processed-g`. -/
lemma commDataProcessedG
    (params : Parameters)
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : family.Bounded strategy.state zeta) :
    CommDataProcessedGConclusion params strategy family gamma zeta := by
  refine
    { postprocessedPointConsistency := ?_
      postprocessedSelfConsistency := by
        -- TODO: Derive self-consistency of the postprocessed left/right
        -- evaluated point families from `hself` (`lem:comm-data-processed-g`);
        -- blocked on the exact `evaluatedPointFamily` rewriting bridge.
        sorry
      stabilityOne := by
        -- TODO: Prove the first insertion/removal stability step for the
        -- appended `G^y` total operator (`lem:comm-data-processed-g`); blocked
        -- on `SDDOpRel` append/postprocess bridge lemmas.
        sorry
      stabilityTwo := by
        -- TODO: Prove the second insertion/removal stability step for the
        -- appended `G^x` total operator (`lem:comm-data-processed-g`); blocked
        -- on the corresponding `SDDOpRel` bridge from the evaluated slice
        -- product scaffold.
        sorry
      evaluatedSliceCommutation := by
        -- TODO: Show approximate commutation of the ordered and reversed
        -- evaluated-slice products (`lem:comm-data-processed-g`); blocked on
        -- chaining the two stability estimates with the processed-point
        -- comparison.
        sorry }
  simpa [evaluatedPointFamily] using hcons.pointConsistency

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
  classical
  simp only [OpFamily.postprocess, OpFamily.leftPlacedOpFamily,
    orderedProductOpFamily, postprocess]
  rw [leftTensor_finset_sum (ι₂ := ι)]
  congr 1
  set S := Finset.univ.filter (fun a₁ => f₁ a₁ = b₁)
  set T := Finset.univ.filter (fun a₂ => f₂ a₂ = b₂)
  trans ∑ a ∈ S ×ˢ T, A.outcome a.1 * B.outcome a.2
  · apply Finset.sum_congr
    · ext ⟨x, y⟩; simp [S, T, Prod.mk.injEq]
    · intros; rfl
  · rw [Finset.sum_product]
    simp_rw [← Finset.mul_sum]
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
  classical
  simp only [OpFamily.postprocess, OpFamily.leftPlacedOpFamily,
    reversedProductOpFamily, postprocess]
  rw [leftTensor_finset_sum (ι₂ := ι)]
  congr 1
  set S := Finset.univ.filter (fun a₁ => f₁ a₁ = b₁)
  set T := Finset.univ.filter (fun a₂ => f₂ a₂ = b₂)
  trans ∑ a ∈ S ×ˢ T, B.outcome a.2 * A.outcome a.1
  · apply Finset.sum_congr
    · ext ⟨x, y⟩; simp [S, T, Prod.mk.injEq]
    · intros; rfl
  · rw [Finset.sum_product]
    simp_rw [← Finset.sum_mul]
    rw [← Finset.mul_sum]

set_option maxHeartbeats 800000 in
-- Heavy `unfold`/`congr` chain in `evaluationSpecialization` proving
-- postprocess-of-product = product-of-postprocess via helper lemmas.
/-- `thm:com-main`. -/
theorem comMain
    (params : Parameters)
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : family.Bounded strategy.state zeta) :
    ComMainConclusion params strategy family gamma zeta := by
  let hEval :=
    commDataProcessedG params strategy eps delta gamma zeta hgood family hcons hself hbound
  refine
    { evaluatedCommutation := hEval
      evaluationSpecialization := by
        -- The evaluated-from-full-slice families equal the evaluated-slice
        -- families (postprocessing a product = product of postprocessings),
        -- so we reuse the evaluated-slice commutation from hEval.
        suffices h :
            sddErrorOp strategy.state
              (uniformDistribution (EvaluatedSliceQuestion params))
              (evaluatedFromFullSliceProductLeft params strategy family)
              (evaluatedFromFullSliceProductRight params strategy family) =
            sddErrorOp strategy.state
              (uniformDistribution (EvaluatedSliceQuestion params))
              (evaluatedSliceProductLeft params strategy family)
              (evaluatedSliceProductRight params strategy family) by
          constructor; rw [h]
          exact hEval.evaluatedSliceCommutation.squaredDistanceBound
        unfold sddErrorOp; congr 1; funext q
        unfold qSDDOp qSDDCore; congr 1; funext ⟨a, b⟩
        have hoL :
          (evaluatedFromFullSliceProductLeft
            params strategy family q).outcome (a, b) =
          (evaluatedSliceProductLeft
            params strategy family q).outcome (a, b) := by
          unfold evaluatedFromFullSliceProductLeft
          unfold evaluatedSliceProductLeft
          unfold fullSliceProductLeft leftOrderedProductOpFamily
          unfold evaluateFullSliceOutcomeAtQuestion
          unfold fullSliceQuestionOfEvaluatedSlice
          exact
            postprocess_leftPlacedOpFamily_orderedProduct_outcome
              (fullSliceFirstFactor params family
                (pointHeight params q.1, pointHeight params q.2))
              (fullSliceSecondFactor params family
                (pointHeight params q.1, pointHeight params q.2))
              (fun g => g (truncatePoint params q.1))
              (fun h => h (truncatePoint params q.2)) a b
        have hoR :
          (evaluatedFromFullSliceProductRight
            params strategy family q).outcome (a, b) =
          (evaluatedSliceProductRight
            params strategy family q).outcome (a, b) := by
          unfold evaluatedFromFullSliceProductRight
          unfold evaluatedSliceProductRight
          unfold fullSliceProductRight
          unfold evaluateFullSliceOutcomeAtQuestion
          unfold fullSliceQuestionOfEvaluatedSlice
          exact
            postprocess_leftPlacedOpFamily_reversedProduct_outcome
              (fullSliceFirstFactor params family
                (pointHeight params q.1, pointHeight params q.2))
              (fullSliceSecondFactor params family
                (pointHeight params q.1, pointHeight params q.2))
              (fun g => g (truncatePoint params q.1))
              (fun h => h (truncatePoint params q.2)) a b
        rw [hoL, hoR]
      fullSliceCommutation := by
        -- TODO: Lift evaluated-slice commutation to the full-slice statement
        -- with the displayed `comMainError` (`thm:com-main`); blocked on
        -- comparison between full-slice and evaluated families plus averaging
        -- infrastructure.
        sorry }

/-- `lem:normalization-condition`. -/
lemma normalizationCondition {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι)
    (Q : ProjSubMeas OutcomeB ι) :
    NormalizationConditionStatement P Q := by
  have hherm :
      ∀ a : OutcomeA,
        (normalizationConditionSandwichedTotalOperator P Q a)ᴴ =
          normalizationConditionSandwichedTotalOperator P Q a := by
    intro a
    exact
      (Matrix.nonneg_iff_posSemidef.mp <|
        by
          simpa [normalizationConditionSandwichedTotalOperator] using
            SubMeas.total_nonneg (normalizationConditionSandwichedTotalFamily P Q a)
      ).isHermitian.eq
  refine
    { sandwichedHermitianSquare := ?_
      sandwichedBoundedByIdentity := ?_ }
  · simp [normalizationConditionAdjointSquareOperator,
      normalizationConditionSquareOperator,
      normalizationConditionAdjointSquareFamily,
      normalizationConditionSquareFamily, hherm]
  · simpa [normalizationConditionSquareOperator, normalizationConditionIdentityBound] using
      (normalizationConditionSquareFamily P Q).total_le_one

end MIPStarRE.LDT.Commutativity
