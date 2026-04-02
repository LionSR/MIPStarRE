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

The strategy state is bipartite.  Local-register fields lift
measurements to the left tensor factor. -/
structure CommDataProcessedGConclusion (params : Parameters)
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) : Prop where
  postprocessedPointConsistency :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeasLeft strategy.pointMeasurement)
      (IdxSubMeas.liftLeft (evaluatedPointFamily params family))
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
      (IdxSubMeas.toIdxOpFamily (commDataProcessedGStabilityOneRight params strategy family))
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
        sorry
      stabilityOne := by
        sorry
      stabilityTwo := by
        sorry
      evaluatedSliceCommutation := by
        sorry }
  simpa [evaluatedPointFamily] using hcons.pointConsistency

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
        sorry
      fullSliceCommutation := by
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
    have hnonneg : 0 ≤ normalizationConditionSandwichedTotalOperator P Q a := by
      simpa [normalizationConditionSandwichedTotalOperator] using
        SubMeas.total_nonneg (normalizationConditionSandwichedTotalFamily P Q a)
    exact (Matrix.nonneg_iff_posSemidef.mp hnonneg).isHermitian.eq
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
