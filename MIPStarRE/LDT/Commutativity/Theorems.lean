import MIPStarRE.LDT.Commutativity.Defs

/-!
Statement packaging and scaffold theorems for Section 11 commutativity.

In the bipartite model, `ψbi : QuantumState (d * d)` is the bipartite state
on both registers.  Fields that involve bipartite-lifted operators (via
`leftPlacedSubMeas` / `rightPlacedSubMeas` / `leftTensor`) use `ψbi`,
while fields that stay on a single register use `strategy.state`.
TODO(bipartite): when `SymStrat` gains separate local/bipartite dimensions,
`ψbi` should come from the strategy directly.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints

noncomputable section

/-- Operator domination, written in source order as `X ≤ Y`. -/
abbrev OperatorDominatedBy (X Y : Operator d) : Prop :=
  OpDominates Y X

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

`ψbi` is the bipartite state on `d * d` used for fields involving
tensor-placed operators.  Fields on a single register use `strategy.state`. -/
structure CommDataProcessedGConclusion (params : Parameters)
    (strategy : SymStrat params.next d)
    (ψbi : QuantumState (d * d))
    (family : IdxPolyFamily params d)
    (gamma zeta : Error) : Prop where
  postprocessedPointConsistency :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (evaluatedPointFamily params family)
      zeta
  postprocessedSelfConsistency :
    SDDRel ψbi
      (uniformDistribution (Point params.next))
      (evaluatedPointFamilyLeft params family)
      (evaluatedPointFamilyRight params family)
      zeta
  stabilityOne :
    SDDRel ψbi
      (uniformDistribution (EvaluatedSliceQuestion params))
      (commDataProcessedGStabilityOneLeft params strategy family)
      (commDataProcessedGStabilityOneRight params strategy family)
      (commDataProcessedGStabilityOneError zeta)
  stabilityTwo :
    SDDRel ψbi
      (uniformDistribution (EvaluatedSliceQuestion params))
      (commDataProcessedGStabilityTwoLeft params strategy family)
      (commDataProcessedGStabilityTwoRight params strategy family)
      (commDataProcessedGStabilityTwoError params gamma zeta)
  evaluatedSliceCommutation :
    SDDRel ψbi
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedSliceProductLeft params strategy family)
      (evaluatedSliceProductRight params strategy family)
      (commDataProcessedGError params gamma zeta)

/-- Output package for `thm:com-main`. -/
structure ComMainConclusion (params : Parameters)
    (strategy : SymStrat params.next d)
    (ψbi : QuantumState (d * d))
    (family : IdxPolyFamily params d)
    (gamma zeta : Error) : Prop where
  evaluatedCommutation :
    CommDataProcessedGConclusion params strategy ψbi family gamma zeta
  evaluationSpecialization :
    SDDRel ψbi
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedFromFullSliceProductLeft params strategy family)
      (evaluatedFromFullSliceProductRight params strategy family)
      (commDataProcessedGError params gamma zeta)
  fullSliceCommutation :
    SDDRel ψbi
      (uniformDistribution (FullSliceQuestion params))
      (fullSliceProductLeft params strategy family)
      (fullSliceProductRight params strategy family)
      (comMainError params gamma zeta)

/-- Output package for `lem:normalization-condition`. -/
structure NormalizationConditionStatement {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA d)
    (Q : ProjSubMeas OutcomeB d) : Prop where
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
    (strategy : SymStrat params.next d)
    (ψbi : QuantumState (d * d))
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params d)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : family.Bounded strategy.state zeta) :
    CommDataProcessedGConclusion params strategy ψbi family gamma zeta := by
  sorry

/-- `thm:com-main`. -/
theorem comMain
    (params : Parameters)
    (strategy : SymStrat params.next d)
    (ψbi : QuantumState (d * d))
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params d)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : family.Bounded strategy.state zeta) :
    ComMainConclusion params strategy ψbi family gamma zeta := by
  sorry

/-- `lem:normalization-condition`. -/
lemma normalizationCondition {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA d)
    (Q : ProjSubMeas OutcomeB d) :
    NormalizationConditionStatement P Q := by
  sorry

end

end MIPStarRE.LDT.Commutativity
