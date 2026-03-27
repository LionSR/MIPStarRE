import MIPStarRE.LDT.MainInductionStep.Defs

/-!
Statement containers for Section 6 of the low individual degree paper.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT

/-- Output package for the induction-level self-improvement theorem. -/
structure SelfImprovementInInductionSectionConclusion (params : Parameters)
    (strategy : SymmetricStrategy params d)
    (_G : SubMeasurement (Polynomial params) d)
    (H : ProjectiveSubMeasurement (Polynomial params) d)
    (Z : Operator d) (eps delta gamma nu : Error) : Prop where
  completeness :
    CompletenessAtLeast strategy.state H.toSubMeasurement
      ((1 - nu) - selfImprovementInInductionError params eps delta gamma)
  pointConsistency :
    ConsistentWithPolynomialEvaluation params strategy.state
      (IndexedProjectiveMeasurement.toIndexedSubMeasurement strategy.pointMeasurement)
      H.toSubMeasurement
      (selfImprovementInInductionError params eps delta gamma)
  strongSelfConsistency :
    PolynomialMeasurementStronglySelfConsistent params strategy.state H.toSubMeasurement
      (selfImprovementInInductionError params eps delta gamma)
  selfCloseness :
    MIPStarRE.LDT.Preliminaries.BipartiteStateDependentDistanceRel
      strategy.state (uniformDistribution Unit)
      (constantSubMeasurementFamily (leftPlacedSubMeasurement H.toSubMeasurement))
      (constantSubMeasurementFamily (rightPlacedSubMeasurement H.toSubMeasurement))
      (selfImprovementInInductionError params eps delta gamma)
  bounded :
    tensorFailureExpectation strategy.state Z H.toSubMeasurement
      ≤ selfImprovementInInductionError params eps delta gamma
  dominatesAveragePointOperator :
    ∀ h : Polynomial params,
      DominatesOperator Z (averagedPointEvaluationOperator params strategy h)

/-- Output package for the section-local pasting theorem. -/
structure LdPastingInInductionSectionConclusion (params : Parameters)
    (strategy : SymmetricStrategy params.next d)
    (_family : IndexedPolynomialFamily params d)
    (H : Measurement (Polynomial params.next) d)
    (eps delta gamma kappa zeta : Error) (k : ℕ) : Prop where
  pointConsistency :
    ConsistentWithPolynomialEvaluation params.next strategy.state
      (IndexedProjectiveMeasurement.toIndexedSubMeasurement strategy.pointMeasurement)
      H.toSubMeasurement
      (ldPastingInInductionError params k eps delta gamma kappa zeta)

/-- Bookkeeping data `x ↦ (ε_x, δ_x, γ_x)` for the restricted strategies. -/
structure RestrictedFailureProfile (params : Parameters)
    (strategy : SymmetricStrategy params.next d) : Type where
  axisParallel : Fq params → Error
  selfConsistency : Fq params → Error
  diagonal : Fq params → Error
  restrictedGood :
    ∀ x,
      (xRestrictedStrategy params strategy x).IsGood
        (axisParallel x)
        (selfConsistency x)
        (diagonal x)

/-- Average restricted axis-parallel error over slices. -/
noncomputable def averageRestrictedAxisParallelError (params : Parameters)
    {strategy : SymmetricStrategy params.next d}
    (profile : RestrictedFailureProfile params strategy) : Error :=
  averageOverSlices params profile.axisParallel

/-- Average restricted self-consistency error over slices. -/
noncomputable def averageRestrictedSelfConsistencyError (params : Parameters)
    {strategy : SymmetricStrategy params.next d}
    (profile : RestrictedFailureProfile params strategy) : Error :=
  averageOverSlices params profile.selfConsistency

/-- Average restricted diagonal-line error over slices. -/
noncomputable def averageRestrictedDiagonalError (params : Parameters)
    {strategy : SymmetricStrategy params.next d}
    (profile : RestrictedFailureProfile params strategy) : Error :=
  averageOverSlices params profile.diagonal

/-- Source-style boundedness input for the induction-level pasting theorem. -/
structure PastingBoundednessInput (params : Parameters)
    (strategy : SymmetricStrategy params.next d)
    (family : IndexedPolynomialFamily params d) (zeta : Error) : Prop where
  bounded : family.Bounded strategy.state zeta
  dominationTargetAgrees :
    ∀ x : Fq params, ∀ g : Polynomial params,
      family.dominationTarget x g =
        averagedSlicePointEvaluationOperator params strategy x g

/-- Bookkeeping package for the restricted-probabilities lemma. -/
structure RestrictedProbabilitiesStatement (params : Parameters)
    (strategy : SymmetricStrategy params.next d)
    (eps delta gamma : Error) : Prop where
  profileExists :
    ∃ profile : RestrictedFailureProfile params strategy,
      weightedAverageOverSlices params
          (sliceTransverseDirectionWeight params) profile.axisParallel ≤ eps ∧
        averageRestrictedAxisParallelError params profile
          ≤ sliceConditioningLoss params * eps ∧
        averageRestrictedSelfConsistencyError params profile ≤ delta ∧
        weightedAverageOverSlices params
          (sliceTransverseDirectionWeight params) profile.diagonal ≤ gamma ∧
        averageRestrictedDiagonalError params profile
          ≤ sliceConditioningLoss params * gamma ∧
        sliceTransverseDirectionWeight params *
          averageRestrictedAxisParallelError params profile ≤ eps ∧
        sliceTransverseDirectionWeight params *
          averageRestrictedDiagonalError params profile ≤ gamma

end MIPStarRE.LDT.MainInductionStep
