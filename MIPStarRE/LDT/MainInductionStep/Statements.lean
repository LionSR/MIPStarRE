import MIPStarRE.LDT.MainInductionStep.Defs

/-!
Statement containers for Section 6 of the low individual degree paper.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT

/-- Output package for the induction-level self-improvement theorem. -/
structure SelfImprovementInInductionSectionConclusion (params : Parameters)
    (strategy : SymStrat params d)
    (_G : SubMeas (Polynomial params) d)
    (H : ProjSubMeas (Polynomial params) d)
    (Z : Operator d) (eps delta gamma nu : Error) : Prop where
  completeness :
    CompletenessAtLeast strategy.state H.toSubMeas
      ((1 - nu) - selfImprovementInInductionError params eps delta gamma)
  pointConsistency :
    ConsWithPolyEval params strategy.state
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      H.toSubMeas
      (selfImprovementInInductionError params eps delta gamma)
  strongSelfConsistency :
    PolyMeasSSC params strategy.state H.toSubMeas
      (selfImprovementInInductionError params eps delta gamma)
  selfCloseness :
    MIPStarRE.LDT.Preliminaries.BipartiteSDDRel
      strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (leftPlacedSubMeas H.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas H.toSubMeas))
      (selfImprovementInInductionError params eps delta gamma)
  bounded :
    tensorFailureExpectation strategy.state Z H.toSubMeas
      ≤ selfImprovementInInductionError params eps delta gamma
  dominatesAveragePointOperator :
    ∀ h : Polynomial params,
      OpDominates Z (averagedPointEvaluationOperator params strategy h)

/-- Output package for the section-local pasting theorem. -/
structure LdPastingInInductionSectionConclusion (params : Parameters)
    (strategy : SymStrat params.next d)
    (_family : IdxPolyFamily params d)
    (H : Measurement (Polynomial params.next) d)
    (eps delta gamma kappa zeta : Error) (k : ℕ) : Prop where
  pointConsistency :
    ConsWithPolyEval params.next strategy.state
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      H.toSubMeas
      (ldPastingInInductionError params k eps delta gamma kappa zeta)

/-- Bookkeeping data `x ↦ (ε_x, δ_x, γ_x)` for the restricted strategies. -/
structure RestrictedFailureProfile (params : Parameters)
    (strategy : SymStrat params.next d) : Type where
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
    {strategy : SymStrat params.next d}
    (profile : RestrictedFailureProfile params strategy) : Error :=
  averageOverSlices params profile.axisParallel

/-- Average restricted self-consistency error over slices. -/
noncomputable def averageRestrictedSelfConsistencyError (params : Parameters)
    {strategy : SymStrat params.next d}
    (profile : RestrictedFailureProfile params strategy) : Error :=
  averageOverSlices params profile.selfConsistency

/-- Average restricted diagonal-line error over slices. -/
noncomputable def averageRestrictedDiagonalError (params : Parameters)
    {strategy : SymStrat params.next d}
    (profile : RestrictedFailureProfile params strategy) : Error :=
  averageOverSlices params profile.diagonal

/-- Source-style boundedness input for the induction-level pasting theorem. -/
structure PastingBoundednessInput (params : Parameters)
    (strategy : SymStrat params.next d)
    (family : IdxPolyFamily params d) (zeta : Error) : Prop where
  bounded : family.Bounded strategy.state zeta
  dominationTargetAgrees :
    ∀ x : Fq params, ∀ g : Polynomial params,
      family.dominationTarget x g =
        averagedSlicePointEvaluationOperator params strategy x g

/-- Bookkeeping package for the restricted-probabilities lemma. -/
structure RestrictedProbabilitiesStatement (params : Parameters)
    (strategy : SymStrat params.next d)
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
