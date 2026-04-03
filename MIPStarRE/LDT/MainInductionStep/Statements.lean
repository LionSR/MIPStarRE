import MIPStarRE.LDT.MainInductionStep.Defs

/-!
Statement containers for Section 6 of the low individual degree paper.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Output package for the induction-level self-improvement theorem.

The strategy's state is bipartite (`QuantumState (ι × ι)`).  Fields that
involve bipartite-lifted operators use `leftPlacedSubMeas` /
`rightPlacedSubMeas` / `tensorFailureExpectation` with honest bipartite
structure. -/
structure SelfImprovementInInductionSectionConclusion (params : Parameters)
    (strategy : SymStrat params ι)
    (_G : SubMeas (Polynomial params) ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) (eps delta gamma nu : Error) : Prop where
  completeness :
    CompletenessAtLeast strategy.state H.toSubMeas.liftLeft
      ((1 - nu) - selfImprovementInInductionError params eps delta gamma)
  pointConsistency :
    ConsWithPolyEval params strategy.state
      (IdxProjMeas.toIdxSubMeasLeft strategy.pointMeasurement)
      H.toSubMeas.liftRight
      (selfImprovementInInductionError params eps delta gamma)
  strongSelfConsistency :
    PolyMeasSSC params strategy.state H.toSubMeas
      (selfImprovementInInductionError params eps delta gamma)
  selfCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ι) H.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ι) H.toSubMeas))
      (selfImprovementInInductionError params eps delta gamma)
  bounded :
    tensorFailureExpectation strategy.state Z H.toSubMeas
      ≤ selfImprovementInInductionError params eps delta gamma
  dominatesAveragePointOperator :
    ∀ h : Polynomial params,
      averagedPointEvaluationOperator params strategy h ≤ Z

/-- Output package for the section-local pasting theorem. -/
structure LdPastingInInductionSectionConclusion (params : Parameters)
    (strategy : SymStrat params.next ι)
    (_family : IdxPolyFamily params ι)
    (H : Measurement (Polynomial params.next) ι)
    (eps delta gamma kappa zeta : Error) (k : ℕ) : Prop where
  pointConsistency :
    ConsWithPolyEval params.next strategy.state
      (IdxProjMeas.toIdxSubMeasLeft strategy.pointMeasurement)
      H.toSubMeas.liftRight
      (ldPastingInInductionError params k eps delta gamma kappa zeta)

/-- Bookkeeping data `x ↦ (ε_x, δ_x, γ_x)` for the restricted strategies. -/
structure RestrictedFailureProfile (params : Parameters)
    (strategy : SymStrat params.next ι) : Type where
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
    {strategy : SymStrat params.next ι}
    (profile : RestrictedFailureProfile params strategy) : Error :=
  avgOver (uniformDistribution (Fq params)) profile.axisParallel

/-- Average restricted self-consistency error over slices. -/
noncomputable def averageRestrictedSelfConsistencyError (params : Parameters)
    {strategy : SymStrat params.next ι}
    (profile : RestrictedFailureProfile params strategy) : Error :=
  avgOver (uniformDistribution (Fq params)) profile.selfConsistency

/-- Average restricted diagonal-line error over slices. -/
noncomputable def averageRestrictedDiagonalError (params : Parameters)
    {strategy : SymStrat params.next ι}
    (profile : RestrictedFailureProfile params strategy) : Error :=
  avgOver (uniformDistribution (Fq params)) profile.diagonal

/-- Source-style boundedness input for the induction-level pasting theorem. -/
structure PastingBoundednessInput (params : Parameters)
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (zeta : Error) : Prop where
  bounded : family.Bounded strategy.state zeta
  dominationTargetAgrees :
    ∀ x : Fq params, ∀ g : Polynomial params,
      family.dominationTarget x g =
        averagedSlicePointEvaluationOperator params strategy x g

/-- Bookkeeping package for the restricted-probabilities lemma. -/
structure RestrictedProbabilitiesStatement (params : Parameters)
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error) : Prop where
  profileExists :
    ∃ profile : RestrictedFailureProfile params strategy,
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params * profile.axisParallel x) ≤ eps ∧
        averageRestrictedAxisParallelError params profile
          ≤ sliceConditioningLoss params * eps ∧
        averageRestrictedSelfConsistencyError params profile ≤ delta ∧
        avgOver (uniformDistribution (Fq params))
          (fun x => sliceDiagonalDirectionWeight params * profile.diagonal x) ≤ gamma ∧
        averageRestrictedDiagonalError params profile
          ≤ sliceDiagonalConditioningLoss params * gamma ∧
        sliceTransverseDirectionWeight params *
          averageRestrictedAxisParallelError params profile ≤ eps ∧
        sliceDiagonalDirectionWeight params *
          averageRestrictedDiagonalError params profile ≤ gamma

end MIPStarRE.LDT.MainInductionStep
