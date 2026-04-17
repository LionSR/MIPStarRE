import MIPStarRE.LDT.MainInductionStep.Defs

/-!
# Section 6 — Statement Packages

This file packages the intermediate conclusion structures and bookkeeping
statements used in the induction step. It contains conclusion packages for the
induction-level self-improvement and pasting theorems, together with restricted
failure profiles and temporary bridge statements for the still-partial assembly
of the main induction argument.

## References

- `blueprint/src/chapter/ch10_induction.tex`
- `references/ldt-paper/inductive_step.tex`
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Output package for the induction-level self-improvement theorem.

The strategy's state is bipartite (`QuantumState (ι × ι)`). Fields that
involve bipartite-lifted operators use `leftPlacedSubMeas` /
`rightPlacedSubMeas` / `tensorFailureExpectation` with honest bipartite
structure. -/
structure SelfImprovementInInductionSectionConclusion (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (_G : SubMeas (Polynomial params) ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) (eps delta gamma nu : Error) : Prop where
  /-- The projective submeasurement remains almost complete. -/
  completeness :
    CompletenessAtLeast strategy.state H.toSubMeas.liftLeft
      ((1 - nu) - selfImprovementInInductionError params eps delta gamma)
  /-- The projective submeasurement stays point-consistent with the original strategy. -/
  pointConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementInInductionError params eps delta gamma)
  /-- The output family is strongly self-consistent in the bipartite sense. -/
  strongSelfConsistency :
    BipartiteSSCRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily H.toSubMeas)
      (selfImprovementInInductionError params eps delta gamma)
  /-- The left and right placements of the output family stay close in squared distance. -/
  selfCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ι) H.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ι) H.toSubMeas))
      (selfImprovementInInductionError params eps delta gamma)
  /-- The dual witness `Z` controls the tensor failure expectation of `H`. -/
  bounded :
    tensorFailureExpectation strategy.state Z H.toSubMeas
      ≤ selfImprovementInInductionError params eps delta gamma
  /-- Every averaged point-evaluation operator is dominated by the dual witness `Z`. -/
  dominatesAveragePointOperator :
    ∀ h : Polynomial params,
      IdxPolyFamily.averagedPointEvaluationOperator strategy h ≤ Z

/-- Output package for the section-local pasting theorem. -/
structure LdPastingInInductionSectionConclusion (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (_family : IdxPolyFamily params ι)
    (H : Measurement (Polynomial params.next) ι)
    (eps delta gamma kappa zeta : Error) (k : ℕ) : Prop where
  /-- The pasted measurement is point-consistent with the ambient strategy. -/
  pointConsistency :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next H.toSubMeas)
      (ldPastingInInductionError params k eps delta gamma kappa zeta)

/-- Bookkeeping data `x ↦ (ε_x, δ_x, γ_x)` for the restricted strategies. -/
structure RestrictedFailureProfile (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) : Type where
  /-- The axis-parallel failure bound attached to each slice height. -/
  axisParallel : Fq params → Error
  /-- The self-consistency failure bound attached to each slice height. -/
  selfConsistency : Fq params → Error
  /-- The diagonal-line failure bound attached to each slice height. -/
  diagonal : Fq params → Error
  /-- Each slice-restricted strategy is good with the recorded parameters. -/
  restrictedGood :
    ∀ x,
      (xRestrictedStrategy params strategy x).IsGood
        (axisParallel x)
        (selfConsistency x)
        (diagonal x)

/-- Average restricted axis-parallel error over slices. -/
noncomputable def averageRestrictedAxisParallelError (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    (profile : RestrictedFailureProfile params strategy) : Error :=
  avgOver (uniformDistribution (Fq params)) profile.axisParallel

/-- Average restricted self-consistency error over slices. -/
noncomputable def averageRestrictedSelfConsistencyError (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    (profile : RestrictedFailureProfile params strategy) : Error :=
  avgOver (uniformDistribution (Fq params)) profile.selfConsistency

/-- Average restricted diagonal-line error over slices. -/
noncomputable def averageRestrictedDiagonalError (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    (profile : RestrictedFailureProfile params strategy) : Error :=
  avgOver (uniformDistribution (Fq params)) profile.diagonal

/-- Source-style boundedness input for the induction-level pasting theorem.

Alias of the shared Section 11/12 boundedness package. -/
abbrev PastingBoundednessInput (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (zeta : Error) : Prop :=
  IdxPolyFamily.SliceBoundednessInput strategy family zeta

/-- Temporary bridge package for the still-unformalized induction assembly.

This isolates the missing recursion/self-improvement/pasting assembly behind an
explicit witness, matching the temporary bridge style already used in Section 9
for `SelfImprovementBridgePackage`. -/
structure MainInductionBridgePackage (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error) (k : ℕ) : Prop where
  /-- A temporary witness measurement already satisfying the target consistency bound. -/
  witness :
    ∃ error : Error, ∃ G : Measurement (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        error ∧
      error ≤ mainInductionError params k eps delta gamma

/-- Bookkeeping package for the restricted-probabilities lemma.

Both the axis-parallel and diagonal branches use the paper's
`((m + 1) / m)` slice-conditioning loss. -/
structure RestrictedProbabilitiesBridgePackage (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (eps gamma : Error) : Prop where
  /-- The weighted average axis-parallel slice error is bounded by `eps`. -/
  axisWeightedBound :
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedStrategy params strategy x).axisParallelFailureProbability) ≤ eps
  /-- The weighted average diagonal slice error is bounded by `gamma`. -/
  diagonalWeightedBound :
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceDiagonalDirectionWeight params *
          (xRestrictedStrategy params strategy x).diagonalFailureProbability) ≤ gamma

/-- Bookkeeping package for the restricted-probabilities lemma.

The self-consistency branch is formalized directly. The axis-parallel and
diagonal conditioning bounds are currently exposed through
`RestrictedProbabilitiesBridgePackage`, matching the temporary bridge-pattern
already used elsewhere in the repository. -/
structure RestrictedProbabilitiesStatement (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error) : Prop where
  /-- There is a slice-wise error profile satisfying all averaged restricted bounds. -/
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
