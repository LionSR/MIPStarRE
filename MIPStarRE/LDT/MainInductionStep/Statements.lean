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
-- TODO(#502, #449): concrete producer pending Section 12 → Section 6 hand-off.
structure MainInductionBridgePackage (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error) (k : ℕ) : Prop where
  /-- Temporary witness measurement already satisfying the target consistency bound. -/
  witness :
    ∃ error : Error, ∃ G : Measurement (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        error ∧
      error ≤ mainInductionError params k eps delta gamma

/-- Bookkeeping package for the restricted-probabilities lemma.

The self-consistency branch is formalized directly. The axis-parallel and
diagonal conditioning bounds now appear as explicit theorem hypotheses rather
than a dedicated bridge-package structure. -/
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

/-- Bookkeeping package for the slice-restriction step of `thm:main-induction`.

This records an explicit restricted failure profile together with the averaged
bounds extracted from `lem:restricted-probabilities`. -/
structure SliceRestrictionPackage (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error) where
  /-- Slice-wise failure profile `x ↦ (ε_x, δ_x, γ_x)`. -/
  profile : RestrictedFailureProfile params strategy
  /-- Averaged axis-parallel slice error bound. -/
  axisAverageBound :
    averageRestrictedAxisParallelError params profile ≤
      sliceConditioningLoss params * eps
  /-- Averaged self-consistency slice error bound. -/
  selfAverageBound :
    averageRestrictedSelfConsistencyError params profile ≤ delta
  /-- Averaged diagonal slice error bound. -/
  diagonalAverageBound :
    averageRestrictedDiagonalError params profile ≤
      sliceDiagonalConditioningLoss params * gamma

/-- Explicit per-slice output of the inductive hypothesis.

This is the recursion-entry package: given a slice restriction package, a proof of
`thm:main-induction` in dimension `m` is expected to produce a measurement `G^x`
for every slice height `x`. -/
structure PerSliceInductionPackage (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (restrictionPkg : SliceRestrictionPackage params strategy eps delta gamma)
    (k : ℕ) where
  /-- Slice-wise inductive error `σ_x`. -/
  sliceError : Fq params → Error
  /-- Slice-wise inductive measurement `G^x`. -/
  sliceMeasurement : Fq params → Measurement (Polynomial params) ι
  /-- Each `G^x` satisfies the dimension-`m` point-consistency conclusion. -/
  pointConsistency :
    ∀ x,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas (xRestrictedStrategy params strategy x).pointMeasurement)
        (polynomialEvaluationFamily params (sliceMeasurement x).toSubMeas)
        (sliceError x)
  /-- The slice-wise error is bounded by the dimension-`m` induction target. -/
  error_le :
    ∀ x,
      sliceError x ≤
        mainInductionError params k
          (restrictionPkg.profile.axisParallel x)
          (restrictionPkg.profile.selfConsistency x)
          (restrictionPkg.profile.diagonal x)

/-- The slice-local self-improvement error `ζ_x`. -/
noncomputable def sliceSelfImprovementError (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    {eps delta gamma : Error}
    (restrictionPkg : SliceRestrictionPackage params strategy eps delta gamma)
    (x : Fq params) : Error :=
  selfImprovementInInductionError params
    (restrictionPkg.profile.axisParallel x)
    (restrictionPkg.profile.selfConsistency x)
    (restrictionPkg.profile.diagonal x)

/-- Slice-wise output of the induction-level self-improvement stage.

Because `xRestrictedStrategy` is not literally a `SymStrat params` (its diagonal
answers still live in `DiagonalLinePolynomial params.next`), this package records
directly the four paper-faithful properties that will later be averaged into the
pasting inputs. -/
structure SelfImprovementPackage (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error) (k : ℕ)
    (restrictionPkg : SliceRestrictionPackage params strategy eps delta gamma)
    (inductionPkg : PerSliceInductionPackage params strategy eps delta gamma restrictionPkg k)
    where
  /-- Slice-wise projective submeasurement `Ĝ^x`. -/
  sliceProj : Fq params → ProjSubMeas (Polynomial params) ι
  /-- Slice-wise PSD witness `Z^x`. -/
  sliceWitness : Fq params → MIPStarRE.Quantum.Op ι
  /-- Slice-wise completeness bound. -/
  completeness :
    ∀ x,
      CompletenessAtLeast strategy.state (sliceProj x).toSubMeas.liftLeft
        ((1 - inductionPkg.sliceError x) -
          sliceSelfImprovementError params restrictionPkg x)
  /-- Slice-wise consistency with the restricted point measurement. -/
  pointConsistency :
    ∀ x,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas (xRestrictedStrategy params strategy x).pointMeasurement)
        (polynomialEvaluationFamily params (sliceProj x).toSubMeas)
        (sliceSelfImprovementError params restrictionPkg x)
  /-- Slice-wise strong self-consistency. -/
  strongSelfConsistency :
    ∀ x,
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (sliceProj x).toSubMeas)
        (sliceSelfImprovementError params restrictionPkg x)
  /-- Slice-wise left/right closeness needed for the averaged self-consistency package. -/
  selfCloseness :
    ∀ x,
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ι) (sliceProj x).toSubMeas))
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ι) (sliceProj x).toSubMeas))
        (sliceSelfImprovementError params restrictionPkg x)
  /-- Slice-wise boundedness residual. -/
  bounded :
    ∀ x,
      tensorFailureExpectation strategy.state (sliceWitness x) (sliceProj x).toSubMeas
        ≤ sliceSelfImprovementError params restrictionPkg x
  /-- Slice-wise domination of the averaged point operator. -/
  dominatesAveragePointOperator :
    ∀ x, ∀ h : Polynomial params,
      IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h ≤ sliceWitness x

namespace SelfImprovementPackage

/-- The slice-indexed polynomial family obtained by collecting the improved
slice measurements `Ĝ^x`. -/
noncomputable def family {params : Parameters}
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    {eps delta gamma : Error} {k : ℕ}
    {restrictionPkg : SliceRestrictionPackage params strategy eps delta gamma}
    {inductionPkg :
      PerSliceInductionPackage params strategy eps delta gamma restrictionPkg k}
    (pkg : SelfImprovementPackage params strategy eps delta gamma k restrictionPkg inductionPkg) :
    IdxPolyFamily params ι :=
  IdxPolyFamily.ofSymStrat strategy pkg.sliceProj

@[simp] theorem family_meas {params : Parameters}
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    {eps delta gamma : Error} {k : ℕ}
    {restrictionPkg : SliceRestrictionPackage params strategy eps delta gamma}
    {inductionPkg :
      PerSliceInductionPackage params strategy eps delta gamma restrictionPkg k}
    (pkg : SelfImprovementPackage params strategy eps delta gamma k restrictionPkg inductionPkg) :
    pkg.family.meas = pkg.sliceProj :=
  rfl

end SelfImprovementPackage

/-- Averaged pasting inputs distilled from the per-slice self-improvement data.

This packages exactly the hypotheses needed to invoke
`thm:ld-pasting-in-induction-section` after the slice-wise self-improvement
outputs have been averaged. -/
structure PastingPackage (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error) (k : ℕ)
    {restrictionPkg : SliceRestrictionPackage params strategy eps delta gamma}
    {inductionPkg :
      PerSliceInductionPackage params strategy eps delta gamma restrictionPkg k}
    (selfPkg : SelfImprovementPackage params strategy eps delta gamma k restrictionPkg inductionPkg)
    where
  /-- Averaged completeness parameter `κ`. -/
  kappa : Error
  /-- Averaged self-improvement / pasting interface parameter `ζ`. -/
  zeta : Error
  /-- Small-parameter hypothesis for the diagonal test branch. -/
  gamma_le_one : gamma ≤ 1
  /-- Small-parameter hypothesis for the averaged self-improvement parameter. -/
  zeta_le_one : zeta ≤ 1
  /-- Source-style low-degree hypothesis for the field size. -/
  dq_le_q : params.d ≤ params.q
  /-- Averaged completeness of the slice family. -/
  complete : selfPkg.family.Complete strategy.state kappa
  /-- Averaged point-consistency of the slice family. -/
  consistent : selfPkg.family.ConsistentWithPoints strategy zeta
  /-- Averaged strong self-consistency of the slice family. -/
  selfConsistent : selfPkg.family.StronglySelfConsistent strategy.state zeta
  /-- Averaged boundedness input for the pasting theorem. -/
  bounded : PastingBoundednessInput params strategy selfPkg.family zeta
  /-- Error telescoping from the induction-section pasting bound to the next-stage target. -/
  error_le :
    ldPastingInInductionError params k eps delta gamma kappa zeta ≤
      mainInductionError params.next k eps delta gamma

end MIPStarRE.LDT.MainInductionStep
