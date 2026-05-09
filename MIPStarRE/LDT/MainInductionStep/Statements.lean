import MIPStarRE.LDT.MainInductionStep.Defs
import MIPStarRE.LDT.Test.StrategyPolynomialFamilies

/-!
# Section 6 — Induction Step Data

This file records the intermediate conclusion structures and bookkeeping
statements used in the induction step. It contains the conclusions of the
induction-level self-improvement and pasting theorems, together with restricted
failure profiles and the stage data for the paper's slice restriction,
slice-wise induction, self-improvement, and pasting assembly.

## References

- `blueprint/src/chapter/ch10_induction.tex`
- `references/ldt-paper/inductive_step.tex`
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Conclusion of the induction-level self-improvement theorem.

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

/-- Conclusion of the section-local pasting theorem. -/
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

/-- Bookkeeping data for answer-valued restricted strategies.

This is the function-answer analogue of `RestrictedFailureProfile`: each slice is
the restricted strategy interface from `inductive_step.tex`, lines 436--455. -/
structure AnswerRestrictedFailureProfile (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) : Type where
  /-- The axis-parallel failure bound attached to each slice height. -/
  axisParallel : Fq params → Error
  /-- The self-consistency failure bound attached to each slice height. -/
  selfConsistency : Fq params → Error
  /-- The diagonal-line failure bound attached to each slice height. -/
  diagonal : Fq params → Error
  /-- Each answer-valued slice-restricted strategy is good with the recorded parameters. -/
  restrictedGood :
    ∀ x,
      (xRestrictedAnswerSymStrat params strategy x).IsGood
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

/-- Average restricted axis-parallel error over answer-valued slices. -/
noncomputable def averageAnswerRestrictedAxisParallelError (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    (profile : AnswerRestrictedFailureProfile params strategy) : Error :=
  avgOver (uniformDistribution (Fq params)) profile.axisParallel

/-- Average restricted self-consistency error over answer-valued slices. -/
noncomputable def averageAnswerRestrictedSelfConsistencyError (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    (profile : AnswerRestrictedFailureProfile params strategy) : Error :=
  avgOver (uniformDistribution (Fq params)) profile.selfConsistency

/-- Average restricted diagonal-line error over answer-valued slices. -/
noncomputable def averageAnswerRestrictedDiagonalError (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    (profile : AnswerRestrictedFailureProfile params strategy) : Error :=
  avgOver (uniformDistribution (Fq params)) profile.diagonal

/-- Paper origin: `references/ldt-paper/inductive_step.tex:374-412`
(`\label{lem:restricted-probabilities}`).

Bookkeeping data for the restricted-probabilities lemma.

This records a slice-wise error profile together with the three averaged bounds
that appear in the paper: the axis-parallel and diagonal branches both incur the
same conditioning loss `((m + 1) / m)`, while the self-consistency branch
restricts exactly. -/
structure RestrictedProbabilitiesStatement (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error) : Prop where
  /-- There is a slice-wise error profile realizing the three averaged restricted bounds. -/
  profileExists :
    ∃ profile : RestrictedFailureProfile params strategy,
      averageRestrictedAxisParallelError params profile ≤
          sliceConditioningLoss params * eps ∧
        averageRestrictedSelfConsistencyError params profile ≤ delta ∧
        averageRestrictedDiagonalError params profile ≤
          sliceConditioningLoss params * gamma

/-- Paper origin: `references/ldt-paper/inductive_step.tex:374-412`
(`\label{lem:restricted-probabilities}`); answer-valued variant carrying the
same axis-parallel/self-consistency/diagonal restriction bounds for the
answer-restricted slice profile.  This is an answer-valued variant of
`RestrictedProbabilitiesStatement` against `xRestrictedAnswerSymStrat` rather
than `xRestrictedStrategy`; no separate paper anchor exists for the
answer-valued variant.

Bookkeeping data for the answer-valued restricted-probabilities lemma. -/
structure AnswerRestrictedProbabilitiesStatement (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error) : Prop where
  /-- There is a slice-wise answer-valued error profile realizing the three averaged bounds. -/
  profileExists :
    ∃ profile : AnswerRestrictedFailureProfile params strategy,
      averageAnswerRestrictedAxisParallelError params profile ≤
          sliceConditioningLoss params * eps ∧
        averageAnswerRestrictedSelfConsistencyError params profile ≤ delta ∧
        averageAnswerRestrictedDiagonalError params profile ≤
          sliceConditioningLoss params * gamma

/-- Bookkeeping data for the slice-restriction step of `thm:main-induction`.

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
      sliceConditioningLoss params * gamma

/-- Answer-valued slice-restriction package for the Section 6 induction step. -/
structure AnswerSliceRestrictionPackage (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error) where
  /-- Slice-wise failure profile for the answer-valued restricted strategies. -/
  profile : AnswerRestrictedFailureProfile params strategy
  /-- Averaged axis-parallel slice error bound. -/
  axisAverageBound :
    averageAnswerRestrictedAxisParallelError params profile ≤
      sliceConditioningLoss params * eps
  /-- Averaged self-consistency slice error bound. -/
  selfAverageBound :
    averageAnswerRestrictedSelfConsistencyError params profile ≤ delta
  /-- Averaged diagonal slice error bound. -/
  diagonalAverageBound :
    averageAnswerRestrictedDiagonalError params profile ≤
      sliceConditioningLoss params * gamma

/-- Explicit per-slice output of the inductive hypothesis.

This is the recursion-entry data: given slice-restriction data, a proof of
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

/-- Explicit per-slice output of the inductive hypothesis for answer-valued slices.

This is the function-answer recursion-entry package: the recursive call is made on
`xRestrictedAnswerSymStrat`, whose diagonal answers retain the whole restricted
function instead of only its value at the base point. -/
structure AnswerPerSliceInductionPackage (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (restrictionPkg : AnswerSliceRestrictionPackage params strategy eps delta gamma)
    (k : ℕ) where
  /-- Slice-wise inductive error `σ_x`. -/
  sliceError : Fq params → Error
  /-- Slice-wise inductive measurement `G^x`. -/
  sliceMeasurement : Fq params → Measurement (Polynomial params) ι
  /-- Each `G^x` satisfies the dimension-`m` point-consistency conclusion. -/
  pointConsistency :
    ∀ x,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas
          (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
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

/-- Main-induction conclusion for a function-answer symmetric strategy.

This is the answer-valued analogue of the conclusion of `thm:main-induction`.
It is used as the explicit predecessor induction hypothesis for the
paper-faithful answer-valued restriction route: for a strategy in dimension `m`,
it supplies a global polynomial measurement consistent with the point
measurement at the Section 6 error `mainInductionError`. -/
def AnswerMainInductionConclusion (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (eps delta gamma : Error) (k : ℕ) : Prop :=
  ∃ G : Measurement (Polynomial params) ι,
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas)
      (mainInductionError params k eps delta gamma)

/-- Predicate form of the answer-valued predecessor main-induction hypothesis.

This is a Lean-only interface for the induction step in
`inductive_step.tex`, lines 441--454.  It is deliberately stated at
`mainInductionError` strength and for `AnswerSymStrat`, so callers can instantiate
the paper-faithful `xRestrictedAnswerSymStrat` slices without appealing to the
public `Test.mainFormal` theorem.

The explicit `.{u,v}` universe binder decouples the universe of `FieldModel`'s
carrier `K : Type u` from the universe of the dimension index `ι : Type v`.
Without this separation, a proof that instantiates `FieldModel.{0}` (as many
`Test.MainTheorem` applications do) would also force `ι` to `Type 0`,
making it impossible to apply the hypothesis to the role-register space
`Role × ι` when the index universe exceeds `0`. -/
def AnswerMainInductionHypothesis.{u,v} (params : Parameters)
    [FieldModel.{u} params.q] : Prop :=
  ∀ (ι : Type v) [Fintype ι] [DecidableEq ι],
    ∀ (strategy : AnswerSymStrat params ι) (eps delta gamma : Error) (k : ℕ),
      0 < params.d →
        strategy.IsGood eps delta gamma →
          1 ≤ k →
            400 * params.m * params.d ≤ k →
              AnswerMainInductionConclusion params strategy eps delta gamma k

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

/-- The slice-local self-improvement error `ζ_x` for answer-valued slices. -/
noncomputable def answerSliceSelfImprovementError (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    {eps delta gamma : Error}
    (restrictionPkg : AnswerSliceRestrictionPackage params strategy eps delta gamma)
    (x : Fq params) : Error :=
  selfImprovementInInductionError params
    (restrictionPkg.profile.axisParallel x)
    (restrictionPkg.profile.selfConsistency x)
    (restrictionPkg.profile.diagonal x)

/-- Slice-wise output of the induction-level self-improvement stage.

Because `xRestrictedStrategy` is a section-local restricted strategy rather than
literally a `SymStrat params` interface—it does not carry the ambient
`permInvState` witness, the diagonal reparametrization-invariance field, or the
downstream role-symmetrization API—this data records directly the four
paper-faithful
properties that will later be averaged into the pasting inputs. -/
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
  /-- Slice-wise left/right closeness needed for the averaged self-consistency input. -/
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
slice measurements `Ĝ^x` together with the slice-wise witnesses `Z^x`. -/
noncomputable def family {params : Parameters}
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    {eps delta gamma : Error} {k : ℕ}
    {restrictionPkg : SliceRestrictionPackage params strategy eps delta gamma}
    {inductionPkg :
      PerSliceInductionPackage params strategy eps delta gamma restrictionPkg k}
    (pkg : SelfImprovementPackage params strategy eps delta gamma k restrictionPkg inductionPkg) :
    IdxPolyFamily params ι where
  meas := pkg.sliceProj
  witness := pkg.sliceWitness
  dominationTarget := fun x g =>
    IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g

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

@[simp] theorem family_witness {params : Parameters}
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    {eps delta gamma : Error} {k : ℕ}
    {restrictionPkg : SliceRestrictionPackage params strategy eps delta gamma}
    {inductionPkg :
      PerSliceInductionPackage params strategy eps delta gamma restrictionPkg k}
    (pkg : SelfImprovementPackage params strategy eps delta gamma k restrictionPkg inductionPkg)
    (x : Fq params) :
    pkg.family.witness x = pkg.sliceWitness x :=
  rfl

@[simp] theorem family_dominationTarget {params : Parameters}
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    {eps delta gamma : Error} {k : ℕ}
    {restrictionPkg : SliceRestrictionPackage params strategy eps delta gamma}
    {inductionPkg :
      PerSliceInductionPackage params strategy eps delta gamma restrictionPkg k}
    (pkg : SelfImprovementPackage params strategy eps delta gamma k restrictionPkg inductionPkg)
    (x : Fq params) (g : Polynomial params) :
    pkg.family.dominationTarget x g =
      IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g :=
  rfl

end SelfImprovementPackage

/-- Slice-wise output of the induction-level self-improvement stage for
answer-valued restricted strategies.

This mirrors `SelfImprovementPackage`, but its point-consistency field is stated
against `xRestrictedAnswerSymStrat`, the function-answer restricted strategy. -/
structure AnswerSelfImprovementPackage (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error) (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionPackage params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionPackage params strategy eps delta gamma restrictionPkg k)
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
          answerSliceSelfImprovementError params restrictionPkg x)
  /-- Slice-wise consistency with the answer-valued restricted point measurement. -/
  pointConsistency :
    ∀ x,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas
          (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
        (polynomialEvaluationFamily params (sliceProj x).toSubMeas)
        (answerSliceSelfImprovementError params restrictionPkg x)
  /-- Slice-wise strong self-consistency. -/
  strongSelfConsistency :
    ∀ x,
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (sliceProj x).toSubMeas)
        (answerSliceSelfImprovementError params restrictionPkg x)
  /-- Slice-wise left/right closeness needed for the averaged self-consistency package. -/
  selfCloseness :
    ∀ x,
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ι) (sliceProj x).toSubMeas))
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ι) (sliceProj x).toSubMeas))
        (answerSliceSelfImprovementError params restrictionPkg x)
  /-- Slice-wise boundedness residual. -/
  bounded :
    ∀ x,
      tensorFailureExpectation strategy.state (sliceWitness x) (sliceProj x).toSubMeas
        ≤ answerSliceSelfImprovementError params restrictionPkg x
  /-- Slice-wise domination of the averaged point operator. -/
  dominatesAveragePointOperator :
    ∀ x, ∀ h : Polynomial params,
      IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h ≤ sliceWitness x

namespace AnswerSelfImprovementPackage

/-- The slice-indexed polynomial family obtained from answer-valued restricted
self-improvement outputs. -/
noncomputable def family {params : Parameters}
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    {eps delta gamma : Error} {k : ℕ}
    {restrictionPkg : AnswerSliceRestrictionPackage params strategy eps delta gamma}
    {inductionPkg :
      AnswerPerSliceInductionPackage params strategy eps delta gamma restrictionPkg k}
    (pkg :
      AnswerSelfImprovementPackage params strategy eps delta gamma k restrictionPkg inductionPkg) :
    IdxPolyFamily params ι where
  meas := pkg.sliceProj
  witness := pkg.sliceWitness
  dominationTarget := fun x g =>
    IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g

@[simp] theorem family_meas {params : Parameters}
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    {eps delta gamma : Error} {k : ℕ}
    {restrictionPkg : AnswerSliceRestrictionPackage params strategy eps delta gamma}
    {inductionPkg :
      AnswerPerSliceInductionPackage params strategy eps delta gamma restrictionPkg k}
    (pkg :
      AnswerSelfImprovementPackage params strategy eps delta gamma k restrictionPkg inductionPkg) :
    pkg.family.meas = pkg.sliceProj :=
  rfl

@[simp] theorem family_witness {params : Parameters}
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    {eps delta gamma : Error} {k : ℕ}
    {restrictionPkg : AnswerSliceRestrictionPackage params strategy eps delta gamma}
    {inductionPkg :
      AnswerPerSliceInductionPackage params strategy eps delta gamma restrictionPkg k}
    (pkg :
      AnswerSelfImprovementPackage params strategy eps delta gamma k restrictionPkg inductionPkg)
    (x : Fq params) :
    pkg.family.witness x = pkg.sliceWitness x :=
  rfl

@[simp] theorem family_dominationTarget {params : Parameters}
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    {eps delta gamma : Error} {k : ℕ}
    {restrictionPkg : AnswerSliceRestrictionPackage params strategy eps delta gamma}
    {inductionPkg :
      AnswerPerSliceInductionPackage params strategy eps delta gamma restrictionPkg k}
    (pkg :
      AnswerSelfImprovementPackage params strategy eps delta gamma k restrictionPkg inductionPkg)
    (x : Fq params) (g : Polynomial params) :
    pkg.family.dominationTarget x g =
      IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g :=
  rfl

end AnswerSelfImprovementPackage

/-- Averaged pasting inputs distilled from the per-slice self-improvement data.

This records exactly the hypotheses needed to invoke
`thm:ld-pasting-in-induction-section` after the slice-wise self-improvement
outputs have been averaged. -/
structure AveragedPastingInput (params : Parameters)
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
  bounded : IdxPolyFamily.SliceBoundednessInput strategy selfPkg.family zeta
  /-- Error telescoping from the induction-section pasting bound to the next-stage target. -/
  error_le :
    ldPastingInInductionError params k eps delta gamma kappa zeta ≤
      mainInductionError params.next k eps delta gamma

end MIPStarRE.LDT.MainInductionStep
