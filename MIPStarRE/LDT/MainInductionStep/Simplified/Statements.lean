import MIPStarRE.LDT.MainInductionStep.Theorems.StageDataConstructors
import MIPStarRE.LDT.SelfImprovement.Simplified.DilationSelfImprovement

/-!
# Simplified main-induction statements

The simplified proof uses a separate degree-zero bound and a positive-degree
bound with no public pasting-length parameter. The answer-valued predecessor
statement supports restriction of diagonal-line answers in the induction step.

## References

- `blueprint/src/low_degree_simplified.tex`, `thm:main-induction`.
- `references/ldt-paper/inductive_step.tex`, `thm:main-induction`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- The positive-degree error in the simplified main induction:
`1000 d² m⁴ (ε^(1/32) + δ^(1/32) + (d/q)^(1/32) + γ^(1/8))`.

Paper origin: `blueprint/src/low_degree_simplified.tex`, `thm:main-induction`.
This replaces the exponential and the public pasting-length parameter in
`references/ldt-paper/inductive_step.tex:7-18`. -/
noncomputable def simplifiedPositiveDegreeError (params : Parameters)
    (eps delta gamma : Error) : Error :=
  1000 * (params.d : Error) ^ (2 : ℕ) * (params.m : Error) ^ (4 : ℕ) *
    (Real.rpow eps (1 / (32 : Error)) +
      Real.rpow delta (1 / (32 : Error)) +
      Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (32 : Error)) +
      Real.rpow gamma (1 / (8 : Error)))

/-- The degree-zero error `δ + √(8mε)` of the direct averaged-point
construction in the simplified proof. -/
noncomputable def simplifiedDegreeZeroError (params : Parameters)
    (eps delta : Error) : Error :=
  delta + Real.sqrt (8 * (params.m : Error) * eps)

/-- The main-induction error of the simplified proof, with its direct
degree-zero branch. -/
noncomputable def simplifiedMainInductionError (params : Parameters)
    (eps delta gamma : Error) : Error :=
  if params.d = 0 then
    simplifiedDegreeZeroError params eps delta
  else
    simplifiedPositiveDegreeError params eps delta gamma

/-- The answer-valued recursive conclusion for the simplified induction.

This is a Lean-only simultaneous-induction strengthening of the source
statement. It has the same point-consistency conclusion and error as the
ordinary strategy theorem, but allows all functions as diagonal-line answers
so that slice restriction remains a complete measurement. -/
def SimplifiedAnswerInductionConclusion (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (eps delta gamma : Error) : Prop :=
  ∃ G : Measurement (Polynomial params) ι,
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas)
      (simplifiedMainInductionError params eps delta gamma)

/-- The universe-polymorphic predecessor hypothesis used for answer-valued
restricted slices. The pasting length is chosen inside the successor proof. -/
def SimplifiedAnswerInductionHypothesis.{uF, vι} (params : Parameters)
    [FieldModel.{uF} params.q] : Prop :=
  ∀ (ι : Type vι) [Fintype ι] [DecidableEq ι],
    ∀ (strategy : AnswerSymStrat params ι) (eps delta gamma : Error),
      strategy.IsGood eps delta gamma →
        SimplifiedAnswerInductionConclusion params strategy eps delta gamma

/-- Slice outputs obtained by applying the simplified induction hypothesis to
the answer-valued restricted strategies. -/
structure SimplifiedAnswerPerSliceData (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma) where
  /-- The recursive polynomial measurement on each slice. -/
  sliceMeasurement : Fq params → Measurement (Polynomial params) ι
  /-- Its consistency with the restricted point measurements. -/
  pointConsistency : ∀ x,
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas
        (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
      (polynomialEvaluationFamily params (sliceMeasurement x).toSubMeas)
      (simplifiedMainInductionError params
        (restrictionPkg.profile.axisParallel x)
        (restrictionPkg.profile.selfConsistency x)
        (restrictionPkg.profile.diagonal x))

/-- Apply the predecessor hypothesis to every answer-valued restricted
strategy. The existing restricted-probabilities record supplies goodness. -/
noncomputable def SimplifiedAnswerPerSliceData.ofInductionHypothesis.{uF}
    (params : Parameters) [FieldModel.{uF} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (hinduction : SimplifiedAnswerInductionHypothesis.{uF, uι} params) :
    SimplifiedAnswerPerSliceData params strategy eps delta gamma restrictionPkg := by
  classical
  let output : ∀ x, SimplifiedAnswerInductionConclusion params
      (xRestrictedAnswerSymStrat params strategy x)
      (restrictionPkg.profile.axisParallel x)
      (restrictionPkg.profile.selfConsistency x)
      (restrictionPkg.profile.diagonal x) := by
    intro x
    exact hinduction ι (xRestrictedAnswerSymStrat params strategy x)
      (restrictionPkg.profile.axisParallel x)
      (restrictionPkg.profile.selfConsistency x)
      (restrictionPkg.profile.diagonal x)
      (restrictionPkg.profile.restrictedGood x)
  refine {
    sliceMeasurement := fun x => Classical.choose (output x)
    pointConsistency := ?_ }
  intro x
  exact Classical.choose_spec (output x)

/-- When the displayed consistency budget is at least one, a complete
distinguished-outcome measurement supplies the answer-valued conclusion. -/
theorem simplifiedAnswerInductionOfOneLeError
    (params : Parameters) [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (eps delta gamma : Error)
    (herror : 1 ≤ simplifiedMainInductionError params eps delta gamma) :
    SimplifiedAnswerInductionConclusion params strategy eps delta gamma := by
  classical
  let G : Measurement (Polynomial params) ι :=
    Measurement.trivialDistinguishedOutcome
      (Classical.choice (inferInstance : Nonempty (Polynomial params)))
  refine ⟨G, ?_⟩
  exact ⟨le_trans
    (bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas))
    herror⟩

/-- The ordinary symmetric-strategy version of the unit-error branch. -/
theorem simplifiedInductionOfOneLeError
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (herror : 1 ≤ simplifiedMainInductionError params eps delta gamma) :
    ∃ G : Measurement (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (simplifiedMainInductionError params eps delta gamma) := by
  classical
  let G : Measurement (Polynomial params) ι :=
    Measurement.trivialDistinguishedOutcome
      (Classical.choice (inferInstance : Nonempty (Polynomial params)))
  refine ⟨G, ?_⟩
  exact ⟨le_trans
    (bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas))
    herror⟩

end MIPStarRE.LDT.MainInductionStep
