import MIPStarRE.LDT.MainInductionStep.Theorems.SelfImprovementAssembly.Core

/-!
# Section 6 — Answer-Valued Self-Improvement Slice Transport

This file contains the answer-valued analogues of the Section 6 slice-transport
constructors.  The ordinary construction, including `selfImprovementInInductionSection`,
lives in `SelfImprovementAssembly.Core` and is imported here so that the
answer-valued construction can reuse the same Section 9 self-improvement
theorem.

## References

- `blueprint/src/chapter/ch10_induction.tex`
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Transport data for producing the answer-valued self-improvement data from
concrete per-slice symmetric strategies.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551` and
`references/ldt-paper/self_improvement.tex:631-811`; this is the answer-valued
restricted-slice interface for the same self-improvement step.

The answer-valued restriction `xRestrictedAnswerSymStrat` has the paper-faithful
answer-valued diagonal interface, while the existing Section 9 self-improvement
theorem is stated for ordinary `SymStrat`s.  This structure records concrete
ordinary slice strategies on which Section 9 can run, together with the state
and point-measurement transports needed to move the resulting conclusions back
to the answer-valued restricted bookkeeping.

The Section 9 analytic proof debt is not stored in this record.  The data record
constructor below calls
`selfImprovementInInductionSection`, whose present proof gap is the tracked
place where that work belongs. -/
structure AnswerSelfImprovementData.SliceStrategyTransport
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k) where
  /-- Concrete symmetric strategies realizing the answer-restricted slice interfaces. -/
  sliceStrategy : Fq params → SymStrat params ι
  /-- Each concrete slice strategy uses the ambient state. -/
  state_eq : ∀ x, (sliceStrategy x).state = strategy.state
  /-- Its point measurement agrees with the answer-valued restricted-slice point interface. -/
  pointMeasurement_eq :
    ∀ x,
      (sliceStrategy x).pointMeasurement =
        (xRestrictedAnswerSymStrat params strategy x).pointMeasurement
  /-- Its averaged point operator is the averaged slice point operator used by
  Section 6. -/
  averagedPoint_eq :
    ∀ x h,
      IdxPolyFamily.averagedPointEvaluationOperator (sliceStrategy x) h =
        IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h
  /-- The concrete slice strategy is good with the answer-restricted failure profile. -/
  good :
    ∀ x,
      (sliceStrategy x).IsGood
        (restrictionPkg.profile.axisParallel x)
        (restrictionPkg.profile.selfConsistency x)
        (restrictionPkg.profile.diagonal x)

/-- The averaged point-operator compatibility for answer-valued slices follows
from point-measurement transport.

Both sides unfold to the same average over `strategy.pointMeasurement
(appendPoint params u x)` once the concrete slice point measurement is identified
with `xRestrictedAnswerSymStrat`. -/
theorem AnswerSelfImprovementData.SliceStrategyTransport.averagedPoint_eq_of_pointMeasurement_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (sliceStrategy : Fq params → SymStrat params ι)
    (hpoint :
      ∀ x,
        (sliceStrategy x).pointMeasurement =
          (xRestrictedAnswerSymStrat params strategy x).pointMeasurement) :
    ∀ x h,
      IdxPolyFamily.averagedPointEvaluationOperator (sliceStrategy x) h =
        IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h := by
  intro x h
  simp [IdxPolyFamily.averagedPointEvaluationOperator,
    IdxPolyFamily.averagedSlicePointEvaluationOperator, hpoint x,
    xRestrictedAnswerSymStrat_pointMeasurement_apply]

/-- Build answer-valued `SliceStrategyTransport` without separately assuming averaged
point-operator compatibility.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551`; the averaged
point-operator compatibility is a formal transport between the answer-valued
restricted slice interface and the Section 9 interface.

The structural averaged-point field is derived from `pointMeasurement_eq`; the
remaining inputs are the concrete slice strategies, their state transport, and
their restricted-profile goodness. -/
noncomputable def AnswerSelfImprovementData.SliceStrategyTransport.ofPointMeasurementEq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k)
    (sliceStrategy : Fq params → SymStrat params ι)
    (state_eq : ∀ x, (sliceStrategy x).state = strategy.state)
    (pointMeasurement_eq :
      ∀ x,
        (sliceStrategy x).pointMeasurement =
          (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
    (good :
      ∀ x,
        (sliceStrategy x).IsGood
          (restrictionPkg.profile.axisParallel x)
          (restrictionPkg.profile.selfConsistency x)
          (restrictionPkg.profile.diagonal x)) :
    AnswerSelfImprovementData.SliceStrategyTransport params strategy eps delta gamma k
      restrictionPkg inductionPkg where
  sliceStrategy := sliceStrategy
  state_eq := state_eq
  pointMeasurement_eq := pointMeasurement_eq
  averagedPoint_eq :=
    AnswerSelfImprovementData.SliceStrategyTransport.averagedPoint_eq_of_pointMeasurement_eq
      params strategy sliceStrategy pointMeasurement_eq
  good := good

/-- Transport answer-restricted goodness to a concrete slice strategy once the
state and verifier-visible measurements agree with `xRestrictedAnswerSymStrat`.

The diagonal compatibility is stated only after postprocessing both diagonal
answer alphabets to their `zeroCoord` value; this is the comparison used by the
LDT diagonal subtest and avoids claiming a false equality between
`DiagonalLinePolynomial` and `DiagonalLineAnswer` families. -/
theorem AnswerSelfImprovementData.SliceStrategyTransport.good_of_restrictedGood
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (sliceStrategy : Fq params → SymStrat params ι)
    (state_eq : ∀ x, (sliceStrategy x).state = strategy.state)
    (pointMeasurement_eq :
      ∀ x,
        (sliceStrategy x).pointMeasurement =
          (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
    (axisParallelMeasurement_eq :
      ∀ x,
        (sliceStrategy x).axisParallelMeasurement.toIdxProjMeas =
          (xRestrictedAnswerSymStrat params strategy x).axisParallelMeasurement.toIdxProjMeas)
    (diagonalZeroCoord_eq :
      ∀ x ℓ,
        postprocess
            (((sliceStrategy x).diagonalMeasurement.toIdxProjMeas ℓ).toSubMeas)
            (fun f : DiagonalLinePolynomial params => f zeroCoord) =
          postprocess
            (((xRestrictedAnswerSymStrat params strategy x).diagonalMeasurement.toIdxProjMeas
              ℓ).toSubMeas)
            (fun f : DiagonalLineAnswer params => f zeroCoord)) :
    ∀ x,
      (sliceStrategy x).IsGood
        (restrictionPkg.profile.axisParallel x)
        (restrictionPkg.profile.selfConsistency x)
        (restrictionPkg.profile.diagonal x) := by
  intro x
  have hgood := restrictionPkg.profile.restrictedGood x
  refine ⟨?_, ?_, ?_⟩
  · have hfail : (sliceStrategy x).axisParallelFailureProbability =
        (xRestrictedAnswerSymStrat params strategy x).axisParallelFailureProbability := by
      unfold SymStrat.axisParallelFailureProbability
        AnswerSymStrat.axisParallelFailureProbability
        axisParallelPointAnswerFamily AnswerSymStrat.axisParallelPointAnswerFamily
        axisParallelLineAnswerFamily AnswerSymStrat.axisParallelLineAnswerFamily
      simp [state_eq x, pointMeasurement_eq x, axisParallelMeasurement_eq x]
    simpa [hfail] using hgood.axisParallelTest
  · have hfail : (sliceStrategy x).selfConsistencyFailureProbability =
        (xRestrictedAnswerSymStrat params strategy x).selfConsistencyFailureProbability := by
      unfold SymStrat.selfConsistencyFailureProbability
        AnswerSymStrat.selfConsistencyFailureProbability
      simp [state_eq x, pointMeasurement_eq x]
    simpa [hfail] using hgood.selfConsistencyTest
  · have hfail : (sliceStrategy x).diagonalFailureProbability =
        (xRestrictedAnswerSymStrat params strategy x).diagonalFailureProbability := by
      unfold SymStrat.diagonalFailureProbability
        AnswerSymStrat.diagonalFailureProbability
        diagonalPointAnswerFamily AnswerSymStrat.diagonalPointAnswerFamily
        diagonalLineAnswerFamily AnswerSymStrat.diagonalLineAnswerFamily
      simp [state_eq x, pointMeasurement_eq x, diagonalZeroCoord_eq x]
    simpa [hfail] using hgood.diagonalLineTest

/-- Build answer-valued `SliceStrategyTransport` from concrete slice strategies and
verifier-visible measurement transport.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551` and
`references/ldt-paper/self_improvement.tex:631-811`.

This constructor fills both structural fields forced by the answer-restricted
interface: averaged point compatibility follows from point-measurement transport,
and goodness follows from the answer-restricted failure profile plus state,
axis-parallel, and diagonal zero-coordinate transport. -/
noncomputable def AnswerSelfImprovementData.SliceStrategyTransport.ofMeasurementEq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k)
    (sliceStrategy : Fq params → SymStrat params ι)
    (state_eq : ∀ x, (sliceStrategy x).state = strategy.state)
    (pointMeasurement_eq :
      ∀ x,
        (sliceStrategy x).pointMeasurement =
          (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
    (axisParallelMeasurement_eq :
      ∀ x,
        (sliceStrategy x).axisParallelMeasurement.toIdxProjMeas =
          (xRestrictedAnswerSymStrat params strategy x).axisParallelMeasurement.toIdxProjMeas)
    (diagonalZeroCoord_eq :
      ∀ x ℓ,
        postprocess
            (((sliceStrategy x).diagonalMeasurement.toIdxProjMeas ℓ).toSubMeas)
            (fun f : DiagonalLinePolynomial params => f zeroCoord) =
          postprocess
            (((xRestrictedAnswerSymStrat params strategy x).diagonalMeasurement.toIdxProjMeas
              ℓ).toSubMeas)
            (fun f : DiagonalLineAnswer params => f zeroCoord)) :
    AnswerSelfImprovementData.SliceStrategyTransport params strategy eps delta gamma k
      restrictionPkg inductionPkg :=
  AnswerSelfImprovementData.SliceStrategyTransport.ofPointMeasurementEq
    params strategy eps delta gamma k restrictionPkg inductionPkg sliceStrategy state_eq
    pointMeasurement_eq
    (AnswerSelfImprovementData.SliceStrategyTransport.good_of_restrictedGood
      params strategy eps delta gamma restrictionPkg sliceStrategy state_eq
      pointMeasurement_eq axisParallelMeasurement_eq diagonalZeroCoord_eq)

/-- Assemble the slice-wise outputs feeding the answer-valued restricted-strategy
self-improvement stage into the bookkeeping object expected by answer-valued
Section 6 assembly.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551` and
`references/ldt-paper/self_improvement.tex:631-811`. -/
noncomputable def AnswerSelfImprovementData.ofSelfImprovementInInductionSection
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k)
    (hslice :
      ∀ x,
        ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
          CompletenessAtLeast strategy.state H.toSubMeas.liftLeft
            ((1 - inductionPkg.sliceError x) -
              answerSliceSelfImprovementError params restrictionPkg x) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas
              (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params H.toSubMeas)
            (answerSliceSelfImprovementError params restrictionPkg x) ∧
          BipartiteSSCRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily H.toSubMeas)
            (answerSliceSelfImprovementError params restrictionPkg x) ∧
          SDDRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily (leftPlacedSubMeas (ιB := ι) H.toSubMeas))
            (constSubMeasFamily (rightPlacedSubMeas (ιA := ι) H.toSubMeas))
            (answerSliceSelfImprovementError params restrictionPkg x) ∧
          tensorFailureExpectation strategy.state Z H.toSubMeas ≤
            answerSliceSelfImprovementError params restrictionPkg x ∧
          (∀ h : Polynomial params,
            IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h ≤ Z)) :
    AnswerSelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg := by
  classical
  let sliceProj : Fq params → ProjSubMeas (Polynomial params) ι :=
    fun x => Classical.choose (hslice x)
  let sliceWitness : Fq params → MIPStarRE.Quantum.Op ι :=
    fun x => Classical.choose (Classical.choose_spec (hslice x))
  have hslice_props :
      ∀ x,
        CompletenessAtLeast strategy.state (sliceProj x).toSubMeas.liftLeft
          ((1 - inductionPkg.sliceError x) -
            answerSliceSelfImprovementError params restrictionPkg x) ∧
        ConsRel strategy.state (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas
            (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
          (polynomialEvaluationFamily params (sliceProj x).toSubMeas)
          (answerSliceSelfImprovementError params restrictionPkg x) ∧
        BipartiteSSCRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily (sliceProj x).toSubMeas)
          (answerSliceSelfImprovementError params restrictionPkg x) ∧
        SDDRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily (leftPlacedSubMeas (ιB := ι) (sliceProj x).toSubMeas))
          (constSubMeasFamily (rightPlacedSubMeas (ιA := ι) (sliceProj x).toSubMeas))
          (answerSliceSelfImprovementError params restrictionPkg x) ∧
        tensorFailureExpectation strategy.state (sliceWitness x) (sliceProj x).toSubMeas ≤
          answerSliceSelfImprovementError params restrictionPkg x ∧
        (∀ h : Polynomial params,
          IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h ≤ sliceWitness x) := by
    intro x
    simpa [sliceProj, sliceWitness] using
      (Classical.choose_spec (Classical.choose_spec (hslice x)))
  exact
    { sliceProj := sliceProj
      sliceWitness := sliceWitness
      completeness := fun x => (hslice_props x).1
      pointConsistency := fun x => (hslice_props x).2.1
      strongSelfConsistency := fun x => (hslice_props x).2.2.1
      selfCloseness := fun x => (hslice_props x).2.2.2.1
      bounded := fun x => (hslice_props x).2.2.2.2.1
      dominatesAveragePointOperator := fun x h => (hslice_props x).2.2.2.2.2 h }

/-- Convert concrete per-slice structural data into the answer-valued Section 6
self-improvement data.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551` and
`references/ldt-paper/self_improvement.tex:631-811`.

The construction assumes ordinary slice strategies and their structural
measurement transports. It applies the theorem
`selfImprovementInInductionSection` slice-by-slice and transports its fields
back to the answer-valued restricted-slice interface via the recorded state and
point-measurement equalities. The theorem itself is currently a tracked proof
gap (#1503); this constructor does not carry the Section 9 proof debt as an
additional data record hypothesis. -/
noncomputable def AnswerSelfImprovementData.ofSliceStrategyTransport
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k)
    (sliceTransport :
      AnswerSelfImprovementData.SliceStrategyTransport params strategy eps delta gamma k
        restrictionPkg inductionPkg) :
    AnswerSelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg := by
  classical
  refine
    AnswerSelfImprovementData.ofSelfImprovementInInductionSection
      params strategy eps delta gamma k restrictionPkg inductionPkg ?_
  intro x
  let sliceStrategy := sliceTransport.sliceStrategy x
  have hconsSlice :
      ConsRel sliceStrategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas sliceStrategy.pointMeasurement)
        (polynomialEvaluationFamily params (inductionPkg.sliceMeasurement x).toSubMeas)
        (inductionPkg.sliceError x) := by
    have hcons := inductionPkg.pointConsistency x
    rw [← sliceTransport.state_eq x, ← sliceTransport.pointMeasurement_eq x] at hcons
    simpa [sliceStrategy] using hcons
  rcases selfImprovementInInductionSection params
      (sliceTransport.sliceStrategy x)
      (restrictionPkg.profile.axisParallel x)
      (restrictionPkg.profile.selfConsistency x)
      (restrictionPkg.profile.diagonal x)
      (inductionPkg.sliceError x)
      (sliceTransport.good x)
      (inductionPkg.sliceMeasurement x).toSubMeas
      hconsSlice with
    ⟨H, Z, hH⟩
  refine ⟨H, Z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hcomp := hH.completeness
    rw [sliceTransport.state_eq x] at hcomp
    simpa [answerSliceSelfImprovementError] using hcomp
  · have hpoint := hH.pointConsistency
    rw [sliceTransport.state_eq x, sliceTransport.pointMeasurement_eq x] at hpoint
    simpa [answerSliceSelfImprovementError] using hpoint
  · have hssc := hH.strongSelfConsistency
    rw [sliceTransport.state_eq x] at hssc
    simpa [answerSliceSelfImprovementError] using hssc
  · have hclose := hH.selfCloseness
    rw [sliceTransport.state_eq x] at hclose
    simpa [answerSliceSelfImprovementError] using hclose
  · have hbounded := hH.bounded
    rw [sliceTransport.state_eq x] at hbounded
    simpa [answerSliceSelfImprovementError] using hbounded
  · intro h
    simpa [sliceTransport.averagedPoint_eq x h] using hH.dominatesAveragePointOperator h

end MIPStarRE.LDT.MainInductionStep
