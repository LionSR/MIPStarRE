import MIPStarRE.LDT.MainInductionStep.Theorems.SelfImprovementBridge.Core

/-!
# Section 6 — Answer-Valued Self-Improvement Slice Bridge

This file contains the answer-valued analogues of the Section 6 slice bridge
constructors.  The ordinary bridge, including `selfImprovementInInductionSection`,
lives in `SelfImprovementBridge.Core` and is imported here so that the
answer-valued package can reuse the same Section 9 self-improvement theorem.

## References

- `blueprint/src/chapter/ch10_induction.tex`
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Bridge inputs for producing the answer-valued self-improvement package from
honest per-slice symmetric strategies.

The answer-valued restriction `xRestrictedAnswerSymStrat` has the paper-faithful
answer-valued diagonal interface, while the existing Section 9 self-improvement
theorem is stated for ordinary `SymStrat`s.  This structure records honest
ordinary slice strategies on which Section 9 can run, together with the state
and point-measurement transports needed to move the resulting conclusions back
to the answer-valued restricted bookkeeping. -/
structure AnswerSelfImprovementPackage.SliceBridgeInputs
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionPackage params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionPackage params strategy eps delta gamma restrictionPkg k) where
  /-- Honest symmetric strategies realizing the answer-restricted slice interfaces. -/
  sliceStrategy : Fq params → SymStrat params ι
  /-- Each honest slice strategy uses the ambient state. -/
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
  /-- The honest slice strategy is good with the answer-restricted failure profile. -/
  good :
    ∀ x,
      (sliceStrategy x).IsGood
        (restrictionPkg.profile.axisParallel x)
        (restrictionPkg.profile.selfConsistency x)
        (restrictionPkg.profile.diagonal x)
  /-- The remaining Section 9 bridge inputs for each honest slice strategy. -/
  bridgeInputs :
    ∀ x,
      SelfImprovement.SelfImprovementBridgeInputs params (sliceStrategy x)
        (restrictionPkg.profile.axisParallel x)
        (restrictionPkg.profile.selfConsistency x)
        (inductionPkg.sliceError x)

/-- The averaged point-operator compatibility for answer-valued slices follows
from point-measurement transport.

Both sides unfold to the same average over `strategy.pointMeasurement
(appendPoint params u x)` once the honest slice point measurement is identified
with `xRestrictedAnswerSymStrat`. -/
theorem AnswerSelfImprovementPackage.SliceBridgeInputs.averagedPoint_eq_of_pointMeasurement_eq
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

/-- Build answer-valued `SliceBridgeInputs` without separately assuming averaged
point-operator compatibility.

The structural averaged-point field is derived from `pointMeasurement_eq`; the
remaining inputs are the honest slice strategies, their state transport,
restricted-profile goodness, and their Section 9 bridge packages. -/
noncomputable def AnswerSelfImprovementPackage.SliceBridgeInputs.ofPointMeasurementEq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionPackage params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionPackage params strategy eps delta gamma restrictionPkg k)
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
          (restrictionPkg.profile.diagonal x))
    (bridgeInputs :
      ∀ x,
        SelfImprovement.SelfImprovementBridgeInputs params (sliceStrategy x)
          (restrictionPkg.profile.axisParallel x)
          (restrictionPkg.profile.selfConsistency x)
          (inductionPkg.sliceError x)) :
    AnswerSelfImprovementPackage.SliceBridgeInputs params strategy eps delta gamma k
      restrictionPkg inductionPkg where
  sliceStrategy := sliceStrategy
  state_eq := state_eq
  pointMeasurement_eq := pointMeasurement_eq
  averagedPoint_eq :=
    AnswerSelfImprovementPackage.SliceBridgeInputs.averagedPoint_eq_of_pointMeasurement_eq
      params strategy sliceStrategy pointMeasurement_eq
  good := good
  bridgeInputs := bridgeInputs

/-- Transport answer-restricted goodness to an honest slice strategy once the
state and verifier-visible measurements agree with `xRestrictedAnswerSymStrat`.

The diagonal compatibility is stated only after postprocessing both diagonal
answer alphabets to their `zeroCoord` value; this is the comparison used by the
LDT diagonal subtest and avoids claiming a false equality between
`DiagonalLinePolynomial` and `DiagonalLineAnswer` families. -/
theorem AnswerSelfImprovementPackage.SliceBridgeInputs.good_of_restrictedGood
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (restrictionPkg : AnswerSliceRestrictionPackage params strategy eps delta gamma)
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

/-- Build answer-valued `SliceBridgeInputs` from honest slice strategies,
verifier-visible measurement transport, and Section 9 bridge inputs.

This constructor fills both structural fields forced by the answer-restricted
interface: averaged point compatibility follows from point-measurement transport,
and goodness follows from the answer-restricted failure profile plus state,
axis-parallel, and diagonal zero-coordinate transport. -/
noncomputable def AnswerSelfImprovementPackage.SliceBridgeInputs.ofMeasurementEq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionPackage params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionPackage params strategy eps delta gamma restrictionPkg k)
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
            (fun f : DiagonalLineAnswer params => f zeroCoord))
    (bridgeInputs :
      ∀ x,
        SelfImprovement.SelfImprovementBridgeInputs params (sliceStrategy x)
          (restrictionPkg.profile.axisParallel x)
          (restrictionPkg.profile.selfConsistency x)
          (inductionPkg.sliceError x)) :
    AnswerSelfImprovementPackage.SliceBridgeInputs params strategy eps delta gamma k
      restrictionPkg inductionPkg :=
  AnswerSelfImprovementPackage.SliceBridgeInputs.ofPointMeasurementEq
    params strategy eps delta gamma k restrictionPkg inductionPkg sliceStrategy state_eq
    pointMeasurement_eq
    (AnswerSelfImprovementPackage.SliceBridgeInputs.good_of_restrictedGood
      params strategy eps delta gamma restrictionPkg sliceStrategy state_eq
      pointMeasurement_eq axisParallelMeasurement_eq diagonalZeroCoord_eq)
    bridgeInputs

/-- Build answer-valued `SliceBridgeInputs` from honest slice strategies and the
constructive orthonormalization repair producer.

As in the ordinary slice bridge, the spectral part of the orthonormalization
input is supplied by the closed source-almost-projective spectral truncation
theorem.  The caller supplies only the locality-preserving repair producer,
besides the helper strong self-consistency and final-fields inputs. -/
noncomputable def AnswerSelfImprovementPackage.SliceBridgeInputs.ofOrthonormalizationRepair
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionPackage params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionPackage params strategy eps delta gamma restrictionPkg k)
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
            (fun f : DiagonalLineAnswer params => f zeroCoord))
    (helperStrongSelfConsistency :
      ∀ x,
        SelfImprovement.HelperStrongSelfConsistencyInput params (sliceStrategy x)
          (restrictionPkg.profile.axisParallel x)
          (restrictionPkg.profile.selfConsistency x))
    (repair :
      ∀ x,
        SelfImprovement.OrthonormalizationRepairProducer params (sliceStrategy x)
          (restrictionPkg.profile.axisParallel x)
          (restrictionPkg.profile.selfConsistency x))
    (finalFields :
      ∀ x,
        SelfImprovement.FinalFieldsInput params (sliceStrategy x)
          (restrictionPkg.profile.axisParallel x)
          (restrictionPkg.profile.selfConsistency x)
          (inductionPkg.sliceError x)) :
    AnswerSelfImprovementPackage.SliceBridgeInputs params strategy eps delta gamma k
      restrictionPkg inductionPkg :=
  AnswerSelfImprovementPackage.SliceBridgeInputs.ofMeasurementEq
    params strategy eps delta gamma k restrictionPkg inductionPkg sliceStrategy state_eq
    pointMeasurement_eq axisParallelMeasurement_eq diagonalZeroCoord_eq
    (fun x =>
      { helperStrongSelfConsistency := helperStrongSelfConsistency x
        orthonormalization :=
          SelfImprovement.orthonormalizationInput_of_producers
            SelfImprovement.orthonormalizationSpectralProducer_of_sourceAlmostProjective
            (repair x)
        finalFields := finalFields x })

/-- Package the slice-wise outputs feeding the answer-valued restricted-strategy
self-improvement stage into the bookkeeping object expected by answer-valued
Section 6 assembly. -/
noncomputable def AnswerSelfImprovementPackage.ofSelfImprovementInInductionSection
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionPackage params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionPackage params strategy eps delta gamma restrictionPkg k)
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
    AnswerSelfImprovementPackage params strategy eps delta gamma k restrictionPkg inductionPkg := by
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

/-- Convert honest per-slice Section 9 bridge inputs into the answer-valued
Section 6 self-improvement package.

The construction assumes ordinary slice strategies and their Section 9 bridge
inputs. It applies the conditional measurement-input theorem
`selfImprovementInInductionSection_ofMeasurement` slice-by-slice and transports
its fields back to the answer-valued restricted-slice interface via the recorded
state and point-measurement equalities. At each slice the package supplies the
complete measurement `inductionPkg.sliceMeasurement x`; the submeasurement-input
theorem remains the tracked obligation in #1503. -/
noncomputable def AnswerSelfImprovementPackage.ofSliceBridgeInputs
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionPackage params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionPackage params strategy eps delta gamma restrictionPkg k)
    (hbridge :
      AnswerSelfImprovementPackage.SliceBridgeInputs params strategy eps delta gamma k
        restrictionPkg inductionPkg) :
    AnswerSelfImprovementPackage params strategy eps delta gamma k restrictionPkg inductionPkg := by
  classical
  refine
    AnswerSelfImprovementPackage.ofSelfImprovementInInductionSection
      params strategy eps delta gamma k restrictionPkg inductionPkg ?_
  intro x
  let sliceStrategy := hbridge.sliceStrategy x
  have hconsSlice :
      ConsRel sliceStrategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas sliceStrategy.pointMeasurement)
        (polynomialEvaluationFamily params (inductionPkg.sliceMeasurement x).toSubMeas)
        (inductionPkg.sliceError x) := by
    have hcons := inductionPkg.pointConsistency x
    rw [← hbridge.state_eq x, ← hbridge.pointMeasurement_eq x] at hcons
    simpa [sliceStrategy] using hcons
  rcases selfImprovementInInductionSection_ofMeasurement params (hbridge.sliceStrategy x)
      (restrictionPkg.profile.axisParallel x)
      (restrictionPkg.profile.selfConsistency x)
      (restrictionPkg.profile.diagonal x)
      (inductionPkg.sliceError x)
      (hbridge.bridgeInputs x).helperStrongSelfConsistency
      (hbridge.bridgeInputs x).orthonormalization
      (hbridge.bridgeInputs x).finalFields
      (hbridge.good x)
      (inductionPkg.sliceMeasurement x).toSubMeas
      (inductionPkg.sliceMeasurement x)
      rfl
      hconsSlice with
    ⟨H, Z, hH⟩
  refine ⟨H, Z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hcomp := hH.completeness
    rw [hbridge.state_eq x] at hcomp
    simpa [answerSliceSelfImprovementError] using hcomp
  · have hpoint := hH.pointConsistency
    rw [hbridge.state_eq x, hbridge.pointMeasurement_eq x] at hpoint
    simpa [answerSliceSelfImprovementError] using hpoint
  · have hssc := hH.strongSelfConsistency
    rw [hbridge.state_eq x] at hssc
    simpa [answerSliceSelfImprovementError] using hssc
  · have hclose := hH.selfCloseness
    rw [hbridge.state_eq x] at hclose
    simpa [answerSliceSelfImprovementError] using hclose
  · have hbounded := hH.bounded
    rw [hbridge.state_eq x] at hbounded
    simpa [answerSliceSelfImprovementError] using hbounded
  · intro h
    simpa [hbridge.averagedPoint_eq x h] using hH.dominatesAveragePointOperator h

end MIPStarRE.LDT.MainInductionStep
