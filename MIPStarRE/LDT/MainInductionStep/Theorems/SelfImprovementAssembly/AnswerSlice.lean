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

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- A covariant diagonal measurement with a fixed zero polynomial outcome.

This measurement is used only as an inert diagonal component when applying the
axis-parallel/self-consistency form of self-improvement to an answer-valued
slice.  The Section 9 conclusion obtained in this way is independent of the
diagonal-line failure probability. -/
noncomputable def dummyDiagonalCovariantMeasurement
    (params : Parameters)
    [FieldModel params.q]
    (ι : Type uι) [Fintype ι] [DecidableEq ι] :
    DiagonalCovariantMeasurement params ι where
  toIdxProjMeas := fun _ =>
    ProjMeas.trivialDistinguishedOutcome (default : DiagonalLinePolynomial params)
  transportInvariant := by
    intro ℓ t
    have hdefault :
        (DiagonalLinePolynomial.reparamAtEquiv (params := params) t)
          (default : DiagonalLinePolynomial params) =
            default := by
      simp [DiagonalLinePolynomial.reparamAtEquiv]
    simp [DiagonalLine.transportMeasurement, hdefault]

/-- Forget the answer-valued diagonal alphabet of a restricted slice, replacing
it by an inert ordinary diagonal measurement.

The point, axis-parallel, state, and normalization data are unchanged.  This is
therefore sufficient for the self-improvement theorem variant whose hypotheses
are exactly the axis-parallel and point self-consistency bounds. -/
noncomputable def answerSelfImprovementCarrier
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    SymStrat params ι where
  state := strategy.state
  permInvState := strategy.permInvState
  densityFixed := strategy.densityFixed
  isNormalized := strategy.isNormalized
  pointMeasurement := strategy.pointMeasurement
  axisParallelMeasurement := strategy.axisParallelMeasurement
  diagonalMeasurement := dummyDiagonalCovariantMeasurement params ι

/-- Restrict an answer-valued diagonal-line measurement to the slice at height
`x`.

This is the answer-valued analogue of `restrictDiagonalAnswerMeasurement`.
Because the diagonal answer alphabet is the full function space on the line,
restriction is the total map
`DiagonalLineAnswer.restrictAtHeight`; no low-degree support theorem is needed
to define this slice. -/
noncomputable def restrictAnswerDiagonalAnswerMeasurement
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (x : Fq params) :
    IdxProjMeas (DiagonalLine params) (DiagonalLineAnswer params) ι :=
  fun ℓ =>
    ProjMeas.postprocess
      (strategy.diagonalMeasurement (DiagonalLine.appendAtHeight params ℓ x))
      (fun f : DiagonalLineAnswer params.next =>
        DiagonalLineAnswer.restrictAtHeight params f x)

/-- Transport covariance for the answer-valued restricted diagonal-line
measurement. -/
private theorem restrictAnswerDiagonalAnswerMeasurement_transportInvariant
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (x : Fq params) :
    DiagonalAnswerMeasurementTransportInvariant params
      (restrictAnswerDiagonalAnswerMeasurement params strategy x) := by
  intro ℓ t
  apply ProjMeas.ext
  intro a
  have htransport :=
    MIPStarRE.LDT.DiagonalAnswerCovariantMeasurement.transportInvariant
      strategy.diagonalMeasurement (DiagonalLine.appendAtHeight params ℓ x) t
  let A := (strategy.diagonalMeasurement (DiagonalLine.appendAtHeight params ℓ x)).toSubMeas
  let eNext := DiagonalLineAnswer.reparamAtEquiv (params := params.next) t
  let eSlice := DiagonalLineAnswer.reparamAtEquiv (params := params) t
  let f : DiagonalLineAnswer params.next → DiagonalLineAnswer params :=
    fun g => DiagonalLineAnswer.restrictAtHeight params g x
  have hcomm : ∀ g, f (eNext g) = eSlice (f g) := by
    intro g
    funext s
    rfl
  have hpost : postprocess (SubMeas.transport eNext A) f =
      SubMeas.transport eSlice (postprocess A f) :=
    SubMeas.postprocess_transport_equiv eNext eSlice A f f hcomm
  exact congrArg (fun M : SubMeas (DiagonalLineAnswer params) ι => M.outcome a) <| by
    simpa [restrictAnswerDiagonalAnswerMeasurement, DiagonalLine.transportMeasurement,
      ProjMeas.transport, Measurement.transport, A, eNext, eSlice, f,
      DiagonalLine.appendAtHeight_rebaseAt, htransport] using hpost

/-- The `x`-restricted strategy of an answer-valued successor strategy.

Paper origin: `references/ldt-paper/inductive_step.tex:436-455`, in the
answer-valued strategy interface used for the recursive slice call.

This is the recursive restriction map needed for a simultaneous answer-valued
form of the main induction theorem.  It preserves the state, point
measurement, axis-parallel measurement, and full answer-valued diagonal
measurement on the slice. -/
noncomputable def xRestrictedAnswerSymStratOfAnswer
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (x : Fq params) : AnswerSymStrat params ι where
  state := strategy.state
  permInvState := strategy.permInvState
  densityFixed := strategy.densityFixed
  isNormalized := strategy.isNormalized
  pointMeasurement := fun u => strategy.pointMeasurement (appendPoint params u x)
  axisParallelMeasurement :=
    (xRestrictedAnswerSymStrat params
      (answerSelfImprovementCarrier params.next strategy) x).axisParallelMeasurement
  diagonalMeasurement :=
    { toIdxProjMeas := restrictAnswerDiagonalAnswerMeasurement params strategy x
      transportInvariant :=
        restrictAnswerDiagonalAnswerMeasurement_transportInvariant params strategy x }

/-- Answer-valued slice restriction does not change the bipartite state. -/
@[simp] theorem xRestrictedAnswerSymStratOfAnswer_state
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (x : Fq params) :
    (xRestrictedAnswerSymStratOfAnswer params strategy x).state = strategy.state :=
  rfl

/-- Answer-valued slice restriction reindexes point questions by appending the
slice height. -/
@[simp] theorem xRestrictedAnswerSymStratOfAnswer_pointMeasurement_apply
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (x : Fq params)
    (u : Point params) :
    (xRestrictedAnswerSymStratOfAnswer params strategy x).pointMeasurement u =
      strategy.pointMeasurement (appendPoint params u x) :=
  rfl

/-- Answer-valued slice restriction reuses the parent normalization witness. -/
@[simp] theorem xRestrictedAnswerSymStratOfAnswer_isNormalized
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (x : Fq params) :
    (xRestrictedAnswerSymStratOfAnswer params strategy x).isNormalized =
      strategy.isNormalized :=
  rfl

/-- The diagonal measurement of an answer-valued slice is the full answer-valued
restriction of the ambient diagonal measurement. -/
@[simp] theorem xRestrictedAnswerSymStratOfAnswer_diagonalMeasurement_apply
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (x : Fq params)
    (ℓ : DiagonalLine params) :
    (xRestrictedAnswerSymStratOfAnswer params strategy x).diagonalMeasurement ℓ =
      restrictAnswerDiagonalAnswerMeasurement params strategy x ℓ :=
  rfl

/-- The averaged point-operator compatibility for answer-valued slices follows
from point-measurement transport.

Both sides unfold to the same average over `strategy.pointMeasurement
(appendPoint params u x)` once the concrete slice point measurement is identified
with `xRestrictedAnswerSymStrat`. -/
theorem AnswerSelfImprovementData.averagedPoint_eq_of_pointMeasurement_eq
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

/-- Convert the slice-wise outputs feeding the answer-valued restricted-strategy
self-improvement stage into the bookkeeping object expected by the answer-valued
successor-step construction.

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

/-- The answer-valued restricted slices directly give the slice-wise Section 9
outputs once self-improvement is applied in its axis-parallel/self-consistency
form.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551` and
`references/ldt-paper/self_improvement.tex:631-811`.

The ordinary carrier used in the proof keeps the slice state, point
measurement, and axis-parallel measurement, and replaces only the diagonal
measurement by an inert covariant measurement.  This is sufficient because the
called self-improvement theorem consumes only the axis-parallel and point
self-consistency bounds. -/
theorem AnswerSelfImprovementData.slice_outputs_ofAnswerCarrier
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k) :
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
          IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h ≤ Z) := by
  classical
  intro x
  let answerSlice := xRestrictedAnswerSymStrat params strategy x
  let carrier := answerSelfImprovementCarrier params answerSlice
  have haxis :
      carrier.axisParallelFailureProbability ≤ restrictionPkg.profile.axisParallel x := by
    have hfail :
        carrier.axisParallelFailureProbability =
          answerSlice.axisParallelFailureProbability := by
      unfold SymStrat.axisParallelFailureProbability
        AnswerSymStrat.axisParallelFailureProbability
        axisParallelPointAnswerFamily AnswerSymStrat.axisParallelPointAnswerFamily
        axisParallelLineAnswerFamily AnswerSymStrat.axisParallelLineAnswerFamily
      simp [carrier, answerSelfImprovementCarrier]
    simpa [hfail] using (restrictionPkg.profile.restrictedGood x).axisParallelTest
  have hself :
      carrier.selfConsistencyFailureProbability ≤
        restrictionPkg.profile.selfConsistency x := by
    have hfail :
        carrier.selfConsistencyFailureProbability =
          answerSlice.selfConsistencyFailureProbability := by
      unfold SymStrat.selfConsistencyFailureProbability
        AnswerSymStrat.selfConsistencyFailureProbability
      simp [carrier, answerSelfImprovementCarrier]
    simpa [hfail] using (restrictionPkg.profile.restrictedGood x).selfConsistencyTest
  have hconsCarrier :
      ConsRel carrier.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas carrier.pointMeasurement)
        (polynomialEvaluationFamily params (inductionPkg.sliceMeasurement x).toSubMeas)
        (inductionPkg.sliceError x) := by
    simpa [carrier, answerSelfImprovementCarrier, answerSlice] using
      inductionPkg.pointConsistency x
  rcases selfImprovementInInductionSection_of_axisParallel_selfConsistency
      params carrier
      (restrictionPkg.profile.axisParallel x)
      (restrictionPkg.profile.selfConsistency x)
      (restrictionPkg.profile.diagonal x)
      (inductionPkg.sliceError x)
      haxis hself
      (inductionPkg.sliceMeasurement x)
      hconsCarrier with
    ⟨H, Z, hH⟩
  refine ⟨H, Z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [carrier, answerSelfImprovementCarrier, answerSlice,
      answerSliceSelfImprovementError] using hH.completeness
  · simpa [carrier, answerSelfImprovementCarrier, answerSlice,
      answerSliceSelfImprovementError] using hH.pointConsistency
  · simpa [carrier, answerSelfImprovementCarrier, answerSlice,
      answerSliceSelfImprovementError] using hH.strongSelfConsistency
  · simpa [carrier, answerSelfImprovementCarrier, answerSlice,
      answerSliceSelfImprovementError] using hH.selfCloseness
  · simpa [carrier, answerSelfImprovementCarrier, answerSlice,
      answerSliceSelfImprovementError] using hH.bounded
  · intro h
    let sliceStrategy : Fq params → SymStrat params ι :=
      fun y => answerSelfImprovementCarrier params (xRestrictedAnswerSymStrat params strategy y)
    have havg_all :=
      AnswerSelfImprovementData.averagedPoint_eq_of_pointMeasurement_eq
        params strategy sliceStrategy (by intro y; rfl)
    have havg :
        IdxPolyFamily.averagedPointEvaluationOperator carrier h =
          IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h := by
      simpa [sliceStrategy, carrier, answerSlice] using havg_all x h
    simpa [havg] using hH.dominatesAveragePointOperator h

/-- Construct the answer-valued Section 6 self-improvement data directly from
the answer-valued restricted slices.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551` and
`references/ldt-paper/self_improvement.tex:631-811`.

This removes the ordinary slice-realization assumption from the
self-improvement stage.  The construction uses the ordinary carrier only as a
device for invoking the Section 9 theorem in the form whose hypotheses are the
axis-parallel and point self-consistency estimates. -/
noncomputable def AnswerSelfImprovementData.ofAnswerCarrier
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k) :
    AnswerSelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg := by
  classical
  exact
    AnswerSelfImprovementData.ofSelfImprovementInInductionSection
      params strategy eps delta gamma k restrictionPkg inductionPkg
      (AnswerSelfImprovementData.slice_outputs_ofAnswerCarrier
        params strategy eps delta gamma k restrictionPkg inductionPkg)

end MIPStarRE.LDT.MainInductionStep
