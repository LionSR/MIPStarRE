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

/-- Transport data for producing the answer-valued self-improvement data from
concrete per-slice symmetric strategies.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551` and
`references/ldt-paper/self_improvement.tex:631-811`; this is the answer-valued
restricted-slice interface for the same self-improvement step.

The answer-valued restriction `xRestrictedAnswerSymStrat` has the paper-faithful
answer-valued diagonal interface, while the existing Section 9 self-improvement
theorem is stated for ordinary `SymStrat`s.  This structure records the
stronger route through concrete ordinary slice strategies, together with the
state and point-measurement transports needed to move the resulting conclusions
back to the answer-valued restricted bookkeeping.

The legacy restricted strategy `xRestrictedStrategy` is not such an ordinary
slice strategy.  It is a `RestrictedSymStrat`, and its diagonal measurement is
only the degree-bounded re-embedding of the sampled base-point value.  Thus it
does not by itself supply the transport-covariant diagonal measurement required
by `SymStrat`.

An ordinary covariant realization is not a formal relabelling of the
answer-valued strategy.  Diagonal covariance after rebasing a line would force
the ordinary polynomial outcome to reproduce all values of the function answer,
not only the value at `zeroCoord` used by the diagonal test.  Thus this route
requires a genuine low-degree support/interpolation theorem for the
answer-valued diagonal measurement.  In the absence of such a theorem, the
mathematically faithful remaining target is an induction-section
self-improvement theorem stated directly for `AnswerSymStrat`.

The Section 9 analytic proof debt is not stored in this record.  The data record
constructor below calls the paper-facing theorem
`selfImprovementInInductionSection`; its proof applies the Section 9 theorem and
then transports the output estimates to the answer-valued induction notation. -/
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

/-- Concrete answer-valued slice strategies give the slice-wise Section 9
outputs used by the answer-valued self-improvement data.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551` and
`references/ldt-paper/self_improvement.tex:631-811`.

This is an internal transport theorem.  It applies
`selfImprovementInInductionSection` to each ordinary slice strategy supplied by
`SliceStrategyTransport`, and then rewrites the state, point-measurement, and
averaged-point conclusions back into the answer-restricted notation of the
successor step. -/
theorem AnswerSelfImprovementData.slice_outputs_ofSliceStrategyTransport
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
      (inductionPkg.sliceMeasurement x)
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
      AnswerSelfImprovementData.SliceStrategyTransport.averagedPoint_eq_of_pointMeasurement_eq
        params strategy sliceStrategy (by intro y; rfl)
    have havg :
        IdxPolyFamily.averagedPointEvaluationOperator carrier h =
          IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h := by
      simpa [sliceStrategy, carrier, answerSlice] using havg_all x h
    simpa [havg] using hH.dominatesAveragePointOperator h

/-- Convert concrete per-slice structural data into the answer-valued Section 6
self-improvement data.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551` and
`references/ldt-paper/self_improvement.tex:631-811`.

The construction assumes ordinary slice strategies and their structural
measurement transports. It applies the theorem
`selfImprovementInInductionSection` slice-by-slice and transports its fields
back to the answer-valued restricted-slice interface via the recorded state and
point-measurement equalities. -/
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
  exact
    AnswerSelfImprovementData.ofSelfImprovementInInductionSection
      params strategy eps delta gamma k restrictionPkg inductionPkg
      (AnswerSelfImprovementData.slice_outputs_ofSliceStrategyTransport
        params strategy eps delta gamma k restrictionPkg inductionPkg sliceTransport)

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
