import MIPStarRE.LDT.Test.MainTheorem.OrdinaryRestriction

/-!
# Answer-valued restricted-slice recursion

Statement-preserving slice of `MIPStarRE.LDT.Test.MainTheorem`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-! ### Answer-valued (preferred) successor route

The declarations in this section form the **answer-valued (preferred) successor
route**, which uses `xRestrictedAnswerSymStrat` as the per-slice recursive
strategy.  This route is preferred over the ordinary successor route because:

* `xRestrictedAnswerSymStrat` preserves the full answer-valued diagonal
  restriction and its transport invariant, so the restricted strategy can serve
  as an honest input to Section 9 self-improvement.
* It maps directly to the paper's answer-register construction, with the
  diagonal outcome function carried end-to-end rather than truncated to
  `zeroCoord`.

These declarations feed into the
`MainFormalRolePackageBranchResidual.answerSuccessor` constructor.  The
ordinary route (`MainFormalRolePackageBranchResidual.successor`) is retained as
a compatibility path for callers already working with ordinary restriction data.
-/

/-- Answer-valued successor-case weighted restricted-axis input for the
role-register symmetrization used by `mainFormal`. -/
def MainFormalSuccessorAnswerAxisWeightedBound (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error) : Prop :=
  avgOver (uniformDistribution (Fq params))
    (fun x => MainInductionStep.sliceTransverseDirectionWeight params *
      (MainInductionStep.xRestrictedAnswerSymStrat params
        strategy.strategySymmetrization x).axisParallelFailureProbability) ≤
    3 * eps

/-- Answer-valued successor-case weighted restricted-diagonal input for the
role-register symmetrization used by `mainFormal`. -/
def MainFormalSuccessorAnswerDiagonalWeightedBound (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error) : Prop :=
  avgOver (uniformDistribution (Fq params))
    (fun x => MainInductionStep.sliceTransverseDirectionWeight params *
      (MainInductionStep.xRestrictedAnswerSymStrat params
        strategy.strategySymmetrization x).diagonalFailureProbability) ≤
    3 * eps

/-- The answer-valued restricted-probability package on the role-register
symmetrization used in the successor branch of `mainFormal`. -/
noncomputable def mainFormalSuccessorAnswerRestrictionPackage
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (haxisWeightedBound : MainFormalSuccessorAnswerAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound :
      MainFormalSuccessorAnswerDiagonalWeightedBound params strategy eps) :
    MainInductionStep.AnswerSliceRestrictionPackage params
      strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps) :=
  MainInductionStep.answerMainInductionPublicRestrictionPackage
    params strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps)
    (SameSpaceProjStrat.strategySymmetrization_isGood_three_mul
      (strategy := strategy) (eps := eps) hpass)
    haxisWeightedBound hdiagonalWeightedBound

/-- Successor-case recursive slice witnesses for answer-valued restricted
strategies. -/
def MainFormalSuccessorAnswerRecursiveSlices (params : Parameters)
    [FieldModel.{0} params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (haxisWeightedBound : MainFormalSuccessorAnswerAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound :
      MainFormalSuccessorAnswerDiagonalWeightedBound params strategy eps) : Prop :=
  let hrestrict :=
    mainFormalSuccessorAnswerRestrictionPackage params strategy eps hpass
      haxisWeightedBound hdiagonalWeightedBound
  ∀ x,
    ∃ error : Error, ∃ G : Measurement (Polynomial params) (Role × ι),
      ConsRel (strategy.strategySymmetrization).state
        (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas
          (MainInductionStep.xRestrictedAnswerSymStrat params
            strategy.strategySymmetrization x).pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        error ∧
      error ≤
        MainInductionStep.mainInductionError params k
          (hrestrict.profile.axisParallel x)
          (hrestrict.profile.selfConsistency x)
          (hrestrict.profile.diagonal x)

/-- A Section 6 answer-valued per-slice induction package supplies the
answer-side recursive slice witnesses needed by the `mainFormal` successor
boundary.

As in the ordinary-register constructor, this only exposes the package fields at
the Test-level boundary; the predecessor induction package must come from a
non-circular induction hypothesis. -/
theorem mainFormalSuccessorAnswerRecursiveSlices_ofInductionPackage
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (haxisWeightedBound : MainFormalSuccessorAnswerAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound :
      MainFormalSuccessorAnswerDiagonalWeightedBound params strategy eps)
    (hinduction :
      MainInductionStep.AnswerPerSliceInductionPackage params
        strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps)
        (mainFormalSuccessorAnswerRestrictionPackage params strategy eps hpass
          haxisWeightedBound hdiagonalWeightedBound)
        k) :
    MainFormalSuccessorAnswerRecursiveSlices params strategy eps hpass k
      haxisWeightedBound hdiagonalWeightedBound := by
  intro x
  exact
    ⟨hinduction.sliceError x, hinduction.sliceMeasurement x,
      hinduction.pointConsistency x, hinduction.error_le x⟩


/-- Answer-side slice-recursion bridge data for the successor branch of
`mainFormal`.

This is the answer-register counterpart of
`MainFormalSuccessorRecursiveSliceData`.  For each field element `x`, it
packages a same-space projective strategy on the role-register space together
with compatibility proofs connecting its point and line measurements on both
registers to the answer-restricted strategy.  The diagonal-line measurements
have different answer alphabets on the two sides, so this package records the
common zero-coordinate readout rather than a false equality between the full
measurement families.

When supplied together with a recursive induction hypothesis (see
`mainFormalSuccessorAnswerRecursiveSlices_ofSliceData`), this data can close the
`MainFormalSuccessorAnswerRecursiveSlices` requirement needed by
`MainFormalSuccessorAnswerBoundary`.  The proof currently consumes only the
state and Alice point-measurement fields; the Bob-side, axis, and diagonal
compatibility fields are carried so a later wiring of the recursive induction
call can make `slicePasses` depend on the actual restricted answer slice. -/
structure MainFormalSuccessorAnswerRecursiveSliceData (params : Parameters)
    [FieldModel.{0} params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) where
  /-- For each field element `x`, a same-space projective strategy on the
  role-register space that captures the answer-restricted slice at `x`. -/
  sliceStrategy : Fq params → SameSpaceProjStrat params (Role × ι)
  /-- The slice strategy shares the symmetrization's bipartite state. -/
  sliceState_eq : ∀ x, (sliceStrategy x).state = (strategy.strategySymmetrization).state
  /-- The slice strategy's Alice point measurement matches the answer-restricted
  point measurement from the main induction step. -/
  slicePoint_eq : ∀ x,
    (sliceStrategy x).pointMeasurementA =
    (MainInductionStep.xRestrictedAnswerSymStrat params
      strategy.strategySymmetrization x).pointMeasurement
  /-- The slice strategy's Alice axis-parallel measurement has the same
  underlying indexed projective measurements as the answer-restricted slice. -/
  sliceAxisParallelA_eq : ∀ x,
    (sliceStrategy x).axisParallelMeasurementA.toIdxProjMeas =
    (MainInductionStep.xRestrictedAnswerSymStrat params
      strategy.strategySymmetrization x).axisParallelMeasurement.toIdxProjMeas
  /-- The slice strategy's Alice diagonal measurement agrees with the
  answer-restricted slice after both line-answer alphabets are evaluated at the
  base point.  The full diagonal families have different answer types
  (`DiagonalLinePolynomial` versus `DiagonalLineAnswer`), so the common
  zero-coordinate readout is the compatible comparison available here. -/
  sliceDiagonalA_zeroCoord_eq : ∀ x ℓ,
    postprocess
        (((sliceStrategy x).diagonalMeasurementA.toIdxProjMeas ℓ).toSubMeas)
        (fun f : DiagonalLinePolynomial params => f zeroCoord) =
      postprocess
        (((MainInductionStep.xRestrictedAnswerSymStrat params
          strategy.strategySymmetrization x).diagonalMeasurement.toIdxProjMeas ℓ).toSubMeas)
        (fun f : DiagonalLineAnswer params => f zeroCoord)
  /-- The slice strategy's Bob point measurement matches the same
  answer-restricted point measurement.  The answer-restricted interface is a
  symmetric one-register strategy, so the same restricted point family is the
  target for both registers of the same-space slice strategy. -/
  slicePointB_eq : ∀ x,
    (sliceStrategy x).pointMeasurementB =
    (MainInductionStep.xRestrictedAnswerSymStrat params
      strategy.strategySymmetrization x).pointMeasurement
  /-- The slice strategy's Bob axis-parallel measurement has the same underlying
  indexed projective measurements as the answer-restricted slice. -/
  sliceAxisParallelB_eq : ∀ x,
    (sliceStrategy x).axisParallelMeasurementB.toIdxProjMeas =
    (MainInductionStep.xRestrictedAnswerSymStrat params
      strategy.strategySymmetrization x).axisParallelMeasurement.toIdxProjMeas
  /-- The slice strategy's Bob diagonal measurement agrees with the
  answer-restricted slice after both line-answer alphabets are evaluated at the
  base point. -/
  sliceDiagonalB_zeroCoord_eq : ∀ x ℓ,
    postprocess
        (((sliceStrategy x).diagonalMeasurementB.toIdxProjMeas ℓ).toSubMeas)
        (fun f : DiagonalLinePolynomial params => f zeroCoord) =
      postprocess
        (((MainInductionStep.xRestrictedAnswerSymStrat params
          strategy.strategySymmetrization x).diagonalMeasurement.toIdxProjMeas ℓ).toSubMeas)
        (fun f : DiagonalLineAnswer params => f zeroCoord)
  /-- Each slice strategy passes LDT with the common symmetrized error `3 * eps`.

  This remains an externally supplied passing hypothesis.  The fields above now
  constrain the shared state, Alice and Bob point measurements, Alice and Bob
  axis-parallel measurements, and the common diagonal zero-coordinate readout on
  both registers.  They do not transport the same-space strategy's
  `permInvState` or `densityFixed` proofs, and they intentionally avoid a false
  full diagonal-family equality between `DiagonalLinePolynomial` and
  `DiagonalLineAnswer`. -/
  slicePasses : ∀ x, (sliceStrategy x).PassesLowIndividualDegreeTest (3 * eps)

/-- Convert per-slice answer-register induction-hypothesis data into a
`MainFormalSuccessorAnswerRecursiveSlices` witness.

This is the abstract induction-step lemma for #1038.  Given the honest
`MainFormalSuccessorAnswerRecursiveSliceData` together with a recursive induction
hypothesis that delivers `mainInductionError`-bounded polynomial measurements
for each slice strategy, this rewrites the state and point-measurement
compatibilities to produce the exact `MainFormalSuccessorAnswerRecursiveSlices`
field needed by `MainFormalSuccessorAnswerBoundary`.

The additional Bob-side, axis-parallel, and diagonal readout compatibility
fields in `MainFormalSuccessorAnswerRecursiveSliceData` are not needed for this
point-consistency target yet; they are retained by the data package so the later
recursive-call wiring can require `slicePasses` for slices whose line
measurements are pinned to the answer restriction on both registers.

The induction hypothesis `hrecSlice` mirrors what the answer-valued
`mainInductionPublicWrapper` (or, equivalently, a recursive call to
`mainFormal`) returns for the predecessor dimension: a polynomial measurement
on the role-register space with consistency bounded by the main induction error
evaluated at the answer-restricted-profile bounds. -/
theorem mainFormalSuccessorAnswerRecursiveSlices_ofSliceData
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (haxisWeightedBound : MainFormalSuccessorAnswerAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound :
      MainFormalSuccessorAnswerDiagonalWeightedBound params strategy eps)
    (sliceData : MainFormalSuccessorAnswerRecursiveSliceData params strategy eps hpass)
    (hrecSlice : ∀ (x : Fq params),
      ∃ error : Error, ∃ G : Measurement (Polynomial params) (Role × ι),
        ConsRel (sliceData.sliceStrategy x).state
          (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas (sliceData.sliceStrategy x).pointMeasurementA)
          (polynomialEvaluationFamily params G.toSubMeas)
          error ∧
        error ≤
          let hrestrict :=
            mainFormalSuccessorAnswerRestrictionPackage params strategy eps hpass
              haxisWeightedBound hdiagonalWeightedBound
          MainInductionStep.mainInductionError params k
            (hrestrict.profile.axisParallel x)
            (hrestrict.profile.selfConsistency x)
            (hrestrict.profile.diagonal x)) :
    MainFormalSuccessorAnswerRecursiveSlices params strategy eps hpass k
      haxisWeightedBound hdiagonalWeightedBound := by
  intro x
  rcases hrecSlice x with ⟨error, G, hG, herr⟩
  refine ⟨error, G, ?_, herr⟩
  -- Rewrite the state and point measurement using the slice-data compatibilities
  simpa [sliceData.sliceState_eq x, sliceData.slicePoint_eq x] using hG
/-- Successor-case answer-valued restricted-strategy self-improvement producer. -/
def MainFormalSuccessorAnswerSelfImprovementProducer (params : Parameters)
    [FieldModel.{0} params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (haxisWeightedBound : MainFormalSuccessorAnswerAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound :
      MainFormalSuccessorAnswerDiagonalWeightedBound params strategy eps) : Type _ :=
  let hrestrict :=
    mainFormalSuccessorAnswerRestrictionPackage params strategy eps hpass
      haxisWeightedBound hdiagonalWeightedBound
  ∀ hinduction :
    MainInductionStep.AnswerPerSliceInductionPackage params
      strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps) hrestrict k,
    MainInductionStep.AnswerSelfImprovementPackage params
      strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps) k
      hrestrict hinduction

/-- Answer-valued successor-case bridge inputs for the restricted-strategy
self-improvement producer.

This is the answer-register counterpart of
`MainFormalSuccessorSelfImprovementBridgeInputs`: for each possible answer-side
per-slice induction package, callers supply the narrow
`AnswerSelfImprovementPackage.SliceBridgeInputs` assumptions. -/
def MainFormalSuccessorAnswerSelfImprovementBridgeInputs (params : Parameters)
    [FieldModel.{0} params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (haxisWeightedBound : MainFormalSuccessorAnswerAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound :
      MainFormalSuccessorAnswerDiagonalWeightedBound params strategy eps) : Type _ :=
  let hrestrict :=
    mainFormalSuccessorAnswerRestrictionPackage params strategy eps hpass
      haxisWeightedBound hdiagonalWeightedBound
  ∀ hinduction :
    MainInductionStep.AnswerPerSliceInductionPackage params
      strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps) hrestrict k,
    MainInductionStep.AnswerSelfImprovementPackage.SliceBridgeInputs params
      strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps) k
      hrestrict hinduction

/-- Convert answer-valued successor-case bridge inputs into the self-improvement
producer expected by the public answer-valued Section 6 boundary wrapper. -/
noncomputable def mainFormalSuccessorAnswerSelfImprovementProducer_ofBridgeInputs
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (haxisWeightedBound : MainFormalSuccessorAnswerAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound :
      MainFormalSuccessorAnswerDiagonalWeightedBound params strategy eps)
    (hbridge :
      MainFormalSuccessorAnswerSelfImprovementBridgeInputs params strategy eps hpass k
        haxisWeightedBound hdiagonalWeightedBound) :
    MainFormalSuccessorAnswerSelfImprovementProducer params strategy eps hpass k
      haxisWeightedBound hdiagonalWeightedBound := by
  let hrestrict :=
    mainFormalSuccessorAnswerRestrictionPackage params strategy eps hpass
      haxisWeightedBound hdiagonalWeightedBound
  intro hinduction
  exact
    MainInductionStep.AnswerSelfImprovementPackage.ofSliceBridgeInputs params
      strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps) k
      hrestrict hinduction (hbridge hinduction)

/-- Answer-valued successor-case Section 6 boundary inputs for `mainFormal`. -/
structure MainFormalSuccessorAnswerBoundary (params : Parameters)
    [FieldModel.{0} params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ) where
  axisWeightedBound :
    MainFormalSuccessorAnswerAxisWeightedBound params strategy eps
  diagonalWeightedBound :
    MainFormalSuccessorAnswerDiagonalWeightedBound params strategy eps
  recursiveSlices :
    MainFormalSuccessorAnswerRecursiveSlices params strategy eps hpass k
      axisWeightedBound diagonalWeightedBound
  selfImprovementProducer :
    MainFormalSuccessorAnswerSelfImprovementProducer params strategy eps hpass k
      axisWeightedBound diagonalWeightedBound

/-- The answer-valued restricted-probabilities theorem supplies the successor-case
weighted axis-parallel input. -/
theorem mainFormalSuccessorAnswerAxisWeightedBound_ofPass
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    MainFormalSuccessorAnswerAxisWeightedBound params strategy eps :=
  MainInductionStep.answer_weighted_axisParallel_bound params
    strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps)
    (SameSpaceProjStrat.strategySymmetrization_isGood_three_mul
      (strategy := strategy) (eps := eps) hpass)

/-- The answer-valued restricted-probabilities theorem supplies the successor-case
weighted diagonal-line input. -/
theorem mainFormalSuccessorAnswerDiagonalWeightedBound_ofPass
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    MainFormalSuccessorAnswerDiagonalWeightedBound params strategy eps :=
  MainInductionStep.answer_weighted_diagonal_bound params
    strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps)
    (SameSpaceProjStrat.strategySymmetrization_isGood_three_mul
      (strategy := strategy) (eps := eps) hpass)

/-- Build the answer-valued successor boundary once the two still-external slice
recursion and restricted-strategy self-improvement inputs are supplied. -/
def mainFormalSuccessorAnswerBoundary_ofRecursiveSelfImprovement
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (hrec : MainFormalSuccessorAnswerRecursiveSlices params strategy eps hpass k
      (mainFormalSuccessorAnswerAxisWeightedBound_ofPass params strategy eps hpass)
      (mainFormalSuccessorAnswerDiagonalWeightedBound_ofPass params strategy eps hpass))
    (hself : MainFormalSuccessorAnswerSelfImprovementProducer params strategy eps hpass k
      (mainFormalSuccessorAnswerAxisWeightedBound_ofPass params strategy eps hpass)
      (mainFormalSuccessorAnswerDiagonalWeightedBound_ofPass params strategy eps hpass)) :
    MainFormalSuccessorAnswerBoundary params strategy eps hpass k :=
  let axisBound := mainFormalSuccessorAnswerAxisWeightedBound_ofPass params strategy eps hpass
  let diagonalBound :=
    mainFormalSuccessorAnswerDiagonalWeightedBound_ofPass params strategy eps hpass
  { axisWeightedBound := axisBound
    diagonalWeightedBound := diagonalBound
    recursiveSlices := hrec
    selfImprovementProducer := hself }

/-- Build the answer-valued successor boundary from bridge inputs instead of an
already-packaged self-improvement producer.

This is the answer-register counterpart of
`mainFormalSuccessorBoundary_ofBridgeInputs`: it wires the answer-valued
per-slice Section 9 bridge inputs through
`mainFormalSuccessorAnswerSelfImprovementProducer_ofBridgeInputs` and packages
that producer together with recursive slice witnesses and the weighted
restricted-probability fields. -/
noncomputable def mainFormalSuccessorAnswerBoundary_ofBridgeInputs
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (hrec : MainFormalSuccessorAnswerRecursiveSlices params strategy eps hpass k
      (mainFormalSuccessorAnswerAxisWeightedBound_ofPass params strategy eps hpass)
      (mainFormalSuccessorAnswerDiagonalWeightedBound_ofPass params strategy eps hpass))
    (hbridge :
      MainFormalSuccessorAnswerSelfImprovementBridgeInputs params strategy eps hpass k
        (mainFormalSuccessorAnswerAxisWeightedBound_ofPass params strategy eps hpass)
        (mainFormalSuccessorAnswerDiagonalWeightedBound_ofPass params strategy eps hpass)) :
    MainFormalSuccessorAnswerBoundary params strategy eps hpass k :=
  mainFormalSuccessorAnswerBoundary_ofRecursiveSelfImprovement params strategy eps hpass k
    hrec
    (mainFormalSuccessorAnswerSelfImprovementProducer_ofBridgeInputs params strategy eps
      hpass k
      (mainFormalSuccessorAnswerAxisWeightedBound_ofPass params strategy eps hpass)
      (mainFormalSuccessorAnswerDiagonalWeightedBound_ofPass params strategy eps hpass)
      hbridge)

/-- Build the answer-valued successor boundary from an explicit predecessor
induction hypothesis and an answer-valued self-improvement producer.

This is the answer-register counterpart of
`mainFormalSuccessorBoundary_ofPredecessorInduction`. The predecessor hypothesis
is already at restricted-profile `mainInductionError` strength; the wrapper only
performs the recorded answer-slice transports and packages the boundary. -/
noncomputable def mainFormalSuccessorAnswerBoundary_ofPredecessorInduction
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (sliceData : MainFormalSuccessorAnswerRecursiveSliceData params strategy eps hpass)
    (hpredecessor : ∀ (x : Fq params),
      ∃ error : Error, ∃ G : Measurement (Polynomial params) (Role × ι),
        ConsRel (sliceData.sliceStrategy x).state
          (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas (sliceData.sliceStrategy x).pointMeasurementA)
          (polynomialEvaluationFamily params G.toSubMeas)
          error ∧
        error ≤
          let hrestrict :=
            mainFormalSuccessorAnswerRestrictionPackage params strategy eps hpass
              (mainFormalSuccessorAnswerAxisWeightedBound_ofPass params strategy eps hpass)
              (mainFormalSuccessorAnswerDiagonalWeightedBound_ofPass params strategy eps hpass)
          MainInductionStep.mainInductionError params k
            (hrestrict.profile.axisParallel x)
            (hrestrict.profile.selfConsistency x)
            (hrestrict.profile.diagonal x))
    (hself : MainFormalSuccessorAnswerSelfImprovementProducer params strategy eps hpass k
      (mainFormalSuccessorAnswerAxisWeightedBound_ofPass params strategy eps hpass)
      (mainFormalSuccessorAnswerDiagonalWeightedBound_ofPass params strategy eps hpass)) :
    MainFormalSuccessorAnswerBoundary params strategy eps hpass k :=
  mainFormalSuccessorAnswerBoundary_ofRecursiveSelfImprovement params strategy eps hpass k
    (mainFormalSuccessorAnswerRecursiveSlices_ofSliceData params strategy eps hpass k
      (mainFormalSuccessorAnswerAxisWeightedBound_ofPass params strategy eps hpass)
      (mainFormalSuccessorAnswerDiagonalWeightedBound_ofPass params strategy eps hpass)
      sliceData hpredecessor)
    hself

/-- Answer-valued successor-case Section 6 handoff for `mainFormal`. -/
theorem mainFormalSuccessorAnswerMainInductionPublicWrapper
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (hd : 0 < params.d)
    (boundary : MainFormalSuccessorAnswerBoundary params strategy eps hpass k)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ G : Measurement (Polynomial params.next) (Role × ι),
      ConsRel (strategy.strategySymmetrization).state
        (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas (strategy.strategySymmetrization).pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (MainInductionStep.mainInductionError params.next k
          (3 * eps) (3 * eps) (3 * eps)) :=
  MainInductionStep.answerMainInductionPublicWrapper params
    (strategy := strategy.strategySymmetrization)
    (eps := 3 * eps) (delta := 3 * eps) (gamma := 3 * eps) (k := k)
    (SameSpaceProjStrat.strategySymmetrization_isGood_three_mul
      (strategy := strategy) (eps := eps) hpass)
    hd
    boundary.axisWeightedBound
    boundary.diagonalWeightedBound
    boundary.recursiveSlices
    boundary.selfImprovementProducer
    hk_pos hk


end Test

end MIPStarRE.LDT
