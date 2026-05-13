import MIPStarRE.LDT.Test.MainTheorem.ClassicalAndBase

/-!
# Answer-valued restricted-slice recursion

Answer-valued `x`-restricted successor route for the `mainFormal` comparison.
This module parallels `OrdinaryRestriction` but works with the answer-side
(`A`-register) specialization of the `x`-restricted strategy
(paper `references/ldt-paper/inductive_step.tex` defines the single
`x`-restricted strategy around line 363; the answer-valued variant is a
Lean-side adaptation restricted to the `A`-register).  It retains the useful
answer-valued restricted-probability targets, recursive-slice target, and slice
data transport lemmas.  The former conditional boundary and public wrapper,
which took unproved recursive and self-improvement data as inputs, have been
removed.

## References

* Paper: `references/ldt-paper/inductive_step.tex`,
  `x`-restricted strategy definition and
  `\Cref{lem:restricted-probabilities}` (lines 363–412).
* Blueprint: `blueprint/src/chapter/ch10_induction.tex`,
  `\label{def:restricted-strategy}`,
  `\label{lem:restricted-probabilities}`, and
  `\label{def:main-formal-successor-boundary}` (answer-valued aliases).
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-! ### Answer-valued (preferred) successor route

The declarations in this section form the **answer-valued successor
route**, which uses `xRestrictedAnswerSymStrat` as the per-slice recursive
strategy.  This route is mathematically closer to the answer-register
construction in the paper because:

* `xRestrictedAnswerSymStrat` preserves the full answer-valued diagonal
  restriction and its transport invariant, so the restricted strategy can serve
  as an honest input to Section 9 self-improvement.
* It maps directly to the paper's answer-register construction, with the
  diagonal outcome function carried end-to-end rather than truncated to
  `zeroCoord`.

These declarations no longer feed a conditional role-residual constructor.  The
missing successor argument is represented by the Section 6 proof
obligation, not by an additional hypothesis on a Section 3 theorem.
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
symmetrization used in the successor branch of `mainFormal`.

Paper origin: `references/ldt-paper/inductive_step.tex:374-412`
(`\label{lem:restricted-probabilities}`), used in the recursive slice step
`references/ldt-paper/inductive_step.tex:441-454`. -/
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
answer-side recursive slice witnesses used in the successor analysis.

As in the ordinary-register constructor, this only exposes the package fields as
recursive-slice targets; the predecessor induction package must come from a
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


/-- Answer-side slice-recursion obligations for the successor branch of
`mainFormal`.

This is the answer-register counterpart of
`MainFormalSuccessorRecursiveSliceData`.  For each field element `x`, it
records a same-space projective strategy on the role-register space together
with compatibility proofs connecting its point and line measurements on both
registers to the answer-restricted strategy.  The diagonal-line measurements
have different answer alphabets on the two sides, so this package records the
common zero-coordinate readout rather than a false equality between the full
measurement families.

When supplied together with a recursive induction hypothesis (see
`mainFormalSuccessorAnswerRecursiveSlices_ofSliceData`), this data can close the
`MainFormalSuccessorAnswerRecursiveSlices` target.  The proof currently
consumes only the state and Alice point-measurement fields; the Bob-side, axis,
and diagonal
compatibility fields are retained so a later recursive-induction argument can
make `slicePasses` depend on the actual restricted answer slice.

**Unfaithful:** this data structure records honest answer-valued slice
strategies, compatibility fields, and passing hypotheses that are not yet
constructed from the successor proof of `thm:main-formal`
(`references/ldt-paper/test_definition.tex:180-202`) and `thm:main-induction`
(`references/ldt-paper/inductive_step.tex:441-551`).  This is tracked by
#1375, #1369, #1363, and #1458.  Elimination: prove the honest answer-valued
slice strategy construction from the paper hypotheses, then use this structure
only as the internal representation for that construction. -/
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
target.

The additional Bob-side, axis-parallel, and diagonal readout compatibility
fields in `MainFormalSuccessorAnswerRecursiveSliceData` are not needed for this
point-consistency target yet; they are retained by the data package so the later
recursive call can require `slicePasses` for slices whose line
measurements are pinned to the answer restriction on both registers.

The induction hypothesis `hrecSlice` mirrors what the predecessor induction
statement returns for the predecessor dimension: a polynomial measurement on
the role-register space with consistency bounded by the main induction error
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
  -- Rewrite the state and point measurement using the slice-data compatibilities.
  simpa [sliceData.sliceState_eq x, sliceData.slicePoint_eq x] using hG

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

end Test

end MIPStarRE.LDT
