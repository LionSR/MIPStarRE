import MIPStarRE.LDT.Test.MainTheorem.ClassicalAndBase

/-!
# Answer-valued restricted-slice recursion

Answer-valued `x`-restricted successor route for the `mainFormal` construction.
This module parallels `OrdinaryRestriction` but works with the answer-side
(`A`-register) specialization of the `x`-restricted strategy
(paper `references/ldt-paper/inductive_step.tex` defines the single
`x`-restricted strategy around line 363; the answer-valued variant is a
Lean-side adaptation restricted to the `A`-register).  It introduces the
answer-valued successor
boundary (`MainFormalSuccessorAnswerBoundary`), recursive slice data
(`MainFormalSuccessorAnswerRecursiveSliceData`), per-slice self-improvement
obligations (`MainFormalSuccessorAnswerSelfImprovementObligation`), and the
corresponding obligations (`MainFormalSuccessorAnswerSelfImprovementObligations`).
The central public theorem
`mainFormalSuccessorAnswerMainInductionPublicWrapper` converts a bundle of
predecessor answer-sided Section 6 inputs, together with the
`400·m·d ≤ k` side condition, into a role-register measurement.

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
a compatibility path for proofs already working with ordinary restriction data.
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
`MainFormalSuccessorAnswerRecursiveSlices` requirement needed by
`MainFormalSuccessorAnswerBoundary`.  The proof currently consumes only the
state and Alice point-measurement fields; the Bob-side, axis, and diagonal
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
field needed by `MainFormalSuccessorAnswerBoundary`.

The additional Bob-side, axis-parallel, and diagonal readout compatibility
fields in `MainFormalSuccessorAnswerRecursiveSliceData` are not needed for this
point-consistency target yet; they are retained by the data package so the later
recursive call can require `slicePasses` for slices whose line
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
/-- Successor-case answer-valued restricted-strategy self-improvement obligation.

Paper origin: the successor branch of `thm:main-induction` in
`references/ldt-paper/inductive_step.tex:352-386`, with the answer-valued
slice recursion corresponding to the restricted-strategy application at
`references/ldt-paper/inductive_step.tex:441-454`. -/
def MainFormalSuccessorAnswerSelfImprovementObligation (params : Parameters)
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

/-- Answer-valued successor-case obligations for the restricted-strategy
self-improvement obligation.

This is the answer-register counterpart of
`MainFormalSuccessorSelfImprovementObligations`: for each possible answer-side
per-slice induction package, the proof supplies the narrow
`AnswerSelfImprovementPackage.SliceObligations` assumptions.

**Unfaithful:** this obligation type records answer-side per-slice Section 9
data that is not yet derived from the successor proof of `thm:main-formal`
(`references/ldt-paper/test_definition.tex:180-202`) and
`thm:main-induction` (`references/ldt-paper/inductive_step.tex:441-551`).
This is tracked by #1376, #1369, #1503, #1515, and #1458.  Elimination:
prove the answer-valued slice obligations from the paper hypotheses, then use
this type only as an internal package consumed by the successor proof. -/
def MainFormalSuccessorAnswerSelfImprovementObligations (params : Parameters)
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
    MainInductionStep.AnswerSelfImprovementPackage.SliceObligations params
      strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps) k
      hrestrict hinduction

/-- The per-slice induction package type used by the answer-valued successor
self-improvement bridge.

Paper origin: `references/ldt-paper/inductive_step.tex:441-454`, with the
answer-valued restricted-slice interface. -/
abbrev MainFormalSuccessorAnswerSelfImprovementInductionPackage (params : Parameters)
    [FieldModel.{0} params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (haxisWeightedBound : MainFormalSuccessorAnswerAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound :
      MainFormalSuccessorAnswerDiagonalWeightedBound params strategy eps) : Type _ :=
  let hrestrict :=
    mainFormalSuccessorAnswerRestrictionPackage params strategy eps hpass
      haxisWeightedBound hdiagonalWeightedBound
  MainInductionStep.AnswerPerSliceInductionPackage params
    strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps) hrestrict k

/-- Assemble answer-valued successor self-improvement obligations from honest
slice strategies, verifier-visible measurement transports, and the remaining
Section 9 obligations.

**Unfaithful:** this helper assumes honest answer-valued slice strategies,
measurement transport fields, and `SelfImprovementObligations` for each slice,
rather than deriving them from
`references/ldt-paper/inductive_step.tex:441-551` and
`references/ldt-paper/self_improvement.tex:628-770`.  This is tracked by
#1375, #1376, #1369, #1503, #1515, and #1458.  Elimination: prove those
slice strategies and Section 9 obligations from the paper hypotheses, then use
this declaration only to record their combination. -/
noncomputable def mainFormalSuccessorAnswerSelfImprovementObligations_ofMeasurementEq
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (haxisWeightedBound : MainFormalSuccessorAnswerAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound :
      MainFormalSuccessorAnswerDiagonalWeightedBound params strategy eps)
    (sliceStrategy :
      MainFormalSuccessorAnswerSelfImprovementInductionPackage params strategy eps hpass k
        haxisWeightedBound hdiagonalWeightedBound →
        Fq params → SymStrat params (Role × ι))
    (state_eq :
      ∀ hinduction x, (sliceStrategy hinduction x).state =
        strategy.strategySymmetrization.state)
    (pointMeasurement_eq :
      ∀ hinduction x,
        (sliceStrategy hinduction x).pointMeasurement =
          (MainInductionStep.xRestrictedAnswerSymStrat params
            strategy.strategySymmetrization x).pointMeasurement)
    (axisParallelMeasurement_eq :
      ∀ hinduction x,
        (sliceStrategy hinduction x).axisParallelMeasurement.toIdxProjMeas =
          (MainInductionStep.xRestrictedAnswerSymStrat params
            strategy.strategySymmetrization x).axisParallelMeasurement.toIdxProjMeas)
    (diagonalZeroCoord_eq :
      ∀ hinduction x ℓ,
        postprocess
            (((sliceStrategy hinduction x).diagonalMeasurement.toIdxProjMeas ℓ).toSubMeas)
            (fun f : DiagonalLinePolynomial params => f zeroCoord) =
          postprocess
            (((MainInductionStep.xRestrictedAnswerSymStrat params
              strategy.strategySymmetrization x).diagonalMeasurement.toIdxProjMeas ℓ).toSubMeas)
            (fun f : DiagonalLineAnswer params => f zeroCoord))
    (obligations :
      ∀ hinduction x,
        SelfImprovement.SelfImprovementObligations params (sliceStrategy hinduction x)
          ((mainFormalSuccessorAnswerRestrictionPackage params strategy eps hpass
            haxisWeightedBound hdiagonalWeightedBound).profile.axisParallel x)
          ((mainFormalSuccessorAnswerRestrictionPackage params strategy eps hpass
            haxisWeightedBound hdiagonalWeightedBound).profile.selfConsistency x)
          (hinduction.sliceError x)) :
    MainFormalSuccessorAnswerSelfImprovementObligations params strategy eps hpass k
      haxisWeightedBound hdiagonalWeightedBound := by
  let hrestrict :=
    mainFormalSuccessorAnswerRestrictionPackage params strategy eps hpass
      haxisWeightedBound hdiagonalWeightedBound
  intro hinduction
  exact
    MainInductionStep.AnswerSelfImprovementPackage.SliceObligations.ofMeasurementEq
      params strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps) k
      hrestrict hinduction (sliceStrategy hinduction) (state_eq hinduction)
      (pointMeasurement_eq hinduction) (axisParallelMeasurement_eq hinduction)
      (diagonalZeroCoord_eq hinduction) (obligations hinduction)

/-- Assemble answer-valued successor self-improvement obligations from the
three named Section 9 inputs, using the closed spectral truncation input for
the orthonormalization stage.

**Unfaithful:** this helper assumes helper strong self-consistency,
orthonormalization repair, and final-fields inputs for every answer-valued
restricted slice; these are not derived here from
`references/ldt-paper/self_improvement.tex:628-770` or the successor induction
proof in `references/ldt-paper/inductive_step.tex:441-551`.  This is tracked by
#1376, #1514, #1515, #1503, and #1458.  Elimination: discharge the answer-side
Section 9 obligations and use this declaration only to combine those proved
inputs. -/
noncomputable def mainFormalSuccessorAnswerSelfImprovementObligations_ofOrthonormalizationRepair
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (haxisWeightedBound : MainFormalSuccessorAnswerAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound :
      MainFormalSuccessorAnswerDiagonalWeightedBound params strategy eps)
    (sliceStrategy :
      MainFormalSuccessorAnswerSelfImprovementInductionPackage params strategy eps hpass k
        haxisWeightedBound hdiagonalWeightedBound →
        Fq params → SymStrat params (Role × ι))
    (state_eq :
      ∀ hinduction x, (sliceStrategy hinduction x).state =
        strategy.strategySymmetrization.state)
    (pointMeasurement_eq :
      ∀ hinduction x,
        (sliceStrategy hinduction x).pointMeasurement =
          (MainInductionStep.xRestrictedAnswerSymStrat params
            strategy.strategySymmetrization x).pointMeasurement)
    (axisParallelMeasurement_eq :
      ∀ hinduction x,
        (sliceStrategy hinduction x).axisParallelMeasurement.toIdxProjMeas =
          (MainInductionStep.xRestrictedAnswerSymStrat params
            strategy.strategySymmetrization x).axisParallelMeasurement.toIdxProjMeas)
    (diagonalZeroCoord_eq :
      ∀ hinduction x ℓ,
        postprocess
            (((sliceStrategy hinduction x).diagonalMeasurement.toIdxProjMeas ℓ).toSubMeas)
            (fun f : DiagonalLinePolynomial params => f zeroCoord) =
          postprocess
            (((MainInductionStep.xRestrictedAnswerSymStrat params
              strategy.strategySymmetrization x).diagonalMeasurement.toIdxProjMeas ℓ).toSubMeas)
            (fun f : DiagonalLineAnswer params => f zeroCoord))
    (helperStrongSelfConsistency :
      ∀ hinduction x,
        SelfImprovement.HelperStrongSelfConsistencyInput params
          (sliceStrategy hinduction x)
          ((mainFormalSuccessorAnswerRestrictionPackage params strategy eps hpass
            haxisWeightedBound hdiagonalWeightedBound).profile.axisParallel x)
          ((mainFormalSuccessorAnswerRestrictionPackage params strategy eps hpass
            haxisWeightedBound hdiagonalWeightedBound).profile.selfConsistency x))
    (repair :
      ∀ hinduction x,
        SelfImprovement.OrthonormalizationRepairObligation params
          (sliceStrategy hinduction x)
          ((mainFormalSuccessorAnswerRestrictionPackage params strategy eps hpass
            haxisWeightedBound hdiagonalWeightedBound).profile.axisParallel x)
          ((mainFormalSuccessorAnswerRestrictionPackage params strategy eps hpass
            haxisWeightedBound hdiagonalWeightedBound).profile.selfConsistency x))
    (finalFields :
      ∀ hinduction x,
        SelfImprovement.FinalFieldsInput params (sliceStrategy hinduction x)
          ((mainFormalSuccessorAnswerRestrictionPackage params strategy eps hpass
            haxisWeightedBound hdiagonalWeightedBound).profile.axisParallel x)
          ((mainFormalSuccessorAnswerRestrictionPackage params strategy eps hpass
            haxisWeightedBound hdiagonalWeightedBound).profile.selfConsistency x)
          (hinduction.sliceError x)) :
    MainFormalSuccessorAnswerSelfImprovementObligations params strategy eps hpass k
      haxisWeightedBound hdiagonalWeightedBound := by
  let hrestrict :=
    mainFormalSuccessorAnswerRestrictionPackage params strategy eps hpass
      haxisWeightedBound hdiagonalWeightedBound
  intro hinduction
  exact
    MainInductionStep.AnswerSelfImprovementPackage.SliceObligations.ofOrthonormalizationRepair
      params strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps) k
      hrestrict hinduction (sliceStrategy hinduction) (state_eq hinduction)
      (pointMeasurement_eq hinduction) (axisParallelMeasurement_eq hinduction)
      (diagonalZeroCoord_eq hinduction) (helperStrongSelfConsistency hinduction)
      (repair hinduction) (finalFields hinduction)

/-- Convert answer-valued successor-case obligations into the self-improvement
obligation expected by the public answer-valued Section 6 boundary.

**Unfaithful:** this helper consumes
`MainFormalSuccessorAnswerSelfImprovementObligations`, whose answer-side
Section 9 fields are not derived from the cited successor proof
(`references/ldt-paper/inductive_step.tex:441-551`).  This is tracked by
#1376, #1369, #1503, #1515, and #1458.  Elimination: prove those obligations
from the paper hypotheses and retain this as a technical conversion. -/
noncomputable def mainFormalSuccessorAnswerSelfImprovementObligation_ofObligations
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (haxisWeightedBound : MainFormalSuccessorAnswerAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound :
      MainFormalSuccessorAnswerDiagonalWeightedBound params strategy eps)
    (obligations :
      MainFormalSuccessorAnswerSelfImprovementObligations params strategy eps hpass k
        haxisWeightedBound hdiagonalWeightedBound) :
    MainFormalSuccessorAnswerSelfImprovementObligation params strategy eps hpass k
      haxisWeightedBound hdiagonalWeightedBound := by
  let hrestrict :=
    mainFormalSuccessorAnswerRestrictionPackage params strategy eps hpass
      haxisWeightedBound hdiagonalWeightedBound
  intro hinduction
  exact
    MainInductionStep.AnswerSelfImprovementPackage.ofSliceObligations params
      strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps) k
      hrestrict hinduction (obligations hinduction)

/-- Answer-valued successor-case Section 6 boundary inputs for `mainFormal`.

**Unfaithful:** as a supplied boundary this structure contains
answer-valued recursive slice witnesses and a self-improvement obligation that
are not hypotheses of `thm:main-formal`
(`references/ldt-paper/test_definition.tex:180-202`).  They must be produced
inside the proof of `mainFormal`, using the successor proof of
`thm:main-induction`
(`references/ldt-paper/inductive_step.tex:441-551`).  This is tracked by
#1375, #1376, #1369, #1363, and #1458.  Elimination: prove the recursive-slice
and self-improvement fields before using this boundary record in the
successor branch of `mainFormal`. -/
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
  selfImprovementObligation :
    MainFormalSuccessorAnswerSelfImprovementObligation params strategy eps hpass k
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
recursion and restricted-strategy self-improvement inputs are supplied.

**Unfaithful:** this conditional constructor assumes answer-valued recursive
slice data and a self-improvement obligation rather than deriving them from
`references/ldt-paper/test_definition.tex:180-202` and
`references/ldt-paper/inductive_step.tex:441-551`.  This is tracked by #1375,
#1376, #1369, #1363, and #1458.  Elimination: construct these inputs inside the
successor branch of `mainFormal` and use this constructor only after the inputs
have been proved. -/
def mainFormalSuccessorAnswerBoundary_ofRecursiveSelfImprovement
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (hrec : MainFormalSuccessorAnswerRecursiveSlices params strategy eps hpass k
      (mainFormalSuccessorAnswerAxisWeightedBound_ofPass params strategy eps hpass)
      (mainFormalSuccessorAnswerDiagonalWeightedBound_ofPass params strategy eps hpass))
    (hself : MainFormalSuccessorAnswerSelfImprovementObligation params strategy eps hpass k
      (mainFormalSuccessorAnswerAxisWeightedBound_ofPass params strategy eps hpass)
      (mainFormalSuccessorAnswerDiagonalWeightedBound_ofPass params strategy eps hpass)) :
    MainFormalSuccessorAnswerBoundary params strategy eps hpass k :=
  let axisBound := mainFormalSuccessorAnswerAxisWeightedBound_ofPass params strategy eps hpass
  let diagonalBound :=
    mainFormalSuccessorAnswerDiagonalWeightedBound_ofPass params strategy eps hpass
  { axisWeightedBound := axisBound
    diagonalWeightedBound := diagonalBound
    recursiveSlices := hrec
    selfImprovementObligation := hself }

/-- Build the answer-valued successor boundary from obligations instead of an
already constructed self-improvement obligation.

This is the answer-register counterpart of
`mainFormalSuccessorBoundary_ofObligations`: it sends the answer-valued
per-slice Section 9 obligations through
`mainFormalSuccessorAnswerSelfImprovementObligation_ofObligations` and combines
that obligation with the recursive slice witnesses and the weighted
restricted-probability fields.

**Unfaithful:** this constructor assumes recursive slice witnesses and
answer-side per-slice Section 9 obligations, rather than deriving them from
`references/ldt-paper/test_definition.tex:180-202` and
`references/ldt-paper/inductive_step.tex:441-551`.  This is tracked by #1375,
#1376, #1369, #1363, and #1458.  Elimination: prove the answer-valued
predecessor induction data and the Section 9 slice obligations inside the
successor proof, then use this declaration only to record their combination. -/
noncomputable def mainFormalSuccessorAnswerBoundary_ofObligations
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (hrec : MainFormalSuccessorAnswerRecursiveSlices params strategy eps hpass k
      (mainFormalSuccessorAnswerAxisWeightedBound_ofPass params strategy eps hpass)
      (mainFormalSuccessorAnswerDiagonalWeightedBound_ofPass params strategy eps hpass))
    (obligations :
      MainFormalSuccessorAnswerSelfImprovementObligations params strategy eps hpass k
        (mainFormalSuccessorAnswerAxisWeightedBound_ofPass params strategy eps hpass)
        (mainFormalSuccessorAnswerDiagonalWeightedBound_ofPass params strategy eps hpass)) :
    MainFormalSuccessorAnswerBoundary params strategy eps hpass k :=
  mainFormalSuccessorAnswerBoundary_ofRecursiveSelfImprovement params strategy eps hpass k
    hrec
    (mainFormalSuccessorAnswerSelfImprovementObligation_ofObligations params strategy eps
      hpass k
      (mainFormalSuccessorAnswerAxisWeightedBound_ofPass params strategy eps hpass)
      (mainFormalSuccessorAnswerDiagonalWeightedBound_ofPass params strategy eps hpass)
      obligations)

/-- Build the answer-valued successor boundary from an explicit predecessor
induction hypothesis and an answer-valued self-improvement obligation.

This is the answer-register counterpart of
`mainFormalSuccessorBoundary_ofPredecessorInduction`. The predecessor hypothesis
is already at restricted-profile `mainInductionError` strength; the construction
only performs the recorded answer-slice transports and combines the boundary
fields.

**Unfaithful:** this helper assumes answer-valued slice data, predecessor
induction witnesses, and an answer-valued self-improvement obligation, none of
which are hypotheses of `thm:main-formal`
(`references/ldt-paper/test_definition.tex:180-202`).  This is tracked by
#1375, #1376, #1369, #1363, and #1458.  Elimination: derive the predecessor
witnesses and answer-side slice obligations from the successor proof of
`thm:main-induction` (`references/ldt-paper/inductive_step.tex:441-551`) before
using this transport helper. -/
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
    (hself : MainFormalSuccessorAnswerSelfImprovementObligation params strategy eps hpass k
      (mainFormalSuccessorAnswerAxisWeightedBound_ofPass params strategy eps hpass)
      (mainFormalSuccessorAnswerDiagonalWeightedBound_ofPass params strategy eps hpass)) :
    MainFormalSuccessorAnswerBoundary params strategy eps hpass k :=
  mainFormalSuccessorAnswerBoundary_ofRecursiveSelfImprovement params strategy eps hpass k
    (mainFormalSuccessorAnswerRecursiveSlices_ofSliceData params strategy eps hpass k
      (mainFormalSuccessorAnswerAxisWeightedBound_ofPass params strategy eps hpass)
      (mainFormalSuccessorAnswerDiagonalWeightedBound_ofPass params strategy eps hpass)
      sliceData hpredecessor)
    hself

/-- Answer-valued successor-case Section 6 handoff for `mainFormal`.

**Unfaithful:** this conditional handoff assumes
`boundary : MainFormalSuccessorAnswerBoundary`, whose fields include
answer-valued recursive slice witnesses and the slice-wise self-improvement
obligation rather than deriving them from the hypotheses of `thm:main-formal`
(`references/ldt-paper/test_definition.tex:180-202`) and the successor case of
`thm:main-induction` (`references/ldt-paper/inductive_step.tex:441-551`).
This is tracked by #1369, #1363, #1507, #1503, and #1458.  Elimination:
construct the answer-valued successor boundary from the paper hypotheses before
invoking this helper in the proof of `mainFormal`. -/
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
    boundary.selfImprovementObligation
    hk_pos hk


end Test

end MIPStarRE.LDT
