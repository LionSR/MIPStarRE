import MIPStarRE.LDT.Test.MainTheorem.ClassicalAndBase
import MIPStarRE.LDT.MainInductionStep.Theorems.SourceTheorems

/-!
# Answer-valued restricted-slice recursion

Answer-valued `x`-restricted successor route for the `mainFormal` comparison.
The paper `references/ldt-paper/inductive_step.tex` defines the single
`x`-restricted strategy around line 363.  The answer-valued variant used here is
a Lean-side adaptation restricted to the `A`-register.  It retains the useful
answer-valued restricted-probability targets and recursive-slice target.  The
former ordinary compatibility route, conditional boundary, public wrapper, and
slice-data witness data record, which took unproved recursive,
self-improvement, or concrete slice-strategy data as inputs, have been removed.

## References

* Paper: `references/ldt-paper/inductive_step.tex`,
  `x`-restricted strategy definition and
  `\Cref{lem:restricted-probabilities}` (lines 363–412).
* Blueprint: `blueprint/src/chapter/ch10_induction.tex`,
  `\label{def:restricted-strategy}`,
  `\label{lem:restricted-probabilities}`, and the unnumbered paragraph
  "Lean successor restricted-recursion targets for the Section 3 proof".
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
  as a concrete input to Section 9 self-improvement.
* It maps directly to the paper's answer-register construction, with the
  diagonal outcome function carried end-to-end rather than truncated to
  `zeroCoord`.

These declarations no longer feed a conditional role-witness constructor.  The
successor argument is now supplied by the corrected Section 6 theorem, not by an
additional hypothesis on a Section 3 theorem.
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

/-- The answer-valued restricted-probability data record on the role-register
symmetrization used in the successor branch of `mainFormal`.

Paper origin: `references/ldt-paper/inductive_step.tex:374-412`
(`\label{lem:restricted-probabilities}`), used in the recursive slice step
`references/ldt-paper/inductive_step.tex:441-454`. -/
noncomputable def mainFormalSuccessorAnswerRestrictionData
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (haxisWeightedBound : MainFormalSuccessorAnswerAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound :
      MainFormalSuccessorAnswerDiagonalWeightedBound params strategy eps) :
    MainInductionStep.AnswerSliceRestrictionData params
      strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps) :=
  MainInductionStep.answerMainInductionPublicRestrictionData
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
    mainFormalSuccessorAnswerRestrictionData params strategy eps hpass
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

/-- A Section 6 answer-valued per-slice induction data record supplies the
answer-side recursive slice witnesses used in the successor analysis.

This only exposes the data record fields as recursive-slice targets; the
predecessor induction data record must come from a non-circular induction
hypothesis. -/
theorem mainFormalSuccessorAnswerRecursiveSlices_ofInductionData
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (haxisWeightedBound : MainFormalSuccessorAnswerAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound :
      MainFormalSuccessorAnswerDiagonalWeightedBound params strategy eps)
    (hinduction :
      MainInductionStep.AnswerPerSliceInductionData params
        strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps)
        (mainFormalSuccessorAnswerRestrictionData params strategy eps hpass
          haxisWeightedBound hdiagonalWeightedBound)
        k) :
    MainFormalSuccessorAnswerRecursiveSlices params strategy eps hpass k
      haxisWeightedBound hdiagonalWeightedBound := by
  intro x
  exact
    ⟨hinduction.sliceError x, hinduction.sliceMeasurement x,
      hinduction.pointConsistency x, hinduction.error_le x⟩

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
