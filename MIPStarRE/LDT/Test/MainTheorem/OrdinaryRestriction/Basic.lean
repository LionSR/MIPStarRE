import MIPStarRE.LDT.Test.MainTheorem.ClassicalAndBase

/-!
# Ordinary restricted-slice recursion: basic inputs

This module contains the ordinary successor-route restricted-probability and
recursive-slice targets used when comparing the Section 3 proof with the
successor case of Section 6.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-! ### Ordinary (compatibility) successor route

The declarations in this section form the **ordinary successor route**, which
uses `xRestrictedStrategy` (ordinary diagonal restriction) as the per-slice
recursive strategy.  This route is kept only at the level of the source
mathematics that remains useful: weighted restricted-probability targets and
recursive-slice targets.  The former conditional boundary record, which bundled
unproved self-improvement input into a Section 3 handoff, has been removed; the
missing successor proof is represented by the `mainInduction`
proof obligation instead.

**Note:** `xRestrictedStrategy` uses `restrictDiagonalMeasurement`, which
post-processes the diagonal outcome to the `zeroCoord` readout and re-embeds it
as a constant polynomial.  This loses full diagonal-covariance and means the
restricted strategy cannot be upgraded to an honest `SymStrat` with the diagonal
transport invariant.  For paper-faithful Section 6 recursion, prefer the
**answer-valued successor route** below.
-/

/-- Weighted restricted-axis input expected by the Section 6 successor step
on the role-register symmetrization. -/
def MainFormalSuccessorAxisWeightedBound (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error) : Prop :=
  avgOver (uniformDistribution (Fq params))
    (fun x => MainInductionStep.sliceTransverseDirectionWeight params *
      (MainInductionStep.xRestrictedStrategy params
        strategy.strategySymmetrization x).axisParallelFailureProbability) ≤
    3 * eps

/-- Weighted restricted-diagonal input expected by the Section 6 successor step
on the role-register symmetrization.

Per `lem:restricted-probabilities` (see
`audits/2026-04-05_lean-code-audit.md`) the paper's slice argument uses the
same transverse-direction factor `m / (m + 1)` for both the axis-parallel and
diagonal branches. `restrictedProbabilities` therefore expects
`sliceTransverseDirectionWeight` on both weighted bounds. -/
def MainFormalSuccessorDiagonalWeightedBound (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error) : Prop :=
  avgOver (uniformDistribution (Fq params))
    (fun x => MainInductionStep.sliceTransverseDirectionWeight params *
      (MainInductionStep.xRestrictedStrategy params
        strategy.strategySymmetrization x).diagonalFailureProbability) ≤
    3 * eps

/-- The restricted-probability record on the role-register symmetrization used
in the successor branch of `mainFormal`.

Paper origin: `references/ldt-paper/inductive_step.tex:374-412`
(`\label{lem:restricted-probabilities}`), used in the recursive slice step
`references/ldt-paper/inductive_step.tex:441-454`. -/
noncomputable def mainFormalSuccessorRestrictionPackage
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (haxisWeightedBound : MainFormalSuccessorAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound : MainFormalSuccessorDiagonalWeightedBound params strategy eps) :
    MainInductionStep.SliceRestrictionPackage params
      strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps) :=
  MainInductionStep.mainInductionPublicRestrictionPackage
    params strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps)
    (SameSpaceProjStrat.strategySymmetrization_isGood_three_mul
      (strategy := strategy) (eps := eps) hpass)
    haxisWeightedBound hdiagonalWeightedBound

/-- Successor-case recursive slice witnesses expected by the public Section 6
successor analysis. -/
def MainFormalSuccessorRecursiveSlices (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (haxisWeightedBound : MainFormalSuccessorAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound :
      MainFormalSuccessorDiagonalWeightedBound params strategy eps) : Prop :=
  let hrestrict :=
    mainFormalSuccessorRestrictionPackage params strategy eps hpass
      haxisWeightedBound hdiagonalWeightedBound
  ∀ x,
    ∃ error : Error, ∃ G : Measurement (Polynomial params) (Role × ι),
      ConsRel (strategy.strategySymmetrization).state
        (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas
          (MainInductionStep.xRestrictedStrategy params
            strategy.strategySymmetrization x).pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        error ∧
      error ≤
        MainInductionStep.mainInductionError params k
          (hrestrict.profile.axisParallel x)
          (hrestrict.profile.selfConsistency x)
          (hrestrict.profile.diagonal x)

/-- A Section 6 per-slice induction record supplies the ordinary recursive
slice witnesses used in the successor analysis.

This constructor is only a translation: the proof must still provide the
`PerSliceInductionPackage` from a genuine predecessor induction hypothesis. It
does not invoke the public `mainFormal` theorem. -/
theorem mainFormalSuccessorRecursiveSlices_ofInductionPackage
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (haxisWeightedBound : MainFormalSuccessorAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound :
      MainFormalSuccessorDiagonalWeightedBound params strategy eps)
    (hinduction :
      MainInductionStep.PerSliceInductionPackage params
        strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps)
        (mainFormalSuccessorRestrictionPackage params strategy eps hpass
          haxisWeightedBound hdiagonalWeightedBound)
        k) :
    MainFormalSuccessorRecursiveSlices params strategy eps hpass k
      haxisWeightedBound hdiagonalWeightedBound := by
  intro x
  exact
    ⟨hinduction.sliceError x, hinduction.sliceMeasurement x,
      hinduction.pointConsistency x, hinduction.error_le x⟩

/-- The public restricted-probabilities theorem supplies the successor-case
weighted axis-parallel input for the role-register symmetrization used by
`mainFormal`. -/
theorem mainFormalSuccessorAxisWeightedBound_ofPass
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    MainFormalSuccessorAxisWeightedBound params strategy eps :=
  MainInductionStep.weighted_axisParallel_bound params
    strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps)
    (SameSpaceProjStrat.strategySymmetrization_isGood_three_mul
      (strategy := strategy) (eps := eps) hpass)

/-- The public restricted-probabilities theorem supplies the successor-case
weighted diagonal-line input for the role-register symmetrization used by
`mainFormal`. -/
theorem mainFormalSuccessorDiagonalWeightedBound_ofPass
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    MainFormalSuccessorDiagonalWeightedBound params strategy eps :=
  MainInductionStep.weighted_diagonal_bound params
    strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps)
    (SameSpaceProjStrat.strategySymmetrization_isGood_three_mul
      (strategy := strategy) (eps := eps) hpass)

end Test

end MIPStarRE.LDT
