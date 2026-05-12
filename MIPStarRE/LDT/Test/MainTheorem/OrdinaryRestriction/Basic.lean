import MIPStarRE.LDT.Test.MainTheorem.ClassicalAndBase

/-!
# Ordinary restricted-slice recursion: basic inputs

This module contains the ordinary successor-route input types, bridge-input
constructors, and the successor boundary package used by the Section 6 main
theorem wrapper.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-! ### Ordinary (compatibility) successor route

The declarations in this section form the **ordinary successor route**, which
uses `xRestrictedStrategy` (ordinary diagonal restriction) as the per-slice
recursive strategy.  This route is kept as a compatibility interface: it
provides `MainFormalSuccessorBoundary` and the associated wrappers, which feed
into the `MainFormalRolePackageBranchResidual.successor` constructor.

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

/-- The restricted-probability package on the role-register symmetrization used
in the successor branch of `mainFormal`. -/
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
boundary wrapper. -/
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

/-- A Section 6 per-slice induction package supplies the recursive slice
witnesses needed by the `mainFormal` successor boundary.

This constructor is only a package adapter: the caller must still provide the
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

/-- Successor-case restricted-strategy self-improvement producer expected by the
public Section 6 boundary wrapper.

Paper origin: the successor branch of `thm:main-induction` in
`references/ldt-paper/inductive_step.tex:352-386`, where the restricted
strategies are improved slice by slice before the pasting step. -/
def MainFormalSuccessorSelfImprovementProducer (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (haxisWeightedBound : MainFormalSuccessorAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound :
      MainFormalSuccessorDiagonalWeightedBound params strategy eps) : Type _ :=
  let hrestrict :=
    mainFormalSuccessorRestrictionPackage params strategy eps hpass
      haxisWeightedBound hdiagonalWeightedBound
  ∀ hinduction :
    MainInductionStep.PerSliceInductionPackage params
      strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps) hrestrict k,
    MainInductionStep.SelfImprovementPackage params
      strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps) k
      hrestrict hinduction

/-- Successor-case bridge-input package for the restricted-strategy
self-improvement producer.

For each possible per-slice induction package, this asks for the narrow
`SelfImprovementPackage.SliceBridgeInputs` assumptions: honest per-slice
`SymStrat`s, equality transports to the restricted-slice interfaces, and the
remaining Section 9 bridge inputs for those honest slice strategies. -/
def MainFormalSuccessorSelfImprovementBridgeInputs (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (haxisWeightedBound : MainFormalSuccessorAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound :
      MainFormalSuccessorDiagonalWeightedBound params strategy eps) : Type _ :=
  let hrestrict :=
    mainFormalSuccessorRestrictionPackage params strategy eps hpass
      haxisWeightedBound hdiagonalWeightedBound
  ∀ hinduction :
    MainInductionStep.PerSliceInductionPackage params
      strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps) hrestrict k,
    MainInductionStep.SelfImprovementPackage.SliceBridgeInputs params
      strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps) k
      hrestrict hinduction

/-- The per-slice induction package type used by the ordinary successor
self-improvement bridge. -/
abbrev MainFormalSuccessorSelfImprovementInductionPackage (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (haxisWeightedBound : MainFormalSuccessorAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound :
      MainFormalSuccessorDiagonalWeightedBound params strategy eps) : Type _ :=
  let hrestrict :=
    mainFormalSuccessorRestrictionPackage params strategy eps hpass
      haxisWeightedBound hdiagonalWeightedBound
  MainInductionStep.PerSliceInductionPackage params
    strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps) hrestrict k

/-- Assemble ordinary successor self-improvement bridge inputs from honest slice
strategies, measurement transports, and the remaining Section 9 bridge data. -/
noncomputable def mainFormalSuccessorSelfImprovementBridgeInputs_ofMeasurementEq
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (haxisWeightedBound : MainFormalSuccessorAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound :
      MainFormalSuccessorDiagonalWeightedBound params strategy eps)
    (sliceStrategy :
      MainFormalSuccessorSelfImprovementInductionPackage params strategy eps hpass k
        haxisWeightedBound hdiagonalWeightedBound →
        Fq params → SymStrat params (Role × ι))
    (state_eq :
      ∀ hinduction x, (sliceStrategy hinduction x).state =
        strategy.strategySymmetrization.state)
    (pointMeasurement_eq :
      ∀ hinduction x,
        (sliceStrategy hinduction x).pointMeasurement =
          (MainInductionStep.xRestrictedStrategy params
            strategy.strategySymmetrization x).pointMeasurement)
    (axisParallelMeasurement_eq :
      ∀ hinduction x,
        (sliceStrategy hinduction x).axisParallelMeasurement.toIdxProjMeas =
          (MainInductionStep.xRestrictedStrategy params
            strategy.strategySymmetrization x).axisParallelMeasurement.toIdxProjMeas)
    (diagonalMeasurement_eq :
      ∀ hinduction x,
        (sliceStrategy hinduction x).diagonalMeasurement.toIdxProjMeas =
          (MainInductionStep.xRestrictedStrategy params
            strategy.strategySymmetrization x).diagonalMeasurement)
    (bridgeInputs :
      ∀ hinduction x,
        SelfImprovement.SelfImprovementBridgeInputs params (sliceStrategy hinduction x)
          ((mainFormalSuccessorRestrictionPackage params strategy eps hpass
            haxisWeightedBound hdiagonalWeightedBound).profile.axisParallel x)
          ((mainFormalSuccessorRestrictionPackage params strategy eps hpass
            haxisWeightedBound hdiagonalWeightedBound).profile.selfConsistency x)
          (hinduction.sliceError x)) :
    MainFormalSuccessorSelfImprovementBridgeInputs params strategy eps hpass k
      haxisWeightedBound hdiagonalWeightedBound := by
  let hrestrict :=
    mainFormalSuccessorRestrictionPackage params strategy eps hpass
      haxisWeightedBound hdiagonalWeightedBound
  intro hinduction
  exact
    MainInductionStep.SelfImprovementPackage.SliceBridgeInputs.ofMeasurementEq
      params strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps) k
      hrestrict hinduction (sliceStrategy hinduction) (state_eq hinduction)
      (pointMeasurement_eq hinduction) (axisParallelMeasurement_eq hinduction)
      (diagonalMeasurement_eq hinduction) (bridgeInputs hinduction)

/-- Assemble ordinary successor self-improvement bridge inputs from the three
named Section 9 producers, using the closed spectral truncation input for the
orthonormalization stage. -/
noncomputable def mainFormalSuccessorSelfImprovementBridgeInputs_ofOrthonormalizationRepair
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (haxisWeightedBound : MainFormalSuccessorAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound :
      MainFormalSuccessorDiagonalWeightedBound params strategy eps)
    (sliceStrategy :
      MainFormalSuccessorSelfImprovementInductionPackage params strategy eps hpass k
        haxisWeightedBound hdiagonalWeightedBound →
        Fq params → SymStrat params (Role × ι))
    (state_eq :
      ∀ hinduction x, (sliceStrategy hinduction x).state =
        strategy.strategySymmetrization.state)
    (pointMeasurement_eq :
      ∀ hinduction x,
        (sliceStrategy hinduction x).pointMeasurement =
          (MainInductionStep.xRestrictedStrategy params
            strategy.strategySymmetrization x).pointMeasurement)
    (axisParallelMeasurement_eq :
      ∀ hinduction x,
        (sliceStrategy hinduction x).axisParallelMeasurement.toIdxProjMeas =
          (MainInductionStep.xRestrictedStrategy params
            strategy.strategySymmetrization x).axisParallelMeasurement.toIdxProjMeas)
    (diagonalMeasurement_eq :
      ∀ hinduction x,
        (sliceStrategy hinduction x).diagonalMeasurement.toIdxProjMeas =
          (MainInductionStep.xRestrictedStrategy params
            strategy.strategySymmetrization x).diagonalMeasurement)
    (helperStrongSelfConsistency :
      ∀ hinduction x,
        SelfImprovement.HelperStrongSelfConsistencyInput params
          (sliceStrategy hinduction x)
          ((mainFormalSuccessorRestrictionPackage params strategy eps hpass
            haxisWeightedBound hdiagonalWeightedBound).profile.axisParallel x)
          ((mainFormalSuccessorRestrictionPackage params strategy eps hpass
            haxisWeightedBound hdiagonalWeightedBound).profile.selfConsistency x))
    (repair :
      ∀ hinduction x,
        SelfImprovement.OrthonormalizationRepairProducer params
          (sliceStrategy hinduction x)
          ((mainFormalSuccessorRestrictionPackage params strategy eps hpass
            haxisWeightedBound hdiagonalWeightedBound).profile.axisParallel x)
          ((mainFormalSuccessorRestrictionPackage params strategy eps hpass
            haxisWeightedBound hdiagonalWeightedBound).profile.selfConsistency x))
    (finalFields :
      ∀ hinduction x,
        SelfImprovement.FinalFieldsInput params (sliceStrategy hinduction x)
          ((mainFormalSuccessorRestrictionPackage params strategy eps hpass
            haxisWeightedBound hdiagonalWeightedBound).profile.axisParallel x)
          ((mainFormalSuccessorRestrictionPackage params strategy eps hpass
            haxisWeightedBound hdiagonalWeightedBound).profile.selfConsistency x)
          (hinduction.sliceError x)) :
    MainFormalSuccessorSelfImprovementBridgeInputs params strategy eps hpass k
      haxisWeightedBound hdiagonalWeightedBound := by
  let hrestrict :=
    mainFormalSuccessorRestrictionPackage params strategy eps hpass
      haxisWeightedBound hdiagonalWeightedBound
  intro hinduction
  exact
    MainInductionStep.SelfImprovementPackage.SliceBridgeInputs.ofOrthonormalizationRepair
      params strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps) k
      hrestrict hinduction (sliceStrategy hinduction) (state_eq hinduction)
      (pointMeasurement_eq hinduction) (axisParallelMeasurement_eq hinduction)
      (diagonalMeasurement_eq hinduction) (helperStrongSelfConsistency hinduction)
      (repair hinduction) (finalFields hinduction)

/-- Convert successor-case bridge inputs into the self-improvement producer
expected by the public Section 6 boundary wrapper.

This does not discharge the bridge-input fields; it only packages them into the
existing `MainFormalSuccessorSelfImprovementProducer` API. -/
noncomputable def mainFormalSuccessorSelfImprovementProducer_ofBridgeInputs
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (haxisWeightedBound : MainFormalSuccessorAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound :
      MainFormalSuccessorDiagonalWeightedBound params strategy eps)
    (hbridge :
      MainFormalSuccessorSelfImprovementBridgeInputs params strategy eps hpass k
        haxisWeightedBound hdiagonalWeightedBound) :
    MainFormalSuccessorSelfImprovementProducer params strategy eps hpass k
      haxisWeightedBound hdiagonalWeightedBound := by
  let hrestrict :=
    mainFormalSuccessorRestrictionPackage params strategy eps hpass
      haxisWeightedBound hdiagonalWeightedBound
  intro hinduction
  exact
    MainInductionStep.SelfImprovementPackage.ofSliceBridgeInputs params
      strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps) k
      hrestrict hinduction (hbridge hinduction)

/-- Successor-case Section 6 boundary inputs for `mainFormal`.

Assume the ambient projective strategy lives over `params.next`. Step 1 already
turns `hpass` into the `(3 * eps, 3 * eps, 3 * eps)`-good role-register
symmetrization `strategy.strategySymmetrization`. The public Section 6 wrapper
expects:
1. weighted restricted-axis and restricted-diagonal bounds,
2. recursive slice witnesses for the restricted strategies, and
3. a restricted-strategy self-improvement producer.

The helper lemmas below now discharge the weighted fields from `hpass`; bundling
all fields into a single named package still gives the successor branch of
`mainFormal` one honest issue-#634 interface, rather than four independent
hypothesis holes. -/
structure MainFormalSuccessorBoundary (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ) where
  axisWeightedBound :
    MainFormalSuccessorAxisWeightedBound params strategy eps
  diagonalWeightedBound :
    MainFormalSuccessorDiagonalWeightedBound params strategy eps
  recursiveSlices :
    MainFormalSuccessorRecursiveSlices params strategy eps hpass k
      axisWeightedBound diagonalWeightedBound
  selfImprovementProducer :
    MainFormalSuccessorSelfImprovementProducer params strategy eps hpass k
      axisWeightedBound diagonalWeightedBound

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

/-- Build the successor boundary once the two still-external slice-recursion and
restricted-strategy self-improvement inputs are supplied. The weighted
restricted-probability fields are now discharged from `hpass` by the public
Section 6 weighted-bound lemmas. -/
def mainFormalSuccessorBoundary_ofRecursiveSelfImprovement
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (hrec : MainFormalSuccessorRecursiveSlices params strategy eps hpass k
      (mainFormalSuccessorAxisWeightedBound_ofPass params strategy eps hpass)
      (mainFormalSuccessorDiagonalWeightedBound_ofPass params strategy eps hpass))
    (hself : MainFormalSuccessorSelfImprovementProducer params strategy eps hpass k
      (mainFormalSuccessorAxisWeightedBound_ofPass params strategy eps hpass)
      (mainFormalSuccessorDiagonalWeightedBound_ofPass params strategy eps hpass)) :
    MainFormalSuccessorBoundary params strategy eps hpass k :=
  let axisBound := mainFormalSuccessorAxisWeightedBound_ofPass params strategy eps hpass
  let diagonalBound :=
    mainFormalSuccessorDiagonalWeightedBound_ofPass params strategy eps hpass
  { axisWeightedBound := axisBound
    diagonalWeightedBound := diagonalBound
    recursiveSlices := hrec
    selfImprovementProducer := hself }

end Test

end MIPStarRE.LDT
