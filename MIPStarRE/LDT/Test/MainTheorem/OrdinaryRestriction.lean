import MIPStarRE.LDT.Test.MainTheorem.ClassicalAndBase

/-!
# Ordinary restricted-slice recursion

Statement-preserving slice of `MIPStarRE.LDT.Test.MainTheorem`.
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
public Section 6 boundary wrapper. -/
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

/-- Slice-recursion bridge data for the successor branch of `mainFormal`.

For each field element `x`, this package names the induction-hypothesis transport
fields that the `MainFormalSuccessorRecursiveSlices` definition currently hides:
a same-space projective strategy on the role-register space
`SameSpaceProjStrat params (Role × ι)` together with compatibility proofs
connecting it to the restricted slice from
`MainInductionStep.xRestrictedStrategy`.

When supplied together with a recursive induction hypothesis (see
`mainFormalSuccessorRecursiveSlices_ofSliceData`), this data can close the
`MainFormalSuccessorRecursiveSlices` requirement needed by
`MainFormalSuccessorBoundary`. -/
structure MainFormalSuccessorRecursiveSliceData (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) where
  /-- For each field element `x`, a same-space projective strategy on the
  role-register space that captures the restricted slice at `x`. -/
  sliceStrategy : Fq params → SameSpaceProjStrat params (Role × ι)
  /-- The slice strategy shares the symmetrization's bipartite state. -/
  sliceState_eq : ∀ x, (sliceStrategy x).state = (strategy.strategySymmetrization).state
  /-- The slice strategy's Alice point measurement matches the restricted
  point measurement from the main induction step.  (The Bob measurement is
  not needed for `MainFormalSuccessorRecursiveSlices`.) -/
  slicePoint_eq : ∀ x,
    (sliceStrategy x).pointMeasurementA =
    (MainInductionStep.xRestrictedStrategy params
      strategy.strategySymmetrization x).pointMeasurement
  /-- The slice strategy's Alice axis-parallel line measurement (underlying
  projective family, without the transport-covariant wrapper) matches the
  restricted axis-parallel measurement from the main induction step. -/
  sliceAxisParallelA_eq : ∀ x,
    (sliceStrategy x).axisParallelMeasurementA.toIdxProjMeas =
    (MainInductionStep.xRestrictedStrategy params
      strategy.strategySymmetrization x).axisParallelMeasurement.toIdxProjMeas
  /-- The slice strategy's Alice diagonal-line measurement (underlying
  projective family, without the transport-covariant wrapper) matches the
  restricted diagonal measurement from the main induction step. -/
  sliceDiagonalA_eq : ∀ x,
    (sliceStrategy x).diagonalMeasurementA.toIdxProjMeas =
    (MainInductionStep.xRestrictedStrategy params
      strategy.strategySymmetrization x).diagonalMeasurement
  /-- The slice strategy's Bob point measurement matches the same restricted
  point measurement.  The restricted interface is a symmetric one-register
  strategy, so the same restricted point family is the target for both
  registers of the same-space slice strategy. -/
  slicePointB_eq : ∀ x,
    (sliceStrategy x).pointMeasurementB =
    (MainInductionStep.xRestrictedStrategy params
      strategy.strategySymmetrization x).pointMeasurement
  /-- The slice strategy's Bob axis-parallel line measurement (underlying
  projective family, without the transport-covariant wrapper) matches the
  restricted axis-parallel measurement from the main induction step. -/
  sliceAxisParallelB_eq : ∀ x,
    (sliceStrategy x).axisParallelMeasurementB.toIdxProjMeas =
    (MainInductionStep.xRestrictedStrategy params
      strategy.strategySymmetrization x).axisParallelMeasurement.toIdxProjMeas
  /-- The slice strategy's Bob diagonal-line measurement (underlying projective
  family, without the transport-covariant wrapper) matches the restricted
  diagonal measurement from the main induction step. -/
  sliceDiagonalB_eq : ∀ x,
    (sliceStrategy x).diagonalMeasurementB.toIdxProjMeas =
    (MainInductionStep.xRestrictedStrategy params
      strategy.strategySymmetrization x).diagonalMeasurement
  /-- Each slice strategy passes LDT with the common symmetrized error `3 * eps`.

  Together with `sliceState_eq`, `slicePoint_eq`, `sliceAxisParallelA_eq`, and
  `sliceDiagonalA_eq`, together with the corresponding Bob-side fields above,
  every verifier-visible measurement of `sliceStrategy x` is constrained to
  match the restricted slice from the main induction step.  The symmetry
  witnesses (`permInvState`, `densityFixed`) are bundled in
  `SameSpaceProjStrat` and supplied independently for each `sliceStrategy x`;
  the one-register restricted strategy does not itself carry separate
  same-space symmetry witnesses to compare against.

  TODO(#1037, #834, #422): the successor-case `mainFormal` proof will need
  a consumer of these compatibility fields (or their `.toIdxProjMeas`-free
  counterparts) to close the recursive call. -/
  slicePasses : ∀ x, (sliceStrategy x).PassesLowIndividualDegreeTest (3 * eps)

/-- The passing hypothesis for a pinned slice bounds the restricted
point-agreement branch.

The new Bob-side point compatibility is the essential input: after rewriting
both provers' point measurements to the restricted slice, the general
three-branch estimate for a passing same-space strategy becomes a statement
  about `MainInductionStep.xRestrictedStrategy`.  Since `slicePasses x` is
  stated with error `3 * eps`, the resulting branch bound is
  `3 * (3 * eps)`. -/
theorem mainFormalSuccessorRestrictedPointAgreement_le_ofSliceData
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (sliceData : MainFormalSuccessorRecursiveSliceData params strategy eps hpass)
    (x : Fq params) :
    bipartiteConsError
      (MainInductionStep.xRestrictedStrategy params
        strategy.strategySymmetrization x).state
      (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas
        (MainInductionStep.xRestrictedStrategy params
          strategy.strategySymmetrization x).pointMeasurement)
      (IdxProjMeas.toIdxSubMeas
        (MainInductionStep.xRestrictedStrategy params
          strategy.strategySymmetrization x).pointMeasurement) ≤
    3 * (3 * eps) := by
  have hpoint :=
    SameSpaceProjStrat.point_agreement_le_three_mul (sliceData.slicePasses x)
  simpa [sliceData.sliceState_eq x, sliceData.slicePoint_eq x,
    sliceData.slicePointB_eq x] using hpoint

/-- The passing hypothesis for a pinned slice bounds the restricted
axis-parallel branch.

The two role choices in the same-space axis branch become the same restricted
axis-parallel test after applying the Alice and Bob compatibility fields.  The
swap-invariance of the slice state identifies the left-line/right-point term
with the left-point/right-line term, so the role average is precisely the
restricted branch. -/
theorem mainFormalSuccessorRestrictedAxisParallel_le_ofSliceData
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (sliceData : MainFormalSuccessorRecursiveSliceData params strategy eps hpass)
    (x : Fq params) :
    (MainInductionStep.xRestrictedStrategy params
      strategy.strategySymmetrization x).axisParallelFailureProbability ≤
    3 * (3 * eps) := by
  let restricted :=
    MainInductionStep.xRestrictedStrategy params strategy.strategySymmetrization x
  let slice := sliceData.sliceStrategy x
  let axParDist := uniformDistribution (AxisParallelTestSample params)
  let leftTerm :=
    bipartiteConsError slice.state axParDist
      (axisParallelLineAnswerFamily slice.leftAsSymmetric)
      (axisParallelPointAnswerFamily slice.rightAsSymmetric)
  let rightTerm :=
    bipartiteConsError slice.state axParDist
      (axisParallelPointAnswerFamily slice.leftAsSymmetric)
      (axisParallelLineAnswerFamily slice.rightAsSymmetric)
  have hleft_eq_restricted : leftTerm = restricted.axisParallelFailureProbability := by
    calc
      leftTerm =
          bipartiteConsError slice.state axParDist
            (axisParallelPointAnswerFamily slice.rightAsSymmetric)
            (axisParallelLineAnswerFamily slice.leftAsSymmetric) := by
            exact bipartiteConsError_symm_of_density_fixed slice.state slice.densityFixed
              axParDist (axisParallelLineAnswerFamily slice.leftAsSymmetric)
              (axisParallelPointAnswerFamily slice.rightAsSymmetric)
      _ = restricted.axisParallelFailureProbability := by
            unfold restricted bipartiteConsError
              MainInductionStep.RestrictedSymStrat.axisParallelFailureProbability
              MainInductionStep.RestrictedSymStrat.axisParallelPointAnswerFamily
              MainInductionStep.RestrictedSymStrat.axisParallelLineAnswerFamily
              axisParallelPointAnswerFamily axisParallelLineAnswerFamily
            apply avgOver_congr
            intro s
            simp [slice, SameSpaceProjStrat.leftAsSymmetric,
              SameSpaceProjStrat.rightAsSymmetric, sliceData.sliceState_eq x,
              sliceData.slicePointB_eq x, sliceData.sliceAxisParallelA_eq x]
  have hright_eq_restricted : rightTerm = restricted.axisParallelFailureProbability := by
    unfold rightTerm restricted bipartiteConsError
      MainInductionStep.RestrictedSymStrat.axisParallelFailureProbability
      MainInductionStep.RestrictedSymStrat.axisParallelPointAnswerFamily
      MainInductionStep.RestrictedSymStrat.axisParallelLineAnswerFamily
      axisParallelPointAnswerFamily axisParallelLineAnswerFamily
    apply avgOver_congr
    intro s
    simp [slice, SameSpaceProjStrat.leftAsSymmetric, SameSpaceProjStrat.rightAsSymmetric,
      sliceData.sliceState_eq x, sliceData.slicePoint_eq x,
      sliceData.sliceAxisParallelB_eq x]
  have hrole :
      slice.axisParallelRoleAverage = restricted.axisParallelFailureProbability := by
    unfold SameSpaceProjStrat.axisParallelRoleAverage
    change (leftTerm + rightTerm) / 2 = restricted.axisParallelFailureProbability
    rw [hleft_eq_restricted, hright_eq_restricted]
    ring
  have haxis :=
    SameSpaceProjStrat.axisParallelRoleAverage_le_three_mul (sliceData.slicePasses x)
  rw [hrole] at haxis
  simpa [restricted] using haxis

/-- The passing hypothesis for a pinned slice bounds the restricted diagonal
branch.

As in the axis-parallel case, the Alice and Bob diagonal compatibility fields
identify the two same-space role choices with the restricted diagonal test.
The slice state's swap symmetry removes the order of the two prover registers
inside the consistency defect. -/
theorem mainFormalSuccessorRestrictedDiagonal_le_ofSliceData
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (sliceData : MainFormalSuccessorRecursiveSliceData params strategy eps hpass)
    (x : Fq params) :
    (MainInductionStep.xRestrictedStrategy params
      strategy.strategySymmetrization x).diagonalFailureProbability ≤
    3 * (3 * eps) := by
  let restricted :=
    MainInductionStep.xRestrictedStrategy params strategy.strategySymmetrization x
  let slice := sliceData.sliceStrategy x
  have hrole :
      slice.diagonalRoleAverage = restricted.diagonalFailureProbability := by
    unfold SameSpaceProjStrat.diagonalRoleAverage
      MainInductionStep.RestrictedSymStrat.diagonalFailureProbability
      MainInductionStep.RestrictedSymStrat.restrictedDiagonalPointAnswerFamily
      MainInductionStep.RestrictedSymStrat.restrictedDiagonalLineAnswerFamily
    refine congrArg (fun t => (1 / (params.m : Error)) * t) ?_
    refine Finset.sum_congr rfl ?_
    intro j _
    let dist := uniformDistribution (RestrictedDiagonalSample params j)
    let leftTerm :=
      bipartiteConsError slice.state dist
        (diagonalLineAnswerFamily slice.leftAsSymmetric j)
        (diagonalPointAnswerFamily slice.rightAsSymmetric j)
    let rightTerm :=
      bipartiteConsError slice.state dist
        (diagonalPointAnswerFamily slice.leftAsSymmetric j)
        (diagonalLineAnswerFamily slice.rightAsSymmetric j)
    have hleft_eq_restricted :
        leftTerm =
          bipartiteConsError restricted.state dist
            (MainInductionStep.RestrictedSymStrat.restrictedDiagonalPointAnswerFamily
              restricted j)
            (MainInductionStep.RestrictedSymStrat.restrictedDiagonalLineAnswerFamily
              restricted j) := by
      calc
        leftTerm =
            bipartiteConsError slice.state dist
              (diagonalPointAnswerFamily slice.rightAsSymmetric j)
              (diagonalLineAnswerFamily slice.leftAsSymmetric j) := by
              exact bipartiteConsError_symm_of_density_fixed slice.state slice.densityFixed
                dist (diagonalLineAnswerFamily slice.leftAsSymmetric j)
                (diagonalPointAnswerFamily slice.rightAsSymmetric j)
        _ = bipartiteConsError restricted.state dist
              (MainInductionStep.RestrictedSymStrat.restrictedDiagonalPointAnswerFamily
                restricted j)
              (MainInductionStep.RestrictedSymStrat.restrictedDiagonalLineAnswerFamily
                restricted j) := by
              unfold bipartiteConsError
                MainInductionStep.RestrictedSymStrat.restrictedDiagonalPointAnswerFamily
                MainInductionStep.RestrictedSymStrat.restrictedDiagonalLineAnswerFamily
                diagonalPointAnswerFamily diagonalLineAnswerFamily
              apply avgOver_congr
              intro s
              simp [restricted, slice, SameSpaceProjStrat.leftAsSymmetric,
                SameSpaceProjStrat.rightAsSymmetric, sliceData.sliceState_eq x,
                sliceData.slicePointB_eq x, sliceData.sliceDiagonalA_eq x]
    have hright_eq_restricted :
        rightTerm =
          bipartiteConsError restricted.state dist
            (MainInductionStep.RestrictedSymStrat.restrictedDiagonalPointAnswerFamily
              restricted j)
            (MainInductionStep.RestrictedSymStrat.restrictedDiagonalLineAnswerFamily
              restricted j) := by
      unfold rightTerm bipartiteConsError
        MainInductionStep.RestrictedSymStrat.restrictedDiagonalPointAnswerFamily
        MainInductionStep.RestrictedSymStrat.restrictedDiagonalLineAnswerFamily
        diagonalPointAnswerFamily diagonalLineAnswerFamily
      apply avgOver_congr
      intro s
      simp [restricted, slice, SameSpaceProjStrat.leftAsSymmetric,
        SameSpaceProjStrat.rightAsSymmetric, sliceData.sliceState_eq x,
        sliceData.slicePoint_eq x, sliceData.sliceDiagonalB_eq x]
    change (leftTerm + rightTerm) / 2 =
      bipartiteConsError restricted.state dist
        (MainInductionStep.RestrictedSymStrat.restrictedDiagonalPointAnswerFamily
          restricted j)
        (MainInductionStep.RestrictedSymStrat.restrictedDiagonalLineAnswerFamily
          restricted j)
    rw [hleft_eq_restricted, hright_eq_restricted]
    ring
  have hdiagonal :=
    SameSpaceProjStrat.diagonalRoleAverage_le_three_mul (sliceData.slicePasses x)
  rw [hrole] at hdiagonal
  simpa [restricted] using hdiagonal

/-- Convert per-slice induction-hypothesis data into a
`MainFormalSuccessorRecursiveSlices` witness.

This is the abstract induction-step lemma for #1021.  Given the honest
`MainFormalSuccessorRecursiveSliceData` together with a recursive induction
hypothesis that delivers `mainInductionError`-bounded polynomial measurements
for each slice strategy, this rewrites the state and point-measurement
compatibilities to produce the exact `MainFormalSuccessorRecursiveSlices` field
needed by `MainFormalSuccessorBoundary`.

The induction hypothesis `hrecSlice` mirrors what `mainInductionPublicWrapper`
(or, equivalently, a recursive call to `mainFormal`) returns for the predecessor
dimension: a polynomial measurement on the role-register space with consistency
bounded by the main induction error evaluated at the restricted-profile bounds. -/
theorem mainFormalSuccessorRecursiveSlices_ofSliceData
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (haxisWeightedBound : MainFormalSuccessorAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound :
      MainFormalSuccessorDiagonalWeightedBound params strategy eps)
    (sliceData : MainFormalSuccessorRecursiveSliceData params strategy eps hpass)
    (hrecSlice : ∀ (x : Fq params),
      ∃ error : Error, ∃ G : Measurement (Polynomial params) (Role × ι),
        ConsRel (sliceData.sliceStrategy x).state
          (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas (sliceData.sliceStrategy x).pointMeasurementA)
          (polynomialEvaluationFamily params G.toSubMeas)
          error ∧
        error ≤
          let hrestrict :=
            mainFormalSuccessorRestrictionPackage params strategy eps hpass
              haxisWeightedBound hdiagonalWeightedBound
          MainInductionStep.mainInductionError params k
            (hrestrict.profile.axisParallel x)
            (hrestrict.profile.selfConsistency x)
            (hrestrict.profile.diagonal x)) :
    MainFormalSuccessorRecursiveSlices params strategy eps hpass k
      haxisWeightedBound hdiagonalWeightedBound := by
  intro x
  rcases hrecSlice x with ⟨error, G, hG, herr⟩
  refine ⟨error, G, ?_, herr⟩
  -- Rewrite the state and point measurement using the slice-data compatibilities
  simpa [sliceData.sliceState_eq x, sliceData.slicePoint_eq x] using hG
/-- Build the successor boundary from bridge inputs instead of the
already-packaged self-improvement producer.

This is the public-facing constructor for issue #1020: it wires the
honest per-slice Section 9 bridge inputs through the existing
`mainFormalSuccessorSelfImprovementProducer_ofBridgeInputs` conversion and
packages them together with the weighted restricted-probability fields and
the recursive slice witnesses into a `MainFormalSuccessorBoundary`.

The weighted restricted-probability fields are discharged from `hpass`
by the public Section 6 weighted-bound lemmas, matching the pattern of
`mainFormalSuccessorBoundary_ofRecursiveSelfImprovement`. -/
noncomputable def mainFormalSuccessorBoundary_ofBridgeInputs
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (hrec : MainFormalSuccessorRecursiveSlices params strategy eps hpass k
      (mainFormalSuccessorAxisWeightedBound_ofPass params strategy eps hpass)
      (mainFormalSuccessorDiagonalWeightedBound_ofPass params strategy eps hpass))
    (hbridge : MainFormalSuccessorSelfImprovementBridgeInputs params strategy eps hpass k
      (mainFormalSuccessorAxisWeightedBound_ofPass params strategy eps hpass)
      (mainFormalSuccessorDiagonalWeightedBound_ofPass params strategy eps hpass)) :
    MainFormalSuccessorBoundary params strategy eps hpass k :=
  let axisBound := mainFormalSuccessorAxisWeightedBound_ofPass params strategy eps hpass
  let diagonalBound :=
    mainFormalSuccessorDiagonalWeightedBound_ofPass params strategy eps hpass
  { axisWeightedBound := axisBound
    diagonalWeightedBound := diagonalBound
    recursiveSlices := hrec
    selfImprovementProducer :=
      mainFormalSuccessorSelfImprovementProducer_ofBridgeInputs params strategy eps hpass k
        axisBound diagonalBound hbridge }

/-- Build the successor boundary from an explicit predecessor induction
hypothesis and the Section 9 bridge inputs.

The predecessor hypothesis is stated at the exact Section 6 strength consumed by
`MainFormalSuccessorRecursiveSlices`: for each restricted slice it supplies a
polynomial measurement bounded by the restricted-profile
`mainInductionError`. This wrapper is non-recursive; it only transports those
slice witnesses across `MainFormalSuccessorRecursiveSliceData` and then reuses
`mainFormalSuccessorBoundary_ofBridgeInputs`. -/
noncomputable def mainFormalSuccessorBoundary_ofPredecessorInduction
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (sliceData : MainFormalSuccessorRecursiveSliceData params strategy eps hpass)
    (hpredecessor : ∀ (x : Fq params),
      ∃ error : Error, ∃ G : Measurement (Polynomial params) (Role × ι),
        ConsRel (sliceData.sliceStrategy x).state
          (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas (sliceData.sliceStrategy x).pointMeasurementA)
          (polynomialEvaluationFamily params G.toSubMeas)
          error ∧
        error ≤
          let hrestrict :=
            mainFormalSuccessorRestrictionPackage params strategy eps hpass
              (mainFormalSuccessorAxisWeightedBound_ofPass params strategy eps hpass)
              (mainFormalSuccessorDiagonalWeightedBound_ofPass params strategy eps hpass)
          MainInductionStep.mainInductionError params k
            (hrestrict.profile.axisParallel x)
            (hrestrict.profile.selfConsistency x)
            (hrestrict.profile.diagonal x))
    (hbridge : MainFormalSuccessorSelfImprovementBridgeInputs params strategy eps hpass k
      (mainFormalSuccessorAxisWeightedBound_ofPass params strategy eps hpass)
      (mainFormalSuccessorDiagonalWeightedBound_ofPass params strategy eps hpass)) :
    MainFormalSuccessorBoundary params strategy eps hpass k :=
  mainFormalSuccessorBoundary_ofBridgeInputs params strategy eps hpass k
    (mainFormalSuccessorRecursiveSlices_ofSliceData params strategy eps hpass k
      (mainFormalSuccessorAxisWeightedBound_ofPass params strategy eps hpass)
      (mainFormalSuccessorDiagonalWeightedBound_ofPass params strategy eps hpass)
      sliceData hpredecessor)
    hbridge

/-- Successor-case Section 6 handoff for `mainFormal`.

This is the actual invocation of
`MainInductionStep.mainInductionPublicWrapper` on the role-register
symmetrization. It proves that, once the `MainFormalSuccessorBoundary` data are
available and the Section 6 side condition `400 * m * d ≤ k` holds, the public
wrapper returns the global polynomial measurement used by the later
unsymmetrization / Schwartz--Zippel / projectivization cascade.

Universe note: the explicit `[FieldModel.{0} params.q]` matches the Section 6
wrapper's universe; the eventual `mainFormal` residual closure must transport or
instantiate this same base-universe field model when choosing predecessor
parameters. -/
theorem mainFormalSuccessorMainInductionPublicWrapper
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (hd : 0 < params.d)
    (boundary : MainFormalSuccessorBoundary params strategy eps hpass k)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ G : Measurement (Polynomial params.next) (Role × ι),
      ConsRel (strategy.strategySymmetrization).state
        (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas (strategy.strategySymmetrization).pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (MainInductionStep.mainInductionError params.next k
          (3 * eps) (3 * eps) (3 * eps)) :=
  MainInductionStep.mainInductionPublicWrapper params
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
