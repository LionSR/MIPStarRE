import MIPStarRE.LDT.Test.MainTheorem.RoleRegister.Core
import MIPStarRE.LDT.Test.MainTheorem.AnswerValuedRestriction

/-!
# Role-register residuals

Role-register measurement construction for the `mainFormal` assembly.  This
module imports `RoleRegister.Core` (defining `MainFormalRoleMeasurementPackage`
and the predecessor-transport helpers) and introduces the branch-level
residual structures for producing the Section 6 role package:

* `MainFormalRolePackageSuccessorResidual` — explicit successor-branch data
  (predecessor decomposition, successor-boundary data, positivity, and `k ≥ 1`)
  for the ordinary restricted-slice route.

* `MainFormalRolePackageAnswerSuccessorResidual` — the answer-valued
  counterpart carrying `MainFormalSuccessorAnswerBoundary`.

* `MainFormalRolePackageBranchResidual` (inductive type) — the three
  alternatives for the role branch: base dimension (`m = 1`), ordinary
  successor, or answer-valued successor.

Each residual can be converted to a concrete `MainFormalRolePackageResidual`
via `toRolePackageResidual` once the public `400·m·d ≤ k` side condition
is supplied.  The constructors (`ofSuccessorBridgeInputs`,
`ofAnswerSuccessorBridgeInputs`, etc.) are structural and do not call
`mainFormal`; they stop before the line-130 orthonormalization and
completion interfaces.

## References

* Paper: `references/ldt-paper/inductive_step.tex`,
  symmetrization with role register and factor-two block estimates
  (lines 97–108).
* Blueprint: `blueprint/src/chapter/ch10_induction.tex`,
  `\label{rem:main-formal-lean-residual-packages}`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-- Successor-branch data for producing the Section 6 role package.

This is narrower than an arbitrary `MainFormalRolePackageResidual`: it contains an
explicit predecessor `pred` with `pred.next = params` and the successor-boundary
data for the transported strategy over `pred.next`. The Section 6 large-`k`
side condition is supplied directly to the conversion from the public theorem's
current-dimension hypothesis and then weakened to the predecessor dimension. -/
structure MainFormalRolePackageSuccessorResidual
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ) where
  /-- A predecessor whose successor is the current parameter bundle. -/
  successor : Parameters.SuccessorDecomposition params
  /-- The bundled successor-boundary inputs for the transported strategy. -/
  boundary :
    letI : FieldModel.{0} successor.pred.q := fieldModelOfSuccessorDecomposition successor
    MainFormalSuccessorBoundary successor.pred
      (projStratTransportSuccessor strategy successor) eps
      (passesLowIndividualDegreeTest_transportSuccessor hpass successor) k
  /-- Positivity of the predecessor degree parameter, needed by the Section 6 wrapper. -/
  dimensionPositive : 0 < successor.pred.d
  /-- The positive-`k` side condition used by the Section 6 wrapper. -/
  kPositive : 1 ≤ k

/-- Type of recursive slice witnesses for the predecessor determined by a
non-base current parameter bundle.  This private abbreviation keeps the three
successor-assembly entry points below from repeating the transported predecessor
setup in every binder. -/
private abbrev successorRecursiveSlicesInput
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hm_ne_one : params.m ≠ 1) : Prop :=
  let successor := Parameters.successorDecompositionOfNeOne params hm_ne_one
  letI : FieldModel.{0} successor.pred.q := fieldModelOfSuccessorDecomposition successor
  let transportedStrategy := projStratTransportSuccessor strategy successor
  let transportedPass := passesLowIndividualDegreeTest_transportSuccessor hpass successor
  MainFormalSuccessorRecursiveSlices successor.pred transportedStrategy eps transportedPass k
    (mainFormalSuccessorAxisWeightedBound_ofPass
      successor.pred transportedStrategy eps transportedPass)
    (mainFormalSuccessorDiagonalWeightedBound_ofPass
      successor.pred transportedStrategy eps transportedPass)

/-- Type of self-improvement bridge inputs for the predecessor determined by a
non-base current parameter bundle. -/
private abbrev successorSelfImprovementBridgeInput
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hm_ne_one : params.m ≠ 1) : Type _ :=
  let successor := Parameters.successorDecompositionOfNeOne params hm_ne_one
  letI : FieldModel.{0} successor.pred.q := fieldModelOfSuccessorDecomposition successor
  let transportedStrategy := projStratTransportSuccessor strategy successor
  let transportedPass := passesLowIndividualDegreeTest_transportSuccessor hpass successor
  MainFormalSuccessorSelfImprovementBridgeInputs
    successor.pred transportedStrategy eps transportedPass k
    (mainFormalSuccessorAxisWeightedBound_ofPass
      successor.pred transportedStrategy eps transportedPass)
    (mainFormalSuccessorDiagonalWeightedBound_ofPass
      successor.pred transportedStrategy eps transportedPass)

namespace MainFormalRolePackageSuccessorResidual

/-- Convert explicit successor-branch data into the isolated Section 6 role
package residual, using the public current-dimension large-`k` hypothesis. -/
theorem toRolePackageResidual
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    (residual : MainFormalRolePackageSuccessorResidual params strategy eps hpass k)
    (hk_large : 400 * params.m * params.d ≤ k) :
    Nonempty (MainFormalRolePackageResidual params strategy eps hpass k) := by
  rcases residual with ⟨⟨pred, hnext⟩, boundary, hd, hk_pos⟩
  subst params
  have hk_pred : 400 * pred.m * pred.d ≤ k := by
    have hm_le : pred.m ≤ pred.m + 1 := Nat.le_succ pred.m
    have hmono : 400 * pred.m * pred.d ≤ 400 * (pred.m + 1) * pred.d :=
      Nat.mul_le_mul_right pred.d (Nat.mul_le_mul_left 400 hm_le)
    exact le_trans hmono (by simpa [Parameters.next] using hk_large)
  -- Keep the transported predecessor instance explicit: `boundary` was stored
  -- under `fieldModelOfSuccessorDecomposition`, and the synthesized canonical
  -- `FieldModel.{0} pred.q` is not definitionally the same instance.
  letI : FieldModel.{0} pred.q :=
    fieldModelOfSuccessorDecomposition (params := pred.next) ⟨pred, rfl⟩
  let transportedStrategy : SameSpaceProjStrat pred.next ι :=
    projStratTransportSuccessor strategy ⟨pred, rfl⟩
  have transportedPass : transportedStrategy.PassesLowIndividualDegreeTest eps := by
    simpa [transportedStrategy] using
      (passesLowIndividualDegreeTest_transportSuccessor hpass ⟨pred, rfl⟩)
  have boundary' :
      MainFormalSuccessorBoundary pred transportedStrategy eps transportedPass k := by
    simpa [transportedStrategy, transportedPass] using boundary
  rcases MainFormalRolePackageResidual.ofSuccessorBoundary pred transportedStrategy eps k
      transportedPass hd boundary' hk_pos hk_pred with ⟨roleResidual⟩
  refine ⟨{ roleMeasurement := roleResidual.roleMeasurement, section6Consistency := ?_ }⟩
  simpa [transportedStrategy, projStratTransportSuccessor, fieldModelOfSuccessorDecomposition]
    using roleResidual.section6Consistency

/-- Constructor for the common syntactic-successor case. -/
def ofSyntacticSuccessor
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error) (k : ℕ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hd : 0 < params.d)
    (boundary : MainFormalSuccessorBoundary params strategy eps hpass k)
    (hk_pos : 1 ≤ k) :
    MainFormalRolePackageSuccessorResidual params.next strategy eps hpass k where
  successor := ⟨params, rfl⟩
  boundary := by
    simpa using boundary
  dimensionPositive := hd
  kPositive := hk_pos

/-- Assemble the successor role-package residual from recursive slices and
self-improvement bridge inputs.

This is the non-base branch constructor used by the live `mainFormal` split.  It
does not assume a raw Section 6 witness: the caller supplies exactly the two
analytic successor inputs for the transported predecessor, namely recursive
slice witnesses and the self-improvement bridge data.  This constructor packages
them through `mainFormalSuccessorBoundary_ofBridgeInputs`; line-130
orthonormalization and completion inputs remain downstream hypotheses. -/
noncomputable def ofSuccessorBridgeInputs
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hm_ne_one : params.m ≠ 1)
    (hd : 0 < params.d)
    (hk_pos : 1 ≤ k)
    (hrec : successorRecursiveSlicesInput (k := k) hpass hm_ne_one)
    (hbridge : successorSelfImprovementBridgeInput (k := k) hpass hm_ne_one) :
    MainFormalRolePackageSuccessorResidual params strategy eps hpass k := by
  let successor := Parameters.successorDecompositionOfNeOne params hm_ne_one
  letI : FieldModel.{0} successor.pred.q := fieldModelOfSuccessorDecomposition successor
  let transportedStrategy := projStratTransportSuccessor strategy successor
  let transportedPass := passesLowIndividualDegreeTest_transportSuccessor hpass successor
  refine
    { successor := successor
      boundary := ?_
      dimensionPositive := ?_
      kPositive := hk_pos }
  · exact
      mainFormalSuccessorBoundary_ofBridgeInputs successor.pred transportedStrategy eps
        transportedPass k hrec hbridge
  · rcases successor with ⟨pred, hnext⟩
    subst params
    simpa [Parameters.next] using hd

end MainFormalRolePackageSuccessorResidual

/-- Answer-valued successor-branch data for producing the Section 6 role package. -/
structure MainFormalRolePackageAnswerSuccessorResidual
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ) where
  /-- A predecessor whose successor is the current parameter bundle. -/
  successor : Parameters.SuccessorDecomposition params
  /-- The bundled answer-valued successor-boundary inputs for the transported strategy. -/
  boundary :
    letI : FieldModel.{0} successor.pred.q := fieldModelOfSuccessorDecomposition successor
    MainFormalSuccessorAnswerBoundary successor.pred
      (projStratTransportSuccessor strategy successor) eps
      (passesLowIndividualDegreeTest_transportSuccessor hpass successor) k
  /-- Positivity of the predecessor degree parameter, needed by the Section 6 wrapper. -/
  dimensionPositive : 0 < successor.pred.d
  /-- The positive-`k` side condition used by the Section 6 wrapper. -/
  kPositive : 1 ≤ k

/-- Type of answer-valued recursive slice witnesses for the predecessor
determined by a non-base current parameter bundle. -/
private abbrev answerSuccessorRecursiveSlicesInput
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hm_ne_one : params.m ≠ 1) : Prop :=
  let successor := Parameters.successorDecompositionOfNeOne params hm_ne_one
  letI : FieldModel.{0} successor.pred.q := fieldModelOfSuccessorDecomposition successor
  let transportedStrategy := projStratTransportSuccessor strategy successor
  let transportedPass := passesLowIndividualDegreeTest_transportSuccessor hpass successor
  MainFormalSuccessorAnswerRecursiveSlices successor.pred transportedStrategy eps transportedPass k
    (mainFormalSuccessorAnswerAxisWeightedBound_ofPass
      successor.pred transportedStrategy eps transportedPass)
    (mainFormalSuccessorAnswerDiagonalWeightedBound_ofPass
      successor.pred transportedStrategy eps transportedPass)

/-- Type of answer-valued self-improvement producers for the predecessor
determined by a non-base current parameter bundle. -/
private abbrev answerSuccessorSelfImprovementInput
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hm_ne_one : params.m ≠ 1) : Type _ :=
  let successor := Parameters.successorDecompositionOfNeOne params hm_ne_one
  letI : FieldModel.{0} successor.pred.q := fieldModelOfSuccessorDecomposition successor
  let transportedStrategy := projStratTransportSuccessor strategy successor
  let transportedPass := passesLowIndividualDegreeTest_transportSuccessor hpass successor
  MainFormalSuccessorAnswerSelfImprovementProducer
    successor.pred transportedStrategy eps transportedPass k
    (mainFormalSuccessorAnswerAxisWeightedBound_ofPass
      successor.pred transportedStrategy eps transportedPass)
    (mainFormalSuccessorAnswerDiagonalWeightedBound_ofPass
      successor.pred transportedStrategy eps transportedPass)

/-- Type of answer-valued self-improvement bridge inputs for the predecessor
determined by a non-base current parameter bundle.

This is the load-bearing companion to `answerSuccessorSelfImprovementInput`: it
supplies exactly the per-slice Section 9 bridge data, and its conversion into a
self-improvement producer is performed internally by the
`MainFormalRolePackageAnswerSuccessorResidual.ofAnswerSuccessorBridgeInputs`
constructor below. -/
private abbrev answerSuccessorSelfImprovementBridgeInput
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hm_ne_one : params.m ≠ 1) : Type _ :=
  let successor := Parameters.successorDecompositionOfNeOne params hm_ne_one
  letI : FieldModel.{0} successor.pred.q := fieldModelOfSuccessorDecomposition successor
  let transportedStrategy := projStratTransportSuccessor strategy successor
  let transportedPass := passesLowIndividualDegreeTest_transportSuccessor hpass successor
  MainFormalSuccessorAnswerSelfImprovementBridgeInputs
    successor.pred transportedStrategy eps transportedPass k
    (mainFormalSuccessorAnswerAxisWeightedBound_ofPass
      successor.pred transportedStrategy eps transportedPass)
    (mainFormalSuccessorAnswerDiagonalWeightedBound_ofPass
      successor.pred transportedStrategy eps transportedPass)

/-- Type of answer-valued per-slice induction packages for the predecessor
determined by a non-base current parameter bundle.

The recursive slice witnesses produced by
`mainFormalSuccessorAnswerRecursiveSlices_ofInductionPackage` consume exactly an
input of this shape.  This is an adapter package for the predecessor Section 6
induction hypothesis, not the direct output of a recursive call to
`mainFormal`. -/
private abbrev answerSuccessorPerSliceInductionPackageInput
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hm_ne_one : params.m ≠ 1) : Type _ :=
  let successor := Parameters.successorDecompositionOfNeOne params hm_ne_one
  letI : FieldModel.{0} successor.pred.q := fieldModelOfSuccessorDecomposition successor
  let transportedStrategy := projStratTransportSuccessor strategy successor
  let transportedPass := passesLowIndividualDegreeTest_transportSuccessor hpass successor
  MainInductionStep.AnswerPerSliceInductionPackage successor.pred
    transportedStrategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps)
    (mainFormalSuccessorAnswerRestrictionPackage successor.pred transportedStrategy eps
      transportedPass
      (mainFormalSuccessorAnswerAxisWeightedBound_ofPass
        successor.pred transportedStrategy eps transportedPass)
      (mainFormalSuccessorAnswerDiagonalWeightedBound_ofPass
        successor.pred transportedStrategy eps transportedPass))
    k

namespace MainFormalRolePackageAnswerSuccessorResidual

/-- Convert explicit answer-valued successor-branch data into the isolated Section 6
role-package residual, using the public current-dimension large-`k` hypothesis. -/
theorem toRolePackageResidual
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    (residual : MainFormalRolePackageAnswerSuccessorResidual params strategy eps hpass k)
    (hk_large : 400 * params.m * params.d ≤ k) :
    Nonempty (MainFormalRolePackageResidual params strategy eps hpass k) := by
  rcases residual with ⟨⟨pred, hnext⟩, boundary, hd, hk_pos⟩
  subst params
  have hk_pred : 400 * pred.m * pred.d ≤ k := by
    have hm_le : pred.m ≤ pred.m + 1 := Nat.le_succ pred.m
    have hmono : 400 * pred.m * pred.d ≤ 400 * (pred.m + 1) * pred.d :=
      Nat.mul_le_mul_right pred.d (Nat.mul_le_mul_left 400 hm_le)
    exact le_trans hmono (by simpa [Parameters.next] using hk_large)
  letI : FieldModel.{0} pred.q :=
    fieldModelOfSuccessorDecomposition (params := pred.next) ⟨pred, rfl⟩
  let transportedStrategy : SameSpaceProjStrat pred.next ι :=
    projStratTransportSuccessor strategy ⟨pred, rfl⟩
  have transportedPass : transportedStrategy.PassesLowIndividualDegreeTest eps := by
    simpa [transportedStrategy] using
      (passesLowIndividualDegreeTest_transportSuccessor hpass ⟨pred, rfl⟩)
  have boundary' :
      MainFormalSuccessorAnswerBoundary pred transportedStrategy eps transportedPass k := by
    simpa [transportedStrategy, transportedPass] using boundary
  rcases mainFormalSuccessorAnswerMainInductionPublicWrapper pred transportedStrategy eps
      transportedPass k hd boundary' hk_pos hk_pred with ⟨G, hG⟩
  refine ⟨{ roleMeasurement := G, section6Consistency := ?_ }⟩
  simpa [transportedStrategy, projStratTransportSuccessor, fieldModelOfSuccessorDecomposition]
    using hG

/-- Constructor for the common syntactic-successor answer-valued case. -/
def ofSyntacticSuccessor
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error) (k : ℕ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hd : 0 < params.d)
    (boundary : MainFormalSuccessorAnswerBoundary params strategy eps hpass k)
    (hk_pos : 1 ≤ k) :
    MainFormalRolePackageAnswerSuccessorResidual params.next strategy eps hpass k where
  successor := ⟨params, rfl⟩
  boundary := by
    simpa using boundary
  dimensionPositive := hd
  kPositive := hk_pos

/-- Assemble the answer-valued successor role-package residual from recursive
answer slices and an answer-valued self-improvement producer.

This is the answer-register counterpart of the ordinary successor role assembly.
It packages exactly the answer-side Section 6 inputs through
`mainFormalSuccessorAnswerBoundary_ofRecursiveSelfImprovement`; it does not call
`mainFormal` and it leaves the completion and line-169 interfaces downstream. -/
noncomputable def ofAnswerSuccessorRecursiveSelfImprovement
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hm_ne_one : params.m ≠ 1)
    (hd : 0 < params.d)
    (hk_pos : 1 ≤ k)
    (hrec : answerSuccessorRecursiveSlicesInput (k := k) hpass hm_ne_one)
    (hself : answerSuccessorSelfImprovementInput (k := k) hpass hm_ne_one) :
    MainFormalRolePackageAnswerSuccessorResidual params strategy eps hpass k :=
  let successor := Parameters.successorDecompositionOfNeOne params hm_ne_one
  letI : FieldModel.{0} successor.pred.q := fieldModelOfSuccessorDecomposition successor
  let transportedStrategy := projStratTransportSuccessor strategy successor
  let transportedPass := passesLowIndividualDegreeTest_transportSuccessor hpass successor
  { successor := successor
    boundary :=
      mainFormalSuccessorAnswerBoundary_ofRecursiveSelfImprovement successor.pred
        transportedStrategy eps transportedPass k hrec hself
    dimensionPositive := by
      rcases successor with ⟨pred, hnext⟩
      subst params
      simpa [Parameters.next] using hd
    kPositive := hk_pos }

/-- Assemble the answer-valued successor role-package residual from recursive
answer slices and answer-side self-improvement bridge inputs.

This is the bridge-inputs counterpart of
`ofAnswerSuccessorRecursiveSelfImprovement` and the answer-side counterpart of
`MainFormalRolePackageSuccessorResidual.ofSuccessorBridgeInputs`.  Instead of an
already-built self-improvement producer the caller supplies the per-slice
Section 9 bridge data, which is converted internally through
`mainFormalSuccessorAnswerSelfImprovementProducer_ofBridgeInputs` and
`mainFormalSuccessorAnswerBoundary_ofBridgeInputs`.  This packages the
answer-side adapters merged in #1062–#1069 into a single Test-level constructor
that does not call `mainFormal` and leaves the line-130 completion and line-169
interfaces downstream. -/
noncomputable def ofAnswerSuccessorBridgeInputs
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hm_ne_one : params.m ≠ 1)
    (hd : 0 < params.d)
    (hk_pos : 1 ≤ k)
    (hrec : answerSuccessorRecursiveSlicesInput (k := k) hpass hm_ne_one)
    (hbridge : answerSuccessorSelfImprovementBridgeInput (k := k) hpass hm_ne_one) :
    MainFormalRolePackageAnswerSuccessorResidual params strategy eps hpass k :=
  let successor := Parameters.successorDecompositionOfNeOne params hm_ne_one
  letI : FieldModel.{0} successor.pred.q := fieldModelOfSuccessorDecomposition successor
  let transportedStrategy := projStratTransportSuccessor strategy successor
  let transportedPass := passesLowIndividualDegreeTest_transportSuccessor hpass successor
  { successor := successor
    boundary :=
      mainFormalSuccessorAnswerBoundary_ofBridgeInputs successor.pred
        transportedStrategy eps transportedPass k hrec hbridge
    dimensionPositive := by
      rcases successor with ⟨pred, hnext⟩
      subst params
      simpa [Parameters.next] using hd
    kPositive := hk_pos }

/-- Assemble the answer-valued successor role-package residual from a
predecessor `AnswerPerSliceInductionPackage` and answer-side self-improvement
bridge inputs.

This adapter route starts from a packaged predecessor per-slice induction
hypothesis together with the Section 9 bridge data on the answer side.  It
composes `mainFormalSuccessorAnswerRecursiveSlices_ofInductionPackage` (which
produces the recursive slice witnesses from the per-slice induction package)
with `ofAnswerSuccessorBridgeInputs`.  Like the other constructors in this
namespace it is pure structural composition over the answer-side adapters
already merged on `main`; it does not call `mainFormal`, does not introduce any
new analytic step, and leaves downstream completion and line-169 interfaces
untouched. -/
noncomputable def ofAnswerSuccessorInductionPackageAndBridgeInputs
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hm_ne_one : params.m ≠ 1)
    (hd : 0 < params.d)
    (hk_pos : 1 ≤ k)
    (hinduction :
      answerSuccessorPerSliceInductionPackageInput (k := k) hpass hm_ne_one)
    (hbridge : answerSuccessorSelfImprovementBridgeInput (k := k) hpass hm_ne_one) :
    MainFormalRolePackageAnswerSuccessorResidual params strategy eps hpass k :=
  let successor := Parameters.successorDecompositionOfNeOne params hm_ne_one
  letI : FieldModel.{0} successor.pred.q := fieldModelOfSuccessorDecomposition successor
  let transportedStrategy := projStratTransportSuccessor strategy successor
  let transportedPass := passesLowIndividualDegreeTest_transportSuccessor hpass successor
  ofAnswerSuccessorBridgeInputs (params := params) (strategy := strategy)
    hpass hm_ne_one hd hk_pos
    (mainFormalSuccessorAnswerRecursiveSlices_ofInductionPackage successor.pred
      transportedStrategy eps transportedPass k
      (mainFormalSuccessorAnswerAxisWeightedBound_ofPass
        successor.pred transportedStrategy eps transportedPass)
      (mainFormalSuccessorAnswerDiagonalWeightedBound_ofPass
        successor.pred transportedStrategy eps transportedPass)
      hinduction)
    hbridge

end MainFormalRolePackageAnswerSuccessorResidual

/-- Branch-level residual for producing the Section 6 role package.

The three constructors expose the real alternatives in the current proof state:
base dimension, an ordinary successor dimension, or an answer-valued successor
dimension, each with explicit predecessor transport and successor-boundary data.
The answer-valued successor constructor records the paper-faithful
answer-restricted route separately from the ordinary restriction route. The
large-`k` condition is supplied once, from the public theorem hypothesis, when
converting the branch to a concrete role-package residual. -/
inductive MainFormalRolePackageBranchResidual
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ) : Type _ where
  /-- Base dimension, handled by the checked base-case handoff. -/
  | base (hm1 : params.m = 1) :
      MainFormalRolePackageBranchResidual params strategy eps hpass k
  /-- Successor dimension with explicit predecessor and successor-boundary data. -/
  | successor
      (successorResidual :
        MainFormalRolePackageSuccessorResidual params strategy eps hpass k) :
      MainFormalRolePackageBranchResidual params strategy eps hpass k
  /-- Successor dimension through answer-valued restriction data. -/
  | answerSuccessor
      (successorResidual :
        MainFormalRolePackageAnswerSuccessorResidual params strategy eps hpass k) :
      MainFormalRolePackageBranchResidual params strategy eps hpass k

namespace MainFormalRolePackageBranchResidual

/-- Convert the branch-level role residual into the isolated Section 6 role-package
residual consumed by the downstream assembly. -/
theorem toRolePackageResidual
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    (residual : MainFormalRolePackageBranchResidual params strategy eps hpass k)
    (hk_large : 400 * params.m * params.d ≤ k) :
    Nonempty (MainFormalRolePackageResidual params strategy eps hpass k) := by
  cases residual with
  | base hm1 =>
      exact MainFormalRolePackageResidual.ofBaseCase params strategy eps k hpass hm1
  | successor successorResidual =>
      exact successorResidual.toRolePackageResidual hk_large
  | answerSuccessor successorResidual =>
      exact successorResidual.toRolePackageResidual hk_large

/-- Successor branch constructor from the answer-valued successor inputs.

This packages answer-valued recursive slice witnesses and the corresponding
self-improvement producer for the transported predecessor into the branch-level
role residual. It stops before the line-130 completion and line-169 transport
interfaces. -/
noncomputable def answerSuccessorOfRecursiveSelfImprovement
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hm_ne_one : params.m ≠ 1)
    (hd : 0 < params.d)
    (hk_pos : 1 ≤ k)
    (hrec : answerSuccessorRecursiveSlicesInput (k := k) hpass hm_ne_one)
    (hself : answerSuccessorSelfImprovementInput (k := k) hpass hm_ne_one) :
    MainFormalRolePackageBranchResidual params strategy eps hpass k :=
  .answerSuccessor
    (MainFormalRolePackageAnswerSuccessorResidual.ofAnswerSuccessorRecursiveSelfImprovement
      hpass hm_ne_one hd hk_pos hrec hself)

/-- Direct role-package residual corollary for the answer-valued successor
branch.

Given answer-valued recursive slices, the matching self-improvement producer,
and the public large-`k` side condition, this produces the isolated Section 6
role residual consumed by the downstream `mainFormal` cascade. -/
theorem rolePackageResidual_ofAnswerSuccessorRecursiveSelfImprovement
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hm_ne_one : params.m ≠ 1)
    (hd : 0 < params.d)
    (hk_pos : 1 ≤ k)
    (hk_large : 400 * params.m * params.d ≤ k)
    (hrec : answerSuccessorRecursiveSlicesInput (k := k) hpass hm_ne_one)
    (hself : answerSuccessorSelfImprovementInput (k := k) hpass hm_ne_one) :
    Nonempty (MainFormalRolePackageResidual params strategy eps hpass k) :=
  (answerSuccessorOfRecursiveSelfImprovement hpass hm_ne_one hd hk_pos hrec hself)
    |>.toRolePackageResidual hk_large

/-- Successor branch constructor from the two analytic successor inputs.

This packages recursive slice witnesses and self-improvement bridge inputs for
the transported predecessor into the branch-level role residual.  It deliberately
stops before the line-130 orthonormalization and completion interfaces. -/
noncomputable def successorOfBridgeInputs
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hm_ne_one : params.m ≠ 1)
    (hd : 0 < params.d)
    (hk_pos : 1 ≤ k)
    (hrec : successorRecursiveSlicesInput (k := k) hpass hm_ne_one)
    (hbridge : successorSelfImprovementBridgeInput (k := k) hpass hm_ne_one) :
    MainFormalRolePackageBranchResidual params strategy eps hpass k :=
  .successor
    (MainFormalRolePackageSuccessorResidual.ofSuccessorBridgeInputs
      hpass hm_ne_one hd hk_pos hrec hbridge)

/-- Direct role-package residual corollary for the successor branch.

Given recursive slices, self-improvement bridge inputs, and the public large-`k`
side condition, this produces the isolated Section 6 role residual consumed by
the downstream `mainFormal` cascade. -/
theorem rolePackageResidual_ofSuccessorBridgeInputs
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hm_ne_one : params.m ≠ 1)
    (hd : 0 < params.d)
    (hk_pos : 1 ≤ k)
    (hk_large : 400 * params.m * params.d ≤ k)
    (hrec : successorRecursiveSlicesInput (k := k) hpass hm_ne_one)
    (hbridge : successorSelfImprovementBridgeInput (k := k) hpass hm_ne_one) :
    Nonempty (MainFormalRolePackageResidual params strategy eps hpass k) :=
  (successorOfBridgeInputs hpass hm_ne_one hd hk_pos hrec hbridge).toRolePackageResidual
    hk_large

/-- Answer-side successor branch constructor from recursive answer slices and
self-improvement bridge inputs.

This is the answer-register counterpart of `successorOfBridgeInputs`: it
packages the answer-valued recursive slice witnesses and the matching
per-slice Section 9 bridge inputs through
`MainFormalRolePackageAnswerSuccessorResidual.ofAnswerSuccessorBridgeInputs`,
then injects into the branch residual.  It does not call `mainFormal` and stops
before the line-130 completion and line-169 transport interfaces. -/
noncomputable def answerSuccessorOfBridgeInputs
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hm_ne_one : params.m ≠ 1)
    (hd : 0 < params.d)
    (hk_pos : 1 ≤ k)
    (hrec : answerSuccessorRecursiveSlicesInput (k := k) hpass hm_ne_one)
    (hbridge : answerSuccessorSelfImprovementBridgeInput (k := k) hpass hm_ne_one) :
    MainFormalRolePackageBranchResidual params strategy eps hpass k :=
  .answerSuccessor
    (MainFormalRolePackageAnswerSuccessorResidual.ofAnswerSuccessorBridgeInputs
      hpass hm_ne_one hd hk_pos hrec hbridge)

/-- Direct role-package residual corollary for the answer-side successor branch
when the analytic inputs are supplied as recursive slice witnesses and
per-slice Section 9 bridge inputs.

This composes `answerSuccessorOfBridgeInputs` with `toRolePackageResidual`. -/
theorem rolePackageResidual_ofAnswerSuccessorBridgeInputs
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hm_ne_one : params.m ≠ 1)
    (hd : 0 < params.d)
    (hk_pos : 1 ≤ k)
    (hk_large : 400 * params.m * params.d ≤ k)
    (hrec : answerSuccessorRecursiveSlicesInput (k := k) hpass hm_ne_one)
    (hbridge : answerSuccessorSelfImprovementBridgeInput (k := k) hpass hm_ne_one) :
    Nonempty (MainFormalRolePackageResidual params strategy eps hpass k) :=
  (answerSuccessorOfBridgeInputs hpass hm_ne_one hd hk_pos hrec hbridge)
    |>.toRolePackageResidual hk_large

/-- Answer-side successor branch constructor from a predecessor
`AnswerPerSliceInductionPackage` and per-slice Section 9 bridge inputs.

This preferred answer-side adapter route consumes a packaged per-slice
induction hypothesis for the transported predecessor together with the
answer-side self-improvement bridge data, and composes them through
`mainFormalSuccessorAnswerRecursiveSlices_ofInductionPackage` and
`mainFormalSuccessorAnswerBoundary_ofBridgeInputs`.  It is pure structural
composition over the answer-side adapters merged on `main`; it does not call
`mainFormal`, introduces no new analytic step, and leaves the line-130
completion and line-169 transport interfaces untouched. -/
noncomputable def answerSuccessorOfInductionPackageAndBridgeInputs
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hm_ne_one : params.m ≠ 1)
    (hd : 0 < params.d)
    (hk_pos : 1 ≤ k)
    (hinduction :
      answerSuccessorPerSliceInductionPackageInput (k := k) hpass hm_ne_one)
    (hbridge : answerSuccessorSelfImprovementBridgeInput (k := k) hpass hm_ne_one) :
    MainFormalRolePackageBranchResidual params strategy eps hpass k :=
  .answerSuccessor
    (MainFormalRolePackageAnswerSuccessorResidual.ofAnswerSuccessorInductionPackageAndBridgeInputs
      hpass hm_ne_one hd hk_pos hinduction hbridge)

/-- Direct role-package residual corollary for the answer-side successor branch
when the analytic inputs are supplied as a predecessor per-slice induction
package and per-slice Section 9 bridge inputs.

This is the most direct route from the load-bearing answer-side adapters to the
isolated Section 6 role residual consumed by the downstream `mainFormal`
cascade.  It composes `answerSuccessorOfInductionPackageAndBridgeInputs` with
`toRolePackageResidual`. -/
theorem rolePackageResidual_ofAnswerSuccessorInductionPackageAndBridgeInputs
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hm_ne_one : params.m ≠ 1)
    (hd : 0 < params.d)
    (hk_pos : 1 ≤ k)
    (hk_large : 400 * params.m * params.d ≤ k)
    (hinduction :
      answerSuccessorPerSliceInductionPackageInput (k := k) hpass hm_ne_one)
    (hbridge : answerSuccessorSelfImprovementBridgeInput (k := k) hpass hm_ne_one) :
    Nonempty (MainFormalRolePackageResidual params strategy eps hpass k) :=
  (answerSuccessorOfInductionPackageAndBridgeInputs hpass hm_ne_one hd hk_pos
    hinduction hbridge)
    |>.toRolePackageResidual hk_large

end MainFormalRolePackageBranchResidual

end Test

end MIPStarRE.LDT
