import MIPStarRE.LDT.Test.MainTheorem.RoleRegister.Core
import MIPStarRE.LDT.Test.MainTheorem.AnswerValuedRestriction

/-!
# Role-register residuals

Role-register measurement construction for the `mainFormal` construction.  This
module imports `RoleRegister.Core` (defining `MainFormalRoleMeasurementPackage`
and the predecessor-transport helpers) and introduces the branch-level
residual structures for producing the Section 6 role measurement:

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
is supplied.  The recursive self-improvement constructors are structural and do
not call `mainFormal`; they stop before the line-130 orthonormalization and
completion interfaces.

## References

* Paper: `references/ldt-paper/inductive_step.tex`,
  symmetrization with role register and factor-two block estimates
  (lines 97–108).
* Blueprint: `blueprint/src/chapter/ch10_induction.tex`,
  `\label{rem:main-formal-lean-residual-records}`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-- Successor-branch data for producing the Section 6 role measurement.

Paper origin: `references/ldt-paper/inductive_step.tex:68-83` and the
successor branch of the Section 6 induction proof in
`references/ldt-paper/inductive_step.tex:429-568`.

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
  /-- A predecessor whose successor is the current parameter choice. -/
  successor : Parameters.SuccessorDecomposition params
  /-- The successor-boundary inputs for the transported strategy. -/
  boundary :
    letI : FieldModel.{0} successor.pred.q := fieldModelOfSuccessorDecomposition successor
    MainFormalSuccessorBoundary successor.pred
      (projStratTransportSuccessor strategy successor) eps
      (passesLowIndividualDegreeTest_transportSuccessor hpass successor) k
  /-- Positivity of the predecessor degree parameter, needed by the Section 6 interface. -/
  dimensionPositive : 0 < successor.pred.d
  /-- The positive-`k` side condition used by the Section 6 interface. -/
  kPositive : 1 ≤ k

/-- Paper origin: `references/ldt-paper/inductive_step.tex:26-149`
and `references/ldt-paper/inductive_step.tex:300-342`.

Type of recursive slice witnesses for the predecessor determined by a
non-base current parameter choice.  This private abbreviation keeps the three
successor-construction entry points below from repeating the transported predecessor
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

/-- Paper origin: `references/ldt-paper/inductive_step.tex:250-315`
and `references/ldt-paper/self_improvement.tex:628-770`
(`\label{thm:self-improvement}`).

Type of self-improvement inputs for the predecessor determined by a non-base
current parameter choice. -/
private abbrev successorSelfImprovementInput
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hm_ne_one : params.m ≠ 1) : Type _ :=
  let successor := Parameters.successorDecompositionOfNeOne params hm_ne_one
  letI : FieldModel.{0} successor.pred.q := fieldModelOfSuccessorDecomposition successor
  let transportedStrategy := projStratTransportSuccessor strategy successor
  let transportedPass := passesLowIndividualDegreeTest_transportSuccessor hpass successor
  MainFormalSuccessorSelfImprovementObligation
    successor.pred transportedStrategy eps transportedPass k
    (mainFormalSuccessorAxisWeightedBound_ofPass
      successor.pred transportedStrategy eps transportedPass)
    (mainFormalSuccessorDiagonalWeightedBound_ofPass
      successor.pred transportedStrategy eps transportedPass)

namespace MainFormalRolePackageSuccessorResidual

/-- Convert explicit successor-branch data into the isolated Section 6 role
residual, using the public current-dimension large-`k` hypothesis. -/
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

/-- Assemble the successor role residual from recursive slices and a
self-improvement input.

This is the non-base ordinary successor constructor.  It does not assume a raw
Section 6 witness: the proof supplies exactly the two analytic successor inputs
for the transported predecessor, namely recursive slice witnesses and the
restricted-strategy self-improvement input.  This constructor combines them
through `mainFormalSuccessorBoundary_ofRecursiveSelfImprovement`; line-130
orthonormalization and completion inputs remain downstream.

**Unfaithful:** this constructor assumes recursive slice witnesses and a
self-improvement input that are not derived from
`references/ldt-paper/test_definition.tex:180-202` or the successor case of
`thm:main-induction` (`references/ldt-paper/inductive_step.tex:441-551`).  This
is tracked by #1035, #1036, #1363, and #1458.  Elimination: prove those inputs
inside the successor branch of `mainFormal`. -/
noncomputable def ofSuccessorRecursiveSelfImprovement
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hm_ne_one : params.m ≠ 1)
    (hd : 0 < params.d)
    (hk_pos : 1 ≤ k)
    (hrec : successorRecursiveSlicesInput (k := k) hpass hm_ne_one)
    (hself : successorSelfImprovementInput (k := k) hpass hm_ne_one) :
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
      mainFormalSuccessorBoundary_ofRecursiveSelfImprovement successor.pred
        transportedStrategy eps transportedPass k hrec hself
  · rcases successor with ⟨pred, hnext⟩
    subst params
    simpa [Parameters.next] using hd

end MainFormalRolePackageSuccessorResidual

/-- Answer-valued successor-branch data for producing the Section 6 role measurement.

Paper origin: `references/ldt-paper/inductive_step.tex:68-83` and the
successor branch of the Section 6 induction proof in
`references/ldt-paper/inductive_step.tex:429-568`. -/
structure MainFormalRolePackageAnswerSuccessorResidual
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ) where
  /-- A predecessor whose successor is the current parameter choice. -/
  successor : Parameters.SuccessorDecomposition params
  /-- The answer-valued successor-boundary inputs for the transported strategy. -/
  boundary :
    letI : FieldModel.{0} successor.pred.q := fieldModelOfSuccessorDecomposition successor
    MainFormalSuccessorAnswerBoundary successor.pred
      (projStratTransportSuccessor strategy successor) eps
      (passesLowIndividualDegreeTest_transportSuccessor hpass successor) k
  /-- Positivity of the predecessor degree parameter, needed by the Section 6 interface. -/
  dimensionPositive : 0 < successor.pred.d
  /-- The positive-`k` side condition used by the Section 6 interface. -/
  kPositive : 1 ≤ k

/-- Paper origin: `references/ldt-paper/inductive_step.tex:26-149`
and `references/ldt-paper/inductive_step.tex:300-342`.

Type of answer-valued recursive slice witnesses for the predecessor
determined by a non-base current parameter choice. -/
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

/-- Paper origin: `references/ldt-paper/inductive_step.tex:250-315`
and `references/ldt-paper/self_improvement.tex:628-770`
(`\label{thm:self-improvement}`).

Type of answer-valued self-improvement obligations for the predecessor
determined by a non-base current parameter choice. -/
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
  MainFormalSuccessorAnswerSelfImprovementObligation
    successor.pred transportedStrategy eps transportedPass k
    (mainFormalSuccessorAnswerAxisWeightedBound_ofPass
      successor.pred transportedStrategy eps transportedPass)
    (mainFormalSuccessorAnswerDiagonalWeightedBound_ofPass
      successor.pred transportedStrategy eps transportedPass)

namespace MainFormalRolePackageAnswerSuccessorResidual

/-- Convert explicit answer-valued successor-branch data into the isolated Section 6
role residual, using the public current-dimension large-`k` hypothesis. -/
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

/-- Assemble the answer-valued successor role residual from recursive
answer slices and an answer-valued self-improvement obligation.

This is the answer-register counterpart of the ordinary successor role construction.
It combines exactly the answer-side Section 6 inputs through
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

end MainFormalRolePackageAnswerSuccessorResidual

/-- Branch-level residual for producing the Section 6 role measurement.

The three constructors expose the real alternatives in the current proof state:
base dimension, an ordinary successor dimension, or an answer-valued successor
dimension, each with explicit predecessor transport and successor-boundary data.
The answer-valued successor constructor records the paper-faithful
answer-restricted route separately from the ordinary restriction route. The
large-`k` condition is supplied once, from the public theorem hypothesis, when
converting the branch to a concrete role residual. -/
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

/-- Convert the branch-level role residual into the isolated Section 6 role
residual consumed by the downstream construction. -/
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

This records answer-valued recursive slice witnesses and the corresponding
self-improvement obligation for the transported predecessor into the branch-level
role residual. It stops before the line-130 completion and line-169 transport
interfaces.

**Unfaithful:** this branch constructor assumes answer-valued recursive slice
witnesses and a self-improvement obligation that are not derived from
`references/ldt-paper/test_definition.tex:180-202` or
`references/ldt-paper/inductive_step.tex:441-551`.  This is tracked by #1369,
#1363, and #1458.  Elimination: derive the answer-valued boundary internally in
the successor proof before using this constructor. -/
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

/-- Direct role-residual corollary for the answer-valued successor
branch.

Given answer-valued recursive slices, the matching self-improvement obligation,
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

/-- Ordinary successor branch constructor from the two analytic successor inputs.

This records recursive slice witnesses and a self-improvement input for
the transported predecessor into the branch-level role residual.  It deliberately
stops before the line-130 orthonormalization and completion interfaces.

**Unfaithful:** this constructor assumes recursive slice witnesses and
self-improvement input, rather than deriving them from
`references/ldt-paper/test_definition.tex:180-202` and
`references/ldt-paper/inductive_step.tex:441-551`.  This is tracked by #1035,
#1036, #1363, and #1458.  Elimination: prove those inputs inside the successor
proof. -/
noncomputable def successorOfRecursiveSelfImprovement
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hm_ne_one : params.m ≠ 1)
    (hd : 0 < params.d)
    (hk_pos : 1 ≤ k)
    (hrec : successorRecursiveSlicesInput (k := k) hpass hm_ne_one)
    (hself : successorSelfImprovementInput (k := k) hpass hm_ne_one) :
    MainFormalRolePackageBranchResidual params strategy eps hpass k :=
  .successor
    (MainFormalRolePackageSuccessorResidual.ofSuccessorRecursiveSelfImprovement
      hpass hm_ne_one hd hk_pos hrec hself)

/-- Direct role-residual corollary for the successor branch.

Given recursive slices, a self-improvement input, and the public large-`k`
side condition, this produces the isolated Section 6 role residual consumed by
the downstream `mainFormal` cascade. -/
theorem rolePackageResidual_ofSuccessorRecursiveSelfImprovement
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hm_ne_one : params.m ≠ 1)
    (hd : 0 < params.d)
    (hk_pos : 1 ≤ k)
    (hk_large : 400 * params.m * params.d ≤ k)
    (hrec : successorRecursiveSlicesInput (k := k) hpass hm_ne_one)
    (hself : successorSelfImprovementInput (k := k) hpass hm_ne_one) :
    Nonempty (MainFormalRolePackageResidual params strategy eps hpass k) :=
  (successorOfRecursiveSelfImprovement hpass hm_ne_one hd hk_pos hrec hself)
    |>.toRolePackageResidual hk_large

end MainFormalRolePackageBranchResidual

end Test

end MIPStarRE.LDT
