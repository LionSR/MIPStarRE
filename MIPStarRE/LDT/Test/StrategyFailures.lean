import MIPStarRE.LDT.Test.StrategyRole

/-!
# Symmetrized-strategy failure probabilities and test bounds

Failure-probability surrogates and basic low-individual-degree test bounds
extracted from `MIPStarRE.LDT.Test.StrategySymmetrized`.
-/

namespace MIPStarRE.LDT

open scoped BigOperators MatrixOrder Matrix ComplexOrder

/-! ### Symmetrized strategies and tested-branch bounds -/

namespace SymStrat

/-- Trace-based failure surrogate for the axis-parallel lines test.
Point answers on the left register, line answers (evaluated at the
base point) on the right register of the bipartite state. -/
noncomputable def axisParallelFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelPointAnswerFamily strategy)
    (axisParallelLineAnswerFamily strategy)

/-- Trace-based failure surrogate for the self-consistency test.
Uses bipartite SSC defect (cross-register overlap).
For projective measurements this equals `bipartiteConsError`
between the same measurement on both registers. -/
noncomputable def selfConsistencyFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) : Error :=
  bipartiteSSCError strategy.state
    (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)

/-- Trace-based failure surrogate for the diagonal lines test.
Averages over the restriction index `j ∈ {0, …, m − 1}`, then
over the `j`-restricted diagonal test. For each `j`, direction
vectors have the last `m − j − 1` coordinates equal to zero. -/
noncomputable def diagonalFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) : Error :=
  -- `params.hm : 0 < params.m` ensures the averaging denominator is nonzero.
  (1 / (params.m : Error)) *
    ∑ j : Fin params.m,
      bipartiteConsError strategy.state
        (uniformDistribution
          (RestrictedDiagonalSample params j))
        (diagonalPointAnswerFamily strategy j)
        (diagonalLineAnswerFamily strategy j)

/-- The paper's notion of an `(ε,δ,γ)`-good symmetric strategy.

Matches the paper's Definition 3.1: three test-passing bounds with no
extra hypotheses.  The reparametrization covariance that was formerly
listed here is now a structural property of `SymStrat`, where it
belongs (the paper treats diagonal measurements as geometrically
covariant by construction). -/
structure IsGood {params : Parameters} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error) : Prop where
  axisParallelTest : strategy.axisParallelFailureProbability ≤ eps
  selfConsistencyTest : strategy.selfConsistencyFailureProbability ≤ delta
  diagonalLineTest : strategy.diagonalFailureProbability ≤ gamma

end SymStrat

/-- The diagonal-line failure surrogate is nonnegative. -/
theorem diagonalFailureProbability_nonneg
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) :
    0 ≤ strategy.diagonalFailureProbability := by
  unfold SymStrat.diagonalFailureProbability
  refine mul_nonneg ?_ ?_
  · positivity
  · refine Finset.sum_nonneg ?_
    intro j _
    exact bipartiteConsError_nonneg strategy.state
      (uniformDistribution (RestrictedDiagonalSample params j))
      (diagonalPointAnswerFamily strategy j)
      (diagonalLineAnswerFamily strategy j)

/-- A good symmetric strategy has a nonnegative axis-parallel error parameter
`ε`. -/
theorem eps_nonneg_of_isGood
    (params : Parameters)
    [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι)
    {eps delta gamma : Error}
    (hgood : strategy.IsGood eps delta gamma) :
    0 ≤ eps := by
  exact le_trans
    (bipartiteConsError_nonneg strategy.state
      (uniformDistribution (AxisParallelTestSample params))
      (axisParallelPointAnswerFamily strategy)
      (axisParallelLineAnswerFamily strategy))
    hgood.axisParallelTest

/-- A good symmetric strategy has a nonnegative self-consistency error
parameter `δ`. -/
theorem delta_nonneg_of_isGood
    (params : Parameters)
    [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι)
    {eps delta gamma : Error}
    (hgood : strategy.IsGood eps delta gamma) :
    0 ≤ delta := by
  exact le_trans
    (bipartiteSSCError_nonneg strategy.state
      (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
    hgood.selfConsistencyTest

/-- A good symmetric strategy has a nonnegative diagonal-lines error parameter
`γ`. -/
theorem gamma_nonneg_of_isGood
    (params : Parameters)
    [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι)
    {eps delta gamma : Error}
    (hgood : strategy.IsGood eps delta gamma) :
    0 ≤ gamma := by
  exact le_trans (diagonalFailureProbability_nonneg params strategy)
    hgood.diagonalLineTest

/-! ### Answer-valued symmetric strategies -/

/-- The answer-valued diagonal-line failure surrogate is nonnegative. -/
theorem answer_diagonalFailureProbability_nonneg
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι) :
    0 ≤ strategy.diagonalFailureProbability := by
  unfold AnswerSymStrat.diagonalFailureProbability
  refine mul_nonneg ?_ ?_
  · positivity
  · refine Finset.sum_nonneg ?_
    intro j _
    exact bipartiteConsError_nonneg strategy.state
      (uniformDistribution (RestrictedDiagonalSample params j))
      (AnswerSymStrat.diagonalPointAnswerFamily strategy j)
      (AnswerSymStrat.diagonalLineAnswerFamily strategy j)

/-- A good answer-valued symmetric strategy has a nonnegative axis-parallel
error parameter `ε`. -/
theorem answer_eps_nonneg_of_isGood
    (params : Parameters)
    [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι)
    {eps delta gamma : Error}
    (hgood : strategy.IsGood eps delta gamma) :
    0 ≤ eps := by
  exact le_trans
    (bipartiteConsError_nonneg strategy.state
      (uniformDistribution (AxisParallelTestSample params))
      (AnswerSymStrat.axisParallelPointAnswerFamily strategy)
      (AnswerSymStrat.axisParallelLineAnswerFamily strategy))
    hgood.axisParallelTest

/-- A good answer-valued symmetric strategy has a nonnegative self-consistency
error parameter `δ`. -/
theorem answer_delta_nonneg_of_isGood
    (params : Parameters)
    [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι)
    {eps delta gamma : Error}
    (hgood : strategy.IsGood eps delta gamma) :
    0 ≤ delta := by
  exact le_trans
    (bipartiteSSCError_nonneg strategy.state
      (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
    hgood.selfConsistencyTest

/-- A good answer-valued symmetric strategy has a nonnegative diagonal-lines
error parameter `γ`. -/
theorem answer_gamma_nonneg_of_isGood
    (params : Parameters)
    [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι)
    {eps delta gamma : Error}
    (hgood : strategy.IsGood eps delta gamma) :
    0 ≤ gamma := by
  exact le_trans (answer_diagonalFailureProbability_nonneg params strategy)
    hgood.diagonalLineTest

/-- If three nonnegative summands have average at most `eps`, each summand is at
most `3 * eps`. -/
lemma three_summand_bounds_of_average_le
    {axis point diagonal eps : Error}
    (haxis : 0 ≤ axis) (hpoint : 0 ≤ point) (hdiagonal : 0 ≤ diagonal)
    (hmain : (axis + point + diagonal) / 3 ≤ eps) :
    axis ≤ 3 * eps ∧ point ≤ 3 * eps ∧ diagonal ≤ 3 * eps := by
  constructor
  · linarith
  constructor
  · linarith
  · linarith

namespace SameSpaceProjStrat

/-- View the left prover's local data as a symmetric-strategy-style package. -/
def leftAsSymmetric {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) :
    SymStrat params ι where
  state := strategy.state
  permInvState := strategy.permInvState
  densityFixed := strategy.densityFixed
  isNormalized := strategy.isNormalized
  pointMeasurement := strategy.pointMeasurementA
  axisParallelMeasurement := strategy.axisParallelMeasurementA
  diagonalMeasurement := strategy.diagonalMeasurementA

/-- View the right prover's local data as a symmetric-strategy-style package. -/
def rightAsSymmetric {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) :
    SymStrat params ι where
  state := strategy.state
  permInvState := strategy.permInvState
  densityFixed := strategy.densityFixed
  isNormalized := strategy.isNormalized
  pointMeasurement := strategy.pointMeasurementB
  axisParallelMeasurement := strategy.axisParallelMeasurementB
  diagonalMeasurement := strategy.diagonalMeasurementB

/-- Axis-parallel branch component where the left prover is queried with a line
and the right prover is queried with the sampled base point.

This is one of the two crossed role choices in the full low-individual-degree
test. It is not the local axis-parallel failure probability of
`strategy.leftAsSymmetric`, which would compare the left prover's point and line
measurements against each other. -/
noncomputable def axisParallelLineLeftPointRightFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelLineAnswerFamily strategy.leftAsSymmetric)
    (axisParallelPointAnswerFamily strategy.rightAsSymmetric)

/-- Axis-parallel branch component where the left prover is queried with the
sampled base point and the right prover is queried with a line.

This is the other crossed role choice in the full test, again distinct from any
same-local `SymStrat.axisParallelFailureProbability`. -/
noncomputable def axisParallelPointLeftLineRightFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelPointAnswerFamily strategy.leftAsSymmetric)
    (axisParallelLineAnswerFamily strategy.rightAsSymmetric)

/-- Diagonal branch component where the left prover is queried with a diagonal
line and the right prover is queried with the sampled base point.

The average is over the restriction index and then over the corresponding
restricted diagonal sample. This crossed component is what the full test bounds;
it is not the diagonal-line failure probability of either local symmetric view. -/
noncomputable def diagonalLineLeftPointRightFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) : Error :=
  (1 / (params.m : Error)) *
    ∑ j : Fin params.m,
      bipartiteConsError strategy.state
        (uniformDistribution (RestrictedDiagonalSample params j))
        (diagonalLineAnswerFamily strategy.leftAsSymmetric j)
        (diagonalPointAnswerFamily strategy.rightAsSymmetric j)

/-- Diagonal branch component where the left prover is queried with the sampled
base point and the right prover is queried with a diagonal line.

Together with `diagonalLineLeftPointRightFailureProbability`, this is the
role-averaged diagonal part of `lowIndividualDegreeFailureProbability`. -/
noncomputable def diagonalPointLeftLineRightFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) : Error :=
  (1 / (params.m : Error)) *
    ∑ j : Fin params.m,
      bipartiteConsError strategy.state
        (uniformDistribution (RestrictedDiagonalSample params j))
        (diagonalPointAnswerFamily strategy.leftAsSymmetric j)
        (diagonalLineAnswerFamily strategy.rightAsSymmetric j)

/-- The paper's axis-parallel branch for a general strategy, averaged over the
two role choices. -/
noncomputable def axisParallelRoleAverage
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) : Error :=
  let left := strategy.leftAsSymmetric
  let right := strategy.rightAsSymmetric
  let axParDist := uniformDistribution (AxisParallelTestSample params)
  (bipartiteConsError strategy.state axParDist
      (axisParallelLineAnswerFamily left)
      (axisParallelPointAnswerFamily right)
    + bipartiteConsError strategy.state axParDist
      (axisParallelPointAnswerFamily left)
      (axisParallelLineAnswerFamily right)) / 2

/-- The paper's diagonal branch for a general strategy, averaged over the two
role choices and the restricted diagonal samples. -/
noncomputable def diagonalRoleAverage
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) : Error :=
  let left := strategy.leftAsSymmetric
  let right := strategy.rightAsSymmetric
  (1 / (params.m : Error)) *
    ∑ j : Fin params.m,
      (bipartiteConsError strategy.state
          (uniformDistribution (RestrictedDiagonalSample params j))
          (diagonalLineAnswerFamily left j)
          (diagonalPointAnswerFamily right j)
        + bipartiteConsError strategy.state
          (uniformDistribution (RestrictedDiagonalSample params j))
          (diagonalPointAnswerFamily left j)
          (diagonalLineAnswerFamily right j)) / 2

/-- Trace-based failure surrogate for the full low-individual-degree
test, matching the paper's `fig:test` with role-based decomposition.

Each of the geometric line branches picks a role `r ∈ {A, B}`:
- Player `r` receives a line and returns a polynomial;
- Player `r̄` receives a point and returns a field element.

The self-consistency branch samples a shared point and checks cross-player point
agreement there.

Note: `SameSpaceProjStrat` currently forces both provers onto the
same index type `ι`; the paper allows `H_A ≠ H_B`. -/
noncomputable def lowIndividualDegreeFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) : Error :=
  let axisParallelBranch := strategy.axisParallelRoleAverage
  -- Self-consistency: the paper samples the same point for Alice and Bob and
  -- checks agreement of their point answers.
  let selfConsistencyBranch :=
    bipartiteConsError strategy.state
      (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
  let diagonalBranch := strategy.diagonalRoleAverage
  (axisParallelBranch + selfConsistencyBranch +
    diagonalBranch) / 3

/-- Passing the full low-individual-degree test with error `ε`. -/
structure PassesLowIndividualDegreeTest {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) : Prop where
  soundnessHypothesis : strategy.lowIndividualDegreeFailureProbability ≤ eps

/-- The axis-parallel role-average branch of the full test is nonnegative. -/
theorem axisParallelRoleAverage_nonneg {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) :
    0 ≤ strategy.axisParallelRoleAverage := by
  dsimp [SameSpaceProjStrat.axisParallelRoleAverage]
  apply div_nonneg
  · linarith [bipartiteConsError_nonneg strategy.state
        (uniformDistribution (AxisParallelTestSample params))
        (axisParallelLineAnswerFamily strategy.leftAsSymmetric)
        (axisParallelPointAnswerFamily strategy.rightAsSymmetric),
      bipartiteConsError_nonneg strategy.state
        (uniformDistribution (AxisParallelTestSample params))
        (axisParallelPointAnswerFamily strategy.leftAsSymmetric)
        (axisParallelLineAnswerFamily strategy.rightAsSymmetric)]
  · norm_num

/-- The diagonal role-average branch of the full test is nonnegative. -/
theorem diagonalRoleAverage_nonneg {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) :
    0 ≤ strategy.diagonalRoleAverage := by
  dsimp [SameSpaceProjStrat.diagonalRoleAverage]
  refine mul_nonneg ?_ ?_
  · positivity
  · refine Finset.sum_nonneg ?_
    intro j _
    apply div_nonneg
    · linarith [bipartiteConsError_nonneg strategy.state
          (uniformDistribution (RestrictedDiagonalSample params j))
          (diagonalLineAnswerFamily strategy.leftAsSymmetric j)
          (diagonalPointAnswerFamily strategy.rightAsSymmetric j),
        bipartiteConsError_nonneg strategy.state
          (uniformDistribution (RestrictedDiagonalSample params j))
          (diagonalPointAnswerFamily strategy.leftAsSymmetric j)
          (diagonalLineAnswerFamily strategy.rightAsSymmetric j)]
    · norm_num

/-- The full low-individual-degree failure probability is nonnegative. -/
theorem lowIndividualDegreeFailureProbability_nonneg {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) :
    0 ≤ strategy.lowIndividualDegreeFailureProbability := by
  let pointAgreement : Error :=
    bipartiteConsError strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
  let axisParallelBranch : Error := strategy.axisParallelRoleAverage
  let diagonalBranch : Error := strategy.diagonalRoleAverage
  have hpoint_nonneg : 0 ≤ pointAgreement := by
    exact bipartiteConsError_nonneg strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
  have haxis_nonneg : 0 ≤ axisParallelBranch := by
    simpa [axisParallelBranch] using axisParallelRoleAverage_nonneg strategy
  have hdiag_nonneg : 0 ≤ diagonalBranch := by
    simpa [diagonalBranch] using diagonalRoleAverage_nonneg strategy
  have hsum : 0 ≤ axisParallelBranch + pointAgreement + diagonalBranch := by
    linarith
  have hmain : 0 ≤ (axisParallelBranch + pointAgreement + diagonalBranch) / 3 :=
    div_nonneg hsum (by norm_num : (0 : Error) ≤ 3)
  simpa [pointAgreement, axisParallelBranch, diagonalBranch,
    SameSpaceProjStrat.lowIndividualDegreeFailureProbability] using hmain

/-- Any passing witness forces the error parameter to be nonnegative. -/
theorem eps_nonneg_of_passes {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error}
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    0 ≤ eps :=
  (lowIndividualDegreeFailureProbability_nonneg strategy).trans hpass.soundnessHypothesis

/-- Passing the full test bounds the role-averaged axis-parallel branch by
`3 * eps`, since it is one of the three nonnegative summands in
`lowIndividualDegreeFailureProbability`. -/
theorem axisParallelRoleAverage_le_three_mul {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error}
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    strategy.axisParallelRoleAverage ≤ 3 * eps := by
  let pointAgreement : Error :=
    bipartiteConsError strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
  have hpoint_nonneg : 0 ≤ pointAgreement := by
    exact bipartiteConsError_nonneg strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
  have haxis_nonneg : 0 ≤ strategy.axisParallelRoleAverage :=
    axisParallelRoleAverage_nonneg strategy
  have hdiag_nonneg : 0 ≤ strategy.diagonalRoleAverage :=
    diagonalRoleAverage_nonneg strategy
  have hmain :
      (strategy.axisParallelRoleAverage + pointAgreement +
        strategy.diagonalRoleAverage) / 3 ≤ eps := by
    simpa [pointAgreement, SameSpaceProjStrat.lowIndividualDegreeFailureProbability] using
      hpass.soundnessHypothesis
  exact
    (three_summand_bounds_of_average_le haxis_nonneg hpoint_nonneg hdiag_nonneg
      hmain).1

/-- Passing the full test bounds the role-averaged diagonal branch by
`3 * eps`, since it is one of the three nonnegative summands in
`lowIndividualDegreeFailureProbability`. -/
theorem diagonalRoleAverage_le_three_mul {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error}
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    strategy.diagonalRoleAverage ≤ 3 * eps := by
  let pointAgreement : Error :=
    bipartiteConsError strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
  have hpoint_nonneg : 0 ≤ pointAgreement := by
    exact bipartiteConsError_nonneg strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
  have haxis_nonneg : 0 ≤ strategy.axisParallelRoleAverage :=
    axisParallelRoleAverage_nonneg strategy
  have hdiag_nonneg : 0 ≤ strategy.diagonalRoleAverage :=
    diagonalRoleAverage_nonneg strategy
  have hmain :
      (strategy.axisParallelRoleAverage + pointAgreement +
        strategy.diagonalRoleAverage) / 3 ≤ eps := by
    simpa [pointAgreement, SameSpaceProjStrat.lowIndividualDegreeFailureProbability] using
      hpass.soundnessHypothesis
  exact
    (three_summand_bounds_of_average_le haxis_nonneg hpoint_nonneg hdiag_nonneg
      hmain).2.2

/-- Passing the full test bounds the cross-prover point-agreement branch by
`3 * eps`, exactly because that branch is one of the three nonnegative terms
averaged in `lowIndividualDegreeFailureProbability`. -/
theorem point_agreement_le_three_mul {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error}
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    bipartiteConsError strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) ≤ 3 * eps := by
  let pointAgreement : Error :=
    bipartiteConsError strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
  let axisParallelBranch : Error := strategy.axisParallelRoleAverage
  let diagonalBranch : Error := strategy.diagonalRoleAverage
  have hpoint_nonneg : 0 ≤ pointAgreement := by
    exact bipartiteConsError_nonneg strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
  have haxis_nonneg : 0 ≤ axisParallelBranch := by
    simpa [axisParallelBranch] using axisParallelRoleAverage_nonneg strategy
  have hdiag_nonneg : 0 ≤ diagonalBranch := by
    simpa [diagonalBranch] using diagonalRoleAverage_nonneg strategy
  have hmain : (axisParallelBranch + pointAgreement + diagonalBranch) / 3 ≤ eps := by
    simpa [axisParallelBranch, pointAgreement, diagonalBranch,
      SameSpaceProjStrat.lowIndividualDegreeFailureProbability,
      SameSpaceProjStrat.axisParallelRoleAverage, SameSpaceProjStrat.diagonalRoleAverage,
      SameSpaceProjStrat.leftAsSymmetric, SameSpaceProjStrat.rightAsSymmetric,
      SymStrat.axisParallelFailureProbability, SymStrat.diagonalFailureProbability] using
      hpass.soundnessHypothesis
  exact
    (three_summand_bounds_of_average_le haxis_nonneg hpoint_nonneg hdiag_nonneg
      hmain).2.1

end SameSpaceProjStrat

end MIPStarRE.LDT
