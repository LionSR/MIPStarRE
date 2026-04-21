import MIPStarRE.LDT.Test.StrategyRoleSymmetrization

/-!
# Symmetric-strategy failure probabilities

Failure surrogates and basic role-averaged branch quantities.
-/

namespace MIPStarRE.LDT

open scoped BigOperators MatrixOrder Matrix ComplexOrder

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

namespace ProjStrat

/-- View the left prover's local data as a symmetric-strategy-style package. -/
def leftAsSymmetric {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) :
    SymStrat params ι where
  state := strategy.state
  permInvState := strategy.permInvState
  isNormalized := strategy.isNormalized
  pointMeasurement := strategy.pointMeasurementA
  axisParallelMeasurement := strategy.axisParallelMeasurementA
  axisParallelReparamInvariant := strategy.axisParallelReparamInvariantA
  diagonalMeasurement := strategy.diagonalMeasurementA
  diagonalReparamInvariant := strategy.diagonalReparamInvariantA

/-- View the right prover's local data as a symmetric-strategy-style package. -/
def rightAsSymmetric {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) :
    SymStrat params ι where
  state := strategy.state
  permInvState := strategy.permInvState
  isNormalized := strategy.isNormalized
  pointMeasurement := strategy.pointMeasurementB
  axisParallelMeasurement := strategy.axisParallelMeasurementB
  axisParallelReparamInvariant := strategy.axisParallelReparamInvariantB
  diagonalMeasurement := strategy.diagonalMeasurementB
  diagonalReparamInvariant := strategy.diagonalReparamInvariantB

/-- Axis-parallel branch component where the left prover is queried with a line
and the right prover is queried with the sampled base point.

This is one of the two crossed role choices in the full low-individual-degree
test. It is not the local axis-parallel failure probability of
`strategy.leftAsSymmetric`, which would compare the left prover's point and line
measurements against each other. -/
noncomputable def axisParallelLineLeftPointRightFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) : Error :=
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
    (strategy : ProjStrat params ι) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelPointAnswerFamily strategy.leftAsSymmetric)
    (axisParallelLineAnswerFamily strategy.rightAsSymmetric)

/-- Auxiliary left-local SSC defect of the point measurement.

This is not the actual self-consistency branch of
`lowIndividualDegreeFailureProbability`; the full test uses the cross-prover
point-agreement branch `pointAgreementFailureProbability`. -/
noncomputable def pointLeftSelfConsistencyFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) : Error :=
  bipartiteSSCError strategy.state
    (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)

/-- Auxiliary right-local SSC defect of the point measurement.

This is not the actual self-consistency branch of
`lowIndividualDegreeFailureProbability`; the full test uses the cross-prover
point-agreement branch `pointAgreementFailureProbability`. -/
noncomputable def pointRightSelfConsistencyFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) : Error :=
  bipartiteSSCError strategy.state
    (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)

/-- Diagonal branch component where the left prover is queried with a diagonal
line and the right prover is queried with the sampled base point.

The average is over the restriction index and then over the corresponding
restricted diagonal sample. This crossed component is what the full test bounds;
it is not the diagonal-line failure probability of either local symmetric view. -/
noncomputable def diagonalLineLeftPointRightFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) : Error :=
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
    (strategy : ProjStrat params ι) : Error :=
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
    (strategy : ProjStrat params ι) : Error :=
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
    (strategy : ProjStrat params ι) : Error :=
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

/-- The paper's self-consistency branch for a general strategy: both provers
receive the same sampled point and are checked for agreement there. -/
noncomputable def pointAgreementFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)

/-- Trace-based failure surrogate for the full low-individual-degree
test, matching the paper's `fig:test` with role-based decomposition.

Each of the geometric line branches picks a role `r ∈ {A, B}`:
- Player `r` receives a line and returns a polynomial;
- Player `r̄` receives a point and returns a field element.

The self-consistency branch samples a shared point and checks cross-player point
agreement there.

TODO(#306): `ProjStrat` currently forces both provers onto the
same index type `ι`; the paper allows `H_A ≠ H_B`. -/
noncomputable def lowIndividualDegreeFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) : Error :=
  let axisParallelBranch := strategy.axisParallelRoleAverage
  let selfConsistencyBranch := strategy.pointAgreementFailureProbability
  let diagonalBranch := strategy.diagonalRoleAverage
  (axisParallelBranch + selfConsistencyBranch +
    diagonalBranch) / 3

/-- The full low-individual-degree failure surrogate is the arithmetic mean of
its axis-parallel, point-agreement, and diagonal branches. -/
theorem lowIndividualDegreeFailureProbability_eq_branchAverage
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) :
    strategy.lowIndividualDegreeFailureProbability =
      (strategy.axisParallelRoleAverage + strategy.pointAgreementFailureProbability +
        strategy.diagonalRoleAverage) / 3 := rfl

/-- Passing the full low-individual-degree test with error `ε`. -/
structure PassesLowIndividualDegreeTest {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) (eps : Error) : Prop where
  soundnessHypothesis : strategy.lowIndividualDegreeFailureProbability ≤ eps

/-- Passing the full test bounds the cross-prover point-agreement branch by
`3 * eps`, exactly because that branch is one of the three nonnegative terms
averaged in `lowIndividualDegreeFailureProbability`. -/
theorem point_agreement_le_three_mul {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : ProjStrat params ι} {eps : Error}
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    strategy.pointAgreementFailureProbability ≤ 3 * eps := by
  let pointAgreement : Error := strategy.pointAgreementFailureProbability
  let axisParallelBranch : Error := strategy.axisParallelRoleAverage
  let diagonalBranch : Error := strategy.diagonalRoleAverage
  have hpoint_nonneg : 0 ≤ pointAgreement := by
    simpa [pointAgreement] using
      (show 0 ≤ strategy.pointAgreementFailureProbability from
        bipartiteConsError_nonneg strategy.state (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB))
  have haxis_nonneg : 0 ≤ axisParallelBranch := by
    dsimp [axisParallelBranch]
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
  have hdiag_nonneg : 0 ≤ diagonalBranch := by
    dsimp [diagonalBranch]
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
  have hmain : (axisParallelBranch + pointAgreement + diagonalBranch) / 3 ≤ eps := by
    simpa [axisParallelBranch, pointAgreement, diagonalBranch,
      ProjStrat.lowIndividualDegreeFailureProbability_eq_branchAverage] using
      hpass.soundnessHypothesis
  linarith


end ProjStrat

end MIPStarRE.LDT
