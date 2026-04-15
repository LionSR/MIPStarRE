import MIPStarRE.LDT.Test.Strategy

/-!
# Section 3 — Classical two-prover strategies

Deterministic classical strategy data and acceptance probabilities for the
repository's currently modeled low individual degree test.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-- A role-tagged sample for the axis-parallel branch of the classical low
individual degree test.

We reuse `AxisParallelTestSample` from `Test.Strategy`: it packages the sampled
base point together with the chosen coordinate direction. The outer `Role`
indicates which prover receives the line query. -/
abbrev ClassicalAxisParallelSample (params : Parameters) :=
  Role × AxisParallelTestSample params

/-- The self-consistency branch sends a point query in the modeled classical
specialization of the repository's current LID test. -/
abbrev ClassicalSelfConsistencySample (params : Parameters) :=
  Point params

/-- A role-tagged sample for the `j`-restricted diagonal branch.

The full diagonal branch first samples `j : Fin params.m` uniformly and then a
restricted diagonal sample for that `j`; the outer `Role` indicates which prover
receives the line query. -/
abbrev ClassicalRestrictedDiagonalSample (params : Parameters)
    (j : Fin params.m) :=
  Role × RestrictedDiagonalSample params j

/-- Deterministic classical answers for the two provers in the low individual
degree test. -/
structure TwoProverClassicalLIDStrategy (params : Parameters) [FieldModel params.q] where
  /-- Prover A's answer to a point query. -/
  pointAnswerA : Point params → Fq params
  /-- Prover A's answer to an axis-parallel line query. -/
  axisParallelAnswerA : AxisParallelLine params → AxisLinePolynomial params
  /-- Prover A's answer to a diagonal-line query. -/
  diagonalAnswerA : DiagonalLine params → DiagonalLinePolynomial params
  /-- Prover B's answer to a point query. -/
  pointAnswerB : Point params → Fq params
  /-- Prover B's answer to an axis-parallel line query. -/
  axisParallelAnswerB : AxisParallelLine params → AxisLinePolynomial params
  /-- Prover B's answer to a diagonal-line query. -/
  diagonalAnswerB : DiagonalLine params → DiagonalLinePolynomial params

namespace TwoProverClassicalLIDStrategy

/-- The axis-parallel line carried by an `AxisParallelTestSample`. -/
def axisParallelLineOfSample (params : Parameters)
    (s : AxisParallelTestSample params) : AxisParallelLine params where
  base := s.1
  direction := s.2

/-- The sampled point in the axis-parallel branch is the line's base point. -/
def axisParallelPointOfSample (params : Parameters)
    (s : AxisParallelTestSample params) : Point params :=
  s.1

/-- The full diagonal direction encoded by a restricted diagonal sample. -/
def restrictedDiagonalDirectionOfSample {params : Parameters}
    [FieldModel params.q] (j : Fin params.m)
    (s : RestrictedDiagonalSample params j) : Point params :=
  extendRestrictedDirection j s.2

/-- The diagonal line carried by a restricted diagonal sample. -/
def restrictedDiagonalLineOfSample {params : Parameters} [FieldModel params.q]
    (j : Fin params.m) (s : RestrictedDiagonalSample params j) :
    DiagonalLine params where
  base := s.1
  direction := restrictedDiagonalDirectionOfSample j s

/-- The sampled point in the restricted diagonal branch is the line's base point. -/
def restrictedDiagonalPointOfSample {params : Parameters}
    (j : Fin params.m) (s : RestrictedDiagonalSample params j) : Point params :=
  s.1

/-- Whether the deterministic strategy is accepted on a sampled axis-parallel
branch instance. -/
def axisParallelAccepts {params : Parameters} [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params)
    (rs : ClassicalAxisParallelSample params) : Prop :=
  let r := rs.1
  let s := rs.2
  let ℓ := axisParallelLineOfSample params s
  let u := axisParallelPointOfSample params s
  match r with
  | .A => strategy.axisParallelAnswerA ℓ zeroCoord = strategy.pointAnswerB u
  | .B => strategy.pointAnswerA u = strategy.axisParallelAnswerB ℓ zeroCoord

/-- Whether the deterministic strategy is accepted on the modeled
self-consistency branch.

The repository's current `ProjStrat.lowIndividualDegreeFailureProbability`
models the self-consistency branch via each prover's own strong
self-consistency defect rather than cross-prover point agreement. For a
deterministic classical point-answer function, that branch succeeds identically,
so the acceptance predicate is `True`. -/
def selfConsistencyAccepts {params : Parameters} [FieldModel params.q]
    (_strategy : TwoProverClassicalLIDStrategy params)
    (_u : ClassicalSelfConsistencySample params) : Prop :=
  True

/-- Whether the deterministic strategy is accepted on a sampled `j`-restricted
 diagonal branch instance. -/
def restrictedDiagonalAccepts {params : Parameters} [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params)
    (j : Fin params.m)
    (rs : ClassicalRestrictedDiagonalSample params j) : Prop :=
  let r := rs.1
  let s := rs.2
  let ℓ := restrictedDiagonalLineOfSample j s
  let u := restrictedDiagonalPointOfSample j s
  match r with
  | .A => strategy.diagonalAnswerA ℓ zeroCoord = strategy.pointAnswerB u
  | .B => strategy.pointAnswerA u = strategy.diagonalAnswerB ℓ zeroCoord

/-- Acceptance probability of the axis-parallel branch of the classical low
individual degree test. -/
open scoped Classical in
noncomputable def axisParallelAcceptanceProbability {params : Parameters}
    [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params) : Error :=
  avgOver (uniformDistribution (ClassicalAxisParallelSample params)) fun rs =>
    if strategy.axisParallelAccepts rs then (1 : Error) else 0

/-- Acceptance probability of the self-consistency branch of the classical low
individual degree test. -/
open scoped Classical in
noncomputable def selfConsistencyAcceptanceProbability {params : Parameters}
    [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params) : Error :=
  avgOver (uniformDistribution (ClassicalSelfConsistencySample params)) fun u =>
    if strategy.selfConsistencyAccepts u then (1 : Error) else 0

/-- Acceptance probability of the `j`-restricted diagonal branch. -/
open scoped Classical in
noncomputable def restrictedDiagonalAcceptanceProbability {params : Parameters}
    [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params)
    (j : Fin params.m) : Error :=
  avgOver (uniformDistribution (ClassicalRestrictedDiagonalSample params j)) fun rs =>
    if strategy.restrictedDiagonalAccepts j rs then (1 : Error) else 0

/-- Acceptance probability of the full diagonal branch of the classical low
individual degree test.

The branch first samples `j : Fin params.m` uniformly and then a role-tagged
restricted diagonal sample for that `j`.

TODO(#404): prove that this classical branch decomposition matches the
repository's modeled `ProjStrat.lowIndividualDegreeFailureProbability`,
especially the order of averaging over the restriction index and the sampled
role. -/
noncomputable def diagonalAcceptanceProbability {params : Parameters}
    [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params) : Error :=
  (1 / (params.m : Error)) *
    ∑ j : Fin params.m, strategy.restrictedDiagonalAcceptanceProbability j

/-- Acceptance probability of the full classical low individual degree test,
averaging the three branches with equal probability. -/
noncomputable def lowIndividualDegreeAcceptanceProbability {params : Parameters}
    [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params) : Error :=
  (strategy.axisParallelAcceptanceProbability +
      strategy.selfConsistencyAcceptanceProbability +
      strategy.diagonalAcceptanceProbability) / 3

/-- Passing the repository's modeled classical low individual degree test with
error `eps`, stated in acceptance-probability form.

This name is deliberately distinct from `ProjStrat.PassesLowIndividualDegreeTest`
so the classical specialization does not collide by dot notation with the
quantum/projective predicate. -/
structure ClassicallyPassesLowIndividualDegreeTest {params : Parameters}
    [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params) (eps : Error) : Prop where
  /-- The modeled classical acceptance probability is at least `1 - eps`. -/
  acceptanceLowerBound :
    1 - eps ≤ strategy.lowIndividualDegreeAcceptanceProbability

end TwoProverClassicalLIDStrategy

end Test

end MIPStarRE.LDT
