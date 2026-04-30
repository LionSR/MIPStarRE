import MIPStarRE.LDT.Test.StrategyCore

/-!
# Section 3 — Classical two-prover strategies

Deterministic classical strategy data and acceptance probabilities for the
paper's two-prover classical low individual degree test from
`references/ldt-paper/test_definition.tex`.

The relation between this paper-faithful classical test model and the
repository's current quantum/projective surrogate
`SameSpaceProjStrat.lowIndividualDegreeFailureProbability` is made explicit through the
role-average lemmas below together with
`SameSpaceProjStrat.lowIndividualDegreeFailureProbability_eq_branchAverage`.
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

/-- The self-consistency branch sends the same point query to both provers. -/
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

/-- Whether the deterministic strategy is accepted on the paper's
self-consistency branch.

This is the actual verifier check from `references/ldt-paper/test_definition.tex`:
both provers receive the same point question and must return the same field
value. On the projective side,
`SameSpaceProjStrat.lowIndividualDegreeFailureProbability_eq_branchAverage` uses the
matching cross-prover point-agreement term
`SameSpaceProjStrat.pointAgreementFailureProbability`, and
`SameSpaceProjStrat.classicalRoleSymmStrategy_selfConsistency_eq_pointAgreement` explains
how that term relates to the role-register-symmetrized SSC defect used
elsewhere in the repository. -/
def selfConsistencyAccepts {params : Parameters} [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params)
    (u : ClassicalSelfConsistencySample params) : Prop :=
  strategy.pointAnswerA u = strategy.pointAnswerB u

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

/-- Reindex the two-element role average along the equivalence `Role ≃ Bool`. -/
private def roleEquivBool : Role ≃ Bool where
  toFun
    | .A => false
    | .B => true
  invFun
    | false => .A
    | true => .B
  left_inv := by
    intro r
    cases r <;> rfl
  right_inv := by
    intro b
    cases b <;> rfl

/-- A uniform average over roles is the arithmetic mean of the two role values. -/
private theorem avgOver_uniform_role (f : Role → Error) :
    avgOver (uniformDistribution Role) f = (f Role.A + f Role.B) / 2 := by
  rw [avgOver_uniform_equiv roleEquivBool f]
  simp [avgOver, uniformDistribution, roleEquivBool]
  ring_nf

/-- Average the indicator of a decidable predicate over a uniform sample space. -/
private noncomputable def indicatorAcceptanceProbability {β : Type*}
    [Fintype β] [DecidableEq β] [Nonempty β]
    (p : β → Prop) : Error := by
  classical
  exact avgOver (uniformDistribution β) fun s => if p s then (1 : Error) else 0

/-- Average the paper's role-tagged acceptance predicate over `Role × β`. -/
private noncomputable def roleTaggedAcceptanceProbability {β : Type*}
    [Fintype β] [DecidableEq β] [Nonempty β]
    (pA pB : β → Prop) : Error := by
  classical
  exact avgOver (uniformDistribution (Role × β)) fun rs =>
    if match rs.1 with
      | Role.A => pA rs.2
      | Role.B => pB rs.2
    then (1 : Error) else 0

/-- A uniform average over `Role × β` is the arithmetic mean of the two
role-specific uniform averages. -/
private theorem roleTaggedAcceptanceProbability_eq_roleAverage {β : Type*}
    [Fintype β] [DecidableEq β] [Nonempty β]
    (pA pB : β → Prop) :
    roleTaggedAcceptanceProbability pA pB =
      (indicatorAcceptanceProbability pA + indicatorAcceptanceProbability pB) / 2 := by
  classical
  unfold roleTaggedAcceptanceProbability indicatorAcceptanceProbability
  let F : Role → β → Error := fun r s =>
    if match r with
      | Role.A => pA s
      | Role.B => pB s
    then (1 : Error) else 0
  change avgOver (uniformDistribution (Role × β)) (fun rs => F rs.1 rs.2) = _
  rw [avgOver_uniform_prod]
  simpa [F] using
    (avgOver_uniform_role (fun r =>
      avgOver (uniformDistribution β) fun s => F r s))

/-- Pull a common scalar through a finite sum of arithmetic means. -/
private theorem smul_sum_half_split {α : Type*} [Fintype α]
    (m : Error) (A B : α → Error) :
    m * ∑ x, (A x + B x) / 2 =
      ((m * ∑ x, A x) + (m * ∑ x, B x)) / 2 := by
  simp_rw [div_eq_mul_inv, add_mul]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, mul_add]
  ring

/-- Axis-parallel acceptance probability for the role choice where Alice gets the
line and Bob gets the sampled base point. -/
noncomputable def axisParallelLineLeftPointRightAcceptanceProbability
    {params : Parameters} [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params) : Error :=
  indicatorAcceptanceProbability fun s : AxisParallelTestSample params =>
    strategy.axisParallelAccepts (Role.A, s)

/-- Axis-parallel acceptance probability for the role choice where Alice gets the
sampled base point and Bob gets the line. -/
noncomputable def axisParallelPointLeftLineRightAcceptanceProbability
    {params : Parameters} [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params) : Error :=
  indicatorAcceptanceProbability fun s : AxisParallelTestSample params =>
    strategy.axisParallelAccepts (Role.B, s)

/-- Acceptance probability of the axis-parallel branch of the classical low
individual degree test. -/
noncomputable def axisParallelAcceptanceProbability {params : Parameters}
    [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params) : Error :=
  roleTaggedAcceptanceProbability
    (fun s : AxisParallelTestSample params =>
      strategy.axisParallelAccepts (Role.A, s))
    (fun s : AxisParallelTestSample params =>
      strategy.axisParallelAccepts (Role.B, s))

/-- The role-tagged axis-parallel average equals the arithmetic mean of the two
crossed role choices. -/
theorem axisParallelAcceptanceProbability_eq_roleAverage {params : Parameters}
    [FieldModel params.q] (strategy : TwoProverClassicalLIDStrategy params) :
    strategy.axisParallelAcceptanceProbability =
      (strategy.axisParallelLineLeftPointRightAcceptanceProbability +
        strategy.axisParallelPointLeftLineRightAcceptanceProbability) / 2 := by
  simpa [axisParallelAcceptanceProbability,
    axisParallelLineLeftPointRightAcceptanceProbability,
    axisParallelPointLeftLineRightAcceptanceProbability] using
      (roleTaggedAcceptanceProbability_eq_roleAverage
        (pA := fun s : AxisParallelTestSample params =>
          strategy.axisParallelAccepts (Role.A, s))
        (pB := fun s : AxisParallelTestSample params =>
          strategy.axisParallelAccepts (Role.B, s)))

/-- Acceptance probability of the self-consistency branch of the classical low
individual degree test. -/
noncomputable def selfConsistencyAcceptanceProbability {params : Parameters}
    [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params) : Error :=
  indicatorAcceptanceProbability fun u : ClassicalSelfConsistencySample params =>
    strategy.selfConsistencyAccepts u

/-- Restricted-diagonal acceptance probability for the role choice where Alice
gets the diagonal line and Bob gets the sampled base point. -/
noncomputable def restrictedDiagonalLineLeftPointRightAcceptanceProbability
    {params : Parameters} [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params) (j : Fin params.m) : Error :=
  indicatorAcceptanceProbability fun s : RestrictedDiagonalSample params j =>
    strategy.restrictedDiagonalAccepts j (Role.A, s)

/-- Restricted-diagonal acceptance probability for the role choice where Alice
gets the sampled base point and Bob gets the diagonal line. -/
noncomputable def restrictedDiagonalPointLeftLineRightAcceptanceProbability
    {params : Parameters} [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params) (j : Fin params.m) : Error :=
  indicatorAcceptanceProbability fun s : RestrictedDiagonalSample params j =>
    strategy.restrictedDiagonalAccepts j (Role.B, s)

/-- Acceptance probability of the `j`-restricted diagonal branch. -/
noncomputable def restrictedDiagonalAcceptanceProbability {params : Parameters}
    [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params)
    (j : Fin params.m) : Error :=
  roleTaggedAcceptanceProbability
    (fun s : RestrictedDiagonalSample params j =>
      strategy.restrictedDiagonalAccepts j (Role.A, s))
    (fun s : RestrictedDiagonalSample params j =>
      strategy.restrictedDiagonalAccepts j (Role.B, s))

/-- The role-tagged restricted-diagonal average equals the arithmetic mean of the
corresponding two crossed role choices. -/
theorem restrictedDiagonalAcceptanceProbability_eq_roleAverage {params : Parameters}
    [FieldModel params.q] (strategy : TwoProverClassicalLIDStrategy params)
    (j : Fin params.m) :
    strategy.restrictedDiagonalAcceptanceProbability j =
      (strategy.restrictedDiagonalLineLeftPointRightAcceptanceProbability j +
        strategy.restrictedDiagonalPointLeftLineRightAcceptanceProbability j) / 2 := by
  simpa [restrictedDiagonalAcceptanceProbability,
    restrictedDiagonalLineLeftPointRightAcceptanceProbability,
    restrictedDiagonalPointLeftLineRightAcceptanceProbability] using
      (roleTaggedAcceptanceProbability_eq_roleAverage
        (pA := fun s : RestrictedDiagonalSample params j =>
          strategy.restrictedDiagonalAccepts j (Role.A, s))
        (pB := fun s : RestrictedDiagonalSample params j =>
          strategy.restrictedDiagonalAccepts j (Role.B, s)))

/-- Diagonal acceptance probability for the role choice where Alice gets the
sampled diagonal line and Bob gets the sampled base point. -/
noncomputable def diagonalLineLeftPointRightAcceptanceProbability
    {params : Parameters} [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params) : Error :=
  (1 / (params.m : Error)) *
    ∑ j : Fin params.m,
      strategy.restrictedDiagonalLineLeftPointRightAcceptanceProbability j

/-- Diagonal acceptance probability for the role choice where Alice gets the
sampled base point and Bob gets the sampled diagonal line. -/
noncomputable def diagonalPointLeftLineRightAcceptanceProbability
    {params : Parameters} [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params) : Error :=
  (1 / (params.m : Error)) *
    ∑ j : Fin params.m,
      strategy.restrictedDiagonalPointLeftLineRightAcceptanceProbability j

/-- Acceptance probability of the full diagonal branch of the classical low
individual degree test.

The branch first samples `j : Fin params.m` uniformly and then a role-tagged
restricted diagonal sample for that `j`. The theorem
`diagonalAcceptanceProbability_eq_roleAverage` below makes the restricted-
diagonal averaging order explicit on the classical side, matching the paper's
role-first presentation. -/
noncomputable def diagonalAcceptanceProbability {params : Parameters}
    [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params) : Error :=
  (1 / (params.m : Error)) *
    ∑ j : Fin params.m, strategy.restrictedDiagonalAcceptanceProbability j

/-- The full diagonal acceptance probability equals the arithmetic mean of the
two crossed role-choice diagonal averages. This makes the restricted-diagonal
averaging order explicit in the classical model. -/
theorem diagonalAcceptanceProbability_eq_roleAverage {params : Parameters}
    [FieldModel params.q] (strategy : TwoProverClassicalLIDStrategy params) :
    strategy.diagonalAcceptanceProbability =
      (strategy.diagonalLineLeftPointRightAcceptanceProbability +
        strategy.diagonalPointLeftLineRightAcceptanceProbability) / 2 := by
  unfold diagonalAcceptanceProbability
    diagonalLineLeftPointRightAcceptanceProbability
    diagonalPointLeftLineRightAcceptanceProbability
  simp_rw [restrictedDiagonalAcceptanceProbability_eq_roleAverage]
  exact smul_sum_half_split (1 / (params.m : Error))
    (fun j => strategy.restrictedDiagonalLineLeftPointRightAcceptanceProbability j)
    (fun j => strategy.restrictedDiagonalPointLeftLineRightAcceptanceProbability j)

/-- Acceptance probability of the full classical low individual degree test,
averaging the three branches with equal probability. -/
noncomputable def lowIndividualDegreeAcceptanceProbability {params : Parameters}
    [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params) : Error :=
  (strategy.axisParallelAcceptanceProbability +
      strategy.selfConsistencyAcceptanceProbability +
      strategy.diagonalAcceptanceProbability) / 3

/-- The full classical test acceptance probability is the acceptance-side
analogue of `SameSpaceProjStrat.lowIndividualDegreeFailureProbability_eq_branchAverage`:
both formulas average the same axis-parallel and diagonal role choices and use
the same cross-prover point-agreement self-consistency branch. Together with
`SameSpaceProjStrat.classicalRoleSymmStrategy_selfConsistency_eq_pointAgreement`, this
also explains how the comparison interfaces with the symmetric-strategy SSC
defect used elsewhere in the repository. -/
theorem lowIndividualDegreeAcceptanceProbability_eq_branchAverage
    {params : Parameters} [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params) :
    strategy.lowIndividualDegreeAcceptanceProbability =
      ((strategy.axisParallelLineLeftPointRightAcceptanceProbability +
          strategy.axisParallelPointLeftLineRightAcceptanceProbability) / 2 +
        strategy.selfConsistencyAcceptanceProbability +
        (strategy.diagonalLineLeftPointRightAcceptanceProbability +
          strategy.diagonalPointLeftLineRightAcceptanceProbability) / 2) / 3 := by
  calc
    strategy.lowIndividualDegreeAcceptanceProbability
      = ((strategy.axisParallelLineLeftPointRightAcceptanceProbability +
            strategy.axisParallelPointLeftLineRightAcceptanceProbability) / 2 +
          strategy.selfConsistencyAcceptanceProbability +
          strategy.diagonalAcceptanceProbability) / 3 := by
            rw [lowIndividualDegreeAcceptanceProbability,
              axisParallelAcceptanceProbability_eq_roleAverage]
    _ = ((strategy.axisParallelLineLeftPointRightAcceptanceProbability +
            strategy.axisParallelPointLeftLineRightAcceptanceProbability) / 2 +
          strategy.selfConsistencyAcceptanceProbability +
          (strategy.diagonalLineLeftPointRightAcceptanceProbability +
            strategy.diagonalPointLeftLineRightAcceptanceProbability) / 2) / 3 := by
            rw [diagonalAcceptanceProbability_eq_roleAverage]

/-- Passing the paper's deterministic two-prover classical low individual degree
test with error `eps`, stated in acceptance-probability form.

This name is deliberately distinct from `SameSpaceProjStrat.PassesLowIndividualDegreeTest`
so this paper-faithful classical predicate does not collide by dot notation with
the repository's quantum/projective surrogate predicate. The precise branch
comparison is exposed concretely by
`lowIndividualDegreeAcceptanceProbability_eq_branchAverage` on the classical side
and `SameSpaceProjStrat.lowIndividualDegreeFailureProbability_eq_branchAverage` on the
projective side. -/
structure ClassicallyPassesLowIndividualDegreeTest {params : Parameters}
    [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params) (eps : Error) : Prop where
  /-- The modeled classical acceptance probability is at least `1 - eps`. -/
  acceptanceLowerBound :
    1 - eps ≤ strategy.lowIndividualDegreeAcceptanceProbability

end TwoProverClassicalLIDStrategy

end Test

end MIPStarRE.LDT
