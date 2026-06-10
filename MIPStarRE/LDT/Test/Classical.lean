import MIPStarRE.LDT.Test.StrategyCore

/-!
# Section 3 — Classical two-prover strategies

Deterministic classical strategy data and acceptance probabilities for the
paper's two-prover classical low individual degree test from
`references/ldt-paper/test_definition.tex`.

The role-average lemmas below make explicit the same branch decomposition used
by the paper-faithful two-space projective strategy container `ProjStrat`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

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

/-- Whether the deterministic strategy is accepted on a sampled axis-parallel
branch instance. -/
def axisParallelAccepts {params : Parameters} [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params)
    (rs : Role × AxisParallelTestSample params) : Prop :=
  let r := rs.1
  let s := rs.2
  let ℓ : AxisParallelLine params := { base := s.1, direction := s.2 }
  let u : Point params := s.1
  match r with
  | .A => strategy.axisParallelAnswerA ℓ zeroCoord = strategy.pointAnswerB u
  | .B => strategy.pointAnswerA u = strategy.axisParallelAnswerB ℓ zeroCoord

/-- Whether the deterministic strategy is accepted on a sampled `j`-restricted
diagonal branch instance. -/
def restrictedDiagonalAccepts {params : Parameters} [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params)
    (j : Fin params.m)
    (rs : Role × RestrictedDiagonalSample params j) : Prop :=
  let r := rs.1
  let s := rs.2
  let ℓ : DiagonalLine params :=
    { base := s.1, direction := extendRestrictedDirection j s.2 }
  let u : Point params := s.1
  match r with
  | .A => strategy.diagonalAnswerA ℓ zeroCoord = strategy.pointAnswerB u
  | .B => strategy.pointAnswerA u = strategy.diagonalAnswerB ℓ zeroCoord

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
    (show avgOver (uniformDistribution Role)
        (fun r => avgOver (uniformDistribution β) fun s => F r s) =
      (avgOver (uniformDistribution β) (fun s => F Role.A s) +
        avgOver (uniformDistribution β) (fun s => F Role.B s)) / 2 by
        have hcard : Fintype.card Role = 2 := by decide
        rw [show avgOver (uniformDistribution Role)
            (fun r => avgOver (uniformDistribution β) fun s => F r s) =
          (1 / (Fintype.card Role : Error)) *
            ∑ r : Role, avgOver (uniformDistribution β) fun s => F r s by
              simp [avgOver, uniformDistribution, Finset.mul_sum]]
        rw [hcard]
        rw [Fintype.sum_eq_add Role.A Role.B (by decide) (by
          intro r hr
          cases r <;> simp at hr)]
        ring_nf)

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
  indicatorAcceptanceProbability fun u : Point params =>
    strategy.pointAnswerA u = strategy.pointAnswerB u

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
  simp_rw [div_eq_mul_inv, add_mul]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, mul_add]
  ring

/-- Acceptance probability of the full classical low individual degree test,
averaging the three branches with equal probability. -/
noncomputable def lowIndividualDegreeAcceptanceProbability {params : Parameters}
    [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params) : Error :=
  (strategy.axisParallelAcceptanceProbability +
      strategy.selfConsistencyAcceptanceProbability +
      strategy.diagonalAcceptanceProbability) / 3

/-- The full classical test acceptance probability is the acceptance-side
analogue of the branch average used for two-space projective strategies:
both formulas average the same axis-parallel and diagonal role choices and use
the same cross-prover point-agreement self-consistency branch. -/
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

This name is deliberately distinct from `ProjStrat.PassesLowIndividualDegreeTest`
so this paper-faithful classical predicate does not collide by dot notation with
the projective strategy predicate.  The precise branch comparison is exposed
concretely by `lowIndividualDegreeAcceptanceProbability_eq_branchAverage`. -/
structure ClassicallyPassesLowIndividualDegreeTest {params : Parameters}
    [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params) (eps : Error) : Prop where
  /-- The modeled classical acceptance probability is at least `1 - eps`. -/
  acceptanceLowerBound :
    1 - eps ≤ strategy.lowIndividualDegreeAcceptanceProbability

end TwoProverClassicalLIDStrategy

/-- Paper origin: `references/ldt-paper/introduction.tex`
(`\label{thm:classical-test-soundness}`).

Overview-level soundness conclusion: a low individual degree polynomial agrees
with the point-answer function except on `slack` average mass, with explicit
bound `slackBound`. -/
def PointAnswerSoundnessConclusion (params : Parameters) [FieldModel params.q]
    (a : Point params → Fq params) (slackBound slack : Error) : Prop :=
  0 ≤ slack ∧
    slack ≤ slackBound ∧
      ∃ g : Polynomial params,
        avgOver (uniformDistribution (Point params))
            (fun u => if g u = a u then (1 : Error) else 0) ≥
          1 - slack

/-- Pass condition for the paper's deterministic two-prover classical low
individual degree test.

This records only the paper-faithful classical test-passing data:
* a deterministic classical strategy for the two-prover low individual degree
  test from `references/ldt-paper/test_definition.tex`,
* a proof that Alice's point-answer function is the ambient `a`, and
* a proof that the strategy passes that classical test with acceptance
  probability at least `1 - eps`.

The quoted Polishchuk--Spielman soundness implication is kept separate in
`PolishchukSpielmanClassicalSoundnessStatement` so downstream theorems state
the external dependency explicitly, without making it ambient proof power. -/
def TwoProverClassicalLIDPassCondition (params : Parameters)
    [FieldModel params.q]
    (a : Point params → Fq params) (eps : Error) : Prop :=
  ∃ strategy : TwoProverClassicalLIDStrategy params,
    strategy.pointAnswerA = a ∧
      strategy.ClassicallyPassesLowIndividualDegreeTest eps

/-- Paper origin: external citation, Polishchuk--Spielman (`\cite{PS94}`),
restated as `\label{thm:classical-test-soundness}` in
`references/ldt-paper/introduction.tex:69-92`.

Hypothesis-style interface for the classical low-individual-degree soundness
result of Polishchuk and Spielman.

This issue-#408 `Prop`-valued interface replaces the earlier ambient axiom with
an explicit hypothesis at each call site. The external witness carries its own
slack bound parameter `slackBound`, so downstream users must supply the specific
error dependence they want to quote rather than inheriting any repository-chosen
placeholder formula for the schematic Chapter 1
`poly(m) * (poly(eps) + poly(d/q))` bound. -/
def PolishchukSpielmanClassicalSoundnessStatement (params : Parameters)
    [FieldModel params.q]
    (a : Point params → Fq params) (eps slackBound : Error) : Prop :=
  TwoProverClassicalLIDPassCondition params a eps →
    ∃ slack : Error,
      PointAnswerSoundnessConclusion params a slackBound slack

/-- `thm:classical-test-soundness`.

Quoted classical overview theorem: from paper-faithful classical LID
test-passing data together with an explicit witness of the Polishchuk--Spielman
soundness statement at a chosen slack bound `slackBound`, conclude that prover
A's point-answer function is close to a low-degree polynomial with that same
bound.  Any concrete overview-style rate must therefore be supplied by
instantiating `slackBound` and the external hypothesis `hPS`. -/
theorem classicalTestSoundness
    (params : Parameters) [FieldModel params.q]
    (a : Point params → Fq params) (eps slackBound : Error)
    (hpass : TwoProverClassicalLIDPassCondition params a eps)
    (hPS : PolishchukSpielmanClassicalSoundnessStatement params a eps slackBound) :
    ∃ slack : Error,
      PointAnswerSoundnessConclusion params a slackBound slack := by
  exact hPS hpass

end Test

end MIPStarRE.LDT
