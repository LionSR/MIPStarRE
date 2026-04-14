import MIPStarRE.LDT.Test.Strategy

/-!
# Section 3 — Main theorem

The main formal output of the low individual degree test (`thm:main-formal`).
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-- The explicit `ν` from `thm:main-formal`, recorded with the paper's formula. -/
noncomputable def mainFormalError (params : Parameters) (k : ℕ) (eps : Error) : Error :=
  100000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
    (Real.rpow eps (1 / (40000 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (40000 : Error)) +
      Real.exp (-((k : Error) / (2560000 * ((params.m : Error) ^ (2 : ℕ))))))

/-- Placeholder polynomial-size slack for the overview Raz--Safra statement.

The Chapter 1 overview records the dependence as `eps + poly(m) * poly(d/q)`;
the exact constants are intentionally left to the future direct formalization of
the classical result. -/
noncomputable def razSafraSlackBound (params : Parameters) (eps : Error) : Error :=
  eps + (params.m : Error) * ((params.d : Error) / (params.q : Error))

/-- Placeholder polynomial-size slack for classical low-individual-degree soundness.

The Chapter 1 overview records the dependence as
`poly(m) * (poly(eps) + poly(d/q))`; this named expression keeps that dependence
visible until the Polishchuk--Spielman theorem is formalized directly. -/
noncomputable def classicalTestSoundnessSlackBound
    (params : Parameters) (eps : Error) : Error :=
  ((params.m : Error) ^ (2 : ℕ)) *
    (Real.sqrt eps + (params.d : Error) / (params.q : Error))

/-- Deterministic classical data for the low individual degree test. -/
structure ClassicalLowIndividualDegreeStrategy
    (params : Parameters) [FieldModel params.q] where
  /-- The prover's point answer. -/
  pointAnswer : Point params → Fq params
  /-- The prover's answer to an axis-parallel line question. -/
  axisParallelAnswer : AxisParallelLine params → AxisLinePolynomial params
  /-- The prover's answer to a diagonal line question. -/
  diagonalAnswer : DiagonalLine params → DiagonalLinePolynomial params

namespace ClassicalLowIndividualDegreeStrategy

/-- Classical failure probability for the axis-parallel branch. -/
noncomputable def axisParallelFailureProbability
    {params : Parameters} [FieldModel params.q]
    (strategy : ClassicalLowIndividualDegreeStrategy params) : Error :=
  avgOver (uniformDistribution (AxisParallelTestSample params)) fun s =>
    let ℓ : AxisParallelLine params := { base := s.1, direction := s.2 }
    if strategy.axisParallelAnswer ℓ zeroCoord = strategy.pointAnswer s.1 then
      0
    else
      1

/-- Classical failure probability for the diagonal-line branch. -/
noncomputable def diagonalFailureProbability
    {params : Parameters} [FieldModel params.q]
    (strategy : ClassicalLowIndividualDegreeStrategy params) : Error :=
  (1 / (params.m : Error)) *
    ∑ j : Fin params.m,
      avgOver (uniformDistribution (RestrictedDiagonalSample params j)) fun s =>
        let v := extendRestrictedDirection j s.2
        let ℓ : DiagonalLine params := { base := s.1, direction := v }
        if strategy.diagonalAnswer ℓ zeroCoord = strategy.pointAnswer s.1 then
          0
        else
          1

/-- Classical failure probability for the deterministic low individual degree test.

For a single deterministic point-answer function the self-consistency branch has
zero failure, so this averages the two line-consistency branches with that zero
branch. -/
noncomputable def lowIndividualDegreeFailureProbability
    {params : Parameters} [FieldModel params.q]
    (strategy : ClassicalLowIndividualDegreeStrategy params) : Error :=
  (strategy.axisParallelFailureProbability + 0 +
    strategy.diagonalFailureProbability) / 3

/-- Passing the deterministic classical low individual degree test with error `eps`. -/
structure PassesLowIndividualDegreeTest
    {params : Parameters} [FieldModel params.q]
    (strategy : ClassicalLowIndividualDegreeStrategy params) (eps : Error) : Prop where
  /-- The strategy's test failure probability is at most `eps`. -/
  soundnessHypothesis : strategy.lowIndividualDegreeFailureProbability ≤ eps

end ClassicalLowIndividualDegreeStrategy

/-- Proof-carrying pass condition for point-answer versions of the classical
surface-versus-point test.

The `a`-dependence is enforced by requiring a classical strategy whose
`pointAnswer` field agrees with `a` and that passes the low individual degree
test with error at most `eps`. -/
def PointTestPassCondition (params : Parameters) [FieldModel params.q]
    (a : Point params → Fq params) (eps : Error) : Prop :=
  ∃ (strategy : ClassicalLowIndividualDegreeStrategy params),
    strategy.pointAnswer = a ∧ strategy.PassesLowIndividualDegreeTest eps

/-- Generic overview-level soundness conclusion: a low individual degree
polynomial agrees with the point-answer function except on `slack` average mass,
where `slack` is constrained by the theorem's named error bound.

This is used for the two classical theorems quoted in Chapter 1, whose exact
constants are not yet formalized in this repository. -/
def PointAnswerSoundnessConclusion (params : Parameters) [FieldModel params.q]
    (a : Point params → Fq params) (slackBound slack : Error) : Prop :=
  0 ≤ slack ∧
    slack ≤ 1 ∧
      slack ≤ slackBound ∧
        ∃ g : Polynomial params,
          avgOver (uniformDistribution (Point params))
              (fun u => if g u = a u then (1 : Error) else 0) ≥
            1 - slack

/-- `thm:raz-safra`.

The surface-versus-point low-degree test itself is not yet modeled in Lean here,
so the hypothesis records an opaque but proof-carrying point-test pass condition.
-/
theorem razSafra
    (params : Parameters) [FieldModel params.q]
    (a : Point params → Fq params) (eps : Error)
    (hpass : PointTestPassCondition params a eps) :
    ∃ slack : Error,
      PointAnswerSoundnessConclusion params a (razSafraSlackBound params eps) slack := by
  sorry

/-- `thm:classical-test-soundness`.

This uses a deterministic classical test strategy with an actual pass predicate,
while leaving the Polishchuk--Spielman soundness proof itself as a quoted
classical result. -/
theorem classicalTestSoundness
    (params : Parameters) [FieldModel params.q]
    (strategy : ClassicalLowIndividualDegreeStrategy params) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    ∃ slack : Error,
      PointAnswerSoundnessConclusion params strategy.pointAnswer
        (classicalTestSoundnessSlackBound params eps) slack := by
  sorry

/-- `thm:main-informal`.

This overview wrapper packages the formal theorem with an existential choice of
the auxiliary interpolation parameter `k`. -/
theorem mainInformal
    (params : Parameters) [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    ∃ k : ℕ, params.m * params.d ≤ k ∧
      ∃ G_A G_B : ProjMeas (Polynomial params) ι,
        ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params G_B.toSubMeas)
            (mainFormalError params k eps) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params G_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
            (mainFormalError params k eps) ∧
          ConsRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily G_A.toSubMeas)
            (constSubMeasFamily G_B.toSubMeas)
            (mainFormalError params k eps) := by
  /-
  Paper reference: `blueprint/src/chapter/ch01_overview.tex`, `thm:main-informal`.
  This is the high-level existential form of `mainFormal`, leaving the choice of
  `k` abstract.
  -/
  sorry

/--
`thm:main-formal` from `test_definition.tex`.

The bipartite tensor placement follows the paper:
- **1a**: `A^A_u ⊗ I ≈_ν I ⊗ G^B_{[g(u)=a]}` — G_B on **right**
- **1b**: `I ⊗ A^B_u ≈_ν G^A_{[g(u)=a]} ⊗ I` — G_A on **left**, A^B on **right**
- **2**: `G^A_g ⊗ I ≈_ν I ⊗ G^B_g` — G_B on **right**

Fixes #137, #239.
-/
theorem mainFormal
    (params : Parameters) [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : params.m * params.d ≤ k) :
    ∃ G_A G_B : ProjMeas (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
          (polynomialEvaluationFamily params G_B.toSubMeas)
          (mainFormalError params k eps) ∧
        ConsRel strategy.state (uniformDistribution (Point params))
          (polynomialEvaluationFamily params G_A.toSubMeas)
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
          (mainFormalError params k eps) ∧
        ConsRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily G_A.toSubMeas)
          (constSubMeasFamily G_B.toSubMeas)
          (mainFormalError params k eps) := by
  /-
  The paper proof still requires the missing Section 3 assembly that turns
  `hpass` and `hk` into a `MainFormalBridgePackage`: symmetrization,
  application of the induction theorem, unsymmetrization, and the final
  projectivization/completion transfer.
  -/
  sorry

end Test

end MIPStarRE.LDT
