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

/-- Placeholder polynomial-size slack for the overview Raz–Safra statement.

The Chapter 1 overview records the dependence as `eps + poly(m) * poly(d/q)`;
the exact constants are intentionally left to the future direct formalization of
the classical result. -/
noncomputable def razSafraSlackBound (params : Parameters) (eps : Error) : Error :=
  eps + (params.m : Error) * ((params.d : Error) / (params.q : Error))

/-- Placeholder polynomial-size slack for classical low-individual-degree soundness.

The Chapter 1 overview records the dependence as
`poly(m) * (poly(eps) + poly(d/q))`; this named expression keeps that dependence
visible until the Polishchuk–Spielman theorem is formalized directly. -/
noncomputable def classicalTestSoundnessSlackBound
    (params : Parameters) (eps : Error) : Error :=
  ((params.m : Error) ^ (2 : ℕ)) *
    (Real.sqrt eps + (params.d : Error) / (params.q : Error))

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

The Raz–Safra theorem concerns the **surface-versus-point** low-degree test,
which is a separate classical result from the low-individual-degree test defined
in `Test/Strategy.lean`. The surface test uses 2-dimensional surface queries and
surface polynomial answers — infrastructure that is not yet modeled here.

The hypothesis `hpass` is therefore an opaque `Prop` that represents "the
answer function `a` passes the surface-versus-point test with error `eps`".
This is intentionally NOT connected to `PassesLowIndividualDegreeTest` or
`ClassicalLowIndividualDegreeStrategy`, which model the wrong test.

When the surface-versus-point test is formalized in a future PR, `hpass`
should be replaced with a concrete `SurfaceVsPointPassCondition params a eps`. -/
theorem razSafra
    (params : Parameters) [FieldModel params.q]
    (a : Point params → Fq params) (eps : Error)
    (hpass : 0 ≤ eps) :
    -- ↑ Placeholder: the real hypothesis should be a surface-vs-point
    -- test pass condition. Using `0 ≤ eps` as a minimal non-trivial
    -- requirement until that infrastructure exists.
    ∃ slack : Error,
      PointAnswerSoundnessConclusion params a (razSafraSlackBound params eps) slack := by
  sorry

/-- `thm:classical-test-soundness`.

Classical soundness of the low-individual-degree test. The paper's statement
covers a two-prover quantum strategy; this stub records the classical
single-prover specialization as a placeholder.

The hypothesis `hpass` is an opaque `Prop` representing "the two provers A and B
pass the classical low-individual-degree test with error `eps`, and `a` is
prover A's point-answer function". This is NOT modeled concretely because the
full two-prover classical test infrastructure is not yet formalized.

When two-prover classical strategies are formalized, `hpass` should become
`strategy.PassesClassicalLowIndividualDegreeTest eps ∧ strategy.pointAnswerA = a`. -/
theorem classicalTestSoundness
    (params : Parameters) [FieldModel params.q]
    (a : Point params → Fq params) (eps : Error)
    (hpass : 0 ≤ eps) :
    -- ↑ Placeholder: the real hypothesis should be a two-prover classical
    -- test pass condition. Using `0 ≤ eps` as a minimal non-trivial
    -- requirement until that infrastructure exists.
    ∃ slack : Error,
      PointAnswerSoundnessConclusion params a
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
