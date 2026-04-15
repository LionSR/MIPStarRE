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
`poly(m) * (√eps + poly(d/q))`; this named expression keeps that dependence
visible until the Polishchuk–Spielman theorem is formalized directly. -/
noncomputable def classicalTestSoundnessSlackBound
    (params : Parameters) (eps : Error) : Error :=
  ((params.m : Error) ^ (2 : ℕ)) *
    (Real.sqrt eps + (params.d : Error) / (params.q : Error))

/-- Generic overview-level soundness conclusion: a low individual degree
polynomial agrees with the point-answer function except on `slack` average mass.

The `slack ≤ max 1 slackBound` guard ensures this is trivially satisfiable
(pick `slack := 1, g := default`) so the statement is vacuously true as a
placeholder. The `slackBound` parameter records the paper's intended error
dependence; once a real test-passing hypothesis constrains `a`, the proof
should produce `slack ≤ slackBound < 1`, which is strictly stronger than
`slack ≤ max 1 slackBound`. -/
def PointAnswerSoundnessConclusion (params : Parameters) [FieldModel params.q]
    (a : Point params → Fq params) (slackBound slack : Error) : Prop :=
  0 ≤ slack ∧
    slack ≤ max 1 slackBound ∧
        ∃ g : Polynomial params,
          avgOver (uniformDistribution (Point params))
              (fun u => if g u = a u then (1 : Error) else 0) ≥
            1 - slack

/-- Placeholder pass condition for the surface-versus-point low-degree test.

The Raz–Safra test uses 2-dimensional surface queries and surface polynomial
answers — infrastructure not yet modeled in this repository. This named
placeholder `def` is `0 ≤ eps` (trivially satisfiable), but its name and
type signature carry the intended semantics. When the surface test is
formalized, replace the body with the actual pass predicate.

This is intentionally NOT `PassesLowIndividualDegreeTest`, which models a
different test. See `references/ldt-paper/introduction.tex`. -/
def SurfaceVsPointPassCondition (_params : Parameters) [FieldModel _params.q]
    (_a : Point _params → Fq _params) (eps : Error) : Prop :=
  0 ≤ eps  -- placeholder body; real definition needs surface test infrastructure

/-- Placeholder pass condition for the two-prover classical low-individual-degree
test.

The paper's `thm:classical-test-soundness` takes two quantum provers A and B
who jointly pass the classical LID test and concludes that prover A's
point-answer function is close to a low-degree polynomial. The two-prover
classical strategy infrastructure is not yet modeled here. This named
placeholder `def` is `0 ≤ eps` (trivially satisfiable), but its name and
type signature carry the intended semantics.

See `references/ldt-paper/test_definition.tex` for the precise statement. -/
def TwoProverClassicalLIDPassCondition (_params : Parameters)
    [FieldModel _params.q]
    (_a : Point _params → Fq _params) (eps : Error) : Prop :=
  0 ≤ eps  -- placeholder body; real definition needs two-prover strategy types

/-- `thm:raz-safra`.

The Raz–Safra theorem: if a point-answer function passes the
surface-versus-point low-degree test with error `eps`, then there exists a
low-degree polynomial agreeing with it on most points. -/
theorem razSafra
    (params : Parameters) [FieldModel params.q]
    (a : Point params → Fq params) (eps : Error)
    (hpass : SurfaceVsPointPassCondition params a eps) :
    ∃ slack : Error,
      PointAnswerSoundnessConclusion params a (razSafraSlackBound params eps) slack := by
  sorry

/-- `thm:classical-test-soundness`.

Classical soundness: if two provers pass the classical LID test with error `eps`,
then prover A's point-answer function is close to a low-degree polynomial. -/
theorem classicalTestSoundness
    (params : Parameters) [FieldModel params.q]
    (a : Point params → Fq params) (eps : Error)
    (hpass : TwoProverClassicalLIDPassCondition params a eps) :
    ∃ slack : Error,
      PointAnswerSoundnessConclusion params a
        (classicalTestSoundnessSlackBound params eps) slack := by
  sorry

/-- Temporary bridge package for the still-unformalized proof of
`thm:main-formal`.

This packages exactly the three projective-measurement conclusions of the main
formal theorem. It isolates the missing Section 3 assembly from the theorem
statement itself: role-register symmetrization, application of
`thm:main-induction`, unsymmetrization, Schwartz-Zippel replacement of point
evaluations by polynomial evaluations, orthonormalization/completion, and the
final triangle/data-processing error bookkeeping. -/
structure MainFormalBridgePackage
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι)
    (eps : Error) (k : ℕ) : Prop where
  witness :
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
          (mainFormalError params k eps)

/-- Producer for the temporary `thm:main-formal` bridge package.

From the paper inputs to `thm:main-formal`, the eventual proof must convert the
possibly nonsymmetric projective strategy into a role-register symmetric
strategy, prove the symmetrized strategy is good with the required constants,
apply `thm:main-induction`, unsymmetrize the resulting measurement into
`G_A` and `G_B`, derive polynomial-level self-consistency using
Schwartz-Zippel, then apply orthonormalization and completion while preserving
the final `mainFormalError` bound. -/
theorem mainFormalBridgePackage
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι)
    (eps : Error)
    (_hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (_hk : params.m * params.d ≤ k) :
    MainFormalBridgePackage params strategy eps k := by
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
  exact (mainFormalBridgePackage params strategy eps hpass k hk).witness

end Test

end MIPStarRE.LDT
