import MIPStarRE.LDT.Test.Classical

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

/-- Generic placeholder overview-level soundness conclusion: a low individual
degree polynomial agrees with the point-answer function except on `slack`
average mass.

The `slack ≤ max 1 slackBound` guard keeps this conclusion compatible with the
still-placeholder Raz–Safra hypothesis. Once the surface-versus-point test is
formalized directly, this should be replaced by the bounded variant below. -/
def PointAnswerSoundnessConclusion (params : Parameters) [FieldModel params.q]
    (a : Point params → Fq params) (slackBound slack : Error) : Prop :=
  0 ≤ slack ∧
    slack ≤ max 1 slackBound ∧
      ∃ g : Polynomial params,
        avgOver (uniformDistribution (Point params))
            (fun u => if g u = a u then (1 : Error) else 0) ≥
          1 - slack

/-- Non-vacuous overview-level soundness conclusion with an explicit slack
bound.

This is the form used by the classical two-prover theorem once the quoted
Polishchuk–Spielman implication is supplied separately as a bridge package. -/
def BoundedPointAnswerSoundnessConclusion (params : Parameters)
    [FieldModel params.q]
    (a : Point params → Fq params) (slackBound slack : Error) : Prop :=
  0 ≤ slack ∧
    slack ≤ slackBound ∧
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
  0 ≤ eps

/-- Pass condition for the paper's deterministic two-prover classical low
individual degree test.

This records only the paper-faithful classical test-passing data:
- a deterministic classical strategy for the two-prover low individual degree
  test from `references/ldt-paper/test_definition.tex`,
- a proof that Alice's point-answer function is the ambient `a`, and
- a proof that the strategy passes that classical test with acceptance
  probability at least `1 - eps`.

The quoted Polishchuk–Spielman soundness implication is kept separate in the
standalone theorem interface `polishchukSpielmanClassicalSoundness`, so
consumers can refer to that external dependency by name rather than projecting a
bundled conclusion out of a hypothesis. -/
def TwoProverClassicalLIDPassCondition (params : Parameters)
    [FieldModel params.q]
    (a : Point params → Fq params) (eps : Error) : Prop :=
  ∃ strategy : TwoProverClassicalLIDStrategy params,
    strategy.pointAnswerA = a ∧
      strategy.ClassicallyPassesLowIndividualDegreeTest eps

/-- Quoted theorem interface for the classical low-individual-degree soundness
result of Polishchuk and Spielman.

This explicit axiom is the single named interface for the external implication
from paper-faithful classical test-passing data to low-degree agreement.
Keeping the quoted-result dependency here, rather than threading an extra bridge
hypothesis through every consumer, makes the remaining external assumption both
localized and visible to `#print axioms`. -/
axiom polishchukSpielmanClassicalSoundness
    (params : Parameters) [FieldModel params.q]
    (a : Point params → Fq params) (eps : Error)
    (hpass : TwoProverClassicalLIDPassCondition params a eps) :
    ∃ slack : Error,
      BoundedPointAnswerSoundnessConclusion params a
        (classicalTestSoundnessSlackBound params eps) slack

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

The overview theorem is now stated directly from paper-faithful classical
LID test-passing data, and its proof simply invokes the dedicated quoted theorem
interface `polishchukSpielmanClassicalSoundness`. This keeps the remaining
external dependency explicit in one named declaration rather than as an extra
hypothesis on every consumer. -/
theorem classicalTestSoundness
    (params : Parameters) [FieldModel params.q]
    (a : Point params → Fq params) (eps : Error)
    (hpass : TwoProverClassicalLIDPassCondition params a eps) :
    ∃ slack : Error,
      BoundedPointAnswerSoundnessConclusion params a
        (classicalTestSoundnessSlackBound params eps) slack := by
  exact polishchukSpielmanClassicalSoundness params a eps hpass

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
