import MIPStarRE.LDT.Test.SurfaceVsPoint

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

The Chapter 1 overview records the dependence only schematically as
`poly(m) * (poly(eps) + poly(d/q))`. The cited bivariate
Polishchuk--Spielman estimate [PS94, Theorem 9] has a square-root shape: a
`δ^2` disagreement hypothesis yields a `2δ` conclusion. We nevertheless use
the simpler linear placeholder `eps` here so the Lean bookkeeping follows the
same integer-polynomial convention as the overview theorem, rather than fixing a
specific fractional exponent before the full classical soundness theorem is
formalized directly. -/
noncomputable def classicalTestSoundnessSlackBound
    (params : Parameters) (eps : Error) : Error :=
  ((params.m : Error) ^ (2 : ℕ)) *
    (eps + (params.d : Error) / (params.q : Error))

/-- Overview-level soundness conclusion: a low individual degree polynomial
agrees with the point-answer function except on `slack` average mass, with
explicit bound `slackBound`. -/
def PointAnswerSoundnessConclusion (params : Parameters) [FieldModel params.q]
    (a : Point params → Fq params) (slackBound slack : Error) : Prop :=
  0 ≤ slack ∧
    slack ≤ slackBound ∧
      ∃ g : Polynomial params,
        avgOver (uniformDistribution (Point params))
            (fun u => if g u = a u then (1 : Error) else 0) ≥
          1 - slack

/-- Pass condition for the classical `k = 2` surface-versus-point low-degree
test from `references/ldt-paper/introduction.tex`.

This records only the paper-faithful classical test-passing data:
- a deterministic classical strategy for the surface-versus-point test,
- a proof that Alice's point-answer function is the ambient `a`, and
- a proof that the strategy passes the modeled random-point / genuine-surface
  acceptance test with probability at least `1 - eps`.

This is intentionally NOT `PassesLowIndividualDegreeTest`, which models a
different test. -/
def SurfaceVsPointPassCondition (params : Parameters) [FieldModel params.q]
    (a : Point params → Fq params) (eps : Error) : Prop :=
  ∃ strategy : TwoProverClassicalSurfaceVsPointStrategy params,
    strategy.pointAnswerA = a ∧
      strategy.ClassicallyPassesSurfaceVsPointTest eps

/-- Pass condition for the paper's deterministic two-prover classical low
individual degree test.

This records only the paper-faithful classical test-passing data:
- a deterministic classical strategy for the two-prover low individual degree
  test from `references/ldt-paper/test_definition.tex`,
- a proof that Alice's point-answer function is the ambient `a`, and
- a proof that the strategy passes that classical test with acceptance
  probability at least `1 - eps`.

The quoted Polishchuk–Spielman soundness implication is kept separate in
`PolishchukSpielmanClassicalSoundnessStatement` so downstream theorems state the
external dependency explicitly, without making it ambient proof power. -/
def TwoProverClassicalLIDPassCondition (params : Parameters)
    [FieldModel params.q]
    (a : Point params → Fq params) (eps : Error) : Prop :=
  ∃ strategy : TwoProverClassicalLIDStrategy params,
    strategy.pointAnswerA = a ∧
      strategy.ClassicallyPassesLowIndividualDegreeTest eps

/-- Hypothesis-style interface for the classical Raz--Safra
surface-versus-point soundness theorem.

This keeps the quoted classical theorem explicit, rather than making it an
ambient axiom. Downstream wrappers take a term of this `Prop` as an explicit
hypothesis, mirroring `PolishchukSpielmanClassicalSoundnessStatement`. -/
def RazSafraSoundnessStatement (params : Parameters)
    [FieldModel params.q] : Prop :=
  ∀ (a : Point params → Fq params) (eps : Error),
    SurfaceVsPointPassCondition params a eps →
      ∃ slack : Error,
        PointAnswerSoundnessConclusion params a (razSafraSlackBound params eps) slack

/-- Hypothesis-style interface for the classical low-individual-degree
soundness result of Polishchuk and Spielman.

This issue-#408 `Prop`-valued interface replaces the earlier ambient axiom with
an explicit hypothesis at each call site. The external witness now carries its
own slack bound parameter `slackBound`, so issue #408 no longer bakes the
still-unaudited placeholder `classicalTestSoundnessSlackBound` into the quoted
external statement. The current placeholder instantiation is kept separate in
`classicalTestSoundnessWithPlaceholderBound`. The regression audit in
`MIPStarRE.LDT.Test.AxiomAudit` checks that `classicalTestSoundness` remains
kernel-clean apart from the standard Lean axioms. -/
def PolishchukSpielmanClassicalSoundnessStatement (params : Parameters)
    [FieldModel params.q]
    (a : Point params → Fq params) (eps slackBound : Error) : Prop :=
  TwoProverClassicalLIDPassCondition params a eps →
    ∃ slack : Error,
      PointAnswerSoundnessConclusion params a slackBound slack

/-- `thm:raz-safra`.

Quoted overview theorem wrapper: from paper-faithful surface-versus-point
classical test-passing data together with an explicit witness of the external
Raz--Safra soundness statement, conclude that Alice's point-answer function is
close to a low-degree polynomial with slack bounded by
`razSafraSlackBound params eps`. -/
theorem razSafra
    (params : Parameters) [FieldModel params.q]
    (a : Point params → Fq params) (eps : Error)
    (hpass : SurfaceVsPointPassCondition params a eps)
    (hRS : RazSafraSoundnessStatement params) :
    ∃ slack : Error,
      PointAnswerSoundnessConclusion params a (razSafraSlackBound params eps) slack := by
  exact hRS a eps hpass

/-- `thm:classical-test-soundness`.

Quoted classical overview theorem wrapper: from paper-faithful classical LID
test-passing data together with an explicit witness of the
Polishchuk–Spielman soundness statement at a chosen slack bound `slackBound`,
conclude that prover A's point-answer function is close to a low-degree
polynomial with that same bound. -/
theorem classicalTestSoundness
    (params : Parameters) [FieldModel params.q]
    (a : Point params → Fq params) (eps slackBound : Error)
    (hpass : TwoProverClassicalLIDPassCondition params a eps)
    (hPS : PolishchukSpielmanClassicalSoundnessStatement params a eps slackBound) :
    ∃ slack : Error,
      PointAnswerSoundnessConclusion params a slackBound slack := by
  exact hPS hpass

/-- Placeholder convenience instantiation of `classicalTestSoundness` using the
repository's current named slack bound.

This wrapper fixes the slack bound to the overview-level linear placeholder
`classicalTestSoundnessSlackBound`, which matches the schematic `poly(eps)`
convention used in Chapter 1. -/
theorem classicalTestSoundnessWithPlaceholderBound
    (params : Parameters) [FieldModel params.q]
    (a : Point params → Fq params) (eps : Error)
    (hpass : TwoProverClassicalLIDPassCondition params a eps)
    (hPS : PolishchukSpielmanClassicalSoundnessStatement params a eps
      (classicalTestSoundnessSlackBound params eps)) :
    ∃ slack : Error,
      PointAnswerSoundnessConclusion params a
        (classicalTestSoundnessSlackBound params eps) slack := by
  exact classicalTestSoundness params a eps
    (classicalTestSoundnessSlackBound params eps) hpass hPS

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
    (hd : 0 < params.d)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : params.m * params.d ≤ k)
    (hk0 : 0 < k) :
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
  -- TODO(Section 3): formalize the paper-faithful assembly from `hpass` and
  -- `hk` through role-register symmetrization, `thm:main-induction`,
  -- unsymmetrization, Schwartz-Zippel, and the final projectivization and
  -- error bookkeeping argument.
  sorry

end Test

end MIPStarRE.LDT
