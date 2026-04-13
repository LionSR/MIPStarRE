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

/-- Generic overview-level soundness conclusion: a low individual degree
polynomial agrees with the point-answer function except on `slack` average mass.

This is used for the two classical theorems quoted in Chapter 1, whose full test
infrastructure is not yet formalized in this repository. -/
def PointAnswerSoundnessConclusion (params : Parameters) [FieldModel params.q]
    (a : Point params → Fq params) (slack : Error) : Prop :=
  ∃ g : Polynomial params,
    avgOver (uniformDistribution (Point params))
        (fun u => if g u = a u then (1 : Error) else 0) ≥
      1 - slack

/-- `thm:raz-safra`.

The surface-versus-point low-degree test itself is not yet modeled in Lean here,
so the hypothesis is kept opaque and this theorem records only the paper-facing
soundness conclusion. -/
theorem razSafra
    (params : Parameters) [FieldModel params.q]
    (a : Point params → Fq params) (eps : Error)
    (_hpass : Prop) :
    ∃ slack : Error, PointAnswerSoundnessConclusion params a slack := by
  sorry

/-- `thm:classical-test-soundness`.

As with `razSafra`, this keeps the classical test-passing hypothesis abstract
until the purely classical low individual degree test is formalized directly. -/
theorem classicalTestSoundness
    (params : Parameters) [FieldModel params.q]
    (a : Point params → Fq params) (eps : Error)
    (_hpass : Prop) :
    ∃ slack : Error, PointAnswerSoundnessConclusion params a slack := by
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
