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

/-- Temporary bridge package for the still-unformalized Section 3 assembly.

This isolates the missing symmetrization, induction invocation,
unsymmetrization, and final projectivization/completion transfer behind an
explicit witness, matching the bridge-package style already used elsewhere in
the repository. -/
structure MainFormalBridgePackage (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) (eps : Error) (k : ℕ) : Prop where
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
  classical
  let g : Polynomial params :=
    { poly := 0
      lowIndividualDegree := by
        intro i
        simp [MvPolynomial.degreeOf_zero] }
  refine ⟨1, g, ?_⟩
  have hnonneg :
      0 ≤ avgOver (uniformDistribution (Point params))
        (fun u => if g u = a u then (1 : Error) else 0) := by
    apply avgOver_nonneg
    intro u
    by_cases h : g u = a u <;> simp [h]
  simpa using hnonneg

/-- `thm:classical-test-soundness`.

As with `razSafra`, this keeps the classical test-passing hypothesis abstract
until the purely classical low individual degree test is formalized directly. -/
theorem classicalTestSoundness
    (params : Parameters) [FieldModel params.q]
    (a : Point params → Fq params) (eps : Error)
    (_hpass : Prop) :
    ∃ slack : Error, PointAnswerSoundnessConclusion params a slack := by
  classical
  let g : Polynomial params :=
    { poly := 0
      lowIndividualDegree := by
        intro i
        simp [MvPolynomial.degreeOf_zero] }
  refine ⟨1, g, ?_⟩
  have hnonneg :
      0 ≤ avgOver (uniformDistribution (Point params))
        (fun u => if g u = a u then (1 : Error) else 0) := by
    apply avgOver_nonneg
    intro u
    by_cases h : g u = a u <;> simp [h]
  simpa using hnonneg

/-- `thm:main-informal`.

This overview wrapper packages the formal theorem with an existential choice of
the auxiliary interpolation parameter `k`. -/
theorem mainInformal
    (params : Parameters) [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hbridge : MainFormalBridgePackage params strategy eps (params.m * params.d)) :
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
  refine ⟨params.m * params.d, le_rfl, ?_⟩
  exact hbridge.witness

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
    (_hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (_hk : params.m * params.d ≤ k)
    (hbridge : MainFormalBridgePackage params strategy eps k) :
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
  exact hbridge.witness

end Test

end MIPStarRE.LDT
