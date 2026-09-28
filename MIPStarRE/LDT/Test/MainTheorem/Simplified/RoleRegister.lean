import MIPStarRE.LDT.MainInductionStep.Simplified.Main
import MIPStarRE.LDT.Test.MainTheorem.SourceRoleRegister.Core

/-!
# Role-register handoff for simplified soundness

The existing heterogeneous role-register construction and block-extraction
lemmas apply unchanged to the simplified main induction. This module replaces
only their old induction call and retains the factor-two unsymmetrization.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-formal`.
- `references/ldt-paper/inductive_step.tex:26-133`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.ProjStrat

/-- A two-space projective strategy yields complete polynomial measurements
whose point consistency is controlled by the simplified induction error. -/
theorem simplifiedRoleRegisterPointConsistency
    (params : Parameters) [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    ∃ G_A : Measurement (Polynomial params) ιA,
      ∃ G_B : Measurement (Polynomial params) ιB,
        ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params G_B.toSubMeas)
            (2 * MainInductionStep.simplifiedMainInductionError params
              (3 * eps) (3 * eps) (3 * eps)) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params G_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
            (2 * MainInductionStep.simplifiedMainInductionError params
              (3 * eps) (3 * eps) (3 * eps)) := by
  obtain ⟨G, hG⟩ :=
    MainInductionStep.simplifiedMainInduction params
      strategy.roleRegisterSymmStrategy
      (3 * eps) (3 * eps) (3 * eps)
      (roleRegisterSymmStrategy_is_good_three_mul
        (strategy := strategy) (eps := eps) hpass)
  exact ⟨Measurement.extractRoleRegisterAlice G,
    Measurement.extractRoleRegisterBob G,
    sourceRoleRegisterPointConsistency_ofSymConsistency
      params strategy G _ hG⟩

/-- The unchanged heterogeneous Step 5 converts both point estimates into
consistency of the complete polynomial measurements. Its intermediate error
is weaker than the simplified blueprint's projective-bridge estimate, but
still gives the requested final `1/64` exponent. -/
theorem simplifiedRoleRegisterPolynomialConsistency
    (params : Parameters) [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    let σ : Error := 2 * MainInductionStep.simplifiedMainInductionError params
      (3 * eps) (3 * eps) (3 * eps)
    ∃ G_A : Measurement (Polynomial params) ιA,
      ∃ G_B : Measurement (Polynomial params) ιB,
        ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params G_B.toSubMeas) σ ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params G_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) σ ∧
          ConsRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily G_A.toSubMeas)
            (constSubMeasFamily G_B.toSubMeas)
            (σ + 2 * Real.sqrt (3 * eps + σ) +
              (params.m * params.d : Error) / params.q) := by
  dsimp
  obtain ⟨G_A, G_B, hA, hB⟩ :=
    simplifiedRoleRegisterPointConsistency params strategy eps hpass
  refine ⟨G_A, G_B, hA, hB, ?_⟩
  exact sourceRoleRegisterFullPolynomialSelfConsistency_ofPointConsistency
    params strategy eps _ hpass G_A G_B hA hB

end MIPStarRE.LDT.ProjStrat
