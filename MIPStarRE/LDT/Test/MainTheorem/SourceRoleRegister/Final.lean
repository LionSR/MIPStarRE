import MIPStarRE.LDT.Test.MainTheorem.SourceRoleRegister.Completion

/-!
# Source-Boundary Role-Register Handoff: Final Point Consistency

This module contains the final completed-measurement and point-consistency
statements used by the paper-facing `thm:main-formal` route.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

open MIPStarRE.LDT.MakingMeasurementsProjective

namespace ProjStrat

/-- Alice-side projective submeasurement from the source role-register route.

This theorem combines the source role-register Step 5 theorem with the
heterogeneous orthonormalization lemma.  It is not the final theorem: it only
constructs the Alice-side projective submeasurement and its left-factor
state-dependent-distance estimate.  The Bob-side construction, completion to
projective measurements, line-169 transport, scalar absorption, and source
range remain separate work.

**Unfaithful:** The proof calls
`sourceRoleRegisterCompletePolynomialSelfConsistency`, hence transitively
`MainInductionStep.mainInduction_sourceStatement`; the latter currently relies
on the tracked source-range obligation
`MainInductionStep.mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation`.
Documented in `docs/paper-gaps/issue-906-main-formal-k-bound.tex` and issue
#1507.  Elimination: discharge the source-range obligation for
`thm:main-induction`; this theorem itself adds no bridge, package, residual,
repair, producer, input, or generic hypothesis to the paper theorem. -/
theorem sourceRoleRegisterLeftProjectiveSubmeasurement
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : params.m * params.d ≤ k) :
    ∃ G_A : Measurement (Polynomial params) ιA,
      ∃ G_B : Measurement (Polynomial params) ιB,
        ∃ P_A : ProjSubMeas (Polynomial params) ιA,
          ConsRel strategy.state (uniformDistribution (Point params))
              (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
              (polynomialEvaluationFamily params G_B.toSubMeas)
              (2 * MainInductionStep.mainInductionError params k
                (3 * eps) (3 * eps) (3 * eps)) ∧
            ConsRel strategy.state (uniformDistribution (Point params))
              (polynomialEvaluationFamily params G_A.toSubMeas)
              (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
              (2 * MainInductionStep.mainInductionError params k
                (3 * eps) (3 * eps) (3 * eps)) ∧
            ConsRel strategy.state (uniformDistribution Unit)
              (constSubMeasFamily G_A.toSubMeas)
              (constSubMeasFamily G_B.toSubMeas)
              (2 * MainInductionStep.mainInductionError params k
                  (3 * eps) (3 * eps) (3 * eps) +
                2 * Real.sqrt (3 * eps +
                  2 * MainInductionStep.mainInductionError params k
                    (3 * eps) (3 * eps) (3 * eps)) +
                (params.m * params.d : Error) / params.q) ∧
            SDDRel strategy.state (uniformDistribution Unit)
              (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
              (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) P_A.toSubMeas))
              (MakingMeasurementsProjective.orthonormalizationError
                (2 * MainInductionStep.mainInductionError params k
                    (3 * eps) (3 * eps) (3 * eps) +
                  2 * Real.sqrt (3 * eps +
                    2 * MainInductionStep.mainInductionError params k
                      (3 * eps) (3 * eps) (3 * eps)) +
                  (params.m * params.d : Error) / params.q)) := by
  rcases sourceRoleRegisterCompletePolynomialSelfConsistency
      params strategy eps hpass k hk with
    ⟨G_A, G_B, hpointAGB, hGApointB, hfull⟩
  rcases sourceRoleRegisterLeftProjectiveSubmeasurement_ofFullConsistency
      params strategy G_A G_B
      (2 * MainInductionStep.mainInductionError params k (3 * eps) (3 * eps) (3 * eps) +
        2 * Real.sqrt (3 * eps +
          2 * MainInductionStep.mainInductionError params k (3 * eps) (3 * eps) (3 * eps)) +
        (params.m * params.d : Error) / params.q)
      hfull with ⟨P_A, hP_A⟩
  exact ⟨G_A, G_B, P_A, hpointAGB, hGApointB, hfull, hP_A⟩

/-- Two-sided projective submeasurements from the source role-register route.

This theorem combines the source role-register Step 5 theorem with the
heterogeneous orthonormalization lemmas on both tensor factors.  It is still not
the final theorem: it constructs projective submeasurements and the two
state-dependent-distance estimates.  Completion to projective measurements,
line-169 transport, scalar absorption, and the source range remain separate
work.

**Unfaithful:** The proof calls
`sourceRoleRegisterCompletePolynomialSelfConsistency`, hence transitively
`MainInductionStep.mainInduction_sourceStatement`; the latter currently relies
on the tracked source-range obligation
`MainInductionStep.mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation`.
Documented in `docs/paper-gaps/issue-906-main-formal-k-bound.tex` and issue
#1507.  Elimination: discharge the source-range obligation for
`thm:main-induction`; this theorem itself adds no bridge, package, residual,
repair, producer, input, or generic hypothesis to the paper theorem. -/
theorem sourceRoleRegisterTwoSidedProjectiveSubmeasurements
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : params.m * params.d ≤ k) :
    ∃ G_A : Measurement (Polynomial params) ιA,
      ∃ G_B : Measurement (Polynomial params) ιB,
        ∃ P_A : ProjSubMeas (Polynomial params) ιA,
          ∃ P_B : ProjSubMeas (Polynomial params) ιB,
            ConsRel strategy.state (uniformDistribution (Point params))
                (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
                (polynomialEvaluationFamily params G_B.toSubMeas)
                (2 * MainInductionStep.mainInductionError params k
                  (3 * eps) (3 * eps) (3 * eps)) ∧
              ConsRel strategy.state (uniformDistribution (Point params))
                (polynomialEvaluationFamily params G_A.toSubMeas)
                (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
                (2 * MainInductionStep.mainInductionError params k
                  (3 * eps) (3 * eps) (3 * eps)) ∧
              ConsRel strategy.state (uniformDistribution Unit)
                (constSubMeasFamily G_A.toSubMeas)
                (constSubMeasFamily G_B.toSubMeas)
                (2 * MainInductionStep.mainInductionError params k
                    (3 * eps) (3 * eps) (3 * eps) +
                  2 * Real.sqrt (3 * eps +
                    2 * MainInductionStep.mainInductionError params k
                      (3 * eps) (3 * eps) (3 * eps)) +
                  (params.m * params.d : Error) / params.q) ∧
              SDDRel strategy.state (uniformDistribution Unit)
                (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
                (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) P_A.toSubMeas))
                (MakingMeasurementsProjective.orthonormalizationError
                  (2 * MainInductionStep.mainInductionError params k
                      (3 * eps) (3 * eps) (3 * eps) +
                    2 * Real.sqrt (3 * eps +
                      2 * MainInductionStep.mainInductionError params k
                        (3 * eps) (3 * eps) (3 * eps)) +
                    (params.m * params.d : Error) / params.q)) ∧
              SDDRel strategy.state (uniformDistribution Unit)
                (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas))
                (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) P_B.toSubMeas))
                (MakingMeasurementsProjective.orthonormalizationError
                  (2 * MainInductionStep.mainInductionError params k
                      (3 * eps) (3 * eps) (3 * eps) +
                    2 * Real.sqrt (3 * eps +
                      2 * MainInductionStep.mainInductionError params k
                        (3 * eps) (3 * eps) (3 * eps)) +
                    (params.m * params.d : Error) / params.q)) := by
  rcases sourceRoleRegisterCompletePolynomialSelfConsistency
      params strategy eps hpass k hk with
    ⟨G_A, G_B, hpointAGB, hGApointB, hfull⟩
  let ζ₁ : Error :=
    2 * MainInductionStep.mainInductionError params k (3 * eps) (3 * eps) (3 * eps) +
      2 * Real.sqrt (3 * eps +
        2 * MainInductionStep.mainInductionError params k (3 * eps) (3 * eps) (3 * eps)) +
      (params.m * params.d : Error) / params.q
  have hfullζ : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ζ₁ := by
    simpa [ζ₁] using hfull
  rcases sourceRoleRegisterLeftProjectiveSubmeasurement_ofFullConsistency
      params strategy G_A G_B ζ₁ hfullζ with ⟨P_A, hP_A⟩
  rcases sourceRoleRegisterRightProjectiveSubmeasurement_ofFullConsistency
      params strategy G_A G_B ζ₁ hfullζ with ⟨P_B, hP_B⟩
  exact ⟨G_A, G_B, P_A, P_B, hpointAGB, hGApointB, hfull, by
    simpa [ζ₁] using hP_A, by
    simpa [ζ₁] using hP_B⟩

/-- Completed projective measurements from the source role-register route.

This theorem carries the heterogeneous role-register construction through the
completion step in `references/ldt-paper/inductive_step.tex:143-149`.  Starting
from the paper hypotheses for the two-space strategy, it constructs the
complete polynomial measurements `G_A,G_B`, the projective submeasurements
`P_A,P_B`, and the completed projective measurements `Q_A,Q_B`, together with
the two tensor-factor state-dependent-distance estimates at the literal
orthonormalize-and-complete error.

It is still not `thm:main-formal`: the remaining source-route work is the
line-169 transport from the polynomial measurements to the point measurements,
the scalar absorption into `mainFormalError`, and the source range.

**Unfaithful:** The proof calls
`sourceRoleRegisterTwoSidedProjectiveSubmeasurements`, hence transitively
`MainInductionStep.mainInduction_sourceStatement`; the latter currently relies
on the tracked source-range obligation
`MainInductionStep.mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation`.
Documented in `docs/paper-gaps/issue-906-main-formal-k-bound.tex` and issue
#1507.  Elimination: discharge the source-range obligation for
`thm:main-induction`; the completion argument in this theorem itself adds no
bridge, package, residual, repair, producer, input, or generic hypothesis to the
paper theorem. -/
theorem sourceRoleRegisterCompletedProjectiveMeasurements
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : params.m * params.d ≤ k) :
    let σ : Error :=
      2 * MainInductionStep.mainInductionError params k (3 * eps) (3 * eps) (3 * eps)
    let ζ₁ : Error :=
      σ + 2 * Real.sqrt (3 * eps + σ) + (params.m * params.d : Error) / params.q
    ∃ G_A : Measurement (Polynomial params) ιA,
      ∃ G_B : Measurement (Polynomial params) ιB,
        ∃ P_A : ProjSubMeas (Polynomial params) ιA,
          ∃ P_B : ProjSubMeas (Polynomial params) ιB,
            ∃ Q_A : ProjMeas (Polynomial params) ιA,
              ∃ Q_B : ProjMeas (Polynomial params) ιB,
                ConsRel strategy.state (uniformDistribution (Point params))
                    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
                    (polynomialEvaluationFamily params G_B.toSubMeas)
                    σ ∧
                  ConsRel strategy.state (uniformDistribution (Point params))
                    (polynomialEvaluationFamily params G_A.toSubMeas)
                    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
                    σ ∧
                  ConsRel strategy.state (uniformDistribution Unit)
                    (constSubMeasFamily G_A.toSubMeas)
                    (constSubMeasFamily G_B.toSubMeas)
                    ζ₁ ∧
                  SDDRel strategy.state (uniformDistribution Unit)
                    (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
                    (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) P_A.toSubMeas))
                    (MakingMeasurementsProjective.orthonormalizationError ζ₁) ∧
                  SDDRel strategy.state (uniformDistribution Unit)
                    (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas))
                    (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) P_B.toSubMeas))
                    (MakingMeasurementsProjective.orthonormalizationError ζ₁) ∧
                  SDDRel strategy.state (uniformDistribution Unit)
                    (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
                    (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas))
                    (MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ₁) ∧
                  SDDRel strategy.state (uniformDistribution Unit)
                    (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas))
                    (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas))
                    (MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ₁) ∧
                  ConsRel strategy.state (uniformDistribution Unit)
                    (constSubMeasFamily Q_A.toSubMeas)
                    (constSubMeasFamily G_B.toSubMeas)
                    (ζ₁ + Real.sqrt
                      (MakingMeasurementsProjective.orthonormalizationError ζ₁)) ∧
                  ConsRel strategy.state (uniformDistribution Unit)
                    (constSubMeasFamily G_A.toSubMeas)
                    (constSubMeasFamily Q_B.toSubMeas)
                    (ζ₁ + Real.sqrt
                      (MakingMeasurementsProjective.orthonormalizationError ζ₁)) := by
  let σ : Error :=
    2 * MainInductionStep.mainInductionError params k (3 * eps) (3 * eps) (3 * eps)
  let ζ₁ : Error :=
    σ + 2 * Real.sqrt (3 * eps + σ) + (params.m * params.d : Error) / params.q
  change ∃ G_A : Measurement (Polynomial params) ιA,
      ∃ G_B : Measurement (Polynomial params) ιB,
        ∃ P_A : ProjSubMeas (Polynomial params) ιA,
          ∃ P_B : ProjSubMeas (Polynomial params) ιB,
            ∃ Q_A : ProjMeas (Polynomial params) ιA,
              ∃ Q_B : ProjMeas (Polynomial params) ιB,
                ConsRel strategy.state (uniformDistribution (Point params))
                    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
                    (polynomialEvaluationFamily params G_B.toSubMeas)
                    σ ∧
                  ConsRel strategy.state (uniformDistribution (Point params))
                    (polynomialEvaluationFamily params G_A.toSubMeas)
                    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
                    σ ∧
                  ConsRel strategy.state (uniformDistribution Unit)
                    (constSubMeasFamily G_A.toSubMeas)
                    (constSubMeasFamily G_B.toSubMeas)
                    ζ₁ ∧
                  SDDRel strategy.state (uniformDistribution Unit)
                    (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
                    (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) P_A.toSubMeas))
                    (MakingMeasurementsProjective.orthonormalizationError ζ₁) ∧
                  SDDRel strategy.state (uniformDistribution Unit)
                    (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas))
                    (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) P_B.toSubMeas))
                    (MakingMeasurementsProjective.orthonormalizationError ζ₁) ∧
                  SDDRel strategy.state (uniformDistribution Unit)
                    (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
                    (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas))
                    (MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ₁) ∧
                  SDDRel strategy.state (uniformDistribution Unit)
                    (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas))
                    (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas))
                    (MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ₁)
                  ∧
                  ConsRel strategy.state (uniformDistribution Unit)
                    (constSubMeasFamily Q_A.toSubMeas)
                    (constSubMeasFamily G_B.toSubMeas)
                    (ζ₁ + Real.sqrt
                      (MakingMeasurementsProjective.orthonormalizationError ζ₁)) ∧
                  ConsRel strategy.state (uniformDistribution Unit)
                    (constSubMeasFamily G_A.toSubMeas)
                    (constSubMeasFamily Q_B.toSubMeas)
                    (ζ₁ + Real.sqrt
                      (MakingMeasurementsProjective.orthonormalizationError ζ₁))
  rcases sourceRoleRegisterTwoSidedProjectiveSubmeasurements
      params strategy eps hpass k hk with
    ⟨G_A, G_B, P_A, P_B, hpointAGB, hGApointB, hfull, hleft, hright⟩
  have hfullζ : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ζ₁ := by
    simpa [ζ₁, σ] using hfull
  have hleftζ :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) P_A.toSubMeas))
        (MakingMeasurementsProjective.orthonormalizationError ζ₁) := by
    simpa [ζ₁, σ] using hleft
  have hrightζ :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas))
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) P_B.toSubMeas))
        (MakingMeasurementsProjective.orthonormalizationError ζ₁) := by
    simpa [ζ₁, σ] using hright
  rcases completedProjectiveMeasurementsAndLine169_ofTwoSidedSubmeasurements
      (params := params) (ιA := ιA) (ιB := ιB)
      (strategy := strategy) (G_A := G_A) (G_B := G_B)
      (P_A := P_A) (P_B := P_B) (ζ := ζ₁)
      hfullζ hleftζ hrightζ with
    ⟨Q_A, Q_B, hleftComplete, hrightComplete, hleftLine169, hrightLine169⟩
  refine ⟨G_A, G_B, P_A, P_B, Q_A, Q_B, ?_, ?_, hfullζ, hleftζ, hrightζ,
    hleftComplete, hrightComplete, hleftLine169, hrightLine169⟩
  · simpa [σ] using hpointAGB
  · simpa [σ] using hGApointB

/-- Final point-consistency estimates obtained from the source role-register
route before scalar absorption.

Paper origin: `references/ldt-paper/inductive_step.tex:158-185`.  This theorem
derives the point-evaluation triangle estimates from the completed projective
measurements.  No point-consistency estimate is assumed: the two line-169
polynomial consistency relations are first postprocessed by evaluation, and the
`Q_A,Q_B` estimate is derived from the original `G_A,G_B` consistency together
with the two completion-distance estimates.

The displayed errors are the literal errors produced by the heterogeneous
triangle inequalities used here.  Absorbing these scalar expressions into the
single `mainFormalError` bound is a separate final step. -/
theorem sourceRoleRegisterFinalPointConsistency
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : params.m * params.d ≤ k) :
    let σ : Error :=
      2 * MainInductionStep.mainInductionError params k (3 * eps) (3 * eps) (3 * eps)
    let ζ₁ : Error :=
      σ + 2 * Real.sqrt (3 * eps + σ) + (params.m * params.d : Error) / params.q
    let ζ₂ : Error := MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ₁
    let η : Error :=
      ζ₁ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ₁)
    let ζ₃ : Error := 6 * ζ₁ + 6 * ζ₂
    ∃ Q_A : ProjMeas (Polynomial params) ιA,
      ∃ Q_B : ProjMeas (Polynomial params) ιB,
        ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params Q_B.toSubMeas)
            (σ + 2 * Real.sqrt (η + ζ₃ / 2)) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params Q_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
            (σ + 2 * Real.sqrt (η + ζ₃ / 2)) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params Q_A.toSubMeas)
            (polynomialEvaluationFamily params Q_B.toSubMeas)
            (ζ₃ / 2) ∧
          ConsRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily Q_A.toSubMeas)
            (constSubMeasFamily Q_B.toSubMeas)
            (ζ₃ / 2) := by
  let σ : Error :=
    2 * MainInductionStep.mainInductionError params k (3 * eps) (3 * eps) (3 * eps)
  let ζ₁ : Error :=
    σ + 2 * Real.sqrt (3 * eps + σ) + (params.m * params.d : Error) / params.q
  let ζ₂ : Error := MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ₁
  let η : Error :=
    ζ₁ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ₁)
  let ζ₃ : Error := 6 * ζ₁ + 6 * ζ₂
  change ∃ Q_A : ProjMeas (Polynomial params) ιA,
      ∃ Q_B : ProjMeas (Polynomial params) ιB,
        ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params Q_B.toSubMeas)
            (σ + 2 * Real.sqrt (η + ζ₃ / 2)) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params Q_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
            (σ + 2 * Real.sqrt (η + ζ₃ / 2)) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params Q_A.toSubMeas)
            (polynomialEvaluationFamily params Q_B.toSubMeas)
            (ζ₃ / 2) ∧
          ConsRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily Q_A.toSubMeas)
            (constSubMeasFamily Q_B.toSubMeas)
            (ζ₃ / 2)
  rcases sourceRoleRegisterCompletedProjectiveMeasurements
      params strategy eps hpass k hk with
    ⟨G_A, G_B, P_A, P_B, Q_A, Q_B, hpointAGB, hGApointB, hfull,
      hleft, hright, hleftComplete, hrightComplete, hleftLine169, hrightLine169⟩
  have hfullζ : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ζ₁ := by
    simpa [ζ₁, σ] using hfull
  have hleftCompleteζ :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas))
        ζ₂ := by
    simpa [ζ₂, ζ₁, σ] using hleftComplete
  have hrightCompleteζ :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas))
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas))
        ζ₂ := by
    simpa [ζ₂, ζ₁, σ] using hrightComplete
  have hQQSDD :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas))
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas))
        ζ₃ := by
    simpa [ζ₃, ζ₂] using
      completedProjectiveConsistency_ofFullConsistency
        (params := params) (strategy := strategy) (G_A := G_A) (G_B := G_B)
        (Q_A := Q_A) (Q_B := Q_B) (ζ := ζ₁)
        hfullζ hleftCompleteζ hrightCompleteζ
  have hQQEval : ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params Q_A.toSubMeas)
      (polynomialEvaluationFamily params Q_B.toSubMeas) (ζ₃ / 2) :=
    Test.projectiveEvaluationConsistency_ofFullPolynomialConsistency_heterogeneous
      (params := params) (ψ := strategy.state) Q_A Q_B (ζ₃ := ζ₃) hQQSDD
  let leftConst : IdxProjMeas Unit (Polynomial params) ιA := fun _ => Q_A
  let rightConst : IdxProjMeas Unit (Polynomial params) ιB := fun _ => Q_B
  have hQQUnitApprox :
      SDDRel strategy.state (uniformDistribution Unit)
        (IdxSubMeas.placeLeft (ιB := ιB) (IdxProjMeas.toIdxSubMeas leftConst))
        (IdxSubMeas.placeRight (ιA := ιA) (IdxProjMeas.toIdxSubMeas rightConst))
        (2 * (ζ₃ / 2)) := by
    change SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas))
      (2 * (ζ₃ / 2))
    convert hQQSDD using 1
    ring
  have hQQUnit : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily Q_A.toSubMeas)
      (constSubMeasFamily Q_B.toSubMeas) (ζ₃ / 2) := by
    have hunit :=
      Preliminaries.approxToSimeq_heterogeneous strategy.state
        (uniformDistribution Unit) leftConst rightConst (ζ₃ / 2) hQQUnitApprox
    simpa [leftConst, rightConst, constSubMeasFamily, IdxProjMeas.toIdxSubMeas] using hunit
  have hleftLineEval : ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params Q_A.toSubMeas)
      (polynomialEvaluationFamily params G_B.toSubMeas) η := by
    simpa [η, ζ₁, σ] using
      Test.consRel_constPolynomialEvaluation_heterogeneous
        (params := params) strategy.state Q_A.toMeasurement G_B hleftLine169
  have hrightLineEval : ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params G_A.toSubMeas)
      (polynomialEvaluationFamily params Q_B.toSubMeas) η := by
    simpa [η, ζ₁, σ] using
      Test.consRel_constPolynomialEvaluation_heterogeneous
        (params := params) strategy.state G_A Q_B.toMeasurement hrightLine169
  let pointA : IdxMeas (Point params) (Fq params) ιA :=
    IdxProjMeas.toIdxMeas strategy.pointMeasurementA
  let pointB : IdxMeas (Point params) (Fq params) ιB :=
    IdxProjMeas.toIdxMeas strategy.pointMeasurementB
  let gAEval : IdxMeas (Point params) (Fq params) ιA :=
    Test.polynomialEvaluationMeasurementFamily params G_A
  let gBEval : IdxMeas (Point params) (Fq params) ιB :=
    Test.polynomialEvaluationMeasurementFamily params G_B
  let qAEval : IdxMeas (Point params) (Fq params) ιA :=
    Test.polynomialEvaluationMeasurementFamily params Q_A.toMeasurement
  let qBEval : IdxMeas (Point params) (Fq params) ιB :=
    Test.polynomialEvaluationMeasurementFamily params Q_B.toMeasurement
  have hpointAGBMeas : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas pointA) (IdxMeas.toIdxSubMeas gBEval) σ := by
    simpa [pointA, gBEval, σ, Test.polynomialEvaluationMeasurementFamily] using hpointAGB
  have hGApointBMeas : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas gAEval) (IdxMeas.toIdxSubMeas pointB) σ := by
    simpa [pointB, gAEval, σ, Test.polynomialEvaluationMeasurementFamily] using hGApointB
  have hleftLineMeas : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas qAEval) (IdxMeas.toIdxSubMeas gBEval) η := by
    simpa [qAEval, gBEval, Test.polynomialEvaluationMeasurementFamily] using hleftLineEval
  have hrightLineMeas : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas gAEval) (IdxMeas.toIdxSubMeas qBEval) η := by
    simpa [gAEval, qBEval, Test.polynomialEvaluationMeasurementFamily] using hrightLineEval
  have hQQEvalMeas : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas qAEval) (IdxMeas.toIdxSubMeas qBEval) (ζ₃ / 2) := by
    simpa [qAEval, qBEval, Test.polynomialEvaluationMeasurementFamily] using hQQEval
  have hAliceFinal : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas pointA) (IdxMeas.toIdxSubMeas qBEval)
      (σ + 2 * Real.sqrt (η + ζ₃ / 2)) := by
    exact
      Preliminaries.simeqTriangleInequality_heterogeneous strategy.state
        (uniformDistribution (Point params)) strategy.isNormalized
        (uniformDistribution_weight_sum_le_one (Point params))
        pointA qAEval gBEval qBEval σ η (ζ₃ / 2)
        hpointAGBMeas hleftLineMeas hQQEvalMeas
  have hrightLineSDD :
      SDDRel strategy.state (uniformDistribution (Point params))
        (IdxSubMeas.placeLeft (ιB := ιB) (IdxMeas.toIdxSubMeas gAEval))
        (IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas qBEval))
        (2 * η) :=
    Preliminaries.simeqToApprox_heterogeneous strategy.state
      (uniformDistribution (Point params)) gAEval qBEval η hrightLineMeas
  have hQQEvalSDD :
      SDDRel strategy.state (uniformDistribution (Point params))
        (IdxSubMeas.placeLeft (ιB := ιB) (IdxMeas.toIdxSubMeas qAEval))
        (IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas qBEval))
        (2 * (ζ₃ / 2)) :=
    Preliminaries.simeqToApprox_heterogeneous strategy.state
      (uniformDistribution (Point params)) qAEval qBEval (ζ₃ / 2) hQQEvalMeas
  have hQGSDD :
      SDDRel strategy.state (uniformDistribution (Point params))
        (IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas qBEval))
        (IdxSubMeas.placeLeft (ιB := ιB) (IdxMeas.toIdxSubMeas qAEval))
        (2 * (ζ₃ / 2)) :=
    Preliminaries.sddRel_symm strategy.state (uniformDistribution (Point params))
      _ _ (2 * (ζ₃ / 2)) hQQEvalSDD
  have hgAqAraw :
      SDDRel strategy.state (uniformDistribution (Point params))
        (IdxSubMeas.placeLeft (ιB := ιB) (IdxMeas.toIdxSubMeas gAEval))
        (IdxSubMeas.placeLeft (ιB := ιB) (IdxMeas.toIdxSubMeas qAEval))
        (2 * ((2 * η) + 2 * (ζ₃ / 2))) :=
    Preliminaries.stateDependentDistanceRel_triangle strategy.state
      (uniformDistribution (Point params))
      (IdxSubMeas.placeLeft (ιB := ιB) (IdxMeas.toIdxSubMeas gAEval))
      (IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas qBEval))
      (IdxSubMeas.placeLeft (ιB := ιB) (IdxMeas.toIdxSubMeas qAEval))
      (2 * η) (2 * (ζ₃ / 2)) hrightLineSDD hQGSDD
  have hgAqA :
      SDDRel strategy.state (uniformDistribution (Point params))
        (IdxSubMeas.placeLeft (ιB := ιB) (IdxMeas.toIdxSubMeas gAEval))
        (IdxSubMeas.placeLeft (ιB := ιB) (IdxMeas.toIdxSubMeas qAEval))
        (4 * (η + ζ₃ / 2)) :=
    Preliminaries.stateDependentDistanceRel_mono strategy.state
      (uniformDistribution (Point params))
      (IdxSubMeas.placeLeft (ιB := ιB) (IdxMeas.toIdxSubMeas gAEval))
      (IdxSubMeas.placeLeft (ιB := ιB) (IdxMeas.toIdxSubMeas qAEval))
      (2 * ((2 * η) + 2 * (ζ₃ / 2))) (4 * (η + ζ₃ / 2)) (by
        ring_nf
        exact le_rfl) hgAqAraw
  have hη_nonneg : 0 ≤ η :=
    le_trans
      (bipartiteConsError_nonneg strategy.state (uniformDistribution (Point params)) _ _)
      hrightLineEval.offDiagonalBound
  have hζ3half_nonneg : 0 ≤ ζ₃ / 2 :=
    le_trans
      (bipartiteConsError_nonneg strategy.state (uniformDistribution (Point params)) _ _)
      hQQEval.offDiagonalBound
  have hsqrt_four :
      Real.sqrt (4 * (η + ζ₃ / 2)) = 2 * Real.sqrt (η + ζ₃ / 2) := by
    have hsum_nonneg : 0 ≤ η + ζ₃ / 2 := add_nonneg hη_nonneg hζ3half_nonneg
    calc
      Real.sqrt (4 * (η + ζ₃ / 2))
        = Real.sqrt (4 : Error) * Real.sqrt (η + ζ₃ / 2) := by
            rw [Real.sqrt_mul (show 0 ≤ (4 : Error) by positivity)]
      _ = 2 * Real.sqrt (η + ζ₃ / 2) := by norm_num
  have hBobRaw : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas qAEval) (IdxMeas.toIdxSubMeas pointB)
      (σ + Real.sqrt (4 * (η + ζ₃ / 2))) :=
    Preliminaries.triangleSub_heterogeneous strategy.state
      (uniformDistribution (Point params)) strategy.isNormalized
      (uniformDistribution_weight_sum_le_one (Point params))
      gAEval qAEval (IdxMeas.toIdxSubMeas pointB) σ (4 * (η + ζ₃ / 2))
      hGApointBMeas hgAqA
  have hBobFinal : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas qAEval) (IdxMeas.toIdxSubMeas pointB)
      (σ + 2 * Real.sqrt (η + ζ₃ / 2)) := by
    simpa [hsqrt_four] using hBobRaw
  refine ⟨Q_A, Q_B, ?_, ?_, hQQEval, hQQUnit⟩
  · simpa [pointA, qBEval, Test.polynomialEvaluationMeasurementFamily] using hAliceFinal
  · simpa [pointB, qAEval, Test.polynomialEvaluationMeasurementFamily] using hBobFinal


end ProjStrat

end MIPStarRE.LDT
