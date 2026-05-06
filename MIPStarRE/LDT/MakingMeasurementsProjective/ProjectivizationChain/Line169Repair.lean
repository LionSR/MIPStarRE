import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Handoff
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.MatchMass

/-!
# Section 10 — local line-169 repair

This module contains the local line-169 repair for the projectivization chain.
It compares a pre-projective measurement with the orthonormalized
submeasurement before completion, so that completion contributes no further
loss to the relevant diagonal match mass.
-/

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries (completeAtOutcomeProj)

/-! ### Local line-169 repair via pre-completion orthonormalization -/

namespace ProjectivizationLine169Repair

/-- A left-lifted `≈`-statement controls the loss in diagonal bipartite match
mass against a fixed partner measurement by the square root of the SDD error.

This is the single-question `Unit` specialization of
`prop:easy-approx-from-approx_delta`, written directly in the bipartite
`qBipartiteMatchMass` notation used by the Step 6 projectivization chain. -/
private theorem qBipartiteMatchMass_ge_sub_sqrt_of_sdd
    {Outcome : Type*} {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    (G : Measurement Outcome ι) (P : SubMeas Outcome ι) (B : Measurement Outcome ι)
    {ε : Error}
    (hclose : SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G.toSubMeas.liftLeft)
      (constSubMeasFamily P.liftLeft)
      ε) :
    qBipartiteMatchMass ψ P B.toSubMeas ≥
      qBipartiteMatchMass ψ G.toSubMeas B.toSubMeas - Real.sqrt ε := by
  have hgap :=
    MIPStarRE.LDT.Preliminaries.easyApproxFromApproxDelta ψ hψ
      (uniformDistribution Unit) (uniformDistribution_weight_sum_le_one Unit)
      (constSubMeasFamily G.toSubMeas.liftLeft)
      (constSubMeasFamily P.liftLeft)
      (constSubMeasFamily B.toSubMeas.liftRight)
      ε hclose
  have hgap' :
      |qBipartiteMatchMass ψ G.toSubMeas B.toSubMeas -
          qBipartiteMatchMass ψ P B.toSubMeas| ≤
        Real.sqrt ε := by
    simpa [avgOver, uniformDistribution, constSubMeasFamily,
      qBipartiteMatchMass, SubMeas.liftLeft, SubMeas.liftRight,
      leftTensor_mul_rightTensor_eq_opTensor] using hgap
  have hdiff :
      qBipartiteMatchMass ψ G.toSubMeas B.toSubMeas -
          qBipartiteMatchMass ψ P B.toSubMeas ≤
        Real.sqrt ε :=
    (abs_le.mp hgap').2
  linarith

/-- Completing the orthonormalized submeasurement after comparing it to the
source measurement before completion yields a repaired line-169 transport with
additive loss `√ε`.

This avoids the larger `ζ + √ζ₂` loss that comes from applying `triangleSub`
only after the completion step.  The completion itself contributes no further
loss here, because it only adds nonnegative diagonal match mass at the chosen
outcome. -/
theorem leftConsistency_of_completion_and_sdd
    {Outcome : Type*} {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    {G_A G_B : Measurement Outcome ι} (P_A : ProjSubMeas Outcome ι) (a_A : Outcome)
    {ζ ε : Error}
    (hpre : ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas)
      ζ)
    (horth : SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas.liftLeft)
      (constSubMeasFamily P_A.toSubMeas.liftLeft)
      ε) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily (completeAtOutcomeProj P_A a_A).toSubMeas)
      (constSubMeasFamily G_B.toSubMeas)
      (ζ + Real.sqrt ε) := by
  let Q_A := completeAtOutcomeProj P_A a_A
  have hpre_q : qBipartiteConsDefect ψ G_A.toSubMeas G_B.toSubMeas ≤ ζ := by
    simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]
      using hpre.offDiagonalBound
  have hζ0 : 0 ≤ ζ :=
    le_trans (qBipartiteConsDefect_nonneg ψ G_A.toSubMeas G_B.toSubMeas) hpre_q
  have hone : ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) = 1 :=
    ev_one_of_isNormalized ψ hψ
  have hmatchG :
      1 - qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas ≤ ζ := by
    have hmax :
        max 0 (ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) -
            qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas) ≤ ζ := by
      simpa [qBipartiteConsDefect, qBipartiteMatchMass, G_A.total_eq_one,
        G_B.total_eq_one, opTensor] using hpre_q
    have hinner :
        ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) -
            qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas ≤ ζ :=
      le_trans (le_max_right 0 _) hmax
    simpa [hone] using hinner
  have hmatchP :
      qBipartiteMatchMass ψ P_A.toSubMeas G_B.toSubMeas ≥
        qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas - Real.sqrt ε :=
    qBipartiteMatchMass_ge_sub_sqrt_of_sdd ψ hψ G_A P_A.toSubMeas G_B horth
  have hmatchQ :
      qBipartiteMatchMass ψ Q_A.toSubMeas G_B.toSubMeas ≥
        qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas - Real.sqrt ε := by
    calc
      qBipartiteMatchMass ψ Q_A.toSubMeas G_B.toSubMeas
          ≥ qBipartiteMatchMass ψ P_A.toSubMeas G_B.toSubMeas :=
            ProjectivizationMatchMassMonotonicity.completeAtOutcomeProj_left_matchMass_ge
              ψ P_A G_B.toSubMeas a_A
      _ ≥ qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas - Real.sqrt ε := hmatchP
  have hmatchQ' :
      1 - qBipartiteMatchMass ψ Q_A.toSubMeas G_B.toSubMeas ≤ ζ + Real.sqrt ε := by
    linarith
  have hdefectQ :
      qBipartiteConsDefect ψ Q_A.toSubMeas G_B.toSubMeas ≤ ζ + Real.sqrt ε := by
    have hmax :
        max 0 (ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) -
            qBipartiteMatchMass ψ Q_A.toSubMeas G_B.toSubMeas) ≤
          ζ + Real.sqrt ε := by
      exact max_le_iff.mpr
        ⟨add_nonneg hζ0 (Real.sqrt_nonneg _), by simpa [hone] using hmatchQ'⟩
    simpa [qBipartiteConsDefect, qBipartiteMatchMass, Q_A.total_eq_one,
      G_B.total_eq_one, opTensor] using hmax
  constructor
  simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]
    using hdefectQ

/-- Bob-side mirror of `leftConsistency_of_completion_and_sdd`, still using the
pre-completion orthonormalization comparison and the fact that completion adds
only nonnegative diagonal match mass. -/
theorem rightConsistency_of_completion_and_sdd
    {Outcome : Type*} {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    {G_A G_B : Measurement Outcome ι} (P_B : ProjSubMeas Outcome ι) (a_B : Outcome)
    {ζ ε : Error}
    (hpre : ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_B.toSubMeas)
      (constSubMeasFamily G_A.toSubMeas)
      ζ)
    (horth : SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_B.toSubMeas.liftLeft)
      (constSubMeasFamily P_B.toSubMeas.liftLeft)
      ε) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily (completeAtOutcomeProj P_B a_B).toSubMeas)
      (constSubMeasFamily G_A.toSubMeas)
      (ζ + Real.sqrt ε) := by
  let Q_B := completeAtOutcomeProj P_B a_B
  have hpre_q : qBipartiteConsDefect ψ G_B.toSubMeas G_A.toSubMeas ≤ ζ := by
    simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]
      using hpre.offDiagonalBound
  have hζ0 : 0 ≤ ζ :=
    le_trans (qBipartiteConsDefect_nonneg ψ G_B.toSubMeas G_A.toSubMeas) hpre_q
  have hone : ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) = 1 :=
    ev_one_of_isNormalized ψ hψ
  have hmatchG :
      1 - qBipartiteMatchMass ψ G_B.toSubMeas G_A.toSubMeas ≤ ζ := by
    have hmax :
        max 0 (ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) -
            qBipartiteMatchMass ψ G_B.toSubMeas G_A.toSubMeas) ≤ ζ := by
      simpa [qBipartiteConsDefect, qBipartiteMatchMass, G_B.total_eq_one,
        G_A.total_eq_one, opTensor] using hpre_q
    have hinner :
        ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) -
            qBipartiteMatchMass ψ G_B.toSubMeas G_A.toSubMeas ≤ ζ :=
      le_trans (le_max_right 0 _) hmax
    simpa [hone] using hinner
  have hmatchP :
      qBipartiteMatchMass ψ P_B.toSubMeas G_A.toSubMeas ≥
        qBipartiteMatchMass ψ G_B.toSubMeas G_A.toSubMeas - Real.sqrt ε :=
    qBipartiteMatchMass_ge_sub_sqrt_of_sdd ψ hψ G_B P_B.toSubMeas G_A horth
  have hmatchQ :
      qBipartiteMatchMass ψ Q_B.toSubMeas G_A.toSubMeas ≥
        qBipartiteMatchMass ψ G_B.toSubMeas G_A.toSubMeas - Real.sqrt ε := by
    calc
      qBipartiteMatchMass ψ Q_B.toSubMeas G_A.toSubMeas
          ≥ qBipartiteMatchMass ψ P_B.toSubMeas G_A.toSubMeas :=
            ProjectivizationMatchMassMonotonicity.completeAtOutcomeProj_left_matchMass_ge
              ψ P_B G_A.toSubMeas a_B
      _ ≥ qBipartiteMatchMass ψ G_B.toSubMeas G_A.toSubMeas - Real.sqrt ε := hmatchP
  have hmatchQ' :
      1 - qBipartiteMatchMass ψ Q_B.toSubMeas G_A.toSubMeas ≤ ζ + Real.sqrt ε := by
    linarith
  have hdefectQ :
      qBipartiteConsDefect ψ Q_B.toSubMeas G_A.toSubMeas ≤ ζ + Real.sqrt ε := by
    have hmax :
        max 0 (ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) -
            qBipartiteMatchMass ψ Q_B.toSubMeas G_A.toSubMeas) ≤
          ζ + Real.sqrt ε := by
      exact max_le_iff.mpr
        ⟨add_nonneg hζ0 (Real.sqrt_nonneg _), by simpa [hone] using hmatchQ'⟩
    simpa [qBipartiteConsDefect, qBipartiteMatchMass, Q_B.total_eq_one,
      G_A.total_eq_one, opTensor] using hmax
  constructor
  simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]
    using hdefectQ

/-- Checked local repair of the paper's line-169 Alice-side replacement step.

Instead of applying `triangleSub` after completion, compare `G_A` directly with
the orthonormalized submeasurement `P_A`, whose `≈`-error is
`orthonormalizationError ζ = 100·ζ^{1/4}`.  The resulting additive loss is
`√(100·ζ^{1/4}) = 10·ζ^{1/8}`, and the completion step itself does not increase
the defect. -/
theorem leftConsistency_with_orthonormalization_loss
    {Outcome : Type*} {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    {G_A G_B : Measurement Outcome ι} (P_A : ProjSubMeas Outcome ι) (a_A : Outcome)
    {ζ : Error}
    (hpre : ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas)
      ζ)
    (horth : SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas.liftLeft)
      (constSubMeasFamily P_A.toSubMeas.liftLeft)
      (orthonormalizationError ζ)) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily (completeAtOutcomeProj P_A a_A).toSubMeas)
      (constSubMeasFamily G_B.toSubMeas)
      (ζ + 10 * Real.rpow ζ (1 / (8 : Error))) := by
  have hpre_q : qBipartiteConsDefect ψ G_A.toSubMeas G_B.toSubMeas ≤ ζ := by
    simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]
      using hpre.offDiagonalBound
  have hζ0 : 0 ≤ ζ :=
    le_trans (qBipartiteConsDefect_nonneg ψ G_A.toSubMeas G_B.toSubMeas) hpre_q
  have hsqrt :=
    MIPStarRE.LDT.MakingMeasurementsProjective.sqrt_orthonormalizationError_eq hζ0
  simpa [hsqrt] using
    leftConsistency_of_completion_and_sdd ψ hψ P_A a_A hpre horth

/-- Bob-side mirror of `leftConsistency_with_orthonormalization_loss`. -/
theorem rightConsistency_with_orthonormalization_loss
    {Outcome : Type*} {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    {G_A G_B : Measurement Outcome ι} (P_B : ProjSubMeas Outcome ι) (a_B : Outcome)
    {ζ : Error}
    (hpre : ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_B.toSubMeas)
      (constSubMeasFamily G_A.toSubMeas)
      ζ)
    (horth : SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_B.toSubMeas.liftLeft)
      (constSubMeasFamily P_B.toSubMeas.liftLeft)
      (orthonormalizationError ζ)) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily (completeAtOutcomeProj P_B a_B).toSubMeas)
      (constSubMeasFamily G_A.toSubMeas)
      (ζ + 10 * Real.rpow ζ (1 / (8 : Error))) := by
  have hpre_q : qBipartiteConsDefect ψ G_B.toSubMeas G_A.toSubMeas ≤ ζ := by
    simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]
      using hpre.offDiagonalBound
  have hζ0 : 0 ≤ ζ :=
    le_trans (qBipartiteConsDefect_nonneg ψ G_B.toSubMeas G_A.toSubMeas) hpre_q
  have hsqrt :=
    MIPStarRE.LDT.MakingMeasurementsProjective.sqrt_orthonormalizationError_eq hζ0
  simpa [hsqrt] using
    rightConsistency_of_completion_and_sdd ψ hψ P_B a_B hpre horth

end ProjectivizationLine169Repair

end MIPStarRE.LDT.MakingMeasurementsProjective
