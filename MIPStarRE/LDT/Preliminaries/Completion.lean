import MIPStarRE.LDT.Preliminaries.SwitchSandwichPrep.Core

/-!
# Preliminary completion lemmas

Structural completion helpers that stay close to `completeAtOutcome` while
keeping only the light projectivity dependencies from
`SwitchSandwichPrep/Core.lean`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- Completing a projective submeasurement at a distinguished outcome preserves
projectivity. The residual effect `1 - P.total` is a projection orthogonal to
`P.outcome a0`, so the completed effect remains idempotent. -/
noncomputable def completeAtOutcomeProj {Outcome : Type*}
    {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (P : ProjSubMeas Outcome ι) (a0 : Outcome) : ProjMeas Outcome ι := by
  classical
  refine
    { toMeasurement := completeAtOutcome P.toSubMeas a0
      proj := ?_ }
  intro a
  by_cases ha : a = a0
  · subst a
    let T : MIPStarRE.Quantum.Op ι := P.total
    let Pa : MIPStarRE.Quantum.Op ι := P.outcome a0
    let R : MIPStarRE.Quantum.Op ι := 1 - T
    have hTT : T * T = T := by
      simpa [T] using projSubMeas_total_proj P
    have hPaT : Pa * T = Pa := by
      simpa [Pa, T] using projSubMeas_outcome_mul_total_eq_outcome P a0
    have hPa_star : IsStarProjection Pa := by
      exact MIPStarRE.Quantum.IsProj.isStarProjection
        { isHermitian := (Matrix.nonneg_iff_posSemidef.mp (P.outcome_pos a0)).isHermitian
          idempotent := by simpa [Pa] using P.proj a0 }
    have hT_star : IsStarProjection T := by
      exact MIPStarRE.Quantum.IsProj.isStarProjection
        { isHermitian := (Matrix.nonneg_iff_posSemidef.mp P.total_nonneg).isHermitian
          idempotent := hTT }
    have hR_star : IsStarProjection R := by
      simpa [R] using hT_star.one_sub
    have hPaR : Pa * R = 0 := by
      calc
        Pa * R = Pa * (1 - T) := by rfl
        _ = Pa - Pa * T := by rw [mul_sub, mul_one]
        _ = 0 := by simp [hPaT]
    have hproj :
        (P.outcome a0 + (1 - P.total)) * (P.outcome a0 + (1 - P.total)) =
          P.outcome a0 + (1 - P.total) := by
      simpa [Pa, R] using (hPa_star.add hR_star hPaR).isIdempotentElem.eq
    simpa [completeAtOutcome] using hproj
  · simpa [completeAtOutcome, ha] using P.proj a

@[simp] theorem completeAtOutcomeProj_toMeasurement {Outcome : Type*}
    {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (P : ProjSubMeas Outcome ι) (a0 : Outcome) :
    (completeAtOutcomeProj P a0).toMeasurement = completeAtOutcome P.toSubMeas a0 :=
  rfl

@[simp] theorem completeAtOutcomeProj_toSubMeas {Outcome : Type*}
    {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (P : ProjSubMeas Outcome ι) (a0 : Outcome) :
    (completeAtOutcomeProj P a0).toSubMeas = (completeAtOutcome P.toSubMeas a0).toSubMeas :=
  rfl

end MIPStarRE.LDT.Preliminaries
