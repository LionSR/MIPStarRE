import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Basic

/-!
# Section 10 — completion match-mass helper

This module contains the only match-mass fact still used by the active Step 6
projectivization route.  Completing a projective submeasurement at one
distinguished outcome can only increase its diagonal match mass against a fixed
partner submeasurement, because the completion adds a positive residual at a
single outcome.

The older exact line-169 monotonicity interfaces have been retired.  The active
`mainFormal` pipeline uses the repaired pre-completion transport in
`ProjectivizationChain.Line169Repair`, and this file now keeps only the
completion lemma that route consumes.
-/

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries (completeAtOutcome completeAtOutcomeProj)

/-! ### Completion preserves diagonal match mass -/

namespace ProjectivizationMatchMassMonotonicity

/-- Completing a projective submeasurement at one outcome can only increase its
diagonal match mass against a fixed right-side submeasurement.

The completed measurement is obtained by adding the positive residual
`1 - P.total` to a single outcome.  The corresponding extra contribution to
`qBipartiteMatchMass` is therefore nonnegative. -/
theorem completeAtOutcomeProj_left_matchMass_ge {Outcome : Type*} {ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (P : ProjSubMeas Outcome ιA)
    (B : SubMeas Outcome ιB) (a0 : Outcome) :
    qBipartiteMatchMass ψ (completeAtOutcomeProj P a0).toSubMeas B ≥
      qBipartiteMatchMass ψ P.toSubMeas B := by
  classical
  unfold qBipartiteMatchMass
  refine Finset.sum_le_sum ?_
  intro a _
  by_cases ha : a = a0
  · subst a
    have hres_nonneg : 0 ≤ (1 : MIPStarRE.Quantum.Op ιA) - P.toSubMeas.total :=
      sub_nonneg.mpr P.toSubMeas.total_le_one
    have hextra_nonneg :
        0 ≤ ev ψ (opTensor ((1 : MIPStarRE.Quantum.Op ιA) - P.toSubMeas.total)
          (B.outcome a0)) :=
      ev_nonneg_of_psd ψ _ <| opTensor_nonneg hres_nonneg (B.outcome_pos a0)
    simp [completeAtOutcome, opTensor_add_left_local, ev_add]
    linarith
  · simp [completeAtOutcome, ha]

end ProjectivizationMatchMassMonotonicity

end MIPStarRE.LDT.MakingMeasurementsProjective
