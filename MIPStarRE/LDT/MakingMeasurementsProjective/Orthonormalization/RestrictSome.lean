import MIPStarRE.LDT.Tactic.LdtSimp
import MIPStarRE.LDT.MakingMeasurementsProjective.Statements
import MIPStarRE.LDT.Basic.MeasurementLift
import MIPStarRE.LDT.Preliminaries.ComparisonCore
import MIPStarRE.LDT.Test.StrategyCore

/-!
# Section 5 — restriction of completed projective submeasurements

This file contains the elementary order algebra used after applying the
orthonormalization theorem to the option completion of a submeasurement.  If
the repaired projective family keeps at least the original residual mass at the
fresh `none` outcome, then the total of the retained `some` outcomes is
bounded by the original submeasurement total.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

/-- Discard the fresh `none` outcome from an option-indexed projective
submeasurement. The remaining `some a` outcomes still form a projective
submeasurement. -/
noncomputable def restrictSomeProjSubMeas {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (P : ProjSubMeas (Option Outcome) ι) :
    ProjSubMeas Outcome ι where
  toSubMeas :=
    { outcome := fun a => P.outcome (some a)
      total := ∑ a : Outcome, P.outcome (some a)
      outcome_pos := fun a => P.outcome_pos (some a)
      sum_eq_total := rfl
      total_le_one := by
        calc
          ∑ a : Outcome, P.outcome (some a)
            ≤ P.outcome none + ∑ a : Outcome, P.outcome (some a) :=
                le_add_of_nonneg_left (P.outcome_pos none)
          _ = ∑ oa : Option Outcome, P.outcome oa := by
                simp [Fintype.sum_option]
          _ = P.total := by rw [P.sum_eq_total]
          _ ≤ 1 := P.total_le_one }
  proj := fun a => by simpa using P.proj (some a)

/-- If the projective replacement of the completed measurement puts at least the
original residual mass on the fresh `none` outcome, then the retained `some`
outcomes have total dominated by the original submeasurement total.

This is the precise construction-level order statement needed by the
monotone-total route in the self-improvement argument.  It separates the
formal algebra from the still-missing repair invariant
`(optionCompletion A).outcome none ≤ P.outcome none`. -/
theorem restrictSomeProjSubMeas_total_le_of_optionCompletion_residual_le
    {Outcome : Type*} {ι : Type*} [Fintype Outcome]
    [Fintype ι] [DecidableEq ι] [DecidableEq Outcome]
    (A : SubMeas Outcome ι) (P : ProjSubMeas (Option Outcome) ι)
    (hresidual : (optionCompletion A).outcome none ≤ P.outcome none) :
    (restrictSomeProjSubMeas P).toSubMeas.total ≤ A.total := by
  let S : MIPStarRE.Quantum.Op ι := ∑ a : Outcome, P.outcome (some a)
  have hsum_le_one :
      P.outcome none + S ≤ (1 : MIPStarRE.Quantum.Op ι) := by
    calc
      P.outcome none + S
          = ∑ oa : Option Outcome, P.outcome oa := by
              simp [S, Fintype.sum_option]
      _ = P.total := by rw [P.sum_eq_total]
      _ ≤ 1 := P.total_le_one
  have hresidual' :
      (1 : MIPStarRE.Quantum.Op ι) - A.total ≤ P.outcome none := by
    simpa using hresidual
  have hcompleted :
      (1 : MIPStarRE.Quantum.Op ι) - A.total + S ≤
        (1 : MIPStarRE.Quantum.Op ι) := by
    calc
      (1 : MIPStarRE.Quantum.Op ι) - A.total + S
          ≤ P.outcome none + S := by
              simpa [add_comm] using add_le_add_right hresidual' S
      _ ≤ 1 := hsum_le_one
  have hnonneg : 0 ≤ A.total - S := by
    have hsub : 0 ≤
        (1 : MIPStarRE.Quantum.Op ι) -
          ((1 : MIPStarRE.Quantum.Op ι) - A.total + S) :=
      sub_nonneg.mpr hcompleted
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hsub
  have hS_le : S ≤ A.total := sub_nonneg.mp hnonneg
  simpa [restrictSomeProjSubMeas, S] using hS_le

/-- The right-register expectation form of
`restrictSomeProjSubMeas_total_le_of_optionCompletion_residual_le`.

This is the scalar comparison needed by the monotone-total transport in the
self-improvement theorem.  The proof first obtains the operator inequality on
the local Hilbert space and then applies monotonicity of right tensor placement
and of expectation in the ambient state. -/
theorem restrictSomeProjSubMeas_rightTensor_total_ev_le_of_optionCompletion_residual_le
    {Outcome : Type*} {ι : Type*} [Fintype Outcome]
    [Fintype ι] [DecidableEq ι] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι)) (A : SubMeas Outcome ι)
    (P : ProjSubMeas (Option Outcome) ι)
    (hresidual : (optionCompletion A).outcome none ≤ P.outcome none) :
    ev ψ (rightTensor (ι₁ := ι) (restrictSomeProjSubMeas P).toSubMeas.total) ≤
      ev ψ (rightTensor (ι₁ := ι) A.total) := by
  exact ev_mono ψ _ _ <|
    rightTensor_mono
      (restrictSomeProjSubMeas_total_le_of_optionCompletion_residual_le A P hresidual)

end MIPStarRE.LDT.MakingMeasurementsProjective
