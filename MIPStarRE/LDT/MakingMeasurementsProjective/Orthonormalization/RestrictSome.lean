import MIPStarRE.LDT.MakingMeasurementsProjective.Statements

/-!
# Section 5 — restriction of completed projective submeasurements

This file contains the elementary order algebra used after applying the
orthonormalization theorem to the option completion of a submeasurement.
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
      total_le_one :=
        ((le_add_of_nonneg_left (P.outcome_pos none)).trans_eq
          ((Fintype.sum_option P.outcome).symm.trans P.sum_eq_total)).trans P.total_le_one }
  proj := fun a => by simpa using P.proj (some a)

end MIPStarRE.LDT.MakingMeasurementsProjective
